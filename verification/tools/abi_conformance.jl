#!/usr/bin/env julia
# SPDX-License-Identifier: MPL-2.0
# Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# abi_conformance.jl — gap-1 (interface) drift gate, MULTI-GUEST.
#
# The Idris2 proofs verify a MODEL of each guest's ABI (ABI.Foreign for safe_nif,
# ABI.BufferAbi for the buffer guest). They do NOT, by themselves, establish that the
# model mirrors the ACTUAL built artifact. This checker closes that interface-level gap
# mechanically: for each guest it parses the authoritative model from its Idris source
# and the REAL exports + signatures from the built .wasm, and FAILS if they drift. So a
# change to a Zig source (or to a proof) that desynchronises the proven ABI from the
# shipped binary breaks CI instead of passing silently.
#
# Scope honesty: this checks the INTERFACE (export names, param types, result types) —
# i.e. that the real binary's signatures are exactly the verified model's signatures.
# It does NOT prove the code's BEHAVIOUR matches the model (that sum_f32 truly sums);
# that is the metamorphic/behaviour gate (GAP-1b) and, long-term, extraction. This is the
# buildable front edge of model<->code faithfulness.
#
# GUESTS (the manifest below): safe_nif (ABI.Foreign, single-return WasmFuncSpec) and
# buffer_abi (ABI.BufferAbi, multi-value/void-faithful WasmSig). burble_fft is intentionally
# NOT here: it is not built into any artifact dir and its fft/ifft use (ptr,len) slice
# marshalling, which is the ABI-6 array obligation — see PROOF-STATUS (ABI-7 ledger).
#
# Usage:
#   julia verification/tools/abi_conformance.jl            # check ALL guests in the manifest
#   julia verification/tools/abi_conformance.jl PATH.wasm  # check one wasm (matched to a guest,
#                                                          # else against the safe_nif model)
# Exit 0 = every checked artifact conforms to its verified ABI model; non-zero = drift.
#
# Julia port of the former verification/tools/abi_conformance.py (Python is banned
# estate-wide); checks, output text and exit codes are unchanged. Tooling only: this
# script is not an FFI or an ABI layer (FFIs stay pure Zig, ABIs stay pure Idris2).

const REPO = normpath(joinpath(@__DIR__, "..", ".."))
const IDRIS = joinpath(REPO, "verification", "proofs", "idris2", "ABI")

# Model value type -> WASM value type.
const TYMAP = Dict("I32" => "i32", "I64" => "i64", "F32" => "f32", "F64" => "f64")
ty(t) = haskey(TYMAP, t) ? TYMAP[t] : error("unknown model value type: $t")
words(s) = String.(split(s))
csv(s) = filter(!isempty, strip.(split(s, ",")))
# Python list repr, e.g. ['i32', 'i32'], used in drift messages.
pyl(a) = "[" * join(("'" * x * "'" for x in a), ", ") * "]"

# The guest manifest: name -> built artifact, Idris model source, constructor, return format.
#   fmt "single": MkWasmFuncSpec "name" [params] Ret      (one result word; safe_nif)
#   fmt "multi" : MkWasmSig      "name" [params] [results] ([] = void; buffer_abi)
const GUESTS = [
    (name = "safe_nif",
     wasm = joinpath(REPO, "priv", "safe_nif_ReleaseSafe.wasm"),
     model = joinpath(IDRIS, "Foreign.idr"), ctor = "MkWasmFuncSpec", fmt = "single"),
    (name = "buffer_abi",
     wasm = joinpath(REPO, "zig", "buffer_abi_build", "buffer_abi_ReleaseSafe.wasm"),
     model = joinpath(IDRIS, "BufferAbi.idr"), ctor = "MkWasmSig", fmt = "multi"),
]

out(s) = println(stdout, s)
err(s) = println(stderr, s)

# Idris spec bindings -> Dict(name => (params, results)).
#
# `single`: `<ctor> "name" [T,..] Ret`        -> results = [Ret]
# `multi` : `<ctor> "name" [T,..] [R,..]`      -> results = [R,..]   ([] = void)
function parse_model(file, ctor, fmt)
    spec = fmt == "single" ?
        Regex("$ctor\\s+\"([^\"]+)\"\\s+\\[([^\\]]*)\\]\\s+(\\w+)") :
        Regex("$ctor\\s+\"([^\"]+)\"\\s+\\[([^\\]]*)\\]\\s+\\[([^\\]]*)\\]")
    model = Dict{String,Tuple{Vector{String},Vector{String}}}()
    for line in split(read(file, String), "\n")
        occursin("constructor", line) && continue # skip the record's constructor declaration line
        m = match(spec, line)
        m === nothing && continue
        params = ty.(csv(m.captures[2]))
        results = fmt == "single" ? [ty(strip(m.captures[3]))] : ty.(csv(m.captures[3]))
        model[m.captures[1]] = (params, results)
    end
    return model
end

# Built .wasm -> (Dict(export_name => func_symbol), Dict(func_symbol => (params, results))).
function parse_wasm(file)
    wat = try
        read(`wasm-tools print $file`, String)
    catch e
        error("wasm-tools print failed: $(sprint(showerror, e))")
    end
    exports = Dict{String,String}()
    for m in eachmatch(r"\(export \"([^\"]+)\" \(func \$([^)\s]+)\)\)", wat)
        exports[m.captures[1]] = m.captures[2]
    end
    funcsig = Dict{String,Tuple{Vector{String},Vector{String}}}()
    fdef = r"\(func \$(\S+) \(;\d+;\)(?: \(type \d+\))?(?: \(param ([^)]*)\))?(?: \(result ([^)]*)\))?"
    for m in eachmatch(fdef, wat)
        haskey(funcsig, m.captures[1]) && continue # first (the real def) wins
        funcsig[m.captures[1]] = (m.captures[2] === nothing ? String[] : words(m.captures[2]),
                                  m.captures[3] === nothing ? String[] : words(m.captures[3]))
    end
    return exports, funcsig
end

# Check one guest's built artifact against its verified model. Returns (ok, nspecs).
function check_guest(name, wasm, model_path, ctor, fmt)
    if !isfile(wasm)
        err("FATAL [$name]: wasm not built: $(relpath(wasm, REPO))  " *
            "(run `just build-wasm` / `bash zig/buffer_abi_build.sh`)")
        return false, 0
    end
    if !isfile(model_path)
        err("FATAL [$name]: model not found: $model_path")
        return false, 0
    end
    model = parse_model(model_path, ctor, fmt)
    if isempty(model)
        err("FATAL [$name]: no specs parsed from $(relpath(model_path, REPO))")
        return false, 0
    end
    exports, funcsig = parse_wasm(wasm)

    out("== ABI conformance [$name]: $(relpath(wasm, REPO)) vs " *
        "$(basename(model_path)) ($(length(model)) specs) ==")
    fails = String[]
    for fname in sort(collect(keys(model)))
        eparams, eresults = model[fname]
        sym = get(exports, fname, nothing)
        if sym === nothing
            push!(fails, "$fname: in the verified model but NOT exported by the .wasm")
            continue
        end
        sig = get(funcsig, sym, nothing)
        if sig === nothing
            push!(fails, "$fname: export -> \$$sym but no func definition found")
            continue
        end
        aparams, aresults = sig
        if aparams != eparams
            push!(fails, "$fname: PARAM drift — model $(pyl(eparams)) vs wasm $(pyl(aparams))")
        elseif aresults != eresults
            push!(fails, "$fname: RESULT drift — model $(pyl(eresults)) vs wasm $(pyl(aresults))")
        else
            ret = isempty(eresults) ? "()" : join(eresults, " ")
            out("  ok   $fname: ($(join(eparams, " "))) -> $ret")
        end
    end

    extra = sort([n for n in keys(exports) if !haskey(model, n) && n != "memory"])
    for n in extra
        out("  warn $n: exported by the .wasm but NOT in the verified ABI model")
    end

    if !isempty(fails)
        err("\nDRIFT [$name] — the built artifact does not match the verified ABI model:")
        for f in fails
            err("  FAIL $f")
        end
        err("$(length(fails)) conformance failure(s) for $name\n")
        return false, length(model)
    end
    out("PASS [$name]: all $(length(model)) verified ABI specs conform" *
        (isempty(extra) ? "" : " ($(length(extra)) un-modelled export(s) warned)") * "\n")
    return true, length(model)
end

# wasm-tools must be present; the gate runs, never silently skips.
function tool_ok()
    if Sys.which("wasm-tools") === nothing
        err("FATAL: wasm-tools not installed — the conformance gate must run, never skip")
        return false
    end
    return true
end

function main()
    tool_ok() || return 2

    # One explicit wasm path: check it against its matching guest, else the safe_nif model.
    if !isempty(ARGS)
        target = abspath(ARGS[1])
        i = findfirst(g -> abspath(g.wasm) == target, GUESTS)
        g = GUESTS[something(i, 1)]
        ok, _ = check_guest(g.name, target, g.model, g.ctor, g.fmt)
        return ok ? 0 : 1
    end

    # No arg: check every guest in the manifest.
    all_ok = true
    total = 0
    for g in GUESTS
        ok, n = check_guest(g.name, g.wasm, g.model, g.ctor, g.fmt)
        all_ok = all_ok && ok
        total += n
    end
    if all_ok
        out("PASS: all $(length(GUESTS)) guest(s) conform ($total ABI specs verified against built artifacts)")
        return 0
    end
    err("FAIL: at least one guest drifted from its verified ABI model")
    return 1
end

exit(main())
