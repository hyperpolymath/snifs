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
#
# The whole file is matched (not line by line), so a binding wrapped across lines
# still parses. Every `<ctor> "` use is counted and compared with what was recovered:
# a declared spec that cannot be parsed is an error, never silently dropped (a dropped
# spec would let the gate pass without checking that export).
function parse_model(file, ctor, fmt)
    spec = fmt == "single" ?
        Regex("$ctor\\s+\"([^\"]+)\"\\s+\\[([^\\]]*)\\]\\s+(\\w+)") :
        Regex("$ctor\\s+\"([^\"]+)\"\\s+\\[([^\\]]*)\\]\\s+\\[([^\\]]*)\\]")
    text = read(file, String)
    declared = length(collect(eachmatch(Regex("$ctor\\s+\""), text)))
    model = Dict{String,Tuple{Vector{String},Vector{String}}}()
    for m in eachmatch(spec, text)
        params = ty.(csv(m.captures[2]))
        results = fmt == "single" ? [ty(strip(m.captures[3]))] : ty.(csv(m.captures[3]))
        model[m.captures[1]] = (params, results)
    end
    if length(model) != declared
        error("$(basename(file)): $declared `$ctor` spec(s) declared but only " *
              "$(length(model)) parsed (continuation or format not understood)")
    end
    return model
end

# Read the balanced "(...)" group starting at text[i] == '('. Returns (inner, next_index).
function paren_group(text, i)
    depth = 0
    j = i
    while j <= lastindex(text)
        c = text[j]
        if c == '('
            depth += 1
        elseif c == ')'
            depth -= 1
            depth == 0 && return text[nextind(text, i):prevind(text, j)], nextind(text, j)
        end
        j = nextind(text, j)
    end
    error("unbalanced parentheses in wasm-tools output")
end

# Value types of one "(param ...)" / "(result ...)" group body; `$name` tokens dropped.
valtypes(body) = filter(w -> !startswith(w, "\$"), words(body))

# Parse consecutive "(type X)" / "(param ..)" / "(result ..)" groups from text[i:].
# Returns (typeref or nothing, params, results).
function parse_sig_groups(text, i)
    tref = nothing
    params = String[]
    results = String[]
    while true
        m = match(r"\G\s*\(", text, i)
        m === nothing && break
        open = m.offset + length(m.match) - 1
        body, nxt = paren_group(text, open)
        head, _, rest = partition(strip(body), r"\s")
        if head == "param"
            append!(params, valtypes(rest))
        elseif head == "result"
            append!(results, valtypes(rest))
        elseif head == "type"
            tref = strip(rest)
        else
            break
        end
        i = nxt
    end
    return tref, params, results
end

# `partition` for a regex separator (Base only has string/char separators).
function partition(s, sep::Regex)
    m = match(sep, s)
    m === nothing && return s, "", ""
    return s[1:prevind(s, m.offset)], m.match, s[m.offset + length(m.match):end]
end

# Built .wasm -> (Dict(export_name => function key), Dict(function key => (params, results))).
#
# Functions are keyed by their numeric index, so exports that print as `(func 3)` (no
# debug names) and `(func $sym)` both resolve. A function's signature comes from its
# `(type X)` reference when it has one (looked up in the type section), else from its
# inline param/result groups. A signature that cannot be decoded is an error, never void.
function parse_wasm(file)
    wat = try
        read(`wasm-tools print $file`, String)
    catch e
        error("wasm-tools print failed: $(sprint(showerror, e))")
    end

    # Type section: key by index and by $name.
    types = Dict{String,Tuple{Vector{String},Vector{String}}}()
    for m in eachmatch(r"\(type (?:(\$\S+) )?\(;(\d+);\)\s*\(func\b", wat)
        _, params, results = parse_sig_groups(wat, m.offset + length(m.match))
        sig = (params, results)
        types[m.captures[2]] = sig
        m.captures[1] === nothing || (types[m.captures[1]] = sig)
    end

    # Function definitions (the first occurrence of an index wins; imports print the same way).
    funcsig = Dict{String,Tuple{Vector{String},Vector{String}}}()
    byname = Dict{String,String}()
    for m in eachmatch(r"\(func (?:(\$\S+) )?\(;(\d+);\)", wat)
        idx = m.captures[2]
        m.captures[1] === nothing || (byname[m.captures[1]] = idx)
        haskey(funcsig, idx) && continue
        tref, params, results = parse_sig_groups(wat, m.offset + length(m.match))
        if tref !== nothing
            haskey(types, tref) ||
                error("function $idx references unknown type $tref; cannot decode signature")
            funcsig[idx] = types[tref]
        else
            funcsig[idx] = (params, results)
        end
    end

    exports = Dict{String,String}()
    for m in eachmatch(r"\(export \"([^\"]+)\" \(func (\$[^)\s]+|\d+)\)\)", wat)
        ref = m.captures[2]
        key = startswith(ref, "\$") ? get(byname, ref, nothing) : ref
        key === nothing && error("export $(m.captures[1]) -> $ref has no matching function definition")
        exports[m.captures[1]] = key
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
            push!(fails, "$fname: export -> func $sym but no func definition found")
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
