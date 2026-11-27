#!/usr/bin/env julia
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# assert_safer.jl — the DISCRIMINATING assertions over snif_eval.sh output.
#
# The point of the SNIF evaluation is NOT that "everything passes". A trivially
# passing harness (e.g. one that only ran ReleaseSafe) would prove nothing. The
# "Safer" claim is substantiated ONLY if the SAME crash mode behaves DIFFERENTLY
# between ReleaseSafe and ReleaseFast: Safe must TRAP (catchable isolation) where
# Fast SILENTLY CORRUPTS (exit 0 with a wrong value). This script asserts that
# discrimination and FAILS LOUD if a mode collapses to "both pass" — which would
# mean the anti-property (silent corruption) was not actually exercised.
#
# Usage:  benches/snif_eval.sh | julia benches/assert_safer.jl
# Exit 0 = all discriminating assertions hold; non-zero = a property failed.
#
# Julia port of the former benches/assert_safer.py (Python is banned estate-wide);
# the assertions and their order are unchanged. Tooling only: this script is not
# an FFI or an ABI layer (FFIs stay pure Zig, ABIs stay pure Idris2).

# --- minimal JSON reader/writer (Julia's stdlib has no JSON) -----------------
# Objects are kept as ordered Vector{Pair{String,Any}} so output keeps key order.
const JObj = Vector{Pair{String,Any}}

function json_parse(s::AbstractString)
    i = firstindex(s)
    n = lastindex(s)
    skip() = (while i <= n && isspace(s[i]); i = nextind(s, i); end)
    function value()
        skip()
        i > n && error("unexpected end of JSON")
        c = s[i]
        if c == '{'
            i = nextind(s, i); obj = JObj(); skip()
            if s[i] == '}'; i = nextind(s, i); return obj; end
            while true
                skip(); k = str(); skip()
                s[i] == ':' || error("expected ':' in JSON object")
                i = nextind(s, i)
                push!(obj, k => value()); skip()
                if s[i] == ','; i = nextind(s, i)
                elseif s[i] == '}'; i = nextind(s, i); return obj
                else error("bad JSON object"); end
            end
        elseif c == '['
            i = nextind(s, i); arr = Any[]; skip()
            if s[i] == ']'; i = nextind(s, i); return arr; end
            while true
                push!(arr, value()); skip()
                if s[i] == ','; i = nextind(s, i)
                elseif s[i] == ']'; i = nextind(s, i); return arr
                else error("bad JSON array"); end
            end
        elseif c == '"'
            return str()
        elseif startswith(SubString(s, i), "true");  i += 4; return true
        elseif startswith(SubString(s, i), "false"); i += 5; return false
        elseif startswith(SubString(s, i), "null");  i += 4; return nothing
        else
            j = i
            while j <= n && (isdigit(s[j]) || s[j] in "+-.eE"); j = nextind(s, j); end
            j == i && error("bad JSON value at byte $i")
            t = SubString(s, i, prevind(s, j)); i = j
            return all(isdigit, lstrip(t, '-')) ? parse(Int, t) : parse(Float64, t)
        end
    end
    function str()
        s[i] == '"' || error("expected string")
        i = nextind(s, i); io = IOBuffer()
        while s[i] != '"'
            if s[i] == '\\'
                i = nextind(s, i); e = s[i]
                if e == 'u'
                    print(io, Char(parse(UInt16, SubString(s, i + 1, i + 4), base = 16))); i += 4
                else
                    print(io, get(Dict('n' => '\n', 't' => '\t', 'r' => '\r', 'b' => '\b', 'f' => '\f'), e, e))
                end
            else
                print(io, s[i])
            end
            i = nextind(s, i)
        end
        i = nextind(s, i)
        return String(take!(io))
    end
    v = value(); skip()
    i > n || error("trailing data after JSON value")
    return v
end

jget(o::JObj, k) = (for (a, b) in o; a == k && return b; end; nothing)

# Failure messages quote rows the way the former Python tool did (its repr),
# so old and new output stay identical.
function py_repr(x)
    x === nothing && return "None"
    x isa Bool && return x ? "True" : "False"
    x isa Number && return string(x)
    x isa AbstractString && return "'" * replace(replace(x, "\\" => "\\\\"), "'" => "\\'") * "'"
    x isa JObj && return "{" * join(("$(py_repr(k)): $(py_repr(v))" for (k, v) in x), ", ") * "}"
    return "[" * join(py_repr.(x), ", ") * "]"
end
show_(x) = py_repr(x)

# --- the assertions ----------------------------------------------------------
# Expected per-mode discrimination, derived from the verified Zig semantics:
#   silent  -> Fast must NOT trap and must return a SPECIFIC wrong value
#   always  -> both modes trap (UB is unconditional, e.g. @panic)
#   nofault -> neither traps (the runtime guard is never hit) — must NOT be
#              mis-asserted as a trap by callers (this is the stale-test trap)
const EXPECT = [
    ("crash_oob",         (cls = "silent", fast_value = "195948557")),   # 0x0BADF00D
    ("crash_overflow",    (cls = "silent", fast_value = "-2147483648")), # i32 wrap
    ("crash_div_zero",    (cls = "silent", fast_value = "0")),           # op elided
    ("crash_panic",       (cls = "always", fast_value = nothing)),       # @panic
    ("crash_unreachable", (cls = "always", fast_value = nothing)),       # OA-2(b): now traps
]

const failures = Ref(0)
err(s) = println(stderr, s)
fail(msg) = (err("ASSERT-FAIL: $msg"); failures[] += 1)
ok(msg) = err("  ok: $msg")

function main()
    data = json_parse(read(stdin, String))
    rows = data isa JObj ? jget(data, "rows") : nothing
    rows isa AbstractVector || error("input has no `rows` array")
    by_fn(fn) = (for r in rows; r isa JObj && jget(r, "fn") == fn && return r; end; nothing)
    by_kind(k) = (for r in rows; r isa JObj && jget(r, "kind") == k && return r; end; nothing)
    g(r, k) = r === nothing ? nothing : jget(r, k)

    err("== SNIF discriminating assertions ==")

    # (A) crash-mode discrimination
    for (fn, exp) in EXPECT
        r = by_fn(fn)
        if r === nothing; fail("$fn: no row produced"); continue; end
        st, ft, fo = g(r, "safe_trap"), g(r, "fast_trap"), g(r, "fast_out")
        if exp.cls == "silent"
            # The CORE anti-property: Safe traps, Fast does NOT and returns the wrong value.
            if st != "yes"; fail("$fn: ReleaseSafe MUST trap, got trap=$st")
            elseif ft != "no"; fail("$fn: ReleaseFast must NOT trap (silent corruption), got trap=$ft")
            elseif fo != exp.fast_value; fail("$fn: ReleaseFast wrong-value mismatch: expected $(exp.fast_value), got $fo")
            else ok("$fn: DISCRIMINATED — Safe traps, Fast silently returns $fo")
            end
        elseif exp.cls == "always"
            if st == "yes" && ft == "yes"; ok("$fn: both modes trap (unconditional UB)")
            else fail("$fn: expected trap in BOTH modes, got safe=$st fast=$ft")
            end
        end
    end

    # anti-trivial meta-assertion: at least one mode must have shown the silent
    # anti-property, else the eval proved nothing about ReleaseSafe's value.
    silent_seen = any(EXPECT) do (fn, exp)
        exp.cls == "silent" && g(by_fn(fn), "fast_trap") == "no"
    end
    silent_seen ? ok("anti-trivial: at least one silent-corruption case was exercised") :
                  fail("NO silent-corruption case was exercised — eval is vacuous")

    # (B) control: still_alive == 42 in both modes
    ctl = by_fn("still_alive")
    if ctl !== nothing && g(ctl, "safe_out") == "42" && g(ctl, "fast_out") == "42"
        ok("control still_alive()==42 in both modes (no false-trap)")
    else
        fail("control still_alive mismatch: $(show_(ctl))")
    end

    # (C) liveness guard: low fuel traps, high fuel completes
    lv = by_kind("liveness")
    hf = g(lv, "high_fuel_out")
    if lv !== nothing && g(lv, "low_fuel_trap") == "yes" && hf !== nothing && hf != "" && hf != 0 && hf != false
        ok("liveness: fuel guard traps a heavy guest at low fuel; completes at high fuel ($hf)")
    else
        fail("liveness guard not demonstrated: $(show_(lv))")
    end

    # (D) Rust guest parity: buffer ABI present + scalar traps match Zig
    rp = by_kind("rust_parity")
    if rp === nothing
        fail("no rust_parity row")
    elseif (sk = g(rp, "skipped")) !== nothing && sk != "" && sk != false
        ok("rust_parity skipped ($sk) — portable degrade, not a failure")
    else
        g(rp, "buffer_abi_exports") == "yes" ?
            ok("Rust guest exports the (ptr,len) buffer ABI the Zig slice-ABI cannot") :
            fail("Rust guest missing buffer-ABI exports")
        g(rp, "crash_overflow_trap") == "yes" && g(rp, "crash_panic_trap") == "yes" ?
            ok("Rust scalar traps match Zig (crash_overflow, crash_panic both trap)") :
            fail("Rust scalar-trap parity broken: $(show_(rp))")
        g(rp, "fibonacci10") == "55" ? ok("Rust fibonacci(10)==55 (functional parity)") :
                                       fail("Rust fibonacci parity broken: $(g(rp, "fibonacci10"))")
    end

    # (E) buffer-case crash isolation: an over-range (ptr,len) read MUST trap
    bi = by_kind("buffer_isolation")
    if bi === nothing
        fail("no buffer_isolation row")
    elseif (sk = g(bi, "skipped")) !== nothing && sk != "" && sk != false
        ok("buffer_isolation skipped ($sk) — portable degrade, not a failure")
    elseif g(bi, "trap") == "yes"
        ok("buffer case: over-range read traps (wasm memory bounds) — isolation holds for buffer NIFs")
    else
        fail("buffer over-read did NOT trap: $(show_(bi))")
    end

    err("\n$(failures[]) assertion failure(s)")
    return failures[] > 0 ? 1 : 0
end

exit(main())
