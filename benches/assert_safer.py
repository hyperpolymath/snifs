#!/usr/bin/env python3
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# assert_safer.py — the DISCRIMINATING assertions over snif_eval.sh output.
#
# The point of the SNIF evaluation is NOT that "everything passes". A trivially
# passing harness (e.g. one that only ran ReleaseSafe) would prove nothing. The
# "Safer" claim is substantiated ONLY if the SAME crash mode behaves DIFFERENTLY
# between ReleaseSafe and ReleaseFast: Safe must TRAP (catchable isolation) where
# Fast SILENTLY CORRUPTS (exit 0 with a wrong value). This script asserts that
# discrimination and FAILS LOUD if a mode collapses to "both pass" — which would
# mean the anti-property (silent corruption) was not actually exercised.
#
# Usage:  benches/snif_eval.sh | benches/assert_safer.py
# Exit 0 = all discriminating assertions hold; non-zero = a property failed.
import json
import sys

# Expected per-mode discrimination, derived from the verified Zig semantics:
#   silent  -> Fast must NOT trap and must return a SPECIFIC wrong value
#   always  -> both modes trap (UB is unconditional, e.g. @panic)
#   nofault -> neither traps (the runtime guard is never hit) — must NOT be
#              mis-asserted as a trap by callers (this is the stale-test trap)
EXPECT = {
    "crash_oob":        {"class": "silent",  "fast_value": "195948557"},   # 0x0BADF00D
    "crash_overflow":   {"class": "silent",  "fast_value": "-2147483648"}, # i32 wrap
    "crash_div_zero":   {"class": "silent",  "fast_value": "0"},           # op elided
    "crash_panic":      {"class": "always"},                                # @panic
    "crash_unreachable":{"class": "always"},                                # OA-2(b): now traps
}

def fail(msg):
    print(f"ASSERT-FAIL: {msg}", file=sys.stderr)
    fail.count += 1
fail.count = 0

def ok(msg):
    print(f"  ok: {msg}", file=sys.stderr)

data = json.load(sys.stdin)
rows = {r.get("fn", r.get("kind")): r for r in data["rows"]}

print("== SNIF discriminating assertions ==", file=sys.stderr)

# (A) crash-mode discrimination
for fn, exp in EXPECT.items():
    r = next((x for x in data["rows"] if x.get("fn") == fn), None)
    if r is None:
        fail(f"{fn}: no row produced")
        continue
    st, ft = r["safe_trap"], r["fast_trap"]
    so, fo = r.get("safe_out"), r.get("fast_out")
    cls = exp["class"]
    if cls == "silent":
        # The CORE anti-property: Safe traps, Fast does NOT and returns the wrong value.
        if st != "yes":
            fail(f"{fn}: ReleaseSafe MUST trap, got trap={st}")
        elif ft != "no":
            fail(f"{fn}: ReleaseFast must NOT trap (silent corruption), got trap={ft}")
        elif fo != exp["fast_value"]:
            fail(f"{fn}: ReleaseFast wrong-value mismatch: expected {exp['fast_value']}, got {fo}")
        else:
            ok(f"{fn}: DISCRIMINATED — Safe traps, Fast silently returns {fo}")
    elif cls == "always":
        if st == "yes" and ft == "yes":
            ok(f"{fn}: both modes trap (unconditional UB)")
        else:
            fail(f"{fn}: expected trap in BOTH modes, got safe={st} fast={ft}")
    elif cls == "nofault":
        if st == "no" and ft == "no":
            ok(f"{fn}: neither traps (guard never hit) — callers must NOT assert a trap here")
        else:
            fail(f"{fn}: expected NO trap in either mode, got safe={st} fast={ft}")

# anti-trivial meta-assertion: at least one mode must have shown the silent
# anti-property, else the eval proved nothing about ReleaseSafe's value.
silent_seen = any(
    (next((x for x in data["rows"] if x.get("fn") == fn), {}) or {}).get("fast_trap") == "no"
    and EXPECT[fn]["class"] == "silent"
    for fn in EXPECT
)
if silent_seen:
    ok("anti-trivial: at least one silent-corruption case was exercised")
else:
    fail("NO silent-corruption case was exercised — eval is vacuous")

# (B) control: still_alive == 42 in both modes
ctl = next((x for x in data["rows"] if x.get("fn") == "still_alive"), None)
if ctl and ctl.get("safe_out") == "42" and ctl.get("fast_out") == "42":
    ok("control still_alive()==42 in both modes (no false-trap)")
else:
    fail(f"control still_alive mismatch: {ctl}")

# (C) liveness guard: low fuel traps, high fuel completes
lv = next((x for x in data["rows"] if x.get("kind") == "liveness"), None)
if lv and lv.get("low_fuel_trap") == "yes" and lv.get("high_fuel_out"):
    ok(f"liveness: fuel guard traps a heavy guest at low fuel; completes at high fuel ({lv['high_fuel_out']})")
else:
    fail(f"liveness guard not demonstrated: {lv}")

# (D) Rust guest parity: buffer ABI present + scalar traps match Zig
rp = next((x for x in data["rows"] if x.get("kind") == "rust_parity"), None)
if rp is None:
    fail("no rust_parity row")
elif rp.get("skipped"):
    ok(f"rust_parity skipped ({rp['skipped']}) — portable degrade, not a failure")
else:
    if rp.get("buffer_abi_exports") == "yes":
        ok("Rust guest exports the (ptr,len) buffer ABI the Zig slice-ABI cannot")
    else:
        fail("Rust guest missing buffer-ABI exports")
    if rp.get("crash_overflow_trap") == "yes" and rp.get("crash_panic_trap") == "yes":
        ok("Rust scalar traps match Zig (crash_overflow, crash_panic both trap)")
    else:
        fail(f"Rust scalar-trap parity broken: {rp}")
    if rp.get("fibonacci10") == "55":
        ok("Rust fibonacci(10)==55 (functional parity)")
    else:
        fail(f"Rust fibonacci parity broken: {rp.get('fibonacci10')}")

# (E) buffer-case crash isolation: an over-range (ptr,len) read MUST trap
bi = next((x for x in data["rows"] if x.get("kind") == "buffer_isolation"), None)
if bi is None:
    fail("no buffer_isolation row")
elif bi.get("skipped"):
    ok(f"buffer_isolation skipped ({bi['skipped']}) — portable degrade, not a failure")
elif bi.get("trap") == "yes":
    ok("buffer case: over-range read traps (wasm memory bounds) — isolation holds for buffer NIFs")
else:
    fail(f"buffer over-read did NOT trap: {bi}")

print(f"\n{fail.count} assertion failure(s)", file=sys.stderr)
sys.exit(1 if fail.count else 0)
