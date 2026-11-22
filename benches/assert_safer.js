#!/usr/bin/env bun
// SPDX-License-Identifier: MPL-2.0
// Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// assert_safer.js — the DISCRIMINATING assertions over snif_eval.sh output.
//
// The point of the SNIF evaluation is NOT that "everything passes". A trivially
// passing harness (e.g. one that only ran ReleaseSafe) would prove nothing. The
// "Safer" claim is substantiated ONLY if the SAME crash mode behaves DIFFERENTLY
// between ReleaseSafe and ReleaseFast: Safe must TRAP (catchable isolation) where
// Fast SILENTLY CORRUPTS (exit 0 with a wrong value). This script asserts that
// discrimination and FAILS LOUD if a mode collapses to "both pass" — which would
// mean the anti-property (silent corruption) was not actually exercised.
//
// Usage:  benches/snif_eval.sh | bun benches/assert_safer.js
// Exit 0 = all discriminating assertions hold; non-zero = a property failed.
//
// Bun port of the former benches/assert_safer.py (Python is banned estate-wide);
// the assertions and their order are unchanged.

// Expected per-mode discrimination, derived from the verified Zig semantics:
//   silent  -> Fast must NOT trap and must return a SPECIFIC wrong value
//   always  -> both modes trap (UB is unconditional, e.g. @panic)
//   nofault -> neither traps (the runtime guard is never hit) — must NOT be
//              mis-asserted as a trap by callers (this is the stale-test trap)
const EXPECT = {
  crash_oob:         { class: "silent", fast_value: "195948557" },   // 0x0BADF00D
  crash_overflow:    { class: "silent", fast_value: "-2147483648" }, // i32 wrap
  crash_div_zero:    { class: "silent", fast_value: "0" },           // op elided
  crash_panic:       { class: "always" },                            // @panic
  crash_unreachable: { class: "always" },                            // OA-2(b): now traps
};

let failures = 0;
const err = (s) => process.stderr.write(s + "\n");
const fail = (msg) => { err(`ASSERT-FAIL: ${msg}`); failures += 1; };
const ok = (msg) => err(`  ok: ${msg}`);
const show = (x) => JSON.stringify(x === undefined ? null : x);

const data = JSON.parse(await Bun.stdin.text());
const rows = data.rows;
if (!Array.isArray(rows)) throw new Error("input has no `rows` array");
const byFn = (fn) => rows.find((x) => x.fn === fn);
const byKind = (k) => rows.find((x) => x.kind === k);

err("== SNIF discriminating assertions ==");

// (A) crash-mode discrimination
for (const [fn, exp] of Object.entries(EXPECT)) {
  const r = byFn(fn);
  if (r === undefined) { fail(`${fn}: no row produced`); continue; }
  const st = r.safe_trap, ft = r.fast_trap, fo = r.fast_out;
  if (exp.class === "silent") {
    // The CORE anti-property: Safe traps, Fast does NOT and returns the wrong value.
    if (st !== "yes") fail(`${fn}: ReleaseSafe MUST trap, got trap=${st}`);
    else if (ft !== "no") fail(`${fn}: ReleaseFast must NOT trap (silent corruption), got trap=${ft}`);
    else if (fo !== exp.fast_value) fail(`${fn}: ReleaseFast wrong-value mismatch: expected ${exp.fast_value}, got ${fo}`);
    else ok(`${fn}: DISCRIMINATED — Safe traps, Fast silently returns ${fo}`);
  } else if (exp.class === "always") {
    if (st === "yes" && ft === "yes") ok(`${fn}: both modes trap (unconditional UB)`);
    else fail(`${fn}: expected trap in BOTH modes, got safe=${st} fast=${ft}`);
  } else if (exp.class === "nofault") {
    if (st === "no" && ft === "no") ok(`${fn}: neither traps (guard never hit) — callers must NOT assert a trap here`);
    else fail(`${fn}: expected NO trap in either mode, got safe=${st} fast=${ft}`);
  }
}

// anti-trivial meta-assertion: at least one mode must have shown the silent
// anti-property, else the eval proved nothing about ReleaseSafe's value.
const silentSeen = Object.keys(EXPECT).some(
  (fn) => (byFn(fn) ?? {}).fast_trap === "no" && EXPECT[fn].class === "silent",
);
if (silentSeen) ok("anti-trivial: at least one silent-corruption case was exercised");
else fail("NO silent-corruption case was exercised — eval is vacuous");

// (B) control: still_alive == 42 in both modes
const ctl = byFn("still_alive");
if (ctl && ctl.safe_out === "42" && ctl.fast_out === "42") ok("control still_alive()==42 in both modes (no false-trap)");
else fail(`control still_alive mismatch: ${show(ctl)}`);

// (C) liveness guard: low fuel traps, high fuel completes
const lv = byKind("liveness");
if (lv && lv.low_fuel_trap === "yes" && lv.high_fuel_out) {
  ok(`liveness: fuel guard traps a heavy guest at low fuel; completes at high fuel (${lv.high_fuel_out})`);
} else fail(`liveness guard not demonstrated: ${show(lv)}`);

// (D) Rust guest parity: buffer ABI present + scalar traps match Zig
const rp = byKind("rust_parity");
if (rp === undefined) fail("no rust_parity row");
else if (rp.skipped) ok(`rust_parity skipped (${rp.skipped}) — portable degrade, not a failure`);
else {
  if (rp.buffer_abi_exports === "yes") ok("Rust guest exports the (ptr,len) buffer ABI the Zig slice-ABI cannot");
  else fail("Rust guest missing buffer-ABI exports");
  if (rp.crash_overflow_trap === "yes" && rp.crash_panic_trap === "yes") ok("Rust scalar traps match Zig (crash_overflow, crash_panic both trap)");
  else fail(`Rust scalar-trap parity broken: ${show(rp)}`);
  if (rp.fibonacci10 === "55") ok("Rust fibonacci(10)==55 (functional parity)");
  else fail(`Rust fibonacci parity broken: ${rp.fibonacci10}`);
}

// (E) buffer-case crash isolation: an over-range (ptr,len) read MUST trap
const bi = byKind("buffer_isolation");
if (bi === undefined) fail("no buffer_isolation row");
else if (bi.skipped) ok(`buffer_isolation skipped (${bi.skipped}) — portable degrade, not a failure`);
else if (bi.trap === "yes") ok("buffer case: over-range read traps (wasm memory bounds) — isolation holds for buffer NIFs");
else fail(`buffer over-read did NOT trap: ${show(bi)}`);

err(`\n${failures} assertion failure(s)`);
process.exit(failures ? 1 : 0);
