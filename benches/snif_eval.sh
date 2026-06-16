#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# snif_eval.sh — self-contained, language-agnostic SNIF EVALUATION harness.
#
# Substantiates the "Safer" claim WITHOUT the BEAM, using the wasmtime 44 CLI as
# the host. This is the part of the methodology that RUNS in the constrained env
# (OTP 25): wasmtime is the same wasmtime that wasmex 0.14 embeds, so the
# trap-vs-silent-return discrimination measured here is the SAME mechanism the
# BEAM relies on for crash isolation.
#
# This harness is SELF-BUILDING: it compiles zig/src/safe_nif.zig to
# wasm32-freestanding in BOTH -OReleaseSafe and -OReleaseFast into a temp dir
# under benches/ (NOT priv/ — it does not touch the deployable artifacts), then
# drives every crash mode + control through wasmtime and prints a results table.
# It depends on NOTHING pre-built: just zig, wasmtime, wasm-tools on PATH.
#
# ── The load-bearing methodological point ────────────────────────────────────
# "Safer" is substantiated by DISCRIMINATION between ReleaseSafe and ReleaseFast
# on the SAME crash mode, NOT by everything passing. ReleaseSafe must TRAP where
# ReleaseFast SILENTLY CORRUPTS. A harness in which every row "passes" would be
# worthless; the silent-corruption anti-property MUST be exercised and observed.
#
# ── GROUND-TRUTH primitives (all verified against zig 0.15.2 + wasmtime 44.0.1)
#   trap        -> stderr contains "wasm trap", process exit 134, NO stdout value
#   silent-bug  -> exit 0, a stdout value that is WRONG (the anti-property)
#   fuel guard  -> wasmtime run -W fuel=N   => "all fuel consumed" trap
#
# ── Outputs ──────────────────────────────────────────────────────────────────
#   stdout : a single machine-readable JSON document (schema snif-eval/1)
#   stderr : a human-readable results table
#   files  : benches/eval_tmp/*.wasm (built artifacts), benches/eval_results.json
#
# NB: parts that need the BEAM scheduler / wasmex marshalling — process-survival
# witness (Process.alive? after a trap), buffer round-trip THROUGH wasmex, the
# Port comparison, pooled-vs-per-call overhead — are NOT produced here. They need
# OTP 28.3 / Elixir 1.19.4 and live in demo/bench/*.exs. They are flagged [OTP28]
# in the table's notes and reported as blockers, never silently claimed.
set -uo pipefail

# ── locations ─────────────────────────────────────────────────────────────────
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"
SRC="$REPO/zig/src/safe_nif.zig"
TMP="$HERE/eval_tmp"                  # built wasm goes here, NOT priv/
SAFE="$TMP/safe_nif_ReleaseSafe.wasm"
FAST="$TMP/safe_nif_ReleaseFast.wasm"
JSON_OUT="$HERE/eval_results.json"    # machine-readable result snapshot
RUNS="${RUNS:-30}"                    # hyperfine sample count for the overhead row
WARMUP="${WARMUP:-3}"

# The export surface of safe_nif.zig (must match the source's `export fn`s).
EXPORTS=(fibonacci checked_add crash_oob crash_unreachable crash_panic
         crash_overflow crash_div_zero still_alive)

# ── preflight: tools + source ────────────────────────────────────────────────
need() { command -v "$1" >/dev/null || { echo "FATAL: '$1' not on PATH" >&2; exit 2; }; }
need zig
need wasmtime
need wasm-tools
[ -f "$SRC" ] || { echo "FATAL: source not found: $SRC" >&2; exit 2; }
HAVE_HF=0; command -v hyperfine >/dev/null && HAVE_HF=1
HAVE_JQ=0; command -v jq        >/dev/null && HAVE_JQ=1

mkdir -p "$TMP"

# ── (1) BUILD: zig -> wasm32-freestanding, ReleaseSafe AND ReleaseFast ─────────
# INVARIANT (owner directive): the deployable mode is -OReleaseSafe; ReleaseFast
# is built ONLY as the negative control that demonstrates silent corruption.
build_mode() { # <Mode> <out>
  local mode="$1" out="$2" exargs=()
  local e; for e in "${EXPORTS[@]}"; do exargs+=("--export=$e"); done
  zig build-exe -fno-entry -O "$mode" -target wasm32-freestanding \
    "${exargs[@]}" -femit-bin="$out" "$SRC"
}
echo "[build] zig 0.15.x -> wasm32-freestanding (ReleaseSafe + ReleaseFast)" >&2
build_mode ReleaseSafe "$SAFE" || { echo "FATAL: ReleaseSafe build failed" >&2; exit 3; }
build_mode ReleaseFast "$FAST" || { echo "FATAL: ReleaseFast build failed" >&2; exit 3; }
wasm-tools validate "$SAFE" || { echo "FATAL: ReleaseSafe wasm invalid" >&2; exit 3; }
wasm-tools validate "$FAST" || { echo "FATAL: ReleaseFast wasm invalid" >&2; exit 3; }
ZIG_VER="$(zig version 2>/dev/null)"
WT_VER="$(wasmtime --version 2>/dev/null | awk '{print $2}')"
echo "[build] OK  Safe=$(wc -c <"$SAFE")B  Fast=$(wc -c <"$FAST")B  zig=$ZIG_VER  wasmtime=$WT_VER" >&2

# ── invoke helpers ───────────────────────────────────────────────────────────
# invoke <wasm> <fn> [args...] -> sets globals G_OUT G_RC G_TRAP
invoke() {
  local wasm="$1" fn="$2"; shift 2
  local err; err="$(mktemp)"
  G_OUT="$(wasmtime run --invoke "$fn" "$wasm" "$@" 2>"$err")"; G_RC=$?
  G_TRAP=no; grep -q 'wasm trap' "$err" && G_TRAP=yes
  rm -f "$err"
}
# invoke_fuel <wasm> <fuel> <fn> [args...] -> sets G_OUT G_RC G_FUELTRAP
invoke_fuel() {
  local wasm="$1" fuel="$2" fn="$3"; shift 3
  local err; err="$(mktemp)"
  G_OUT="$(wasmtime run -W fuel="$fuel" --invoke "$fn" "$wasm" "$@" 2>"$err")"; G_RC=$?
  G_FUELTRAP=no; grep -q 'all fuel consumed' "$err" && G_FUELTRAP=yes
  rm -f "$err"
}

# json string-or-null helper
jstr() { [ -z "${1:-}" ] && printf 'null' || printf '"%s"' "$1"; }

json_rows=()
add_row() { json_rows+=("$1"); }

# ── (2) crash-isolation × ReleaseSafe-vs-ReleaseFast ──────────────────────────
# For each crash mode, record BOTH modes. The DISCRIMINATING fact is the triple
# (safe_trap, fast_trap, fast_value): a real isolation property shows Safe traps
# where Fast silently corrupts. Expected classes (ground-truthed from the source
# semantics, encoded so the table is self-documenting):
#   silent  : Safe traps, Fast returns a SPECIFIC wrong value (the anti-property)
#   always  : both modes trap (unconditional @panic)
#   nofault : neither traps (UB guard never fires at runtime_index=3)
declare -A EXPECT=(
  [crash_oob]=silent          # Safe trap; Fast -> 195948557 (0x0BADF00D canary)
  [crash_overflow]=silent     # Safe trap; Fast -> -2147483648 (wrap)
  [crash_div_zero]=silent     # Safe trap; Fast -> 0 (op removed)
  [crash_panic]=always        # both trap (unconditional @panic)
  [crash_unreachable]=always  # OA-2(b): unconditional unreachable -> traps in BOTH modes
)
MODES=(crash_oob crash_overflow crash_div_zero crash_panic crash_unreachable)
silent_seen=0
for fn in "${MODES[@]}"; do
  invoke "$SAFE" "$fn"; safe_trap=$G_TRAP; safe_rc=$G_RC; safe_out="$G_OUT"
  invoke "$FAST" "$fn"; fast_trap=$G_TRAP; fast_rc=$G_RC; fast_out="$G_OUT"
  exp="${EXPECT[$fn]}"
  [ "$exp" = silent ] && [ "$safe_trap" = yes ] && [ "$fast_trap" = no ] && silent_seen=$((silent_seen+1))
  add_row "{\"kind\":\"crash\",\"fn\":\"$fn\",\"expect\":\"$exp\",\"safe_trap\":\"$safe_trap\",\"safe_exit\":$safe_rc,\"safe_out\":$(jstr "$safe_out"),\"fast_trap\":\"$fast_trap\",\"fast_exit\":$fast_rc,\"fast_out\":$(jstr "$fast_out")}"
done

# ANTI-TRIVIAL meta-fact: at least one silent-corruption case must have actually
# been exercised (Safe trap + Fast no-trap). If silent_seen==0 the harness has
# degenerated and proves nothing.
add_row "{\"kind\":\"meta\",\"silent_corruption_cases_observed\":$silent_seen,\"anti_trivial_ok\":$([ "$silent_seen" -ge 1 ] && echo true || echo false)}"

# ── (3) controls: correctness must hold in BOTH modes ─────────────────────────
invoke "$SAFE" still_alive;  sa_safe="$G_OUT"
invoke "$FAST" still_alive;  sa_fast="$G_OUT"
add_row "{\"kind\":\"control\",\"fn\":\"still_alive\",\"safe_out\":$(jstr "$sa_safe"),\"fast_out\":$(jstr "$sa_fast"),\"expect\":\"42\"}"

invoke "$SAFE" fibonacci 20; fib_safe="$G_OUT"
invoke "$FAST" fibonacci 20; fib_fast="$G_OUT"
add_row "{\"kind\":\"control\",\"fn\":\"fibonacci(20)\",\"safe_out\":$(jstr "$fib_safe"),\"fast_out\":$(jstr "$fib_fast"),\"expect\":\"6765\"}"

# checked_add uses wrapping (+%) by design: i32::MAX + 1 wraps in BOTH modes (NOT
# a trap) — this is intentional and documented in the source. Record it so the
# table shows the deliberate wrap rather than implying it is a discrimination row.
invoke "$SAFE" checked_add 2147483647 1; ca_safe="$G_OUT"
invoke "$FAST" checked_add 2147483647 1; ca_fast="$G_OUT"
add_row "{\"kind\":\"control\",\"fn\":\"checked_add(MAX,1)\",\"safe_out\":$(jstr "$ca_safe"),\"fast_out\":$(jstr "$ca_fast"),\"expect\":\"-2147483648 (intentional wrap, both modes)\"}"

# ── (4) liveness / DoS guard (language-agnostic) ──────────────────────────────
# Too little fuel -> deterministic "all fuel consumed" trap; enough -> result.
# This is the same mechanism Snif.Worker uses (wasmex 0.14 has no epoch API).
invoke_fuel "$SAFE" 100      fibonacci 90; low_trap=$G_FUELTRAP
invoke_fuel "$SAFE" 10000000 fibonacci 90; hi_out="$G_OUT"
add_row "{\"kind\":\"liveness\",\"guard\":\"fuel\",\"low_fuel_trap\":\"$low_trap\",\"high_fuel_out\":$(jstr "$hi_out")}"

# ── (5) overhead: wasmtime per-call cost (statistical, UPPER bound) ───────────
# wasmtime-CLI cost = process spawn + module load + instantiate + 1 call. It is
# the CLI analogue of wasmex's ADR-003 per-call instantiation and BRACKETS the
# upper bound of SNIF per-call overhead (real in-VM wasmex omits process spawn).
# The pooled / raw-NIF / Port rows are [OTP28] and produced by demo/bench.
if [ "$HAVE_HF" = 1 ]; then
  hf="$(mktemp)"
  hyperfine --warmup "$WARMUP" --runs "$RUNS" --export-json "$hf" \
    -n "wasmtime_percall_fib20" \
    "wasmtime run --invoke fibonacci $SAFE 20" >/dev/null 2>&1
  if [ "$HAVE_JQ" = 1 ]; then
    mean_ms="$(jq -r '.results[0].mean*1000'   "$hf")"
    sd_ms="$(jq   -r '.results[0].stddev*1000' "$hf")"
    min_ms="$(jq  -r '.results[0].min*1000'    "$hf")"
  else
    mean_ms="$(python3 -c "import json,sys;print(json.load(open('$hf'))['results'][0]['mean']*1000)")"
    sd_ms="$(python3  -c "import json,sys;print(json.load(open('$hf'))['results'][0]['stddev']*1000)")"
    min_ms="$(python3 -c "import json,sys;print(json.load(open('$hf'))['results'][0]['min']*1000)")"
  fi
  rm -f "$hf"
  add_row "{\"kind\":\"overhead\",\"case\":\"wasmtime_percall_fib20\",\"runs\":$RUNS,\"mean_ms\":$mean_ms,\"stddev_ms\":$sd_ms,\"min_ms\":$min_ms,\"note\":\"UPPER bound (incl. OS process spawn); pooled/raw-NIF/Port rows are [OTP28]\"}"
  OV_MEAN="$mean_ms"; OV_SD="$sd_ms"; OV_MIN="$min_ms"
else
  add_row "{\"kind\":\"overhead\",\"case\":\"wasmtime_percall_fib20\",\"error\":\"hyperfine not available\"}"
  OV_MEAN="n/a"; OV_SD=""; OV_MIN=""
fi

# ── (6) Rust→wasm32 guest parity (the verifier-on-by-default guest) ───────────
# Prefer the pre-built artifact; else run the guest's build script; else SKIP with
# an explicit row so the harness stays portable.
echo "[rust] locating/building Rust→wasm32 guest" >&2
RUST_WASM=""
if [ -f "$REPO/priv/demo_guest_rust.wasm" ]; then
  RUST_WASM="$REPO/priv/demo_guest_rust.wasm"
elif [ -x "$REPO/rust/build-wasm.sh" ]; then
  ( cd "$REPO" && bash rust/build-wasm.sh ) >/dev/null 2>&1 && RUST_WASM="$REPO/priv/demo_guest_rust.wasm"
fi
if [ -n "$RUST_WASM" ] && [ -f "$RUST_WASM" ]; then
  rexp="$(wasm-tools print "$RUST_WASM" 2>/dev/null | grep -oE '\(export "[^"]+"')"
  bufok=no
  if echo "$rexp" | grep -q 'snif_alloc' && echo "$rexp" | grep -q 'sum_f32'; then bufok=yes; fi
  invoke "$RUST_WASM" crash_overflow; rov=$G_TRAP
  invoke "$RUST_WASM" crash_panic;    rpn=$G_TRAP
  invoke "$RUST_WASM" fibonacci 10;   rfib="$G_OUT"
  add_row "{\"kind\":\"rust_parity\",\"buffer_abi_exports\":\"$bufok\",\"crash_overflow_trap\":\"$rov\",\"crash_panic_trap\":\"$rpn\",\"fibonacci10\":$(jstr "$rfib")}"
  echo "[rust] parity: buffer_abi=$bufok overflow_trap=$rov panic_trap=$rpn fib10=$rfib" >&2
else
  add_row "{\"kind\":\"rust_parity\",\"skipped\":\"rust wasm32 toolchain/artifact unavailable\"}"
  echo "[rust] SKIPPED (no wasm32 toolchain/artifact)" >&2
fi

# ── (7) Buffer-ABI crash isolation (an over-range read MUST trap) ──────────────
# Prefer the pre-built buffer ABI wasm; else run its build script; else SKIP.
echo "[buffer] locating/building Zig Buffer ABI guest" >&2
BUF=""
if [ -f "$REPO/zig/buffer_abi_build/buffer_abi_ReleaseSafe.wasm" ]; then
  BUF="$REPO/zig/buffer_abi_build/buffer_abi_ReleaseSafe.wasm"
elif [ -x "$REPO/zig/buffer_abi_build.sh" ]; then
  ( cd "$REPO" && bash zig/buffer_abi_build.sh ) >/dev/null 2>&1 && BUF="$REPO/zig/buffer_abi_build/buffer_abi_ReleaseSafe.wasm"
fi
if [ -n "$BUF" ] && [ -f "$BUF" ]; then
  # Genuine buffer-NIF isolation: a host-supplied over-range (ptr,len) makes the
  # f32 loads run past linear memory, so wasmtime's memory bound traps (this holds
  # in BOTH modes — the sandbox bound is unconditional, unlike Zig's array checks).
  invoke "$BUF" sum_f32 1000000000 4; bitrap=$G_TRAP
  add_row "{\"kind\":\"buffer_isolation\",\"trap\":\"$bitrap\",\"probe\":\"sum_f32(ptr=1e9,len=4)\"}"
  echo "[buffer] sum_f32 over-range (ptr=1e9) trap=$bitrap" >&2
else
  add_row "{\"kind\":\"buffer_isolation\",\"skipped\":\"buffer_abi.zig artifact unavailable\"}"
  echo "[buffer] SKIPPED (no buffer ABI artifact)" >&2
fi

# ── emit machine-readable JSON (stdout + snapshot file) ───────────────────────
emit_json() {
  printf '{"schema":"snif-eval/1","zig":"%s","wasmtime":"%s","source":"zig/src/safe_nif.zig","runs":%s,"rows":[' \
    "$ZIG_VER" "$WT_VER" "$RUNS"
  local i
  for i in "${!json_rows[@]}"; do
    [ "$i" -gt 0 ] && printf ','
    printf '%s' "${json_rows[$i]}"
  done
  printf ']}\n'
}
emit_json | tee "$JSON_OUT"

# ── human-readable table -> stderr (does not pollute the JSON on stdout) ──────
fmt_num() { printf "%.3f" "$1" 2>/dev/null || printf "%s" "$1"; }
{
  echo
  echo "==========================================================================================="
  echo " SNIF EVALUATION  —  language-agnostic (zig $ZIG_VER -> wasm32-freestanding, wasmtime $WT_VER)"
  echo " Self-built from zig/src/safe_nif.zig into benches/eval_tmp/ (priv/ untouched)."
  echo "==========================================================================================="
  echo
  echo " (2) CRASH ISOLATION  —  the discriminating anti-property"
  echo " -------------------------------------------------------------------------------------------"
  printf " %-18s | %-8s | %-7s | %-13s | %-7s | %-13s\n" "crash mode" "class" "Safe" "Safe out" "Fast" "Fast out"
  printf " %-18s | %-8s | %-7s | %-13s | %-7s | %-13s\n" "------------------" "--------" "trap" "------------" "trap" "------------"
  for fn in "${MODES[@]}"; do
    invoke "$SAFE" "$fn"; st=$G_TRAP; so="${G_OUT:---}"
    invoke "$FAST" "$fn"; ft=$G_TRAP; fo="${G_OUT:---}"
    printf " %-18s | %-8s | %-7s | %-13s | %-7s | %-13s\n" "$fn" "${EXPECT[$fn]}" "$st" "$so" "$ft" "$fo"
  done
  echo
  echo "   READING THE TABLE:"
  echo "     silent  = Safe TRAPS while Fast returns a SPECIFIC wrong value  <- this IS the proof"
  echo "               crash_oob:      Fast -> 195948557 (0x0BADF00D canary, OOB read)"
  echo "               crash_overflow: Fast -> -2147483648 (silent i32 wrap)"
  echo "               crash_div_zero: Fast -> 0 (div op removed by optimiser)"
  echo "     always  = both modes trap (crash_panic: @panic; crash_unreachable: unconditional"
  echo "               unreachable — OA-2(b) fixed the prior never-firing 'index==99' guard)"
  echo "     nofault = neither traps (no export is in this class after OA-2(b))"
  echo "   anti-trivial: silent-corruption cases actually observed = $silent_seen (must be >= 1)"
  echo
  echo " (3) CONTROLS  —  correctness must hold in BOTH modes"
  echo " -------------------------------------------------------------------------------------------"
  printf " %-22s | %-13s | %-13s | %s\n" "fn" "Safe" "Fast" "expect"
  printf " %-22s | %-13s | %-13s | %s\n" "still_alive"        "$sa_safe"  "$sa_fast"  "42"
  printf " %-22s | %-13s | %-13s | %s\n" "fibonacci(20)"      "$fib_safe" "$fib_fast" "6765"
  printf " %-22s | %-13s | %-13s | %s\n" "checked_add(MAX,1)" "$ca_safe"  "$ca_fast"  "-2147483648 (intentional wrap)"
  echo
  echo " (4) LIVENESS / DoS GUARD  —  fuel (the wasmex-0.14 mechanism)"
  echo " -------------------------------------------------------------------------------------------"
  printf " %-22s | %s\n" "fuel=100,  fib(90)" "trap('all fuel consumed') = $low_trap"
  printf " %-22s | %s\n" "fuel=1e7,  fib(90)" "completes -> $hi_out"
  echo
  echo " (5) OVERHEAD  —  wasmtime per-call (UPPER bound; pooled rows are [OTP28])"
  echo " -------------------------------------------------------------------------------------------"
  if [ "$HAVE_HF" = 1 ]; then
    printf " %-22s | mean=%s ms  sd=%s ms  min=%s ms  (n=%s)\n" \
      "wasmtime_percall_fib20" "$(fmt_num "$OV_MEAN")" "$(fmt_num "$OV_SD")" "$(fmt_num "$OV_MIN")" "$RUNS"
    echo "   note: includes OS process-spawn cost ABSENT from in-VM wasmex; this brackets but"
    echo "         does NOT equal the real wasmex per-call cost."
  else
    echo "   (hyperfine not available — overhead row skipped)"
  fi
  echo
  echo " [OTP28] — NOT produced here (need OTP 28.3 / Elixir 1.19.4 + wasmex 0.14):"
  echo "     - BEAM process-survival witness (Process.alive? after a guest trap)"
  echo "     - buffer round-trip THROUGH wasmex (alloc -> write linear mem -> call -> read)"
  echo "     - pooled (ADR-004) vs per-call (ADR-003) overhead, Port comparison, raw-NIF baseline"
  echo "   This env is OTP 25; those rows live in demo/bench/*.exs and run via 'just eval-otp28'."
  echo "==========================================================================================="
} >&2
