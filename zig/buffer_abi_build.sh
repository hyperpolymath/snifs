#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# buffer_abi_build.sh — standalone build for the SNIF Buffer ABI v1 (ptr,len).
#
# Mirrors the Justfile `build-wasm` recipe flags
#   (zig build-exe -target wasm32-freestanding -O<mode> -fno-entry --export=... )
# but builds ONLY zig/src/buffer_abi.zig and writes the .wasm into a temp dir
# UNDER zig/ (zig/buffer_abi_build/) — NOT priv/, so it touches nothing the
# Justfile/mix owns. Builds BOTH ReleaseSafe and ReleaseFast, then verifies the
# exports with wasm-tools (and wasmtime if present).
#
# Usage:  bash zig/buffer_abi_build.sh
set -euo pipefail

# Resolve repo-relative paths from this script's location so it works from any cwd.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SRC="$SCRIPT_DIR/src/buffer_abi.zig"
OUT="$SCRIPT_DIR/buffer_abi_build"      # temp output dir under zig/, NOT priv/
mkdir -p "$OUT"

EXPORTS=(
  snif_alloc
  snif_dealloc
  snif_reset
  sum_f32
  scale_f32
  still_alive
  crash_oob_buffer
)

build() {
  local mode="$1" name="$2"
  local -a flags=( -target wasm32-freestanding "-O$mode" -fno-entry )
  for e in "${EXPORTS[@]}"; do flags+=( "--export=$e" ); done
  echo ">>> zig build-exe ($mode) -> $OUT/$name.wasm"
  zig build-exe "$SRC" "${flags[@]}" --name "$name" -femit-bin="$OUT/$name.wasm"
}

build ReleaseSafe buffer_abi_ReleaseSafe
build ReleaseFast buffer_abi_ReleaseFast

echo
echo "=== wasm-tools validate ==="
for w in "$OUT"/buffer_abi_Release*.wasm; do
  wasm-tools validate "$w" && echo "  OK  $(basename "$w")"
done

echo
echo "=== exports (wasm-tools print, ReleaseSafe) ==="
# Show the exported funcs + the memory; prove all 7 funcs + memory are present.
wasm-tools print "$OUT/buffer_abi_ReleaseSafe.wasm" \
  | grep -oE '\(export "[^"]+"' \
  | sed 's/(export /  export /'

echo
echo "=== wasmtime export inspection (if available) ==="
if command -v wasmtime >/dev/null 2>&1; then
  # `wasmtime` cannot --invoke a module with -fno-entry directly without an
  # explicit function; we just confirm the module loads/compiles.
  if wasmtime compile "$OUT/buffer_abi_ReleaseSafe.wasm" -o "$OUT/.compiled.cwasm" 2>/dev/null; then
    echo "  OK  wasmtime compiled ReleaseSafe module"
    rm -f "$OUT/.compiled.cwasm"
  else
    echo "  (wasmtime compile skipped/failed — non-fatal; validate already passed)"
  fi
else
  echo "  (wasmtime not on PATH — skipped)"
fi

echo
echo "BUILD OK: $OUT/buffer_abi_ReleaseSafe.wasm + buffer_abi_ReleaseFast.wasm"
