#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# Build the Rust SNIF guest to wasm32-unknown-unknown with the SNIF safety
# invariant (overflow-checks + panic=abort, set in the workspace [profile.release]).
# Mirrors zig/build.zig's role for the Zig guest.
#
# VERIFIED working under: rustc 1.95.0, wasm-tools 1.249, wasmtime 44.
set -euo pipefail
cd "$(dirname "$0")"

TARGET="wasm32-unknown-unknown"   # ADR: no WASI (freestanding-equivalent, ADR-002)
rustup target add "$TARGET" >/dev/null 2>&1 || true

echo ">> build"
cargo build --release --target "$TARGET"

WASM="target/${TARGET}/release/demo_guest.wasm"

echo ">> validate"
wasm-tools validate "$WASM"

echo ">> assert NO WASI/host imports (sandbox must be self-contained)"
if wasm-tools print "$WASM" | grep -q '(import'; then
  echo "FAIL: guest has imports — not self-contained" >&2
  wasm-tools print "$WASM" | grep '(import' >&2
  exit 1
fi
echo "   ok: zero imports"

echo ">> exports"
wasm-tools print "$WASM" | grep -oE '\(export "[^"]+"' | sort

# install into priv/ alongside the Zig artifacts so the demo can load it
mkdir -p ../priv
cp "$WASM" ../priv/demo_guest_rust.wasm
echo ">> installed ../priv/demo_guest_rust.wasm ($(wc -c < "$WASM") bytes)"
