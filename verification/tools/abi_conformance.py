#!/usr/bin/env python3
# SPDX-License-Identifier: MPL-2.0
# Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# abi_conformance.py — gap-1 (interface) drift gate, MULTI-GUEST.
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
#   python3 verification/tools/abi_conformance.py            # check ALL guests in the manifest
#   python3 verification/tools/abi_conformance.py PATH.wasm  # check one wasm (matched to a guest,
#                                                            # else against the safe_nif model)
# Exit 0 = every checked artifact conforms to its verified ABI model; non-zero = drift.

import os
import re
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
IDRIS = os.path.join(REPO, "verification", "proofs", "idris2", "ABI")

# Model value type -> WASM value type.
TYMAP = {"I32": "i32", "I64": "i64", "F32": "f32", "F64": "f64"}

# The guest manifest: name -> built artifact, Idris model source, constructor, return format.
#   fmt "single": MkWasmFuncSpec "name" [params] Ret      (one result word; safe_nif)
#   fmt "multi" : MkWasmSig      "name" [params] [results] ([] = void; buffer_abi)
GUESTS = [
    {
        "name": "safe_nif",
        "wasm": os.path.join(REPO, "priv", "safe_nif_ReleaseSafe.wasm"),
        "model": os.path.join(IDRIS, "Foreign.idr"),
        "ctor": "MkWasmFuncSpec",
        "fmt": "single",
    },
    {
        "name": "buffer_abi",
        "wasm": os.path.join(REPO, "zig", "buffer_abi_build", "buffer_abi_ReleaseSafe.wasm"),
        "model": os.path.join(IDRIS, "BufferAbi.idr"),
        "ctor": "MkWasmSig",
        "fmt": "multi",
    },
]


def parse_model(path, ctor, fmt):
    """Idris spec bindings -> {name: (params:list, results:list)}.

    `single`: `<ctor> "name" [T,..] Ret`        -> results = [Ret]
    `multi` : `<ctor> "name" [T,..] [R,..]`      -> results = [R,..]   ([] = void)
    """
    if fmt == "single":
        spec = re.compile(rf'{ctor}\s+"([^"]+)"\s+\[([^\]]*)\]\s+(\w+)')
    else:
        spec = re.compile(rf'{ctor}\s+"([^"]+)"\s+\[([^\]]*)\]\s+\[([^\]]*)\]')
    model = {}
    with open(path) as fh:
        for line in fh:
            if "constructor" in line:  # skip the record's constructor declaration line
                continue
            m = spec.search(line)
            if not m:
                continue
            name = m.group(1)
            params = [TYMAP[p.strip()] for p in m.group(2).split(",") if p.strip()]
            if fmt == "single":
                results = [TYMAP[m.group(3).strip()]]
            else:
                results = [TYMAP[r.strip()] for r in m.group(3).split(",") if r.strip()]
            model[name] = (params, results)
    return model


def parse_wasm(path):
    """Built .wasm -> ({export_name: func_symbol}, {func_symbol: (params, results)})."""
    wat = subprocess.run(["wasm-tools", "print", path], capture_output=True, text=True, check=True).stdout
    exports = dict(re.findall(r'\(export "([^"]+)" \(func \$([^\)\s]+)\)\)', wat))
    funcsig = {}
    fdef = re.compile(
        r'\(func \$(\S+) \(;\d+;\)(?: \(type \d+\))?(?: \(param ([^\)]*)\))?(?: \(result ([^\)]*)\))?')
    for m in fdef.finditer(wat):
        sym = m.group(1)
        params = m.group(2).split() if m.group(2) else []
        results = m.group(3).split() if m.group(3) else []
        funcsig.setdefault(sym, (params, results))  # first (the real def) wins
    return exports, funcsig


def check_guest(name, wasm, model_path, ctor, fmt):
    """Check one guest's built artifact against its verified model. Returns (ok, n_specs)."""
    if not os.path.exists(wasm):
        print(f"FATAL [{name}]: wasm not built: {os.path.relpath(wasm, REPO)}  "
              f"(run `just build-wasm` / `bash zig/buffer_abi_build.sh`)", file=sys.stderr)
        return False, 0
    if not os.path.exists(model_path):
        print(f"FATAL [{name}]: model not found: {model_path}", file=sys.stderr)
        return False, 0
    model = parse_model(model_path, ctor, fmt)
    if not model:
        print(f"FATAL [{name}]: no specs parsed from {os.path.relpath(model_path, REPO)}", file=sys.stderr)
        return False, 0
    exports, funcsig = parse_wasm(wasm)

    print(f"== ABI conformance [{name}]: {os.path.relpath(wasm, REPO)} vs "
          f"{os.path.basename(model_path)} ({len(model)} specs) ==")
    fails = []
    for fname, (eparams, eresults) in sorted(model.items()):
        sym = exports.get(fname)
        if sym is None:
            fails.append(f"{fname}: in the verified model but NOT exported by the .wasm")
            continue
        aparams, aresults = funcsig.get(sym, (None, None))
        if aparams is None:
            fails.append(f"{fname}: export -> ${sym} but no func definition found")
            continue
        if aparams != eparams:
            fails.append(f"{fname}: PARAM drift — model {eparams} vs wasm {aparams}")
        elif aresults != eresults:
            fails.append(f"{fname}: RESULT drift — model {eresults} vs wasm {aresults}")
        else:
            ret = " ".join(eresults) if eresults else "()"
            print(f"  ok   {fname}: ({' '.join(eparams)}) -> {ret}")

    modelled = set(model)
    extra = sorted(n for n in exports if n not in modelled and n != "memory")
    for n in extra:
        print(f"  warn {n}: exported by the .wasm but NOT in the verified ABI model")

    if fails:
        print(f"\nDRIFT [{name}] — the built artifact does not match the verified ABI model:",
              file=sys.stderr)
        for f in fails:
            print(f"  FAIL {f}", file=sys.stderr)
        print(f"{len(fails)} conformance failure(s) for {name}\n", file=sys.stderr)
        return False, len(model)
    print(f"PASS [{name}]: all {len(model)} verified ABI specs conform" +
          (f" ({len(extra)} un-modelled export(s) warned)" if extra else "") + "\n")
    return True, len(model)


def main():
    if not subprocess_ok():
        return 2

    # One explicit wasm path: check it against its matching guest, else the safe_nif model.
    if len(sys.argv) > 1:
        target = os.path.abspath(sys.argv[1])
        for g in GUESTS:
            if os.path.abspath(g["wasm"]) == target:
                ok, _ = check_guest(g["name"], target, g["model"], g["ctor"], g["fmt"])
                return 0 if ok else 1
        # Unrecognised path: keep the old behaviour (check against the safe_nif model).
        sn = GUESTS[0]
        ok, _ = check_guest(sn["name"], target, sn["model"], sn["ctor"], sn["fmt"])
        return 0 if ok else 1

    # No arg: check every guest in the manifest.
    all_ok, total = True, 0
    for g in GUESTS:
        ok, n = check_guest(g["name"], g["wasm"], g["model"], g["ctor"], g["fmt"])
        all_ok = all_ok and ok
        total += n
    if all_ok:
        print(f"PASS: all {len(GUESTS)} guest(s) conform ({total} ABI specs verified against built artifacts)")
        return 0
    print("FAIL: at least one guest drifted from its verified ABI model", file=sys.stderr)
    return 1


def subprocess_ok():
    """wasm-tools must be present; the gate runs, never silently skips."""
    from shutil import which
    if which("wasm-tools") is None:
        print("FATAL: wasm-tools not installed — the conformance gate must run, never skip",
              file=sys.stderr)
        return False
    return True


if __name__ == "__main__":
    sys.exit(main())
