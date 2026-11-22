#!/usr/bin/env bun
// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// abi_conformance.js — gap-1 (interface) drift gate, MULTI-GUEST.
//
// The Idris2 proofs verify a MODEL of each guest's ABI (ABI.Foreign for safe_nif,
// ABI.BufferAbi for the buffer guest). They do NOT, by themselves, establish that the
// model mirrors the ACTUAL built artifact. This checker closes that interface-level gap
// mechanically: for each guest it parses the authoritative model from its Idris source
// and the REAL exports + signatures from the built .wasm, and FAILS if they drift. So a
// change to a Zig source (or to a proof) that desynchronises the proven ABI from the
// shipped binary breaks CI instead of passing silently.
//
// Scope honesty: this checks the INTERFACE (export names, param types, result types) —
// i.e. that the real binary's signatures are exactly the verified model's signatures.
// It does NOT prove the code's BEHAVIOUR matches the model (that sum_f32 truly sums);
// that is the metamorphic/behaviour gate (GAP-1b) and, long-term, extraction. This is the
// buildable front edge of model<->code faithfulness.
//
// GUESTS (the manifest below): safe_nif (ABI.Foreign, single-return WasmFuncSpec) and
// buffer_abi (ABI.BufferAbi, multi-value/void-faithful WasmSig). burble_fft is intentionally
// NOT here: it is not built into any artifact dir and its fft/ifft use (ptr,len) slice
// marshalling, which is the ABI-6 array obligation — see PROOF-STATUS (ABI-7 ledger).
//
// Usage:
//   bun verification/tools/abi_conformance.js            # check ALL guests in the manifest
//   bun verification/tools/abi_conformance.js PATH.wasm  # check one wasm (matched to a guest,
//                                                        # else against the safe_nif model)
// Exit 0 = every checked artifact conforms to its verified ABI model; non-zero = drift.
//
// Bun port of the former verification/tools/abi_conformance.py (Python is banned
// estate-wide); checks, output text and exit codes are unchanged.

import { existsSync, readFileSync } from "node:fs";
import { spawnSync } from "node:child_process";
import path from "node:path";

const REPO = path.resolve(import.meta.dir, "..", "..");
const IDRIS = path.join(REPO, "verification", "proofs", "idris2", "ABI");

// Model value type -> WASM value type.
const TYMAP = { I32: "i32", I64: "i64", F32: "f32", F64: "f64" };
const ty = (t) => {
  if (!Object.hasOwn(TYMAP, t)) throw new Error(`unknown model value type: ${t}`);
  return TYMAP[t];
};
const words = (s) => s.split(/\s+/).filter(Boolean);
const csv = (s) => s.split(",").map((p) => p.trim()).filter(Boolean);
const pyl = (a) => `[${a.map((x) => `'${x}'`).join(", ")}]`; // Python list repr
const same = (a, b) => a.length === b.length && a.every((v, i) => v === b[i]);

// The guest manifest: name -> built artifact, Idris model source, constructor, return format.
//   fmt "single": MkWasmFuncSpec "name" [params] Ret      (one result word; safe_nif)
//   fmt "multi" : MkWasmSig      "name" [params] [results] ([] = void; buffer_abi)
const GUESTS = [
  {
    name: "safe_nif",
    wasm: path.join(REPO, "priv", "safe_nif_ReleaseSafe.wasm"),
    model: path.join(IDRIS, "Foreign.idr"),
    ctor: "MkWasmFuncSpec",
    fmt: "single",
  },
  {
    name: "buffer_abi",
    wasm: path.join(REPO, "zig", "buffer_abi_build", "buffer_abi_ReleaseSafe.wasm"),
    model: path.join(IDRIS, "BufferAbi.idr"),
    ctor: "MkWasmSig",
    fmt: "multi",
  },
];

const out = (s) => process.stdout.write(s + "\n");
const err = (s) => process.stderr.write(s + "\n");

/** Idris spec bindings -> Map(name -> [params, results]).
 *
 * `single`: `<ctor> "name" [T,..] Ret`        -> results = [Ret]
 * `multi` : `<ctor> "name" [T,..] [R,..]`      -> results = [R,..]   ([] = void)
 */
function parseModel(file, ctor, fmt) {
  const spec = fmt === "single"
    ? new RegExp(`${ctor}\\s+"([^"]+)"\\s+\\[([^\\]]*)\\]\\s+(\\w+)`)
    : new RegExp(`${ctor}\\s+"([^"]+)"\\s+\\[([^\\]]*)\\]\\s+\\[([^\\]]*)\\]`);
  const model = new Map();
  for (const line of readFileSync(file, "utf8").split("\n")) {
    if (line.includes("constructor")) continue; // skip the record's constructor declaration line
    const m = spec.exec(line);
    if (!m) continue;
    const params = csv(m[2]).map(ty);
    const results = fmt === "single" ? [ty(m[3].trim())] : csv(m[3]).map(ty);
    model.set(m[1], [params, results]);
  }
  return model;
}

/** Built .wasm -> [Map(export_name -> func_symbol), Map(func_symbol -> [params, results])]. */
function parseWasm(file) {
  const r = spawnSync("wasm-tools", ["print", file], { encoding: "utf8", maxBuffer: 1 << 30 });
  if (r.error || r.status !== 0) {
    throw new Error(`wasm-tools print failed: ${r.error ?? r.stderr}`);
  }
  const wat = r.stdout;
  const exports = new Map();
  for (const m of wat.matchAll(/\(export "([^"]+)" \(func \$([^)\s]+)\)\)/g)) exports.set(m[1], m[2]);
  const funcsig = new Map();
  const fdef = /\(func \$(\S+) \(;\d+;\)(?: \(type \d+\))?(?: \(param ([^)]*)\))?(?: \(result ([^)]*)\))?/g;
  for (const m of wat.matchAll(fdef)) {
    if (!funcsig.has(m[1])) { // first (the real def) wins
      funcsig.set(m[1], [m[2] ? words(m[2]) : [], m[3] ? words(m[3]) : []]);
    }
  }
  return [exports, funcsig];
}

/** Check one guest's built artifact against its verified model. Returns [ok, nSpecs]. */
function checkGuest(name, wasm, modelPath, ctor, fmt) {
  if (!existsSync(wasm)) {
    err(`FATAL [${name}]: wasm not built: ${path.relative(REPO, wasm)}  ` +
        "(run `just build-wasm` / `bash zig/buffer_abi_build.sh`)");
    return [false, 0];
  }
  if (!existsSync(modelPath)) {
    err(`FATAL [${name}]: model not found: ${modelPath}`);
    return [false, 0];
  }
  const model = parseModel(modelPath, ctor, fmt);
  if (model.size === 0) {
    err(`FATAL [${name}]: no specs parsed from ${path.relative(REPO, modelPath)}`);
    return [false, 0];
  }
  const [exports, funcsig] = parseWasm(wasm);

  out(`== ABI conformance [${name}]: ${path.relative(REPO, wasm)} vs ` +
      `${path.basename(modelPath)} (${model.size} specs) ==`);
  const fails = [];
  for (const fname of [...model.keys()].sort()) {
    const [eparams, eresults] = model.get(fname);
    const sym = exports.get(fname);
    if (sym === undefined) {
      fails.push(`${fname}: in the verified model but NOT exported by the .wasm`);
      continue;
    }
    const sig = funcsig.get(sym);
    if (sig === undefined) {
      fails.push(`${fname}: export -> $${sym} but no func definition found`);
      continue;
    }
    const [aparams, aresults] = sig;
    if (!same(aparams, eparams)) {
      fails.push(`${fname}: PARAM drift — model ${pyl(eparams)} vs wasm ${pyl(aparams)}`);
    } else if (!same(aresults, eresults)) {
      fails.push(`${fname}: RESULT drift — model ${pyl(eresults)} vs wasm ${pyl(aresults)}`);
    } else {
      const ret = eresults.length ? eresults.join(" ") : "()";
      out(`  ok   ${fname}: (${eparams.join(" ")}) -> ${ret}`);
    }
  }

  const extra = [...exports.keys()].filter((n) => !model.has(n) && n !== "memory").sort();
  for (const n of extra) out(`  warn ${n}: exported by the .wasm but NOT in the verified ABI model`);

  if (fails.length) {
    err(`\nDRIFT [${name}] — the built artifact does not match the verified ABI model:`);
    for (const f of fails) err(`  FAIL ${f}`);
    err(`${fails.length} conformance failure(s) for ${name}\n`);
    return [false, model.size];
  }
  out(`PASS [${name}]: all ${model.size} verified ABI specs conform` +
      (extra.length ? ` (${extra.length} un-modelled export(s) warned)` : "") + "\n");
  return [true, model.size];
}

/** wasm-tools must be present; the gate runs, never silently skips. */
function toolOk() {
  if (Bun.which("wasm-tools") === null) {
    err("FATAL: wasm-tools not installed — the conformance gate must run, never skip");
    return false;
  }
  return true;
}

function main() {
  if (!toolOk()) return 2;

  // One explicit wasm path: check it against its matching guest, else the safe_nif model.
  if (process.argv.length > 2) {
    const target = path.resolve(process.argv[2]);
    const g = GUESTS.find((x) => path.resolve(x.wasm) === target) ?? GUESTS[0];
    const [ok] = checkGuest(g.name, target, g.model, g.ctor, g.fmt);
    return ok ? 0 : 1;
  }

  // No arg: check every guest in the manifest.
  let allOk = true, total = 0;
  for (const g of GUESTS) {
    const [ok, n] = checkGuest(g.name, g.wasm, g.model, g.ctor, g.fmt);
    allOk = allOk && ok;
    total += n;
  }
  if (allOk) {
    out(`PASS: all ${GUESTS.length} guest(s) conform (${total} ABI specs verified against built artifacts)`);
    return 0;
  }
  err("FAIL: at least one guest drifted from its verified ABI model");
  return 1;
}

process.exit(main());
