<!--
SPDX-License-Identifier: MPL-2.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Proof Requirements — SNIFs (Safer NIFs)

> **Standing requirements catalogue.** This file lists the proof obligations this repo
> *commits to carrying*. For the **live status** of each (proven / tested / trusted, with
> the adversarial-audit caveats), see [`PROOF-STATUS.md`](PROOF-STATUS.md) — that is the
> authoritative tracker; this file is the more stable "what must exist and why".

## Proof Tier

<!-- T1 (Critical), T2 (High), T3 (Standard), T4 (Light), T5 (Exempt) -->
**Tier**: **T2 — High.** SNIF's entire value proposition is a *safety* claim (a guest fault
becomes `{:error,_}` and the BEAM survives), so the operational isolation theorem (SEC-1) and
the ABI boundary are load-bearing. It is not T1 only because the residual runtime-faithfulness
assumption (`wasmtime ⊨ FaithfulRuntime`) is explicitly *trusted*, not yet machine-verified —
which is exactly why the product is "Safer", not "Safe".

## Proof Categories

| Code | Meaning | Applies? |
|------|---------|----------|
| **TP** | Typing Proofs (type soundness, type safety) | **Yes** — result-type algebra, verdict model |
| **INV** | Invariant Proofs (state machines, monotonicity, bounds) | Partial — fuel/liveness bound in SEC-1 |
| **SEC** | Security Proofs (crypto, injection freedom, access control) | **Yes** — SEC-1 crash isolation + deniability |
| **CONC** | Concurrency Proofs (linearizability, deadlock freedom) | No (pool isolation is tested, not proven) |
| **ALG** | Algorithm Proofs (termination, correctness, bounds) | Partial — run termination via fuel |
| **ABI** | ABI/FFI Proofs (memory layout, pointer safety, platform compat) | **Yes** — the guest export boundary |
| **DOM** | Domain-Specific Proofs (bespoke to this project) | **Yes** — echo×epistemic verdict bridge |

## Mandatory Proofs (All RSR Repos)

ABI/FFI boundary (Idris2) and core typing — all present and CI-gated by `just proof-check-all`:

| # | Proof | Status | File |
|---|-------|--------|------|
| ABI-1 | Non-null pointer proofs (`So (ptr /= 0)`) | ✅ Gated | `verification/proofs/idris2/ABI/Pointers.idr` |
| ABI-2 | Memory layout correctness (`HasSize`, `HasAlignment`) | ✅ Gated | `verification/proofs/idris2/ABI/Layout.idr` |
| ABI-3 | Platform type size proofs | ✅ Gated | `verification/proofs/idris2/ABI/Platform.idr` |
| ABI-4 | FFI function return-type proofs (safe_nif, 8 exports) | ✅ Gated | `verification/proofs/idris2/ABI/Foreign.idr` |
| ABI-5 | C ABI compliance (`CABICompliant`, `FieldsAligned`) | ✅ Gated | `verification/proofs/idris2/ABI/Compliance.idr` |
| TP-1 | Core data-type well-formedness | ✅ Gated | `verification/proofs/idris2/Types.idr` |
| TP-2 | Public API type safety (exported functions) | ✅ Gated | `verification/proofs/lean4/ApiTypes.lean` |

## Project-Specific Proofs

| # | Proof Needed | Category | Prover | Status | File(s) |
|---|-------------|----------|--------|--------|---------|
| SEC-1 | Operational crash-isolation: guest fault ⇒ `{:error,_}` ∧ host survives, over a fuelled host↔guest run, *modulo* the explicit `FaithfulRuntime` TCB | SEC | Agda | ✅ Proven-modulo-TCB | `verification/proofs/agda/SnifIsolation.agda` |
| SEC-1-F1 | **Deniability wired into the operational run**: trap residue = redacted secret (`fault-via-observe`), two equal-redaction faults host-indistinguishable (`run-deniable`) | SEC | Agda | ✅ Done (SNIFs 2) | `SnifIsolation.agda` |
| SEC-1-F2 | **Outcome taxonomy**: `TrapOrigin` (guestFault / hostBudget / preExec) + `call` front-end covering all 6 `error_reason` origins | TP/SEC | Agda | ✅ Done (SNIFs 2) | `SnifIsolation.agda` |
| SEC-1-TCB | Discharge **`wasmtime ⊨ FaithfulRuntime`** in-prover (WASM trap-soundness; trap→`{:error,_}`; scheduler resumed) | SEC | Coq (WasmCert-Coq) | ⏳ Open (the "Safer ≠ Safe" residue) | `verification/proofs/coq/` (slot) |
| DOM-1 | Verdict bridge: crash-isolation dichotomy + non-forgery + restricted deniability (echo×epistemic, tropical-free) | DOM | Agda | ✅ Gated | `verification/proofs/agda/SnifVerdict.agda` |
| ABI-6 | Buffer/array marshalling round-trip + in-bounds (the `(ptr,len)` *semantics*, unblocks FFT-class guests) | ABI | Idris2 | ⏳ Framework only | `Compliance.WasmArray*` |
| ABI-7 | Coverage: model + gate every real guest export | ABI | Idris2 + Python | ◐ buffer_abi done (15/20 Zig sites); burble_fft + Rust guests ledgered | `verification/proofs/idris2/ABI/BufferAbi.idr`, `verification/tools/abi_conformance.py` |
| GAP-1b | Behaviour faithfulness: metamorphic relations prove kernels *behave* as modelled, not just match signatures | TP | metamorphic tests | ◐ scalar kernels done (fibonacci, checked_add); buffer kernels next | `demo/test/snif_metamorphic_test.exs` |
| CI-1 | `abi-conformance` runs in CI (not just local `just`) | ABI | CI | ✅ Done (job added); *required-check* = owner branch-protection | `.github/workflows/proofs.yml` |

**Ledgered out of current scope (named, not silently dropped):**
- `zig/src/burble_fft.zig` (`fft`/`ifft`/`crash_oob_fft`/`test_constant`): not built into any artifact dir, and its slice params are `(ptr,len)` marshalling = **ABI-6** territory. Model once ABI-6 lands and the guest is built.
- Rust guests: `rust/crates/demo-guest` (canonical, loaded by the demo) and the standalone `rust-guest/` experiment share the buffer ABI; their conformance is pending the buffer-ABI multi-language gate (and the `rust/` vs `rust-guest/` relationship is documented, not merged — see PROOF-STATUS).

## Dangerous Patterns (BANNED — scanned by `just proof-scan-dangerous`, part of the gate)

| Pattern | Language | Meaning |
|---------|----------|---------|
| `believe_me` | Idris2 | Unsafe cast / trust-me |
| `assert_total` | Idris2 | Skip totality check |
| `postulate` | Idris2/Agda | Unproven axiom (SEC-1's TCB is a *record hypothesis*, NOT a postulate — by design) |
| `sorry` | Lean4 | Incomplete proof |
| `Admitted` | Coq | Incomplete proof |
| `unsafeCoerce` | Haskell | Unsafe type cast |
| `Obj.magic` | OCaml/ReScript | Unsafe type cast |
| `unsafe` (unaudited) | Rust | Unsafe block without safety comment |

## Prover Selection Guide

| Use Case | Prover | Why |
|----------|--------|-----|
| ABI/FFI boundaries | **Idris2** | Dependent types model layouts + signatures precisely |
| Public API type safety | **Lean4** | Algebraic/type metatheory |
| Operational isolation, (co)induction, the verdict bridge | **Agda** (`--safe --without-K`) | Self-contained small-step model; native induction |
| WASM operational semantics (the TCB discharge) | **Coq** (WasmCert-Coq) | Existing mechanised WASM semantics |

## Proof File Locations

```
verification/proofs/
├── idris2/ABI/      # ABI-1..5 + ABI-7 (Foreign.idr safe_nif, BufferAbi.idr buffer guest)
├── idris2/Types.idr # TP-1
├── lean4/           # TP-2 (ApiTypes.lean)
├── agda/            # SEC-1 (SnifIsolation.agda) + DOM-1 (SnifVerdict.agda)  [GATED]
│                    # Properties.agda is unrendered rsr-template SCAFFOLD (NOT gated)
├── coq/             # SEC-1-TCB slot (WasmCert-Coq); current file is SCAFFOLD
└── tlaplus/         # unused scaffold
verification/tools/abi_conformance.py   # the gap-1 interface drift gate
demo/test/snif_metamorphic_test.exs     # GAP-1b behaviour gate
```

## References

- Live proof status (authoritative): [`PROOF-STATUS.md`](PROOF-STATUS.md)
- Honesty boundary (what "Safer" may claim): `AUDIT.adoc`, README `Honesty` section
- Proven library (Idris2 verified foundations): `proven` repo
- Template origin: `rsr-template-repo/PROOF-NEEDS.md`
