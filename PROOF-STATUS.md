<!--
SPDX-License-Identifier: MPL-2.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Proof Status — SNIF
<!-- Template: rsr-template-repo/PROOF-STATUS.md -->
<!-- Tracks proof completion. Requirements defined in PROOF-NEEDS.md -->

## Summary

| Category | Total | Done | In Progress | Blocked | Remaining |
|----------|-------|------|-------------|---------|-----------|
| ABI/FFI (ABI) | 6 | 6 | 0 | 0 | 0 |
| Typing (TP) | 2 | 2 | 0 | 0 | 0 |
| Security / bridge (SEC, DOM) | 2 | 2 | 0 | 0 | 0 |
| **Total** | **10** | **10** | **0** | **0** | **0** |

**Overall**: 10/10 gated proof artifacts machine-check via `just proof-check-all` — 7 Idris2
(ABI-1..5 + ABI-7 buffer guest + TP-1 core types), 1 Lean4 (TP-2), 2 Agda (DOM-1 `SnifVerdict`
bridge + SEC-1 `SnifIsolation`). **SEC-1 is proven-modulo-the-explicit `FaithfulRuntime` TCB**
(the Safer-not-Safe gap); the other nine are unconditional.

> **Scope honesty.** These 7 proofs verify the **interface model** — ABI layout/pointer
> safety and the result-type algebra — *not* the operational crash-isolation theorem.
> The operational theorem **SEC-1** ("a guest trap becomes `{:error, _}`, the BEAM
> survives, and the error carries no guest value") is now **PROVEN-MODULO-EXPLICIT-TCB**
> in Agda (`SnifIsolation.agda`, `agda --safe --without-K`, gated) — see the SEC-1
> section below. It is proven over a small-step host↔guest model *modulo* an explicit,
> type-visible trust boundary (`FaithfulRuntime`); the boundary's faithfulness to
> wasmtime/wasmex (the WASM-opsem TCB) is **assumed, not yet discharged in-prover**.
> This residual assumption is exactly why the project is **Safer** NIFs, not Safe NIFs.

> **Scope ceiling (by design).** SNIF proofs cover the *safer-NIF* obligation **only**: the
> ABI/type model, crash-isolation (SEC-1), and the boundary residue being deniable/non-forging
> (`SnifVerdict`). SNIF does **not** extend past the NIF goal — it adapts and perfects the
> existing NIF for safety. Obligations belonging to *graduated integration beyond a NIF* (the
> transmutable **cleave** surface, its well-founded "staircase" teardown, transaction-gating,
> mode-indexed permissions) are **not SNIF's** and are tracked in the cleave proof-needs
> (`~/developer/dev-notes/2026-06-16-cleave-proof-needs.adoc`), not here. A SNIF *realizes one
> residue-clean cleave instance* at the BEAM↔native boundary; it is **not** the cleave.

## Verification (ground-truthed 2026-06-16)

All seven typecheck from a clean build cache under the pinned toolchain
(`idris2 0.8.0`, `lean 4.13.0`). Run the gate with:

```bash
just proof-check-all      # idris2 (--source-dir) + lean4 + dangerous-pattern scan; fails-on-skip
```

CI enforces this via `.github/workflows/proofs.yml` (Idris2 + Lean4 via Nix). To make it
**blocking**, add the check "Formal proofs — Idris2 + Lean4" to branch-protection required
status checks (owner-only).

> **History correction.** Entries dated 2026-04-16 below claimed "100% proven", but
> `ABI/Foreign`, `ABI/Platform`, and `ABI/Compliance` never actually compiled (Idris2
> unbound-implicit auto-binding shadowing the global specs; unary-`Nat` blow-up on the
> 65536-scale page-size arithmetic), and no CI job ever ran a prover (the `just
> proof-check-*` targets used a broken invocation and exited 0 when the tool was absent).
> Repaired and genuinely verified on 2026-06-16.

## Proofs Done

| ID | Proof | Prover | File | Verified | By |
|----|-------|--------|------|----------|-----|
| ABI-1 | Non-null pointer proofs (WasmAddr, SafePtr, MemRegion) | Idris2 | `verification/proofs/idris2/ABI/Pointers.idr` | 2026-06-16 | `idris2 --check` |
| ABI-2 | Memory layout correctness (WasmValType sizes, alignment) | Idris2 | `verification/proofs/idris2/ABI/Layout.idr` | 2026-06-16 | `idris2 --check` |
| ABI-3 | Platform type size proofs (WASM32 Zig-WASM correspondence) | Idris2 | `verification/proofs/idris2/ABI/Platform.idr` | 2026-06-16 | `idris2 --check` |
| ABI-4 | FFI function return type proofs (8 SNIF exports) | Idris2 | `verification/proofs/idris2/ABI/Foreign.idr` | 2026-06-16 | `idris2 --check` |
| ABI-5 | C ABI compliance (scalar exports, array layout framework) | Idris2 | `verification/proofs/idris2/ABI/Compliance.idr` | 2026-06-16 | `idris2 --check` |
| TP-1 | Core data type well-formedness (WasmTrapKind, SNIFCallResult, CompilationMode) | Idris2 | `verification/proofs/idris2/Types.idr` | 2026-06-16 | `idris2 --check` |
| TP-2 | Public API type safety (SNIFResult functor/monad laws, BEAM survival model) | Lean4 | `verification/proofs/lean4/ApiTypes.lean` | 2026-06-16 | `lean` |

### Repairs applied 2026-06-16 (no theorem weakened; no `believe_me`/`postulate`/`sorry`)
- **Foreign / Compliance** — global spec names (`specFibonacci`, …) in proof signatures
  were being auto-bound as fresh implicits (Idris2 unbound-implicits), making `Refl`
  unprovable; qualified them (`Foreign.specX`) to force resolution to the globals.
- **Platform** — WASM memory-size facts re-modeled `Nat → Integer` (faithful: WASM is
  32-bit addressed) so `65536²` and `mod 65536` evaluate in O(1) instead of hanging the
  typechecker. 5 signatures in the linear-memory section changed (comment-tagged).
- **Compliance** — `CABICompliant` / `WasmArrayValid` gained an explicit
  `NonZero alignment` witness (the originals used `SIsNonZero`, which cannot solve
  `NonZero (abstract divisor)`); a faithful strengthening, not a weakening.
- **Types / Lean** — supplied the missing `LTE max max` / `{max : Nat}` witnesses.

## Safety/security bridge (Agda, gated 2026-06-16)

`verification/proofs/agda/SnifVerdict.agda` (`agda --safe --without-K`, gated via
`just proof-check-agda-snif`, included in `proof-check-all`) is a **real** proof (not
scaffold): it models the host verdict as `ok ⊕ trap` and proves, **tropical-free** —
`dichotomy` (crash isolation), `no-reflect` (non-forgery: no extractor exists; epistemic
non-factivity) and `deniable-upto-redaction` / `perfect-deniable` (confidentiality: echo
deniability up to a `redact : S→R` channel). It bridges echo-types (loss/deniability) ×
epistemic-types (factive/belief). **Scope honesty:** this is the *verdict-type* result; it
does NOT replace SEC-1 (the operational theorem that the boundary actually *produces* such
verdicts). Model-level here — but as of **SNIFs 2** the deniability/redaction machinery is also
re-derived **operationally** over the actual fuelled run in `SnifIsolation.agda`
(`fault-via-observe`, `run-deniable`); see the SEC-1 audit section (F1 resolved).

## SEC-1 — operational crash-isolation (Agda, PROVEN-MODULO-EXPLICIT-TCB, gated 2026-06-16)

`verification/proofs/agda/SnifIsolation.agda` (module `SnifIsolation`,
`agda --safe --without-K --no-libraries -i verification/proofs/agda`, exit 0 from a clean
cache) mechanically proves **SEC-1**, the operational crash-isolation theorem, over a
small-step host↔guest model. The theorem is

```
Model.isolation : (rt : FaithfulRuntime) (n : Nat) (g : G) (h : H)
                → Alive h → Isolated rt n g h
```

inside the parameterised `module Model (G H A R : Set)` (G = opaque guest config / the
secret: linear memory/pc/locals; H = host/BEAM state; A = success value; R = public
`{:error,reason}`). Callers `open Model G H A R`; the witnesses use `open Model ⊤ ⊤ ⊤ ⊤`
and `open Model Nat ⊤ ⊤ ⊤`. So SEC-1's externally-qualified name is **`Model.isolation`**.
`FaithfulRuntime` and `Isolated` live in **Set₁** (because `Alive : H → Set` and
`noForgery` quantifies over `Set`) — benign under `--safe --without-K`.

`Isolated` bundles exactly the three SEC-1 conjuncts about the fuelled run `run rt n g h`:

| Conjunct | Field | How it is established |
|----------|-------|----------------------|
| **crash isolation** (verdict ∈ ok ⊕ trap) | `okOrTrap` | `SnifVerdict.dichotomy` applied to the `Verdict A R` that `run` builds **by construction** (returned↦ok, trapped↦trap, fuel-0↦trap). Not a `FaithfulRuntime` field. |
| **preservation** (host survives the call) | `hostSafe` | **DERIVED** by `survives`, an induction on the `Nat` fuel: zero→`timeout-host`; `suc` dispatches on `step rt g h` via with-inversion to continue→F3, returned→F4, trapped→F5 (each equation-guarded). Not a field. |
| **non-forgery** (error carries no guest value) | `noForgery` | `SnifVerdict.no-reflect` reused **verbatim** (no total `Verdict A R → A` extractor). Independent of every runtime field. |

**The TCB is an explicit hypothesis, never a postulate.** `FaithfulRuntime : Set₁` bundles
only PRIMITIVE single-step facts: `step : G → H → Step` (F1; the exhaustive
continue/returned/trapped trichotomy IS "no stuck / no host-observable UB"); the opaque
`Alive : H → Set` (F2; the predicate the conclusion is ABOUT, only transported); and
equation-guarded per-step preservation F3 `step-continue-host` (host-transparent internal
step), F4 `step-return-host` (survives across `onReturn`), **F5 `step-trap-host`** (the
crash-isolation primitive: survives across `recover`), F6 `timeout-host` (fuel/epoch
exhaustion surfaced as a trap, survives across `onTimeout`). **No field mentions a whole
run, "the call survives", or "ok-or-trap".**

**Non-circularity — verified by mutation, not by reading.** Replacing the trap-branch
discharge `trapOk r refl alive` in `survives` with the bare hypothesis `alive` makes the
file FAIL with `h != FaithfulRuntime.recover rt h of type H`: the run MUTATES the host to
`recover h` on a fault, so `Alive (recover h)` is unobtainable from `Alive h` and can come
only from F5. Deleting the `trapped` clause of `survives` fails with a `CoverageIssue`, so
the trap branch is coverage-mandatory for **every** `rt`. F5 is load-bearing.

**Non-vacuity — the model admits faulting runs, witnessed by `refl`.**
`UnitWitness.trapping-runtime` (step = `λ _ _ → trapped tt`) gives
`actually-traps : verdict (run … 1 …) ≡ trap tt` by `refl`; `Countdown.skipRT` reaches a
trap only AFTER two `continue` recursions (4→2→0→trap) with `multistep-traps = refl`, so
the **inductive** trap path is exercised (holing that `refl` breaks the build with
`UnsolvedInteractionMetas`); `multistep-isolated = isolation skipRT 3 4 tt tt` instantiates
SEC-1 on a real faulting trace; `timeout-traps` shows fuel-0 surfaces as a trap, not a
stuck state. Dual `returning-runtime` / `ok-case-live` make the dichotomy a genuine
two-sided ⊕, not an always-ok degenerate.

**What is ASSUMED (the WASM-opsem TCB, NOT discharged here).** The prose claim
**"wasmtime ⊨ FaithfulRuntime"** — that wasmtime + the wasmex embedding actually realise
these primitive facts (WASM trap-soundness, signal-caught trap → `{:error,reason}`, host
scheduler resumed unchanged) — is the stated trust boundary. It sits in the theorem's
TYPE as the `(rt : FaithfulRuntime)` binder (gate-legal: a record, not a `postulate`), and
is **explicitly out of scope** for in-Agda discharge. Discharging it via WasmCert-Coq
trap-soundness + a wasmtime signal-handling model is the remaining obligation (see "Not
yet proven"). **SEC-1 is therefore proven-modulo-this-explicit-TCB, and the TCB itself is
not yet machine-verified — the honest Safer-not-Safe gap.**

Banned-token scan clean (the only `postulate` string is a design-rule comment); zero `?`
holes; `run`/`survives` are structurally recursive on the `Nat` fuel (native termination,
no `TERMINATING` pragma). Gated via `just proof-check-agda-snif` (included in
`proof-check-all`; orchestrator wires the Justfile target — not edited here).

## SEC-1 — audit caveats (2026-06-16): F1/F2 RESOLVED in SNIFs 2; F3/F4/F5 standing precision notes

An adversarial proof-skeptic pass (`agda --safe --without-K`, exit 0 — the proofs are **sound**)
originally found the prose over-claiming in five ways (F1–F5). **F1 and F2 have since been fixed,
and the fixes mutation-confirmed load-bearing** by a 4-skeptic re-audit (2026-06-16); **F3/F4/F5**
remain as accurate *precision* caveats (they bound what the prose may claim, not soundness).

- **F1 — RESOLVED (SNIFs 2): confidentiality is now wired into the operational theorem.**
  `SnifIsolation.agda` imports `observe`/`faulted` from `SnifVerdict`; its `Step.trapped : S → Step`
  carries the guest **secret**; `FaithfulRuntime.redact : S → R` is the sole secret→public channel; and
  the run's fault verdict is `trap (guestFault (redact s))`, shown to factor through `observe`
  (`fault-via-observe`). Operational deniability is re-derived over the actual run (`run-deniable`):
  two faults whose secrets redact equally are host-indistinguishable. **Mutation-confirmed non-vacuous:**
  making `redact` injective (lossless) makes `SecretWitness.secrets-indistinguishable` fail to typecheck
  (`one ≠ two`) — the lossy redaction is genuinely load-bearing.
- **F2 / MODEL-1 — RESOLVED (SNIFs 2): the verdict models the real outcome taxonomy.** The host reason
  is now `TrapOrigin` = `guestFault` (`:trap`) ⊕ `hostBudget` (`:fuel_exhausted` / `:timeout`) ⊕
  `preExec` (`:load` / `:no_such_export` / `:pool`), and a `call` front-end models the three
  pre-execution origins the old run-only model could not express — covering all six `SnifDemo.Snif`
  `error_reason` origins; `PreExecWitness` exercises the pre-exec path. **Mutation-confirmed:** deleting
  the `preFail` branch of `survives` is rejected (`[CoverageIssue]`); retagging the trapped clause
  `guestFault`→`hostBudget` is rejected.
- **F3 — `dichotomy`/`noForgery` are structural, not runtime (standing, accurate).** `okOrTrap` and
  `noForgery` typecheck with *no* `FaithfulRuntime` in scope (re-confirmed: standalone lemmas taking no
  `rt` argument accept); only `hostSafe`/`survives` consumes the TCB. The load-bearing operational
  content of SEC-1 is **host preservation**, not the ok|trap split (true for any 2-constructor type).
- **F4 — `noForgery` is parametric, not instance-level (standing, accurate).** It proves no total
  `∀{A R}. Verdict A R → A` exists; the instance-level discharge is rejected (`A !=< ⊥`). Sound,
  labelled precisely.
- **F5 — `Alive` faithfulness remains TCB; vacuity now rebutted by a witness (SNIFs 2).** `PartialAlive`
  exhibits a *non-trivial* liveness (`Alive? dead = ⊥`; mutation-confirmed — making it `⊤` breaks
  `dead-not-alive`) whose `recover` maps a dying host to a live one. This rebuts the *vacuity* worry, but
  `Alive`'s faithfulness to wasmtime/wasmex is still part of the TCB: `survives` *transports* a liveness,
  it does not *establish* the real one.

**Positive control (F6):** `step-trap-host` *is* load-bearing (mutating `survives`' trap branch to bare
`alive` is rejected: `h != recover rt h`); `perfect-deniable`'s constant redaction *is* load-bearing.
SEC-1 is **not vacuous** — host-preservation-across-`recover` + the structural ok|trap split +
operational deniability + the origin taxonomy, all *modulo* the `Alive`/`FaithfulRuntime` TCB. A
2026-06-16 mutation re-audit (4 independent skeptics, every targeted mutation rejected as expected)
confirmed all of the above; the only weakness found was stale prose, now corrected here.

## Scaffold (NOT counted, NOT gated)

`verification/proofs/{agda,coq,tlaplus}/` contain **unmodified rsr-template stubs** (a
toy list/Nat Agda lemma, a toy Nat/Bool Coq soundness proof, a generic TLA+ pipeline) —
they have nothing to do with SNIF and are excluded from `proof-check-all`. Each now
carries a `SCAFFOLD — NOT A SNIF PROOF` banner. They are kept as homes for real future
obligations (e.g. the Coq slot → the WasmCert-Coq isolation theorem).

## Not yet proven (the real gap / next obligations)

| ID | Proof needed | Category | Prover | Notes |
|----|--------------|----------|--------|-------|
| SEC-1-TCB | Discharge **"wasmtime ⊨ FaithfulRuntime"** in-prover: prove that wasmtime + the wasmex embedding actually realise the primitive single-step facts (WASM trap-soundness; trap → `{:error,_}`; host scheduler resumed unchanged) that `SnifIsolation.agda` assumes as its TCB record | SEC | Coq (WasmCert-Coq) | SEC-1's **operational** layer is now PROVEN-MODULO-EXPLICIT-TCB in Agda (`Model.isolation`). This row is the REMAINING half: machine-verifying the runtime-faithfulness assumption that is currently in the theorem's *type* but not proven. |
| ABI-6 | Buffer/array marshalling round-trip + in-bounds (unblocks "powerful" NIFs; FFT) | ABI | Idris2 | `Compliance.WasmArray*` is only a framework today |
| ABI-7 | ◐ **Coverage 15 of 20 — buffer_abi DONE 2026-06-16.** `safe_nif` (8, `Foreign.idr`) + `buffer_abi` (7, `BufferAbi.idr`, incl. 3 void returns) are modelled+gated, both in the `abi_conformance.py` guest manifest. **Remaining (ledgered):** `zig/src/burble_fft.zig` (5 — `fft`/`ifft`/… use `(ptr,len)` slice marshalling = ABI-6, and it is not built into any artifact) + the Rust buffer guest | ABI | Idris2 + Python | Buffer guest closed; FFT + Rust pending the multi-language buffer-ABI gate |
| GAP-1b | ◐ **Behaviour faithfulness — scalar kernels DONE 2026-06-16.** `demo/test/snif_metamorphic_test.exs` (dep-free, 9 metamorphic tests, green on OTP 25). **Load-bearing relations (do not delete):** the `fibonacci` recurrence n=2..40 + base cases (uniquely determines fib), and the `checked_add` `wrap32` oracle over a 100-case boundary-spanning family + the boundary-wrap test. Buffer kernels (`sum_f32` permutation/additivity) are next | TP | metamorphic tests (extraction long-term) | Surfaced a finding: `checked_add` is a **misnomer** — it is wrapping (`a +% b`), not trapping (the trapping demo is `crash_overflow`); doc-comment corrected |
| CI-1 | ✅ **DONE 2026-06-16**: `abi-conformance` now runs as a CI job in `.github/workflows/proofs.yml` (builds both guests, fails on signature drift) | ABI | CI wiring | Making it a *required* status check is the owner-only branch-protection step |
| MODEL-1 | ◐ **Largely RESOLVED by F2 (SNIFs 2).** The 6 `error_reason` origins are now modelled via `TrapOrigin` (guestFault/hostBudget/preExec) + the `call` front-end in `SnifIsolation`. **Residual:** the `snif_alloc`-returns-0 OOM "third outcome" is not yet modelled as a distinct verdict | TP | Agda | Taxonomy half done; only the OOM-sentinel nuance remains |

## Changelog

| Date | Change | By |
|------|--------|-----|
| 2026-04-04 | Initial proof status tracking | Template |
| 2026-04-16 | (Claimed) all 7 proofs complete — see History correction; not actually compiling | Claude Code |
| 2026-06-16 | All 7 proofs **genuinely** machine-checked (clean-cache); real gate wired; scaffold de-counted; scope honesty added | Claude Opus 4.8 |
| 2026-06-16 | **SEC-1 (`Model.isolation`) PROVEN-MODULO-EXPLICIT-TCB** in Agda (`SnifIsolation.agda`, `--safe --without-K`, clean-cache exit 0); TCB = `FaithfulRuntime` record hypothesis (primitive single-step facts), non-circularity + non-vacuity confirmed by mutation; WASM-opsem discharge ("wasmtime ⊨ FaithfulRuntime") remains as SEC-1-TCB | Claude Opus 4.8 (1M context) |
| 2026-06-16 | **SNIFs 2.** SEC-1 sharpened: F1 deniability wired operationally (`run-deniable`/`fault-via-observe` + `SecretWitness`), F2 6-origin `TrapOrigin` taxonomy + `call` front-end (`PreExecWitness`), F5 non-trivial-`Alive` recovery witness (`PartialAlive`) — all mutation-confirmed load-bearing by a 4-skeptic re-audit. ABI-7: `buffer_abi` modelled+gated (`BufferAbi.idr`, 15/20 sites); guest-aware `abi_conformance.py`; CI-1 conformance job added; GAP-1b scalar metamorphic gate (found + corrected the `checked_add` misnomer). | Claude Opus 4.8 (1M context) |
