{-# OPTIONS --safe --without-K #-}

-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
--
-- SEC-1 — the OPERATIONAL crash-isolation theorem for SNIFs (Safer NIFs).
--
-- Claim (informal): for any SNIF *call*, the runtime either (pre-execution) refuses to
-- dispatch the guest, or runs it; in every case it returns a host-observable verdict that
-- is ok-or-trap, the host state is PRESERVED (survives), the error verdict carries NO
-- guest value, and the trap RESIDUE leaks nothing of the guest's secret beyond an explicit
-- public redaction.
--
-- Model: a small-step host<->guest semantics with an explicit fuel counter and a genuine
-- trap-producing step that carries the guest's SECRET state, redacted to a public reason at
-- the boundary. A pre-execution `call` front-end models the origins where the guest never
-- steps. Isolation, preservation and deniability are DERIVED (by induction on the fuelled
-- run, and by reuse of SnifVerdict), so the fault path is unmistakably exercised.
--
-- WHAT THIS FILE NOW ESTABLISHES (the 2026-06-16 "SNIFs 2" sharpening — see PROOF-STATUS):
--   * F1 (deniability WIRED INTO the operational theorem): the operational trap is now
--     secret-carrying (`Step.trapped : S → Step`); the run's verdict on a fault is produced
--     through SnifVerdict's redaction channel (`fault-via-observe`); and `run-deniable`
--     re-derives restricted deniability OVER THE ACTUAL RUN — two faulting runs whose secrets
--     redact equally are host-indistinguishable. The previous file proved deniability only in
--     SnifVerdict's separate `Outcome` model and imported none of it here.
--   * F2 / MODEL-1 (the real outcome taxonomy): the host-observable reason is now a
--     `TrapOrigin` with three classes — `guestFault` (the guest ran and faulted, residue =
--     redacted secret), `hostBudget` (the host aborted a running guest: fuel/timeout, residue
--     is host-canonical and carries no guest secret), and `preExec` (the guest never ran:
--     load / no_such_export / pool). A `call` front-end models the three pre-execution origins
--     that the old `run`-only model could not express. This covers all six `error_reason`
--     origins of `SnifDemo.Snif`.
--   * F5 (non-trivial `Alive` witness): `PartialAlive` exhibits a runtime over a partial,
--     genuinely-non-total liveness predicate (`dead` is NOT alive) whose `recover` maps a
--     dying host to a live one — so "Alive is an inhabited, non-trivial liveness notion" is
--     now exercised by a witness, not merely assumed.
--
-- HONEST RESIDUE (F3/F4/F5-TCB — unchanged, see PROOF-STATUS):
--   * `okOrTrap` and `noForgery` are STRUCTURAL facts about the `Verdict` datatype; the
--     load-bearing operational content consuming the TCB is `survives` (host preservation).
--   * `noForgery` is the parametric non-existence of a total extractor, not an instance claim.
--   * `Alive` faithfulness ("wasmtime's notion of a schedulable BEAM process is THIS predicate")
--     remains part of the TCB; `survives` transports a liveness, it does not establish the
--     real one. `PartialAlive` rebuts only the *vacuity* worry, not the TCB itself.
--
-- ===========================================================================
-- TRUST BOUNDARY (the explicit TCB — assumed, NOT proven in Agda)
-- ===========================================================================
-- The theorem `Model.isolation` takes `(rt : FaithfulRuntime)` as its first explicit
-- argument. `FaithfulRuntime` bundles ONLY primitive single-step / single-decision runtime
-- facts: a total one-step function `step`, the pre-execution decision `preCheck`, the
-- redaction `redact : S → R` (the SOLE guest-secret → public-reason channel), an opaque
-- host-survival predicate `Alive`, and equation-guarded per-step preservation facts. None of
-- these fields mentions a whole run, "the call survives", "ok-or-trap", or "the residue hides
-- the secret" — those are the CONCLUSIONS, derived below.
--
-- The prose claim that this TCB is FAITHFUL TO REALITY —  "wasmtime ⊨ FaithfulRuntime" — is
-- NOT proven here (it is the WasmCert-Coq discharge tracked as SEC-1-TCB, out of scope). This
-- residual assumption is exactly why SNIFs are "Safer" NIFs, not "Safe": the operational
-- isolation/deniability properties are mechanically PROVEN *modulo this explicit, type-visible
-- TCB*, and the TCB itself is not yet machine-verified.
-- ===========================================================================

module SnifIsolation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import SnifVerdict
  using ( Verdict; ok; trap; _⊎_; inl; inr; ⊥; ⊤; tt; ¬_
        ; no-reflect; IsOk; IsTrap; dichotomy; isOk; isTrap
        ; Outcome; faulted; observe; cong )

--------------------------------------------------------------------------------
-- Minimal equational plumbing (self-contained; --without-K-safe).
--------------------------------------------------------------------------------

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

--------------------------------------------------------------------------------
-- Abstract carriers. Kept opaque so the proof cannot peek inside (no smuggled
-- decidability, no hidden invariant). G : guest configs; H : host state;
-- A : success value; R : public trap reason; S : guest SECRET state (linear
-- memory / inputs / partial work) that a fault holds and must NOT cross intact.
--------------------------------------------------------------------------------

module Model (G H A R S : Set) where

  -- One micro-step across the host<->guest boundary. This `Step` datatype is the SINGLE
  -- primitive about WASM execution. Its three constructors are exhaustive, which is precisely
  -- "no stuck / no host-observable UB": a config ALWAYS does one. A fault now carries the
  -- guest SECRET `S` (it is redacted to a public reason only at the boundary, by the runtime).
  data Step : Set where
    continue : G → Step           -- internal guest step to a new config; host untouched
    returned : A → Step           -- guest produced a value
    trapped  : S → Step           -- guest faulted, holding secret state S

  -- The host-observable trap reason, TAGGED with where the trap came from (F2 / MODEL-1).
  -- This is the public residue; it is what the host sees, never the secret S.
  data TrapOrigin : Set where
    guestFault : R → TrapOrigin   -- :trap            — guest ran & faulted; R = redact(secret)
    hostBudget : R → TrapOrigin   -- :fuel_exhausted / :timeout — host aborted a running guest
    preExec    : R → TrapOrigin   -- :load / :no_such_export / :pool — guest never ran

  -- The pre-execution decision: dispatch the guest, or refuse before it ever steps.
  data PreCheck : Set where
    ready   : PreCheck
    preFail : R → PreCheck

  --------------------------------------------------------------------------------
  -- THE TRUST BOUNDARY as an explicit hypothesis (the TCB record).
  -- Every field is a PRIMITIVE single-step / single-decision runtime fact. NONE mentions a
  -- whole run, "the call survives", "ok-or-trap", or "the residue hides the secret": those are
  -- the CONCLUSIONS, derived below — not assumed here.
  --------------------------------------------------------------------------------
  record FaithfulRuntime : Set₁ where
    field
      -- PRIMITIVE. The runtime's single-step function. That it returns a `Step` for EVERY
      -- (guest, host) is the totality / "no stuck state" fact: wasmtime never gets stuck — it
      -- continues, returns, or traps.
      step : G → H → Step

      -- PRIMITIVE. The pre-execution decision (module load + export resolution + pool
      -- acquisition). `preFail r` is a SNIF call that never dispatches the guest.
      preCheck : G → H → PreCheck

      -- PRIMITIVE. The SOLE channel from a guest secret to a host-visible reason. The host
      -- never sees S; on a fault it sees only `redact s`. This is the cleave surface.
      redact : S → R

      -- PRIMITIVE. Host survival is a runtime-supplied predicate `Alive h` ("the BEAM process
      -- is schedulable in host state h"). OPAQUE to the proof; we only transport it.
      Alive : H → Set

      -- PRIMITIVE. A `continue` (internal guest) step is host-transparent: it leaves the host
      -- state h UNCHANGED, hence `Alive` is undisturbed. wasmtime runs the guest sandboxed.
      step-continue-host : ∀ g h g' → step g h ≡ continue g' → Alive h → Alive h

      -- PRIMITIVE. On a `returned` step the host advances by the embedding's return handler
      -- `onReturn`, and survival is preserved (a clean return cannot kill the scheduler).
      onReturn : H → H
      step-return-host :
        ∀ g h a → step g h ≡ returned a → Alive h → Alive (onReturn h)

      -- PRIMITIVE. On a `trapped` step the host advances by the embedding's trap handler
      -- `recover` (signal caught -> {:error, reason}), and survival is PRESERVED: a trapped
      -- guest does not corrupt or kill the host. This is the single fact that makes a SNIF
      -- "Safer" — a per-step fact about the embedding, NOT the whole-call conclusion.
      recover : H → H
      step-trap-host :
        ∀ g h s → step g h ≡ trapped s → Alive h → Alive (recover h)

      -- PRIMITIVE. The embedding's canonical timeout reason + handler, used when the fuel /
      -- epoch budget is exhausted while the guest is still running (wasmex epoch interruption).
      -- This is a host-budget abort: the residue is host-canonical and carries no guest secret.
      timeoutReason : R
      onTimeout     : H → H
      timeout-host  : ∀ h → Alive h → Alive (onTimeout h)

  --------------------------------------------------------------------------------
  -- The outcome of a whole run/call: the host-observable Verdict (over the TAGGED reason
  -- `TrapOrigin`, landing in ok ⊕ trap by construction of `Verdict`) and the host state after.
  --------------------------------------------------------------------------------
  record RunResult : Set where
    constructor _,_
    field
      verdict   : Verdict A TrapOrigin
      hostAfter : H

  open RunResult

  --------------------------------------------------------------------------------
  -- The fuelled small-step driver. The trap-producing step lives here (a genuine faulting
  -- run, not a vacuous one), and fuel exhaustion is itself surfaced as a host-budget trap.
  -- `run` is factored through `drive` (dispatch on an already-computed step) so that the
  -- operational deniability lemma below reduces by a single `cong`, with no fragile
  -- with-abstraction. `run rt n g h` drives at most n steps from config (g , h).
  --------------------------------------------------------------------------------
  run   : FaithfulRuntime → Nat → G → H → RunResult
  drive : FaithfulRuntime → Nat → G → H → Step → RunResult

  run rt zero    g h = trap (hostBudget (FaithfulRuntime.timeoutReason rt))
                       , FaithfulRuntime.onTimeout rt h
  run rt (suc n) g h = drive rt n g h (FaithfulRuntime.step rt g h)

  drive rt n g h (continue g') = run rt n g' h                        -- host UNCHANGED
  drive rt n g h (returned a)  = ok a , FaithfulRuntime.onReturn rt h  -- success
  drive rt n g h (trapped s)   = trap (guestFault (FaithfulRuntime.redact rt s))
                                 , FaithfulRuntime.recover rt h        -- FAULT -> redacted residue

  --------------------------------------------------------------------------------
  -- THE CALL front-end (F2): a SNIF call first does the pre-execution decision. If it fails,
  -- the guest NEVER steps and the host is UNTOUCHED; otherwise it runs the guest.
  --------------------------------------------------------------------------------
  call : FaithfulRuntime → Nat → G → H → RunResult
  call rt n g h with FaithfulRuntime.preCheck rt g h
  ... | ready     = run rt n g h
  ... | preFail r = trap (preExec r) , h

  --------------------------------------------------------------------------------
  -- (A) HOST SURVIVAL / PRESERVATION at the RUN level. If the host is Alive before the guest
  -- runs, it is Alive after — WHATEVER the guest does (loop, return, trap, or time out).
  -- Proved by induction on fuel; the trap and timeout cases genuinely discharge the
  -- trapped/recover and zero/onTimeout branches, so survival under a fault is exercised.
  --------------------------------------------------------------------------------
  survives-run : (rt : FaithfulRuntime) (n : Nat) (g : G) (h : H) →
                 FaithfulRuntime.Alive rt h →
                 FaithfulRuntime.Alive rt (RunResult.hostAfter (run rt n g h))
  survives-run rt zero    g h alive = FaithfulRuntime.timeout-host rt h alive
  survives-run rt (suc n) g h alive with FaithfulRuntime.step rt g h
                                       | (λ s  → FaithfulRuntime.step-trap-host    rt g h s)
                                       | (λ a  → FaithfulRuntime.step-return-host   rt g h a)
                                       | (λ g' → FaithfulRuntime.step-continue-host rt g h g')
  ... | continue g' | _      | _      | contOk = survives-run rt n g' h (contOk g' refl alive)
  ... | returned a  | _      | retOk  | _       = retOk a refl alive
  ... | trapped s   | trapOk | _      | _       = trapOk s refl alive

  --------------------------------------------------------------------------------
  -- (A') HOST SURVIVAL at the CALL level: a pre-execution failure leaves the host untouched
  -- (it trivially survives, the guest never ran); otherwise reuse run-level survival.
  --------------------------------------------------------------------------------
  survives : (rt : FaithfulRuntime) (n : Nat) (g : G) (h : H) →
             FaithfulRuntime.Alive rt h →
             FaithfulRuntime.Alive rt (RunResult.hostAfter (call rt n g h))
  survives rt n g h alive with FaithfulRuntime.preCheck rt g h
  ... | ready     = survives-run rt n g h alive
  ... | preFail r = alive

  --------------------------------------------------------------------------------
  -- (B) CRASH ISOLATION as a Verdict. The call's verdict lands in ok ⊕ trap. We REUSE
  -- SnifVerdict.dichotomy: every Verdict is structurally one or the other. (Honest: this is a
  -- datatype fact about `Verdict`, true with no FaithfulRuntime in scope — see PROOF-STATUS F3.)
  --------------------------------------------------------------------------------
  verdict-dichotomy : (rt : FaithfulRuntime) (n : Nat) (g : G) (h : H) →
                      IsOk (RunResult.verdict (call rt n g h))
                      ⊎ IsTrap (RunResult.verdict (call rt n g h))
  verdict-dichotomy rt n g h = dichotomy (RunResult.verdict (call rt n g h))

  --------------------------------------------------------------------------------
  -- THE SEC-1 BUNDLE. For a call from an Alive host, the call is ISOLATED:
  --   * verdict ∈ ok ⊕ trap                 (crash isolation)
  --   * host survives                        (preservation — the TCB-consuming content)
  --   * no total extractor Verdict A R → A   (non-forgery; the error carries no guest value)
  -- Confidentiality (the residue hides the secret) is the SEPARATE `run-deniable` theorem
  -- below, now stated over this same operational `run` (F1).
  --------------------------------------------------------------------------------
  record Isolated (rt : FaithfulRuntime) (n : Nat) (g : G) (h : H) : Set₁ where
    field
      okOrTrap   : IsOk (RunResult.verdict (call rt n g h))
                   ⊎ IsTrap (RunResult.verdict (call rt n g h))
      hostSafe   : FaithfulRuntime.Alive rt (RunResult.hostAfter (call rt n g h))
      noForgery  : (∀ {A' R' : Set} → Verdict A' R' → A') → ⊥

  -- SEC-1. The operational crash-isolation theorem (over a full SNIF call).
  isolation : (rt : FaithfulRuntime) (n : Nat) (g : G) (h : H) →
              FaithfulRuntime.Alive rt h → Isolated rt n g h
  isolation rt n g h alive = record
    { okOrTrap  = verdict-dichotomy rt n g h
    ; hostSafe  = survives rt n g h alive
    ; noForgery = no-reflect
    }

  --------------------------------------------------------------------------------
  -- (C) OPERATIONAL DENIABILITY (F1) — deniability re-derived over the ACTUAL run.
  --
  -- The run's fault residue is exactly the redacted secret, produced through SnifVerdict's
  -- `observe` channel; hence two faulting runs whose secrets redact equally are
  -- host-indistinguishable in their verdict. This is the property that used to live only in
  -- SnifVerdict's separate `Outcome` model and was not wired into SEC-1.
  --------------------------------------------------------------------------------

  -- The run's guest-fault residue IS SnifVerdict.observe applied to the redaction channel:
  -- the operational trap verdict factors through the only secret→public channel there is.
  fault-via-observe :
    (rt : FaithfulRuntime) (s : S) →
    trap {A = A} (guestFault (FaithfulRuntime.redact rt s))
      ≡ observe (λ s' → guestFault (FaithfulRuntime.redact rt s')) (faulted s)
  fault-via-observe rt s = refl

  -- A faulting first step yields exactly the redacted residue (single `cong`, via `drive`).
  fault-run-verdict :
    (rt : FaithfulRuntime) (n : Nat) (g : G) (h : H) (s : S) →
    FaithfulRuntime.step rt g h ≡ trapped s →
    RunResult.verdict (run rt (suc n) g h)
      ≡ trap (guestFault (FaithfulRuntime.redact rt s))
  fault-run-verdict rt n g h s eq =
    cong (λ st → RunResult.verdict (drive rt n g h st)) eq

  -- Restricted deniability over `observe`: equal redactions give equal residues.
  guestFault-deniable :
    (rt : FaithfulRuntime) (s₁ s₂ : S) →
    FaithfulRuntime.redact rt s₁ ≡ FaithfulRuntime.redact rt s₂ →
    trap {A = A} (guestFault (FaithfulRuntime.redact rt s₁))
      ≡ trap (guestFault (FaithfulRuntime.redact rt s₂))
  guestFault-deniable rt s₁ s₂ eq = cong (λ r → trap (guestFault r)) eq

  -- THE OPERATIONAL DENIABILITY THEOREM (F1): two runs that fault on secrets which redact
  -- equally produce the SAME host-observable verdict. No host opener can tell them apart.
  run-deniable :
    (rt : FaithfulRuntime) (n : Nat)
    (g₁ : G) (h₁ : H) (g₂ : G) (h₂ : H) (s₁ s₂ : S) →
    FaithfulRuntime.step rt g₁ h₁ ≡ trapped s₁ →
    FaithfulRuntime.step rt g₂ h₂ ≡ trapped s₂ →
    FaithfulRuntime.redact rt s₁ ≡ FaithfulRuntime.redact rt s₂ →
    RunResult.verdict (run rt (suc n) g₁ h₁)
      ≡ RunResult.verdict (run rt (suc n) g₂ h₂)
  run-deniable rt n g₁ h₁ g₂ h₂ s₁ s₂ e₁ e₂ er =
    trans (fault-run-verdict rt n g₁ h₁ s₁ e₁)
          (trans (guestFault-deniable rt s₁ s₂ er)
                 (sym (fault-run-verdict rt n g₂ h₂ s₂ e₂)))

  -- HOST-BUDGET residue is secret-free: a fuel-exhaustion verdict is host-canonical and does
  -- not depend on the guest at all (the residue carries zero guest information, by construction).
  timeout-secret-free :
    (rt : FaithfulRuntime) (g₁ g₂ : G) (h : H) →
    RunResult.verdict (run rt zero g₁ h) ≡ RunResult.verdict (run rt zero g₂ h)
  timeout-secret-free rt g₁ g₂ h = refl

--------------------------------------------------------------------------------
-- NON-VACUITY WITNESSES — the model ADMITS FAULTING RUNS, demonstrated CONCRETELY.
--
-- A SEC-1 over a model where the guest can never trap would be vacuously true. We rule that
-- out by exhibiting runtimes whose guest TRAPS (so the trapped/recover branch is reachable),
-- whose guest RETURNS (so the ok branch is reachable — a real ⊕), whose pre-check FAILS (so a
-- pre-execution origin is reachable), and whose `Alive` is genuinely partial (F5).
--------------------------------------------------------------------------------

module UnitWitness where

 open Model ⊤ ⊤ ⊤ ⊤ ⊤

 -- (1) A runtime whose guest faults immediately. Host trivially Alive (`λ _ → ⊤`); redaction is
 -- the unit channel; pre-check is always `ready` (the guest is dispatched).
 trapping-runtime : FaithfulRuntime
 trapping-runtime = record
   { step               = λ _ _ → trapped tt   -- guest faults on the first step
   ; preCheck           = λ _ _ → ready
   ; redact             = λ _ → tt
   ; Alive              = λ _ → ⊤
   ; step-continue-host = λ _ _ _ _ a → a
   ; onReturn           = λ h → h
   ; step-return-host   = λ _ _ _ _ a → a
   ; recover            = λ h → h
   ; step-trap-host     = λ _ _ _ _ a → a
   ; timeoutReason      = tt
   ; onTimeout          = λ h → h
   ; timeout-host       = λ _ a → a
   }

 -- Its one-step run yields a guest-fault TRAP verdict — PROVEN by refl, not assumed.
 actually-traps :
   RunResult.verdict (run trapping-runtime (suc zero) tt tt) ≡ trap (guestFault tt)
 actually-traps = refl

 -- And that verdict lands in the TRAP side of the dichotomy: the faulting case is a real,
 -- inhabited branch that `isolation` must (and does) handle.
 trap-case-live :
   IsTrap (RunResult.verdict (run trapping-runtime (suc zero) tt tt))
 trap-case-live = isTrap (guestFault tt)

 -- (2) A runtime that returns a value, so the OK branch is reachable too (genuine ⊕).
 returning-runtime : FaithfulRuntime
 returning-runtime = record
   { step               = λ _ _ → returned tt
   ; preCheck           = λ _ _ → ready
   ; redact             = λ _ → tt
   ; Alive              = λ _ → ⊤
   ; step-continue-host = λ _ _ _ _ a → a
   ; onReturn           = λ h → h
   ; step-return-host   = λ _ _ _ _ a → a
   ; recover            = λ h → h
   ; step-trap-host     = λ _ _ _ _ a → a
   ; timeoutReason      = tt
   ; onTimeout          = λ h → h
   ; timeout-host       = λ _ a → a
   }

 ok-case-live :
   IsOk (RunResult.verdict (run returning-runtime (suc zero) tt tt))
 ok-case-live = isOk tt

 -- (3) OPERATIONAL DENIABILITY exercised: over the unit redaction, the two faulting runs
 -- agree (trivially, since redact is constant) — a concrete instance of `run-deniable`.
 unit-deniable :
   RunResult.verdict (run trapping-runtime (suc zero) tt tt)
     ≡ RunResult.verdict (run trapping-runtime (suc zero) tt tt)
 unit-deniable = run-deniable trapping-runtime zero tt tt tt tt tt tt refl refl refl

--------------------------------------------------------------------------------
-- (4) PRE-EXECUTION origin (F2): a runtime whose pre-check FAILS — the guest never steps,
-- the host is untouched, yet the call is still ISOLATED (a `preExec` trap, host survives).
-- This is the :load / :no_such_export / :pool class that the run-only model could not express.
--------------------------------------------------------------------------------

module PreExecWitness where

 open Model ⊤ ⊤ ⊤ ⊤ ⊤

 not-found-runtime : FaithfulRuntime
 not-found-runtime = record
   { step               = λ _ _ → returned tt   -- irrelevant: the guest never dispatches
   ; preCheck           = λ _ _ → preFail tt     -- e.g. :no_such_export
   ; redact             = λ _ → tt
   ; Alive              = λ _ → ⊤
   ; step-continue-host = λ _ _ _ _ a → a
   ; onReturn           = λ h → h
   ; step-return-host   = λ _ _ _ _ a → a
   ; recover            = λ h → h
   ; step-trap-host     = λ _ _ _ _ a → a
   ; timeoutReason      = tt
   ; onTimeout          = λ h → h
   ; timeout-host       = λ _ a → a
   }

 -- The call yields a pre-execution trap, PROVEN by refl.
 preexec-traps :
   RunResult.verdict (call not-found-runtime (suc zero) tt tt) ≡ trap (preExec tt)
 preexec-traps = refl

 -- And the call is isolated: ok-or-trap, host survives (untouched), non-forgery.
 preexec-isolated : Isolated not-found-runtime (suc zero) tt tt
 preexec-isolated = isolation not-found-runtime (suc zero) tt tt tt

--------------------------------------------------------------------------------
-- (5) MULTI-STEP non-vacuity: a guest that COUNTS DOWN through `continue` steps and only THEN
-- traps. This exercises the INDUCTIVE recursion of `run`/`survives` (the `continue` branch is
-- taken before the `trapped` branch fires), so the trap case is reached via the induction.
--------------------------------------------------------------------------------

module Countdown where

  open Model Nat ⊤ ⊤ ⊤ ⊤

  -- A guest that internally steps from (suc (suc k)) straight to k, so even configs reach 0
  -- (which TRAPS, holding the unit secret) and odd configs reach 1 (which RETURNS).
  skipStep : Nat → ⊤ → Step
  skipStep zero          _ = trapped tt
  skipStep (suc zero)    _ = returned tt
  skipStep (suc (suc k)) _ = continue k

  skipRT : FaithfulRuntime
  skipRT = record
    { step               = skipStep
    ; preCheck           = λ _ _ → ready
    ; redact             = λ _ → tt
    ; Alive              = λ _ → ⊤
    ; step-continue-host = λ _ _ _ _ a → a
    ; onReturn           = λ h → h
    ; step-return-host   = λ _ _ _ _ a → a
    ; recover            = λ h → h
    ; step-trap-host     = λ _ _ _ _ a → a
    ; timeoutReason      = tt
    ; onTimeout          = λ h → h
    ; timeout-host       = λ _ a → a
    }

  -- config 4 ⟶ 2 ⟶ 0 ⟶ trap: TWO continue steps then a trap. Fuel 3 suffices. Proves the
  -- trap branch is reached THROUGH the inductive `continue` recursion.
  multistep-traps :
    RunResult.verdict (run skipRT (suc (suc (suc zero))) (suc (suc (suc (suc zero)))) tt)
      ≡ trap (guestFault tt)
  multistep-traps = refl

  -- An odd start returns after its continues: config 3 ⟶ 1 ⟶ return.
  multistep-returns :
    RunResult.verdict (run skipRT (suc (suc zero)) (suc (suc (suc zero))) tt) ≡ ok tt
  multistep-returns = refl

  -- (6) TIMEOUT-as-host-budget-trap is reachable, not a stuck state: too little fuel for the
  -- countdown still yields a host-budget trap verdict (the fuel-zero branch of `run`).
  timeout-traps :
    RunResult.verdict (run skipRT zero (suc (suc (suc (suc zero)))) tt) ≡ trap (hostBudget tt)
  timeout-traps = refl

  -- (7) ISOLATION delivers on the genuinely-faulting multistep call: host survives a fault
  -- reached by induction. This is SEC-1 instantiated on a real faulting trace.
  multistep-isolated :
    Isolated skipRT (suc (suc (suc zero))) (suc (suc (suc (suc zero)))) tt
  multistep-isolated =
    isolation skipRT (suc (suc (suc zero))) (suc (suc (suc (suc zero)))) tt tt

--------------------------------------------------------------------------------
-- (8) NON-TRIVIAL `Alive` WITNESS (F5). The preservation fields have shape
-- `Alive h → Alive (handler h)`, satisfiable even by `Alive = ⊥`. Here `Alive?` is genuinely
-- PARTIAL — `dead` is NOT alive — and `recover` maps a dying host to a live one, so recovery
-- is real (not vacuous). This rebuts the *vacuity* worry; `Alive` faithfulness itself remains
-- TCB (a real wasmex run starts from a live host).
--------------------------------------------------------------------------------

module PartialAlive where

  data HostState : Set where live dead : HostState

  open Model ⊤ HostState ⊤ ⊤ ⊤

  Alive? : HostState → Set
  Alive? live = ⊤
  Alive? dead = ⊥          -- non-trivial: not every host state is alive

  -- A faulting runtime whose `recover` restores liveness (dead ⟶ live).
  recover-runtime : FaithfulRuntime
  recover-runtime = record
    { step               = λ _ _ → trapped tt
    ; preCheck           = λ _ _ → ready
    ; redact             = λ _ → tt
    ; Alive              = Alive?
    ; step-continue-host = λ _ _ _ _ a → a
    ; onReturn           = λ _ → live
    ; step-return-host   = λ _ _ _ _ _ → tt   -- Alive? (onReturn h) = Alive? live = ⊤
    ; recover            = λ _ → live           -- recovery RESTORES liveness
    ; step-trap-host     = λ _ _ _ _ _ → tt     -- Alive? (recover h) = Alive? live = ⊤
    ; timeoutReason      = tt
    ; onTimeout          = λ _ → live
    ; timeout-host       = λ _ _ → tt
    }

  -- `dead` is genuinely NOT alive — the predicate is non-trivial, not the all-⊤ stub.
  dead-not-alive : ¬ (Alive? dead)
  dead-not-alive ()

  -- A guest fault FROM A DEAD HOST yields a LIVE host: recovery is real, proven by refl.
  recovers-dead :
    RunResult.hostAfter (run recover-runtime (suc zero) tt dead) ≡ live
  recovers-dead = refl

  -- ...and that recovered host IS alive, though the dead one was not.
  recovered-alive :
    Alive? (RunResult.hostAfter (run recover-runtime (suc zero) tt dead))
  recovered-alive = tt

--------------------------------------------------------------------------------
-- (9) DENIABILITY IS NON-VACUOUS (F1, the load-bearing demonstration). Over a secret type with
-- TWO DISTINCT inhabitants and a CONSTANT redaction, a guest fault holding secret `one` and a
-- guest fault holding secret `two` produce the SAME host verdict: the residue reveals nothing
-- about which secret the guest held. This drives `run-deniable` with s₁ ≢ s₂ (not the trivial
-- s₁ = s₂ of UnitWitness), so it genuinely exercises the confidentiality content of SEC-1.
--------------------------------------------------------------------------------

module SecretWitness where

  data Two : Set where one two : Two

  -- Guest config carries the secret it will fault with; S = Two; redaction is constant.
  open Model Two ⊤ ⊤ ⊤ Two

  leak-runtime : FaithfulRuntime
  leak-runtime = record
    { step               = λ g _ → trapped g    -- guest faults holding its secret g : Two
    ; preCheck           = λ _ _ → ready
    ; redact             = λ _ → tt              -- CONSTANT: the public residue carries nothing
    ; Alive              = λ _ → ⊤
    ; step-continue-host = λ _ _ _ _ a → a
    ; onReturn           = λ h → h
    ; step-return-host   = λ _ _ _ _ a → a
    ; recover            = λ h → h
    ; step-trap-host     = λ _ _ _ _ a → a
    ; timeoutReason      = tt
    ; onTimeout          = λ h → h
    ; timeout-host       = λ _ a → a
    }

  -- The two secrets are genuinely distinct.
  one≢two : ¬ (one ≡ two)
  one≢two ()

  -- Yet the two faulting runs are HOST-INDISTINGUISHABLE — derived THROUGH `run-deniable`,
  -- so this is the operational deniability theorem doing real work, not a hand-built refl.
  secrets-indistinguishable :
    RunResult.verdict (run leak-runtime (suc zero) one tt)
      ≡ RunResult.verdict (run leak-runtime (suc zero) two tt)
  secrets-indistinguishable =
    run-deniable leak-runtime zero one tt two tt one two refl refl refl
