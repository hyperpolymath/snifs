{-# OPTIONS --safe --without-K #-}

-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- SnifVerdict — a tropical-free safety/security model for SNIF (Safer NIF) verdicts.
--
-- DRAFT (2026-06-16). Bridges the two QUALITATIVE cores identified with the owner:
--   * echo-types  `EchoDeniability.IsDeniable`  — the LOSS / TRACE side: "the guest's
--     information is gone, and you cannot recover which history produced the residue".
--     Gives CONFIDENTIALITY (the trapped guest's secret state does not leak).
--   * epistemic-types `BeliefModality` (NO `reflect`) — the NOT-HOLDING side: "the host
--     holds no guest value". Gives NON-FORGERY / integrity (a trapped guest cannot hand
--     the host a value).
--
-- Neither core needs the tropical grade: crash-isolation, non-forgery and restricted
-- deniability are all STRUCTURAL. (Tropical re-enters only for the cost/liveness view —
-- "how much was lost", fuel bounds — which is deliberately absent here.)
--
-- Self-contained (only Agda.Builtin.Equality) so it `agda --safe --without-K`-checks with
-- no library. Upstream homes for the generic versions:
--   echo-types/proofs/agda/EchoDeniability.agda  (IsDeniable, perfect/partial spectrum)
--   epistemic-types/src/EpistemicTypes/{Base,EchoBridge}.agda  (Factive vs Belief modality)

module SnifVerdict where

open import Agda.Builtin.Equality using (_≡_; refl)

data ⊥ : Set where
record ⊤ : Set where constructor tt

¬_ : Set → Set
¬ A = A → ⊥

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

--------------------------------------------------------------------------------
-- The guest outcome (private) and the host-observable verdict (public).
--------------------------------------------------------------------------------

-- A guest either returned a value of type A, or faulted while holding some secret
-- internal state of type S (linear memory, inputs, partial work).
data Outcome (A S : Set) : Set where
  ran     : A → Outcome A S
  faulted : S → Outcome A S

-- The host verdict carries a value (ok) or a PUBLIC reason of type R (trap).
-- Crucially `trap` never carries S: the secret cannot cross the cleave surface.
data Verdict (A R : Set) : Set where
  ok   : A → Verdict A R
  trap : R → Verdict A R

-- The SNIF boundary. A fault's secret is REDACTED to a public reason via `redact`,
-- the only channel from guest secret to host-visible residue.
observe : {A R S : Set} (redact : S → R) → Outcome A S → Verdict A R
observe redact (ran a)     = ok a
observe redact (faulted s) = trap (redact s)

--------------------------------------------------------------------------------
-- (1) CRASH ISOLATION — every verdict is ok-or-trap (the {:ok,_} | {:error,_} ⊕).
--------------------------------------------------------------------------------

data IsOk   {A R : Set} : Verdict A R → Set where isOk   : (a : A) → IsOk   (ok a)
data IsTrap {A R : Set} : Verdict A R → Set where isTrap : (r : R) → IsTrap (trap r)

dichotomy : {A R : Set} (v : Verdict A R) → IsOk v ⊎ IsTrap v
dichotomy (ok a)   = inl (isOk a)
dichotomy (trap r) = inr (isTrap r)

--------------------------------------------------------------------------------
-- (2) NON-FORGERY / non-factivity (epistemic BeliefModality: there is no `reflect`).
--     No total extractor `Verdict A R → A` exists: a trapped guest cannot hand the
--     host a value. Proof: instantiate A = ⊥; `trap tt : Verdict ⊥ ⊤` would yield ⊥.
--------------------------------------------------------------------------------

no-reflect : (∀ {A R : Set} → Verdict A R → A) → ⊥
no-reflect extract = extract {⊥} {⊤} (trap tt)

--------------------------------------------------------------------------------
-- (3) RESTRICTED DENIABILITY (echo EchoDeniability.IsDeniable): the guest secret is
--     recoverable from the verdict only up to `redact`. Two faults whose secrets
--     redact equally yield the SAME verdict, so no host opener can distinguish them.
--------------------------------------------------------------------------------

deniable-upto-redaction : {A R S : Set} (redact : S → R) (s₁ s₂ : S) →
                          redact s₁ ≡ redact s₂ →
                          observe {A = A} redact (faulted s₁) ≡ observe {A = A} redact (faulted s₂)
deniable-upto-redaction redact s₁ s₂ eq = cong trap eq

-- Perfect deniability (echo `produce-perfect`): a CONSTANT redaction (the reason carries
-- nothing of the secret) makes every fault indistinguishable — full confidentiality.
perfect-deniable : {A R S : Set} (c : R) (s₁ s₂ : S) →
                   observe {A = A} (λ _ → c) (faulted s₁) ≡ observe {A = A} (λ _ → c) (faulted s₂)
perfect-deniable c s₁ s₂ = refl

-- Any external opener `d` that reads the verdict learns nothing of S beyond `redact`:
-- it agrees on faults that redact equally. (The host, a privileged opener, may still
-- read the public reason R — the echo `partial-deniable-restricted` cut-point.)
opener-cannot-distinguish : {A R S : Set} (redact : S → R) (d : Verdict A R → S)
                            (s₁ s₂ : S) → redact s₁ ≡ redact s₂ →
                            d (observe {A = A} redact (faulted s₁))
                              ≡ d (observe {A = A} redact (faulted s₂))
opener-cannot-distinguish redact d s₁ s₂ eq = cong d (cong trap eq)

--------------------------------------------------------------------------------
-- BRIDGE THEOREM (informal): for every SNIF call,
--   `dichotomy`                 — the host lands in ok ⊕ trap            (crash isolation)
--   `no-reflect`                — the trap branch yields no guest value   (non-forgery / integrity)
--   `deniable-upto-redaction`   — the trap residue hides the secret       (non-leak / confidentiality)
-- All three are tropical-free. The cost grade (how much was lost / fuel) is a SEPARATE,
-- optional view and is intentionally not imported here.
--------------------------------------------------------------------------------
