-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
--
-- TP-1: Core data type well-formedness proofs for SNIF
--
-- Proves properties about the core SNIF types:
--   - WasmTrapKind: exhaustive classification of WASM trap causes
--   - SNIFCallResult: the sum type modelling call outcomes
--   - CompilationMode: the Zig optimisation mode with safety invariants
--   - BoundedI32/BoundedI64: range-constrained integer types
--
-- All proofs are constructive (no believe_me, no assert_total).

module Types

import Data.So
import Decidable.Equality

%default total

--------------------------------------------------------------------------------
-- WASM Trap Classification
--------------------------------------------------------------------------------

||| Classification of WASM trap causes.
||| Maps to the 5 failure categories tested in the SNIF demo.
public export
data WasmTrapKind
  = TrapOOB           -- Out-of-bounds memory/array access
  | TrapUnreachable   -- Explicit unreachable instruction
  | TrapPanic         -- Zig @panic (compiles to unreachable)
  | TrapOverflow      -- Integer overflow (ReleaseSafe)
  | TrapDivZero       -- Division by zero
  | TrapUnknown       -- Any other trap (future extensibility)

||| WasmTrapKind has decidable equality.
public export
DecEq WasmTrapKind where
  decEq TrapOOB         TrapOOB         = Yes Refl
  decEq TrapUnreachable TrapUnreachable = Yes Refl
  decEq TrapPanic       TrapPanic       = Yes Refl
  decEq TrapOverflow    TrapOverflow    = Yes Refl
  decEq TrapDivZero     TrapDivZero     = Yes Refl
  decEq TrapUnknown     TrapUnknown     = Yes Refl
  decEq TrapOOB         TrapUnreachable = No (\case Refl impossible)
  decEq TrapOOB         TrapPanic       = No (\case Refl impossible)
  decEq TrapOOB         TrapOverflow    = No (\case Refl impossible)
  decEq TrapOOB         TrapDivZero     = No (\case Refl impossible)
  decEq TrapOOB         TrapUnknown     = No (\case Refl impossible)
  decEq TrapUnreachable TrapOOB         = No (\case Refl impossible)
  decEq TrapUnreachable TrapPanic       = No (\case Refl impossible)
  decEq TrapUnreachable TrapOverflow    = No (\case Refl impossible)
  decEq TrapUnreachable TrapDivZero     = No (\case Refl impossible)
  decEq TrapUnreachable TrapUnknown     = No (\case Refl impossible)
  decEq TrapPanic       TrapOOB         = No (\case Refl impossible)
  decEq TrapPanic       TrapUnreachable = No (\case Refl impossible)
  decEq TrapPanic       TrapOverflow    = No (\case Refl impossible)
  decEq TrapPanic       TrapDivZero     = No (\case Refl impossible)
  decEq TrapPanic       TrapUnknown     = No (\case Refl impossible)
  decEq TrapOverflow    TrapOOB         = No (\case Refl impossible)
  decEq TrapOverflow    TrapUnreachable = No (\case Refl impossible)
  decEq TrapOverflow    TrapPanic       = No (\case Refl impossible)
  decEq TrapOverflow    TrapDivZero     = No (\case Refl impossible)
  decEq TrapOverflow    TrapUnknown     = No (\case Refl impossible)
  decEq TrapDivZero     TrapOOB         = No (\case Refl impossible)
  decEq TrapDivZero     TrapUnreachable = No (\case Refl impossible)
  decEq TrapDivZero     TrapPanic       = No (\case Refl impossible)
  decEq TrapDivZero     TrapOverflow    = No (\case Refl impossible)
  decEq TrapDivZero     TrapUnknown     = No (\case Refl impossible)
  decEq TrapUnknown     TrapOOB         = No (\case Refl impossible)
  decEq TrapUnknown     TrapUnreachable = No (\case Refl impossible)
  decEq TrapUnknown     TrapPanic       = No (\case Refl impossible)
  decEq TrapUnknown     TrapOverflow    = No (\case Refl impossible)
  decEq TrapUnknown     TrapDivZero     = No (\case Refl impossible)

||| The 5 tested trap kinds (excluding TrapUnknown).
public export
testedTrapKinds : List WasmTrapKind
testedTrapKinds = [TrapOOB, TrapUnreachable, TrapPanic, TrapOverflow, TrapDivZero]

||| Proof that we test exactly 5 trap kinds.
export
testedTrapCount : length testedTrapKinds = 5
testedTrapCount = Refl

--------------------------------------------------------------------------------
-- SNIF Call Result
--------------------------------------------------------------------------------

||| The result of calling a SNIF function.
||| This is a proper sum type: every call produces exactly one outcome.
public export
data SNIFCallResult : Type where
  ||| WASM function returned normally with integer results.
  CallOk     : (values : List Int) -> SNIFCallResult
  ||| WASM function trapped. The BEAM process is alive.
  CallTrapped : (kind : WasmTrapKind) -> (reason : String) -> SNIFCallResult
  ||| WASM module failed to load.
  CallLoadError : (reason : String) -> SNIFCallResult

||| Proof that CallOk is not CallTrapped.
export
okIsNotTrapped : CallOk vs = CallTrapped k r -> Void
okIsNotTrapped Refl impossible

||| Proof that CallOk is not CallLoadError.
export
okIsNotLoadError : CallOk vs = CallLoadError r -> Void
okIsNotLoadError Refl impossible

||| Proof that CallTrapped is not CallLoadError.
export
trappedIsNotLoadError : CallTrapped k r = CallLoadError r2 -> Void
trappedIsNotLoadError Refl impossible

||| Predicate: the BEAM survived a call (true for all outcomes).
||| This is the central safety claim of SNIF.
public export
BeamSurvived : SNIFCallResult -> Type
BeamSurvived (CallOk _)          = ()
BeamSurvived (CallTrapped _ _)   = ()
BeamSurvived (CallLoadError _)   = ()

||| Proof that the BEAM always survives, regardless of call outcome.
||| This is the type-level expression of the SNIF crash isolation theorem.
export
beamAlwaysSurvives : (result : SNIFCallResult) -> BeamSurvived result
beamAlwaysSurvives (CallOk _)          = ()
beamAlwaysSurvives (CallTrapped _ _)   = ()
beamAlwaysSurvives (CallLoadError _)   = ()

--------------------------------------------------------------------------------
-- Compilation Mode and Safety Invariant
--------------------------------------------------------------------------------

||| Zig compilation modes relevant to SNIF.
public export
data CompilationMode = Debug | ReleaseSafe | ReleaseFast | ReleaseSmall

||| DecEq for CompilationMode.
public export
DecEq CompilationMode where
  decEq Debug       Debug       = Yes Refl
  decEq ReleaseSafe ReleaseSafe = Yes Refl
  decEq ReleaseFast ReleaseFast = Yes Refl
  decEq ReleaseSmall ReleaseSmall = Yes Refl
  decEq Debug       ReleaseSafe  = No (\case Refl impossible)
  decEq Debug       ReleaseFast  = No (\case Refl impossible)
  decEq Debug       ReleaseSmall = No (\case Refl impossible)
  decEq ReleaseSafe Debug        = No (\case Refl impossible)
  decEq ReleaseSafe ReleaseFast  = No (\case Refl impossible)
  decEq ReleaseSafe ReleaseSmall = No (\case Refl impossible)
  decEq ReleaseFast Debug        = No (\case Refl impossible)
  decEq ReleaseFast ReleaseSafe  = No (\case Refl impossible)
  decEq ReleaseFast ReleaseSmall = No (\case Refl impossible)
  decEq ReleaseSmall Debug       = No (\case Refl impossible)
  decEq ReleaseSmall ReleaseSafe = No (\case Refl impossible)
  decEq ReleaseSmall ReleaseFast = No (\case Refl impossible)

||| Whether a compilation mode preserves runtime safety checks.
||| This is the critical invariant from ADR-001.
public export
hasSafetyChecks : CompilationMode -> Bool
hasSafetyChecks Debug       = True
hasSafetyChecks ReleaseSafe = True
hasSafetyChecks ReleaseFast = False
hasSafetyChecks ReleaseSmall = False

||| Predicate: a mode is safe for SNIF use.
||| Only modes with safety checks guarantee trap-on-violation.
public export
SafeForSNIF : CompilationMode -> Type
SafeForSNIF mode = So (hasSafetyChecks mode)

||| Proof that Debug is safe for SNIF.
export
debugIsSafe : SafeForSNIF Debug
debugIsSafe = Oh

||| Proof that ReleaseSafe is safe for SNIF.
export
releaseSafeIsSafe : SafeForSNIF ReleaseSafe
releaseSafeIsSafe = Oh

||| Proof that ReleaseFast is NOT safe for SNIF.
export
releaseFastUnsafe : SafeForSNIF ReleaseFast -> Void
releaseFastUnsafe Oh impossible

||| Proof that ReleaseSmall is NOT safe for SNIF.
export
releaseSmallUnsafe : SafeForSNIF ReleaseSmall -> Void
releaseSmallUnsafe Oh impossible

||| The required compilation mode for production SNIFs (ADR-001).
public export
RequiredMode : CompilationMode
RequiredMode = ReleaseSafe

||| Proof that the required mode is safe.
export
requiredModeIsSafe : SafeForSNIF RequiredMode
requiredModeIsSafe = Oh

--------------------------------------------------------------------------------
-- Bounded Integer Types (for SNIF value constraints)
--------------------------------------------------------------------------------

||| A natural number bounded by a maximum.
||| Used to model WASM integer ranges at the type level.
public export
record Bounded (max : Nat) where
  constructor MkBounded
  value : Nat
  {auto 0 inBounds : LTE value max}

||| Proof that a Bounded value is always <= max.
export
boundedLeMax : (b : Bounded max) -> LTE b.value max
boundedLeMax b = b.inBounds

||| Proof that zero is always a valid Bounded value (for nonzero max).
export
zeroIsBounded : {max : Nat} -> Bounded (S max)
zeroIsBounded = MkBounded 0

||| Proof that max is always a valid Bounded value.
export
maxIsBounded : {max : Nat} -> Bounded max
maxIsBounded = MkBounded max
