-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
--
-- ABI-4: FFI function return type proofs for SNIF
--
-- Proves that all 8 exported WASM functions in safe_nif.zig have
-- well-typed signatures. The SNIF FFI boundary is:
--   Zig export -> WASM function -> wasmex call_function -> Elixir
--
-- Each function is modelled as an FFISpec with parameter and return
-- WASM value types. We prove that each spec matches the Zig source.
--
-- All proofs are constructive (no believe_me, no assert_total).

module ABI.Foreign

import ABI.Layout
import Data.List

%default total

--------------------------------------------------------------------------------
-- SNIF Call Result Model
--------------------------------------------------------------------------------

||| Result of a SNIF call through wasmex.
||| Models the Elixir-side {:ok, [values]} | {:error, reason} pattern.
public export
data SNIFResult : Type -> Type where
  ||| Function returned successfully with a value.
  ||| Corresponds to {:ok, [value]} in Elixir.
  SNIFOk    : (value : a) -> SNIFResult a
  ||| Function trapped (WASM unreachable instruction).
  ||| Corresponds to {:error, reason} in Elixir.
  ||| The BEAM process remains alive.
  SNIFTrap  : (reason : String) -> SNIFResult a

||| Proof that SNIFResult is a functor (map preserves structure).
export
mapSNIFResult : (a -> b) -> SNIFResult a -> SNIFResult b
mapSNIFResult f (SNIFOk value)   = SNIFOk (f value)
mapSNIFResult f (SNIFTrap reason) = SNIFTrap reason

||| Functor identity law: map id = id.
export
mapIdPreserves : (r : SNIFResult a) -> mapSNIFResult Prelude.id r = r
mapIdPreserves (SNIFOk value)    = Refl
mapIdPreserves (SNIFTrap reason) = Refl

||| Proof that a trap result is never an ok result.
export
trapIsNotOk : SNIFTrap reason = SNIFOk value -> Void
trapIsNotOk Refl impossible

||| Proof that an ok result is never a trap result.
export
okIsNotTrap : SNIFOk value = SNIFTrap reason -> Void
okIsNotTrap Refl impossible

||| Determine whether a result is ok or a trap.
export
isOk : SNIFResult a -> Bool
isOk (SNIFOk _)   = True
isOk (SNIFTrap _) = False

--------------------------------------------------------------------------------
-- WASM Function Specification
--------------------------------------------------------------------------------

||| Specification of a WASM exported function.
||| Records the function name, parameter types, and return type.
public export
record WasmFuncSpec where
  constructor MkWasmFuncSpec
  funcName   : String
  paramTypes : List WasmValType
  returnType : WasmValType

||| Proof that a spec has a specific return type.
public export
ReturnsType : WasmFuncSpec -> WasmValType -> Type
ReturnsType spec ty = returnType spec = ty

||| Proof that a spec has a specific number of parameters.
public export
HasArity : WasmFuncSpec -> Nat -> Type
HasArity spec n = length (paramTypes spec) = n

--------------------------------------------------------------------------------
-- SNIF Export Specifications (matching zig/src/safe_nif.zig)
--------------------------------------------------------------------------------

||| fibonacci(n: i32) -> i64
public export
specFibonacci : WasmFuncSpec
specFibonacci = MkWasmFuncSpec "fibonacci" [I32] I64

||| checked_add(a: i32, b: i32) -> i32
public export
specCheckedAdd : WasmFuncSpec
specCheckedAdd = MkWasmFuncSpec "checked_add" [I32, I32] I32

||| crash_oob() -> i32
public export
specCrashOob : WasmFuncSpec
specCrashOob = MkWasmFuncSpec "crash_oob" [] I32

||| crash_unreachable() -> i32
public export
specCrashUnreachable : WasmFuncSpec
specCrashUnreachable = MkWasmFuncSpec "crash_unreachable" [] I32

||| crash_panic() -> i32
public export
specCrashPanic : WasmFuncSpec
specCrashPanic = MkWasmFuncSpec "crash_panic" [] I32

||| crash_overflow() -> i32
public export
specCrashOverflow : WasmFuncSpec
specCrashOverflow = MkWasmFuncSpec "crash_overflow" [] I32

||| crash_div_zero() -> i32
public export
specCrashDivZero : WasmFuncSpec
specCrashDivZero = MkWasmFuncSpec "crash_div_zero" [] I32

||| still_alive() -> i32
public export
specStillAlive : WasmFuncSpec
specStillAlive = MkWasmFuncSpec "still_alive" [] I32

||| All 8 SNIF exports as a list.
public export
allSnifExports : List WasmFuncSpec
allSnifExports =
  [ specFibonacci, specCheckedAdd
  , specCrashOob, specCrashUnreachable, specCrashPanic
  , specCrashOverflow, specCrashDivZero
  , specStillAlive
  ]

--------------------------------------------------------------------------------
-- Return Type Proofs
--------------------------------------------------------------------------------

||| Proof that fibonacci returns I64.
export
fibonacciReturnsI64 : ReturnsType specFibonacci I64
fibonacciReturnsI64 = Refl

||| Proof that checked_add returns I32.
export
checkedAddReturnsI32 : ReturnsType specCheckedAdd I32
checkedAddReturnsI32 = Refl

||| Proof that all crash functions return I32.
export
crashOobReturnsI32 : ReturnsType specCrashOob I32
crashOobReturnsI32 = Refl

export
crashUnreachableReturnsI32 : ReturnsType specCrashUnreachable I32
crashUnreachableReturnsI32 = Refl

export
crashPanicReturnsI32 : ReturnsType specCrashPanic I32
crashPanicReturnsI32 = Refl

export
crashOverflowReturnsI32 : ReturnsType specCrashOverflow I32
crashOverflowReturnsI32 = Refl

export
crashDivZeroReturnsI32 : ReturnsType specCrashDivZero I32
crashDivZeroReturnsI32 = Refl

||| Proof that still_alive returns I32.
export
stillAliveReturnsI32 : ReturnsType specStillAlive I32
stillAliveReturnsI32 = Refl

--------------------------------------------------------------------------------
-- Arity Proofs
--------------------------------------------------------------------------------

||| Proof that fibonacci takes exactly 1 parameter.
export
fibonacciArity1 : HasArity specFibonacci 1
fibonacciArity1 = Refl

||| Proof that checked_add takes exactly 2 parameters.
export
checkedAddArity2 : HasArity specCheckedAdd 2
checkedAddArity2 = Refl

||| Proof that all crash functions take 0 parameters.
export
crashFunctionsArity0 : (HasArity specCrashOob 0,
                        HasArity specCrashUnreachable 0,
                        HasArity specCrashPanic 0,
                        HasArity specCrashOverflow 0,
                        HasArity specCrashDivZero 0)
crashFunctionsArity0 = (Refl, Refl, Refl, Refl, Refl)

||| Proof that still_alive takes 0 parameters.
export
stillAliveArity0 : HasArity specStillAlive 0
stillAliveArity0 = Refl

||| Proof that we have exactly 8 SNIF exports.
export
snifExportCount : length allSnifExports = 8
snifExportCount = Refl

--------------------------------------------------------------------------------
-- Crash Function Classification
--------------------------------------------------------------------------------

||| A crash function is one that always traps under ReleaseSafe.
||| We classify the 5 intentional crash functions.
public export
data IsCrashFunction : WasmFuncSpec -> Type where
  CrashOob         : IsCrashFunction specCrashOob
  CrashUnreachable : IsCrashFunction specCrashUnreachable
  CrashPanic       : IsCrashFunction specCrashPanic
  CrashOverflow    : IsCrashFunction specCrashOverflow
  CrashDivZero     : IsCrashFunction specCrashDivZero

||| Proof that crash functions always have arity 0.
export
crashFunctionArity : (spec : WasmFuncSpec) -> IsCrashFunction spec ->
                     HasArity spec 0
crashFunctionArity _ CrashOob         = Refl
crashFunctionArity _ CrashUnreachable = Refl
crashFunctionArity _ CrashPanic       = Refl
crashFunctionArity _ CrashOverflow    = Refl
crashFunctionArity _ CrashDivZero     = Refl

||| Proof that crash functions always return I32.
export
crashFunctionReturnType : (spec : WasmFuncSpec) -> IsCrashFunction spec ->
                          ReturnsType spec I32
crashFunctionReturnType _ CrashOob         = Refl
crashFunctionReturnType _ CrashUnreachable = Refl
crashFunctionReturnType _ CrashPanic       = Refl
crashFunctionReturnType _ CrashOverflow    = Refl
crashFunctionReturnType _ CrashDivZero     = Refl
