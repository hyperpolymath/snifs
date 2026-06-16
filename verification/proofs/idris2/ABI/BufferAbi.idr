-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
--
-- ABI-7: FFI signature proofs for the SNIF Buffer ABI v1 guest (zig/src/buffer_abi.zig).
--
-- Companion to ABI.Foreign (which models the 8 safe_nif crash/compute exports). The buffer
-- guest's exports cross the (ptr,len) marshalling boundary and — crucially — three of them
-- RETURN VOID (snif_dealloc, snif_reset, scale_f32). The single-value `WasmFuncSpec` of
-- ABI.Foreign cannot express a void return, so this module uses a WASM-faithful MULTI-VALUE
-- signature record (`resultTypes : List WasmValType`, where `[]` = void, `[t]` = one result).
--
-- Each spec records the WASM-level signature (i32/i64/f32/f64) of an export, exactly as it
-- appears in the built `buffer_abi_ReleaseSafe.wasm`. The Python conformance gate
-- (verification/tools/abi_conformance.py, "buffer_abi" guest) parses these specs and FAILS if
-- the built artifact's real signatures drift from this verified model.
--
-- SCOPE (honest): like ABI.Foreign this verifies the INTERFACE (names, params, results), not
-- BEHAVIOUR (that sum_f32 truly sums) — that is the metamorphic gate (GAP-1b). The pointer
-- SEMANTICS of the (ptr,len) words (in-bounds, ownership) are the deeper ABI-6 array-marshalling
-- obligation and are deliberately NOT claimed here: at the wasm signature level a `usize` is an
-- `i32` and that is all this gate asserts.
--
-- All proofs are constructive (no believe_me, no assert_total).

module ABI.BufferAbi

import ABI.Layout
import Data.List

%default total

--------------------------------------------------------------------------------
-- WASM multi-value function signature (void-faithful)
--------------------------------------------------------------------------------

||| Specification of a WASM exported function with MULTI-VALUE results.
||| `resultTypes = []` models a void return; `[t]` a single result; `[t,u,..]`
||| the WASM multi-value case. This is strictly more faithful than ABI.Foreign's
||| single `returnType`, which the safe_nif guest (no void exports) did not need.
public export
record WasmSig where
  constructor MkWasmSig
  funcName    : String
  paramTypes  : List WasmValType
  resultTypes : List WasmValType

||| Proof that a signature has specific result types (`[]` = void).
public export
Returns : WasmSig -> List WasmValType -> Type
Returns sig rs = resultTypes sig = rs

||| Proof that a signature has a specific number of parameters.
public export
HasArity : WasmSig -> Nat -> Type
HasArity sig n = length (paramTypes sig) = n

||| Proof that a signature returns void (no results).
public export
IsVoid : WasmSig -> Type
IsVoid sig = resultTypes sig = []

--------------------------------------------------------------------------------
-- Buffer ABI export specifications (matching zig/src/buffer_abi.zig, wasm-level)
--------------------------------------------------------------------------------

||| snif_alloc(len: usize) -> usize        (i32) -> i32   — bump-allocate a scratch region
public export
specSnifAlloc : WasmSig
specSnifAlloc = MkWasmSig "snif_alloc" [I32] [I32]

||| snif_dealloc(ptr: usize, len: usize) -> void   (i32 i32) -> ()
public export
specSnifDealloc : WasmSig
specSnifDealloc = MkWasmSig "snif_dealloc" [I32, I32] []

||| snif_reset() -> void    () -> ()   — reset the bump allocator
public export
specSnifReset : WasmSig
specSnifReset = MkWasmSig "snif_reset" [] []

||| sum_f32(ptr: usize, n: usize) -> f32    (i32 i32) -> f32
public export
specSumF32 : WasmSig
specSumF32 = MkWasmSig "sum_f32" [I32, I32] [F32]

||| scale_f32(ptr: usize, n: usize, k: f32) -> void    (i32 i32 f32) -> ()  — in place
public export
specScaleF32 : WasmSig
specScaleF32 = MkWasmSig "scale_f32" [I32, I32, F32] []

||| still_alive() -> i32    () -> i32   — liveness probe (shared name with safe_nif)
public export
specStillAlive : WasmSig
specStillAlive = MkWasmSig "still_alive" [] [I32]

||| crash_oob_buffer(ptr: usize, n: usize) -> f32    (i32 i32) -> f32  — traps OOB under ReleaseSafe
public export
specCrashOobBuffer : WasmSig
specCrashOobBuffer = MkWasmSig "crash_oob_buffer" [I32, I32] [F32]

||| All 7 buffer-ABI exports as a list.
public export
allBufferExports : List WasmSig
allBufferExports =
  [ specSnifAlloc, specSnifDealloc, specSnifReset
  , specSumF32, specScaleF32
  , specStillAlive, specCrashOobBuffer
  ]

--------------------------------------------------------------------------------
-- Count
--------------------------------------------------------------------------------

||| Proof that we model exactly 7 buffer-ABI exports.
export
bufferExportCount : length BufferAbi.allBufferExports = 7
bufferExportCount = Refl

--------------------------------------------------------------------------------
-- Result-type proofs (value-returning AND void)
--------------------------------------------------------------------------------

export
snifAllocReturnsI32 : Returns BufferAbi.specSnifAlloc [I32]
snifAllocReturnsI32 = Refl

export
sumF32ReturnsF32 : Returns BufferAbi.specSumF32 [F32]
sumF32ReturnsF32 = Refl

export
crashOobBufferReturnsF32 : Returns BufferAbi.specCrashOobBuffer [F32]
crashOobBufferReturnsF32 = Refl

export
stillAliveReturnsI32 : Returns BufferAbi.specStillAlive [I32]
stillAliveReturnsI32 = Refl

||| The three void-returning exports — representable only because results are a List.
export
snifDeallocIsVoid : IsVoid BufferAbi.specSnifDealloc
snifDeallocIsVoid = Refl

export
snifResetIsVoid : IsVoid BufferAbi.specSnifReset
snifResetIsVoid = Refl

export
scaleF32IsVoid : IsVoid BufferAbi.specScaleF32
scaleF32IsVoid = Refl

--------------------------------------------------------------------------------
-- Arity proofs
--------------------------------------------------------------------------------

export
snifAllocArity1 : HasArity BufferAbi.specSnifAlloc 1
snifAllocArity1 = Refl

export
snifDeallocArity2 : HasArity BufferAbi.specSnifDealloc 2
snifDeallocArity2 = Refl

export
snifResetArity0 : HasArity BufferAbi.specSnifReset 0
snifResetArity0 = Refl

export
sumF32Arity2 : HasArity BufferAbi.specSumF32 2
sumF32Arity2 = Refl

export
scaleF32Arity3 : HasArity BufferAbi.specScaleF32 3
scaleF32Arity3 = Refl

export
stillAliveArity0 : HasArity BufferAbi.specStillAlive 0
stillAliveArity0 = Refl

export
crashOobBufferArity2 : HasArity BufferAbi.specCrashOobBuffer 2
crashOobBufferArity2 = Refl
