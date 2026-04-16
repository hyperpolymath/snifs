-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
--
-- ABI-1: Non-null pointer proofs for SNIF
--
-- Proves safety properties about WASM linear memory addresses used at
-- the SNIF boundary. In WASM32, pointers are 32-bit indices into linear
-- memory. All memory accesses are bounds-checked by the runtime; these
-- proofs establish that our address types cannot represent invalid states.
--
-- All proofs are constructive (no believe_me, no assert_total).

module ABI.Pointers

import Data.So
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- WASM Linear Memory Model
--------------------------------------------------------------------------------

||| WASM page size is 65536 bytes (2^16). This is a constant in the WASM spec.
public export
WasmPageSize : Nat
WasmPageSize = 65536

||| A WASM linear memory address (32-bit index).
||| Carries a proof that it is strictly less than the memory size.
public export
record WasmAddr (memSize : Nat) where
  constructor MkWasmAddr
  index : Nat
  0 inBounds : LT index memSize

||| Proof that a WasmAddr is always strictly less than the memory size.
export
wasmAddrInBounds : (addr : WasmAddr memSize) -> LT addr.index memSize
wasmAddrInBounds addr = addr.inBounds

||| Proof that if memSize > 0, then address 0 is always valid.
export
zeroAddrValid : {memSize : Nat} -> {auto 0 pos : LT 0 memSize} -> WasmAddr memSize
zeroAddrValid = MkWasmAddr 0 pos

||| Attempt to create a WasmAddr with a runtime bounds check.
||| Returns Nothing if the index is out of bounds.
export
checkAddr : (index : Nat) -> (memSize : Nat) -> Maybe (WasmAddr memSize)
checkAddr index memSize = case isLT index memSize of
  Yes prf => Just (MkWasmAddr index prf)
  No _    => Nothing

||| Proof that checkAddr with an index >= memSize returns Nothing.
||| (We prove the specific case: checkAddr n n = Nothing for all n.)
export
checkAddrOutOfBounds : (n : Nat) -> checkAddr n n = Nothing
checkAddrOutOfBounds n = rewrite ltIrrefl n in Refl
  where
    ltIrrefl : (k : Nat) -> isLT k k = No (succNotLTEpred k)
    ltIrrefl Z = Refl
    ltIrrefl (S k) = rewrite ltIrrefl k in Refl

--------------------------------------------------------------------------------
-- Non-null Pointer Safety (for host-side handles)
--------------------------------------------------------------------------------

||| A pointer value that has been proven non-null.
||| Used for wasmex GenServer PIDs and WASM instance handles on the host side.
||| The `So` constraint carries a compile-time witness that `ptr /= 0`.
public export
record SafePtr where
  constructor MkSafePtr
  ptr : Bits64
  {auto 0 nonNull : So (ptr /= 0)}

||| Proof that SafePtr can never hold a null (zero) value.
export
safePtrNeverNull : (sp : SafePtr) -> So (sp.ptr /= 0)
safePtrNeverNull sp = sp.nonNull

||| Wrap a raw pointer with a runtime null check.
||| Returns Nothing if the pointer is null.
export
checkPtr : (raw : Bits64) -> Maybe SafePtr
checkPtr 0 = Nothing
checkPtr raw = case choose (raw /= 0) of
  Left prf => Just (MkSafePtr raw)
  Right _  => Nothing

||| Proof that checkPtr 0 always returns Nothing.
export
checkPtrZeroIsNothing : checkPtr 0 = Nothing
checkPtrZeroIsNothing = Refl

--------------------------------------------------------------------------------
-- WASM Instance Handle
--------------------------------------------------------------------------------

||| An opaque handle to a WASM instance, backed by a non-null pointer.
||| Represents the wasmex GenServer PID wrapper on the host side.
||| Tagged with a phantom type for the WASM module name.
public export
record WasmHandle (moduleName : String) where
  constructor MkWasmHandle
  safePtr : SafePtr

||| Proof that two handles with equal pointers are equal.
export
wasmHandlePtrEq : (h1, h2 : WasmHandle tag) ->
                  h1.safePtr.ptr = h2.safePtr.ptr -> h1 = h2
wasmHandlePtrEq (MkWasmHandle (MkSafePtr p)) (MkWasmHandle (MkSafePtr p)) Refl = Refl

--------------------------------------------------------------------------------
-- Bounded Memory Region
--------------------------------------------------------------------------------

||| A contiguous region within WASM linear memory.
||| Carries proofs that both start and start+length are within bounds.
public export
record MemRegion (memSize : Nat) where
  constructor MkMemRegion
  start  : Nat
  length : Nat
  0 startInBounds : LT start memSize
  0 endInBounds   : LTE (start + length) memSize

||| Proof that an empty region at a valid address is always valid.
export
emptyRegionValid : {memSize : Nat} -> (addr : WasmAddr memSize) ->
                   MemRegion memSize
emptyRegionValid (MkWasmAddr idx prf) =
  MkMemRegion idx 0 prf (rewrite plusZeroRightNeutral idx in lteSuccLeft prf)

||| Proof that the length of a MemRegion never exceeds memSize.
export
regionLengthBounded : (r : MemRegion memSize) -> LTE r.length memSize
regionLengthBounded (MkMemRegion start length startInBounds endInBounds) =
  lteTransitive (lteAddLeft start) endInBounds
