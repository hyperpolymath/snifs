-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
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
  -- un-erased: required for constructive proof of wasmAddrInBounds
  inBounds : LT index memSize

||| Proof that a WasmAddr is always strictly less than the memory size.
export
wasmAddrInBounds : (addr : WasmAddr memSize) -> LT addr.index memSize
wasmAddrInBounds addr = addr.inBounds

||| Proof that if memSize > 0, then address 0 is always valid.
||| memSize must be (S k) for `LT 0 memSize` to be inhabited; the Z case is
||| absurd (its erased `pos : LT 0 Z` is uninhabited) so coverage stays total.
export
zeroAddrValid : {memSize : Nat} -> {auto 0 pos : LT 0 memSize} -> WasmAddr memSize
zeroAddrValid {memSize = (S k)} = MkWasmAddr 0 (LTESucc LTEZero)

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
checkAddrOutOfBounds n with (isLT n n)
  checkAddrOutOfBounds n | Yes prf = absurd (succNotLTEpred prf)
  checkAddrOutOfBounds n | No _    = Refl

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
  -- un-erased: required for constructive proof of safePtrNeverNull
  {auto nonNull : So (ptr /= 0)}

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

||| So-proofs over the same boolean are unique (proof irrelevance for So).
||| Needed because SafePtr now carries an un-erased nonNull witness.
export
soUnique : (x, y : So b) -> x = y
soUnique Oh Oh = Refl

||| Proof that two handles with equal pointers are equal.
export
wasmHandlePtrEq : (h1, h2 : WasmHandle tag) ->
                  h1.safePtr.ptr = h2.safePtr.ptr -> h1 = h2
wasmHandlePtrEq (MkWasmHandle (MkSafePtr p {nonNull = n1}))
                (MkWasmHandle (MkSafePtr q {nonNull = n2})) prf =
  case prf of
    Refl => rewrite soUnique n1 n2 in Refl

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
  -- un-erased: required for constructive proof of regionLengthBounded
  endInBounds   : LTE (start + length) memSize

||| Proof that an empty region at a valid address is always valid.
export
emptyRegionValid : {memSize : Nat} -> (addr : WasmAddr memSize) ->
                   MemRegion memSize
emptyRegionValid (MkWasmAddr idx prf) =
  MkMemRegion idx 0 prf (rewrite plusZeroRightNeutral idx in lteSuccLeft prf)

||| Proof that the length of a MemRegion never exceeds memSize.
||| length <= start + length (lteAddLeft) and start + length <= memSize
||| (endInBounds), so by transitivity length <= memSize.
export
regionLengthBounded : (r : MemRegion memSize) -> LTE r.length memSize
regionLengthBounded (MkMemRegion start length startInBounds endInBounds) =
  lteTrans (lteAddLeft start length) endInBounds
  where
    lteAddLeft : (s, l : Nat) -> LTE l (s + l)
    lteAddLeft s l = rewrite plusCommutative s l in lteAddRight l
    lteTrans : LTE a b -> LTE b c -> LTE a c
    lteTrans LTEZero _ = LTEZero
    lteTrans (LTESucc xy) (LTESucc yz) = LTESucc (lteTrans xy yz)
