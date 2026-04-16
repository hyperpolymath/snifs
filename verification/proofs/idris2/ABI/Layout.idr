-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
--
-- ABI-2: Memory layout correctness for SNIF
--
-- Proves that WASM value types used at the SNIF boundary have correct
-- sizes, alignments, and padding properties. WASM defines four value
-- types (i32, i64, f32, f64); SNIF exports currently use i32 and i64.
--
-- All proofs are constructive (no believe_me, no assert_total).

module ABI.Layout

%default total

--------------------------------------------------------------------------------
-- WASM Value Types
--------------------------------------------------------------------------------

||| The four WASM MVP value types.
||| SNIF exports use I32 (for crash functions, checked_add, still_alive)
||| and I64 (for fibonacci).
public export
data WasmValType = I32 | I64 | F32 | F64

||| Size in bytes of each WASM value type.
||| These are fixed by the WASM specification.
public export
wasmValSize : WasmValType -> Nat
wasmValSize I32 = 4
wasmValSize I64 = 8
wasmValSize F32 = 4
wasmValSize F64 = 8

||| Natural alignment of each WASM value type.
||| WASM linear memory is byte-addressable; these are the natural alignments.
public export
wasmValAlign : WasmValType -> Nat
wasmValAlign I32 = 4
wasmValAlign I64 = 8
wasmValAlign F32 = 4
wasmValAlign F64 = 8

--------------------------------------------------------------------------------
-- Size and Alignment Proofs
--------------------------------------------------------------------------------

||| Witness that a type has a known size in bytes at compile time.
public export
interface HasSize (ty : Type) where
  sizeOf : Nat

||| Witness that a type has a known alignment in bytes.
public export
interface HasAlignment (ty : Type) where
  alignOf : Nat

||| Proof that all WASM value type sizes are either 4 or 8 bytes.
export
wasmValSizeValid : (t : WasmValType) -> Either (wasmValSize t = 4) (wasmValSize t = 8)
wasmValSizeValid I32 = Left Refl
wasmValSizeValid I64 = Right Refl
wasmValSizeValid F32 = Left Refl
wasmValSizeValid F64 = Right Refl

||| Proof that WASM value alignment always equals size (naturally aligned).
export
wasmValNaturallyAligned : (t : WasmValType) -> wasmValAlign t = wasmValSize t
wasmValNaturallyAligned I32 = Refl
wasmValNaturallyAligned I64 = Refl
wasmValNaturallyAligned F32 = Refl
wasmValNaturallyAligned F64 = Refl

||| Proof that all WASM value sizes are at least 4 bytes.
export
wasmValSizeAtLeast4 : (t : WasmValType) -> LTE 4 (wasmValSize t)
wasmValSizeAtLeast4 I32 = lteRefl
wasmValSizeAtLeast4 I64 = lteSuccRight (lteSuccRight (lteSuccRight (lteSuccRight lteRefl)))
wasmValSizeAtLeast4 F32 = lteRefl
wasmValSizeAtLeast4 F64 = lteSuccRight (lteSuccRight (lteSuccRight (lteSuccRight lteRefl)))

||| Proof that all WASM value sizes are positive (> 0).
export
wasmValSizePositive : (t : WasmValType) -> LT 0 (wasmValSize t)
wasmValSizePositive I32 = LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))
wasmValSizePositive I64 = LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))
wasmValSizePositive F32 = LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))
wasmValSizePositive F64 = LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))

--------------------------------------------------------------------------------
-- Padding and Alignment Arithmetic
--------------------------------------------------------------------------------

||| Calculate padding needed to reach the next aligned offset.
||| paddingFor offset alignment = bytes to add so (offset + padding) `mod` alignment == 0
public export
paddingFor : (offset : Nat) -> (alignment : Nat) -> {auto 0 ok : NonZero alignment} -> Nat
paddingFor offset alignment = let r = modNatNZ offset alignment ok
                              in case r of
                                   Z => Z
                                   (S _) => minus alignment r

||| Proof that an offset with zero remainder needs zero padding.
export
alignedNeedsPadding : (n : Nat) -> (a : Nat) -> {auto 0 ok : NonZero a} ->
                      modNatNZ n a ok = 0 -> paddingFor n a = 0
alignedNeedsPadding n a prf = rewrite prf in Refl

--------------------------------------------------------------------------------
-- Struct Field Model (for future array-passing FFT extension)
--------------------------------------------------------------------------------

||| A field within a struct layout, carrying its offset and type.
public export
record StructField where
  constructor MkField
  fieldName      : String
  fieldOffset    : Nat
  fieldType      : WasmValType

||| Derived size from the field's WASM type.
public export
fieldSize : StructField -> Nat
fieldSize f = wasmValSize f.fieldType

||| Derived alignment from the field's WASM type.
public export
fieldAlignment : StructField -> Nat
fieldAlignment f = wasmValAlign f.fieldType

||| Proof that a field is correctly aligned within a struct.
public export
FieldAligned : StructField -> Type
FieldAligned f = modNatNZ (fieldOffset f) (fieldAlignment f) SIsNonZero = 0

||| Proof that a field does not overflow past a given struct size.
public export
FieldInBounds : (structSize : Nat) -> StructField -> Type
FieldInBounds sz f = LTE (fieldOffset f + fieldSize f) sz

||| A struct layout with a total size and alignment.
public export
record StructLayout where
  constructor MkLayout
  layoutName      : String
  layoutFields    : List StructField
  layoutSize      : Nat
  layoutAlignment : Nat

--------------------------------------------------------------------------------
-- SNIF-Specific Layout: WASM function arguments are stack-passed values
--------------------------------------------------------------------------------

||| An I32 field at offset 0 is always aligned (0 mod 4 = 0).
export
i32AtZeroAligned : FieldAligned (MkField "arg0" 0 I32)
i32AtZeroAligned = Refl

||| An I64 field at offset 0 is always aligned (0 mod 8 = 0).
export
i64AtZeroAligned : FieldAligned (MkField "arg0" 0 I64)
i64AtZeroAligned = Refl

||| An I64 field at offset 8 is aligned (8 mod 8 = 0).
export
i64AtOffset8Aligned : FieldAligned (MkField "arg1" 8 I64)
i64AtOffset8Aligned = Refl

||| Proof that two I32 fields packed sequentially are both aligned.
||| Layout: [i32 @ 0, i32 @ 4] — total 8 bytes.
||| This matches checked_add(a: i32, b: i32) -> i32.
export
twoI32sAligned : (FieldAligned (MkField "a" 0 I32),
                  FieldAligned (MkField "b" 4 I32))
twoI32sAligned = (Refl, Refl)
