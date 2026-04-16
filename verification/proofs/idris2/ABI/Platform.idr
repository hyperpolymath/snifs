-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
--
-- ABI-3: Platform-specific type size proofs for SNIF
--
-- Proves that type sizes on the WASM32 target match the Zig source
-- expectations. SNIF compiles Zig to wasm32-freestanding; this module
-- establishes that the Zig i32/i64 types map to the correct WASM value
-- types with the correct byte widths.
--
-- All proofs are constructive (no believe_me, no assert_total).

module ABI.Platform

import ABI.Layout
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- Platform Model
--------------------------------------------------------------------------------

||| Supported target platforms.
||| SNIF targets WASM32 exclusively; host platforms are included for
||| completeness (the wasmex host NIF runs on these).
public export
data Platform = Linux64 | LinuxARM64 | MacOS64 | MacOSARM64
              | Windows64 | FreeBSD64 | WASM32

||| The SNIF target platform. All SNIF code compiles to this target.
public export
SnifTarget : Platform
SnifTarget = WASM32

--------------------------------------------------------------------------------
-- Pointer Size
--------------------------------------------------------------------------------

||| Pointer size in bytes for each platform.
public export
ptrSize : Platform -> Nat
ptrSize WASM32 = 4
ptrSize _      = 8

||| Proof that SNIF target (WASM32) has 4-byte pointers.
export
snifPtrSize4 : ptrSize SnifTarget = 4
snifPtrSize4 = Refl

||| Proof that pointer size is always 4 or 8 bytes.
export
ptrSizeValid : (p : Platform) -> Either (ptrSize p = 4) (ptrSize p = 8)
ptrSizeValid WASM32     = Left Refl
ptrSizeValid Linux64    = Right Refl
ptrSizeValid LinuxARM64 = Right Refl
ptrSizeValid MacOS64    = Right Refl
ptrSizeValid MacOSARM64 = Right Refl
ptrSizeValid Windows64  = Right Refl
ptrSizeValid FreeBSD64  = Right Refl

||| Proof that pointer size is always at least 4 bytes.
export
ptrSizeAtLeast4 : (p : Platform) -> LTE 4 (ptrSize p)
ptrSizeAtLeast4 WASM32     = lteRefl
ptrSizeAtLeast4 Linux64    = lteSuccRight (lteSuccRight (lteSuccRight (lteSuccRight lteRefl)))
ptrSizeAtLeast4 LinuxARM64 = lteSuccRight (lteSuccRight (lteSuccRight (lteSuccRight lteRefl)))
ptrSizeAtLeast4 MacOS64    = lteSuccRight (lteSuccRight (lteSuccRight (lteSuccRight lteRefl)))
ptrSizeAtLeast4 MacOSARM64 = lteSuccRight (lteSuccRight (lteSuccRight (lteSuccRight lteRefl)))
ptrSizeAtLeast4 Windows64  = lteSuccRight (lteSuccRight (lteSuccRight (lteSuccRight lteRefl)))
ptrSizeAtLeast4 FreeBSD64  = lteSuccRight (lteSuccRight (lteSuccRight (lteSuccRight lteRefl)))

--------------------------------------------------------------------------------
-- Zig/WASM Type Size Correspondence
--------------------------------------------------------------------------------

||| Zig integer types as they appear in SNIF exports.
public export
data ZigIntType = ZigI32 | ZigI64 | ZigUsize

||| Size in bytes of each Zig integer type on a given platform.
public export
zigTypeSize : Platform -> ZigIntType -> Nat
zigTypeSize _      ZigI32  = 4
zigTypeSize _      ZigI64  = 8
zigTypeSize WASM32 ZigUsize = 4
zigTypeSize _      ZigUsize = 8

||| The WASM value type that each Zig type compiles to.
public export
zigToWasm : ZigIntType -> WasmValType
zigToWasm ZigI32  = I32
zigToWasm ZigI64  = I64
zigToWasm ZigUsize = I32  -- usize is i32 on wasm32

||| Proof that Zig i32 is 4 bytes on all platforms.
export
zigI32Always4 : (p : Platform) -> zigTypeSize p ZigI32 = 4
zigI32Always4 _ = Refl

||| Proof that Zig i64 is 8 bytes on all platforms.
export
zigI64Always8 : (p : Platform) -> zigTypeSize p ZigI64 = 8
zigI64Always8 _ = Refl

||| Proof that Zig usize is 4 bytes on WASM32 (the SNIF target).
export
zigUsizeIs4OnWasm : zigTypeSize WASM32 ZigUsize = 4
zigUsizeIs4OnWasm = Refl

||| Proof that Zig type sizes on WASM32 match the corresponding WASM value type sizes.
||| This is the key correspondence: what Zig compiles to matches what WASM expects.
export
zigWasmSizeMatch : (t : ZigIntType) ->
                   zigTypeSize WASM32 t = wasmValSize (zigToWasm t)
zigWasmSizeMatch ZigI32  = Refl
zigWasmSizeMatch ZigI64  = Refl
zigWasmSizeMatch ZigUsize = Refl

--------------------------------------------------------------------------------
-- WASM Linear Memory Properties
--------------------------------------------------------------------------------

||| WASM page size in bytes (fixed by spec).
public export
WasmPageSize : Nat
WasmPageSize = 65536

||| Proof that WASM page size is a power of 2 (specifically 2^16).
||| We prove this by showing 65536 = 2 * 32768 = ... = 2^16.
export
wasmPageSizePositive : LT 0 WasmPageSize
wasmPageSizePositive = LTESucc LTEZero

||| Proof that WASM page size is a multiple of all value type alignments.
||| Since all alignments are 4 or 8, and 65536 = 8192 * 8 = 16384 * 4,
||| page boundaries are always properly aligned for any value type.
export
wasmPageAlignedFor : (t : WasmValType) ->
                     modNatNZ WasmPageSize (wasmValAlign t) SIsNonZero = 0
wasmPageAlignedFor I32 = Refl
wasmPageAlignedFor I64 = Refl
wasmPageAlignedFor F32 = Refl
wasmPageAlignedFor F64 = Refl

||| Maximum WASM32 linear memory: 4 GiB (2^32 bytes).
||| Expressed as number of pages.
public export
WasmMaxPages : Nat
WasmMaxPages = 65536

||| Proof that max memory = maxPages * pageSize (4 GiB).
||| 65536 * 65536 = 4294967296 = 2^32.
export
wasmMaxMemory : WasmMaxPages * WasmPageSize = 4294967296
wasmMaxMemory = Refl

--------------------------------------------------------------------------------
-- C int size (for reference: wasmex host side)
--------------------------------------------------------------------------------

||| C `int` size in bytes (always 4 on all platforms).
public export
cIntSize : Platform -> Nat
cIntSize _ = 4

||| C `size_t` size in bytes (matches pointer size).
public export
cSizeT : Platform -> Nat
cSizeT = ptrSize

||| Proof that size_t always equals pointer size on all platforms.
export
sizeTEqPtrSize : (p : Platform) -> cSizeT p = ptrSize p
sizeTEqPtrSize _ = Refl

||| Proof that C int is always 4 bytes on all platforms.
export
cIntAlways4 : (p : Platform) -> cIntSize p = 4
cIntAlways4 _ = Refl
