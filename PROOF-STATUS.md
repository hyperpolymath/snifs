# Proof Status — SNIF
<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- Template: rsr-template-repo/PROOF-STATUS.md -->
<!-- Tracks proof completion. Requirements defined in PROOF-NEEDS.md -->

## Summary

| Category | Total | Done | In Progress | Blocked | Remaining |
|----------|-------|------|-------------|---------|-----------|
| ABI/FFI (ABI) | 5 | 5 | 0 | 0 | 0 |
| Typing (TP) | 2 | 2 | 0 | 0 | 0 |
| Invariant (INV) | 0 | 0 | 0 | 0 | 0 |
| Security (SEC) | 0 | 0 | 0 | 0 | 0 |
| Concurrency (CONC) | 0 | 0 | 0 | 0 | 0 |
| Algorithm (ALG) | 0 | 0 | 0 | 0 | 0 |
| Domain (DOM) | 0 | 0 | 0 | 0 | 0 |
| **Total** | **7** | **7** | **0** | **0** | **0** |

**Overall**: 100% proven

## Proofs Done

| ID | Proof | Prover | File | Date | Verified By |
|----|-------|--------|------|------|-------------|
| ABI-1 | Non-null pointer proofs (WasmAddr, SafePtr, MemRegion) | Idris2 | `verification/proofs/idris2/ABI/Pointers.idr` | 2026-04-16 | idris2 --check |
| ABI-2 | Memory layout correctness (WasmValType sizes, alignment) | Idris2 | `verification/proofs/idris2/ABI/Layout.idr` | 2026-04-16 | idris2 --check |
| ABI-3 | Platform type size proofs (WASM32 Zig-WASM correspondence) | Idris2 | `verification/proofs/idris2/ABI/Platform.idr` | 2026-04-16 | idris2 --check |
| ABI-4 | FFI function return type proofs (8 SNIF exports) | Idris2 | `verification/proofs/idris2/ABI/Foreign.idr` | 2026-04-16 | idris2 --check |
| ABI-5 | C ABI compliance (scalar exports, array layout framework) | Idris2 | `verification/proofs/idris2/ABI/Compliance.idr` | 2026-04-16 | idris2 --check |
| TP-1 | Core data type well-formedness (WasmTrapKind, SNIFCallResult, CompilationMode) | Idris2 | `verification/proofs/idris2/Types.idr` | 2026-04-16 | idris2 --check |
| TP-2 | Public API type safety (SNIFResult functor/monad laws, BEAM survival) | Lean4 | `verification/proofs/lean4/ApiTypes.lean` | 2026-04-16 | lean4 |

## Proofs In Progress

| ID | Proof | Prover | Assignee | Started | Blocker |
|----|-------|--------|----------|---------|---------|
| — | — | — | — | — | — |

## Proofs Blocked

| ID | Proof | Blocked By | Notes |
|----|-------|------------|-------|
| — | — | — | — |

## Proofs Remaining

| ID | Proof | Category | Prover | Priority | Est. Effort |
|----|-------|----------|--------|----------|-------------|
| — | All proofs completed | — | — | — | — |

## Verification Commands

```bash
# Check all Idris2 proofs
just proof-check-idris2

# Check all Lean4 proofs
just proof-check-lean4

# Check all Agda proofs
just proof-check-agda

# Check all Coq proofs
just proof-check-coq

# Run all proof checks
just proof-check-all

# Scan for dangerous patterns
panic-attack assail --proofs-only
```

## Proof Summary by File

### ABI-1: Pointers.idr — WASM Linear Memory Pointer Safety
- `WasmAddr`: bounded linear memory index with `LT index memSize` proof
- `SafePtr`: non-null host-side pointer with `So (ptr /= 0)` witness
- `WasmHandle`: tagged WASM instance handle with non-null guarantee
- `MemRegion`: contiguous memory region with start/end bounds proofs
- Key theorems: `wasmAddrInBounds`, `checkPtrZeroIsNothing`, `regionLengthBounded`

### ABI-2: Layout.idr — WASM Value Type Memory Layout
- `WasmValType`: I32/I64/F32/F64 with size and alignment functions
- Natural alignment proof: `wasmValNaturallyAligned` (align = size for all types)
- Size validity: all sizes are 4 or 8, all positive, all >= 4
- `StructField`/`StructLayout` framework for future array-passing
- Concrete alignment proofs for SNIF function signatures (e.g., `twoI32sAligned`)

### ABI-3: Platform.idr — WASM32 Platform Type Sizes
- `Platform` enumeration with `SnifTarget = WASM32`
- `ZigIntType` with `zigToWasm` mapping (i32->I32, i64->I64, usize->I32)
- Key theorem: `zigWasmSizeMatch` — Zig type sizes equal WASM type sizes on WASM32
- WASM memory properties: page size, max pages, page alignment
- Pointer size proofs: `snifPtrSize4`, `ptrSizeValid`, `ptrSizeAtLeast4`

### ABI-4: Foreign.idr — FFI Function Return Types
- `SNIFResult`: models {:ok, value} | {:error, trap} with functor identity proof
- `WasmFuncSpec`: function name, param types, return type
- All 8 SNIF exports specified: fibonacci, checked_add, 5 crash functions, still_alive
- Return type proofs for each export (e.g., `fibonacciReturnsI64`)
- Arity proofs for each export (e.g., `checkedAddArity2`)
- `IsCrashFunction` classifier with arity and return type proofs

### ABI-5: Compliance.idr — C ABI Compliance
- `CABICompliant`: struct alignment + bounds + size divisibility
- `ScalarABICompliant`: trivial compliance for scalar-only functions
- Individual compliance proofs for all 8 exports
- `AllScalarCompliant`: aggregate proof for the full export list
- `WasmArrayLayout`/`WasmArrayValid`: framework for future FFT array passing

### TP-1: Types.idr — Core Data Type Well-Formedness
- `WasmTrapKind`: 6-variant enum with full DecEq (30 cases)
- `SNIFCallResult`: 3-variant sum (CallOk, CallTrapped, CallLoadError)
- Disjointness proofs: `okIsNotTrapped`, `okIsNotLoadError`, `trappedIsNotLoadError`
- `BeamSurvived`: predicate trivially satisfied for all outcomes (crash isolation theorem)
- `CompilationMode` with `SafeForSNIF` predicate: `releaseFastUnsafe`, `requiredModeIsSafe`

### TP-2: ApiTypes.lean — Public API Type Safety
- `SNIFResult` functor laws: `map_id`, `map_comp`
- `SNIFResult` monad laws: `bind_left_id`, `bind_right_id`, `bind_assoc`
- `beam_always_survives`: every result is ok or trap (no third state)
- `sequential_calls_safe`: composing calls preserves BEAM survival
- Compilation mode safety: `releaseSafe_is_safe`, `releaseFast_not_safe`
- `WasmFuncSpec` with `snifExportCount` proof (8 exports)

## Changelog

| Date | Change | By |
|------|--------|-----|
| 2026-04-04 | Initial proof status tracking | Template |
| 2026-04-16 | All 7 proofs completed (ABI-1 through ABI-5, TP-1, TP-2) | Claude Code |
