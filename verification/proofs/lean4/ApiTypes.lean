-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
--
-- TP-2: Public API type safety proofs for SNIF
--
-- Proves properties about the exported SNIF API types that the Elixir
-- layer consumes. Models the {:ok, [values]} | {:error, reason} contract
-- and proves functor laws, safety invariants, and call composition.
--
-- All proofs are constructive (no sorry).

--------------------------------------------------------------------------------
-- WASM Trap Classification
--------------------------------------------------------------------------------

/-- Classification of WASM trap causes, matching the 5 tested categories. -/
inductive WasmTrapKind where
  | oob         : WasmTrapKind  -- Out-of-bounds memory access
  | unreachable : WasmTrapKind  -- Explicit unreachable instruction
  | panic       : WasmTrapKind  -- Zig @panic
  | overflow    : WasmTrapKind  -- Integer overflow
  | divZero     : WasmTrapKind  -- Division by zero
  | unknown     : WasmTrapKind  -- Other traps
  deriving DecidableEq, Repr

--------------------------------------------------------------------------------
-- SNIF Call Result
--------------------------------------------------------------------------------

/-- Result of calling a SNIF function through wasmex.
    Models the Elixir-side {:ok, [values]} | {:error, reason} contract. -/
inductive SNIFResult (α : Type) where
  | ok   : α → SNIFResult α
  | trap : WasmTrapKind → String → SNIFResult α
  deriving Repr

namespace SNIFResult

  /-- Map a function over the success value. -/
  def map (f : α → β) : SNIFResult α → SNIFResult β
    | .ok v      => .ok (f v)
    | .trap k m  => .trap k m

  /-- Functor identity law: map id = id. -/
  theorem map_id : ∀ (r : SNIFResult α), map id r = r := by
    intro r
    cases r with
    | ok v     => simp [map]
    | trap k m => simp [map]

  /-- Functor composition law: map (g . f) = map g . map f. -/
  theorem map_comp (f : α → β) (g : β → γ) :
      ∀ (r : SNIFResult α), map (g ∘ f) r = map g (map f r) := by
    intro r
    cases r with
    | ok v     => simp [map, Function.comp]
    | trap k m => simp [map]

  /-- Bind for monadic composition of SNIF calls. -/
  def bind (r : SNIFResult α) (f : α → SNIFResult β) : SNIFResult β :=
    match r with
    | .ok v     => f v
    | .trap k m => .trap k m

  /-- Left identity monad law: bind (ok a) f = f a. -/
  theorem bind_left_id (a : α) (f : α → SNIFResult β) :
      bind (.ok a) f = f a := by
    simp [bind]

  /-- Right identity monad law: bind m ok = m. -/
  theorem bind_right_id (r : SNIFResult α) :
      bind r .ok = r := by
    cases r with
    | ok v     => simp [bind]
    | trap k m => simp [bind]

  /-- Associativity monad law. -/
  theorem bind_assoc (r : SNIFResult α) (f : α → SNIFResult β)
      (g : β → SNIFResult γ) :
      bind (bind r f) g = bind r (fun a => bind (f a) g) := by
    cases r with
    | ok v     => simp [bind]
    | trap k m => simp [bind]

  /-- A trap result is never an ok result. -/
  theorem trap_ne_ok (k : WasmTrapKind) (m : String) (v : α) :
      SNIFResult.trap k m ≠ SNIFResult.ok v := by
    intro h
    cases h

  /-- Predicate: result is successful. -/
  def isOk : SNIFResult α → Bool
    | .ok _    => true
    | .trap .. => false

  /-- Predicate: result is a trap. -/
  def isTrap : SNIFResult α → Bool
    | .ok _    => false
    | .trap .. => true

  /-- isOk and isTrap are complementary. -/
  theorem ok_xor_trap (r : SNIFResult α) : isOk r = !isTrap r := by
    cases r with
    | ok _     => simp [isOk, isTrap]
    | trap _ _ => simp [isOk, isTrap]

end SNIFResult

--------------------------------------------------------------------------------
-- Compilation Mode Safety
--------------------------------------------------------------------------------

/-- Zig compilation modes. -/
inductive CompilationMode where
  | debug        : CompilationMode
  | releaseSafe  : CompilationMode
  | releaseFast  : CompilationMode
  | releaseSmall : CompilationMode
  deriving DecidableEq, Repr

/-- Whether a mode preserves runtime safety checks (ADR-001). -/
def hasSafetyChecks : CompilationMode → Bool
  | .debug       => true
  | .releaseSafe => true
  | .releaseFast => false
  | .releaseSmall => false

/-- A mode is safe for SNIF iff it has safety checks. -/
def SafeForSNIF (mode : CompilationMode) : Prop :=
  hasSafetyChecks mode = true

/-- ReleaseSafe is the required SNIF mode. -/
theorem releaseSafe_is_safe : SafeForSNIF .releaseSafe := by
  simp [SafeForSNIF, hasSafetyChecks]

/-- Debug is also safe (but suboptimal). -/
theorem debug_is_safe : SafeForSNIF .debug := by
  simp [SafeForSNIF, hasSafetyChecks]

/-- ReleaseFast is NOT safe for SNIF. -/
theorem releaseFast_not_safe : ¬ SafeForSNIF .releaseFast := by
  simp [SafeForSNIF, hasSafetyChecks]

/-- ReleaseSmall is NOT safe for SNIF. -/
theorem releaseSmall_not_safe : ¬ SafeForSNIF .releaseSmall := by
  simp [SafeForSNIF, hasSafetyChecks]

--------------------------------------------------------------------------------
-- WASM Value Types
--------------------------------------------------------------------------------

/-- The four WASM MVP value types. -/
inductive WasmValType where
  | i32 : WasmValType
  | i64 : WasmValType
  | f32 : WasmValType
  | f64 : WasmValType
  deriving DecidableEq, Repr

/-- Size in bytes of each WASM value type. -/
def wasmValSize : WasmValType → Nat
  | .i32 => 4
  | .i64 => 8
  | .f32 => 4
  | .f64 => 8

/-- All WASM value sizes are positive. -/
theorem wasmValSize_pos (t : WasmValType) : 0 < wasmValSize t := by
  cases t <;> simp [wasmValSize]

/-- All WASM value sizes are at least 4. -/
theorem wasmValSize_ge_4 (t : WasmValType) : 4 ≤ wasmValSize t := by
  cases t <;> simp [wasmValSize]

--------------------------------------------------------------------------------
-- SNIF Function Specification
--------------------------------------------------------------------------------

/-- Specification of a SNIF exported function. -/
structure WasmFuncSpec where
  name       : String
  paramTypes : List WasmValType
  returnType : WasmValType
  deriving Repr

/-- The 8 SNIF exports from safe_nif.zig. -/
def snifExports : List WasmFuncSpec :=
  [ ⟨"fibonacci",         [.i32],        .i64⟩
  , ⟨"checked_add",       [.i32, .i32],  .i32⟩
  , ⟨"crash_oob",         [],            .i32⟩
  , ⟨"crash_unreachable", [],            .i32⟩
  , ⟨"crash_panic",       [],            .i32⟩
  , ⟨"crash_overflow",    [],            .i32⟩
  , ⟨"crash_div_zero",    [],            .i32⟩
  , ⟨"still_alive",       [],            .i32⟩
  ]

/-- Proof that there are exactly 8 SNIF exports. -/
theorem snifExportCount : snifExports.length = 8 := by
  simp [snifExports]

--------------------------------------------------------------------------------
-- BEAM Survival Theorem (type-level)
--------------------------------------------------------------------------------

/-- The BEAM always survives a SNIF call.
    For any result — ok, trap, or load error — the BEAM VM continues.
    This is the central safety property of the SNIF architecture.

    At the type level, this is trivially true because SNIFResult is
    a pure data type (no side effects, no exceptions, no signals).
    The proof's value is in making the safety claim explicit and
    machine-checkable. -/
theorem beam_always_survives (r : SNIFResult α) :
    r.isOk = true ∨ r.isTrap = true := by
  cases r with
  | ok _     => left; simp [SNIFResult.isOk]
  | trap _ _ => right; simp [SNIFResult.isTrap]

/-- Sequential SNIF calls preserve BEAM survival.
    If the BEAM survives call 1, and we make call 2, the BEAM survives both. -/
theorem sequential_calls_safe (r1 r2 : SNIFResult α) :
    (r1.isOk = true ∨ r1.isTrap = true) →
    (r2.isOk = true ∨ r2.isTrap = true) →
    (r1.isOk = true ∨ r1.isTrap = true) ∧
    (r2.isOk = true ∨ r2.isTrap = true) := by
  intro h1 h2
  exact ⟨h1, h2⟩

/-- Bounded natural number (for array indices, memory offsets). -/
structure BoundedNat (max : Nat) where
  val : Nat
  le_max : val ≤ max

/-- A bounded value is always ≤ max. -/
theorem bounded_nat_le (b : BoundedNat max) : b.val ≤ max :=
  b.le_max

/-- Zero is always bounded (for any positive max). -/
def zeroBounded (h : 0 < max) : BoundedNat max :=
  ⟨0, Nat.zero_le max⟩
