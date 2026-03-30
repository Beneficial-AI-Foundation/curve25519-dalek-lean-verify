import Aeneas

open Aeneas Aeneas.Std Result Aeneas.Std.WP

-- Stage 1 produces two values, stage 2 combines and doubles
def example_fn (a b : U32) : Result U32 := do
  -- Stage 1: produce two values
  let x ← a + b
  let y ← a * b
  -- Stage 2: combine and double
  let z ← x + y
  let w ← z + z
  ok w

-- Helper for stage 1: returns a pair
def stage1 (a b : U32) : Result (U32 × U32) := do
  let x ← a + b
  let y ← a * b
  ok (x, y)

-- Fold theorem for stage 1
theorem fold_stage1 {α : Type} (a b : U32) (f : U32 → U32 → Result α) :
    (do let x ← a + b; let y ← a * b; f x y) =
    (do let r ← stage1 a b; f r.1 r.2) := by
  simp only [stage1, bind_assoc_eq, bind_tc_ok]

-- Spec for stage 1
@[step]
theorem stage1_spec (a b : U32) (h1 : a.val + b.val ≤ U32.max) (h2 : a.val * b.val ≤ U32.max) :
    stage1 a b ⦃ r => r.1.val = a.val + b.val ∧ r.2.val = a.val * b.val ⦄ := by
  unfold stage1
  step*

-- Helper for stage 2: returns a single value
def stage2 (x y : U32) : Result U32 := do
  let z ← x + y
  let w ← z + z
  ok w

-- Fold theorem for stage 2
theorem fold_stage2 {α : Type} (x y : U32) (f : U32 → Result α) :
    (do let z ← x + y; let w ← z + z; f w) =
    (do let r ← stage2 x y; f r) := by
  simp only [stage2, bind_assoc_eq, bind_tc_ok]

-- Spec for stage 2
@[step]
theorem stage2_spec (x y : U32) (h : x.val + y.val + (x.val + y.val) ≤ U32.max) :
    stage2 x y ⦃ r => r.val = 2 * (x.val + y.val) ⦄ := by
  unfold stage2
  step*

-- Main proof: fold both stages, then step* uses both specs
example (a b : U32) (h1 : a.val + b.val ≤ U32.max)
    (h2 : a.val * b.val ≤ U32.max)
    (h3 : a.val + b.val + a.val * b.val + (a.val + b.val + a.val * b.val) ≤ U32.max) :
    example_fn a b ⦃ r => r.val = 2 * (a.val + b.val + a.val * b.val) ⦄ := by
  unfold example_fn
  simp_rw [fold_stage1, fold_stage2]
  step*
