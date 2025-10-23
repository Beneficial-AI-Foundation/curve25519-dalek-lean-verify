import Curve25519Dalek.Funs

/-! # M

The main statement concerning `m` is `m_spec` (below).
-/

open Aeneas.Std Result
open curve25519_dalek
open backend.serial.u64.scalar

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `m` -/

/-- **Spec for `backend.serial.u64.scalar.m`**:
- Does not overflow and hence returns a result
- The result equals the product of the two input values -/
-- @[progress]
theorem m_spec (x y : U64) :
    ∃ result, m x y = ok (result) ∧
    result.val = x.val * y.val := by
  unfold m
  progress*
  simp [*];
  scalar_tac
