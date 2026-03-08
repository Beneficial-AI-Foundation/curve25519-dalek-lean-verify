import Curve25519Dalek.Funs

/-! # M

The main statement concerning `m` is `m_spec` (below).
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek
open backend.serial.u64.scalar

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `m` -/

namespace curve25519_dalek.backend.serial.u64.scalar

/-- **Spec for `backend.serial.u64.scalar.m`**:
- The result equals the product of the two input values -/
@[progress]
theorem m_spec (x y : U64) :
    m x y ⦃ (result : U128) => result.val = x.val * y.val ⦄ := by
  unfold m
  progress*

end curve25519_dalek.backend.serial.u64.scalar
