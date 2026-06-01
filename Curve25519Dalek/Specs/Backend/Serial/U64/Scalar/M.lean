/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Theodore Ehrenborg, Liao Zhang
-/
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
@[step]
theorem m_spec (x y : U64) :
    m x y ⦃ (result : U128) => result.val = x.val * y.val ⦄ := by
  unfold m
  step*

end curve25519_dalek.backend.serial.u64.scalar
