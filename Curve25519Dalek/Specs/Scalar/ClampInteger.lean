/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Defs
import Curve25519Dalek.Funs
import Mathlib

set_option linter.style.setOption false
set_option grind.warning false

/-! # clamp_integer -/

open Aeneas
open scoped Aeneas
open Aeneas.Std Result
open curve25519_dalek
open scalar

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Auxiliary theorems -/

/- This allows `bvify` to automatically do the conversion `a ∣ b ↔ b % a = 0`,
   which can then be lifted to something which uses bit-vectors -/
attribute [bvify_simps] Nat.dvd_iff_mod_eq_zero

/-! ## Spec for `clamp_integer` -/

namespace curve25519_dalek.scalar

/-- **Spec and proof concerning `scalar.clamp_integer`**:
- No panic
- (as_nat_32_u8 result) is divisible by h (cofactor of curve25519)
- as_nat_32_u8 result < 2^255
- 2^254 ≤ as_nat_32_u8 result
-/
@[progress]
theorem clamp_integer_spec (bytes : Array U8 32#usize) :
    clamp_integer bytes ⦃ result =>
      h ∣ U8x32_as_Nat result ∧
      U8x32_as_Nat result < 2^255 ∧
      2^254 ≤ U8x32_as_Nat result ⦄ := by
  sorry

end curve25519_dalek.scalar
