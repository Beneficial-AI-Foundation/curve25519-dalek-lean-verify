/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.FromBytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Pack

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::mul_assign`

This function multiplies two scalars modulo the group order
ℓ = 2^252 + 27742317777372353535851937790883648493.
Both inputs (`self` and `_rhs`) are passed by value in the Lean extraction,
corresponding to the Rust `Scalar` value and `&'a Scalar` reference respectively.
The algorithm:
1. Unpacks both inputs from their 32-byte little-endian representation into the
   5-limb base-2^52 internal representation (`Scalar52`) via `Scalar::unpack`,
   which internally calls `Scalar52::from_bytes`; each limb is bounded by 2^52
   and the represented integer equals the little-endian value of the byte array
2. Calls `Scalar52::mul` to multiply the two unpacked scalars via a double Montgomery
   reduction: computing the wide 9-limb product via `mul_internal`, applying
   `montgomery_reduce` to obtain `(a·b)·R⁻¹ mod ℓ`, then multiplying by `RR = R² mod ℓ`
   and applying `montgomery_reduce` again to recover `a·b mod ℓ` in canonical form in [0, ℓ)
3. Packs the result back into a canonical 32-byte `Scalar` via `Scalar52::pack`

Both inputs must satisfy Scalar invariant #2 (canonical form), i.e., their byte
encodings represent integers strictly less than ℓ. This invariant is always satisfied
by publicly observable scalars in the library.

This file covers two Lean extraction variants: the primary implementation
(`CoreOpsArithMulAssignSharedAScalar`) and a by-value `Scalar *= Scalar` wrapper
(`CoreOpsArithMulAssignScalar`) generated via the `define_mul_assign_variants!` macro
in `macros.rs`, which delegates directly to the primary implementation.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAssignSharedAScalar

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::mul_assign`**
• The function always succeeds (no panic)
• `U8x32_as_Nat result.bytes ≡ U8x32_as_Nat self.bytes * U8x32_as_Nat _rhs.bytes [MOD L]`
• The result is canonical: `U8x32_as_Nat result.bytes < L`
-/
@[step]
theorem mul_assign_spec (self _rhs : Scalar)
    (h_self : U8x32_as_Nat self.bytes < L)
    (h_rhs : U8x32_as_Nat _rhs.bytes < L) :
    mul_assign self _rhs ⦃ (result : Scalar) =>
      U8x32_as_Nat result.bytes ≡ U8x32_as_Nat self.bytes * U8x32_as_Nat _rhs.bytes [MOD L] ∧
      U8x32_as_Nat result.bytes < L ⦄ := by
  unfold mul_assign scalar.Scalar.unpack
  let* ⟨ s, s_post1, s_post2 ⟩ ← backend.serial.u64.scalar.Scalar52.from_bytes_spec
  let* ⟨ s1, s1_post1, s1_post2 ⟩ ← backend.serial.u64.scalar.Scalar52.from_bytes_spec
  let* ⟨ s2, s2_post1, s2_post2, s2_post3 ⟩ ← backend.serial.u64.scalar.Scalar52.mul_spec
  · -- s < L (from h_self), s1 < L (from h_rhs), so s * s1 < L * L < R * L
    have h_s_lt : Scalar52_as_Nat s < L := s_post1 ▸ h_self
    have h_s1_lt : Scalar52_as_Nat s1 < L := s1_post1 ▸ h_rhs
    exact Nat.lt_trans (Nat.mul_lt_mul_of_lt_of_lt h_s_lt h_s1_lt)
      (Nat.mul_lt_mul_of_pos_right (by unfold R L; omega) (by unfold L; omega))
  let* ⟨ result, result_post1, result_post2 ⟩ ← scalar.Scalar52.pack_spec
  have heq : Scalar52_as_Nat s * Scalar52_as_Nat s1 =
             U8x32_as_Nat self.bytes * U8x32_as_Nat _rhs.bytes := by
    rw [s_post1, s1_post1]
  exact ⟨Nat.ModEq.trans result_post1 (heq ▸ s2_post1), result_post2⟩

end curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAssignSharedAScalar

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAssignScalar

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::mul_assign`**
• The function always succeeds (no panic)
• `U8x32_as_Nat result.bytes ≡ U8x32_as_Nat self.bytes * U8x32_as_Nat rhs.bytes [MOD L]`
• The result is canonical: `U8x32_as_Nat result.bytes < L`
-/
@[step]
theorem mul_assign_spec (self rhs : Scalar)
    (h_self : U8x32_as_Nat self.bytes < L)
    (h_rhs : U8x32_as_Nat rhs.bytes < L) :
    mul_assign self rhs ⦃ (result : Scalar) =>
      U8x32_as_Nat result.bytes ≡ U8x32_as_Nat self.bytes * U8x32_as_Nat rhs.bytes [MOD L] ∧
      U8x32_as_Nat result.bytes < L ⦄ := by
  unfold mul_assign
  step*

end curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAssignScalar
