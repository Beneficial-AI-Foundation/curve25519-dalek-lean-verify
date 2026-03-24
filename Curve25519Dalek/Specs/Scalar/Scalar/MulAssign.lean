/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.FromBytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Pack
/-! # Spec Theorem for `Scalar::mul_assign`

Specification and proof for the
`MulAssign<&'a Scalar> for Scalar` trait implementation for Scalar.

This function multiplies two scalars modulo the group order
ℓ = 2^252 + 27742317777372353535851937790883648493
by:
1. Unpacking both inputs from their 32-byte little-endian representation into
   the 5-limb base-2^52 internal representation (`Scalar52`) via `Scalar::unpack`,
   which internally calls `Scalar52::from_bytes`
2. Calling `Scalar52::mul` to multiply the two unpacked scalars, which internally
   performs a double Montgomery reduction (via `mul_internal` and `montgomery_reduce`
   twice, using the precomputed constant `RR = R² mod ℓ`), producing a canonical
   result in [0, ℓ)
3. Packing the result back into a canonical 32-byte `Scalar` via `Scalar52::pack`

Both inputs must satisfy Scalar invariant #2 (canonical form), i.e., their byte
encodings represent integers strictly less than ℓ.  This invariant is always satisfied
by publicly observable scalars in the library.

**Source**: curve25519-dalek/src/scalar.rs (lines 316:4-318:5)
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAssignSharedAScalar

/-
natural language description:

• Takes two Scalars `self` and `_rhs` (both passed by value in the Lean extraction,
  corresponding to the Rust `Scalar` value and `&'a Scalar` reference)
• Unpacks both via `Scalar::unpack`, which delegates to `Scalar52::from_bytes` to
  produce 5-limb base-2^52 `Scalar52` values; each limb is bounded by 2^52 and the
  represented integer equals the little-endian value of the byte array
• Calls `Scalar52::mul` which performs scalar multiplication via a double Montgomery
  reduction: computing the wide 9-limb product via `mul_internal`, applying
  `montgomery_reduce` to obtain `(a·b)·R⁻¹ mod ℓ`, then multiplying by `RR = R² mod ℓ`
  and applying `montgomery_reduce` again to recover `a·b mod ℓ` in canonical form
• Packs the canonical `Scalar52` back into a 32-byte `Scalar` via `Scalar52::pack`

natural language specs:

• The function always succeeds (no panic) when both input scalars are canonical
  (their byte values satisfy U8x32_as_Nat bytes < ℓ)
• The result's byte representation, viewed as a little-endian integer, is congruent
  to (U8x32_as_Nat self.bytes * U8x32_as_Nat _rhs.bytes) modulo ℓ
• The result is canonical: U8x32_as_Nat result.bytes < ℓ
-/

/-- **Spec and proof concerning `scalar.Scalar.Insts.CoreOpsArithMulAssignSharedAScalar.mul_assign`**:
• Precondition: both `self` and `_rhs` are canonical scalars (their byte values are < ℓ),
  consistent with Scalar invariant #2
• The function always succeeds (no panic)
• The result satisfies:
  `U8x32_as_Nat result.bytes ≡ U8x32_as_Nat self.bytes * U8x32_as_Nat _rhs.bytes [MOD L]`
• The result is canonical: `U8x32_as_Nat result.bytes < L`
-/
@[progress]
theorem mul_assign_spec (self _rhs : scalar.Scalar) :
    mul_assign self _rhs ⦃ result =>
      U8x32_as_Nat result.bytes ≡
        U8x32_as_Nat self.bytes * U8x32_as_Nat _rhs.bytes [MOD L] ∧
      U8x32_as_Nat result.bytes < L ⦄ := by
  unfold mul_assign
  unfold scalar.Scalar.unpack
  progress as ⟨s, hs_nat, hs_bounds⟩
  progress as ⟨s1, hs1_nat, hs1_bounds⟩
  have hs_62  : ∀ i < 5, s[i]!.val  < 2 ^ 62 :=
    fun i hi => Nat.lt_trans (hs_bounds  i hi) (by norm_num)
  have hs1_62 : ∀ i < 5, s1[i]!.val < 2 ^ 62 :=
    fun i hi => Nat.lt_trans (hs1_bounds i hi) (by norm_num)
  progress as ⟨s2, hs2_cong, hs2_bounds⟩
  progress as ⟨hpack, hpack_cong, hpack_lt⟩
  refine ⟨?_, hpack_lt⟩
  have heq : Scalar52_as_Nat s * Scalar52_as_Nat s1 =
             U8x32_as_Nat self.bytes * U8x32_as_Nat _rhs.bytes := by
    rw [hs_nat, hs1_nat]
  exact Nat.ModEq.trans hpack_cong (heq ▸ hs2_cong)

end curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAssignSharedAScalar

/-! ## Wrapper: `Scalar *= Scalar` (by-value rhs)

The following variant wraps the core multiplication-assignment by delegating directly to
`scalar.Scalar.Insts.CoreOpsArithMulAssignSharedAScalar.mul_assign`.
-/

namespace curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAssignScalar

/-
natural language description:

• Takes a Scalar `self` (by value) and a Scalar `rhs` (by value in the Lean extraction,
  generated via the `define_mul_assign_variants!` macro in macros.rs)
• Delegates to the core `MulAssignSharedAScalar...mul_assign` implementation

natural language specs:

• Same as the core `mul_assign`: always succeeds when both scalars are canonical,
  result ≡ (self * rhs) [MOD L], result < L
-/

/-- **Spec and proof concerning `scalar.Scalar.Insts.CoreOpsArithMulAssignScalar.mul_assign`**:
• Same spec as the core `mul_assign`; proof delegates via `progress*`
-/
@[progress]
theorem mul_assign_spec (self rhs : scalar.Scalar) :
    mul_assign self rhs ⦃ result =>
      U8x32_as_Nat result.bytes ≡
        U8x32_as_Nat self.bytes * U8x32_as_Nat rhs.bytes [MOD L] ∧
      U8x32_as_Nat result.bytes < L ⦄ := by
  unfold mul_assign
  progress*

end curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAssignScalar
