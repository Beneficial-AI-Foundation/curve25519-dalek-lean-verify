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
/-! # Spec Theorem for `Scalar::mul`

Specification and proof for the
`Mul<&'a Scalar, Scalar> for &Scalar` trait implementation for Scalar.

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

**Source**: curve25519-dalek/src/scalar.rs (lines 325:4-327:5)
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedAScalarScalar

/-
natural language description:

• Takes two Scalars `self` and `_rhs` (both passed by value in the Lean extraction,
  corresponding to the Rust `&Scalar` and `&'a Scalar` references)
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

/-- **Spec and proof concerning `Shared0Scalar.Insts.CoreOpsArithMulSharedAScalarScalar.mul`**:
• Precondition: both `self` and `_rhs` are canonical scalars (their byte values are < ℓ),
  consistent with Scalar invariant #2 (scalar.rs:221: "for all public non-legacy uses,
  invariant #2 always holds").
  Mathematically only one `< L` is needed (the other is `< R` from limb bounds),
  but both are required to reflect the Rust type invariant.
• The function always succeeds (no panic)
• The result satisfies:
  `U8x32_as_Nat result.bytes ≡ U8x32_as_Nat self.bytes * U8x32_as_Nat _rhs.bytes [MOD L]`
• The result is canonical: `U8x32_as_Nat result.bytes < L`
-/
@[step]
theorem mul_spec (self _rhs : scalar.Scalar)
    (h_self : U8x32_as_Nat self.bytes < L)
    (h_rhs : U8x32_as_Nat _rhs.bytes < L) :
    mul self _rhs ⦃ (result : scalar.Scalar) =>
      U8x32_as_Nat result.bytes ≡ U8x32_as_Nat self.bytes * U8x32_as_Nat _rhs.bytes [MOD L] ∧
      U8x32_as_Nat result.bytes < L ⦄ := by
  unfold mul scalar.Scalar.unpack
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

end curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedAScalarScalar

/-! ## Wrapper: `Scalar * &Scalar` (non-borrow lhs)

The following variant wraps the core multiplication by delegating directly to
`Shared0Scalar.Insts.CoreOpsArithMulSharedAScalarScalar.mul`.
Generated by the `define_mul_variants!` macro (macros.rs, lines 93:12-95:13).
-/

namespace curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBScalarScalar

/-
natural language description:

• Takes a Scalar `self` (by value) and a Scalar `rhs` (by value in the Lean extraction,
  corresponding to the Rust `&'b Scalar` reference)
• Delegates to the core `Shared0Scalar...mul` implementation

natural language specs:

• Same as the core `mul`: always succeeds when both scalars are canonical,
  result ≡ (self * rhs) [MOD L], result < L
-/

/-- **Spec and proof concerning `scalar.Scalar.Insts.CoreOpsArithMulSharedBScalarScalar.mul`**:
• Same spec as the core `mul`; proof delegates via `step*`
-/
@[step]
theorem mul_spec (self rhs : scalar.Scalar)
    (h_self : U8x32_as_Nat self.bytes < L)
    (h_rhs : U8x32_as_Nat rhs.bytes < L) :
    mul self rhs ⦃ result =>
      U8x32_as_Nat result.bytes ≡
        U8x32_as_Nat self.bytes * U8x32_as_Nat rhs.bytes [MOD L] ∧
      U8x32_as_Nat result.bytes < L ⦄ := by
  unfold mul
  step*

end curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBScalarScalar

/-! ## Wrapper: `&Scalar * Scalar` (non-borrow rhs)

The following variant wraps the core multiplication by delegating directly to
`Shared0Scalar.Insts.CoreOpsArithMulSharedAScalarScalar.mul`.
Generated by the `define_mul_variants!` macro (macros.rs, lines 100:12-102:13).
-/

namespace curve25519_dalek.SharedAScalar.Insts.CoreOpsArithMulScalarScalar

/-
natural language description:

• Takes a Scalar `self` (by reference in Rust, by value in the Lean extraction)
  and a Scalar `rhs` (by value in both Rust and the Lean extraction)
• Delegates to the core `Shared0Scalar...mul` implementation

natural language specs:

• Same as the core `mul`: always succeeds when both scalars are canonical,
  result ≡ (self * rhs) [MOD L], result < L
-/

/-- **Spec and proof concerning `SharedAScalar.Insts.CoreOpsArithMulScalarScalar.mul`**:
• Same spec as the core `mul`; proof delegates via `step*`
-/
@[step]
theorem mul_spec (self rhs : scalar.Scalar)
    (h_self : U8x32_as_Nat self.bytes < L)
    (h_rhs : U8x32_as_Nat rhs.bytes < L) :
    mul self rhs ⦃ result =>
      U8x32_as_Nat result.bytes ≡
        U8x32_as_Nat self.bytes * U8x32_as_Nat rhs.bytes [MOD L] ∧
      U8x32_as_Nat result.bytes < L ⦄ := by
  unfold mul
  step*

end curve25519_dalek.SharedAScalar.Insts.CoreOpsArithMulScalarScalar

/-! ## Wrapper: `Scalar * Scalar` (fully by-value)

The following variant wraps the core multiplication by delegating directly to
`Shared0Scalar.Insts.CoreOpsArithMulSharedAScalarScalar.mul`.
Generated by the `define_mul_variants!` macro (macros.rs, lines 107:12-109:13).
-/

namespace curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulScalarScalar

/-
natural language description:

• Takes a Scalar `self` (by value) and a Scalar `rhs` (by value in both Rust
  and the Lean extraction, generated via the `define_mul_variants!` macro in macros.rs)
• Delegates to the core `Shared0Scalar...mul` implementation

natural language specs:

• Same as the core `mul`: always succeeds when both scalars are canonical,
  result ≡ (self * rhs) [MOD L], result < L
-/

/-- **Spec and proof concerning `scalar.Scalar.Insts.CoreOpsArithMulScalarScalar.mul`**:
• Same spec as the core `mul`; proof delegates via `step*`
-/
@[step]
theorem mul_spec (self rhs : scalar.Scalar)
    (h_self : U8x32_as_Nat self.bytes < L)
    (h_rhs : U8x32_as_Nat rhs.bytes < L) :
    mul self rhs ⦃ result =>
      U8x32_as_Nat result.bytes ≡
        U8x32_as_Nat self.bytes * U8x32_as_Nat rhs.bytes [MOD L] ∧
      U8x32_as_Nat result.bytes < L ⦄ := by
  unfold mul
  step*

end curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulScalarScalar
