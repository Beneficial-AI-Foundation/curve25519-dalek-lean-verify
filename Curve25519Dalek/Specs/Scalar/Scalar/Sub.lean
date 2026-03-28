/-
Copyright 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.FromBytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Pack
/-! # Spec theorem for `Scalar::sub`

Specification and proof for the
`Sub<&'a Scalar, Scalar> for &Scalar` trait implementation for Scalar.

This function subtracts two scalars modulo the group order
ℓ = 2^252 + 27742317777372353535851937790883648493
by:
1. Unpacking both inputs from their 32-byte little-endian representation into
   the 5-limb base-2^52 internal representation (`Scalar52`) via `Scalar::unpack`,
   which internally calls `Scalar52::from_bytes`
2. Calling `Scalar52::sub` to subtract the two unpacked scalars with limb-wise borrow
   propagation and a final conditional addition of ℓ if the difference underflowed,
   producing a result in [0, ℓ)
3. Packing the result back into a canonical 32-byte `Scalar` via `Scalar52::pack`

Both inputs must satisfy Scalar invariant #2 (canonical form), i.e., their byte
encodings represent integers strictly less than ℓ.  This invariant is always satisfied
by publicly observable scalars in the library.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithSubSharedAScalarScalar

/-
natural language description:

• Takes two Scalars `self` and `rhs` (both passed by value in the Lean extraction,
  corresponding to the Rust `&Scalar` references)
• Unpacks both via `Scalar::unpack`, which delegates to `Scalar52::from_bytes` to
  produce 5-limb base-2^52 `Scalar52` values; each limb is bounded by 2^52 and the
  represented integer equals the little-endian value of the byte array
• Calls `Scalar52::sub` which performs limb-wise subtraction with borrow propagation,
  then adds ℓ if the difference underflowed (i.e., self < rhs in the field), yielding
  a canonical result in [0, ℓ)
• Packs the canonical `Scalar52` back into a 32-byte `Scalar` via `Scalar52::pack`

natural language specs:

• The function always succeeds (no panic) when both input scalars are canonical
  (their byte values satisfy U8x32_as_Nat bytes < ℓ)
• The result's byte representation, viewed as a little-endian integer, satisfies
  (U8x32_as_Nat result.bytes + U8x32_as_Nat rhs.bytes) ≡ U8x32_as_Nat self.bytes
  modulo ℓ, i.e., result ≡ self - rhs [MOD ℓ]
• The result is canonical: U8x32_as_Nat result.bytes < ℓ
-/

/-- **Spec and proof concerning `Shared0Scalar.Insts.CoreOpsArithSubSharedAScalarScalar.sub`**:
• Precondition: both `self` and `rhs` are canonical scalars (their byte values are < ℓ),
  consistent with Scalar invariant #2
• The function always succeeds (no panic)
• The result satisfies:
  `U8x32_as_Nat result.bytes + U8x32_as_Nat rhs.bytes ≡ U8x32_as_Nat self.bytes [MOD L]`
• The result is canonical: `U8x32_as_Nat result.bytes < L`
-/
@[progress]
theorem sub_spec (self rhs : scalar.Scalar)
    (h_self : U8x32_as_Nat self.bytes < L)
    (h_rhs : U8x32_as_Nat rhs.bytes < L) :
    sub self rhs ⦃ (result : scalar.Scalar) =>
      U8x32_as_Nat result.bytes + U8x32_as_Nat rhs.bytes ≡
        U8x32_as_Nat self.bytes [MOD L] ∧
      U8x32_as_Nat result.bytes < L ⦄ := by
  unfold sub
  unfold scalar.Scalar.unpack
  progress as ⟨s, hs_nat, hs_bounds⟩
  progress as ⟨s1, hs1_nat, hs1_bounds⟩
  have hs_lt   : Scalar52_as_Nat s  < Scalar52_as_Nat s1 + L := by
    rw [hs_nat]; omega
  have hs1_le_L : Scalar52_as_Nat s1 ≤ L := by rw [hs1_nat]; exact Nat.le_of_lt h_rhs
  progress as ⟨s2, hs2_cong, hs2_lt, _⟩
  progress as ⟨hpack, hpack_cong, hpack_lt⟩
  refine ⟨?_, hpack_lt⟩
  have hcong : U8x32_as_Nat hpack.bytes + U8x32_as_Nat rhs.bytes ≡
               Scalar52_as_Nat s2 + Scalar52_as_Nat s1 [MOD L] := by
    rw [← hs1_nat]
    exact Nat.ModEq.add_right _ hpack_cong
  rw [hs_nat] at hs2_cong
  exact Nat.ModEq.trans hcong hs2_cong

end curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithSubSharedAScalarScalar

/-! ## Wrapper: `Scalar - &Scalar`

The following variant wraps the core subtraction by delegating directly to
`Shared0Scalar.Insts.CoreOpsArithSubSharedAScalarScalar.sub`.
-/

namespace curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithSubSharedBScalarScalar

/-
natural language description:

• Takes a Scalar `self` (by value) and a Scalar `rhs` (by reference in Rust,
  by value in the Lean extraction)
• Delegates to the core `Shared0Scalar...sub` implementation

natural language specs:

• Same as the core `sub`: always succeeds when both scalars are canonical,
  result + rhs ≡ self [MOD L], result < L
-/

/-- **Spec and proof concerning `scalar.Scalar.Insts.CoreOpsArithSubSharedBScalarScalar.sub`**:
• Same spec as the core `sub`; proof delegates via `progress*`
-/
@[progress]
theorem sub_spec (self rhs : scalar.Scalar)
    (h_self : U8x32_as_Nat self.bytes < L)
    (h_rhs : U8x32_as_Nat rhs.bytes < L) :
    sub self rhs ⦃ (result : scalar.Scalar) =>
      U8x32_as_Nat result.bytes + U8x32_as_Nat rhs.bytes ≡
        U8x32_as_Nat self.bytes [MOD L] ∧
      U8x32_as_Nat result.bytes < L ⦄ := by
  unfold sub
  progress*

end curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithSubSharedBScalarScalar
