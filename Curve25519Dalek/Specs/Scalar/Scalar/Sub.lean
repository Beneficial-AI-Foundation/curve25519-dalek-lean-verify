/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.FromBytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Pack

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::sub`

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

This file covers both the `Scalar - Scalar` (by-value) and `Scalar - &Scalar`
(by-reference) trait implementations; the by-reference variant delegates to the
by-value one.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithSubSharedAScalarScalar

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::sub`**
• The function always succeeds (no panic)
• The result satisfies:
  `U8x32_as_Nat result.bytes + U8x32_as_Nat rhs.bytes ≡ U8x32_as_Nat self.bytes [MOD L]`
• The result is canonical: `U8x32_as_Nat result.bytes < L`
-/
@[step]
theorem sub_spec (self rhs : scalar.Scalar)
    (h_self : U8x32_as_Nat self.bytes < L)
    (h_rhs : U8x32_as_Nat rhs.bytes < L) :
    sub self rhs ⦃ (result : scalar.Scalar) =>
      U8x32_as_Nat result.bytes + U8x32_as_Nat rhs.bytes ≡
        U8x32_as_Nat self.bytes [MOD L] ∧
      U8x32_as_Nat result.bytes < L ⦄ := by
  unfold sub
  unfold scalar.Scalar.unpack
  step as ⟨s, hs_nat, hs_bounds⟩
  step as ⟨s1, hs1_nat, hs1_bounds⟩
  have hs_lt : Scalar52_as_Nat s < Scalar52_as_Nat s1 + L := by
    rw [hs_nat]; omega
  have hs1_le_L : Scalar52_as_Nat s1 ≤ L := by rw [hs1_nat]; exact Nat.le_of_lt h_rhs
  step as ⟨s2, hs2_cong, hs2_lt, _⟩
  step as ⟨hpack, hpack_cong, hpack_lt⟩
  refine ⟨?_, hpack_lt⟩
  have hcong : U8x32_as_Nat hpack.bytes + U8x32_as_Nat rhs.bytes ≡
               Scalar52_as_Nat s2 + Scalar52_as_Nat s1 [MOD L] := by
    rw [← hs1_nat]
    exact Nat.ModEq.add_right _ hpack_cong
  rw [hs_nat] at hs2_cong
  exact Nat.ModEq.trans hcong hs2_cong

end curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithSubSharedAScalarScalar

namespace curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithSubSharedBScalarScalar

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::sub`**
• The function always succeeds (no panic)
• The result satisfies:
  `U8x32_as_Nat result.bytes + U8x32_as_Nat rhs.bytes ≡ U8x32_as_Nat self.bytes [MOD L]`
• The result is canonical: `U8x32_as_Nat result.bytes < L`
-/
@[step]
theorem sub_spec (self rhs : Scalar)
    (h_self : U8x32_as_Nat self.bytes < L)
    (h_rhs : U8x32_as_Nat rhs.bytes < L) :
    sub self rhs ⦃ (result : Scalar) =>
      U8x32_as_Nat result.bytes + U8x32_as_Nat rhs.bytes ≡
        U8x32_as_Nat self.bytes [MOD L] ∧
      U8x32_as_Nat result.bytes < L ⦄ := by
  unfold sub
  step*

end curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithSubSharedBScalarScalar
