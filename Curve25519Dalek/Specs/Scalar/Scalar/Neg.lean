/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.FromBytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MulInternal
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryReduce
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Pack
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Zero
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.R

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::neg`

Negates a scalar modulo the group order ℓ = 2^252 + 27742317777372353535851937790883648493.
The input `self` is passed by value in the Lean extraction (corresponding to the Rust `&Scalar`
reference). The computation proceeds as follows:
1. Unpacking the input from its 32-byte little-endian representation into the 5-limb base-2^52
   internal representation (`Scalar52`) via `Scalar::unpack` (which calls `Scalar52::from_bytes`);
   each limb is bounded by 2^62 and the represented integer equals the little-endian byte value
2. Computing `self_R = Scalar52::mul_internal(s, R)` — the wide 9-limb product of the unpacked
   scalar with the Montgomery constant R = 2^260; each product limb is bounded by 2^127
3. Calling `Scalar52::montgomery_reduce(self_R)` to recover `self_mod_l ≡ s (mod ℓ)` in
   canonical form (each limb < 2^52), via the Montgomery reduction identity:
   `montgomery_reduce(s · R) * R ≡ s · R (mod ℓ)  ⟹  montgomery_reduce(s · R) ≡ s (mod ℓ)`
   (valid since gcd(R, ℓ) = 1)
4. Calling `Scalar52::sub(ZERO, self_mod_l)` which computes 0 − self_mod_l modulo ℓ using
   limb-wise borrow propagation with a conditional addition of ℓ on underflow; when
   self_mod_l = 0 the result is 0, otherwise ℓ − self_mod_l ∈ (0, ℓ)
5. Packing the canonical `Scalar52` back into a 32-byte `Scalar` via `Scalar52::pack`

The input must satisfy Scalar invariant #2 (canonical form), i.e., its byte encoding represents
an integer strictly less than ℓ. This invariant is always satisfied by publicly observable
scalars in the library.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

set_option exponentiation.threshold 260

namespace curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithNegScalar

private lemma R_limb_bounds : ∀ i < 5, backend.serial.u64.constants.R[i]!.val < 2 ^ 62 := by
  unfold backend.serial.u64.constants.R; decide

private lemma ZERO_limb_bounds :
    ∀ i < 5, backend.serial.u64.scalar.Scalar52.ZERO[i]!.val < 2 ^ 52 := by
  unfold backend.serial.u64.scalar.Scalar52.ZERO; decide

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::neg`**
• The function always succeeds (no panic) when `self` is a canonical scalar
  (`U8x32_as_Nat self.bytes < L`)
• The result satisfies `U8x32_as_Nat result.bytes + U8x32_as_Nat self.bytes ≡ 0 [MOD L]`,
  i.e., result ≡ −self (mod ℓ)
• The result is canonical: `U8x32_as_Nat result.bytes < L`
-/
@[step]
theorem neg_spec (self : scalar.Scalar)
    (h_self : U8x32_as_Nat self.bytes < L) :
    neg self ⦃ (result : scalar.Scalar) =>
      U8x32_as_Nat result.bytes + U8x32_as_Nat self.bytes ≡ 0 [MOD L] ∧
      U8x32_as_Nat result.bytes < L ⦄ := by
  unfold neg
  unfold scalar.Scalar.unpack
  step as ⟨s, hs_nat, hs_bounds⟩
  step as ⟨self_R, hself_R_nat, hself_R_bounds⟩
  · exact R_limb_bounds
  step as ⟨self_mod_l, h_mont_eq, h_mod_bounds, h_mod_lt⟩
  · -- h_canonical: Scalar52_wide_as_Nat self_R < R * L
    rw [hself_R_nat]
    have h_s_lt_L : Scalar52_as_Nat s < L := hs_nat ▸ h_self
    have h_R_lt_R : Scalar52_as_Nat backend.serial.u64.constants.R < R :=
      Scalar52_as_Nat_bounded _ (by unfold backend.serial.u64.constants.R; decide)
    have h_L_pos : 0 < L := by unfold L; omega
    nlinarith [Nat.mul_comm L R]
  have hmod_le_L : Scalar52_as_Nat self_mod_l ≤ L := Nat.le_of_lt h_mod_lt
  have hZERO_lt : Scalar52_as_Nat backend.serial.u64.scalar.Scalar52.ZERO <
      Scalar52_as_Nat self_mod_l + L := by
    simp only [backend.serial.u64.scalar.Scalar52.ZERO_spec]
    linarith
  have hZERO_bounds : ∀ i < 5, backend.serial.u64.scalar.Scalar52.ZERO[i]!.val < 2 ^ 52 :=
    ZERO_limb_bounds
  step as ⟨s1, hs1_cong, hs1_lt, _⟩
  step as ⟨hpack, hpack_cong, hpack_lt⟩
  refine ⟨?_, hpack_lt⟩
  have h_R_cong : Scalar52_as_Nat backend.serial.u64.constants.R ≡ R [MOD L] :=
    backend.serial.u64.constants.R_spec
  have h_wide_cong : Scalar52_wide_as_Nat self_R ≡ Scalar52_as_Nat s * R [MOD L] := by
    rw [hself_R_nat]
    exact Nat.ModEq.mul_left _ h_R_cong
  have h_mont_cong : Scalar52_as_Nat self_mod_l * R ≡ Scalar52_as_Nat s * R [MOD L] :=
    h_mont_eq.trans h_wide_cong
  have h_self_mod_l_eq : Scalar52_as_Nat self_mod_l ≡ Scalar52_as_Nat s [MOD L] :=
    Nat.ModEq.cancel_right_of_coprime (by decide) h_mont_cong
  have h_self_mod_cong : Scalar52_as_Nat self_mod_l ≡ U8x32_as_Nat self.bytes [MOD L] :=
    hs_nat ▸ h_self_mod_l_eq
  rw [backend.serial.u64.scalar.Scalar52.ZERO_spec] at hs1_cong
  calc U8x32_as_Nat hpack.bytes + U8x32_as_Nat self.bytes
      ≡ Scalar52_as_Nat s1 + U8x32_as_Nat self.bytes [MOD L] :=
        Nat.ModEq.add_right _ hpack_cong
    _ ≡ Scalar52_as_Nat s1 + Scalar52_as_Nat self_mod_l [MOD L] :=
        Nat.ModEq.add_left _ h_self_mod_cong.symm
    _ ≡ 0 [MOD L] := hs1_cong

end curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithNegScalar

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::neg`

The following variant wraps the core negation by delegating directly to
`Shared0Scalar.Insts.CoreOpsArithNegScalar.neg`.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithNegScalar

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::neg`**
• The function always succeeds (no panic) when `self` is a canonical scalar
  (`U8x32_as_Nat self.bytes < L`)
• The result satisfies `U8x32_as_Nat result.bytes + U8x32_as_Nat self.bytes ≡ 0 [MOD L]`
• The result is canonical: `U8x32_as_Nat result.bytes < L`
-/
@[step]
theorem neg_spec (self : scalar.Scalar)
    (h_self : U8x32_as_Nat self.bytes < L) :
    neg self ⦃ (result : scalar.Scalar) =>
      U8x32_as_Nat result.bytes + U8x32_as_Nat self.bytes ≡ 0 [MOD L] ∧
      U8x32_as_Nat result.bytes < L ⦄ := by
  unfold neg
  step*

end curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithNegScalar
