/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Ristretto.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.CtEq
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Mathlib.Data.Nat.ModEq

/-! # Spec Theorem for `RistrettoPoint::ct_eq`

Specification and proof for the `ConstantTimeEq` trait implementation for `RistrettoPoint`.

This function performs constant-time equality comparison of two Ristretto points by checking
whether X1·Y2 == Y1·X2 or X1·X2 == Y1·Y2 on the underlying extended coordinates, and
returning the bitwise OR of the two comparisons as a `Choice`.

Two Ristretto points (represented as extended twisted Edwards coordinates) are considered
equal if they represent the same element in the Ristretto quotient group 2E/E[4]. The
two cross-product checks capture this equivalence relation. Only X and Y coordinates are
used because the Z coordinates cancel out in the projective ratios.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field.FieldElement51

namespace curve25519_dalek.ristretto.RistrettoPoint.Insts.SubtleConstantTimeEq

/-
natural language description:

    Compares two RistrettoPoint values for equality in constant time.
    RistrettoPoint is a type alias for EdwardsPoint (extended twisted Edwards coordinates
    with fields X, Y, Z, T). Two Ristretto points are considered equal if they represent
    the same element in the Ristretto quotient group 2E/E[4].

    The implementation computes four field multiplications:
      X1Y2 = r1.X * r2.Y,  Y1X2 = r1.Y * r2.X,
      X1X2 = r1.X * r2.X,  Y1Y2 = r1.Y * r2.Y,
    then checks:
      c  = FE51.ct_eq(X1Y2, Y1X2)   -- X1·Y2 == Y1·X2 (mod p)?
      c1 = FE51.ct_eq(X1X2, Y1Y2)   -- X1·X2 == Y1·Y2 (mod p)?
    and returns bitor(c, c1), i.e., Choice.one if either condition holds (as either is sufficient for equality)

    Note: only X and Y coordinates are used because the Z coordinates cancel out
    in the projective cross-product ratios.

natural language specs:

    The result is Choice.one if and only if
      Field51_as_Nat(r1.X) * Field51_as_Nat(r2.Y) ≡ Field51_as_Nat(r1.Y) * Field51_as_Nat(r2.X) (mod p)
    OR
      Field51_as_Nat(r1.X) * Field51_as_Nat(r2.X) ≡ Field51_as_Nat(r1.Y) * Field51_as_Nat(r2.Y) (mod p)
-/

/-- **Spec and proof concerning `ristretto.RistrettoPoint.Insts.SubtleConstantTimeEq.ct_eq`**:
- No panic (always returns successfully given valid inputs)
- The result is Choice.one iff the two points satisfy the multiplicative Ristretto equivalence condition:
  X1·Y2 ≡ Y1·X2 (mod p) or X1·X2 ≡ Y1·Y2 (mod p)
-/
@[progress]
theorem ct_eq_spec
    (self other : RistrettoPoint)
    (h_self_valid : self.IsValid)
    (h_other_valid : other.IsValid) :
    ct_eq self other ⦃ (result : subtle.Choice) =>
      result = Choice.one ↔
        (Field51_as_Nat self.X * Field51_as_Nat other.Y) ≡ (Field51_as_Nat self.Y * Field51_as_Nat other.X) [MOD p] ∨
        (Field51_as_Nat self.X * Field51_as_Nat other.X) ≡ (Field51_as_Nat self.Y * Field51_as_Nat other.Y) [MOD p] ⦄ := by
  have h_s := h_self_valid.1
  have h_o := h_other_valid.1
  unfold ct_eq
  have lb {f : ℕ → ℕ} (h : ∀ i, i < 5 → f i < 2^53) : ∀ i, i < 5 → f i < 2^54 :=
    fun i hi => Nat.lt_trans (h i hi) (by norm_num)
  have := lb h_s.X_bounds
  have := lb h_s.Y_bounds
  have := lb h_o.X_bounds
  have := lb h_o.Y_bounds
  progress as ⟨_, h2⟩
  progress as ⟨_, h4⟩
  progress as ⟨_, h6⟩
  progress as ⟨_, h8⟩
  progress as ⟨h9, h10⟩
  progress as ⟨h11, h12⟩
  unfold subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor
  have tbm (x y : backend.serial.u64.field.FieldElement51) :
      x.to_bytes = y.to_bytes ↔ Field51_as_Nat x % p = Field51_as_Nat y % p := by
    have ⟨xb, hxe, hxm, hxl⟩ := spec_imp_exists (to_bytes_spec x)
    have ⟨yb, hye, hym, hyl⟩ := spec_imp_exists (to_bytes_spec y)
    simp only [hxe, hye, ok.injEq]
    have hx : U8x32_as_Nat xb = Field51_as_Nat x % p := by rw [←Nat.mod_eq_of_lt hxl, hxm]
    have hy : U8x32_as_Nat yb = Field51_as_Nat y % p := by rw [←Nat.mod_eq_of_lt hyl, hym]
    exact ⟨fun h => by rw [←hx, ←hy, h], fun h => U8x32_as_Nat_injective (by rw [hx, hy, h])⟩
  rw [tbm] at h10 h12
  have vo (c : subtle.Choice) : c.val = 1#u8 ↔ c = Choice.one := by
    rcases c with ⟨_, hv | hv⟩
    all_goals simp [hv, Choice.one]
  split
  · rename_i h_or
    exact ⟨fun _ => h_or.elim
      (fun hv => .inl ((h2.symm.trans (h10.mp ((vo h9).mp hv))).trans h4))
      (fun hv => .inr ((h6.symm.trans (h12.mp ((vo h11).mp hv))).trans h8)),
      fun _ => rfl⟩
  · rename_i h_not
    push_neg at h_not
    exact ⟨nofun, fun h_or => h_or.elim
      (fun hmod => absurd ((vo h9).mpr (h10.mpr (h2.trans (hmod.trans h4.symm)))) h_not.1)
      (fun hmod => absurd ((vo h11).mpr (h12.mpr (h6.trans (hmod.trans h8.symm)))) h_not.2)⟩

end curve25519_dalek.ristretto.RistrettoPoint.Insts.SubtleConstantTimeEq
