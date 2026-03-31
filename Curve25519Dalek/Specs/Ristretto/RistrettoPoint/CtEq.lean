/-
Copyright 2026 Beneficial AI Foundation. All rights reserved.
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
    and returns bitor(c, c1), i.e., Choice.one if either condition holds
    (as either is sufficient for equality)

    Note: only X and Y coordinates are used because the Z coordinates cancel out
    in the projective cross-product ratios.

natural language specs:

    The result is Choice.one if and only if
      Field51_as_Nat(r1.X) * Field51_as_Nat(r2.Y)
        ≡ Field51_as_Nat(r1.Y) * Field51_as_Nat(r2.X) (mod p)
    OR
      Field51_as_Nat(r1.X) * Field51_as_Nat(r2.X)
        ≡ Field51_as_Nat(r1.Y) * Field51_as_Nat(r2.Y) (mod p)
-/

/-- **Spec and proof concerning
`ristretto.RistrettoPoint.Insts.SubtleConstantTimeEq.ct_eq`**:
- No panic (always returns successfully given valid inputs)
- The result is Choice.one iff the two points satisfy the multiplicative
  Ristretto equivalence condition:
  X1·Y2 ≡ Y1·X2 (mod p) or X1·X2 ≡ Y1·Y2 (mod p)
-/
@[step]
theorem ct_eq_spec
    (self other : RistrettoPoint)
    (h_self_valid : self.IsValid)
    (h_other_valid : other.IsValid) :
    ct_eq self other ⦃ (result : subtle.Choice) =>
      result = Choice.one ↔
        (Field51_as_Nat self.X * Field51_as_Nat other.Y) ≡
          (Field51_as_Nat self.Y * Field51_as_Nat other.X) [MOD p] ∨
        (Field51_as_Nat self.X * Field51_as_Nat other.X) ≡
          (Field51_as_Nat self.Y * Field51_as_Nat other.Y) [MOD p] ⦄ := by
  unfold ct_eq
  step*
  all_goals (try (
    have lb {f : ℕ → ℕ} (h : ∀ i, i < 5 → f i < 2^53) : ∀ i, i < 5 → f i < 2^54 :=
      fun i hi => Nat.lt_trans (h i hi) (by norm_num)
    first
    | exact lb h_self_valid.1.X_bounds
    | exact lb h_self_valid.1.Y_bounds
    | exact lb h_other_valid.1.X_bounds
    | exact lb h_other_valid.1.Y_bounds))
  unfold subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor
  have tbm (x y : backend.serial.u64.field.FieldElement51) :
      x.to_bytes = y.to_bytes ↔ Field51_as_Nat x % p = Field51_as_Nat y % p := by
    have ⟨xb, hxe, hxm, hxl⟩ := spec_imp_exists (to_bytes_spec x)
    have ⟨yb, hye, hym, hyl⟩ := spec_imp_exists (to_bytes_spec y)
    simp only [hxe, hye, ok.injEq]
    have hx : U8x32_as_Nat xb = Field51_as_Nat x % p := by rw [←Nat.mod_eq_of_lt hxl, hxm]
    have hy : U8x32_as_Nat yb = Field51_as_Nat y % p := by rw [←Nat.mod_eq_of_lt hyl, hym]
    exact ⟨fun h => by rw [←hx, ←hy, h], fun h => U8x32_as_Nat_injective (by rw [hx, hy, h])⟩
  rw [tbm] at c_post c1_post
  rw [X1Y2_post1, Y1X2_post1] at c_post
  rw [X1X2_post1, Y1Y2_post1] at c1_post
  have vo (c : subtle.Choice) : c.val = 1#u8 ↔ c = Choice.one := by
    rcases c with ⟨_, hv | hv⟩
    all_goals (subst hv;
               simp only [Choice.one, subtle.Choice.mk.injEq])
  split
  · rename_i h
    exact ⟨fun _ => h.elim (.inl ∘ c_post.mp ∘ (vo c).mp)
        (.inr ∘ c1_post.mp ∘ (vo c1).mp), fun _ => rfl⟩
  · rename_i h
    push_neg at h
    exact ⟨nofun, fun hm => hm.elim
      (fun hm => absurd ((vo c).mpr (c_post.mpr hm)) h.1)
      (fun hm => absurd ((vo c1).mpr (c1_post.mpr hm)) h.2)⟩

end curve25519_dalek.ristretto.RistrettoPoint.Insts.SubtleConstantTimeEq
