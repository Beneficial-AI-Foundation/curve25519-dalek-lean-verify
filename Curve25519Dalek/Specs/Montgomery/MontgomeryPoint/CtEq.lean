/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Aux
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromBytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.CtEq
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes
import Mathlib.Data.Nat.ModEq

/-!
# Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::ct_eq`

Compares two `MontgomeryPoint` values for equality in constant time:
- Interprets each `MontgomeryPoint` byte array as a `FieldElement51` via `from_bytes`.
- Calls the `FieldElement51` constant-time equality routine on the two decoded field elements.

Source: "curve25519-dalek/src/montgomery.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.montgomery.MontgomeryPoint.Insts.SubtleConstantTimeEq

/-- **Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::ct_eq`**
• No panic (always returns successfully)
• `Choice.one` is returned iff the two 32-byte encodings represent the same
  field element modulo p (after the `from_bytes` reduction)
-/
@[step]
theorem ct_eq_spec (self other : MontgomeryPoint) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      (c = Choice.one ↔
        (U8x32_as_Nat self % 2 ^ 255) ≡ (U8x32_as_Nat other % 2 ^ 255) [MOD p]) ⦄ := by
  unfold ct_eq
  step*
  have to_bytes_iff_mod (x y : backend.serial.u64.field.FieldElement51) :
      x.to_bytes = y.to_bytes ↔ Field51_as_Nat x % p = Field51_as_Nat y % p := by
    have ⟨xb, hxb_eq, hxb_mod, hxb_lt⟩ := spec_imp_exists (to_bytes_spec x)
    have ⟨yb, hyb_eq, hyb_mod, hyb_lt⟩ := spec_imp_exists (to_bytes_spec y)
    rw [hxb_eq, hyb_eq]
    simp only [ok.injEq]
    have h_x_canon : U8x32_as_Nat xb = Field51_as_Nat x % p := by
      rw [← Nat.mod_eq_of_lt hxb_lt]; exact hxb_mod
    have h_y_canon : U8x32_as_Nat yb = Field51_as_Nat y % p := by
      rw [← Nat.mod_eq_of_lt hyb_lt]; exact hyb_mod
    constructor
    · intro h_bytes
      rw [← h_x_canon, ← h_y_canon, h_bytes]
    · intro h_mod
      have h_nat_eq : U8x32_as_Nat xb = U8x32_as_Nat yb := by
        rw [h_x_canon, h_y_canon]; exact h_mod
      exact U8x32_as_Nat_injective h_nat_eq
  have key := c_post.trans (to_bytes_iff_mod self_fe other_fe)
  rw [key, ← Nat.ModEq]
  constructor
  · intro h; exact (self_fe_post1.symm.trans h).trans other_fe_post1
  · intro h; exact (self_fe_post1.trans h).trans other_fe_post1.symm

end curve25519_dalek.montgomery.MontgomeryPoint.Insts.SubtleConstantTimeEq
