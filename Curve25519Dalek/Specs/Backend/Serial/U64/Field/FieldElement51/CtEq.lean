/-
Copyright (c) 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes

/-! # Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::ct_eq`

This function compares two `FieldElement51` values for equality in constant time. It
normalises both operands to their canonical 32-byte little-endian wire format via
`to_bytes()` and then compares the two byte slices using `ConstantTimeEq` on `[u8]`.

Source: "curve25519-dalek/src/field.rs#L96-L98"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConstantTimeEq

/-- **Spec theorem for `curve25519_dalek::backend::serial::u64::field::FieldElement51::ct_eq`**
• The function always succeeds (no panic)
• The result equals `Choice.one` iff the canonical 32-byte encodings of the inputs agree
  (i.e. iff `a.to_bytes = b.to_bytes`)
-/
@[step]
theorem ct_eq_spec (a b : backend.serial.u64.field.FieldElement51) :
    ct_eq a b ⦃ (c : subtle.Choice) =>
      (c = Choice.one ↔ a.to_bytes = b.to_bytes) ⦄ := by
  unfold ct_eq
  have ⟨a_bytes, ha_ok, _⟩ := spec_imp_exists (to_bytes_spec a)
  have ⟨b_bytes, hb_ok, _⟩ := spec_imp_exists (to_bytes_spec b)
  rw [ha_ok, hb_ok]
  simp only [step_simps]
  let* ⟨ s, s_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ s1, s1_post ⟩ ← Array.to_slice.step_spec
  let* ⟨ c, c_post ⟩ ← Slice.Insts.SubtleConstantTimeEq.ct_eq_spec
  simp_all only [Array.to_slice, Slice.eq_iff]
  exact ⟨fun h => Subtype.ext h, fun h => h ▸ rfl⟩

end curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConstantTimeEq
