/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes
/-! # Spec Theorem for `FieldElement51::ct_eq`

Specification and proof for constant-time equality on FieldElement51.

The Rust implementation normalizes both operands to canonical wire format with
`to_bytes()` and then compares the two byte slices in constant time.

Source: curve25519-dalek/src/field.rs (lines 96:4-98:5)
-/

open Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConstantTimeEq

/-!
Natural language description:

  • Compares two field elements for equality in constant time by comparing their
    canonical 32-byte encodings.

  • Internally computes `a_bytes ← a.to_bytes()` and `b_bytes ← b.to_bytes()`,
    then returns `ConstantTimeEqSlice<u8>(a_bytes, b_bytes)`.

Spec:

  • No panic (always returns successfully)
  • The result is `Choice.one` iff the canonical encodings are equal
    (i.e. iff `to_bytes a = to_bytes b`).
-/


/-- **Spec for `field.ConstantTimeEqFieldElement51.ct_eq`**:
- No panic (always returns successfully)
- Returns `Choice.one` iff the canonical encodings (32-byte LE) are equal
-/
@[progress]
theorem ct_eq_spec (a b : backend.serial.u64.field.FieldElement51) :
    spec (ct_eq a b) (fun c =>
    (c = Choice.one ↔ a.to_bytes = b.to_bytes )) := by
  unfold ct_eq
  have ⟨a_bytes, ha_ok, _⟩ := spec_imp_exists (to_bytes_spec a)
  have ⟨b_bytes, hb_ok, _⟩ := spec_imp_exists (to_bytes_spec b)
  rw [ha_ok, hb_ok]
  progress*
  simp_all only [Array.to_slice, Slice.eq_iff]
  exact ⟨fun h => Subtype.ext h, fun h => h ▸ rfl⟩

end curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConstantTimeEq
