/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Defs.Edwards.Representation

/-! # Spec Theorem for `ProjectivePoint::as_affine`

Specification and proof for `ProjectivePoint::as_affine`.

This function converts a Montgomery ProjectivePoint (U:W) to affine coordinates
by computing U / W in the field and returning the canonical byte encoding.

**Source**: curve25519-dalek/src/montgomery.rs
-/

open Aeneas
open scoped Aeneas
open scoped Aeneas.Std.WP
open Aeneas.Std Result
namespace curve25519_dalek.montgomery.ProjectivePoint

/-
natural language description:

    • Computes the affine Montgomery u-coordinate from projective coordinates (U:W)
      by computing u = U / W in 𝔽_p.
    • Returns the canonical 32-byte encoding of u.

natural language specs:

    • The function always succeeds (no panic) for valid field element inputs
    • If W ≠ 0 (mod p), the output u satisfies u * W ≡ U (mod p)
    • If W = 0 (mod p), the output is zero
    • The output bytes are canonical (< p)
-/

/-- **Spec and proof concerning `montgomery.ProjectivePoint.as_affine`**:
- No panic (always returns successfully)
- If W ≠ 0 (mod p), the affine u satisfies u * W ≡ U (mod p)
- If W = 0 (mod p), the output encodes zero
- The output bytes are canonical (< p)
-/
@[progress]
theorem as_affine_spec (pp : ProjectivePoint)
  (hU : backend.serial.u64.field.FieldElement51.IsValid pp.U)
  (hW : backend.serial.u64.field.FieldElement51.IsValid pp.W) :
  as_affine pp ⦃ mp =>
    let u := Field51_as_Nat pp.U % p
    let w := Field51_as_Nat pp.W % p
    (w ≠ 0 → (U8x32_as_Nat mp * w) % p = u) ∧
    (w = 0 → U8x32_as_Nat mp = 0) ∧
    U8x32_as_Nat mp < p ⦄ := by
  sorry

end curve25519_dalek.montgomery.ProjectivePoint
