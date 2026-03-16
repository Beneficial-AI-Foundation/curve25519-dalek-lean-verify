/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.BitList
import Curve25519Dalek.ExternallyVerified

/-! # Spec Theorem for `Scalar52::to_bytes`

Specification and proof for `Scalar52::to_bytes`.

This function converts the structure to its byte representation.

Source: curve25519-dalek/src/backend/serial/u64/scalar.rs

## TODO
- Complete proof
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52
open List BitList

/-
natural language description:

    • Takes an unpacked scalar u (five 52-bit limbs stored in U64 values) and
      returns a 32-byte array b that represents the same 256-bit integer value modulo L
      in little-endian byte representation.

natural language specs:

    • u8x32_to_nat(b) ≡ scalar_to_nat(u) (mod L)
-/

/-- The limb bound follows from Equiv. -/
theorem as_nat_bound_of_equiv (self : Scalar52) (result : Array U8 32#usize)
    (h : ∀ i : Fin 4,
      ofU64 self[i]! ≈ₗ (ofByteArray result).extract (52 * i.val) (52 * i.val + 52))
    (h' : (ofU64 self[4]).extract 0 48 ≈ₗ (ofByteArray result).extract 208 256)
    (hbound : Scalar52_as_Nat self < L) :
    U8x32_as_Nat result < L := by
    sorry

/-- Equiv implies the limb value equals the slice value. -/
theorem scalar52_eq_of_bitList (self : Scalar52) (result : Array U8 32#usize)
    (h : ∀ i : Fin 4,
      ofU64 self[i]! ≈ₗ (ofByteArray result).extract (52 * i.val) (52 * i.val + 52))
    (h' : (ofU64 self[4]).extract 0 48 ≈ₗ (ofByteArray result).extract 208 256)
    (hbound : Scalar52_as_Nat self < L) :
    U8x32_as_Nat result = Scalar52_as_Nat self := by
    sorry

/-- The pure List Bool spec for to_bytes, using `BitList.Equiv` (≈ₗ). -/
@[progress]
theorem to_bytes_bitList_spec (self : Scalar52) (h : ∀ i < 5, self[i]!.val < 2 ^ 52)
    (h' : Scalar52_as_Nat self < L) :
    to_bytes self ⦃ (result : Array U8 32#usize) =>
      (∀ i : Fin 4,
        ofU64 self[i]! ≈ₗ (ofByteArray result).extract (52 * i.val) (52 * i.val + 52)) ∧
        (ofU64 self[4]).extract 0 48 ≈ₗ (ofByteArray result).extract 208 256 ⦄ := by
    sorry

/-- **Spec and proof concerning `scalar.Scalar52.to_bytes`**:
- No panic (always returns successfully)
- The result byte array represents the same number as the input unpacked scalar modulo L
- The result is in canonical form (less than L) -/
@[externally_verified, progress] -- proven in Verus
theorem to_bytes_spec (self : Scalar52) (h : ∀ i < 5, self[i]!.val < 2 ^ 52)
    (h' : Scalar52_as_Nat self < L) :
    to_bytes self ⦃ (result : Std.Array U8 32#usize) =>
      U8x32_as_Nat result = Scalar52_as_Nat self ∧
      U8x32_as_Nat result < L ⦄ := by
    progress*
    constructor
    · -- To prove U8x32_as_Nat result = Scalar52_as_Nat self
      rw [scalar52_eq_of_bitList self result _]; repeat assumption
    · -- To prove U8x32_as_Nat result < L
      apply as_nat_bound_of_equiv self result _ _ _; repeat assumption

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
