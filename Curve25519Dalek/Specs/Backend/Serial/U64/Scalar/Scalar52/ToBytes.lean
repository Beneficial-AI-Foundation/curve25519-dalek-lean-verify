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
theorem limb_bound_of_equiv (b : Array U8 32#usize) (u : Scalar52)
    (hequiv : ∀ i : Fin 5,
      ofU64 u[i]! ≈ₗ (ofByteArray b).extract (52 * i.val) (52 * i.val + 52)) :
    U8x32_as_Nat b < L := by
    -- Since Scalar52_as_Nat u < L
    sorry

/-- Equiv implies the limb value equals the slice value. -/
theorem scalar52_eq_of_bitList (b : Array U8 32#usize) (u : Scalar52)
    (hequiv : ∀ i : Fin 5,
      ofU64 u[i]! ≈ₗ (ofByteArray b).extract (52 * i.val) (52 * i.val + 52)) :
    U8x32_as_Nat b = Scalar52_as_Nat u := by
    sorry

/-- The pure List Bool spec for to_bytes, using `BitList.Equiv` (≈ₗ). -/
@[progress]
theorem to_bytes_bitList_spec (u : Scalar52) :
    to_bytes u ⦃ (b : Array U8 32#usize) =>
      ∀ i : Fin 5,
        ofU64 u[i]! ≈ₗ (ofByteArray b).extract (52 * i.val) (52 * i.val + 52) ⦄ := by
    sorry

/-- **Spec and proof concerning `scalar.Scalar52.to_bytes`**:
- No panic (always returns successfully)
- The result byte array represents the same number as the input unpacked scalar modulo L
- The result is in canonical form (less than L) -/
@[externally_verified, progress] -- proven in Verus
theorem to_bytes_spec (u : Scalar52) :
    to_bytes u ⦃ b =>
    U8x32_as_Nat b ≡ Scalar52_as_Nat u [MOD L] ∧
    U8x32_as_Nat b < L ⦄ := by
    progress*
    constructor
    · -- To prove U8x32_as_Nat b ≡ Scalar52_as_Nat u [MOD L]
      rw [scalar52_eq_of_bitList b u _]
      assumption
    · -- To prove U8x32_as_Nat b < L
      exact limb_bound_of_equiv b u ‹_›

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
