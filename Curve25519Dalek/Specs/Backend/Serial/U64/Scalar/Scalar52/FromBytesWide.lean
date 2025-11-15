/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryMul
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Add
/-! # Spec Theorem for `Scalar52::from_bytes_wide`

Specification and proof for `Scalar52::from_bytes_wide`.

This function constructs an unpacked scalar from a wide byte array.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-
natural language description:

    • Takes a 64-byte array b as input and returns an unpacked scalar u that
      represents the 512-bit integer value reduced modulo L, redistributed into five limbs.

natural language specs:

    • scalar_to_nat(u) = u8x64_to_nat(b) % L
-/

lemma U8x64_as_Nat_split (b : Array U8 64#usize) :
    ∃ lo4 hi4, U8x64_as_Nat b = Scalar52_as_Nat lo4 + Scalar52_as_Nat hi4 * 2^256 := by
  sorry

/-- **Spec and proof concerning `scalar.Scalar52.from_bytes_wide`**:
- No panic (always returns successfully)
- The result represents the input byte array reduced modulo L (canonical form) -/
@[progress]
theorem from_bytes_wide_spec (b : Array U8 64#usize) :
    ∃ u, from_bytes_wide b = ok u ∧
    Scalar52_as_Nat u = U8x64_as_Nat b % L := by
  unfold from_bytes_wide
  progress*

  -- U8x64_as_Nat b = lo_nat + hi_nat * 2^256
  have h_lo4_hi4: ∃ lo4 hi4, U8x64_as_Nat b = Scalar52_as_Nat lo4 + Scalar52_as_Nat hi4 * 2^256 := U8x64_as_Nat_split b
  obtain ⟨lo4, hi4, h_lo4_hi4⟩ := h_lo4_hi4
  -- (lo * R) / R = lo
  obtain ⟨lo5, h_lo5_ok, h_lo5_spec⟩ := montgomery_mul_spec lo4 constants.R (by sorry) (by sorry)
  obtain ⟨hi5, h_hi5_ok, h_hi5_spec⟩ := montgomery_mul_spec hi4 constants.RR (by sorry) (by sorry)

  -- (hi * R^2) / R + (lo * R) / R = u
  obtain ⟨u, h_u_ok, h_u_spec⟩ := add_spec hi5 lo5

  -- Keypoint:2^256 * R ≡ R^2 [MOD L]
  have h_key : 2^256 * R % L = R^2 % L := by
    sorry
  -- Combine all relations
  use u
  constructor
  · -- from_bytes_wide b = ok u
    sorry
  · -- Scalar52_as_Nat u = U8x64_as_Nat b % L
    sorry

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
