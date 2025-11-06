/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryMul
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.RR

set_option exponentiation.threshold 260

/-! # Spec Theorem for `Scalar52::as_montgomery`

Specification and proof for `Scalar52::as_montgomery`.

This function converts to Montgomery form.

Source: curve25519-dalek/src/backend/serial/u64/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-
natural language description:

    • Takes an input unpacked scalar u and returns an unpacked scalar m representing
      the value (u * R) mod L, where R = 2^260 is the Montgomery constant and L is the group order.

natural language specs:

    • scalar_to_nat(m) = (scalar_to_nat(u) * R) mod L
-/

/-- **Spec and proof concerning `scalar.Scalar52.as_montgomery`**:
- No panic (always returns successfully)
- The result represents the input scalar multiplied by the Montgomery constant R = 2^260, modulo L
-/
theorem as_montgomery_spec (u : Scalar52) :
    ∃ m, as_montgomery u = ok m ∧
    Scalar52_as_Nat m ≡ (Scalar52_as_Nat u * R) [MOD L] := by
  unfold as_montgomery
  have := montgomery_mul_spec u constants.RR
  obtain ⟨m, pos, pos'⟩ := this
  refine ⟨m, pos, ?_⟩
  have rr_eq := RR_spec
  -- From montgomery_mul_spec: (u * RR) ≡ m * R [MOD L]
  -- From RR_spec: RR ≡ R^2 [MOD L]
  -- Substituting: u * R^2 ≡ m * R [MOD L]
  -- Therefore: m ≡ u * R [MOD L]
  calc Scalar52_as_Nat m
      ≡ Scalar52_as_Nat m [MOD L] := by rfl
    _ ≡ Scalar52_as_Nat u * R [MOD L] := by
        -- From pos': (u * RR) ≡ m * R [MOD L]
        -- From rr_eq: RR ≡ R^2 [MOD L]
        have h1 : Scalar52_as_Nat u * Scalar52_as_Nat constants.RR ≡
                  Scalar52_as_Nat u * (R ^ 2) [MOD L] := by
          apply Nat.ModEq.mul_left
          exact rr_eq
        have h2 : Scalar52_as_Nat u * (R ^ 2) ≡
                  Scalar52_as_Nat m * R [MOD L] := by
          exact Nat.ModEq.trans h1.symm pos'
        -- Now we have: u * R^2 ≡ m * R [MOD L]
        -- We need: m ≡ u * R [MOD L]
        -- This requires cancelling R, which needs coprimality
        have coprime_L_R : L.gcd R = 1 := by decide
        have h3 : Scalar52_as_Nat m * R ≡ Scalar52_as_Nat u * (R ^ 2) [MOD L] := h2.symm
        -- Rewrite R^2 as R * R
        have h4 : Scalar52_as_Nat u * (R ^ 2) = Scalar52_as_Nat u * R * R := by ring
        rw [h4] at h3
        -- Cancel R from both sides
        exact Nat.ModEq.cancel_right_of_coprime coprime_L_R h3

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
