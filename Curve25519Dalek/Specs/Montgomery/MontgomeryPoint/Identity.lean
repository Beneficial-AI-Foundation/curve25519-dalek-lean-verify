/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-!
# Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::identity`

• Returns the identity element of the Montgomery curve group for `MontgomeryPoint`
• The identity element has group order 4
• It is represented as 32 zero bytes

Source: "curve25519-dalek/src/montgomery.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek
namespace curve25519_dalek.montgomery.MontgomeryPoint.Insts.Curve25519_dalekTraitsIdentity

/-- **Spec theorem for `curve25519_dalek::montgomery::MontgomeryPoint::identity`**
• The function always succeeds (no panic)
• The resulting `MontgomeryPoint` is 32 zero bytes
• Interpreted as a natural number via `U8x32_as_Nat`, the result equals 0
-/
@[step]
theorem identity_spec :
    identity ⦃ (result : MontgomeryPoint) =>
      (∀ i : Fin 32, result[i]! = 0#u8) ∧
      U8x32_as_Nat result = 0 ⦄ := by
  unfold identity
  suffices (∀ (i : Fin 32), (Array.repeat 32#usize 0#u8)[i] = 0#u8) ∧
    U8x32_as_Nat (Array.repeat 32#usize 0#u8) = 0 by simpa
  constructor
  · intro i
    fin_cases i <;> simp_all only [Fin.zero_eta, Fin.isValue, Fin.getElem_fin, Nat.reduceAdd,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod] <;> decide
  · unfold U8x32_as_Nat
    simp only [Finset.sum_eq_zero_iff, Finset.mem_range]
    intro i hi
    have : (Array.repeat 32#usize 0#u8 : List U8)[i]!.val = 0 := by
      interval_cases i <;> simp [Array.repeat]
    simpa [*]

end curve25519_dalek.montgomery.MontgomeryPoint.Insts.Curve25519_dalekTraitsIdentity
