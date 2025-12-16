import Aeneas

/-! # Definitions

Common definitions used across spec theorems.
-/

open Aeneas.Std Result

/-! ## Constants -/

/-- Curve25519 is the elliptic curve over the prime field with order p -/
def p : Nat := 2^255 - 19

/-- The group order L for Scalar52 arithmetic -/
def L : Nat := 2^252 + 27742317777372353535851937790883648493

/-- The Montgomery constant R = 2^260 used for Scalar52 Montgomery form conversions -/
def R : Nat := 2^260

/-- The cofactor of Curve25519 -/
def h : Nat := 8

/-- The constant d in the defining equation for the twisted Edwards curve: ax^2 + y^2 = 1 + dx^2y^2 -/
def d : Nat := 37095705934669439343138083508754565189542113879843219016388785533085940283555

/-- The constant a in the defining equation for the twisted Edwards curve: ax^2 + y^2 = 1 + dx^2y^2 -/
def a : Int := -1

/-! ## Auxiliary definitions for interpreting arrays as natural numbers -/

/-- Interpret a Field51 (five u64 limbs used to represent 51 bits each) as a natural number -/
def Field51_as_Nat (limbs : Array U64 5#usize) : Nat :=
  ∑ i ∈ Finset.range 5, 2^(51 * i) * (limbs[i]!).val

/-- Interpret a Field51 (five UInt64 limbs used to represent 51 bits each) as a natural number -/
def FAE_Field51_as_Nat (limbs : Vector UInt64 5) : ℕ :=
  ∑ i : Fin 5, 2^(51 * (i : ℕ)) * (((limbs.get i).toBitVec).toNat)

def U64.to_UInt : U64 → UInt64 := (.ofBitVec ·)

def UInt.to_U64 : UInt64 → U64 := (⟨·.toBitVec.toNat, by scalar_tac⟩)

def UInt_equiv : UInt64 ≃ U64 where
  toFun := UInt.to_U64
  invFun := U64.to_UInt
  left_inv := by
    intro v
    simp [U64.to_UInt, UInt.to_U64]
  right_inv := by
    intro v
    simp [U64.to_UInt, UInt.to_U64]; rfl

@[simp]
lemma UInt_comp : UInt.to_U64 ∘ U64.to_UInt = id := Function.RightInverse.id UInt_equiv.right_inv

@[simp]
lemma U64_comp : U64.to_UInt ∘ UInt.to_U64 = id := Function.RightInverse.id UInt_equiv.left_inv

def eq_field51 : Array U64 5#usize ≃ Vector UInt64 5 where
  toFun := fun A ↦ ⟨(List.map U64.to_UInt A).toArray,
      by simp [List.size_toArray, List.length_map, List.Vector.length_val, UScalar.ofNat_val_eq]⟩
  invFun := fun ⟨A, l⟩ ↦ ⟨List.map UInt.to_U64 A.toList, by
      rwa [List.length_map, Array.length_toList, UScalar.ofNat_val_eq]⟩
  left_inv := fun _ ↦ by simp
  right_inv := fun _ ↦ by simp


/-- Interpret a Scalar52 (five u64 limbs used to represent 52 bits each) as a natural number -/
def Scalar52_as_Nat (limbs : Array U64 5#usize) : Nat :=
  ∑ i ∈ Finset.range 5, 2^(52 * i) * (limbs[i]!).val

/-- Interpret a 9-element u128 array (each limb representing 52 bits) as a natural number -/
def Scalar52_wide_as_Nat (limbs : Array U128 9#usize) : Nat :=
  ∑ i ∈ Finset.range 9, 2^(52 * i) * (limbs[i]!).val

/-- Interpret a 32-element byte array as a natural number. -/
def U8x32_as_Nat (bytes : Array U8 32#usize) : Nat :=
  ∑ i ∈ Finset.range 32, 2^(8 * i) * (bytes[i]!).val

/-- Interpret a 64-element byte array as a natural number. -/
def U8x64_as_Nat (bytes : Array U8 64#usize) : Nat :=
  ∑ i ∈ Finset.range 64, 2^(8 * i) * (bytes[i]!).val
