-- [curve25519_dalek]: external functions.
import Aeneas
import Curve25519Dalek.Types
open Aeneas.Std Result

namespace curve25519_dalek

/- Convenience definitions for Choice values -/
def Choice.zero : subtle.Choice := { val := 0#u8, valid := Or.inl rfl }
def Choice.one : subtle.Choice := { val := 1#u8, valid := Or.inr rfl }

/- [subtle::{subtle::Choice}::unwrap_u8]:
   Name pattern: [subtle::{subtle::Choice}::unwrap_u8]
   Returns 0u8 if Choice.zero (0), 1u8 if Choice.one (1) -/
def subtle.Choice.unwrap_u8 (c : subtle.Choice) : Result U8 :=
  ok c.val

/- [subtle::{core::ops::bit::BitAnd<subtle::Choice, subtle::Choice> for subtle::Choice}::bitand]:
Name pattern: [subtle::{core::ops::bit::BitAnd<subtle::Choice, subtle::Choice, subtle::Choice>}::bitand]
Bitwise AND for Choice values (0 & 0 = 0, 0 & 1 = 0, 1 & 0 = 0, 1 & 1 = 1) -/
def subtle.BitAndsubtleChoicesubtleChoicesubtleChoice.bitand
  (a : subtle.Choice) (b : subtle.Choice) : Result subtle.Choice :=
  if a.val = 0#u8 ∨ b.val = 0#u8 then
    ok Choice.zero
  else
    ok Choice.one

/- [subtle::{core::convert::From<u8> for subtle::Choice}::from]:
   Name pattern: [subtle::{core::convert::From<subtle::Choice, u8>}::from]
   Converts a u8 to a Choice. The input should be 0 or 1. -/
def subtle.FromsubtleChoiceU8.from (input : U8) : Result subtle.Choice :=
  if h : input = 0#u8 then
    ok { val := input, valid := Or.inl h }
  else if h' : input = 1#u8 then
    ok { val := input, valid := Or.inr h' }
  else
    fail Error.panic

/- [subtle::{core::convert::From<subtle::Choice> for bool}::from]:
   Name pattern: [subtle::{core::convert::From<bool, subtle::Choice>}::from]
   Converts Choice to bool: Choice.zero -> false, Choice.one -> true -/
def subtle.FromBoolsubtleChoice.from (c : subtle.Choice) : Result Bool :=
  ok (c.val = 1#u8)

/- [subtle::{core::ops::bit::BitOr<subtle::Choice, subtle::Choice> for subtle::Choice}::bitor]:
   Name pattern: [subtle::{core::ops::bit::BitOr<subtle::Choice, subtle::Choice, subtle::Choice>}::bitor]
   Bitwise OR for Choice values (0 | 0 = 0, 0 | 1 = 1, 1 | 0 = 1, 1 | 1 = 1) -/
def subtle.BitOrsubtleChoicesubtleChoicesubtleChoice.bitor
  (a : subtle.Choice) (b : subtle.Choice) : Result subtle.Choice :=
  if a.val = 1#u8 ∨ b.val = 1#u8 then
    ok Choice.one
  else
    ok Choice.zero

/- [subtle::{subtle::ConditionallyNegatable for T}::conditional_negate]:
   Name pattern: [subtle::{subtle::ConditionallyNegatable<@T>}::conditional_negate]
   Negate self if choice == Choice(1); otherwise, leave it unchanged -/
def subtle.ConditionallyNegatable.Blanket.conditional_negate
  {T : Type} (ConditionallySelectableInst : subtle.ConditionallySelectable T)
  (coreopsarithNeg_TTInst : core.ops.arith.Neg T T)
  (self : T) (choice : subtle.Choice) : Result T := do
  let self_neg ← coreopsarithNeg_TTInst.neg self
  ConditionallySelectableInst.conditional_select self self_neg choice

/- [subtle::{subtle::ConstantTimeEq for @Slice<T>}::ct_eq]:
   Name pattern: [subtle::{subtle::ConstantTimeEq<[@T]>}::ct_eq]
   Constant-time equality for slices -/
axiom subtle.ConstantTimeEqSlice.ct_eq
  {T : Type} (ConstantTimeEqInst : subtle.ConstantTimeEq T)
  : Slice T → Slice T → Result subtle.Choice

/- Specification axiom for equal-length slices -/
axiom subtle.ConstantTimeEqSlice.ct_eq_spec
  {T : Type} (ConstantTimeEqInst : subtle.ConstantTimeEq T) (a b : Slice T) (ha : a.length < 2 ^ UScalarTy.Usize.numBits)
  (hb : b.length < 2 ^ UScalarTy.Usize.numBits) (h_eq_len : a.length = b.length) :
  let result := subtle.ConstantTimeEqSlice.ct_eq ConstantTimeEqInst a b
  -- Returns Choice(1) if and only if all elements are equal
  result = ok Choice.one ↔
  (∀ i : Nat, (hi : i < a.length) →
     ∃ (elem_a elem_b : T) (eq_result : subtle.Choice),
       let i_bound : i < 2 ^ UScalarTy.Usize.numBits := Nat.lt_trans hi ha
       Slice.index_usize a ⟨i, i_bound⟩ = ok elem_a ∧
       Slice.index_usize b ⟨i, i_bound⟩ = ok elem_b ∧
       ConstantTimeEqInst.ct_eq elem_a elem_b = ok eq_result ∧
       eq_result.val = 1#u8)

/- [subtle::{subtle::ConstantTimeEq for u8}::ct_eq]:
Name pattern: [subtle::{subtle::ConstantTimeEq<u8>}::ct_eq]
Constant-time equality for U8 values -/
def subtle.ConstantTimeEqU8.ct_eq (a : U8) (b : U8) : Result subtle.Choice :=
  if a = b then ok Choice.one
  else ok Choice.zero

/- [subtle::{subtle::ConditionallySelectable for u64}::conditional_select]:
Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_select]
Conditional select: returns a if choice(0), b if choice(1) -/
def subtle.ConditionallySelectableU64.conditional_select
  (a : U64) (b : U64) (choice : subtle.Choice) : Result U64 :=
  if choice.val = 1#u8 then ok b
  else ok a

/- [subtle::{subtle::ConditionallySelectable for u64}::conditional_assign]:
   Conditionally assign b to a if choice(1); otherwise leave a unchanged -/
def subtle.ConditionallySelectableU64.conditional_assign
  (a : U64) (b : U64) (choice : subtle.Choice) : Result U64 :=
  subtle.ConditionallySelectableU64.conditional_select a b choice

/- [subtle::{subtle::ConditionallySelectable for u64}::conditional_swap]:
   Conditionally swap a and b if choice(1); otherwise leave them unchanged -/
def subtle.ConditionallySelectableU64.conditional_swap
  (a : U64) (b : U64) (choice : subtle.Choice) : Result (U64 × U64) := do
  let a_new ← subtle.ConditionallySelectableU64.conditional_select a b choice
  let b_new ← subtle.ConditionallySelectableU64.conditional_select b a choice
  ok (a_new, b_new)

/- [subtle::{subtle::CtOption<T>}::new]:
Name pattern: [subtle::{subtle::CtOption<@T>}::new]
Create a new CtOption with a value and a Choice indicating if it's Some -/
def subtle.CtOption.new
  {T : Type} (value : T) (is_some : subtle.Choice) : Result (subtle.CtOption T) :=
  ok { value := value, is_some := is_some }

end curve25519_dalek
