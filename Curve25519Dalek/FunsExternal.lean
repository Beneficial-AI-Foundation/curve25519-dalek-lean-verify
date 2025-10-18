-- [curve25519_dalek]: external functions.
import Aeneas
import Curve25519Dalek.Types
open Aeneas.Std Result

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

/- [subtle::{subtle::ConditionallySelectable for u64}::conditional_select]:
   Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_select]
   Conditional select: returns a if choice=0, b if choice=1 -/
def subtle.ConditionallySelectableU64.conditional_select
  (a : U64) (b : U64) (choice : subtle.Choice) : Result U64 :=
  if choice.val = 1#u8 then
    ok b
  else
    ok a
