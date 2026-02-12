-- [curve25519_dalek]: external functions.
import Aeneas
import Curve25519Dalek.Types
-- import Mathlib

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace curve25519_dalek

/- Convenience definitions for Choice values -/
def Choice.zero : subtle.Choice := { val := 0#u8, valid := Or.inl rfl }
def Choice.one : subtle.Choice := { val := 1#u8, valid := Or.inr rfl }

/- [subtle::{subtle::Choice}::unwrap_u8]:
   Name pattern: [subtle::{subtle::Choice}::unwrap_u8]
   Returns 0u8 if Choice.zero (0), 1u8 if Choice.one (1) -/
def subtle.Choice.unwrap_u8 (c : subtle.Choice) : Result U8 :=
  ok c.val

/- [subtle::{core::convert::From<subtle::Choice> for bool}::from]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 153:4-153:35
   Name pattern: [subtle::{core::convert::From<bool, subtle::Choice>}::from]
   Converts Choice to bool: Choice.zero -> false, Choice.one -> true -/
@[rust_fun "subtle::{core::convert::From<bool, subtle::Choice>}::from"]
def Bool.Insts.CoreConvertFromChoice.from (c : subtle.Choice) : Result Bool :=
  ok (c.val = 1#u8)

/- [subtle::{core::ops::bit::BitAnd<subtle::Choice, subtle::Choice> for subtle::Choice}::bitand]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 162:4-162:42
   Name pattern: [subtle::{core::ops::bit::BitAnd<subtle::Choice, subtle::Choice, subtle::Choice>}::bitand] -/
@[rust_fun
  "subtle::{core::ops::bit::BitAnd<subtle::Choice, subtle::Choice, subtle::Choice>}::bitand"]
def subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand
  (a : subtle.Choice) (b : subtle.Choice) : Result subtle.Choice :=
  if a.val = 0#u8 ∨ b.val = 0#u8 then
    ok Choice.zero
  else
    ok Choice.one

/-- **Spec theorem for `subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand`**:
- No panic (always returns successfully)
- Returns `Choice.one` if and only if both inputs are `Choice.one`
-/
@[progress]
theorem subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand_spec (a b : subtle.Choice) :
    subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand a b ⦃ c =>
    (c = Choice.one ↔ a = Choice.one ∧ b = Choice.one) ⦄ := by
  unfold subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand
  split
  · -- Case: a.val = 0 ∨ b.val = 0
    rename_i h_or
    simp only [spec_ok]
    constructor
    · intro h
      -- Choice.zero = Choice.one is impossible
      cases h
    · intro ⟨ha, hb⟩
      -- a = Choice.one ∧ b = Choice.one, but a.val = 0 ∨ b.val = 0 is a contradiction
      rw [ha, hb] at h_or
      unfold Choice.one at h_or
      simp at h_or
  · -- Case: ¬(a.val = 0 ∨ b.val = 0)
    rename_i h_not_or
    simp only [spec_ok]
    constructor
    · intro _
      -- Need to show a = Choice.one ∧ b = Choice.one
      constructor
      · -- Show a = Choice.one
        cases a with | mk val valid =>
        cases valid with
        | inl h =>
          -- val = 0, but this contradicts h_not_or
          simp [h] at h_not_or
        | inr h =>
          -- val = 1, so a = Choice.one
          unfold Choice.one
          simp [h]
      · -- Show b = Choice.one
        cases b with | mk val valid =>
        cases valid with
        | inl h =>
          -- val = 0, but this contradicts h_not_or
          simp [h] at h_not_or
        | inr h =>
          -- val = 1, so b = Choice.one
          unfold Choice.one
          simp [h]
    · intro ⟨ha, hb⟩
      -- a = Choice.one ∧ b = Choice.one, so we're done
      trivial

/- [subtle::{core::ops::bit::BitOr<subtle::Choice, subtle::Choice> for subtle::Choice}::bitor]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 177:4-177:41
   Name pattern: [subtle::{core::ops::bit::BitOr<subtle::Choice, subtle::Choice, subtle::Choice>}::bitor]
   Bitwise OR for Choice values (0 | 0 = 0, 0 | 1 = 1, 1 | 0 = 1, 1 | 1 = 1) -/
@[rust_fun
  "subtle::{core::ops::bit::BitOr<subtle::Choice, subtle::Choice, subtle::Choice>}::bitor"]
def subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor (a : subtle.Choice) (b : subtle.Choice) :
    Result subtle.Choice :=
  if a.val = 1#u8 ∨ b.val = 1#u8 then
    ok Choice.one
  else
    ok Choice.zero

/- [subtle::{core::ops::bit::Not<subtle::Choice> for subtle::Choice}::not]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 207:4-207:26
   Name pattern: [subtle::{core::ops::bit::Not<subtle::Choice, subtle::Choice>}::not]
   Bitwise NOT for Choice values (NOT 0 = 1, NOT 1 = 0) -/
@[rust_fun
  "subtle::{core::ops::bit::Not<subtle::Choice, subtle::Choice>}::not"]
def subtle.Choice.Insts.CoreOpsBitNotChoice.not (c : subtle.Choice) : Result subtle.Choice :=
  if c.val = 1#u8 then
    ok Choice.zero
  else
    ok Choice.one

/- [subtle::{subtle::ConstantTimeEq for u16}::ct_eq]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 348:12-348:51
   Name pattern: [subtle::{subtle::ConstantTimeEq<u16>}::ct_eq]
   Constant-time equality for U16 values -/
@[rust_fun "subtle::{subtle::ConstantTimeEq<u16>}::ct_eq"]
def U16.Insts.SubtleConstantTimeEq.ct_eq (a : U16) (b : U16) : Result subtle.Choice :=
  if a = b then ok Choice.one
  else ok Choice.zero

/-- **Spec theorem for `U16.Insts.SubtleConstantTimeEq.ct_eq`**:
- No panic (always returns successfully)
- Returns `Choice.one` if and only if the two U16 values are equal
-/
@[progress]
theorem U16.Insts.SubtleConstantTimeEq.ct_eq_spec (a b : U16) :
  U16.Insts.SubtleConstantTimeEq.ct_eq a b ⦃ c =>
  (c = Choice.one ↔ a = b) ⦄ := by
  unfold U16.Insts.SubtleConstantTimeEq.ct_eq
  split
  · -- Case: a = b
    rename_i h_eq
    simp only [spec_ok]
    simp [h_eq]
  · -- Case: a ≠ b
    rename_i h_ne
    simp only [spec_ok]
    constructor
    · intro h
      -- Choice.zero = Choice.one is a contradiction
      cases h
    · intro h
      -- a = b but a ≠ b is a contradiction
      contradiction

/- [subtle::{core::convert::From<u8> for subtle::Choice}::from]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 238:4-238:32
   Name pattern: [subtle::{core::convert::From<subtle::Choice, u8>}::from]
   Converts a u8 to a Choice. The input should be 0 or 1. -/
@[rust_fun "subtle::{core::convert::From<subtle::Choice, u8>}::from"]
def subtle.Choice.Insts.CoreConvertFromU8.from (input : U8) : Result subtle.Choice :=
  if h : input = 0#u8 then
    ok { val := input, valid := Or.inl h }
  else if h' : input = 1#u8 then
    ok { val := input, valid := Or.inr h' }
  else
    fail Error.panic

/- [subtle::{subtle::ConstantTimeEq for @Slice<T>}::ct_eq]:
   Name pattern: [subtle::{subtle::ConstantTimeEq<[@T]>}::ct_eq]
   Constant-time equality for slices -/
@[rust_fun "subtle::{subtle::ConstantTimeEq<[@T]>}::ct_eq"]
axiom Slice.Insts.SubtleConstantTimeEq.ct_eq
  {T : Type} (ConstantTimeEqInst : subtle.ConstantTimeEq T)
  : Slice T → Slice T → Result subtle.Choice

/-- **Spec theorem for `Slice.Insts.SubtleConstantTimeEq.ct_eq`**:
- No panic (always returns successfully)
- Returns Choice.one (true) if and only if all corresponding elements are equal
- Requires equal-length slices with valid bounds
-/
@[progress]
axiom Slice.Insts.SubtleConstantTimeEq.ct_eq_spec
  {T : Type} (ConstantTimeEqInst : subtle.ConstantTimeEq T) (a b : Slice T)
  (ha : a.length < 2 ^ UScalarTy.Usize.numBits)
  (hb : b.length < 2 ^ UScalarTy.Usize.numBits)
  (h_eq_len : a.length = b.length) :
  Slice.Insts.SubtleConstantTimeEq.ct_eq ConstantTimeEqInst a b ⦃ c =>
  (c = Choice.one ↔ a = b) ⦄

/- [subtle::{subtle::ConstantTimeEq for u8}::ct_eq]:
Name pattern: [subtle::{subtle::ConstantTimeEq<u8>}::ct_eq]
Constant-time equality for U8 values -/
@[rust_fun "subtle::{subtle::ConstantTimeEq<u8>}::ct_eq"]
def U8.Insts.SubtleConstantTimeEq.ct_eq (a : U8) (b : U8) : Result subtle.Choice :=
  if a = b then ok Choice.one
  else ok Choice.zero

/-- **Spec theorem for `U8.Insts.SubtleConstantTimeEq.ct_eq`**:
- No panic (always returns successfully)
- Returns `Choice.one` if and only if the two U8 values are equal
-/
@[progress]
theorem U8.Insts.SubtleConstantTimeEq.ct_eq_spec (a b : U8) :
  U8.Insts.SubtleConstantTimeEq.ct_eq a b ⦃ c =>
  (c = Choice.one ↔ a = b) ⦄ := by
  unfold U8.Insts.SubtleConstantTimeEq.ct_eq
  split
  · -- Case: a = b
    rename_i h_eq
    simp only [spec_ok]
    simp [h_eq]
  · -- Case: a ≠ b
    rename_i h_ne
    simp only [spec_ok]
    constructor
    · intro h
      -- Choice.zero = Choice.one is a contradiction
      cases h
    · intro h
      -- a = b but a ≠ b is a contradiction
      contradiction

/- [subtle::ConditionallySelectable::conditional_assign]:
   Source: '/home/oliver/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 442:4-442:66
   Name pattern: [subtle::ConditionallySelectable::conditional_assign]
   Conditionally assign: returns conditional_select(a, b, choice) -/
@[rust_fun "subtle::ConditionallySelectable::conditional_assign"]
def subtle.ConditionallySelectable.conditional_assign.default
  {Self : Type} (ConditionallySelectableInst : subtle.ConditionallySelectable
  Self) :
  Self → Self → subtle.Choice → Result Self :=
  fun a b choice =>
    ConditionallySelectableInst.conditional_select a b choice

/-- **Spec theorem for `subtle.ConditionallySelectable.conditional_assign.default`**:
- No panic (if conditional_select succeeds)
- Returns the result of conditional_select(a, b, choice)
-/
@[progress]
theorem subtle.ConditionallySelectable.conditional_assign.default_spec
  {Self : Type} (ConditionallySelectableInst : subtle.ConditionallySelectable Self)
  (a b : Self) (choice : subtle.Choice)
  (h : ∃ res, ConditionallySelectableInst.conditional_select a b choice = ok res) :
  subtle.ConditionallySelectable.conditional_assign.default ConditionallySelectableInst a b choice ⦃ res =>
  ConditionallySelectableInst.conditional_select a b choice = ok res ⦄ := by
  unfold subtle.ConditionallySelectable.conditional_assign.default
  obtain ⟨res, h_eq⟩ := h
  simp only [h_eq, spec_ok]

/- [subtle::ConditionallySelectable::conditional_swap]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 469:4-469:67
   Name pattern: [subtle::ConditionallySelectable::conditional_swap]
   Conditionally swap a and b if choice(1); otherwise leave them unchanged -/
@[rust_fun "subtle::ConditionallySelectable::conditional_swap"]
def subtle.ConditionallySelectable.conditional_swap.default
  {Self : Type} (ConditionallySelectableInst : subtle.ConditionallySelectable
  Self) :
  Self → Self → subtle.Choice → Result (Self × Self) :=
  fun a b choice => do
    let a_new ← ConditionallySelectableInst.conditional_select a b choice
    let b_new ← ConditionallySelectableInst.conditional_select b a choice
    ok (a_new, b_new)

/-- **Spec theorem for `subtle.ConditionallySelectable.conditional_swap.default`**:
- No panic (if conditional_select succeeds)
- Returns (a_new, b_new) where:
  - a_new = conditional_select(a, b, choice)
  - b_new = conditional_select(b, a, choice)
- If choice = Choice.one: swaps a and b
- If choice = Choice.zero: leaves them unchanged
-/
@[progress]
theorem subtle.ConditionallySelectable.conditional_swap.default_spec
  {Self : Type} (ConditionallySelectableInst : subtle.ConditionallySelectable Self)
  (a b : Self) (choice : subtle.Choice)
  (h_a : ∃ res, ConditionallySelectableInst.conditional_select a b choice = ok res)
  (h_b : ∃ res, ConditionallySelectableInst.conditional_select b a choice = ok res) :
  subtle.ConditionallySelectable.conditional_swap.default ConditionallySelectableInst a b choice ⦃ c =>
    ConditionallySelectableInst.conditional_select a b choice = ok c.1 ∧
    ConditionallySelectableInst.conditional_select b a choice = ok c.2 ⦄ := by
  unfold subtle.ConditionallySelectable.conditional_swap.default
  obtain ⟨a_new, h_a_eq⟩ := h_a
  obtain ⟨b_new, h_b_eq⟩ := h_b
  simp only [h_a_eq, h_b_eq, bind_tc_ok, spec_ok, and_self]

/- [subtle::{subtle::ConditionallySelectable for u64}::conditional_select]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 513:12-513:77
   Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_select]
Conditional select: returns a if choice(0), b if choice(1) -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<u64>}::conditional_select"]
def U64.Insts.SubtleConditionallySelectable.conditional_select
  (a : U64) (b : U64) (choice : subtle.Choice) : Result U64 :=
  if choice.val = 1#u8 then ok b
  else ok a

/-- Progress spec for U64.Insts.SubtleConditionallySelectable.conditional_select -/
@[progress]
theorem U64.Insts.SubtleConditionallySelectable.conditional_select_spec (a b : U64) (choice : subtle.Choice) :
    U64.Insts.SubtleConditionallySelectable.conditional_select a b choice ⦃ res =>
    res = if choice.val = 1#u8 then b else a ⦄ := by
  unfold U64.Insts.SubtleConditionallySelectable.conditional_select
  split <;> simp_all

/- [subtle::{subtle::ConditionallySelectable for u64}::conditional_assign]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 521:12-521:74
   Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_assign]
   Conditionally assign b to a if choice(1); otherwise leave a unchanged -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<u64>}::conditional_assign"]
def U64.Insts.SubtleConditionallySelectable.conditional_assign
  (a : U64) (b : U64) (choice : subtle.Choice) : Result U64 :=
  U64.Insts.SubtleConditionallySelectable.conditional_select a b choice

/- [subtle::{subtle::ConditionallySelectable for u64}::conditional_swap]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 529:12-529:75
   Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_swap]
   Conditionally swap a and b if choice(1); otherwise leave them unchanged -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u64>}::conditional_swap"]
def U64.Insts.SubtleConditionallySelectable.conditional_swap
  (a : U64) (b : U64) (choice : subtle.Choice) : Result (U64 × U64) := do
  let a_new ← U64.Insts.SubtleConditionallySelectable.conditional_select a b choice
  let b_new ← U64.Insts.SubtleConditionallySelectable.conditional_select b a choice
  ok (a_new, b_new)

/- [subtle::{subtle::ConditionallyNegatable for T}::conditional_negate]:
   Name pattern: [subtle::{subtle::ConditionallyNegatable<@T>}::conditional_negate]
   Negate self if choice == Choice(1); otherwise, leave it unchanged -/
def subtle.ConditionallyNegatable.Blanket.conditional_negate
  {T : Type} (ConditionallySelectableInst : subtle.ConditionallySelectable T)
  (coreopsarithNeg_TTInst : core.ops.arith.Neg T T)
  (self : T) (choice : subtle.Choice) : Result T := do
  let self_neg ← coreopsarithNeg_TTInst.neg self
  ConditionallySelectableInst.conditional_select self self_neg choice

/- [subtle::{subtle::CtOption<T>}::new]:
Name pattern: [subtle::{subtle::CtOption<@T>}::new]
Create a new CtOption with a value and a Choice indicating if it's Some -/
@[rust_fun "subtle::{subtle::CtOption<@T>}::new"]
def subtle.CtOption.new
  {T : Type} (value : T) (is_some : subtle.Choice) : Result (subtle.CtOption T) :=
  ok { value := value, is_some := is_some }

/-- **Spec theorem for `subtle.CtOption.new`**:
- No panic (always returns successfully)
- Returns a CtOption with the given value and is_some flag
- The returned CtOption's fields match the inputs exactly
-/
@[progress]
theorem subtle.CtOption.new_spec {T : Type} (value : T) (is_some : subtle.Choice) :
  subtle.CtOption.new value is_some ⦃ opt =>
  opt.value = value ∧ opt.is_some = is_some ⦄ := by
  unfold subtle.CtOption.new
  simp [spec_ok]

/- [zeroize::{zeroize::Zeroize for Z}::zeroize]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.8.2/src/lib.rs', lines 301:4-301:25
   Name pattern: [zeroize::{zeroize::Zeroize<@Z>}::zeroize] -/
@[rust_fun "zeroize::{zeroize::Zeroize<@Z>}::zeroize"]
axiom zeroize.Zeroize.Blanket.zeroize
  {Z : Type} (DefaultIsZeroesInst : zeroize.DefaultIsZeroes Z) : Z → Result Z

/- [zeroize::{zeroize::Zeroize for @Array<Z, N>}::zeroize]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.8.2/src/lib.rs', lines 373:4-373:25
   Name pattern: [zeroize::{zeroize::Zeroize<[@Z; @N]>}::zeroize] -/
@[rust_fun "zeroize::{zeroize::Zeroize<[@Z; @N]>}::zeroize"]
axiom Array.Insts.ZeroizeZeroize.zeroize
  {Z : Type} {N : Usize} (ZeroizeInst : zeroize.Zeroize Z) :
  Array Z N → Result (Array Z N)

/- [curve25519_dalek::backend::serial::curve_models::{subtle::ConditionallySelectable for curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint}::conditional_swap]:
   Source: 'curve25519-dalek/src/backend/serial/curve_models/mod.rs', lines 296:0-312:1 -/
axiom
  backend.serial.curve_models.ProjectiveNielsPoint.Insts.SubtleConditionallySelectable.conditional_swap
  :
  backend.serial.curve_models.ProjectiveNielsPoint →
    backend.serial.curve_models.ProjectiveNielsPoint → subtle.Choice →
    Result (backend.serial.curve_models.ProjectiveNielsPoint ×
    backend.serial.curve_models.ProjectiveNielsPoint)

/- [curve25519_dalek::backend::serial::curve_models::{subtle::ConditionallySelectable for curve25519_dalek::backend::serial::curve_models::AffineNielsPoint}::conditional_swap]:
   Source: 'curve25519-dalek/src/backend/serial/curve_models/mod.rs', lines 314:0-328:1 -/
axiom
  backend.serial.curve_models.AffineNielsPoint.Insts.SubtleConditionallySelectable.conditional_swap
  :
  backend.serial.curve_models.AffineNielsPoint →
    backend.serial.curve_models.AffineNielsPoint → subtle.Choice → Result
    (backend.serial.curve_models.AffineNielsPoint ×
    backend.serial.curve_models.AffineNielsPoint)

/- [subtle::{subtle::ConditionallySelectable for u8}::conditional_select]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 513:12-513:77
   Name pattern: [subtle::{subtle::ConditionallySelectable<u8>}::conditional_select]
   Conditional select: returns a if choice(0), b if choice(1) -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u8>}::conditional_select"]
def U8.Insts.SubtleConditionallySelectable.conditional_select
  (a : U8) (b : U8) (choice : subtle.Choice) : Result U8 :=
  if choice.val = 1#u8 then ok b
  else ok a

/-- Progress spec for U8.Insts.SubtleConditionallySelectable.conditional_select -/
@[progress]
theorem U8.Insts.SubtleConditionallySelectable.conditional_select_spec (a b : U8) (choice : subtle.Choice) :
    U8.Insts.SubtleConditionallySelectable.conditional_select a b choice ⦃ res =>
    res = if choice.val = 1#u8 then b else a ⦄ := by
  unfold U8.Insts.SubtleConditionallySelectable.conditional_select
  split <;> simp_all

/- [subtle::{subtle::ConditionallySelectable for u8}::conditional_assign]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 521:12-521:74
   Name pattern: [subtle::{subtle::ConditionallySelectable<u8>}::conditional_assign]
   Conditionally assign b to a if choice(1); otherwise leave a unchanged -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u8>}::conditional_assign"]
def U8.Insts.SubtleConditionallySelectable.conditional_assign
  (a : U8) (b : U8) (choice : subtle.Choice) : Result U8 :=
  U8.Insts.SubtleConditionallySelectable.conditional_select a b choice

/- [subtle::{subtle::ConditionallySelectable for u8}::conditional_swap]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 529:12-529:75
   Name pattern: [subtle::{subtle::ConditionallySelectable<u8>}::conditional_swap]
   Conditionally swap a and b if choice(1); otherwise leave them unchanged -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u8>}::conditional_swap"]
def U8.Insts.SubtleConditionallySelectable.conditional_swap
  (a : U8) (b : U8) (choice : subtle.Choice) : Result (U8 × U8) := do
  let a_new ← U8.Insts.SubtleConditionallySelectable.conditional_select a b choice
  let b_new ← U8.Insts.SubtleConditionallySelectable.conditional_select b a choice
  ok (a_new, b_new)

/- [zeroize::{zeroize::Zeroize for alloc::vec::Vec<Z>}::zeroize]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.8.2/src/lib.rs', lines 551:4-551:25
   Name pattern: [zeroize::{zeroize::Zeroize<alloc::vec::Vec<@Z>>}::zeroize] -/
@[rust_fun "zeroize::{zeroize::Zeroize<alloc::vec::Vec<@Z>>}::zeroize"]
axiom alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize
  {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) :
  alloc.vec.Vec Z → Result (alloc.vec.Vec Z)

/- [curve25519_dalek::backend::serial::curve_models::{core::cmp::PartialEq<curve25519_dalek::backend::serial::curve_models::AffineNielsPoint> for curve25519_dalek::backend::serial::curve_models::AffineNielsPoint}::ne]:
   Source: 'curve25519-dalek/src/backend/serial/curve_models/mod.rs', lines 182:26-182:35 -/
axiom backend.serial.curve_models.AffineNielsPoint.Insts.CoreCmpPartialEqAffineNielsPoint.ne
  :
  backend.serial.curve_models.AffineNielsPoint →
    backend.serial.curve_models.AffineNielsPoint → Result Bool

/- [curve25519_dalek::field::{core::cmp::PartialEq<curve25519_dalek::backend::serial::u64::field::FieldElement51> for curve25519_dalek::backend::serial::u64::field::FieldElement51}::ne]:
   Source: 'curve25519-dalek/src/field.rs', lines 86:0-90:1 -/
axiom backend.serial.u64.field.FieldElement51.Insts.CoreCmpPartialEqFieldElement51.ne
  :
  backend.serial.u64.field.FieldElement51 →
    backend.serial.u64.field.FieldElement51 → Result Bool

/- [curve25519_dalek::scalar::{core::cmp::PartialEq<curve25519_dalek::scalar::Scalar> for curve25519_dalek::scalar::Scalar}::ne]:
   Source: 'curve25519-dalek/src/scalar.rs', lines 294:0-298:1 -/
axiom scalar.Scalar.Insts.CoreCmpPartialEqScalar.ne
  : scalar.Scalar → scalar.Scalar → Result Bool

/- [curve25519_dalek::scalar::{core::cmp::Eq for curve25519_dalek::scalar::Scalar}::assert_receiver_is_total_eq]:
   Source: 'curve25519-dalek/src/scalar.rs', lines 293:0-293:21 -/
axiom scalar.Scalar.Insts.CoreCmpEq.assert_receiver_is_total_eq
  : scalar.Scalar → Result Unit

/- [curve25519_dalek::scalar::{subtle::ConditionallySelectable for curve25519_dalek::scalar::Scalar}::conditional_assign]:
   Source: 'curve25519-dalek/src/scalar.rs', lines 389:0-398:1 -/
axiom scalar.Scalar.Insts.SubtleConditionallySelectable.conditional_assign
  : scalar.Scalar → scalar.Scalar → subtle.Choice → Result scalar.Scalar

/- [curve25519_dalek::scalar::{subtle::ConditionallySelectable for curve25519_dalek::scalar::Scalar}::conditional_swap]:
   Source: 'curve25519-dalek/src/scalar.rs', lines 389:0-398:1 -/
axiom scalar.Scalar.Insts.SubtleConditionallySelectable.conditional_swap
  :
  scalar.Scalar → scalar.Scalar → subtle.Choice → Result (scalar.Scalar
    × scalar.Scalar)

/- [subtle::{subtle::ConditionallySelectable for @Array<T, N>}::conditional_select]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 581:4-581:69
   Name pattern: [subtle::{subtle::ConditionallySelectable<[@T; @N]>}::conditional_select]
   Conditional select for arrays: returns a if choice=0, b if choice=1 -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<[@T; @N]>}::conditional_select"]
def Array.Insts.SubtleConditionallySelectable.conditional_select
  {T : Type} {N : Usize} (_ConditionallySelectableInst :
  subtle.ConditionallySelectable T)
  (a : Array T N) (b : Array T N) (choice : subtle.Choice) : Result (Array T N) :=
  if choice.val = 1#u8 then ok b
  else ok a

/-- Progress spec for Array.Insts.SubtleConditionallySelectable.conditional_select -/
@[progress]
theorem Array.Insts.SubtleConditionallySelectable.conditional_select_spec {T : Type} {N : Usize}
    (inst : subtle.ConditionallySelectable T)
    (a b : Array T N) (choice : subtle.Choice) :
    Array.Insts.SubtleConditionallySelectable.conditional_select inst a b choice ⦃ res =>
    res = if choice.val = 1#u8 then b else a ⦄ := by
  unfold Array.Insts.SubtleConditionallySelectable.conditional_select
  split <;> simp_all

/- [subtle::{subtle::ConditionallySelectable for @Array<T, N>}::conditional_assign]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 587:4-587:66
   Name pattern: [subtle::{subtle::ConditionallySelectable<[@T; @N]>}::conditional_assign]
   Conditional assign for arrays: assign a with the value of conditional_select(a, b, choice). -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<[@T; @N]>}::conditional_assign"]
def Array.Insts.SubtleConditionallySelectable.conditional_assign
  {T : Type} {N : Usize} (ConditionallySelectableInst :
  subtle.ConditionallySelectable T)
  (a : Array T N) (b : Array T N) (choice : subtle.Choice) : Result (Array T N) :=
  Array.Insts.SubtleConditionallySelectable.conditional_select ConditionallySelectableInst a b choice

/- [subtle::{subtle::ConditionallySelectable for @Array<T, N>}::conditional_swap]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 576:0-578:31
   Name pattern: [subtle::{subtle::ConditionallySelectable<[@T; @N]>}::conditional_swap]
   Conditional swap for arrays: swaps a and b if choice is 1 -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<[@T; @N]>}::conditional_swap"]
def Array.Insts.SubtleConditionallySelectable.conditional_swap
  {T : Type} {N : Usize} (ConditionallySelectableInst :
  subtle.ConditionallySelectable T)
  (a : Array T N) (b : Array T N) (choice : subtle.Choice) : Result ((Array T N) × (Array T N)) := do
  let a_new ← Array.Insts.SubtleConditionallySelectable.conditional_select ConditionallySelectableInst a b choice
  let b_new ← Array.Insts.SubtleConditionallySelectable.conditional_select ConditionallySelectableInst b a choice
  ok (a_new, b_new)

/- [curve25519_dalek::montgomery::{subtle::ConditionallySelectable for curve25519_dalek::montgomery::ProjectivePoint}::conditional_swap]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 311:0-322:1 -/
axiom montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_swap
  :
  montgomery.ProjectivePoint → montgomery.ProjectivePoint → subtle.Choice
    → Result (montgomery.ProjectivePoint × montgomery.ProjectivePoint)

/- [curve25519_dalek::montgomery::{subtle::ConditionallySelectable for curve25519_dalek::montgomery::MontgomeryPoint}::conditional_assign]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 87:0-91:1 -/
axiom montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_assign
  :
  montgomery.MontgomeryPoint → montgomery.MontgomeryPoint → subtle.Choice
    → Result montgomery.MontgomeryPoint

/- [curve25519_dalek::montgomery::{subtle::ConditionallySelectable for curve25519_dalek::montgomery::MontgomeryPoint}::conditional_swap]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 87:0-91:1 -/
axiom montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_swap
  :
  montgomery.MontgomeryPoint → montgomery.MontgomeryPoint → subtle.Choice
    → Result (montgomery.MontgomeryPoint × montgomery.MontgomeryPoint)

/- [curve25519_dalek::montgomery::{core::cmp::PartialEq<curve25519_dalek::montgomery::MontgomeryPoint> for curve25519_dalek::montgomery::MontgomeryPoint}::ne]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 93:0-97:1 -/
axiom montgomery.MontgomeryPoint.Insts.CoreCmpPartialEqMontgomeryPoint.ne
  : montgomery.MontgomeryPoint → montgomery.MontgomeryPoint → Result Bool

/- [curve25519_dalek::montgomery::{core::cmp::Eq for curve25519_dalek::montgomery::MontgomeryPoint}::assert_receiver_is_total_eq]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 99:0-99:30 -/
axiom montgomery.MontgomeryPoint.Insts.CoreCmpEq.assert_receiver_is_total_eq
  : montgomery.MontgomeryPoint → Result Unit

/- [curve25519_dalek::montgomery::{subtle::ConditionallySelectable for curve25519_dalek::montgomery::ProjectivePoint}::conditional_assign]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 311:0-322:1 -/
axiom montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_assign
  :
  montgomery.ProjectivePoint → montgomery.ProjectivePoint → subtle.Choice
    → Result montgomery.ProjectivePoint

end curve25519_dalek
