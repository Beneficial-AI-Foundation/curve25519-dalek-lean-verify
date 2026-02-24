-- [curve25519_dalek]: external functions.
import Aeneas
import Curve25519Dalek.Types

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace curve25519_dalek

/- [core::result::{core::result::Result<T, E>}::map]:
   Source: '/rustc/library/core/src/result.rs', lines 831:4-833:53
   Name pattern: [core::result::{core::result::Result<@T, @E>}::map] -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::map"]
axiom core.result.Result.map
  {T : Type} {E : Type} {U : Type} {F : Type} (opsfunctionFnOnceFTupleTUInst :
  core.ops.function.FnOnce F T U) :
  core.result.Result T E → F → Result (core.result.Result U E)

/- [core::slice::index::{core::slice::index::SliceIndex<@Slice<T>, @Slice<T>> for core::ops::range::RangeFull}::index_mut]:
   Source: '/rustc/library/core/src/slice/index.rs', lines 660:4-660:51
   Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index_mut] -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index_mut"]
axiom
  core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut
  {T : Type} :
  core.ops.range.RangeFull → Slice T → Result ((Slice T) × (Slice T →
    Slice T))

/- [core::slice::index::{core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::index]:
   Source: '/rustc/library/core/src/slice/index.rs', lines 655:4-655:39
   Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index] -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index"]
def core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index
  {T : Type} : core.ops.range.RangeFull → Slice T → Result (Slice T) :=
  fun _ s => ok s

/-- RangeFull indexing (`s[..]`) is the identity on slices. -/
@[simp]
theorem core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_spec
  {T : Type} (s : Slice T) :
  core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index () s = ok s := by
  simp [core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index]

/- [core::slice::index::{core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::get_unchecked_mut]:
   Source: '/rustc/library/core/src/slice/index.rs', lines 650:4-650:66
   Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked_mut] -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked_mut"]
axiom
  core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut
  {T : Type} :
  core.ops.range.RangeFull → MutRawPtr (Slice T) → Result (MutRawPtr (Slice
    T))

/- [core::slice::index::{core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::get_unchecked]:
   Source: '/rustc/library/core/src/slice/index.rs', lines 645:4-645:66
   Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked] -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked"]
axiom
  core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked
  {T : Type} :
  core.ops.range.RangeFull → ConstRawPtr (Slice T) → Result (ConstRawPtr
    (Slice T))

/- [core::slice::index::{core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::get_mut]:
   Source: '/rustc/library/core/src/slice/index.rs', lines 640:4-640:57
   Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_mut] -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_mut"]
axiom core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut
  {T : Type} :
  core.ops.range.RangeFull → Slice T → Result ((Option (Slice T)) ×
    (Option (Slice T) → Slice T))

/- [core::slice::index::{core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::get]:
   Source: '/rustc/library/core/src/slice/index.rs', lines 635:4-635:45
   Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get] -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get"]
axiom core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get
  {T : Type} :
  core.ops.range.RangeFull → Slice T → Result (Option (Slice T))

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

/- [curve25519_dalek::field::{core::cmp::Eq for curve25519_dalek::backend::serial::u64::field::FieldElement51}::assert_receiver_is_total_eq]:
   Source: 'curve25519-dalek/src/field.rs', lines 84:0-84:27 -/
axiom
  backend.serial.u64.field.FieldElement51.Insts.CoreCmpEq.assert_receiver_is_total_eq
  : backend.serial.u64.field.FieldElement51 → Result Unit

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

/-- [curve25519_dalek::backend::serial::u64::field::{subtle::ConditionallySelectable for curve25519_dalek::backend::serial::u64::field::FieldElement51}::conditional_select]:
   Source: 'curve25519-dalek/src/backend/serial/u64/field.rs', lines 228:4-240:5
It is in Funs.Lean previously, we copy it here locally (with private and ' suffix) since montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_swap depends on it -/
private def
  backend.serial.u64.field.ConditionallySelectableFieldElement51.conditional_select'
  (a : backend.serial.u64.field.FieldElement51)
  (b : backend.serial.u64.field.FieldElement51) (choice : subtle.Choice) :
  Result backend.serial.u64.field.FieldElement51
  := do
  let i ← Array.index_usize a 0#usize
  let i1 ← Array.index_usize b 0#usize
  let i2 ← U64.Insts.SubtleConditionallySelectable.conditional_select i i1 choice
  let i3 ← Array.index_usize a 1#usize
  let i4 ← Array.index_usize b 1#usize
  let i5 ← U64.Insts.SubtleConditionallySelectable.conditional_select i3 i4 choice
  let i6 ← Array.index_usize a 2#usize
  let i7 ← Array.index_usize b 2#usize
  let i8 ← U64.Insts.SubtleConditionallySelectable.conditional_select i6 i7 choice
  let i9 ← Array.index_usize a 3#usize
  let i10 ← Array.index_usize b 3#usize
  let i11 ←
    U64.Insts.SubtleConditionallySelectable.conditional_select i9 i10 choice
  let i12 ← Array.index_usize a 4#usize
  let i13 ← Array.index_usize b 4#usize
  let i14 ←
    U64.Insts.SubtleConditionallySelectable.conditional_select i12 i13 choice
  ok (Array.make 5#usize [ i2, i5, i8, i11, i14 ])

/-- [curve25519_dalek::montgomery::{subtle::ConditionallySelectable for curve25519_dalek::montgomery::ProjectivePoint}::conditional_select]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 311:4-320:5
  It is in Funs.Lean previously, we copy it here locally (with private and ' suffix) since montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_swap depends on it -/
private def montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_select'
  (a : montgomery.ProjectivePoint) (b : montgomery.ProjectivePoint)
  (choice : subtle.Choice) :
  Result montgomery.ProjectivePoint
  := do
  let fe ←
    backend.serial.u64.field.ConditionallySelectableFieldElement51.conditional_select'
      a.U b.U choice
  let fe1 ←
    backend.serial.u64.field.ConditionallySelectableFieldElement51.conditional_select'
      a.W b.W choice
  ok { U := fe, W := fe1 }

/-- [curve25519_dalek::montgomery::{subtle::ConditionallySelectable for curve25519_dalek::montgomery::ProjectivePoint}::conditional_swap]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 311:0-322:1

   Conditionally swaps two ProjectivePoint values in constant time.
   If choice.val = 1, swaps the points; otherwise leaves them unchanged. -/
def montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_swap
  (a : montgomery.ProjectivePoint) (b : montgomery.ProjectivePoint)
  (choice : subtle.Choice) :
  Result (montgomery.ProjectivePoint × montgomery.ProjectivePoint) := do
  let a_new ← montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_select' a b choice
  let b_new ← montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_select' b a choice
  ok (a_new, b_new)

/-- **Spec theorem for `montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_swap`**:
- No panic (if both conditional_select operations succeed)
- Conditionally swaps two ProjectivePoint values in constant time
- Returns (a, b) if choice.val = 0, or (b, a) if choice.val = 1
-/
@[progress]
theorem montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_swap_spec
  (a b : montgomery.ProjectivePoint) (choice : subtle.Choice)
  (h_a : ∃ res, montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_select' a b choice = ok res)
  (h_b : ∃ res, montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_select' b a choice = ok res) :
  montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_swap a b choice ⦃ c =>
    montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_select' a b choice = ok c.1 ∧
    montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_select' b a choice = ok c.2 ⦄ := by
  unfold montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_swap
  obtain ⟨a_new, h_a_eq⟩ := h_a
  obtain ⟨b_new, h_b_eq⟩ := h_b
  simp [h_a_eq, h_b_eq, bind_tc_ok, spec_ok, and_self]

/-- Trait implementation: [subtle::{subtle::ConditionallySelectable for u8}]
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 511:8-537:10
   Name pattern: [subtle::ConditionallySelectable<u8>] -/
@[reducible, rust_trait_impl "subtle::ConditionallySelectable<u8>"]
private def subtle.ConditionallySelectableU8' : subtle.ConditionallySelectable U8 := {
  coremarkerCopyInst := core.marker.CopyU8
  conditional_select := U8.Insts.SubtleConditionallySelectable.conditional_select
  conditional_assign := U8.Insts.SubtleConditionallySelectable.conditional_assign
  conditional_swap := U8.Insts.SubtleConditionallySelectable.conditional_swap
}

/-- [curve25519_dalek::montgomery::{subtle::ConditionallySelectable for curve25519_dalek::montgomery::MontgomeryPoint}::conditional_select]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 88:4-90:5
   It is in Funs.Lean previously, we copy it here locally (with private and ' suffix) for conditional_swap -/
private def montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_select'
  (a : montgomery.MontgomeryPoint) (b : montgomery.MontgomeryPoint)
  (choice : subtle.Choice) :
  Result montgomery.MontgomeryPoint
  := do
  let a1 ←
    Array.Insts.SubtleConditionallySelectable.conditional_select
      subtle.ConditionallySelectableU8' a b choice
  ok a1

/-- [curve25519_dalek::montgomery::{subtle::ConditionallySelectable for curve25519_dalek::montgomery::MontgomeryPoint}::conditional_swap]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 87:0-91:1

   Conditionally swaps two MontgomeryPoint values in constant time.
   If choice.val = 1, swaps the points; otherwise leaves them unchanged. -/
def montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_swap
  (a : montgomery.MontgomeryPoint) (b : montgomery.MontgomeryPoint)
  (choice : subtle.Choice) :
  Result (montgomery.MontgomeryPoint × montgomery.MontgomeryPoint) := do
  let a_new ← montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_select' a b choice
  let b_new ← montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_select' b a choice
  ok (a_new, b_new)

/-- **Spec theorem for `montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_swap`**:
- No panic (always succeeds)
- Conditionally swaps two MontgomeryPoint values in constant time
- Returns (a, b) if choice.val = 0#u8, or (b, a) if choice.val = 1#u8
- Implements constant-time conditional swap for MontgomeryPoint
-/
@[progress]
theorem montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_swap_spec
  (a b : montgomery.MontgomeryPoint) (choice : subtle.Choice) :
  montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_swap a b choice ⦃ res =>
    res = (if choice.val = 1#u8 then (b, a) else (a, b)) ⦄ := by
  unfold montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_swap
  unfold montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_select'
  unfold Array.Insts.SubtleConditionallySelectable.conditional_select
  split <;> simp_all [bind_tc_ok, spec_ok]

/-- [curve25519_dalek::montgomery::{subtle::ConditionallySelectable for curve25519_dalek::montgomery::MontgomeryPoint}::conditional_assign]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 87:0-91:1

   Conditionally assigns b to a in constant time.
   This is a wrapper around conditional_select. -/
def montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_assign
  (a : montgomery.MontgomeryPoint) (b : montgomery.MontgomeryPoint)
  (choice : subtle.Choice) :
  Result montgomery.MontgomeryPoint :=
  montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_select' a b choice

/-- **Spec theorem for `montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_assign`**:
- No panic (if conditional_select succeeds)
- Returns the result of conditional_select(a, b, choice)
- This is a wrapper around conditional_select
- Implements constant-time conditional assignment for MontgomeryPoint
-/
@[progress]
theorem montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_assign_spec
  (a b : montgomery.MontgomeryPoint) (choice : subtle.Choice)
  (h : ∃ res, montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_select' a b choice = ok res) :
  montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_assign a b choice ⦃ res =>
    montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_select' a b choice = ok res ⦄ := by
  unfold montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_assign
  obtain ⟨res, h_eq⟩ := h
  simp [h_eq, spec_ok]

/- [curve25519_dalek::montgomery::{core::cmp::PartialEq<curve25519_dalek::montgomery::MontgomeryPoint> for curve25519_dalek::montgomery::MontgomeryPoint}::ne]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 93:0-97:1 -/
axiom montgomery.MontgomeryPoint.Insts.CoreCmpPartialEqMontgomeryPoint.ne
  : montgomery.MontgomeryPoint → montgomery.MontgomeryPoint → Result Bool

/-- [curve25519_dalek::montgomery::{core::cmp::Eq for curve25519_dalek::montgomery::MontgomeryPoint}::assert_receiver_is_total_eq]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 99:0-99:30

   Marker method required by the Eq trait to assert that the type has total equality.
   This is a no-op for MontgomeryPoint, always returning Unit. -/
def montgomery.MontgomeryPoint.Insts.CoreCmpEq.assert_receiver_is_total_eq
  (_self : montgomery.MontgomeryPoint) : Result Unit :=
  ok ()

/-- **Spec theorem for `montgomery.MontgomeryPoint.Insts.CoreCmpEq.assert_receiver_is_total_eq`**:
- No panic (always succeeds)
- Always returns ok ()
- Marker method required by the Eq trait to assert total equality
-/
@[progress]
theorem montgomery.MontgomeryPoint.Insts.CoreCmpEq.assert_receiver_is_total_eq_spec
  (self : montgomery.MontgomeryPoint) :
  montgomery.MontgomeryPoint.Insts.CoreCmpEq.assert_receiver_is_total_eq self ⦃ _ => True ⦄ := by
  unfold montgomery.MontgomeryPoint.Insts.CoreCmpEq.assert_receiver_is_total_eq
  simp [spec_ok]

/-- [curve25519_dalek::montgomery::{subtle::ConditionallySelectable for curve25519_dalek::montgomery::ProjectivePoint}::conditional_assign]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 311:0-322:1

   Conditionally assigns b to a in constant time.
   This is a wrapper around conditional_select. -/
def montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_assign
  (a : montgomery.ProjectivePoint) (b : montgomery.ProjectivePoint)
  (choice : subtle.Choice) :
  Result montgomery.ProjectivePoint :=
  montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_select' a b choice

/-- **Spec theorem for `montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_assign`**:
- No panic (if conditional_select succeeds)
- Returns b if choice.val = 1, otherwise returns a
- Equivalent to conditional_select(a, b, choice)
- Implements constant-time conditional assignment for ProjectivePoint
-/
@[progress]
theorem montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_assign_spec
  (a b : montgomery.ProjectivePoint) (choice : subtle.Choice)
  (h : ∃ res, montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_select' a b choice = ok res) :
  montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_assign a b choice ⦃ res =>
    montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_select' a b choice = ok res ⦄ := by
  unfold montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_assign
  obtain ⟨res, h_eq⟩ := h
  simp [h_eq, spec_ok]

/- [curve25519_dalek::edwards::affine::{subtle::ConditionallySelectable for curve25519_dalek::edwards::affine::AffinePoint}::conditional_swap]:
   Source: 'curve25519-dalek/src/edwards/affine.rs', lines 23:0-30:1 -/
axiom
  edwards.affine.AffinePoint.Insts.SubtleConditionallySelectable.conditional_swap
  :
  edwards.affine.AffinePoint → edwards.affine.AffinePoint → subtle.Choice
    → Result (edwards.affine.AffinePoint × edwards.affine.AffinePoint)

/- [curve25519_dalek::edwards::affine::{subtle::ConditionallySelectable for curve25519_dalek::edwards::affine::AffinePoint}::conditional_assign]:
   Source: 'curve25519-dalek/src/edwards/affine.rs', lines 23:0-30:1 -/
axiom
  edwards.affine.AffinePoint.Insts.SubtleConditionallySelectable.conditional_assign
  :
  edwards.affine.AffinePoint → edwards.affine.AffinePoint → subtle.Choice
    → Result edwards.affine.AffinePoint

/- [curve25519_dalek::edwards::affine::{core::cmp::PartialEq<curve25519_dalek::edwards::affine::AffinePoint> for curve25519_dalek::edwards::affine::AffinePoint}::ne]:
   Source: 'curve25519-dalek/src/edwards/affine.rs', lines 47:0-51:1 -/
axiom edwards.affine.AffinePoint.Insts.CoreCmpPartialEqAffinePoint.ne
  : edwards.affine.AffinePoint → edwards.affine.AffinePoint → Result Bool

/- [curve25519_dalek::edwards::affine::{core::cmp::Eq for curve25519_dalek::edwards::affine::AffinePoint}::assert_receiver_is_total_eq]:
   Source: 'curve25519-dalek/src/edwards/affine.rs', lines 53:0-53:26 -/
axiom edwards.affine.AffinePoint.Insts.CoreCmpEq.assert_receiver_is_total_eq
  : edwards.affine.AffinePoint → Result Unit

/- [curve25519_dalek::edwards::{core::cmp::PartialEq<curve25519_dalek::edwards::CompressedEdwardsY> for curve25519_dalek::edwards::CompressedEdwardsY}::ne]:
   Source: 'curve25519-dalek/src/edwards.rs', lines 172:26-172:35 -/
axiom edwards.CompressedEdwardsY.Insts.CoreCmpPartialEqCompressedEdwardsY.ne
  : edwards.CompressedEdwardsY → edwards.CompressedEdwardsY → Result Bool

/- [curve25519_dalek::edwards::{subtle::ConditionallySelectable for curve25519_dalek::edwards::EdwardsPoint}::conditional_swap]:
   Source: 'curve25519-dalek/src/edwards.rs', lines 478:0-487:1 -/
axiom edwards.EdwardsPoint.Insts.SubtleConditionallySelectable.conditional_swap
  :
  edwards.EdwardsPoint → edwards.EdwardsPoint → subtle.Choice → Result
    (edwards.EdwardsPoint × edwards.EdwardsPoint)

/- [curve25519_dalek::edwards::{subtle::ConditionallySelectable for curve25519_dalek::edwards::EdwardsPoint}::conditional_assign]:
   Source: 'curve25519-dalek/src/edwards.rs', lines 478:0-487:1 -/
axiom
  edwards.EdwardsPoint.Insts.SubtleConditionallySelectable.conditional_assign
  :
  edwards.EdwardsPoint → edwards.EdwardsPoint → subtle.Choice → Result
    edwards.EdwardsPoint

/- [curve25519_dalek::edwards::{core::cmp::PartialEq<curve25519_dalek::edwards::EdwardsPoint> for curve25519_dalek::edwards::EdwardsPoint}::ne]:
   Source: 'curve25519-dalek/src/edwards.rs', lines 506:0-510:1 -/
axiom edwards.EdwardsPoint.Insts.CoreCmpPartialEqEdwardsPoint.ne
  : edwards.EdwardsPoint → edwards.EdwardsPoint → Result Bool

/- [curve25519_dalek::edwards::{core::cmp::Eq for curve25519_dalek::edwards::EdwardsPoint}::assert_receiver_is_total_eq]:
   Source: 'curve25519-dalek/src/edwards.rs', lines 512:0-512:27 -/
axiom edwards.EdwardsPoint.Insts.CoreCmpEq.assert_receiver_is_total_eq
  : edwards.EdwardsPoint → Result Unit

/- [curve25519_dalek::ristretto::{core::cmp::PartialEq<curve25519_dalek::ristretto::CompressedRistretto> for curve25519_dalek::ristretto::CompressedRistretto}::ne]:
   Source: 'curve25519-dalek/src/ristretto.rs', lines 220:26-220:35 -/
axiom
  ristretto.CompressedRistretto.Insts.CoreCmpPartialEqCompressedRistretto.ne
  :
  ristretto.CompressedRistretto → ristretto.CompressedRistretto → Result
    Bool

/- [curve25519_dalek::ristretto::{core::cmp::PartialEq<curve25519_dalek::ristretto::RistrettoPoint> for curve25519_dalek::ristretto::RistrettoPoint}::ne]:
   Source: 'curve25519-dalek/src/ristretto.rs', lines 858:0-862:1 -/
axiom ristretto.RistrettoPoint.Insts.CoreCmpPartialEqRistrettoPoint.ne
  : ristretto.RistrettoPoint → ristretto.RistrettoPoint → Result Bool

/- [curve25519_dalek::ristretto::{core::cmp::Eq for curve25519_dalek::ristretto::RistrettoPoint}::assert_receiver_is_total_eq]:
   Source: 'curve25519-dalek/src/ristretto.rs', lines 881:0-881:29 -/
axiom ristretto.RistrettoPoint.Insts.CoreCmpEq.assert_receiver_is_total_eq
  : ristretto.RistrettoPoint → Result Unit

/- [curve25519_dalek::ristretto::{subtle::ConditionallySelectable for curve25519_dalek::ristretto::RistrettoPoint}::conditional_swap]:
   Source: 'curve25519-dalek/src/ristretto.rs', lines 1167:0-1199:1 -/
axiom
  ristretto.RistrettoPoint.Insts.SubtleConditionallySelectable.conditional_swap
  :
  ristretto.RistrettoPoint → ristretto.RistrettoPoint → subtle.Choice →
    Result (ristretto.RistrettoPoint × ristretto.RistrettoPoint)

/- [curve25519_dalek::ristretto::{subtle::ConditionallySelectable for curve25519_dalek::ristretto::RistrettoPoint}::conditional_assign]:
   Source: 'curve25519-dalek/src/ristretto.rs', lines 1167:0-1199:1 -/
axiom
  ristretto.RistrettoPoint.Insts.SubtleConditionallySelectable.conditional_assign
  :
  ristretto.RistrettoPoint → ristretto.RistrettoPoint → subtle.Choice →
    Result ristretto.RistrettoPoint

end curve25519_dalek
