-- [curve25519_dalek]: external functions.
import Aeneas
import Curve25519Dalek.Types
import Mathlib

open Aeneas.Std Result

namespace curve25519_dalek


/- [core::slice::index::{core::slice::index::SliceIndex<@Slice<T>, @Slice<T>> for core::ops::range::RangeFull}::get]:
   Source: '/rustc/library/core/src/slice/index.rs', lines 635:4-635:45
   Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get] -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get"]
axiom core.slice.index.SliceIndexRangeFullSliceSlice.get
  {T : Type} :
  core.ops.range.RangeFull → Slice T → Result (Option (Slice T))

/- [core::slice::index::{core::slice::index::SliceIndex<@Slice<T>, @Slice<T>> for core::ops::range::RangeFull}::get_mut]:
   Source: '/rustc/library/core/src/slice/index.rs', lines 640:4-640:57
   Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_mut] -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_mut"]
axiom core.slice.index.SliceIndexRangeFullSliceSlice.get_mut
  {T : Type} :
  core.ops.range.RangeFull → Slice T → Result ((Option (Slice T)) ×
    (Option (Slice T) → Slice T))

/- [core::slice::index::{core::slice::index::SliceIndex<@Slice<T>, @Slice<T>> for core::ops::range::RangeFull}::get_unchecked]:
   Source: '/rustc/library/core/src/slice/index.rs', lines 645:4-645:66
   Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked] -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked"]
axiom core.slice.index.SliceIndexRangeFullSliceSlice.get_unchecked
  {T : Type} :
  core.ops.range.RangeFull → ConstRawPtr (Slice T) → Result (ConstRawPtr
    (Slice T))

/- [core::slice::index::{core::slice::index::SliceIndex<@Slice<T>, @Slice<T>> for core::ops::range::RangeFull}::get_unchecked_mut]:
   Source: '/rustc/library/core/src/slice/index.rs', lines 650:4-650:66
   Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked_mut] -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked_mut"]
axiom core.slice.index.SliceIndexRangeFullSliceSlice.get_unchecked_mut
  {T : Type} :
  core.ops.range.RangeFull → MutRawPtr (Slice T) → Result (MutRawPtr (Slice
    T))

/- [core::slice::index::{core::slice::index::SliceIndex<@Slice<T>, @Slice<T>> for core::ops::range::RangeFull}::index]:
   Source: '/rustc/library/core/src/slice/index.rs', lines 655:4-655:39
   Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index] -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index"]
axiom core.slice.index.SliceIndexRangeFullSliceSlice.index
  {T : Type} : core.ops.range.RangeFull → Slice T → Result (Slice T)

/- [core::slice::index::{core::slice::index::SliceIndex<@Slice<T>, @Slice<T>> for core::ops::range::RangeFull}::index_mut]:
   Source: '/rustc/library/core/src/slice/index.rs', lines 660:4-660:51
   Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index_mut] -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index_mut"]
axiom core.slice.index.SliceIndexRangeFullSliceSlice.index_mut
  {T : Type} :
  core.ops.range.RangeFull → Slice T → Result ((Slice T) × (Slice T →
    Slice T))

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
def subtle.FromBoolChoice.from (c : subtle.Choice) : Result Bool :=
  ok (c.val = 1#u8)

/- [subtle::{core::ops::bit::BitAnd<subtle::Choice, subtle::Choice> for subtle::Choice}::bitand]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 162:4-162:42
   Name pattern: [subtle::{core::ops::bit::BitAnd<subtle::Choice, subtle::Choice, subtle::Choice>}::bitand] -/
@[rust_fun
  "subtle::{core::ops::bit::BitAnd<subtle::Choice, subtle::Choice, subtle::Choice>}::bitand"]
def subtle.BitAndChoiceChoiceChoice.bitand
  (a : subtle.Choice) (b : subtle.Choice) : Result subtle.Choice :=
  if a.val = 0#u8 ∨ b.val = 0#u8 then
    ok Choice.zero
  else
    ok Choice.one

/-- **Spec theorem for `subtle.BitAndChoiceChoiceChoice.bitand`**:
- No panic (always returns successfully)
- Returns `Choice.one` if and only if both inputs are `Choice.one`
-/
@[progress]
axiom subtle.BitAndChoiceChoiceChoice.bitand_spec (a b : subtle.Choice) :
    ∃ c, subtle.BitAndChoiceChoiceChoice.bitand a b = ok c ∧
    (c = Choice.one ↔ a = Choice.one ∧ b = Choice.one)

/- [subtle::{core::ops::bit::BitOr<subtle::Choice, subtle::Choice> for subtle::Choice}::bitor]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 177:4-177:41
   Name pattern: [subtle::{core::ops::bit::BitOr<subtle::Choice, subtle::Choice, subtle::Choice>}::bitor]
   Bitwise OR for Choice values (0 | 0 = 0, 0 | 1 = 1, 1 | 0 = 1, 1 | 1 = 1) -/
@[rust_fun
  "subtle::{core::ops::bit::BitOr<subtle::Choice, subtle::Choice, subtle::Choice>}::bitor"]
def subtle.BitOrChoiceChoiceChoice.bitor (a : subtle.Choice) (b : subtle.Choice) :
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
def subtle.NotChoiceChoice.not (c : subtle.Choice) : Result subtle.Choice :=
  if c.val = 1#u8 then
    ok Choice.zero
  else
    ok Choice.one

/- [subtle::{subtle::ConstantTimeEq for u16}::ct_eq]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 348:12-348:51
   Name pattern: [subtle::{subtle::ConstantTimeEq<u16>}::ct_eq] -/
@[rust_fun "subtle::{subtle::ConstantTimeEq<u16>}::ct_eq"]
axiom subtle.ConstantTimeEqU16.ct_eq : U16 → U16 → Result subtle.Choice

/- [subtle::{core::convert::From<u8> for subtle::Choice}::from]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 238:4-238:32
   Name pattern: [subtle::{core::convert::From<subtle::Choice, u8>}::from]
   Converts a u8 to a Choice. The input should be 0 or 1. -/
def subtle.FromChoiceU8.from (input : U8) : Result subtle.Choice :=
  if h : input = 0#u8 then
    ok { val := input, valid := Or.inl h }
  else if h' : input = 1#u8 then
    ok { val := input, valid := Or.inr h' }
  else
    fail Error.panic

/- [subtle::{subtle::ConstantTimeEq for @Slice<T>}::ct_eq]:
   Name pattern: [subtle::{subtle::ConstantTimeEq<[@T]>}::ct_eq]
   Constant-time equality for slices -/
axiom subtle.ConstantTimeEqSlice.ct_eq
  {T : Type} (ConstantTimeEqInst : subtle.ConstantTimeEq T)
  : Slice T → Slice T → Result subtle.Choice

/-- **Spec axiom for `subtle.ConstantTimeEqSlice.ct_eq`**:
- No panic (always returns successfully)
- Returns Choice.one (true) if and only if all corresponding elements are equal
- Requires equal-length slices with valid bounds
-/
@[progress]
axiom subtle.ConstantTimeEqSlice.ct_eq_spec
  {T : Type} (ConstantTimeEqInst : subtle.ConstantTimeEq T) (a b : Slice T)
  (ha : a.length < 2 ^ UScalarTy.Usize.numBits)
  (hb : b.length < 2 ^ UScalarTy.Usize.numBits)
  (h_eq_len : a.length = b.length) :
  ∃ c, subtle.ConstantTimeEqSlice.ct_eq ConstantTimeEqInst a b = ok c ∧
  (c = Choice.one ↔ a = b)

/- [subtle::{subtle::ConstantTimeEq for u8}::ct_eq]:
Name pattern: [subtle::{subtle::ConstantTimeEq<u8>}::ct_eq]
Constant-time equality for U8 values -/
def subtle.ConstantTimeEqU8.ct_eq (a : U8) (b : U8) : Result subtle.Choice :=
  if a = b then ok Choice.one
  else ok Choice.zero

/-- **Spec axiom for `subtle.ConstantTimeEqU8.ct_eq`**:
- No panic (always returns successfully)
- Returns `Choice.one` if and only if the two U8 values are equal
-/
@[progress]
axiom subtle.ConstantTimeEqU8.ct_eq_spec (a b : U8) :
  ∃ c, subtle.ConstantTimeEqU8.ct_eq a b = ok c ∧
  (c = Choice.one ↔ a = b)

/- [subtle::ConditionallySelectable::conditional_assign]:
   Source: '/home/oliver/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 442:4-442:66
   Name pattern: [subtle::ConditionallySelectable::conditional_assign] -/
axiom subtle.ConditionallySelectable.conditional_assign.default
  {Self : Type} (ConditionallySelectableInst : subtle.ConditionallySelectable
  Self) :
  Self → Self → subtle.Choice → Result Self

/- [subtle::ConditionallySelectable::conditional_swap]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 469:4-469:67
   Name pattern: [subtle::ConditionallySelectable::conditional_swap] -/
@[rust_fun "subtle::ConditionallySelectable::conditional_swap"]
axiom subtle.ConditionallySelectable.conditional_swap.default
  {Self : Type} (ConditionallySelectableInst : subtle.ConditionallySelectable
  Self) :
  Self → Self → subtle.Choice → Result (Self × Self)

/- [subtle::{subtle::ConditionallySelectable for u64}::conditional_select]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 513:12-513:77
   Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_select]
Conditional select: returns a if choice(0), b if choice(1) -/
def subtle.ConditionallySelectableU64.conditional_select
  (a : U64) (b : U64) (choice : subtle.Choice) : Result U64 :=
  if choice.val = 1#u8 then ok b
  else ok a

/-- Progress spec for ConditionallySelectableU64.conditional_select -/
@[progress]
theorem conditional_select_U64_spec (a b : U64) (choice : subtle.Choice) :
    ∃ res, subtle.ConditionallySelectableU64.conditional_select a b choice = ok res ∧
    res = if choice.val = 1#u8 then b else a := by
  unfold subtle.ConditionallySelectableU64.conditional_select
  split <;> simp_all

/- [subtle::{subtle::ConditionallySelectable for u64}::conditional_assign]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 521:12-521:74
   Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_assign]
   Conditionally assign b to a if choice(1); otherwise leave a unchanged -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<u64>}::conditional_assign"]
def subtle.ConditionallySelectableU64.conditional_assign
  (a : U64) (b : U64) (choice : subtle.Choice) : Result U64 :=
  subtle.ConditionallySelectableU64.conditional_select a b choice

/- [subtle::{subtle::ConditionallySelectable for u64}::conditional_swap]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 529:12-529:75
   Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_swap]
   Conditionally swap a and b if choice(1); otherwise leave them unchanged -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u64>}::conditional_swap"]
def subtle.ConditionallySelectableU64.conditional_swap
  (a : U64) (b : U64) (choice : subtle.Choice) : Result (U64 × U64) := do
  let a_new ← subtle.ConditionallySelectableU64.conditional_select a b choice
  let b_new ← subtle.ConditionallySelectableU64.conditional_select b a choice
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
def subtle.CtOption.new
  {T : Type} (value : T) (is_some : subtle.Choice) : Result (subtle.CtOption T) :=
  ok { value := value, is_some := is_some }

/-- **Spec axiom for `subtle.CtOption.new`**:
- No panic (always returns successfully)
- Returns a CtOption with the given value and is_some flag
- The returned CtOption's fields match the inputs exactly
-/
@[progress]
axiom subtle.CtOption.new_spec {T : Type} (value : T) (is_some : subtle.Choice) :
  ∃ opt, subtle.CtOption.new value is_some = ok opt ∧
  opt.value = value ∧ opt.is_some = is_some

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
axiom zeroize.ZeroizeArray.zeroize
  {Z : Type} {N : Usize} (ZeroizeInst : zeroize.Zeroize Z) :
  Array Z N → Result (Array Z N)

/- [core::slice::index::{core::slice::index::SliceIndex<@Slice<T>, @Slice<T>> for core::ops::range::RangeFull}::get]:
   Source: '/rustc/library/core/src/slice/index.rs', lines 630:4-630:45
   Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get]
   Returns the entire slice wrapped in Some (RangeFull .. always selects the whole slice) -/
def core.slice.index.SliceIndexcoreopsrangeRangeFullSliceSlice.get
  {T : Type} :
  core.ops.range.RangeFull → Slice T → Result (Option (Slice T)) :=
  fun _ slice => ok (some slice)

/- [core::slice::index::{core::slice::index::SliceIndex<@Slice<T>, @Slice<T>> for core::ops::range::RangeFull}::get_mut]:
   Source: '/rustc/library/core/src/slice/index.rs', lines 635:4-635:57
   Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_mut]
   Returns the entire slice wrapped in Some and a back function for updating -/
def core.slice.index.SliceIndexcoreopsrangeRangeFullSliceSlice.get_mut
  {T : Type} :
  core.ops.range.RangeFull → Slice T → Result ((Option (Slice T)) ×
    (Option (Slice T) → Slice T)) :=
  fun _ slice =>
    let back := fun (opt : Option (Slice T)) =>
      match opt with
      | some s => s
      | none => slice  -- fallback to original slice if None
    ok (some slice, back)

/- [core::slice::index::{core::slice::index::SliceIndex<@Slice<T>, @Slice<T>> for core::ops::range::RangeFull}::get_unchecked]:
   Source: '/rustc/library/core/src/slice/index.rs', lines 640:4-640:66
   Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked]
   Returns the pointer unchanged (RangeFull .. always selects the whole slice) -/
def core.slice.index.SliceIndexcoreopsrangeRangeFullSliceSlice.get_unchecked
  {T : Type} :
  core.ops.range.RangeFull → ConstRawPtr (Slice T) → Result (ConstRawPtr
    (Slice T)) :=
  fun _ ptr => ok ptr

/- [core::slice::index::{core::slice::index::SliceIndex<@Slice<T>, @Slice<T>> for core::ops::range::RangeFull}::get_unchecked_mut]:
   Source: '/rustc/library/core/src/slice/index.rs', lines 645:4-645:66
   Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked_mut]
   Returns the mutable pointer unchanged (RangeFull .. always selects the whole slice) -/
def core.slice.index.SliceIndexcoreopsrangeRangeFullSliceSlice.get_unchecked_mut
  {T : Type} :
  core.ops.range.RangeFull → MutRawPtr (Slice T) → Result (MutRawPtr (Slice
    T)) :=
  fun _ ptr => ok ptr

/- [core::slice::index::{core::slice::index::SliceIndex<@Slice<T>, @Slice<T>> for core::ops::range::RangeFull}::index]:
   Source: '/rustc/library/core/src/slice/index.rs', lines 650:4-650:39
   Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index]
   Returns the entire slice unchanged (RangeFull .. always selects the whole slice) -/
def core.slice.index.SliceIndexcoreopsrangeRangeFullSliceSlice.index
  {T : Type} : core.ops.range.RangeFull → Slice T → Result (Slice T) :=
  fun _ slice => ok slice

/- [core::slice::index::{core::slice::index::SliceIndex<@Slice<T>, @Slice<T>> for core::ops::range::RangeFull}::index_mut]:
   Source: '/rustc/library/core/src/slice/index.rs', lines 655:4-655:51
   Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index_mut]
   Returns the entire slice and a back function for updating -/
def core.slice.index.SliceIndexcoreopsrangeRangeFullSliceSlice.index_mut
  {T : Type} :
  core.ops.range.RangeFull → Slice T → Result ((Slice T) × (Slice T →
    Slice T)) :=
  fun _ slice =>
    let back := fun (s : Slice T) => s
    ok (slice, back)

/- [curve25519_dalek::backend::serial::curve_models::{subtle::ConditionallySelectable for curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint}::conditional_swap]:
   Source: 'curve25519-dalek/src/backend/serial/curve_models/mod.rs', lines 295:0-311:1 -/
axiom
  backend.serial.curve_models.ConditionallySelectableProjectiveNielsPoint.conditional_swap
  :
  backend.serial.curve_models.ProjectiveNielsPoint →
    backend.serial.curve_models.ProjectiveNielsPoint → subtle.Choice →
    Result (backend.serial.curve_models.ProjectiveNielsPoint ×
    backend.serial.curve_models.ProjectiveNielsPoint)

/- [curve25519_dalek::backend::serial::curve_models::{subtle::ConditionallySelectable for curve25519_dalek::backend::serial::curve_models::AffineNielsPoint}::conditional_swap]:
   Source: 'curve25519-dalek/src/backend/serial/curve_models/mod.rs', lines 313:0-327:1 -/
axiom
  backend.serial.curve_models.ConditionallySelectableAffineNielsPoint.conditional_swap
  :
  backend.serial.curve_models.AffineNielsPoint →
    backend.serial.curve_models.AffineNielsPoint → subtle.Choice → Result
    (backend.serial.curve_models.AffineNielsPoint ×
    backend.serial.curve_models.AffineNielsPoint)

/- [core::iter::range::{core::iter::range::Step for usize}::steps_between]:
   Source: '/rustc/library/core/src/iter/range.rs', lines 263:16-263:84
   Name pattern: [core::iter::range::{core::iter::range::Step<usize>}::steps_between] -/
@[rust_fun
  "core::iter::range::{core::iter::range::Step<usize>}::steps_between"]
axiom core.iter.range.StepUsize.steps_between
  : Usize → Usize → Result (Usize × (Option Usize))

/- [core::iter::range::{core::iter::range::Step for usize}::forward_checked]:
   Source: '/rustc/library/core/src/iter/range.rs', lines 274:16-274:73
   Name pattern: [core::iter::range::{core::iter::range::Step<usize>}::forward_checked] -/
@[rust_fun
  "core::iter::range::{core::iter::range::Step<usize>}::forward_checked"]
axiom core.iter.range.StepUsize.forward_checked
  : Usize → Usize → Result (Option Usize)

/- [core::iter::range::{core::iter::range::Step for usize}::backward_checked]:
   Source: '/rustc/library/core/src/iter/range.rs', lines 282:16-282:74
   Name pattern: [core::iter::range::{core::iter::range::Step<usize>}::backward_checked] -/
@[rust_fun
  "core::iter::range::{core::iter::range::Step<usize>}::backward_checked"]
axiom core.iter.range.StepUsize.backward_checked
  : Usize → Usize → Result (Option Usize)

/- [core::iter::range::{core::iter::traits::iterator::Iterator<A> for core::ops::range::Range<A>}::next]:
   Source: '/rustc/library/core/src/iter/range.rs', lines 849:4-849:35
   Name pattern: [core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, @A>}::next] -/
@[rust_fun
  "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, @A>}::next"]
axiom core.iter.range.IteratorRangeA.next
  {A : Type} (StepInst : core.iter.range.Step A) :
  core.ops.range.Range A → Result ((Option A) × (core.ops.range.Range A))

/- [core::iter::traits::collect::{core::iter::traits::collect::IntoIterator<Clause0_Item, I> for I}::into_iter]:
   Source: '/rustc/library/core/src/iter/traits/collect.rs', lines 319:4-319:27
   Name pattern: [core::iter::traits::collect::{core::iter::traits::collect::IntoIterator<@I, @Clause0_Item, @I>}::into_iter] -/
@[rust_fun
  "core::iter::traits::collect::{core::iter::traits::collect::IntoIterator<@I, @Clause0_Item, @I>}::into_iter"]
axiom core.iter.traits.collect.IntoIterator.Blanket.into_iter
  {I : Type} {Clause0_Item : Type} (iteratorIteratorInst :
  core.iter.traits.iterator.Iterator I Clause0_Item) :
  I → Result I

/- [subtle::{subtle::ConditionallySelectable for u8}::conditional_select]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 513:12-513:77
   Name pattern: [subtle::{subtle::ConditionallySelectable<u8>}::conditional_select]
   Conditional select: returns a if choice(0), b if choice(1) -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u8>}::conditional_select"]
def subtle.ConditionallySelectableU8.conditional_select
  (a : U8) (b : U8) (choice : subtle.Choice) : Result U8 :=
  if choice.val = 1#u8 then ok b
  else ok a

/-- Progress spec for ConditionallySelectableU8.conditional_select -/
@[progress]
theorem conditional_select_U8_spec (a b : U8) (choice : subtle.Choice) :
    ∃ res, subtle.ConditionallySelectableU8.conditional_select a b choice = ok res ∧
    res = if choice.val = 1#u8 then b else a := by
  unfold subtle.ConditionallySelectableU8.conditional_select
  split <;> simp_all

/- [subtle::{subtle::ConditionallySelectable for u8}::conditional_assign]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 521:12-521:74
   Name pattern: [subtle::{subtle::ConditionallySelectable<u8>}::conditional_assign]
   Conditionally assign b to a if choice(1); otherwise leave a unchanged -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u8>}::conditional_assign"]
def subtle.ConditionallySelectableU8.conditional_assign
  (a : U8) (b : U8) (choice : subtle.Choice) : Result U8 :=
  subtle.ConditionallySelectableU8.conditional_select a b choice

/- [subtle::{subtle::ConditionallySelectable for u8}::conditional_swap]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 529:12-529:75
   Name pattern: [subtle::{subtle::ConditionallySelectable<u8>}::conditional_swap]
   Conditionally swap a and b if choice(1); otherwise leave them unchanged -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u8>}::conditional_swap"]
def subtle.ConditionallySelectableU8.conditional_swap
  (a : U8) (b : U8) (choice : subtle.Choice) : Result (U8 × U8) := do
  let a_new ← subtle.ConditionallySelectableU8.conditional_select a b choice
  let b_new ← subtle.ConditionallySelectableU8.conditional_select b a choice
  ok (a_new, b_new)

/- [zeroize::{zeroize::Zeroize for alloc::vec::Vec<Z>}::zeroize]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.8.2/src/lib.rs', lines 551:4-551:25
   Name pattern: [zeroize::{zeroize::Zeroize<alloc::vec::Vec<@Z>>}::zeroize] -/
@[rust_fun "zeroize::{zeroize::Zeroize<alloc::vec::Vec<@Z>>}::zeroize"]
axiom zeroize.ZeroizeVec.zeroize
  {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) :
  alloc.vec.Vec Z → Result (alloc.vec.Vec Z)

/- [curve25519_dalek::backend::serial::curve_models::{core::cmp::PartialEq<curve25519_dalek::backend::serial::curve_models::AffineNielsPoint> for curve25519_dalek::backend::serial::curve_models::AffineNielsPoint}::ne]:
   Source: 'curve25519-dalek/src/backend/serial/curve_models/mod.rs', lines 182:26-182:35 -/
axiom backend.serial.curve_models.PartialEqAffineNielsPointAffineNielsPoint.ne
  :
  backend.serial.curve_models.AffineNielsPoint →
    backend.serial.curve_models.AffineNielsPoint → Result Bool

/- [curve25519_dalek::field::{core::cmp::PartialEq<curve25519_dalek::backend::serial::u64::field::FieldElement51> for curve25519_dalek::backend::serial::u64::field::FieldElement51}::ne]:
   Source: 'curve25519-dalek/src/field.rs', lines 86:0-90:1 -/
axiom field.PartialEqFieldElement51FieldElement51.ne
  :
  backend.serial.u64.field.FieldElement51 →
    backend.serial.u64.field.FieldElement51 → Result Bool

/- [curve25519_dalek::scalar::{core::cmp::PartialEq<curve25519_dalek::scalar::Scalar> for curve25519_dalek::scalar::Scalar}::ne]:
   Source: 'curve25519-dalek/src/scalar.rs', lines 294:0-298:1 -/
axiom scalar.PartialEqScalarScalar.ne
  : scalar.Scalar → scalar.Scalar → Result Bool

/- [curve25519_dalek::scalar::{core::cmp::Eq for curve25519_dalek::scalar::Scalar}::assert_receiver_is_total_eq]:
   Source: 'curve25519-dalek/src/scalar.rs', lines 293:0-293:21 -/
axiom scalar.EqScalar.assert_receiver_is_total_eq
  : scalar.Scalar → Result Unit

/- [curve25519_dalek::scalar::{subtle::ConditionallySelectable for curve25519_dalek::scalar::Scalar}::conditional_assign]:
   Source: 'curve25519-dalek/src/scalar.rs', lines 389:0-398:1 -/
axiom scalar.ConditionallySelectableScalar.conditional_assign
  : scalar.Scalar → scalar.Scalar → subtle.Choice → Result scalar.Scalar

/- [curve25519_dalek::scalar::{subtle::ConditionallySelectable for curve25519_dalek::scalar::Scalar}::conditional_swap]:
   Source: 'curve25519-dalek/src/scalar.rs', lines 389:0-398:1 -/
axiom scalar.ConditionallySelectableScalar.conditional_swap
  :
  scalar.Scalar → scalar.Scalar → subtle.Choice → Result (scalar.Scalar
    × scalar.Scalar)

/- [subtle::{subtle::ConditionallySelectable for @Array<T, N>}::conditional_select]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 581:4-581:69
   Name pattern: [subtle::{subtle::ConditionallySelectable<[@T; @N]>}::conditional_select]
   Conditional select for arrays: returns a if choice=0, b if choice=1 -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<[@T; @N]>}::conditional_select"]
def subtle.ConditionallySelectableArray.conditional_select
  {T : Type} {N : Usize} (_ConditionallySelectableInst :
  subtle.ConditionallySelectable T)
  (a : Array T N) (b : Array T N) (choice : subtle.Choice) : Result (Array T N) :=
  if choice.val = 1#u8 then ok b
  else ok a

/-- Progress spec for ConditionallySelectableArray.conditional_select -/
@[progress]
theorem conditional_select_Array_spec {T : Type} {N : Usize}
    (inst : subtle.ConditionallySelectable T)
    (a b : Array T N) (choice : subtle.Choice) :
    ∃ res, subtle.ConditionallySelectableArray.conditional_select inst a b choice = ok res ∧
    res = if choice.val = 1#u8 then b else a := by
  unfold subtle.ConditionallySelectableArray.conditional_select
  split <;> simp_all

/- [subtle::{subtle::ConditionallySelectable for @Array<T, N>}::conditional_assign]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 587:4-587:66
   Name pattern: [subtle::{subtle::ConditionallySelectable<[@T; @N]>}::conditional_assign]
   Conditional assign for arrays: assign a with the value of conditional_select(a, b, choice). -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<[@T; @N]>}::conditional_assign"]
def subtle.ConditionallySelectableArray.conditional_assign
  {T : Type} {N : Usize} (ConditionallySelectableInst :
  subtle.ConditionallySelectable T)
  (a : Array T N) (b : Array T N) (choice : subtle.Choice) : Result (Array T N) :=
  subtle.ConditionallySelectableArray.conditional_select ConditionallySelectableInst a b choice

/- [subtle::{subtle::ConditionallySelectable for @Array<T, N>}::conditional_swap]:
   Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 576:0-578:31
   Name pattern: [subtle::{subtle::ConditionallySelectable<[@T; @N]>}::conditional_swap]
   Conditional swap for arrays: swaps a and b if choice is 1 -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<[@T; @N]>}::conditional_swap"]
def subtle.ConditionallySelectableArray.conditional_swap
  {T : Type} {N : Usize} (ConditionallySelectableInst :
  subtle.ConditionallySelectable T)
  (a : Array T N) (b : Array T N) (choice : subtle.Choice) : Result ((Array T N) × (Array T N)) := do
  let a_new ← subtle.ConditionallySelectableArray.conditional_select ConditionallySelectableInst a b choice
  let b_new ← subtle.ConditionallySelectableArray.conditional_select ConditionallySelectableInst b a choice
  ok (a_new, b_new)

/- [curve25519_dalek::montgomery::{subtle::ConditionallySelectable for curve25519_dalek::montgomery::ProjectivePoint}::conditional_swap]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 310:0-321:1 -/
axiom montgomery.ConditionallySelectableProjectivePoint.conditional_swap
  :
  montgomery.ProjectivePoint → montgomery.ProjectivePoint → subtle.Choice
    → Result (montgomery.ProjectivePoint × montgomery.ProjectivePoint)

/- [curve25519_dalek::montgomery::{subtle::ConditionallySelectable for curve25519_dalek::montgomery::MontgomeryPoint}::conditional_assign]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 87:0-91:1 -/
axiom montgomery.ConditionallySelectableMontgomeryPoint.conditional_assign
  :
  montgomery.MontgomeryPoint → montgomery.MontgomeryPoint → subtle.Choice
    → Result montgomery.MontgomeryPoint

/- [curve25519_dalek::montgomery::{subtle::ConditionallySelectable for curve25519_dalek::montgomery::MontgomeryPoint}::conditional_swap]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 87:0-91:1 -/
axiom montgomery.ConditionallySelectableMontgomeryPoint.conditional_swap
  :
  montgomery.MontgomeryPoint → montgomery.MontgomeryPoint → subtle.Choice
    → Result (montgomery.MontgomeryPoint × montgomery.MontgomeryPoint)

/- [curve25519_dalek::montgomery::{core::cmp::PartialEq<curve25519_dalek::montgomery::MontgomeryPoint> for curve25519_dalek::montgomery::MontgomeryPoint}::ne]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 93:0-97:1 -/
axiom montgomery.PartialEqMontgomeryPointMontgomeryPoint.ne
  : montgomery.MontgomeryPoint → montgomery.MontgomeryPoint → Result Bool

/- [curve25519_dalek::montgomery::{core::cmp::Eq for curve25519_dalek::montgomery::MontgomeryPoint}::assert_receiver_is_total_eq]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 99:0-99:30 -/
axiom montgomery.EqMontgomeryPoint.assert_receiver_is_total_eq
  : montgomery.MontgomeryPoint → Result Unit

/- [curve25519_dalek::montgomery::{subtle::ConditionallySelectable for curve25519_dalek::montgomery::ProjectivePoint}::conditional_assign]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 310:0-321:1 -/
axiom montgomery.ConditionallySelectableProjectivePoint.conditional_assign
  :
  montgomery.ProjectivePoint → montgomery.ProjectivePoint → subtle.Choice
    → Result montgomery.ProjectivePoint

end curve25519_dalek
