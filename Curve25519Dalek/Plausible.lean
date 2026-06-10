import Plausible
import Aeneas
-- Registers the `linter.mathlibStandardSet` set enabled in `lakefile.toml`; `import Aeneas`
-- alone does not pull it in transitively.
import Mathlib.Tactic.Linter

/-! # Plausible property-based testing support for generic Aeneas types

This file provides the *generic*, project-independent `Plausible` infrastructure for
Aeneas-extracted code: `Arbitrary`/`Shrinkable`/`Repr` instances for the primitive
scalar types (`Std.U8/…/Usize` and `Std.I8/…/Isize`), the fixed-length
`Aeneas.Std.Array T n`, decidability of bounded universal quantifiers, and a
`Decidable` instance for `WP.spec`. None of it depends on curve25519-dalek, so it can be
reviewed in isolation and eventually upstreamed to Aeneas. Project-specific domain
instances live in `Curve25519Dalek.PlausibleDomain`, which imports this file.

Key findings from Aeneas source (used to guide the instances below):
  `Std.U64`  = `UScalar .U64` = `{ bv : BitVec 64 }`
  `Std.Array T n` = `{ l : List T // l.length = n.val }`
  Scalar bounds are provided as `irreducible_def`s: `UScalar.max`, `IScalar.min`,
  `IScalar.max` (`Aeneas/Std/Scalar/Core.lean`); using them keeps the generators in
  step with Aeneas should those definitions ever change.
  `WP.spec x p = theta x p`, where `theta` dispatches on `ok` / `fail` / `div`. -/

open Plausible Arbitrary
open Aeneas Aeneas.Std Result Aeneas.Std.WP

/-! ## Primitive scalar types

`Std.U8/U16/U32/U64/USize` are all `UScalar ty = { bv : BitVec ty.numBits }`.
`BitVec.ofNat` wraps any `Nat` via modulo, so no bounds proof is needed at the
call site — values from `Gen.choose` are already in range.
`Nat.shrink` halves toward 0, giving a proper shrink sequence (not just `[]`). -/

private def mkUScalar {ty : UScalarTy} (m : Nat) : UScalar ty :=
  .mk (BitVec.ofNat _ m)

-- Uniformly sample a `UScalar` from `[0, UScalar.max ty]` (`UScalar.max` is the same
-- bound Aeneas uses to define the type, so this tracks any future change there).
private def genUScalar (ty : UScalarTy) : Gen (UScalar ty) := do
  let ⟨m, _⟩ ← Gen.choose Nat 0 (UScalar.max ty) (Nat.zero_le _)
  return mkUScalar m

instance : Arbitrary Std.U8    where arbitrary := genUScalar .U8
instance : Arbitrary Std.U16   where arbitrary := genUScalar .U16
instance : Arbitrary Std.U32   where arbitrary := genUScalar .U32
instance : Arbitrary Std.U64   where arbitrary := genUScalar .U64
instance : Arbitrary Std.Usize where arbitrary := genUScalar .Usize

-- Shrink by halving the underlying Nat toward 0, then re-wrapping.
instance : Shrinkable Std.U8    where shrink u := Nat.shrink u.val |>.map mkUScalar
instance : Shrinkable Std.U16   where shrink u := Nat.shrink u.val |>.map mkUScalar
instance : Shrinkable Std.U32   where shrink u := Nat.shrink u.val |>.map mkUScalar
instance : Shrinkable Std.U64   where shrink u := Nat.shrink u.val |>.map mkUScalar
instance : Shrinkable Std.Usize where shrink u := Nat.shrink u.val |>.map mkUScalar

/-! ## Signed scalar types

`Std.I8/I16/I32/I64/Isize` are all `IScalar ty = { bv : BitVec ty.numBits }`.
Signed integers use two's complement representation with range `[-2^(N-1), 2^(N-1)-1]`.
`BitVec.ofInt` handles the conversion. A single parametric generator covers all five
types, drawing the bounds from `IScalar.min`/`IScalar.max` (the very definitions Aeneas
uses, so `Isize` automatically gets the platform-correct 64-bit range). -/

private def mkIScalar {ty : IScalarTy} (m : Int) : IScalar ty :=
  .mk (BitVec.ofInt _ m)

-- Shrink an Int toward 0. Each step offers both the next value one closer to 0
-- (`n - 1` / `n + 1`) — so Plausible can walk to the exact boundary of a violated
-- bound — and the halved value, for fast convergence from large magnitudes.
private def shrinkInt (n : Int) : List Int :=
  if n = 0 then []
  else if n > 0 then
    (n - 1) :: (Nat.shrink n.natAbs).map Int.ofNat
  else
    (n + 1) :: (Nat.shrink n.natAbs).map fun m => -(Int.ofNat m)

-- Uniformly sample an `IScalar` from `[IScalar.min ty, IScalar.max ty]`.
private def genIScalar (ty : IScalarTy) : Gen (IScalar ty) := do
  -- `IScalar.min ty = -2^(numBits-1)` and `IScalar.max ty = 2^(numBits-1) - 1`, so the
  -- range is always nonempty (`min ≤ 0 ≤ max`); `Isize` gets the platform-correct bounds.
  let h : IScalar.min ty ≤ IScalar.max ty := by
    simp only [IScalar.min, IScalar.max]
    have : (0 : Int) < 2 ^ (ty.numBits - 1) := by positivity
    omega
  let ⟨m, _⟩ ← Gen.choose Int (IScalar.min ty) (IScalar.max ty) h
  return mkIScalar m

instance : Arbitrary Std.I8    where arbitrary := genIScalar .I8
instance : Arbitrary Std.I16   where arbitrary := genIScalar .I16
instance : Arbitrary Std.I32   where arbitrary := genIScalar .I32
instance : Arbitrary Std.I64   where arbitrary := genIScalar .I64
instance : Arbitrary Std.Isize where arbitrary := genIScalar .Isize

-- Shrink by stepping toward 0, working with the signed interpretation.
instance : Shrinkable Std.I8    where shrink i := shrinkInt i.val |>.map mkIScalar
instance : Shrinkable Std.I16   where shrink i := shrinkInt i.val |>.map mkIScalar
instance : Shrinkable Std.I32   where shrink i := shrinkInt i.val |>.map mkIScalar
instance : Shrinkable Std.I64   where shrink i := shrinkInt i.val |>.map mkIScalar
instance : Shrinkable Std.Isize where shrink i := shrinkInt i.val |>.map mkIScalar

-- Aeneas derives `Repr (IScalar ty)` from the structure, which prints the raw bitvector
-- (`{ bv := 0x01ff#16 }`). Override with the human-readable signed value so reported
-- counter-examples show `511` rather than the two's-complement encoding.
instance : Repr Std.I8    where reprPrec i prec := reprPrec i.val prec
instance : Repr Std.I16   where reprPrec i prec := reprPrec i.val prec
instance : Repr Std.I32   where reprPrec i prec := reprPrec i.val prec
instance : Repr Std.I64   where reprPrec i prec := reprPrec i.val prec
instance : Repr Std.Isize where reprPrec i prec := reprPrec i.val prec

/-! ## Generic `Aeneas.Std.Array T n` instance

Builds a list of exactly `n.val` elements by structural recursion on `n`, so the
length proof is `rfl` / `by simp` at each step.  No `Inhabited` constraint is needed
because every slot is drawn from `arbitrary`. -/

private def genListN {T : Type} [Arbitrary T] :
    (n : Nat) → Gen {l : List T // l.length = n}
  | 0     => pure ⟨[], rfl⟩
  | n + 1 => do
    let x      ← arbitrary
    let ⟨xs, h⟩ ← genListN n
    return ⟨x :: xs, by simp [h]⟩

instance {T : Type} {n : Usize} [Arbitrary T] :
    Arbitrary (Aeneas.Std.Array T n) where
  arbitrary := do
    let ⟨elems, h⟩ ← genListN n.val
    return Array.make n elems h

-- Shrink one element at a time; the fixed-length subtype invariant is preserved by List.set.
private def shrinkListAt {T : Type} [Shrinkable T]
    (l : List T) : List {l' : List T // l'.length = l.length} :=
  (List.finRange l.length).flatMap fun ⟨i, hi⟩ =>
    (Shrinkable.shrink (l.get ⟨i, hi⟩)).map fun x' =>
      ⟨l.set i x', by simp⟩

instance {T : Type} {n : Usize} [Shrinkable T] :
    Shrinkable (Aeneas.Std.Array T n) where
  shrink A :=
    (shrinkListAt A.val).map fun ⟨l', h'⟩ =>
      Array.make n l' (h'.trans A.property)

instance {T : Type} {n : Usize} [Repr T] :
    Repr (Aeneas.Std.Array T n) where
  reprPrec A prec := reprPrec A.val prec

-- `Array α n = {l : List α // l.length = n.val}` is a non-reducible def, so
-- Lean's generic subtype instance doesn't fire. Bridge explicitly.
instance {T : Type} {n : Usize} [DecidableEq T] : DecidableEq (Aeneas.Std.Array T n) :=
  fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm

/-! ## Decidable bounded universal quantification

Three instances together let Plausible evaluate hypotheses of the form
`∀ i < 5, a[i]!.val < 2^53` as guards (via `decGuardTestable`) rather than
treating them as universally-quantified things to sample.

`NamedBinder` is `@[expose]` (not `@[reducible]`), so instance synthesis does
not see through it automatically — the bridge and body instances are both needed. -/

-- Bridge: strip a NamedBinder wrapper for decidability.
instance {s : String} {P : Prop} [Decidable P] :
    Decidable (Plausible.NamedBinder s P) := ‹Decidable P›

-- Body: decide ∀ i : ℕ, NamedBinder s (i < n → Q i), the exact shape Plausible
-- generates for a bounded-hypothesis binder such as `ha : ∀ i < 5, a[i]!.val < 2^53`.
instance {n : Nat} {Q : Nat → Prop} [DecidablePred Q] {s : String} :
    Decidable (∀ i : Nat, Plausible.NamedBinder s (i < n → Q i)) :=
  decidable_of_iff (∀ j : Fin n, Q j.val)
    ⟨fun h i hi => h ⟨i, hi⟩, fun h j => h j.val j.isLt⟩

-- Plain form: decide ∀ i < n, P i (used in postconditions, which carry no NamedBinder).
instance {n : Nat} {P : Nat → Prop} [DecidablePred P] :
    Decidable (∀ i < n, P i) :=
  decidable_of_iff (∀ i : Fin n, P i.val)
    ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i.val i.isLt⟩

/-! ## `WP.spec` Decidable instance

`WP.spec x p = theta x p`.  `theta` pattern-matches on `Result`: `ok x` reduces to
`wp_return x p = p x` (decidable when `p x` is), while `fail` and `div` reduce to `False`. -/

instance {α : Type*} {x : Result α} {p : Post α} [∀ a, Decidable (p a)] :
    Decidable (WP.spec x p) := by
  unfold WP.spec theta wp_return
  split <;> infer_instance

/-! ## TODO

**Bound-aware scalar sampling.** Many specs guard a `U64` (or other wide scalar)
input by a precondition far tighter than the type, e.g. `i : U64, i < 2^52 → P i`
(field-element limbs are 52-bit; `2^52 ≪ 2^64`). The `Arbitrary Std.U64` instance
above samples uniformly over the full `[0, 2^64)` range, so `i < 2^52` holds only
about `2^-12` of the time. Plausible then spends ~99.98 % of its budget on inputs
that satisfy the guard *vacuously* (`i ≥ 2^52` makes `i < 2^52 → P i` trivially
true) and essentially never reaches `P i` — the property goes untested while the
run still reports "passed".

Fix: when a hypothesis has the shape `i < bound → P i` with `bound` below the
type's max, infer `i` from `[0, bound)` directly instead of from the full type.
-/
