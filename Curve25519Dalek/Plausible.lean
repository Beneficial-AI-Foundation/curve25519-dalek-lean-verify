-- Plausible property-based testing support for curve25519-dalek types.
--
-- Key findings from Aeneas source (used to guide instances below):
--   Std.U64  = UScalar .U64 = { bv : BitVec 64 }
--   Std.Array T n = { l : List T // l.length = n.val }
--   Construction: ⟨BitVec.ofNat 64 m⟩ for scalar types;
--                 Array.make / Array.repeat for array types.
--   WP.spec x p = theta x p, where theta dispatches on ok / fail / div.

import Plausible
import Curve25519Dalek.Funs

open Plausible Arbitrary
open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek

/-! ## Primitive scalar types

`Std.U8/U16/U32/U64/USize` are all `UScalar ty = { bv : BitVec ty.numBits }`.
`BitVec.ofNat` wraps any `Nat` via modulo, so no bounds proof is needed at the
call site — values from `Gen.choose` are already in range.
`Nat.shrink` halves toward 0, giving a proper shrink sequence (not just `[]`). -/

private def mkUScalar {ty : UScalarTy} (m : Nat) : UScalar ty :=
  { bv := BitVec.ofNat _ m }

-- Generate a UScalar with edge-case bias toward 0 and the max value.
private def genUScalarN (ty : UScalarTy) : Gen (UScalar ty) := do
  let max := 2 ^ ty.numBits - 1
  let rand := do let ⟨v, _⟩ ← Gen.choose Nat 0 max (Nat.zero_le _); pure v
  let m ← Gen.frequency rand [(90, rand), (5, pure 0), (5, pure max)]
  return mkUScalar m

instance : Arbitrary Std.U8    where arbitrary := genUScalarN .U8
instance : Arbitrary Std.U16   where arbitrary := genUScalarN .U16
instance : Arbitrary Std.U32   where arbitrary := genUScalarN .U32
instance : Arbitrary Std.U64   where arbitrary := genUScalarN .U64
instance : Arbitrary Std.Usize where arbitrary := genUScalarN .Usize

-- Shrink by halving the underlying Nat toward 0, then re-wrapping.
instance : Shrinkable Std.U8    where shrink u := Nat.shrink u.val |>.map mkUScalar
instance : Shrinkable Std.U16   where shrink u := Nat.shrink u.val |>.map mkUScalar
instance : Shrinkable Std.U32   where shrink u := Nat.shrink u.val |>.map mkUScalar
instance : Shrinkable Std.U64   where shrink u := Nat.shrink u.val |>.map mkUScalar
instance : Shrinkable Std.Usize where shrink u := Nat.shrink u.val |>.map mkUScalar

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

/-! ## Bounded `Array U64 5` sampling for subtype preconditions

Plausible's `subtypeVarTestable` instance (priority 2000) handles propositions of
the shape `∀ (a : α), p a → Q a` by sampling `a` from `{ a : α // p a }` directly,
rather than generating `a` freely and then filtering.  This eliminates the
vacuous-success problem for hypotheses like `ha : ∀ i < 5, a[i]!.val < 2^53`,
which are satisfied by only ≈ 1/2^110 of unconstrained arrays.

The required `Repr` and `Shrinkable` pieces come for free:
• `Repr` — Lean 4's built-in `Repr (Subtype p)` delegates to `Repr (Array U64 5)`.
• `Shrinkable` — Plausible's `Subtype.shrinkable` shrinks the inner array and
  filters candidates via the decidable predicate.
• `SampleableExt` — `SampleableExt.selfContained` assembles the above three.

The only piece we must supply is `Arbitrary`. -/

-- Like `genListN` but driven by an explicit element generator.
private def genListNWith {T : Type} (g : Gen T) :
    (n : Nat) → Gen {l : List T // l.length = n}
  | 0     => pure ⟨[], rfl⟩
  | n + 1 => do
    let x      ← g
    let ⟨xs, h⟩ ← genListNWith g n
    return ⟨x :: xs, by simp [h]⟩

-- Single U64 limb uniformly sampled from [0, bound − 1]; falls back to 0 for bound = 0.
private def genBoundedLimb (bound : Nat) : Gen U64 := do
  let max := if 0 < bound then bound - 1 else 0
  let rand := do let ⟨v, _⟩ ← Gen.choose Nat 0 max (Nat.zero_le _); pure v
  let m ← Gen.frequency rand [(90, rand), (5, pure 0), (5, pure max)]
  return mkUScalar m

-- `Array U64 5` with every limb < bound.
private def genBoundedFEArr (bound : Nat) : Gen (Array U64 5#usize) := do
  let ⟨elems, h⟩ ← genListNWith (genBoundedLimb bound) 5
  return Array.make 5#usize elems h

/-- `Arbitrary` for `{ a : Array U64 5 // ∀ i < 5, a[i]!.val < bound }`.

`genBoundedFEArr` keeps every limb in `[0, bound − 1]`, so the runtime decidability
check always succeeds for `bound > 0`.  For `bound = 0` the subtype is empty and
`throw` causes Plausible to report "gave up", which is the correct outcome. -/
instance (bound : Nat) :
    Arbitrary { a : Array U64 5#usize // ∀ i < 5, a[i]!.val < bound } where
  arbitrary := do
    let arr ← genBoundedFEArr bound
    if h : ∀ i < 5, arr[i]!.val < bound then
      pure ⟨arr, h⟩
    else
      throw (.genError s!"bounded-limb generator produced a limb ≥ {bound}")

/-! ## Domain types

`@[reducible]` def aliases (`FieldElement51`, `Scalar52`, `CompressedEdwardsY`,
`MontgomeryPoint`, `CompressedRistretto`, `RistrettoPoint`) inherit all instances from
the array/EdwardsPoint instances above via typeclass unfolding — no explicit delegation needed.

Explicit instances are required for each concrete `structure`. -/

-- scalar.Scalar { bytes : Array U8 32 }
instance : Arbitrary scalar.Scalar where
  arbitrary := do return { bytes := ← arbitrary }

instance : Shrinkable scalar.Scalar where
  shrink s := (Shrinkable.shrink s.bytes).map fun b => { bytes := b }

instance : Repr scalar.Scalar where
  reprPrec s prec := reprPrec s.bytes prec

-- edwards.EdwardsPoint { X Y Z T : FieldElement51 }
instance : Arbitrary edwards.EdwardsPoint where
  arbitrary := do
    return { X := ← arbitrary, Y := ← arbitrary, Z := ← arbitrary, T := ← arbitrary }

instance : Shrinkable edwards.EdwardsPoint where
  shrink p :=
    (Shrinkable.shrink p.X).map (fun x => { p with X := x }) ++
    (Shrinkable.shrink p.Y).map (fun y => { p with Y := y }) ++
    (Shrinkable.shrink p.Z).map (fun z => { p with Z := z }) ++
    (Shrinkable.shrink p.T).map (fun t => { p with T := t })

instance : Repr edwards.EdwardsPoint where
  reprPrec p prec := reprPrec (p.X, p.Y, p.Z, p.T) prec

-- edwards.affine.AffinePoint { x y : FieldElement51 }
instance : Arbitrary edwards.affine.AffinePoint where
  arbitrary := do return { x := ← arbitrary, y := ← arbitrary }

instance : Shrinkable edwards.affine.AffinePoint where
  shrink p :=
    (Shrinkable.shrink p.x).map (fun x => { p with x := x }) ++
    (Shrinkable.shrink p.y).map (fun y => { p with y := y })

instance : Repr edwards.affine.AffinePoint where
  reprPrec p prec := reprPrec (p.x, p.y) prec

-- montgomery.ProjectivePoint { U W : FieldElement51 }
instance : Arbitrary montgomery.ProjectivePoint where
  arbitrary := do return { U := ← arbitrary, W := ← arbitrary }

instance : Shrinkable montgomery.ProjectivePoint where
  shrink p :=
    (Shrinkable.shrink p.U).map (fun u => { p with U := u }) ++
    (Shrinkable.shrink p.W).map (fun w => { p with W := w })

instance : Repr montgomery.ProjectivePoint where
  reprPrec p prec := reprPrec (p.U, p.W) prec

-- backend.serial.curve_models.ProjectivePoint { X Y Z : FieldElement51 }
instance : Arbitrary backend.serial.curve_models.ProjectivePoint where
  arbitrary := do return { X := ← arbitrary, Y := ← arbitrary, Z := ← arbitrary }

instance : Shrinkable backend.serial.curve_models.ProjectivePoint where
  shrink p :=
    (Shrinkable.shrink p.X).map (fun x => { p with X := x }) ++
    (Shrinkable.shrink p.Y).map (fun y => { p with Y := y }) ++
    (Shrinkable.shrink p.Z).map (fun z => { p with Z := z })

instance : Repr backend.serial.curve_models.ProjectivePoint where
  reprPrec p prec := reprPrec (p.X, p.Y, p.Z) prec

-- backend.serial.curve_models.ProjectiveNielsPoint { Y_plus_X Y_minus_X Z T2d : FieldElement51 }
instance : Arbitrary backend.serial.curve_models.ProjectiveNielsPoint where
  arbitrary := do
    return { Y_plus_X := ← arbitrary, Y_minus_X := ← arbitrary,
             Z        := ← arbitrary, T2d       := ← arbitrary }

instance : Shrinkable backend.serial.curve_models.ProjectiveNielsPoint where
  shrink p :=
    (Shrinkable.shrink p.Y_plus_X).map  (fun x => { p with Y_plus_X  := x }) ++
    (Shrinkable.shrink p.Y_minus_X).map (fun x => { p with Y_minus_X := x }) ++
    (Shrinkable.shrink p.Z).map         (fun z => { p with Z         := z }) ++
    (Shrinkable.shrink p.T2d).map       (fun t => { p with T2d       := t })

instance : Repr backend.serial.curve_models.ProjectiveNielsPoint where
  reprPrec p prec := reprPrec (p.Y_plus_X, p.Y_minus_X, p.Z, p.T2d) prec

-- backend.serial.curve_models.AffineNielsPoint { y_plus_x y_minus_x xy2d : FieldElement51 }
instance : Arbitrary backend.serial.curve_models.AffineNielsPoint where
  arbitrary := do
    return { y_plus_x := ← arbitrary, y_minus_x := ← arbitrary, xy2d := ← arbitrary }

instance : Shrinkable backend.serial.curve_models.AffineNielsPoint where
  shrink p :=
    (Shrinkable.shrink p.y_plus_x).map  (fun x => { p with y_plus_x  := x }) ++
    (Shrinkable.shrink p.y_minus_x).map (fun x => { p with y_minus_x := x }) ++
    (Shrinkable.shrink p.xy2d).map      (fun d => { p with xy2d      := d })

instance : Repr backend.serial.curve_models.AffineNielsPoint where
  reprPrec p prec := reprPrec (p.y_plus_x, p.y_minus_x, p.xy2d) prec

-- backend.serial.curve_models.CompletedPoint { X Y Z T : FieldElement51 }
instance : Arbitrary backend.serial.curve_models.CompletedPoint where
  arbitrary := do
    return { X := ← arbitrary, Y := ← arbitrary, Z := ← arbitrary, T := ← arbitrary }

instance : Shrinkable backend.serial.curve_models.CompletedPoint where
  shrink p :=
    (Shrinkable.shrink p.X).map (fun x => { p with X := x }) ++
    (Shrinkable.shrink p.Y).map (fun y => { p with Y := y }) ++
    (Shrinkable.shrink p.Z).map (fun z => { p with Z := z }) ++
    (Shrinkable.shrink p.T).map (fun t => { p with T := t })

instance : Repr backend.serial.curve_models.CompletedPoint where
  reprPrec p prec := reprPrec (p.X, p.Y, p.Z, p.T) prec

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
  unfold WP.spec theta
  split
  · unfold wp_return; infer_instance
  · infer_instance
  · infer_instance

/-! ## Smoke tests -/

-- Arbitrary instances exist for all key types.
#check (inferInstance : Arbitrary scalar.Scalar)
#check (inferInstance : Arbitrary backend.serial.u64.field.FieldElement51)
#check (inferInstance : Arbitrary edwards.EdwardsPoint)
#check (inferInstance : Arbitrary ristretto.RistrettoPoint)

-- WP.spec is Decidable for a simple postcondition.
example : Decidable (WP.spec (Result.ok (⟨0⟩ : Std.U64)) (fun x => x = ⟨0⟩)) :=
  inferInstance
