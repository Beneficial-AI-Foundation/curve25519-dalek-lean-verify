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
