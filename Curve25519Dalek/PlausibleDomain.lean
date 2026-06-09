import Curve25519Dalek.Plausible
import Curve25519Dalek.Funs

/-! # Plausible instances for curve25519-dalek domain types

Project-specific `Arbitrary`/`Shrinkable`/`Repr` instances for the curve25519-dalek
structs (`scalar.Scalar`, `edwards.EdwardsPoint`, the `backend.serial.curve_models.*`
points, …) plus the bounded `Array U64 5` sampler used for field-element preconditions.

The generic, upstreamable Aeneas instances live in `Curve25519Dalek.Plausible`; this
file imports them and `Curve25519Dalek.Funs` (for the domain type definitions). -/

open Plausible Arbitrary
open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek

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
