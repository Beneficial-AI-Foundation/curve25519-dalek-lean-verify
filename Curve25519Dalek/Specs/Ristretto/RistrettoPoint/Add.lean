/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs.Edwards.Representation

/-! # Spec Theorem for `RistrettoPoint::add`

Specification and proof for the `add` trait implementation for Ristretto points.

This function adds two Ristretto points via elliptic curve addition by delegating to the underlying Edwards point addition.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas.Std Result
namespace curve25519_dalek.ristretto.AddShared0RistrettoPointSharedARistrettoPointRistrettoPoint

/-
natural language description:

• Takes two RistrettoPoints `self` and `other`
• Returns their sum as a RistrettoPoint via elliptic curve group addition
• Implementation: unwraps both points to their underlying EdwardsPoint representations,
  performs Edwards addition, and wraps the result back as a RistrettoPoint

natural language specs:

• The function always succeeds (no panic) for valid input Ristretto points
• The result is a valid Ristretto point
• The result represents the sum of the inputs (in the context of elliptic curve addition)
-/

/-- **Spec and proof concerning `ristretto.AddShared0RistrettoPointSharedARistrettoPointRistrettoPoint.add`**:
• The function always succeeds (no panic) for valid inputs
• The result is a valid Ristretto point
• The result represents the sum of the inputs (in the context of elliptic curve addition)
-/
@[progress]
theorem add_spec (self other : RistrettoPoint) (h_self_valid : self.IsValid) (h_other_valid : other.IsValid) :

    ∃ result, add self other = ok result ∧

    result.IsValid ∧

    result.toPoint = self.toPoint + other.toPoint := by

  sorry

/-

Note:

One RistrettoPoint r corresponds to an equivalence class of several
mathematical curve points.

The command r.toPoint thus maps r to one of these concrete representatives on the curve (to the representative
that currently just so happens to represent r).

The equation

result.toPoint = self.toPoint + other.toPoint

thus assures that the concrete representatives of the input RistrettoPoints on the curve sum up to
the concrete representative of the output Ristretto point on the curve. Since the addition on RistrettoPoints is
mathematically well-defined (i.e., it does not depend on the choice of representatives), the condition

result.toPoint = self.toPoint + other.toPoint

thus indeed implies that the output RistrettoPoint (seen as an equivalence class) is the mathematically correct sum
of the input RistrettoPoints (seen as equivalence classes), even though we are only working at the level
of (fairly arbitrary) representatives.

The fact that the addition of RistrettoPoints is indeed well-defined and does not depend on the chosen
representatives follows from standard results in abstract algebra: in any set of left cosets G/N, the product

(aN)(bN)=(ab)N

constitutes a well-defined operation that does not depend on the chosen representatives a, b iff N is a normal subgroup;
and in an Abelian group (our elliptic curve group is Abelian), every subgroup is normal.

-/

end curve25519_dalek.ristretto.AddShared0RistrettoPointSharedARistrettoPointRistrettoPoint
