/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Defs

/-! # Spec Theorem for `Scalar52::montgomery_invert`

Specification and proof for `Scalar52::montgomery_invert`.

This function computes the multiplicative inverse using Montgomery form.

**Source**: curve25519-dalek/src/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.scalar.Scalar52

/-
natural language description:

    • Takes as input an UnpackedScalar u that is assumed to be
      in Montgomery form. Then efficiently computes and returns an
      UnpackedScalar u' (also in Montgomery form)  that represents
      the multiplicative inverse of u within the underlying field
      \mathbb{Z} / \ell \mathbb{Z}.

natural language specs:

    • \forall UnpackedScalars u in Montgomery form with u ≠ 0:
      scalar_to_nat(u) * scalar_to_nat(u') is congruent to 1 (mod \ell)
-/


end curve25519_dalek.scalar.Scalar52
