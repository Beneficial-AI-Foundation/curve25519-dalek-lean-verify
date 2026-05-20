/-
Chapter: Scalar arithmetic.

Covers: Curve25519Dalek/Specs/Scalar/*
        — operations on scalars mod ℓ (the group order).

TODO (authors):
  - Replace the placeholder prose with an overview of scalar arithmetic
    and the canonical/non-canonical byte encodings.
  - Add a `:::definition` or `:::theorem` block per spec in
    `Curve25519Dalek/Specs/Scalar/`.
-/

import VersoManual
import VersoBlueprint
import Curve25519Dalek.Specs.Scalar.ClampInteger

open Verso.Genre Manual
open Informal


#doc (Manual) "Scalar arithmetic" =>
%%%
tag := "scalar"
%%%

TODO: overview of `Scalar` (52-bit limb form), the group order ℓ,
Montgomery form, and canonical byte encodings.

# Example: clamping

:::theorem "scalar_clamp_integer" (lean := "curve25519_dalek.scalar.clamp_integer_spec")
TODO: describe `clamp_integer` — the standard bit-clamping required
before treating raw bytes as an X25519/Ed25519 scalar.
:::
