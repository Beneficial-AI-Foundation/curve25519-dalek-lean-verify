/-
Sub-chapter: Montgomery curve operations.

Covers: Curve25519Dalek/Specs/Montgomery/*
-/

import VersoManual
import VersoBlueprint
import Curve25519Dalek.Specs.Montgomery.MontgomeryPoint.Identity

open Verso.Genre Manual
open Informal


#doc (Manual) "Montgomery form" =>
%%%
tag := "curves-montgomery"
%%%

TODO: overview of the Montgomery model of Curve25519 (used for X25519),
the `MontgomeryPoint` u-coordinate-only representation, projective
coordinates, and the relationship to the mathematical model in the
Montgomery section of the Math chapter.

# Example: identity point

:::theorem "montgomery_identity" (lean := "curve25519_dalek.montgomery.MontgomeryPoint.Insts.Curve25519_dalekTraitsIdentity.identity_spec")
TODO: describe the identity element of the Montgomery form.
:::
