/-
Sub-chapter: Edwards curve operations.

Covers: Curve25519Dalek/Specs/Edwards/*
-/

import VersoManual
import VersoBlueprint
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Double

open Verso.Genre Manual
open Informal


#doc (Manual) "Edwards form" =>
%%%
tag := "curves-edwards"
%%%

TODO: overview of the twisted Edwards model of Curve25519 (Ed25519),
`EdwardsPoint` in projective coordinates, and the relationship to the
mathematical model in the Edwards section of the Math chapter.

# Example: point doubling

:::theorem "edwards_double" (lean := "curve25519_dalek.edwards.EdwardsPoint.double_spec")
TODO: describe `EdwardsPoint.double` and its specification.
:::
