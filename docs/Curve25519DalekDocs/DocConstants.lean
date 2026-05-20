/-
Chapter: Curve constants.

Covers: Curve25519Dalek/Specs/Constants/*
        — global constant values (basepoints, group order) used across
          the rest of the formalization.

TODO (authors):
  - Add a `:::definition` block per constant.
-/

import VersoManual
import VersoBlueprint
import Curve25519Dalek.Specs.Constants.RISTRETTO_BASEPOINT_POINT

open Verso.Genre Manual
open Informal


#doc (Manual) "Constants" =>
%%%
tag := "constants"
%%%

TODO: overview of the named constants used throughout the formalization.

# Example: Ristretto basepoint

:::definition "const_ristretto_basepoint" (lean := "curve25519_dalek.constants.RISTRETTO_BASEPOINT_POINT_spec")
TODO: state the Ristretto basepoint constant.
:::
