/-
Chapter: Curve models.

Parent of three sub-chapters, one per curve representation:
  - Edwards form (Ed25519, twisted Edwards)
  - Montgomery form (Curve25519, used for X25519)
  - Ristretto form (prime-order quotient)

Each sub-chapter lives in its own `Doc*.lean` and is inlined here with
`{include 1 …}`. To add another curve view, create a `DocCurves<Name>.lean`,
`import` it, and add another `{include 1 …}` line.
-/

import VersoManual
import VersoBlueprint
import Curve25519DalekDocs.DocCurvesEdwards
import Curve25519DalekDocs.DocCurvesMontgomery
import Curve25519DalekDocs.DocCurvesRistretto

open Verso.Genre Manual
open Informal


#doc (Manual) "Curve models" =>
%%%
tag := "curves"
%%%

TODO: high-level overview connecting the three curve representations.
Each sub-section below covers one representation in detail.

{include 1 Curve25519DalekDocs.DocCurvesEdwards}

{include 1 Curve25519DalekDocs.DocCurvesMontgomery}

{include 1 Curve25519DalekDocs.DocCurvesRistretto}
