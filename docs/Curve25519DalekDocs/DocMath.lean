/-
Chapter: Mathematical models.

Covers: Curve25519Dalek/Math/*
        — abstract Edwards / Montgomery / Ristretto curves the specs
          target, plus shared field constants and prime certificates.

TODO (authors):
  - Replace the placeholder prose with an exposition of the curve theory
    used as the spec target (twisted Edwards equation, Montgomery form,
    Ristretto quotient).
-/

import VersoManual
import VersoBlueprint
import Curve25519Dalek.Math.Edwards.Curve
import Curve25519Dalek.Math.Edwards.Basepoint
import Curve25519Dalek.Math.Montgomery.Curve

open Verso.Genre Manual
open Informal


#doc (Manual) "Mathematical models" =>
%%%
tag := "math"
%%%

TODO: overview of the underlying curve theory.

# Edwards model

:::group "math-edwards"
The twisted Edwards model of Curve25519, used as the spec target for
Ed25519 group operations.
:::

:::definition "math_ed25519" (lean := "Edwards.Ed25519") (parent := "math-edwards")
TODO: state the twisted-Edwards curve equation and the Ed25519 parameters
`a = -1`, `d`.
:::

:::definition "math_edwards_basepoint" (lean := "Edwards.basepoint") (parent := "math-edwards")
TODO: describe the standard Ed25519 basepoint as a `Point Ed25519`.
:::

# Montgomery model

:::group "math-montgomery"
The Montgomery model of Curve25519, used as the spec target for X25519.
:::

:::definition "math_montgomery_curve" (lean := "Montgomery.MontgomeryCurveCurve25519") (parent := "math-montgomery")
TODO: state the Montgomery curve equation `y² = x³ + Ax² + x` and the
Curve25519 parameter `A = 486662`.
:::

# Ristretto model

:::group "math-ristretto"
The Ristretto quotient: a prime-order group obtained from the Edwards
curve by identifying torsion-equivalent points.
:::

TODO: definition blocks for the Ristretto compress/decompress maps in
`Curve25519Dalek/Math/Ristretto/Representation.lean`.
