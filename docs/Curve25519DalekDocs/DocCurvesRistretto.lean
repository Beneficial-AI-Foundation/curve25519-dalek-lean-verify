/-
Sub-chapter: Ristretto group operations.

Covers: Curve25519Dalek/Specs/Ristretto/*
-/

import VersoManual
import VersoBlueprint
import Curve25519Dalek.Specs.Ristretto.RistrettoPoint.Compress

open Verso.Genre Manual
open Informal


#doc (Manual) "Ristretto form" =>
%%%
tag := "curves-ristretto"
%%%

TODO: overview of the Ristretto encoding — a prime-order quotient of the
Edwards curve — including `RistrettoPoint`, compression / decompression,
and the relationship to the mathematical model in the Ristretto section
of the Math chapter.

# Example: compression

:::theorem "ristretto_compress" (lean := "curve25519_dalek.ristretto.RistrettoPoint.compress_spec")
TODO: describe the Ristretto compression spec — canonical encoding of a
point as 32 bytes.
:::
