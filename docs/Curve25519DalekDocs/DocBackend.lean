/-
Chapter: Backend implementations.

Covers: Curve25519Dalek/Specs/Backend/*
        Curve25519Dalek/Specs/Window/*
        — serial u64 backend, multi-scalar multiplication strategies,
          lookup tables.

TODO (authors):
  - Replace the placeholder prose with a tour of the serial-u64 backend
    and the multi-scalar-multiplication algorithms (Straus, vartime
    double-base).
  - Add `:::definition`/`:::theorem` blocks per spec.
-/

import VersoManual
import VersoBlueprint
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.M

open Verso.Genre Manual
open Informal


#doc (Manual) "Backend implementations" =>
%%%
tag := "backend"
%%%

TODO: overview of the serial-u64 backend representations, multi-scalar
multiplication algorithms, and precomputed lookup tables that the curve
operations dispatch through.

# Example: limb-wise multiplication helper

:::theorem "backend_scalar_m" (lean := "curve25519_dalek.backend.serial.u64.scalar.m_spec")
TODO: describe `Scalar52.m` — the per-limb 64×64 → 128-bit multiplication
helper underlying Montgomery-form scalar arithmetic.
:::
