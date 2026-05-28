/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Alessandro D'Angelo, Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec theorem for `curve25519_dalek::backend::serial::scalar_mul::vartime_double_base::mul`

Computes the double-base scalar multiplication \(aA + bB\) in variable time, where \(B\) is
the Ed25519 basepoint, using joint non-adjacent form (NAF) representations of the two scalars
and precomputed NAF lookup tables for both points.

Source: "curve25519-dalek/src/backend/serial/scalar_mul/vartime_double_base.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.scalar_mul.vartime_double_base

-- Specification theorem to be written here

end curve25519_dalek.backend.serial.scalar_mul.vartime_double_base
