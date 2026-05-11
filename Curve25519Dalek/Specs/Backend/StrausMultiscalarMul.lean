/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Alessandro D'Angelo, Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec theorem for `curve25519_dalek::backend::straus_multiscalar_mul`

Performs a multi-scalar multiplication of the form `∑ᵢ sᵢ · Pᵢ` on the Edwards
curve using Straus' algorithm.

Source: "curve25519-dalek/src/backend/mod.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend

-- Specification theorem to be written here

end curve25519_dalek.backend
