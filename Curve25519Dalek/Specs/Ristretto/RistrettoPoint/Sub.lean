/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Ristretto.Representation

/-! # Spec Theorem for `RistrettoPoint::sub`

Specification and proof for the `Sub` trait implementation for Ristretto points.

This function subtracts two Ristretto points via elliptic curve subtraction by delegating
to the underlying Edwards point subtraction.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.ristretto
namespace curve25519_dalek.Shared0RistrettoPoint.Insts.CoreOpsArithSubSharedARistrettoPointRistrettoPoint

/-
natural language description:

-/

/-- **Spec and proof concerning `Shared0RistrettoPoint.Insts.CoreOpsArithSubSharedARistrettoPointRistrettoPoint.sub`**:
-/
theorem sub_spec : True := by
  sorry

end curve25519_dalek.Shared0RistrettoPoint.Insts.CoreOpsArithSubSharedARistrettoPointRistrettoPoint
