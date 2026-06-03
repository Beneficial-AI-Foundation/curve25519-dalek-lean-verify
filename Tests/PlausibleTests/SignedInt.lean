/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Curve25519Dalek.Plausible

/-! # Plausible tests for signed-integer instances

Sanity checks that the `Arbitrary`/`Shrinkable` instances for signed scalar types
(`I8`/`I16`/`I32`/`I64`/`Isize`) generate in-range values and that arrays of them
work. Part of the `Tests` library, which is not in `defaultTargets`, so these
randomized `#eval`s do not run on a normal `lake build` — use `lake build Tests`. -/

open Plausible
open Aeneas.Std

-- Test that signed integers can be generated and tested (should pass)
#eval Plausible.Testable.check
  (∀ (x : I8), x.val ≥ -128 ∧ x.val ≤ 127)
  (cfg := { numInst := 100 })

#eval Plausible.Testable.check
  (∀ (x : I16), x.val ≥ -32768 ∧ x.val ≤ 32767)
  (cfg := { numInst := 100 })

#eval Plausible.Testable.check
  (∀ (x : I64), x.val ≥ -9223372036854775808)
  (cfg := { numInst := 100 })

-- Test that arrays of signed integers work (should pass)
#eval Plausible.Testable.check
  (∀ (arr : Array I8 5#usize), arr.val.length = 5)
  (cfg := { numInst := 100 })

-- Test that I32 and Isize also work
#eval Plausible.Testable.check
  (∀ (x : I32), x.val ≥ -2147483648 ∧ x.val ≤ 2147483647)
  (cfg := { numInst := 100 })

#eval Plausible.Testable.check
  (∀ (x : Isize), x.val ≥ -9223372036854775808)
  (cfg := { numInst := 100 })
