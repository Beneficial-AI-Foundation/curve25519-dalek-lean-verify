/-
Chapter: Field arithmetic.

Covers: Curve25519Dalek/Specs/Field/FieldElement51/*
        — operations on field elements in 𝔽_{2^255 - 19}.

TODO (authors):
  - Replace the placeholder prose with a field-arithmetic overview.
  - Add a `:::definition` or `:::theorem` block for each top-level spec
    in `Curve25519Dalek/Specs/Field/FieldElement51/`.
  - For each block, set `(lean := "fully.qualified.Decl")` to link to the
    corresponding Lean declaration.
  - Wrap proved theorems with `:::proof` blocks for status tracking.
-/

import VersoManual
import VersoBlueprint
import Curve25519Dalek.Specs.Field.FieldElement51.IsZero
import Curve25519Dalek.Specs.Field.FieldElement51.Invert

open Verso.Genre Manual
open Informal


#doc (Manual) "Field arithmetic" =>
%%%
tag := "field"
%%%

TODO: overview of the prime field with `p = 2^255 - 19`, the 51-bit limb
representation (`FieldElement51`), and the operations specified in this chapter.

# Example: zero test

:::definition "field_is_zero" (lean := "curve25519_dalek.field.FieldElement51.is_zero_spec")
TODO: describe the `is_zero` spec for `FieldElement51`.
:::

# Example: inversion

:::theorem "field_invert" (lean := "curve25519_dalek.field.FieldElement51.invert_spec")
TODO: state the `invert` spec — multiplicative inverse in the prime field.
:::
