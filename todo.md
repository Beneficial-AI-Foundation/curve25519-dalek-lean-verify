# TODO

- Update to latest version of Aeneas to avoid the progress problem which is now patched.
- Hide functions if required
- Avoid the Opaque Default Trait Methods problem: these are the axioms we added to funsexternal. mostly these are not used in the rest of the code and are better excluded from extraction.
- Remove all task markers
- check that namespaces are correct so that all spec theorems are counted correctly

## Proofs replaced with `sorry`, have long build times

- `Curve25519Dalek/Specs/Field/FieldElement51/SqrtRatioi.lean` — `sqrt_ratio_i_spec` (~1070 lines, extensive WP migration issues: rcases on WP-style match, identifier renames, inlined conditional_negate). A WP proof skeleton (`unfold; progress* <;> try grind` + decide/sorry) is commented out in the file but was not build-tested.
- `Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/MontgomeryReduce.lean` — `montgomery_reduce_spec` (main spec still sorry, was commented out even in old version)
- `Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Pow2K.lean` — `pow2k_spec`
- `Curve25519Dalek/Specs/Field/FieldElement51/Pow22501.lean` — `pow22501_spec`
