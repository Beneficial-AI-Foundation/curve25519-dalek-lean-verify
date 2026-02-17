# TODO

- Hide functions if required 
- Avoid the Opaque Default Trait Methods problem: these are the axioms we added to funsexternal. mostly these are not used in the rest of the code and are better excluded.
- Remove all task markers
- check that namespaces are correct so that all spec theorems are counted correctly
- Mend all the proofs which have been replaced with a sorry in the updates. 


## Proofs replaced with `sorry` (old proofs kept as comments)

These proofs were working with the old Aeneas spec form but need updating for the new WP `spec` form:

- `Curve25519Dalek/Specs/Field/FieldElement51/IsNegative.lean` — `is_negative_spec`
- `Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/CtEq.lean` — `ct_eq_spec`
- `Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Sub.lean` — `sub_spec` (manual `obtain` pattern incompatible with WP; needs step-by-step `progress` rewrite)
- `Curve25519Dalek/Specs/Montgomery/MontgomeryPoint/CtEq.lean` — `ct_eq_spec` (needs proof update for WP spec form)
- `Curve25519Dalek/Specs/Backend/Serial/CurveModels/AffineNielsPoint/Eq.lean` — `eq_spec`
- `Curve25519Dalek/Specs/Montgomery/MontgomeryPoint/Eq.lean` — `eq_spec` (needs proof update for WP spec form)
- `Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/ConditionalAssign.lean` — `conditional_assign_spec`
- `Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/Sub.lean` — `sub_loop_spec` (progress tactic subgoal resolution changed in WP form)
- `Curve25519Dalek/Specs/Montgomery/MontgomeryPoint/MulBaseClamped.lean` — `mul_base_clamped_spec` (postcondition uses `= ok` which WP trace doesn't expose)
- `Curve25519Dalek/Specs/Field/FieldElement51/SqrtRatioi.lean` — `sqrt_ratio_i_spec` (~1070 lines, extensive WP migration issues: rcases on WP-style match, identifier renames, inlined conditional_negate)
- `Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/MontgomeryReduce.lean` — `part1_spec`, `part2_spec` (tuple-returning functions, spec form conversion)
- `Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/FromMontgomery.lean` — `from_montgomery_loop_spec`, `from_montgomery_spec`
- `Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/MontgomerySquare.lean` — `montgomery_square_spec`
- `Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/MontgomeryMul.lean` — `montgomery_mul_spec`
- `Curve25519Dalek/Specs/Field/FieldElement51/InvSqrt.lean` — `inv_sqrt_spec`
- `Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/AsMontgomery.lean` — `as_montgomery_spec`
- `Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareMultiply.lean` — `square_multiply_loop_spec`, `square_multiply_spec`
- `Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/MontgomeryInvert.lean` — `montgomery_invert_spec`
- `Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/Invert.lean` — `invert_spec`
- `Curve25519Dalek/Specs/Scalar/Scalar/Reduce.lean` — `reduce_spec`
- `Curve25519Dalek/Specs/Scalar/Scalar/Invert.lean` — `invert_spec`
- `Curve25519Dalek/Specs/Scalar/Scalar/IsCanonical.lean` — `is_canonical_spec`
- `Curve25519Dalek/Specs/Scalar/Scalar/FromBytesModOrder.lean` — `from_bytes_mod_order_spec`
- `Curve25519Dalek/Specs/Scalar/Scalar/FromCanonicalBytes.lean` — `from_canonical_bytes_spec`
- `Curve25519Dalek/Specs/Edwards/EdwardsPoint/ToAffine.lean` — `to_affine_spec`
- `Curve25519Dalek/Specs/Edwards/EdwardsPoint/ToMontgomery.lean` — `to_montgomery_spec`
- `Curve25519Dalek/Specs/Montgomery/MontgomeryPoint/MulClamped.lean` — `mul_clamped_spec`
- `Curve25519Dalek/Specs/Edwards/EdwardsPoint/MulBaseClamped.lean` — `mul_base_clamped_spec`
- `Curve25519Dalek/Specs/Field/FieldElement51/Invert.lean` — `invert_spec`
- `Curve25519Dalek/Specs/Edwards/EdwardsPoint/MulByCofactor.lean` — `mul_by_cofactor_spec`
- `Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/ConditionalAddL.lean` — `conditional_add_l_loop_spec`, `conditional_add_l_spec`


## Proofs which have long build times replaced by sorry to concentrate on others.

- `Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Pow2K.lean` — `pow2k_spec`
- `Curve25519Dalek/Specs/Field/FieldElement51/Pow22501.lean` — `pow22501_spec`