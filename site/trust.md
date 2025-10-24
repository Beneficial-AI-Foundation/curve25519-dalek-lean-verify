# Trust and Verification Method

## Verification Approach

[Lean] is an open-source programming language and proof assistant, allowing us to write mathematical specifications and prove that the implementation meets these specifications.

In this approach to formal verification, the Rust code is extracted (translated) to a representation in Lean.
The idea is that the Lean code is then a faithful functional representation of the Rust code. 
This is done in a way that panics, failure to terminate, etc., are represented in the extracted code, in addition to being an accurate function representation. 
In this project we use [Aeneas] for this extraction.

## What You Need to Trust

To trust that the curve25519-dalek implementation satisfies the proven specifications, you need to trust:

### 1. The Lean Proof Checker
- Lean’s minimal trusted kernel guarantees absolute correctness in the proofs

### 2. The Aeneas Translation
- One needs to know that the Lean code extracted by Aeneas faithfully represents the Rust code, this is a limited set of translations and subject to ongoing [soundness proofs][aeneas-proofs] 

### 3. The Specifications
- The specifications are written in Lean which allows a phrasing which is convenient for humans to parse and allows easy drilling down into details using the interactive feature of Lean

### 4. External specifications
- External dependencies of the crate have specs written in `FunsExternal.lean` and `TypesExternal.lean` so these files need to be inspected to ensure that these specs are correct

## What You Don't Need to Check
- Trust of spec proofs doesn't require inspecting the proofs themselves since this is checked by Lean
- That no additional axioms have been introduced in the proofs can be checked by `#print axioms spec_theorem_name`

[Aeneas]: https://github.com/AeneasVerif/aeneas
[Lean]: https://lean-lang.org
[aeneas-proofs]: https://github.com/AeneasVerif/aeneas#formalization