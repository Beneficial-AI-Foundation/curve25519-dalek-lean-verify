# TODO

## Proofs blocked on elaboration issue

Symptom: `step` (or `let*`) succeeds locally in the InfoView but the global theorem elaboration hangs / does not terminate, or rejects the proof term at the kernel. 

- [`Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/FromBytes.lean`](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/FromBytes.lean)
- [`Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/FromBytesWide.lean`](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/FromBytesWide.lean)
- [`Curve25519Dalek/Specs/Ristretto/CompressedRistretto/Decompress.lean`](Curve25519Dalek/Specs/Ristretto/CompressedRistretto/Decompress.lean)
- [`Curve25519Dalek/Specs/Scalar/Scalar/AsRadix2w.lean`](Curve25519Dalek/Specs/Scalar/Scalar/AsRadix2w.lean)
