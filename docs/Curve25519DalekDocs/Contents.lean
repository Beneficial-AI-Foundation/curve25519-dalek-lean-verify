/-
Copyright (c) 2024-2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VersoManual

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso. Here, they're used to have the text refer to Verso code used in the text's
-- own source.
open Verso.Genre.Manual.InlineLean

-- This gets access to tools for showing Lean code that's loaded from external modules.
open Verso.Code.External

set_option pp.rawOnError true

-- This is the source of code examples to be shown in the document. It should be relative to the
-- current Lake workspace.
set_option verso.exampleProject "."

-- This is the module that will be consulted for example code. It can be overridden using the
-- `(module := ...)` argument to most elements that show code.
set_option verso.exampleModule "Curve25519Dalek"

#doc (Manual) "Curve25519-Dalek Lean Verification" =>
%%%
authors := ["Beneficial AI Foundation"]
shortTitle := "Curve25519-Dalek Verification"
%%%

This project provides a formal verification of the
[curve25519-dalek](https://github.com/dalek-cryptography/curve25519-dalek)
Rust cryptographic library using Lean 4 and
[Aeneas](https://github.com/AeneasVerif/aeneas).

# Overview

Curve25519-dalek is a widely-used Rust library implementing elliptic curve
operations on Curve25519 and the Ristretto group. This verification effort
aims to prove functional correctness of the core cryptographic primitives.

## Verification Approach

The verification uses *Aeneas* to automatically extract Lean 4 code from
the Rust implementation. We then write specifications and proofs for the
extracted functions, ensuring they correctly implement the mathematical
operations.

Key components:

- *Field Arithmetic*: Verification of modular arithmetic over the prime
  field GF(2^255 - 19)
- *Edwards Curve Operations*: Point addition, doubling, and scalar
  multiplication on the twisted Edwards curve
- *Montgomery Ladder*: Constant-time scalar multiplication
- *Ristretto Group*: Abstraction layer providing a prime-order group

# Project Structure

The verification is organized as follows:

- `Curve25519Dalek/Funs.lean` - Auto-generated function definitions from Aeneas
- `Curve25519Dalek/Types.lean` - Auto-generated type definitions from Aeneas
- `Curve25519Dalek/Specs/` - Formal specifications for each function
- `Curve25519Dalek/Math/` - Mathematical foundations (curves, fields, groups)

# Getting Started

To build the project and documentation:

```
lake build
./scripts/build-blueprint.sh
```

The generated documentation will be available in `_out/blueprint/html-multi/`.

# References

- [Curve25519: new Diffie-Hellman speed records](https://cr.yp.to/ecdh/curve25519-20060209.pdf) - Bernstein, 2006
- [The Ristretto Group](https://ristretto.group/) - de Valence et al.
- [curve25519-dalek documentation](https://docs.rs/curve25519-dalek/)
