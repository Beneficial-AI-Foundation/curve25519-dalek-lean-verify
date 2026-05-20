/-
Top-level blueprint chapter for the Curve25519-Dalek Lean verification.

This file assembles individual chapter modules via `{include 1 …}`. Each
chapter lives in `Curve25519DalekDocs/Doc*.lean`. Add a new chapter by
creating the file, importing it here, and inserting a corresponding
`{include 1 ModuleName}` line below.
-/

import VersoManual

import Curve25519DalekDocs.DocField
import Curve25519DalekDocs.DocScalar
import Curve25519DalekDocs.DocCurves
import Curve25519DalekDocs.DocBackend
import Curve25519DalekDocs.DocMath
import Curve25519DalekDocs.DocConstants

open Verso.Genre Manual

set_option doc.verso true
set_option pp.rawOnError true


#doc (Manual) "Curve25519-Dalek Lean Verification" =>
%%%
authors := []
shortTitle := "Curve25519-Dalek"
%%%

This is the blueprint for the Lean 4 formalization of the
[curve25519-dalek](https://github.com/dalek-cryptography/curve25519-dalek)
Rust library. Rust source is extracted into Lean by
[Aeneas](https://github.com/AeneasVerif/aeneas); the chapters below
relate the formal specifications and theorems back to the underlying
mathematical objects.

The source code is available on
[GitHub](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify).

{include 1 Curve25519DalekDocs.DocField}

{include 1 Curve25519DalekDocs.DocScalar}

{include 1 Curve25519DalekDocs.DocCurves}

{include 1 Curve25519DalekDocs.DocBackend}

{include 1 Curve25519DalekDocs.DocMath}

{include 1 Curve25519DalekDocs.DocConstants}
