/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Lean

/-! # Externally Verified attribute

`@[externally_verified]` marks a theorem whose proof uses `sorry` but has been
verified externally (e.g., a proof exists but not in Lean).

This allows distinguishing intentional `sorry` from genuinely incomplete proofs, both
for human readers and for automated tools that harvest verification status. -/

open Lean

/-- `@[externally_verified]` marks a theorem whose proof uses `sorry` but has been
verified externally. Attach details as a comment close to the attribute. -/
initialize externallyVerifiedAttr : TagAttribute ←
  registerTagAttribute `externally_verified
    "Marks a theorem as externally verified (sorry is intentional)."
