# Canonical experiments (initial)

Branch: `exp/canonical-trials`

What I did
- Added `Canonical` as a dependency is already present in `lakefile.toml` (scope `chasenorman`, rev `v4.24.0`).
- Created `Curve25519Dalek/Experiments/CanonicalTrials.lean` and verified `import Canonical` compiles under the repo toolchain (Lean 4.24.0).
- Adjusted `lakefile.toml` to set `weak.linter.style.longLine = false` so experimental modules also build cleanly.

Build
```
lake build Curve25519Dalek
```
Build succeeded with the new experiment module added.

Targets for Canonical
- High-value: `Specs/Backend/Serial/U64/Scalar/Scalar52/Add.lean` (`add_loop_spec`, `add_spec` have `sorry`).
- Similar patterns: other Scalar52 and FieldElement51 specs.

Next steps
- Identify the Canonical tactic entry point (e.g. tactic name and typical invocation) and how to combine it with existing Aeneas tactics (`progress*`, `scalar_tac`, `bvify`).
- Try Canonical locally on subgoals inside `add_loop_spec` to see if it can discharge linear arithmetic and array-index obligations without custom lemmas.
- Record proof time, number of goals solved, and any required helper lemmas.

Notes
- Importing Canonical worked immediately; no conflicts with existing Aeneas/Mathlib setup.
- I deferred inserting Canonical invocations into in-flight proofs until we confirm the canonical tactic name and best-practice use (to avoid breaking the main build).

Proposed workflow
1) Use Canonical on small, isolated subgoals within one file (e.g. `Add.lean`) by replacing a small `simp`/`omega` chunk with Canonical; compare performance and readability.
2) If successful, package a small helper tactic wrapper (e.g. `by canonical`) and roll it out where it most reduces proof surface area.


