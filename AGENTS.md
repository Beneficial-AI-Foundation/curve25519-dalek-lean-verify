# Repository Guidelines

## Verification Goal
- Eliminate all `sorry` placeholders across the Lean library by incremental, automated, and maintainable proofs.
- Leverage automation first; prefer small helper lemmas and reusable tactics to reduce proof surface area.

## Automation and Tactics
- Aeneas automations and custom tactics already in this repo (see `Curve25519Dalek/Tactics.lean`), including:
  - `progress` / `progress*` symbolic execution tactics
  - `scalar_tac` for limb arithmetic
  - `bvify`, `bv_decide` for bitvector reasoning
  - Mathlib's `grind` for automated proof search (preferred over `omega` as it subsumes it)
- Built-in `grind` from Lean 4 for algebraic/simplifier-style reasoning (see Lean Reference: [Lean 4 Reference](https://lean-lang.org/doc/reference/latest)).
- Canonical tactic for search/synthesis in dependent type theory; pin to Lean v4.24.0 (repo: [CanonicalLean](https://github.com/chasenorman/CanonicalLean)).
- lean4-skills collection for additional skills/tactics (repo: `https://github.com/cameronfreer/lean4-skills`).
- Use MCP extensively (Lean LSP MCP) to inspect goals, terms, diagnostics during proof development.

## Workflow Notes
- Review commit history (especially contributions by Oliver) to follow established patterns for integrating Aeneas tactics and structuring proofs.
- Prefer targeted imports; keep proofs local to `Specs/<component>/…` and add small reusable lemmas to `Aux.lean`.
- Rebuild frequently (`lake build`); keep proofs fast and deterministic.
- When adding dependencies (Canonical, lean4-skills), pin versions compatible with the current toolchain (see `lean-toolchain`).


## Project Structure & Module Organization
- `Curve25519Dalek/` holds the Lean library; `Defs.lean`, `Funs.lean`, `Types.lean`, and `Tactics.lean` supply shared foundations, while `Specs/<component>/` hosts proofs grouped as Backend, Edwards, Montgomery, Ristretto, and Scalar.
- `Curve25519Dalek.lean` lists modules for Lake builds; register new files here when expanding the library.
- `curve25519-dalek/` vendors the upstream Rust crate and should stay untouched unless syncing with upstream patches.
- `site/` contains the VitePress documentation backed by `status.md` and `status.csv`; `scripts/src-diff.js` supports Rust/Lean drift checks.

## Build, Test, and Development Commands
- `lake build`: type-checks every Lean module; run on each branch before pushing.
- `lake build Curve25519Dalek`: optional focused build when iterating on the primary library.
- `npm install`: one-time setup of the docs toolchain; rerun after dependency bumps.
- `npm run docs:dev` / `npm run docs:build`: preview or validate the VitePress site.
- `node scripts/src-diff.js`: compare Lean signatures with the vendored Rust code.

## Coding Style & Naming Conventions
- Follow Mathlib conventions: two-space indentation, `by` blocks for proofs, and explicit binder declarations (`autoImplicit = false`).
- Name specs after the Rust function (`fn_name_spec`) and keep helper lemmas short and reusable.
- Mirror Rust terminology in `FunsExternal.lean` and `TypesExternal.lean`; document non-obvious rewrites with brief comments.

## Testing Guidelines
- Place new proofs in the relevant `Specs/<component>/` namespace and import only needed modules.
- Run `lake build` as the primary test; add `npm run docs:build` when touching docs or status data.
- Update `status.md` and `status.csv` alongside new proofs so the VitePress charts remain accurate.

## Commit & Pull Request Guidelines
- Use concise, imperative commit subjects (`verify …`, `chore: …`) and append issue links such as `(#101)` when appropriate.
- Keep PRs focused: describe the verified surface area, list affected Lean files, and call out docs or status updates.
- Confirm `lake build` (and docs build when relevant) before requesting review, and note any Rust syncs performed.

## Agent Notes
- Drive Lean development with `lake env lean --server` or `lean-lsp-mcp` for goal inspection; rebuild frequently to refresh caches.
- Prefer `rg` or `ast-grep` for cross-references, and add new automation to `Tactics.lean` with concise module-level comments.
