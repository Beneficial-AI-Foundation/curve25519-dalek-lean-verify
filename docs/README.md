# Curve25519-Dalek Blueprint

Verso-blueprint documentation for the Lean 4 formalization of
[curve25519-dalek](https://github.com/dalek-cryptography/curve25519-dalek).

This is a separate Lake subproject (`docs/`) that depends on
[verso-blueprint](https://github.com/leanprover/verso-blueprint) and the
parent `Curve25519Dalek` library. It produces a static HTML site that
bridges the paper-math of the curve constructions and the formal Lean
declarations that realise them.

## Building locally

From the repository root:

```bash
# 1. Build the parent library (and its Lean cache) first, if needed
lake build

# 2. Build the doc modules (validates all (lean := "...") refs)
lake -d docs build Curve25519DalekDocs

# 3. Render HTML and serve
./scripts/build-blueprint.sh
python3 -m http.server 8080 -d _out/blueprint/html-multi
```

Open <http://localhost:8080>.

## Project structure

```
docs/
├── lakefile.toml                     # depends on versoBlueprint (v4.30.0) + parent
├── lean-toolchain                    # must match parent (v4.30.0-rc2)
├── lake-manifest.json                # pinned dependency versions
├── Main.lean                         # entry point: CSS, JS, render call
├── Curve25519DalekDocs.lean          # re-exports all chapter modules
└── Curve25519DalekDocs/
    ├── Contents.lean                 # top-level #doc, assembles chapters via {include}
    ├── SourceBlock.lean              # custom ```source DeclName``` code block
    ├── DocField.lean                 # Field arithmetic
    ├── DocScalar.lean                # Scalar arithmetic
    ├── DocCurves.lean                # Curve models (shell)
    ├── DocCurvesEdwards.lean         #   ├── Edwards form
    ├── DocCurvesMontgomery.lean      #   ├── Montgomery form
    ├── DocCurvesRistretto.lean       #   └── Ristretto form
    ├── DocBackend.lean               # Backend implementations
    ├── DocMath.lean                  # Mathematical models
    └── DocConstants.lean             # Curve constants
```

## Writing chapters (author guide)

Each `Doc*.lean` file is a Verso chapter using
`#doc (Manual) "Title" =>` blocks with embedded blueprint directives.

> **Looking for a worked example?** The
> [PQXDH Lean formalization](https://github.com/Beneficial-AI-Foundation/PostQuantumeXtendedDiffieHellman-model/tree/main/docs)
> uses the same verso-blueprint setup and has fully-written chapters
> (see `docs/PQXDHDocs/DocDH.lean`, `DocKDF.lean`, etc.). It's a useful
> reference when filling in this project's stubs.

### Block syntax cheat sheet

| Construct | Purpose |
|---|---|
| `#doc (Manual) "Title" =>` | Open a chapter |
| `%%% tag := "name" %%%` | Chapter metadata block (anchor, authors, shortTitle) |
| `# Heading` / `## Subheading` | Section / subsection within a chapter |
| `:::definition "tag" (lean := "Decl") :::` | Math definition linked to a Lean declaration |
| `:::theorem "tag" (lean := "Decl") :::` | Theorem statement linked to a Lean declaration |
| `:::lemma "tag" (lean := "Decl") :::` | Lemma (same as theorem, lower-status) |
| `:::proof :::` | Informal proof — place immediately after a theorem/lemma |
| `:::group "tag" :::` | Anchor that other blocks attach to via `(parent := "tag")` |
| `(parent := "tag")` | Argument on `:::definition`/`:::theorem`; attaches block to a group |
| `` ```source Decl `` | Embed the actual Lean source of a declaration (custom block) |
| `{include 1 Module}` | Inline a sibling chapter as a subsection (heading level 1 = `#`) |
| `[link text](url)` / `` `code` `` / `*italic*` | Standard Markdown for prose formatting |

`:::definition` vs `:::theorem`: use `:::definition` when the Lean declaration introduces an object (`def`, `abbrev`, `structure`), and `:::theorem` when it asserts a proposition (`theorem`, `lemma`). The rendered HTML labels them differently and counts theorems for status tracking.

### Linking prose to Lean declarations

Use `:::definition` and `:::theorem` blocks with a `(lean := "FullDeclName")`
attribute. Elaboration *fails* if the declaration cannot be resolved — this
is what keeps the blueprint and code in sync.

```lean
:::definition "field_invert" (lean := "curve25519_dalek.field.FieldElement51.invert_spec")
The multiplicative inverse of a field element, computed via the
Fermat-style exponentiation `x ↦ x^(p−2)`.
:::
```

To find the fully-qualified Lean name, look for the `namespace` declarations
at the top of the source file and concatenate with the declaration's local name.

### Grouping declarations

Use `:::group "tag"` to give related declarations a shared anchor on the
dependency graph:

```lean
:::group "field-arith"
Core operations on `FieldElement51`.
:::

:::definition "field_invert" (lean := "...") (parent := "field-arith") :::
:::definition "field_square" (lean := "...") (parent := "field-arith") :::
```

### Adding a `:::proof` block

When you write a proof you want to expose in the rendered HTML, wrap it
in a `:::proof` block immediately after the theorem:

```lean
:::theorem "thm_foo" (lean := "Foo.bar_eq") :::
Statement.
:::

:::proof :::
Proof sketch (informal).
:::
```

The status of the proof (`proved`/`sorry`) is detected automatically from
the Lean declaration. Rendering shows a ✓ or ⚠ badge accordingly.

### Showing the actual Lean proof text

The custom `source` code block (defined in `SourceBlock.lean`) extracts
the proof body from the .lean source and renders it inline:

````lean
```source Foo.bar_eq
```
````

This is paired with the JS in `Main.lean` that wires it into a
hover-preview "L∃∀N" badge on the proof card.

### Adding a new chapter

1. Create a new `Curve25519DalekDocs/DocXxx.lean` with the standard
   chapter scaffold (see existing stubs for a model).
2. Import it in `Curve25519DalekDocs/Contents.lean` and add a
   `{include 1 Curve25519DalekDocs.DocXxx}` line.
3. Also import it in `Curve25519DalekDocs.lean` so the library target
   covers it.

### Adding a sub-section to an existing chapter

Either:

- Add an `# Subheading` followed by content inline in the parent file, or
- Create `DocXxxSubsection.lean` and use `{include 1 Curve25519DalekDocs.DocXxxSubsection}`
  inside the parent chapter — this is how `DocCurves.lean` folds in
  Edwards/Montgomery/Ristretto.

### Common parse errors

**`unknown identifier 'X.Y'`** during `lake -d docs build`
The `(lean := "X.Y")` reference doesn't resolve. Check that:
1. The fully-qualified name matches `^namespace` declarations + the local name in the source file (e.g. `curve25519_dalek.field.FieldElement51.invert_spec`, not just `invert_spec`).
2. The chapter file `import`s the module that contains the declaration.

**`'['; expected '![', '$$', '$', '*', '[', '_', '`' or '{'`** in chapter prose
Verso parses `{...}` as a role-call macro. Common triggers:
- `𝔽_{p}` — subscript braces. Write `𝔽_p` or use a code span: `` `𝔽 with p = 2^255 - 19` ``.
- `{ref "tag"}[]` — only valid if that role is actually defined. Drop placeholder refs until you wire them up.

**`unexpected token`** near `:::`
Every `:::name args` opening needs a matching `:::` close on its own line. Self-closing form is `:::name args :::` on one line.

**Build hangs / very slow on `Building Mathlib...`**
The mathlib precompiled cache wasn't fetched. From the repo root:
```bash
lake exe cache get
lake -d docs exe cache get
```

**Editing a chapter doesn't change the rendered HTML**
You ran `lake env lean --run Main.lean ...` without first running `lake -d docs build` — Lake re-uses stale .olean files. Use `./scripts/build-blueprint.sh`, which does both in order.

## Lean version

Both the library and docs must use the same Lean toolchain. Currently
`leanprover/lean4:v4.30.0-rc2`, matching Mathlib and verso-blueprint.

## Reference

- [verso-blueprint repo](https://github.com/leanprover/verso-blueprint)
- [Verso manual](https://github.com/leanprover/verso)
- [PQXDH formalization](https://github.com/Beneficial-AI-Foundation/PostQuantumeXtendedDiffieHellman-model) — same setup, complete chapters to learn from
