# Extracting Rust to Lean with Aeneas

A practical guide for using **Charon** and **Aeneas** to extract Rust code into Lean 4 for formal verification.

## Overview

The extraction pipeline has two stages:

1. **Charon** compiles your Rust crate into LLBC (Low-Level Borrow Calculus), an intermediate representation
2. **Aeneas** translates LLBC into Lean 4 code

Not all Rust code can be extracted. The workflow is iterative: start small, fix errors, expand scope.

## Quick Start

```bash
# Install aeneas locally
npm run aeneas -- install

# Run extraction
npm run aeneas -- extract

# Check what commands would run (without executing)
npm run aeneas -- extract --dry-run
```

All configuration lives in `aeneas-config.yml` at the project root.

## Configuration

### Minimal config

```yaml
aeneas:
  commit: "1620d2ad..."          # pin a specific aeneas version
  repo: "https://github.com/AeneasVerif/aeneas.git"

crate:
  dir: "my-crate"                # path to the Rust crate
  name: "my_crate"               # crate name (underscores, not hyphens)

charon:
  preset: aeneas
  package: "my-crate"
  cargo_args: []
  start_from: []
  exclude: []
  opaque: []

aeneas_args:
  backend: lean
  options:
    - loops-to-rec                # convert loops to recursive functions
    - split-files                 # generate separate Types.lean / Funs.lean
  dest: "MyLeanOutput"

tweaks:
  files: []
  substitutions: []
```

### Key fields

| Field | Purpose |
|---|---|
| `start_from` | Which modules/functions to extract (whitelist) |
| `exclude` | Items to skip entirely (removed from output) |
| `opaque` | Items kept as opaque declarations (type exists, no body) |
| `cargo_args` | Extra flags passed to `cargo` via Charon |
| `tweaks` | Find/replace patches applied to generated Lean files |

## Iterative Workflow

### Step 1: Start with a single module

Begin with the simplest, most self-contained module in your crate:

```yaml
charon:
  start_from:
    - "my_crate::field"
```

Run extraction and see what happens. If it succeeds, open the generated Lean files and check that they look reasonable.

### Step 2: Fix errors by excluding problematic items

Extraction will often fail on certain items. Common causes:

- **Trait impls Aeneas doesn't support** (iterators, Debug, Hash, etc.)
- **Dynamic array indexing** (`array[i]` where `i` is computed)
- **Complex generics** or higher-kinded trait bounds
- **Closures and function pointers** in certain positions

When you get an error, identify the offending item from the error message and add it to `exclude`:

```yaml
charon:
  exclude:
    # Debug/Hash/Clone impls are never needed for verification
    - "my_crate::field::{impl core::fmt::Debug for _}"
    - "my_crate::field::{impl core::hash::Hash for _}"

    # Iterator-based impls can't be extracted
    - "my_crate::scalar::{impl core::iter::traits::accum::Sum<_> for _}"
```

The `_` wildcard in exclude patterns matches any type. This is useful for blanket exclusions like "all Debug impls in this module".

### Step 3: Expand scope gradually

Once one module works, add more to `start_from`:

```yaml
charon:
  start_from:
    - "my_crate::field"
    - "my_crate::scalar"
    - "my_crate::point"
```

Each new module may introduce new errors. Fix them before adding more.

### Step 4: Use `opaque` for dependencies you don't need to verify

If your code depends on functions whose internals you don't care about, mark them opaque. Lean will see the type signature but not the implementation:

```yaml
charon:
  opaque:
    - "my_crate::utils::some_helper"
```

## When to Modify the Rust Source

Sometimes exclusion isn't enough. If a function you **need** uses a pattern Aeneas can't handle, you may need to rewrite it.

### Use `#[cfg(not(verify))]` to swap implementations

Add a `verify` cfg flag to `.cargo/config.toml`:

```toml
[build]
rustflags = ["--cfg", "verify"]
```

Then provide alternative implementations:

```rust
#[cfg(not(verify))]
fn mul(self, scalar: &Scalar) -> MontgomeryPoint {
    // Original: uses iterators
    let bits = scalar.bits_le().rev().skip(1);
    // ...
}

#[cfg(verify)]
fn mul(self, scalar: &Scalar) -> MontgomeryPoint {
    // Rewritten: uses a while loop (Aeneas-friendly)
    let scalar_bytes = scalar.as_bytes();
    let mut i: isize = 254;
    while i >= 0 {
        let byte_idx = (i >> 3) as usize;
        let bit_idx = (i & 7) as usize;
        let cur_bit = ((scalar_bytes[byte_idx] >> bit_idx) & 1u8) == 1u8;
        // ... same logic, no iterators ...
        i -= 1;
    }
}
```

### Common patterns that need rewriting

| Pattern | Problem | Fix |
|---|---|---|
| `for x in iter` with `.map()`, `.filter()`, etc. | Iterator trait machinery | Rewrite as `while` loop with index |
| `array[computed_index] = val` | Dynamic array indexing | Restructure or exclude |
| `impl Iterator for MyType` | Trait object / associated type | Exclude or provide simpler alternative |
| Closures passed as arguments | Higher-order functions | Inline the closure at call site |

### Rule of thumb

Only modify source when:
1. The function is needed for your verification goals
2. There's no way to exclude it without losing something important
3. The rewritten version is provably equivalent

Always keep both implementations (gated with `cfg`) so the crate still compiles normally.

## Post-Extraction Tweaks

Aeneas output sometimes has minor issues that prevent Lean from compiling. Use the `tweaks` section to patch these automatically.

### Literal find/replace

```yaml
tweaks:
  files:
    - "Funs.lean"
    - "Types.lean"
  substitutions:
    # Shorten mangled names
    - find: "AddAssigncurve25519_dalekbackendserialu64fieldFieldElement51..."
      replace: "FieldElement51.AddAssign"

    # Fix syntax errors
    - find: "  let i41 ← lift (U64.shr i36 20#i32)"
      replace: "  let i41 ← (i36 >>> 20#i32)"
```

### Regex find/replace

```yaml
    - find_regex: "some_pattern_(\\d+)"
      replace: "fixed_$1"
```

### Common tweaks

| Issue | Tweak |
|---|---|
| **Mangled trait impl names** that are too long for Lean identifiers | Shorten with find/replace |
| **`&` in identifier names** (from reference types) | Replace `&` with `_` |
| **Missing `Result` wrapper** on constant definitions | Add `Result (...)` to the type and `ok` to the body |
| **`maxRecDepth` overflow** on deeply recursive functions | Insert `set_option maxRecDepth 4096 in` before the definition |
| **Linter warnings** | Add `set_option linter.style.whitespace false` etc. |
| **Block comments `/-`** should be doc comments | Replace `/-\n` with `/--\n` |
| **Name shadowing** (variable name matches a namespace) | Adjust the generated call syntax |

Tweaks are applied **in order** -- this matters when one tweak changes text that a later tweak needs to match. For example, inserting `set_option maxRecDepth` before a function must happen before converting `/-` to `/--`, because the find pattern matches the original `/-` form.

The tool warns if any find/replace pattern is not found in the file. This helps catch tweaks that become stale after an Aeneas update.

## Troubleshooting

### Charon errors

**"failed to compile crate"** -- Your Rust code doesn't compile with the cfg flags. Check `cargo build --features ...` works standalone.

**"unsupported: ..."** -- Charon can't translate a specific Rust construct. Add the item to `exclude`.

### Aeneas errors

**"Internal error"** -- Usually means a pattern in the LLBC that Aeneas doesn't handle. Check the `.logs/aeneas.log` for details. The error typically names the function -- add it to `exclude`.

**"Could not find ..."** -- A dependency wasn't included. Either add the module to `start_from` or mark the dependency `opaque`.

### Lean errors after extraction

**"unknown identifier"** -- A mangled name is too long or contains illegal characters. Add a tweak to rename it.

**"type mismatch"** -- Often a constant that should return `Result T` but was generated as `T`. Add a tweak to fix the return type.

**"deep recursion"** -- Add `set_option maxRecDepth N in` before the definition via a tweak.

### General tips

- Check `.logs/charon.log` and `.logs/aeneas.log` for detailed error output
- Run `npm run aeneas -- extract --dry-run` to see the exact commands
- Pin your aeneas version in the config -- extraction output can change between versions
- After updating aeneas, re-run extraction and check if tweaks are still needed (the tool will warn about stale tweaks)
- Keep `extraction_notes.md` (or similar) to document why each exclusion and tweak exists
