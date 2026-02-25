# Design: Aeneas Item Manifest (`manifest.json`)

**Status:** Draft
**Date:** 2025-02-25

## Summary

Add a `manifest.json` output to Aeneas that emits structured metadata for every
item it extracts. This provides machine-readable access to Rust-origin metadata
(visibility, source location, Rust name, item kind, etc.) keyed by the exact
Lean definition name that Aeneas generates — eliminating the need to scrape this
information from docstrings at Lean elaboration time.

## Motivation

### Current state

The verification project needs Rust-origin metadata (source file, line range,
Rust name, visibility) for each extracted Lean definition. Today this is obtained
by a fragile pipeline:

1. Aeneas embeds metadata in Lean docstrings: `/-- [rust_name]: Source: 'path', lines X:Y-A:B -/`
2. At Lean elaboration time, `Utils/Lib/Docstring.lean` parses these strings
   with `splitOn` to recover the Rust name, source path, and line range
3. `Utils/Lib/ListFuns.lean` applies heuristics: suffix-matching for extraction
   artifacts (`_body`, `_loop`), path-matching for relevance (`isRelevantSource`),
   and a 360-entry manually-maintained hidden functions list (`Config.lean`)

This approach has several problems:

- **Fragile parsing.** Docstring format changes break `Docstring.lean`.
- **Incomplete data.** Visibility (`pub`), inline hints, `is_local`, source text,
  and `item_source` (trait impl vs inherent impl vs free function) are not exposed.
- **Manual maintenance.** The hidden functions list in `Config.lean` (360+ entries)
  and the extraction artifact suffix list must be maintained by hand.
- **Redundant work.** Aeneas already has all this data in memory — it computes the
  Lean name, resolves the Rust name, and reads `item_meta` from the LLBC. The
  docstring is the only channel, and Utils re-parses it at elaboration time.

### What this enables

A JSON manifest eliminates the scraping layer and provides new capabilities:

| Capability | Before | After |
|---|---|---|
| Rust name, source, lines | Parse docstring | JSON lookup |
| Visibility (`pub`) | Not available | `is_public` field |
| Item kind (trait impl, free fn, etc.) | Suffix heuristics | `item_source` field |
| `is_local` (from this crate?) | Path heuristic | Direct field |
| Inline hint | Not available | `inline` field |
| Source text | Not available | `source_text` field (opt-in via `-manifest-include-source`) |
| Is extraction artifact | Suffix matching | `is_extraction_artifact` flag |
| Docstring.lean (78 lines) | Required | **Eliminable** |
| Config.lean hidden list (360 entries) | Manual | Derivable from `item_source` + `is_public` |

## Design

### Output file

Aeneas writes `manifest.json` to the same destination directory as the generated
Lean files (specified by `-dest`). For this project:

```
Curve25519Dalek/
├── Funs.lean            (existing)
├── Types.lean           (existing)
├── FunsExternal.lean    (existing)
└── manifest.json        (new)
```

### Schema

```jsonc
{
  // Aeneas and Charon version for reproducibility
  "aeneas_version": "0.1.0",
  "charon_version": "0.1.160",
  "crate_name": "curve25519_dalek",

  // All items extracted, keyed by generated Lean name.
  // Includes both local (crate) and non-local (external/stdlib) items.
  "items": {

    // --- A regular function (inherent impl method) ---
    "curve25519_dalek.backend.serial.u64.field.FieldElement51.reduce": {
      "kind": "function",
      "rust_name": "curve25519_dalek::backend::serial::u64::field::{impl FieldElement51}::reduce",
      "source": {
        "file": "curve25519-dalek/src/backend/serial/u64/field.rs",
        "start_line": 292,
        "start_col": 4,
        "end_line": 325,
        "end_col": 5
      },
      "is_public": false,
      "is_local": true,

      // What kind of item source this is (from Pure.item_source / Types.item_source)
      "item_source": "inherent_impl",
      // Possible values:
      //   "top_level"      - free function / top-level type / global constant
      //   "inherent_impl"  - method in an inherent impl block
      //   "trait_decl"     - default method in a trait declaration
      //   "trait_impl"     - method in a trait impl block
      //   "closure"        - closure body
      //   "vtable"         - vtable entry

      // For trait_impl items: which trait is being implemented (null otherwise)
      "impl_trait": null,

      "inline": "Always",                   // "Always" | "Never" | "Hint" | null
      // Rust-side doc comment (/// or /** */) from the source code.
      // This is NOT the Aeneas-generated Lean docstring — it is the original
      // Rust documentation the author wrote. null if the item has no Rust doc comment.
      // Aeneas has access via item_meta.attr_info.attributes (AttrDocComment variants).
      "doc_comment": "Given 64-bit input limbs, reduce to enforce the bound 2^(51 + epsilon).",
      "is_extraction_artifact": false,

      // Parent Lean name: null for items that map 1:1 to a Rust item.
      // Non-null for extraction artifacts — points to the Lean def they were split from.
      "parent": null
    },

    // --- A global constant ---
    "curve25519_dalek.backend.serial.u64.constants.EDWARDS_D": {
      "kind": "global",
      "rust_name": "curve25519_dalek::backend::serial::u64::constants::EDWARDS_D",
      "source": {
        "file": "curve25519-dalek/src/backend/serial/u64/constants.rs",
        "start_line": 45,
        "start_col": 0,
        "end_line": 51,
        "end_col": 1
      },
      "is_public": false,
      "is_local": true,
      "item_source": "top_level",
      "impl_trait": null,
      "inline": null,
      "doc_comment": null,
      "is_extraction_artifact": false,
      "parent": null
    },

    // --- Global body: extraction artifact pointing to its parent constant ---
    "curve25519_dalek.backend.serial.u64.constants.EDWARDS_D_body": {
      "kind": "function",
      "rust_name": "curve25519_dalek::backend::serial::u64::constants::EDWARDS_D",
      "source": { /* same as EDWARDS_D */ },
      "is_public": false,
      "is_local": true,
      "item_source": "top_level",
      "impl_trait": null,
      "inline": null,
      "doc_comment": null,
      "is_extraction_artifact": true,
      // Points to the global constant this body initialises
      "parent": "curve25519_dalek.backend.serial.u64.constants.EDWARDS_D"
    },

    // --- Loop helper: extraction artifact pointing to enclosing function ---
    "curve25519_dalek.scalar.Scalar.batch_invert_loop0": {
      "kind": "function",
      "rust_name": "curve25519_dalek::scalar::{impl Scalar}::batch_invert",
      "source": { /* same span as batch_invert */ },
      "is_public": true,
      "is_local": true,
      "item_source": "inherent_impl",
      "impl_trait": null,
      "inline": null,
      "doc_comment": null,
      "is_extraction_artifact": true,
      // Points to the function this loop was extracted from
      "parent": "curve25519_dalek.scalar.Scalar.batch_invert"
    },

    // --- Inner constant: artifact nested inside a function ---
    "curve25519_dalek.backend.serial.u64.field.FieldElement51.reduce.LOW_51_BIT_MASK": {
      "kind": "global",
      "rust_name": "curve25519_dalek::backend::serial::u64::field::{impl FieldElement51}::reduce::LOW_51_BIT_MASK",
      "source": { /* span of the inner constant */ },
      "is_public": false,
      "is_local": true,
      "item_source": "top_level",
      "impl_trait": null,
      "inline": null,
      "doc_comment": null,
      "is_extraction_artifact": true,
      // Points to the enclosing function
      "parent": "curve25519_dalek.backend.serial.u64.field.FieldElement51.reduce"
    },

    // --- Non-local (external) item: reduced metadata ---
    "core.ops.arith.Add": {
      "kind": "trait_decl",
      "rust_name": "core::ops::arith::Add",
      "source": {
        "file": "/rustc/library/core/src/ops/arith.rs",
        "start_line": 65,
        "start_col": 0,
        "end_line": 76,
        "end_col": 1
      },
      "is_public": true,
      "is_local": false,         // external item — not from the target crate
      "item_source": "top_level",
      "impl_trait": null,
      "inline": null,
      "doc_comment": null,
      "is_extraction_artifact": false,
      "parent": null
    }

    // ... one entry per extracted Lean definition
  }
}
```

### Field reference

| Field | Type | Source in Aeneas | Notes |
|---|---|---|---|
| `kind` | `"function" \| "type" \| "global" \| "trait_decl" \| "trait_impl"` | Which declaration map the item comes from | Matches the five `*_decls` categories in the LLBC |
| `rust_name` | `string` | `item_meta.name` formatted via Charon's name printer | The `::` delimited Rust path |
| `source.file` | `string` | `item_meta.span.data.file.name` | File path as Charon records it |
| `source.start_line` | `int` | `item_meta.span.data.beg_loc.line` | 1-indexed |
| `source.start_col` | `int` | `item_meta.span.data.beg_loc.col` | 0-indexed |
| `source.end_line` | `int` | `item_meta.span.data.end_loc.line` | |
| `source.end_col` | `int` | `item_meta.span.data.end_loc.col` | |
| `is_public` | `bool` | `item_meta.attr_info.public` | Charon's boolean; no `pub(crate)` distinction |
| `is_local` | `bool` | `item_meta.is_local` | `true` = defined in the extracted crate |
| `item_source` | `string` | `Pure.fun_decl.src` / `Types.item_source` | See enum mapping above |
| `impl_trait` | `string \| null` | `TraitImplItem` variant's `trait_decl_ref` | Only for trait impl items |
| `inline` | `string \| null` | `item_meta.attr_info.inline` | |
| `doc_comment` | `string \| null` | `item_meta.attr_info.attributes` filtered to `AttrDocComment` | The **Rust-side** doc comment (`///` or `/** */`), not the Aeneas-generated Lean docstring. Concatenated if multiple. `null` for items without Rust doc comments. |
| `is_extraction_artifact` | `bool` | Derived: `true` for loop helpers, `_body` globals, inner constants | Aeneas knows which items it synthesises |
| `parent` | `string \| null` | See [Parent tracking](#parent-tracking) | Lean name of the parent item. `null` for items that map 1:1 to a Rust item. |
| `source_text` | `string` (optional key) | `item_meta.source_text` | Full Rust source. **Only emitted with `-manifest-include-source`**. Key is absent by default. |

### Key: Lean names as manifest keys

The critical design choice is **keying items by the generated Lean name**, not the
LLBC ID or Rust name. This is what makes the manifest directly usable by
downstream tools without name-matching:

```python
# Instead of this (current approach — fragile):
for lean_def in lean_environment:
    docstring = get_docstring(lean_def)
    rust_name = parse_between_brackets(docstring)  # brittle
    source = parse_source_pattern(docstring)        # brittle

# The manifest enables this (robust):
manifest = json.load(open("manifest.json"))
metadata = manifest["items"][lean_def_name]  # direct lookup
```

Aeneas already computes this mapping internally in `extraction_ctx.names_maps`
(`id_to_name : string IdMap.t`), so emitting it is essentially free.

### Extraction artifact classification

Aeneas currently generates several kinds of "artifacts" that are not direct
translations of a single Rust item:

| Artifact | Current detection | Manifest approach |
|---|---|---|
| `foo_body` (global constant body) | Suffix `_body` | `is_extraction_artifact: true` |
| `foo_loop`, `foo_loop0`..`foo_loop3` | Suffix `_loop*` | `is_extraction_artifact: true` |
| `foo.closure` | Checked against `item_source` | `item_source: "closure"` |
| `foo.bar` (inner constant) | Not detected | `is_extraction_artifact: true` (nested scope) |

Aeneas is the authority on what it synthesises. By emitting
`is_extraction_artifact` directly, the downstream `Config.lean` suffix list
becomes unnecessary.

### Parent tracking

A single Rust item can produce multiple Lean definitions. The `parent` field
links each extraction artifact back to the Lean definition it was split from,
so downstream tools can treat them as parts of one logical unit.

Aeneas already tracks these relationships internally:

| Artifact type | How Aeneas knows the parent | `parent` value |
|---|---|---|
| **Loop helper** (`foo_loop0`) | `fun_decl.loop_id` is `Some id` — the function shares `def_id` with its parent. Aeneas creates the loop decl via `FromLlbc (FunId (FRegular def_id), Some loop_id)`. | Lean name of the enclosing function |
| **Global body** (`FOO_body`) | `fun_decl.is_global_decl_body = true`. The parent global's `body_id : FunDeclId.id` points back. | Lean name of the global constant |
| **Inner constant** (`foo.BAR`) | `item_meta.name` path is strictly longer than the enclosing function's path — it is a nested scope. | Lean name of the enclosing function (derived from shared name prefix) |
| **Closure** (`foo.closure`) | `item_source = ClosureItem _`. The enclosing function is encoded in `item_meta.name` (the closure's name path includes the parent). | Lean name of the enclosing function |

**What `parent` replaces.** The current `ListFuns.lean` has a
[docstring-inheritance hack](Utils/Lib/ListFuns.lean#L117-L123) where a function
with no docstring tries to inherit from its `_body` variant. With `parent`, a
consumer simply follows the link:

```python
item = manifest["items"][lean_name]
if item["is_extraction_artifact"]:
    parent = manifest["items"][item["parent"]]
    # parent has the authoritative metadata for this Rust item
```

## Implementation

### Where in Aeneas

The manifest is generated in `Translate.ml`, in the `extract_translated_crate`
function. The insertion point is after name registration is complete (all
`extract_*_register_names` calls have run, so `names_maps` is fully populated)
and before or alongside the Lean file extraction.

```
extract_translated_crate
  │
  ├─ Destructure trans_crate (line ~1300)
  ├─ Initialize names_maps   (line ~1313)
  ├─ Build extraction_ctx    (line ~1351)
  ├─ Register all names      (lines ~1407-1543)
  │
  ├─ ★ emit_manifest ctx dest_dir   ← INSERT HERE
  │
  ├─ Extract Types.lean      (line ~1700+)
  ├─ Extract Funs.lean
  └─ Extract FunsExternal.lean
```

### Implementation sketch (OCaml)

```ocaml
(* In Translate.ml *)

let emit_manifest (ctx : extraction_ctx) (dest_dir : string)
    ~(include_source : bool) : unit =
  let open Yojson.Basic in
  let items = ref [] in

  (* Helper: get Lean name for an id *)
  let lean_name id = ctx_get None id ctx in

  (* Helper: span to JSON *)
  let span_to_json (span : Meta.span) : json =
    let d = span.data in
    let file = match d.file.name with
      | Virtual s | Local s | NotReal s -> s
    in
    `Assoc [
      "file", `String file;
      "start_line", `Int d.beg_loc.line;
      "start_col", `Int d.beg_loc.col;
      "end_line", `Int d.end_loc.line;
      "end_col", `Int d.end_loc.col;
    ]
  in

  (* Helper: item_meta to common fields *)
  let meta_fields (im : Types.item_meta) : (string * json) list =
    let doc = im.attr_info.attributes |> List.filter_map (function
      | Meta.AttrDocComment s -> Some s | _ -> None)
      |> String.concat "\n" in
    let inline = match im.attr_info.inline with
      | None -> `Null | Some Always -> `String "Always"
      | Some Never -> `String "Never" | Some Hint -> `String "Hint"
    in
    let base = [
      "source", span_to_json im.span;
      "is_public", `Bool im.attr_info.public;
      "is_local", `Bool im.is_local;
      "inline", inline;
      "doc_comment", (if doc = "" then `Null else `String doc);
    ] in
    if include_source then
      base @ (match im.source_text with
        | Some s -> ["source_text", `String s]
        | None -> [])
    else
      base
  in

  (* Helper: resolve parent Lean name for an artifact *)
  let parent_of_fun (decl : Pure.fun_decl) : json =
    if decl.is_global_decl_body then
      (* Body of a global constant — find the global whose body_id matches *)
      let parent_global = GlobalDeclId.Map.find_opt ... ctx.trans_globals in
      match parent_global with
      | Some g -> `String (lean_name (GlobalId g.def_id))
      | None -> `Null
    else match decl.loop_id with
      | Some _ ->
        (* Loop helper — parent is the non-loop function with same def_id *)
        `String (lean_name (FunId (FromLlbc (FunId (FRegular decl.def_id), None))))
      | None ->
        (* Check if this is a nested inner item by name prefix *)
        `Null  (* or derive from item_meta.name hierarchy *)
  in

  (* Emit function declarations (both local and non-local) *)
  FunDeclId.Map.iter (fun _id (decl : Pure.fun_decl) ->
    let name = lean_name (FunId id) in
    let item_source_str = ... (* map Pure.item_source to string *) in
    let is_artifact = decl.is_global_decl_body || decl.loop_id <> None in
    let entry = `Assoc ([
      "kind", `String "function";
      "rust_name", `String (name_to_string decl.item_meta.name);
      "item_source", `String item_source_str;
      "is_extraction_artifact", `Bool is_artifact;
      "parent", parent_of_fun decl;
    ] @ meta_fields decl.item_meta) in
    items := (name, entry) :: !items
  ) ctx.trans_funs;

  (* Similarly for trans_types, trans_globals, trans_trait_decls, trans_trait_impls.
     For globals: parent is null (globals are not artifacts).
     For global _body functions: parent points to the global (handled above).
     For trait_decls/trait_impls: parent is null. *)
  (* ... *)

  let manifest = `Assoc [
    "aeneas_version", `String version;
    "charon_version", `String charon_version;
    "crate_name", `String ctx.crate.name;
    "items", `Assoc (List.rev !items);
  ] in
  let path = Filename.concat dest_dir "manifest.json" in
  Yojson.Basic.to_file ~std:true path manifest
```

### CLI flags

```
aeneas -backend lean -split-files -dest Curve25519Dalek/ curve25519_dalek.llbc
       ^^^ manifest.json is emitted by default (without source_text)

aeneas -no-manifest -backend lean ...
       ^^^ suppress manifest output entirely

aeneas -manifest-include-source -backend lean ...
       ^^^ include source_text field for local items (~5x larger manifest)
```

| Flag | Default | Effect |
|---|---|---|
| `-no-manifest` | off | Suppress manifest output entirely |
| `-manifest-include-source` | off | Include `source_text` field for local items |

The manifest is emitted by default because it is cheap to produce and has no
effect on the generated Lean code. The `source_text` field is opt-in because it
significantly increases manifest size (the Rust source for all local items) and
most consumers do not need it — source location (`source.file` + line range) is
sufficient for linking back to the Rust code.

### extract-lean.sh changes

No changes required — the manifest appears alongside the Lean files automatically.
Optionally, the script could log it:

```bash
echo "- Manifest: $OUTPUT_DIR/manifest.json"
```

## Downstream impact

### Utils simplification

With the manifest available, the Utils pipeline changes:

**Eliminable code:**
- `Utils/Lib/Docstring.lean` — all 78 lines (docstring parsing becomes a JSON read)
- `Config.lean` extraction artifact suffix list — replaced by `is_extraction_artifact`
- `Config.lean` hidden functions list (360+ entries) — replaceable by filtering on
  `item_source == "trait_impl"` combined with trait name patterns, though the
  hidden list may still be useful for fine-grained control

**Simplified code:**
- `ListFuns.lean` `isRelevantSource` heuristic → replaced by `is_local`
- `ListFuns.lean` `gatherRawData` docstring inheritance hack → replaced by `parent` field
- `ListFuns.lean` `isExtractionArtifactName` suffix check → read from manifest
- `ListFuns.lean` `isHiddenFunction` manual name check → derivable from `item_source` + `impl_trait`

**Unchanged code:**
- Dependency analysis (`getDirectDeps`, `getTransitiveDeps`) — requires Lean env
- Verification status (`isVerified`, `isFullyVerified`) — requires Lean env
- Spec theorem extraction (`getSpecParts`) — requires reading Lean proof files
- `StatusCsv` sync pipeline — consumes the above

### New `loadManifest` function

```lean
-- Utils/Lib/Manifest.lean (new, ~30 lines)
structure ManifestItem where
  kind : String
  rust_name : String
  source_file : String
  start_line : Nat
  end_line : Nat
  is_public : Bool
  is_local : Bool
  item_source : String
  impl_trait : Option String := none
  is_extraction_artifact : Bool
  parent : Option String := none    -- Lean name of parent item (for artifacts)
  doc_comment : Option String := none
  deriving FromJson

structure Manifest where
  crate_name : String
  items : Std.HashMap String ManifestItem  -- keyed by Lean name
  deriving FromJson

def loadManifest (path : System.FilePath := "Curve25519Dalek/manifest.json") : IO Manifest := do
  let content ← IO.FS.readFile path
  match Json.parse content >>= fromJson? with
  | .ok m => return m
  | .error e => throw (IO.userError s!"Failed to parse manifest: {e}")
```

### Revised `buildFunctionRecords` pipeline

```lean
def buildFunctionRecords (env : Environment) (manifest : Manifest) : IO (Array FunctionRecord) := do
  let allDefs := getModuleDefinitions env funsModule
  let mut records := #[]
  for name in allDefs do
    let nameStr := name.toString
    -- Direct manifest lookup instead of docstring parsing
    match manifest.items.find? nameStr with
    | some item =>
      -- For artifacts, inherit metadata from parent if needed
      let effectiveItem := match item.parent with
        | some parentName => manifest.items.find? parentName |>.getD item
        | none => item
      records := records.push {
        leanName := name
        rustName := effectiveItem.rust_name
        source := effectiveItem.source_file
        lineRange := (effectiveItem.start_line, effectiveItem.end_line)
        isRelevant := item.is_local                        -- was: heuristic
        isExtractionArtifact := item.is_extraction_artifact -- was: suffix match
        isPublic := item.is_public                          -- NEW
        parent := item.parent                               -- NEW
        isSpecified := hasSpecTheorem env name
        isVerified := isVerified env name
        -- ... etc
      }
    | none => pure ()  -- item not in manifest (e.g. Aeneas builtins)
  return records
```

### functions.json compatibility

The existing `functions.json` format (consumed by the website and `status.csv`
sync) can be extended with new fields from the manifest:

```jsonc
{
  "lean_name": "curve25519_dalek.backend.serial.u64.field.FieldElement51.reduce",
  "rust_name": "...",
  "source": "...",
  "lines": "L292-L325",
  "is_public": false,          // NEW: from manifest
  "item_source": "inherent_impl",  // NEW: from manifest
  // ... existing fields unchanged
}
```

This is a backwards-compatible addition. No existing consumers break.

## Migration

### Phase 1: Implement and emit (Aeneas PR)

- Add `emit_manifest` to `Translate.ml`
- Emit `manifest.json` alongside Lean files
- No changes to existing Lean output (docstrings remain)

### Phase 2: Consume in Utils (this repo)

- Add `Utils/Lib/Manifest.lean` with `loadManifest`
- Update `ListFuns.lean` to read manifest instead of parsing docstrings
- Add `is_public` to `FunctionRecord` and `FunctionOutput`
- Update `SyncStatus.lean` to include new fields in `functions.json`

### Phase 3: Simplify (this repo, follow-up)

- Remove `Utils/Lib/Docstring.lean`
- Trim `Config.lean` hidden list (replace with manifest-based filtering)
- Remove extraction artifact suffix list from `Config.lean`

Phases 2 and 3 can be done gradually. The manifest is additive — it doesn't
change existing behavior, so there is no breaking transition.

## Alternatives considered

### A: Parse the .llbc directly

A Python script could extract `item_meta.attr_info.public` from
`curve25519_dalek.llbc`. However:

- Name matching between .llbc and Lean is only ~73% accurate without
  reimplementing Aeneas's naming logic (trait impl names are mangled differently)
- Separate tool to maintain outside both Charon and Aeneas
- Duplicates work Aeneas already does

### B: Docstring annotations only (current approach, extended)

Already working for visibility. But each new field requires another docstring
parser, and the docstring becomes increasingly overloaded. Not suitable for
machine-readable data (source text, structured item_source, etc.).

### C: Embed as Lean attributes instead of JSON

Aeneas could emit Lean attributes like `@[rust_public]` or
`@[rust_meta {is_public := true, ...}]`. This would make the data accessible
at elaboration time without a separate file. However:

- More complex Aeneas changes (defining custom attributes in the Lean library)
- Harder to consume from non-Lean tools (Python scripts, CI, website)
- JSON is the simpler and more universal format

## Resolved questions

1. **Should `source_text` be included by default?**
   No. Opt-in via `-manifest-include-source`. See [CLI flags](#cli-flags).

2. **Should the manifest include non-local (external) items?**
   Yes. All items Aeneas extracts are included, with `is_local: false` for
   external/stdlib items. This lets downstream tools enumerate the full API
   surface (e.g., which external traits are used) without a separate data source.
   External items may have reduced metadata (no `source_text`, source paths
   pointing to `/rustc/...`), but the structural fields (`kind`, `is_public`,
   `item_source`, `parent`) are always present.

3. **Should extraction artifacts reference their parent?**
   Yes. The `parent` field (Lean name of the parent item, or `null`) is always
   present. See [Parent tracking](#parent-tracking).
