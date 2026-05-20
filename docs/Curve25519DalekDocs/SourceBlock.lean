/-
Custom block for displaying proof bodies extracted from source files.

Usage in doc files:
  ```source SomeDeclName
  ```

Reads the declaration source, extracts only the proof body (after `:= by`),
and renders it in a styled card with the `proof-source` CSS class.
-/
import VersoManual

open Verso Genre Manual Doc Elab
open Verso.Doc
open Verso.ArgParse
open Lean

structure SourceConfig where
  name : Ident
deriving Inhabited

instance : FromArgs SourceConfig DocElabM :=
  ⟨SourceConfig.mk <$> positional' (α := Ident) `name⟩

/-- Find the first occurrence of `needle` in `haystack`. -/
private def findSubstring (haystack needle : String) : Option Nat := Id.run do
  let hLen := haystack.length
  let nLen := needle.length
  if nLen > hLen then return none
  for i in [:hLen - nLen + 1] do
    if (haystack.drop i).startsWith needle then return some i
  return none

/-- Extract the proof body from source text (everything after `:= by` or `:=`). -/
private def extractProofBody (source : String) : String :=
  if let some idx := findSubstring source ":= by" then
    "by" ++ (source.drop (idx + ":= by".length)).toString
  else if let some idx := findSubstring source ":= " then
    (source.drop (idx + ":= ".length)).toString
  else
    source

@[code_block]
meta def «source» : SourceConfig → StrLit → DocElabM Term
  | cfg, _code => do
    let declName := cfg.name.getId

    let some ranges ← findDeclarationRanges? declName
      | throwError s!"source: declaration '{declName}' not found or has no source range"

    let env ← getEnv
    let some modIdx := env.getModuleIdxFor? declName
      | throwError s!"source: could not find module for '{declName}'"
    let modName := env.header.moduleNames[modIdx.toNat]!

    let parts := modName.components.map (·.toString)
    let relPath := String.intercalate "/" parts ++ ".lean"
    -- Try CWD-relative first (lake -d docs from repo root), then ../
    let candidates : List System.FilePath := [relPath, ".." / relPath]
    let some path ← candidates.findM? (·.pathExists)
      | throwError s!"source: source file not found (tried {candidates})"

    let contents ← IO.FS.readFile path
    let lines := contents.splitOn "\n"
    let startLine := ranges.range.pos.line
    let endLine := ranges.range.endPos.line
    let selected := lines.drop startLine |>.take (endLine - startLine + 1)
    let fullSource := "\n".intercalate selected

    let proofBody := (extractProofBody fullSource).trimAscii.toString

    -- Use Block.code with a marker prefix so JS can identify and style it
    let markedCode := "-- PROOF-SOURCE\n" ++ proofBody
    ``(Block.code $(quote markedCode))
