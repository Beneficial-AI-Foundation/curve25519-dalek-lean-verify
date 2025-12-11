/-
  Analysis: Core dependency analysis logic.
-/
import Lean
import Std.Data.HashSet

open Lean

namespace Cli.Analysis

/-- Get direct dependencies of a constant from its value expression -/
def getDirectDeps (env : Environment) (name : Name) : Except String (Array Name) := do
  let some constInfo := env.find? name
    | throw s!"Constant '{name}' not found in environment"
  let some value := constInfo.value?
    | throw s!"Constant '{name}' has no value (it may be an axiom, opaque, or primitive)"
  return value.getUsedConstants

/-- Filter dependencies to only include names in the given set -/
def filterToKnownFunctions (knownNames : Std.HashSet Name) (deps : Array Name) : Array Name :=
  deps.filter (fun name => knownNames.contains name)

/-- Check if a _spec theorem exists for the given function name -/
def hasSpecTheorem (env : Environment) (name : Name) : Bool :=
  let specName := name.appendAfter "_spec"
  env.find? specName |>.isSome

/-- Check if a proof directly contains sorry (sorryAx) -/
def proofContainsSorry (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some constInfo =>
    match constInfo.value? with
    | some value => value.getUsedConstants.any (· == ``sorryAx)
    | none => true  -- No value means axiom/opaque, treat as not verified
  | none => true

/-- Check if a function is verified (has _spec theorem without direct sorry) -/
def isVerified (env : Environment) (name : Name) : Bool :=
  let specName := name.appendAfter "_spec"
  match env.find? specName with
  | some _ => !proofContainsSorry env specName
  | none => false

/-- Result of analyzing a single function -/
structure AnalysisResult where
  name : Name
  allDeps : Array Name
  filteredDeps : Array Name
  specified : Bool
  verified : Bool
  error : Option String := none
  deriving Repr

/-- Analyze a single function in the given environment -/
def analyzeFunction (env : Environment) (knownNames : Std.HashSet Name) (name : Name) : AnalysisResult :=
  match getDirectDeps env name with
  | .ok deps =>
    { name := name
      allDeps := deps
      filteredDeps := filterToKnownFunctions knownNames deps
      specified := hasSpecTheorem env name
      verified := isVerified env name
      error := none }
  | .error msg =>
    { name := name
      allDeps := #[]
      filteredDeps := #[]
      specified := false
      verified := false
      error := some msg }

/-- Analyze multiple functions -/
def analyzeFunctions (env : Environment) (knownNames : Std.HashSet Name) (names : List Name) : List AnalysisResult :=
  names.map (analyzeFunction env knownNames)

/-- Try to find a constant by name, with fallback to common prefixes -/
def resolveConstantName (env : Environment) (nameStr : String) : Option Name :=
  let name := nameStr.toName
  -- Try as-is first
  if env.find? name |>.isSome then
    some name
  else
    -- Try with common prefixes
    let prefixes := #[`curve25519_dalek, `Curve25519Dalek]
    prefixes.findSome? (fun pfx =>
      let qualified := pfx ++ name
      if env.find? qualified |>.isSome then some qualified else none)

end Cli.Analysis
