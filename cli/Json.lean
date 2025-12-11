/-
  Json: JSON utilities using Lean's built-in JSON support.
-/
import Lean.Data.Json

open Lean

namespace cli.Json

/-- Input: A single function to analyze -/
structure FunctionInput where
  name : String
  deriving FromJson, ToJson, Repr

/-- Input: List of functions to analyze -/
structure AnalysisInput where
  functions : Array FunctionInput
  deriving FromJson, ToJson, Repr

/-- Output: Dependencies for a single function -/
structure DependencyOutput where
  name : String
  dependencies : Array String
  error : Option String := none
  deriving Repr

instance : ToJson DependencyOutput where
  toJson d :=
    let base := Json.mkObj [
      ("name", Json.str d.name),
      ("dependencies", toJson d.dependencies)
    ]
    match d.error with
    | none => base
    | some err =>
      match base with
      | .obj fields => .obj (fields.insert "error" (Json.str err))
      | other => other

/-- Summary statistics -/
structure Summary where
  total : Nat
  succeeded : Nat
  failed : Nat
  deriving ToJson, Repr

/-- Output: Full analysis results -/
structure AnalysisOutput where
  results : Array DependencyOutput
  summary : Summary
  deriving Repr

instance : ToJson AnalysisOutput where
  toJson o := Json.mkObj [
    ("results", toJson o.results),
    ("summary", toJson o.summary)
  ]

/-- Parse JSON input from string -/
def parseInput (s : String) : Except String AnalysisInput :=
  match Json.parse s with
  | .error e => .error s!"JSON parse error: {e}"
  | .ok json =>
    match fromJson? json with
    | .error e => .error s!"JSON decode error: {e}"
    | .ok input => .ok input

/-- Render output to JSON string -/
def renderOutput (output : AnalysisOutput) (pretty : Bool := true) : String :=
  let json := toJson output
  if pretty then json.pretty else json.compress

end cli.Json
