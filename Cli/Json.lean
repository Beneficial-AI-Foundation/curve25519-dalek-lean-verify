/-
  Json: JSON utilities using Lean's built-in JSON support.
-/
import Lean.Data.Json

open Lean

namespace Cli.Json

/-- Input: A single function to analyze -/
structure FunctionInput where
  lean_name : String
  deriving FromJson, ToJson, Repr

/-- Input: List of functions to analyze -/
structure AnalysisInput where
  functions : Array FunctionInput
  deriving FromJson, ToJson, Repr

/-- Output: Dependencies for a single function -/
structure DependencyOutput where
  lean_name : String
  dependencies : Array String
  specified : Bool
  verified : Bool
  deriving ToJson, Repr

/-- Output: Full analysis results -/
structure AnalysisOutput where
  results : Array DependencyOutput
  deriving Repr

instance : ToJson AnalysisOutput where
  toJson o := Json.mkObj [
    ("functions", toJson o.results)
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

end Cli.Json
