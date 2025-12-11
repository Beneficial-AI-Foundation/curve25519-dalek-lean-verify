/-
  Deps: A CLI tool to find dependencies of a Lean function/definition.

  Usage: lake exe deps <module> <name>

  Example: lake exe deps Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Reduce reduce
-/
import Lean

open Lean

/-- Get direct dependencies of a constant from its value expression -/
def getDirectDeps (env : Environment) (name : Name) : Except String (Array Name) := do
  let some constInfo := env.find? name
    | throw s!"Constant '{name}' not found in environment"
  let some value := constInfo.value?
    | throw s!"Constant '{name}' has no value (it may be an axiom, opaque, or primitive)"
  return value.getUsedConstants

/-- Filter to only show "interesting" dependencies (exclude Lean builtins) -/
def isInteresting (name : Name) : Bool :=
  -- Filter out very common Lean primitives
  let prefixes := #[`Lean, `IO, `String, `Nat, `Int, `Bool, `List, `Array, `Option, `Except, `Unit, `UInt8, `UInt16, `UInt32, `UInt64, `USize, `Float, `Char]
  !prefixes.any (fun p => p.isPrefixOf name) &&
  !name.isInternal &&
  name != `sorryAx

def main (args : List String) : IO UInt32 := do
  match args with
  | [moduleName, constName] =>
    -- Parse module name
    let module := moduleName.toName

    -- Parse constant name (try as-is first, then qualified with module)
    let name := constName.toName

    -- Initialize Lean search path
    Lean.initSearchPath (← Lean.findSysroot)

    -- Import the module
    let env ← importModules #[{ module }] {}

    -- Try to find the constant (first as given, then qualified)
    let fullName := if env.find? name |>.isSome then name else module ++ name

    match getDirectDeps env fullName with
    | .ok deps =>
      let interesting := deps.filter isInteresting
      IO.println s!"Dependencies of '{fullName}':"
      IO.println s!"  Total: {deps.size}, Filtered: {interesting.size}"
      IO.println ""
      for dep in interesting.toList.mergeSort (·.toString < ·.toString) do
        IO.println s!"  {dep}"
      return 0
    | .error msg =>
      IO.eprintln s!"Error: {msg}"
      return 1
  | _ =>
    IO.eprintln "Usage: lake exe deps <module> <name>"
    IO.eprintln ""
    IO.eprintln "Arguments:"
    IO.eprintln "  <module>  The module to import (e.g., Curve25519Dalek.SomeModule)"
    IO.eprintln "  <name>    The constant name (can be unqualified if unique)"
    IO.eprintln ""
    IO.eprintln "Example:"
    IO.eprintln "  lake exe deps Mathlib.Data.Nat.Basic Nat.add_comm"
    return 1
