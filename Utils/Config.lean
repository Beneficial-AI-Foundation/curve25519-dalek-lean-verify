/-
  Config: Project-specific configuration for Utils tools.

  This file centralizes all project-specific values. To adapt these tools
  for a different Aeneas-generated project, modify the values here.
-/
import Lean

open Lean

namespace Utils.Config

/-- The main module to import (contains Funs and Specs) -/
def mainModule : Name := `Curve25519Dalek

/-- The module containing function definitions -/
def funsModule : Name := `Curve25519Dalek.Funs

/-- The crate name used for relevance filtering (matches source paths) -/
def crateName : String := "curve25519-dalek"

end Utils.Config
