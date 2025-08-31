import Lake
open Lake DSL

package AvgRare {
  -- Link LeanCopilot's native lib (as in your current project)
  --moreLinkArgs := #[
  --  "-L./.lake/packages/LeanCopilot/.lake/build/lib",
  --  "-lctranslate2"
  -- ]
}

@[default_target]
lean_lib AvgRare where
  roots := #[
    -- Basics
    `AvgRare.Basics.General,           -- General lemmas
    `AvgRare.Basics.SetFamily,         -- Basics about set families and ideals
    `AvgRare.Basics.SetTrace,      -- Basics about trace
    `AvgRare.Functional.FuncSetup,           -- About preorders
    `AvgRare.Functional.TraceFunctional,     -- Trace of functional is functional
    `AvgRare.Functional.FuncPoset,     -- FuncSetup for the second half
    `AvgRare.Reductions.Rare, -- Monotonicity of trace
    `AvgRare.Reductions.Reduction,   -- ← Composition layer of trace×FuncSetup. May rename. PaperLemma etc.
    `AvgRare.Secondary.UniqueMax,       -- Partial orders and induction
    `AvgRare.Secondary.SumProduct,   -- Union product of partial orders
    `AvgRare.Secondary.MainStatement  -- ← Main theorem
  ]
  srcDir := "."

-- tiny executable for running toy checks
lean_exe tests where
  root := `tests.SmallExamples

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"  @ "v4.23.0-rc2"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot.git" @ "v4.22.0"
