import Lake
open Lake DSL

package AvgRare {
  -- Link LeanCopilot's native lib (as in your current project)
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
  ]
}

@[default_target]
lean_lib AvgRare where
  roots := #[
    `AvgRare.Basics.Nds,
    `AvgRare.Basics.Trace,
    `AvgRare.Basics.Excess,
    `AvgRare.SPO.SetupSpo,
    `AvgRare.SPO.Spo2,
    `AvgRare.SPO.PoTranslation,
    `AvgRare.Forests.Induction,
    `AvgRare.Forests.DirectProduct,
    `AvgRare.PaperSync.Statements
  ]
  srcDir := "."

-- tiny executable for running toy checks
lean_exe tests where
  root := `tests.SmallExamples

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"  @ "v4.21.0"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot.git" @ "v4.21.0"
