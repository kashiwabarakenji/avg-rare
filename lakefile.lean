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
    `AvgRare.Basics.General,           --一般的な補題
    `AvgRare.Basics.SetFamily,         --集合族とIdealに関する基本
    `AvgRare.Basics.SetTrace,      --Traceに関する基本
    `AvgRare.Functional.FuncSetup,           --前順序に関すること
    `AvgRare.Functional.TraceFunctional,     -- FunctionalのTraceがFunctional
    `AvgRare.Functional.FuncPoset,     -- 後半用のFuncSetup
    `AvgRare.Reductions.Rare, --Traceの単調性
    `AvgRare.Reductions.Reduction,   -- ← trace×FuncSetup の結合レイヤ。名前を変えるかも。PaperLemmaとか。
    `AvgRare.Secondary.UniqueMax,       --半順序と帰納法
    `AvgRare.Secondary.SumProduct,   --半順序のunion product
    `AvgRare.Secondary.MainStatement  -- ← 主定理
  ]
  srcDir := "."

-- tiny executable for running toy checks
lean_exe tests where
  root := `tests.SmallExamples

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"  @ "v4.23.0-rc2"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot.git" @ "v4.22.0"
