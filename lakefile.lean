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
    `AvgRare.Basics.SetFamily,         --集合族とIdealに関する基本
    `AvgRare.Basics.Trace.Common,      --Traceに関する基本
    `AvgRare.Basics.Trace.Monotonicity, --Traceの単調性
    `AvgRare.Basics.Ideals,            --イデアルに関する基本

    -- 2) SPO（functional preorder）
    `AvgRare.SPO.FuncSetup,           --前順序に関すること
    `AvgRare.SPO.Forest,              -- 半順序に関すること

    -- 3) Forests（アルゴリズム／帰納用の補題群）
    `AvgRare.Forests.Induction,       --半順序と帰納法
    `AvgRare.Forests.DirectProduct,   --半順序のunion product

    -- 4) PaperSync（論文と同期する高レベル補題・主定理）
    `AvgRare.PaperSync.IdealsTrace,   -- ← trace×FuncSetup の結合レイヤ
    `AvgRare.PaperSync.MainStatement  -- ← 主定理
  ]
  srcDir := "."

-- tiny executable for running toy checks
lean_exe tests where
  root := `tests.SmallExamples

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"  @ "v4.23.0-rc2"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot.git" @ "v4.22.0"
