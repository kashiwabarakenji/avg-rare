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
    `AvgRare.Basics.SetFamily,
    `AvgRare.Basics.Trace.Common,
    `AvgRare.Basics.Trace.Monotonicity,
    --`AvgRare.Basics.Excess,          -- 使っていれば。未使用なら一旦外してOK

    -- 2) SPO（functional preorder）
    `AvgRare.SPO.FuncSetup,
    `AvgRare.SPO.Forest,              -- ここで is_rooted_forest の型だけ先に定義予定

    -- 3) Forests（アルゴリズム／帰納用の補題群）
    `AvgRare.Forests.Induction,
    `AvgRare.Forests.DirectProduct,

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
