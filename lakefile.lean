import Lake
open Lake DSL

package «formalization-of-mathematics» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require lean_slides from git
  "https://github.com/0art0/lean-slides"

@[default_target]
lean_lib «FormalizationOfMathematics» {
  -- add any library configuration options here
}

@[default_target]
lean_exe new_file where
  root := `Scripts.NewFile