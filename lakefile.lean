import Lake
open Lake DSL

package «formalization-of-mathematics» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «FormalizationOfMathematics» {
  -- add any library configuration options here
}

@[default_target]
lean_lib «Scripts» {

}
