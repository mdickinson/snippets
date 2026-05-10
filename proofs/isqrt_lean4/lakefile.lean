import Lake
open Lake DSL

package «isqrt-lean4» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «IsqrtLean4» where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "03fe349eb1f7c7f75cbfca8289ab530bc78fdfdd"
