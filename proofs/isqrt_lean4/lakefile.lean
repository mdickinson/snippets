import Lake
open Lake DSL

package «isqrt-lean4» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «IsqrtLean4» where
  srcDir := "."

@[default_target]
lean_lib «IsqrtLean4Tests» where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.29.1"
