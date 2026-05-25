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
  "https://github.com/leanprover-community/mathlib4" @ "5e932f97dd25535344f80f9dd8da3aab83df0fe6"
