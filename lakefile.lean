import Lake
open Lake DSL

package «csd-lean4» where
  name := "csd-lean4"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «CsdLean4» where
