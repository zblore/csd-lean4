import Lake
open Lake DSL

package «csd-lean4» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «CsdLean4» where
