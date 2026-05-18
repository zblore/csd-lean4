import Lake
open Lake DSL

package «csd-lean4» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «CsdLean4» where
  -- Library consumers (`import CsdLean4`, `import CsdLean4.Basic`) get the
  -- LF1 / LF2 / LF3 development. The Tests/ subtree is excluded from the
  -- root module and lives in the separate `CsdLeanTests` target below.

/-- Test target: AxiomAudit regression suite and Examples worked
    computations. Build with `lake build CsdLeanTests`. CI exercises both
    targets (see `.github/workflows/ci.yml`).

    `AxiomAudit.lean` uses `#guard_msgs` to pin `#print axioms` output for
    every theorem in `AXIOMS.md §5`; build-fails if any theorem acquires
    or sheds an axiom. Drift detection therefore requires this target to
    be built, not just the default `CsdLean4` library. -/
lean_lib «CsdLeanTests» where
  roots := #[`CsdLean4.Tests.AxiomAudit, `CsdLean4.Tests.Examples]
