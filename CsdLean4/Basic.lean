import CsdLean4.LF1.MainTheorem
import CsdLean4.LF2.BornWrapper
import CsdLean4.LF2.Interface
import CsdLean4.LF3.Interface

/-!
# CsdLean4.Basic

Conventional entry point for the package, following the Lean 4 idiom of `Pkg.Basic`.
External consumers who write `import CsdLean4.Basic` get the full LF1 + LF2 + LF3
development.

The canonical top-level import is `CsdLean4` (the root file), which lists every module
explicitly. This file re-exports the deepest leaves of each layer:
- `LF1.MainTheorem` transitively pulls in the LF1 chain (Setup → … → MainTheorem).
- `LF2.BornWrapper` is the self-contained Born-weight layer (not reachable through
  the LF1↔LF2 interface chain, so it must be imported separately).
- `LF2.Interface` transitively pulls in the rest of the LF2 chain (Setup →
  MeasureBridge → Weights → Interface).
- `LF3.Interface` transitively pulls in the full LF3 chain (Setup, Hamiltonian,
  BranchSeparation, Projectors/*, Singlet/*, ContextMap) and re-exposes the four
  capstone theorems including the LF1↔LF2↔LF3 empirical chain.

## Invariant

Any new top-level module added to `CsdLean4.lean` (the canonical explicit list)
must also be reachable from this file, either directly or transitively through
one of the imports above. When a new sibling layer (e.g. `LF4.Interface`) lands,
add it here as well. Failure to do so silently strands the layer for external
consumers who `import CsdLean4.Basic` but not the canonical root.
-/
