import CsdLean4.LF1.MainTheorem

/-!
# CsdLean4.Basic

Conventional entry point for the package, following the Lean 4 idiom of `Pkg.Basic`.
External consumers who write `import CsdLean4.Basic` get the full LF1 development.

The canonical top-level import is `CsdLean4` (the root file), which lists every module
explicitly. This file simply re-exports `MainTheorem`, which transitively pulls in the
entire module chain (Setup → Preparation → Outcomes → Trials → Indicators →
Expectation → Convergence → MainTheorem).
-/
