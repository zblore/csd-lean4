import CsdLean4

/-!
# CsdLean4.Basic

**Category:** Special (convenience re-export of the full package).

Conventional entry point for the package, following the Lean 4 idiom of `Pkg.Basic`.
External consumers who write `import CsdLean4.Basic` get the **entire** development:
LF1 → LF2 → LF3 → LF4 → LF5 → Empirical → the Cat-1 `Mathlib/` staging tree.

This file imports the canonical root module `CsdLean4` (the explicit module list),
so the documented invariant — every top-level module is reachable from `Basic` —
holds structurally and cannot drift: any module added to `CsdLean4.lean` is
automatically re-exported here. (Before 2026-06-11 this file hand-listed the
LF1–LF3 leaf modules and the invariant had silently broken when LF4/LF5/Empirical
landed; importing the root retires that failure mode. The root does not import
`Basic`, so this is acyclic.)

Consumers who want only a sub-chain should import the relevant leaf directly
(e.g. `CsdLean4.LF1.MainTheorem`, `CsdLean4.LF3.Interface`).
-/
