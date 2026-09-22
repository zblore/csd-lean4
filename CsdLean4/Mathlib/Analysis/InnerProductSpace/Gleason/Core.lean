/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.Gleason.Reduction
public import CsdLean4.Mathlib.Analysis.InnerProductSpace.Gleason.General

/-!
# Gleason's theorem, finite-dimensional: the core lemma discharged, the theorem proved

**Category:** 1-Mathlib (CSD-free; staged for upstream). The end of the staged plan of
`specs/gleason-feasibility.md` (BACKLOG #57): `Gleason/General.lean` proved the core lemma
(`frameFunction_regular_sphere`, stage 57(e)) and `Gleason/Reduction.lean` proved the theorem
from it. This file joins the two.

* `coreLemma` — the core lemma in the form `Reduction.lean` consumes: `CoreLemma` holds.
* ★★ `ProjectionPackage.gleason_representation` — **Gleason's theorem for `ℂᴺ`, `N ≥ 3`:** for
  every projection package `OP` there is a unique density matrix `ρ` with `OP.p P = Re Tr(ρ P)`
  for every orthogonal projection `P`. No hypothesis beyond `N ≥ 3`; `#print axioms` reports the
  foundational triple (pinned in `Tests/AxiomAudit/MathlibStaging.lean`).

What is and is not claimed. This is the finite-dimensional theorem (`ℂᴺ`, `N ≥ 3`) for
projection-valued measures. The infinite-dimensional theorem, dimension `2` (where the
statement fails) and the POVM generalisation (Busch's, `LF2/EffectGleason.lean`, proved
separately) are outside it. Neither of the two theorems is derived from the other: the proofs
share the Jordan–von Neumann engine (`Gleason/Polarization.lean`) and the descent
(`Gleason/Descent.lean`), nothing else.

## Source

Gleason 1957, *J. Math. Mech.* **6**, 885 (Theorem 2.3, the core lemma; Theorem 3.1, the
theorem); Cooke, Keane, Moran 1985, *Math. Proc. Cambridge Philos. Soc.* **98**, 117 (the
elementary proof of the core lemma followed in `Gleason/Sphere.lean` through
`Gleason/General.lean`).
-/

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace Gleason

/-- The core lemma, in the form `Reduction.lean` consumes. -/
theorem coreLemma : CoreLemma := fun f _ hf h0 => frameFunction_regular_sphere f hf h0

variable {N : ℕ}

/-- ★★ **Gleason's theorem for `ℂᴺ`, `N ≥ 3`.** For every projection package `OP` there is a
unique density matrix `ρ` with `OP.p P = Re Tr(ρ P)` for every orthogonal projection `P`. -/
theorem ProjectionPackage.gleason_representation (OP : ProjectionPackage N) (hN : 3 ≤ N) :
    ∃! ρ : Matrix (Fin N) (Fin N) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ P, IsStarProjection P → OP.p P = ((ρ * P).trace).re :=
  OP.gleason_representation_of_core coreLemma hN

end Gleason

end
