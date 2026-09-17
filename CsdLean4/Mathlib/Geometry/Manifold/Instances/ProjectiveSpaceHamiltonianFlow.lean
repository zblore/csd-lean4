/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.HamiltonianFlowVolume
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudyVolume
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudySymplectic

/-!
# Every Hamiltonian flow on `ℂℙⁿ` preserves the Fubini–Study volume

**TERM-SCOPE(Hamiltonian)** **TERM-SCOPE(Liouville)** **TERM-SCOPE(Kahler)** — this module uses
the *restricted* senses of "Hamiltonian", "Liouville" and "Kahler"; `specs/TERMS.md` records what
is backed and what is not.

**Category:** 1-Mathlib (CSD-free). Q29(d′) of `specs/generator-layer-scoping.md` on `ℂℙⁿ`.

`HamiltonianFlowVolume.lean` proves Liouville's theorem on a compact symplectic manifold: the
Hamiltonian flow of a smooth energy preserves the measure of every power of the symplectic form.
`ℂℙⁿ` with the Fubini–Study form is symplectic (`fsForm_isSymplectic`) and its volume `fsVolume n`
is the measure of the `n`-th power (`fsTopForm n = wedgePow fsForm n`), so:

* ★★★ `Projectivization.fsVolume_map_hamiltonianFlow` — **the Hamiltonian flow of every smooth
  `H : ℂℙⁿ → ℝ` preserves the Fubini–Study volume**, at every time;
* `Projectivization.fsVolumeNormalized_map_hamiltonianFlow` — and the normalised volume, which
  is `fsMeasure p₀` (`fsVolumeNormalized_eq_fsMeasure`).

Before this file the only Hamiltonian flows on `ℂℙⁿ` known to preserve the volume were the
unitary ones (`fsVolume_map_smul`, `fsVolume_map_torusUnitary_smul`), by group invariance; this
is the statement for an arbitrary smooth energy, from the manifold-level flow theory.
-/

@[expose] public section

open MeasureTheory DifferentialForm
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace Projectivization

variable {n : ℕ}

/-- ★★★ **Liouville on `ℂℙⁿ`.** The Hamiltonian flow of every smooth `H` preserves the
Fubini–Study volume. -/
theorem fsVolume_map_hamiltonianFlow {H : ℙ ℂ (Ambient n) → ℝ}
    (hH : ContMDiff (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ ℝ) ∞ H) (t : ℝ) :
    Measure.map ((fsForm_isSymplectic n).hamiltonianFlow hH t) (fsVolume n) = fsVolume n :=
  (fsForm_isSymplectic n).map_hamiltonianFlow_topFormMeasure_wedgePow volume hH n (stdBasis n)
    (affineChartCover n) t

/-- The normalised Fubini–Study volume is invariant under every Hamiltonian flow. -/
theorem fsVolumeNormalized_map_hamiltonianFlow {H : ℙ ℂ (Ambient n) → ℝ}
    (hH : ContMDiff (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ ℝ) ∞ H) (t : ℝ) :
    Measure.map ((fsForm_isSymplectic n).hamiltonianFlow hH t) (fsVolumeNormalized n)
      = fsVolumeNormalized n := by
  rw [fsVolumeNormalized, Measure.map_smul' _ _
    ((fsForm_isSymplectic n).continuous_hamiltonianFlow hH t).measurable,
    fsVolume_map_hamiltonianFlow]

end Projectivization
