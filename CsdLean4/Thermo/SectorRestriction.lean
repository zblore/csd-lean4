/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.KahlerInstance
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudyLebesgue

/-!
# Restricting the Liouville measure to a constraint surface (E3, the spike)

**Category:** 7-SigmaLayer / Thermo (the measure-theoretic foundation of the equilibration arc).

The equilibration arc (`specs/equilibration-arc-plan.md`) needs the base pushforward of the
Liouville measure **restricted to a constraint surface**:

  `π_*(μ_L|_S) = μ_FS^{H_R}` ?

E3 was scoped as the spike for the arc because it is the item most likely to fail. **It fails,
for a sharper reason than anticipated, and this module records the failure as theorems.**

## What is true (the saturated case)

`projectiveLaw_restrict_saturated` — when the constraint surface is **fibre-saturated**
(`S = π⁻¹ B`, i.e. it constrains only the base and imposes nothing on the torus fibre), the
pushforward is exactly the restricted Fubini–Study measure:

  `π_*(μ_L|_{π⁻¹B}) = μ_FS|_B`.

This is the honest generalisation of `kahlerFstSector_projectiveLaw`'s `c = 1`: it is a
*product-measure computation*, and it needs saturation because that is what lets
`Prod.fst ⁻¹' B = B ×ˢ univ` factor.

## ★★ What is false (the microcanonical case), and why

`projectiveLaw_restrict_sector_eq_zero` — for a **proper** spectral sector `R ⊊ H`, the
constraint surface "the state lies in `R`" pushes forward to the **zero measure**:

  `π_*(μ_L|_{π⁻¹(rays in R)}) = 0`.

The reason is not that a constant fails to compute. It is that the constraint set is
**Fubini–Study-null**: the rays of a proper subspace form a proper projective subvariety, whose
cone is the subspace itself, which is Lebesgue-null
(`Matrix.UnitaryGroup.fubiniStudyMeasure_subspaceRays`). So *conditioning* on it is undefined
and *restricting* to it is the zero measure. No choice of normalisation repairs this.

## Consequences for the arc (the decision E3 was run to force)

A microcanonical statement on `Σ` therefore **cannot** be obtained by restricting `μ_L` to an
exact spectral sector. Two repairs remain, and they differ in status:

1. **Positive-measure energy windows.** Constrain `{p | ⟨H⟩_p ∈ [E, E+Δ]}` instead of an exact
   eigenspace. This set has positive `μ_FS` measure (for a suitable window), so conditioning is
   well defined — but the conditioned measure is **not** `μ_FS` on any `ℙ(H_R)`; it is a genuinely
   different shell measure, and every statement about it must say so. This keeps the Σ-level
   content and is a **theorem route**.
2. **The sector as its own arena.** Work on `Σ_R = ℙ(H_R) × T²` with its own Liouville measure.
   Then the pushforward statement is `kahlerFstSector_projectiveLaw` at dimension `d_R` — true,
   but about a *different* `Σ`. The claim that the constrained dynamics is described by the
   sector arena is then a **posit**, not a theorem derived from the ambient `μ_L`.

⚠️ Whichever route the arc takes, this module is the reason the choice must be stated. Writing
"the microcanonical measure is `μ_FS` on the sector" without naming route 1 or 2 asserts
something these theorems refute.

## References

`specs/equilibration-arc-plan.md` (E3 and the three-way gate this resolves);
`LF4/KahlerInstance.lean` (`kMuL`, `KSigma`); `SigmaLayer/PreparationDensity.lean`
(`kahlerFstSector_projectiveLaw`, the unrestricted `c = 1`);
`Mathlib/LinearAlgebra/Projectivization/FubiniStudyLebesgue.lean` (the null theorem).
-/

@[expose] public section

open MeasureTheory Matrix.UnitaryGroup

namespace CSD.Thermo

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- The Liouville measure of a base cylinder is the Fubini–Study measure of its base — the
product computation behind every statement in this file. -/
lemma kMuL_preimage_fst (p₀ : LF4.CPN N) {B : Set (LF4.CPN N)} (_hB : MeasurableSet B) :
    LF4.kMuL p₀ (Prod.fst ⁻¹' B) = fubiniStudyMeasure p₀ B := by
  have hset : (Prod.fst ⁻¹' B : Set (LF4.KSigma N)) = B ×ˢ (Set.univ : Set LF4.KTorus) := by
    ext x
    simp
  rw [LF4.kMuL, hset, Measure.prod_prod, measure_univ, mul_one]

omit [NeZero N] in
/-- **The saturated case is a theorem.** If the constraint surface constrains only the base
(`S = π⁻¹ B`), its Liouville restriction pushes forward to the restricted Fubini–Study measure.
The honest generalisation of the unrestricted `c = 1`. -/
theorem projectiveLaw_restrict_saturated (p₀ : LF4.CPN N)
    {B : Set (LF4.CPN N)} (hB : MeasurableSet B) :
    Measure.map Prod.fst ((LF4.kMuL p₀).restrict (Prod.fst ⁻¹' B))
      = (fubiniStudyMeasure p₀).restrict B := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply measurable_fst hA,
    Measure.restrict_apply (measurable_fst hA),
    Measure.restrict_apply hA, ← Set.preimage_inter,
    kMuL_preimage_fst p₀ (hA.inter hB)]

/-- ★★ **The microcanonical restriction to a proper spectral sector is the zero measure.**

Not a normalisation problem: the constraint set is Fubini–Study-null, so there is nothing to
condition on. This refutes the naive form of the arc's E3 statement and forces the choice
recorded in the module header. -/
theorem projectiveLaw_restrict_sector_eq_zero (p₀ : LF4.CPN N)
    {R : Submodule ℂ (EuclideanSpace ℂ (Fin N))} (hR : R ≠ ⊤) :
    Measure.map Prod.fst
        ((LF4.kMuL p₀).restrict (Prod.fst ⁻¹' subspaceRays R)) = 0 := by
  rw [projectiveLaw_restrict_saturated p₀ (measurableSet_subspaceRays R),
    Measure.restrict_eq_zero]
  exact fubiniStudyMeasure_subspaceRays p₀ hR

/-- The same statement at the level of the constraint surface itself: it is `μ_L`-null, so it
carries no Liouville weight to condition on. -/
theorem kMuL_sector_eq_zero (p₀ : LF4.CPN N)
    {R : Submodule ℂ (EuclideanSpace ℂ (Fin N))} (hR : R ≠ ⊤) :
    LF4.kMuL p₀ (Prod.fst ⁻¹' subspaceRays R) = 0 := by
  rw [kMuL_preimage_fst p₀ (measurableSet_subspaceRays R)]
  exact fubiniStudyMeasure_subspaceRays p₀ hR

end CSD.Thermo
