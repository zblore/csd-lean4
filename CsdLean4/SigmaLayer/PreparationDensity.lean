/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.IsolationPreparation
public import CsdLean4.SigmaLayer.ProjectiveSector
public import CsdLean4.LF4.KahlerInstance
public import CsdLean4.LF4.TypicalityForcing
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Q28 items 3 and 4b: the projective preparation density ρ_ep, and overlapping preparations

**Category:** 7-SigmaLayer (BACKLOG Q28, `specs/c2-support-plan.md` items 3 and 4).

This module is deliberately the FIRST file that speaks both preparation
interfaces at once — `SigmaLayer.Preparation` (region preparations and their
conditional measures) and the projective measure bridge (the pushforward of the
Liouville measure being a multiple of the Fubini–Study measure). C2 v1.01 tore
exactly at that unspoken seam; this module is the seam, spoken.

* `Preparation.conditionalMeasure_absolutelyContinuous` — the conditional law
  of a region preparation is absolutely continuous w.r.t. the Liouville
  measure. Immediate from `conditionalMeasure_apply`.
* ★ `ProjectiveSector.projectivePreparationLaw_absolutelyContinuous` — under a
  measure bridge `π_* muL = c • μFS`, the projective preparation law is
  absolutely continuous w.r.t. `μFS`. (No `c ≠ 0` needed for THIS direction:
  `c • μFS ≪ μFS` holds for every `c`.)
* ★ `ProjectiveSector.preparationDensity` + `projectivePreparationLaw_withDensity`
  — **ρ_ep exists**: the projective preparation law IS `μFS.withDensity ρ_ep`
  with `ρ_ep` the Radon–Nikodym derivative. The object Papers C and TN2 use,
  in the corpus for the first time.
* `kahlerFstSector` + ★★ `kahler_preparation_density` — **the seam corollary at
  `c = 1`**: on the Kähler arena `Σ = ℂℙ^{N-1} × T²` with Liouville measure
  `kMuL`, the base projection is a `ProjectiveSector`, its bridge constant is
  exactly `1` (`kahlerFstSector_projectiveLaw`), and every region preparation's
  projective law has a density against THE Fubini–Study measure.
* `openBasePreparation` + ★★ `kahler_preparations_overlap` (Q28 item 4b) — the
  **finite-resolution preparation-overlap** witness: preparations localised on overlapping
  projective opens
  — each an open neighbourhood of its own ray — have conditional measures that
  are NOT mutually singular (`Preparation.conditional_not_mutuallySingular`,
  the item-4a density argument).

⚠️ Scope: the witness is the topological existence form. The quantified
"ε-balls around any two states closer than 2ε" form needs a metric on `ℙ`,
which neither Mathlib nor this corpus has (`MATHLIB-GAPS.md`, Fubini–Study
metric row).

## References

`specs/c2-support-plan.md` (items 3–4); `SigmaLayer/IsolationPreparation.lean`
(`Preparation`, `conditional_not_mutuallySingular`);
`SigmaLayer/ProjectiveSector.lean` (`projectivePreparationLaw`);
`LF4/KahlerInstance.lean` (`kMuL`); `LF4/TypicalityForcing.lean`
(`fubiniStudyMeasure_pos_of_isOpen`); `specs/BACKLOG.md` (Q28);
`specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD.SigmaLayer

variable {Sigma : Type*} [MeasurableSpace Sigma] [Nonempty Sigma] {N : ℕ}
variable {D : ConstraintDynamics Sigma}

/-! ### Item 3 — the projective preparation density ρ_ep -/

/-- The conditional law of a region preparation is absolutely continuous with
respect to the Liouville measure: a Liouville-null set stays null after
conditioning on the region. -/
theorem Preparation.conditionalMeasure_absolutelyContinuous (P : Preparation D) :
    ((P.conditionalMeasure : ProbabilityMeasure Sigma) : Measure Sigma)
      ≪ (D.muL : Measure Sigma) := by
  refine Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_
  rw [P.conditionalMeasure_apply A hA,
    measure_mono_null Set.inter_subset_left h0, ENNReal.zero_div]

instance instIsProbabilityMeasureProjectivePreparationLaw
    (Q : ProjectiveSector N D) (P : Preparation D) :
    IsProbabilityMeasure (Q.projectivePreparationLaw P) := by
  unfold ProjectiveSector.projectivePreparationLaw ProjectiveSector.projectiveLaw
  exact Measure.isProbabilityMeasure_map Q.measurable_pi.aemeasurable

/-- ★ **The projective preparation law is absolutely continuous w.r.t. the
Fubini–Study measure**, under a measure bridge `π_* muL = c • μFS`. Note no
`c ≠ 0` is needed for this direction: `c • μFS ≪ μFS` for every `c`. -/
theorem ProjectiveSector.projectivePreparationLaw_absolutelyContinuous
    (Q : ProjectiveSector N D) (P : Preparation D)
    {μFS : Measure (ProjectiveState N)} {c : ENNReal}
    (hbridge : Q.projectiveLaw (D.muL : Measure Sigma) = c • μFS) :
    Q.projectivePreparationLaw P ≪ μFS := by
  have h1 : Q.projectivePreparationLaw P
      ≪ Q.projectiveLaw (D.muL : Measure Sigma) := by
    unfold ProjectiveSector.projectivePreparationLaw ProjectiveSector.projectiveLaw
    exact Measure.AbsolutelyContinuous.map
      P.conditionalMeasure_absolutelyContinuous Q.measurable_pi
  refine h1.trans (Measure.AbsolutelyContinuous.mk fun s _ h0 => ?_)
  rw [hbridge, Measure.smul_apply, h0, smul_zero]

/-- **ρ_ep** — the projective preparation density: the Radon–Nikodym derivative
of the projective preparation law against the reference measure. -/
noncomputable def ProjectiveSector.preparationDensity
    (Q : ProjectiveSector N D) (P : Preparation D)
    (μFS : Measure (ProjectiveState N)) : ProjectiveState N → ENNReal :=
  (Q.projectivePreparationLaw P).rnDeriv μFS

/-- ★ **The projective preparation law IS a density against `μFS`** (Q28 item
3): `π_* muH = μFS.withDensity ρ_ep`. The missing rung between LF1's region
typicality and the projective weights, delivered by Radon–Nikodym. -/
theorem ProjectiveSector.projectivePreparationLaw_withDensity
    (Q : ProjectiveSector N D) (P : Preparation D)
    {μFS : Measure (ProjectiveState N)} [SigmaFinite μFS] {c : ENNReal}
    (hbridge : Q.projectiveLaw (D.muL : Measure Sigma) = c • μFS) :
    μFS.withDensity (Q.preparationDensity P μFS)
      = Q.projectivePreparationLaw P :=
  Measure.withDensity_rnDeriv_eq _ _
    (Q.projectivePreparationLaw_absolutelyContinuous P hbridge)

/-! ### The Kähler seam at `c = 1` -/

/-- The base projection of the Kähler arena `Σ = ℂℙ^{N-1} × T²`, as a
`ProjectiveSector` for any dynamics on the arena. -/
def kahlerFstSector (D : ConstraintDynamics (CSD.LF4.KSigma N)) :
    ProjectiveSector N D where
  pi := Prod.fst
  measurable_pi := measurable_fst

/-- **The Kähler bridge constant is exactly `1`**: the base pushforward of the
Liouville measure `kMuL = μFS ⊗ vol_{T²}` is the Fubini–Study measure. -/
theorem kahlerFstSector_projectiveLaw (p₀ : CSD.LF4.CPN N)
    (D : ConstraintDynamics (CSD.LF4.KSigma N))
    (hmuL : (D.muL : Measure (CSD.LF4.KSigma N)) = CSD.LF4.kMuL p₀) :
    (kahlerFstSector D).projectiveLaw (D.muL : Measure (CSD.LF4.KSigma N))
      = (1 : ENNReal) • fubiniStudyMeasure p₀ := by
  rw [one_smul]
  refine Measure.ext fun s hs => ?_
  rw [ProjectiveSector.projectiveLaw_apply _ _ hs]
  show (D.muL : Measure (CSD.LF4.KSigma N)) (Prod.fst ⁻¹' s)
    = fubiniStudyMeasure p₀ s
  rw [hmuL]
  show ((fubiniStudyMeasure p₀).prod (volume : Measure CSD.LF4.KTorus))
      (Prod.fst ⁻¹' s)
    = fubiniStudyMeasure p₀ s
  rw [← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]

/-- ★★ **ρ_ep on the Kähler arena** (the seam corollary, Q28 item 3): for any
dynamics carrying the Liouville measure and any region preparation, the
projective preparation law is absolutely continuous against THE Fubini–Study
measure and equals `μFS.withDensity ρ_ep`. The first statement in the corpus
connecting `SigmaLayer.Preparation` to the LF4 measure bridge. -/
theorem kahler_preparation_density (p₀ : CSD.LF4.CPN N) [NeZero N]
    (D : ConstraintDynamics (CSD.LF4.KSigma N))
    (hmuL : (D.muL : Measure (CSD.LF4.KSigma N)) = CSD.LF4.kMuL p₀)
    (P : Preparation D) :
    ((kahlerFstSector D).projectivePreparationLaw P ≪ fubiniStudyMeasure p₀)
      ∧ (fubiniStudyMeasure p₀).withDensity
          ((kahlerFstSector D).preparationDensity P (fubiniStudyMeasure p₀))
        = (kahlerFstSector D).projectivePreparationLaw P :=
  ⟨(kahlerFstSector D).projectivePreparationLaw_absolutelyContinuous P
      (kahlerFstSector_projectiveLaw p₀ D hmuL),
    (kahlerFstSector D).projectivePreparationLaw_withDensity P
      (kahlerFstSector_projectiveLaw p₀ D hmuL)⟩

/-- ★ **Single fibres are Liouville-null** (via Q28 item 1's atomlessness).

Single projective fibres are `kMuL`-null, so an exact fibre-supported sharp preparation
cannot be obtained by conditioning `kMuL` on a positive-volume region. Singular exact
preparations remain a **separate admissible preparation interface** — see
`RecordLayer.no_region_preparation_exact_fibre` for this stated as the disjointness of the
two classes, and `RecordLayer.sharp_preparations_mutuallySingular` for that interface's
Harrigan–Spekkens classification.

⚠️ **Commentary corrected 2026-08-25.** This read "the physical story is the region one",
which wrongly implied exact sharp measures are illegitimate. They are not; they are
singular rather than absolutely continuous, which is a different thing. -/
theorem kMuL_fibre_null (hN : 2 ≤ N) (p₀ q : CSD.LF4.CPN N) :
    CSD.LF4.kMuL p₀ (Prod.fst ⁻¹' {q}) = 0 := by
  have : NeZero N := ⟨by omega⟩
  show ((fubiniStudyMeasure p₀).prod (volume : Measure CSD.LF4.KTorus))
    (Prod.fst ⁻¹' {q}) = 0
  rw [← Set.prod_univ, Measure.prod_prod,
    fubiniStudyMeasure_singleton hN p₀ q, zero_mul]

/-! ### Item 4b — overlapping preparations on the Kähler arena -/

/-- A region preparation carved from a projective open set: the region is the
full preimage of a nonempty open `V ⊆ ℂℙ^{N-1}` under the base projection,
with positive Liouville measure by the full support of `μFS`. -/
noncomputable def openBasePreparation (p₀ : CSD.LF4.CPN N) [NeZero N]
    {V : Set (CSD.LF4.CPN N)} (hV : IsOpen V) (hne : V.Nonempty) :
    Preparation (trivialDynamics
      (⟨CSD.LF4.kMuL p₀, inferInstance⟩ : FiniteMeasure (CSD.LF4.KSigma N))) where
  region := Prod.fst ⁻¹' V
  measurable_region := measurable_fst hV.measurableSet
  nonzero_region := by
    show ((fubiniStudyMeasure p₀).prod (volume : Measure CSD.LF4.KTorus))
      (Prod.fst ⁻¹' V) ≠ 0
    rw [← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]
    exact CSD.LF4.fubiniStudyMeasure_pos_of_isOpen p₀ hV hne

/-- ★★ **The finite-resolution preparation-overlap witness** (Q28 item 4b): two
preparations, each localised on an open neighbourhood of its own ray, with overlapping
neighbourhoods, have conditional measures that are NOT mutually singular. For distinct
rays `x ≠ y` this is the statement that distinct quantum states can be knowledge about
overlapping ontic situations — **at the level of finite-resolution, region-based
preparations**.

⚠️ **Scope corrected 2026-08-25.** This was labelled "the ψ-epistemic overlap witness".
Region-preparation overlap does NOT establish Harrigan–Spekkens ψ-epistemicity of exact
pure states: that classification is about the exact sharp interface, where the corpus
proves ψ-**onticity** (`RecordLayer.sharp_preparations_mutuallySingular`). Two different
preparation classes, two different claims, both true. -/
theorem kahler_preparations_overlap (p₀ : CSD.LF4.CPN N) [NeZero N]
    {x y : CSD.LF4.CPN N} {Ux Uy : Set (CSD.LF4.CPN N)}
    (hUx : IsOpen Ux) (hUy : IsOpen Uy) (hx : x ∈ Ux) (hy : y ∈ Uy)
    (hover : (Ux ∩ Uy).Nonempty) :
    ¬ (((openBasePreparation p₀ hUx ⟨x, hx⟩).conditionalMeasure
          : ProbabilityMeasure (CSD.LF4.KSigma N)) : Measure (CSD.LF4.KSigma N)).MutuallySingular
        (((openBasePreparation p₀ hUy ⟨y, hy⟩).conditionalMeasure
          : ProbabilityMeasure (CSD.LF4.KSigma N)) : Measure (CSD.LF4.KSigma N)) := by
  apply Preparation.conditional_not_mutuallySingular
  show ((fubiniStudyMeasure p₀).prod (volume : Measure CSD.LF4.KTorus))
    (Prod.fst ⁻¹' Ux ∩ Prod.fst ⁻¹' Uy) ≠ 0
  rw [← Set.preimage_inter, ← Set.prod_univ, Measure.prod_prod,
    measure_univ, mul_one]
  exact CSD.LF4.fubiniStudyMeasure_pos_of_isOpen p₀ (hUx.inter hUy) hover

end CSD.SigmaLayer
