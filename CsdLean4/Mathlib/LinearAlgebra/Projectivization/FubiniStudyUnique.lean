/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudy
public import CsdLean4.Mathlib.MeasureTheory.MapProbability
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitaryTransitive
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.Instances.Matrix

/-!
# Uniqueness of the invariant measure on complex projective space (Phases G1, G4, G5)

**Category:** 1-Mathlib (CSD-free Mathlib upstream candidate).

**Glossary:** https://glossary.constraintsurfacedynamics.com/fubini-study-measure/
Plain-language, CSD-role and formal statements of the Fubini-Study measure, with
this module as its Lean anchor. Kept symmetric by `scripts/check-glossary.sh`.
**On upstreaming:** this is a Category 1 file. Strip this Glossary block before any
Mathlib or Physlib PR; a personal project link has no place in a canonical header.

Strengthens the `ContinuousConstSMul` instance from `Unitary.lean`
(continuity in the projective argument for fixed unitary) to the
full `ContinuousSMul` (joint continuity in both arguments).

## Argument

Use the open-quotient-map structure of
`Projectivization.mk' : V₀ → ℙ ℂ V` (where `V₀ := {v : V // v ≠ 0}`):

- `id × mk' : G × V₀ → G × ℙ ℂ V` is an open quotient map (via
  `IsOpenQuotientMap.id.prodMap Projectivization.isOpenQuotientMap_mk'`).
- A function out of `G × ℙ ℂ V` is continuous iff its precomposition
  with `id × mk'` is.
- The precomposition `(U, ⟨v, hv⟩) ↦ U • mk' ⟨v, hv⟩ = mk' ⟨U.val.mulVec v, ...⟩`
  is continuous, via joint continuity of matrix-vector multiplication
  (`Continuous.matrix_mulVec`), `PiLp.continuous_toLp`, `continuous_mk'`,
  and subtype machinery.

## Main results

The file is named for its headline, `fsMeasure_unique`, but it carries the
whole chain from joint continuity to base-point independence. (The title said only
Phase G1 until 2026-08-19, which understated it by two phases.)

* **G1** `Matrix.UnitaryGroup.instContinuousSMul_projectivization` —
  `ContinuousSMul (Matrix.unitaryGroup ι ℂ) (ℙ ℂ (EuclideanSpace ℂ ι))`.
  Joint continuity, hence joint measurability, which the Fubini swap in G4 needs.
* ★★ **G4** `fsMeasure_unique` — any `U(N)`-invariant probability measure on
  `ℂℙ^(N-1)` IS `fsMeasure p₀`. The uniqueness the whole programme leans on.
* ★ **G5** `fsMeasure_basepoint_independent` / `fsMeasure_eq_default`
  — the reference point is immaterial, so `defaultFsMeasure` names *the*
  measure rather than one of a family. A corollary of G4.

## What this unlocks

Joint continuity gives joint measurability (`Continuous.measurable`),
which is the prerequisite for the Fubini swap in Phase G4
(`fsMeasure_unique`).

## Provenance

Staged as upstream Mathlib material. Intended location:
`Mathlib/LinearAlgebra/Projectivization/FubiniStudyUnique.lean`.

## Tags

projectivization, continuous group action, joint continuity
-/

@[expose] public section

open Matrix
open scoped LinearAlgebra.Projectivization

namespace Matrix.UnitaryGroup

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Joint continuity of the unitary action on `ℂℙ^(N-1)`.

The action `(U, p) ↦ U • p` is jointly continuous on
`Matrix.unitaryGroup ι ℂ × ℙ ℂ (EuclideanSpace ℂ ι)`. -/
instance instContinuousSMul_projectivization :
    ContinuousSMul (Matrix.unitaryGroup ι ℂ)
      (ℙ ℂ (EuclideanSpace ℂ ι)) where
  continuous_smul := by
    -- Open-quotient structure: id × mk' is an open quotient on G × V₀.
    rw [← (IsOpenQuotientMap.id.prodMap
            Projectivization.isOpenQuotientMap_mk').continuous_comp_iff]
    -- After the rewrite, the goal is:
    --   Continuous (fun (Uv : G × {v // v ≠ 0}) =>
    --     Uv.1 • Projectivization.mk' ℂ Uv.2)
    -- which by definitional unfolding (compHom action + mapEquiv +
    -- Projectivization.map_mk) equals
    --   Continuous (fun Uv => mk' ⟨(toEuclideanLin Uv.1.val) Uv.2.1, ...⟩).
    -- Compose continuous_mk' with subtype_mk on the matrix-vector-mul
    -- composition (which is jointly continuous in (M, v)).
    refine Projectivization.continuous_mk'.comp ?_
    refine Continuous.subtype_mk ?_ _
    -- Goal: Continuous (fun (Uv : G × {v // v ≠ 0}) =>
    --   (toEuclideanLin Uv.1.val) Uv.2.1)
    -- This is the WithLp.toLp ∘ (M *ᵥ ofLp) composition.
    show Continuous (fun (Uv : Matrix.unitaryGroup ι ℂ
                          × {v : EuclideanSpace ℂ ι // v ≠ 0}) =>
        WithLp.toLp 2 ((Uv.1.val : Matrix ι ι ℂ)
            *ᵥ (Uv.2.val.ofLp : ι → ℂ)))
    refine (PiLp.continuous_toLp _ _).comp ?_
    refine Continuous.matrix_mulVec ?_ ?_
    · -- Continuous (fun Uv => Uv.1.val) — subtype_val ∘ fst
      exact continuous_subtype_val.comp continuous_fst
    · -- Continuous (fun Uv => Uv.2.val.ofLp) — ofLp ∘ subtype_val ∘ snd
      exact (PiLp.continuous_ofLp _ _).comp
              (continuous_subtype_val.comp continuous_snd)

/-! ## Phase G2 — right-invariance of `unitaryHaarProb`

On a compact group, every Haar probability measure is both left- and
right-invariant. Mathlib gives left-invariance directly (via
`IsHaarMeasure`); we obtain right-invariance via Haar uniqueness:
the right-translate `Measure.map (· * g) unitaryHaarProb` is again a
Haar probability measure, hence equal to `unitaryHaarProb`.
-/

/-- `unitaryHaarProb` is right-invariant under group multiplication.

Proof: `Measure.map (· * g) unitaryHaarProb` is `IsHaarMeasure` (via
`isHaarMeasure_map_mul_right`, an instance) and `IsProbabilityMeasure`
(via `Measure.isProbabilityMeasure_map'`, since `(· * g)` is measurable).
`unitaryHaarProb` itself is both. By Haar uniqueness on compact groups
(`isHaarMeasure_eq_of_isProbabilityMeasure`), the two measures coincide. -/
instance instIsMulRightInvariantUnitaryHaarProb (ι : Type*) [Fintype ι] [DecidableEq ι] :
    MeasureTheory.Measure.IsMulRightInvariant
      (unitaryHaarProb : MeasureTheory.Measure (Matrix.unitaryGroup ι ℂ)) where
  map_mul_right_eq_self g := by
    have : MeasureTheory.IsProbabilityMeasure
        (MeasureTheory.Measure.map (· * g)
          (unitaryHaarProb : MeasureTheory.Measure
            (Matrix.unitaryGroup ι ℂ))) :=
      MeasureTheory.Measure.isProbabilityMeasure_map'
        (continuous_mul_const g).measurable.aemeasurable
    exact MeasureTheory.Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-! ## Phase G3 — Haar-orbit-indicator key lemma

The Haar-measure mass of the set of unitaries mapping a fixed point
`p` into a target Borel set `B` is independent of `p`. By transitivity
(Phase F), any two base points are related by some unitary `V`;
by right-invariance of Haar (Phase G2), the right-translation by `V`
preserves the measure. -/

/-- **Phase G3.** For any Borel set `B ⊆ ℙ ℂ V` and any two base points
`p₀, p`, the Haar mass of the set `{U | U • p ∈ B}` equals that of
`{U | U • p₀ ∈ B}`.

Proof: take `V_p` with `V_p • p₀ = p` (from `IsPretransitive`, which
auto-includes `[Nonempty ι]` from the section variable). Then
`{U | U • p ∈ B} = (· * V_p) ⁻¹' {U | U • p₀ ∈ B}` by `smul_smul`.
Right-invariance of Haar (Phase G2) discharges the measure equality. -/
lemma haar_orbit_indicator_eq
    {B : Set (ℙ ℂ (EuclideanSpace ℂ ι))} (hB : MeasurableSet B)
    (p₀ p : ℙ ℂ (EuclideanSpace ℂ ι)) :
    unitaryHaarProb {U : Matrix.unitaryGroup ι ℂ | U • p ∈ B}
      = unitaryHaarProb {U : Matrix.unitaryGroup ι ℂ | U • p₀ ∈ B} := by
  -- Get a unitary V_p with V_p • p₀ = p via transitivity.
  obtain ⟨V_p, hV_p⟩ :=
    MulAction.exists_smul_eq (Matrix.unitaryGroup ι ℂ) p₀ p
  -- Set equality: {U | U • p ∈ B} = (· * V_p) ⁻¹' {U | U • p₀ ∈ B}.
  have h_set_eq :
      {U : Matrix.unitaryGroup ι ℂ | U • p ∈ B}
        = (· * V_p) ⁻¹' {U | U • p₀ ∈ B} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [← hV_p, smul_smul]
  -- Measurability of the inner set (orbit map preimage of Borel).
  have h_S_meas :
      MeasurableSet {U : Matrix.unitaryGroup ι ℂ | U • p₀ ∈ B} :=
    orbit_map_measurable p₀ hB
  rw [h_set_eq, ← MeasureTheory.Measure.map_apply
        (continuous_mul_const V_p).measurable h_S_meas,
      MeasureTheory.map_mul_right_eq_self]

/-! ## Phase G4 — uniqueness of the U(N)-invariant probability measure

Headline theorem: any U(N)-invariant probability measure on
`ℂℙ^(N-1)` equals `fsMeasure p₀` for any reference point `p₀`.

Proof via Fubini chain:

  μ B = ∫⁻ U, μ B ∂λ                          -- λ is prob
      = ∫⁻ U, ∫⁻ p, B.indicator 1 (U • p) ∂μ ∂λ  -- invariance of μ
      = ∫⁻ p, ∫⁻ U, B.indicator 1 (U • p) ∂λ ∂μ  -- Fubini swap
      = ∫⁻ p, ν B ∂μ                          -- Phase G3
      = ν B                                    -- μ is prob

where λ = `unitaryHaarProb`, ν = `fsMeasure p₀`.
-/

/-- **Phase G4.** Uniqueness of the U(N)-invariant probability measure
on `ℂℙ^(N-1)`: any invariant probability measure `μ` equals
`fsMeasure p₀`. (`[Nonempty ι]` is required by the implicit
transitivity-instance synthesis through `haar_orbit_indicator_eq`,
auto-included from the section variable.) -/
theorem fsMeasure_unique
    (p₀ : ℙ ℂ (EuclideanSpace ℂ ι))
    (μ : MeasureTheory.Measure (ℙ ℂ (EuclideanSpace ℂ ι)))
    [MeasureTheory.IsProbabilityMeasure μ]
    (hμ_inv : ∀ U : Matrix.unitaryGroup ι ℂ,
       MeasureTheory.Measure.map (fun p => U • p) μ = μ) :
    μ = fsMeasure p₀ := by
  apply MeasureTheory.Measure.ext
  intro B hB
  -- Joint measurability of (U, p) ↦ U • p, derived from G1's ContinuousSMul.
  have h_smul_meas : Measurable
      (fun Up : Matrix.unitaryGroup ι ℂ
            × ℙ ℂ (EuclideanSpace ℂ ι) => Up.1 • Up.2) :=
    continuous_smul.measurable
  -- Measurability of the indicator function `B.indicator (fun _ => 1)`.
  have h_ind_meas :
      Measurable (B.indicator (fun _ : ℙ ℂ (EuclideanSpace ℂ ι) =>
                                  (1 : ENNReal))) :=
    measurable_const.indicator hB
  -- The integrand f(U, p) := B.indicator 1 (U • p) is measurable (joint).
  have h_indicator_meas : Measurable
      (fun Up : Matrix.unitaryGroup ι ℂ
            × ℙ ℂ (EuclideanSpace ℂ ι) =>
        B.indicator (fun _ => (1 : ENNReal)) (Up.1 • Up.2)) :=
    h_ind_meas.comp h_smul_meas
  -- Inner integral over μ, with U fixed: equals μ B by invariance.
  have h_inner_mu (U : Matrix.unitaryGroup ι ℂ) :
      ∫⁻ p, B.indicator (fun _ => (1 : ENNReal)) (U • p) ∂μ = μ B := by
    have hcont : Measurable (fun p : ℙ ℂ (EuclideanSpace ℂ ι) => U • p) :=
      (continuous_const_smul U).measurable
    rw [← MeasureTheory.lintegral_map h_ind_meas hcont, hμ_inv U,
        MeasureTheory.lintegral_indicator_const hB 1, one_mul]
  -- fsMeasure p₀ in terms of unitaryHaarProb (unfold the def).
  have h_fubini_def : fsMeasure p₀ B
      = unitaryHaarProb {U : Matrix.unitaryGroup ι ℂ | U • p₀ ∈ B} := by
    show (MeasureTheory.Measure.map (orbitMap p₀) unitaryHaarProb) B = _
    rw [MeasureTheory.Measure.map_apply (orbit_map_measurable p₀) hB]
    rfl
  -- Inner integral over λ, with p fixed: equals fsMeasure p₀ B by G3.
  have h_inner_haar (p : ℙ ℂ (EuclideanSpace ℂ ι)) :
      ∫⁻ U : Matrix.unitaryGroup ι ℂ,
          B.indicator (fun _ => (1 : ENNReal)) (U • p) ∂unitaryHaarProb
        = fsMeasure p₀ B := by
    have hcont : Measurable (fun U : Matrix.unitaryGroup ι ℂ => U • p) :=
      (orbit_map_continuous p).measurable
    rw [← MeasureTheory.lintegral_map h_ind_meas hcont,
        MeasureTheory.lintegral_indicator_const hB 1, one_mul,
        MeasureTheory.Measure.map_apply hcont hB]
    show unitaryHaarProb {U | U • p ∈ B} = fsMeasure p₀ B
    rw [haar_orbit_indicator_eq hB p₀ p, h_fubini_def]
  -- λ univ = 1 (probability measure).
  have h_lam_univ : unitaryHaarProb
      (Set.univ : Set (Matrix.unitaryGroup ι ℂ)) = 1 :=
    MeasureTheory.measure_univ
  -- μ univ = 1 (probability measure).
  have h_mu_univ : μ (Set.univ : Set (ℙ ℂ (EuclideanSpace ℂ ι))) = 1 :=
    MeasureTheory.measure_univ
  -- Compose the chain via Fubini.
  calc μ B
      = ∫⁻ _ : Matrix.unitaryGroup ι ℂ, μ B ∂unitaryHaarProb := by
            rw [MeasureTheory.lintegral_const, h_lam_univ, mul_one]
    _ = ∫⁻ U, ∫⁻ p, B.indicator (fun _ => (1 : ENNReal)) (U • p) ∂μ
            ∂unitaryHaarProb := by
            congr 1 with U
            exact (h_inner_mu U).symm
    _ = ∫⁻ p, ∫⁻ U, B.indicator (fun _ => (1 : ENNReal)) (U • p) ∂unitaryHaarProb ∂μ :=
            MeasureTheory.lintegral_lintegral_swap h_indicator_meas.aemeasurable
    _ = ∫⁻ _ : ℙ ℂ (EuclideanSpace ℂ ι), fsMeasure p₀ B ∂μ := by
            congr 1 with p
            exact h_inner_haar p
    _ = fsMeasure p₀ B := by
            rw [MeasureTheory.lintegral_const, h_mu_univ, mul_one]

/-! ## Phase G5 — invariant finite measures are scalar multiples of Fubini–Study

`fsMeasure_unique` pins every *probability* measure invariant under
the unitary action to `fsMeasure p₀`. The two corollaries below
extend that to arbitrary **finite** invariant measures (normalising by the
total mass) and re-express the result in the `∃ c, μ = c • μFS` shape that the
source repository's concrete measure bridges consume.

This is the invariant-measure-uniqueness fact for the `ℂℙ^{N-1}` / `U(N)`
instantiation: when the source repository instantiates its abstract measure-space data with
`P := ℙ ℂ (EuclideanSpace ℂ ι)`, `G := Matrix.unitaryGroup ι ℂ`,
and `μFS := fsMeasure p₀`, the concrete bridges
(`cp_measure_bridge` / `k_measure_bridge`) route through
`invariant_measure_uniqueness_cpn` and cite no axiom. (Historically this was
the concrete realisation of an abstract invariant-measure-uniqueness
axiom of that repository — stated over an arbitrary pretransitive `(P, G)` with no topology; that
axiom and the abstract `measure_bridge` lemma it served were **removed
2026-06-04**, since nothing downstream used the abstract statement. The
concrete fact proved here is all that was ever load-bearing.) -/

/-- **Phase G5.** Any finite measure on `ℂℙ^{N-1}` invariant under the unitary
action is a scalar multiple of the Fubini–Study measure at any reference
point. The scalar is the total mass `μ Set.univ`.

Proof: if the total mass is zero the measure is zero; otherwise normalise by
the total mass to obtain an invariant *probability* measure, pin it to
`fsMeasure p₀` via `fsMeasure_unique`, and scale back. -/
theorem invariant_finiteMeasure_eq_smul_fubiniStudy
    (p₀ : ℙ ℂ (EuclideanSpace ℂ ι))
    (μ : MeasureTheory.Measure (ℙ ℂ (EuclideanSpace ℂ ι)))
    [MeasureTheory.IsFiniteMeasure μ]
    (hμ_inv : ∀ U : Matrix.unitaryGroup ι ℂ,
        MeasureTheory.MeasurePreserving (fun p => U • p) μ μ) :
    ∃ c : ENNReal, μ = c • fsMeasure p₀ := by
  rcases eq_or_ne (μ Set.univ) 0 with h0 | h0
  · exact ⟨0, by rw [zero_smul]; exact MeasureTheory.Measure.measure_univ_eq_zero.mp h0⟩
  · have htop : μ Set.univ ≠ ⊤ := MeasureTheory.measure_ne_top μ Set.univ
    -- The mass-normalised measure is a probability measure.
    have hprob : MeasureTheory.IsProbabilityMeasure ((μ Set.univ)⁻¹ • μ) := by
      refine ⟨?_⟩
      rw [MeasureTheory.Measure.smul_apply, smul_eq_mul]
      exact ENNReal.inv_mul_cancel h0 htop
    -- Scaling preserves invariance, so the normalised measure is invariant.
    have hinv : ∀ U : Matrix.unitaryGroup ι ℂ,
        MeasureTheory.Measure.map (fun p => U • p) ((μ Set.univ)⁻¹ • μ)
          = (μ Set.univ)⁻¹ • μ := by
      intro U
      rw [MeasureTheory.Measure.map_smul' _ _ (hμ_inv U).measurable, (hμ_inv U).map_eq]
    -- Uniqueness pins the normalised measure to Fubini–Study.
    have heq : ((μ Set.univ)⁻¹ • μ) = fsMeasure p₀ :=
      fsMeasure_unique p₀ ((μ Set.univ)⁻¹ • μ) hinv
    refine ⟨μ Set.univ, ?_⟩
    rw [← heq, smul_smul, ENNReal.mul_inv_cancel h0 htop, one_smul]

/-- **Invariant finite measures are multiples of `μ_FS`** (the source repository's phase G5,
the concrete realisation of its former invariant-measure-uniqueness axiom).
For the `ℂℙ^{N-1}` / `U(N)` instantiation, any unitary-invariant probability
measure `μFS` and any unitary-invariant finite measure `μ` satisfy
`∃ c, μ = c • μFS`. This matches that axiom's conclusion shape (with
the reference point `p₀` made explicit), and is proved — no axiom — from
`fsMeasure_unique` plus `invariant_finiteMeasure_eq_smul_fubiniStudy`.

`μFS` is pinned to `fsMeasure p₀` by uniqueness; `μ` is a scalar
multiple of the same; composing gives `μ = c • μFS`. -/
theorem invariant_measure_uniqueness_cpn
    (p₀ : ℙ ℂ (EuclideanSpace ℂ ι))
    (μFS : MeasureTheory.Measure (ℙ ℂ (EuclideanSpace ℂ ι)))
    [MeasureTheory.IsProbabilityMeasure μFS]
    (hμFS_inv : ∀ U : Matrix.unitaryGroup ι ℂ,
        MeasureTheory.MeasurePreserving (fun p => U • p) μFS μFS)
    (μ : MeasureTheory.Measure (ℙ ℂ (EuclideanSpace ℂ ι)))
    [MeasureTheory.IsFiniteMeasure μ]
    (hμ_inv : ∀ U : Matrix.unitaryGroup ι ℂ,
        MeasureTheory.MeasurePreserving (fun p => U • p) μ μ) :
    ∃ c : ENNReal, μ = c • μFS := by
  have hFS : μFS = fsMeasure p₀ :=
    fsMeasure_unique p₀ μFS (fun U => (hμFS_inv U).map_eq)
  obtain ⟨c, hc⟩ := invariant_finiteMeasure_eq_smul_fubiniStudy p₀ μ hμ_inv
  exact ⟨c, by rw [hc, hFS]⟩

/-! ## Phase G5 — the base point is not a degree of freedom

`fsMeasure` is defined as a pushforward along the orbit map at a chosen `p₀`,
so on its face it is a family of measures. It is not: the choice is immaterial, and G4
says why in one step. Any `U(N)`-invariant probability measure equals
`fsMeasure p₀`, and `fsMeasure p₁` is such a measure, so the two agree.

Recorded because it was a real defect rather than a missing convenience: the
`FubiniStudy.lean` module docstring advertised `defaultPoint` and
`defaultFsMeasure` as the "canonical choice" while neither existed, and nothing
anywhere proved the base point could be dropped. Both are now supplied (2026-08-19).

⚠️ Deliberately **not** `@[simp]`. Rewriting every `fsMeasure p₀` downstream
to the default form would touch several hundred sites for no proof-level gain, and simp
lemmas that rename a widely-used term are how a build becomes unpredictable. Consumers
that want the canonical form should rewrite with it explicitly. -/

/-- ★ **The Fubini–Study measure does not depend on its base point.** Immediate from
Phase G4: `fsMeasure p₀` is a `U(N)`-invariant probability measure
(`fsMeasure_smul_invariant`), and G4 says every such measure is
`fsMeasure p₁`. -/
theorem fsMeasure_basepoint_independent
    (p₀ p₁ : ℙ ℂ (EuclideanSpace ℂ ι)) :
    fsMeasure p₀ = fsMeasure p₁ :=
  fsMeasure_unique p₁ (fsMeasure p₀)
    (fun U => fsMeasure_smul_invariant U p₀)

/-- The Fubini–Study measure at any base point IS the canonical one. This is what makes
`defaultFsMeasure` an honest name rather than one choice among many. -/
theorem fsMeasure_eq_default (p₀ : ℙ ℂ (EuclideanSpace ℂ ι)) :
    fsMeasure p₀ = defaultFsMeasure ι :=
  fsMeasure_basepoint_independent p₀ (defaultPoint ι)

open MeasureTheory

/-! ### Atomlessness (Q28 item 1)

Every singleton is `μ_FS`-null for `2 ≤ N`, by pigeonhole: transitivity and
invariance make all singletons equal in measure, the projective space is
infinite, and a probability measure cannot give arbitrarily many disjoint
points a common positive mass. No stabiliser subgroup is consulted — the
"Haar-of-subgroup" route the source repository once assumed necessary is bypassed
entirely. -/

/-- All singletons carry the same Fubini–Study mass: move one point onto the
other by transitivity, and use invariance. -/
lemma fsMeasure_singleton_eq
    (p₀ q q' : ℙ ℂ (EuclideanSpace ℂ ι)) :
    fsMeasure p₀ {q} = fsMeasure p₀ {q'} := by
  obtain ⟨U, hU⟩ := MulAction.exists_smul_eq (Matrix.unitaryGroup ι ℂ) q q'
  have hpre : (fun p : ℙ ℂ (EuclideanSpace ℂ ι) => U • p) ⁻¹' {q'} = {q} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      exact smul_left_cancel U (h.trans hU.symm)
    · rintro rfl
      exact hU
  calc fsMeasure p₀ {q}
      = fsMeasure p₀
          ((fun p : ℙ ℂ (EuclideanSpace ℂ ι) => U • p) ⁻¹' {q'}) := by
        rw [hpre]
    _ = (Measure.map (fun p : ℙ ℂ (EuclideanSpace ℂ ι) => U • p)
          (fsMeasure p₀)) {q'} := by
        rw [Measure.map_apply (continuous_const_smul U).measurable
          isClosed_singleton.measurableSet]
    _ = fsMeasure p₀ {q'} := by
        rw [fsMeasure_smul_invariant U p₀]

omit [Nonempty ι] in
/-- For `2 ≤ card ι` the projective space is infinite: for two distinct indices `i0 ≠ i1` the
rays `[e_{i0} + t • e_{i1}]`, `t : ℕ`, are pairwise distinct. -/
theorem projectivization_infinite (hN : 2 ≤ Fintype.card ι) :
    Infinite (ℙ ℂ (EuclideanSpace ℂ ι)) := by
  obtain ⟨i0, i1, hne⟩ : ∃ i0 i1 : ι, i0 ≠ i1 := Fintype.exists_pair_of_one_lt_card (by omega)
  set v : ℕ → EuclideanSpace ℂ ι := fun t =>
    EuclideanSpace.single i0 1 + (t : ℂ) • EuclideanSpace.single i1 1 with hv_def
  have hv0 : ∀ t, v t i0 = 1 := by
    intro t
    simp [hv_def, PiLp.add_apply, PiLp.smul_apply, hne]
  have hv1 : ∀ t, v t i1 = (t : ℂ) := by
    intro t
    simp [hv_def, PiLp.add_apply, PiLp.smul_apply, Ne.symm hne]
  have hvne : ∀ t, v t ≠ 0 := by
    intro t h0
    have := congrArg (fun z : EuclideanSpace ℂ ι => z i0) h0
    rw [hv0 t] at this
    simp at this
  refine Infinite.of_injective
    (fun t => Projectivization.mk ℂ (v t) (hvne t)) ?_
  intro s t hst
  rw [Projectivization.mk_eq_mk_iff] at hst
  obtain ⟨c, hc⟩ := hst
  have h0 := congrArg (fun z : EuclideanSpace ℂ ι => z i0) hc
  have h1 := congrArg (fun z : EuclideanSpace ℂ ι => z i1) hc
  simp only [Units.smul_def, PiLp.smul_apply, smul_eq_mul, hv0, hv1,
    mul_one] at h0 h1
  rw [h0] at h1
  rw [one_mul] at h1
  exact_mod_cast h1.symm

/-- ★ **The Fubini–Study measure is atomless** (Q28 item 1): for `2 ≤ N` every
singleton is null. Pigeonhole, with no stabiliser Haar measure anywhere: all
singletons share one mass `a` by transitivity + invariance; were `a ≠ 0`, a
finite set of more than `1/a` distinct points — available since the space is
infinite — would carry measure exceeding `1`. -/
theorem fsMeasure_singleton (hN : 2 ≤ Fintype.card ι)
    (p₀ q : ℙ ℂ (EuclideanSpace ℂ ι)) :
    fsMeasure p₀ {q} = 0 := by
  by_contra ha
  have := projectivization_infinite hN
  set a := fsMeasure p₀ {q} with ha_def
  have ha_le : a ≤ 1 :=
    (measure_mono (Set.subset_univ _)).trans_eq measure_univ
  have ha_ne_top : a ≠ ⊤ := (ha_le.trans_lt ENNReal.one_lt_top).ne
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt
    (ENNReal.div_lt_top ENNReal.one_ne_top ha).ne
  obtain ⟨S, hScard⟩ :=
    Infinite.exists_subset_card_eq (ℙ ℂ (EuclideanSpace ℂ ι)) n
  have hSmeas : fsMeasure p₀ ↑S = n * a := by
    calc fsMeasure p₀ ↑S
        = ∑ x ∈ S, fsMeasure p₀ {x} := sum_measure_singleton.symm
      _ = ∑ _x ∈ S, a :=
          Finset.sum_congr rfl fun x _ =>
            fsMeasure_singleton_eq p₀ x q
      _ = n * a := by rw [Finset.sum_const, hScard, nsmul_eq_mul]
  have hcontr : (1 : ENNReal) < n * a :=
    (ENNReal.div_lt_iff (Or.inl ha) (Or.inl ha_ne_top)).mp hn
  have hle : fsMeasure p₀ ↑S ≤ 1 := prob_le_one
  rw [hSmeas] at hle
  exact absurd (hcontr.trans_le hle) (lt_irrefl _)

end Matrix.UnitaryGroup
