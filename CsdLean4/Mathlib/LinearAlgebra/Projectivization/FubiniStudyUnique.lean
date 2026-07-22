/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudy
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitaryTransitive
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.Instances.Matrix

/-!
# Joint continuity of the unitary action on complex projective space (Phase G1)

**Category:** 1-Mathlib (CSD-free Mathlib upstream candidate).

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

## Main result

`Matrix.UnitaryGroup.instContinuousSMul_projectivization` —
`ContinuousSMul (Matrix.unitaryGroup (Fin N) ℂ) (ℙ ℂ (EuclideanSpace ℂ (Fin N)))`.

## What this unlocks

Joint continuity gives joint measurability (`Continuous.measurable`),
which is the prerequisite for the Fubini swap in Phase G4
(`fubiniStudyMeasure_unique`).

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

variable {N : ℕ} [NeZero N]

/-- Joint continuity of the unitary action on `ℂℙ^(N-1)`.

The action `(U, p) ↦ U • p` is jointly continuous on
`Matrix.unitaryGroup (Fin N) ℂ × ℙ ℂ (EuclideanSpace ℂ (Fin N))`. -/
instance instContinuousSMul_projectivization :
    ContinuousSMul (Matrix.unitaryGroup (Fin N) ℂ)
      (ℙ ℂ (EuclideanSpace ℂ (Fin N))) where
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
    show Continuous (fun (Uv : Matrix.unitaryGroup (Fin N) ℂ
                          × {v : EuclideanSpace ℂ (Fin N) // v ≠ 0}) =>
        WithLp.toLp 2 ((Uv.1.val : Matrix (Fin N) (Fin N) ℂ)
            *ᵥ (Uv.2.val.ofLp : Fin N → ℂ)))
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
(via `Measure.isProbabilityMeasure_map`, since `(· * g)` is measurable).
`unitaryHaarProb` itself is both. By Haar uniqueness on compact groups
(`isHaarMeasure_eq_of_isProbabilityMeasure`), the two measures coincide. -/
instance instIsMulRightInvariantUnitaryHaarProb (N : ℕ) :
    MeasureTheory.Measure.IsMulRightInvariant
      (unitaryHaarProb : MeasureTheory.Measure (Matrix.unitaryGroup (Fin N) ℂ)) where
  map_mul_right_eq_self g := by
    haveI : MeasureTheory.IsProbabilityMeasure
        (MeasureTheory.Measure.map (· * g)
          (unitaryHaarProb : MeasureTheory.Measure
            (Matrix.unitaryGroup (Fin N) ℂ))) :=
      MeasureTheory.Measure.isProbabilityMeasure_map
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
auto-includes `[NeZero N]` from the section variable). Then
`{U | U • p ∈ B} = (· * V_p) ⁻¹' {U | U • p₀ ∈ B}` by `smul_smul`.
Right-invariance of Haar (Phase G2) discharges the measure equality. -/
lemma haar_orbit_indicator_eq
    {B : Set (ℙ ℂ (EuclideanSpace ℂ (Fin N)))} (hB : MeasurableSet B)
    (p₀ p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    unitaryHaarProb {U : Matrix.unitaryGroup (Fin N) ℂ | U • p ∈ B}
      = unitaryHaarProb {U : Matrix.unitaryGroup (Fin N) ℂ | U • p₀ ∈ B} := by
  -- Get a unitary V_p with V_p • p₀ = p via transitivity.
  obtain ⟨V_p, hV_p⟩ :=
    MulAction.exists_smul_eq (Matrix.unitaryGroup (Fin N) ℂ) p₀ p
  -- Set equality: {U | U • p ∈ B} = (· * V_p) ⁻¹' {U | U • p₀ ∈ B}.
  have h_set_eq :
      {U : Matrix.unitaryGroup (Fin N) ℂ | U • p ∈ B}
        = (· * V_p) ⁻¹' {U | U • p₀ ∈ B} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [← hV_p, smul_smul]
  -- Measurability of the inner set (orbit map preimage of Borel).
  have h_S_meas :
      MeasurableSet {U : Matrix.unitaryGroup (Fin N) ℂ | U • p₀ ∈ B} :=
    orbit_map_measurable p₀ hB
  rw [h_set_eq, ← MeasureTheory.Measure.map_apply
        (continuous_mul_const V_p).measurable h_S_meas,
      MeasureTheory.map_mul_right_eq_self]

/-! ## Phase G4 — uniqueness of the SU(N)-invariant probability measure

Headline theorem: any SU(N)-invariant probability measure on
`ℂℙ^(N-1)` equals `fubiniStudyMeasure p₀` for any reference point `p₀`.

Proof via Fubini chain:

  μ B = ∫⁻ U, μ B ∂λ                          -- λ is prob
      = ∫⁻ U, ∫⁻ p, B.indicator 1 (U • p) ∂μ ∂λ  -- invariance of μ
      = ∫⁻ p, ∫⁻ U, B.indicator 1 (U • p) ∂λ ∂μ  -- Fubini swap
      = ∫⁻ p, ν B ∂μ                          -- Phase G3
      = ν B                                    -- μ is prob

where λ = `unitaryHaarProb`, ν = `fubiniStudyMeasure p₀`.
-/

/-- **Phase G4.** Uniqueness of the SU(N)-invariant probability measure
on `ℂℙ^(N-1)`: any invariant probability measure `μ` equals
`fubiniStudyMeasure p₀`. (`[NeZero N]` is required by the implicit
transitivity-instance synthesis through `haar_orbit_indicator_eq`,
auto-included from the section variable.) -/
theorem fubiniStudyMeasure_unique
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N)))
    (μ : MeasureTheory.Measure (ℙ ℂ (EuclideanSpace ℂ (Fin N))))
    [MeasureTheory.IsProbabilityMeasure μ]
    (hμ_inv : ∀ U : Matrix.unitaryGroup (Fin N) ℂ,
       MeasureTheory.Measure.map (fun p => U • p) μ = μ) :
    μ = fubiniStudyMeasure p₀ := by
  apply MeasureTheory.Measure.ext
  intro B hB
  -- Joint measurability of (U, p) ↦ U • p, derived from G1's ContinuousSMul.
  have h_smul_meas : Measurable
      (fun Up : Matrix.unitaryGroup (Fin N) ℂ
            × ℙ ℂ (EuclideanSpace ℂ (Fin N)) => Up.1 • Up.2) :=
    continuous_smul.measurable
  -- Measurability of the indicator function `B.indicator (fun _ => 1)`.
  have h_ind_meas :
      Measurable (B.indicator (fun _ : ℙ ℂ (EuclideanSpace ℂ (Fin N)) =>
                                  (1 : ENNReal))) :=
    measurable_const.indicator hB
  -- The integrand f(U, p) := B.indicator 1 (U • p) is measurable (joint).
  have h_indicator_meas : Measurable
      (fun Up : Matrix.unitaryGroup (Fin N) ℂ
            × ℙ ℂ (EuclideanSpace ℂ (Fin N)) =>
        B.indicator (fun _ => (1 : ENNReal)) (Up.1 • Up.2)) :=
    h_ind_meas.comp h_smul_meas
  -- Inner integral over μ, with U fixed: equals μ B by invariance.
  have h_inner_mu (U : Matrix.unitaryGroup (Fin N) ℂ) :
      ∫⁻ p, B.indicator (fun _ => (1 : ENNReal)) (U • p) ∂μ = μ B := by
    have hcont : Measurable (fun p : ℙ ℂ (EuclideanSpace ℂ (Fin N)) => U • p) :=
      (continuous_const_smul U).measurable
    rw [← MeasureTheory.lintegral_map h_ind_meas hcont, hμ_inv U,
        MeasureTheory.lintegral_indicator_const hB 1, one_mul]
  -- fubiniStudyMeasure p₀ in terms of unitaryHaarProb (unfold the def).
  have h_fubini_def : fubiniStudyMeasure p₀ B
      = unitaryHaarProb {U : Matrix.unitaryGroup (Fin N) ℂ | U • p₀ ∈ B} := by
    show (MeasureTheory.Measure.map (orbitMap p₀) unitaryHaarProb) B = _
    rw [MeasureTheory.Measure.map_apply (orbit_map_measurable p₀) hB]
    rfl
  -- Inner integral over λ, with p fixed: equals fubiniStudyMeasure p₀ B by G3.
  have h_inner_haar (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
      ∫⁻ U : Matrix.unitaryGroup (Fin N) ℂ,
          B.indicator (fun _ => (1 : ENNReal)) (U • p) ∂unitaryHaarProb
        = fubiniStudyMeasure p₀ B := by
    have hcont : Measurable (fun U : Matrix.unitaryGroup (Fin N) ℂ => U • p) :=
      (orbit_map_continuous p).measurable
    rw [← MeasureTheory.lintegral_map h_ind_meas hcont,
        MeasureTheory.lintegral_indicator_const hB 1, one_mul,
        MeasureTheory.Measure.map_apply hcont hB]
    show unitaryHaarProb {U | U • p ∈ B} = fubiniStudyMeasure p₀ B
    rw [haar_orbit_indicator_eq hB p₀ p, h_fubini_def]
  -- λ univ = 1 (probability measure).
  have h_lam_univ : unitaryHaarProb
      (Set.univ : Set (Matrix.unitaryGroup (Fin N) ℂ)) = 1 :=
    MeasureTheory.measure_univ
  -- μ univ = 1 (probability measure).
  have h_mu_univ : μ (Set.univ : Set (ℙ ℂ (EuclideanSpace ℂ (Fin N)))) = 1 :=
    MeasureTheory.measure_univ
  -- Compose the chain via Fubini.
  calc μ B
      = ∫⁻ _ : Matrix.unitaryGroup (Fin N) ℂ, μ B ∂unitaryHaarProb := by
            rw [MeasureTheory.lintegral_const, h_lam_univ, mul_one]
    _ = ∫⁻ U, ∫⁻ p, B.indicator (fun _ => (1 : ENNReal)) (U • p) ∂μ
            ∂unitaryHaarProb := by
            congr 1 with U
            exact (h_inner_mu U).symm
    _ = ∫⁻ p, ∫⁻ U, B.indicator (fun _ => (1 : ENNReal)) (U • p) ∂unitaryHaarProb ∂μ :=
            MeasureTheory.lintegral_lintegral_swap h_indicator_meas.aemeasurable
    _ = ∫⁻ _ : ℙ ℂ (EuclideanSpace ℂ (Fin N)), fubiniStudyMeasure p₀ B ∂μ := by
            congr 1 with p
            exact h_inner_haar p
    _ = fubiniStudyMeasure p₀ B := by
            rw [MeasureTheory.lintegral_const, h_mu_univ, mul_one]

/-! ## Phase G5 — invariant finite measures are scalar multiples of Fubini–Study

`fubiniStudyMeasure_unique` pins every *probability* measure invariant under
the unitary action to `fubiniStudyMeasure p₀`. The two corollaries below
extend that to arbitrary **finite** invariant measures (normalising by the
total mass) and re-express the result in the `∃ c, μ = c • μFS` shape that the
LF4 concrete measure bridges consume.

This is the invariant-measure-uniqueness fact for the `ℂℙ^{N-1}` / `U(N)`
instantiation: when LF4 instantiates `SectorData` with
`P := ℙ ℂ (EuclideanSpace ℂ (Fin N))`, `G := Matrix.unitaryGroup (Fin N) ℂ`,
and `μFS := fubiniStudyMeasure p₀`, the concrete bridges
(`cp_measure_bridge` / `k_measure_bridge`) route through
`invariant_measure_uniqueness_cpn` and cite no axiom. (Historically this was
the concrete realisation of an abstract `CSD.LF2.invariant_measure_uniqueness`
axiom — stated over an arbitrary pretransitive `(P, G)` with no topology; that
axiom and the abstract `measure_bridge` lemma it served were **removed
2026-06-04**, since nothing downstream used the abstract statement. The
concrete fact proved here is all that was ever load-bearing.) -/

/-- **Phase G5.** Any finite measure on `ℂℙ^{N-1}` invariant under the unitary
action is a scalar multiple of the Fubini–Study measure at any reference
point. The scalar is the total mass `μ Set.univ`.

Proof: if the total mass is zero the measure is zero; otherwise normalise by
the total mass to obtain an invariant *probability* measure, pin it to
`fubiniStudyMeasure p₀` via `fubiniStudyMeasure_unique`, and scale back. -/
theorem invariant_finiteMeasure_eq_smul_fubiniStudy
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N)))
    (μ : MeasureTheory.Measure (ℙ ℂ (EuclideanSpace ℂ (Fin N))))
    [MeasureTheory.IsFiniteMeasure μ]
    (hμ_inv : ∀ U : Matrix.unitaryGroup (Fin N) ℂ,
        MeasureTheory.MeasurePreserving (fun p => U • p) μ μ) :
    ∃ c : ENNReal, μ = c • fubiniStudyMeasure p₀ := by
  rcases eq_or_ne (μ Set.univ) 0 with h0 | h0
  · exact ⟨0, by rw [zero_smul]; exact MeasureTheory.Measure.measure_univ_eq_zero.mp h0⟩
  · have htop : μ Set.univ ≠ ⊤ := MeasureTheory.measure_ne_top μ Set.univ
    -- The mass-normalised measure is a probability measure.
    haveI hprob : MeasureTheory.IsProbabilityMeasure ((μ Set.univ)⁻¹ • μ) := by
      refine ⟨?_⟩
      rw [MeasureTheory.Measure.smul_apply, smul_eq_mul]
      exact ENNReal.inv_mul_cancel h0 htop
    -- Scaling preserves invariance, so the normalised measure is invariant.
    have hinv : ∀ U : Matrix.unitaryGroup (Fin N) ℂ,
        MeasureTheory.Measure.map (fun p => U • p) ((μ Set.univ)⁻¹ • μ)
          = (μ Set.univ)⁻¹ • μ := by
      intro U
      rw [MeasureTheory.Measure.map_smul, (hμ_inv U).map_eq]
    -- Uniqueness pins the normalised measure to Fubini–Study.
    have heq : ((μ Set.univ)⁻¹ • μ) = fubiniStudyMeasure p₀ :=
      fubiniStudyMeasure_unique p₀ ((μ Set.univ)⁻¹ • μ) hinv
    refine ⟨μ Set.univ, ?_⟩
    rw [← heq, smul_smul, ENNReal.mul_inv_cancel h0 htop, one_smul]

/-- **Phase G5 — concrete realisation of `CSD.LF2.invariant_measure_uniqueness`.**
For the `ℂℙ^{N-1}` / `U(N)` instantiation, any unitary-invariant probability
measure `μFS` and any unitary-invariant finite measure `μ` satisfy
`∃ c, μ = c • μFS`. This matches the LF2 spec axiom's conclusion shape (with
the reference point `p₀` made explicit), and is proved — no axiom — from
`fubiniStudyMeasure_unique` plus `invariant_finiteMeasure_eq_smul_fubiniStudy`.

`μFS` is pinned to `fubiniStudyMeasure p₀` by uniqueness; `μ` is a scalar
multiple of the same; composing gives `μ = c • μFS`. -/
theorem invariant_measure_uniqueness_cpn
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N)))
    (μFS : MeasureTheory.Measure (ℙ ℂ (EuclideanSpace ℂ (Fin N))))
    [MeasureTheory.IsProbabilityMeasure μFS]
    (hμFS_inv : ∀ U : Matrix.unitaryGroup (Fin N) ℂ,
        MeasureTheory.MeasurePreserving (fun p => U • p) μFS μFS)
    (μ : MeasureTheory.Measure (ℙ ℂ (EuclideanSpace ℂ (Fin N))))
    [MeasureTheory.IsFiniteMeasure μ]
    (hμ_inv : ∀ U : Matrix.unitaryGroup (Fin N) ℂ,
        MeasureTheory.MeasurePreserving (fun p => U • p) μ μ) :
    ∃ c : ENNReal, μ = c • μFS := by
  have hFS : μFS = fubiniStudyMeasure p₀ :=
    fubiniStudyMeasure_unique p₀ μFS (fun U => (hμFS_inv U).map_eq)
  obtain ⟨c, hc⟩ := invariant_finiteMeasure_eq_smul_fubiniStudy p₀ μ hμ_inv
  exact ⟨c, by rw [hc, hFS]⟩

end Matrix.UnitaryGroup
