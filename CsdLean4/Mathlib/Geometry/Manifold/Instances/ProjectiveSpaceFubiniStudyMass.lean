/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudyVolume
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitaryTransitive
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.TransitionProbability
public import CsdLean4.Mathlib.Analysis.SpecialFunctions.JapaneseBracketIntegral
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Complex

/-!
# The mass of the Fubini–Study volume: `ω_FS^{∧n} = (4π)ⁿ · μ_FS`

**TERM-SCOPE(Kahler)** **TERM-SCOPE(Liouville)** — this module uses the *restricted* senses of
"Kahler" and "Liouville"; the source repository's terms register records what is backed and what is
not.

**Category:** 1-Mathlib (CSD-free).

The constant. `ProjectiveSpaceFubiniStudyVolume.lean`
proved that the *normalised* volume of the top power of the Fubini–Study form is
`fsMeasure p₀`; this module computes the total mass, so the identity holds with its
constant. Three steps.

* **The density everywhere on the chart.** `mulVecCLM A` (a complex matrix acting on `ℂⁿ` as a
  real linear map) with ★ `det_mulVecCLM` — its real determinant is `|det_ℂ A|²`
  (`LinearMap.det_restrictScalars`, `Algebra.norm_complex_apply`); `fsModelForm_apply` (the model
  form written out from `fsChartForm_apply`); ★ `fsModelForm_mulVec` — a unitary matrix acting
  linearly on the chart pulls the model form at `U w` back to the model form at `w`; `fsScale r`,
  the diagonal scaling `diag(t⁻¹, t^{-1/2}, …)` with `t = 1 + r²`, and ★ `fsModelForm_single` —
  at `r e₀` the model form is the pullback of the model form at the origin along it; hence, with
  the Jacobian rule `compContinuousLinearMap_apply_basis` and the count at the origin,
  ★★ `wedgePow_fsModelForm_stdBasis`: **the coefficient of the top power at every `w` is
  `(-4)ⁿ n! (1 + ‖w‖²)^{-(n+1)}`** (rotate `w` to the first axis by `exists_unitary_map_unit`,
  where the form is diagonal).
* **The mass is one chart integral.** `chartAt_origin_source`, `chartAt_origin_symm`;
  `fsVolume_chartSource_zero` (on the domain of the chart at `origin 0` the volume is the chart
  integral over all of `ℂⁿ`) and ★ `fsVolume_compl_chartSource_zero` (the hyperplane `z₀ = 0` is
  null: in every other affine chart it is a coordinate hyperplane, `Measure.addHaar_submodule`);
  ★ `fsVolume_univ_eq_lintegral`.
* **The constant.** ★★ `fsVolume_univ` — **`fsVolume n univ = (4π)ⁿ`**, by
  `lintegral_pi_pow_inv_one_add_sum_norm_sq` (`∫_{ℂⁿ} (1 + ‖w‖²)^{-(n+1)} = πⁿ/n!`); and
  ★★★ `fsVolume_eq_smul_fsMeasure` — **`fsVolume n = (4π)ⁿ • fsMeasure p₀`**:
  the measure of the top power of the Fubini–Study form *is* the Fubini–Study measure, up to the
  explicit constant `(4π)ⁿ`.

## Honest scope

⚠️ **The constant is convention-bound.** `fsChartForm` carries the factor `-4` of its potential
`log(1 + ‖z‖²)` (`fsChartForm_zero : fsChartForm 0 = -4 • fundamentalFormAlt`), and the wedge
`ContinuousAlternatingMap.wedge` has its own normalisation (`Alternating/Wedge.lean`); the `(4π)ⁿ`
is the mass of *this* top power against Lebesgue measure on the model, and the literal `ωⁿ/n!`
of the textbooks is `fsVolume n / n!` with the same measure — the identity below is the honest
form of that sentence, with every factor visible.

⚠️ **`n = 0` is included**: the manifold is a point, `fsVolume 0 = δ`, and `(4π)⁰ = 1`.

**Provenance and references.** The top-power plan (M7);
`Instances/ProjectiveSpaceFubiniStudyVolume.lean`
(`fsVolumeNormalized_eq_fsMeasure`, `wedgePow_fsModelForm_zero_stdBasis`);
`Analysis/SpecialFunctions/JapaneseBracketIntegral.lean`;
`LinearAlgebra/Projectivization/UnitaryTransitive.lean`
(`exists_unitary_map_unit`); `LinearAlgebra/Projectivization/TransitionProbability.lean`
(`inner_toEuclideanLin_unitary`); `Geometry/Manifold/TopFormMeasure.lean` (`chartMeasure_apply`,
`topFormMeasure_apply_of_subset_source`); `Mathlib/RingTheory/Norm/Transitivity.lean`
(`LinearMap.det_restrictScalars`); the terms register (Liouville); the completed-work ledger.
-/

@[expose] public section

open MeasureTheory Set
open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix ENNReal Real
open Kahler

noncomputable section

namespace Projectivization

open DifferentialForm Matrix.UnitaryGroup

variable {n : ℕ}

/-! ### Real determinants of complex matrices -/

/-- A complex matrix acting on the pi model, as a real continuous linear map. -/
def mulVecCLM (A : Matrix (Fin n) (Fin n) ℂ) : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap ((Matrix.toLin' A).restrictScalars ℝ)

theorem mulVecCLM_apply (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    mulVecCLM A v = A *ᵥ v := by
  simp [mulVecCLM]

/-- ★ The real determinant of a complex matrix acting on `ℂⁿ` is the square modulus of its
complex determinant. -/
theorem det_mulVecCLM (A : Matrix (Fin n) (Fin n) ℂ) :
    (mulVecCLM A).det = Complex.normSq A.det := by
  rw [ContinuousLinearMap.det, mulVecCLM, LinearMap.coe_toContinuousLinearMap,
    LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]

theorem normSq_det_unitary (U : Matrix.unitaryGroup (Fin n) ℂ) :
    Complex.normSq U.val.det = 1 := by
  have h := Unitary.star_mul_self_of_mem (Matrix.det_of_mem_unitary U.2)
  have : ((Complex.normSq U.val.det : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]; exact h
  exact_mod_cast this

theorem norm_toEuclideanLin_unitary (U : Matrix.unitaryGroup (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) : ‖Matrix.toEuclideanLin U.val x‖ = ‖x‖ := by
  have h1 := norm_sq_eq_re_inner (𝕜 := ℂ) (Matrix.toEuclideanLin U.val x)
  have h2 := norm_sq_eq_re_inner (𝕜 := ℂ) x
  rw [inner_toEuclideanLin_unitary] at h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h1.trans h2.symm)

theorem toLpCLM_mulVec (A : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) :
    toLpCLM (A *ᵥ w) = Matrix.toEuclideanLin A (toLpCLM w) := rfl

theorem toLpCLM_apply (x : Fin n → ℂ) (j : Fin n) : (toLpCLM x).ofLp j = x j := rfl

/-! ### The model form, and its rotation invariance -/

/-- The model form written out: `-4 (t⁻¹ Im⟪u,v⟫ - t⁻² Im(⟪u,w⟫⟪w,v⟫))` with `t = 1 + ‖w‖²`. -/
theorem fsModelForm_apply (w u v : Fin n → ℂ) :
    fsModelForm w ![u, v]
      = -4 * ((1 + ‖toLpCLM w‖ ^ 2)⁻¹ * (inner ℂ (toLpCLM u) (toLpCLM v)).im
        - (1 + ‖toLpCLM w‖ ^ 2)⁻¹ ^ 2
          * (inner ℂ (toLpCLM u) (toLpCLM w) * inner ℂ (toLpCLM w) (toLpCLM v)).im) := by
  have h : (inner ℂ (toLpCLM u) (toLpCLM w) * inner ℂ (toLpCLM w) (toLpCLM v)).im
      = (inner ℂ (toLpCLM w) (toLpCLM u)).re * (inner ℂ (toLpCLM w) (toLpCLM v)).im
        - (inner ℂ (toLpCLM w) (toLpCLM v)).re * (inner ℂ (toLpCLM w) (toLpCLM u)).im := by
    rw [← inner_conj_symm (toLpCLM u) (toLpCLM w)]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [h]
  simp only [fsModelForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    fsChartForm_apply, Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one, metric,
    fundamentalForm]

/-- ★ **Rotation invariance of the model form**: a unitary matrix acting linearly on the chart
pulls the model form at `U w` back to the model form at `w`. -/
theorem fsModelForm_mulVec (U : Matrix.unitaryGroup (Fin n) ℂ) (w : Fin n → ℂ) :
    (fsModelForm (U.val *ᵥ w)).compContinuousLinearMap (mulVecCLM U.val) = fsModelForm w := by
  ext v
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hv : (⇑(mulVecCLM U.val) ∘ v) = ![U.val *ᵥ v 0, U.val *ᵥ v 1] := by
    funext i; fin_cases i <;> simp [mulVecCLM_apply]
  have hv' : v = ![v 0, v 1] := by
    funext i; fin_cases i <;> rfl
  rw [hv, fsModelForm_apply]
  conv_rhs => rw [hv', fsModelForm_apply]
  simp only [toLpCLM_mulVec, inner_toEuclideanLin_unitary, norm_toEuclideanLin_unitary]

/-! ### The form on the first axis is a diagonal pullback of the form at the origin -/

section Scale

variable [NeZero n]

/-- The diagonal entries `t⁻¹, t^{-1/2}, …, t^{-1/2}`, `t = 1 + r²`. -/
def fsScaleEntry (r : ℝ) (j : Fin n) : ℝ :=
  if j = 0 then (1 + r ^ 2)⁻¹ else Real.sqrt (1 + r ^ 2)⁻¹

/-- The diagonal scaling `diag(t⁻¹, t^{-1/2}, …, t^{-1/2})`. -/
def fsScale (r : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun j => (fsScaleEntry r j : ℂ)

theorem fsScale_mulVec_apply (r : ℝ) (u : Fin n → ℂ) (j : Fin n) :
    (fsScale r *ᵥ u) j = (fsScaleEntry r j : ℂ) * u j := by
  rw [fsScale, Matrix.mulVec_diagonal]

theorem fsScaleEntry_mul_self (r : ℝ) (j : Fin n) :
    fsScaleEntry r j * fsScaleEntry r j
      = (1 + r ^ 2)⁻¹ - (1 + r ^ 2)⁻¹ ^ 2 * r ^ 2 * (if j = 0 then 1 else 0) := by
  have ht : (0 : ℝ) < 1 + r ^ 2 := by positivity
  unfold fsScaleEntry
  split_ifs
  · field_simp
    ring
  · rw [Real.mul_self_sqrt (inv_nonneg.2 ht.le)]
    ring

theorem inner_fsScale (r : ℝ) (u v : Fin n → ℂ) :
    inner ℂ (toLpCLM (fsScale r *ᵥ u)) (toLpCLM (fsScale r *ᵥ v))
      = (((1 + r ^ 2)⁻¹ : ℝ) : ℂ) * inner ℂ (toLpCLM u) (toLpCLM v)
        - (((1 + r ^ 2)⁻¹ ^ 2 * r ^ 2 : ℝ) : ℂ) * inner ℂ (u 0) (v 0) := by
  have hterm : ∀ j, inner ℂ ((fsScale r *ᵥ u) j) ((fsScale r *ᵥ v) j)
      = (((1 + r ^ 2)⁻¹ : ℝ) : ℂ) * inner ℂ (u j) (v j)
        - (((1 + r ^ 2)⁻¹ ^ 2 * r ^ 2 : ℝ) : ℂ) * (if j = 0 then inner ℂ (u 0) (v 0) else 0) := by
    intro j
    rw [fsScale_mulVec_apply, fsScale_mulVec_apply, ← smul_eq_mul, ← smul_eq_mul, inner_smul_left,
      inner_smul_right, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
      fsScaleEntry_mul_self]
    split_ifs with hj
    · subst hj
      push_cast
      ring
    · push_cast
      ring
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [toLpCLM_apply]
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_ite_eq']
  simp

/-- ★ At `r e₀` the model form is the pullback of the model form at the origin along the diagonal
scaling. -/
theorem fsModelForm_single (r : ℝ) :
    fsModelForm (Pi.single (0 : Fin n) (r : ℂ))
      = (fsModelForm 0).compContinuousLinearMap (mulVecCLM (fsScale r)) := by
  ext v
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hv : (⇑(mulVecCLM (fsScale r)) ∘ v) = ![fsScale r *ᵥ v 0, fsScale r *ᵥ v 1] := by
    funext i; fin_cases i <;> simp [mulVecCLM_apply]
  have hv' : v = ![v 0, v 1] := by
    funext i; fin_cases i <;> rfl
  rw [hv, fsModelForm_apply]
  conv_lhs => rw [hv', fsModelForm_apply]
  rw [inner_fsScale]
  have hs : toLpCLM (Pi.single (0 : Fin n) (r : ℂ)) = EuclideanSpace.single 0 (r : ℂ) := rfl
  rw [hs, EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_left, PiLp.norm_single,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, map_zero, norm_zero]
  simp only [inner_zero_right, inner_zero_left, Complex.zero_im, zero_mul,
    mul_zero, Complex.conj_ofReal,
    toLpCLM_apply, RCLike.inner_apply, Complex.sub_im, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, zero_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, add_zero, inv_one, one_mul]
  ring

theorem normSq_det_fsScale (r : ℝ) :
    Complex.normSq (fsScale (n := n) r).det = ((1 + r ^ 2)⁻¹) ^ (n + 1) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  subst hm
  rw [fsScale, Matrix.det_diagonal, map_prod, Fin.prod_univ_succ]
  simp only [fsScaleEntry, if_true, Fin.succ_ne_zero, if_false, Complex.normSq_ofReal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Real.mul_self_sqrt (inv_nonneg.2 (by positivity)), Nat.succ_eq_add_one, pow_succ]
  ring

/-- ★ The coefficient of the top power at `r e₀` is `(-4)ⁿ n! (1 + r²)^{-(n+1)}`. -/
theorem wedgePow_fsModelForm_single (r : ℝ) :
    ContinuousAlternatingMap.wedgePow (fsModelForm (Pi.single (0 : Fin n) (r : ℂ))) n (stdBasis n)
      = (-4 : ℝ) ^ n * n.factorial * ((1 + r ^ 2)⁻¹) ^ (n + 1) := by
  rw [fsModelForm_single, ← ContinuousAlternatingMap.wedgePow_compContinuousLinearMap,
    ContinuousAlternatingMap.compContinuousLinearMap_apply_basis, det_mulVecCLM,
    normSq_det_fsScale, wedgePow_fsModelForm_zero_stdBasis]
  ring

end Scale

/-! ### The density everywhere -/

/-- ★★ **The density of the top power, everywhere on the chart**: the coefficient of
`fsModelForm w ^ ∧n` against the standard basis is `(-4)ⁿ n! (1 + ‖w‖²)^{-(n+1)}`. Rotate `w`
to the first axis by a unitary matrix, where the form is a diagonal pullback of the form at the
origin, and apply the Jacobian rule twice. -/
theorem wedgePow_fsModelForm_stdBasis (w : Fin n → ℂ) :
    ContinuousAlternatingMap.wedgePow (fsModelForm w) n (stdBasis n)
      = (-4 : ℝ) ^ n * n.factorial * ((1 + ‖toLpCLM w‖ ^ 2)⁻¹) ^ (n + 1) := by
  by_cases hw : w = 0
  · subst hw
    rw [wedgePow_fsModelForm_zero_stdBasis, map_zero, norm_zero]
    simp
  · have : NeZero n := ⟨fun h => hw (by subst h; exact Subsingleton.elim _ _)⟩
    have hx : toLpCLM w ≠ 0 := fun h => hw (by
      have := congrArg WithLp.ofLp h
      simpa using this)
    obtain ⟨U, hU⟩ := Matrix.UnitaryGroup.exists_unitary_map_unit (‖toLpCLM w‖⁻¹ • toLpCLM w)
      (EuclideanSpace.single 0 (1 : ℂ)) (norm_smul_inv_norm hx) (by simp)
    have h1 : Matrix.toEuclideanLin U.val (toLpCLM w)
        = ‖toLpCLM w‖ • EuclideanSpace.single 0 (1 : ℂ) := by
      have hsm : toLpCLM w = ‖toLpCLM w‖ • (‖toLpCLM w‖⁻¹ • toLpCLM w) := by
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx), one_smul]
      conv_lhs => rw [hsm]
      rw [LinearMap.map_smul_of_tower, hU]
    have hUw : U.val *ᵥ w = Pi.single 0 ((‖toLpCLM w‖ : ℝ) : ℂ) := by
      have h2 : toLpCLM (U.val *ᵥ w) = ‖toLpCLM w‖ • EuclideanSpace.single 0 (1 : ℂ) := by
        rw [toLpCLM_mulVec, h1]
      funext j
      have hj := congrArg (fun z => z j) h2
      simpa [toLpCLM_apply, PiLp.single_apply, Pi.single_apply] using hj
    rw [← fsModelForm_mulVec U w, ← ContinuousAlternatingMap.wedgePow_compContinuousLinearMap,
      ContinuousAlternatingMap.compContinuousLinearMap_apply_basis, det_mulVecCLM,
      normSq_det_unitary, one_mul, hUw, wedgePow_fsModelForm_single]

/-- The chart density of the Fubini–Study volume, at `origin 0`, as a function of the coordinate
sum `∑ⱼ ‖wⱼ‖²`. -/
theorem chartDensity_fsTopForm_origin_zero (w : Fin n → ℂ) :
    chartDensity (stdBasis n) (fun x => fsTopForm n x) (origin 0) w
      = ENNReal.ofReal (4 ^ n * n.factorial * ((1 + ∑ j, ‖w j‖ ^ 2)⁻¹) ^ (n + 1)) := by
  rw [chartDensity, localRep_fsTopForm, wedgePow_fsModelForm_stdBasis, abs_mul, abs_mul, abs_pow,
    abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos (Nat.cast_pos.2 n.factorial_pos),
    abs_of_pos (by positivity), EuclideanSpace.norm_sq_eq]
  simp only [toLpCLM_apply]

/-! ### The mass is one chart integral -/

theorem chartAt_origin_source (i : Fin (n + 1)) :
    (chartAt (Fin n → ℂ) (origin i)).source = chartSource i := by
  show (chartAtIdx (idx (origin i))).source = chartSource i
  rw [idx_origin]
  rfl

theorem chartAt_origin_symm (i : Fin (n + 1)) (w : Fin n → ℂ) :
    (chartAt (Fin n → ℂ) (origin i)).symm w = chartInv i w := by
  show (chartAtIdx (idx (origin i))).symm w = chartInv i w
  rw [idx_origin]
  rfl

/-- On the domain of the chart at `origin 0`, the Fubini–Study volume is the chart integral over
all of `ℂⁿ`. -/
theorem fsVolume_chartSource_zero :
    fsVolume n (chartSource 0)
      = ∫⁻ w, chartDensity (stdBasis n) (fun x => fsTopForm n x) (origin 0) w := by
  have hmeas : MeasurableSet (chartSource (n := n) 0) := (isOpen_chartSource 0).measurableSet
  rw [fsVolume, topFormMeasure_apply_of_subset_source volume (stdBasis n) (fun x => fsTopForm n x)
    (affineChartCover n) (origin 0) hmeas (by rw [chartAt_origin_source]),
    chartMeasure_apply volume (stdBasis n) (fun x => fsTopForm n x) (origin 0) hmeas]
  have : (chartAt (Fin n → ℂ) (origin (n := n) 0)).target
      ∩ (chartAt (Fin n → ℂ) (origin (n := n) 0)).symm ⁻¹' chartSource 0 = univ := by
    apply Set.eq_univ_of_forall
    intro w
    refine ⟨Set.mem_univ _, ?_⟩
    rw [Set.mem_preimage, chartAt_origin_symm]
    exact chartInv_mem_chartSource 0 w
  rw [this, Measure.restrict_univ]

/-- ★ The complement of the chart domain at `origin 0` — the hyperplane `z₀ = 0` — is null: in
every other affine chart it is a coordinate hyperplane of `ℂⁿ`, which has Lebesgue measure zero. -/
theorem fsVolume_compl_chartSource_zero : fsVolume n (chartSource 0)ᶜ = 0 := by
  have hsub : (chartSource (n := n) 0)ᶜ
      ⊆ ⋃ i : Fin (n + 1), (chartSource i ∩ (chartSource 0)ᶜ) := fun p hp =>
    Set.mem_iUnion.2 ⟨idx p, idx_spec p, hp⟩
  refine measure_mono_null hsub (measure_iUnion_null fun i => ?_)
  have hmeas : MeasurableSet (chartSource (n := n) i ∩ (chartSource 0)ᶜ) :=
    (isOpen_chartSource i).measurableSet.inter (isOpen_chartSource 0).measurableSet.compl
  rw [fsVolume, topFormMeasure_apply_of_subset_source volume (stdBasis n) (fun x => fsTopForm n x)
    (affineChartCover n) (origin i) hmeas (by rw [chartAt_origin_source]; exact
        Set.inter_subset_left),
    chartMeasure_apply volume (stdBasis n) (fun x => fsTopForm n x) (origin i) hmeas]
  by_cases hi : i = 0
  · subst hi
    have : (chartAt (Fin n → ℂ) (origin (n := n) 0)).target
        ∩ (chartAt (Fin n → ℂ) (origin (n := n) 0)).symm ⁻¹' (chartSource 0 ∩ (chartSource 0)ᶜ)
        = ∅ := by
      simp
    rw [this, Measure.restrict_empty, lintegral_zero_measure]
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (Ne.symm hi)
    have hnull : volume {w : Fin n → ℂ | w k = 0} = 0 := by
      have : {w : Fin n → ℂ | w k = 0}
          = ((LinearMap.proj k : (Fin n → ℂ) →ₗ[ℝ] ℂ).ker : Set (Fin n → ℂ)) := by
        ext w
        simp [LinearMap.mem_ker]
      rw [this]
      refine Measure.addHaar_submodule volume _ ?_
      intro htop
      have hmem : (Pi.single k (1 : ℂ) : Fin n → ℂ)
          ∈ (LinearMap.proj k : (Fin n → ℂ) →ₗ[ℝ] ℂ).ker := htop ▸ Submodule.mem_top
      simp at hmem
    refine nonpos_iff_eq_zero.1 ?_
    calc ∫⁻ w in (chartAt (Fin n → ℂ) (origin i)).target
          ∩ (chartAt (Fin n → ℂ) (origin i)).symm ⁻¹' (chartSource i ∩ (chartSource 0)ᶜ),
          chartDensity (stdBasis n) (fun x => fsTopForm n x) (origin i) w
        ≤ ∫⁻ w in {w : Fin n → ℂ | w k = 0},
            chartDensity (stdBasis n) (fun x => fsTopForm n x) (origin i) w := by
          apply lintegral_mono_set
          rintro w ⟨-, hw⟩
          rw [Set.mem_preimage, chartAt_origin_symm] at hw
          have h2 := hw.2
          rw [Set.mem_compl_iff, chartInv, mem_chartSource_mk] at h2
          show w k = 0
          rw [← insertOne_apply_succAbove i w k, hk]
          exact not_not.1 h2
      _ = 0 := setLIntegral_measure_zero _ _ hnull

/-- ★ **The mass of the Fubini–Study volume is the chart-0 integral of its density.** -/
theorem fsVolume_univ_eq_lintegral :
    fsVolume n univ = ∫⁻ w, chartDensity (stdBasis n) (fun x => fsTopForm n x) (origin 0) w := by
  rw [← measure_add_measure_compl (isOpen_chartSource 0).measurableSet,
    fsVolume_compl_chartSource_zero, add_zero, fsVolume_chartSource_zero]

/-! ### The constant -/

/-- ★★ **The mass of the Fubini–Study volume is `(4π)ⁿ`.** -/
theorem fsVolume_univ : fsVolume n univ = ENNReal.ofReal ((4 * π) ^ n) := by
  rw [fsVolume_univ_eq_lintegral]
  simp_rw [chartDensity_fsTopForm_origin_zero]
  have hmeas : Measurable fun w : Fin n → ℂ =>
      ENNReal.ofReal (((1 + ∑ j, ‖w j‖ ^ 2)⁻¹) ^ (n + 1)) :=
    (((Finset.measurable_sum _ fun j _ =>
      (measurable_pi_apply j).norm.pow_const 2).const_add 1).inv.pow_const _).ennreal_ofReal
  simp_rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 ^ n * n.factorial)]
  rw [lintegral_const_mul _ hmeas, lintegral_pi_pow_inv_one_add_sum_norm_sq n,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_pow]
  field_simp

/-- ★★★ **The measure of the top power of the Fubini–Study form is `(4π)ⁿ` times the
Fubini–Study measure**, for every base point `p₀`: `ω_FS^{∧n} = (4π)ⁿ · μ_FS`, with every factor
visible. -/
theorem fsVolume_eq_smul_fsMeasure (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :
    fsVolume n = ENNReal.ofReal ((4 * π) ^ n) • fsMeasure p₀ := by
  have h := fsVolumeNormalized_eq_fsMeasure (n := n) p₀
  rw [fsVolumeNormalized, fsVolume_univ] at h
  rw [← h, smul_smul, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 (by positivity)).ne'
    ENNReal.ofReal_ne_top, one_smul]

end Projectivization
