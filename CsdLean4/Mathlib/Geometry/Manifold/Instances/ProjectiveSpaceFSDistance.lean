/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFSLength
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.WignerRigidity
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceSchrodingerFlow
public import Mathlib.Geometry.Manifold.Riemannian.PathELength
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Fubini–Study distance is `2 arccos √P`

**TERM-SCOPE(Kahler)** — this module uses the restricted sense of "Kähler"; `specs/TERMS.md`
records what is backed.

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold.Instances`).
BACKLOG #330 (geometric QM, item 5 of the 2026-11-08 plan).

Mathlib's Riemannian distance `Manifold.riemannianEDist` is the infimum of the lengths of `C¹`
paths, for whatever extended norm the tangent spaces carry. Given the Fubini–Study norm
`‖v‖ = √g(v, v)` (`fsENorm`, a local instance: `ℂℙⁿ`'s tangent spaces carry no norm otherwise),
it is the Fubini–Study distance `fsEDist`, and it is `2 arccos √P(p, q)` with `P` the transition
probability: the angle between the rays, doubled by the corpus's normalisation of `fsForm`.

## The norm, the length, the distance

* `fsENorm` (local instance), `fsENorm_apply`, `fsPathLength`, `fsPathLength_eq`, `fsEDist`;
* `fsModelMetric_smul_smul`, `fsMetric_smul_smul`, `fsENormSMulClass` (local instance).

## The lower bound

* `continuous_transProb_right`, `fsAngle p q = arccos √P(p, q)`, `fsAngle_self`,
  `fsAngle_nonneg`, `fsAngle_le_pi_div_two`, `continuous_fsAngle_right`;
* `hasDerivAt_chartFun_comp` — a differentiable curve read in the chart of its point;
* ★★ `hasDerivAt_fsAngle_comp` — **away from `P ∈ {0, 1}` the angle to a fixed ray changes at most
  at half the Fubini–Study speed** (#330's `sq_dTransProb_le`);
* `ofReal_two_mul_sub_le_fsPathLength` — the integral step (the derivative is measurable, so a
  finite length makes it integrable);
* ★★★ `ofReal_two_mul_fsAngle_le_fsPathLength_of` — **a path continuous on `[0, 1]` and
  differentiable inside is at least `2 arccos √P(γ 0, γ 1)` long**: the angle is integrated on a
  stretch where it climbs from `0` to any level below its final value, where it is
  differentiable; ★★★ `ofReal_two_mul_fsAngle_le_fsPathLength` — the `C¹` case.

## The upper bound and the distance

* `contMDiff_projCurve` — a projected curve with a smooth lift is `C¹`;
  `inner_orthonormal_pair`; ★★ `fsPathLength_greatCircle` — **the great circle
  `t ↦ [cos(tθ) φ + sin(tθ) χ]` of an orthonormal pair has length `2θ`**;
* `transProb_eq_norm_inner_normalize_sq`; ★★★ `exists_fsPathLength_eq` — **between any two rays
  there is a `C¹` path of length `2 arccos √P`** (a great circle);
* ★★★ `fsEDist_eq` — **`fsEDist p q = 2 arccos √P(p, q)`**; `fsEDist_le_pi`, ★
  `fsEDist_eq_zero_iff`.

## Honest scope

⚠️ **The norm is a local instance.** `fsENorm` is not a global instance, because nothing else in the
corpus gives the tangent spaces of `ℂℙⁿ` a norm and a global instance would decide that for every
importer; `fsEDist` and `fsPathLength` package Mathlib's constructions with it.

⚠️ **The factor 2 is the corpus's normalisation** (`g = 4 Re h`, #327): for the textbook
Fubini–Study metric `g / 4` the distance is `arccos √P`.

## References

W. K. Wootters, Phys. Rev. D 23 (1981) 357; J. Anandan, Y. Aharonov, Phys. Rev. Lett. 65 (1990)
1697; `Instances/ProjectiveSpaceFSLength.lean` (#330, first part); `specs/BACKLOG.md` #330, #331;
`specs/future-work.md`.
-/

@[expose] public section

open scoped Manifold ContDiff LinearAlgebra.Projectivization ENNReal Topology
open Kahler DifferentialForm FisherRao Set MeasureTheory

noncomputable section

namespace Projectivization

variable {n : ℕ}

/-! ### The Fubini–Study norm, length and distance -/

/-- **The Fubini–Study extended norm** `‖v‖ₑ = √g(v, v)` on the tangent space at `x`. -/
@[instance_reducible]
def fsENorm (x : ℙ ℂ (Ambient n)) : ENorm (TangentSpace (𝓘(ℝ, Fin n → ℂ)) x) :=
  ⟨fun v => ENNReal.ofReal √(fsMetric x v v)⟩

attribute [local instance] fsENorm

theorem fsENorm_apply (x : ℙ ℂ (Ambient n)) (v : TangentSpace (𝓘(ℝ, Fin n → ℂ)) x) :
    ‖v‖ₑ = ENNReal.ofReal √(fsMetric x v v) := rfl

/-- **The Fubini–Study length** of a path on `[a, b]`. -/
def fsPathLength (γ : ℝ → ℙ ℂ (Ambient n)) (a b : ℝ) : ℝ≥0∞ :=
  Manifold.pathELength (𝓘(ℝ, Fin n → ℂ)) γ a b

/-- **The Fubini–Study distance**: Mathlib's Riemannian distance for the Fubini–Study norm. -/
def fsEDist (p q : ℙ ℂ (Ambient n)) : ℝ≥0∞ :=
  Manifold.riemannianEDist (𝓘(ℝ, Fin n → ℂ)) p q

theorem fsPathLength_eq (γ : ℝ → ℙ ℂ (Ambient n)) (a b : ℝ) :
    fsPathLength γ a b
      = ∫⁻ t in Icc a b, ENNReal.ofReal
          √(fsMetric (γ t) (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ t (1 : ℝ))
            (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ t (1 : ℝ))) := by
  rw [fsPathLength, Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  rfl

/-! ### The angle between two rays -/

theorem continuous_transProb_right (p : ℙ ℂ (Ambient n)) :
    Continuous (fun q : ℙ ℂ (Ambient n) => transProb p q) := by
  rw [continuous_iff]
  have hcomp : ((fun q => transProb p q) ∘ (mk' ℂ : _ → ℙ ℂ (Ambient n)))
      = fun v : {v : Ambient n // v ≠ 0} => transProbVec p.rep (v : Ambient n) := by
    funext v
    show transProb p (mk ℂ (v : Ambient n) v.2) = _
    conv_lhs => rw [← mk_rep p]
    exact transProb_mk _ _
  rw [hcomp]
  have hnum : Continuous fun v : {v : Ambient n // v ≠ 0} => ‖inner ℂ p.rep (v : Ambient n)‖ ^ 2 :=
    ((continuous_const.inner continuous_subtype_val).norm).pow 2
  have hden : Continuous fun v : {v : Ambient n // v ≠ 0} => ‖p.rep‖ ^ 2 * ‖(v : Ambient n)‖ ^ 2 :=
    continuous_const.mul (continuous_subtype_val.norm.pow 2)
  exact hnum.div hden fun v => mul_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.2 (rep_nonzero p)))
    (pow_ne_zero 2 (norm_ne_zero_iff.2 v.2))

/-- **The Fubini–Study angle** `arccos √P(p, q)` between two rays. -/
def fsAngle (p q : ℙ ℂ (Ambient n)) : ℝ := Real.arccos √(transProb p q)

theorem fsAngle_self (p : ℙ ℂ (Ambient n)) : fsAngle p p = 0 := by
  rw [fsAngle, transProb_self, Real.sqrt_one, Real.arccos_one]

theorem fsAngle_nonneg (p q : ℙ ℂ (Ambient n)) : 0 ≤ fsAngle p q := Real.arccos_nonneg _

theorem fsAngle_le_pi_div_two (p q : ℙ ℂ (Ambient n)) : fsAngle p q ≤ Real.pi / 2 :=
  Real.arccos_le_pi_div_two.2 (Real.sqrt_nonneg _)

theorem continuous_fsAngle_right (p : ℙ ℂ (Ambient n)) :
    Continuous (fun q : ℙ ℂ (Ambient n) => fsAngle p q) :=
  Real.continuous_arccos.comp (Real.continuous_sqrt.comp (continuous_transProb_right p))

/-! ### The angle along a curve -/

/-- A curve differentiable at `t`, read in the chart of `γ t`, has the manifold derivative as its
velocity. -/
theorem hasDerivAt_chartFun_comp {γ : ℝ → ℙ ℂ (Ambient n)} {t : ℝ}
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ t) :
    HasDerivAt (fun s => chartFun (idx (γ t)) (γ s))
      (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ t (1 : ℝ)) t := by
  have h := hγ.hasMFDerivAt
  have hw : writtenInExtChartAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) t γ
      = fun s => chartFun (idx (γ t)) (γ s) := by
    funext s
    simp only [writtenInExtChartAt, Function.comp, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id]
    rfl
  have h2 := h.2
  rw [hw] at h2
  simp only [modelWithCornersSelf_coe, range_id, extChartAt_coe, Function.comp_apply, id] at h2
  have h3 : HasFDerivAt (fun s => chartFun (idx (γ t)) (γ s))
      (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ t) t := by
    exact h2.hasFDerivAt Filter.univ_mem
  show HasFDerivAt _
    ((1 : ℝ →L[ℝ] ℝ).smulRight (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ t (1 : ℝ))) t
  refine h3.congr_fderiv (ContinuousLinearMap.ext_ring ?_)
  change _ = (1 : ℝ) • (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ t (1 : ℝ) : Fin n → ℂ)
  rw [one_smul]
  rfl

/-- ★★ **Away from `P ∈ {0, 1}` the angle to a fixed ray changes at most at half the
Fubini–Study speed.** -/
theorem hasDerivAt_fsAngle_comp (x : ℙ ℂ (Ambient n)) {γ : ℝ → ℙ ℂ (Ambient n)} {t : ℝ}
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ t)
    (h0 : 0 < transProb x (γ t)) (h1 : transProb x (γ t) < 1) :
    ∃ f', HasDerivAt (fun s => fsAngle x (γ s)) f' t ∧
      2 * |f'| ≤ √(fsMetric (γ t) (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ t (1 : ℝ))
        (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ t (1 : ℝ))) := by
  set i := idx (γ t)
  set v := mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ t (1 : ℝ)
  set w : ℝ → Fin n → ℂ := fun s => chartFun i (γ s)
  have hw : HasDerivAt w v t := hasDerivAt_chartFun_comp hγ
  set ψ : ℝ → Ambient n := fun s => insertOne i (w s)
  have hψ : HasDerivAt ψ (insertZero i v) t := by
    have := (hasFDerivAt_insertOne i (w t)).comp_hasDerivAt t hw
    exact this
  -- near `t` the curve lies in the chart, so `P(x, γ s) = P(x.rep, ψ s)`
  have hsrc : ∀ᶠ s in 𝓝 t, γ s ∈ chartSource i := by
    refine hγ.continuousAt.preimage_mem_nhds (isOpen_chartSource i |>.mem_nhds ?_)
    exact idx_spec (γ t)
  have hP : (fun s => transProb x (γ s)) =ᶠ[𝓝 t] fun s => transProbVec x.rep (ψ s) := by
    filter_upwards [hsrc] with s hs
    have hγs : γ s = mk ℂ (ψ s) (insertOne_ne_zero i (w s)) :=
      (chartInv_chartFun i (γ s) hs).symm
    rw [hγs, ← transProb_mk (rep_nonzero x), mk_rep]
  have hψ0 : ψ t ≠ 0 := insertOne_ne_zero i (w t)
  have hPd : HasDerivAt (fun s => transProb x (γ s)) (dTransProb x.rep (ψ t) (insertZero i v)) t :=
    (hasDerivAt_transProbVec x.rep hψ hψ0).congr_of_eventuallyEq hP
  set P := transProb x (γ t)
  set dP := dTransProb x.rep (ψ t) (insertZero i v)
  have hPt : transProbVec x.rep (ψ t) = P := (hP.eq_of_nhds).symm
  -- the chain rule through `√` and `arccos`
  have hsq : HasDerivAt (fun s => √(transProb x (γ s))) (dP / (2 * √P)) t := by
    have := (Real.hasDerivAt_sqrt h0.ne').comp t hPd
    refine this.congr_deriv ?_
    field_simp
  have hsP0 : 0 < √P := Real.sqrt_pos.2 h0
  have hsP1 : √P < 1 := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt h0.le h1
  have hac := (Real.hasDerivAt_arccos (by linarith) hsP1.ne).comp t hsq
  refine ⟨_, hac, ?_⟩
  -- the bound
  have hg : fsMetric (γ t) v v = fsInnerHom (ψ t) (insertZero i v) (insertZero i v) :=
    fsMetric_eq_fsInnerHom (γ t) v v
  rw [hg]
  have hbound := sq_dTransProb_le (rep_nonzero x) hψ0 (insertZero i v)
  rw [hPt] at hbound
  have hsq1 : 1 - √P ^ 2 = 1 - P := by rw [Real.sq_sqrt h0.le]
  have hden : 0 < √(1 - √P ^ 2) := Real.sqrt_pos.2 (by rw [hsq1]; linarith)
  have hf0 : 0 ≤ fsInnerHom (ψ t) (insertZero i v) (insertZero i v) := by
    have := sq_nonneg dP
    nlinarith [mul_pos h0 (sub_pos.2 h1)]
  have habs : |dP| ≤ √P * √(1 - P) * √(fsInnerHom (ψ t) (insertZero i v) (insertZero i v)) := by
    rw [← Real.sqrt_mul h0.le, ← Real.sqrt_mul (mul_nonneg h0.le (sub_pos.2 h1).le)]
    exact Real.abs_le_sqrt hbound
  rw [hsq1] at hden ⊢
  rw [abs_mul, abs_neg, abs_div, abs_one, abs_div, abs_mul, abs_of_pos hden, abs_of_pos hsP0,
    abs_two]
  rw [show 2 * (1 / √(1 - P) * (|dP| / (2 * √P))) = |dP| / (√P * √(1 - P)) by
    field_simp]
  rw [div_le_iff₀ (mul_pos hsP0 hden)]
  linarith [habs]

/-- The integral step: on a stretch `(t₀, t₁)` where the angle is differentiable with
`2 |F'| ≤ √g`, the rise `2 (F t₁ − F t₀)` is at most the length of the path on `[0, 1]`. -/
theorem ofReal_two_mul_sub_le_fsPathLength {γ : ℝ → ℙ ℂ (Ambient n)} {F : ℝ → ℝ} {t₀ t₁ : ℝ}
    (h01 : t₀ ≤ t₁) (hsub : Icc t₀ t₁ ⊆ Icc 0 1) (hFc : ContinuousOn F (Icc t₀ t₁))
    (hF : ∀ s ∈ Ioo t₀ t₁, HasDerivAt F (deriv F s) s ∧
      2 * |deriv F s| ≤ √(fsMetric (γ s) (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ s (1 : ℝ))
        (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ s (1 : ℝ)))) :
    ENNReal.ofReal (2 * (F t₁ - F t₀)) ≤ fsPathLength γ 0 1 := by
  set G : ℝ → ℝ := fun s => 2 * deriv F s
  have hGm : Measurable G := (measurable_deriv F).const_mul 2
  set I := ∫⁻ s in Ioo t₀ t₁, ENNReal.ofReal |G s|
  have hIL : I ≤ fsPathLength γ 0 1 := by
    rw [fsPathLength_eq]
    refine le_trans ?_ (lintegral_mono_set (Ioo_subset_Icc_self.trans hsub))
    refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioo fun s hs => ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    rw [abs_mul, abs_two]
    exact (hF s hs).2
  by_cases hI : I = ⊤
  · rw [hI, top_le_iff] at hIL
    rw [hIL]
    exact le_top
  have hGi : IntegrableOn G (Ioo t₀ t₁) := by
    refine ⟨hGm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    simp_rw [Real.enorm_eq_ofReal_abs]
    exact lt_top_iff_ne_top.2 hI
  have hdi : IntervalIntegrable (deriv F) MeasureTheory.volume t₀ t₁ := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le h01]
    have h2 : IntegrableOn (fun s => G s / 2) (Ioo t₀ t₁) := hGi.div_const 2
    refine IntegrableOn.congr_fun h2 (fun s _ => ?_) measurableSet_Ioo
    show 2 * deriv F s / 2 = deriv F s
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h01 hFc
    (fun s hs => (hF s hs).1) hdi
  have hint : 2 * (F t₁ - F t₀) = ∫ s in Ioo t₀ t₁, G s := by
    rw [← hftc, intervalIntegral.integral_of_le h01, integral_Ioc_eq_integral_Ioo,
      ← integral_const_mul]
  have hle : ∫ s in Ioo t₀ t₁, G s ≤ ∫ s in Ioo t₀ t₁, |G s| :=
    integral_mono hGi hGi.abs fun s => le_abs_self _
  have heq : ENNReal.ofReal (∫ s in Ioo t₀ t₁, |G s|) = I :=
    ofReal_integral_eq_lintegral_ofReal hGi.abs (Filter.Eventually.of_forall fun s => abs_nonneg _)
  calc ENNReal.ofReal (2 * (F t₁ - F t₀)) ≤ ENNReal.ofReal (∫ s in Ioo t₀ t₁, |G s|) := by
        rw [hint]
        exact ENNReal.ofReal_le_ofReal hle
    _ = I := heq
    _ ≤ fsPathLength γ 0 1 := hIL

/-- ★★★ **A path continuous on `[0, 1]` and differentiable inside is at least
`2 arccos √P(γ 0, γ 1)` long.** -/
theorem ofReal_two_mul_fsAngle_le_fsPathLength_of {γ : ℝ → ℙ ℂ (Ambient n)}
    (hc : ContinuousOn γ (Icc 0 1))
    (hd : ∀ s ∈ Ioo (0 : ℝ) 1, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ s) :
    ENNReal.ofReal (2 * fsAngle (γ 0) (γ 1)) ≤ fsPathLength γ 0 1 := by
  set x := γ 0
  set F : ℝ → ℝ := fun s => fsAngle x (γ s)
  have hFc : ContinuousOn F (Icc 0 1) :=
    (continuous_fsAngle_right x).comp_continuousOn hc
  set θ := F 1
  have hF0 : F 0 = 0 := fsAngle_self x
  -- the claim for every level `α ∈ (0, θ)`
  have key : ∀ α, 0 < α → α < θ → ENNReal.ofReal (2 * α) ≤ fsPathLength γ 0 1 := by
    intro α hα hαθ
    -- the last zero of `F`
    set Z := Icc (0 : ℝ) 1 ∩ F ⁻¹' {0}
    have hZc : IsClosed Z := hFc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hZn : Z.Nonempty := ⟨0, ⟨left_mem_Icc.2 zero_le_one, hF0⟩⟩
    have hZb : BddAbove Z := ⟨1, fun s hs => hs.1.2⟩
    set t₀ := sSup Z
    have ht₀ : t₀ ∈ Z := hZc.csSup_mem hZn hZb
    -- the first time after `t₀` the angle reaches `α`
    set A := Icc t₀ 1 ∩ F ⁻¹' Ici α
    have hsub0 : Icc t₀ 1 ⊆ Icc 0 1 := Icc_subset_Icc_left ht₀.1.1
    have hAc : IsClosed A :=
      (hFc.mono hsub0).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hAn : A.Nonempty := ⟨1, ⟨⟨ht₀.1.2, le_rfl⟩, hαθ.le⟩⟩
    have hAb : BddBelow A := ⟨t₀, fun s hs => hs.1.1⟩
    set t₁ := sInf A
    have ht₁ : t₁ ∈ A := hAc.csInf_mem hAn hAb
    have h01 : t₀ ≤ t₁ := ht₁.1.1
    have hsub : Icc t₀ t₁ ⊆ Icc 0 1 := Icc_subset_Icc ht₀.1.1 ht₁.1.2
    have hθ : θ ≤ Real.pi / 2 := fsAngle_le_pi_div_two _ _
    have hF : ∀ s ∈ Ioo t₀ t₁, HasDerivAt F (deriv F s) s ∧
        2 * |deriv F s| ≤ √(fsMetric (γ s) (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ s (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ s (1 : ℝ))) := by
      intro s hs
      have hs01 : s ∈ Ioo (0 : ℝ) 1 := ⟨ht₀.1.1.trans_lt hs.1, hs.2.trans_le ht₁.1.2⟩
      have hsI : s ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hs01
      -- `0 < F s < α`
      have hpos : 0 < F s := by
        rcases (fsAngle_nonneg x (γ s)).lt_or_eq with h | h
        · exact h
        · exfalso
          have hz : s ∈ Z := ⟨hsI, h.symm⟩
          exact absurd (le_csSup hZb hz) (not_le.2 hs.1)
      have hlt : F s < α := by
        by_contra hge
        have ha : s ∈ A := ⟨⟨hs.1.le, hsI.2⟩, le_of_not_gt hge⟩
        exact absurd (csInf_le hAb ha) (not_le.2 hs.2)
      have hP1 : transProb x (γ s) < 1 := by
        have h1 : √(transProb x (γ s)) < 1 := Real.arccos_pos.1 hpos
        simpa using (Real.sqrt_lt' one_pos).1 h1
      have hP0 : 0 < transProb x (γ s) := by
        have hlt' : fsAngle x (γ s) < Real.pi / 2 := by
          have : F s = fsAngle x (γ s) := rfl
          linarith
        have h2 : 0 < √(transProb x (γ s)) := Real.arccos_lt_pi_div_two.1 hlt'
        exact Real.sqrt_pos.1 h2
      have hmd : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) γ s := hd s hs01
      obtain ⟨f', hf', hbound⟩ := hasDerivAt_fsAngle_comp x hmd hP0 hP1
      rw [hf'.deriv]
      exact ⟨hf', hbound⟩
    have h := ofReal_two_mul_sub_le_fsPathLength h01 hsub (hFc.mono hsub) hF
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) h
    have : F t₀ = 0 := ht₀.2
    rw [this]
    have hα1 : α ≤ F t₁ := ht₁.2
    linarith
  -- from every level below `θ` to `θ` itself
  by_contra hcon
  rw [not_le] at hcon
  have hne : fsPathLength γ 0 1 ≠ ⊤ := ne_top_of_lt hcon
  have hθ0 : 0 < θ := by
    by_contra hθ
    rw [not_lt] at hθ
    have : 2 * fsAngle (γ 0) (γ 1) ≤ 0 := by
      have : fsAngle (γ 0) (γ 1) = θ := rfl
      linarith
    rw [ENNReal.ofReal_of_nonpos this] at hcon
    exact ENNReal.not_lt_zero hcon
  set L := (fsPathLength γ 0 1).toReal
  have hL : L < 2 * θ := by
    have := (ENNReal.lt_ofReal_iff_toReal_lt hne).1 hcon
    exact this
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  set α := (L / 2 + θ) / 2 with hαdef
  have hα := key α (by rw [hαdef]; positivity) (by rw [hαdef]; linarith)
  rw [ENNReal.ofReal_le_iff_le_toReal hne, hαdef] at hα
  linarith

/-- ★★★ **Every `C¹` path from `p` to `q` is at least `2 arccos √P(p, q)` long.** -/
theorem ofReal_two_mul_fsAngle_le_fsPathLength {γ : ℝ → ℙ ℂ (Ambient n)}
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) 1 γ (Icc 0 1)) :
    ENNReal.ofReal (2 * fsAngle (γ 0) (γ 1)) ≤ fsPathLength γ 0 1 :=
  ofReal_two_mul_fsAngle_le_fsPathLength_of hγ.continuousOn fun _ hs =>
    (hγ.contMDiffAt (Icc_mem_nhds hs.1 hs.2)).mdifferentiableAt one_ne_zero

/-! ### The upper bound: great circles -/

theorem fsModelMetric_smul_smul (w : Fin n → ℂ) (c : ℝ) (u : Fin n → ℂ) :
    fsModelMetric w (c • u) (c • u) = c ^ 2 * fsModelMetric w u u := by
  rw [LinearMap.map_smul₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem fsMetric_smul_smul (x : ℙ ℂ (Ambient n)) (c : ℝ) (v : TangentSpace (𝓘(ℝ, Fin n → ℂ)) x) :
    fsMetric x (c • v) (c • v) = c ^ 2 * fsMetric x v v :=
  fsModelMetric_smul_smul (chartFun (idx x) x) c v

/-- The Fubini–Study norm scales with the scalar. -/
theorem fsENormSMulClass (x : ℙ ℂ (Ambient n)) :
    ENormSMulClass ℝ (TangentSpace (𝓘(ℝ, Fin n → ℂ)) x) where
  enorm_smul c v := by
    rw [fsENorm_apply, fsENorm_apply, fsMetric_smul_smul, Real.sqrt_mul (sq_nonneg c),
      Real.sqrt_sq_eq_abs, ENNReal.ofReal_mul (abs_nonneg c), Real.enorm_eq_ofReal_abs]

attribute [local instance] fsENormSMulClass

/-- A projected curve with a smooth lift is `C¹`. -/
theorem contMDiff_projCurve {Ψ : ℝ → Ambient n} (h : ∀ t, Ψ t ≠ 0) (hΨ : ContDiff ℝ ∞ Ψ) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) 1 (projFamily Ψ h) := by
  intro t
  rw [contMDiffAt_iff]
  refine ⟨(hasMFDerivAt_projCurve h
    ((hΨ.differentiable (by simp)) t).hasDerivAt).continuousAt, ?_⟩
  have hw : (extChartAt (𝓘(ℝ, Fin n → ℂ)) (projFamily Ψ h t)) ∘ projFamily Ψ h
      ∘ (extChartAt (𝓘(ℝ, ℝ)) t).symm
      = fun y => coordRatio (idx (projFamily Ψ h t)) (Ψ y) := by
    funext y
    simp only [Function.comp, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id]
    exact chartFun_mk _ _ _
  rw [hw]
  simp only [modelWithCornersSelf_coe, range_id, extChartAt_coe, Function.comp_apply, id]
  exact ((contDiffAt_coordRatio hΨ _ (idx_ne_zero h t)).of_le (by simp)).contDiffWithinAt

/-- Inner products in an orthonormal pair with real coefficients. -/
theorem inner_orthonormal_pair {φ χ : Ambient n} (hφ : ‖φ‖ = 1) (hχ : ‖χ‖ = 1)
    (h : inner ℂ φ χ = 0) (a b a' b' : ℝ) :
    inner ℂ ((a : ℂ) • φ + (b : ℂ) • χ) ((a' : ℂ) • φ + (b' : ℂ) • χ)
      = ((a * a' + b * b' : ℝ) : ℂ) := by
  have h' : inner ℂ χ φ = 0 := by rw [← inner_conj_symm, h, map_zero]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, h, h',
    inner_self_eq_ofReal, hφ, hχ, Complex.conj_ofReal]
  push_cast
  ring

/-- ★★ **A great circle of constant speed `2θ`**: for an orthonormal pair `φ, χ`, the curve
`t ↦ [cos(tθ) φ + sin(tθ) χ]` has length `2θ` on `[0, 1]`. -/
theorem fsPathLength_greatCircle {φ χ : Ambient n} (hφ : ‖φ‖ = 1) (hχ : ‖χ‖ = 1)
    (h : inner ℂ φ χ = 0) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∃ (hne : ∀ t, ((Real.cos (t * θ) : ℂ) • φ + (Real.sin (t * θ) : ℂ) • χ) ≠ 0),
      ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) 1
          (projFamily (fun t => (Real.cos (t * θ) : ℂ) • φ + (Real.sin (t * θ) : ℂ) • χ) hne) ∧
      fsPathLength
          (projFamily (fun t => (Real.cos (t * θ) : ℂ) • φ + (Real.sin (t * θ) : ℂ) • χ) hne) 0 1
        = ENNReal.ofReal (2 * θ) := by
  set Ψ : ℝ → Ambient n := fun t => (Real.cos (t * θ) : ℂ) • φ + (Real.sin (t * θ) : ℂ) • χ
  have hnorm : ∀ t, ‖Ψ t‖ = 1 := by
    intro t
    have h1 := inner_orthonormal_pair hφ hχ h (Real.cos (t * θ)) (Real.sin (t * θ))
      (Real.cos (t * θ)) (Real.sin (t * θ))
    rw [inner_self_eq_ofReal] at h1
    have h2 : ‖Ψ t‖ ^ 2 = 1 := by
      have := Complex.ofReal_injective h1
      rw [this]
      nlinarith [Real.cos_sq_add_sin_sq (t * θ)]
    have := norm_nonneg (Ψ t)
    nlinarith
  have hne : ∀ t, Ψ t ≠ 0 := fun t h0 => by
    have := hnorm t
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  set Ψ' : ℝ → Ambient n := fun t =>
    ((-(θ * Real.sin (t * θ)) : ℝ) : ℂ) • φ + ((θ * Real.cos (t * θ) : ℝ) : ℂ) • χ
  have hd : ∀ t, HasDerivAt Ψ (Ψ' t) t := by
    intro t
    have hl : HasDerivAt (fun s : ℝ => s * θ) θ t := by
      simpa using (hasDerivAt_id t).mul_const θ
    have hc := ((Real.hasDerivAt_cos (t * θ)).comp t hl).ofReal_comp
    have hs := ((Real.hasDerivAt_sin (t * θ)).comp t hl).ofReal_comp
    have := (hc.smul_const φ).add (hs.smul_const χ)
    refine this.congr_deriv ?_
    simp only [Ψ']
    push_cast
    ring_nf
  have hΨc : ContDiff ℝ ∞ Ψ := by
    have hl : ContDiff ℝ ∞ (fun s : ℝ => s * θ) := contDiff_id.mul contDiff_const
    exact ((Complex.ofRealCLM.contDiff.comp (Real.contDiff_cos.comp hl)).smul contDiff_const).add
      ((Complex.ofRealCLM.contDiff.comp (Real.contDiff_sin.comp hl)).smul contDiff_const)
  refine ⟨hne, contMDiff_projCurve hne hΨc, ?_⟩
  rw [fsPathLength_eq]
  have hspeed : ∀ t, √(fsMetric (projFamily Ψ hne t)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) (projFamily Ψ hne) t (1 : ℝ))
      (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) (projFamily Ψ hne) t (1 : ℝ))) = 2 * θ := by
    intro t
    rw [fsMetric_mfderiv_projCurve hne (hd t)]
    have h1 : inner ℂ (Ψ' t) (Ψ' t) = ((-(θ * Real.sin (t * θ)) * -(θ * Real.sin (t * θ))
        + θ * Real.cos (t * θ) * (θ * Real.cos (t * θ)) : ℝ) : ℂ) :=
      inner_orthonormal_pair hφ hχ h _ _ _ _
    have h2 : inner ℂ (Ψ' t) (Ψ t) = ((-(θ * Real.sin (t * θ)) * Real.cos (t * θ)
        + θ * Real.cos (t * θ) * Real.sin (t * θ) : ℝ) : ℂ) :=
      inner_orthonormal_pair hφ hχ h _ _ _ _
    have h3 : inner ℂ (Ψ t) (Ψ' t) = ((Real.cos (t * θ) * -(θ * Real.sin (t * θ))
        + Real.sin (t * θ) * (θ * Real.cos (t * θ)) : ℝ) : ℂ) :=
      inner_orthonormal_pair hφ hχ h _ _ _ _
    have hsc := Real.cos_sq_add_sin_sq (t * θ)
    unfold fsInnerHom
    rw [h1, h2, h3, hnorm t]
    simp only [Complex.ofReal_re, ← Complex.ofReal_mul, one_pow, div_one]
    have : 4 * (-(θ * Real.sin (t * θ)) * -(θ * Real.sin (t * θ))
        + θ * Real.cos (t * θ) * (θ * Real.cos (t * θ))
        - (-(θ * Real.sin (t * θ)) * Real.cos (t * θ) + θ * Real.cos (t * θ) * Real.sin (t * θ))
          * (Real.cos (t * θ) * -(θ * Real.sin (t * θ))
            + Real.sin (t * θ) * (θ * Real.cos (t * θ)))) = (2 * θ) ^ 2 := by
      linear_combination (4 * θ ^ 2) * hsc
    rw [this, Real.sqrt_sq (by linarith)]
  refine (lintegral_congr fun t => congrArg ENNReal.ofReal (hspeed t)).trans ?_
  rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]

/-! ### The distance -/

theorem transProb_eq_norm_inner_normalize_sq (x y : ℙ ℂ (Ambient n)) :
    transProb x y = ‖inner ℂ (normalize x.rep) (normalize y.rep)‖ ^ 2 := by
  have hx := rep_nonzero x
  have hy := rep_nonzero y
  have hxc : ((‖x.rep‖ : ℂ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast norm_ne_zero_iff.2 hx)
  have hyc : ((‖y.rep‖ : ℂ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast norm_ne_zero_iff.2 hy)
  rw [transProb_def, ← transProbVec_smul_left hxc, ← transProbVec_smul_right hyc]
  show ‖inner ℂ (normalize x.rep) (normalize y.rep)‖ ^ 2
      / (‖normalize x.rep‖ ^ 2 * ‖normalize y.rep‖ ^ 2) = _
  rw [norm_normalize hx, norm_normalize hy]
  ring

/-- ★★★ **A great circle is a shortest path**: between any two rays there is a `C¹` path of
Fubini–Study length `2 arccos √P` (a great circle, or the constant path when the rays coincide). -/
theorem exists_fsPathLength_eq (x y : ℙ ℂ (Ambient n)) :
    ∃ γ : ℝ → ℙ ℂ (Ambient n), ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) 1 γ ∧ γ 0 = x ∧ γ 1 = y ∧
      fsPathLength γ 0 1 = ENNReal.ofReal (2 * fsAngle x y) := by
  have hx := rep_nonzero x
  have hy := rep_nonzero y
  set φ := normalize x.rep
  set ψ0 := normalize y.rep
  have hφ : ‖φ‖ = 1 := norm_normalize hx
  have hψ0 : ‖ψ0‖ = 1 := norm_normalize hy
  set a := inner ℂ φ ψ0
  set u : ℂ := Complex.exp (((-a.arg : ℝ) : ℂ) * Complex.I) with hudef
  have hu : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hua : u * a = (‖a‖ : ℂ) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I a]
    rw [hudef, mul_left_comm, ← Complex.exp_add,
      show ((-a.arg : ℝ) : ℂ) * Complex.I + (a.arg : ℂ) * Complex.I = 0 by push_cast; ring,
      Complex.exp_zero, mul_one]
  set ψ1 := u • ψ0
  have hψ1 : ‖ψ1‖ = 1 := by rw [norm_smul, hu, hψ0, one_mul]
  have hφψ1 : inner ℂ φ ψ1 = (‖a‖ : ℂ) := by
    rw [inner_smul_right, hua]
  set c := ‖a‖
  have hc1 : c ≤ 1 := by
    have := norm_inner_le_norm (𝕜 := ℂ) φ ψ0
    rwa [hφ, hψ0, one_mul] at this
  have hc0 : 0 ≤ c := norm_nonneg _
  have hθ : fsAngle x y = Real.arccos c := by
    rw [fsAngle, transProb_eq_norm_inner_normalize_sq, Real.sqrt_sq hc0]
  have hmx : mk ℂ φ (by rw [← norm_ne_zero_iff, hφ]; exact one_ne_zero) = x := by
    conv_rhs => rw [← mk_rep x]
    exact (mk_eq_mk_iff' ℂ _ _ _ hx).2 ⟨((‖x.rep‖ : ℂ))⁻¹, rfl⟩
  have hmy : mk ℂ ψ1 (by rw [← norm_ne_zero_iff, hψ1]; exact one_ne_zero) = y := by
    conv_rhs => rw [← mk_rep y]
    exact (mk_eq_mk_iff' ℂ _ _ _ hy).2 ⟨u * ((‖y.rep‖ : ℂ))⁻¹, by rw [mul_smul]; rfl⟩
  rcases hc1.lt_or_eq with hc1' | hc1'
  · -- a genuine great circle
    set θ := Real.arccos c
    have hs : 0 < Real.sin θ := Real.sin_arccos c ▸ Real.sqrt_pos.2 (by nlinarith)
    set χ := ((Real.sin θ : ℝ) : ℂ)⁻¹ • (ψ1 - (c : ℂ) • φ)
    have hua' : u * inner ℂ φ ψ0 = (c : ℂ) := hua
    have horth : inner ℂ φ χ = 0 := by
      rw [inner_smul_right, inner_sub_right, inner_smul_right, hua', inner_smul_right,
        inner_self_eq_ofReal, hφ]
      simp
    have hnorm2 : ‖ψ1 - (c : ℂ) • φ‖ = Real.sin θ := by
      have h1 : ‖ψ1 - (c : ℂ) • φ‖ ^ 2 = 1 - c ^ 2 := by
        rw [@norm_sub_sq ℂ, inner_smul_right, ← inner_conj_symm, hφψ1, Complex.conj_ofReal,
          hψ1, norm_smul, hφ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0,
          RCLike.re_to_complex, ← Complex.ofReal_mul, Complex.ofReal_re]
        ring
      have h2 : Real.sin θ ^ 2 = 1 - c ^ 2 := by
        rw [Real.sin_arccos, Real.sq_sqrt (by nlinarith)]
      have := norm_nonneg (ψ1 - (c : ℂ) • φ)
      nlinarith [hs]
    have hχ : ‖χ‖ = 1 := by
      rw [norm_smul, hnorm2, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs, inv_mul_cancel₀ hs.ne']
    obtain ⟨hne, hcm, hlen⟩ := fsPathLength_greatCircle hφ hχ horth (Real.arccos_nonneg c)
    have h0 : projFamily (fun t => (Real.cos (t * θ) : ℂ) • φ + (Real.sin (t * θ) : ℂ) • χ)
        hne 0 = x := by
      rw [← hmx]
      simp [projFamily]
    have h1 : projFamily (fun t => (Real.cos (t * θ) : ℂ) • φ + (Real.sin (t * θ) : ℂ) • χ)
        hne 1 = y := by
      rw [← hmy]
      simp only [projFamily, one_mul]
      congr 1
      rw [Real.cos_arccos (by linarith) hc1'.le, smul_smul, ← Complex.ofReal_inv,
        ← Complex.ofReal_mul, mul_inv_cancel₀ hs.ne', Complex.ofReal_one, one_smul]
      abel
    exact ⟨_, hcm, h0, h1, by rw [hlen, hθ]⟩
  · -- `c = 1`: the rays coincide
    have hxy : x = y := by
      rw [← transProb_eq_one_iff, transProb_eq_norm_inner_normalize_sq]
      show c ^ 2 = 1
      rw [hc1']
      norm_num
    subst hxy
    refine ⟨fun _ => x, contMDiff_const, rfl, rfl, ?_⟩
    rw [fsAngle_self, mul_zero, ENNReal.ofReal_zero, fsPathLength_eq]
    have h0 : ∀ t : ℝ, ENNReal.ofReal
        √(fsMetric x (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) (fun _ : ℝ => x) t (1 : ℝ))
          (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℂ)) (fun _ : ℝ => x) t (1 : ℝ))) = 0 := by
      intro t
      rw [mfderiv_const]
      show ENNReal.ofReal √(fsModelMetric (chartFun (idx x) x) 0 0) = 0
      simp
    exact (lintegral_congr h0).trans (lintegral_zero)

/-- ★★★ **The Fubini–Study distance is `2 arccos √P`**: Mathlib's Riemannian distance for the
Fubini–Study norm, between rays `p` and `q`, is twice their angle `arccos √P(p, q)`, and a great
circle attains it (`exists_fsPathLength_eq`). -/
theorem fsEDist_eq (x y : ℙ ℂ (Ambient n)) :
    fsEDist x y = ENNReal.ofReal (2 * fsAngle x y) := by
  apply le_antisymm
  · obtain ⟨γ, hγ, h0, h1, hlen⟩ := exists_fsPathLength_eq x y
    exact (Manifold.riemannianEDist_le_pathELength (I := 𝓘(ℝ, Fin n → ℂ)) hγ.contMDiffOn h0 h1
      zero_le_one).trans_eq hlen
  · -- every path is at least as long
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨γ, h0, h1, hγ, hγlt⟩ := Manifold.exists_lt_of_riemannianEDist_lt hlt
    have := ofReal_two_mul_fsAngle_le_fsPathLength hγ
    rw [h0, h1] at this
    exact absurd hγlt (not_lt.2 this)

/-- The distance is at most `π`. -/
theorem fsEDist_le_pi (x y : ℙ ℂ (Ambient n)) : fsEDist x y ≤ ENNReal.ofReal Real.pi := by
  rw [fsEDist_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith [fsAngle_le_pi_div_two x y]

/-- ★ **The distance vanishes exactly on the diagonal.** -/
theorem fsEDist_eq_zero_iff (x y : ℙ ℂ (Ambient n)) : fsEDist x y = 0 ↔ x = y := by
  rw [fsEDist_eq, ENNReal.ofReal_eq_zero]
  constructor
  · intro h
    have h0 : fsAngle x y = 0 := le_antisymm (by linarith) (fsAngle_nonneg x y)
    have h1 : √(transProb x y) = 1 := by
      have := Real.arccos_eq_zero.1 h0
      exact le_antisymm (by
        rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
        exact Real.sqrt_le_sqrt (transProbVec_le_one _ _)) this
    rw [← transProb_eq_one_iff]
    exact Real.sqrt_eq_one.1 h1
  · rintro rfl
    rw [fsAngle_self, mul_zero]

end Projectivization
