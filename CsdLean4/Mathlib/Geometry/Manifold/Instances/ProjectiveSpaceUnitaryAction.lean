/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudyForm
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Unitary
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The unitary action on `ℂℙⁿ` in charts, and the invariance of the Fubini–Study form

**TERM-SCOPE(Kahler)** — this module uses the *restricted* sense of "Kahler";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 1-Mathlib (CSD-free).

Milestone **M4** of `specs/top-power-scoping.md`, the chart half. The unitary group
`U(n+1)` acts on `ℂℙⁿ` (`Projectivization/Unitary.lean`); read from the affine chart `i` to the
affine chart `j`, a unitary `U` is the map `uTrans U i j : w ↦ coordRatio j (U (insertOne i w))`,
a linear-fractional map, holomorphic wherever the `j`-th coordinate of `U (insertOne i w)` does
not vanish. Under it the Fubini–Study potential shifts by `-2 log ‖·‖` of that coordinate — an
affine, hence pluriharmonic, correction — so the chart form is invariant:

* `Kahler.ddcForm_log_norm_eq_zero_of_holomorphic` — `log ‖f‖` is pluriharmonic off the zeros
  of a holomorphic `f` (the linear case `ddcForm_log_norm_eq_zero` of
  `KahlerPluriharmonic.lean`, with `L` replaced by any holomorphic `f`; this is what lets the
  affine coordinate of the unitary action be handled);
* `norm_toEuclideanLinearEquiv` — a unitary preserves the Euclidean norm;
* `uTrans`, `uTransE` — the chart expression of the action; `smul_chartInv`,
  `chartFun_smul_chartInv` — it is what the action does to a chart inverse;
  `contDiffOn_uTrans`, `contDiffAt_uTransE` — holomorphy on its domain;
* `fsPotential_uTransE` — the potential's pluriharmonic shift;
* ★★ `fsChartForm_uTransE` — **the Fubini–Study chart form is invariant under the unitary
  action**, read from chart `i` to chart `j`: `(U^* ω_j) = ω_i` on the overlap;
* ★★ `fsModelForm_uTrans` — the same on the `Fin n → ℂ` model the manifold is charted on.

## Honest scope

⚠️ Chart statements only. The manifold-level statement "`fsForm` is `U(n+1)`-invariant" is
consumed directly in this chart form by the volume-invariance argument
(`Instances/ProjectiveSpaceFubiniStudyVolume.lean`); no pullback of forms along maps of manifolds
is defined here (that general API is not built).

⚠️ The `j = i` case of the chart transition needed a case split in `fsChartForm_transE`; the
holomorphic-`f` formulation of pluriharmonicity removes it here.

References: `specs/top-power-scoping.md` (M4);
`Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudy.lean` (the chart-transition invariance
this mirrors); `Analysis/InnerProductSpace/KahlerPluriharmonic.lean`;
`LinearAlgebra/Projectivization/Unitary.lean` (the action); `specs/future-work.md`.
-/

@[expose] public section

open Bundle Filter Topology
open scoped Manifold Bundle Topology ContDiff LinearAlgebra.Projectivization


namespace Kahler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `log ‖f‖` is pluriharmonic off the zeros of a holomorphic `f`. -/
theorem ddcForm_log_norm_eq_zero_of_holomorphic {f : E → ℂ} {x : E} (hf : ContDiffAt ℂ ω f x)
    (hx : f x ≠ 0) : ddcForm (fun w => Real.log ‖f w‖) x = 0 := by
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hx with h | h
  · have hlog : ContDiffAt ℂ ω (fun w => Complex.log (f w)) x :=
      (Complex.contDiffAt_log h).comp x hf
    have : (fun w => Real.log ‖f w‖) = fun w => (Complex.log (f w)).re := by
      funext w; rw [Complex.log_re]
    rw [this]; exact ddcForm_re_eq_zero hlog
  · have hneg : ContDiffAt ℂ ω (fun w => -f w) x := hf.neg
    have hlog : ContDiffAt ℂ ω (fun w => Complex.log (-f w)) x :=
      ContDiffAt.comp (g := Complex.log) x (Complex.contDiffAt_log h) hneg
    have : (fun w => Real.log ‖f w‖) = fun w => (Complex.log (-f w)).re := by
      funext w; rw [Complex.log_re, norm_neg]
    rw [this]; exact ddcForm_re_eq_zero hlog

end Kahler

namespace Projectivization

open Kahler Matrix.UnitaryGroup

variable {n : ℕ}

/-- A unitary matrix preserves the Euclidean norm. -/
theorem norm_toEuclideanLinearEquiv (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (v : Ambient n) :
    ‖toEuclideanLinearEquiv U v‖ = ‖v‖ := by
  have hinner : inner ℂ (toEuclideanLinearEquiv U v) (toEuclideanLinearEquiv U v) = inner ℂ v v := by
    rw [toEuclideanLinearEquiv_apply, ← LinearMap.adjoint_inner_right,
      ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, ← LinearMap.comp_apply,
      ← Matrix.toLpLin_mul_same, ← Matrix.star_eq_conjTranspose,
      Matrix.UnitaryGroup.star_mul_self, Matrix.toLpLin_one, LinearMap.id_apply]
  have h1 := norm_sq_eq_re_inner (𝕜 := ℂ) (toEuclideanLinearEquiv U v)
  have h2 := norm_sq_eq_re_inner (𝕜 := ℂ) v
  rw [hinner] at h1
  have := h1.trans h2.symm
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

/-- The chart expression of the unitary action, from chart `i` to chart `j`, on the `Pi` model. -/
noncomputable def uTrans (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (i j : Fin (n + 1)) :
    (Fin n → ℂ) → (Fin n → ℂ) :=
  fun w => coordRatio j (toEuclideanLinearEquiv U (insertOne i w))

/-- The same on the Euclidean model. -/
noncomputable def uTransE (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (i j : Fin (n + 1)) :
    EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) :=
  fun z => WithLp.toLp 2 (uTrans U i j (WithLp.ofLp z))

theorem uTransE_eq (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (i j : Fin (n + 1)) :
    uTransE (n := n) U i j
      = toLpCLM ∘ uTrans U i j ∘ (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)) := by
  funext z; rfl

/-- The action on a chart inverse. -/
theorem smul_chartInv (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (i : Fin (n + 1)) (w : Fin n → ℂ) :
    U • chartInv i w
      = mk ℂ (toEuclideanLinearEquiv U (insertOne i w))
          ((toEuclideanLinearEquiv U).map_ne_zero_iff.2 (insertOne_ne_zero i w)) := by
  show mapEquiv (toEuclideanLinearEquivHom U) (mk ℂ (insertOne i w) _) = _
  rw [mapEquiv, Projectivization.map_mk]
  rfl

theorem chartFun_smul_chartInv (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (i j : Fin (n + 1))
    (w : Fin n → ℂ) :
    chartFun j (U • chartInv i w) = uTrans U i j w := by
  rw [smul_chartInv, chartFun_mk]
  rfl

/-- The coordinates of `U (insertOne i w)` are holomorphic (affine) in `w`. -/
theorem contDiff_uAct_coord (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (i k : Fin (n + 1)) :
    ContDiff ℂ ω (fun w : Fin n → ℂ => toEuclideanLinearEquiv U (insertOne i w) k) := by
  have h : (fun w : Fin n → ℂ => toEuclideanLinearEquiv U (insertOne i w) k)
      = fun w => ∑ l, (U.val : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) k l * insertOne i w l := by
    funext w
    simp [toEuclideanLinearEquiv_apply, Matrix.mulVec, dotProduct, insertOne]
  rw [h]
  exact ContDiff.sum fun l _ => contDiff_const.mul (contDiff_insertOne_coord i l)

theorem contDiffOn_uTrans (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (i j : Fin (n + 1)) :
    ContDiffOn ℂ ω (uTrans U i j)
      {w : Fin n → ℂ | toEuclideanLinearEquiv U (insertOne i w) j ≠ 0} := by
  refine contDiffOn_pi.2 fun k => ?_
  exact ContDiffOn.div (contDiff_uAct_coord U i _).contDiffOn
    (contDiff_uAct_coord U i j).contDiffOn fun w hw => hw

theorem isOpen_uDomain (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (i j : Fin (n + 1)) :
    IsOpen {w : Fin n → ℂ | toEuclideanLinearEquiv U (insertOne i w) j ≠ 0} :=
  isOpen_ne_fun ((contDiff_uAct_coord U i j).continuous) continuous_const

theorem contDiffAt_uTransE (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (i j : Fin (n + 1))
    {z : EuclideanSpace ℂ (Fin n)} (hz : toEuclideanLinearEquiv U (insertOne i (WithLp.ofLp z)) j ≠ 0) :
    ContDiffAt ℂ ⊤ (uTransE U i j) z := by
  have h1 : ContDiffAt ℂ ⊤ (uTrans U i j) (WithLp.ofLp z) :=
    ((contDiffOn_uTrans U i j).contDiffAt ((isOpen_uDomain U i j).mem_nhds hz)).of_le le_top
  exact (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.contDiff.contDiffAt.comp z
    (h1.comp z (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).contDiff.contDiffAt)

/-- The potential transforms by a pluriharmonic correction under the unitary action. -/
theorem fsPotential_uTransE (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (i j : Fin (n + 1))
    {z : EuclideanSpace ℂ (Fin n)} (hz : toEuclideanLinearEquiv U (insertOne i (WithLp.ofLp z)) j ≠ 0) :
    fsPotential (uTransE U i j z)
      = fsPotential z - 2 * Real.log ‖toEuclideanLinearEquiv U (insertOne i (WithLp.ofLp z)) j‖ := by
  rw [uTransE, uTrans, fsPotential_toLp_coordRatio j _ hz, norm_toEuclideanLinearEquiv,
    norm_sq_insertOne, ← EuclideanSpace.norm_sq_eq]
  rfl

/-- ★ **Invariance of the Fubini–Study chart form under the unitary action**, in charts. -/
theorem fsChartForm_uTransE (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (i j : Fin (n + 1))
    {z : EuclideanSpace ℂ (Fin n)} (hz : toEuclideanLinearEquiv U (insertOne i (WithLp.ofLp z)) j ≠ 0) :
    (fsChartForm (uTransE U i j z)).compContinuousLinearMap (fderiv ℝ (uTransE U i j) z)
      = fsChartForm z := by
  have hcomp := ddcForm_comp (K := fsPotential (E := EuclideanSpace ℂ (Fin n))) (τ := uTransE U i j)
    contDiff_fsPotential (contDiffAt_uTransE U i j hz)
  rw [show fsChartForm (uTransE U i j z) = ddcForm fsPotential (uTransE U i j z) from rfl, ← hcomp]
  set f : EuclideanSpace ℂ (Fin n) → ℂ := fun y => toEuclideanLinearEquiv U (insertOne i (WithLp.ofLp y)) j
    with hfdef
  have hfC : ContDiffAt ℂ ⊤ f z :=
    ((contDiff_uAct_coord U i j).of_le le_top).contDiffAt.comp z
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).contDiff.contDiffAt
  have hz' : f z ≠ 0 := hz
  have hfcont : Continuous f :=
    (contDiff_uAct_coord U i j).continuous.comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).continuous
  have hopen : IsOpen {y : EuclideanSpace ℂ (Fin n) | f y ≠ 0} :=
    isOpen_ne_fun hfcont continuous_const
  have hev : (fsPotential ∘ uTransE U i j) =ᶠ[𝓝 z]
      (fsPotential - (2 : ℝ) • fun y : EuclideanSpace ℂ (Fin n) => Real.log ‖f y‖) := by
    filter_upwards [hopen.mem_nhds hz'] with y hy
    simp only [Function.comp_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      fsPotential_uTransE U i j hy, hfdef]
  have hfR : ContDiffAt ℝ ⊤ f z := hfC.restrict_scalars ℝ
  have hnorm : ContDiffAt ℝ ⊤ (fun y : EuclideanSpace ℂ (Fin n) => ‖f y‖) z :=
    ContDiffAt.norm ℝ hfR hz'
  have hlog : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℂ (Fin n) => Real.log ‖f y‖) z := by
    have := (Real.contDiffAt_log (n := 2).2 (norm_ne_zero_iff.2 hz')).comp z (hnorm.of_le le_top)
    simpa [Function.comp_def] using this
  have h₂ : ContDiffAt ℝ 2 ((2 : ℝ) • fun y : EuclideanSpace ℂ (Fin n) => Real.log ‖f y‖) z := by
    rw [Pi.smul_def]; exact hlog.const_smul 2
  rw [ddcForm_congr hev,
    ddcForm_sub' (contDiff_fsPotential.contDiffAt.of_le (by norm_cast)) h₂,
    ddcForm_const_smul' 2 hlog, ddcForm_log_norm_eq_zero_of_holomorphic hfC hz', smul_zero,
    sub_zero]
  rfl

/-- ★ **Invariance of the Fubini–Study model form under the unitary action**, on the `Pi` model. -/
theorem fsModelForm_uTrans (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (i j : Fin (n + 1))
    {w : Fin n → ℂ} (hw : toEuclideanLinearEquiv U (insertOne i w) j ≠ 0) :
    (fsModelForm (uTrans U i j w)).compContinuousLinearMap (fderiv ℝ (uTrans U i j) w)
      = fsModelForm w := by
  set e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ) with he
  have hz : toEuclideanLinearEquiv U (insertOne i (WithLp.ofLp (toLpCLM w))) j ≠ 0 := by simpa using hw
  have hinv := fsChartForm_uTransE U i j hz
  have hP : DifferentiableAt ℝ (uTrans U i j) w := by
    have := ((contDiffOn_uTrans U i j).contDiffAt ((isOpen_uDomain U i j).mem_nhds hw)).restrict_scalars ℝ
    exact this.differentiableAt (by simp)
  have hew : e (toLpCLM w) = w := e.apply_symm_apply w
  have hd : fderiv ℝ (uTransE U i j) (toLpCLM w)
      = (toLpCLM : (Fin n → ℂ) →L[ℝ] _).comp ((fderiv ℝ (uTrans U i j) w).comp (e : _ →L[ℝ] _)) := by
    rw [uTransE_eq]
    have h1 : HasFDerivAt (e : EuclideanSpace ℂ (Fin n) → (Fin n → ℂ)) (e : _ →L[ℝ] _) (toLpCLM w) :=
      e.hasFDerivAt
    have h2 : HasFDerivAt (uTrans U i j) (fderiv ℝ (uTrans U i j) w) (e (toLpCLM w)) := by
      rw [hew]; exact hP.hasFDerivAt
    have h3 : HasFDerivAt (toLpCLM : (Fin n → ℂ) → EuclideanSpace ℂ (Fin n)) toLpCLM
        ((uTrans U i j ∘ e) (toLpCLM w)) := (toLpCLM : (Fin n → ℂ) →L[ℝ] _).hasFDerivAt
    exact (h3.comp (toLpCLM w) (h2.comp (toLpCLM w) h1)).fderiv
  have hval : uTransE U i j (toLpCLM w) = toLpCLM (uTrans U i j w) := rfl
  rw [hval, hd] at hinv
  ext v
  have := congrArg (fun α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ =>
    α (fun k => toLpCLM (v k))) hinv
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Function.comp_def] at this
  simp only [fsModelForm, toLpCLM, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe, Function.comp_def,
    PiLp.continuousLinearEquiv_symm_apply] at this ⊢
  exact this

end Projectivization
