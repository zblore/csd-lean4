/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpace
public import CsdLean4.Mathlib.Analysis.InnerProductSpace.KahlerPluriharmonic

/-!
# The Fubini–Study chart form is invariant under the chart transitions of `ℂℙⁿ`

**TERM-SCOPE(Kahler)** — this module uses the *restricted* sense of "Kahler";
the source repository's terms register records what is backed and what is not.

**Category:** 1-Mathlib (CSD-free).

The mathematical heart of "the Fubini–Study form is a global object on `ℂℙⁿ`". The chart form
`fsChartForm = dd^c log(1 + ‖z‖²)` (`KahlerPotential.lean`) is defined chart by chart; this
module proves that the affine-chart transitions of `ProjectiveSpace.lean` carry the form in
chart `j` to the form in chart `i`:

* `fsPotential_transE` — under the transition `i → j` the potential changes by `-2 log ‖zⱼ‖`,
  a pluriharmonic correction (the classical `1 + ‖τ z‖² = (1 + ‖z‖²)/‖zⱼ‖²`);
* ★★ `fsChartForm_transE` — hence the **form** is invariant, `τ^* ω_j = ω_i` on the overlap:
  `dd^c` naturality (`ddcForm_comp`), linearity in the potential, and pluriharmonicity of
  `log ‖L ·‖` for the coordinate functional `L` (`ddcForm_log_norm_eq_zero`); the `j = i`
  case is the identity transition;
* ★ `fsModelForm_transP` — the same on the `Fin n → ℂ` model the manifold is charted on, the
  form a bundle argument consumes.

## Honest scope

Invariance of a family of **flat** forms under **flat** maps — exactly what assembling a
global section of the alternating bundle on `ℂℙⁿ` needs; that assembly (the bundle-level
local-representative identity and the section's smoothness) is `ProjectiveSpaceFubiniStudyForm.lean`
(`fsForm`). Still no exterior derivative on the manifold (step (2b)): nothing here states
`dω = 0` on `ℂℙⁿ`.

**Provenance and references.** `KahlerPotential.lean`; `KahlerPluriharmonic.lean`;
`Geometry/Manifold/Instances/ProjectiveSpace.lean`;
`Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudyForm.lean` (the consumer);
the completed-work ledger.
-/

@[expose] public section
open Filter Topology

namespace Kahler
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- L3: `dd^c` only sees the potential near the point. -/
theorem ddcForm_congr {K₁ K₂ : E → ℝ} {x : E} (h : K₁ =ᶠ[𝓝 x] K₂) :
    ddcForm K₁ x = ddcForm K₂ x := by
  have hd : dcForm K₁ =ᶠ[𝓝 x] dcForm K₂ := by
    filter_upwards [h.eventually_nhds] with y hy
    ext v
    simp [dcForm_apply, Filter.EventuallyEq.fderiv_eq hy]
  rw [ddcForm, ddcForm, Filter.EventuallyEq.extDeriv_eq hd]
end Kahler

namespace Projectivization
open Kahler
variable {n : ℕ}

/-- The chart transition `i → j`, read on the Euclidean model. -/
noncomputable def transE (i j : Fin (n + 1)) : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) :=
  fun z => WithLp.toLp 2 (coordRatio j (insertOne i (WithLp.ofLp z)))

lemma norm_sq_insertOne (i : Fin (n + 1)) (w : Fin n → ℂ) :
    ‖insertOne i w‖ ^ 2 = 1 + ∑ k, ‖w k‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succAbove _ i]
  simp [insertOne_apply_same, insertOne_apply_succAbove]

lemma norm_sq_toLp_coordRatio (j : Fin (n + 1)) (v : Ambient n) :
    ‖(WithLp.toLp 2 (coordRatio j v) : EuclideanSpace ℂ (Fin n))‖ ^ 2 = (‖v‖ ^ 2 - ‖v j‖ ^ 2) / ‖v j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq (x := v), Fin.sum_univ_succAbove _ j]
  simp only [coordRatio, norm_div, div_pow]
  rw [← Finset.sum_div]
  congr 1
  ring

lemma fsPotential_toLp_coordRatio (j : Fin (n + 1)) (v : Ambient n) (hv : v j ≠ 0) :
    Kahler.fsPotential (WithLp.toLp 2 (coordRatio j v) : EuclideanSpace ℂ (Fin n))
      = Real.log (‖v‖ ^ 2) - 2 * Real.log ‖v j‖ := by
  have hj : 0 < ‖v j‖ := norm_pos_iff.2 hv
  have hv0 : 0 < ‖v‖ ^ 2 := by
    have : v ≠ 0 := fun h => hv (by simp [h])
    positivity
  rw [Kahler.fsPotential, norm_sq_toLp_coordRatio j v]
  have : 1 + (‖v‖ ^ 2 - ‖v j‖ ^ 2) / ‖v j‖ ^ 2 = ‖v‖ ^ 2 / ‖v j‖ ^ 2 := by
    field_simp
    ring
  rw [this, Real.log_div hv0.ne' (by positivity), Real.log_pow ‖v j‖ 2]
  push_cast; ring

lemma contDiffAt_transE (i j : Fin (n + 1)) {z : EuclideanSpace ℂ (Fin n)} (hz : insertOne i (WithLp.ofLp z) j ≠ 0) :
    ContDiffAt ℂ ⊤ (transE i j) z := by
  have hopen : IsOpen {w : Fin n → ℂ | insertOne i w j ≠ 0} :=
    isOpen_ne_fun (by fun_prop : Continuous fun w : Fin n → ℂ => insertOne i w j) continuous_const
  have h1 : ContDiffAt ℂ ⊤ (fun w : Fin n → ℂ => coordRatio j (insertOne i w)) (WithLp.ofLp z) :=
    ((contDiffOn_transition i j).contDiffAt (hopen.mem_nhds hz)).of_le le_top
  exact (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.contDiff.contDiffAt.comp z
    (h1.comp z (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).contDiff.contDiffAt)

/-- L1: the transition from a chart to itself is the identity. -/
lemma coordRatio_insertOne_self (i : Fin (n + 1)) (w : Fin n → ℂ) :
    coordRatio i (insertOne i w) = w := by
  funext k
  simp [coordRatio, insertOne_apply_same, insertOne_apply_succAbove]

lemma transE_self (i : Fin (n + 1)) : transE (n := n) i i = id := by
  funext z
  simp [transE, coordRatio_insertOne_self]

/-- L4: the potential transforms by a pluriharmonic correction. -/
lemma fsPotential_transE (i j : Fin (n + 1)) {z : EuclideanSpace ℂ (Fin n)}
    (hz : insertOne i (WithLp.ofLp z) j ≠ 0) :
    Kahler.fsPotential (transE i j z)
      = Kahler.fsPotential z - 2 * Real.log ‖insertOne i (WithLp.ofLp z) j‖ := by
  rw [transE, fsPotential_toLp_coordRatio j _ hz, norm_sq_insertOne, ← EuclideanSpace.norm_sq_eq]
  rfl




/-- ★ L5: **chart invariance of the Fubini–Study form.** The pullback of the chart-`j` form along
the transition from chart `i` is the chart-`i` form, wherever the transition is defined. -/
theorem fsChartForm_transE (i j : Fin (n + 1)) {z : EuclideanSpace ℂ (Fin n)}
    (hz : insertOne i (WithLp.ofLp z) j ≠ 0) :
    (fsChartForm (transE i j z)).compContinuousLinearMap (fderiv ℝ (transE i j) z)
      = fsChartForm z := by
  have hcomp := ddcForm_comp (K := fsPotential (E := EuclideanSpace ℂ (Fin n))) (τ := transE i j) contDiff_fsPotential
    (contDiffAt_transE i j hz)
  rw [show fsChartForm (transE i j z) = ddcForm fsPotential (transE i j z) from rfl, ← hcomp]
  by_cases hij : j = i
  · subst hij
    rw [transE_self, Function.comp_id]
    rfl
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij
    set L : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ := EuclideanSpace.proj k with hLdef
    have hL : ∀ y : EuclideanSpace ℂ (Fin n), L y = insertOne i (WithLp.ofLp y) j := by
      intro y; rw [← hk]; simp [hLdef, insertOne_apply_succAbove]
    have hz' : L z ≠ 0 := by rw [hL]; exact hz
    have hopen : IsOpen {y : EuclideanSpace ℂ (Fin n) | L y ≠ 0} := isOpen_ne_fun L.continuous continuous_const
    have hev : (fsPotential ∘ transE i j) =ᶠ[𝓝 z]
        (fsPotential - (2 : ℝ) • fun y : EuclideanSpace ℂ (Fin n) => Real.log ‖L y‖) := by
      filter_upwards [hopen.mem_nhds hz'] with y hy
      have hy' : insertOne i (WithLp.ofLp y) j ≠ 0 := by rw [← hL]; exact hy
      simp only [Function.comp_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        fsPotential_transE i j hy', hL]
    have hLR : ContDiffAt ℝ ⊤ (fun y : EuclideanSpace ℂ (Fin n) => L y) z :=
      (L.restrictScalars ℝ).contDiff.contDiffAt
    have hnorm : ContDiffAt ℝ ⊤ (fun y : EuclideanSpace ℂ (Fin n) => ‖L y‖) z :=
      ContDiffAt.norm ℝ hLR hz'
    have hlog : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℂ (Fin n) => Real.log ‖L y‖) z := by
      have := (Real.contDiffAt_log (n := 2).2 (norm_ne_zero_iff.2 hz')).comp z (hnorm.of_le le_top)
      simpa [Function.comp_def] using this
    have h₂ : ContDiffAt ℝ 2 ((2 : ℝ) • fun y : EuclideanSpace ℂ (Fin n) => Real.log ‖L y‖) z := by
      rw [Pi.smul_def]; exact hlog.const_smul 2
    rw [ddcForm_congr hev,
      ddcForm_sub' (contDiff_fsPotential.contDiffAt.of_le (by norm_cast)) h₂,
      ddcForm_const_smul' 2 hlog, ddcForm_log_norm_eq_zero L hz', smul_zero, sub_zero]
    rfl


/-! ### The form on the `Fin n → ℂ` model, and its invariance there -/

/-- The Euclidean structure map, as an `ℝ`-continuous-linear map from the `Pi` model. -/
noncomputable abbrev toLpCLM : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap

/-- The Fubini–Study chart form transported to the `Fin n → ℂ` model. -/
noncomputable def fsModelForm (w : Fin n → ℂ) : (Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ :=
  (fsChartForm (toLpCLM w)).compContinuousLinearMap toLpCLM

/-- The `Pi`-model transition. -/
noncomputable def transP (i j : Fin (n + 1)) : (Fin n → ℂ) → (Fin n → ℂ) :=
  fun w => coordRatio j (insertOne i w)

lemma transE_eq (i j : Fin (n + 1)) :
    transE (n := n) i j = toLpCLM ∘ transP i j ∘ (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)) := by
  funext z; rfl

/-- ★ B3c-1: **chart invariance on the `Pi` model.** -/
theorem fsModelForm_transP (i j : Fin (n + 1)) {w : Fin n → ℂ} (hw : insertOne i w j ≠ 0) :
    (fsModelForm (transP i j w)).compContinuousLinearMap (fderiv ℝ (transP i j) w)
      = fsModelForm w := by
  set e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ) with he
  have hz : insertOne i (WithLp.ofLp (toLpCLM w)) j ≠ 0 := by simpa using hw
  have hinv := fsChartForm_transE i j hz
  have hopen : IsOpen {w : Fin n → ℂ | insertOne i w j ≠ 0} :=
    isOpen_ne_fun (by fun_prop : Continuous fun w : Fin n → ℂ => insertOne i w j) continuous_const
  have hP : DifferentiableAt ℝ (transP i j) w := by
    have := ((contDiffOn_transition i j).contDiffAt (hopen.mem_nhds hw)).restrict_scalars ℝ
    exact this.differentiableAt (by simp)
  -- fderiv of transE = toLpCLM ∘L fderiv transP ∘L e, at the point toLpCLM w (where e ∘ toLpCLM = id)
  have hew : e (toLpCLM w) = w := e.apply_symm_apply w
  have hd : fderiv ℝ (transE i j) (toLpCLM w)
      = (toLpCLM : (Fin n → ℂ) →L[ℝ] _).comp ((fderiv ℝ (transP i j) w).comp (e : _ →L[ℝ] _)) := by
    rw [transE_eq]
    have h1 : HasFDerivAt (e : EuclideanSpace ℂ (Fin n) → (Fin n → ℂ)) (e : _ →L[ℝ] _) (toLpCLM w) :=
      e.hasFDerivAt
    have h2 : HasFDerivAt (transP i j) (fderiv ℝ (transP i j) w) (e (toLpCLM w)) := by
      rw [hew]; exact hP.hasFDerivAt
    have h3 : HasFDerivAt (toLpCLM : (Fin n → ℂ) → EuclideanSpace ℂ (Fin n)) toLpCLM
        ((transP i j ∘ e) (toLpCLM w)) := (toLpCLM : (Fin n → ℂ) →L[ℝ] _).hasFDerivAt
    exact (h3.comp (toLpCLM w) (h2.comp (toLpCLM w) h1)).fderiv
  have hval : transE i j (toLpCLM w) = toLpCLM (transP i j w) := rfl
  rw [hval, hd] at hinv
  have hew' : ∀ x : Fin n → ℂ, e (toLpCLM x) = x := fun x => e.apply_symm_apply x
  ext v
  have := congrArg (fun ω : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ =>
    ω (fun k => toLpCLM (v k))) hinv
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Function.comp_def] at this
  simp only [fsModelForm, toLpCLM, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe, Function.comp_def,
    PiLp.continuousLinearEquiv_symm_apply] at this ⊢
  exact this

end Projectivization
