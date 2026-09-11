/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudyForm
public import CsdLean4.Mathlib.Geometry.Manifold.SymplecticForm
public import CsdLean4.Mathlib.Geometry.Manifold.HamiltonianVectorField
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudyMass

/-!
# `ℂℙⁿ` with the Fubini–Study form is a symplectic manifold

**TERM-SCOPE(Kahler)** — this module uses the *restricted* sense of "Kahler";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 1-Mathlib-staging (CSD-free; upstream target `Mathlib.Geometry.Manifold`).

**Glossary:** https://glossary.constraintsurfacedynamics.com/kahler-form/
Plain-language, CSD-role and formal statements of the Kahler form, with
this module as its Lean anchor (`fsForm_isKahler`). Kept symmetric by `scripts/check-glossary.sh`.

`ProjectiveSpaceFubiniStudyForm.lean` built the Fubini–Study form `fsForm` as a `C^∞` global
2-form on `ℂℙⁿ` and proved it closed (`fsForm_mextDeriv`). This module proves it
**non-degenerate at every point** and concludes that `ℂℙⁿ` is a symplectic manifold:

* `Kahler.metric_mul_fundamentalForm_complexStructure_sub` — the taming bracket of the chart
  form's components, `g(x,v) ω(x,Jv) − g(x,Jv) ω(x,v) = |⟪x,v⟫|²`;
* `Kahler.fsChartForm_apply_complexStructure` — hence
  `fsChartForm x (v, Jv) = -4 (1+‖x‖²)⁻² ((1+‖x‖²) ‖v‖² − |⟪x,v⟫|²)` at every chart point;
* ★ `Kahler.fsChartForm_complexStructure_self_neg` — **taming at every chart point**: for
  `v ≠ 0` that value is negative, by Cauchy–Schwarz (`|⟪x,v⟫|² ≤ ‖x‖² ‖v‖² < (1+‖x‖²) ‖v‖²`).
  At the origin it is `-4 ‖v‖²`, the flat taming identity `fundamentalForm_complexStructure_self`
  scaled by the normalisation of `fsChartForm_zero`;
* ★★ `fsForm_nondegenerate` — **non-degeneracy of the Fubini–Study form at every point of
  `ℂℙⁿ`**: the section at `x` is the model form at `x`'s own chart coordinate, so the witness is
  `i • v` in the model;
* ★★★ `fsForm_isSymplectic` — **`ℂℙⁿ` with the Fubini–Study form is a symplectic manifold**
  (`DifferentialForm.IsSymplectic`: closed by `fsForm_mextDeriv`, non-degenerate by
  `fsForm_nondegenerate`). Real dimension `2n`, even, as the word requires;
* **G7 (2026-09-09).** `fsJ` (`J = i·` on each tangent space), `fsJ_fsJ` (`J² = -1`), ★
  `fsForm_smul_I_smul_I` (`ω` is `J`-invariant, a `(1,1)`-form), and ★★ `fsForm_isAlmostKahler` —
  **`ℂℙⁿ` with the Fubini–Study form and `J = i·` is almost Kähler**
  (`DifferentialForm.IsAlmostKahler`: symplectic, `J² = -1`, `J`-invariant, `J`-tamed), with the
  compatible metric `g = ω (J ·, ·)` positive definite (`fsForm_metric_self_pos`); and ★
  `fderiv_chart_transition_smul_I` / `fsJ_symmL` — **`J` is the complex structure of the atlas**:
  the chart transitions are holomorphic (`contDiffOn_uTrans`), so their derivatives are
  `ℂ`-linear and `J = i·` reads as `i·` in every chart;
* **G14a (2026-09-10).** `modelJ` (`i·` on the model as a real-linear map) and ★★★ `fsForm_isKahler`
  — **`ℂℙⁿ` with the Fubini–Study form and `J = i·` is a Kähler manifold**
  (`DifferentialForm.IsKahler`: almost Kähler, and `J` is the complex structure of the holomorphic
  atlas, by `fsJ_symmL`);
* **G15 (2026-09-10).** `fsJL` (`J = i·` as a continuous linear map on each tangent space) and ★★
  `contMDiff_fsJL` — **`J` is a `C^∞` section of `Hom(TM, TM)`**, constant `i·` in every chart;
* **G14b (2026-09-10).** ★★ `nijenhuis_fsJ_eq_zero` — **the Nijenhuis tensor of `J = i·` vanishes**
  (`IsKahler.nijenhuis_eq_zero` on `fsForm_isKahler`): `ℂℙⁿ` is Kähler in the tensor sense too.

## Honest scope

⚠️ **Kähler in the atlas sense.** `fsForm_isKahler` packages symplectic + compatible `J` + `J` is
the complex structure of the holomorphic atlas (`fsJ_symmL`, `fderiv_chart_transition_smul_I`),
which is the textbook definition. The tensor formulation of integrability (a vanishing Nijenhuis
tensor) is `nijenhuis_fsJ_eq_zero` (G14b). `J` as a smooth section of the endomorphism bundle is
`contMDiff_fsJL` (G15), for the linear-map version `fsJL` of `fsJ`. The pointwise triple
`IsFubiniStudyKahler` on the flat model is the origin's case.

⚠️ **No volume.** Non-degeneracy plus closedness does not produce the top-power identity
`ωⁿ/n! = μ_FS`; that is step (3), top forms → measures, and is not attempted.

⚠️ **Sign convention.** With `fsChartForm = dd^c log(1+‖z‖²)` the taming value `ω (v, J v)` is
negative (`-4` at the origin); the almost Kähler predicate absorbs it by the metric convention
`g = ω (J ·, ·)`, so `ω (J v, v) > 0`. Nothing downstream depends on the sign, only on
non-vanishing.

References: `Geometry/Manifold/SymplecticForm.lean` (the predicate);
`Geometry/Manifold/HamiltonianVectorField.lean` (`IsAlmostKahler`, `apply_swap`);
`Instances/ProjectiveSpaceUnitaryAction.lean` (`contDiffOn_uTrans`, `chartFun_smul_chartInv`);
`Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudyForm.lean` (`fsForm`, `fsForm_mextDeriv`);
`Analysis/InnerProductSpace/KahlerPotential.lean` (`fsChartForm_apply`);
`Analysis/InnerProductSpace/KahlerForm.lean` (the taming identity, `complexStructure`);
`MATHLIB-GAPS.md` (Kahler / symplectic manifold API); `specs/BACKLOG.md` (XL, "Manifold
exterior calculus"); `specs/TERMS.md` ("symplectic / manifold"); `specs/future-work.md`.
-/

@[expose] public section

open Bundle Filter Topology
open scoped Manifold Bundle Topology ContDiff LinearAlgebra.Projectivization

namespace Kahler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The taming bracket of the Fubini–Study chart-form components:
`g(x,v) ω(x,Jv) − g(x,Jv) ω(x,v) = |⟪x,v⟫|²`. -/
theorem metric_mul_fundamentalForm_complexStructure_sub (x v : E) :
    metric x v * fundamentalForm x (complexStructure v)
      - metric x (complexStructure v) * fundamentalForm x v
      = Complex.normSq (inner ℂ x v) := by
  have h1 : fundamentalForm x (complexStructure v) = metric x v :=
    (metric_eq_fundamentalForm_complexStructure x v).symm
  have h2 : metric x (complexStructure v) = - fundamentalForm x v := by
    rw [metric_eq_fundamentalForm_complexStructure, complexStructure_involutive]
    simp [fundamentalForm, inner_neg_right]
  rw [h1, h2]
  simp only [metric, fundamentalForm, Complex.normSq_apply]
  ring

/-- Taming at every chart point:
`fsChartForm x (v, Jv) = -4 (1+‖x‖²)⁻² ((1+‖x‖²) ‖v‖² − |⟪x,v⟫|²)`. -/
theorem fsChartForm_apply_complexStructure (x v : E) :
    fsChartForm x ![v, complexStructure v]
      = -4 * (1 + ‖x‖ ^ 2)⁻¹ ^ 2 * ((1 + ‖x‖ ^ 2) * ‖v‖ ^ 2 - Complex.normSq (inner ℂ x v)) := by
  rw [fsChartForm_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fundamentalForm_complexStructure_self, metric_mul_fundamentalForm_complexStructure_sub]
  have h : (1 + ‖x‖ ^ 2) ≠ 0 := by positivity
  field_simp

/-- ★ **Taming at every chart point**: for `v ≠ 0`, `fsChartForm x (v, Jv) < 0`
(Cauchy–Schwarz: `|⟪x,v⟫|² ≤ ‖x‖² ‖v‖² < (1+‖x‖²) ‖v‖²`). -/
theorem fsChartForm_complexStructure_self_neg (x : E) {v : E} (hv : v ≠ 0) :
    fsChartForm x ![v, complexStructure v] < 0 := by
  rw [fsChartForm_apply_complexStructure]
  have hv' : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv) 2
  have hcs : Complex.normSq (inner ℂ x v) ≤ ‖x‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm x v) 2
  have hpos : 0 < (1 + ‖x‖ ^ 2) * ‖v‖ ^ 2 - Complex.normSq (inner ℂ x v) := by nlinarith
  have hinv : 0 < (1 + ‖x‖ ^ 2)⁻¹ ^ 2 := by positivity
  have := mul_pos hinv hpos
  linarith

end Kahler

namespace Projectivization

open Kahler Matrix.UnitaryGroup DifferentialForm

variable {n : ℕ}

/-- Taming for the model form: `fsModelForm w (v, i • v) < 0` for `v ≠ 0`. -/
theorem fsModelForm_smul_I_neg (w : Fin n → ℂ) {v : Fin n → ℂ} (hv : v ≠ 0) :
    fsModelForm w ![v, Complex.I • v] < 0 := by
  have h : fsModelForm w ![v, Complex.I • v]
      = fsChartForm (toLpCLM w) ![toLpCLM v, complexStructure (toLpCLM v)] := by
    simp only [fsModelForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    ext i
    fin_cases i <;> simp [complexStructure_apply]
  rw [h]
  refine fsChartForm_complexStructure_self_neg _ ?_
  intro h0
  apply hv
  have := congrArg WithLp.ofLp h0
  simpa using this

/-- Taming for the section, in the model: `fsSection x (v, i • v) < 0` for `v ≠ 0`. -/
theorem fsSection_smul_I_neg (x : ℙ ℂ (Ambient n)) {v : Fin n → ℂ} (hv : v ≠ 0) :
    fsSection x ![v, Complex.I • v] < 0 :=
  fsModelForm_smul_I_neg _ hv

/-- ★★ **Non-degeneracy of the Fubini–Study form at every point of `ℂℙⁿ`.** -/
theorem fsForm_nondegenerate (x : ℙ ℂ (Ambient n))
    (v : TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ)) x) (hv : v ≠ 0) :
    ∃ w, fsForm x ![v, w] ≠ 0 :=
  ⟨Complex.I • (show Fin n → ℂ from v), (fsSection_smul_I_neg x hv).ne⟩

/-- ★★★ **`ℂℙⁿ` with the Fubini–Study form is a symplectic manifold**: closed
(`fsForm_mextDeriv`) and non-degenerate at every point (`fsForm_nondegenerate`). -/
theorem fsForm_isSymplectic (n : ℕ) : (fsForm (n := n)).IsSymplectic :=
  ⟨fsForm_mextDeriv, fsForm_nondegenerate⟩

/-! ### The almost Kähler structure of `ℂℙⁿ`: `J = i·` (G7) -/

/-- Definitional identification of a tangent vector of `ℂℙⁿ` with a model vector (the model
carries the `ℂ`-action the tangent space does not expose). -/
abbrev tangentToModel {x : ℙ ℂ (Ambient n)}
    (v : TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ)) x) : Fin n → ℂ := v

/-- The complex structure of `ℂℙⁿ`: multiplication by `i` on each tangent space, read in the
chart at the point. -/
def fsJ (x : ℙ ℂ (Ambient n)) (v : TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ)) x) :
    TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ)) x :=
  Complex.I • tangentToModel v

theorem fsJ_fsJ (x : ℙ ℂ (Ambient n)) (v : TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ)) x) :
    fsJ x (fsJ x v) = -v := by
  show Complex.I • (Complex.I • tangentToModel v) = -tangentToModel v
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]

/-- `J`-invariance of the model form: `fsModelForm w (i • u, i • v) = fsModelForm w (u, v)`. -/
theorem fsModelForm_smul_I_smul_I (w u v : Fin n → ℂ) :
    fsModelForm w ![Complex.I • u, Complex.I • v] = fsModelForm w ![u, v] := by
  have hu : toLpCLM (Complex.I • u) = Complex.I • toLpCLM u := by
    ext k
    simp
  have hv : toLpCLM (Complex.I • v) = Complex.I • toLpCLM v := by
    ext k
    simp
  simp only [fsModelForm_apply, hu, hv, inner_smul_left, inner_smul_right, Complex.conj_I,
    Complex.mul_im, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

/-- ★ `J`-invariance of the Fubini–Study form: it is a `(1,1)`-form. -/
theorem fsForm_smul_I_smul_I (x : ℙ ℂ (Ambient n))
    (u v : TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ)) x) :
    fsForm x ![fsJ x u, fsJ x v] = fsForm x ![u, v] := by
  show fsSection x ![Complex.I • tangentToModel u, Complex.I • tangentToModel v]
    = fsSection x ![tangentToModel u, tangentToModel v]
  exact fsModelForm_smul_I_smul_I _ _ _

/-- ★★ **`ℂℙⁿ` with the Fubini–Study form and `J = i·` is almost Kähler**: symplectic
(`fsForm_isSymplectic`), `J² = -1`, `ω` is `J`-invariant, and `ω (J v, v) > 0` — the taming
`fsSection_smul_I_neg`, its sign (the `-4` of the potential) absorbed by the metric convention
`g = ω (J ·, ·)`. -/
theorem fsForm_isAlmostKahler (n : ℕ) : IsAlmostKahler (fsForm (n := n)) fsJ where
  isSymplectic := fsForm_isSymplectic n
  J_J := fsJ_fsJ
  invariant := fsForm_smul_I_smul_I
  pos := fun x v hv => by
    have h : fsSection x ![tangentToModel v, Complex.I • tangentToModel v] < 0 :=
      fsSection_smul_I_neg x hv
    have hs : fsSection x ![tangentToModel v, Complex.I • tangentToModel v]
        = -fsSection x ![Complex.I • tangentToModel v, tangentToModel v] :=
      apply_swap (fun x => fsForm x) x v (fsJ x v)
    show 0 < fsSection x ![Complex.I • tangentToModel v, tangentToModel v]
    linarith

/-- The compatible metric of `ℂℙⁿ` is positive definite: the Fubini–Study metric, up to the
convention. -/
theorem fsForm_metric_self_pos (x : ℙ ℂ (Ambient n))
    {v : TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ)) x} (hv : v ≠ 0) :
    0 < (fsForm_isAlmostKahler n).metric x v v :=
  (fsForm_isAlmostKahler n).metric_self_pos x hv

/-! ### `J` is the complex structure of the atlas -/

/-- The chart transition of `ℂℙⁿ` is the unitary-action chart map for `U = 1`. -/
theorem chart_transition_eq_uTrans (x₀ y : ℙ ℂ (Ambient n)) :
    (chartAt (Fin n → ℂ) y ∘ (chartAt (Fin n → ℂ) x₀).symm) = uTrans 1 (idx x₀) (idx y) := by
  funext w
  show chartFun (idx y) (chartInv (idx x₀) w) = _
  rw [← chartFun_smul_chartInv (1 : Matrix.unitaryGroup (Fin (n + 1)) ℂ), one_smul]

/-- ★ **`J` is the complex structure of the atlas**: the derivative of every chart transition is
`ℂ`-linear, because the transitions are holomorphic (`contDiffOn_uTrans`). So `J = i·` in one
chart is `J = i·` in every chart. -/
theorem fderiv_chart_transition_smul_I (x₀ y : ℙ ℂ (Ambient n)) {w : Fin n → ℂ}
    (hy : (chartAt (Fin n → ℂ) x₀).symm w ∈ (chartAt (Fin n → ℂ) y).source) (v : Fin n → ℂ) :
    fderiv ℝ (chartAt (Fin n → ℂ) y ∘ (chartAt (Fin n → ℂ) x₀).symm) w (Complex.I • v)
      = Complex.I • fderiv ℝ (chartAt (Fin n → ℂ) y ∘ (chartAt (Fin n → ℂ) x₀).symm) w v := by
  rw [chart_transition_eq_uTrans]
  have hmem : w ∈ {w : Fin n → ℂ |
      toEuclideanLinearEquiv (1 : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (insertOne (idx x₀) w)
        (idx y) ≠ 0} := by
    show toEuclideanLinearEquiv (1 : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (insertOne (idx x₀) w)
      (idx y) ≠ 0
    rw [toEuclideanLinearEquiv_one, LinearEquiv.refl_apply]
    exact (mem_chartSource_mk (idx y) _ (insertOne_ne_zero _ _)).1 hy
  have hd : DifferentiableAt ℂ (uTrans 1 (idx x₀) (idx y)) w :=
    ((contDiffOn_uTrans 1 (idx x₀) (idx y)).contDiffAt
      ((isOpen_uDomain 1 (idx x₀) (idx y)).mem_nhds hmem)).differentiableAt (by simp)
  have hR : HasFDerivAt (uTrans 1 (idx x₀) (idx y))
      ((fderiv ℂ (uTrans 1 (idx x₀) (idx y)) w).restrictScalars ℝ) w :=
    hd.hasFDerivAt.restrictScalars ℝ
  rw [hR.fderiv]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul]

/-- ★ `J` commutes with the tangent trivialisation: in the chart at `x₀`, `J y` is still `i·`
for every `y` in the chart source. -/
theorem fsJ_symmL (x₀ y : ℙ ℂ (Ambient n)) (hy : y ∈ (chartAt (Fin n → ℂ) x₀).source)
    (v : Fin n → ℂ) :
    fsJ y ((trivializationAt (Fin n → ℂ) (TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ))) x₀).symmL
        ℝ y v)
      = (trivializationAt (Fin n → ℂ) (TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ))) x₀).symmL
          ℝ y (Complex.I • v) := by
  rw [tangent_symmL_eq_fderiv x₀ y hy]
  have hy' : (chartAt (Fin n → ℂ) x₀).symm (chartAt (Fin n → ℂ) x₀ y)
      ∈ (chartAt (Fin n → ℂ) y).source := by
    rw [(chartAt (Fin n → ℂ) x₀).left_inv hy]
    exact mem_chart_source _ y
  unfold fsJ
  exact (fderiv_chart_transition_smul_I x₀ y hy' v).symm

/-! ### ★★★ `ℂℙⁿ` is a Kähler manifold (G14a) -/

/-- The complex structure of the model `Fin n → ℂ`: multiplication by `i`, as a real-linear map. -/
noncomputable def modelJ : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
  (Complex.I • ContinuousLinearMap.id ℂ (Fin n → ℂ)).restrictScalars ℝ

@[simp] theorem modelJ_apply (v : Fin n → ℂ) : modelJ v = Complex.I • v := rfl

/-- ★★★ **`ℂℙⁿ` with the Fubini–Study form and `J = i·` is a Kähler manifold**: almost Kähler
(`fsForm_isAlmostKahler`), and `J` is the complex structure of the holomorphic atlas — `i·` in
every chart (`fsJ_symmL`, from the holomorphy of the transitions `contDiffOn_uTrans`). Kähler in
the atlas sense of `DifferentialForm.IsKahler`; the tensor sense is G14b. -/
theorem fsForm_isKahler (n : ℕ) : IsKahler (fsForm (n := n)) fsJ modelJ where
  toIsAlmostKahler := fsForm_isAlmostKahler n
  J_symmL := fun x₀ y hy v => by
    rw [modelJ_apply]
    exact fsJ_symmL x₀ y hy v

/-! ### `J` as a smooth section of the endomorphism bundle (G15) -/

/-- `J = i·` on each tangent space, as a continuous linear map: the section of `Hom(TM, TM)`. -/
noncomputable def fsJL (x : ℙ ℂ (Ambient n)) :
    TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ)) x →L[ℝ]
      TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ)) x :=
  modelJ

@[simp] theorem fsJL_apply (x : ℙ ℂ (Ambient n))
    (v : TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ)) x) : fsJL x v = fsJ x v := rfl

/-- ★★ **`J` is a smooth section of `Hom(TM, TM)` on `ℂℙⁿ`**: in every chart it is the constant
`i·` (`IsKahler.contMDiff_hom_section` on `fsForm_isKahler`). -/
theorem contMDiff_fsJL :
    ContMDiff (modelWithCornersSelf ℝ (Fin n → ℂ))
      ((modelWithCornersSelf ℝ (Fin n → ℂ)).prod
        (modelWithCornersSelf ℝ ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ)))) ∞
      (fun x : ℙ ℂ (Ambient n) => TotalSpace.mk' ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) x (fsJL x)) :=
  (fsForm_isKahler n).contMDiff_hom_section fsJL fun _ _ => rfl

/-! ### The Nijenhuis tensor of `J = i·` vanishes (G14b) -/

/-- ★★ **`J = i·` is integrable in the tensor sense on `ℂℙⁿ`**: its Nijenhuis tensor vanishes on
vector fields differentiable at the point (`IsKahler.nijenhuis_eq_zero` on `fsForm_isKahler`). -/
theorem nijenhuis_fsJ_eq_zero
    {V W : ∀ x : ℙ ℂ (Ambient n), TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ)) x}
    (x₀ : ℙ ℂ (Ambient n))
    (hV : MDifferentiableAt (modelWithCornersSelf ℝ (Fin n → ℂ))
      (modelWithCornersSelf ℝ (Fin n → ℂ)).tangent
      (fun x => TotalSpace.mk' (Fin n → ℂ) x (V x)) x₀)
    (hW : MDifferentiableAt (modelWithCornersSelf ℝ (Fin n → ℂ))
      (modelWithCornersSelf ℝ (Fin n → ℂ)).tangent
      (fun x => TotalSpace.mk' (Fin n → ℂ) x (W x)) x₀) :
    nijenhuis fsJ V W x₀ = 0 :=
  (fsForm_isKahler n).nijenhuis_eq_zero x₀ hV hW

end Projectivization
