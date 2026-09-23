/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Calculus.DifferentialForm.Poincare
public import CsdLean4.Mathlib.Analysis.InnerProductSpace.KahlerClosed
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Darboux's theorem by Moser's trick

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #8 (Q31 = G18), the assembly.

A closed 2-form that is non-degenerate at a point is, near that point, the pullback of a
**constant** form by a local diffeomorphism — Moser's proof. With `ω₀ = ω(x₀)`,
`η = ω − ω₀` and the interpolation `ω_t = ω₀ + tη`:

* `η` is closed and vanishes at `x₀`, so the Poincaré lemma
  (`Analysis/Calculus/DifferentialForm/Poincare.lean`) gives a `C¹` primitive `β` with `dβ = η`,
  `β(x₀) = 0`, `Dβ(x₀) = 0` — `moserPrimitive`;
* non-degeneracy is open (`isOpen_nondegenerate`: it is invertibility of `curryLeft`, and
  `ContinuousLinearEquiv.isOpen`), so `ω_t` is non-degenerate near `x₀` for `|t| < 2`
  (`exists_moser_radius`), and **Moser's field** `X_t = −(ω_t)^♭⁻¹ β`, i.e. `ι_{X_t} ω_t = −β`
  (`moserField`, `curryLeft_moserForm_moserField`), is jointly `C¹`
  (`contDiffOn_moserFieldJoint`, through `contDiffAt_map_inverse`) and vanishes to second order
  at `x₀` (`hasFDerivAt_moserField_self`);
* its flow up to time `1` exists on a small ball (`Analysis/ODE/FlowDerivative.lean`,
  `exists_flow_hasFDerivAt_of_norm_fderiv_le`, with `‖DX_t‖ ≤ ¼` there by a tube-lemma argument),
  and **transports the interpolation**: `∂ₜω_t + L_{X_t} ω_t = η + d(ι_{X_t} ω_t) + ι_{X_t} dω_t
  = η − dβ + 0 = 0` (the flat Cartan formula `flatLieDeriv_eq_extDeriv_flatInteriorProduct_add`),
  so `form_invariant_of_flatLieDeriv_eq_zero_timeDependent` gives `φ_1^* ω = φ_0^* ω₀ = ω₀`;
* the time-`1` map approximates the identity with constant `¼ e^{¼} < 1`
  (`approximatesLinearOn_flow`, Grönwall + the mean value inequality), so it is an
  `OpenPartialHomeomorph` by Mathlib's inverse function theorem
  (`ApproximatesLinearOn.toOpenPartialHomeomorph`); its derivative is invertible because the
  pullback of a non-degenerate form is non-degenerate.

* ★★ `exists_openPartialHomeomorph_pullback_eq` — **Darboux on a ball**: for `ω` `C¹` and closed on
  `ball x₀ R` with `ω(x₀)` non-degenerate, there is an open partial homeomorphism `Φ` of `E`
  with `x₀ ∈ Φ.source ⊆ ball x₀ R`, `Φ x₀ = x₀`, **`C¹` on its source with `C¹` inverse on its
  target**, differentiable at every point of its source with invertible derivative `D`, and
  `ω(Φ x)(D u, D v) = ω(x₀)(u, v)`: `Φ^* ω = ω(x₀)`. The `C¹` regularity is the continuity of
  `x ↦ Dφ_1(x)` (`exists_flow_hasFDerivAt_of_norm_fderiv_le`: continuous dependence of the
  variational solution on the initial point) through `contDiffAt_one_iff`, and Mathlib's
  `OpenPartialHomeomorph.contDiffAt_symm` for the inverse;
* ★ `exists_openPartialHomeomorph_symm_pullback_eq` — the same read on the chart `Φ.symm`:
  `ω y (u, v) = ω(x₀)(D(Φ⁻¹)(y) u, D(Φ⁻¹)(y) v)` on `Φ.target` — **in the chart `Φ⁻¹`, `ω` is the
  constant form `ω(x₀)`**;
* `mem_contDiffGroupoid_of_contDiffOn` — an open partial homeomorphism of the model space that is
  `C^n` with `C^n` inverse belongs to the `C^n` groupoid; `StructureGroupoid.trans_mem_maximalAtlas`
  — a chart of the maximal atlas composed with a member of the groupoid stays in the maximal atlas;
* ★★ `DifferentialForm.IsSymplectic.exists_openPartialHomeomorph_localRep_pullback_eq` — **Darboux
  on a symplectic manifold**: at every point the local representative of the form in the chart
  is, after a further open partial homeomorphism `Φ` of the model space fixing the point,
  the constant form `ω_loc(chart x₀)`; **the Darboux chart `Φ⁻¹ ∘ chartAt E x₀` contains `x₀` and
  belongs to the `C¹` maximal atlas of `M`**. The standard form `∑ dpᵢ ∧ dqᵢ` is
  `Geometry/Manifold/DarbouxStandardForm.lean`.

## Honest scope

⚠️ **`C¹`, not `C^k`.** The form is `C¹` (a symplectic form is `C^∞`, but only its `C¹` part is
used), Moser's field is `C¹`, and the chart `Φ` is `C¹` with `C¹` inverse — the Darboux chart is a
member of the `C¹` maximal atlas. A `C^k` form has a `C^k` Darboux chart, which needs `C^k`
dependence of flows on the initial point (in neither Mathlib nor the corpus at the pin);
BACKLOG #60 prices this residue.

**The constant form here; the standard form downstream.** Moser's trick produces the constant
form `ω(x₀)`; `Geometry/Manifold/DarbouxStandardForm.lean` composes the chart with the coordinates
of a symplectic basis of `ω(x₀)` (`LinearAlgebra/BilinearForm/SymplecticBasis.lean`) and states the
textbook form `ω = Ψ^* (∑ dpᵢ ∧ dqᵢ)` on `ℝ^{2n}`, with `finrank E = 2n`.

References: J. Moser, *On the volume elements on a manifold*, Trans. AMS 120 (1965);
A. Weinstein, *Symplectic manifolds and their Lagrangian submanifolds*, Adv. Math. 6 (1971);
D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, Thm 3.2.2;
`Analysis/Calculus/DifferentialForm/Poincare.lean`; `Analysis/ODE/FlowDerivative.lean`;
`Geometry/Manifold/HamiltonianLieDerivative.lean`; `specs/BACKLOG.md` #8;
`specs/generator-layer-scoping.md` §9 (G18) and Q31.
-/

@[expose] public section

open Set Metric Filter Topology
open scoped Manifold NNReal

noncomputable section

/-! ### Non-degeneracy is open -/

section Nondegenerate

/-- `curryLeft` is a bounded linear map on 2-forms. -/
theorem isBoundedLinearMap_curryLeft (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsBoundedLinearMap ℝ
      (fun ξ : E [⋀^Fin 2]→L[ℝ] ℝ => ContinuousAlternatingMap.curryLeft ξ) :=
  ⟨⟨fun ξ ξ' => ContinuousAlternatingMap.curryLeft_add ξ ξ',
    fun c ξ => ContinuousAlternatingMap.curryLeft_smul c ξ⟩,
    1, one_pos, fun ξ => le_of_eq
      ((ContinuousAlternatingMap.norm_curryLeft ξ).trans (one_mul _).symm)⟩

/-- `curryLeft` is `C^n` on 2-forms. -/
theorem contDiff_curryLeft (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun ξ : E [⋀^Fin 2]→L[ℝ] ℝ => ContinuousAlternatingMap.curryLeft ξ) :=
  IsBoundedLinearMap.contDiff (𝕜 := ℝ) (n := n)
    (f := fun ξ : E [⋀^Fin 2]→L[ℝ] ℝ => ContinuousAlternatingMap.curryLeft ξ)
    ⟨⟨fun ξ ξ' => ContinuousAlternatingMap.curryLeft_add ξ ξ',
      fun c ξ => ContinuousAlternatingMap.curryLeft_smul c ξ⟩,
      1, one_pos, fun ξ => le_of_eq
        ((ContinuousAlternatingMap.norm_curryLeft ξ).trans (one_mul _).symm)⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Non-degeneracy of a 2-form is invertibility of `curryLeft`. -/
theorem nondegenerate_iff_curryLeft_mem_range (ξ : E [⋀^Fin 2]→L[ℝ] ℝ) :
    (∀ v : E, v ≠ 0 → ∃ u, ξ ![v, u] ≠ 0) ↔
      ContinuousAlternatingMap.curryLeft ξ ∈
        range ((↑) : (E ≃L[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ)) → E →L[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ)) := by
  constructor
  · intro h
    exact ⟨DifferentialForm.flatCLE ξ h, DifferentialForm.coe_flatCLE ξ h⟩
  · rintro ⟨e, he⟩ v hv
    by_contra hcon
    push Not at hcon
    apply hv
    have h1 : ContinuousAlternatingMap.curryLeft ξ v = 0 := by
      ext m
      rw [ContinuousAlternatingMap.curryLeft_apply_apply]
      have hm : Matrix.vecCons v m = ![v, m 0] := by
        funext i
        fin_cases i <;> rfl
      rw [hm]
      exact hcon (m 0)
    rw [← he] at h1
    exact e.map_eq_zero_iff.mp h1

/-- **Non-degeneracy is an open condition** on 2-forms. -/
theorem isOpen_nondegenerate :
    IsOpen {ξ : E [⋀^Fin 2]→L[ℝ] ℝ | ∀ v : E, v ≠ 0 → ∃ u, ξ ![v, u] ≠ 0} := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h : {ξ : E [⋀^Fin 2]→L[ℝ] ℝ | ∀ v : E, v ≠ 0 → ∃ u, ξ ![v, u] ≠ 0}
      = (fun ξ : E [⋀^Fin 2]→L[ℝ] ℝ => ContinuousAlternatingMap.curryLeft ξ) ⁻¹'
        range ((↑) : (E ≃L[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ)) → E →L[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ)) := by
    ext ξ
    exact nondegenerate_iff_curryLeft_mem_range ξ
  rw [h]
  exact ContinuousLinearEquiv.isOpen.preimage (isBoundedLinearMap_curryLeft E).continuous

/-- Every 2-form close to a non-degenerate one is non-degenerate. -/
theorem exists_nondegenerate_of_norm_sub_lt {ξ₀ : E [⋀^Fin 2]→L[ℝ] ℝ}
    (h : ∀ v : E, v ≠ 0 → ∃ u, ξ₀ ![v, u] ≠ 0) :
    ∃ δ > 0, ∀ ξ : E [⋀^Fin 2]→L[ℝ] ℝ, ‖ξ - ξ₀‖ < δ →
      ∀ v : E, v ≠ 0 → ∃ u, ξ ![v, u] ≠ 0 := by
  have hmem : {ξ : E [⋀^Fin 2]→L[ℝ] ℝ | ∀ v : E, v ≠ 0 → ∃ u, ξ ![v, u] ≠ 0} ∈ 𝓝 ξ₀ :=
    isOpen_nondegenerate.mem_nhds h
  rcases Metric.mem_nhds_iff.mp hmem with ⟨δ, hδ, hball⟩
  exact ⟨δ, hδ, fun ξ hξ => hball (mem_ball_iff_norm.mpr hξ)⟩

end Nondegenerate

/-! ### Moser's data -/

section Moser

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The deviation `η = ω − ω(x₀)` of a 2-form from its value at the centre. -/
def moserDeviation (ω : E → E [⋀^Fin 2]→L[ℝ] ℝ) (x₀ : E) : E → E [⋀^Fin 2]→L[ℝ] ℝ :=
  fun z => ω z - ω x₀

/-- Moser's interpolation `ω_t = ω(x₀) + t (ω − ω(x₀))`. -/
def moserForm (ω : E → E [⋀^Fin 2]→L[ℝ] ℝ) (x₀ : E) (t : ℝ) (z : E) :
    E [⋀^Fin 2]→L[ℝ] ℝ :=
  ω x₀ + t • (ω z - ω x₀)

variable {ω : E → E [⋀^Fin 2]→L[ℝ] ℝ} {x₀ : E} {R : ℝ}

theorem moserForm_zero (z : E) : moserForm ω x₀ 0 z = ω x₀ := by
  simp [moserForm]

theorem moserForm_one (z : E) : moserForm ω x₀ 1 z = ω z := by
  simp [moserForm]

theorem moserForm_self (t : ℝ) : moserForm ω x₀ t x₀ = ω x₀ := by
  simp [moserForm]

theorem moserForm_eq_add_smul (t : ℝ) (z : E) :
    moserForm ω x₀ t z = ω x₀ + t • moserDeviation ω x₀ z :=
  rfl

theorem norm_moserForm_sub (t : ℝ) (z : E) :
    ‖moserForm ω x₀ t z - ω x₀‖ = |t| * ‖ω z - ω x₀‖ := by
  rw [moserForm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]

theorem contDiffOn_moserDeviation (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) :
    ContDiffOn ℝ 1 (moserDeviation ω x₀) (ball x₀ R) :=
  hω.sub contDiffOn_const

theorem moserDeviation_self : moserDeviation ω x₀ x₀ = 0 := sub_self _

theorem extDeriv_moserDeviation (hω : ContDiffOn ℝ 1 ω (ball x₀ R))
    (hclosed : ∀ y ∈ ball x₀ R, extDeriv ω y = 0) {y : E} (hy : y ∈ ball x₀ R) :
    extDeriv (moserDeviation ω x₀) y = 0 := by
  have hωd : DifferentiableAt ℝ ω y :=
    (hω.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hy)
  have h : moserDeviation ω x₀ = fun z => ω z + (fun _ : E => -ω x₀) z := by
    funext z
    simp [moserDeviation, sub_eq_add_neg]
  rw [h, extDeriv_fun_add hωd (differentiableAt_const _), hclosed y hy, extDeriv_const_apply,
    add_zero]

variable (ω x₀ R) in
/-- The radial primitive `β` of the deviation on the ball: `dβ = ω − ω(x₀)`. -/
def moserPrimitive [FiniteDimensional ℝ E] : E → E [⋀^Fin 1]→L[ℝ] ℝ :=
  radialPrimitiveForm (moserDeviation ω x₀) x₀ R

variable (ω x₀ R) in
/-- **Moser's vector field** `X_t = −(ω_t)^♭⁻¹ β`, i.e. `ι_{X_t} ω_t = −β` where `ω_t` is
non-degenerate (`ContinuousLinearMap.inverse` is `0` elsewhere), as a function of `(t, z)`. -/
def moserFieldJoint [FiniteDimensional ℝ E] (q : ℝ × E) : E :=
  ContinuousLinearMap.inverse (ContinuousAlternatingMap.curryLeft (moserForm ω x₀ q.1 q.2))
    (-(moserPrimitive ω x₀ R q.2))

variable (ω x₀ R) in
/-- Moser's vector field at time `t`. -/
def moserField [FiniteDimensional ℝ E] (t : ℝ) (z : E) : E :=
  moserFieldJoint ω x₀ R (t, z)

variable [FiniteDimensional ℝ E]

theorem uncurry_moserField : Function.uncurry (moserField ω x₀ R) = moserFieldJoint ω x₀ R := by
  funext ⟨t, z⟩
  rfl

theorem contDiffOn_moserPrimitive (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) :
    ContDiffOn ℝ 1 (moserPrimitive ω x₀ R) (ball x₀ R) :=
  contDiffOn_radialPrimitiveForm (contDiffOn_moserDeviation hω)

theorem moserPrimitive_self (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) (hR : 0 < R) :
    moserPrimitive ω x₀ R x₀ = 0 :=
  radialPrimitiveForm_self (contDiffOn_moserDeviation hω) hR

/-- `β` vanishes to second order at the centre. -/
theorem hasFDerivAt_moserPrimitive_self (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) (hR : 0 < R) :
    HasFDerivAt (moserPrimitive ω x₀ R) (0 : E →L[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ)) x₀ :=
  hasFDerivAt_radialPrimitiveForm_self (contDiffOn_moserDeviation hω) hR moserDeviation_self

/-- `dβ = ω − ω(x₀)` on the ball (the Poincaré lemma). -/
theorem extDeriv_moserPrimitive (hω : ContDiffOn ℝ 1 ω (ball x₀ R))
    (hclosed : ∀ y ∈ ball x₀ R, extDeriv ω y = 0) {y : E} (hy : y ∈ ball x₀ R) :
    extDeriv (moserPrimitive ω x₀ R) y = moserDeviation ω x₀ y :=
  extDeriv_radialPrimitiveForm (contDiffOn_moserDeviation hω)
    (fun _ hz => extDeriv_moserDeviation hω hclosed hz) hy

omit [FiniteDimensional ℝ E] in
/-- The interpolation is jointly `C¹` in `(t, z)`. -/
theorem contDiffOn_moserForm_uncurry (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) :
    ContDiffOn ℝ 1 (Function.uncurry (moserForm ω x₀)) (univ ×ˢ ball x₀ R) := by
  have h1 : ContDiffOn ℝ 1 (fun p : ℝ × E => ω p.2 - ω x₀) (univ ×ˢ ball x₀ R) :=
    (hω.sub contDiffOn_const).comp contDiff_snd.contDiffOn fun p hp => hp.2
  exact contDiffOn_const.add (contDiff_fst.contDiffOn.smul h1)

omit [FiniteDimensional ℝ E] in
theorem extDeriv_moserForm (hω : ContDiffOn ℝ 1 ω (ball x₀ R))
    (hclosed : ∀ y ∈ ball x₀ R, extDeriv ω y = 0) (t : ℝ) {y : E} (hy : y ∈ ball x₀ R) :
    extDeriv (moserForm ω x₀ t) y = 0 := by
  have hηd : DifferentiableAt ℝ (moserDeviation ω x₀) y :=
    ((contDiffOn_moserDeviation hω).differentiableOn one_ne_zero).differentiableAt
      (isOpen_ball.mem_nhds hy)
  have h : moserForm ω x₀ t = fun z => (fun _ : E => ω x₀) z + (t • moserDeviation ω x₀) z := by
    funext z
    rfl
  rw [h, extDeriv_fun_add (differentiableAt_const _) (hηd.const_smul t), extDeriv_const_apply,
    extDeriv_smul, extDeriv_moserDeviation hω hclosed hy, smul_zero, add_zero]

/-- Where `ω_t` is non-degenerate, `ι_{X_t} ω_t = −β`. -/
theorem curryLeft_moserForm_moserField {t : ℝ} {z : E}
    (h : ∀ v : E, v ≠ 0 → ∃ u, moserForm ω x₀ t z ![v, u] ≠ 0) :
    ContinuousAlternatingMap.curryLeft (moserForm ω x₀ t z) (moserField ω x₀ R t z)
      = -(moserPrimitive ω x₀ R z) := by
  rw [moserField, moserFieldJoint, ← DifferentialForm.coe_flatCLE _ h,
    ContinuousLinearMap.inverse_equiv]
  exact (DifferentialForm.flatCLE _ h).apply_symm_apply _

/-- `X_t(x₀) = 0`. -/
theorem moserField_self (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) (hR : 0 < R) (t : ℝ) :
    moserField ω x₀ R t x₀ = 0 := by
  rw [moserField, moserFieldJoint]
  dsimp only
  rw [moserPrimitive_self hω hR, neg_zero, map_zero]

end Moser

/-! ### The assembly -/

section Assembly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ω : E → E [⋀^Fin 2]→L[ℝ] ℝ} {x₀ : E} {R : ℝ}

/-- The ball on which Moser's interpolation stays non-degenerate for `|t| < 2`. -/
theorem exists_moser_radius (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) (hR : 0 < R)
    (hnd : ∀ v : E, v ≠ 0 → ∃ u, ω x₀ ![v, u] ≠ 0) :
    ∃ r, 0 < r ∧ r ≤ R ∧ ∀ t ∈ Ioo (-2 : ℝ) 2, ∀ z ∈ ball x₀ r,
      ∀ v : E, v ≠ 0 → ∃ u, moserForm ω x₀ t z ![v, u] ≠ 0 := by
  obtain ⟨δ, hδ, hδnd⟩ := exists_nondegenerate_of_norm_sub_lt hnd
  have hc : ContinuousAt ω x₀ :=
    hω.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hR))
  obtain ⟨ε, hε, hεω⟩ := Metric.continuousAt_iff.mp hc (δ / 2) (by positivity)
  refine ⟨min ε R, lt_min hε hR, min_le_right _ _, fun t ht z hz => ?_⟩
  apply hδnd
  rw [norm_moserForm_sub]
  have hz' : dist z x₀ < ε := lt_of_lt_of_le hz (min_le_left _ _)
  have h1 : ‖ω z - ω x₀‖ < δ / 2 := by
    have := hεω hz'
    rwa [dist_eq_norm] at this
  have h2 : |t| ≤ 2 := abs_le.mpr ⟨ht.1.le, ht.2.le⟩
  calc |t| * ‖ω z - ω x₀‖ ≤ 2 * ‖ω z - ω x₀‖ := by gcongr
    _ < 2 * (δ / 2) := by gcongr
    _ = δ := by ring

/-- Moser's field is jointly `C¹` on `Ioo (-2) 2 ×ˢ ball x₀ r` where the interpolation is
non-degenerate. -/
theorem contDiffOn_moserFieldJoint (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) {r : ℝ} (hr : r ≤ R)
    (hnd : ∀ t ∈ Ioo (-2 : ℝ) 2, ∀ z ∈ ball x₀ r,
      ∀ v : E, v ≠ 0 → ∃ u, moserForm ω x₀ t z ![v, u] ≠ 0) :
    ContDiffOn ℝ 1 (moserFieldJoint ω x₀ R) (Ioo (-2 : ℝ) 2 ×ˢ ball x₀ r) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro p hp
  have hpR : p.2 ∈ ball x₀ R := ball_subset_ball hr hp.2
  have hΩ : ContDiffAt ℝ 1
      (fun q : ℝ × E => ContinuousAlternatingMap.curryLeft (moserForm ω x₀ q.1 q.2)) p :=
    (contDiff_curryLeft E).contDiffAt.comp p
      ((contDiffOn_moserForm_uncurry hω).contDiffAt
        ((isOpen_univ.prod isOpen_ball).mem_nhds ⟨mem_univ _, hpR⟩))
  have hinv : ContDiffAt ℝ 1 (fun q : ℝ × E => ContinuousLinearMap.inverse
      (ContinuousAlternatingMap.curryLeft (moserForm ω x₀ q.1 q.2))) p := by
    have h := contDiffAt_map_inverse (𝕜 := ℝ) (n := 1)
      (DifferentialForm.flatCLE _ (hnd p.1 hp.1 p.2 hp.2))
    rw [DifferentialForm.coe_flatCLE] at h
    exact h.comp p hΩ
  have hβ : ContDiffAt ℝ 1 (fun q : ℝ × E => -(moserPrimitive ω x₀ R q.2)) p :=
    (((contDiffOn_moserPrimitive hω).contDiffAt (isOpen_ball.mem_nhds hpR)).comp p
      contDiffAt_snd).neg
  have hfin : ContDiffAt ℝ 1 (fun q : ℝ × E =>
      ContinuousLinearMap.inverse (ContinuousAlternatingMap.curryLeft (moserForm ω x₀ q.1 q.2))
        (-(moserPrimitive ω x₀ R q.2))) p :=
    ContDiffAt.clm_apply (f := fun q : ℝ × E => ContinuousLinearMap.inverse
      (ContinuousAlternatingMap.curryLeft (moserForm ω x₀ q.1 q.2)))
      (g := fun q : ℝ × E => -(moserPrimitive ω x₀ R q.2)) hinv hβ
  exact hfin.contDiffWithinAt

/-- `X_t` for fixed `t` is `C¹` at a point where the joint field is. -/
theorem contDiffAt_moserField_of_joint {r : ℝ} {t : ℝ} {z : E}
    (hmf : ContDiffOn ℝ 1 (moserFieldJoint ω x₀ R) (Ioo (-2 : ℝ) 2 ×ˢ ball x₀ r))
    (ht : t ∈ Ioo (-2 : ℝ) 2) (hz : z ∈ ball x₀ r) :
    ContDiffAt ℝ 1 (moserField ω x₀ R t) z := by
  have hV : IsOpen (Ioo (-2 : ℝ) 2 ×ˢ ball x₀ r) := isOpen_Ioo.prod isOpen_ball
  exact (hmf.contDiffAt (hV.mem_nhds ⟨ht, hz⟩)).comp z (contDiffAt_const.prodMk contDiffAt_id)

/-- The derivative of `X_t` in `z` is the partial derivative of the joint field. -/
theorem fderiv_moserField_eq {r : ℝ} {t : ℝ} {z : E}
    (hmf : ContDiffOn ℝ 1 (moserFieldJoint ω x₀ R) (Ioo (-2 : ℝ) 2 ×ˢ ball x₀ r))
    (ht : t ∈ Ioo (-2 : ℝ) 2) (hz : z ∈ ball x₀ r) :
    fderiv ℝ (moserField ω x₀ R t) z
      = (fderiv ℝ (moserFieldJoint ω x₀ R) (t, z)).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  have hV : IsOpen (Ioo (-2 : ℝ) 2 ×ˢ ball x₀ r) := isOpen_Ioo.prod isOpen_ball
  have hF : HasFDerivAt (moserFieldJoint ω x₀ R) (fderiv ℝ (moserFieldJoint ω x₀ R) (t, z))
      (t, z) :=
    ((hmf.contDiffAt (hV.mem_nhds ⟨ht, hz⟩)).differentiableAt one_ne_zero).hasFDerivAt
  exact (hF.comp z (hasFDerivAt_prodMk_right t z)).fderiv

/-- `X_t` vanishes to second order at `x₀`: `D X_t (x₀) = 0`. -/
theorem hasFDerivAt_moserField_self (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) (hR : 0 < R)
    (hnd : ∀ v : E, v ≠ 0 → ∃ u, ω x₀ ![v, u] ≠ 0) (t : ℝ) :
    HasFDerivAt (moserField ω x₀ R t) (0 : E →L[ℝ] E) x₀ := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hΩ : ContDiffAt ℝ 1 (moserForm ω x₀ t) x₀ :=
    ((contDiffOn_moserForm_uncurry hω).contDiffAt
      ((isOpen_univ.prod isOpen_ball).mem_nhds ⟨mem_univ _, mem_ball_self hR⟩)).comp x₀
      (contDiffAt_const.prodMk contDiffAt_id)
  have hc : ContDiffAt ℝ 1 (fun z => ContinuousLinearMap.inverse
      (ContinuousAlternatingMap.curryLeft (moserForm ω x₀ t z))) x₀ := by
    have hnd' : ∀ v : E, v ≠ 0 → ∃ u, moserForm ω x₀ t x₀ ![v, u] ≠ 0 := by
      rw [moserForm_self]
      exact hnd
    have h := contDiffAt_map_inverse (𝕜 := ℝ) (n := 1) (DifferentialForm.flatCLE _ hnd')
    rw [DifferentialForm.coe_flatCLE] at h
    exact h.comp x₀ ((contDiff_curryLeft E).contDiffAt.comp x₀ hΩ)
  have hu : HasFDerivAt (fun z => -(moserPrimitive ω x₀ R z))
      (0 : E →L[ℝ] (E [⋀^Fin 1]→L[ℝ] ℝ)) x₀ := by
    have := (hasFDerivAt_moserPrimitive_self hω hR).neg
    rwa [neg_zero] at this
  have h := ((hc.differentiableAt one_ne_zero).hasFDerivAt).clm_apply hu
  have h' : HasFDerivAt (moserField ω x₀ R t) _ x₀ := h
  refine h'.congr_fderiv ?_
  simp [moserPrimitive_self hω hR]

/-- **The small ball**: a radius `a` on which `‖D X_t‖ ≤ ¼` for all `t ∈ [0, 1]`, by the tube
lemma along the compact `[0, 1] × {x₀}`. -/
theorem exists_moser_small_ball (hω : ContDiffOn ℝ 1 ω (ball x₀ R)) (hR : 0 < R)
    (hnd : ∀ v : E, v ≠ 0 → ∃ u, ω x₀ ![v, u] ≠ 0) {r : ℝ} (hr0 : 0 < r)
    (hmf : ContDiffOn ℝ 1 (moserFieldJoint ω x₀ R) (Ioo (-2 : ℝ) 2 ×ˢ ball x₀ r)) :
    ∃ a, 0 < a ∧ a < r ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ closedBall x₀ a, ‖fderiv ℝ (moserField ω x₀ R t) z‖ ≤ 1 / 4 := by
  have hV : IsOpen (Ioo (-2 : ℝ) 2 ×ˢ ball x₀ r) := isOpen_Ioo.prod isOpen_ball
  -- the joint derivative is continuous on `V`
  set G : ℝ × E → E →L[ℝ] E := fun p =>
    (fderiv ℝ (moserFieldJoint ω x₀ R) p).comp (ContinuousLinearMap.inr ℝ ℝ E) with hG
  have hDc : ContinuousOn G (Ioo (-2 : ℝ) 2 ×ˢ ball x₀ r) :=
    (hmf.continuousOn_fderiv_of_isOpen hV le_rfl).clm_comp continuousOn_const
  have hP : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ q : E × ℝ in 𝓝 (x₀, t), ‖G (q.2, q.1)‖ < 1 / 4 := by
    intro t ht
    have htV : (t, x₀) ∈ Ioo (-2 : ℝ) 2 ×ˢ ball x₀ r :=
      ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, mem_ball_self hr0⟩
    have h0 : G (t, x₀) = 0 := by
      rw [hG]
      dsimp only
      rw [← fderiv_moserField_eq hmf htV.1 htV.2, (hasFDerivAt_moserField_self hω hR hnd t).fderiv]
    have hswap : ContinuousAt (fun q : E × ℝ => (q.2, q.1)) (x₀, t) :=
      continuous_swap.continuousAt
    have hcont : ContinuousAt (fun q : E × ℝ => G (q.2, q.1)) (x₀, t) :=
      ContinuousAt.comp (f := fun q : E × ℝ => (q.2, q.1)) (hDc.continuousAt (hV.mem_nhds htV))
        hswap
    have hnorm := hcont.norm.tendsto
    rw [h0, norm_zero] at hnorm
    exact hnorm.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 4)
  have hev := isCompact_Icc.eventually_forall_of_forall_eventually (x₀ := x₀)
    (P := fun z t => ‖G (t, z)‖ < 1 / 4) hP
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨min ε r / 2, by positivity, ?_, fun t ht z hz => ?_⟩
  · linarith [min_le_right ε r, min_le_left ε r]
  · have hzε : z ∈ ball x₀ ε := by
      calc dist z x₀ ≤ min ε r / 2 := hz
        _ < ε := by linarith [min_le_left ε r]
    have hzr : z ∈ ball x₀ r := by
      calc dist z x₀ ≤ min ε r / 2 := hz
        _ < r := by linarith [min_le_right ε r]
    rw [fderiv_moserField_eq hmf ⟨by linarith [ht.1], by linarith [ht.2]⟩ hzr]
    exact (hεP z hzε t ht).le

omit [FiniteDimensional ℝ E] in
/-- The time-`1` map of a flow whose field is `¼`-Lipschitz on the trajectories' ball approximates
the identity with constant `¼ e^{¼}` (the mean value inequality on the difference of two
trajectories, with the Grönwall separation). -/
theorem approximatesLinearOn_flow {f : ℝ → E → E} {a : ℝ}
    (hlip : ∀ t ∈ Icc (0 : ℝ) 1, LipschitzOnWith (1 / 4 : ℝ≥0) (f t) (closedBall x₀ a))
    {α : E → ℝ → E}
    (hα : ∀ x ∈ closedBall x₀ (a / 2), α x 0 = x ∧
      (∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (α x) (f t (α x t)) (Icc 0 1) t) ∧
      ∀ t, α x t ∈ closedBall x₀ a)
    (hsep : ∀ x ∈ closedBall x₀ (a / 2), ∀ y ∈ closedBall x₀ (a / 2), ∀ t ∈ Icc (0 : ℝ) 1,
      dist (α x t) (α y t) ≤ dist x y * Real.exp (1 / 4 * t)) :
    ApproximatesLinearOn (fun x => α x 1) (1 : E →L[ℝ] E) (ball x₀ (a / 2))
      ⟨1 / 4 * Real.exp (1 / 4), by positivity⟩ := by
  intro x hx y hy
  have hx' : x ∈ closedBall x₀ (a / 2) := ball_subset_closedBall hx
  have hy' : y ∈ closedBall x₀ (a / 2) := ball_subset_closedBall hy
  obtain ⟨hx0, hxd, hxb⟩ := hα x hx'
  obtain ⟨hy0, hyd, hyb⟩ := hα y hy'
  set g : ℝ → E := fun s => α x s - α y s - (x - y) with hg
  have hgd : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt g (f s (α x s) - f s (α y s)) (Icc 0 1) s :=
    fun s hs => ((hxd s hs).sub (hyd s hs)).sub_const _
  have hbound : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖f s (α x s) - f s (α y s)‖ ≤ 1 / 4 * Real.exp (1 / 4) * ‖x - y‖ := by
    intro s hs
    have h1 := (hlip s hs).dist_le_mul (α x s) (hxb s) (α y s) (hyb s)
    rw [dist_eq_norm, dist_eq_norm] at h1
    have h2 := hsep x hx' y hy' s hs
    rw [dist_eq_norm, dist_eq_norm] at h2
    have h3 : Real.exp (1 / 4 * s) ≤ Real.exp (1 / 4) :=
      Real.exp_le_exp.mpr (by nlinarith [hs.1, hs.2])
    calc ‖f s (α x s) - f s (α y s)‖ ≤ ((1 / 4 : ℝ≥0) : ℝ) * ‖α x s - α y s‖ := h1
      _ = 1 / 4 * ‖α x s - α y s‖ := by norm_num
      _ ≤ 1 / 4 * (‖x - y‖ * Real.exp (1 / 4 * s)) := by gcongr
      _ ≤ 1 / 4 * (‖x - y‖ * Real.exp (1 / 4)) := by gcongr
      _ = 1 / 4 * Real.exp (1 / 4) * ‖x - y‖ := by ring
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hgd hbound (convex_Icc 0 1)
    (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
  have hg0 : g 0 = 0 := by simp [hg, hx0, hy0]
  have hg1 : g 1 = α x 1 - α y 1 - (x - y) := rfl
  rw [hg0, hg1, sub_zero] at hmv
  show ‖α x 1 - α y 1 - (1 : E →L[ℝ] E) (x - y)‖ ≤ 1 / 4 * Real.exp (1 / 4) * ‖x - y‖
  rw [one_apply_eq_self]
  calc ‖α x 1 - α y 1 - (x - y)‖ ≤ 1 / 4 * Real.exp (1 / 4) * ‖x - y‖ * ‖(1 : ℝ) - 0‖ := hmv
    _ = 1 / 4 * Real.exp (1 / 4) * ‖x - y‖ := by simp

/-- The contraction constant `¼ e^{¼}` is below the inverse norm of the identity. -/
theorem quarter_exp_quarter_lt_one : (1 / 4 : ℝ) * Real.exp (1 / 4) < 1 := by
  have h1 : Real.exp (1 / 4) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
  have h2 := Real.exp_one_lt_d9
  linarith

omit [FiniteDimensional ℝ E] in
/-- The pullback of a non-degenerate form along `D` is non-degenerate only if `D` is injective:
so a derivative `D` with `ω(Φ x) ∘ D = ω(x₀)` is a linear equivalence. -/
theorem injective_of_compContinuousLinearMap_eq {ξ ξ₀ : E [⋀^Fin 2]→L[ℝ] ℝ} {D : E →L[ℝ] E}
    (hnd : ∀ v : E, v ≠ 0 → ∃ u, ξ₀ ![v, u] ≠ 0) (h : ξ.compContinuousLinearMap D = ξ₀) :
    Function.Injective D := by
  refine (injective_iff_map_eq_zero D).mpr fun v hv => ?_
  by_contra hv0
  obtain ⟨u, hu⟩ := hnd v hv0
  apply hu
  rw [← h, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  refine ContinuousAlternatingMap.map_coord_zero _ (0 : Fin 2) ?_
  simpa using hv

end Assembly

/-! ### Darboux's theorem on a ball -/

section Darboux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ω : E → E [⋀^Fin 2]→L[ℝ] ℝ} {x₀ : E} {R : ℝ}

/-- ★★ **Darboux's theorem on a ball, by Moser's trick.** If `ω` is `C¹` and closed on
`ball x₀ R` and `ω(x₀)` is non-degenerate, there is an open partial homeomorphism `Φ` of `E`
with `x₀ ∈ Φ.source ⊆ ball x₀ R`, `Φ.target ⊆ ball x₀ R` and `Φ x₀ = x₀`, `C¹` on its source
with `C¹` inverse on its target, differentiable at every point `x` of its source with an
invertible derivative `D`, such that `ω(Φ x)(D u, D v) = ω(x₀)(u, v)`: `Φ^* ω` is the constant
form `ω(x₀)`. -/
theorem exists_openPartialHomeomorph_pullback_eq (hω : ContDiffOn ℝ 1 ω (ball x₀ R))
    (hR : 0 < R) (hclosed : ∀ y ∈ ball x₀ R, extDeriv ω y = 0)
    (hnd : ∀ v : E, v ≠ 0 → ∃ u, ω x₀ ![v, u] ≠ 0) :
    ∃ Φ : OpenPartialHomeomorph E E, Φ.source ⊆ ball x₀ R ∧ Φ.target ⊆ ball x₀ R ∧
      x₀ ∈ Φ.source ∧ Φ x₀ = x₀ ∧
      ContDiffOn ℝ 1 Φ Φ.source ∧ ContDiffOn ℝ 1 Φ.symm Φ.target ∧
      ∀ x ∈ Φ.source, ∃ D : E ≃L[ℝ] E, HasFDerivAt Φ (D : E →L[ℝ] E) x ∧
        (ω (Φ x)).compContinuousLinearMap (D : E →L[ℝ] E) = ω x₀ := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  -- the ball where the interpolation is non-degenerate, and the small ball where `‖DX_t‖ ≤ ¼`
  obtain ⟨r, hr0, hrR, hndr⟩ := exists_moser_radius hω hR hnd
  have hmf := contDiffOn_moserFieldJoint hω hrR hndr
  have hmfu : ContDiffOn ℝ 1 (Function.uncurry (moserField ω x₀ R))
      (Ioo (-2 : ℝ) 2 ×ˢ ball x₀ r) := by
    rw [uncurry_moserField]
    exact hmf
  obtain ⟨a, ha, har', hDle⟩ := exists_moser_small_ball hω hR hnd hr0 hmf
  have har : closedBall x₀ a ⊆ ball x₀ r := closedBall_subset_ball har'
  have hV : IsOpen (Ioo (-2 : ℝ) 2 ×ˢ ball x₀ r) := isOpen_Ioo.prod isOpen_ball
  have hsub : Icc (0 : ℝ) 1 ×ˢ ball x₀ r ⊆ Ioo (-2 : ℝ) 2 ×ˢ ball x₀ r :=
    prod_mono (Icc_subset_Ioo (by norm_num) (by norm_num)) subset_rfl
  have htI : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Ioo (-2 : ℝ) 2 :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- the flow of Moser's field up to time `1`
  obtain ⟨α, Y, hα, hsep, hY, hYc⟩ := exists_flow_hasFDerivAt_of_norm_fderiv_le
    (f := moserField ω x₀ R) (x₀ := x₀) (a := a) (T := 1) (M := 1 / 4) ha one_pos isOpen_ball har
    (hmfu.continuousOn.mono hsub)
    (fun t ht z hz => (((contDiffAt_moserField_of_joint hmf (htI t ht) hz).differentiableAt
      one_ne_zero).hasFDerivAt))
    (by
      have h := ((hmf.continuousOn_fderiv_of_isOpen hV le_rfl).clm_comp
        (continuousOn_const (c := ContinuousLinearMap.inr ℝ ℝ E))).mono hsub
      refine h.congr fun p hp => ?_
      exact fderiv_moserField_eq hmf (htI p.1 hp.1) hp.2)
    (by norm_num) hDle (by norm_num) (fun t _ => moserField_self hω hR t)
  -- Lipschitz control of the field on the trajectories' ball
  have hlip : ∀ t ∈ Icc (0 : ℝ) 1,
      LipschitzOnWith (1 / 4 : ℝ≥0) (moserField ω x₀ R t) (closedBall x₀ a) := by
    intro t ht
    refine (convex_closedBall x₀ a).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun z hz => (contDiffAt_moserField_of_joint hmf (htI t ht) (har hz)).differentiableAt
        one_ne_zero) (fun z hz => ?_)
    have := hDle t ht z hz
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    simpa using this
  -- the time-`1` map is an open partial homeomorphism
  have happ : ApproximatesLinearOn (fun x => α x 1)
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) (ball x₀ (a / 2))
      ⟨1 / 4 * Real.exp (1 / 4), by positivity⟩ :=
    approximatesLinearOn_flow (x₀ := x₀) hlip hα hsep
  have hc : Subsingleton E ∨
      (⟨1 / 4 * Real.exp (1 / 4), by positivity⟩ : ℝ≥0) <
        ‖((ContinuousLinearEquiv.refl ℝ E).symm : E →L[ℝ] E)‖₊⁻¹ := by
    rcases subsingleton_or_nontrivial E with h | h
    · exact Or.inl h
    · right
      rw [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
        ContinuousLinearMap.nnnorm_id, inv_one]
      show ((⟨1 / 4 * Real.exp (1 / 4), by positivity⟩ : ℝ≥0) : ℝ) < ((1 : ℝ≥0) : ℝ)
      rw [NNReal.coe_one]
      exact quarter_exp_quarter_lt_one
  set Φ := happ.toOpenPartialHomeomorph (fun x => α x 1) (ball x₀ (a / 2)) hc isOpen_ball with hΦ
  have hΦs : Φ.source = ball x₀ (a / 2) := rfl
  have hΦc : ∀ x, Φ x = α x 1 := fun x => rfl
  -- the derivative at every point of the source, and the pullback identity
  have hDpt : ∀ x ∈ Φ.source, ∃ D : E ≃L[ℝ] E, HasFDerivAt Φ (D : E →L[ℝ] E) x ∧
      (ω (Φ x)).compContinuousLinearMap (D : E →L[ℝ] E) = ω x₀ := by
    intro x hx
    rw [hΦs] at hx
    obtain ⟨hY0, hYd, hYf⟩ := hY x hx
    have hxc : x ∈ closedBall x₀ (a / 2) := ball_subset_closedBall hx
    obtain ⟨hx0, hxd, hxb⟩ := hα x hxc
    -- transport of the interpolation along the flow
    have htrans := form_invariant_of_flatLieDeriv_eq_zero_timeDependent
      (f := moserField ω x₀ R) (U := ball x₀ r) (T := 1) (Ω := moserForm ω x₀)
      (fun t ht z hz => ((contDiffOn_moserForm_uncurry hω).contDiffAt
        ((isOpen_univ.prod isOpen_ball).mem_nhds
          ⟨mem_univ _, ball_subset_ball hrR hz⟩)).differentiableAt one_ne_zero)
      (fun t ht z hz m => by
        have hzR : z ∈ ball x₀ R := ball_subset_ball hrR hz
        have hXd : ContDiffAt ℝ 1 (moserField ω x₀ R t) z :=
          contDiffAt_moserField_of_joint hmf (htI t ht) hz
        have hηd : DifferentiableAt ℝ (moserDeviation ω x₀) z :=
          ((contDiffOn_moserDeviation hω).differentiableOn one_ne_zero).differentiableAt
            (isOpen_ball.mem_nhds hzR)
        have hΩd : ContDiffAt ℝ 1 (moserForm ω x₀ t) z :=
          ((contDiffOn_moserForm_uncurry hω).contDiffAt
            ((isOpen_univ.prod isOpen_ball).mem_nhds ⟨mem_univ _, hzR⟩)).comp z
            (contDiffAt_const.prodMk contDiffAt_id)
        -- Cartan
        have hLie := flatLieDeriv_eq_extDeriv_flatInteriorProduct_add hXd hΩd m
        have hint : flatInteriorProduct (moserField ω x₀ R t) (moserForm ω x₀ t)
            =ᶠ[𝓝 z] fun y => -(moserPrimitive ω x₀ R y) := by
          filter_upwards [isOpen_ball.mem_nhds hz] with y hy
          exact curryLeft_moserForm_moserField (hndr t (htI t ht) y hy)
        have hneg : extDeriv (fun y => -(moserPrimitive ω x₀ R y)) z
            = -(moserDeviation ω x₀ z) := by
          have h : (fun y => -(moserPrimitive ω x₀ R y))
              = (-1 : ℝ) • moserPrimitive ω x₀ R :=
            (neg_one_smul ℝ (moserPrimitive ω x₀ R)).symm
          rw [h, extDeriv_smul, extDeriv_moserPrimitive hω hclosed hzR, neg_one_smul]
        rw [hint.extDeriv_eq, hneg, extDeriv_moserForm hω hclosed t hzR] at hLie
        simp only [ContinuousAlternatingMap.coe_zero, Pi.zero_apply, add_zero,
          ContinuousAlternatingMap.neg_apply] at hLie
        -- the time derivative of the interpolation
        have hjoint : HasFDerivAt (Function.uncurry (moserForm ω x₀))
            ((t • ((fderiv ℝ (moserDeviation ω x₀) z).comp (ContinuousLinearMap.snd ℝ ℝ E)))
              + (ContinuousLinearMap.fst ℝ ℝ E).smulRight (moserDeviation ω x₀ z)) (t, z) := by
          have h2 : HasFDerivAt (moserDeviation ω x₀ ∘ Prod.snd)
              ((fderiv ℝ (moserDeviation ω x₀) z).comp (ContinuousLinearMap.snd ℝ ℝ E)) (t, z) :=
            hηd.hasFDerivAt.comp (t, z) hasFDerivAt_snd
          have h1 : HasFDerivAt (Prod.fst • (moserDeviation ω x₀ ∘ Prod.snd))
              ((t • ((fderiv ℝ (moserDeviation ω x₀) z).comp (ContinuousLinearMap.snd ℝ ℝ E)))
                + (ContinuousLinearMap.fst ℝ ℝ E).smulRight (moserDeviation ω x₀ z)) (t, z) :=
            hasFDerivAt_fst.smul h2
          exact h1.const_add (ω x₀)
        have hfd : fderiv ℝ (moserForm ω x₀ t) z = t • fderiv ℝ (moserDeviation ω x₀) z := by
          have h : moserForm ω x₀ t = fun y => ω x₀ + t • moserDeviation ω x₀ y := rfl
          rw [h, fderiv_const_add]
          exact (hηd.hasFDerivAt.const_smul t).fderiv
        rw [hjoint.fderiv]
        simp only [flatLieDeriv, hfd] at hLie
        simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.coe_snd', ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.coe_fst', ContinuousAlternatingMap.add_apply,
          ContinuousAlternatingMap.smul_apply, one_smul, smul_eq_mul] at hLie ⊢
        linarith)
      hx0 hxd (fun t _ => har (hxb t)) hY0 hYd 1 (right_mem_Icc.mpr zero_le_one)
    have hpull : (ω (α x 1)).compContinuousLinearMap (Y x 1) = ω x₀ := by
      ext m
      have := htrans m
      rw [moserForm_one, moserForm_zero] at this
      rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
      exact this
    have hinj : Function.Injective (Y x 1) :=
      injective_of_compContinuousLinearMap_eq hnd hpull
    let D : E ≃L[ℝ] E :=
      (LinearEquiv.ofInjectiveEndo ((Y x 1 : E →L[ℝ] E) : E →ₗ[ℝ] E) hinj).toContinuousLinearEquiv
    have hD : (D : E →L[ℝ] E) = Y x 1 := by
      ext u
      rfl
    refine ⟨D, ?_, ?_⟩
    · rw [hD]
      exact hYf 1 (right_mem_Icc.mpr zero_le_one)
    · rw [hD, hΦc]
      exact hpull
  -- the chart is `C¹`: its derivative `x ↦ Y x 1` is continuous on the source
  have hΦ1 : ∀ x ∈ Φ.source, ContDiffAt ℝ 1 Φ x := by
    intro x hx
    rw [hΦs] at hx
    exact contDiffAt_one_iff.mpr ⟨fun y => Y y 1, ball x₀ (a / 2), isOpen_ball.mem_nhds hx,
      hYc 1 (right_mem_Icc.mpr zero_le_one),
      fun y hy => (hY y hy).2.2 1 (right_mem_Icc.mpr zero_le_one)⟩
  -- and so is its inverse (the easy half of the inverse function theorem)
  have hΦs1 : ∀ y ∈ Φ.target, ContDiffAt ℝ 1 Φ.symm y := by
    intro y hy
    obtain ⟨D, hDf, -⟩ := hDpt (Φ.symm y) (Φ.map_target hy)
    exact Φ.contDiffAt_symm hy hDf (hΦ1 _ (Φ.map_target hy))
  refine ⟨Φ, ?_, ?_, ?_, ?_, fun x hx => (hΦ1 x hx).contDiffWithinAt,
    fun y hy => (hΦs1 y hy).contDiffWithinAt, hDpt⟩
  · rw [hΦs]
    exact ball_subset_ball (by linarith)
  · -- the target: the time-`1` flow stays in the closed ball
    rw [← Φ.image_source_eq_target, hΦs]
    rintro _ ⟨x, hx, rfl⟩
    rw [hΦc]
    exact ball_subset_ball hrR (har ((hα x (ball_subset_closedBall hx)).2.2 1))
  · rw [hΦs]
    exact mem_ball_self (by positivity)
  · -- `Φ x₀ = x₀`: uniqueness of the constant trajectory
    rw [hΦc]
    obtain ⟨h0, hd, hb⟩ := hα x₀ (mem_closedBall_self (by positivity))
    have huniq := ODE_solution_unique_of_mem_Icc_right (v := moserField ω x₀ R)
      (s := fun _ => closedBall x₀ a) (K := (1 / 4 : ℝ≥0)) (a := 0) (b := 1)
      (f := α x₀) (g := fun _ => x₀)
      (fun t ht => hlip t (Ico_subset_Icc_self ht))
      (fun t ht => (hd t ht).continuousWithinAt)
      (fun t ht => (hd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)))
      (fun t _ => hb t)
      continuousOn_const
      (fun t ht => by
        rw [moserField_self hω hR]
        exact hasDerivWithinAt_const _ _ _)
      (fun _ _ => mem_closedBall_self ha.le)
      (by simp [h0])
    exact huniq (right_mem_Icc.mpr zero_le_one)

/-- ★ **Darboux's theorem, read on the chart**: in the `C¹` chart `Φ⁻¹` the form is constant —
`ω y (u, v) = ω(x₀)(D(Φ⁻¹)(y) u, D(Φ⁻¹)(y) v)` at every `y ∈ Φ.target`. -/
theorem exists_openPartialHomeomorph_symm_pullback_eq (hω : ContDiffOn ℝ 1 ω (ball x₀ R))
    (hR : 0 < R) (hclosed : ∀ y ∈ ball x₀ R, extDeriv ω y = 0)
    (hnd : ∀ v : E, v ≠ 0 → ∃ u, ω x₀ ![v, u] ≠ 0) :
    ∃ Φ : OpenPartialHomeomorph E E, Φ.source ⊆ ball x₀ R ∧ Φ.target ⊆ ball x₀ R ∧
      x₀ ∈ Φ.source ∧ Φ x₀ = x₀ ∧
      ContDiffOn ℝ 1 Φ Φ.source ∧ ContDiffOn ℝ 1 Φ.symm Φ.target ∧
      ∀ y ∈ Φ.target, ∃ D : E ≃L[ℝ] E, HasFDerivAt Φ.symm (D : E →L[ℝ] E) y ∧
        ω y = (ω x₀).compContinuousLinearMap (D : E →L[ℝ] E) := by
  obtain ⟨Φ, hsub, htsub, hx₀, hfix, hΦ1, hΦs1, hD⟩ :=
    exists_openPartialHomeomorph_pullback_eq hω hR hclosed hnd
  refine ⟨Φ, hsub, htsub, hx₀, hfix, hΦ1, hΦs1, fun y hy => ?_⟩
  obtain ⟨D, hDf, hDp⟩ := hD (Φ.symm y) (Φ.map_target hy)
  refine ⟨D.symm, Φ.hasFDerivAt_symm hy hDf, ?_⟩
  rw [← hDp, Φ.right_inv hy]
  ext m
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  simp

end Darboux

/-! ### Charts of the `C^n` maximal atlas -/

section Atlas

/-- An open partial homeomorphism of the model space `E` that is `C^n` on its source with a `C^n`
inverse on its target belongs to the `C^n` groupoid of `𝓘(ℝ, E)`. -/
theorem mem_contDiffGroupoid_of_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {Φ : OpenPartialHomeomorph E E}
    (h : ContDiffOn ℝ n Φ Φ.source) (h' : ContDiffOn ℝ n Φ.symm Φ.target) :
    Φ ∈ contDiffGroupoid n 𝓘(ℝ, E) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id, Set.inter_univ]
  exact ⟨h, h'⟩

/-- A chart of the maximal atlas composed with a member of the groupoid on the model side stays
in the maximal atlas. -/
theorem StructureGroupoid.trans_mem_maximalAtlas {H M : Type*} [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M] {G : StructureGroupoid H}
    {e : OpenPartialHomeomorph M H} (he : e ∈ G.maximalAtlas M)
    {f : OpenPartialHomeomorph H H} (hf : f ∈ G) : e.trans f ∈ G.maximalAtlas M := by
  intro e' he'
  obtain ⟨h₁, h₂⟩ := he e' he'
  refine ⟨?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc]
    exact G.trans (G.symm hf) h₁
  · rw [← OpenPartialHomeomorph.trans_assoc]
    exact G.trans h₂ hf

end Atlas

/-! ### Darboux on a symplectic manifold -/

section Manifold

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

namespace DifferentialForm

/-- ★★ **Darboux's theorem on a symplectic manifold.** At every point `x₀` there is an open partial
homeomorphism `Φ` of the model space, fixing `chartAt E x₀ x₀` and contained in the chart's
target, `C¹` with `C¹` inverse, along which the local representative of the form pulls back to
the constant form `ω_loc(chartAt E x₀ x₀)`: the Darboux chart `Φ⁻¹ ∘ chartAt E x₀` contains `x₀`
and belongs to the `C¹` maximal atlas of `M`. -/
theorem IsSymplectic.exists_openPartialHomeomorph_localRep_pullback_eq
    {α : DifferentialForm (𝓘(ℝ, E)) M ∞ (Fin 2) ℝ} (hα : IsSymplectic α) (x₀ : M) :
    ∃ Φ : OpenPartialHomeomorph E E, Φ.source ⊆ (chartAt E x₀).target ∧
      Φ.target ⊆ (chartAt E x₀).target ∧
      chartAt E x₀ x₀ ∈ Φ.source ∧ Φ (chartAt E x₀ x₀) = chartAt E x₀ x₀ ∧
      ContDiffOn ℝ 1 Φ Φ.source ∧ ContDiffOn ℝ 1 Φ.symm Φ.target ∧
      x₀ ∈ ((chartAt E x₀).trans Φ.symm).source ∧
      (chartAt E x₀).trans Φ.symm ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M ∧
      ∀ w ∈ Φ.source, ∃ D : E ≃L[ℝ] E, HasFDerivAt Φ (D : E →L[ℝ] E) w ∧
        (localRep (fun x => α x) x₀ (Φ w)).compContinuousLinearMap (D : E →L[ℝ] E)
          = localRep (fun x => α x) x₀ (chartAt E x₀ x₀) := by
  have : IsManifold (𝓘(ℝ, E)) (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
  have : ContMDiffVectorBundle ∞ E (TangentSpace (𝓘(ℝ, E)) : M → Type _) (𝓘(ℝ, E)) :=
    TangentBundle.contMDiffVectorBundle
  set w₀ := chartAt E x₀ x₀ with hw₀
  have hw₀t : w₀ ∈ (chartAt E x₀).target := (chartAt E x₀).map_source (mem_chart_source E x₀)
  obtain ⟨R, hR, hRt⟩ := Metric.isOpen_iff.mp (chartAt E x₀).open_target w₀ hw₀t
  have hω : ContDiffOn ℝ 1 (localRep (fun x => α x) x₀) (ball w₀ R) := fun w hw =>
    ((contDiffAt_localRep (fun x => α x) α.contMDiff_toFun x₀ (hRt hw)).of_le
      (by simp)).contDiffWithinAt
  have hclosed : ∀ y ∈ ball w₀ R, extDeriv (localRep (fun x => α x) x₀) y = 0 :=
    fun y hy => extDeriv_localRep_eq_zero α hα x₀ (hRt hy)
  have hnd := localRep_nondegenerate α hα.nondegenerate x₀ hw₀t
  obtain ⟨Φ, hsub, htsub, hmem, hfix, hΦ1, hΦs1, hD⟩ :=
    exists_openPartialHomeomorph_pullback_eq hω hR hclosed hnd
  have hw₀Φ : w₀ ∈ Φ.target := by
    have := Φ.map_source hmem
    rwa [hfix] at this
  refine ⟨Φ, hsub.trans hRt, htsub.trans hRt, hmem, hfix, hΦ1, hΦs1, ?_, ?_, hD⟩
  · rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    exact ⟨mem_chart_source E x₀, hw₀Φ⟩
  · exact IsManifold.mem_maximalAtlas_iff.mpr (StructureGroupoid.trans_mem_maximalAtlas
      (StructureGroupoid.chart_mem_maximalAtlas (contDiffGroupoid 1 𝓘(ℝ, E)) x₀)
      ((contDiffGroupoid 1 𝓘(ℝ, E)).symm (mem_contDiffGroupoid_of_contDiffOn hΦ1 hΦs1)))

end DifferentialForm

end Manifold

end
