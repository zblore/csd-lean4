/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceSchrodingerKilling
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceUncertainty

/-!
# Schrödinger orbits through maximal-uncertainty states are geodesics

**TERM-SCOPE(Hamiltonian)** **TERM-SCOPE(Kahler)** — this module uses the vector-field sense of
"Hamiltonian" and the restricted sense of "Kähler"; `specs/TERMS.md` records what is backed.

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold.Instances`).
BACKLOG #342 (geometric QM, completion item 8c, second half; split from #340).

For a Killing field `X`, the Koszul formula gives `⟨∇_X X, Z⟩ = −½ Z(‖X‖²)`. The Schrödinger field
`X_H` is Killing (#341) and `‖X_H‖² = 4 (ΔH)²` (#329), so `∇_{X_H} X_H` vanishes wherever
`(ΔH)²` is stationary (the converse also follows from the formula, but is not stated). At a state
of maximal uncertainty it is; the variance is conserved along the flow, so the whole orbit
`t ↦ exp(-itH) • q` consists of maximisers, and **its velocity field
is parallel along itself: the orbit is a geodesic of the Levi-Civita connection of the
Fubini–Study metric.** (For `H = i(|χ⟩⟨φ| − |φ⟩⟨χ|)` the orbit of `[φ]` is the great circle
through `φ` and `χ`.)

* `mfderiv_apply_eq_zero_of_isLocalMax` — Fermat's rule on a manifold, through the chart;
* `mdifferentiableAt_schrodingerField` — `X_H` is differentiable as a section;
  `mdifferentiableAt_variance`;
* ★★ `inner_leviCivita_schrodingerField_self` — **`⟨∇_{X_H} X_H, Z⟩ = −½ d(‖X_H‖²)(Z)`**, from
  Mathlib's Koszul formula `leviCivitaConnection_apply_inner` and #341;
* ★★★ `leviCivita_schrodingerField_self_eq_zero_of_mfderiv_variance` — **wherever `(ΔH)²` is
  stationary, `∇_{X_H} X_H = 0`**; ★★★ `leviCivita_schrodingerField_self_eq_zero_of_isLocalMax` —
  in particular at a local maximum;
* ★★★ `leviCivita_schrodingerField_self_orbit_eq_zero` — **along the Schrödinger orbit of a
  global maximiser, `∇_{X_H} X_H = 0` at every time**: with
  `isMIntegralCurve_schrodingerUnitary_smul`, the orbit is a geodesic in the sense that its
  velocity field is parallel along it.

## Honest scope

⚠️ **Geodesic, in the field sense.** "Geodesic" is stated as `∇_{X_H} X_H = 0` along an integral
curve of `X_H`, which is `∇_{γ'} γ' = 0` for that curve; the general derivative along a curve is
#339 and is not used. The identification of the orbit for `H = i(|χ⟩⟨φ| − |φ⟩⟨χ|)` with #330's
explicit great circle `t ↦ [cos t φ + sin t χ]` is not stated here.

## References

`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean` (Koszul);
`Instances/ProjectiveSpaceSchrodingerKilling.lean` (#341),
`Instances/ProjectiveSpaceUncertainty.lean` (#329),
`Instances/ProjectiveSpaceFubiniStudyRiemannianBundle.lean` (#338); `specs/BACKLOG.md` #342,
#340, #339; `specs/future-work.md`.
-/

@[expose] public section

open scoped Manifold ContDiff LinearAlgebra.Projectivization RealInnerProductSpace
open Bundle Kahler DifferentialForm VectorField Projectivization.FubiniStudy

noncomputable section

namespace Projectivization

variable {n : ℕ}

/-- **Fermat's rule on a manifold**: at a local maximum of a function differentiable there, its
derivative vanishes. -/
theorem mfderiv_apply_eq_zero_of_isLocalMax {f : ℙ ℂ (Ambient n) → ℝ} {x : ℙ ℂ (Ambient n)}
    (hf : MDifferentiableAt 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, ℝ) f x) (h : IsLocalMax f x)
    (v : TangentSpace 𝓘(ℝ, Fin n → ℂ) x) : mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, ℝ) f x v = 0 := by
  set φ := chartAt (Fin n → ℂ) x
  have hloc : IsLocalMax (f ∘ φ.symm) (φ x) := by
    have hx : φ.symm (φ x) = x := φ.left_inv (mem_chart_source _ x)
    have h' : IsLocalMax f (φ.symm (φ x)) := by rw [hx]; exact h
    exact IsMaxFilter.comp_tendsto (g := φ.symm) (b := φ x) h'
      (φ.continuousAt_symm (mem_chart_target _ x))
  rw [← fderiv_comp_chartAt_symm_trivializationAt_snd x (mem_chart_source _ x) hf v,
    hloc.fderiv_eq_zero]
  rfl

/-- The Schrödinger field is differentiable as a section of the tangent bundle. -/
theorem mdifferentiableAt_schrodingerField {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (x : ℙ ℂ (Ambient n)) :
    MDifferentiableAt 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ).tangent
      (fun q => TotalSpace.mk' (Fin n → ℂ) q (schrodingerField H q)) x := by
  rw [schrodingerField_eq_hamiltonianVectorField hH]
  exact ((fsForm_isSymplectic n).contMDiff_hamiltonianVectorField _
    (contMDiff_schrodingerHamiltonian H) x).mdifferentiableAt (by simp)

/-- ★★ **`⟨∇_{X_H} X_H, Z⟩ = −½ d(‖X_H‖²)(Z)`**: the Koszul formula for a Killing field. -/
theorem inner_leviCivita_schrodingerField_self {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (x : ℙ ℂ (Ambient n))
    {Z : ∀ q : ℙ ℂ (Ambient n), TangentSpace 𝓘(ℝ, Fin n → ℂ) q}
    (hZ : MDifferentiableAt 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ).tangent
      (fun q => TotalSpace.mk' (Fin n → ℂ) q (Z q)) x) :
    ⟪CovariantDerivative.leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))
        (schrodingerField H) x (schrodingerField H x), Z x⟫
      = -(1 / 2) * @id ℝ (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, ℝ)
          (fun q => fsMetric q (schrodingerField H q) (schrodingerField H q)) x (Z x)) := by
  have hX := mdifferentiableAt_schrodingerField hH x
  rw [CovariantDerivative.leviCivitaConnection_apply_inner _ hX hX hZ]
  have hK := mfderiv_fsMetric_schrodingerField hH x hZ
  have hswap : mlieBracket 𝓘(ℝ, Fin n → ℂ) Z (schrodingerField H) x
      = -mlieBracket 𝓘(ℝ, Fin n → ℂ) (schrodingerField H) Z x := mlieBracket_swap_apply
  have hself : mlieBracket 𝓘(ℝ, Fin n → ℂ) (schrodingerField H) (schrodingerField H) x = 0 :=
    congrFun mlieBracket_self x
  have hcomm : (fun q => ⟪Z q, schrodingerField H q⟫)
      = fun q => fsMetric q (schrodingerField H q) (Z q) := by
    funext q
    rw [real_inner_comm]
    rfl
  have hXZ : (fun q => ⟪schrodingerField H q, Z q⟫)
      = fun q => fsMetric q (schrodingerField H q) (Z q) := rfl
  have hXX : (fun q => ⟪schrodingerField H q, schrodingerField H q⟫)
      = fun q => fsMetric q (schrodingerField H q) (schrodingerField H q) := rfl
  have hin : ⟪schrodingerField H x, mlieBracket 𝓘(ℝ, Fin n → ℂ) (schrodingerField H) Z x⟫
      = fsMetric x (schrodingerField H x) (mlieBracket 𝓘(ℝ, Fin n → ℂ) (schrodingerField H) Z x) :=
    rfl
  simp only [hswap, hself, inner_zero_right, inner_neg_right, hcomm, hXZ, hXX, hin]
  erw [hK]
  simp only [id]
  ring_nf
  exact mul_comm _ _

/-- The variance is differentiable. -/
theorem mdifferentiableAt_variance (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (x : ℙ ℂ (Ambient n)) :
    MDifferentiableAt 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, ℝ) (variance H) x := by
  have h1 := mdifferentiableAt_expectation (H * H) x
  have h2 := mdifferentiableAt_expectation H x
  exact h1.sub (h2.pow 2)

/-- ★★★ **Wherever `(ΔH)²` is stationary, `∇_{X_H} X_H = 0`.** -/
theorem leviCivita_schrodingerField_self_eq_zero_of_mfderiv_variance
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : H.IsHermitian) {x : ℙ ℂ (Ambient n)}
    (hcrit : ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℂ) x,
      mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, ℝ) (variance H) x v = 0) :
    CovariantDerivative.leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))
      (schrodingerField H) x (schrodingerField H x) = 0 := by
  apply injective_inner_mdifferentiableAt_section 𝓘(ℝ, Fin n → ℂ) (Fin n → ℂ)
    (TangentSpace 𝓘(ℝ, Fin n → ℂ)) x
  funext Z hZ
  beta_reduce
  rw [inner_leviCivita_schrodingerField_self hH x hZ, inner_zero_left]
  have hf : (fun q => fsMetric q (schrodingerField H q) (schrodingerField H q))
      = (4 : ℝ) • variance H := funext fun q => by
    rw [fsMetric_schrodingerField_self hH q]
    rfl
  have hd := (mdifferentiableAt_variance H x).hasMFDerivAt.const_smul (4 : ℝ)
  rw [hf, hd.mfderiv]
  have h0 := hcrit (Z x)
  change -(1 / 2) * ((4 : ℝ) * @id ℝ (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, ℝ) (variance H) x (Z x))) = 0
  rw [show @id ℝ (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, ℝ) (variance H) x (Z x)) = 0 from h0]
  norm_num

/-- ★★★ **At a local maximum of `(ΔH)²`, `∇_{X_H} X_H = 0`.** -/
theorem leviCivita_schrodingerField_self_eq_zero_of_isLocalMax
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : H.IsHermitian) {x : ℙ ℂ (Ambient n)}
    (hmax : IsLocalMax (variance H) x) :
    CovariantDerivative.leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))
      (schrodingerField H) x (schrodingerField H x) = 0 :=
  leviCivita_schrodingerField_self_eq_zero_of_mfderiv_variance hH
    (mfderiv_apply_eq_zero_of_isLocalMax (mdifferentiableAt_variance H x) hmax)

/-- ★★★ **The Schrödinger orbit of a global maximiser of `(ΔH)²` is a geodesic**: it is an
integral curve of `X_H`, and `∇_{X_H} X_H = 0` at every point of it. (Global, so that conservation
of `(ΔH)²` makes every point of the orbit a maximiser.) -/
theorem leviCivita_schrodingerField_self_orbit_eq_zero
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : H.IsHermitian) {q : ℙ ℂ (Ambient n)}
    (hmax : ∀ p, variance H p ≤ variance H q) :
    IsMIntegralCurve (fun t : ℝ => Matrix.schrodingerUnitary hH t • q) (schrodingerField H) ∧
      ∀ t : ℝ, CovariantDerivative.leviCivitaConnection 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Ambient n))
        (schrodingerField H) (Matrix.schrodingerUnitary hH t • q)
        (schrodingerField H (Matrix.schrodingerUnitary hH t • q)) = 0 :=
  ⟨isMIntegralCurve_schrodingerUnitary_smul hH q, fun t =>
    leviCivita_schrodingerField_self_eq_zero_of_isLocalMax hH <|
      IsMaxOn.isLocalMax (s := Set.univ) (fun p _ => by
        rw [Set.mem_ofPred_eq, variance_schrodingerUnitary_smul hH]
        exact hmax p) Filter.univ_mem⟩

end Projectivization
