/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The geometric (Aharonov–Anandan) phase of a cyclic evolution

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #10, brick BP-1 of
`specs/berry-phase-scoping.md`.

A curve `ψ : ℝ → E` of unit vectors in a complex inner product space whose rays close,
`ψ T = e^{iφ} ψ 0`, carries three phases: the **total phase** `φ`, the **dynamical phase**
`∫₀ᵀ Im⟪ψ, ψ̇⟫` (for a Schrödinger evolution `iψ̇ = Hψ`, minus the time-integrated energy), and
their difference, the **geometric phase**. `A = Im⟪ψ, dψ⟫` is the connection form of the canonical
`U(1)`-connection on the Hopf bundle `S → ℙ(E)`, so the geometric phase is its holonomy — stated
here without bundles, on the sphere:

* `connectionForm ψ t = Im⟪ψ t, ψ̇ t⟫`, `dynamicalPhase ψ T`, `geometricPhase ψ T φ = φ − ∫₀ᵀ A`,
  and `rephase θ ψ = e^{iθ} ψ`, the change of lift by a differentiable phase;
* `connectionForm_rephase` — `A` shifts by `θ'` under a rephasing (`⟪ψ, ψ⟫ = 1` is all it uses);
* ★★ `geometricPhase_rephase` — **gauge invariance**: the geometric phase of `e^{iθ} ψ` (whose
  total phase is `φ + θ T − θ 0`) equals that of `ψ`, for every differentiable `θ`. The
  geometric phase is a function of the closed curve of rays alone;
* ★ `connectionForm_horizontalLift`, ★★ `horizontalLift_cyclic` — **the geometric phase is the
  holonomy**: the horizontal lift `e^{−i∫₀ᵗ A} ψ` has `A = 0` along it and returns as
  `e^{iβ}` times its start, `β` the geometric phase;
* ★ `connectionForm_of_schrodinger`, `inner_self_const_of_schrodinger`,
  ★ `geometricPhase_of_schrodinger` — for `ψ̇ = −iHψ` with `H` self-adjoint the connection form
  is `−⟪ψ, Hψ⟫`, the energy is conserved, and `β = φ + T ⟪ψ 0, H ψ 0⟫`.

## Honest scope

⚠️ No bundle, no parallel transport as an object: the holonomy statement is the horizontal-lift
theorem on the sphere. The curvature formula `β = −∫∫ dA` is `GeometricPhaseCurvature.lean` (BP-3);
Berry's adiabatic setting (a slowly driven `H(R)`) and the Aharonov–Bohm flux are
`specs/berry-phase-scoping.md` BP-4 and BP-5.

References: Y. Aharonov, J. Anandan, PRL 58 (1987) 1593; M. V. Berry, Proc. R. Soc. A 392 (1984) 45;
B. Simon, PRL 51 (1983) 2167; `specs/berry-phase-scoping.md`; `specs/BACKLOG.md` #10.
-/

@[expose] public section

open scoped ComplexConjugate
open intervalIntegral

namespace GeometricPhase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ### The connection form, the phases, and rephasing -/

/-- The canonical connection form along a curve: `A(t) = Im ⟪ψ t, ψ̇ t⟫`. -/
noncomputable def connectionForm (ψ : ℝ → E) (t : ℝ) : ℝ :=
  (inner ℂ (ψ t) (deriv ψ t)).im

/-- The dynamical phase over `[0, T]`: `∫₀ᵀ Im ⟪ψ, ψ̇⟫`. -/
noncomputable def dynamicalPhase (ψ : ℝ → E) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, connectionForm ψ t

/-- The geometric phase of a cyclic evolution with total phase `φ`: `φ − ∫₀ᵀ Im ⟪ψ, ψ̇⟫`. -/
noncomputable def geometricPhase (ψ : ℝ → E) (T φ : ℝ) : ℝ :=
  φ - dynamicalPhase ψ T

/-- The rephased lift `e^{iθ(t)} ψ(t)`. -/
noncomputable def rephase (θ : ℝ → ℝ) (ψ : ℝ → E) (t : ℝ) : E :=
  Complex.exp ((θ t : ℂ) * Complex.I) • ψ t

theorem hasDerivAt_cexp_ofReal_mul_I {θ : ℝ → ℝ} {θ' t : ℝ} (hθ : HasDerivAt θ θ' t) :
    HasDerivAt (fun s => Complex.exp ((θ s : ℂ) * Complex.I))
      (Complex.exp ((θ t : ℂ) * Complex.I) * ((θ' : ℂ) * Complex.I)) t :=
  (hθ.ofReal_comp.mul_const Complex.I).cexp

theorem hasDerivAt_rephase {θ : ℝ → ℝ} {ψ : ℝ → E} {θ' t : ℝ} {ψ' : E}
    (hθ : HasDerivAt θ θ' t) (hψ : HasDerivAt ψ ψ' t) :
    HasDerivAt (rephase θ ψ)
      (Complex.exp ((θ t : ℂ) * Complex.I) • ψ'
        + (Complex.exp ((θ t : ℂ) * Complex.I) * ((θ' : ℂ) * Complex.I)) • ψ t) t :=
  (hasDerivAt_cexp_ofReal_mul_I hθ).smul hψ

theorem conj_cexp_mul_self (x : ℝ) :
    conj (Complex.exp ((x : ℂ) * Complex.I)) * Complex.exp ((x : ℂ) * Complex.I) = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  simp

theorem inner_self_eq_one {ψ : ℝ → E} {t : ℝ} (hunit : ‖ψ t‖ = 1) :
    inner ℂ (ψ t) (ψ t) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hunit]
  simp

/-- The connection form shifts by `θ'` under the rephasing `e^{iθ}`. -/
theorem connectionForm_rephase {θ : ℝ → ℝ} {ψ : ℝ → E} {t : ℝ}
    (hθ : DifferentiableAt ℝ θ t) (hψ : DifferentiableAt ℝ ψ t) (hunit : ‖ψ t‖ = 1) :
    connectionForm (rephase θ ψ) t = connectionForm ψ t + deriv θ t := by
  rw [connectionForm, connectionForm, (hasDerivAt_rephase hθ.hasDerivAt hψ.hasDerivAt).deriv,
    rephase, inner_smul_left, inner_add_right, inner_smul_right, inner_smul_right,
    inner_self_eq_one hunit, mul_one]
  have h : conj (Complex.exp ((θ t : ℂ) * Complex.I))
      * (Complex.exp ((θ t : ℂ) * Complex.I) * inner ℂ (ψ t) (deriv ψ t)
        + Complex.exp ((θ t : ℂ) * Complex.I) * (((deriv θ t : ℝ) : ℂ) * Complex.I))
      = inner ℂ (ψ t) (deriv ψ t) + ((deriv θ t : ℝ) : ℂ) * Complex.I := by
    rw [← mul_add, ← mul_assoc, conj_cexp_mul_self, one_mul]
  rw [h]
  simp

/-- The rephased curve is cyclic with total phase `φ + θ T − θ 0`. -/
theorem rephase_cyclic {θ : ℝ → ℝ} {ψ : ℝ → E} {T φ : ℝ}
    (hcyc : ψ T = Complex.exp ((φ : ℂ) * Complex.I) • ψ 0) :
    rephase θ ψ T = Complex.exp (((φ + (θ T - θ 0) : ℝ) : ℂ) * Complex.I) • rephase θ ψ 0 := by
  rw [rephase, rephase, hcyc, smul_smul, smul_smul, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-! ### Gauge invariance -/

variable {ψ : ℝ → E}

theorem continuous_connectionForm (hψ : ContDiff ℝ 1 ψ) : Continuous (connectionForm ψ) :=
  Complex.continuous_im.comp (hψ.continuous.inner (hψ.continuous_deriv le_rfl))

theorem dynamicalPhase_rephase {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ) (hψ : ContDiff ℝ 1 ψ)
    (hunit : ∀ t, ‖ψ t‖ = 1) (T : ℝ) :
    dynamicalPhase (rephase θ ψ) T = dynamicalPhase ψ T + (θ T - θ 0) := by
  have h : connectionForm (rephase θ ψ) = fun t => connectionForm ψ t + deriv θ t :=
    funext fun t => connectionForm_rephase (hθ.differentiable one_ne_zero t)
      (hψ.differentiable one_ne_zero t) (hunit t)
  have hA : IntervalIntegrable (connectionForm ψ) MeasureTheory.volume 0 T :=
    (continuous_connectionForm hψ).intervalIntegrable 0 T
  have hθ' : IntervalIntegrable (deriv θ) MeasureTheory.volume 0 T :=
    (hθ.continuous_deriv le_rfl).intervalIntegrable 0 T
  rw [dynamicalPhase, h, integral_add hA hθ',
    integral_eq_sub_of_hasDerivAt (fun t _ => (hθ.differentiable one_ne_zero t).hasDerivAt) hθ']
  rfl

/-- ★★ **Gauge invariance of the geometric phase.** Rephasing the lift by any differentiable
`θ` changes the total phase to `φ + θ T − θ 0` and the dynamical phase by the same amount: the
geometric phase depends on the closed curve of rays alone. -/
theorem geometricPhase_rephase {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ) (hψ : ContDiff ℝ 1 ψ)
    (hunit : ∀ t, ‖ψ t‖ = 1) (T φ : ℝ) :
    geometricPhase (rephase θ ψ) T (φ + (θ T - θ 0)) = geometricPhase ψ T φ := by
  rw [geometricPhase, geometricPhase, dynamicalPhase_rephase hθ hψ hunit]
  ring

/-! ### The horizontal lift: the geometric phase is the holonomy -/

/-- The horizontal (parallel) lift `e^{−i ∫₀ᵗ A} ψ`. -/
noncomputable def horizontalLift (ψ : ℝ → E) : ℝ → E :=
  rephase (fun t => -dynamicalPhase ψ t) ψ

theorem hasDerivAt_dynamicalPhase (hψ : ContDiff ℝ 1 ψ) (t : ℝ) :
    HasDerivAt (dynamicalPhase ψ) (connectionForm ψ t) t :=
  ((continuous_connectionForm hψ).integral_hasStrictDerivAt 0 t).hasDerivAt

theorem contDiff_neg_dynamicalPhase (hψ : ContDiff ℝ 1 ψ) :
    ContDiff ℝ 1 fun t => -dynamicalPhase ψ t := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => ((hasDerivAt_dynamicalPhase hψ t).neg).differentiableAt, ?_⟩
  have h : deriv (fun t => -dynamicalPhase ψ t) = fun t => -connectionForm ψ t :=
    funext fun t => ((hasDerivAt_dynamicalPhase hψ t).neg).deriv
  rw [h]
  exact (continuous_connectionForm hψ).neg

/-- ★ **The horizontal lift is horizontal**: its connection form vanishes. -/
theorem connectionForm_horizontalLift (hψ : ContDiff ℝ 1 ψ) (hunit : ∀ t, ‖ψ t‖ = 1) (t : ℝ) :
    connectionForm (horizontalLift ψ) t = 0 := by
  have hd : HasDerivAt (fun t => -dynamicalPhase ψ t) (-connectionForm ψ t) t :=
    (hasDerivAt_dynamicalPhase hψ t).neg
  rw [horizontalLift, connectionForm_rephase ((contDiff_neg_dynamicalPhase hψ).differentiable
    one_ne_zero t) (hψ.differentiable one_ne_zero t) (hunit t), hd.deriv]
  ring

/-- ★★ **The geometric phase is the holonomy**: the horizontal lift of a cyclic evolution returns
as `e^{iβ}` times its start, `β` the geometric phase. -/
theorem horizontalLift_cyclic {T φ : ℝ}
    (hcyc : ψ T = Complex.exp ((φ : ℂ) * Complex.I) • ψ 0) :
    horizontalLift ψ T
      = Complex.exp ((geometricPhase ψ T φ : ℂ) * Complex.I) • horizontalLift ψ 0 := by
  rw [horizontalLift, rephase_cyclic hcyc]
  congr 3
  simp only [geometricPhase, dynamicalPhase, integral_same]
  push_cast
  ring

/-! ### Schrödinger evolutions: the dynamical phase is minus the energy -/

variable {H : E →L[ℂ] E}

/-- For `ψ̇ = −iHψ`, the connection form is `−⟪ψ, Hψ⟫` (real for self-adjoint `H`). -/
theorem connectionForm_of_schrodinger {t : ℝ}
    (hψ : HasDerivAt ψ ((-Complex.I) • H (ψ t)) t) :
    connectionForm ψ t = -(inner ℂ (ψ t) (H (ψ t))).re := by
  rw [connectionForm, hψ.deriv, inner_smul_right]
  simp

/-- The energy `⟪ψ, Hψ⟫` is conserved along a Schrödinger evolution with self-adjoint `H`. -/
theorem inner_self_const_of_schrodinger (hH : ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y))
    (hψ : ∀ t, HasDerivAt ψ ((-Complex.I) • H (ψ t)) t) (s t : ℝ) :
    inner ℂ (ψ s) (H (ψ s)) = inner ℂ (ψ t) (H (ψ t)) := by
  have hd : ∀ t, HasDerivAt (fun t => inner ℂ (ψ t) (H (ψ t))) 0 t := by
    intro t
    have hHψ : HasDerivAt (⇑H ∘ ψ) (H ((-Complex.I) • H (ψ t))) t :=
      (H.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hψ t)
    have h := (hψ t).inner ℂ hHψ
    have hzero : inner ℂ (ψ t) (H ((-Complex.I) • H (ψ t)))
        + inner ℂ ((-Complex.I) • H (ψ t)) ((⇑H ∘ ψ) t) = 0 := by
      simp only [Function.comp_apply]
      rw [map_smul, inner_smul_right, inner_smul_left, ← hH (ψ t) (H (ψ t))]
      simp only [map_neg, Complex.conj_I]
      ring
    exact h.congr_deriv hzero
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) s t

/-- ★ **The geometric phase of a Schrödinger evolution**: `β = φ + T ⟪ψ 0, H ψ 0⟫` — the total
phase plus the time-integrated energy. -/
theorem geometricPhase_of_schrodinger (hH : ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y))
    (hψ : ∀ t, HasDerivAt ψ ((-Complex.I) • H (ψ t)) t) (T φ : ℝ) :
    geometricPhase ψ T φ = φ + T * (inner ℂ (ψ 0) (H (ψ 0))).re := by
  have h : connectionForm ψ = fun _ => -(inner ℂ (ψ 0) (H (ψ 0))).re := by
    funext t
    rw [connectionForm_of_schrodinger (hψ t), inner_self_const_of_schrodinger hH hψ t 0]
  rw [geometricPhase, dynamicalPhase, h, integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

end GeometricPhase

end
