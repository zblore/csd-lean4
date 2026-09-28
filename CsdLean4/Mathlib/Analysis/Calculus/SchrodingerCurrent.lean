/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.Complex.Basic

/-!
# The probability current, the continuity equation, and the two single-trajectory readings

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #46.

For a wavefunction `ψ(t, x)` solving `i ∂_t ψ = −½ ∂²_x ψ + V ψ` with `V` real (units `ℏ = m = 1`),
the Born density `ρ = |ψ|²` and the current `J = Im(ψ̄ ∂_x ψ)` satisfy

`∂_t ρ + ∂_x J = 0`,

and that one identity is what both single-trajectory formulations of quantum mechanics run on:

* **Bohm.** In polar form `ψ = R e^{iS}` the current is `J = R² ∂_x S = ρ v` with `v = ∂_x S` the
  guidance velocity, so the continuity equation reads `∂_t ρ + ∂_x(ρ v) = 0`: **the Born density is
  transported by the guidance field** — equivariance. Along a trajectory `ẋ = v` that is
  `dρ/dt = −ρ ∂_x v` (`deriv_probDensity_along_bohmTrajectory`), the Lagrangian form.
* **Nelson.** The same flux, split as `ρ v + ½ ∂_x ρ = ρ b` with `b = v + ½ ∂_x log ρ` the osmotic
  drift, turns the continuity equation into the **Fokker–Planck equation** of a diffusion with
  constant coefficient `½`: `∂_t ρ = −∂_x(ρ b) + ½ ∂²_x ρ` (`nelson_fokkerPlanck`). So `|ψ|²` is the
  law of Nelson's diffusion at every time, as an identity between derivatives.

Contents:

* `probDensity`, `probCurrent`;
* ★ `hasDerivAt_probCurrent` — `∂_x J = Im(ψ̄ ∂²_x ψ)`: the `Im(∂ψ̄ ∂ψ) = 0` cancellation;
* ★ `hasDerivAt_probDensity_time` — `∂_t ρ = 2 Re(ψ̄ ∂_t ψ)`;
* ★★ `continuity_equation` — `∂_t ρ + ∂_x J = 0` from the pointwise Schrödinger equation;
* `hasDerivAt_polar`, ★ `probCurrent_polar` — `J = R² ∂_x S`;
* ★★ `continuity_polar` — `∂_t ρ + ∂_x(ρ v) = 0`, **equivariance**;
* ★★ `deriv_probDensity_along_bohmTrajectory` — `dρ/dt = −ρ ∂_x v` along a Bohmian trajectory;
* ★★ `nelson_fokkerPlanck` — the Fokker–Planck form with the osmotic drift.

## Honest scope

⚠️ **One dimension.** `∂_x` is `deriv`; nothing here is stated on `ℝᵈ`, where the divergence would
have to be assembled coordinatewise.

⚠️ **The Schrödinger equation is a hypothesis, pointwise.** This module proves an identity about any
`ψ` that satisfies it at the point in question, together with the differentiability the identity
needs; it does not solve the equation and does not connect to the semigroup of
`Analysis/Semigroup/SchrodingerSchwartz.lean` (that would need the strong `L²` derivative to be read
pointwise, which is a regularity theorem, not this identity).

⚠️ **No diffusion process.** `nelson_fokkerPlanck` is the Fokker–Planck *equation*, an identity
between derivatives of `ρ`. That some diffusion process has `ρ` as its law at every time — Nelson's
theorem — needs stochastic differential equations, which Mathlib does not have at the pin
(MATHLIB-ABSENT(ProbabilityTheory.itoIntegral)): that half of BACKLOG #46 stays unclaimed, and
the row says so.

⚠️ **No trajectory existence.** `deriv_probDensity_along_bohmTrajectory` takes a trajectory as given
(a curve whose velocity is the guidance field at the point). Existence and uniqueness of Bohmian
trajectories — the flow of `v`, which is singular at the nodes of `ψ` — is not addressed.

References: D. Bohm, Phys. Rev. 85 (1952) 166, §4 (the guidance equation and equivariance);
E. Nelson, Phys. Rev. 150 (1966) 1079 (the osmotic drift and the Fokker–Planck equation);
`specs/bohm-nelson-scoping.md`; `specs/BACKLOG.md` #46; `specs/future-work.md`.
-/

@[expose] public section

open Complex

namespace Schrodinger

variable {ψ ψx : ℝ → ℝ → ℂ} {t x : ℝ}

/-- The **Born density** of a wavefunction. -/
noncomputable def probDensity (ψ : ℝ → ℝ → ℂ) (t x : ℝ) : ℝ := ‖ψ t x‖ ^ 2

/-- The **probability current** `Im(ψ̄ ∂_x ψ)`, in units `ℏ = m = 1`, read off the wavefunction and
its spatial derivative. -/
def probCurrent (ψ ψx : ℝ → ℝ → ℂ) (t x : ℝ) : ℝ := ((starRingEnd ℂ) (ψ t x) * ψx t x).im

theorem probDensity_apply (ψ : ℝ → ℝ → ℂ) (t x : ℝ) : probDensity ψ t x = ‖ψ t x‖ ^ 2 := rfl

theorem probCurrent_apply (ψ ψx : ℝ → ℝ → ℂ) (t x : ℝ) :
    probCurrent ψ ψx t x = ((starRingEnd ℂ) (ψ t x) * ψx t x).im := rfl

/-! ### The two derivatives -/

theorem probDensity_eq_re (ψ : ℝ → ℝ → ℂ) (t x : ℝ) :
    probDensity ψ t x = ((starRingEnd ℂ) (ψ t x) * ψ t x).re := by
  rw [probDensity_apply, mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- ★ **The spatial derivative of the current is `Im(ψ̄ ∂²_x ψ)`**: the term from differentiating the
conjugate is `Im(∂ψ̄ ∂ψ) = 0`, because `z̄ z` is real. -/
theorem hasDerivAt_probCurrent {ψxx : ℂ} (h1 : HasDerivAt (ψ t) (ψx t x) x)
    (h2 : HasDerivAt (ψx t) ψxx x) :
    HasDerivAt (probCurrent ψ ψx t) (((starRingEnd ℂ) (ψ t x) * ψxx).im) x := by
  have hmul : HasDerivAt (fun y => (starRingEnd ℂ) (ψ t y) * ψx t y)
      ((starRingEnd ℂ) (ψ t x) * ψxx + (starRingEnd ℂ) (ψx t x) * ψx t x) x := by
    have h := h1.star.mul h2
    rwa [add_comm] at h
  have hcancel : ((starRingEnd ℂ) (ψx t x) * ψx t x).im = 0 := by
    rw [mul_comm, Complex.mul_conj]
    exact Complex.ofReal_im _
  have him : HasDerivAt (probCurrent ψ ψx t)
      (Complex.imCLM ((starRingEnd ℂ) (ψ t x) * ψxx
        + (starRingEnd ℂ) (ψx t x) * ψx t x)) x :=
    HasFDerivAt.comp_hasDerivAt x Complex.imCLM.hasFDerivAt hmul
  refine him.congr_deriv ?_
  show ((starRingEnd ℂ) (ψ t x) * ψxx + (starRingEnd ℂ) (ψx t x) * ψx t x).im = _
  rw [Complex.add_im, hcancel, add_zero]

/-- ★ **The time derivative of the density is `2 Re(ψ̄ ∂_t ψ)`.** -/
theorem hasDerivAt_probDensity_time {ψt : ℂ} (ht : HasDerivAt (fun s => ψ s x) ψt t) :
    HasDerivAt (fun s => probDensity ψ s x) (2 * ((starRingEnd ℂ) (ψ t x) * ψt).re) t := by
  have hfun : (fun s => probDensity ψ s x) = fun s => ((starRingEnd ℂ) (ψ s x) * ψ s x).re := by
    funext s
    exact probDensity_eq_re ψ s x
  rw [hfun]
  have hmul : HasDerivAt (fun s => (starRingEnd ℂ) (ψ s x) * ψ s x)
      ((starRingEnd ℂ) (ψ t x) * ψt + (starRingEnd ℂ) ψt * ψ t x) t := by
    have h := ht.star.mul ht
    rwa [add_comm] at h
  have hconj : ((starRingEnd ℂ) ψt * ψ t x).re = ((starRingEnd ℂ) (ψ t x) * ψt).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hre : HasDerivAt (fun s => ((starRingEnd ℂ) (ψ s x) * ψ s x).re)
      (Complex.reCLM ((starRingEnd ℂ) (ψ t x) * ψt + (starRingEnd ℂ) ψt * ψ t x)) t :=
    HasFDerivAt.comp_hasDerivAt t Complex.reCLM.hasFDerivAt hmul
  refine hre.congr_deriv ?_
  show ((starRingEnd ℂ) (ψ t x) * ψt + (starRingEnd ℂ) ψt * ψ t x).re = _
  rw [Complex.add_re, hconj]
  ring

/-! ### The continuity equation -/

/-- ★★ **The continuity equation** `∂_t ρ + ∂_x J = 0`, from the Schrödinger equation at the point
with a real potential. -/
theorem continuity_equation {ψt ψxx : ℂ} {V : ℝ → ℝ}
    (h1 : HasDerivAt (ψ t) (ψx t x) x) (h2 : HasDerivAt (ψx t) ψxx x)
    (ht : HasDerivAt (fun s => ψ s x) ψt t)
    (hschr : Complex.I * ψt = -(1 / 2 : ℂ) * ψxx + (V x : ℂ) * ψ t x) :
    deriv (fun s => probDensity ψ s x) t + deriv (probCurrent ψ ψx t) x = 0 := by
  have hre_neg_I : ∀ z : ℂ, (-Complex.I * z).re = z.im := by
    intro z
    simp [Complex.mul_re]
  have hhalf : ∀ z : ℂ, (-(1 / 2 : ℂ) * z).im = -(1 / 2) * z.im := by
    intro z
    simp [Complex.mul_im]
  have hreal : ((starRingEnd ℂ) (ψ t x) * ((V x : ℂ) * ψ t x)).im = 0 := by
    have hrw : (starRingEnd ℂ) (ψ t x) * ((V x : ℂ) * ψ t x)
        = (V x : ℂ) * (ψ t x * (starRingEnd ℂ) (ψ t x)) := by ring
    rw [hrw, Complex.mul_conj]
    simp
  have hψt : ψt = -Complex.I * (-(1 / 2 : ℂ) * ψxx + (V x : ℂ) * ψ t x) := by
    rw [← hschr, ← mul_assoc]
    norm_num [Complex.I_mul_I]
  have hkey : 2 * ((starRingEnd ℂ) (ψ t x) * ψt).re = -((starRingEnd ℂ) (ψ t x) * ψxx).im := by
    have hexp : (starRingEnd ℂ) (ψ t x) * ψt
        = -Complex.I * (-(1 / 2 : ℂ) * ((starRingEnd ℂ) (ψ t x) * ψxx)
            + (starRingEnd ℂ) (ψ t x) * ((V x : ℂ) * ψ t x)) := by
      rw [hψt]
      ring
    rw [hexp, hre_neg_I, Complex.add_im, hreal, add_zero, hhalf]
    ring
  rw [(hasDerivAt_probDensity_time ht).deriv, (hasDerivAt_probCurrent h1 h2).deriv, hkey]
  ring

/-! ### Bohm: the polar form, and equivariance -/

/-- The spatial derivative of a polar-form wavefunction:
`∂_x (R e^{iS}) = (∂_x R + i R ∂_x S) e^{iS}`. -/
theorem hasDerivAt_polar {R S : ℝ → ℝ} {R' S' : ℝ} (hR : HasDerivAt R R' x)
    (hS : HasDerivAt S S' x) :
    HasDerivAt (fun y => (R y : ℂ) * Complex.exp ((S y : ℂ) * Complex.I))
      (((R' : ℂ) + Complex.I * (R x : ℂ) * (S' : ℂ)) * Complex.exp ((S x : ℂ) * Complex.I)) x := by
  have hRc : HasDerivAt (fun y => (R y : ℂ)) (R' : ℂ) x := hR.ofReal_comp
  have hSc : HasDerivAt (fun y => (S y : ℂ) * Complex.I) ((S' : ℂ) * Complex.I) x :=
    hS.ofReal_comp.mul_const Complex.I
  have hexp : HasDerivAt (fun y => Complex.exp ((S y : ℂ) * Complex.I))
      (Complex.exp ((S x : ℂ) * Complex.I) * ((S' : ℂ) * Complex.I)) x := hSc.cexp
  refine (hRc.mul hexp).congr_deriv ?_
  ring

/-- The density in polar form is `R²`. -/
theorem probDensity_polar {R S : ℝ}
    (hval : ψ t x = (R : ℂ) * Complex.exp ((S : ℂ) * Complex.I)) :
    probDensity ψ t x = R ^ 2 := by
  rw [probDensity_apply, hval, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- ★ **The current in polar form is `R² ∂_x S`** — the Born density times the guidance velocity. -/
theorem probCurrent_polar {R S R' S' : ℝ}
    (hval : ψ t x = (R : ℂ) * Complex.exp ((S : ℂ) * Complex.I))
    (hder : ψx t x
      = ((R' : ℂ) + Complex.I * (R : ℂ) * (S' : ℂ)) * Complex.exp ((S : ℂ) * Complex.I)) :
    probCurrent ψ ψx t x = R ^ 2 * S' := by
  have hconj : (starRingEnd ℂ) (ψ t x) = (R : ℂ) * Complex.exp (-((S : ℂ) * Complex.I)) := by
    rw [hval, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  have hcancel : Complex.exp (-((S : ℂ) * Complex.I)) * Complex.exp ((S : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  rw [probCurrent_apply, hconj, hder,
    show (R : ℂ) * Complex.exp (-((S : ℂ) * Complex.I))
        * (((R' : ℂ) + Complex.I * (R : ℂ) * (S' : ℂ)) * Complex.exp ((S : ℂ) * Complex.I))
        = (R : ℂ) * ((R' : ℂ) + Complex.I * (R : ℂ) * (S' : ℂ))
          * (Complex.exp (-((S : ℂ) * Complex.I)) * Complex.exp ((S : ℂ) * Complex.I)) from by
      ring,
    hcancel, mul_one,
    show (R : ℂ) * ((R' : ℂ) + Complex.I * (R : ℂ) * (S' : ℂ))
        = ((R * R' : ℝ) : ℂ) + ((R * R * S' : ℝ) : ℂ) * Complex.I from by
      push_cast
      ring,
    Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    Complex.ofReal_im, Complex.I_re]
  ring

/-- ★★ **Equivariance**: with the guidance velocity `v = ∂_x S`, the continuity equation reads
`∂_t ρ + ∂_x (ρ v) = 0` — **the Born density is transported by the guidance field**, which is Bohm's
equivariance. -/
theorem continuity_polar {R S R' S' : ℝ → ℝ} {V : ℝ → ℝ} {ψt ψxx : ℂ}
    (hval : ∀ y, ψ t y = (R y : ℂ) * Complex.exp ((S y : ℂ) * Complex.I))
    (hder : ∀ y, ψx t y = ((R' y : ℂ) + Complex.I * (R y : ℂ) * (S' y : ℂ))
      * Complex.exp ((S y : ℂ) * Complex.I))
    (h1 : HasDerivAt (ψ t) (ψx t x) x) (h2 : HasDerivAt (ψx t) ψxx x)
    (ht : HasDerivAt (fun s => ψ s x) ψt t)
    (hschr : Complex.I * ψt = -(1 / 2 : ℂ) * ψxx + (V x : ℂ) * ψ t x) :
    deriv (fun s => probDensity ψ s x) t + deriv (fun y => probDensity ψ t y * S' y) x = 0 := by
  have hJ : probCurrent ψ ψx t = fun y => probDensity ψ t y * S' y := by
    funext y
    rw [probCurrent_polar (hval y) (hder y), probDensity_polar (hval y)]
  rw [← hJ]
  exact continuity_equation h1 h2 ht hschr

/-- ★★ **Equivariance in Lagrangian form**: along a trajectory whose velocity is the guidance field,
the density obeys `dρ/dt = −ρ ∂_x v`. Stated for any density and velocity field satisfying the
continuity equation at the point, which is what `continuity_polar` provides. -/
theorem hasDerivAt_density_along_trajectory {ρ v : ℝ → ℝ → ℝ} {γ : ℝ → ℝ} {t : ℝ}
    {L : ℝ × ℝ →L[ℝ] ℝ} {ρt ρx vx : ℝ}
    (hγ : HasDerivAt γ (v t (γ t)) t)
    (hρ : HasFDerivAt (fun p : ℝ × ℝ => ρ p.1 p.2) L (t, γ t))
    (hL1 : L (1, 0) = ρt) (hL2 : L (0, 1) = ρx)
    (hcont : ρt + (ρx * v t (γ t) + ρ t (γ t) * vx) = 0) :
    HasDerivAt (fun s => ρ s (γ s)) (-(ρ t (γ t) * vx)) t := by
  have hcurve : HasDerivAt (fun s : ℝ => (s, γ s)) (1, v t (γ t)) t :=
    (hasDerivAt_id' (x := t)).prodMk hγ
  have hcomp' : HasDerivAt ((fun p : ℝ × ℝ => ρ p.1 p.2) ∘ fun s : ℝ => (s, γ s))
      (L (1, v t (γ t))) t := HasFDerivAt.comp_hasDerivAt t hρ hcurve
  have hcomp : HasDerivAt (fun s => ρ s (γ s)) (L (1, v t (γ t))) t := hcomp'
  refine hcomp.congr_deriv ?_
  have hsplit : ((1 : ℝ), v t (γ t)) = (1, 0) + v t (γ t) • ((0 : ℝ), (1 : ℝ)) := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [hsplit, map_add, map_smul, hL1, hL2, smul_eq_mul]
  linarith [hcont]

/-! ### Nelson: the osmotic drift and the Fokker–Planck equation -/

/-- **Nelson's flux** `ρ b = ρ v + ½ ∂_x ρ`: the guidance flux plus the osmotic one. -/
noncomputable def nelsonFlux (ρ ρ' v : ℝ → ℝ) (y : ℝ) : ℝ := ρ y * v y + (1 / 2) * ρ' y

/-- The osmotic drift written as a drift: where the density does not vanish,
`ρ b = ρ (v + ½ ∂_x log ρ)`. -/
theorem nelsonFlux_eq_mul_drift {ρ ρ' v : ℝ → ℝ} {y : ℝ} (hρ : ρ y ≠ 0) :
    nelsonFlux ρ ρ' v y = ρ y * (v y + (1 / 2) * (ρ' y / ρ y)) := by
  rw [nelsonFlux]
  field_simp

/-- The spatial derivative of Nelson's flux: the guidance flux's derivative plus `½ ∂²_x ρ`. -/
theorem hasDerivAt_nelsonFlux {ρ ρ' v : ℝ → ℝ} {dflux ρ'' x : ℝ}
    (hflux : HasDerivAt (fun y => ρ y * v y) dflux x) (hρ'' : HasDerivAt ρ' ρ'' x) :
    HasDerivAt (nelsonFlux ρ ρ' v) (dflux + (1 / 2) * ρ'') x := by
  exact hflux.add (hρ''.const_mul (1 / 2))

/-- ★★ **The Born density solves the Fokker–Planck equation of Nelson's diffusion.** With the
osmotic drift `b = v + ½ ∂_x log ρ`, so that the flux is `nelsonFlux`, the continuity equation
`∂_t ρ + ∂_x(ρ v) = 0` becomes

`∂_t ρ = −∂_x(ρ b) + ½ ∂²_x ρ`,

the Fokker–Planck equation of a diffusion with constant coefficient `½`: the osmotic term of the
drift is exactly what cancels the diffusion term. `ρ'` is the density's spatial derivative and `ρ''`
its second. -/
theorem nelson_fokkerPlanck {v ρ' : ℝ → ℝ} {dflux ρ'' ρt : ℝ}
    (hflux : HasDerivAt (fun y => probDensity ψ t y * v y) dflux x)
    (hρ'' : HasDerivAt ρ' ρ'' x)
    (hcont : ρt + dflux = 0) :
    ρt = -deriv (nelsonFlux (probDensity ψ t) ρ' v) x + (1 / 2) * ρ'' := by
  rw [(hasDerivAt_nelsonFlux hflux hρ'').deriv]
  linarith

end Schrodinger

end
