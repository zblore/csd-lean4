/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Fourier.MoyalBracket
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The free Wigner equation

**Category:** 1-Mathlib (CSD-free; staged for upstream).

[`Wigner.lean`](Wigner.lean) proves that the free group transports the Wigner function rigidly,
`W_{U₀(t)ψ}(x, ξ) = W_ψ(x − 2πtξ, ξ)`, and [`MoyalBracket.lean`](MoyalBracket.lean) proves that the
potential term of the Wigner equation is the Wigner transform of the commutator, with its `ℏ²`
remainder. Both are statements about the *generator*. This module (BACKLOG #64, the time-dependent
half) writes the **evolution equation itself**, for the free Hamiltonian:

* ★ `norm_mul_norm_le` — the Wigner integrand `ψ(x + y/2) conj ψ(x − y/2)` decays like `1/(1 + y²)`
  **uniformly in the position**: the two arguments differ by `y`, so
  `1 + y² ≤ 2(1 + (x + y/2)²)(1 + (x − y/2)²)` and the two Schwartz bounds
  (`exists_bound_one_add_sq`) multiply with no `x` left over;
* ★★ `hasDerivAt_wigner_left` — **the Wigner function is differentiable in the position, and
  `∂_x W_ψ = W(ψ', ψ) + W(ψ, ψ')`** (`wignerPosDeriv`), a sum of the cross Wigner functions of
  `MoyalBracket.lean`. The derivative passes under the Fourier integral by Mathlib's
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, dominated by the uniform bound above; the
  `deriv` form is `deriv_wigner_left`;
* ★ `hasDerivAt_wigner_freeSchrodingerS_pos` — the `x`-derivative of the evolved function is the
  transported `x`-derivative (the flow moves `W` rigidly, so it moves its derivative with it);
* ★★ `hasDerivAt_wigner_freeSchrodingerS_time` — the **time** derivative is `−2πξ` times that same
  transported derivative, by differentiating the transport identity in `t`;
* ★★★ `wigner_liouville` — **the free Wigner equation**:
  `∂_t W_t(x, ξ) = − 2πξ ∂_x W_t(x, ξ)` for `W_t = W_{U₀(t)ψ}`, which in the momentum `p = 2πξ` is
  `∂_t W + p ∂_x W = 0` (`wigner_liouville_add_eq_zero`) — **the classical Liouville equation, exact,
  with no quantum correction**. Both derivatives are of the same function at the same point, so this
  is a partial differential equation satisfied by the quantum phase-space density, not a pair of
  separately computed expressions.

## Honest scope

⚠️ **Free Hamiltonian only.** The interacting equation
`∂_t W_{U_V(t)ψ} = − 2πξ ∂_x W + moyalPot V ψ` is still **not** proved, and the obstacle is the
propagator, not the derivative: the corpus's propagator for `H₀ + V` is a Trotter limit on `L²`
([`Semigroup/BoundedPerturbation.lean`](../Semigroup/BoundedPerturbation.lean)) with no
differentiability in `t` on Schwartz functions, and `H₀ + V` has no generator or domain theory at the
pin (MATHLIB-ABSENT(LinearPMap.generator)). `specs/BACKLOG.md` #64 carries that half with its
measurement.

⚠️ What the pin *does* have, contrary to #64's earlier measurement, is **first-order**
differentiation under the integral sign (`Mathlib/Analysis/Calculus/ParametricIntegral.lean`), which
is all `∂_x W` needs. What is absent is the all-orders-with-bounds version — that file has no
`ContDiff` or `iteratedFDeriv` lemma at all (MATHLIB-ABSENT(contDiff_integral)) — and that, not this,
is the gap #92(a) runs into.

⚠️ One dimension, Schwartz data. No statement is made about `W` as a function of two variables
beyond the slicewise derivatives, and nothing here is a smoothness claim about `W` on the plane.

References: J. E. Moyal, *Quantum mechanics as a statistical theory*, Proc. Cambridge Philos. Soc. 45
(1949) 99 §7; M. Hillery, R. F. O'Connell, M. O. Scully, E. P. Wigner, Phys. Rep. 106 (1984) 121
§3.1 (the Wigner equation and its free case); `Wigner.lean`, `MoyalBracket.lean`;
`specs/BACKLOG.md` #64; `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory SchwartzMap Real
open scoped FourierTransform ComplexConjugate LineDeriv Topology

noncomputable section

namespace WignerFunction

/-! ### A bound on the Wigner integrand, uniform in the position -/

/-- Schwartz decay in the form the parametric derivative needs: `(1 + z²)‖f z‖` is bounded. -/
theorem exists_bound_one_add_sq (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, (1 + z ^ 2) * ‖f z‖ ≤ C := by
  obtain ⟨C₀, hC₀, h₀⟩ := f.decay 0 0
  obtain ⟨C₂, hC₂, h₂⟩ := f.decay 2 0
  refine ⟨C₀ + C₂, by positivity, fun z => ?_⟩
  have e₀ : ‖f z‖ ≤ C₀ := by simpa using h₀ z
  have e₂ : ‖z‖ ^ 2 * ‖f z‖ ≤ C₂ := by simpa using h₂ z
  have hz : ‖z‖ ^ 2 = z ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  rw [hz] at e₂
  nlinarith [norm_nonneg (f z)]

/-- ★ **The Wigner integrand decays in `y`, uniformly in the position `x`.** The two arguments
`x ± y/2` differ by `y`, so `1 + y² ≤ 2(1 + (x + y/2)²)(1 + (x − y/2)²)` and the two Schwartz bounds
multiply with no `x` left over. This uniformity is what lets the `x`-derivative pass under the
Fourier integral. -/
theorem norm_mul_norm_le {f g : 𝓢(ℝ, ℂ)} {C D : ℝ}
    (hf : ∀ z : ℝ, (1 + z ^ 2) * ‖f z‖ ≤ C) (hg : ∀ z : ℝ, (1 + z ^ 2) * ‖g z‖ ≤ D) (x y : ℝ) :
    ‖f (x + y / 2)‖ * ‖g (x - y / 2)‖ ≤ 2 * C * D * (1 + y ^ 2)⁻¹ := by
  have ha := hf (x + y / 2)
  have hb := hg (x - y / 2)
  have hC : 0 ≤ C := le_trans (by positivity) (hf 0)
  have hD : 0 ≤ D := le_trans (by positivity) (hg 0)
  have hy : (0 : ℝ) < 1 + y ^ 2 := by positivity
  have hsq : (1 : ℝ) + y ^ 2 ≤ 2 * ((1 + (x + y / 2) ^ 2) * (1 + (x - y / 2) ^ 2)) := by
    nlinarith [sq_nonneg x, sq_nonneg ((x + y / 2) * (x - y / 2))]
  have key : ‖f (x + y / 2)‖ * ‖g (x - y / 2)‖ * (1 + y ^ 2) ≤ 2 * C * D := by
    calc ‖f (x + y / 2)‖ * ‖g (x - y / 2)‖ * (1 + y ^ 2)
        ≤ ‖f (x + y / 2)‖ * ‖g (x - y / 2)‖
            * (2 * ((1 + (x + y / 2) ^ 2) * (1 + (x - y / 2) ^ 2))) := by
          gcongr
      _ = 2 * ((1 + (x + y / 2) ^ 2) * ‖f (x + y / 2)‖)
            * ((1 + (x - y / 2) ^ 2) * ‖g (x - y / 2)‖) := by ring
      _ ≤ 2 * C * D := by gcongr
  calc ‖f (x + y / 2)‖ * ‖g (x - y / 2)‖
      = ‖f (x + y / 2)‖ * ‖g (x - y / 2)‖ * (1 + y ^ 2) * (1 + y ^ 2)⁻¹ := by
        field_simp
    _ ≤ 2 * C * D * (1 + y ^ 2)⁻¹ := by gcongr

/-- The Wigner integrand is integrable: the kernel is Schwartz and the character is unimodular. -/
theorem integrable_phase_mul_kernel₂ (φ ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    Integrable fun y : ℝ => (𝐞 (-(y * ξ)) : ℂ) * (φ (x + y / 2) * conj (ψ (x - y / 2))) := by
  have hk : Integrable fun y : ℝ => wignerKernel₂ φ ψ x y := (wignerKernel₂ φ ψ x).integrable
  have hm : AEStronglyMeasurable (fun y : ℝ => (𝐞 (-(y * ξ)) : ℂ)) volume :=
    (by fun_prop : Continuous fun y : ℝ => (𝐞 (-(y * ξ)) : ℂ)).aestronglyMeasurable
  have hb : ∀ᵐ y : ℝ, ‖(𝐞 (-(y * ξ)) : ℂ)‖ ≤ 1 :=
    Filter.Eventually.of_forall fun y => le_of_eq (Circle.norm_coe _)
  simpa only [wignerKernel₂_apply] using hk.bdd_mul hm hb

/-! ### The `x`-derivative of the Wigner function -/

/-- The `x`-derivative of the Wigner function, written as a sum of cross Wigner functions:
`∂_x W_ψ = W(ψ', ψ) + W(ψ, ψ')`. That this *is* the derivative is `hasDerivAt_wigner_left`. -/
def wignerPosDeriv (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) : ℂ :=
  wigner₂ (derivCLM ℂ ℂ ψ) ψ x ξ + wigner₂ ψ (derivCLM ℂ ℂ ψ) x ξ

/-- The `x`-derivative of the integrand, pointwise in `y`: the product rule, with `conj` carried
through by `HasDerivAt.star`. -/
theorem hasDerivAt_wignerKernel_left (ψ : 𝓢(ℝ, ℂ)) (x y : ℝ) :
    HasDerivAt (fun z : ℝ => ψ (z + y / 2) * conj (ψ (z - y / 2)))
      (deriv ψ (x + y / 2) * conj (ψ (x - y / 2))
        + ψ (x + y / 2) * conj (deriv ψ (x - y / 2))) x := by
  have h1 : HasDerivAt (fun z : ℝ => ψ (z + y / 2)) (deriv ψ (x + y / 2)) x :=
    HasDerivAt.comp_add_const x (y / 2) (ψ.differentiableAt (x := x + y / 2)).hasDerivAt
  have h2 : HasDerivAt (fun z : ℝ => ψ (z - y / 2)) (deriv ψ (x - y / 2)) x :=
    HasDerivAt.comp_sub_const x (y / 2) (ψ.differentiableAt (x := x - y / 2)).hasDerivAt
  have h3 : HasDerivAt (fun z : ℝ => conj (ψ (z - y / 2))) (conj (deriv ψ (x - y / 2))) x := by
    simpa [Complex.star_def] using h2.star
  exact h1.mul h3

/-- ★★ **The Wigner function is differentiable in the position, and the derivative is a sum of
cross Wigner functions**: `∂_x W_ψ(x, ξ) = W(ψ', ψ)(x, ξ) + W(ψ, ψ')(x, ξ)`.

The derivative passes under the Fourier integral by Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, dominated by `4CD/(1 + y²)` — a bound that does
not depend on the position at all (`norm_mul_norm_le`), which is why no local-uniformity argument is
needed. -/
theorem hasDerivAt_wigner_left (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    HasDerivAt (fun z : ℝ => wigner ψ z ξ) (wignerPosDeriv ψ x ξ) x := by
  obtain ⟨C, hC, hCb⟩ := exists_bound_one_add_sq ψ
  obtain ⟨D, hD, hDb⟩ := exists_bound_one_add_sq (derivCLM ℂ ℂ ψ)
  have hcont : ∀ z : ℝ, Continuous fun y : ℝ =>
      (𝐞 (-(y * ξ)) : ℂ) * (ψ (z + y / 2) * conj (ψ (z - y / 2))) := by
    intro z
    refine (by fun_prop : Continuous fun y : ℝ => (𝐞 (-(y * ξ)) : ℂ)).mul ?_
    exact (ψ.continuous.comp (by fun_prop)).mul
      (Complex.continuous_conj.comp (ψ.continuous.comp (by fun_prop)))
  have hcont' : ∀ z : ℝ, Continuous fun y : ℝ => (𝐞 (-(y * ξ)) : ℂ) *
      (deriv ψ (z + y / 2) * conj (ψ (z - y / 2))
        + ψ (z + y / 2) * conj (deriv ψ (z - y / 2))) := by
    intro z
    have hd : Continuous fun w : ℝ => deriv ψ w := by
      have : (fun w : ℝ => deriv ψ w) = fun w : ℝ => (derivCLM ℂ ℂ ψ) w :=
        funext fun w => (SchwartzMap.derivCLM_apply ℂ ψ w).symm
      rw [this]
      exact (derivCLM ℂ ℂ ψ).continuous
    refine (by fun_prop : Continuous fun y : ℝ => (𝐞 (-(y * ξ)) : ℂ)).mul ?_
    refine Continuous.add ?_ ?_
    · exact (hd.comp (by fun_prop)).mul
        (Complex.continuous_conj.comp (ψ.continuous.comp (by fun_prop)))
    · exact (ψ.continuous.comp (by fun_prop)).mul
        (Complex.continuous_conj.comp (hd.comp (by fun_prop)))
  have hbound : ∀ᵐ y : ℝ, ∀ z ∈ Metric.ball x 1,
      ‖(𝐞 (-(y * ξ)) : ℂ) * (deriv ψ (z + y / 2) * conj (ψ (z - y / 2))
        + ψ (z + y / 2) * conj (deriv ψ (z - y / 2)))‖ ≤ 4 * C * D * (1 + y ^ 2)⁻¹ := by
    refine Filter.Eventually.of_forall fun y => fun z _ => ?_
    rw [norm_mul, Circle.norm_coe, one_mul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
    have b1 : ‖deriv ψ (z + y / 2)‖ * ‖ψ (z - y / 2)‖ ≤ 2 * D * C * (1 + y ^ 2)⁻¹ := by
      simpa only [SchwartzMap.derivCLM_apply] using norm_mul_norm_le hDb hCb z y
    have b2 : ‖ψ (z + y / 2)‖ * ‖deriv ψ (z - y / 2)‖ ≤ 2 * C * D * (1 + y ^ 2)⁻¹ := by
      simpa only [SchwartzMap.derivCLM_apply] using norm_mul_norm_le hCb hDb z y
    have : 2 * D * C * (1 + y ^ 2)⁻¹ + 2 * C * D * (1 + y ^ 2)⁻¹
        = 4 * C * D * (1 + y ^ 2)⁻¹ := by ring
    linarith
  have hbi : Integrable fun y : ℝ => 4 * C * D * (1 + y ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul (4 * C * D)
  have hdiff : ∀ᵐ y : ℝ, ∀ z ∈ Metric.ball x 1,
      HasDerivAt (fun z' : ℝ => (𝐞 (-(y * ξ)) : ℂ) * (ψ (z' + y / 2) * conj (ψ (z' - y / 2))))
        ((𝐞 (-(y * ξ)) : ℂ) * (deriv ψ (z + y / 2) * conj (ψ (z - y / 2))
          + ψ (z + y / 2) * conj (deriv ψ (z - y / 2)))) z :=
    Filter.Eventually.of_forall fun y => fun z _ =>
      (hasDerivAt_wignerKernel_left ψ z y).const_mul _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (Metric.ball_mem_nhds x one_pos)
    (Filter.Eventually.of_forall fun z => (hcont z).aestronglyMeasurable)
    (integrable_phase_mul_kernel₂ ψ ψ x ξ) (hcont' x).aestronglyMeasurable hbound hbi hdiff
  have hWeq : (fun z : ℝ => wigner ψ z ξ)
      = fun z : ℝ => ∫ y : ℝ, (𝐞 (-(y * ξ)) : ℂ) * (ψ (z + y / 2) * conj (ψ (z - y / 2))) :=
    funext fun z => wigner_eq_integral ψ z ξ
  have hsplit : (∫ y : ℝ, (𝐞 (-(y * ξ)) : ℂ) * (deriv ψ (x + y / 2) * conj (ψ (x - y / 2))
      + ψ (x + y / 2) * conj (deriv ψ (x - y / 2)))) = wignerPosDeriv ψ x ξ := by
    rw [wignerPosDeriv, wigner₂_eq_integral, wigner₂_eq_integral,
      ← integral_add (integrable_phase_mul_kernel₂ (derivCLM ℂ ℂ ψ) ψ x ξ)
        (integrable_phase_mul_kernel₂ ψ (derivCLM ℂ ℂ ψ) x ξ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [SchwartzMap.derivCLM_apply]
    ring
  rw [hWeq]
  exact key.2.congr_deriv hsplit

theorem deriv_wigner_left (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    deriv (fun z : ℝ => wigner ψ z ξ) x = wignerPosDeriv ψ x ξ :=
  (hasDerivAt_wigner_left ψ x ξ).deriv

/-! ### The free Wigner equation -/

/-- ★ The `x`-derivative of the evolved Wigner function is the transported `x`-derivative: the free
flow moves `W` rigidly, so it moves its derivative with it. -/
theorem hasDerivAt_wigner_freeSchrodingerS_pos (t : ℝ) (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    HasDerivAt (fun z : ℝ => wigner (SchrodingerGroup.freeSchrodingerS t ψ) z ξ)
      (wignerPosDeriv ψ (x - 2 * π * t * ξ) ξ) x := by
  have heq : (fun z : ℝ => wigner (SchrodingerGroup.freeSchrodingerS t ψ) z ξ)
      = fun z : ℝ => wigner ψ (z - 2 * π * t * ξ) ξ :=
    funext fun z => wigner_freeSchrodingerS t ψ z ξ
  rw [heq]
  exact HasDerivAt.comp_sub_const x (2 * π * t * ξ)
    (hasDerivAt_wigner_left ψ (x - 2 * π * t * ξ) ξ)

/-- ★★ **The time derivative of the free Wigner function** is `−2πξ` times its `x`-derivative:
differentiating the exact transport `W_t(x, ξ) = W_0(x − 2πtξ, ξ)` in the time. -/
theorem hasDerivAt_wigner_freeSchrodingerS_time (t : ℝ) (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    HasDerivAt (fun s : ℝ => wigner (SchrodingerGroup.freeSchrodingerS s ψ) x ξ)
      (-(2 * (π : ℂ) * ξ) * wignerPosDeriv ψ (x - 2 * π * t * ξ) ξ) t := by
  have heq : (fun s : ℝ => wigner (SchrodingerGroup.freeSchrodingerS s ψ) x ξ)
      = (fun u : ℝ => wigner ψ u ξ) ∘ fun s : ℝ => x - 2 * π * s * ξ :=
    funext fun s => wigner_freeSchrodingerS s ψ x ξ
  have hinner : HasDerivAt (fun s : ℝ => x - 2 * π * s * ξ) (-(2 * π * ξ)) t := by
    have h1 : HasDerivAt (fun s : ℝ => 2 * π * s * ξ) (2 * π * ξ) t := by
      simpa using ((hasDerivAt_id t).const_mul (2 * π)).mul_const ξ
    simpa using h1.const_sub x
  rw [heq]
  refine ((hasDerivAt_wigner_left ψ (x - 2 * π * t * ξ) ξ).scomp t hinner).congr_deriv ?_
  rw [Complex.real_smul]
  push_cast
  ring

/-- ★★★ **The free Wigner equation**: for `W_t = W_{U₀(t)ψ}`,
`∂_t W_t(x, ξ) = −2πξ ∂_x W_t(x, ξ)` — in the momentum `p = 2πξ`, `∂_t W + p ∂_x W = 0`, the
classical Liouville equation, exactly and with no quantum correction. Both derivatives are of the
same function at the same point: the identity closes because the free flow transports `W` rigidly
(`hasDerivAt_wigner_freeSchrodingerS_pos`). -/
theorem wigner_liouville (t : ℝ) (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    deriv (fun s : ℝ => wigner (SchrodingerGroup.freeSchrodingerS s ψ) x ξ) t
      = -(2 * (π : ℂ) * ξ)
        * deriv (fun z : ℝ => wigner (SchrodingerGroup.freeSchrodingerS t ψ) z ξ) x := by
  rw [(hasDerivAt_wigner_freeSchrodingerS_time t ψ x ξ).deriv,
    (hasDerivAt_wigner_freeSchrodingerS_pos t ψ x ξ).deriv]

/-- ★★ The same equation in the form the physics writes it: `∂_t W + p ∂_x W = 0` with `p = 2πξ`. -/
theorem wigner_liouville_add_eq_zero (t : ℝ) (ψ : 𝓢(ℝ, ℂ)) (x ξ : ℝ) :
    deriv (fun s : ℝ => wigner (SchrodingerGroup.freeSchrodingerS s ψ) x ξ) t
        + 2 * (π : ℂ) * ξ
          * deriv (fun z : ℝ => wigner (SchrodingerGroup.freeSchrodingerS t ψ) z ξ) x = 0 := by
  rw [wigner_liouville]
  ring

end WignerFunction

end

end
