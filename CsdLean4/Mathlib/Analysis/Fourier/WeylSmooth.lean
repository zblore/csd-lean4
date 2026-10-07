/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Fourier.PartialFourier
public import CsdLean4.Mathlib.Analysis.Calculus.ContDiffParametricIntegral

/-!
# The Weyl operator's output is smooth

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #122, the smoothness half.

#92(a1) proved the Weyl operator's output **continuous** on the Schwartz kernel class and said that
continuity is the first of the Schwartz seminorm estimates, not the last. This is the next one: the
output is `C^∞`.

* ★★ `norm_iteratedFDeriv_comp_affine_le` and ★★ `iteratedFDeriv_comp_affine` — **the iterated chain
  rule along an affine line**, which is what the Weyl kernel needs because `x` enters `K` through
  `((x+y)/2, x−y) = (y/2, −y) + x·(1/2, 1)`: an affine path with constant velocity. Mathlib has the
  two halves (`ContinuousLinearMap.iteratedFDeriv_comp_right` for the linear part,
  `iteratedFDeriv_comp_add_left` for the translation) and not the composite;
* ★ `exists_bound_snd_iteratedFDeriv` — #92(a1)'s second-slot decay, now at every order;
* ★★★ `contDiff_weylOpK` — **the output is `C^∞`**, by #120 on each ball with the bound family the
  two previous items supply.

## Honest scope — and what the decay half is waiting for

⚠️ **This is smoothness, not Schwartzness.** `Op(K) : 𝓢(ℝ, ℂ) →L 𝓢(ℝ, ℂ)` needs the output and all
its derivatives to decay faster than every power, with the bound linear in `ψ`'s seminorms
(`SchwartzMap.mkCLM`). Nothing here gives decay of a single derivative.

⚠️ **And the obstruction is now identified, which is the useful part.** The decay estimate needs the
derivative **formula** — that `∂ˣₖ (Op(K)ψ)(x) = ∫ y, ψ y · (iteratedFDeriv ℝ k K (A y x)) (v, …, v)`
— so that the weight `xᴺ` can be moved onto the kernel through the substitution. #120 and #124
deliberately give smoothness *without* the formula; both say so in their own scope notes. So the next
brick on this row is a formula-tracking version of #120, not more estimates: the estimates are
straightforward once the formula is available, and impossible without it.

References: [`WeylSymbolClass.lean`](WeylSymbolClass.lean) (#92(a1), `weylOpK`, `exists_bound_snd`),
[`ContDiffParametricIntegral.lean`](../Calculus/ContDiffParametricIntegral.lean) (#120),
[`SchwartzSlice.lean`](SchwartzSlice.lean) (#121(i)); `specs/BACKLOG.md` #122, #92, #120, #124.
-/

@[expose] public section

open MeasureTheory SchwartzMap Metric

namespace WignerFunction

/-! ### The iterated chain rule along an affine line -/

section Affine

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- ★★ **The iterated derivative along an affine line**, as an identity: the linear part contributes
its velocity in every slot. -/
theorem iteratedFDeriv_comp_affine {K : H → E} (hK : ContDiff ℝ (⊤ : ℕ∞) K) (c v : H) (k : ℕ)
    (t : ℝ) :
    iteratedFDeriv ℝ k (fun s : ℝ => K (c + s • v)) t
      = (iteratedFDeriv ℝ k K (c + t • v)).compContinuousLinearMap
          fun _ => (1 : ℝ →L[ℝ] ℝ).smulRight v := by
  set L : ℝ →L[ℝ] H := (1 : ℝ →L[ℝ] ℝ).smulRight v with hL
  have hLapply : ∀ s : ℝ, L s = s • v := fun s => by simp [hL]
  have hKc : ContDiff ℝ (⊤ : ℕ∞) fun p : H => K (c + p) :=
    hK.comp (contDiff_const.add contDiff_id)
  have hfun : (fun s : ℝ => K (c + s • v)) = (fun p : H => K (c + p)) ∘ L := by
    funext s; simp [hLapply]
  have hcr : iteratedFDeriv ℝ k ((fun p : H => K (c + p)) ∘ L) t
      = (iteratedFDeriv ℝ k (fun p : H => K (c + p)) (L t)).compContinuousLinearMap fun _ => L :=
    L.iteratedFDeriv_comp_right hKc t (by exact_mod_cast le_top)
  rw [hfun, hcr, iteratedFDeriv_comp_add_left, hLapply]

/-- ★★ **And the bound it gives**: the velocity's norm to the order. -/
theorem norm_iteratedFDeriv_comp_affine_le {K : H → E} (hK : ContDiff ℝ (⊤ : ℕ∞) K) (c v : H)
    (k : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ k (fun s : ℝ => K (c + s • v)) t‖
      ≤ ‖iteratedFDeriv ℝ k K (c + t • v)‖ * ‖v‖ ^ k := by
  have hLnorm : ‖(1 : ℝ →L[ℝ] ℝ).smulRight v‖ = ‖v‖ := by
    simp [ContinuousLinearMap.norm_smulRight_apply]
  rw [iteratedFDeriv_comp_affine hK c v k t]
  refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
  simp [hLnorm, Finset.prod_const]

end Affine

/-! ### Second-slot decay at every order -/

/-- ★ #92(a1)'s second-slot decay, at every order of derivative. -/
theorem exists_bound_snd_iteratedFDeriv (K : 𝓢(ℝ × ℝ, ℂ)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × ℝ, ‖iteratedFDeriv ℝ k K p‖ ≤ C * (1 + p.2 ^ 2)⁻¹ := by
  obtain ⟨C₂, hC₂⟩ := K.decay 2 k
  obtain ⟨C₀, hC₀⟩ := K.decay 0 k
  refine ⟨C₀ + C₂, by linarith [hC₀.1, hC₂.1], fun p => ?_⟩
  have h2 := hC₂.2 p
  have h0 := hC₀.2 p
  rw [pow_zero, one_mul] at h0
  have hsnd : p.2 ^ 2 ≤ ‖p‖ ^ 2 := by
    have h1 : |p.2| ≤ ‖p‖ := by simpa using norm_snd_le p
    nlinarith [abs_nonneg p.2, norm_nonneg p, sq_abs p.2]
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + p.2 ^ 2)]
  nlinarith [norm_nonneg (iteratedFDeriv ℝ k K p), h2, h0, hsnd]

/-! ### The Weyl kernel as an affine path, and the output's smoothness -/

/-- The affine path the Weyl kernel's first argument travels as `x` varies. -/
theorem weylKernel_eq_affine (y x : ℝ) :
    (((x + y) / 2, x - y) : ℝ × ℝ) = ((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ)) := by
  simp [Prod.ext_iff]
  constructor <;> ring

/-- The majorant the second-slot decay supplies, uniformly on a unit ball of parameters. -/
theorem inv_one_add_sq_le_of_abs_sub_le {x₀ x y : ℝ} (hx : |x - x₀| ≤ 1) :
    (1 + (x - y) ^ 2)⁻¹ ≤ 4 * (1 + (y - x₀) ^ 2)⁻¹ := by
  have hd : (x - x₀) ^ 2 ≤ 1 := by
    have h := abs_le.1 hx
    nlinarith [h.1, h.2]
  have hkey : (1 + (y - x₀) ^ 2) / 4 ≤ 1 + (x - y) ^ 2 := by
    nlinarith [hd, sq_nonneg ((x - x₀) + (x - y)), sq_nonneg (x - y)]
  have hpos : (0 : ℝ) < (1 + (y - x₀) ^ 2) / 4 := by positivity
  calc (1 + (x - y) ^ 2)⁻¹ ≤ ((1 + (y - x₀) ^ 2) / 4)⁻¹ := by gcongr
    _ = 4 * (1 + (y - x₀) ^ 2)⁻¹ := by rw [inv_div]; ring

/-- ★★★ **The Weyl operator's output is `C^∞`.** #92(a1) gave continuity; this gives every order, by
#120 on each ball with the bound supplied by the affine chain rule and the kernel's second-slot
decay. -/
theorem contDiff_weylOpK (K : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) (m : ℕ) :
    ContDiff ℝ (m : ℕ) (weylOpK K ψ) := by
  classical
  obtain ⟨D, hD⟩ := exists_norm_le ψ
  have hD0 : 0 ≤ D := le_trans (norm_nonneg _) (hD 0)
  choose C hC0 hC using fun k => exists_bound_snd_iteratedFDeriv K k
  have hKsm : ContDiff ℝ (⊤ : ℕ∞) (K : ℝ × ℝ → ℂ) := K.smooth'
  have hvnorm : ‖((1 / 2, 1) : ℝ × ℝ)‖ = 1 := by rw [Prod.norm_def]; norm_num
  set F : ℝ → ℝ → ℂ := fun x y => K ((x + y) / 2, x - y) * ψ y with hF
  have hpathsm : ∀ y : ℝ, ContDiff ℝ (⊤ : ℕ∞)
      fun x : ℝ => K ((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ)) := fun y =>
    hKsm.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hslice : ∀ y : ℝ, (fun x => F x y)
      = (ψ y) • fun x : ℝ => K ((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ)) := by
    intro y
    funext x
    simp only [hF, Pi.smul_apply, ← weylKernel_eq_affine y x]
    simp [mul_comm]
  have hFsm : ∀ y : ℝ, ContDiff ℝ (m : ℕ) fun x => F x y := by
    intro y
    rw [hslice y]
    exact (((hpathsm y).const_smul (ψ y)).of_le (by exact_mod_cast le_top))
  -- the second slot of the affine path is `x - y`, which is what carries the decay
  have hp2 : ∀ x y : ℝ, (((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ)) : ℝ × ℝ).2 = x - y := by
    intro x y
    simp
    ring
  -- the parameter derivatives, as an identity and as a bound
  have hid : ∀ (k : ℕ) (x y : ℝ), partialDeriv F k x y
      = ψ y • (iteratedFDeriv ℝ k (fun s : ℝ =>
          K ((y / 2, -y) + s • ((1 / 2, 1) : ℝ × ℝ))) x) (fun _ => 1) := by
    intro k x y
    rw [partialDeriv_eq_iteratedDeriv, iteratedDeriv_eq_iteratedFDeriv, hslice y,
      iteratedFDeriv_const_smul_apply
        (((hpathsm y).of_le (by exact_mod_cast le_top)).contDiffAt)]
    rfl
  have hbd : ∀ (k : ℕ) (x y : ℝ),
      ‖partialDeriv F k x y‖ ≤ D * (C k * (1 + (x - y) ^ 2)⁻¹) := by
    intro k x y
    rw [hid k x y, norm_smul]
    have h1 : ‖(iteratedFDeriv ℝ k (fun s : ℝ =>
        K ((y / 2, -y) + s • ((1 / 2, 1) : ℝ × ℝ))) x) (fun _ => 1)‖
        ≤ ‖iteratedFDeriv ℝ k (fun s : ℝ =>
            K ((y / 2, -y) + s • ((1 / 2, 1) : ℝ × ℝ))) x‖ := by
      have h := (iteratedFDeriv ℝ k (fun s : ℝ =>
        K ((y / 2, -y) + s • ((1 / 2, 1) : ℝ × ℝ))) x).le_opNorm (fun _ : Fin k => (1 : ℝ))
      simpa using h
    have h2 : ‖iteratedFDeriv ℝ k (fun s : ℝ =>
        K ((y / 2, -y) + s • ((1 / 2, 1) : ℝ × ℝ))) x‖
        ≤ C k * (1 + (x - y) ^ 2)⁻¹ := by
      refine le_trans (norm_iteratedFDeriv_comp_affine_le hKsm _ _ k x) ?_
      rw [hvnorm, one_pow, mul_one]
      have hdec := hC k ((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ))
      rw [hp2 x y] at hdec
      exact hdec
    exact mul_le_mul (hD y) (le_trans h1 h2) (norm_nonneg _) hD0
  -- measurability of each parameter derivative, in the integration variable
  have hmeas : ∀ (k : ℕ) (x : ℝ), AEStronglyMeasurable (partialDeriv F k x) volume := by
    intro k x
    have heq : (fun y : ℝ => partialDeriv F k x y)
        = fun y : ℝ => ψ y • (iteratedFDeriv ℝ k (K : ℝ × ℝ → ℂ)
            ((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ))) (fun _ => ((1 / 2, 1) : ℝ × ℝ)) := by
      funext y
      rw [hid k x y, iteratedFDeriv_comp_affine hKsm]
      congr 1
      simp
    have hiter : Continuous fun p : ℝ × ℝ => iteratedFDeriv ℝ k (K : ℝ × ℝ → ℂ) p :=
      ContDiff.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top) hKsm
    have hpath : Continuous fun y : ℝ => ((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ) : ℝ × ℝ) :=
      ((continuous_id.div_const 2).prodMk continuous_neg).add continuous_const
    have hcont : Continuous fun y : ℝ => partialDeriv F k x y := by
      rw [heq]
      exact ψ.continuous.smul
        ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => ℝ × ℝ) ℂ
          (fun _ => ((1 / 2, 1) : ℝ × ℝ))).continuous.comp (hiter.comp hpath))
    exact hcont.aestronglyMeasurable
  -- assemble through #120, on a ball around each point
  rw [contDiff_iff_contDiffAt]
  intro x₀
  have hint : ∀ k : ℕ,
      Integrable (fun y : ℝ => D * (C k * (4 * (1 + (y - x₀) ^ 2)⁻¹))) volume := fun k =>
    (((integrable_inv_one_add_sq.comp_sub_right x₀).const_mul 4).const_mul (C k)).const_mul D
  have hball : ContDiffOn ℝ (m : ℕ) (fun x => ∫ y, F x y) (ball x₀ 1) := by
    refine contDiffOn_integral_of_bound m F (ball x₀ 1)
      (fun k y => D * (C k * (4 * (1 + (y - x₀) ^ 2)⁻¹))) isOpen_ball hFsm
      (fun k _ x => hmeas k x) (fun k _ => hint k) ?_
    intro k _ x hx y
    have hx' : |x - x₀| ≤ 1 := by
      rw [mem_ball, Real.dist_eq] at hx
      exact hx.le
    refine le_trans (hbd k x y) ?_
    have h4 := inv_one_add_sq_le_of_abs_sub_le (x₀ := x₀) (y := y) hx'
    gcongr
    exact hC0 k
  exact hball.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))

end WignerFunction

end
