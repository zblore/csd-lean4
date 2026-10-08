/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Fourier.PartialFourier
public import CsdLean4.Mathlib.Analysis.Calculus.ContDiffParametricIntegral

/-!
# The Weyl operator maps Schwartz space to Schwartz space

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #122, both halves.

#92(a1) proved the Weyl operator's output **continuous** on the Schwartz kernel class and said that
continuity is the first of the Schwartz seminorm estimates, not the last. This file proves the rest
of them and assembles the operator.

**The smoothness half.**
* ★★ `iteratedFDeriv_comp_affine` and ★★ `norm_iteratedFDeriv_comp_affine_le` — **the iterated chain
  rule along an affine line**, which is what the Weyl kernel needs because `x` enters `K` through
  `((x+y)/2, x−y) = (y/2, −y) + x·(1/2, 1)`: an affine path with constant velocity. Mathlib has the
  two halves (`ContinuousLinearMap.iteratedFDeriv_comp_right` for the linear part,
  `iteratedFDeriv_comp_add_left` for the translation) and not the composite;
* ★ `exists_bound_snd_iteratedFDeriv` — #92(a1)'s second-slot decay, now at every order;
* ★★ `partialDeriv_weylIntegrand` and ★★ `norm_partialDeriv_weylIntegrand_le` — the integrand's
  parameter derivatives, as an identity and in the primitive bound *both* halves run on;
* ★★★ `contDiff_weylOpK` — **the output is `C^∞`**, by #120 on each ball with the bound family the
  previous items supply.

**The decay half**, which #122 first recorded as blocked on a derivative *formula*. #125 supplied the
formula, and this is what it buys:
* ★★ `iteratedDeriv_weylOpK` — #125's formula on this integrand, so that a weight has something to
  move onto;
* ★ `abs_le_norm_weylPath` — `|x| ≤ (3/2)·‖A y x‖`: the weight moves off the parameter and onto the
  kernel, which is the one inequality the whole half turns on;
* ★★ `exists_bound_snd_iteratedFDeriv_weighted` — the kernel's decay at orders `N` and `N + 2`
  combined into a weighted bound that still has an integrable profile in the second slot;
* ★★★ `exists_bound_weylOpK` — **every derivative decays in every weight**, with the constant
  depending only on `K` and the bound *linear in one seminorm of the state*, which is the shape
  `SchwartzMap.mkCLM` consumes;
* ★★★ `weylCLM` — **`Op(K) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)`**, row 122's statement.

## Honest scope

⚠️ **One kernel class.** `weylCLM` is the operator of a *jointly Schwartz* kernel. Weyl quantisation
of a wider symbol class (polynomially bounded symbols, Hörmander classes) is a different theorem and
is not proved here; #92's slicing caveat in `WeylSymbolClass.lean` still stands as written.

⚠️ **The constant is not sharp.** `(3/2)ᴺ·C·π` falls out of this route, not out of an optimisation.

⚠️ **Nothing about composition.** That `Op(a) ∘ Op(b)` is again a Weyl operator — the Moyal product —
is a separate brick and is not proved here; `WignerCalculus.lean` carries the ℏ² statement this file
does not touch.

References: [`WeylSymbolClass.lean`](WeylSymbolClass.lean) (#92(a1), `weylOpK`, `exists_bound_snd`),
[`ContDiffParametricIntegral.lean`](../Calculus/ContDiffParametricIntegral.lean) (#120 and #125,
`partialDeriv`, `contDiffOn_integral_of_bound`, `iteratedDeriv_integral_of_bound_le`),
[`SchwartzSlice.lean`](SchwartzSlice.lean) (#121(i)); `specs/BACKLOG.md` #122, #92, #120, #125.
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

/-! ### The Weyl kernel as an affine path -/

/-- The affine path the Weyl kernel's argument travels as `x` varies. -/
theorem weylKernel_eq_affine (y x : ℝ) :
    (((x + y) / 2, x - y) : ℝ × ℝ) = ((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ)) := by
  simp [Prod.ext_iff]
  constructor <;> ring

/-- The path's velocity is a unit vector, which is why no power of it appears in any bound. -/
theorem norm_weylVelocity : ‖((1 / 2, 1) : ℝ × ℝ)‖ = 1 := by rw [Prod.norm_def]; norm_num

/-- The second slot of the path is `x - y`, which is what carries the decay. -/
theorem snd_weylPath (x y : ℝ) :
    (((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ)) : ℝ × ℝ).2 = x - y := by
  simp
  ring

/-- ★ **The weight transfers to the path.** `|x| ≤ (3/2)‖path‖`, so a polynomial weight in `x` can be
moved onto the kernel — which is what the decay estimate runs on. -/
theorem abs_le_norm_weylPath (x y : ℝ) :
    |x| ≤ 3 / 2 * ‖(((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ)) : ℝ × ℝ)‖ := by
  set p : ℝ × ℝ := ((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ)) with hp
  have h1 : p.1 = (x + y) / 2 := by rw [hp]; simp; ring
  have h2 : p.2 = x - y := snd_weylPath x y
  have hb1 : |p.1| ≤ ‖p‖ := by simpa using norm_fst_le p
  have hb2 : |p.2| ≤ ‖p‖ := by simpa using norm_snd_le p
  rw [h1] at hb1
  rw [h2] at hb2
  have c1 := abs_le.1 hb1
  have c2 := abs_le.1 hb2
  refine abs_le.2 ⟨by linarith [c1.1, c2.1], by linarith [c1.2, c2.2]⟩

/-- The path is smooth in the parameter. -/
theorem contDiff_weylPath (K : 𝓢(ℝ × ℝ, ℂ)) (y : ℝ) : ContDiff ℝ (⊤ : ℕ∞)
    fun x : ℝ => K ((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ)) :=
  (K.smooth' : ContDiff ℝ (⊤ : ℕ∞) (K : ℝ × ℝ → ℂ)).comp
    (contDiff_const.add (contDiff_id.smul contDiff_const))

/-! ### The integrand, its parameter derivatives, and the bound they obey -/

/-- The Weyl operator's integrand. -/
noncomputable def weylIntegrand (K : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) : ℝ → ℝ → ℂ :=
  fun x y => K ((x + y) / 2, x - y) * ψ y

theorem weylOpK_eq_integral (K : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) :
    weylOpK K ψ = fun x => ∫ y, weylIntegrand K ψ x y := rfl

theorem weylIntegrand_slice (K : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) (y : ℝ) :
    (fun x => weylIntegrand K ψ x y)
      = (ψ y) • fun x : ℝ => K ((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ)) := by
  funext x
  simp only [weylIntegrand, Pi.smul_apply, ← weylKernel_eq_affine y x]
  simp [mul_comm]

theorem contDiff_weylIntegrand (K : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) (m : ℕ) (y : ℝ) :
    ContDiff ℝ (m : ℕ) fun x => weylIntegrand K ψ x y := by
  rw [weylIntegrand_slice K ψ y]
  exact (((contDiff_weylPath K y).const_smul (ψ y)).of_le (by exact_mod_cast le_top))

/-- ★★ **The parameter derivatives of the integrand, as an identity.** `ψ` does not depend on the
parameter, so no product rule enters: the whole `x`-dependence is the affine path. -/
theorem partialDeriv_weylIntegrand (K : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) (k : ℕ) (x y : ℝ) :
    partialDeriv (weylIntegrand K ψ) k x y
      = ψ y • (iteratedFDeriv ℝ k (fun s : ℝ =>
          K ((y / 2, -y) + s • ((1 / 2, 1) : ℝ × ℝ))) x) (fun _ => 1) := by
  rw [partialDeriv_eq_iteratedDeriv, iteratedDeriv_eq_iteratedFDeriv,
    weylIntegrand_slice K ψ y,
    iteratedFDeriv_const_smul_apply
      (((contDiff_weylPath K y).of_le (by exact_mod_cast le_top)).contDiffAt)]
  rfl

/-- ★★ **The bound they obey**, in the primitive form both halves of #122 use: the state's value
times the kernel's `k`-th derivative at the path point. The velocity contributes nothing because it
is a unit vector. -/
theorem norm_partialDeriv_weylIntegrand_le (K : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) (k : ℕ) (x y : ℝ) :
    ‖partialDeriv (weylIntegrand K ψ) k x y‖
      ≤ ‖ψ y‖ * ‖iteratedFDeriv ℝ k (K : ℝ × ℝ → ℂ)
          ((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ))‖ := by
  rw [partialDeriv_weylIntegrand, norm_smul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h1 : ‖(iteratedFDeriv ℝ k (fun s : ℝ =>
      K ((y / 2, -y) + s • ((1 / 2, 1) : ℝ × ℝ))) x) (fun _ => 1)‖
      ≤ ‖iteratedFDeriv ℝ k (fun s : ℝ =>
          K ((y / 2, -y) + s • ((1 / 2, 1) : ℝ × ℝ))) x‖ := by
    have h := (iteratedFDeriv ℝ k (fun s : ℝ =>
      K ((y / 2, -y) + s • ((1 / 2, 1) : ℝ × ℝ))) x).le_opNorm (fun _ : Fin k => (1 : ℝ))
    simpa using h
  refine le_trans h1 ?_
  have hKsm : ContDiff ℝ (⊤ : ℕ∞) (K : ℝ × ℝ → ℂ) := K.smooth'
  refine le_trans (norm_iteratedFDeriv_comp_affine_le hKsm _ _ k x) ?_
  rw [norm_weylVelocity, one_pow, mul_one]

theorem aestronglyMeasurable_partialDeriv_weylIntegrand (K : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ))
    (k : ℕ) (x : ℝ) :
    AEStronglyMeasurable (partialDeriv (weylIntegrand K ψ) k x) volume := by
  have hKsm : ContDiff ℝ (⊤ : ℕ∞) (K : ℝ × ℝ → ℂ) := K.smooth'
  have heq : partialDeriv (weylIntegrand K ψ) k x
      = fun y : ℝ => ψ y • (iteratedFDeriv ℝ k (K : ℝ × ℝ → ℂ)
          ((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ))) (fun _ => ((1 / 2, 1) : ℝ × ℝ)) := by
    funext y
    rw [partialDeriv_weylIntegrand]
    congr 1
    rw [show (fun s : ℝ => K ((y / 2, -y) + s • ((1 / 2, 1) : ℝ × ℝ)))
        = (fun s : ℝ => (K : ℝ × ℝ → ℂ) ((y / 2, -y) + s • ((1 / 2, 1) : ℝ × ℝ))) from rfl,
      iteratedFDeriv_comp_affine hKsm,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext _
    simp
  have hiter : Continuous fun p : ℝ × ℝ => iteratedFDeriv ℝ k (K : ℝ × ℝ → ℂ) p :=
    ContDiff.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top) hKsm
  have hpath : Continuous fun y : ℝ => ((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ) : ℝ × ℝ) :=
    ((continuous_id.div_const 2).prodMk continuous_neg).add continuous_const
  rw [heq]
  refine Continuous.aestronglyMeasurable ?_
  exact ψ.continuous.smul
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => ℝ × ℝ) ℂ
      (fun _ => ((1 / 2, 1) : ℝ × ℝ))).continuous.comp (hiter.comp hpath))

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

/-- The dominating bound both #120 statements consume, assembled once: on a unit ball of parameters
every parameter derivative is dominated by an integrable profile in the integration variable. -/
theorem exists_weylIntegrand_ball_bound (K : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) (x₀ : ℝ) :
    ∃ bound : ℕ → ℝ → ℝ, (∀ k, Integrable (bound k) volume) ∧
      ∀ (k : ℕ), ∀ x ∈ ball x₀ 1, ∀ y, ‖partialDeriv (weylIntegrand K ψ) k x y‖ ≤ bound k y := by
  classical
  obtain ⟨D, hD⟩ := exists_norm_le ψ
  have hD0 : 0 ≤ D := le_trans (norm_nonneg _) (hD 0)
  choose C hC0 hC using fun k => exists_bound_snd_iteratedFDeriv K k
  refine ⟨fun k y => D * (C k * (4 * (1 + (y - x₀) ^ 2)⁻¹)), fun k =>
    (((integrable_inv_one_add_sq.comp_sub_right x₀).const_mul 4).const_mul (C k)).const_mul D,
    fun k x hx y => ?_⟩
  have hbd : ‖partialDeriv (weylIntegrand K ψ) k x y‖ ≤ D * (C k * (1 + (x - y) ^ 2)⁻¹) := by
    refine le_trans (norm_partialDeriv_weylIntegrand_le K ψ k x y) ?_
    have hdec := hC k ((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ))
    rw [snd_weylPath x y] at hdec
    exact mul_le_mul (hD y) hdec (norm_nonneg _) hD0
  have hx' : |x - x₀| ≤ 1 := by
    rw [mem_ball, Real.dist_eq] at hx
    exact hx.le
  refine le_trans hbd ?_
  show D * (C k * (1 + (x - y) ^ 2)⁻¹) ≤ D * (C k * (4 * (1 + (y - x₀) ^ 2)⁻¹))
  have h4 := inv_one_add_sq_le_of_abs_sub_le (x₀ := x₀) (y := y) hx'
  gcongr
  exact hC0 k

/-- ★★★ **The Weyl operator's output is `C^∞`.** #92(a1) gave continuity; this gives every order, by
#120 on each ball with the bound supplied by the affine chain rule and the kernel's second-slot
decay. -/
theorem contDiff_weylOpK (K : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) (m : ℕ) :
    ContDiff ℝ (m : ℕ) (weylOpK K ψ) := by
  rw [contDiff_iff_contDiffAt]
  intro x₀
  obtain ⟨bound, hint, hbd⟩ := exists_weylIntegrand_ball_bound K ψ x₀
  have hball : ContDiffOn ℝ (m : ℕ) (fun x => ∫ y, weylIntegrand K ψ x y) (ball x₀ 1) :=
    contDiffOn_integral_of_bound m (weylIntegrand K ψ) (ball x₀ 1) bound isOpen_ball
      (fun y => contDiff_weylIntegrand K ψ m y)
      (fun k _ x => aestronglyMeasurable_partialDeriv_weylIntegrand K ψ k x)
      (fun k _ => hint k) (fun k _ x hx y => hbd k x hx y)
  exact hball.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))

/-- ★★ **#125's formula on this integrand**: every derivative of the output is the integral of the
corresponding parameter derivative. The decay estimate is stated on the right-hand side, which is
why the smoothness statement above is not enough on its own. -/
theorem iteratedDeriv_weylOpK (K : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (weylOpK K ψ) x = ∫ y, partialDeriv (weylIntegrand K ψ) k x y := by
  obtain ⟨bound, hint, hbd⟩ := exists_weylIntegrand_ball_bound K ψ x
  rw [weylOpK_eq_integral]
  exact iteratedDeriv_integral_of_bound_le (U := ball x 1) (n := k) isOpen_ball
    (fun y => contDiff_weylIntegrand K ψ k y)
    (fun j _ z => aestronglyMeasurable_partialDeriv_weylIntegrand K ψ j z)
    (fun j _ => hint j) (fun j _ z hz y => hbd j z hz y) le_rfl (mem_ball_self one_pos)

/-! ### The output's decay

Smoothness alone does not make `Op(K) ψ` a Schwartz function: every derivative must decay in every
polynomial weight too. The weight moves off the parameter and onto the kernel through
`abs_le_norm_weylPath`, the kernel's own decay at two orders apart supplies a majorant that is still
integrable in the integration variable, and `∫ (1 + y²)⁻¹ = π` finishes it. The constant comes out
depending only on the kernel, and the bound *linear in a single seminorm of the state* — which is
exactly the hypothesis `SchwartzMap.mkCLM` consumes. -/

/-- ★★ **Weighted second-slot decay.** `exists_bound_snd_iteratedFDeriv` is the case `N = 0`: the
kernel's decay at orders `N` and `N + 2` combine into a bound that already carries the weight
`‖p‖ ^ N` and still decays in the second slot. -/
theorem exists_bound_snd_iteratedFDeriv_weighted (K : 𝓢(ℝ × ℝ, ℂ)) (N k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × ℝ,
      ‖p‖ ^ N * ‖iteratedFDeriv ℝ k K p‖ ≤ C * (1 + p.2 ^ 2)⁻¹ := by
  obtain ⟨C₂, hC₂⟩ := K.decay (N + 2) k
  obtain ⟨C₀, hC₀⟩ := K.decay N k
  refine ⟨C₀ + C₂, by linarith [hC₀.1, hC₂.1], fun p => ?_⟩
  have h2 := hC₂.2 p
  have h0 := hC₀.2 p
  rw [pow_add] at h2
  have hsnd : p.2 ^ 2 ≤ ‖p‖ ^ 2 := by
    have h1 : |p.2| ≤ ‖p‖ := by simpa using norm_snd_le p
    nlinarith [abs_nonneg p.2, norm_nonneg p, sq_abs p.2]
  have hq : 0 ≤ ‖p‖ ^ N * ‖iteratedFDeriv ℝ k K p‖ := by positivity
  have hstep : ‖p‖ ^ N * ‖iteratedFDeriv ℝ k K p‖ * p.2 ^ 2
      ≤ ‖p‖ ^ N * ‖iteratedFDeriv ℝ k K p‖ * ‖p‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hsnd hq
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + p.2 ^ 2)]
  nlinarith [h0, h2, hstep]

/-- A real scalar can be moved under a norm, which is how the weight gets inside the integral. -/
theorem norm_real_smul_eq {t : ℝ} (z : ℂ) (ht : 0 ≤ t) : t * ‖z‖ = ‖t • z‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]

/-- ★★★ **Every derivative of the output decays, in every weight.** The constant depends only on
the kernel and the bound is linear in one seminorm of the state: this is the Schwartz seminorm
estimate #92(a1) called continuity the first of, now at every order and weight. -/
theorem exists_bound_weylOpK (K : 𝓢(ℝ × ℝ, ℂ)) (N k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : 𝓢(ℝ, ℂ)) (x : ℝ),
      ‖x‖ ^ N * ‖iteratedFDeriv ℝ k (weylOpK K ψ) x‖
        ≤ C * SchwartzMap.seminorm ℂ 0 0 ψ := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_snd_iteratedFDeriv_weighted K N k
  refine ⟨(3 / 2) ^ N * C * Real.pi, by positivity, fun ψ x => ?_⟩
  have hS0 : 0 ≤ SchwartzMap.seminorm ℂ 0 0 ψ :=
    le_trans (norm_nonneg _) (SchwartzMap.norm_le_seminorm ℂ ψ 0)
  have ht0 : (0 : ℝ) ≤ ‖x‖ ^ N := by positivity
  have hmajint : Integrable
      (fun y : ℝ => (3 / 2) ^ N * (C * SchwartzMap.seminorm ℂ 0 0 ψ) * (1 + (y - x) ^ 2)⁻¹)
      volume := (integrable_inv_one_add_sq.comp_sub_right x).const_mul _
  have hmajval : ∫ y : ℝ, (3 / 2) ^ N * (C * SchwartzMap.seminorm ℂ 0 0 ψ)
        * (1 + (y - x) ^ 2)⁻¹
      = (3 / 2) ^ N * C * Real.pi * SchwartzMap.seminorm ℂ 0 0 ψ := by
    rw [integral_const_mul, integral_sub_right_eq_self (fun y : ℝ => (1 + y ^ 2)⁻¹) x,
      integral_univ_inv_one_add_sq]
    ring
  -- the pointwise estimate, with the weight already transferred to the kernel
  have hpt : ∀ y : ℝ, ‖(‖x‖ ^ N : ℝ) • partialDeriv (weylIntegrand K ψ) k x y‖
      ≤ (3 / 2) ^ N * (C * SchwartzMap.seminorm ℂ 0 0 ψ) * (1 + (y - x) ^ 2)⁻¹ := by
    intro y
    have hw : ‖x‖ ^ N ≤ (3 / 2) ^ N * ‖((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ) : ℝ × ℝ)‖ ^ N := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (norm_nonneg x) ?_ N
      rw [Real.norm_eq_abs]
      exact abs_le_norm_weylPath x y
    have hdec : ‖((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ) : ℝ × ℝ)‖ ^ N
        * ‖iteratedFDeriv ℝ k (K : ℝ × ℝ → ℂ) ((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ))‖
        ≤ C * (1 + (y - x) ^ 2)⁻¹ := by
      have h := hC ((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ))
      rw [snd_weylPath x y, show (x - y) ^ 2 = (y - x) ^ 2 from by ring] at h
      exact h
    rw [← norm_real_smul_eq _ ht0]
    calc ‖x‖ ^ N * ‖partialDeriv (weylIntegrand K ψ) k x y‖
        ≤ ((3 / 2) ^ N * ‖((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ) : ℝ × ℝ)‖ ^ N)
            * (‖ψ y‖ * ‖iteratedFDeriv ℝ k (K : ℝ × ℝ → ℂ)
                ((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ))‖) :=
          mul_le_mul hw (norm_partialDeriv_weylIntegrand_le K ψ k x y) (norm_nonneg _)
            (by positivity)
      _ = (3 / 2) ^ N * ‖ψ y‖
            * (‖((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ) : ℝ × ℝ)‖ ^ N
              * ‖iteratedFDeriv ℝ k (K : ℝ × ℝ → ℂ)
                  ((y / 2, -y) + x • ((1 / 2, 1) : ℝ × ℝ))‖) := by ring
      _ ≤ (3 / 2) ^ N * SchwartzMap.seminorm ℂ 0 0 ψ * (C * (1 + (y - x) ^ 2)⁻¹) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℂ ψ y)
            (by positivity)) hdec (by positivity) (mul_nonneg (by positivity) hS0)
      _ = (3 / 2) ^ N * (C * SchwartzMap.seminorm ℂ 0 0 ψ) * (1 + (y - x) ^ 2)⁻¹ := by ring
  calc ‖x‖ ^ N * ‖iteratedFDeriv ℝ k (weylOpK K ψ) x‖
      = ‖x‖ ^ N * ‖iteratedDeriv k (weylOpK K ψ) x‖ := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    _ = ‖(‖x‖ ^ N : ℝ) • ∫ y, partialDeriv (weylIntegrand K ψ) k x y‖ := by
        rw [iteratedDeriv_weylOpK]
        exact norm_real_smul_eq _ ht0
    _ = ‖∫ y, (‖x‖ ^ N : ℝ) • partialDeriv (weylIntegrand K ψ) k x y‖ := by
        rw [integral_smul]
    _ ≤ ∫ y : ℝ, (3 / 2) ^ N * (C * SchwartzMap.seminorm ℂ 0 0 ψ) * (1 + (y - x) ^ 2)⁻¹ :=
        norm_integral_le_of_norm_le hmajint (Filter.Eventually.of_forall hpt)
    _ = (3 / 2) ^ N * C * Real.pi * SchwartzMap.seminorm ℂ 0 0 ψ := hmajval

/-! ### The operator on Schwartz space -/

/-- ★★★ **`Op(K)` is a continuous linear map `𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)`** — row 122's statement, and
the form every further Weyl-calculus statement (composition, the Moyal product, adjoints) needs. The
two halves are exactly the two hypotheses: smoothness from `contDiff_weylOpK`, decay from
`exists_bound_weylOpK`, with the single seminorm on the right. -/
noncomputable def weylCLM (K : 𝓢(ℝ × ℝ, ℂ)) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  mkCLM (fun ψ => weylOpK K ψ)
    (fun ψ φ x => by
      show ∫ y, K ((x + y) / 2, x - y) * (ψ + φ) y
          = (∫ y, K ((x + y) / 2, x - y) * ψ y) + ∫ y, K ((x + y) / 2, x - y) * φ y
      rw [← integral_add (integrable_weylOpK_integrand K ψ x)
        (integrable_weylOpK_integrand K φ x)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show K ((x + y) / 2, x - y) * (ψ + φ) y
          = K ((x + y) / 2, x - y) * ψ y + K ((x + y) / 2, x - y) * φ y
      rw [add_apply, mul_add])
    (fun a ψ x => by
      show ∫ y, K ((x + y) / 2, x - y) * (a • ψ) y
          = (RingHom.id ℂ) a • ∫ y, K ((x + y) / 2, x - y) * ψ y
      rw [RingHom.id_apply, ← integral_smul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show K ((x + y) / 2, x - y) * (a • ψ) y = a • (K ((x + y) / 2, x - y) * ψ y)
      rw [smul_apply, smul_eq_mul, smul_eq_mul]
      ring)
    (fun ψ => contDiff_infty.2 fun m => contDiff_weylOpK K ψ m)
    (fun n => by
      obtain ⟨C, hC0, hC⟩ := exists_bound_weylOpK K n.1 n.2
      exact ⟨{(0, 0)}, C, hC0, fun ψ x => by simpa using hC ψ x⟩)

/-- ★ **The row reads on `weylOp`, not only on `weylOpK`.** #121(i)'s slice family is what
discharges the gating this row recorded: the continuous linear map above *is* the Weyl operator of
the slice family, so `Op(a) : 𝓢(ℝ, ℂ) →L 𝓢(ℝ, ℂ)` holds in the vocabulary #92 stated it in. -/
theorem weylCLM_apply_eq_weylOp (K : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    weylCLM K ψ x = weylOp (SchwartzMap.slice K) ψ x :=
  weylOpK_eq_weylOp_slice K ψ x

@[simp]
theorem weylCLM_apply (K : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    weylCLM K ψ x = weylOpK K ψ x := rfl

end WignerFunction

end
