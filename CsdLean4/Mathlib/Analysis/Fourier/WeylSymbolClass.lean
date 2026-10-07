/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Fourier.WignerWeyl
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Weyl operator's symbol class

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #92(a), brick (a1).

#92's measurement of its own part (a) was that `Op(a)` as a continuous operator on `𝒢(ℝ, ℂ)` is *not*
a gap in the proofs but **a statement needing a different symbol class**: with `weylOp`'s datum — a
family `b : ℝ → 𝒢(ℝ, ℂ)` with no regularity in its first slot — `weylOp b ψ` need not even be
continuous. `WignerWeyl.lean` works around this by *assuming* what it needs: `integrable_weylPair`
takes joint continuity (`hbc`) and a uniform bound integrable in the first slot (`hM`, `hbM`) as
hypotheses.

This file fixes the class and discharges those hypotheses as theorems.

* ★ `exists_bound_fst`, ★ `exists_bound_snd` — a Schwartz function on the plane decays like
  `(1 + t²)⁻¹` **in each slot separately**, uniformly in the other. Two orders of `SchwartzMap.decay`
  (`k = 2` and `k = 0`) and `‖p‖² ≥ pᵢ²`;
* `weylOpK` — the Weyl operator of a **jointly Schwartz kernel**, and ★ `weylOpK_eq_weylOp`: it
  agrees with `weylOp` of any slice family, so everything already proved about `weylOp` transfers
  whenever a slice family is available;
* ★ `continuous_weylKernel` and ★★ `exists_integrable_bound` — `WignerWeyl.lean`'s three assumed
  hypotheses, now theorems on this class;
* ★ `integrable_weylOpK_integrand` and ★★ `continuous_weylOpK` — **the defect #92 recorded, fixed**:
  on the Schwartz kernel class the Weyl operator's output *is* continuous, by dominated continuity
  against `4C·(1 + (y − x₀)²)⁻¹`, the majorant the second-slot decay supplies uniformly on a unit
  ball of parameters.

## Honest scope

⚠️ **This is the symbol class, not the calculus.** `Op(a) : 𝒢(ℝ, ℂ) →L 𝒢(ℝ, ℂ)` is *not* proved —
continuity of the output function is the first of the Schwartz seminorm estimates, not the last. The
remaining obstruction is the one #92 measured and it is unchanged: smoothness of the output to all
orders needs differentiation under the integral sign **to all orders with bounds**, which the pin has
in no form for integrals over `ℝ` (the corpus's `ContDiffParametricIntervalIntegral.lean`, from #60,
is *interval* integrals on a compact interval, where the bounds come free from continuity).

⚠️ **No slicing.** `weylOpK_eq_weylOp` takes a slice family as a *hypothesis*. That a Schwartz
function on the plane slices into a Schwartz-valued family is precisely the two-variable Schwartz API
#92 names as absent, and nothing here supplies it — which is why the properties above are proved for
`weylOpK` directly rather than inherited through `weylOp`.

References: [`WignerWeyl.lean`](WignerWeyl.lean) (`weylOp`, `integrable_weylPair`,
`integral_conj_mul_weylOp`), [`WignerCalculus.lean`](WignerCalculus.lean) (#92(b)(c)),
`Mathlib/Analysis/Calculus/ContDiffParametricIntervalIntegral.lean` (#60, the interval case);
`specs/BACKLOG.md` #92, #63, #60.
-/

@[expose] public section

open MeasureTheory SchwartzMap

namespace WignerFunction

/-! ### A Schwartz function on the plane decays in each slot separately -/

theorem exists_bound_fst (K : 𝓢(ℝ × ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × ℝ, ‖K p‖ ≤ C * (1 + p.1 ^ 2)⁻¹ := by
  obtain ⟨C₂, hC₂⟩ := K.decay 2 0
  obtain ⟨C₀, hC₀⟩ := K.decay 0 0
  refine ⟨C₀ + C₂, by linarith [hC₀.1, hC₂.1], fun p => ?_⟩
  have h2 := hC₂.2 p
  have h0 := hC₀.2 p
  rw [norm_iteratedFDeriv_zero] at h2 h0
  rw [pow_zero, one_mul] at h0
  have hfst : p.1 ^ 2 ≤ ‖p‖ ^ 2 := by
    have h1 : |p.1| ≤ ‖p‖ := by simpa using norm_fst_le p
    nlinarith [abs_nonneg p.1, norm_nonneg p, sq_abs p.1]
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + p.1 ^ 2)]
  nlinarith [norm_nonneg (K p), h2, h0, hfst]

theorem exists_bound_snd (K : 𝓢(ℝ × ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × ℝ, ‖K p‖ ≤ C * (1 + p.2 ^ 2)⁻¹ := by
  obtain ⟨C₂, hC₂⟩ := K.decay 2 0
  obtain ⟨C₀, hC₀⟩ := K.decay 0 0
  refine ⟨C₀ + C₂, by linarith [hC₀.1, hC₂.1], fun p => ?_⟩
  have h2 := hC₂.2 p
  have h0 := hC₀.2 p
  rw [norm_iteratedFDeriv_zero] at h2 h0
  rw [pow_zero, one_mul] at h0
  have hsnd : p.2 ^ 2 ≤ ‖p‖ ^ 2 := by
    have h1 : |p.2| ≤ ‖p‖ := by simpa using norm_snd_le p
    nlinarith [abs_nonneg p.2, norm_nonneg p, sq_abs p.2]
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + p.2 ^ 2)]
  nlinarith [norm_nonneg (K p), h2, h0, hsnd]

/-! ### The Weyl operator of a jointly Schwartz kernel -/

/-- **The Weyl operator of a jointly Schwartz kernel.** Same integral as `weylOp`, with the kernel
given as one Schwartz function on the plane instead of a family with no regularity in its first
slot. -/
noncomputable def weylOpK (K : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  ∫ y, K ((x + y) / 2, x - y) * ψ y

/-- ★ **The bridge.** Whenever a slice family is available, this is `weylOp` of it — so every
statement already proved about `weylOp` transfers. The hypothesis is what the absent two-variable
Schwartz API would supply. -/
theorem weylOpK_eq_weylOp (K : 𝓢(ℝ × ℝ, ℂ)) (b : ℝ → 𝓢(ℝ, ℂ))
    (hb : ∀ u w, b u w = K (u, w)) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    weylOpK K ψ x = weylOp b ψ x := by
  rw [weylOpK, weylOp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [hb]

/-- ★ `WignerWeyl.lean`'s joint-continuity hypothesis, now a theorem. -/
theorem continuous_weylKernel (K : 𝓢(ℝ × ℝ, ℂ)) :
    Continuous fun p : ℝ × ℝ => K (p.1, p.2) := by
  simpa using K.continuous

/-- ★★ `WignerWeyl.lean`'s two bound hypotheses, now a theorem: on the Schwartz kernel class there
*is* a bound integrable in the first slot and uniform in the second. -/
theorem exists_integrable_bound (K : 𝓢(ℝ × ℝ, ℂ)) :
    ∃ M : ℝ → ℝ, Integrable M ∧ ∀ u w : ℝ, ‖K (u, w)‖ ≤ M u := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_fst K
  refine ⟨fun u => C * (1 + u ^ 2)⁻¹, ?_, fun u w => ?_⟩
  · exact integrable_inv_one_add_sq.const_mul C
  · exact hC (u, w)

/-- The majorant the second-slot decay supplies, uniformly for parameters in a unit ball. -/
theorem norm_weylKernel_le {K : 𝓢(ℝ × ℝ, ℂ)} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ p : ℝ × ℝ, ‖K p‖ ≤ C * (1 + p.2 ^ 2)⁻¹) {x₀ x : ℝ} (hx : |x - x₀| ≤ 1) (y : ℝ) :
    ‖K ((x + y) / 2, x - y)‖ ≤ 4 * C * (1 + (y - x₀) ^ 2)⁻¹ := by
  have hd : (x - x₀) ^ 2 ≤ 1 := by
    have h := abs_le.1 hx
    nlinarith [h.1, h.2]
  -- with `d = x - x₀` and `a = x - y`, `y - x₀ = d - a` and `(d - a)² ≤ 2d² + 2a²`
  have hkey : (1 + (y - x₀) ^ 2) / 4 ≤ 1 + (x - y) ^ 2 := by
    nlinarith [hd, sq_nonneg ((x - x₀) + (x - y)), sq_nonneg (x - y)]
  calc ‖K ((x + y) / 2, x - y)‖ ≤ C * (1 + (x - y) ^ 2)⁻¹ := hC _
    _ ≤ C * ((1 + (y - x₀) ^ 2) / 4)⁻¹ := by gcongr
    _ = 4 * C * (1 + (y - x₀) ^ 2)⁻¹ := by
        rw [inv_div]
        ring

/-- ★ The defining integral converges, with no hypotheses. -/
theorem integrable_weylOpK_integrand (K : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Integrable fun y => K ((x + y) / 2, x - y) * ψ y := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_snd K
  obtain ⟨D, hD⟩ := exists_norm_le ψ
  have hD0 : 0 ≤ D := le_trans (norm_nonneg _) (hD 0)
  have hmaj : Integrable fun y : ℝ => 4 * C * (1 + (y - x) ^ 2)⁻¹ * D :=
    ((integrable_inv_one_add_sq.comp_sub_right x).const_mul (4 * C)).mul_const D
  refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · have h1 : Continuous fun y : ℝ => K ((x + y) / 2, x - y) := by
      refine K.continuous.comp ?_
      exact ((continuous_const.add continuous_id).div_const 2).prodMk
        (continuous_const.sub continuous_id)
    exact (h1.mul ψ.continuous).aestronglyMeasurable
  · rw [norm_mul]
    refine mul_le_mul (norm_weylKernel_le hC0 hC (by simp) y) (hD y) (norm_nonneg _) (by positivity)

/-- ★★ **The defect #92 recorded, fixed: on the Schwartz kernel class the Weyl operator's output is
continuous.** Dominated continuity against the second-slot majorant, which is uniform for parameters
within `1` of the point. -/
theorem continuous_weylOpK (K : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) : Continuous (weylOpK K ψ) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_snd K
  obtain ⟨D, hD⟩ := exists_norm_le ψ
  have hD0 : 0 ≤ D := le_trans (norm_nonneg _) (hD 0)
  rw [continuous_iff_continuousAt]
  intro x₀
  have hmaj : Integrable fun y : ℝ => 4 * C * (1 + (y - x₀) ^ 2)⁻¹ * D :=
    ((integrable_inv_one_add_sq.comp_sub_right x₀).const_mul (4 * C)).mul_const D
  refine continuousAt_of_dominated (bound := fun y => 4 * C * (1 + (y - x₀) ^ 2)⁻¹ * D)
    ?_ ?_ hmaj ?_
  · filter_upwards with x
    have h1 : Continuous fun y : ℝ => K ((x + y) / 2, x - y) := by
      refine K.continuous.comp ?_
      exact ((continuous_const.add continuous_id).div_const 2).prodMk
        (continuous_const.sub continuous_id)
    exact (h1.mul ψ.continuous).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0:ℝ) < 1)] with x hx
    filter_upwards with y
    have hx' : |x - x₀| ≤ 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hx
      exact hx.le
    rw [norm_mul]
    refine mul_le_mul (norm_weylKernel_le hC0 hC hx' y) (hD y) (norm_nonneg _) (by positivity)
  · filter_upwards with y
    have h1 : Continuous fun x : ℝ => K ((x + y) / 2, x - y) := by
      refine K.continuous.comp ?_
      exact ((continuous_id.add continuous_const).div_const 2).prodMk
        (continuous_id.sub continuous_const)
    exact ((h1.mul continuous_const).continuousAt)

end WignerFunction

end
