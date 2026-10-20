/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Semigroup.BoundedPerturbation

/-!
# The generator of a bounded perturbation: the mild solution is a classical one

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #129 (out of ~~#64(iii)~~); consumed by `SchrodingerGenerator.lean`.

`BoundedPerturbation.lean` builds the perturbed semigroup `𝒮 = hS.perturbed B` of a strongly
continuous contraction semigroup `S` by a bounded `B` as the Dyson series, and characterises it
by the Duhamel equation — a **mild** solution. This file proves the mild solution is **classical**
on the generator's domain, without ever naming an unbounded operator: the generator is read off the
orbit as a right derivative at time zero.

* `HasGeneratorAt T ψ v`: the orbit `t ↦ T t ψ` has right derivative `v` at `0` — `ψ` lies in the
  domain of the generator of `T` and the generator sends it to `v`
  (`hasGeneratorAt_iff_hasDerivWithinAt`).
* ★ `tendsto_inv_smul_duhamelIntegral`: the Duhamel integral `∫₀ᵗ S(t−s) B 𝒮(s) χ ds` is `t · Bχ + o(t)`
  — the one analytic input, from joint continuity of the integrand at `(0, 0)`.
* ★★ `hasGeneratorAt_perturbed_iff`: **the generator of `𝒮` is `A + B` on the domain of `A`, and the
  domains agree**: `HasGeneratorAt 𝒮 χ (v + Bχ) ↔ HasGeneratorAt S χ v`.
* For any semigroup-like family (`T 0 = 1`, the law for nonnegative times, strong continuity, a
  bound on `[0, t]`): `HasGeneratorAt.tendsto_right` (right derivative along the orbit),
  `HasGeneratorAt.apply` (**the orbit stays in the generator's domain**, with
  `gen (T t ψ) = T t (gen ψ)`), ★★ `HasGeneratorAt.hasDerivAt` (**two-sided derivative at every
  `t > 0`**: the left difference quotient is `T (t − k)` applied to the right quotient at `0`,
  controlled by the bound and strong continuity).
* ★★★ `hasDerivAt_perturbed`: for `ψ` in the domain of the generator of `S` with value `v`, and
  `t > 0`, `d/dt 𝒮(t)ψ = 𝒮(t)(v + Bψ)`; `hasDerivWithinAt_perturbed_zero` at `t = 0`;
  ★★ `hasGeneratorAt_of_perturbed`: **`𝒮(t)ψ` stays in the domain of the generator of `S`**, with
  `A(𝒮(t)ψ) = 𝒮(t)(A + B)ψ − B(𝒮(t)ψ)`, so the equation also reads
  `d/dt 𝒮(t)ψ = A(𝒮(t)ψ) + B(𝒮(t)ψ)` (★★★ `perturbed_classical`).

## Honest scope

* **The generator is a right derivative, not an operator.** `HasGeneratorAt` is the standard
  definition of the infinitesimal generator applied one vector at a time; no `LinearPMap` is
  formed and no closedness is used. Consumers that have the generator as an operator
  (`SchrodingerGenerator.lean`) connect through the derivative statement they already have.
* **Nonnegative times.** `S` and `𝒮` are extended by the identity to `t ≤ 0`, so at `t = 0` only
  the derivative within `[0, ∞)` is stated. For `t > 0` the derivative is two-sided.
* Nothing is said about the *converse* domain question for a concrete `S` — that a vector whose
  orbit has a right derivative lies in a concretely described domain — which is a statement about
  that `S`, not about the perturbation.

References: K.-J. Engel, R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
II.1 (generators, the orbit in the domain), III.1 (bounded perturbations); A. Pazy, *Semigroups of
Linear Operators*, Thm 3.1.1; `BoundedPerturbation.lean` (`dysonSum_eq_add_integral`,
`perturbed_add`, `norm_perturbed_le`); `specs/BACKLOG.md` #129, ~~#64~~.
-/

@[expose] public section

open scoped Topology Interval
open MeasureTheory intervalIntegral Filter Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### The generator as a right derivative at time zero -/

/-- `HasGeneratorAt T ψ v`: the orbit `t ↦ T t ψ` has right derivative `v` at `0`, i.e. `ψ` is in
the domain of the generator of `T` and the generator sends `ψ` to `v`. -/
def HasGeneratorAt (T : ℝ → E →L[ℂ] E) (ψ v : E) : Prop :=
  Tendsto (fun h : ℝ => h⁻¹ • (T h ψ - ψ)) (𝓝[>] 0) (𝓝 v)

theorem HasGeneratorAt.unique {T : ℝ → E →L[ℂ] E} {ψ v v' : E} (h : HasGeneratorAt T ψ v)
    (h' : HasGeneratorAt T ψ v') : v = v' :=
  tendsto_nhds_unique h h'

theorem Ici_zero_diff_zero : (Ici (0 : ℝ)) \ {0} = Ioi 0 := by
  ext x
  exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, h.ne'⟩⟩

/-- The generator statement is the derivative of the orbit within `[0, ∞)` at `0`. -/
theorem hasGeneratorAt_iff_hasDerivWithinAt {T : ℝ → E →L[ℂ] E} (h0 : T 0 = 1) (ψ v : E) :
    HasGeneratorAt T ψ v ↔ HasDerivWithinAt (fun t => T t ψ) v (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_zero_diff_zero]
  unfold HasGeneratorAt
  refine tendsto_congr fun h => ?_
  rw [slope_def_module, sub_zero, h0, one_apply_eq_self]

/-! ### Semigroup-like families: the orbit stays in the domain and is differentiable -/

section Semigroup

variable {T : ℝ → E →L[ℂ] E}

/-- The right derivative along the orbit: `d⁺/dt T t ψ = T t v`. -/
theorem HasGeneratorAt.tendsto_right (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = T s * T t)
    {ψ v : E} (hv : HasGeneratorAt T ψ v) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun h : ℝ => h⁻¹ • (T (t + h) ψ - T t ψ)) (𝓝[>] 0) (𝓝 (T t v)) := by
  have hc : Tendsto (fun h : ℝ => T t (h⁻¹ • (T h ψ - ψ))) (𝓝[>] 0) (𝓝 (T t v)) :=
    ((T t).continuous.tendsto v).comp hv
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [hadd t h ht (le_of_lt hh), ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.map_smul_of_tower, map_sub]

/-- ★ **The orbit stays in the generator's domain**, and the generator commutes with the
semigroup along it: `gen (T t ψ) = T t (gen ψ)`. -/
theorem HasGeneratorAt.apply (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = T s * T t)
    {ψ v : E} (hv : HasGeneratorAt T ψ v) {t : ℝ} (ht : 0 ≤ t) :
    HasGeneratorAt T (T t ψ) (T t v) := by
  have h := hv.tendsto_right hadd ht
  unfold HasGeneratorAt
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [add_comm, hadd h t (le_of_lt hh) ht, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_apply]

/-- ★★ **The orbit is differentiable at every positive time**, with derivative `T t (gen ψ)`. The
right derivative is `tendsto_right`; the left difference quotient at `t` is `T (t − k)` applied to
the right quotient at `0`, which the bound on `[0, t]` and strong continuity control. -/
theorem HasGeneratorAt.hasDerivAt (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = T s * T t)
    (hcont : ∀ ψ, Continuous fun t => T t ψ) {t : ℝ} (ht : 0 < t) {M : ℝ}
    (hM : ∀ s, 0 ≤ s → s ≤ t → ‖T s‖ ≤ M) {ψ v : E} (hv : HasGeneratorAt T ψ v) :
    HasDerivAt (fun s => T s ψ) (T t v) t := by
  rw [hasDerivAt_iff_tendsto_slope_zero, ← nhdsLT_sup_nhdsGT, tendsto_sup]
  refine ⟨?_, hv.tendsto_right hadd ht.le⟩
  -- the reflection carries the left filter to the right one
  have hneg : Tendsto (fun h : ℝ => -h) (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (continuous_neg.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Iio 0))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact neg_pos.2 hh
  -- the left quotient, reflected: `T (t − k)` applied to the right quotient at `0`
  have hq : Tendsto (fun k : ℝ => T (t - k) (k⁻¹ • (T k ψ - ψ))) (𝓝[>] 0) (𝓝 (T t v)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hA : Tendsto (fun k : ℝ => M * ‖k⁻¹ • (T k ψ - ψ) - v‖) (𝓝[>] 0) (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hv).const_mul M
      simpa using this
    have hB : Tendsto (fun k : ℝ => ‖T (t - k) v - T t v‖) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun k : ℝ => T (t - k) v) (𝓝[>] 0) (𝓝 (T t v)) := by
        have h2 : Tendsto (fun k : ℝ => t - k) (𝓝[>] (0 : ℝ)) (𝓝 t) := by
          have h3 : Tendsto (fun k : ℝ => k) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
            tendsto_id.mono_left nhdsWithin_le_nhds
          simpa using (tendsto_const_nhds (x := t)).sub h3
        exact ((hcont v).tendsto t).comp h2
      exact tendsto_iff_norm_sub_tendsto_zero.1 h1
    have hsum := hA.add hB
    rw [add_zero] at hsum
    refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ hsum
    filter_upwards [self_mem_nhdsWithin, (eventually_le_nhds ht).filter_mono nhdsWithin_le_nhds]
      with k hk hkt
    have hk' : 0 < k := hk
    have hdecomp : T (t - k) (k⁻¹ • (T k ψ - ψ)) - T t v
        = T (t - k) (k⁻¹ • (T k ψ - ψ) - v) + (T (t - k) v - T t v) := by
      rw [map_sub]
      abel
    rw [hdecomp]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ le_rfl)
    exact le_trans ((T (t - k)).le_opNorm _)
      (mul_le_mul_of_nonneg_right (hM (t - k) (by linarith) (by linarith)) (norm_nonneg _))
  refine (hq.comp hneg).congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds (neg_lt_zero.2 ht)).filter_mono nhdsWithin_le_nhds] with h hh hth
  have hk : 0 < -h := neg_pos.2 hh
  have hsplit : T (t + h) (T (-h) ψ) = T t ψ := by
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def,
      ← hadd (t + h) (-h) (by linarith) hk.le, show t + h + -h = t by ring]
  show T (t - -h) ((-h)⁻¹ • (T (-h) ψ - ψ)) = h⁻¹ • (T (t + h) ψ - T t ψ)
  rw [sub_neg_eq_add, ContinuousLinearMap.map_smul_of_tower, map_sub, hsplit, ← neg_inv, neg_smul,
    ← smul_neg, neg_sub]

end Semigroup

/-! ### The Duhamel integral is `t · Bχ + o(t)` -/

namespace ContractionSemigroup

variable [CompleteSpace E] {S : ℝ → E →L[ℂ] E} (B : E →L[ℂ] E)

/-- ★ **The Duhamel integral has right derivative `Bχ` at `0`**: `t⁻¹ ∫₀ᵗ S(t−s) B 𝒮(s) χ ds → Bχ`,
by joint continuity of the integrand at `(0, 0)`. -/
theorem tendsto_inv_smul_duhamelIntegral (hS : IsContractionSemigroup S) (χ : E) :
    Tendsto (fun t : ℝ => t⁻¹ • ∫ s in (0 : ℝ)..t, S (t - s) (B (dysonSum S B s χ)))
      (𝓝[>] 0) (𝓝 (B χ)) := by
  have hg : Continuous fun p : ℝ × ℝ => S p.1 (B (dysonSum S B p.2 χ)) :=
    hS.continuous_uncurry.comp
      (continuous_fst.prodMk (B.continuous.comp ((continuous_dysonSum B hS χ).comp continuous_snd)))
  have hg0 : S (0 : ℝ) (B (dysonSum S B 0 χ)) = B χ := by
    rw [dysonSum_zero B hS, hS.map_zero, one_apply_eq_self]
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.1 (hg.continuousAt (x := ((0 : ℝ), (0 : ℝ))))
    (ε / 2) (half_pos hε)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < δ :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hev] with t ht htδ
  have ht0 : 0 < t := ht
  have hbound : ∀ s ∈ Ι (0 : ℝ) t, ‖S (t - s) (B (dysonSum S B s χ)) - B χ‖ ≤ ε / 2 := by
    intro s hs
    rw [uIoc_of_le ht0.le] at hs
    have hd : dist ((t - s, s) : ℝ × ℝ) ((0 : ℝ), (0 : ℝ)) < δ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero,
        abs_of_nonneg (by linarith [hs.2]), abs_of_nonneg hs.1.le]
      exact max_lt (by linarith [hs.1]) (lt_of_le_of_lt hs.2 htδ)
    have h := hδε hd
    dsimp only at h
    rw [hg0, dist_eq_norm] at h
    exact h.le
  have hint : IntervalIntegrable (fun s => S (t - s) (B (dysonSum S B s χ))) volume 0 t :=
    (continuous_dysonSum_integrand B hS t χ).intervalIntegrable _ _
  have hsub : ∫ s in (0 : ℝ)..t, (S (t - s) (B (dysonSum S B s χ)) - B χ)
      = (∫ s in (0 : ℝ)..t, S (t - s) (B (dysonSum S B s χ))) - t • B χ := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const,
      sub_zero]
  have hle : ‖(∫ s in (0 : ℝ)..t, S (t - s) (B (dysonSum S B s χ))) - t • B χ‖ ≤ ε / 2 * |t - 0| := by
    rw [← hsub]
    exact intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [dist_eq_norm]
  have hre : t⁻¹ • (∫ s in (0 : ℝ)..t, S (t - s) (B (dysonSum S B s χ))) - B χ
      = t⁻¹ • ((∫ s in (0 : ℝ)..t, S (t - s) (B (dysonSum S B s χ))) - t • B χ) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]
  rw [hre, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ht0]
  calc t⁻¹ * ‖(∫ s in (0 : ℝ)..t, S (t - s) (B (dysonSum S B s χ))) - t • B χ‖
      ≤ t⁻¹ * (ε / 2 * |t - 0|) := mul_le_mul_of_nonneg_left hle (inv_nonneg.2 ht0.le)
    _ = ε / 2 := by
        rw [sub_zero, abs_of_pos ht0]
        field_simp
    _ < ε := half_lt_self hε

/-! ### The generator of the perturbed semigroup -/

/-- ★★ **The generator of `𝒮` is `A + B` on the domain of `A`, and the domains agree.** -/
theorem hasGeneratorAt_perturbed_iff (hS : IsContractionSemigroup S) (χ v : E) :
    HasGeneratorAt (hS.perturbed B) χ (v + B χ) ↔ HasGeneratorAt S χ v := by
  have hI := tendsto_inv_smul_duhamelIntegral B hS χ
  have heq : ∀ᶠ h in 𝓝[>] (0 : ℝ), h⁻¹ • (hS.perturbed B h χ - χ)
      = h⁻¹ • (S h χ - χ) + h⁻¹ • ∫ s in (0 : ℝ)..h, S (h - s) (B (dysonSum S B s χ)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [perturbed_apply, dysonSum_eq_add_integral B hS (le_of_lt hh), ← smul_add,
      add_sub_right_comm]
  unfold HasGeneratorAt
  constructor
  · intro H
    have h2 := H.sub hI
    rw [add_sub_cancel_right] at h2
    refine h2.congr' ?_
    filter_upwards [heq] with h hh
    rw [hh, add_sub_cancel_right]
  · intro H
    refine (H.add hI).congr' ?_
    filter_upwards [heq] with h hh
    exact hh.symm

/-- The perturbed family satisfies the semigroup law in the order `hadd` wants. -/
theorem perturbed_add' (hS : IsContractionSemigroup S) :
    ∀ s t, 0 ≤ s → 0 ≤ t → hS.perturbed B (s + t) = hS.perturbed B s * hS.perturbed B t :=
  fun _ _ hs ht => perturbed_add B hS ht hs

/-- The perturbed family is bounded by `e^{‖B‖ t}` on `[0, t]`. -/
theorem norm_perturbed_le_of_le (hS : IsContractionSemigroup S) {t : ℝ} :
    ∀ s, 0 ≤ s → s ≤ t → ‖hS.perturbed B s‖ ≤ Real.exp (‖B‖ * t) := fun s hs hst =>
  le_trans (norm_perturbed_le B hS s)
    (Real.exp_le_exp.2 (by rw [max_eq_left hs]; exact mul_le_mul_of_nonneg_left hst (norm_nonneg _)))

/-- ★★★ **The mild solution is classical**: for `ψ` in the domain of the generator of `S` with value
`v`, the perturbed orbit is differentiable at every `t > 0` with `d/dt 𝒮(t)ψ = 𝒮(t)(v + Bψ)`. -/
theorem hasDerivAt_perturbed (hS : IsContractionSemigroup S) {ψ v : E} (hv : HasGeneratorAt S ψ v)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => hS.perturbed B s ψ) (hS.perturbed B t (v + B ψ)) t :=
  HasGeneratorAt.hasDerivAt (perturbed_add' B hS) (continuous_perturbed_apply B hS) ht
    (norm_perturbed_le_of_le B hS) ((hasGeneratorAt_perturbed_iff B hS ψ v).2 hv)

/-- The same at `t = 0`, within `[0, ∞)`: the derivative is `v + Bψ`. -/
theorem hasDerivWithinAt_perturbed_zero (hS : IsContractionSemigroup S) {ψ v : E}
    (hv : HasGeneratorAt S ψ v) :
    HasDerivWithinAt (fun s => hS.perturbed B s ψ) (v + B ψ) (Ici 0) 0 :=
  (hasGeneratorAt_iff_hasDerivWithinAt (perturbed_zero B hS) ψ (v + B ψ)).1
    ((hasGeneratorAt_perturbed_iff B hS ψ v).2 hv)

/-- The perturbed orbit stays in the generator's domain of `𝒮`, with
`gen (𝒮(t)ψ) = 𝒮(t)(v + Bψ)`. -/
theorem hasGeneratorAt_perturbed_apply (hS : IsContractionSemigroup S) {ψ v : E}
    (hv : HasGeneratorAt S ψ v) {t : ℝ} (ht : 0 ≤ t) :
    HasGeneratorAt (hS.perturbed B) (hS.perturbed B t ψ) (hS.perturbed B t (v + B ψ)) :=
  ((hasGeneratorAt_perturbed_iff B hS ψ v).2 hv).apply (perturbed_add' B hS) ht

/-- ★★ **The perturbed orbit stays in the domain of the generator of `S`**, with
`A(𝒮(t)ψ) = 𝒮(t)(A + B)ψ − B(𝒮(t)ψ)`. -/
theorem hasGeneratorAt_of_perturbed (hS : IsContractionSemigroup S) {ψ v : E}
    (hv : HasGeneratorAt S ψ v) {t : ℝ} (ht : 0 ≤ t) :
    HasGeneratorAt S (hS.perturbed B t ψ)
      (hS.perturbed B t (v + B ψ) - B (hS.perturbed B t ψ)) := by
  refine (hasGeneratorAt_perturbed_iff B hS _ _).1 ?_
  rw [sub_add_cancel]
  exact hasGeneratorAt_perturbed_apply B hS hv ht

/-- ★★★ **The classical equation in the generator's own terms**: at every `t > 0` the orbit is
differentiable, its point lies in the domain of the generator of `S` with a named value `w`, and
the derivative is `w + B(𝒮(t)ψ)` — i.e. `d/dt 𝒮(t)ψ = (A + B)(𝒮(t)ψ)`. -/
theorem perturbed_classical (hS : IsContractionSemigroup S) {ψ v : E} (hv : HasGeneratorAt S ψ v)
    {t : ℝ} (ht : 0 < t) :
    ∃ w : E, HasGeneratorAt S (hS.perturbed B t ψ) w
      ∧ HasDerivAt (fun s => hS.perturbed B s ψ) (w + B (hS.perturbed B t ψ)) t := by
  refine ⟨_, hasGeneratorAt_of_perturbed B hS hv ht.le, ?_⟩
  rw [sub_add_cancel]
  exact hasDerivAt_perturbed B hS hv ht

end ContractionSemigroup

end
