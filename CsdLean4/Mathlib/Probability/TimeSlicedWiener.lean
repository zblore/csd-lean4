/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Semigroup.HeatSemigroup

/-!
# The time-sliced Wiener functional is the iterated heat–potential product

**Category:** 1-Mathlib (CSD-free; staged for upstream).

Feynman's finite-slice formula in the Euclidean continuum. For a pre-Brownian motion `B`, a slice
length `h > 0`, a bounded weight `g` (think `g = e^{−h V}`) and a bounded `f ∈ L²`, the
**time-sliced Wiener functional**

  `W_n(x) = E[ g (x + B_h) · g (x + B_{2h}) ⋯ g (x + B_{nh}) · f (x + B_{nh}) ]`

equals, almost everywhere in `x`, the `n`-fold operator product `((P_h ∘ M_g)ⁿ f)(x)`, `P_h` the heat
semigroup and `M_g` multiplication by `g`. The sum over paths of the finite-dimensional
`Matrix.pow_succ_apply_eq_sum_pathWeight` becomes an integral over the `n` intermediate positions
of the Brownian path, the one-step amplitude the Gaussian kernel times the weight.

* `slicedWiener B P h g f n x` — the functional; `slicedWiener_zero` (`W₀ = f`);
* `integral_prod_of_indepFun` — **the freezing lemma**: for independent `X`, `Y` and bounded
  measurable `Ψ`, `E[Ψ (X, Y)] = E_ω[ E_ω'[Ψ (X ω, Y ω')] ]`;
* ★ `slicedWiener_succ` — **the Markov step**: `W_{n+1}^B(x) = ∫ g (x + y) · W_n^{B'}(x + y) dγ_h(y)`
  with `B'` the process shifted by `h` (`IsPreBrownianReal.shift`, `indepFun_shift`);
* ★★ `pow_stepOp_apply_ae_eq_slicedWiener` — **the time-sliced formula**:
  `(P_h ∘ M_g)ⁿ f =ᵐ W_n`, by induction on `n` through the Markov step and the pointwise formula of
  the heat semigroup.

## Honest scope

⚠️ **Bounded data.** `g` and `f` are bounded strongly measurable (and `f ∈ L²`), so every
expectation is of a bounded random variable; the extension to `f ∈ L²` alone is by continuity in
Feynman–Kac (FC-4). On `ℝᵈ`, for a pre-Brownian motion in `ℝᵈ` (`IsPreBrownianVec`,
`Probability/BrownianVec.lean`; one dimension before BACKLOG #41).

References: M. Kac, Trans. AMS 65, 1 (1949); B. Simon, *Functional Integration and Quantum Physics*,
§1; `Analysis/Semigroup/HeatSemigroup.lean` (FC-2); `LinearAlgebra/Matrix/PathSum.lean` (the
finite-dimensional sum over paths); `specs/feynman-continuum-scoping.md` (FC-3); `specs/BACKLOG.md`
#36(c).
-/

@[expose] public section

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter HeatSemigroup

namespace TimeSlicedWiener

variable {ι : Type*} [Fintype ι]

/-- Euclidean space `ℝᵈ`. -/
local notation "E" => EuclideanSpace ℝ ι

/-- `L²(ℝᵈ, ℂ)` with Lebesgue measure. -/
local notation "L2" => Lp ℂ 2 (volume : Measure E)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ### The freezing lemma -/

omit [Fintype ι] in
/-- **Freezing an independent variable**: for independent `X : Ω → 𝒳` and `Y : Ω → 𝒴` and a bounded
measurable `Ψ`, `E[Ψ (X, Y)] = E_ω[E_ω'[Ψ (X ω, Y ω')]]`. -/
theorem integral_prod_of_indepFun [IsProbabilityMeasure P] {𝒳 𝒴 : Type*} [MeasurableSpace 𝒳]
    [MeasurableSpace 𝒴] {X : Ω → 𝒳} {Y : Ω → 𝒴} (hXY : IndepFun X Y P) (hX : AEMeasurable X P)
    (hY : AEMeasurable Y P) {Ψ : 𝒳 × 𝒴 → ℂ} (hΨ : Measurable Ψ) {C : ℝ} (hC : ∀ p, ‖Ψ p‖ ≤ C) :
    ∫ ω, Ψ (X ω, Y ω) ∂P = ∫ ω, (∫ ω', Ψ (X ω, Y ω') ∂P) ∂P := by
  have hmap := hXY.map_prod_eq_prod_map_map hX hY
  have hΨs : StronglyMeasurable Ψ := hΨ.stronglyMeasurable
  rw [← integral_map (hX.prodMk hY) hΨs.aestronglyMeasurable, hmap,
    integral_prod _ (Integrable.of_bound hΨs.aestronglyMeasurable C (Eventually.of_forall hC)),
    integral_map hX]
  · refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only
    rw [integral_map hY]
    exact (hΨs.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact (hΨs.integral_prod_right').aestronglyMeasurable

/-! ### The time-sliced Wiener functional -/

variable (P) in
/-- **The time-sliced Wiener functional**: `n` slices of length `h`, the weight `g` sampled at the
slice ends and `f` at the final time. -/
noncomputable def slicedWiener (B : ℝ≥0 → Ω → E) (h : ℝ≥0) (g f : E → ℂ) (n : ℕ) (x : E) : ℂ :=
  ∫ ω, (∏ k ∈ Finset.range n, g (x + B (((k + 1 : ℕ) : ℝ≥0) * h) ω)) * f (x + B ((n : ℝ≥0) * h) ω) ∂P

theorem slicedWiener_zero [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → E} (hB : IsPreBrownianVec B P)
    (h : ℝ≥0) (g f : E → ℂ) (x : E) : slicedWiener P B h g f 0 x = f x := by
  rw [slicedWiener]
  simp only [Finset.range_zero, Finset.prod_empty, one_mul, Nat.cast_zero, zero_mul]
  rw [integral_congr_ae (g := fun _ => f x) ?_, integral_const]
  · simp
  · filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
    rw [hω, add_zero]

/-- The path functional of `n` slices, as a measurable function of the starting point and the
path. -/
theorem measurable_pathFunctional {g f : E → ℂ} (hg : Measurable g) (hf : Measurable f) (h : ℝ≥0)
    (n : ℕ) :
    Measurable fun p : E × (ℝ≥0 → E) =>
      (∏ k ∈ Finset.range n, g (p.1 + p.2 (((k + 1 : ℕ) : ℝ≥0) * h))) * f (p.1 + p.2 ((n : ℝ≥0) * h)) := by
  refine Measurable.mul (Finset.measurable_prod _ fun k _ => ?_) ?_
  · exact hg.comp (measurable_fst.add ((measurable_pi_apply _).comp measurable_snd))
  · exact hf.comp (measurable_fst.add ((measurable_pi_apply _).comp measurable_snd))

omit [Fintype ι] in
theorem norm_pathFunctional_le {g f : E → ℂ} {Cg Cf : ℝ} (hCg : ∀ x, ‖g x‖ ≤ Cg)
    (hCf : ∀ x, ‖f x‖ ≤ Cf) (h : ℝ≥0) (n : ℕ) (p : E × (ℝ≥0 → E)) :
    ‖(∏ k ∈ Finset.range n, g (p.1 + p.2 (((k + 1 : ℕ) : ℝ≥0) * h))) * f (p.1 + p.2 ((n : ℝ≥0) * h))‖
      ≤ Cg ^ n * Cf := by
  have hCg0 : 0 ≤ Cg := le_trans (norm_nonneg _) (hCg 0)
  rw [norm_mul, norm_prod]
  refine mul_le_mul ?_ (hCf _) (norm_nonneg _) (by positivity)
  calc ∏ k ∈ Finset.range n, ‖g (p.1 + p.2 (((k + 1 : ℕ) : ℝ≥0) * h))‖
      ≤ ∏ _k ∈ Finset.range n, Cg := Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun _ _ => hCg _
    _ = Cg ^ n := by rw [Finset.prod_const, Finset.card_range]

/-- `x ↦ W_n(x)` is measurable. -/
theorem measurable_slicedWiener [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → E}
    (hB : ∀ t, Measurable (B t)) (h : ℝ≥0) {g f : E → ℂ} (hg : Measurable g) (hf : Measurable f)
    (n : ℕ) : Measurable (slicedWiener P B h g f n) := by
  have hΨ := (measurable_pathFunctional hg hf h n).stronglyMeasurable
  have hB' : Measurable fun ω : Ω => fun t => B t ω := measurable_pi_iff.mpr hB
  have := (hΨ.comp_measurable (measurable_fst.prodMk (hB'.comp measurable_snd))).integral_prod_right'
    (ν := P)
  exact this.measurable

/-- ★ **The Markov step.** With `B'` the process shifted by `h`,
`W_{n+1}^B(x) = ∫ g (x + y) · W_n^{B'}(x + y) dγ_h(y)`. -/
theorem slicedWiener_succ [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → E} (hB : IsPreBrownianVec B P)
    (hBm : ∀ t, Measurable (B t)) (h : ℝ≥0) {g f : E → ℂ} (hg : Measurable g)
    (hf : Measurable f) {Cg Cf : ℝ} (hCg : ∀ x, ‖g x‖ ≤ Cg) (hCf : ∀ x, ‖f x‖ ≤ Cf) (n : ℕ) (x : E) :
    slicedWiener P B h g f (n + 1) x
      = ∫ y, g (x + y) * slicedWiener P (fun t ω => B (h + t) ω - B h ω) h g f n (x + y)
          ∂gaussian (h : ℝ) := by
  -- the freezing lemma with `X = B_h`, `Y` = the shifted path
  set B' : ℝ≥0 → Ω → E := fun t ω => B (h + t) ω - B h ω with hB'
  have hind : IndepFun (B h) (fun ω t => B' t ω) P := hB.indepFun_shift hBm h
  set Ψ : E × (ℝ≥0 → E) → ℂ := fun p =>
    g (x + p.1) * ((∏ k ∈ Finset.range n, g (x + p.1 + p.2 (((k + 1 : ℕ) : ℝ≥0) * h)))
      * f (x + p.1 + p.2 ((n : ℝ≥0) * h))) with hΨ
  have hΨm : Measurable Ψ := by
    refine (hg.comp (measurable_const.add measurable_fst)).mul
      (Measurable.mul (Finset.measurable_prod _ fun k _ => ?_) ?_)
    · exact hg.comp ((measurable_const.add measurable_fst).add
        ((measurable_pi_apply _).comp measurable_snd))
    · exact hf.comp ((measurable_const.add measurable_fst).add
        ((measurable_pi_apply _).comp measurable_snd))
  have hCg0 : 0 ≤ Cg := le_trans (norm_nonneg _) (hCg 0)
  have hΨb : ∀ p, ‖Ψ p‖ ≤ Cg * (Cg ^ n * Cf) := fun p => by
    rw [hΨ]
    simp only
    rw [norm_mul]
    exact mul_le_mul (hCg _) (norm_pathFunctional_le hCg hCf h n (x + p.1, p.2)) (norm_nonneg _) hCg0
  have hB'm : ∀ t, Measurable (B' t) := fun t => (hBm _).sub (hBm _)
  -- the left side is `E[Ψ (B_h, B')]`
  have hL : slicedWiener P B h g f (n + 1) x = ∫ ω, Ψ (B h ω, fun t => B' t ω) ∂P := by
    rw [slicedWiener]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    have e1 : ∀ k : ℕ, x + B h ω + B' (((k + 1 : ℕ) : ℝ≥0) * h) ω
        = x + B (((k + 1 + 1 : ℕ) : ℝ≥0) * h) ω := by
      intro k
      rw [hB']
      simp only
      rw [show (h + ((k + 1 : ℕ) : ℝ≥0) * h : ℝ≥0) = ((k + 1 + 1 : ℕ) : ℝ≥0) * h by push_cast; ring]
      abel
    have e2 : x + B h ω + B' ((n : ℝ≥0) * h) ω = x + B (((n + 1 : ℕ) : ℝ≥0) * h) ω := by
      rw [hB']
      simp only
      rw [show (h + (n : ℝ≥0) * h : ℝ≥0) = ((n + 1 : ℕ) : ℝ≥0) * h by push_cast; ring]
      abel
    rw [hΨ]
    simp only [e1, e2]
    rw [Finset.prod_range_succ', show (((0 + 1 : ℕ) : ℝ≥0) * h : ℝ≥0) = h by simp]
    ring
  rw [hL, integral_prod_of_indepFun hind (hBm h).aemeasurable
    (measurable_pi_iff.mpr hB'm).aemeasurable hΨm hΨb]
  -- `E[Φ(B_h)] = ∫ Φ dγ_h`
  have hlaw := hB.hasLaw_eval hBm h
  set Φ : E → ℂ := fun z => g (x + z) * slicedWiener P B' h g f n (x + z) with hΦdef
  have hΦm : Measurable Φ :=
    (hg.comp (measurable_const.add measurable_id)).mul
      ((measurable_slicedWiener hB'm h hg hf n).comp (measurable_const.add measurable_id))
  have hΦeq : ∀ z, (∫ ω', Ψ (z, fun t => B' t ω') ∂P) = Φ z := by
    intro z
    rw [hΦdef]
    simp only [hΨ, slicedWiener]
    rw [← integral_const_mul]
  calc ∫ ω, (∫ ω', Ψ (B h ω, fun t => B' t ω') ∂P) ∂P
      = ∫ ω, (Φ ∘ B h) ω ∂P := integral_congr_ae (Eventually.of_forall fun ω => hΦeq _)
    _ = ∫ z, Φ z ∂gaussianVec ι h := hlaw.integral_comp hΦm.aestronglyMeasurable
    _ = ∫ y, g (x + y) * slicedWiener P B' h g f n (x + y) ∂gaussian (h : ℝ) := by
        rw [gaussian, Real.toNNReal_coe]

/-! ### The operator side -/

/-- **The one-step operator** `P_h ∘ M_g`: multiply by the weight, then diffuse for time `h`. -/
noncomputable def stepOp (h : ℝ≥0) (gL : Lp ℂ ∞ (volume : Measure E)) : L2 →L[ℂ] L2 :=
  heatSemigroup (h : ℝ) * potential gL

theorem stepOp_apply (h : ℝ≥0) (gL : Lp ℂ ∞ (volume : Measure E)) (v : L2) :
    stepOp h gL v = heatSemigroup (h : ℝ) (potential gL v) :=
  mul_apply_eq_comp _ _ _

/-- An almost-everywhere identity on `ℝᵈ` holds `γ_h`-almost everywhere along every translate. -/
theorem ae_gaussian_of_ae {h : ℝ≥0} (hh : 0 < h) {u v : E → ℂ} (huv : u =ᵐ[volume] v) (x : E) :
    (fun y => u (x + y)) =ᵐ[gaussian (h : ℝ)] fun y => v (x + y) := by
  have h1 := (measurePreserving_add_left (volume : Measure E) x).quasiMeasurePreserving.ae_eq_comp huv
  rw [gaussian, Real.toNNReal_coe]
  exact (gaussianVec_absolutelyContinuous hh.ne').ae_eq h1

/-- ★★ **The time-sliced formula.** For every pre-Brownian motion `B`, slice length `h > 0`, bounded
measurable weight `g` (with `gL` its `L^∞` class) and bounded measurable `f ∈ L²`,

  `((P_h ∘ M_g)ⁿ f)(x) = E[ g (x + B_h) ⋯ g (x + B_{nh}) · f (x + B_{nh}) ]`  for a.e. `x`.

Feynman's sum over paths with `n` slices, in the Euclidean continuum: the operator product on the
left, the integral over Brownian paths on the right. -/
theorem pow_stepOp_apply_ae_eq_slicedWiener [IsProbabilityMeasure P] {h : ℝ≥0} (hh : 0 < h)
    {g f : E → ℂ} (hg : Measurable g) (hf : Measurable f) {Cg Cf : ℝ} (hCg : ∀ x, ‖g x‖ ≤ Cg)
    (hCf : ∀ x, ‖f x‖ ≤ Cf) (hf2 : MemLp f 2 volume) {gL : Lp ℂ ∞ (volume : Measure E)}
    (hgL : gL =ᵐ[volume] g) :
    ∀ (n : ℕ) (B : ℝ≥0 → Ω → E), IsPreBrownianVec B P → (∀ t, Measurable (B t)) →
      (stepOp h gL ^ n) (hf2.toLp f) =ᵐ[volume] slicedWiener P B h g f n := by
  intro n
  induction n with
  | zero =>
    intro B hB _
    rw [pow_zero, one_apply_eq_self]
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx, slicedWiener_zero hB]
  | succ n ih =>
    intro B hB hBm
    set B' : ℝ≥0 → Ω → E := fun t ω => B (h + t) ω - B h ω with hB'
    have hB'pre : IsPreBrownianVec B' P := hB.shift h
    have hB'm : ∀ t, Measurable (B' t) := fun t => (hBm _).sub (hBm _)
    have ihB' := ih B' hB'pre hB'm
    set u : L2 := potential gL ((stepOp h gL ^ n) (hf2.toLp f)) with hu
    have hueq : (u : E → ℂ) =ᵐ[volume] fun z => g z * slicedWiener P B' h g f n z := by
      filter_upwards [coeFn_potential gL ((stepOp h gL ^ n) (hf2.toLp f)), hgL, ihB'] with z h1 h2 h3
      rw [h1, h2, h3]
    have hstep : (stepOp h gL ^ (n + 1)) (hf2.toLp f) = heatSemigroup (h : ℝ) u := by
      rw [pow_succ', mul_apply_eq_comp, stepOp_apply]
    rw [hstep]
    filter_upwards [heatSemigroup_apply_ae_eq (h : ℝ) u] with x hx
    rw [hx, heatConv, slicedWiener_succ hB hBm h hg hf hCg hCf n x]
    exact integral_congr_ae (ae_gaussian_of_ae hh hueq x)

end TimeSlicedWiener
