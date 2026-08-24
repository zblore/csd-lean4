/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Probability.CompetingExponentials
public import CsdLean4.Mathlib.MeasureTheory.MomentDeterminacy
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The race of iid clocks at general rates, and the moments it forces

**Category:** 1-Mathlib. No CSD content: this is the competing-risks computation of
`CompetingExponentials.lean` with the exponential assumption removed.

That file proves the `⇐` half of `specs/record-layer-plan.md` §3c: *exponential* waiting times make
the first clock to fire win in proportion to its rate. This file is the apparatus for the `⇒` half
— step 1 of `specs/q12c-exponential-characterisation-route.md`.

## The change of framing

There, clock `j` had its own law `Exp bⱼ` and the race was `ξ i < ξ j`. Here all clocks are **iid**
with one unknown law `μ`, and the rate enters as a *scaling*: clock `j` fires at `ξ j / b j`. For
the exponential the two framings agree (`hasRaceProperty_expMeasure`); for a general `μ` only the
second makes sense, because "the law of the clock" is exactly what is being solved for.

* `scaledRaceCell` — the readings on which clock `i` fires first. `scaledRaceCell_one` records that
  at unit rates it is `raceCell`.
* ★★ `measure_scaledRaceCell` — the **kernel identity**: the winning probability is
  `∫ ∏ⱼ G(bⱼ/bᵢ · t) dμ(t)`, with `G t = μ (Ioi t)` the survival function. No hypothesis on `μ`
  beyond being a probability measure, and — unlike the exponential case — the slice is a box at
  *every* `t`, not merely almost every one.
* `HasRaceProperty` — the hypothesis of §3c, quantified over **every** number of clocks.
* `hasRaceProperty_expMeasure` — the witness that the hypothesis is satisfiable at all.

## ★ What the `k`-clock family buys

Instantiating the race at rates `(1, c, c, …, c)` turns an integral equation into a **moment
sequence**:

* ★★ `HasRaceProperty.lintegral_measure_Ioi_pow` — `E[G(cξ)ᵏ] = 1/(1 + kc)` for every `k`, which is
  `(1)` of the route memo, and
* ★★ `HasRaceProperty.lintegral_measure_Ioi_pow_mul_pow` — the mixed form
  `E[G(cξ)ᵖ G(ξ)ᵏ] = 1/(1 + pc + k)` at rates `(1, c^p, 1^k)`, which is the form step 3′
  (`MeasureTheory.eq_of_forall_integral_mul_pow_eq`) consumes: at `p = 1` it is a *fixed continuous
  weight* integrated against every power.

`G(cξ)` takes values in `[0,1]`, where moments determine the law — which is why the two-clock
version of the same question looks like Choquet–Deny and this one does not.

## ⚠️ Scope

Nothing here is a new physical claim, and **this file does not prove §3c**. It supplies the
probabilistic input; converting the moment identities into `G(ct) = G(t)ᶜ` is steps 2–4 of the route
memo, which are not in the corpus. The hypothesis `HasRaceProperty` also quantifies over the number
of clocks, and that is not free: at a *fixed* number of outcomes the moment sequence is finite and
determines nothing. The honest reading of anything built on it carries a second conjunct — *given
that one clock law serves every `n`* — which is the measurement-independence
`specs/sigma-fibre-contextuality.md` already commits to.

Reference: `specs/q12c-exponential-characterisation-route.md` (the four-step route, and step 1 in
particular); `specs/q12-fibre-mechanism-scoping.md`; `specs/record-layer-plan.md` §3b–§3c;
`specs/future-work.md`. See `ProbabilityTheory.measure_raceCell` for the `⇐` direction and
`MeasureTheory.eq_of_forall_integral_mul_pow_eq` for the determinacy step downstream.
-/

@[expose] public section

open MeasureTheory Set Real

namespace ProbabilityTheory

variable {n : ℕ}

/-! ### The race at general rates -/

/-- **The scaled race cell**: the readings on which clock `i` fires first, when clock `j` reads
`ξ j` and fires at `ξ j / b j`.

The rate enters by scaling the *reading* rather than by changing the *law*, which is what lets the
law stay an unknown. At unit rates this is `raceCell` (`scaledRaceCell_one`). -/
def scaledRaceCell (b : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : Set (Fin (n + 1) → ℝ) :=
  {ξ | ∀ j, j ≠ i → ξ i / b i < ξ j / b j}

@[simp] lemma mem_scaledRaceCell {b : Fin (n + 1) → ℝ} {i : Fin (n + 1)} {ξ : Fin (n + 1) → ℝ} :
    ξ ∈ scaledRaceCell b i ↔ ∀ j, j ≠ i → ξ i / b i < ξ j / b j := Iff.rfl

/-- At unit rates the scaled race is the plain race of `CompetingExponentials.lean`. -/
lemma scaledRaceCell_one (i : Fin (n + 1)) :
    scaledRaceCell (fun _ => (1 : ℝ)) i = raceCell i := by
  ext ξ
  simp [scaledRaceCell, raceCell]

lemma measurableSet_scaledRaceCell (b : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    MeasurableSet (scaledRaceCell b i) := by
  have h : scaledRaceCell b i
      = ⋂ j ∈ {j : Fin (n + 1) | j ≠ i}, {ξ : Fin (n + 1) → ℝ | ξ i / b i < ξ j / b j} := by
    ext ξ; simp [scaledRaceCell]
  rw [h]
  exact MeasurableSet.biInter (Set.to_countable _)
    (fun j _ => measurableSet_lt ((measurable_pi_apply i).div_const _)
      ((measurable_pi_apply j).div_const _))

/-- The race cells are pairwise disjoint at any rates: two clocks cannot both be strictly first.
Like `raceCell_pairwiseDisjoint`, this is the partition content and needs no hypothesis on the
rates at all. -/
lemma scaledRaceCell_pairwiseDisjoint (b : Fin (n + 1) → ℝ) :
    Pairwise (Function.onFun Disjoint (scaledRaceCell b)) := by
  intro i j hij
  refine Set.disjoint_left.mpr (fun ξ hi hj => ?_)
  exact absurd (hi j (Ne.symm hij)) (not_lt.mpr (hj i hij).le)

/-- ★★ **The kernel identity.** For iid clocks with law `μ` at rates `b`, clock `i` wins with
probability `∫ ∏ⱼ G(bⱼ/bᵢ · t) dμ(t)`, where `G t = μ (Ioi t)` is the survival function and the
product runs over the other clocks.

This is `measure_raceCell` with the exponential assumption removed and the integral left standing:
there `G` was known and the integral could be evaluated, here `G` is the unknown. The proof splits
coordinate `i` off the product (`measurePreserving_piFinSuccAbove`) and reads the remaining clocks'
survival as a *box* (`Measure.pi_pi`) — and because the rates are carried by the scaling rather than
by the law, the slice is a box at every `t`, so no almost-everywhere step is needed. -/
theorem measure_scaledRaceCell (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (b : Fin (n + 1) → ℝ) (hb : ∀ j, 0 < b j) (i : Fin (n + 1)) :
    Measure.pi (fun _ : Fin (n + 1) => μ) (scaledRaceCell b i)
      = ∫⁻ t, ∏ j : Fin n, μ (Ioi (b (i.succAbove j) / b i * t)) ∂μ := by
  classical
  -- with positive rates, clock `i` reading `x` beats clock `j` reading `y` exactly when `y`
  -- exceeds `bⱼ/bᵢ · x` — which is what turns each slice into a box
  have hratio : ∀ x y u v : ℝ, 0 < u → 0 < v → (x / u < y / v ↔ v / u * x < y) := by
    intro x y u v hu hv
    rw [div_lt_div_iff₀ hu hv, div_mul_eq_mul_div, div_lt_iff₀ hu, mul_comm x v]
  set W : Set (ℝ × (Fin n → ℝ)) := {p | ∀ j, p.1 / b i < p.2 j / b (i.succAbove j)} with hW
  have hWmeas : MeasurableSet W := by
    have h : W = ⋂ j, {p : ℝ × (Fin n → ℝ) | p.1 / b i < p.2 j / b (i.succAbove j)} := by
      ext p; simp [hW]
    rw [h]
    exact MeasurableSet.iInter (fun j =>
      measurableSet_lt (measurable_fst.div_const _)
        (((measurable_pi_apply j).comp measurable_snd).div_const _))
  have hpre : scaledRaceCell b i = (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i) ⁻¹' W := by
    ext ξ
    simp only [scaledRaceCell, Set.mem_preimage, Set.mem_ofPred_eq, hW]
    show (∀ j, j ≠ i → ξ i / b i < ξ j / b j) ↔
      ∀ j : Fin n, ξ i / b i < ξ (i.succAbove j) / b (i.succAbove j)
    refine ⟨fun h j => h _ (Fin.succAbove_ne i j), fun h j hj => ?_⟩
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    exact h k
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  rw [hpre, hmp.measure_preimage hWmeas.nullMeasurableSet, Measure.prod_apply hWmeas]
  refine lintegral_congr (fun t => ?_)
  have hbox : (Prod.mk t ⁻¹' W)
      = Set.pi univ (fun j : Fin n => Ioi (b (i.succAbove j) / b i * t)) := by
    ext ζ
    simp only [hW, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
      forall_const, Set.mem_Ioi]
    exact forall_congr' (fun j => hratio _ _ _ _ (hb i) (hb _))
  rw [hbox, Measure.pi_pi]

/-! ### The race property, and the moment sequence it forces -/

/-- **The race property** of `specs/record-layer-plan.md` §3c: for iid clocks with law `μ`, the
first to fire is clock `i` with probability `bᵢ / Σⱼ bⱼ`, for **every** number of clocks and every
positive rate vector.

The quantification over `n` is the load-bearing part and is not free — see the scope note in the
module docstring. `hasRaceProperty_expMeasure` is the witness that the hypothesis is satisfiable. -/
def HasRaceProperty (μ : Measure ℝ) : Prop :=
  ∀ (n : ℕ) (b : Fin (n + 1) → ℝ), (∀ j, 0 < b j) → ∀ i : Fin (n + 1),
    Measure.pi (fun _ : Fin (n + 1) => μ) (scaledRaceCell b i) = ENNReal.ofReal (b i / ∑ j, b j)

/-- Putting the winning clock at rate `1` in front of positive rates keeps every rate positive. -/
lemma cons_one_pos {r : Fin n → ℝ} (hr : ∀ j, 0 < r j) :
    ∀ j : Fin (n + 1), 0 < (Fin.cons 1 r : Fin (n + 1) → ℝ) j := by
  refine Fin.cases ?_ ?_
  · simp
  · intro j; simpa using hr j

/-- The kernel identity at a **unit-rate winner**: clock `0` runs at rate `1` and the rest at rates
`r`, so the ratios `rⱼ/1` are the rates themselves. -/
lemma measure_scaledRaceCell_cons_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (r : Fin n → ℝ) (hr : ∀ j, 0 < r j) :
    Measure.pi (fun _ : Fin (n + 1) => μ) (scaledRaceCell (Fin.cons 1 r) 0)
      = ∫⁻ t, ∏ j : Fin n, μ (Ioi (r j * t)) ∂μ := by
  rw [measure_scaledRaceCell μ _ (cons_one_pos hr) 0]
  simp

/-- ★★ **The race property turns into a family of moments.** For any positive rates `r` on the
losing clocks, `∫ ∏ⱼ G(rⱼ t) dμ(t) = 1/(1 + Σⱼ rⱼ)`.

This is step 1 of `specs/q12c-exponential-characterisation-route.md` in its general form; the two
corollaries below are the instantiations the route uses. -/
theorem HasRaceProperty.lintegral_prod_measure_Ioi {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : HasRaceProperty μ) (r : Fin n → ℝ) (hr : ∀ j, 0 < r j) :
    ∫⁻ t, ∏ j : Fin n, μ (Ioi (r j * t)) ∂μ = ENNReal.ofReal (1 / (1 + ∑ j, r j)) := by
  rw [← measure_scaledRaceCell_cons_one μ r hr, h n (Fin.cons 1 r) (cons_one_pos hr) 0,
    Fin.cons_zero, Fin.sum_cons]

/-- ★★ **`(1)` of the route memo.** Racing one clock at rate `1` against `k` clocks at rate `c`
gives the moment sequence `E[G(cξ)ᵏ] = 1/(1 + kc)`.

The integral equation of the two-clock case has become a *moment problem* on `[0,1]`, where the
moments determine the law. -/
theorem HasRaceProperty.lintegral_measure_Ioi_pow {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : HasRaceProperty μ) {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ∫⁻ t, (μ (Ioi (c * t))) ^ k ∂μ = ENNReal.ofReal (1 / (1 + k * c)) := by
  have hk := h.lintegral_prod_measure_Ioi (fun _ : Fin k => c) (fun _ => hc)
  simpa [Finset.prod_const, Finset.sum_const, nsmul_eq_mul] using hk

/-- ★★ **The mixed moments**, at rates `(1, c^p, 1^k)`: `E[G(cξ)ᵖ G(ξ)ᵏ] = 1/(1 + pc + k)`.

This is the form step 3′ consumes. At `p = 1` the left-hand side is a *fixed continuous weight*
integrated against every power of `G(ξ)`, which is exactly the hypothesis of
`MeasureTheory.eq_of_forall_integral_mul_pow_eq` — so no joint law, no rearrangement theory and no
two-dimensional determinacy is needed. -/
theorem HasRaceProperty.lintegral_measure_Ioi_pow_mul_pow {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : HasRaceProperty μ) {c : ℝ} (hc : 0 < c) (p k : ℕ) :
    ∫⁻ t, (μ (Ioi (c * t))) ^ p * (μ (Ioi t)) ^ k ∂μ
      = ENNReal.ofReal (1 / (1 + p * c + k)) := by
  set r : Fin (p + k) → ℝ := Fin.append (fun _ : Fin p => c) (fun _ : Fin k => (1 : ℝ)) with hr
  have hpos : ∀ j : Fin (p + k), 0 < r j := by
    refine Fin.addCases ?_ ?_
    · intro j; simpa [hr] using hc
    · intro j; simp [hr]
  have hmain := h.lintegral_prod_measure_Ioi r hpos
  have hprod : ∀ t : ℝ, ∏ j : Fin (p + k), μ (Ioi (r j * t))
      = (μ (Ioi (c * t))) ^ p * (μ (Ioi t)) ^ k := by
    intro t
    rw [Fin.prod_univ_add]
    simp [hr]
  have hsum : (1 : ℝ) + ∑ j, r j = 1 + p * c + k := by
    rw [Fin.sum_univ_add]
    simp only [hr, Fin.append_left, Fin.append_right, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  rw [lintegral_congr hprod, hsum] at hmain
  exact hmain

/-! ### Non-vacuity: the exponential laws have the race property -/

/-- **The hypothesis is satisfiable.** Every exponential law has the race property — which is the
`⇐` direction of §3c in the iid framing, and the check that `HasRaceProperty` is not vacuous.

Compare `measure_raceCell`, which is the same fact in the other framing: there the rate lived in
the law (`Exp bⱼ`) and the race was unscaled; here one law serves every clock and the rate scales
the reading. The two agree because `ξ / b` is `Exp (rb)` when `ξ` is `Exp r` — visible in the proof
as the rate `r` cancelling out of `r / (r + r·S/bᵢ)`. -/
theorem hasRaceProperty_expMeasure {r : ℝ} (hr : 0 < r) : HasRaceProperty (expMeasure r) := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  intro n b hb i
  rw [measure_scaledRaceCell _ b hb i]
  set S : ℝ := ∑ j : Fin n, b (i.succAbove j) with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun j _ => (hb _).le)
  have hbi : 0 < b i := hb i
  have hSb : 0 ≤ r * (S / b i) := by positivity
  have hslice : ∀ t : ℝ, 0 ≤ t →
      ∏ j : Fin n, expMeasure r (Ioi (b (i.succAbove j) / b i * t))
        = ENNReal.ofReal (exp (-(r * (S / b i) * t))) := by
    intro t ht
    have hnn : ∀ j : Fin n, 0 ≤ b (i.succAbove j) / b i * t :=
      fun j => mul_nonneg (div_nonneg (hb _).le hbi.le) ht
    have hfac : ∀ j : Fin n, -(r * (b (i.succAbove j) / b i * t))
        = (-(r * t / b i)) * b (i.succAbove j) := by
      intro j; field_simp
    have hexp : ∑ j : Fin n, -(r * (b (i.succAbove j) / b i * t))
        = -(r * (S / b i) * t) := by
      rw [Finset.sum_congr rfl (fun j _ => hfac j), ← Finset.mul_sum, ← hS]
      field_simp
    rw [Finset.prod_congr rfl (fun j _ => expMeasure_Ioi hr (hnn j)),
      ← ENNReal.ofReal_prod_of_nonneg (fun j _ => (exp_pos _).le), ← Real.exp_sum, hexp]
  rw [lintegral_congr_ae ((expMeasure_ae_nonneg hr).mono hslice),
    lintegral_exp_neg_expMeasure hr hSb]
  congr 1
  rw [Fin.sum_univ_succAbove b i, ← hS]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  field_simp

/-! ### Step 2: the race property forces the survival function to be uniform -/

/-- **The survival function** `G t = P(ξ > t)` of a law on the line, as a real-valued function.

Real-valued, whereas the kernel identity above states the same thing in `ℝ≥0∞` because that is
where `lintegral` lives: the analytic half of the route consumes a *continuous real* function
(`MeasureTheory.eq_of_forall_integral_mul_pow_eq` lives on `C(Icc a b, ℝ)`), and this is the form
it wants. -/
noncomputable def survival (μ : Measure ℝ) (t : ℝ) : ℝ := (μ (Ioi t)).toReal

lemma survival_nonneg (μ : Measure ℝ) (t : ℝ) : 0 ≤ survival μ t := ENNReal.toReal_nonneg

lemma survival_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) : survival μ t ≤ 1 := by
  have h : μ (Ioi t) ≤ 1 := prob_le_one
  simpa [survival] using ENNReal.toReal_mono ENNReal.one_ne_top h

lemma survival_mem_Icc (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    survival μ t ∈ Icc (0 : ℝ) 1 :=
  ⟨survival_nonneg μ t, survival_le_one μ t⟩

lemma antitone_survival (μ : Measure ℝ) [IsFiniteMeasure μ] : Antitone (survival μ) :=
  fun _ _ hst => ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Ioi_subset_Ioi hst))

lemma measurable_survival (μ : Measure ℝ) [IsFiniteMeasure μ] : Measurable (survival μ) :=
  (antitone_survival μ).measurable

/-- The `ℝ≥0∞` form of the moment identity, read back as a real integral of `survival`. -/
lemma integral_survival_pow (μ : Measure ℝ) [IsProbabilityMeasure μ] (k : ℕ) :
    ∫ t, (survival μ t) ^ k ∂μ = (∫⁻ t, (μ (Ioi t)) ^ k ∂μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun t => pow_nonneg (survival_nonneg μ t) k))
    ((measurable_survival μ).pow_const k).aestronglyMeasurable]
  congr 1
  refine lintegral_congr (fun t => ?_)
  rw [survival, ← ENNReal.toReal_pow,
    ENNReal.ofReal_toReal (ENNReal.pow_ne_top (measure_ne_top μ _))]

/-- ★★ **Step 2 — the probability integral transform, and the regularity comes free.**

`G(ξ)` is uniform on `[0,1]`.

The route memo assumes `G` continuous and strictly decreasing, and reaches this by the standard
probability integral transform. It does not have to: the `c = 1` case of the moment family already
says `E[G(ξ)ᵏ] = 1/(1+k)` for every `k`, and those are exactly the moments of the uniform law, so
Hausdorff determinacy (`MeasureTheory.ext_of_forall_integral_pow_eq_of_null_compl`) delivers the
conclusion with **no hypothesis on `μ` at all**.

So atomlessness of `μ` is a *consequence* of the race property rather than an assumption on it —
as it must be, since the `k+1`-clock race at equal rates says the smallest of `k+1` iid readings is
*strictly* smallest with probability `1/(k+1)`, and ties would cost. -/
theorem HasRaceProperty.map_survival {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : HasRaceProperty μ) :
    μ.map (survival μ) = volume.restrict (Icc 0 1) := by
  have hmeas := measurable_survival μ
  have : IsProbabilityMeasure (μ.map (survival μ)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  have : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  refine MeasureTheory.ext_of_forall_integral_pow_eq_of_null_compl (a := 0) (b := 1) ?_ ?_ ?_
  · have hempty : (survival μ) ⁻¹' (Icc (0 : ℝ) 1)ᶜ = ∅ := by
      ext t
      simpa using survival_mem_Icc μ t
    rw [Measure.map_apply hmeas measurableSet_Icc.compl, hempty, measure_empty]
  · rw [Measure.restrict_apply measurableSet_Icc.compl, Set.compl_inter_self, measure_empty]
  · intro k
    have hL : ∫ x, (survival μ x) ^ k ∂μ = 1 / (1 + k) := by
      rw [integral_survival_pow μ k]
      have hmom := h.lintegral_measure_Ioi_pow (c := 1) one_pos k
      simp only [one_mul, mul_one] at hmom
      rw [hmom, ENNReal.toReal_ofReal (by positivity)]
    have hR : ∫ x, x ^ k ∂(volume.restrict (Icc (0 : ℝ) 1)) = 1 / (1 + k) := by
      rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc,
        ← intervalIntegral.integral_of_le zero_le_one, integral_pow]
      norm_num
      ring
    rw [integral_map (f := fun x : ℝ => x ^ k) hmeas.aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop)), hL, hR]

end ProbabilityTheory
