/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Probability.CompetingExponentials
public import CsdLean4.Mathlib.MeasureTheory.MapProbability
public import CsdLean4.Mathlib.MeasureTheory.MomentDeterminacy
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The race of iid clocks: the exponential law is forced

**Category:** 1-Mathlib. No CSD content: this is the classical competing-risks characterisation,
which Mathlib does not have.

**Glossary:** https://glossary.constraintsurfacedynamics.com/first-passage-race/
Plain-language, CSD-role and formal statements of the first-passage race, with this module as the
Lean anchor. Kept symmetric by `scripts/check-glossary.sh`.

★★★ **`hasRaceProperty_iff_exists_expMeasure`** — for iid clocks at linear rates, the first to fire
wins in proportion to its rate **iff** the waiting-time law is exponential. This is the statement of
`specs/record-layer-plan.md` §3c, and the route to it is
`specs/q12c-exponential-characterisation-route.md`. `CompetingExponentials.lean` supplies the `⇐`
direction in its own framing; everything here is the `⇒` direction.

## The change of framing

There, clock `j` had its own law `Exp bⱼ` and the race was `ξ i < ξ j`. Here all clocks are **iid**
with one unknown law `μ`, and the rate enters as a *scaling*: clock `j` fires at `ξ j / b j`. For
the exponential the two framings agree (`hasRaceProperty_expMeasure`); for a general `μ` only the
second makes sense, because "the law of the clock" is exactly what is being solved for.

* `scaledRaceCell` — the readings on which clock `i` fires first. `scaledRaceCell_one` records that
  at unit rates it is `raceCell`.
* ★★ `measure_scaledRaceCell` — the **kernel identity**: the winning probability is
  `∫ ∏ⱼ G(bⱼ/bᵢ · t) dμ(t)`, with `G t = μ (Ioi t)` the survival function (`survival`). No
  hypothesis on `μ` beyond being a probability measure, and — unlike the exponential case — the
  slice is a box at *every* `t`, not merely almost every one.
* `HasRaceProperty` — the hypothesis of §3c, quantified over **every** number of clocks.

## ★ What the `k`-clock family buys

Instantiating the race at rates `(1, c, c, …, c)` turns an integral equation into a **moment
sequence** — ★★ `HasRaceProperty.lintegral_measure_Ioi_pow` gives `E[G(cξ)ᵏ] = 1/(1 + kc)`, and
★★ `…_pow_mul_pow` the mixed form `E[G(cξ)ᵖ G(ξ)ᵏ] = 1/(1 + pc + k)`. `G(cξ)` takes values in
`[0,1]`, where moments determine the law — which is why the two-clock version of the same question
looks like Choquet–Deny and this one does not. Three consequences, in order:

1. ★★ `HasRaceProperty.map_survival` — `G(ξ)` is uniform on `[0,1]`, with **no regularity
   hypothesis on `μ`**: the `c = 1` moments *are* the uniform moments, so Hausdorff determinacy
   (`MeasureTheory.ext_of_forall_integral_pow_eq_of_null_compl`) closes it. Atomlessness of `μ` is
   therefore *derived* from the race property, not assumed of it.
2. ★★ `HasRaceProperty.survival_natMul_ae` — `G(mt) = G(t)ᵐ` almost everywhere, for every natural
   `m`. ★ The proof needs no quantile, no determinacy in two variables and no injectivity of `G`:
   when the ratio is a **natural number**, `G(t)ᵐ` is itself a product of `m` survival factors at
   rate `1`, so all three terms of `∫ (G(mt) − G(t)ᵐ)² dμ` are instances of the *same* race family
   and cancel.
3. ★ `raceRate_le` — the rate is the same at every good reading. The functional equation ties `G`
   together only along the lattice `{mt}`; **antitonicity** connects two lattices, because
   `mt ≤ nt'` forces `G(t)ᵐ ≥ G(t')ⁿ`. Letting the integer ratio climb to `t'/t` gives the
   comparison, and the real ratios the argument never had are not missed.

Then `HasRaceProperty.exists_eq_expMeasure` reads the law off through `map_survival`.

## ⚠️ The second conjunct is not optional

`HasRaceProperty` quantifies over the **number of clocks**, and that is load-bearing: at a fixed
number of outcomes `n` the family supplies only `n−1` moments, and finitely many moments determine
nothing. What is forced is the exponential law *given that one clock law serves every `n`* — the
measurement-independence of the fibre law that `specs/sigma-fibre-contextuality.md` commits to.
Never state the conclusion without it.

Nothing here is a new physical claim: it removes a posit from the record layer's fibre construction
rather than adding one.

Reference: `specs/q12c-exponential-characterisation-route.md`;
`specs/q12-fibre-mechanism-scoping.md`; `specs/record-layer-plan.md` §3b–§3c;
`specs/sigma-fibre-contextuality.md`; `specs/future-work.md`. See
`ProbabilityTheory.measure_raceCell` for the `⇐` direction in the other framing and
`MeasureTheory.ext_of_forall_integral_pow_eq_of_null_compl` for the determinacy step.
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
    Measure.isProbabilityMeasure_map' hmeas.aemeasurable
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

/-! ### Step 3: the multiplicative functional equation, almost everywhere -/

lemma ofReal_survival (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    ENNReal.ofReal (survival μ t) = μ (Ioi t) :=
  ENNReal.ofReal_toReal (measure_ne_top μ _)

lemma measurable_survival_pow_mul_pow (μ : Measure ℝ) [IsFiniteMeasure μ] (c : ℝ) (p k : ℕ) :
    Measurable (fun t => (survival μ (c * t)) ^ p * (survival μ t) ^ k) :=
  (((measurable_survival μ).comp (measurable_id.const_mul c)).pow_const p).mul
    ((measurable_survival μ).pow_const k)

lemma survival_pow_mul_pow_nonneg (μ : Measure ℝ) (c : ℝ) (p k : ℕ) (t : ℝ) :
    0 ≤ (survival μ (c * t)) ^ p * (survival μ t) ^ k :=
  mul_nonneg (pow_nonneg (survival_nonneg _ _) _) (pow_nonneg (survival_nonneg _ _) _)

lemma integrable_survival_pow_mul_pow (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ)
    (p k : ℕ) : Integrable (fun t => (survival μ (c * t)) ^ p * (survival μ t) ^ k) μ := by
  refine Integrable.of_bound (measurable_survival_pow_mul_pow μ c p k).aestronglyMeasurable 1
    (ae_of_all _ (fun t => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (survival_pow_mul_pow_nonneg μ c p k t)]
  exact mul_le_one₀ (pow_le_one₀ (survival_nonneg _ _) (survival_le_one _ _))
    (pow_nonneg (survival_nonneg _ _) _)
    (pow_le_one₀ (survival_nonneg _ _) (survival_le_one _ _))

/-- The mixed moment identity as a **real** integral of `survival`. -/
theorem HasRaceProperty.integral_survival_pow_mul_pow {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : HasRaceProperty μ) {c : ℝ} (hc : 0 < c) (p k : ℕ) :
    ∫ t, (survival μ (c * t)) ^ p * (survival μ t) ^ k ∂μ = 1 / (1 + p * c + k) := by
  rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ (survival_pow_mul_pow_nonneg μ c p k))
      (measurable_survival_pow_mul_pow μ c p k).aestronglyMeasurable]
  have hpt : ∀ t : ℝ, ENNReal.ofReal ((survival μ (c * t)) ^ p * (survival μ t) ^ k)
      = (μ (Ioi (c * t))) ^ p * (μ (Ioi t)) ^ k := by
    intro t
    rw [ENNReal.ofReal_mul (pow_nonneg (survival_nonneg _ _) _),
      ENNReal.ofReal_pow (survival_nonneg _ _),
      ENNReal.ofReal_pow (survival_nonneg _ _), ofReal_survival, ofReal_survival]
  rw [lintegral_congr hpt, h.lintegral_measure_Ioi_pow_mul_pow hc p k,
    ENNReal.toReal_ofReal (by positivity)]

/-- ★★ **The multiplicative functional equation.** For every `m ≥ 1`, `G(mt) = G(t)ᵐ` for
`μ`-almost every `t`.

★ This is the route's real surprise, and it replaces all three of the assemblies the memo had
mapped — no quantile `G⁻¹`, no two-dimensional determinacy, no injectivity of `G`. The reason is
that when the ratio is a **natural number** `m`, the function `G(t)ᵐ` is *itself a product of `m`
survival factors at rate `1`*, so all three terms of `∫ (G(mt) − G(t)ᵐ)² dμ` are instances of the
same race family:

* `∫ G(mt)² dμ = 1/(1+2m)` at rates `(1, m, m)`;
* `∫ G(mt)·G(t)ᵐ dμ = 1/(1+2m)` at rates `(1, m, 1ᵐ)`;
* `∫ G(t)²ᵐ dμ = 1/(1+2m)` at rates `(1, 1²ᵐ)`.

They cancel, so the square has integral zero and vanishes almost everywhere. Restricting the ratio
to the integers is exactly what makes the cross term computable — and `HasRaceProperty.eq_expMeasure`
shows the integers are enough, because monotonicity supplies what the missing real ratios would
have. -/
theorem HasRaceProperty.survival_natMul_ae {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : HasRaceProperty μ) {m : ℕ} (hm : 0 < m) :
    ∀ᵐ t ∂μ, survival μ ((m : ℝ) * t) = (survival μ t) ^ m := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hexp : ∀ t : ℝ, (survival μ ((m : ℝ) * t) - (survival μ t) ^ m) ^ 2
      = ((survival μ ((m : ℝ) * t)) ^ 2 * (survival μ t) ^ 0
        - 2 * ((survival μ ((m : ℝ) * t)) ^ 1 * (survival μ t) ^ m))
        + (survival μ ((m : ℝ) * t)) ^ 0 * (survival μ t) ^ (2 * m) := by
    intro t
    rw [pow_mul]
    ring
  have hI2 : Integrable
      (fun t => 2 * ((survival μ ((m : ℝ) * t)) ^ 1 * (survival μ t) ^ m)) μ :=
    (integrable_survival_pow_mul_pow μ (m : ℝ) 1 m).const_mul 2
  have hIsub : Integrable (fun t => (survival μ ((m : ℝ) * t)) ^ 2 * (survival μ t) ^ 0
      - 2 * ((survival μ ((m : ℝ) * t)) ^ 1 * (survival μ t) ^ m)) μ :=
    (integrable_survival_pow_mul_pow μ (m : ℝ) 2 0).sub hI2
  have hIall : Integrable (fun t => (survival μ ((m : ℝ) * t) - (survival μ t) ^ m) ^ 2) μ :=
    (hIsub.add (integrable_survival_pow_mul_pow μ (m : ℝ) 0 (2 * m))).congr
      (ae_of_all _ (fun t => (hexp t).symm))
  have hzero : ∫ t, (survival μ ((m : ℝ) * t) - (survival μ t) ^ m) ^ 2 ∂μ = 0 := by
    rw [integral_congr_ae (ae_of_all _ hexp),
      integral_add hIsub (integrable_survival_pow_mul_pow μ (m : ℝ) 0 (2 * m)),
      integral_sub (integrable_survival_pow_mul_pow μ (m : ℝ) 2 0) hI2,
      integral_const_mul, h.integral_survival_pow_mul_pow hmR 2 0,
      h.integral_survival_pow_mul_pow hmR 1 m, h.integral_survival_pow_mul_pow hmR 0 (2 * m)]
    push_cast
    ring
  have hae := (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg _) hIall).mp hzero
  filter_upwards [hae] with t ht
  have hsq : (survival μ ((m : ℝ) * t) - (survival μ t) ^ m) ^ 2 = 0 := ht
  have hz := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  linarith [hz]

/-! ### Step 4: from the functional equation to the exponential law -/

/-- The survival function avoids both endpoints almost everywhere — immediate from step 2, since
`{0, 1}` is Lebesgue-null. -/
theorem HasRaceProperty.survival_mem_Ioo_ae {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : HasRaceProperty μ) : ∀ᵐ t ∂μ, survival μ t ∈ Ioo (0 : ℝ) 1 := by
  have hmeas := measurable_survival μ
  have hfin' : ({0, 1} : Set ℝ).Finite := Set.toFinite _
  have hfin : MeasurableSet ({0, 1} : Set ℝ) := hfin'.measurableSet
  have hnull : μ ((survival μ) ⁻¹' ({0, 1} : Set ℝ)) = 0 := by
    rw [← Measure.map_apply hmeas hfin, h.map_survival, Measure.restrict_apply hfin]
    exact measure_mono_null Set.inter_subset_left (hfin'.measure_zero _)
  rw [ae_iff]
  refine measure_mono_null (fun t ht => ?_) hnull
  simp only [Set.mem_ofPred_eq, Set.mem_Ioo, not_and, not_lt] at ht
  have h0 := survival_nonneg μ t
  have h1 := survival_le_one μ t
  rcases eq_or_lt_of_le h0 with heq | hpos
  · simp [Set.mem_preimage, ← heq]
  · have : survival μ t = 1 := le_antisymm h1 (ht hpos)
    simp [Set.mem_preimage, this]

/-- The clock readings are almost surely **positive** — derived, not assumed.

The route memo sets the problem up with `ξ` supported on `(0,∞)`; it does not have to. Antitonicity
plus the `m = 2` case of the functional equation is enough: for `t ≤ 0` one has `2t ≤ t`, so
`G(t) ≤ G(2t) = G(t)²`, which is false for `G(t) ∈ (0,1)`. -/
theorem HasRaceProperty.pos_ae {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : HasRaceProperty μ) :
    ∀ᵐ t ∂μ, 0 < t := by
  filter_upwards [h.survival_mem_Ioo_ae, h.survival_natMul_ae (m := 2) two_pos] with t ht h2
  by_contra hle
  push Not at hle
  have hmono : survival μ t ≤ survival μ ((2 : ℕ) * t) := by
    refine antitone_survival μ ?_
    push_cast
    linarith
  rw [h2] at hmono
  nlinarith [ht.1, ht.2]

/-- **A good reading**: positive, with the survival function strictly inside `(0,1)`, and satisfying
the whole multiplicative family. `HasRaceProperty.ae_regular` says almost every reading is good;
everything after this point is an argument about good readings and their ratios to one another. -/
def RaceRegular (μ : Measure ℝ) (t : ℝ) : Prop :=
  0 < t ∧ survival μ t ∈ Ioo (0 : ℝ) 1 ∧
    ∀ m : ℕ, 0 < m → survival μ ((m : ℝ) * t) = (survival μ t) ^ m

/-- The three almost-everywhere facts, bundled: positivity, both endpoints avoided, and the whole
multiplicative family at once (a countable intersection, via `ae_all_iff`). -/
theorem HasRaceProperty.ae_regular {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : HasRaceProperty μ) : ∀ᵐ t ∂μ, RaceRegular μ t := by
  have hall : ∀ᵐ t ∂μ, ∀ m : ℕ, 0 < m → survival μ ((m : ℝ) * t) = (survival μ t) ^ m := by
    rw [ae_all_iff]
    intro m
    by_cases hm : 0 < m
    · filter_upwards [h.survival_natMul_ae hm] with t ht using fun _ => ht
    · exact ae_of_all _ (fun _ hm' => absurd hm' hm)
  filter_upwards [h.pos_ae, h.survival_mem_Ioo_ae, hall] with t h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- The rate read off at a good reading: the `λ` for which `G t = e^{-λt}` at that one point. -/
noncomputable def raceRate (μ : Measure ℝ) (t : ℝ) : ℝ := -Real.log (survival μ t) / t

lemma raceRate_pos {μ : Measure ℝ} {t : ℝ} (ht : RaceRegular μ t) : 0 < raceRate μ t := by
  have hlog : Real.log (survival μ t) < 0 := Real.log_neg ht.2.1.1 ht.2.1.2
  exact div_pos (by linarith) ht.1

lemma survival_eq_exp_raceRate {μ : Measure ℝ} {t : ℝ} (ht : RaceRegular μ t) :
    survival μ t = Real.exp (-(raceRate μ t * t)) := by
  simp only [raceRate]
  rw [div_mul_cancel₀ _ ht.1.ne', neg_neg, Real.exp_log ht.2.1.1]

/-- ★ **The rate is the same at every good reading**, which is what makes the *integer* ratios of
`survival_natMul_ae` enough to pin the law down.

The functional equation ties `G` together only along the lattice `{mt}`, and a priori nothing
connects the lattices of two different readings. **Antitonicity connects them**: whenever `mt ≤ nt'`
one has `G(t)ᵐ = G(mt) ≥ G(nt') = G(t')ⁿ`, so `m·λ(t)·t ≤ n·λ(t')·t'`. Letting the integer ratio
`m/n` climb to `t'/t` gives `λ(t) ≤ λ(t')`, and symmetry gives equality. Neither density of the
support nor a real ratio is needed anywhere. -/
lemma raceRate_le {μ : Measure ℝ} [IsFiniteMeasure μ] {t t' : ℝ}
    (ht : RaceRegular μ t) (ht' : RaceRegular μ t') : raceRate μ t ≤ raceRate μ t' := by
  set a : ℝ := -Real.log (survival μ t) with ha
  set b : ℝ := -Real.log (survival μ t') with hb
  have hapos : 0 < a := by
    have := Real.log_neg ht.2.1.1 ht.2.1.2
    rw [ha]; linarith
  have hbpos : 0 < b := by
    have := Real.log_neg ht'.2.1.1 ht'.2.1.2
    rw [hb]; linarith
  have key : ∀ m n : ℕ, 0 < m → 0 < n → (m : ℝ) * t ≤ (n : ℝ) * t' →
      (m : ℝ) * a ≤ (n : ℝ) * b := by
    intro m n hm hn hle
    have h1 : survival μ ((n : ℝ) * t') ≤ survival μ ((m : ℝ) * t) := antitone_survival μ hle
    rw [ht.2.2 m hm, ht'.2.2 n hn] at h1
    have h2 := Real.log_le_log (pow_pos ht'.2.1.1 n) h1
    rw [Real.log_pow, Real.log_pow] at h2
    rw [ha, hb]
    linarith
  have hmain : a * t' ≤ b * t := by
    by_contra hcon
    push Not at hcon
    set d : ℝ := a * t' - b * t with hd
    have hdpos : 0 < d := by rw [hd]; linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (max (a * t / d) (t / t'))
    have hn1 : a * t / d < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
    have hn2 : t / t' < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
    have hnpos : 0 < (n : ℝ) := lt_trans (div_pos ht.1 ht'.1) hn2
    have hnnat : 0 < n := Nat.cast_pos.mp hnpos
    have hone : (1 : ℝ) ≤ (n : ℝ) * t' / t := by
      rw [le_div_iff₀ ht.1]
      rw [div_lt_iff₀ ht'.1] at hn2
      linarith
    have hmpos : 0 < ⌊(n : ℝ) * t' / t⌋₊ := Nat.le_floor (by exact_mod_cast hone)
    have hmle : ((⌊(n : ℝ) * t' / t⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) * t' / t := Nat.floor_le (div_nonneg (mul_nonneg (Nat.cast_nonneg n) ht'.1.le) ht.1.le)
    have hmgt : (n : ℝ) * t' / t < ((⌊(n : ℝ) * t' / t⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have hmt : ((⌊(n : ℝ) * t' / t⌋₊ : ℕ) : ℝ) * t ≤ (n : ℝ) * t' := by
      rw [le_div_iff₀ ht.1] at hmle; linarith
    have hkey := key _ n hmpos hnnat hmt
    have hmt' : (n : ℝ) * t' - t < ((⌊(n : ℝ) * t' / t⌋₊ : ℕ) : ℝ) * t := by
      rw [div_lt_iff₀ ht.1] at hmgt; linarith
    have hcontra : (n : ℝ) * d < a * t := by
      rw [hd]
      nlinarith [hkey, hmt', hapos, ht.1, ht'.1]
    rw [div_lt_iff₀ hdpos] at hn1
    linarith
  simp only [raceRate, ← ha, ← hb]
  rw [div_le_div_iff₀ ht.1 ht'.1]
  exact hmain

/-- ★★★ **The race property forces the exponential law.**

This is the `⇒` direction of `specs/record-layer-plan.md` §3c: if for **every** number of clocks and
every positive rate vector the first of `n` iid clocks to fire is clock `i` with probability
`bᵢ/Σⱼbⱼ`, then the clock law is exponential. With `hasRaceProperty_expMeasure` for the converse it
is the characterisation.

⚠️ **The second conjunct travels with the first.** `HasRaceProperty` quantifies over the number of
clocks, and that is not a formality: at a *fixed* number of outcomes `n` the family supplies only
`n−1` moments, and finitely many moments determine nothing. So what is forced is the exponential law
**given that one clock law serves every `n`** — the measurement-independence of the fibre law that
`specs/sigma-fibre-contextuality.md` commits to. Never state the conclusion without it. -/
theorem HasRaceProperty.exists_eq_expMeasure {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : HasRaceProperty μ) : ∃ lam : ℝ, 0 < lam ∧ μ = expMeasure lam := by
  have hreg := h.ae_regular
  obtain ⟨t₀, ht₀⟩ := hreg.exists
  set lam : ℝ := raceRate μ t₀ with hlamdef
  have hlampos : 0 < lam := raceRate_pos ht₀
  refine ⟨lam, hlampos, ?_⟩
  have hprobExp : IsProbabilityMeasure (expMeasure lam) := isProbabilityMeasure_expMeasure hlampos
  have hmeas := measurable_survival μ
  have hG : ∀ t, RaceRegular μ t → survival μ t = Real.exp (-(lam * t)) := by
    intro t ht
    have hrate : raceRate μ t = lam := le_antisymm (raceRate_le ht ht₀) (raceRate_le ht₀ ht)
    rw [survival_eq_exp_raceRate ht, hrate]
  have hIoi : ∀ s : ℝ, μ (Ioi s) = expMeasure lam (Ioi s) := by
    intro s
    set c : ℝ := Real.exp (-(lam * s)) with hc
    have hcpos : 0 < c := Real.exp_pos _
    have hset : Ioi s =ᵐ[μ] (survival μ) ⁻¹' (Iio c) := by
      rw [Filter.eventuallyEq_set]
      filter_upwards [hreg] with t ht
      rw [Set.mem_Ioi, Set.mem_preimage, Set.mem_Iio, hG t ht, hc, Real.exp_lt_exp]
      constructor <;> intro hh <;> nlinarith [hlampos]
    rw [measure_congr hset, ← Measure.map_apply hmeas measurableSet_Iio, h.map_survival,
      Measure.restrict_apply measurableSet_Iio]
    rcases le_or_gt 0 s with hs | hs
    · have hc1 : c ≤ 1 := by
        rw [hc, Real.exp_le_one_iff]
        nlinarith
      have hslice : Iio c ∩ Icc (0 : ℝ) 1 = Ico 0 c := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
        constructor
        · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1, le_trans h2.le hc1⟩
      rw [hslice, Real.volume_Ico, sub_zero, expMeasure_Ioi hlampos hs, hc]
    · have hc1 : 1 < c := by
        rw [hc, ← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by nlinarith)
      have hslice : Iio c ∩ Icc (0 : ℝ) 1 = Icc 0 1 := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc]
        exact ⟨fun hx => hx.2, fun hx => ⟨lt_of_le_of_lt hx.2 hc1, hx⟩⟩
      have hIic : expMeasure lam (Iic s) = 0 := by
        rw [← ofReal_cdf, cdf_expMeasure_eq hlampos s, if_neg (not_le.mpr hs)]
        simp
      rw [hslice, Real.volume_Icc, ← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, hIic]
      simp
  refine Measure.ext_of_Iic μ (expMeasure lam) (fun s => ?_)
  rw [← compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi,
    prob_compl_eq_one_sub measurableSet_Ioi, hIoi s]

/-- ★★★ **The characterisation** of `specs/record-layer-plan.md` §3c: for iid linear clocks,
first-to-fire is proportional to the rate **iff** the waiting times are exponential.

The `⇐` direction is `hasRaceProperty_expMeasure`; the `⇒` direction is
`HasRaceProperty.exists_eq_expMeasure`, and it carries the second conjunct documented there —
`HasRaceProperty` quantifies over the number of clocks, so what is characterised is *the law that
serves every `n`*. -/
theorem hasRaceProperty_iff_exists_expMeasure {μ : Measure ℝ} [IsProbabilityMeasure μ] :
    HasRaceProperty μ ↔ ∃ lam : ℝ, 0 < lam ∧ μ = expMeasure lam :=
  ⟨fun h => h.exists_eq_expMeasure,
    fun ⟨_, hlam, hμ⟩ => hμ ▸ hasRaceProperty_expMeasure hlam⟩

end ProbabilityTheory
