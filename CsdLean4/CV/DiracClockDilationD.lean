/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.DiracClockPacketD

/-!
# The clock on a packet in `d` dimensions is dilated, and its error is the window's width

**Category:** 3-Local. BACKLOG #296, eighth part (obligation UO-17, Task 8 of the plan
`specs/unified-records-spacetime-task-plans.md` §6).

`CV/DiracClockPacketD.lean` shows that the coherence between two mass levels of one packet
of the torus turns at the level splitting `E¹(k₀) − E⁰(k₀)` at the window's centre, within
`|t|` times the window's spread of splittings. This module says what that splitting is and
bounds the spread.

The lattice energy in `d` dimensions is the one-dimensional dispersion at the size
`|s| = sNorm (sinS J k)` of the lattice momentum, so the ring's statements about the clock
rate (`CV/DiracClockChain.lean`, `CV/DiracDevice.lean`) apply at that size.

* `latticeED_sub_eq_levelClockRate` — the splitting is `levelClockRate` at `|s|`;
* ★★ `levelClockRateD_mem` — `(μ₁ − μ₀) μ₀/E⁰ ≤ E¹ − E⁰ ≤ (μ₁ − μ₀) μ₁/E¹`;
* ★★★ `levelClockRateD_dilation` — the splitting over the rest splitting is within
  `(μ₁ − μ₀)/E⁰` of `μ₀/E⁰`;
* ★★ `sq_div_latticeED` — `(μ/E)² = 1 − |v|²/(2J)² − (Σ s_i⁴)/((2J)² E²)` with `v` the group
  velocity `groupVelD`: the Lorentz factor of the group velocity in units of the lattice
  speed `2J`, less a lattice term of fourth order in the momentum;
* ★★ `abs_levelClockRateD_sub_le` — the splitting at two momenta differs by at most
  `4J² (μ₁ − μ₀)/μ₀² · Σ_i |k_i − k'_i|`;
* ★★ `levelErrorD_le` — the window's spread of splittings is at most the total weight times
  `4J² (μ₁ − μ₀)/μ₀²` times the window's width in angle;
* ★★★ `levelCoherenceD_rate_width` — the coherence turns at the splitting at the centre
  within `|t|` times that bound.

## Honest scope

⚠️ **The dilation is against the lattice momentum.** `μ₀/E⁰` is the Lorentz factor of the
group velocity only up to the term `(Σ s_i⁴)/((2J)² E²)`, which is not bounded here in terms
of a lattice spacing; no continuum limit is taken.

⚠️ **The residue `(μ₁ − μ₀)/E⁰`** of the dilation is the finite level splitting, as on the
ring.

⚠️ **Flow time; no pointer reads the clock; `0 < μ₀ ≤ μ₁`.** The device is not normalised
here: the bound carries the total weight `Σ ‖w_m‖` as it stands.

References: `specs/BACKLOG.md` #296; `specs/unified-record-spacetime-plan.md` (UO-17,
UD-235, UD-238); `specs/unified-records-spacetime-task-plans.md` (§6);
`CV/DiracClockPacketD.lean` (`levelCoherenceD_rate`, `levelErrorD`);
`CV/DiracClockChain.lean` (`levelClockRate`, `clockRate_mem`, `abs_clockRate_div_sub_le`);
`CV/DiracDevice.lean` (`abs_levelClockRate_sub_le`); `CV/DiracAnisotropy.lean` (`groupVelD`,
`latticeED`, `sinS`); `specs/future-work.md`.
-/

@[expose] public section

open Complex Matrix

noncomputable section

namespace CSD.CV

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [DecidableEq S]
  {L : ℕ} [NeZero L]

/-! ### The splitting and its dilation -/

omit [DecidableEq ι] in
/-- The level splitting in `d` dimensions is the ring's clock rate at the size of the lattice
momentum. -/
theorem latticeED_sub_eq_levelClockRate (J μ₀ μ₁ : ℝ) (k : ι → ℝ) :
    latticeED J μ₁ k - latticeED J μ₀ k = levelClockRate μ₀ μ₁ (sNorm (sinS J k)) :=
  rfl

omit [DecidableEq ι] in
/-- ★★ **The moving clock's rate lies between its two levels' dilated rest rates.** -/
theorem levelClockRateD_mem {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ ≤ μ₁) (J : ℝ) (k : ι → ℝ) :
    (μ₁ - μ₀) * (μ₀ / latticeED J μ₀ k) ≤ latticeED J μ₁ k - latticeED J μ₀ k
      ∧ latticeED J μ₁ k - latticeED J μ₀ k ≤ (μ₁ - μ₀) * (μ₁ / latticeED J μ₁ k) :=
  clockRate_mem h0 h01 (sNorm (sinS J k))

omit [DecidableEq ι] in
/-- ★★★ **Time dilation of the clock in `d` dimensions, with its error**: the level splitting
over the rest splitting is within `(μ₁ − μ₀)/E⁰` of `μ₀/E⁰`. -/
theorem levelClockRateD_dilation {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ < μ₁) (J : ℝ)
    (k : ι → ℝ) :
    |(latticeED J μ₁ k - latticeED J μ₀ k) / (μ₁ - μ₀) - μ₀ / latticeED J μ₀ k|
      ≤ (μ₁ - μ₀) / latticeED J μ₀ k := by
  have hd : 0 < μ₁ - μ₀ := by linarith
  have hE0 : 0 < latticeED J μ₀ k := dispE_pos h0 _
  have hE1 : 0 < latticeED J μ₁ k := dispE_pos (h0.trans h01) _
  obtain ⟨hlo, hhi⟩ := levelClockRateD_mem h0 h01.le J k
  have hlo' : μ₀ / latticeED J μ₀ k ≤ (latticeED J μ₁ k - latticeED J μ₀ k) / (μ₁ - μ₀) := by
    rw [le_div_iff₀ hd]
    linarith
  have hhi' : (latticeED J μ₁ k - latticeED J μ₀ k) / (μ₁ - μ₀) ≤ μ₁ / latticeED J μ₁ k := by
    rw [div_le_iff₀ hd]
    linarith
  have hE01 : latticeED J μ₀ k ≤ latticeED J μ₁ k := by
    have := hlo
    have hnn : 0 ≤ (μ₁ - μ₀) * (μ₀ / latticeED J μ₀ k) :=
      mul_nonneg hd.le (div_nonneg h0.le hE0.le)
    linarith
  have hgap : μ₁ / latticeED J μ₁ k - μ₀ / latticeED J μ₀ k ≤ (μ₁ - μ₀) / latticeED J μ₀ k := by
    have h1 : μ₁ / latticeED J μ₁ k ≤ μ₁ / latticeED J μ₀ k :=
      div_le_div_of_nonneg_left (h0.trans h01).le hE0 hE01
    rw [sub_div]
    linarith
  rw [abs_of_nonneg (by linarith)]
  linarith

omit [DecidableEq ι] in
/-- The square of one component of the group velocity. -/
theorem groupVelD_sq_mul (J μ : ℝ) {k : ι → ℝ} (hE : 0 < latticeED J μ k) (i : ι) :
    groupVelD J μ k i ^ 2 * latticeED J μ k ^ 2
      = (2 * J) ^ 2 * sinS J k i ^ 2 - sinS J k i ^ 4 := by
  unfold groupVelD
  rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hE.ne'), mul_pow, mul_pow, Real.cos_sq']
  unfold sinS
  ring

omit [DecidableEq ι] in
/-- ★★ **The rest energy over the energy is the Lorentz factor of the group velocity, less a
lattice term**: `(μ/E)² = 1 − |v|²/(2J)² − (Σ s_i⁴)/((2J)² E²)`. -/
theorem sq_div_latticeED {J : ℝ} (hJ : J ≠ 0) (μ : ℝ) {k : ι → ℝ} (hE : 0 < latticeED J μ k) :
    (μ / latticeED J μ k) ^ 2
      = 1 - (∑ i, groupVelD J μ k i ^ 2) / (2 * J) ^ 2
        - (∑ i, sinS J k i ^ 4) / ((2 * J) ^ 2 * latticeED J μ k ^ 2) := by
  have hc : (2 * J) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero two_ne_zero hJ)
  have hE2 : latticeED J μ k ^ 2 ≠ 0 := pow_ne_zero 2 hE.ne'
  have hsum : (∑ i, groupVelD J μ k i ^ 2) * latticeED J μ k ^ 2
      = (2 * J) ^ 2 * (latticeED J μ k ^ 2 - μ ^ 2) - ∑ i, sinS J k i ^ 4 := by
    rw [Finset.sum_mul, Finset.sum_congr rfl fun i _ => groupVelD_sq_mul J μ hE i,
      Finset.sum_sub_distrib, ← Finset.mul_sum, latticeED_sq]
    congr 2
    rw [add_sub_cancel_left]
    rfl
  have hA : ∑ i, groupVelD J μ k i ^ 2
      = ((2 * J) ^ 2 * (latticeED J μ k ^ 2 - μ ^ 2) - ∑ i, sinS J k i ^ 4)
        / latticeED J μ k ^ 2 := by
    rw [eq_div_iff hE2]
    exact hsum
  rw [div_pow, hA]
  field_simp
  ring

/-! ### The spread of splittings over a window -/

omit [DecidableEq ι] in
/-- ★★ **The splitting moves slowly with the momentum**: at two sets of angles it differs by
at most `4J² (μ₁ − μ₀)/μ₀²` times the sum of the angles' differences. -/
theorem abs_levelClockRateD_sub_le {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ ≤ μ₁) (J : ℝ)
    (k k' : ι → ℝ) :
    |(latticeED J μ₁ k - latticeED J μ₀ k) - (latticeED J μ₁ k' - latticeED J μ₀ k')|
      ≤ 4 * J ^ 2 * (μ₁ - μ₀) / μ₀ ^ 2 * ∑ i, |k i - k' i| := by
  have hΔ : 0 ≤ μ₁ - μ₀ := by linarith
  have h := abs_levelClockRate_sub_le h0 h01 (sNorm (sinS J k)) (sNorm (sinS J k'))
  rw [latticeED_sub_eq_levelClockRate, latticeED_sub_eq_levelClockRate]
  refine h.trans ?_
  have hsq : |sNorm (sinS J k) ^ 2 - sNorm (sinS J k') ^ 2|
      ≤ 8 * J ^ 2 * ∑ i, |k i - k' i| := by
    rw [sNorm_sq, sNorm_sq, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    unfold sinS
    have h1 := Real.abs_sin_sub_sin_le (k i) (k' i)
    have h2 : |Real.sin (k i) + Real.sin (k' i)| ≤ 2 := by
      refine (abs_add_le _ _).trans ?_
      linarith [Real.abs_sin_le_one (k i), Real.abs_sin_le_one (k' i)]
    have e : (2 * J * Real.sin (k i)) ^ 2 - (2 * J * Real.sin (k' i)) ^ 2
        = 4 * J ^ 2 * ((Real.sin (k i) - Real.sin (k' i))
          * (Real.sin (k i) + Real.sin (k' i))) := by ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * J ^ 2), abs_mul]
    have h3 : |Real.sin (k i) - Real.sin (k' i)| * |Real.sin (k i) + Real.sin (k' i)|
        ≤ |k i - k' i| * 2 := mul_le_mul h1 h2 (abs_nonneg _) (abs_nonneg _)
    nlinarith [sq_nonneg J]
  have hμ : 0 < 2 * μ₀ ^ 2 := by positivity
  rw [div_le_iff₀ hμ]
  have hS : 0 ≤ ∑ i, |k i - k' i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have e2 : 4 * J ^ 2 * (μ₁ - μ₀) / μ₀ ^ 2 * (∑ i, |k i - k' i|) * (2 * μ₀ ^ 2)
      = 8 * J ^ 2 * (∑ i, |k i - k' i|) * (μ₁ - μ₀) := by
    field_simp
    ring
  rw [e2]
  exact mul_le_mul_of_nonneg_right hsq hΔ

variable (α : ι → Matrix S S ℂ) (β : Matrix S S ℂ)

omit [NeZero L] [DecidableEq ι] in
/-- ★★ **The spread of splittings is at most the window's width in angle**: if every momentum
of the window has angles within `w` (in the sum over axes) of the centre `k₀`, the coherence
error is at most the total weight times `4J² (μ₁ − μ₀)/μ₀² · w`. -/
theorem levelErrorD_le {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ ≤ μ₁) (J : ℝ) (e₀ : S → ℂ)
    {W : Finset (ι → ℤ)} (a₀ a₁ : (ι → ℤ) → ℂ) (k₀ : ι → ℝ) {w : ℝ}
    (hW : ∀ m ∈ W, ∑ i, |angleZD L m i - k₀ i| ≤ w) :
    levelErrorD (L := L) α β J μ₀ μ₁ e₀ W a₀ a₁ k₀
      ≤ (∑ m ∈ W, ‖levelWeightD (L := L) α β J μ₀ μ₁ e₀ a₀ a₁ m‖)
        * (4 * J ^ 2 * (μ₁ - μ₀) / μ₀ ^ 2 * w) := by
  have hc : 0 ≤ 4 * J ^ 2 * (μ₁ - μ₀) / μ₀ ^ 2 :=
    div_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
  unfold levelErrorD
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h := abs_levelClockRateD_sub_le h0 h01 J (angleZD L m) k₀
  have e : latticeED J μ₀ (angleZD L m) - latticeED J μ₁ (angleZD L m)
        - (latticeED J μ₀ k₀ - latticeED J μ₁ k₀)
      = -((latticeED J μ₁ (angleZD L m) - latticeED J μ₀ (angleZD L m))
        - (latticeED J μ₁ k₀ - latticeED J μ₀ k₀)) := by ring
  rw [e, abs_neg]
  exact h.trans (mul_le_mul_of_nonneg_left (hW m hm) hc)

/-- ★★★ **The clock on a packet, with its error from the window's width**: the coherence
between the two levels turns at the level splitting at the centre `k₀` within `|t|` times
the total weight times `4J² (μ₁ − μ₀)/μ₀² · w`. -/
theorem levelCoherenceD_rate_width {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ ≤ μ₁) (J : ℝ)
    (e₀ : S → ℂ) {W : Finset (ι → ℤ)} (hD : DistinctD L W) (a₀ a₁ : (ι → ℤ) → ℂ)
    (k₀ : ι → ℝ) {w : ℝ} (hW : ∀ m ∈ W, ∑ i, |angleZD L m i - k₀ i| ≤ w) (t : ℝ) :
    ‖levelCoherenceD (L := L) α β J μ₀ μ₁ e₀ W a₀ a₁ t
        - exp (I * (((latticeED J μ₀ k₀ - latticeED J μ₁ k₀ : ℝ) : ℂ) * t))
          * levelCoherenceD (L := L) α β J μ₀ μ₁ e₀ W a₀ a₁ 0‖
      ≤ |t| * ((∑ m ∈ W, ‖levelWeightD (L := L) α β J μ₀ μ₁ e₀ a₀ a₁ m‖)
        * (4 * J ^ 2 * (μ₁ - μ₀) / μ₀ ^ 2 * w)) :=
  (levelCoherenceD_rate α β J μ₀ μ₁ e₀ hD a₀ a₁ k₀ t).trans
    (mul_le_mul_of_nonneg_left (levelErrorD_le α β h0 h01 J e₀ a₀ a₁ k₀ hW) (abs_nonneg t))

end CSD.CV

end
