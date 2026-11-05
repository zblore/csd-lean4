/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import CsdLean4.RecordLayer.LorentzKinematics

/-!
# The spatial radar chart: trilateration by co-moving observers

**Category:** 7-SigmaLayer (the record layer). BACKLOG #293 (split of #289;
`specs/beyond-1p1-scoping.md`).

One observer's radar gives an event's time and its distance, `(e + r)/2` and `(r − e)/2`, but not
its direction. A group of co-moving observers in general position, a base observer at `o` and
others at `p i` whose displacements `p i − o` span space, fixes the position by trilateration. This
file proves that the chart is exact, that it is stable under reading errors with a geometry
constant, and that a moving group's chart is the Lorentz boost of the event
(`LorentzKinematics.lean`), the `d + 1` form of `radar_lorentz_exact`.

## Trilateration

* `RadarGeneralPosition` (the displacements `p i − o` span the space);
* `two_inner_sub_eq` (`2⟪y − x, p − o⟫` from the four squared distances), ★★★ `trilateration_unique`
  (**the distances to the observers determine the position**);
* ★★ `exists_trilateration_const` (**the geometry constant**: in finite dimension, `‖z‖ ≤ K Σ_i
  |⟪z, p i − o⟫|` for some `K > 0`), `abs_sq_sub_sq_le`;
* ★★★ `trilateration_stable` (**a point whose distances are within `δ₀`, `δ i` of the event's is
  within `K Σ_i (δ i (2ρ_i + δ i) + δ₀ (2ρ₀ + δ₀))/2` of it**, `ρ` the true distances: linear in
  the errors to leading order); ★★★ `trilateration_scaling` (**for every `ε` there is a reading
  resolution below which every consistent point is within `ε`**, for events within `R`).

## Radar by a moving group

* `null_future_time_eq` (a future null displacement has time equal to its length),
  ★★ `null_future_boostD` (**a boost keeps a displacement future null**), `boostD_zero`;
* ★★★ `radar_boostD` (**an observer at rest at `q` in the frame boosted by `(n, v)`, emitting at
  its clock reading `τe` and receiving the return at `τr`, reads time `(τe + τr)/2` equal to the
  boosted event's time and distance `(τr − τe)/2` equal to its distance from `q` in the boosted
  frame**);
* ★★★ `trilateration_chart_boostD` (**the `d + 1` `radar_lorentz_exact`: a moving group's radar
  chart of an event is the Lorentz boost of the event** — every observer's radar time is the boosted
  time, and the only position with the read distances is the boosted position; at `v = 0`, the
  resting group's chart is the event).

## Honest scope

⚠️ **Kinematic, as in 1+1.** Light moves at `1` along null lines and each observer's clock reads its
rest-frame time (its proper time, synchronised in its rest frame by Einstein's convention); the
chain realises both within its errors only after #294–#298.

⚠️ **The estimator is any consistent point.** Stability is stated for any point whose distances to
the observers are within the given errors of the event's; computing it (a linear solve) is not
written out. The constant `K` comes from finite dimension (`LinearMap.injective_iff_antilipschitz`),
not from an explicit formula in the observers' positions.

References: `specs/BACKLOG.md` #293, #289, #292; `specs/beyond-1p1-scoping.md` §2.8;
`RecordLayer/DiracTwoCharts.lean` (`radar_lorentz_exact`, `radar_lorentz_scaling`);
`RecordLayer/LorentzKinematics.lean`; B. Coll, J. M. Pozo, Class. Quantum Grav. 23 (2006) 7395;
`specs/future-work.md`.
-/

@[expose] public section

open RealInnerProductSpace

noncomputable section

namespace CSD.RecordLayer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*} [Fintype ι]

/-! ### Trilateration -/

/-- The observers at `o` and `p i` are in general position: the displacements `p i − o` span. -/
def RadarGeneralPosition (o : E) (p : ι → E) : Prop :=
  Submodule.span ℝ (Set.range fun i => p i - o) = ⊤

/-- The inner product with a displacement of the observers, from four squared distances. -/
theorem two_inner_sub_eq (x y o q : E) :
    2 * ⟪y - x, q - o⟫ = (‖y - o‖ ^ 2 - ‖x - o‖ ^ 2) - (‖y - q‖ ^ 2 - ‖x - q‖ ^ 2) := by
  simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right]
  ring

omit [Fintype ι] in
/-- A vector orthogonal to every displacement of observers in general position is zero. -/
theorem eq_zero_of_inner_eq_zero {o : E} {p : ι → E} (hG : RadarGeneralPosition o p) {z : E}
    (hz : ∀ i, ⟪z, p i - o⟫ = 0) : z = 0 := by
  have hspan : Submodule.span ℝ (Set.range fun i => p i - o) ≤ (ℝ ∙ z)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.2 (hz i)
  have hmem : z ∈ (ℝ ∙ z)ᗮ := by
    rw [hG] at hspan
    exact hspan Submodule.mem_top
  exact inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 hmem)

omit [Fintype ι] in
/-- ★★★ **The distances to observers in general position determine the position.** -/
theorem trilateration_unique {o : E} {p : ι → E} (hG : RadarGeneralPosition o p) {x y : E}
    (h0 : ‖y - o‖ = ‖x - o‖) (h : ∀ i, ‖y - p i‖ = ‖x - p i‖) : y = x := by
  refine sub_eq_zero.1 (eq_zero_of_inner_eq_zero hG fun i => ?_)
  have := two_inner_sub_eq x y o (p i)
  rw [h0, h i] at this
  linarith

/-- ★★ **The geometry constant.** In finite dimension, observers in general position bound every
vector by its inner products with their displacements. -/
theorem exists_trilateration_const [FiniteDimensional ℝ E] {o : E} {p : ι → E}
    (hG : RadarGeneralPosition o p) :
    ∃ K : ℝ, 0 < K ∧ ∀ z : E, ‖z‖ ≤ K * ∑ i, |⟪z, p i - o⟫| := by
  set f : E →ₗ[ℝ] (ι → ℝ) := LinearMap.pi fun i => (innerSL ℝ (p i - o)).toLinearMap with hf
  have hfa : ∀ z i, f z i = ⟪z, p i - o⟫ := fun z i => by
    simp only [hf, LinearMap.pi_apply, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
    exact real_inner_comm _ _
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro z hz0
    exact eq_zero_of_inner_eq_zero hG fun i => by rw [← hfa, hz0, Pi.zero_apply]
  obtain ⟨K, hK, hA⟩ := (LinearMap.injective_iff_antilipschitz f).1 hinj
  refine ⟨K, by exact_mod_cast hK, fun z => ?_⟩
  have h1 := hA.le_mul_norm (map_zero f) z
  have h2 : ‖f z‖ ≤ ∑ i, |⟪z, p i - o⟫| := by
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs, hfa]
    exact Finset.single_le_sum (f := fun i => |⟪z, p i - o⟫|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)
  exact h1.trans (mul_le_mul_of_nonneg_left h2 K.coe_nonneg)

/-- Squares of close nonnegative numbers are close. -/
theorem abs_sq_sub_sq_le {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : |a - b| ≤ δ) :
    |a ^ 2 - b ^ 2| ≤ δ * (2 * b + δ) := by
  have hab : a ≤ b + δ := by linarith [le_abs_self (a - b)]
  rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring, abs_mul,
    abs_of_nonneg (by linarith : 0 ≤ a + b)]
  exact mul_le_mul h (by linarith) (by linarith) ((abs_nonneg _).trans h)

/-- ★★★ **Trilateration is stable.** A point whose distances to the observers are within `δ₀` and
`δ i` of the event's lies within `K Σ_i (δ i (2ρ_i + δ i) + δ₀ (2ρ₀ + δ₀))/2` of the event, where
`ρ` are the event's distances and `K` the geometry constant. -/
theorem trilateration_stable {o : E} {p : ι → E} {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ z : E, ‖z‖ ≤ K * ∑ i, |⟪z, p i - o⟫|) {x y : E} {δ₀ : ℝ} {δ : ι → ℝ}
    (h0 : |‖y - o‖ - ‖x - o‖| ≤ δ₀) (h : ∀ i, |‖y - p i‖ - ‖x - p i‖| ≤ δ i) :
    ‖y - x‖ ≤ K * ∑ i, (δ i * (2 * ‖x - p i‖ + δ i) + δ₀ * (2 * ‖x - o‖ + δ₀)) / 2 := by
  refine (hK (y - x)).trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) hK0)
  have he := two_inner_sub_eq x y o (p i)
  have h1 := abs_sq_sub_sq_le (norm_nonneg _) (norm_nonneg _) h0
  have h2 := abs_sq_sub_sq_le (norm_nonneg _) (norm_nonneg _) (h i)
  have h3 : |2 * ⟪y - x, p i - o⟫| ≤ δ i * (2 * ‖x - p i‖ + δ i) + δ₀ * (2 * ‖x - o‖ + δ₀) := by
    rw [he]
    exact (abs_sub _ _).trans (by linarith)
  rw [abs_mul, abs_two] at h3
  linarith

/-- ★★★ **The scaling law for the spatial chart.** For observers in general position, every `ε > 0`
and every range `R`, there is a resolution `δ > 0` such that, for an event within `R` of every
observer, every point whose distances are within `δ` of the event's lies within `ε` of it. -/
theorem trilateration_scaling [FiniteDimensional ℝ E] {o : E} {p : ι → E}
    (hG : RadarGeneralPosition o p) {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) :
    ∃ δ > 0, ∀ x y : E, ‖x - o‖ ≤ R → (∀ i, ‖x - p i‖ ≤ R) →
      |‖y - o‖ - ‖x - o‖| ≤ δ → (∀ i, |‖y - p i‖ - ‖x - p i‖| ≤ δ) → ‖y - x‖ ≤ ε := by
  obtain ⟨K, hK0, hK⟩ := exists_trilateration_const hG
  set C : ℝ := (K * Fintype.card ι + 1) * (2 * R + 1) with hC
  have hCpos : 0 < C := by positivity
  refine ⟨min 1 (ε / C), lt_min one_pos (div_pos hε hCpos), fun x y hxo hxp h0 h => ?_⟩
  set δ := min 1 (ε / C)
  have hδ0 : 0 ≤ δ := le_min zero_le_one (div_pos hε hCpos).le
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδC : δ * C ≤ ε := by
    have := min_le_right 1 (ε / C)
    calc δ * C ≤ ε / C * C := mul_le_mul_of_nonneg_right this hCpos.le
      _ = ε := div_mul_cancel₀ ε hCpos.ne'
  refine (trilateration_stable hK0.le hK h0 h).trans ?_
  have hterm : ∀ i, (δ * (2 * ‖x - p i‖ + δ) + δ * (2 * ‖x - o‖ + δ)) / 2 ≤ δ * (2 * R + 1) :=
    fun i => by nlinarith [hxp i]
  calc K * ∑ i, (δ * (2 * ‖x - p i‖ + δ) + δ * (2 * ‖x - o‖ + δ)) / 2
      ≤ K * ∑ _i : ι, δ * (2 * R + 1) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) hK0.le
    _ = K * Fintype.card ι * (δ * (2 * R + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
    _ ≤ δ * C := by
        rw [hC]
        nlinarith [mul_nonneg hδ0 (by linarith : (0 : ℝ) ≤ 2 * R + 1)]
    _ ≤ ε := hδC

/-! ### Radar by a moving group -/

/-- A future null displacement has time equal to its length. -/
theorem null_future_time_eq {Δ : ℝ × E} (h : minkowskiSqD Δ = 0) (h0 : 0 ≤ Δ.1) :
    Δ.1 = ‖Δ.2‖ := by
  rw [minkowskiSqD_eq, sub_eq_zero] at h
  exact (pow_left_inj₀ h0 (norm_nonneg _) two_ne_zero).1 h

/-- ★★ **A boost keeps a displacement future null.** -/
theorem null_future_boostD {n : E} (hn : ‖n‖ = 1) {v : ℝ} (hv : |v| < 1) {Δ : ℝ × E}
    (h : minkowskiSqD Δ = 0) (h0 : 0 ≤ Δ.1) :
    minkowskiSqD (boostD n v Δ) = 0 ∧ 0 ≤ (boostD n v Δ).1 := by
  refine ⟨(minkowskiSqD_boostD hn hv Δ).trans h, ?_⟩
  have ht := null_future_time_eq h h0
  have hle : v * ⟪n, Δ.2⟫ ≤ Δ.1 := by
    calc v * ⟪n, Δ.2⟫ ≤ |v * ⟪n, Δ.2⟫| := le_abs_self _
      _ = |v| * |⟪n, Δ.2⟫| := abs_mul _ _
      _ ≤ 1 * (‖n‖ * ‖Δ.2‖) :=
          mul_le_mul hv.le (abs_real_inner_le_norm _ _) (abs_nonneg _) zero_le_one
      _ = Δ.1 := by rw [hn, ht, one_mul, one_mul]
  have hb : (boostD n v Δ).1 = boostGamma v * (Δ.1 - v * ⟪n, Δ.2⟫) := rfl
  rw [hb]
  exact mul_nonneg (boostGamma_pos hv).le (by linarith)

theorem boostD_zero (n : E) (e : ℝ × E) : boostD n 0 e = e := by
  simp [boostD, boostGamma]

/-- ★★★ **Radar by an observer of a moving group.** The observer rests at `q` in the frame boosted
by `(n, v)`: its emission `a` and the return `b` are on its worldline at its readings `τe`, `τr`;
the messenger runs future null from `a` to the event `e` and from `e` back to `b`. Then its radar
time `(τe + τr)/2` is the boosted event's time and its radar distance `(τr − τe)/2` is the boosted
event's distance from `q`. -/
theorem radar_boostD {n : E} (hn : ‖n‖ = 1) {v : ℝ} (hv : |v| < 1) {q : E} {τe τr : ℝ}
    {a b e : ℝ × E} (ha : boostD n v a = (τe, q)) (hb : boostD n v b = (τr, q))
    (hae : minkowskiSqD (e - a) = 0) (hae0 : 0 ≤ (e - a).1)
    (heb : minkowskiSqD (b - e) = 0) (heb0 : 0 ≤ (b - e).1) :
    (τe + τr) / 2 = (boostD n v e).1 ∧ (τr - τe) / 2 = ‖(boostD n v e).2 - q‖ := by
  obtain ⟨h1, h1'⟩ := null_future_boostD hn hv hae hae0
  obtain ⟨h2, h2'⟩ := null_future_boostD hn hv heb heb0
  have t1 := null_future_time_eq h1 h1'
  have t2 := null_future_time_eq h2 h2'
  rw [boostD_sub, ha] at t1
  rw [boostD_sub, hb] at t2
  simp only [Prod.fst_sub, Prod.snd_sub] at t1 t2
  rw [norm_sub_rev] at t2
  constructor <;> linarith

omit [Fintype ι] in
/-- ★★★ **The `d + 1` `radar_lorentz_exact`: a moving group's radar chart is the Lorentz boost.**
For a group at rest in the frame boosted by `(n, v)`, a base observer at `o` and others at `p i` in
general position, each running radar on the event `e` (emission and return on its worldline at its
readings, the messenger future null both ways): every observer's radar time is the boosted event's
time, and the only position at the read radar distances from the observers is the boosted event's
position. At `v = 0` (`boostD_zero`) the resting group's chart is the event itself. -/
theorem trilateration_chart_boostD {n : E} (hn : ‖n‖ = 1) {v : ℝ} (hv : |v| < 1) {o : E}
    {p : ι → E} (hG : RadarGeneralPosition o p) {e : ℝ × E}
    {τe₀ τr₀ : ℝ} {a₀ b₀ : ℝ × E} (ha₀ : boostD n v a₀ = (τe₀, o)) (hb₀ : boostD n v b₀ = (τr₀, o))
    (hae₀ : minkowskiSqD (e - a₀) = 0) (hae₀' : 0 ≤ (e - a₀).1)
    (heb₀ : minkowskiSqD (b₀ - e) = 0) (heb₀' : 0 ≤ (b₀ - e).1)
    {τe τr : ι → ℝ} {a b : ι → ℝ × E} (ha : ∀ i, boostD n v (a i) = (τe i, p i))
    (hb : ∀ i, boostD n v (b i) = (τr i, p i))
    (hae : ∀ i, minkowskiSqD (e - a i) = 0) (hae' : ∀ i, 0 ≤ (e - a i).1)
    (heb : ∀ i, minkowskiSqD (b i - e) = 0) (heb' : ∀ i, 0 ≤ (b i - e).1) :
    (τe₀ + τr₀) / 2 = (boostD n v e).1 ∧ (∀ i, (τe i + τr i) / 2 = (boostD n v e).1) ∧
      ∀ y : E, ‖y - o‖ = (τr₀ - τe₀) / 2 → (∀ i, ‖y - p i‖ = (τr i - τe i) / 2) →
        y = (boostD n v e).2 := by
  have r₀ := radar_boostD hn hv ha₀ hb₀ hae₀ hae₀' heb₀ heb₀'
  have r := fun i => radar_boostD hn hv (ha i) (hb i) (hae i) (hae' i) (heb i) (heb' i)
  refine ⟨r₀.1, fun i => (r i).1, fun y hy0 hy => ?_⟩
  exact trilateration_unique hG (hy0.trans r₀.2) fun i => (hy i).trans (r i).2

end CSD.RecordLayer
