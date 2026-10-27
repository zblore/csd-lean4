/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.ChainExchange
public import CsdLean4.CV.TwoCones
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The two cones compared on the chain

**Category:** 3-Local (CV; continuous variables — the chain witness against the Lieb–Robinson
bound).
BACKLOG #205, first brick, out of #39.

The corpus has two cones on the same chain and had never compared them:

* the **hop-time cone** of [`ChainExchange.lean`](ChainExchange.lean): the scheduled chain moves the
  excitation exactly one site per hop time `τ_hop = πħ/(2J)` (`chain_transfer`), so its slope is
  `hopVelocity J ħ = 1/τ_hop` sites per unit time;
* the **Lieb–Robinson cone** of [`TwoCones.lean`](TwoCones.lean): outside slope
  `lrVelocity F = 4e‖Σ_e h_e‖` the error of `record_lightcone` is at most `2^{-d}`
  (`lr_bound_le_half_pow`).

This file computes the second on the chain and compares it with the first.

## What is proved

* ★ `norm_swapHop` — the hop on a genuine edge has L2 operator norm exactly `1` (above by the
  C*-identity and `swapHop_mul_swapHop`, below by one entry); hence ★ `norm_chainGen`,
  `‖chainGen J ħ k k'‖ = |J/ħ|`, and ★★ `lrVelocity_edgeFlow`, a stage's velocity is `4e|J/ħ|`;
* ★★★ `lrVelocity_mul_hopTime` and ★★★ `lrVelocity_eq_coneRatio_mul` — **per stage the two cones are
  proportional with a universal ratio**: `v_LR · τ_hop = 2πe`, so `v_LR = 2πe · v_hop` whatever `J`
  and `ħ`; ★ `seventeen_lt_coneRatio`, ★ `coneRatio_lt_eighteen` pin `17 < 2πe < 18`;
* ★★ `arrival_eq_coneRatio_mul`, ★★ `arrival_mem_lrCone`, ★★ `lrTime_lt_arrival` — the arrival at
  `d` sites at `d · τ_hop` is inside the Lieb–Robinson cone, which opens at `d / v_LR`, `2πe` times
  earlier: the bound is respected, and it is loose by that factor;
* ★★ `lr_bound_one_stage` — over one stage of length `τ_hop` the bound suppresses influence only
  beyond `18` sites, while the stage moves the excitation exactly one site;
* `pathFlow` — the same couplings as **one** time-independent flow on every edge of the path graph;
  ★ `card_moved_mul_two` (an edge moves exactly half the configurations, by flipping one end),
  ★★ `half_le_norm_pathHop` (the all-ones test vector, through `norm_sum_entries_le`) and
  `norm_pathHop_le` give `n/2 ≤ ‖Σ_e X_e‖ ≤ n`, hence ★★★
  `pathFlow_lrVelocity_mul_hopTime_bounds`: **packaged as one flow, the Lieb–Robinson slope is
  between `n/2` and `n` times a stage's**;
* ★★★ `cone_comparison` — the capstone: the per-stage ratio on every active stage of
  `chainSchedule`, the numeric pin, arrival inside the cone and after it opens, the one-stage
  suppression threshold, and the whole-chain sandwich.

## The findings

1. **On the schedule the two cones are one cone up to a universal constant.** Both slopes scale as
   `J/ħ`, so no change of coupling or of units separates them: the hop-time cone is the sharp one
   (it is the transport itself) and the Lieb–Robinson cone is it widened by `2πe`. The corrected
   radar readings of [`ThreeStation.lean`](ThreeStation.lean) and
   [`WalkSchedule.lean`](WalkSchedule.lean) count stages of length `τ_hop`, so they read the
   hop-time cone, not the bound.
2. **The corpus's Lieb–Robinson cone does not survive a change of coarse description.**
   `lrVelocity` is built from the norm of the *whole* generator, so describing the same couplings as
   one flow on `n` edges instead of a schedule of single edges multiplies its slope by between `n/2`
   and `n`. That is a property of the bound as the corpus states it (`norm_commutator_velocity_le`),
   not of the chain: the velocity built from the local terms and the graph's degree,
   `localLRVelocity` in [`LocalLiebRobinson.lean`](LocalLiebRobinson.lean), does not grow
   with `n`.

## Honest scope

⚠️ **This compares a bound with a transport; it does not identify them.** `lrVelocity`'s `4e` is the
Stirling constant of `TwoCones.lean` at suppression `2^{-d}`, so `2πe` is the ratio for *that*
bound, not a sharp constant. Nothing here is a universal `c`, a continuum limit or a Lorentz statement.

⚠️ **The whole-chain flow's own transport is not computed here.** `pathFlow` is used only to price
the bound under a change of description; how fast `pathFlow` actually moves an excitation is not a
statement of this file.

References: [`records-to-spacetime-scoping.md`](../../specs/records-to-spacetime-scoping.md);
[`future-work.md`](../../specs/future-work.md); `CV/ChainExchange.lean` (`chain_transfer`,
`chainSchedule`, `pathGraph`), `CV/TwoCones.lean` (`lrVelocity`, `lr_bound_le_half_pow`),
`CV/LiebRobinson.lean` (`norm_commutator_velocity_le`), `CV/SignalExchange.lean` (`hopTime`);
`specs/BACKLOG.md` #205, #39, #98, #190, #203, #213.
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace CSD.CV

variable {L : ℕ}

/-! ### The norm of one hop -/

/-- The projector on the configurations an edge moves has norm at most one. -/
theorem norm_swapProj_le (k k' : Fin L) : ‖swapProj k k'‖ ≤ 1 := by
  rw [swapProj, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun c => ?_
  split_ifs <;> simp

/-- The hop has norm at most one: `‖X‖² = ‖XᴴX‖ = ‖P‖ ≤ 1` by the C*-identity. -/
theorem norm_swapHop_le (k k' : Fin L) : ‖swapHop k k'‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self (swapHop k k')
  rw [swapHop_conjTranspose, swapHop_mul_swapHop] at h
  have h1 := norm_swapProj_le k k'
  nlinarith [norm_nonneg (swapHop k k')]

/-- On a genuine edge the hop has norm at least one: its entry from `e_k` to `e_{k'}` is `1`. -/
theorem one_le_norm_swapHop {k k' : Fin L} (h : k ≠ k') : 1 ≤ ‖swapHop k k'‖ := by
  have hc : excAt k k ≠ excAt k k' := by
    rw [excAt_apply_self, excAt_apply_of_ne (Ne.symm h)]
    decide
  have := norm_entry_le_l2_opNorm (swapHop k k') (excAt k) (excAt k')
  rwa [swapHop_apply, ite_eq_left ⟨(swapSites_excAt k k').symm, hc⟩, norm_one] at this

/-- ★ **The hop on a genuine edge has norm exactly one.** -/
theorem norm_swapHop {k k' : Fin L} (h : k ≠ k') : ‖swapHop k k'‖ = 1 :=
  le_antisymm (norm_swapHop_le k k') (one_le_norm_swapHop h)

/-- ★ **The generator of one stage has norm `|J/ħ|`.** -/
theorem norm_chainGen (J ħ : ℝ) {k k' : Fin L} (h : k ≠ k') :
    ‖chainGen J ħ k k'‖ = |J / ħ| := by
  rw [chainGen, norm_smul, norm_swapHop h, mul_one, norm_neg, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]

/-! ### The Lieb–Robinson velocity of one stage, and the universal ratio -/

/-- ★★ **The Lieb–Robinson velocity of one stage of the chain is `4e|J/ħ|`.** -/
theorem lrVelocity_edgeFlow (J ħ : ℝ) {k k' : Fin L} (h : k ≠ k') :
    lrVelocity (edgeFlow J ħ k k') = 4 * Real.exp 1 * |J / ħ| := by
  simp only [lrVelocity, edgeFlow, Finset.sum_singleton]
  rw [norm_chainGen J ħ h]

/-- **The hop-time cone's slope**: one hop per hop time, `1/τ_hop = 2J/(πħ)`. -/
noncomputable def hopVelocity (J ħ : ℝ) : ℝ := (hopTime J ħ)⁻¹

/-- **The cone ratio** `2πe`: the Lieb–Robinson slope of a stage over its hop-time slope. -/
noncomputable def coneRatio : ℝ := 2 * Real.pi * Real.exp 1

theorem coneRatio_pos : 0 < coneRatio := by
  unfold coneRatio
  positivity

/-- ★★★ **The Lieb–Robinson velocity times the hop time is `2πe`**, whatever `J` and `ħ`. -/
theorem lrVelocity_mul_hopTime {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {k k' : Fin L} (h : k ≠ k') :
    lrVelocity (edgeFlow J ħ k k') * hopTime J ħ = coneRatio := by
  rw [lrVelocity_edgeFlow J ħ h, abs_of_pos (div_pos hJ hħ), hopTime, coneRatio]
  field_simp
  ring

/-- ★★★ **The two cones of a stage are proportional**: `v_LR = 2πe · v_hop`. -/
theorem lrVelocity_eq_coneRatio_mul {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {k k' : Fin L}
    (h : k ≠ k') : lrVelocity (edgeFlow J ħ k k') = coneRatio * hopVelocity J ħ := by
  rw [hopVelocity, ← lrVelocity_mul_hopTime hJ hħ h, mul_assoc,
    mul_inv_cancel₀ (hopTime_pos hJ hħ).ne', mul_one]

/-- ★ **`17 < 2πe`.** -/
theorem seventeen_lt_coneRatio : 17 < coneRatio := by
  have h1 := Real.pi_gt_d2
  have h2 := Real.exp_one_gt_d9
  have h3 : (3.14 : ℝ) * 2.7182818283 < Real.pi * Real.exp 1 :=
    mul_lt_mul'' h1 h2 (by norm_num) (by norm_num)
  unfold coneRatio
  nlinarith

/-- ★ **`2πe < 18`.** -/
theorem coneRatio_lt_eighteen : coneRatio < 18 := by
  have h1 := Real.pi_lt_d2
  have h2 := Real.exp_one_lt_d9
  have h3 : Real.pi * Real.exp 1 < (3.15 : ℝ) * 2.7182818286 :=
    mul_lt_mul'' h1 h2 Real.pi_pos.le (Real.exp_pos 1).le
  unfold coneRatio
  nlinarith

/-! ### Arrival against the Lieb–Robinson cone -/

/-- ★★ **The hop arrival time is `2πe` times the Lieb–Robinson cone's time**: at `d` hops the
excitation arrives at `d · τ_hop`, and the Lieb–Robinson cone of a stage reaches `d` hops at
`d / v_LR`. -/
theorem arrival_eq_coneRatio_mul {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {k k' : Fin L}
    (h : k ≠ k') (d : ℝ) :
    d * hopTime J ħ = coneRatio * (d / lrVelocity (edgeFlow J ħ k k')) := by
  have hv : lrVelocity (edgeFlow J ħ k k') ≠ 0 := by
    rw [lrVelocity_eq_coneRatio_mul hJ hħ h, hopVelocity]
    exact mul_ne_zero coneRatio_pos.ne' (inv_ne_zero (hopTime_pos hJ hħ).ne')
  rw [← lrVelocity_mul_hopTime hJ hħ h]
  field_simp

/-- ★★ **The arrival is inside the Lieb–Robinson cone**: `d ≤ v_LR · d τ_hop` — the actual transport
never contradicts the bound, as it must not. -/
theorem arrival_mem_lrCone {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {k k' : Fin L} (h : k ≠ k')
    {d : ℝ} (hd : 0 ≤ d) : d ≤ lrVelocity (edgeFlow J ħ k k') * (d * hopTime J ħ) := by
  rw [mul_comm d, ← mul_assoc, lrVelocity_mul_hopTime hJ hħ h]
  nlinarith [seventeen_lt_coneRatio]

/-- ★★ **The Lieb–Robinson cone of a stage opens strictly earlier than the arrival**: for `d > 0`
hops, `d / v_LR < d · τ_hop`. -/
theorem lrTime_lt_arrival {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {k k' : Fin L} (h : k ≠ k')
    {d : ℝ} (hd : 0 < d) : d / lrVelocity (edgeFlow J ħ k k') < d * hopTime J ħ := by
  rw [arrival_eq_coneRatio_mul hJ hħ h d]
  have hpos : 0 < d / lrVelocity (edgeFlow J ħ k k') := by
    rw [lrVelocity_eq_coneRatio_mul hJ hħ h, hopVelocity]
    exact div_pos hd (mul_pos coneRatio_pos (inv_pos.2 (hopTime_pos hJ hħ)))
  nlinarith [seventeen_lt_coneRatio]

/-- ★★ **Over one stage the Lieb–Robinson bound suppresses only beyond `18` hops**: at
`t = τ_hop` its error at `d ≥ 18` hops is at most `2^{-d}`, while the stage itself moves the
excitation exactly one hop. -/
theorem lr_bound_one_stage {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {k k' : Fin L} (h : k ≠ k')
    {d : ℕ} (hd : 18 ≤ d) :
    (2 * ‖∑ e ∈ (edgeFlow J ħ k k').edges, (edgeFlow J ħ k k').piece e‖ * hopTime J ħ) ^ d
        / (d.factorial : ℝ) ≤ (1 / 2 : ℝ) ^ d := by
  refine lr_bound_le_half_pow (norm_nonneg _) (hopTime_pos hJ hħ).le (by omega) ?_
  have h1 := lrVelocity_mul_hopTime hJ hħ h
  have h2 := coneRatio_lt_eighteen
  have h3 : (18 : ℝ) ≤ d := by exact_mod_cast hd
  rw [lrVelocity] at h1
  linarith

/-! ### The same couplings as one flow on every edge -/

/-- **The whole chain at once**: every edge of the path graph carries its hop simultaneously, a
time-independent field-structured flow with the same couplings as the schedule. -/
noncomputable def pathFlow (n : ℕ) (J ħ : ℝ) : FieldStructuredFlow (n + 1) 2 where
  edges := pathGraph n
  piece := fun e => chainGen J ħ e.1 e.2
  piece_supported := fun e _ => SupportedOn.smul _ (swapHop_supportedOn e.1 e.2)
  gen_skew := by
    rw [Matrix.conjTranspose_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun e _ => chainGen_skew J ħ e.1 e.2

theorem pathFlow_edges (n : ℕ) (J ħ : ℝ) : (pathFlow n J ħ).edges = pathGraph n := rfl

theorem card_pathGraph (n : ℕ) : (pathGraph n).card = n := by
  rw [pathGraph, Finset.card_image_of_injective _ fun a b hab => Fin.castSucc_injective _
    (Prod.ext_iff.1 hab).1, Finset.card_univ, Fintype.card_fin]

theorem fst_ne_snd_of_mem_pathGraph {n : ℕ} {e : Fin (n + 1) × Fin (n + 1)}
    (he : e ∈ pathGraph n) : e.1 ≠ e.2 := by
  obtain ⟨k, rfl⟩ := mem_pathGraph.1 he
  exact (Fin.castSucc_lt_succ (i := k)).ne

/-- The total sum of the entries of a square matrix is at most its norm times the dimension — the
all-ones test vector. -/
theorem norm_sum_entries_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    ‖∑ c, ∑ d, A c d‖ ≤ ‖A‖ * Fintype.card ι := by
  set x : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm (fun _ => 1) with hxdef
  have hx : ‖x‖ ^ 2 = Fintype.card ι := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [hxdef]
  have h1 := l2_opNorm_mulVec A x
  have h2 := norm_inner_le_norm (𝕜 := ℂ) x ((EuclideanSpace.equiv ι ℂ).symm (A *ᵥ x))
  have hin : inner ℂ x ((EuclideanSpace.equiv ι ℂ).symm (A *ᵥ x)) = ∑ c, ∑ d, A c d := by
    simp [hxdef, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mulVec]
  rw [hin] at h2
  calc ‖∑ c, ∑ d, A c d‖ ≤ ‖x‖ * (‖A‖ * ‖x‖) :=
        h2.trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
    _ = ‖A‖ * ‖x‖ ^ 2 := by ring
    _ = ‖A‖ * Fintype.card ι := by rw [hx]

/-! ### Counting the configurations an edge moves -/

/-- The sum of the hop's entries is the number of configurations the edge moves. -/
theorem sum_entries_swapHop (k k' : Fin L) :
    ∑ c, ∑ d, swapHop k k' c d
      = ((Finset.univ.filter fun c : ChainConfig L => c k ≠ c k').card : ℂ) := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  simp_rw [swapHop_apply]
  by_cases hc : c k ≠ c k'
  · simp [hc]
  · simp [hc]

/-- **Flip the occupation at site `k`.** -/
def flipAt (k : Fin L) (c : ChainConfig L) : ChainConfig L := Function.update c k (c k + 1)

theorem flipAt_flipAt (k : Fin L) (c : ChainConfig L) : flipAt k (flipAt k c) = c := by
  have h2 : ∀ x : Fin 2, x + 1 + 1 = x := by decide
  funext j
  by_cases hj : j = k
  · subst hj
    simp [flipAt, h2]
  · simp [flipAt, Function.update_of_ne hj]

theorem flipAt_moved_iff {k k' : Fin L} (h : k ≠ k') (c : ChainConfig L) :
    flipAt k c k ≠ flipAt k c k' ↔ ¬ (c k ≠ c k') := by
  have h2 : ∀ x y : Fin 2, x + 1 ≠ y ↔ ¬ (x ≠ y) := by decide
  rw [flipAt, Function.update_self, Function.update_of_ne (Ne.symm h)]
  exact h2 _ _

/-- ★ **An edge moves exactly half the configurations**: flipping one end is a bijection between
the moved and the unmoved ones. -/
theorem card_moved_mul_two {k k' : Fin L} (h : k ≠ k') :
    (Finset.univ.filter fun c : ChainConfig L => c k ≠ c k').card * 2 = 2 ^ L := by
  have hbij : (Finset.univ.filter fun c : ChainConfig L => c k ≠ c k').card
      = (Finset.univ.filter fun c : ChainConfig L => ¬ (c k ≠ c k')).card := by
    refine Finset.card_nbij' (flipAt k) (flipAt k) ?_ ?_ ?_ ?_
    · intro c hc
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hc ⊢
      exact fun h' => ((flipAt_moved_iff h c).1 h') hc
    · intro c hc
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hc ⊢
      exact (flipAt_moved_iff h c).2 hc
    · intro c _
      exact flipAt_flipAt k c
    · intro c _
      exact flipAt_flipAt k c
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (ChainConfig L))) (fun c : ChainConfig L => c k ≠ c k')
  rw [← hbij, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at hsplit
  omega

/-! ### The whole chain at once: the Lieb–Robinson velocity grows with its length -/

/-- The assembled hop of the whole chain. -/
noncomputable def pathHop (n : ℕ) : Matrix (ChainConfig (n + 1)) (ChainConfig (n + 1)) ℂ :=
  ∑ e ∈ pathGraph n, swapHop e.1 e.2

theorem sum_pathFlow_piece (n : ℕ) (J ħ : ℝ) :
    ∑ e ∈ (pathFlow n J ħ).edges, (pathFlow n J ħ).piece e
      = (-(Complex.I * ((J / ħ : ℝ) : ℂ))) • pathHop n := by
  simp only [pathFlow, pathHop, chainGen, Finset.smul_sum]

/-- ★★ **The Lieb–Robinson velocity of the whole chain is `4e|J/ħ| · ‖Σ X_e‖`.** -/
theorem lrVelocity_pathFlow (n : ℕ) (J ħ : ℝ) :
    lrVelocity (pathFlow n J ħ) = 4 * Real.exp 1 * |J / ħ| * ‖pathHop n‖ := by
  rw [lrVelocity, sum_pathFlow_piece, norm_smul, norm_neg, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  ring

/-- The assembled hop has norm at most the number of edges. -/
theorem norm_pathHop_le (n : ℕ) : ‖pathHop n‖ ≤ n := by
  calc ‖pathHop n‖ ≤ ∑ e ∈ pathGraph n, ‖swapHop e.1 e.2‖ := norm_sum_le _ _
    _ ≤ ∑ _e ∈ pathGraph n, (1 : ℝ) := Finset.sum_le_sum fun e _ => norm_swapHop_le e.1 e.2
    _ = n := by rw [Finset.sum_const, card_pathGraph, nsmul_eq_mul, mul_one]

/-- The entries of the assembled hop sum to `n · 2ⁿ`: each of the `n` edges moves `2ⁿ` of the
`2ⁿ⁺¹` configurations. -/
theorem sum_entries_pathHop (n : ℕ) :
    ∑ c, ∑ d, pathHop n c d = (n : ℂ) * 2 ^ n := by
  calc ∑ c, ∑ d, pathHop n c d
      = ∑ c, ∑ e ∈ pathGraph n, ∑ d, swapHop e.1 e.2 c d := by
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [pathHop, Matrix.sum_apply]
        exact Finset.sum_comm
    _ = ∑ e ∈ pathGraph n, ∑ c, ∑ d, swapHop e.1 e.2 c d := Finset.sum_comm
    _ = ∑ _e ∈ pathGraph n, (2 : ℂ) ^ n := by
        refine Finset.sum_congr rfl fun e he => ?_
        have h := card_moved_mul_two (fst_ne_snd_of_mem_pathGraph he)
        rw [pow_succ] at h
        rw [sum_entries_swapHop, Nat.eq_of_mul_eq_mul_right (by norm_num) h]
        push_cast
        ring
    _ = (n : ℂ) * 2 ^ n := by rw [Finset.sum_const, card_pathGraph, nsmul_eq_mul]

/-- ★★ **The assembled hop has norm at least `n/2`** — the all-ones test vector. -/
theorem half_le_norm_pathHop (n : ℕ) : (n : ℝ) / 2 ≤ ‖pathHop n‖ := by
  have h := norm_sum_entries_le (pathHop n)
  rw [sum_entries_pathHop] at h
  have hcard : (Fintype.card (ChainConfig (n + 1)) : ℝ) = 2 ^ n * 2 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    ring
  have hn : ‖(n : ℂ) * 2 ^ n‖ = (n : ℝ) * 2 ^ n := by
    rw [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_ofNat]
  rw [hn, hcard] at h
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  nlinarith

/-- ★★★ **Packaged as one flow, the same couplings have a Lieb–Robinson cone `n/2` to `n` times a
stage's**: `(n/2) · 2πe ≤ v_LR(whole chain) · τ_hop ≤ n · 2πe`. The hop-time cone does not change;
the bound's slope grows linearly with the length of the chain. -/
theorem pathFlow_lrVelocity_mul_hopTime_bounds {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (n : ℕ) :
    (n : ℝ) / 2 * coneRatio ≤ lrVelocity (pathFlow n J ħ) * hopTime J ħ
      ∧ lrVelocity (pathFlow n J ħ) * hopTime J ħ ≤ n * coneRatio := by
  have hstage : 4 * Real.exp 1 * |J / ħ| * hopTime J ħ = coneRatio := by
    rw [abs_of_pos (div_pos hJ hħ), hopTime, coneRatio]
    field_simp
    ring
  have hτ := hopTime_pos hJ hħ
  have hpre : 0 ≤ 4 * Real.exp 1 * |J / ħ| := by positivity
  rw [lrVelocity_pathFlow, ← hstage]
  constructor
  · have := half_le_norm_pathHop n
    nlinarith [mul_nonneg hpre hτ.le]
  · have := norm_pathHop_le n
    nlinarith [mul_nonneg hpre hτ.le]

/-! ### The capstone -/

/-- ★★★ **The two cones compared on the chain** (BACKLOG #205, first brick).
1. every active stage of the scheduled chain has Lieb–Robinson velocity `2πe` times its hop-time
   velocity, with `17 < 2πe < 18`;
2. the hop arrival at `d` hops lies inside the Lieb–Robinson cone and strictly after it opens;
3. over one stage the bound suppresses only beyond `18` hops;
4. the same couplings packaged as one flow on all `n` edges have a Lieb–Robinson slope between
   `n/2` and `n` times a stage's. -/
theorem cone_comparison {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (n : ℕ) :
    (∀ m (_ : m < n), lrVelocity ((chainSchedule n J ħ).stage m) = coneRatio * hopVelocity J ħ)
      ∧ (17 < coneRatio ∧ coneRatio < 18)
      ∧ (∀ m (_ : m < n) (d : ℝ), 0 < d →
          d ≤ lrVelocity ((chainSchedule n J ħ).stage m) * (d * hopTime J ħ)
            ∧ d / lrVelocity ((chainSchedule n J ħ).stage m) < d * hopTime J ħ)
      ∧ (∀ m (_ : m < n) (d : ℕ), 18 ≤ d →
          (2 * ‖∑ e ∈ ((chainSchedule n J ħ).stage m).edges,
                ((chainSchedule n J ħ).stage m).piece e‖
              * hopTime J ħ) ^ d / (d.factorial : ℝ) ≤ (1 / 2 : ℝ) ^ d)
      ∧ ((n : ℝ) / 2 * coneRatio ≤ lrVelocity (pathFlow n J ħ) * hopTime J ħ
          ∧ lrVelocity (pathFlow n J ħ) * hopTime J ħ ≤ n * coneRatio) := by
  have hne : ∀ m (hm : m < n), (Fin.castSucc (⟨m, hm⟩ : Fin n)) ≠ Fin.succ ⟨m, hm⟩ :=
    fun m hm => (Fin.castSucc_lt_succ (i := ⟨m, hm⟩)).ne
  refine ⟨fun m hm => ?_, ⟨seventeen_lt_coneRatio, coneRatio_lt_eighteen⟩, fun m hm d hd => ?_,
    fun m hm d hd => ?_, pathFlow_lrVelocity_mul_hopTime_bounds hJ hħ n⟩
  · rw [chainSchedule_stage_of_lt J ħ hm]
    exact lrVelocity_eq_coneRatio_mul hJ hħ (hne m hm)
  · rw [chainSchedule_stage_of_lt J ħ hm]
    exact ⟨arrival_mem_lrCone hJ hħ (hne m hm) hd.le, lrTime_lt_arrival hJ hħ (hne m hm) hd⟩
  · rw [chainSchedule_stage_of_lt J ħ hm]
    exact lr_bound_one_stage hJ hħ (hne m hm) hd

end CSD.CV

end
