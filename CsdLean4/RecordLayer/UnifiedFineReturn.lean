/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedCompositeCarrier

/-!
# The return leg: the messenger comes back to the gate, at any margin

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 7-SigmaLayer (the record layer). BACKLOG #379 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Remainder (a) of #375 and the
return leg asked for under UO-16.

#375 placed the fine packet of index `n` outside the far half of the ring before the predicted
angle `π/6` and inside it between `5π/6` and `7π/6`, for the coupled carrier at the one margin
`π/3`, and stopped at the angle `3π/2`. The ring brings the messenger back to the near half.
This module follows it once round, to the angle `5π/2`, at any margin `δ`, and reads the gated
pointer of #376 on the three intervals.

* ★ `fine_budget_round` — the error budget of #375 is still at most `1/(6n)` up to the flow
  time `3125π n²` (predicted angle `5π/2`);
* ★ `regionWeight_fine_back` — **back in the near half**: while the predicted angle is
  between `3π/2 + δ` and `5π/2 − δ`, the far half's weight times `1 − cos δ` is at most
  `1/(6n)`;
* `roundFibres` (`37500 π n³ (|g₁ f(θ₂)| + |g₂ h(ψ₂)|) < 1`), `isOpen_roundFibres`,
  `zero_mem_roundFibres_trainF`, `volume_roundFibres_trainF_pos`, `round_backReaction_le`;
* `fineEta` (`(1/(6n)) (1 + 1/(1 − cos δ))`), `le_fineEta`, ★ `fineCarrier_far_le_before`,
  `fineCarrier_near_le_away`, `fineCarrier_far_le_back` — **the coupled carrier at a general
  margin**: its far-half occupancy is at most `fineEta n δ` while the predicted angle is at
  most `π/2 − δ` and again between `3π/2 + δ` and `5π/2 − δ`, and at least `1 − fineEta n δ`
  between `π/2 + δ` and `3π/2 − δ`;
* `abs_gateShift_sub_sub_free_le`, `abs_gateShift_sub_sub_free_le_of_le` — the gating bound of
  #376 between two flow times;
* ★ `round_gateClock_before`, `round_gateClock_away`, `round_gateClock_back` — **the gated
  pointer through one round trip**: while the messenger is in the near half its displacement
  is close to that of the pointer of #357 on the clock's own arena; while the messenger is in
  the far half it moves at a rate at most `2|k'(χ₂)||g_c| fineEta n δ`; and after the messenger
  is back its advance is again close to that of the pointer of #357. Each bound is
  `2|k'(χ₂)||g_c| fineEta n δ` times the length of the interval.

## Exact scope

* **Displacements, not ticks.** The three statements are about the real displacement of the gated
  pointer and of the pointer of #357 on the clock's own arena. On the return interval the gated
  pointer starts from an angle that no theorem here locates (a rate bound while the messenger is
  away, nothing in the gaps), so the swing of #377, which is read from the flow time `0`, does
  not apply there. The three bounds are joined, and the return leg read in ticks, in
  `RecordLayer/UnifiedGateReturn.lean` (#380). No tick, count or record is stated on the return
  leg in this module, and no radar time is formed from counts.
* **Three intervals, with gaps.** Nothing is stated while the predicted angle is within `δ` of
  `π/2` or of `3π/2`, or after `5π/2 − δ`. The gaps have length `2500 n² δ` in flow time.
* **The bounds are rates times lengths.** `fineEta n δ` is of order `1/(n δ²)` for small `δ`,
  but each bound is `2|k'||g_c| fineEta n δ` times the length of its interval, and the
  intervals have length of order `n²`. Over a whole interval the bound is of order
  `|g_c| n/δ²`. It is small against the swing only when `|g_c| n/δ²` is small, that is for a
  clock whose rate falls with `n`; for a given clock and large `n` it is small only on
  sub-intervals of length much less than `n δ²/|g_c|`. A calculation, not in Lean.
* **The fibres shrink.** The round fibres are a subset of the fine fibres of #375 (by
  comparing the constants; no lemma), open and of positive measure for `trainF`, with the
  allowed back-reaction smaller by the factor `7/15`.
* **Earlier returns.** #200 and #202 have a round trip with emission and return records and a
  radar reading on the two-site echo arena; #270 a return by reflection on the Dirac chain
  under a stated detector law; #274 and #278 a relay under a stated hybrid law. None is on a
  joint flow with the clock. This one is a free round of the ring, with no record.
* **The arena and its limits are those of #376 (UA-17)** for the gated pointer: a fibre where
  its profile vanishes and a product start (null sets by calculations not in Lean). The gate is
  the messenger's occupancy, not a record. The comparison with the pointer of #357 is across
  arenas: the clock has no pointer of its own on the composite carrier.
* **The same clock, not a second observer.** One messenger, one clock, one round of one ring.
  The ring's length fixes the round-trip time; no distance is measured.
* **Flow times throughout (UA-7).** No speed appears: the angle `t/(1250 n²)` is the predicted
  one of #375.
* **Little weight, not none.** Not a light-cone statement.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-2,
UA-4, UA-5, UA-7, UA-8, UA-12, UA-13, UA-15, UA-17, UO-16, UD-108, UD-109, UD-112, UD-117 to
UD-119); `RecordLayer/UnifiedFineTransit.lean` (#375: `finePacket`, `fine_budget`,
`regionWeight_fine_far`, `regionWeight_fine_near`, `fineCarrier`,
`abs_arenaObs_fineCarrier_sub_le`); `RecordLayer/UnifiedCompositeCarrier.lean` (#376:
`gateShift`, `gateClockShift`, `abs_gateShift_sub_le_of_le`, `abs_gateShift_sub_free_le_of_le`,
`idxPointerShift_eq_free`); `RecordLayer/DiracArrival.lean` (`regionWeight_ringPacket_le`,
`angle_farHalf`); `RecordLayer/DiracTiming.lean` (`cos_le_cos_of_abs`);
`RecordLayer/UnifiedGateTicks.lean` (#377: the swing before departure).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### The free packet once round the ring -/

section Packet

variable {L : ℕ} [NeZero L] {n : ℕ} (hn : 0 < n) (hL : 640000 * n ^ 3 ≤ L)
include hn hL

/-- ★ **The fine packet's error budget is at most `1/(6n)` up to the flow time `3125π n²`**,
the predicted angle `5π/2`: one round of the ring and a quarter. -/
theorem fine_budget_round {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 3125 * Real.pi * (n : ℝ) ^ 2) :
    1 - (transPhase (finePacket (L := L) n 0)).re
      + |t| * limitErr 1 3 (2000 * Real.pi * (n : ℝ) ^ 2) (1 / (125 * (n : ℝ))) 4
          (2000 * Real.pi * (n : ℝ) ^ 2 / L) ≤ 1 / (6 * (n : ℝ)) := by
  have hπ := Real.pi_pos
  have hπ2 : Real.pi < 63 / 20 := by
    have := Real.pi_lt_d2
    norm_num at this ⊢
    linarith
  have hr1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (0 : ℝ) < n := by linarith
  have hLr : 640000 * (n : ℝ) ^ 3 ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le (by positivity) hLr
  set u : ℝ := 1 / (n : ℝ) with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := by
    rw [hu, div_le_one hr]
    exact hr1
  have hu2 : u ^ 2 ≤ u := by nlinarith
  have hu4 : u ^ 4 ≤ u := by nlinarith [sq_nonneg u, sq_nonneg (u ^ 2)]
  obtain ⟨hW, -⟩ := noWrap_distinct_of_window (L := L) (fine_win hn hL)
  have hRe := re_transPhase_ringPacket_ge (L := L) (c := 1) (μ := 3)
    (ℓ := 2000 * Real.pi * (n : ℝ) ^ 2) (by norm_num) (by positivity) hW
    (fun _ => 1 / Real.sqrt ((8 * n : ℕ) : ℝ)) (fun _ => by positivity)
  rw [(flat_sums (4000 * (n : ℤ) ^ 2) (N := 8 * n) (by omega)).2] at hRe
  have h6 : Real.pi * 1 / (2000 * Real.pi * (n : ℝ) ^ 2 * 3) = u ^ 2 / 6000 := by
    rw [hu]
    field_simp
    ring
  have h8 : (1 : ℝ) / ((8 * n : ℕ) : ℝ) = u / 8 := by
    rw [hu]
    push_cast
    field_simp
  rw [h6, h8] at hRe
  have hRe' : 1 - u / 8 - u / 36000000 ≤ (transPhase (finePacket (L := L) n 0)).re := by
    refine le_trans ?_ hRe
    have e : (u ^ 2 / 6000) ^ 2 = u ^ 4 / 36000000 := by ring
    rw [e]
    nlinarith [mul_nonneg (pow_nonneg hu0.le 4) hu0.le]
  set a := 2000 * Real.pi * (n : ℝ) ^ 2 / L with ha
  have ha0 : 0 ≤ a := by positivity
  have hale : a ≤ 63 / 6400 * u := by
    rw [ha, hu, div_le_iff₀ hLpos]
    have e : 63 / 6400 * (1 / (n : ℝ)) * L = 63 / 6400 * L / n := by ring
    rw [e, le_div_iff₀ hr]
    have h3 : Real.pi * (n : ℝ) ^ 3 ≤ 63 / 20 * (n : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right hπ2.le (by positivity)
    nlinarith
  have ha2 : a ^ 2 ≤ (63 / 6400) ^ 2 * u := by
    have h := pow_le_pow_left₀ ha0 hale 2
    have e : (63 / 6400 * u) ^ 2 = (63 / 6400) ^ 2 * u ^ 2 := by ring
    rw [e] at h
    nlinarith
  have herr : limitErr 1 3 (2000 * Real.pi * (n : ℝ) ^ 2) (1 / (125 * (n : ℝ))) 4 a
      = u ^ 2 / 1000 * (1 / 3 * (u / 125 + u ^ 2 / 1000) + 104 / 9 * a ^ 2) := by
    unfold limitErr
    rw [hu]
    field_simp
    ring
  set E := 1 / 3 * (u / 125 + u ^ 2 / 1000) + 104 / 9 * a ^ 2 with hE
  have hE0 : 0 ≤ E := by positivity
  have hEle : E ≤ 1 / 3 * (u / 125 + u / 1000) + 104 / 9 * ((63 / 6400) ^ 2 * u) := by
    rw [hE]
    nlinarith
  have htu : t * (u ^ 2 / 1000) ≤ 315 / 32 := by
    have e : (n : ℝ) ^ 2 * u ^ 2 = 1 := by
      rw [hu]
      field_simp
    have h1 := mul_le_mul_of_nonneg_right ht (by positivity : (0 : ℝ) ≤ u ^ 2 / 1000)
    have e2 : 3125 * Real.pi * (n : ℝ) ^ 2 * (u ^ 2 / 1000)
        = 25 / 8 * Real.pi * ((n : ℝ) ^ 2 * u ^ 2) := by ring
    rw [e2, e] at h1
    linarith
  have hterm : |t| * limitErr 1 3 (2000 * Real.pi * (n : ℝ) ^ 2) (1 / (125 * (n : ℝ))) 4 a
      ≤ 315 / 32 * (1 / 3 * (u / 125 + u / 1000) + 104 / 9 * ((63 / 6400) ^ 2 * u)) := by
    rw [herr, abs_of_nonneg ht0, ← mul_assoc]
    calc t * (u ^ 2 / 1000) * E ≤ 315 / 32 * E := mul_le_mul_of_nonneg_right htu hE0
      _ ≤ _ := mul_le_mul_of_nonneg_left hEle (by norm_num)
  have e6 : 1 / (6 * (n : ℝ)) = u / 6 := by
    rw [hu]
    field_simp
  rw [e6]
  linarith

/-- ★ **Back in the near half.** While the predicted angle is between `3π/2 + δ` and
`5π/2 − δ`, the far half's weight times `1 − cos δ` is at most `1/(6n)`: for
`1250 n² (3π/2 + δ) ≤ t ≤ 1250 n² (5π/2 − δ)`. -/
theorem regionWeight_fine_back {δ t : ℝ} (hδ0 : 0 ≤ δ)
    (ht0 : 1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 + δ) ≤ t)
    (ht : t ≤ 1250 * (n : ℝ) ^ 2 * (5 * Real.pi / 2 - δ)) :
    regionWeight (finePacket (L := L) n t) (farHalf L) * (1 - Real.cos δ)
      ≤ 1 / (6 * (n : ℝ)) := by
  have hπ := Real.pi_pos
  have hr : (0 : ℝ) < n := by exact_mod_cast hn
  have hr2 : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos hr 2
  have hθ0 : 3 * Real.pi / 2 + δ ≤ 1 / (1250 * (n : ℝ) ^ 2) * t := by
    rw [one_div, le_inv_mul_iff₀ (by positivity)]
    exact ht0
  have hθ : 1 / (1250 * (n : ℝ) ^ 2) * t ≤ 5 * Real.pi / 2 - δ := by
    rw [one_div, inv_mul_le_iff₀ (by positivity)]
    exact ht
  have h := regionWeight_ringPacket_le (L := L) (c := 1) (μ := 3)
    (ℓ := 2000 * Real.pi * (n : ℝ) ^ 2) (P := 4) (D := 1 / (125 * (n : ℝ))) (p₀ := 4)
    (by norm_num) (by norm_num) (by positivity) (by norm_num) (by positivity)
    (fine_win hn hL) (fine_spread hn) _ (fine_norm hn hL) (B := farHalf L)
    (γ := Real.cos δ) t
    (fun k hk => by
      rw [omega_fine hn]
      obtain ⟨h1, h2⟩ := (angle_farHalf (fine_sites hn hL) k).1 hk
      apply cos_le_cos_of_abs hδ0 <;> rw [abs_of_nonpos (by linarith)] <;> linarith)
  have ht0' : 0 ≤ t := le_trans (by positivity) ht0
  have hδr := mul_nonneg hr2.le hδ0
  have hπr := mul_pos hπ hr2
  have hb := fine_budget_round hn hL ht0' (by nlinarith)
  unfold finePacket at hb h ⊢
  linarith

end Packet

/-! ### The coupled carrier at a general margin -/

section Carrier

variable {M : ℕ} {f h : ℝ → ℝ} (g₁ g₂ : ℝ) (hf : Function.Periodic f 1)
  (hh : Function.Periodic h 1) {n : ℕ}

/-- **The round fibres of index `n`**: the pairs of conserved angles at which the back-reaction
of the two detectors stays small through one round of the ring,
`37500 π n³ (|g₁ f(θ₂)| + |g₂ h(ψ₂)|) < 1`. -/
def roundFibres (n : ℕ) : Set (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) :=
  {x | 37500 * Real.pi * (n : ℝ) ^ 3 * (|g₁ * hf.lift x.1| + |g₂ * hh.lift x.2|) < 1}

/-- The round fibres are open. -/
theorem isOpen_roundFibres (n : ℕ) (hf1 : ContDiff ℝ 1 f) (hh1 : ContDiff ℝ 1 h) :
    IsOpen (roundFibres g₁ g₂ hf hh n) := by
  have hb : Continuous fun x : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
      37500 * Real.pi * (n : ℝ) ^ 3 * (|g₁ * hf.lift x.1| + |g₂ * hh.lift x.2|) :=
    continuous_const.mul ((continuous_const.mul
        ((continuous_periodicLift hf hf1.continuous).comp continuous_fst)).abs.add
      (continuous_const.mul
        ((continuous_periodicLift hh hh1.continuous).comp continuous_snd)).abs)
  exact isOpen_lt hb continuous_const

/-- For both profiles `trainF` and any strengths the pair `(0, 0)` is a round fibre. -/
theorem zero_mem_roundFibres_trainF (n : ℕ) :
    ((0 : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ)))
      ∈ roundFibres g₁ g₂ trainF_periodic trainF_periodic n := by
  show 37500 * Real.pi * (n : ℝ) ^ 3 * (|g₁ * trainF_periodic.lift 0|
    + |g₂ * trainF_periodic.lift 0|) < 1
  rw [trainF_lift_zero]
  simp

/-- The round fibres have positive measure for both profiles `trainF` and any strengths. -/
theorem volume_roundFibres_trainF_pos (n : ℕ) :
    0 < volume (roundFibres g₁ g₂ trainF_periodic trainF_periodic n) :=
  (isOpen_roundFibres g₁ g₂ trainF_periodic trainF_periodic n
    (contDiff_trainF.of_le (by simp)) (contDiff_trainF.of_le (by simp))).measure_pos volume
    ⟨(0, 0), zero_mem_roundFibres_trainF g₁ g₂ n⟩

variable (hn : 0 < n)
include hn

/-- On a round fibre the back-reaction up to `3125π n²` is at most `1/(6n)`. -/
theorem round_backReaction_le {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ roundFibres g₁ g₂ hf hh n) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ 3125 * Real.pi * (n : ℝ) ^ 2) :
    2 * |t| * (|g₁ * hf.lift φ| + |g₂ * hh.lift χ|) ≤ 1 / (6 * (n : ℝ)) := by
  have hb' : 37500 * Real.pi * (n : ℝ) ^ 3 * (|g₁ * hf.lift φ| + |g₂ * hh.lift χ|) < 1 := hx
  have hr : (0 : ℝ) < n := by exact_mod_cast hn
  set b := |g₁ * hf.lift φ| + |g₂ * hh.lift χ| with hbdef
  have hb0 : 0 ≤ b := by positivity
  rw [abs_of_nonneg ht0, le_div_iff₀ (by positivity)]
  have h1 := mul_le_mul_of_nonneg_right ht (mul_nonneg hb0 hr.le)
  nlinarith

/-- **The bound at the margin `δ`**: `(1/(6n)) (1 + 1/(1 − cos δ))`. -/
noncomputable def fineEta (n : ℕ) (δ : ℝ) : ℝ := 1 / (6 * (n : ℝ)) * (1 + 1 / (1 - Real.cos δ))

omit hn in
/-- A weight whose product with `1 − cos δ` is at most `1/(6n)`, moved by at most `1/(6n)`, is
at most `fineEta n δ`. -/
theorem le_fineEta {δ w o : ℝ} (hcos : Real.cos δ < 1)
    (hw : w * (1 - Real.cos δ) ≤ 1 / (6 * (n : ℝ)))
    (ho : o ≤ w + 1 / (6 * (n : ℝ))) : o ≤ fineEta n δ := by
  have hpos : 0 < 1 - Real.cos δ := by linarith
  have h1 : w ≤ 1 / (6 * (n : ℝ)) / (1 - Real.cos δ) := (le_div_iff₀ hpos).2 hw
  have e : fineEta n δ = 1 / (6 * (n : ℝ)) + 1 / (6 * (n : ℝ)) / (1 - Real.cos δ) := by
    unfold fineEta
    ring
  rw [e]
  linarith

variable (hL : 640000 * n ^ 3 ≤ M + 1)
include hL

/-- ★ **Before the transit, at any margin.** On a round fibre the coupled carrier's far-half
occupancy is at most `fineEta n δ` at every flow time with predicted angle at most `π/2 − δ`. -/
theorem fineCarrier_far_le_before {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ roundFibres g₁ g₂ hf hh n) {δ : ℝ} (hδ0 : 0 ≤ δ) (hcos : Real.cos δ < 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - δ)) :
    arenaObs (regionProj (farHalf (M + 1))) (fineCarrier g₁ g₂ hf hh hn hL φ χ t)
      ≤ fineEta n δ := by
  have hπ := Real.pi_pos
  have hr2 : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos (by exact_mod_cast hn) 2
  have hδr := mul_nonneg hr2.le hδ0
  have h1 := abs_le.1 (abs_arenaObs_fineCarrier_sub_le g₁ g₂ hf hh hn hL φ χ t)
  have h2 := round_backReaction_le g₁ g₂ hf hh hn hx ht0 (by nlinarith [mul_pos hπ hr2])
  exact le_fineEta hcos (regionWeight_fine_far (L := M + 1) hn hL hδ0 ht0 ht) (by linarith)

/-- **While the messenger is away, at any margin.** On a round fibre the coupled carrier's
far-half occupancy is at least `1 − fineEta n δ` at every flow time with predicted angle
between `π/2 + δ` and `3π/2 − δ`. -/
theorem fineCarrier_near_le_away {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ roundFibres g₁ g₂ hf hh n) {δ : ℝ} (hδ0 : 0 ≤ δ) (hcos : Real.cos δ < 1)
    {t : ℝ} (ht0 : 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + δ) ≤ t)
    (ht : t ≤ 1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 - δ)) :
    1 - arenaObs (regionProj (farHalf (M + 1))) (fineCarrier g₁ g₂ hf hh hn hL φ χ t)
      ≤ fineEta n δ := by
  have hπ := Real.pi_pos
  have hr2 : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos (by exact_mod_cast hn) 2
  have hδr := mul_nonneg hr2.le hδ0
  have ht0' : 0 ≤ t := le_trans (by positivity) ht0
  have h1 := abs_le.1 (abs_arenaObs_fineCarrier_sub_le g₁ g₂ hf hh hn hL φ χ t)
  have h2 := round_backReaction_le g₁ g₂ hf hh hn hx ht0' (by nlinarith [mul_pos hπ hr2])
  exact le_fineEta hcos (regionWeight_fine_near (L := M + 1) hn hL hδ0 ht0 ht) (by linarith)

/-- **After the return, at any margin.** On a round fibre the coupled carrier's far-half
occupancy is at most `fineEta n δ` at every flow time with predicted angle between
`3π/2 + δ` and `5π/2 − δ`. -/
theorem fineCarrier_far_le_back {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ roundFibres g₁ g₂ hf hh n) {δ : ℝ} (hδ0 : 0 ≤ δ) (hcos : Real.cos δ < 1)
    {t : ℝ} (ht0 : 1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 + δ) ≤ t)
    (ht : t ≤ 1250 * (n : ℝ) ^ 2 * (5 * Real.pi / 2 - δ)) :
    arenaObs (regionProj (farHalf (M + 1))) (fineCarrier g₁ g₂ hf hh hn hL φ χ t)
      ≤ fineEta n δ := by
  have hπ := Real.pi_pos
  have hr2 : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos (by exact_mod_cast hn) 2
  have hδr := mul_nonneg hr2.le hδ0
  have ht0' : 0 ≤ t := le_trans (by positivity) ht0
  have h1 := abs_le.1 (abs_arenaObs_fineCarrier_sub_le g₁ g₂ hf hh hn hL φ χ t)
  have h2 := round_backReaction_le g₁ g₂ hf hh hn hx ht0' (by nlinarith [mul_pos hπ hr2])
  exact le_fineEta hcos (regionWeight_fine_back (L := M + 1) hn hL hδ0 ht0 ht) (by linarith)

end Carrier

/-! ### The gating bound between two flow times -/

section Gate

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
  {f h k : ℝ → ℝ} {A₀ B₁ B₂ P : Matrix ι ι ℂ} {C₀ X : Matrix κ κ ℂ}

/-- **Between two flow times the gated pointer's advance is within `2|k'(ζ)| c` times the
accumulated `1 − ⟨P⟩` of the advance of the pointer coupled to `X` alone**, when `⟨P⟩ ≤ 1` at
every ray and `‖X‖ ≤ c`. -/
theorem abs_gateShift_sub_sub_free_le (hA : A₀.IsHermitian) (hB₁ : B₁.IsHermitian)
    (hB₂ : B₂.IsHermitian) (hC : C₀.IsHermitian) (hf : Function.Periodic f 1)
    (hh : Function.Periodic h 1) (hk : Function.Periodic k 1) (φ χ ζ : AddCircle (1 : ℝ))
    (p : GenArena ι) (q : GenArena κ) (hP1 : ∀ r : GenArena ι, arenaObs P r ≤ 1) {c : ℝ}
    (hX : ‖X‖ ≤ c) {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    |gateShift hA hB₁ hB₂ hC P X hf hh hk φ χ ζ p q t₂
        - gateShift hA hB₁ hB₂ hC P X hf hh hk φ χ ζ p q t₁
        - -2 * hk.deriv_periodic.lift ζ
          * ∫ s in t₁..t₂, arenaObs X (arenaKick (idxFreeU hC s) q)|
      ≤ 2 * |hk.deriv_periodic.lift ζ| * c
        * ∫ s in t₁..t₂,
            (1 - arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p)) := by
  have ho := continuous_arenaObs_idxTwoCarrierU hA hB₁ hB₂ P hf hh φ χ p
  have hx := continuous_arenaObs_idxFreeU hC X q
  have hox : Continuous fun s : ℝ =>
      arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p)
        * arenaObs X (arenaKick (idxFreeU hC s) q) := ho.mul hx
  have hkey : |∫ s in t₁..t₂,
        (arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p)
          * arenaObs X (arenaKick (idxFreeU hC s) q)
        - arenaObs X (arenaKick (idxFreeU hC s) q))|
      ≤ c * ∫ s in t₁..t₂,
          (1 - arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine (intervalIntegral.abs_integral_le_integral_abs ht).trans ?_
    refine intervalIntegral.integral_mono_on ht ((hox.sub hx).abs.intervalIntegrable t₁ t₂)
      ((continuous_const.mul (continuous_const.sub ho)).intervalIntegrable t₁ t₂) fun s _ => ?_
    have h1 : 0 ≤ 1 - arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p) :=
      sub_nonneg.2 (hP1 _)
    have e : arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p)
          * arenaObs X (arenaKick (idxFreeU hC s) q) - arenaObs X (arenaKick (idxFreeU hC s) q)
        = -((1 - arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p))
            * arenaObs X (arenaKick (idxFreeU hC s) q)) := by ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg h1]
    exact (mul_comm _ _).trans_le
      (mul_le_mul_of_nonneg_right ((abs_arenaObs_le X _).trans hX) h1)
  rw [gateShift, gateShift, ← mul_sub,
    intervalIntegral.integral_interval_sub_left (hox.intervalIntegrable 0 t₂)
      (hox.intervalIntegrable 0 t₁), ← mul_sub,
    ← intervalIntegral.integral_sub (hox.intervalIntegrable t₁ t₂)
      (hx.intervalIntegrable t₁ t₂), abs_mul, abs_mul, abs_neg, abs_two]
  exact (mul_le_mul_of_nonneg_left hkey
    (show (0 : ℝ) ≤ 2 * |hk.deriv_periodic.lift ζ| by positivity)).trans_eq (by ring)

/-- The same with a pointwise bound `1 − ⟨P⟩ ≤ η` on the interval. -/
theorem abs_gateShift_sub_sub_free_le_of_le (hA : A₀.IsHermitian) (hB₁ : B₁.IsHermitian)
    (hB₂ : B₂.IsHermitian) (hC : C₀.IsHermitian) (hf : Function.Periodic f 1)
    (hh : Function.Periodic h 1) (hk : Function.Periodic k 1) (φ χ ζ : AddCircle (1 : ℝ))
    (p : GenArena ι) (q : GenArena κ) (hP1 : ∀ r : GenArena ι, arenaObs P r ≤ 1) {c : ℝ}
    (hc0 : 0 ≤ c) (hX : ‖X‖ ≤ c) {t₁ t₂ η : ℝ} (ht : t₁ ≤ t₂)
    (hη : ∀ s ∈ Icc t₁ t₂,
      1 - arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p) ≤ η) :
    |gateShift hA hB₁ hB₂ hC P X hf hh hk φ χ ζ p q t₂
        - gateShift hA hB₁ hB₂ hC P X hf hh hk φ χ ζ p q t₁
        - -2 * hk.deriv_periodic.lift ζ
          * ∫ s in t₁..t₂, arenaObs X (arenaKick (idxFreeU hC s) q)|
      ≤ 2 * |hk.deriv_periodic.lift ζ| * c * (η * (t₂ - t₁)) := by
  refine (abs_gateShift_sub_sub_free_le hA hB₁ hB₂ hC hf hh hk φ χ ζ p q hP1 hX ht).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have ho := continuous_arenaObs_idxTwoCarrierU hA hB₁ hB₂ P hf hh φ χ p
  refine (intervalIntegral.integral_mono_on ht
    ((continuous_const.sub ho).intervalIntegrable t₁ t₂)
    (continuous_const.intervalIntegrable t₁ t₂) hη).trans_eq ?_
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]

end Gate

/-! ### The gated pointer through one round trip -/

section Round

variable {M Mc : ℕ} {f h k : ℝ → ℝ} (g₁ g₂ : ℝ) (Jc μ₀ μ₁ gc : ℝ)
  (hf : Function.Periodic f 1) (hh : Function.Periodic h 1) (hk : Function.Periodic k 1)
  {n : ℕ} (hn : 0 < n) (hL : 640000 * n ^ 3 ≤ M + 1)
include hn hL

/-- ★ **Before the messenger leaves, at any margin, the gated pointer's displacement is close to
that of the clock's pointer on its own arena.** On a round fibre, on a fibre `ζ` where the gated
pointer's profile vanishes: at every flow time `t` with predicted angle at most `π/2 − δ` the
gated pointer's displacement is within `2|k'(ζ)||g_c| fineEta n δ · t` of that of the pointer of
#357 on the same clock. -/
theorem round_gateClock_before {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ roundFibres g₁ g₂ hf hh n) {ζ : AddCircle (1 : ℝ)} (hz : hk.lift ζ = 0)
    (q : GenArena ((ZMod (Mc + 1) × Fin 2) × Fin 2)) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hcos : Real.cos δ < 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - δ)) :
    |gateClockShift (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) Jc μ₀ μ₁
          gc hf hh hk φ χ ζ
          (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)) q t
        - idxPointerShift (deviceHam_isHermitian Jc μ₀ μ₁) (clockB_isHermitian gc) hk ζ q t|
      ≤ 2 * |hk.deriv_periodic.lift ζ| * |gc| * (fineEta n δ * t) := by
  rw [idxPointerShift_eq_free Jc μ₀ μ₁ gc hk hz q t]
  refine abs_gateShift_sub_free_le_of_le (diracHam_isHermitian _ _)
    (regionProj_smul_isHermitian g₁ _) (regionProj_smul_isHermitian g₂ _)
    (deviceHam_isHermitian Jc μ₀ μ₁) hf hh hk φ χ ζ _ q
    (fun r => arenaObs_regionProj_le_one _ r) (abs_nonneg gc) (norm_clockB_le gc) ht0
    fun s hs => ?_
  rw [arenaObs_regionProj_compl, sub_sub_cancel]
  exact fineCarrier_far_le_before g₁ g₂ hf hh hn hL hx hδ0 hcos hs.1 (hs.2.trans ht)

/-- ★ **While the messenger is away the gated pointer moves at a rate at most
`2|k'(ζ)||g_c| fineEta n δ`.** The inequality holds for
`gateClockShift` at every `ζ` and every clock ray; `gateClockShift` is the gated pointer's
displacement only on a fibre where the profile vanishes (`gateClockFlow_apply`). With the same
fibres: between two flow times
`t₁ ≤ t₂` with predicted angles between `π/2 + δ` and `3π/2 − δ` the gated pointer's
displacement changes by at most `2|k'(ζ)||g_c| fineEta n δ (t₂ − t₁)`. -/
theorem round_gateClock_away {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ roundFibres g₁ g₂ hf hh n) (ζ : AddCircle (1 : ℝ))
    (q : GenArena ((ZMod (Mc + 1) × Fin 2) × Fin 2)) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hcos : Real.cos δ < 1) {t₁ t₂ : ℝ}
    (ht0 : 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + δ) ≤ t₁) (ht : t₁ ≤ t₂)
    (ht2 : t₂ ≤ 1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 - δ)) :
    |gateClockShift (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) Jc μ₀
          μ₁ gc hf hh hk φ χ ζ
          (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)) q t₂
        - gateClockShift (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) Jc
          μ₀ μ₁ gc hf hh hk φ χ ζ
          (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)) q t₁|
      ≤ 2 * |hk.deriv_periodic.lift ζ| * |gc| * (fineEta n δ * (t₂ - t₁)) := by
  refine abs_gateShift_sub_le_of_le (diracHam_isHermitian _ _)
    (regionProj_smul_isHermitian g₁ _) (regionProj_smul_isHermitian g₂ _)
    (deviceHam_isHermitian Jc μ₀ μ₁) hf hh hk φ χ ζ _ q
    (fun r => arenaObs_regionProj_nonneg _ r) (abs_nonneg gc) (norm_clockB_le gc) ht
    fun s hs => ?_
  rw [arenaObs_regionProj_compl]
  exact fineCarrier_near_le_away g₁ g₂ hf hh hn hL hx hδ0 hcos (ht0.trans hs.1)
    (hs.2.trans ht2)

/-- ★ **After the messenger is back the gated pointer's advance is again close to that of
the clock's pointer on its own arena.**
With the same fibres, on a fibre `ζ` where the gated pointer's profile vanishes: between two
flow times `t₁ ≤ t₂` with predicted angles between `3π/2 + δ` and `5π/2 − δ` the advance of
the gated pointer is within `2|k'(ζ)||g_c| fineEta n δ (t₂ − t₁)` of the advance of the pointer
of #357 on the same clock. -/
theorem round_gateClock_back {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ roundFibres g₁ g₂ hf hh n) {ζ : AddCircle (1 : ℝ)} (hz : hk.lift ζ = 0)
    (q : GenArena ((ZMod (Mc + 1) × Fin 2) × Fin 2)) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hcos : Real.cos δ < 1) {t₁ t₂ : ℝ}
    (ht0 : 1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 + δ) ≤ t₁) (ht : t₁ ≤ t₂)
    (ht2 : t₂ ≤ 1250 * (n : ℝ) ^ 2 * (5 * Real.pi / 2 - δ)) :
    |gateClockShift (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) Jc μ₀
          μ₁ gc hf hh hk φ χ ζ
          (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)) q t₂
        - gateClockShift (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) Jc
          μ₀ μ₁ gc hf hh hk φ χ ζ
          (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)) q t₁
        - (idxPointerShift (deviceHam_isHermitian Jc μ₀ μ₁) (clockB_isHermitian gc) hk ζ q t₂
          - idxPointerShift (deviceHam_isHermitian Jc μ₀ μ₁) (clockB_isHermitian gc) hk ζ q
            t₁)|
      ≤ 2 * |hk.deriv_periodic.lift ζ| * |gc| * (fineEta n δ * (t₂ - t₁)) := by
  have hx' := continuous_arenaObs_idxFreeU (deviceHam_isHermitian Jc μ₀ μ₁) (clockB Mc gc) q
  rw [idxPointerShift_eq_free Jc μ₀ μ₁ gc hk hz q t₂,
    idxPointerShift_eq_free Jc μ₀ μ₁ gc hk hz q t₁, ← mul_sub,
    intervalIntegral.integral_interval_sub_left (hx'.intervalIntegrable 0 t₂)
      (hx'.intervalIntegrable 0 t₁)]
  refine abs_gateShift_sub_sub_free_le_of_le (diracHam_isHermitian _ _)
    (regionProj_smul_isHermitian g₁ _) (regionProj_smul_isHermitian g₂ _)
    (deviceHam_isHermitian Jc μ₀ μ₁) hf hh hk φ χ ζ _ q
    (fun r => arenaObs_regionProj_le_one _ r) (abs_nonneg gc) (norm_clockB_le gc) ht
    fun s hs => ?_
  rw [arenaObs_regionProj_compl, sub_sub_cancel]
  exact fineCarrier_far_le_back g₁ g₂ hf hh hn hL hx hδ0 hcos (ht0.trans hs.1)
    (hs.2.trans ht2)

end Round

end CSD.RecordLayer

end
