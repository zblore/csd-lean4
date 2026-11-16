/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedGateTimes

/-!
# The tolerance test for one gate of the walled chain; the two clocks' gate

**Category:** 7-SigmaLayer (the record layer). BACKLOG #415 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; item R6 of the list under
UD-164 for one messenger–clock gate, and of item R1 the gate between the two clocks. No new
assumption beyond UA-18.

#413 leaves a question open: can one choice of the parameters make the messenger's budget
small against the gate's resolution, the gate's closing short against a tick, and the
messenger fast, together? This module answers it for the bounds of one gate. The clock's
bound of #409 was taken at the end of a horizon `4π n/Δ`, which is too coarse for the answer;
it is restated at each packet time.

* `heavy_packet_budget_time`, `regionWeight_heavyWall_away_le`,
  `deviceRegionWeight_icoWall_time_le`, ★★ `one_sub_sum_arenaObs_wallArcs_icoDevice_time_le`
  — a flat clock wall state at each packet time `t`: the occupancy outside its two double
  arcs, times `1 − cos δ`, is at most `4 · lightBudget n N 1 t`;
* `wallN`, `wallK`, `wallGap`, `wallDelta`, `wallMu`, ★★★ `wall_values` — **the test is
  passed for the bounds**: for every `k ≥ 1`, with `n = N = 10¹⁶ k⁴`, gap `Δ = k/K`,
  `δ = 1/(10⁵ k)` and messenger rest energy `1/k`, at all packet times within `10 K`:
  the two carriers' bounds together are at most `(1/(1000 k)) (1 − cos δ)`; the closing
  interval `4δ K · 20` takes at most `1/1000` of the clock's phase; the whole run takes at
  most `1/100` of a phase times the gate's weight; and the messenger is within `2/k²` of
  speed `1`;
* ★★ `wallGate_clocks_not_le`, ★★ `wallGate_clocks_le` — the wall gate between two clock
  rays, from their four double arcs.

## Exact scope

* **The test is of bounds, not of readings.** `wall_values` says that the quantities which
  the gate theorems of #413 and #414 bound, and the closing interval of #414, are small
  together along a family. The reading theorems (#394, #399, #400) have further size
  conditions of their own; they are not checked here, and no count or reading is stated.
* **The relative speed is taken to be at least `1/20`** in the closing interval, and the run
  to last at most `10 K` in the flow time; neither is derived from the packets here. For
  `k ≥ 2` the messenger's velocity is at least `1/2` and the clock's lower level moves at
  about `0.447`, a difference of about `0.05` (a calculation, not in Lean).
* **The family lets the gap go to zero** (`Δ = k/K`): the clock ticks about `k` times in a
  run. The dilation is to be resolved against `2/k²` and the gate's `1/(1000 k)`; that
  comparison is not made here.
* **The two clocks' gate is for any two clock rays**; it is not combined with the clocks'
  wall states.
* **Uncoupled orbits, angles**, as #413.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-164, UD-176, UD-179, UD-182, UD-183, UD-184, UD-185);
`RecordLayer/UnifiedFastMessenger.lean` (#413: `lightBudget`, `light_packet_budget`,
`one_sub_vRel_half_le`); `RecordLayer/UnifiedWallBudgets.lean` (#409: `ico_packet_start_le`,
`mirror_ico_mem_range`, `negWin_Ico`); `RecordLayer/UnifiedWallOrbits.lean` (#411:
`one_sub_sum_arenaObs_wallArcs_icoDevice_le`, `icoWindow_mem_range`);
`RecordLayer/UnifiedWallGate.lean` (#410: `wallNear_of_mem_wallArc`,
`not_wallNear_of_mem_wallArc`); `RecordLayer/UnifiedEmissionValues.lean` (#397:
`sq_div_five_le_one_sub_cos`); `RecordLayer/UnifiedReturnValues.lean` (#403: the same test on
the ring); `RecordLayer/UnifiedGatedReading.lean` (#394:
`arenaObs_coincProj_prodRay_le_of_disjoint`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### The clock's wall state at each packet time -/

section Timed

variable {n N M : ℕ} {lo lo₁ : ℤ}

/-- The budget of a flat packet of rest energy `μ ≥ 1` at the packet time `t` is at most
`lightBudget n N 1 t`. -/
theorem heavy_packet_budget_time (hn : 0 < n) (hN : 0 < N) (hM : 210000 * n ^ 2 * N ≤ M)
    (hWin : ∀ m ∈ Finset.Ico lo (lo + N), lo₁ ≤ m ∧ m + 1 < lo₁ + ((M + 1 : ℕ) : ℤ))
    {μ : ℝ} (hμ : 1 ≤ μ) (t : ℝ) :
    1 - (transPhase (ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N))
          (Finset.Ico lo (lo + N)) (flatAmpN N) 0)).re
      + |t| * limitErr 1 μ (ringLen (1200 * n * N)) (1 / (600 * n)) (1 / 2)
          (ringLen (1200 * n * N) / (M + 1 : ℕ))
      ≤ lightBudget n N 1 t := by
  have hstart := ico_packet_start_le (M := M) hn hN hWin hμ
  have hrate := (flat_packet_limitErr_le hn hN hM hμ).2
  have hdrift := mul_le_mul_of_nonneg_left hrate (abs_nonneg t)
  have e : (1 / (2 * (1200 * (n : ℝ) * N))) ^ 2 = 1 / (4 * (1200 * (n : ℝ) * N) ^ 2) := by
    rw [div_pow, one_pow, mul_pow]
    norm_num
  simp only [lightBudget, mul_one, div_one, one_mul]
  rw [e]
  linarith

/-- The wall state of a flat packet of rest energy `μ ≥ 1`, at each packet time. -/
theorem regionWeight_heavyWall_away_le (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {μ : ℝ} (hμ : 1 ≤ μ) {p₀ : ℝ} (hp₀ : |p₀| ≤ 1 / 2)
    (hWin : ∀ m ∈ Finset.Ico lo (lo + N), lo₁ ≤ m ∧ m + 1 < lo₁ + ((M + 1 : ℕ) : ℤ))
    (hWD : ∀ m ∈ Finset.Ico lo (lo + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - p₀| ≤ 1 / (600 * n))
    {B : Finset (ZMod (M + 1))} {γ : ℝ} (hγ : γ < 1) (t : ℝ)
    (hB : ∀ k ∈ B, Real.cos (2 * Real.pi * k.val / (M + 1 : ℕ)
      - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 * p₀) * t) ≤ γ)
    (hB' : ∀ k ∈ B, Real.cos (2 * Real.pi * k.val / (M + 1 : ℕ)
      - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 * -p₀) * t) ≤ γ) :
    regionWeight (oddWall (L := M + 1) 1 μ (ringLen (1200 * n * N))
        (Finset.Ico lo (lo + N)) (flatAmpN N) t) B * (1 - γ)
      ≤ 4 * lightBudget n N 1 t := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : 0 < 1200 * n * N := by positivity
  have h := regionWeight_oddWall_away_le (L := M + 1) (c := 1) (P := 1 / 2)
    (D := 1 / (600 * n)) one_pos (by linarith) (ringLen_pos hK) hp₀ (by positivity) hWin hWD
    (flatAmpN N) (sum_norm_flatAmpN_Ico lo hN) hγ t hB hB'
  have b1 := heavy_packet_budget_time hn hN hM hWin hμ t
  have b2 := heavy_packet_budget_time hn hN hM (mirror_ico_mem_range hWin) hμ t
  have em : mirrorPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) (Finset.Ico lo (lo + N))
      (flatAmpN N) 0
      = ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N))
        (Finset.Ico (-lo - N + 1) (-lo - N + 1 + N)) (flatAmpN N) 0 := by
    rw [mirrorPacket, negWin_Ico]
    rfl
  rw [em] at h
  linarith

/-- The two-level clock's flat wall state, at each packet time. -/
theorem deviceRegionWeight_icoWall_time_le (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) {p₀ : ℝ} (hp₀ : |p₀| ≤ 1 / 2)
    (hW : ∀ m ∈ Finset.Ico lo (lo + N), -m ∉ Finset.Ico lo (lo + N))
    (hWin : ∀ m ∈ Finset.Ico lo (lo + N), lo₁ ≤ m ∧ m + 1 < lo₁ + ((M + 1 : ℕ) : ℤ))
    (hWD : ∀ m ∈ Finset.Ico lo (lo + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - p₀| ≤ 1 / (600 * n))
    {B : Finset (ZMod (M + 1))} {γ : ℝ} (hγ : γ < 1) (t : ℝ)
    (hB0 : ∀ k ∈ B, Real.cos (2 * Real.pi * k.val / (M + 1 : ℕ)
      - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 1 (1 * p₀) * t) ≤ γ)
    (hB0' : ∀ k ∈ B, Real.cos (2 * Real.pi * k.val / (M + 1 : ℕ)
      - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 1 (1 * -p₀) * t) ≤ γ)
    (hB1 : ∀ k ∈ B, Real.cos (2 * Real.pi * k.val / (M + 1 : ℕ)
      - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 (1 + Δ) (1 * p₀) * t) ≤ γ)
    (hB1' : ∀ k ∈ B, Real.cos (2 * Real.pi * k.val / (M + 1 : ℕ)
      - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 (1 + Δ) (1 * -p₀) * t) ≤ γ) :
    deviceRegionWeight (devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
        (Finset.Ico lo (lo + N) ∪ negWin (Finset.Ico lo (lo + N)))
        (oddExt (Finset.Ico lo (lo + N)) (flatAmpN N)) t) B * (1 - γ)
      ≤ 4 * lightBudget n N 1 t := by
  have a0 := regionWeight_heavyWall_away_le hn hN hM (μ := 1) le_rfl hp₀ hWin hWD hγ t hB0
    hB0'
  have a1 := regionWeight_heavyWall_away_le hn hN hM (μ := 1 + Δ) (by linarith) hp₀ hWin hWD
    hγ t hB1 hB1'
  have hgoal : deviceRegionWeight (devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1
      (1 + Δ) (Finset.Ico lo (lo + N) ∪ negWin (Finset.Ico lo (lo + N)))
      (oddExt (Finset.Ico lo (lo + N)) (flatAmpN N)) t) B
      = deviceRegionWeight (devicePacket (L := M + 1)
        (scaledHop 1 (ringLen (1200 * n * N) / ((M + 1 : ℕ) : ℝ))) 1 (1 + Δ)
        (Finset.Ico lo (lo + N) ∪ negWin (Finset.Ico lo (lo + N)))
        (oddExt (Finset.Ico lo (lo + N)) (flatAmpN N)) t) B := rfl
  rw [hgoal, deviceRegionWeight_wall 1 (ringLen (1200 * n * N)) 1 (1 + Δ) hW]
  have e : (regionWeight (oddWall (L := M + 1) 1 1 (ringLen (1200 * n * N))
          (Finset.Ico lo (lo + N)) (flatAmpN N) t) B
        + regionWeight (oddWall (L := M + 1) 1 (1 + Δ) (ringLen (1200 * n * N))
          (Finset.Ico lo (lo + N)) (flatAmpN N) t) B) / 2 * (1 - γ)
      = (regionWeight (oddWall (L := M + 1) 1 1 (ringLen (1200 * n * N))
          (Finset.Ico lo (lo + N)) (flatAmpN N) t) B * (1 - γ)
        + regionWeight (oddWall (L := M + 1) 1 (1 + Δ) (ringLen (1200 * n * N))
          (Finset.Ico lo (lo + N)) (flatAmpN N) t) B * (1 - γ)) / 2 := by ring
  rw [e]
  linarith

/-- ★★ **A flat clock wall state stays in its two double arcs, at each packet time.** Along
the uncoupled orbit from the packet time `t₁`, at the flow time `s`: the occupancy outside
the two double arcs of half-angle `δ`, times `1 − cos δ`, is at most
`4 · lightBudget n N 1 (t₁ + s)`. -/
theorem one_sub_sum_arenaObs_wallArcs_icoDevice_time_le (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) {lo : ℤ} (hlo : 0 < lo)
    (hhi : 2 * (lo + N) ≤ M) {p₀ : ℝ} (hp₀ : |p₀| ≤ 1 / 2)
    (hWD : ∀ m ∈ Finset.Ico lo (lo + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - p₀| ≤ 1 / (600 * n)) (t₁ : ℝ)
    (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
      (Finset.Ico lo (lo + N) ∪ negWin (Finset.Ico lo (lo + N)))
      (oddExt (Finset.Ico lo (lo + N)) (flatAmpN N)) t₁ ≠ 0) {δ : ℝ}
    (hδ : Real.cos δ < 1) (s : ℝ) :
    (1 - ∑ k ∈ wallArc (M + 1)
            (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 1 (1 * p₀) * (t₁ + s)) δ
          ∪ wallArc (M + 1)
            (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 (1 + Δ) (1 * p₀) * (t₁ + s)) δ,
        arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k)
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ))) * (1 - Real.cos δ)
      ≤ 4 * lightBudget n N 1 (t₁ + s) := by
  have hW : ∀ m ∈ Finset.Ico lo (lo + N), -m ∉ Finset.Ico lo (lo + N) := by
    intro m hm h
    rw [Finset.mem_Ico] at hm h
    omega
  have hWinS : ∀ m ∈ Finset.Ico lo (lo + N) ∪ negWin (Finset.Ico lo (lo + N)),
      (-(lo + N) : ℤ) ≤ m ∧ m + 1 < (-(lo + N) : ℤ) + ((M + 1 : ℕ) : ℤ) := by
    intro m hm
    rcases Finset.mem_union.1 hm with h | h
    · rw [Finset.mem_Ico] at h
      refine ⟨by omega, ?_⟩
      push_cast
      omega
    · have h' := (mem_negWin _ m).1 h
      rw [Finset.mem_Ico] at h'
      refine ⟨by omega, ?_⟩
      push_cast
      omega
  have hD := (noWrap_distinct_of_window (L := M + 1) hWinS).2
  have hnorm : (deviceNorm (devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
      (Finset.Ico lo (lo + N) ∪ negWin (Finset.Ico lo (lo + N)))
      (oddExt (Finset.Ico lo (lo + N)) (flatAmpN N)) t₁)).re = 1 := by
    rw [deviceNorm_devicePacket one_pos (by linarith) hD,
      sum_norm_oddExt hW (sum_norm_flatAmpN_Ico lo hN)]
    simp
  rw [one_sub_sum_arenaObs_siteSel, sum_arenaObs_siteSel_free_deviceRay, hnorm, div_one,
    deviceProp_devicePacket_shift]
  have hneg : ∀ μ' : ℝ,
      2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ' (1 * -p₀) * (t₁ + s)
        = -(2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ' (1 * p₀) * (t₁ + s)) := fun μ' => by
    rw [mul_neg, vRel_neg]
    ring
  refine deviceRegionWeight_icoWall_time_le hn hN hM hΔ0 hp₀ hW (icoWindow_mem_range hlo hhi)
    hWD hδ (t₁ + s) (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_)
  all_goals
    rw [Finset.mem_compl, Finset.mem_union, not_or, mem_wallArc, mem_wallArc, not_or, not_or,
      mem_ringArc, mem_ringArc, mem_ringArc, mem_ringArc, not_lt, not_lt, not_lt, not_lt] at hk
  · exact hk.1.1
  · rw [hneg]
    exact hk.1.2
  · exact hk.2.1
  · rw [hneg]
    exact hk.2.2

end Timed

/-! ### Values: the tolerance test for one gate -/

/-- The number of modes and the tick parameter of the family: `10¹⁶ k⁴`. -/
def wallN (k : ℕ) : ℕ := 10 ^ 16 * k ^ 4

/-- The ring's size parameter of the family: `K = 1200 · wallN²`. -/
def wallK (k : ℕ) : ℝ := 1200 * (wallN k : ℝ) * wallN k

/-- The clock's level gap of the family: `k/K`. -/
def wallGap (k : ℕ) : ℝ := k / wallK k

/-- The arcs' half-angle of the family: `1/(10⁵ k)`. -/
def wallDelta (k : ℕ) : ℝ := 1 / (10 ^ 5 * (k : ℝ))

/-- The messenger's rest energy of the family: `1/k`. -/
def wallMu (k : ℕ) : ℝ := 1 / (k : ℝ)

/-- ★★★ **The tolerance test for one gate, passed for the bounds.** For every `k ≥ 1`, with
`n = N = 10¹⁶ k⁴`, at all packet times within `10 K`: (i) the messenger's and the clock's
bounds of #413 and of this module together are at most `(1/(1000 k)) (1 − cos δ)`; (ii) the
closing interval `4δ K · 20` (relative angular speed at least `1/(20 K)`) takes at most
`1/1000` of the clock's phase; (iii) a run of `10 K` takes `10 k` of phase, and that times
the gate's weight `1/(1000 k)` is `1/100`; (iv) the messenger's velocity is within `2/k²` of
`1`; (v) `0 < μ ≤ 1` and `0 < Δ ≤ 1/2`. -/
theorem wall_values {k : ℕ} (hk : 1 ≤ k) {t t' : ℝ} (ht : |t| ≤ 10 * wallK k)
    (ht' : |t'| ≤ 10 * wallK k) :
    4 * lightBudget (wallN k) (wallN k) (wallMu k) t
        + 4 * lightBudget (wallN k) (wallN k) 1 t'
      ≤ 1 / (1000 * (k : ℝ)) * (1 - Real.cos (wallDelta k))
    ∧ wallGap k * (4 * wallDelta k * wallK k * 20) ≤ 1 / 1000
    ∧ wallGap k * (10 * wallK k) * (1 / (1000 * (k : ℝ))) = 1 / 100
    ∧ 1 - vRel 1 (wallMu k) (1 * (1 / 2)) ≤ 2 / (k : ℝ) ^ 2
    ∧ (0 < wallMu k ∧ wallMu k ≤ 1)
    ∧ (0 < wallGap k ∧ wallGap k ≤ 1 / 2) := by
  have hX1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hX0 : (0 : ℝ) < k := by linarith
  have hN : ((wallN k : ℕ) : ℝ) = 10 ^ 16 * (k : ℝ) ^ 4 := by
    rw [wallN]
    push_cast
    ring
  have hπ := Real.pi_gt_three
  unfold wallMu wallDelta wallGap
  generalize hXd : (k : ℝ) = X at *
  set Nr : ℝ := 10 ^ 16 * X ^ 4 with hNr
  have hX4 : 1 ≤ X ^ 4 := one_le_pow₀ hX1
  have hXX4 : X ≤ X ^ 4 := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ 4 := pow_le_pow_right₀ hX1 (by norm_num)
  have hNr1 : 1 ≤ Nr := by rw [hNr]; nlinarith
  have hNr0 : 0 < Nr := by linarith
  have hNrX : 10 ^ 16 * X ≤ Nr := by rw [hNr]; nlinarith
  have hK : wallK k = 1200 * Nr * Nr := by rw [wallK, hN]
  have hK0 : 0 < wallK k := by rw [hK]; positivity
  have hKN : Nr ≤ wallK k := by rw [hK]; nlinarith
  have hinv : 0 < 1 / Nr := by positivity
  have hinv1 : 1 / Nr ≤ 1 := by rw [div_le_one hNr0]; exact hNr1
  -- the two squared terms
  have hsq : ∀ m : ℝ, 0 < m → 1 / m ≤ 2400 * Nr →
      (1 / (2 * (1200 * Nr * Nr) * m)) ^ 2 ≤ 1 / Nr := by
    intro m hm hmle
    have h0 : 0 ≤ 1 / (2 * (1200 * Nr * Nr) * m) := by positivity
    have h1 : 1 / (2 * (1200 * Nr * Nr) * m) ≤ 1 / Nr := by
      rw [div_le_div_iff₀ (by positivity) hNr0, one_mul, one_mul]
      have hm' : 1 ≤ 2400 * Nr * m := by
        have := (div_le_iff₀ hm).1 hmle
        linarith
      nlinarith
    calc (1 / (2 * (1200 * Nr * Nr) * m)) ^ 2 ≤ (1 / Nr) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 1 / Nr * (1 / Nr) := sq _
      _ ≤ 1 / Nr * 1 := mul_le_mul_of_nonneg_left hinv1 hinv.le
      _ = 1 / Nr := mul_one _
  have hμ0 : 0 < 1 / X := by positivity
  have hμ1 : 1 / X ≤ 1 := by rw [div_le_one hX0]; exact hX1
  -- the two time terms
  have hrate : 1 / (1200 * Nr * Nr) * (1 / (300 * Nr)) * (10 * (1200 * Nr * Nr))
      = 1 / (30 * Nr) := by
    field_simp
    ring
  have htime : ∀ (m s : ℝ), 0 < m → |s| ≤ 10 * (1200 * Nr * Nr) →
      |s| * (1 / m * (1 / (1200 * Nr * Nr) * (1 / (300 * Nr)))) ≤ 1 / m * (1 / (30 * Nr)) := by
    intro m s hm hs
    have hc : 0 ≤ 1 / m * (1 / (1200 * Nr * Nr) * (1 / (300 * Nr))) := by positivity
    calc |s| * (1 / m * (1 / (1200 * Nr * Nr) * (1 / (300 * Nr))))
        ≤ 10 * (1200 * Nr * Nr) * (1 / m * (1 / (1200 * Nr * Nr) * (1 / (300 * Nr)))) :=
          mul_le_mul_of_nonneg_right hs hc
      _ = 1 / m * (1 / (1200 * Nr * Nr) * (1 / (300 * Nr)) * (10 * (1200 * Nr * Nr))) := by
          ring
      _ = 1 / m * (1 / (30 * Nr)) := by rw [hrate]
  rw [hK] at ht ht'
  have b1 : lightBudget (wallN k) (wallN k) (1 / X) t ≤ 1 / Nr + 1 / Nr + X * (1 / (30 * Nr)) := by
    rw [lightBudget, hN]
    have s1 := hsq (1 / X) hμ0 (by rw [one_div_one_div]; nlinarith)
    have s2 := htime (1 / X) t hμ0 ht
    rw [one_div_one_div] at s2 ⊢
    linarith
  have b2 : lightBudget (wallN k) (wallN k) 1 t' ≤ 1 / Nr + 1 / Nr + 1 * (1 / (30 * Nr)) := by
    rw [lightBudget, hN]
    have s1 := hsq 1 one_pos (by rw [div_one]; nlinarith)
    have s2 := htime 1 t' one_pos ht'
    rw [div_one] at s2 ⊢
    linarith
  have hδabs : |1 / (10 ^ 5 * X)| ≤ Real.pi := by
    rw [abs_of_pos (by positivity)]
    have : 1 / (10 ^ 5 * X) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    linarith
  have hcos := sq_div_five_le_one_sub_cos hδabs
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have hsum : 4 * (1 / Nr + 1 / Nr + X * (1 / (30 * Nr)))
          + 4 * (1 / Nr + 1 / Nr + 1 * (1 / (30 * Nr)))
        ≤ 17 * X / Nr := by
      have e : 4 * (1 / Nr + 1 / Nr + X * (1 / (30 * Nr)))
            + 4 * (1 / Nr + 1 / Nr + 1 * (1 / (30 * Nr)))
          = (16 + 4 * X / 30 + 4 / 30) / Nr := by
        field_simp
        ring
      rw [e, div_le_div_iff_of_pos_right hNr0]
      linarith
    have hlow : 17 * X / Nr ≤ 1 / (1000 * X) * ((1 / (10 ^ 5 * X)) ^ 2 / 5) := by
      have e : 1 / (1000 * X) * ((1 / (10 ^ 5 * X)) ^ 2 / 5) = 1 / (5 * 10 ^ 13 * X ^ 3) := by
        field_simp
        ring
      rw [e, div_le_div_iff₀ hNr0 (by positivity), hNr]
      nlinarith [pow_pos hX0 4]
    have hmul : 1 / (1000 * X) * ((1 / (10 ^ 5 * X)) ^ 2 / 5)
        ≤ 1 / (1000 * X) * (1 - Real.cos (1 / (10 ^ 5 * X))) :=
      mul_le_mul_of_nonneg_left hcos (by positivity)
    linarith
  · rw [hK]
    have e : X / (1200 * Nr * Nr) * (4 * (1 / (10 ^ 5 * X)) * (1200 * Nr * Nr) * 20)
        = 8 / 10 ^ 4 := by
      field_simp
      ring
    rw [e]
    norm_num
  · rw [hK]
    field_simp
    ring
  · have h := one_sub_vRel_half_le (μ := 1 / X) hμ0
    have e : 2 * (1 / X) ^ 2 = 2 / X ^ 2 := by
      rw [div_pow, one_pow, mul_one_div]
    linarith
  · exact hμ0
  · exact hμ1
  · exact div_pos hX0 hK0
  · rw [hK, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hNr1 hNr0.le]

/-! ### The gate between the two clocks -/

section Clocks

variable {M : ℕ}

/-- ★★ **The two clocks near each other: little weight outside the relation.** For any two
clock rays: if each of the first clock's two angles is within `w − 2δ` of each of the
second's, the weight outside `wallNear` is at most the two clocks' weights outside their
double arcs. -/
theorem wallGate_clocks_not_le {w δ x₀ x₁ y₀ y₁ : ℝ} (hδ : 0 ≤ δ) (hw : 2 * δ ≤ w)
    (hwπ : w ≤ Real.pi) (h00 : Real.cos (w - 2 * δ) ≤ Real.cos (x₀ - y₀))
    (h01 : Real.cos (w - 2 * δ) ≤ Real.cos (x₀ - y₁))
    (h10 : Real.cos (w - 2 * δ) ≤ Real.cos (x₁ - y₀))
    (h11 : Real.cos (w - 2 * δ) ≤ Real.cos (x₁ - y₁))
    (p q : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) :
    arenaObs (coincProj (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
        (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
        fun k k' => ¬ wallNear (M + 1) w k k') (prodRay p q)
      ≤ (1 - ∑ k ∈ wallArc (M + 1) x₀ δ ∪ wallArc (M + 1) x₁ δ,
            arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k) p)
        + (1 - ∑ k ∈ wallArc (M + 1) y₀ δ ∪ wallArc (M + 1) y₁ δ,
            arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k) q) := by
  refine arenaObs_coincProj_prodRay_le_of_disjoint _ _ _ _ _ (fun k hk k' hk' hn => hn ?_) p q
  rcases Finset.mem_union.1 hk with h | h <;> rcases Finset.mem_union.1 hk' with h' | h'
  · exact wallNear_of_mem_wallArc hδ hw hwπ h00 h h'
  · exact wallNear_of_mem_wallArc hδ hw hwπ h01 h h'
  · exact wallNear_of_mem_wallArc hδ hw hwπ h10 h h'
  · exact wallNear_of_mem_wallArc hδ hw hwπ h11 h h'

/-- ★★ **The two clocks apart: little weight inside the relation.** For any two clock rays:
if each of the first clock's two angles is more than `w + 2δ` from each of the second's and
from its mirror image, the weight inside `wallNear` is at most the two clocks' weights
outside their double arcs. -/
theorem wallGate_clocks_le {w δ x₀ x₁ y₀ y₁ : ℝ} (hδ : 0 ≤ δ) (hw : 0 ≤ w)
    (hwπ : w + 2 * δ ≤ Real.pi)
    (h00 : Real.cos (x₀ - y₀) < Real.cos (w + 2 * δ))
    (h00' : Real.cos (x₀ + y₀) < Real.cos (w + 2 * δ))
    (h01 : Real.cos (x₀ - y₁) < Real.cos (w + 2 * δ))
    (h01' : Real.cos (x₀ + y₁) < Real.cos (w + 2 * δ))
    (h10 : Real.cos (x₁ - y₀) < Real.cos (w + 2 * δ))
    (h10' : Real.cos (x₁ + y₀) < Real.cos (w + 2 * δ))
    (h11 : Real.cos (x₁ - y₁) < Real.cos (w + 2 * δ))
    (h11' : Real.cos (x₁ + y₁) < Real.cos (w + 2 * δ))
    (p q : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) :
    arenaObs (coincProj (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
        (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (wallNear (M + 1) w)) (prodRay p q)
      ≤ (1 - ∑ k ∈ wallArc (M + 1) x₀ δ ∪ wallArc (M + 1) x₁ δ,
            arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k) p)
        + (1 - ∑ k ∈ wallArc (M + 1) y₀ δ ∪ wallArc (M + 1) y₁ δ,
            arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k) q) := by
  refine arenaObs_coincProj_prodRay_le_of_disjoint _ _ _ _ _ (fun k hk k' hk' => ?_) p q
  rcases Finset.mem_union.1 hk with h | h <;> rcases Finset.mem_union.1 hk' with h' | h'
  · exact not_wallNear_of_mem_wallArc hδ hw hwπ h00 h00' h h'
  · exact not_wallNear_of_mem_wallArc hδ hw hwπ h01 h01' h h'
  · exact not_wallNear_of_mem_wallArc hδ hw hwπ h10 h10' h h'
  · exact not_wallNear_of_mem_wallArc hδ hw hwπ h11 h11' h h'

end Clocks

end CSD.RecordLayer

end
