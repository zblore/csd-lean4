/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedWallBudgets
public import CsdLean4.RecordLayer.UnifiedWallGate
public import CsdLean4.RecordLayer.UnifiedStopBand

/-!
# The wall gate, open and closed, for wall states; the wall clocks' swing

**Category:** 7-SigmaLayer (the record layer). BACKLOG #411 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; of items R1 and R2 of the list
under UD-164: Remainders (a) and (b) of #410. No new assumption beyond UA-18.

#409 bounds the weights of wall states at packet times; #410 has the wall gate for any rays.
This module joins them: along the uncoupled orbits of a messenger's wall state and a clock's
wall state the weight outside (inside) the chain's coincidence relation is small while their
predicted angles are near (apart). It also gives the swing with a margin for both wall
clocks, after #396's and #400's swing theorems were generalised as #391 was in #409.

* `vRel_neg`, `chainProp_oddWall_shift`, `negWin_mem_range`, `negWin_width`,
  `sum_norm_negWin`, `icoWindow_ne_neg`, `chainInner_icoWall`;
* ★★ `one_sub_sum_arenaObs_wallArc_icoWall_le` — along the uncoupled orbit of a flat
  messenger wall state, the occupancy outside the double arc about its predicted angle,
  times `1 − cos δ`, is at most `4 (1/N + 1/(20000 Δ n N))`;
* ★★ `one_sub_sum_arenaObs_wallArcs_icoDevice_le` — the same for a flat clock wall state and
  its two double arcs;
* ★★★ `wall_gate_open`, ★★★ `wall_gate_closed` — the weight outside (inside) `wallNear`, times
  `1 − cos δ`, is at most `8 (1/N + 1/(20000 Δ n N))` while the messenger's angle is within
  `w − 2δ` of both levels' angles (more than `w + 2δ` from them and from their mirror
  images);
* `wallSym_range`, `wallSym_width`, ★★ `wall_clock_swing_fine` — the clock at rest beside the
  wall swings within `1/(24 j)` up to `2π n/(j R)`;
* `flatSym_range`, `flatSym_width`, ★★ `wall_moving_clock_swing_fine` — the same for the
  moving clock's wall state.

## Exact scope

* **Two of the three hypotheses of #394, and the swing, separately.** `wall_gate_open` and
  `wall_gate_closed` are the hypotheses `hopen` and `hclosed` of the history theorems for a
  messenger and one clock on the walled chain; the swing theorems are their hypothesis on the
  clock's own reading. They are not combined: no history, count or reading is stated here.
* **The messenger is slow.** Its packet has momenta within `1/(600 n)` of `|p₀| ≤ 1/2` and
  rest energy `μ ≥ 1`, so its velocity is at most about `0.45`. The top-down statement
  (UD-164) is exact only for a messenger at speed `1`; a slower one enters its tolerances.
  A fast messenger with these budgets is not exhibited; that is the open question of R3.
* **Angles, not times.** The conditions are on predicted angles at a flow time; no flow time
  at which they hold is exhibited.
* **Uncoupled orbits**, from a product start on the fibres where the profiles vanish
  (#393). Null sets (R7).
* **A messenger and one clock.** The gate between the two clocks is not stated.
* **The odd sector of the ring**, as #407.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-148, UD-151, UD-159, UD-164, UD-170, UD-176, UD-177, UD-178, UD-179,
UD-180); `RecordLayer/UnifiedWallBudgets.lean` (#409: `regionWeight_icoWall_away_le`,
`deviceRegionWeight_icoWall_away_le`); `RecordLayer/UnifiedWallGate.lean` (#410: `wallNear`,
`wallArc`, `wallGate_not_le`, `wallGate_le`); `RecordLayer/UnifiedGateRegions.lean` (#395:
`one_sub_sum_arenaObs_siteSel`, `sum_arenaObs_siteSel_free_chainRay`,
`sum_arenaObs_siteSel_free_deviceRay`, `flat_gate_open`); `RecordLayer/UnifiedStopBand.lean`
(#400: `narrow_clock_packet_swing_fine`); `RecordLayer/UnifiedOddWall.lean` (#407:
`oddWall`, `chainProp_oddWall`, `chainInner_oddWall`,
`chainInner_ringPacket_mirrorPacket`); `CV/DiracPacketLimit.lean` (`dirac_packet_limit`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### Helpers -/

/-- The relativistic velocity is odd in the momentum term. -/
theorem vRel_neg (c μ s : ℝ) : vRel c μ (-s) = -vRel c μ s := by
  rw [vRel, vRel, dispE_neg]
  ring

section Helpers

variable {L : ℕ} [NeZero L]

/-- The ring's evolution carries a wall state from any packet time to the later one. -/
theorem chainProp_oddWall_shift (c μ ℓ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (t₀ s : ℝ) :
    chainProp (L := L) (scaledHop c (ℓ / L)) μ s *ᵥ oddWall c μ ℓ W β t₀
      = oddWall c μ ℓ W β (t₀ + s) := by
  rw [← chainProp_oddWall c μ ℓ W β t₀, ← chainProp_oddWall c μ ℓ W β (t₀ + s),
    Matrix.mulVec_mulVec, chainProp_add]

omit [NeZero L] in
theorem negWin_mem_range {W : Finset ℤ} {lo : ℤ} (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L) :
    ∀ m ∈ negWin W, (2 - lo - L : ℤ) ≤ m ∧ m + 1 < (2 - lo - L : ℤ) + L := by
  intro m hm
  obtain ⟨h1, h2⟩ := hWin (-m) ((mem_negWin W m).1 hm)
  constructor <;> omega

theorem negWin_width {W : Finset ℤ} {ℓ p₀ D : ℝ}
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D) :
    ∀ m ∈ negWin W, |2 * Real.pi * m / ℓ - -p₀| ≤ D := by
  intro m hm
  have h := hWD (-m) ((mem_negWin W m).1 hm)
  rw [show 2 * Real.pi * (m : ℝ) / ℓ - -p₀
      = -(2 * Real.pi * ((-m : ℤ) : ℝ) / ℓ - p₀) by push_cast; ring, abs_neg]
  exact h

theorem sum_norm_negWin {W : Finset ℤ} {β : ℤ → ℂ} (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) :
    ∑ m ∈ negWin W, ‖β (-m)‖ ^ 2 = 1 := by
  rw [negWin, Finset.sum_image (fun x _ y _ h => neg_injective h)]
  simpa using hβ

end Helpers

section Orbits

variable {n N M : ℕ}

/-- No mode of a window of positive modes, short against the ring, is the opposite of another
modulo the ring. -/
theorem icoWindow_ne_neg {lo : ℤ} (hlo : 0 < lo) (hhi : 2 * (lo + N) ≤ M) :
    ∀ m ∈ Finset.Ico lo (lo + N), ∀ m' ∈ Finset.Ico lo (lo + N),
      (m : ZMod (M + 1)) ≠ ((-m' : ℤ) : ZMod (M + 1)) := by
  intro m hm m' hm' heq
  rw [Finset.mem_Ico] at hm hm'
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at heq
  obtain ⟨k, hk⟩ := heq
  push_cast at hk
  have hM0 : (0 : ℤ) ≤ (M : ℤ) + 1 := by positivity
  rcases lt_or_ge k 0 with h | h
  · have hk1 : k ≤ -1 := by omega
    nlinarith [mul_le_mul_of_nonneg_left hk1 hM0]
  · nlinarith [mul_nonneg hM0 h]

/-- A window of positive modes, short against the ring, lies in a window of the ring. -/
theorem icoWindow_mem_range {lo : ℤ} (hlo : 0 < lo) (hhi : 2 * (lo + N) ≤ M) :
    ∀ m ∈ Finset.Ico lo (lo + N), (0 : ℤ) ≤ m ∧ m + 1 < (0 : ℤ) + ((M + 1 : ℕ) : ℤ) := by
  intro m hm
  rw [Finset.mem_Ico] at hm
  refine ⟨by omega, ?_⟩
  push_cast
  omega

/-- **A flat wall state on positive modes is normalised**, at every packet time. -/
theorem chainInner_icoWall (hn : 0 < n) (hN : 0 < N) {μ : ℝ} (hμ : 0 < μ) {lo : ℤ}
    (hlo : 0 < lo) (hhi : 2 * (lo + N) ≤ M) {p₀ : ℝ} (hp₀ : |p₀| ≤ 1 / 2)
    (hWD : ∀ m ∈ Finset.Ico lo (lo + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - p₀| ≤ 1 / (600 * n)) (t : ℝ) :
    chainInner (oddWall (L := M + 1) 1 μ (ringLen (1200 * n * N)) (Finset.Ico lo (lo + N))
        (flatAmpN N) t)
      (oddWall (L := M + 1) 1 μ (ringLen (1200 * n * N)) (Finset.Ico lo (lo + N))
        (flatAmpN N) t) = 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : 0 < 1200 * n * N := by positivity
  have hWin := icoWindow_mem_range (M := M) hlo hhi
  have hR1 := (dirac_packet_limit (L := M + 1) (c := 1) (P := 1 / 2) (D := 1 / (600 * n))
    one_pos hμ (ringLen_pos hK) hp₀ (by positivity) hWin hWD (flatAmpN N)
    (sum_norm_flatAmpN_Ico lo hN)).1 t
  have hM1 : chainInner
      (mirrorPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) (Finset.Ico lo (lo + N))
        (flatAmpN N) t)
      (mirrorPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) (Finset.Ico lo (lo + N))
        (flatAmpN N) t) = 1 :=
    (dirac_packet_limit (L := M + 1) (c := 1) (P := 1 / 2) (D := 1 / (600 * n))
      (p₀ := -p₀) one_pos hμ (ringLen_pos hK) (by rw [abs_neg]; exact hp₀) (by positivity)
      (negWin_mem_range hWin) (negWin_width hWD) (fun m => flatAmpN N (-m))
      (sum_norm_negWin (sum_norm_flatAmpN_Ico lo hN))).1 t
  exact chainInner_oddWall
    (chainInner_ringPacket_mirrorPacket 1 μ _ (icoWindow_ne_neg hlo hhi) (flatAmpN N) t)
    hR1 hM1

/-- ★★ **A flat messenger wall state stays in the double arc about its predicted angle.**
Along the uncoupled orbit from the packet time `t₀`, at the flow time `s` with
`|t₀ + s| ≤ 4π n/Δ`: the occupancy outside the double arc of half-angle `δ` about
`Ω (t₀ + s)`, `Ω = v(p₀)/K`, times `1 − cos δ`, is at most `4 (1/N + 1/(20000 Δ n N))`. -/
theorem one_sub_sum_arenaObs_wallArc_icoWall_le (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {μ : ℝ} (hμ : 1 ≤ μ) {Δ : ℝ} (hΔ0 : 0 < Δ)
    (hΔ : Δ ≤ 1 / 2) {lo : ℤ} (hlo : 0 < lo) (hhi : 2 * (lo + N) ≤ M) {p₀ : ℝ}
    (hp₀ : |p₀| ≤ 1 / 2)
    (hWD : ∀ m ∈ Finset.Ico lo (lo + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - p₀| ≤ 1 / (600 * n)) (t₀ : ℝ)
    (hψ : oddWall (L := M + 1) 1 μ (ringLen (1200 * n * N)) (Finset.Ico lo (lo + N))
      (flatAmpN N) t₀ ≠ 0) {δ s : ℝ} (hδ : Real.cos δ < 1)
    (ht : |t₀ + s| ≤ 4 * Real.pi * n / Δ) :
    (1 - ∑ k ∈ wallArc (M + 1)
          (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 * p₀) * (t₀ + s)) δ,
        arenaObs (siteSel (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1)) k)
          (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))) * (1 - Real.cos δ)
      ≤ 4 * (1 / N + 1 / (20000 * Δ * n * N)) := by
  have hnorm := chainInner_icoWall (M := M) hn hN (by linarith : 0 < μ) hlo hhi hp₀ hWD t₀
  unfold ringHop
  rw [one_sub_sum_arenaObs_siteSel, sum_arenaObs_siteSel_free_chainRay, hnorm, Complex.one_re,
    div_one, chainProp_oddWall_shift]
  refine regionWeight_icoWall_away_le hn hN hM hμ hΔ0 hΔ hp₀ (icoWindow_mem_range hlo hhi)
    hWD hδ ht (fun k hk => ?_) (fun k hk => ?_)
  · rw [Finset.mem_compl, mem_wallArc, not_or, mem_ringArc, not_lt] at hk
    exact hk.1
  · rw [Finset.mem_compl, mem_wallArc, not_or, mem_ringArc, mem_ringArc, not_lt, not_lt] at hk
    rw [show 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 * -p₀) * (t₀ + s)
        = -(2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 * p₀) * (t₀ + s)) by
      rw [mul_neg, vRel_neg]; ring]
    exact hk.2

/-- ★★ **A flat clock wall state stays in the two double arcs about its levels' predicted
angles.** Along the uncoupled orbit from the packet time `t₁`, at the flow time `s` with
`|t₁ + s| ≤ 4π n/Δ`: the occupancy outside the two double arcs of half-angle `δ`, times
`1 − cos δ`, is at most `4 (1/N + 1/(20000 Δ n N))`. -/
theorem one_sub_sum_arenaObs_wallArcs_icoDevice_le (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2) {lo : ℤ}
    (hlo : 0 < lo) (hhi : 2 * (lo + N) ≤ M) {p₀ : ℝ} (hp₀ : |p₀| ≤ 1 / 2)
    (hWD : ∀ m ∈ Finset.Ico lo (lo + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - p₀| ≤ 1 / (600 * n)) (t₁ : ℝ)
    (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
      (Finset.Ico lo (lo + N) ∪ negWin (Finset.Ico lo (lo + N)))
      (oddExt (Finset.Ico lo (lo + N)) (flatAmpN N)) t₁ ≠ 0) {δ s : ℝ}
    (hδ : Real.cos δ < 1) (ht : |t₁ + s| ≤ 4 * Real.pi * n / Δ) :
    (1 - ∑ k ∈ wallArc (M + 1)
            (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 1 (1 * p₀) * (t₁ + s)) δ
          ∪ wallArc (M + 1)
            (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 (1 + Δ) (1 * p₀) * (t₁ + s)) δ,
        arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k)
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ))) * (1 - Real.cos δ)
      ≤ 4 * (1 / N + 1 / (20000 * Δ * n * N)) := by
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
  refine deviceRegionWeight_icoWall_away_le hn hN hM hΔ0 hΔ hp₀ hW (icoWindow_mem_range hlo hhi)
    hWD hδ ht (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_)
  all_goals
    rw [Finset.mem_compl, Finset.mem_union, not_or, mem_wallArc, mem_wallArc, not_or, not_or,
      mem_ringArc, mem_ringArc, mem_ringArc, mem_ringArc, not_lt, not_lt, not_lt, not_lt] at hk
  · exact hk.1.1
  · rw [hneg]
    exact hk.1.2
  · exact hk.2.1
  · rw [hneg]
    exact hk.2.2

/-- ★★★ **The wall gate is open while the messenger is near the clock.** A flat messenger
wall state and a flat clock wall state on the walled chain, at a flow time `s` with both
packet times within `4π n/Δ`. If the messenger's predicted angle is within `w − 2δ` of both
levels' predicted angles: (weight outside `wallNear w`) `· (1 − cos δ)` is at most
`8 (1/N + 1/(20000 Δ n N))`. -/
theorem wall_gate_open (hn : 0 < n) (hN : 0 < N) (hM : 210000 * n ^ 2 * N ≤ M) {μ : ℝ}
    (hμ : 1 ≤ μ) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2) {lo lc : ℤ} (hlo : 0 < lo)
    (hhi : 2 * (lo + N) ≤ M) (hlc : 0 < lc) (hhc : 2 * (lc + N) ≤ M) {p₀ q₀ : ℝ}
    (hp₀ : |p₀| ≤ 1 / 2) (hq₀ : |q₀| ≤ 1 / 2)
    (hWD : ∀ m ∈ Finset.Ico lo (lo + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - p₀| ≤ 1 / (600 * n))
    (hWDc : ∀ m ∈ Finset.Ico lc (lc + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - q₀| ≤ 1 / (600 * n)) (t₀ t₁ : ℝ)
    (hψ : oddWall (L := M + 1) 1 μ (ringLen (1200 * n * N)) (Finset.Ico lo (lo + N))
      (flatAmpN N) t₀ ≠ 0)
    (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
      (Finset.Ico lc (lc + N) ∪ negWin (Finset.Ico lc (lc + N)))
      (oddExt (Finset.Ico lc (lc + N)) (flatAmpN N)) t₁ ≠ 0) {w δ s : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : Real.cos δ < 1) (hw : 2 * δ ≤ w) (hwπ : w ≤ Real.pi)
    (ht₀ : |t₀ + s| ≤ 4 * Real.pi * n / Δ) (ht₁ : |t₁ + s| ≤ 4 * Real.pi * n / Δ)
    (h0 : Real.cos (w - 2 * δ)
      ≤ Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 * p₀) * (t₀ + s)
          - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 1 (1 * q₀) * (t₁ + s)))
    (h1 : Real.cos (w - 2 * δ)
      ≤ Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 * p₀) * (t₀ + s)
          - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 (1 + Δ) (1 * q₀) * (t₁ + s))) :
    arenaObs (coincProj (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
          (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1)
          fun k k' => ¬ wallNear (M + 1) w k k')
        (prodRay
          (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ)))
        * (1 - Real.cos δ)
      ≤ 8 * (1 / N + 1 / (20000 * Δ * n * N)) := by
  have hpos : 0 ≤ 1 - Real.cos δ := by linarith
  have g := mul_le_mul_of_nonneg_right (wallGate_not_le hδ0 hw hwπ h0 h1
    (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
      (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))
    (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
      (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ))) hpos
  have a := one_sub_sum_arenaObs_wallArc_icoWall_le hn hN hM hμ hΔ0 hΔ hlo hhi hp₀ hWD t₀ hψ
    hδ ht₀
  have b := one_sub_sum_arenaObs_wallArcs_icoDevice_le hn hN hM hΔ0 hΔ hlc hhc hq₀ hWDc t₁ hΨ
    hδ ht₁
  rw [add_mul] at g
  linarith

/-- ★★★ **The wall gate is closed while the messenger is away from the clock.** As
`wall_gate_open`, at a flow time at which the messenger's predicted angle is more than
`w + 2δ` from both levels' predicted angles and from their mirror images: (weight inside
`wallNear w`) `· (1 − cos δ)` is at most `8 (1/N + 1/(20000 Δ n N))`. -/
theorem wall_gate_closed (hn : 0 < n) (hN : 0 < N) (hM : 210000 * n ^ 2 * N ≤ M) {μ : ℝ}
    (hμ : 1 ≤ μ) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2) {lo lc : ℤ} (hlo : 0 < lo)
    (hhi : 2 * (lo + N) ≤ M) (hlc : 0 < lc) (hhc : 2 * (lc + N) ≤ M) {p₀ q₀ : ℝ}
    (hp₀ : |p₀| ≤ 1 / 2) (hq₀ : |q₀| ≤ 1 / 2)
    (hWD : ∀ m ∈ Finset.Ico lo (lo + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - p₀| ≤ 1 / (600 * n))
    (hWDc : ∀ m ∈ Finset.Ico lc (lc + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - q₀| ≤ 1 / (600 * n)) (t₀ t₁ : ℝ)
    (hψ : oddWall (L := M + 1) 1 μ (ringLen (1200 * n * N)) (Finset.Ico lo (lo + N))
      (flatAmpN N) t₀ ≠ 0)
    (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
      (Finset.Ico lc (lc + N) ∪ negWin (Finset.Ico lc (lc + N)))
      (oddExt (Finset.Ico lc (lc + N)) (flatAmpN N)) t₁ ≠ 0) {w δ s : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : Real.cos δ < 1) (hw : 0 ≤ w) (hwπ : w + 2 * δ ≤ Real.pi)
    (ht₀ : |t₀ + s| ≤ 4 * Real.pi * n / Δ) (ht₁ : |t₁ + s| ≤ 4 * Real.pi * n / Δ)
    (h0 : Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 * p₀) * (t₀ + s)
          - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 1 (1 * q₀) * (t₁ + s))
      < Real.cos (w + 2 * δ))
    (h0' : Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 * p₀) * (t₀ + s)
          + 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 1 (1 * q₀) * (t₁ + s))
      < Real.cos (w + 2 * δ))
    (h1 : Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 * p₀) * (t₀ + s)
          - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 (1 + Δ) (1 * q₀) * (t₁ + s))
      < Real.cos (w + 2 * δ))
    (h1' : Real.cos (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 * p₀) * (t₀ + s)
          + 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 (1 + Δ) (1 * q₀) * (t₁ + s))
      < Real.cos (w + 2 * δ)) :
    arenaObs (coincProj (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1))
          (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) (wallNear (M + 1) w))
        (prodRay
          (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ)))
        * (1 - Real.cos δ)
      ≤ 8 * (1 / N + 1 / (20000 * Δ * n * N)) := by
  have hpos : 0 ≤ 1 - Real.cos δ := by linarith
  have g := mul_le_mul_of_nonneg_right (wallGate_le hδ0 hw hwπ h0 h0' h1 h1'
    (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
      (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))
    (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
      (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ))) hpos
  have a := one_sub_sum_arenaObs_wallArc_icoWall_le hn hN hM hμ hΔ0 hΔ hlo hhi hp₀ hWD t₀ hψ
    hδ ht₀
  have b := one_sub_sum_arenaObs_wallArcs_icoDevice_le hn hN hM hΔ0 hΔ hlc hhc hq₀ hWDc t₁ hΨ
    hδ ht₁
  rw [add_mul] at g
  linarith

end Orbits

/-! ### The wall clocks' swing -/

section Swing

variable {n N M : ℕ}

/-- The modes `±1, …, ±N` lie in a window of the ring. -/
theorem wallSym_range (hn : 0 < n) (hM : 210000 * n ^ 2 * N ≤ M) :
    ∀ m ∈ wallWindow N ∪ negWin (wallWindow N),
      (-N : ℤ) ≤ m ∧ m + 1 < (-N : ℤ) + ((M + 1 : ℕ) : ℤ) := by
  have h3 : 3 * N ≤ M := by
    have h1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
    have h2 : 3 * N ≤ 210000 * n ^ 2 * N := Nat.mul_le_mul_right N (by nlinarith)
    exact h2.trans hM
  have hz : (3 * N : ℤ) ≤ M := by exact_mod_cast h3
  intro m hm
  rcases Finset.mem_union.1 hm with h | h
  · rw [wallWindow, Finset.mem_Ico] at h
    refine ⟨by omega, ?_⟩
    push_cast
    omega
  · have h' := (mem_negWin _ m).1 h
    rw [wallWindow, Finset.mem_Ico] at h'
    refine ⟨by omega, ?_⟩
    push_cast
    omega

/-- The modes `±1, …, ±N` have momenta within `1/(600 n)` of `0`. -/
theorem wallSym_width (hn : 0 < n) (hN : 0 < N) :
    ∀ m ∈ wallWindow N ∪ negWin (wallWindow N),
      |(m : ℝ) / ((1200 * n * N : ℕ) : ℝ) - 0| ≤ 1 / (600 * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  intro m hm
  have hb : (-N : ℤ) ≤ m ∧ m ≤ N := by
    rcases Finset.mem_union.1 hm with h | h
    · rw [wallWindow, Finset.mem_Ico] at h
      constructor <;> omega
    · have h' := (mem_negWin _ m).1 h
      rw [wallWindow, Finset.mem_Ico] at h'
      constructor <;> omega
  have h1' : (-(N : ℝ)) ≤ m := by exact_mod_cast hb.1
  have h2' : (m : ℝ) ≤ N := by exact_mod_cast hb.2
  have habs : |(m : ℝ)| ≤ N := abs_le.2 ⟨h1', h2'⟩
  have hden : (0 : ℝ) < 1200 * n * N := by positivity
  push_cast
  rw [sub_zero, abs_div, abs_of_pos hden, div_le_div_iff₀ hden (by positivity)]
  nlinarith [abs_nonneg (m : ℝ)]

/-- ★★ **The clock at rest beside the wall swings, with a margin.** For the clock of
`wall_clock_ticks` and `1 ≤ j ≤ n`: for some strength `0 < g ≤ R/5` the pointer's displacement
is within `1/(24 j)` of `(1/4)(1 − cos R t)` up to `2π n/(j R)`, `R` the rate at momentum
`0`. -/
theorem wall_clock_swing_fine {j : ℕ} (hj : 0 < j) (hjn : j ≤ n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2) :
    ∃ (g : ℝ) (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
          (wallWindow N ∪ negWin (wallWindow N)) (oddExt (wallWindow N) (flatAmpN N))
          (-(Real.pi / (2 * ringRate (1200 * n * N) M 0 Δ))) ≠ 0),
      0 < g ∧ g ≤ ringRate (1200 * n * N) M 0 Δ / 5
      ∧ ∀ t, 0 ≤ t → t ≤ 2 * Real.pi * n / (j * ringRate (1200 * n * N) M 0 Δ) →
        |clockPointerShift (ringHop (1200 * n * N) M) 1 (1 + Δ) g trainF_periodic
              (0 : AddCircle (1 : ℝ)) (deviceRay _ hΨ) t
            - 1 / 4 * (1 - Real.cos (ringRate (1200 * n * N) M 0 Δ * t))|
          ≤ 1 / (24 * j) := by
  have hn : 0 < n := hj.trans_le hjn
  exact narrow_clock_packet_swing_fine (lo := -N) (p₀ := 0) hj hjn (by positivity) le_rfl
    (by norm_num) (wallSym_range hn hM) (fun m hm => Or.inl (wallSym_width hn hN m hm))
    (oddExt (wallWindow N) (flatAmpN N))
    (sum_norm_oddExt (wallWindow_neg_notMem N) (sum_norm_flatAmpN_wall hN)) hΔ0 hΔ

/-- The flat window and its reflection lie in a window of the ring. -/
theorem flatSym_range (hn : 0 < n) (hN : 0 < N) (hM : 210000 * n ^ 2 * N ≤ M) :
    ∀ m ∈ flatWindow n N ∪ negWin (flatWindow n N),
      (-(600 * (n : ℤ) * N + N)) ≤ m
        ∧ m + 1 < (-(600 * (n : ℤ) * N + N)) + ((M + 1 : ℕ) : ℤ) := by
  have hMz : (210000 : ℤ) * n ^ 2 * N ≤ M := by exact_mod_cast hM
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hN1 : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℤ) ≤ N := Int.natCast_nonneg N
  have hnN : (0 : ℤ) ≤ n * N := by positivity
  have hsq : (n : ℤ) * N ≤ n ^ 2 * N := by nlinarith
  have hNle : (N : ℤ) ≤ n * N := by nlinarith
  intro m hm
  have hb : (-(600 * (n : ℤ) * N + N)) ≤ m ∧ m ≤ 600 * (n : ℤ) * N + N := by
    rcases Finset.mem_union.1 hm with h | h
    · rw [flatWindow, Finset.mem_Ico] at h
      constructor <;> nlinarith [h.1, h.2]
    · have h' := (mem_negWin _ m).1 h
      rw [flatWindow, Finset.mem_Ico] at h'
      constructor <;> nlinarith [h'.1, h'.2]
  refine ⟨hb.1, ?_⟩
  push_cast
  linarith [hb.2]

/-- The flat window and its reflection have momenta within `1/(600 n)` of `1/2` or of
`−1/2`. -/
theorem flatSym_width (hn : 0 < n) (hN : 0 < N) :
    ∀ m ∈ flatWindow n N ∪ negWin (flatWindow n N),
      |(m : ℝ) / ((1200 * n * N : ℕ) : ℝ) - 1 / 2| ≤ 1 / (600 * n)
        ∨ |(m : ℝ) / ((1200 * n * N : ℕ) : ℝ) + 1 / 2| ≤ 1 / (600 * n) := by
  intro m hm
  rcases Finset.mem_union.1 hm with h | h
  · exact Or.inl (flatWindow_width hn hN m h)
  · right
    have h' := flatWindow_width hn hN (-m) ((mem_negWin _ m).1 h)
    rw [show (m : ℝ) / ((1200 * n * N : ℕ) : ℝ) + 1 / 2
        = -((((-m : ℤ)) : ℝ) / ((1200 * n * N : ℕ) : ℝ) - 1 / 2) by push_cast; ring, abs_neg]
    exact h'

/-- ★★ **The moving clock's wall state swings, with a margin.** For the clock of
`wall_moving_clock_ticks` and `1 ≤ j ≤ n`: for some strength `0 < g ≤ R/5` the pointer's
displacement is within `1/(24 j)` of `(1/4)(1 − cos R t)` up to `2π n/(j R)`, `R` the rate
at momentum `1/2`. -/
theorem wall_moving_clock_swing_fine {j : ℕ} (hj : 0 < j) (hjn : j ≤ n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2) :
    ∃ (g : ℝ) (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
          (flatWindow n N ∪ negWin (flatWindow n N)) (oddExt (flatWindow n N) (flatAmpN N))
          (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ))) ≠ 0),
      0 < g ∧ g ≤ ringRate (1200 * n * N) M (1 / 2) Δ / 5
      ∧ ∀ t, 0 ≤ t → t ≤ 2 * Real.pi * n / (j * ringRate (1200 * n * N) M (1 / 2) Δ) →
        |clockPointerShift (ringHop (1200 * n * N) M) 1 (1 + Δ) g trainF_periodic
              (0 : AddCircle (1 : ℝ)) (deviceRay _ hΨ) t
            - 1 / 4 * (1 - Real.cos (ringRate (1200 * n * N) M (1 / 2) Δ * t))|
          ≤ 1 / (24 * j) := by
  have hn : 0 < n := hj.trans_le hjn
  exact narrow_clock_packet_swing_fine (lo := -(600 * (n : ℤ) * N + N)) (p₀ := 1 / 2) hj hjn
    (by positivity) (by norm_num) (by norm_num) (flatSym_range hn hN hM) (flatSym_width hn hN)
    (oddExt (flatWindow n N) (flatAmpN N))
    (sum_norm_oddExt (flatWindow_neg_notMem hn hN) (sum_norm_flatAmpN n hN)) hΔ0 hΔ

end Swing

end CSD.RecordLayer

end
