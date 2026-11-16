/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedWallOrbits
public import CsdLean4.RecordLayer.UnifiedRadarTimes
public import CsdLean4.RecordLayer.UnifiedEmissionValues

/-!
# A fast messenger on the walled chain

**Category:** 7-SigmaLayer (the record layer). BACKLOG #413 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; of item R2 of the list under
UD-164: Remainder (a) of #411. No new assumption beyond UA-18.

#412 shows that the messenger of M6 must have `μ²/p²` small against `v²`, and that the
messenger of #411 (rest energy `μ ≥ 1`) does not. The budgets of #392 and #409 were stated
for `μ ≥ 1`. This module restates them for `0 < μ ≤ 1`, where they grow like `1/μ` and
`1/μ²`, and carries the wall state and the wall gate through for such a messenger.

* `light_packet_start_le`, `lightBudget`, ★ `light_packet_budget` — a flat packet on any `N`
  neighbouring modes, rest energy `0 < μ ≤ 1`: the budget at the packet time `t` is at most
  `1/N + 1/(2 K μ)² + |t|/(μ · 300 n K)`, `K = 1200 n N`;
* ★★ `regionWeight_lightWall_away_le` — its wall state: weight away from the two mirror
  directions, times `1 − γ`, at most `4 · lightBudget`;
* ★★ `one_sub_sum_arenaObs_wallArc_lightWall_le` — the same as an occupancy along the orbit;
* ★★★ `light_wall_gate_open`, ★★★ `light_wall_gate_closed` — the wall gate between that
  messenger and a flat clock wall state: the bound is `4 · lightBudget` for the messenger
  plus `4 (1/N + 1/(20000 Δ n N))` for the clock;
* ★★ `one_sub_vRel_half_le` — at the momentum `1/2` the messenger's velocity is within `2μ²`
  of `1`.

## Exact scope

* **The price of speed is explicit and is not yet paid.** With `μ` small the messenger is
  fast (`1 − u ≤ 2μ²`) and its budget carries `1/(2Kμ)²` and `|t|/(μ · 300 n K)`. Whether
  one choice of `n`, `N`, `μ`, `Δ`, `δ`, `w` makes the budget small against `1 − cos δ`,
  the gate's closing short against a tick, and `μ²` small against `v²` together is R6. No
  values are exhibited here.
* **Momentum at most `1/2`.** The lattice error of #261 is stated for `|p₀| ≤ P = 1/2`; a
  messenger made fast by a larger momentum is not treated.
* **Weights along uncoupled orbits, conditions on angles, a messenger and one clock**, as
  #411. No flow time, history, count or reading.
* **The odd sector of the ring**, as #407.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-164, UD-176, UD-179, UD-181, UD-182);
`RecordLayer/UnifiedWallOrbits.lean` (#411: `chainInner_icoWall`,
`one_sub_sum_arenaObs_wallArcs_icoDevice_le`, `wall_gate_open`);
`RecordLayer/UnifiedWallBudgets.lean` (#409: `ico_packet_start_le`, `mirror_ico_mem_range`,
`negWin_Ico`); `RecordLayer/UnifiedWallObservers.lean` (#408:
`regionWeight_oddWall_away_le`); `RecordLayer/UnifiedRadarTimes.lean` (#412:
`one_sub_vRel_le`); `RecordLayer/UnifiedClockPacketLocalised.lean` (#392:
`flat_packet_limitErr_le`); `RecordLayer/UnifiedEmissionValues.lean` (#397: `limitErr_le_inv_mul`,
`flat_messenger_budget`, the same budget for the window of #392);
`RecordLayer/DiracArrival.lean` (#265:
`re_transPhase_ringPacket_ge`); `CV/DiracPacketLimit.lean` (#261: `limitErr`, `flat_sums`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### The budgets at small rest energy -/

section Light

variable {n N M : ℕ} {lo lo₁ : ℤ}

/-- **A flat packet of any rest energy starts localised**:
`1 − Re T(0) ≤ 1/N + (1/(2 K μ))²`, `K = 1200 n N`. -/
theorem light_packet_start_le (hn : 0 < n) (hN : 0 < N)
    (hWin : ∀ m ∈ Finset.Ico lo (lo + N), lo₁ ≤ m ∧ m + 1 < lo₁ + ((M + 1 : ℕ) : ℤ))
    {μ : ℝ} (hμ0 : 0 < μ) :
    1 - (transPhase (ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N))
          (Finset.Ico lo (lo + N)) (flatAmpN N) 0)).re
      ≤ 1 / N + (1 / (2 * (1200 * (n : ℝ) * N) * μ)) ^ 2 := by
  have hπ := Real.pi_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hK : 0 < 1200 * n * N := by positivity
  have hKr : ((1200 * n * N : ℕ) : ℝ) = 1200 * n * N := by push_cast; ring
  have hK0 : (0 : ℝ) < 1200 * n * N := by positivity
  have hLen : ringLen (1200 * n * N) = 2 * Real.pi * (1200 * n * N) := by rw [ringLen, hKr]
  obtain ⟨hW, -⟩ := noWrap_distinct_of_window (L := M + 1) hWin
  have hRe := re_transPhase_ringPacket_ge (L := M + 1) (c := 1) (μ := μ)
    (ℓ := ringLen (1200 * n * N)) hμ0 (ringLen_pos hK) hW
    (fun _ => 1 / Real.sqrt N) (fun _ => by positivity)
  rw [(flat_sums lo hN).2] at hRe
  have he : Real.pi * 1 / (ringLen (1200 * n * N) * μ) = 1 / (2 * (1200 * n * N) * μ) := by
    rw [hLen]
    field_simp
  rw [he] at hRe
  have hesq0 : 0 ≤ (1 / (2 * (1200 * (n : ℝ) * N) * μ)) ^ 2 := sq_nonneg _
  have hinvN0 : 0 ≤ 1 / (N : ℝ) := by positivity
  have hprod : (1 / (2 * (1200 * (n : ℝ) * N) * μ)) ^ 2 * (1 - 1 / (N : ℝ))
      ≤ (1 / (2 * (1200 * (n : ℝ) * N) * μ)) ^ 2 := by
    calc (1 / (2 * (1200 * (n : ℝ) * N) * μ)) ^ 2 * (1 - 1 / (N : ℝ))
        ≤ (1 / (2 * (1200 * (n : ℝ) * N) * μ)) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) hesq0
      _ = (1 / (2 * (1200 * (n : ℝ) * N) * μ)) ^ 2 := mul_one _
  have hexp : (1 - (1 / (2 * (1200 * (n : ℝ) * N) * μ)) ^ 2) * (1 - 1 / (N : ℝ))
      = 1 - 1 / (N : ℝ)
        - (1 / (2 * (1200 * (n : ℝ) * N) * μ)) ^ 2 * (1 - 1 / (N : ℝ)) := by ring
  rw [hexp] at hRe
  unfold flatAmpN
  linarith

/-- **The budget of a light flat packet** at the packet time `t`:
`1/N + (1/(2 K μ))² + |t| · (1/μ) · 1/(300 n K)`, `K = 1200 n N`. -/
def lightBudget (n N : ℕ) (μ t : ℝ) : ℝ :=
  1 / N + (1 / (2 * (1200 * (n : ℝ) * N) * μ)) ^ 2
    + |t| * (1 / μ * (1 / (1200 * (n : ℝ) * N) * (1 / (300 * n))))

/-- ★ **The budget of a flat packet of rest energy `0 < μ ≤ 1`**, on any `N` neighbouring
modes, at every packet time. -/
theorem light_packet_budget (hn : 0 < n) (hN : 0 < N) (hM : 210000 * n ^ 2 * N ≤ M)
    (hWin : ∀ m ∈ Finset.Ico lo (lo + N), lo₁ ≤ m ∧ m + 1 < lo₁ + ((M + 1 : ℕ) : ℤ))
    {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (t : ℝ) :
    1 - (transPhase (ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N))
          (Finset.Ico lo (lo + N)) (flatAmpN N) 0)).re
      + |t| * limitErr 1 μ (ringLen (1200 * n * N)) (1 / (600 * n)) (1 / 2)
          (ringLen (1200 * n * N) / (M + 1 : ℕ))
      ≤ lightBudget n N μ t := by
  have hK : 0 < 1200 * n * N := by positivity
  have hstart := light_packet_start_le (M := M) hn hN hWin hμ0
  have hrate1 := (flat_packet_limitErr_le hn hN hM (μ := 1) le_rfl).2
  have hrate := limitErr_le_inv_mul (D := 1 / (600 * (n : ℝ))) (P := 1 / 2)
    (a := ringLen (1200 * n * N) / ((M + 1 : ℕ) : ℝ)) hμ0 hμ1 (ringLen_pos hK)
  have hinv : 0 ≤ 1 / μ := by positivity
  have hrate' : limitErr 1 μ (ringLen (1200 * n * N)) (1 / (600 * n)) (1 / 2)
        (ringLen (1200 * n * N) / (M + 1 : ℕ))
      ≤ 1 / μ * (1 / (1200 * (n : ℝ) * N) * (1 / (300 * n))) :=
    hrate.trans (mul_le_mul_of_nonneg_left hrate1 hinv)
  have hdrift := mul_le_mul_of_nonneg_left hrate' (abs_nonneg t)
  rw [lightBudget]
  linarith

/-- ★★ **Where a light messenger's wall state is.** The wall state of the flat packet on `N`
neighbouring modes within `1/(600 n)` of `|p₀| ≤ 1/2`, rest energy `0 < μ ≤ 1`: at every
packet time, on every region at `cos ≤ γ < 1` from the packet's predicted direction and from
the mirror direction, (weight on `B`) `· (1 − γ) ≤ 4 · lightBudget n N μ t`. -/
theorem regionWeight_lightWall_away_le (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {p₀ : ℝ}
    (hp₀ : |p₀| ≤ 1 / 2)
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
      ≤ 4 * lightBudget n N μ t := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : 0 < 1200 * n * N := by positivity
  have h := regionWeight_oddWall_away_le (L := M + 1) (c := 1) (P := 1 / 2)
    (D := 1 / (600 * n)) one_pos hμ0 (ringLen_pos hK) hp₀ (by positivity) hWin hWD
    (flatAmpN N) (sum_norm_flatAmpN_Ico lo hN) hγ t hB hB'
  have b1 := light_packet_budget hn hN hM hWin hμ0 hμ1 t
  have b2 := light_packet_budget hn hN hM (mirror_ico_mem_range hWin) hμ0 hμ1 t
  have em : mirrorPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) (Finset.Ico lo (lo + N))
      (flatAmpN N) 0
      = ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N))
        (Finset.Ico (-lo - N + 1) (-lo - N + 1 + N)) (flatAmpN N) 0 := by
    rw [mirrorPacket, negWin_Ico]
    rfl
  rw [em] at h
  linarith

/-- ★★ **A light messenger's wall state stays in the double arc about its predicted angle.**
Along the uncoupled orbit from the packet time `t₀`, at the flow time `s`: the occupancy
outside the double arc of half-angle `δ`, times `1 − cos δ`, is at most
`4 · lightBudget n N μ (t₀ + s)`. -/
theorem one_sub_sum_arenaObs_wallArc_lightWall_le (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {lo : ℤ}
    (hlo : 0 < lo) (hhi : 2 * (lo + N) ≤ M) {p₀ : ℝ} (hp₀ : |p₀| ≤ 1 / 2)
    (hWD : ∀ m ∈ Finset.Ico lo (lo + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - p₀| ≤ 1 / (600 * n)) (t₀ : ℝ)
    (hψ : oddWall (L := M + 1) 1 μ (ringLen (1200 * n * N)) (Finset.Ico lo (lo + N))
      (flatAmpN N) t₀ ≠ 0) {δ : ℝ} (hδ : Real.cos δ < 1) (s : ℝ) :
    (1 - ∑ k ∈ wallArc (M + 1)
          (2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 * p₀) * (t₀ + s)) δ,
        arenaObs (siteSel (Prod.fst : ZMod (M + 1) × Fin 2 → ZMod (M + 1)) k)
          (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))) * (1 - Real.cos δ)
      ≤ 4 * lightBudget n N μ (t₀ + s) := by
  have hnorm := chainInner_icoWall (M := M) hn hN hμ0 hlo hhi hp₀ hWD t₀
  unfold ringHop
  rw [one_sub_sum_arenaObs_siteSel, sum_arenaObs_siteSel_free_chainRay, hnorm, Complex.one_re,
    div_one, chainProp_oddWall_shift]
  refine regionWeight_lightWall_away_le hn hN hM hμ0 hμ1 hp₀ (icoWindow_mem_range hlo hhi)
    hWD hδ (t₀ + s) (fun k hk => ?_) (fun k hk => ?_)
  · rw [Finset.mem_compl, mem_wallArc, not_or, mem_ringArc, not_lt] at hk
    exact hk.1
  · rw [Finset.mem_compl, mem_wallArc, not_or, mem_ringArc, mem_ringArc, not_lt, not_lt] at hk
    rw [show 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 * -p₀) * (t₀ + s)
        = -(2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 * p₀) * (t₀ + s)) by
      rw [mul_neg, vRel_neg]; ring]
    exact hk.2

/-- ★★★ **The wall gate is open while the light messenger is near the clock.** A flat
messenger wall state of rest energy `0 < μ ≤ 1` and a flat clock wall state, at a flow time
`s` with the clock's packet time within `4π n/Δ`. If the messenger's predicted angle is
within `w − 2δ` of both levels' predicted angles: (weight outside `wallNear w`)
`· (1 − cos δ) ≤ 4 · lightBudget n N μ (t₀ + s) + 4 (1/N + 1/(20000 Δ n N))`. -/
theorem light_wall_gate_open (hn : 0 < n) (hN : 0 < N) (hM : 210000 * n ^ 2 * N ≤ M)
    {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2)
    {lo lc : ℤ} (hlo : 0 < lo) (hhi : 2 * (lo + N) ≤ M) (hlc : 0 < lc)
    (hhc : 2 * (lc + N) ≤ M) {p₀ q₀ : ℝ} (hp₀ : |p₀| ≤ 1 / 2) (hq₀ : |q₀| ≤ 1 / 2)
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
    (ht₁ : |t₁ + s| ≤ 4 * Real.pi * n / Δ)
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
      ≤ 4 * lightBudget n N μ (t₀ + s) + 4 * (1 / N + 1 / (20000 * Δ * n * N)) := by
  have hpos : 0 ≤ 1 - Real.cos δ := by linarith
  have g := mul_le_mul_of_nonneg_right (wallGate_not_le hδ0 hw hwπ h0 h1
    (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
      (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))
    (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
      (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ))) hpos
  have a := one_sub_sum_arenaObs_wallArc_lightWall_le hn hN hM hμ0 hμ1 hlo hhi hp₀ hWD t₀ hψ
    hδ s
  have b := one_sub_sum_arenaObs_wallArcs_icoDevice_le hn hN hM hΔ0 hΔ hlc hhc hq₀ hWDc t₁ hΨ
    hδ ht₁
  rw [add_mul] at g
  linarith

/-- ★★★ **The wall gate is closed while the light messenger is away from the clock.** As
`light_wall_gate_open`, at a flow time at which the messenger's predicted angle is more than
`w + 2δ` from both levels' predicted angles and from their mirror images. -/
theorem light_wall_gate_closed (hn : 0 < n) (hN : 0 < N) (hM : 210000 * n ^ 2 * N ≤ M)
    {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2)
    {lo lc : ℤ} (hlo : 0 < lo) (hhi : 2 * (lo + N) ≤ M) (hlc : 0 < lc)
    (hhc : 2 * (lc + N) ≤ M) {p₀ q₀ : ℝ} (hp₀ : |p₀| ≤ 1 / 2) (hq₀ : |q₀| ≤ 1 / 2)
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
    (ht₁ : |t₁ + s| ≤ 4 * Real.pi * n / Δ)
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
      ≤ 4 * lightBudget n N μ (t₀ + s) + 4 * (1 / N + 1 / (20000 * Δ * n * N)) := by
  have hpos : 0 ≤ 1 - Real.cos δ := by linarith
  have g := mul_le_mul_of_nonneg_right (wallGate_le hδ0 hw hwπ h0 h0' h1 h1'
    (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1)
      (ringHop (1200 * n * N) M) μ) s) (chainRay _ hψ))
    (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
      (ringHop (1200 * n * N) M) 1 (1 + Δ)) s) (deviceRay _ hΨ))) hpos
  have a := one_sub_sum_arenaObs_wallArc_lightWall_le hn hN hM hμ0 hμ1 hlo hhi hp₀ hWD t₀ hψ
    hδ s
  have b := one_sub_sum_arenaObs_wallArcs_icoDevice_le hn hN hM hΔ0 hΔ hlc hhc hq₀ hWDc t₁ hΨ
    hδ ht₁
  rw [add_mul] at g
  linarith

end Light

/-- ★★ **At the momentum `1/2` a packet of rest energy `μ` is within `2μ²` of speed `1`.** -/
theorem one_sub_vRel_half_le {μ : ℝ} (hμ : 0 < μ) : 1 - vRel 1 μ (1 * (1 / 2)) ≤ 2 * μ ^ 2 := by
  have h := one_sub_vRel_le hμ (by norm_num : (0 : ℝ) < 1 / 2)
  rw [one_mul]
  have e : μ ^ 2 / (2 * (1 / 2 : ℝ) ^ 2) = 2 * μ ^ 2 := by
    field_simp
  linarith

end CSD.RecordLayer

end
