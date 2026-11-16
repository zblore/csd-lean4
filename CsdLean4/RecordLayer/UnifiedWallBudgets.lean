/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedWallObservers

/-!
# The walled chain with numbers: flat wall states, and a moving clock that ticks

**Category:** 7-SigmaLayer (the record layer). BACKLOG #409 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; of item R2 of the list under
UD-164: the budgets of #408 evaluated, the place of the clock beside the wall, and the moving
clock's wall state ticking. No new assumption beyond UA-18 (a), (b).

#408 bounds the wall states' weights by budgets of #265 that it does not evaluate, and its
moving clock does not tick because #391 asked for a window narrow about one momentum. Here
the budgets are evaluated for every flat window of `N` neighbouring modes and its mirror, and
#391 (generalised in the same commit to a window within `1/(600 n)` of `p₀` or of `−p₀`,
since the level splitting is even in the momentum) is applied to the moving wall state.

* `negWin_Ico`, `sum_norm_flatAmpN_Ico`, `ico_packet_start_le`, ★ `ico_packet_budget` — a flat
  packet on any `N` neighbouring modes of the ring of length `2π · 1200 n N`: the budget is at
  most `1/N + 1/(20000 Δ n N)` up to `|t| ≤ 4π n/Δ`;
* ★★ `regionWeight_icoWall_away_le` — the wall state of such a packet, reference momentum
  `|p₀| ≤ 1/2`: weight away from the two mirror directions, times `1 − γ`, at most
  `4 (1/N + 1/(20000 Δ n N))`;
* ★★ `deviceRegionWeight_icoWall_away_le` — the same for the two-level clock's wall state;
* ★★★ `wall_clock_localised` — **the clock at rest beside the wall stays beside it**: the
  clock of `wall_clock_ticks`, at every packet time `|t| ≤ 4π n/Δ`;
* `flatWindow_neg_notMem`, ★★★ `wall_moving_clock_ticks` — **the moving clock's wall state
  ticks**: the wall state of #392's flat packet at momentum `1/2` has at least `n` ticks,
  with the dilated rate within `1/n + Δ`.

## Exact scope

* **The odd sector of the ring**, as #407.
* **Weights of state vectors at packet times**, for uncoupled carriers. No gate, no
  coincidence weight, no pointer history of UD-170.
* **No region is exhibited.** The bounds hold for every region `B` meeting the cosine
  conditions, the empty one among them. They say something when `1 − γ` exceeds four times
  the budget, that is for arcs wide against `1/√N`.
* **The clock beside the wall is within the bound of the site `0` of the ring**, one of the
  two self-mirror sites; which wall UA-18 calls the right one is a naming.
* **The moving clock: ticks and place are two theorems about the same state**, the wall state
  of #392's packet. The count is at one flow time, on one fibre and from one start, as #391.
  Its place is `deviceRegionWeight_icoWall_away_le` with `p₀ = 1/2`; the four directions
  (two levels, two mirror images) must all be avoided.
* **The level splitting is even in the momentum**, which is why a window and its mirror
  share a rate. The generalisation of #391 changes only its hypothesis on the window; the
  earlier instances use the first alternative.
* **Units and constants.** Speed `1`, lower level `1`; the constants are not sharp.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-8,
UA-12, UA-18, UO-16, UD-142, UD-143, UD-144, UD-164, UD-174, UD-175, UD-176, UD-177);
`RecordLayer/UnifiedWallObservers.lean` (#408: `regionWeight_oddWall_away_le`,
`deviceRegionWeight_wall_away_le`, `oddExt`, `wallWindow`, `wall_clock_ticks`);
`RecordLayer/UnifiedClockPacketLocalised.lean` (#392: `flatWindow`, `flatAmpN`,
`flat_packet_limitErr_le`, `flatWindow_width`, `flatWindow_mem_range`);
`RecordLayer/UnifiedClockPacketInstance.lean` (#391: `narrow_clock_packet_ticks`);
`RecordLayer/DiracArrival.lean` (#265: `re_transPhase_ringPacket_ge`);
`CV/DiracPacketLimit.lean` (`flat_sums`, `limitErr`); `CV/DiracDevice.lean`
(`abs_sq_sub_sq_scaled_le_or`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set CSD.CV Complex
open scoped Matrix

namespace CSD.RecordLayer

open CSD.SigmaLayer

/-! ### Flat packets on any `N` neighbouring modes -/

/-- The reflection of `N` neighbouring modes is `N` neighbouring modes. -/
theorem negWin_Ico (lo : ℤ) (N : ℕ) :
    negWin (Finset.Ico lo (lo + N)) = Finset.Ico (-lo - N + 1) (-lo - N + 1 + N) := by
  ext m
  rw [mem_negWin, Finset.mem_Ico, Finset.mem_Ico]
  constructor <;> intro h <;> constructor <;> omega

theorem sum_norm_flatAmpN_Ico (lo : ℤ) {N : ℕ} (hN : 0 < N) :
    ∑ m ∈ Finset.Ico lo (lo + N), ‖flatAmpN N m‖ ^ 2 = 1 := by
  have hpos : 0 ≤ 1 / Real.sqrt N := by positivity
  have h := (flat_sums lo hN).1
  simpa [flatAmpN, Complex.norm_real, abs_of_nonneg hpos] using h

/-- **A flat packet on any `N` neighbouring modes starts localised**:
`1 − Re T(0) ≤ 1/N + 1/(4 K²)`, `K = 1200 n N`. -/
theorem ico_packet_start_le {n N M : ℕ} (hn : 0 < n) (hN : 0 < N) {lo lo₁ : ℤ}
    (hWin : ∀ m ∈ Finset.Ico lo (lo + N), lo₁ ≤ m ∧ m + 1 < lo₁ + ((M + 1 : ℕ) : ℤ))
    {μ : ℝ} (hμ : 1 ≤ μ) :
    1 - (transPhase (ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N))
          (Finset.Ico lo (lo + N)) (flatAmpN N) 0)).re
      ≤ 1 / N + 1 / (4 * (1200 * (n : ℝ) * N) ^ 2) := by
  have hπ := Real.pi_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hμ0 : 0 < μ := by linarith
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
  have hesq : (1 / (2 * (1200 * (n : ℝ) * N) * μ)) ^ 2 ≤ 1 / (4 * (1200 * (n : ℝ) * N) ^ 2) := by
    rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have hμsq : 1 ≤ μ ^ 2 := by nlinarith
    have hKsq : (0 : ℝ) ≤ 4 * (1200 * (n : ℝ) * N) ^ 2 := by positivity
    have e : (2 * (1200 * (n : ℝ) * N) * μ) ^ 2 = 4 * (1200 * (n : ℝ) * N) ^ 2 * μ ^ 2 := by ring
    rw [e, one_mul, one_mul]
    exact le_mul_of_one_le_right hKsq hμsq
  have hinvN0 : 0 ≤ 1 / (N : ℝ) := by positivity
  have hinvN1 : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one hN0]; exact hN'
  have hprod : (1 / (2 * (1200 * (n : ℝ) * N) * μ)) ^ 2 * (1 - 1 / (N : ℝ))
      ≤ 1 / (4 * (1200 * (n : ℝ) * N) ^ 2) := by
    calc (1 / (2 * (1200 * (n : ℝ) * N) * μ)) ^ 2 * (1 - 1 / (N : ℝ))
        ≤ (1 / (2 * (1200 * (n : ℝ) * N) * μ)) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) hesq0
      _ ≤ 1 / (4 * (1200 * (n : ℝ) * N) ^ 2) := by rw [mul_one]; exact hesq
  have hexp : (1 - (1 / (2 * (1200 * (n : ℝ) * N) * μ)) ^ 2) * (1 - 1 / (N : ℝ))
      = 1 - 1 / (N : ℝ)
        - (1 / (2 * (1200 * (n : ℝ) * N) * μ)) ^ 2 * (1 - 1 / (N : ℝ)) := by ring
  rw [hexp] at hRe
  unfold flatAmpN
  linarith

/-- ★ **The budget of a flat packet on any `N` neighbouring modes.** For a level of rest
energy `1 ≤ μ`, at every packet time with `|t| ≤ 4π n/Δ`:
`1 − Re T(0) + |t| · limitErr ≤ 1/N + 1/(20000 Δ n N)`. -/
theorem ico_packet_budget {n N M : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {lo lo₁ : ℤ}
    (hWin : ∀ m ∈ Finset.Ico lo (lo + N), lo₁ ≤ m ∧ m + 1 < lo₁ + ((M + 1 : ℕ) : ℤ))
    {μ : ℝ} (hμ : 1 ≤ μ) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2) {t : ℝ}
    (ht : |t| ≤ 4 * Real.pi * n / Δ) :
    1 - (transPhase (ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N))
          (Finset.Ico lo (lo + N)) (flatAmpN N) 0)).re
      + |t| * limitErr 1 μ (ringLen (1200 * n * N)) (1 / (600 * n)) (1 / 2)
          (ringLen (1200 * n * N) / (M + 1 : ℕ))
      ≤ 1 / N + 1 / (20000 * Δ * n * N) := by
  have hπ := Real.pi_pos
  have hπu : Real.pi < 3.15 := Real.pi_lt_d2
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hstart := ico_packet_start_le hn hN hWin hμ
  obtain ⟨hrate0, hrate⟩ := flat_packet_limitErr_le hn hN hM hμ
  have hdrift : |t| * limitErr 1 μ (ringLen (1200 * n * N)) (1 / (600 * n)) (1 / 2)
        (ringLen (1200 * n * N) / (M + 1 : ℕ))
      ≤ 4 * Real.pi * n / Δ * (1 / (1200 * (n : ℝ) * N) * (1 / (300 * n))) :=
    mul_le_mul ht hrate hrate0 (by positivity)
  have hy0 : 0 < 1 / (Δ * n * N) := by positivity
  have e1 : 4 * Real.pi * n / Δ * (1 / (1200 * (n : ℝ) * N) * (1 / (300 * n)))
      = Real.pi / 90000 * (1 / (Δ * n * N)) := by
    field_simp
    ring
  have hnN : (1 : ℝ) ≤ n * N := by nlinarith
  have hΔy : 1 / ((n : ℝ) * N) ≤ 1 / (Δ * n * N) / 2 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hn0 hN0]
  have hk : 1 / (4 * (1200 * (n : ℝ) * N) ^ 2) ≤ 1 / (5760000 * ((n : ℝ) * N)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hn0 hN0, sq_nonneg ((n : ℝ) * N)]
  have hk2 : 1 / (5760000 * ((n : ℝ) * N)) = 1 / ((n : ℝ) * N) / 5760000 := by
    field_simp
  have e3 : 1 / (20000 * Δ * n * N) = 1 / (Δ * n * N) / 20000 := by
    field_simp
  have hπ9 : Real.pi / 90000 ≤ 7 / 200000 := by
    norm_num at hπu
    linarith
  have hπy : Real.pi / 90000 * (1 / (Δ * n * N)) ≤ 7 / 200000 * (1 / (Δ * n * N)) :=
    mul_le_mul_of_nonneg_right hπ9 hy0.le
  rw [e3]
  linarith

/-! ### Flat wall states, with numbers -/

section FlatWall

variable {n N M : ℕ} {lo lo₁ : ℤ}

/-- The mirror window of `N` neighbouring modes lies in a window of the ring when the modes
do. -/
theorem mirror_ico_mem_range
    (hWin : ∀ m ∈ Finset.Ico lo (lo + N), lo₁ ≤ m ∧ m + 1 < lo₁ + ((M + 1 : ℕ) : ℤ)) :
    ∀ m ∈ Finset.Ico (-lo - N + 1) (-lo - N + 1 + N),
      (2 - lo₁ - ((M + 1 : ℕ) : ℤ)) ≤ m
        ∧ m + 1 < (2 - lo₁ - ((M + 1 : ℕ) : ℤ)) + ((M + 1 : ℕ) : ℤ) := by
  intro m hm
  rw [← negWin_Ico, mem_negWin] at hm
  obtain ⟨h1, h2⟩ := hWin (-m) hm
  constructor <;> omega

/-- ★★ **Where a flat wall state is, with numbers.** The wall state of the flat packet on `N`
neighbouring modes of the ring of length `2π · 1200 n N`, the modes within `1/(600 n)` of a
reference momentum `|p₀| ≤ 1/2`, rest energy `μ ≥ 1`. At every packet time `|t| ≤ 4π n/Δ`,
on every region `B` at `cos ≤ γ < 1` from the packet's predicted direction and from the mirror
direction: (weight on `B`) `· (1 − γ) ≤ 4 (1/N + 1/(20000 Δ n N))`. -/
theorem regionWeight_icoWall_away_le (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {μ : ℝ} (hμ : 1 ≤ μ) {Δ : ℝ} (hΔ0 : 0 < Δ)
    (hΔ : Δ ≤ 1 / 2) {p₀ : ℝ} (hp₀ : |p₀| ≤ 1 / 2)
    (hWin : ∀ m ∈ Finset.Ico lo (lo + N), lo₁ ≤ m ∧ m + 1 < lo₁ + ((M + 1 : ℕ) : ℤ))
    (hWD : ∀ m ∈ Finset.Ico lo (lo + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - p₀| ≤ 1 / (600 * n))
    {B : Finset (ZMod (M + 1))} {γ : ℝ} (hγ : γ < 1) {t : ℝ}
    (ht : |t| ≤ 4 * Real.pi * n / Δ)
    (hB : ∀ k ∈ B, Real.cos (2 * Real.pi * k.val / (M + 1 : ℕ)
      - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 * p₀) * t) ≤ γ)
    (hB' : ∀ k ∈ B, Real.cos (2 * Real.pi * k.val / (M + 1 : ℕ)
      - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 μ (1 * -p₀) * t) ≤ γ) :
    regionWeight (oddWall (L := M + 1) 1 μ (ringLen (1200 * n * N))
        (Finset.Ico lo (lo + N)) (flatAmpN N) t) B * (1 - γ)
      ≤ 4 * (1 / N + 1 / (20000 * Δ * n * N)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : 0 < 1200 * n * N := by positivity
  have h := regionWeight_oddWall_away_le (L := M + 1) (c := 1) (P := 1 / 2)
    (D := 1 / (600 * n)) one_pos (by linarith) (ringLen_pos hK) hp₀ (by positivity) hWin hWD
    (flatAmpN N) (sum_norm_flatAmpN_Ico lo hN) hγ t hB hB'
  have b1 := ico_packet_budget hn hN hM hWin hμ hΔ0 hΔ ht
  have b2 := ico_packet_budget hn hN hM (mirror_ico_mem_range hWin) hμ hΔ0 hΔ ht
  have em : mirrorPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) (Finset.Ico lo (lo + N))
      (flatAmpN N) 0
      = ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N))
        (Finset.Ico (-lo - N + 1) (-lo - N + 1 + N)) (flatAmpN N) 0 := by
    rw [mirrorPacket, negWin_Ico]
    rfl
  rw [em] at h
  linarith

/-- ★★ **Where a flat two-level wall state is, with numbers.** The clock's wall state on `N`
neighbouring modes and their reflections, levels `1` and `1 + Δ`: at every packet time
`|t| ≤ 4π n/Δ`, on every region at `cos ≤ γ < 1` from the four predicted directions,
(weight on `B`) `· (1 − γ) ≤ 4 (1/N + 1/(20000 Δ n N))`. -/
theorem deviceRegionWeight_icoWall_away_le (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2) {p₀ : ℝ}
    (hp₀ : |p₀| ≤ 1 / 2) (hW : ∀ m ∈ Finset.Ico lo (lo + N), -m ∉ Finset.Ico lo (lo + N))
    (hWin : ∀ m ∈ Finset.Ico lo (lo + N), lo₁ ≤ m ∧ m + 1 < lo₁ + ((M + 1 : ℕ) : ℤ))
    (hWD : ∀ m ∈ Finset.Ico lo (lo + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - p₀| ≤ 1 / (600 * n))
    {B : Finset (ZMod (M + 1))} {γ : ℝ} (hγ : γ < 1) {t : ℝ}
    (ht : |t| ≤ 4 * Real.pi * n / Δ)
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
      ≤ 4 * (1 / N + 1 / (20000 * Δ * n * N)) := by
  have a0 := regionWeight_icoWall_away_le hn hN hM (μ := 1) le_rfl hΔ0 hΔ hp₀ hWin hWD hγ ht
    hB0 hB0'
  have a1 := regionWeight_icoWall_away_le hn hN hM (μ := 1 + Δ) (by linarith) hΔ0 hΔ hp₀ hWin
    hWD hγ ht hB1 hB1'
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

end FlatWall

/-! ### The clock at rest beside the wall: its place -/

/-- ★★★ **The clock at rest beside the wall stays beside it.** For the clock of
`wall_clock_ticks`, at every packet time `|t| ≤ 4π n/Δ` and every region `B` of sites with
`cos(2π k/L) ≤ γ < 1`: (weight of the clock on `B`) `· (1 − γ) ≤ 4 (1/N + 1/(20000 Δ n N))`. -/
theorem wall_clock_localised {n N M : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2)
    {B : Finset (ZMod (M + 1))} {γ : ℝ} (hγ : γ < 1) {t : ℝ}
    (ht : |t| ≤ 4 * Real.pi * n / Δ)
    (hB : ∀ k ∈ B, Real.cos (2 * Real.pi * k.val / (M + 1 : ℕ)) ≤ γ) :
    deviceRegionWeight (devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
        (wallWindow N ∪ negWin (wallWindow N)) (oddExt (wallWindow N) (flatAmpN N)) t) B
        * (1 - γ)
      ≤ 4 * (1 / N + 1 / (20000 * Δ * n * N)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h3 : 3 * N ≤ M := by
    have h1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
    have h2 : 3 * N ≤ 210000 * n ^ 2 * N := Nat.mul_le_mul_right N (by nlinarith)
    exact h2.trans hM
  have hz : (3 * N : ℤ) ≤ M := by exact_mod_cast h3
  have hWin : ∀ m ∈ Finset.Ico (1 : ℤ) (1 + N),
      (0 : ℤ) ≤ m ∧ m + 1 < (0 : ℤ) + ((M + 1 : ℕ) : ℤ) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    refine ⟨by omega, ?_⟩
    push_cast
    omega
  have hWD : ∀ m ∈ Finset.Ico (1 : ℤ) (1 + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - 0| ≤ 1 / (600 * n) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have h1 : (0 : ℝ) ≤ m := by exact_mod_cast (by omega : (0 : ℤ) ≤ m)
    have h2 : (m : ℝ) ≤ N := by exact_mod_cast (by omega : m ≤ (N : ℤ))
    have hπ := Real.pi_pos
    have hden : (0 : ℝ) < 1200 * n * N := by positivity
    have e : 2 * Real.pi * (m : ℝ) / ringLen (1200 * n * N) = (m : ℝ) / (1200 * n * N) := by
      rw [ringLen]
      push_cast
      field_simp
    rw [e, sub_zero, abs_of_nonneg (by positivity), div_le_div_iff₀ hden (by positivity)]
    nlinarith
  exact deviceRegionWeight_icoWall_away_le (lo := 1) (lo₁ := 0) (p₀ := 0) hn hN hM hΔ0 hΔ
    (by rw [abs_zero]; norm_num) (wallWindow_neg_notMem N) hWin hWD hγ ht
    (fun k hk => by
      simp only [vRel, mul_zero, zero_div, zero_mul, sub_zero]
      exact hB k hk)
    (fun k hk => by
      simp only [vRel, neg_zero, mul_zero, zero_div, zero_mul, sub_zero]
      exact hB k hk)
    (fun k hk => by
      simp only [vRel, mul_zero, zero_div, zero_mul, sub_zero]
      exact hB k hk)
    (fun k hk => by
      simp only [vRel, neg_zero, mul_zero, zero_div, zero_mul, sub_zero]
      exact hB k hk)

/-! ### The moving clock's wall state ticks -/

theorem flatWindow_neg_notMem {n N : ℕ} (hn : 0 < n) (hN : 0 < N) :
    ∀ m ∈ flatWindow n N, -m ∉ flatWindow n N := by
  have hn1 : (0 : ℤ) < n := by exact_mod_cast hn
  have hN1 : (0 : ℤ) < N := by exact_mod_cast hN
  have hpos : (0 : ℤ) < 600 * n * N := mul_pos (mul_pos (by norm_num) hn1) hN1
  intro m hm h
  rw [flatWindow, Finset.mem_Ico] at hm h
  linarith [hm.1, h.1]

/-- ★★★ **The moving clock's wall state ticks.** The wall state of #392's flat clock packet
(the `N` modes from `600 n N` upward on the ring of length `2π · 1200 n N`, reference momentum
`1/2`) is the device packet on those modes and their reflections with the odd extension of
the amplitudes. For some strength its count at `T = 2π n/R` is at least `n`, and the
operational time per flow time is within `1/n + Δ` of `√(1 − v²)`, `v ≥ 1/(2π)`. -/
theorem wall_moving_clock_ticks {n N M : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2) :
    1 / 2 / Real.pi ≤ vRel 1 1 (ringSigma (1200 * n * N) M (1 / 2))
    ∧ ∃ (g : ℝ) (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
          (flatWindow n N ∪ negWin (flatWindow n N)) (oddExt (flatWindow n N) (flatAmpN N))
          (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ))) ≠ 0) (N' : ℕ),
      n ≤ N'
      ∧ IsTickCount (tickReady M) (tickDisplay M)
          (fun t => clockPointerFlow M (ringHop (1200 * n * N) M) 1 (1 + Δ) g
            trainF_periodic contDiff_trainF t
            (clockArenaEquiv M (deviceRay _ hΨ),
              ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))))
          (2 * Real.pi * n / ringRate (1200 * n * N) M (1 / 2) Δ) N'
      ∧ |clockOpTime 1 (1 + Δ) N' / (2 * Real.pi * n / ringRate (1200 * n * N) M (1 / 2) Δ)
            - Real.sqrt (1 - (vRel 1 1 (ringSigma (1200 * n * N) M (1 / 2)) / 1) ^ 2)|
          ≤ 1 / n + Δ := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hK : 0 < 1200 * n * N := by positivity
  have hMr : (210000 : ℝ) * n ^ 2 * N ≤ M := by exact_mod_cast hM
  have hMz : (210000 : ℤ) * n ^ 2 * N ≤ M := by exact_mod_cast hM
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℤ) ≤ N := Int.natCast_nonneg N
  have hnN : (0 : ℤ) ≤ n * N := by positivity
  have hsq : (n : ℤ) * N ≤ n ^ 2 * N := by nlinarith
  have hNle : (N : ℤ) ≤ n * N := by nlinarith
  have hmem : ∀ m ∈ flatWindow n N ∪ negWin (flatWindow n N),
      (-(600 * (n : ℤ) * N + N)) ≤ m ∧ m ≤ 600 * (n : ℤ) * N + N := by
    intro m hm
    rcases Finset.mem_union.1 hm with h | h
    · rw [flatWindow, Finset.mem_Ico] at h
      constructor <;> nlinarith [h.1, h.2]
    · have h' := (mem_negWin _ m).1 h
      rw [flatWindow, Finset.mem_Ico] at h'
      constructor <;> nlinarith [h'.1, h'.2]
  have hWin : ∀ m ∈ flatWindow n N ∪ negWin (flatWindow n N),
      (-(600 * (n : ℤ) * N + N)) ≤ m
        ∧ m + 1 < (-(600 * (n : ℤ) * N + N)) + ((M + 1 : ℕ) : ℤ) := by
    intro m hm
    obtain ⟨h1, h2⟩ := hmem m hm
    refine ⟨h1, ?_⟩
    push_cast
    nlinarith
  have hWD : ∀ m ∈ flatWindow n N ∪ negWin (flatWindow n N),
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
  have hM6 : 6 * ((1200 * n * N : ℕ) : ℝ) * (1 / 2) ≤ ((M + 1 : ℕ) : ℝ) := by
    push_cast
    have hnsq : (n : ℝ) ≤ n ^ 2 := by nlinarith
    have : (n : ℝ) * N ≤ n ^ 2 * N := mul_le_mul_of_nonneg_right hnsq hN'.le
    nlinarith
  obtain ⟨hv, g, hΨ, N', a1, a2, -, a4⟩ := narrow_clock_packet_ticks
    (lo := -(600 * (n : ℤ) * N + N)) (p₀ := 1 / 2) (M := M) hn hK (by norm_num)
    (by norm_num) hM6 hWin hWD (oddExt (flatWindow n N) (flatAmpN N))
    (sum_norm_oddExt (flatWindow_neg_notMem hn hN) (sum_norm_flatAmpN n hN)) hΔ0 hΔ
  exact ⟨hv, g, hΨ, N', a1, a2, a4⟩

end CSD.RecordLayer

end
