/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedClockPacketLocalised

/-!
# A clock at rest, and the moving clock's rate against it

**Category:** 7-SigmaLayer (the record layer). BACKLOG #406 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; item R4 of the list under
UD-164, and of item R2 the clock at rest. No new assumption.

The top-down statement of #402 asks for the moving clock's rate `R_B` and the resting clock's
rate `R₀` with `|R_B − √(1 − v²) R₀| ≤ κ R₀`. The clock packets of #391 and #392 were stated
for a positive reference momentum and built at momentum `1/2`. This module gives the rate
inequality, and a flat clock packet at reference momentum `0`.

* ★★ `abs_movingRate_sub_le` — for the clock with levels `1` and `1 + Δ`, at any momentum term
  `s`: `|R(s) − √(1 − v(s)²) · R(0)| ≤ Δ · R(0)`, `v(s) = s/E₀(s)`, and `R(0) = Δ`;
* `ringRate_zero`, ★ `abs_ringRate_sub_le` — the same for the ring's reference rates;
* `restWindow`, `sum_norm_flatAmpN_rest`, `restWindow_mem_range`, `restWindow_width`;
* ★★ `rest_clock_packet_ticks` — the `N` flat modes from `0` upward on the ring of length
  `2π · 1200 n N` meet `narrow_clock_packet_ticks` at reference momentum `0`: at least `n`
  ticks, at the rate `Δ` within `1/n + Δ` in relative size;
* `rest_packet_start_le`, ★ `rest_packet_budget`;
* ★★★ `rest_clock_packet_localised` — at every packet time `|t| ≤ 4π n/Δ` the clock's weight
  on a region `B` of sites with `cos(2π k/L) ≤ γ`, times `1 − γ`, is at most
  `1/N + 1/(20000 Δ n N)`: the packet stays where it starts.

## Exact scope

* **R4 is an inequality between level splittings**, at any momentum term `s`. `v` is `s/E₀`,
  the relativistic velocity of the lower level at that momentum term; that a packet moves at
  that velocity is not shown here, and on a lattice the band velocity differs from it (R3).
  The error is `Δ`, the relative gap of the levels.
* **"At rest" is reference momentum `0`.** The window holds the modes `0, …, N − 1`, whose
  momenta lie in `[0, 1/(1200 n))`. The localisation bound has the predicted position fixed;
  the modes' own small drift is inside the budget.
* **On the ring.** No wall. A clock at rest on the chain with walls is not built.
* **The localisation is a weight of the state vector** at a packet time, as #392; it is not
  restated at flow times, and no region is exhibited (the hypotheses hold for the empty
  region).
* **One clock, its own pointer, one fibre and one start for the ticks**, as #391. No
  messenger, no gate, no second clock.
* **Units and constants.** Speed `1`, lower level `1`; the constants are not sharp.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-7,
UA-12, UO-16, UD-142, UD-143, UD-144, UD-164, UD-171, UD-172);
`RecordLayer/UnifiedClockPacketLocalised.lean` (#392: `flatAmpN`,
`flat_packet_limitErr_le`, `deviceRegionWeight_devicePacket_le`);
`RecordLayer/UnifiedClockPacketInstance.lean` (#391: `narrow_clock_packet_ticks`,
`ringRate`, `ringSigma`); `CV/DiracClockChain.lean` (`abs_clockRate_div_sub_le`,
`clockRate_zero`); `CV/DiracPacketLimit.lean` (`flat_sums`, `limitErr`);
`RecordLayer/DiracArrival.lean` (`re_transPhase_ringPacket_ge`);
`RecordLayer/UnifiedRadarSkeleton.lean` (#402: the hypothesis `hκ`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### The moving clock's rate against the resting clock's -/

/-- ★★ **The moving clock's rate against the resting clock's.** For levels `1` and `1 + Δ`,
at any momentum term `s`: the splitting at `s` is `√(1 − v²)` times the splitting at rest,
within `Δ` times the splitting at rest; `v = s/E₀(s)`. -/
theorem abs_movingRate_sub_le {Δ : ℝ} (hΔ : 0 < Δ) (s : ℝ) :
    |levelClockRate 1 (1 + Δ) s
        - Real.sqrt (1 - vRel 1 1 s ^ 2) * levelClockRate 1 (1 + Δ) 0|
      ≤ Δ * levelClockRate 1 (1 + Δ) 0 := by
  have h := abs_clockRate_div_sub_le (c := 1) one_ne_zero one_pos
    (by linarith : (1 : ℝ) < 1 + Δ) s
  rw [add_sub_cancel_left, div_one] at h
  have h0 : levelClockRate 1 (1 + Δ) 0 = Δ := by
    rw [clockRate_zero zero_le_one (by linarith)]
    ring
  have hE : Δ / dispE 1 s ≤ Δ := div_le_self hΔ.le (le_dispE 1 s)
  have e : levelClockRate 1 (1 + Δ) s - Real.sqrt (1 - vRel 1 1 s ^ 2) * Δ
      = (levelClockRate 1 (1 + Δ) s / Δ - Real.sqrt (1 - vRel 1 1 s ^ 2)) * Δ := by
    field_simp
  rw [h0, e, abs_mul, abs_of_pos hΔ]
  exact mul_le_mul_of_nonneg_right (h.trans hE) hΔ.le

/-- The ring's reference rate at momentum `0` is the gap. -/
theorem ringRate_zero (K M : ℕ) {Δ : ℝ} (hΔ : 0 ≤ Δ) : ringRate K M 0 Δ = Δ := by
  rw [ringRate, ringSigma, mul_zero, Real.sin_zero, mul_zero,
    clockRate_zero zero_le_one (by linarith)]
  ring

/-- ★ **The rate inequality of #402 for the ring's reference rates**: the clock at reference
momentum `p` against the clock at reference momentum `0`, with `κ = Δ`. -/
theorem abs_ringRate_sub_le (K M : ℕ) {Δ : ℝ} (hΔ : 0 < Δ) (p : ℝ) :
    |ringRate K M p Δ
        - Real.sqrt (1 - vRel 1 1 (ringSigma K M p) ^ 2) * ringRate K M 0 Δ|
      ≤ Δ * ringRate K M 0 Δ := by
  have h := abs_movingRate_sub_le hΔ (ringSigma K M p)
  have h0 : levelClockRate 1 (1 + Δ) 0 = Δ := by
    rw [clockRate_zero zero_le_one (by linarith)]
    ring
  rw [h0] at h
  rw [ringRate_zero K M hΔ.le]
  exact h

/-! ### The flat window at reference momentum zero -/

/-- **The rest window**: the `N` modes from `0` upward. On the ring of length `2π · 1200 n N`
their momenta lie in `[0, 1/(1200 n))`. -/
def restWindow (N : ℕ) : Finset ℤ := Finset.Ico 0 (0 + N)

theorem sum_norm_flatAmpN_rest {N : ℕ} (hN : 0 < N) :
    ∑ m ∈ restWindow N, ‖flatAmpN N m‖ ^ 2 = 1 := by
  have hpos : 0 ≤ 1 / Real.sqrt N := by positivity
  have h := (flat_sums 0 hN).1
  simpa [restWindow, flatAmpN, Complex.norm_real, abs_of_nonneg hpos] using h

theorem restWindow_mem_range {n N M : ℕ} (hn : 0 < n) (hM : 210000 * n ^ 2 * N ≤ M) :
    ∀ m ∈ restWindow N, (0 : ℤ) ≤ m ∧ m + 1 < 0 + ((M + 1 : ℕ) : ℤ) := by
  intro m hm
  rw [restWindow, Finset.mem_Ico] at hm
  have hNM : N ≤ M := by
    have h1 : N ≤ 210000 * n ^ 2 * N := Nat.le_mul_of_pos_left N (by positivity)
    exact h1.trans hM
  have hz : (N : ℤ) ≤ M := by exact_mod_cast hNM
  constructor
  · exact hm.1
  · push_cast
    linarith [hm.2]

theorem restWindow_width {n N : ℕ} (hn : 0 < n) (hN : 0 < N) :
    ∀ m ∈ restWindow N, |(m : ℝ) / ((1200 * n * N : ℕ) : ℝ) - 0| ≤ 1 / (600 * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  intro m hm
  rw [restWindow, Finset.mem_Ico] at hm
  have h1 : (0 : ℝ) ≤ m := by exact_mod_cast hm.1
  have h2 : (m : ℝ) < ((0 + N : ℤ) : ℝ) := by exact_mod_cast hm.2
  push_cast at h2
  have hden : (0 : ℝ) < 1200 * n * N := by positivity
  rw [sub_zero, abs_of_nonneg (by positivity)]
  push_cast
  rw [div_le_div_iff₀ hden (by positivity)]
  nlinarith

/-- ★★ **A flat clock packet at rest ticks at least `n` times.** The instance of
`narrow_clock_packet_ticks` on the rest window of `N` modes, reference momentum `0`: the
count at `T = 2π n/R` is at least `n`, and the operational time per flow time is within
`1/n + Δ` of `√(1 − v²)` with `v` the velocity term at momentum `0`. -/
theorem rest_clock_packet_ticks {n N M : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2) :
    ∃ (g : ℝ) (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
          (restWindow N) (flatAmpN N)
          (-(Real.pi / (2 * ringRate (1200 * n * N) M 0 Δ))) ≠ 0) (N' : ℕ),
      n ≤ N'
      ∧ IsTickCount (tickReady M) (tickDisplay M)
          (fun t => clockPointerFlow M (ringHop (1200 * n * N) M) 1 (1 + Δ) g
            trainF_periodic contDiff_trainF t
            (clockArenaEquiv M (deviceRay _ hΨ),
              ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))))
          (2 * Real.pi * n / ringRate (1200 * n * N) M 0 Δ) N'
      ∧ |clockOpTime 1 (1 + Δ) N' / (2 * Real.pi * n / ringRate (1200 * n * N) M 0 Δ)
            - Real.sqrt (1 - (vRel 1 1 (ringSigma (1200 * n * N) M 0) / 1) ^ 2)|
          ≤ 1 / n + Δ := by
  have hK : 0 < 1200 * n * N := by positivity
  obtain ⟨-, g, hΨ, N', h1, h2, -, h4⟩ := narrow_clock_packet_ticks (lo := 0) (p₀ := 0)
    (M := M) hn hK le_rfl (by norm_num) (by rw [mul_zero]; positivity)
    (restWindow_mem_range hn hM) (restWindow_width hn hN) (flatAmpN N)
    (sum_norm_flatAmpN_rest hN) hΔ0 hΔ
  exact ⟨g, hΨ, N', h1, h2, h4⟩

/-- **The rest packet starts localised**: `1 − Re T(0) ≤ 1/N + 1/(4 K²)`, `K = 1200 n N`. -/
theorem rest_packet_start_le {n N M : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {μ : ℝ} (hμ : 1 ≤ μ) :
    1 - (transPhase (ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) (restWindow N)
          (flatAmpN N) 0)).re
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
  obtain ⟨hW, -⟩ := noWrap_distinct_of_window (L := M + 1) (restWindow_mem_range hn hM)
  have hRe := re_transPhase_ringPacket_ge (L := M + 1) (c := 1) (μ := μ)
    (ℓ := ringLen (1200 * n * N)) hμ0 (ringLen_pos hK) hW
    (fun _ => 1 / Real.sqrt N) (fun _ => by positivity)
  rw [restWindow, (flat_sums 0 hN).2] at hRe
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
  unfold restWindow flatAmpN
  linarith

/-- ★ **The rest packet's budget.** For a level of rest energy `1 ≤ μ`, at every packet time
with `|t| ≤ 4π n/Δ`: `1 − Re T(0) + |t| · limitErr ≤ 1/N + 1/(20000 Δ n N)`. -/
theorem rest_packet_budget {n N M : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {μ : ℝ} (hμ : 1 ≤ μ) {Δ : ℝ} (hΔ0 : 0 < Δ)
    (hΔ : Δ ≤ 1 / 2) {t : ℝ} (ht : |t| ≤ 4 * Real.pi * n / Δ) :
    1 - (transPhase (ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) (restWindow N)
          (flatAmpN N) 0)).re
      + |t| * limitErr 1 μ (ringLen (1200 * n * N)) (1 / (600 * n)) (1 / 2)
          (ringLen (1200 * n * N) / (M + 1 : ℕ))
      ≤ 1 / N + 1 / (20000 * Δ * n * N) := by
  have hπ := Real.pi_pos
  have hπu : Real.pi < 3.15 := Real.pi_lt_d2
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hstart := rest_packet_start_le hn hN hM hμ
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

/-- ★★★ **The flat clock packet at rest stays where it starts.** For the uncoupled packet of
`rest_clock_packet_ticks`, at every packet time `t` with `|t| ≤ 4π n/Δ` and every region `B`
whose sites lie at `cos(2π k/L) ≤ γ` from the starting direction:

`(weight of the clock on B) · (1 − γ) ≤ 1/N + 1/(20000 Δ n N)`. -/
theorem rest_clock_packet_localised {n N M : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2)
    {B : Finset (ZMod (M + 1))} {γ t : ℝ} (ht : |t| ≤ 4 * Real.pi * n / Δ)
    (hB : ∀ k ∈ B, Real.cos (2 * Real.pi * k.val / (M + 1 : ℕ)) ≤ γ) :
    deviceRegionWeight (devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
        (restWindow N) (flatAmpN N) t) B * (1 - γ)
      ≤ 1 / N + 1 / (20000 * Δ * n * N) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : 0 < 1200 * n * N := by positivity
  have hWD : ∀ m ∈ restWindow N,
      |2 * Real.pi * m / ringLen (1200 * n * N) - 0| ≤ 1 / (600 * n) := by
    intro m hm
    have hK' : (0 : ℝ) < ((1200 * n * N : ℕ) : ℝ) := by exact_mod_cast hK
    have e : 2 * Real.pi * (m : ℝ) / ringLen (1200 * n * N)
        = (m : ℝ) / ((1200 * n * N : ℕ) : ℝ) := by
      rw [ringLen]
      have := Real.pi_pos
      field_simp
    rw [e]
    exact restWindow_width hn hN m hm
  have h := deviceRegionWeight_devicePacket_le (L := M + 1) (c := 1) (μ₀ := 1) (μ₁ := 1 + Δ)
    (ℓ := ringLen (1200 * n * N)) (P := 1 / 2) (D := 1 / (600 * n)) (p₀ := 0) one_pos
    one_pos (by linarith) (ringLen_pos hK) (by rw [abs_zero]; norm_num) (by positivity)
    (restWindow_mem_range hn hM) hWD (flatAmpN N) (sum_norm_flatAmpN_rest hN) (B := B)
    (γ := γ) t
    (fun k hk => by
      simp only [vRel, mul_zero, zero_div, zero_mul, sub_zero]
      exact hB k hk)
    (fun k hk => by
      simp only [vRel, mul_zero, zero_div, zero_mul, sub_zero]
      exact hB k hk)
  have b0 := rest_packet_budget hn hN hM (μ := 1) le_rfl hΔ0 hΔ ht
  have b1 := rest_packet_budget hn hN hM (μ := 1 + Δ) (by linarith) hΔ0 hΔ ht
  have hgoal : deviceRegionWeight (devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1
      (1 + Δ) (restWindow N) (flatAmpN N) t) B
      = deviceRegionWeight (devicePacket (L := M + 1)
        (scaledHop 1 (ringLen (1200 * n * N) / ((M + 1 : ℕ) : ℝ))) 1 (1 + Δ)
        (restWindow N) (flatAmpN N) t) B := rfl
  rw [hgoal]
  linarith

end CSD.RecordLayer

end
