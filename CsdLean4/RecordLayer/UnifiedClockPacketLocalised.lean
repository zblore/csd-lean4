/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedClockPacketInstance
public import CsdLean4.RecordLayer.UnifiedFineTransit

/-!
# A clock packet that ticks stays where it is predicted to be

**Category:** 7-SigmaLayer (the record layer). BACKLOG #392 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; step (2) of the plan of
2026-11-14, Remainder (a) of #391. No new assumption.

#391 shows that a clock packet narrow in momentum writes at least `n` ticks, and says nothing
about where the clock carrier is. This module bounds the clock carrier's weight away from its
predicted position, for one family of packets that also tick.

**How.** The device's packet carries each internal level as a Dirac packet of its own rest
energy with weight `1/2` (`deviceRegionWeight_devicePacket`). #264's bound
(`regionWeight_ringPacket_le`) applies to each level.

* `deviceRegionWeight`, `deviceRegionWeight_nonneg`, `regionWeight_const_mul`,
  ★ `deviceRegionWeight_devicePacket`;
* ★★ `deviceRegionWeight_devicePacket_le` — for any device packet: the weight on a region away
  from both levels' predicted directions, times `1 − γ`, is at most the mean of the two
  levels' budgets `1 − Re T_i(0) + |t| · limitErr_i`;
* `flatWindow`, `flatAmpN`, `sum_norm_flatAmpN`, `flatWindow_mem_range`, `flatWindow_width`,
  ★★ `flat_clock_packet_ticks` — the `N` flat modes from `600 n N` upward on the ring of
  length `2π · 1200 n N` meet `narrow_clock_packet_ticks`: count at least `n` at `2π n/R`;
* `flat_packet_start_le`, `flat_packet_limitErr_le`, ★★ `flat_packet_budget` — for that
  window, a level `μ ≥ 1` and `|t| ≤ 4π n/Δ`: the budget is at most `1/N + 1/(20000 Δ n N)`;
* ★★★ `flat_clock_packet_localised` — the same packet, at every packet time `|t| ≤ 4π n/Δ`:
  (weight of the clock on `B`) `· (1 − γ) ≤ 1/N + 1/(20000 Δ n N)` for every region `B` at
  `cos ≤ γ` from both levels' predicted directions;
* `abs_sub_quarter_turn_le` — a flow time in `[0, 2π n/R]` is a packet time in that range.

## Exact scope

* **A weight of the state vector, not a record and not yet an arena observable.** The bound
  is on `deviceRegionWeight` of `devicePacket` at a packet time `t`. That the ray of
  `clockPointerFlow` at flow time `s`, on the fibre where the profile vanishes, is that
  packet at `t = s − π/(2R)` is used inside #388 and is not restated here; no expectation of
  a region projector on the clock arena is stated.
* **The resolution is coarse.** The bound is `(1/N + …)/(1 − γ)`. For an arc of half-angle
  `δ` about the predicted position `1 − γ = 1 − cos δ`, so the weight outside is small only
  for `δ` large against `1/√N`. The packet's own angular width is of order `1/N` (a
  calculation, not in Lean). The bound does not resolve the packet's width.
* **Two predicted positions.** The levels move at `v₀ = vRel 1 1 (1/2)` and
  `v₁ = vRel 1 (1 + Δ) (1/2)`; the region must be away from both. Over the horizon they
  separate by an angle of at most `π/(300 N)` (a calculation, not in Lean).
* **How far the clock travels is not stated.** Over the horizon the predicted angle is of
  order `v/(Δ N)`; whether that exceeds the resolved arc depends on the choice of `Δ`, `n`,
  `N`. A calculation suggests it can (take `Δ` small against `1/√N` and `n` large); nothing
  in Lean says so.
* **The predicted velocity is the continuum one** at momentum `1/2`; the lattice's correction
  is in the budget and needs `M ≥ 210000 n² N` sites.
* **A clock, not an observer; one fibre and one start for the ticks**, as #391. The
  localisation bound itself is about the uncoupled packet.
* **Units and constants.** Speed `1`, lower level `1`, reference momentum `1/2`; the
  constants are not sharp.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-12,
UO-16, UD-141, UD-142, UD-143, UD-144); `RecordLayer/UnifiedClockPacketInstance.lean` (#391:
`narrow_clock_packet_ticks`, `ringLen`, `ringHop`, `ringRate`);
`RecordLayer/DiracArrival.lean` (#264: `regionWeight`, `regionWeight_ringPacket_le`,
`re_transPhase_ringPacket_ge`); `CV/DiracPacketLimit.lean` (#261: `limitErr`, `flat_sums`,
`ringPacket`); `CV/DiracDevice.lean` (#262: `devicePacket`, `levelMass`);
`RecordLayer/UnifiedFineTransit.lean` (#375: the same budget for the messenger).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### The device's weight on a region of sites -/

section Device

variable {L : ℕ} [NeZero L]

/-- **The weight of a device state on a region of sites**: both internal levels together. -/
def deviceRegionWeight (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) (B : Finset (ZMod L)) : ℝ :=
  regionWeight (fun p => Ψ (p, 0)) B + regionWeight (fun p => Ψ (p, 1)) B

omit [NeZero L] in
theorem deviceRegionWeight_nonneg (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) (B : Finset (ZMod L)) :
    0 ≤ deviceRegionWeight Ψ B :=
  add_nonneg (regionWeight_nonneg _ _) (regionWeight_nonneg _ _)

omit [NeZero L] in
theorem regionWeight_const_mul (z : ℂ) (ψ : ZMod L × Fin 2 → ℂ) (B : Finset (ZMod L)) :
    regionWeight (fun p => z * ψ p) B = ‖z‖ ^ 2 * regionWeight ψ B := by
  simp only [regionWeight, siteWeight, norm_mul, mul_pow, Finset.mul_sum]

/-- ★ **The device's weight on a region is the mean of its two levels' weights.** -/
theorem deviceRegionWeight_devicePacket (c ℓ μ₀ μ₁ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (t : ℝ)
    (B : Finset (ZMod L)) :
    deviceRegionWeight (devicePacket (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ W β t) B
      = (regionWeight (ringPacket (L := L) c μ₀ ℓ W β t) B
          + regionWeight (ringPacket (L := L) c μ₁ ℓ W β t) B) / 2 := by
  have hm0 : levelMass μ₀ μ₁ 0 = μ₀ := by simp [levelMass]
  have hm1 : levelMass μ₀ μ₁ 1 = μ₁ := by simp [levelMass]
  have e0 : (fun p => devicePacket (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ W β t (p, 0))
      = fun p => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ringPacket (L := L) c μ₀ ℓ W β t p := by
    funext p
    simp only [devicePacket, ringPacket, hm0]
  have e1 : (fun p => devicePacket (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ W β t (p, 1))
      = fun p => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ringPacket (L := L) c μ₁ ℓ W β t p := by
    funext p
    simp only [devicePacket, ringPacket, hm1]
  have hnorm : ‖(((Real.sqrt 2 : ℝ) : ℂ))⁻¹‖ ^ 2 = 1 / 2 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (by norm_num)), inv_pow,
      Real.sq_sqrt (by norm_num)]
    norm_num
  rw [deviceRegionWeight, e0, e1, regionWeight_const_mul, regionWeight_const_mul, hnorm]
  ring

/-- ★★ **Far from where both levels are predicted to be, the device has little weight.** For
a device packet and a region `B` whose sites all lie at `cos(2πk/L − Ω_i t) ≤ γ` from the
predicted direction of each level, `Ω_i = (2π/ℓ) v_i(p₀)`, the device's weight on `B` times
`1 − γ` is at most the mean of the two levels' budgets `1 − Re T_i(0) + |t| · limitErr_i`. -/
theorem deviceRegionWeight_devicePacket_le {c μ₀ μ₁ ℓ P D p₀ : ℝ} (hc : 0 < c) (h0 : 0 < μ₀)
    (h1 : 0 < μ₁) (hℓ : 0 < ℓ) (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D) {W : Finset ℤ} {lo : ℤ}
    (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L)
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D) (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) {B : Finset (ZMod L)} {γ : ℝ} (t : ℝ)
    (hB0 : ∀ k ∈ B,
      Real.cos (2 * Real.pi * k.val / L - 2 * Real.pi / ℓ * vRel c μ₀ (c * p₀) * t) ≤ γ)
    (hB1 : ∀ k ∈ B,
      Real.cos (2 * Real.pi * k.val / L - 2 * Real.pi / ℓ * vRel c μ₁ (c * p₀) * t) ≤ γ) :
    deviceRegionWeight (devicePacket (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ W β t) B * (1 - γ)
      ≤ ((1 - (transPhase (ringPacket (L := L) c μ₀ ℓ W β 0)).re
            + |t| * limitErr c μ₀ ℓ D P (ℓ / L))
          + (1 - (transPhase (ringPacket (L := L) c μ₁ ℓ W β 0)).re
            + |t| * limitErr c μ₁ ℓ D P (ℓ / L))) / 2 := by
  have a0 := regionWeight_ringPacket_le (L := L) hc h0 hℓ hp₀ hD0 hWin hWD β hβ t hB0
  have a1 := regionWeight_ringPacket_le (L := L) hc h1 hℓ hp₀ hD0 hWin hWD β hβ t hB1
  rw [deviceRegionWeight_devicePacket]
  have e : (regionWeight (ringPacket (L := L) c μ₀ ℓ W β t) B
        + regionWeight (ringPacket (L := L) c μ₁ ℓ W β t) B) / 2 * (1 - γ)
      = (regionWeight (ringPacket (L := L) c μ₀ ℓ W β t) B * (1 - γ)
        + regionWeight (ringPacket (L := L) c μ₁ ℓ W β t) B * (1 - γ)) / 2 := by ring
  rw [e]
  linarith

end Device

/-! ### The flat packet that ticks -/

/-- **The flat window**: `N` neighbouring modes from `600 n N` upward. On the ring of length
`2π · 1200 n N` their momenta start at `1/2` and span less than `1/(1200 n)`. -/
def flatWindow (n N : ℕ) : Finset ℤ :=
  Finset.Ico (600 * (n : ℤ) * N) (600 * (n : ℤ) * N + N)

/-- **Equal amplitudes on `N` modes.** -/
def flatAmpN (N : ℕ) : ℤ → ℂ := fun _ => ((1 / Real.sqrt N : ℝ) : ℂ)

theorem sum_norm_flatAmpN (n : ℕ) {N : ℕ} (hN : 0 < N) :
    ∑ m ∈ flatWindow n N, ‖flatAmpN N m‖ ^ 2 = 1 := by
  have hpos : 0 ≤ 1 / Real.sqrt N := by positivity
  have h := (flat_sums (600 * (n : ℤ) * N) hN).1
  simpa [flatWindow, flatAmpN, Complex.norm_real, abs_of_nonneg hpos] using h

theorem flatWindow_mem_range {n N M : ℕ} (hn : 0 < n) (hM : 210000 * n ^ 2 * N ≤ M) :
    ∀ m ∈ flatWindow n N, (0 : ℤ) ≤ m ∧ m + 1 < 0 + ((M + 1 : ℕ) : ℤ) := by
  intro m hm
  rw [flatWindow, Finset.mem_Ico] at hm
  have hMz : (210000 : ℤ) * n ^ 2 * N ≤ M := by exact_mod_cast hM
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℤ) ≤ N := Int.natCast_nonneg N
  have hnN : (0 : ℤ) ≤ n * N := by positivity
  have hsq : (n : ℤ) * N ≤ n ^ 2 * N := by nlinarith
  have hNle : (N : ℤ) ≤ n * N := by nlinarith
  constructor
  · nlinarith [hm.1]
  · push_cast
    nlinarith [hm.2]

theorem flatWindow_width {n N : ℕ} (hn : 0 < n) (hN : 0 < N) :
    ∀ m ∈ flatWindow n N,
      |(m : ℝ) / ((1200 * n * N : ℕ) : ℝ) - 1 / 2| ≤ 1 / (600 * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  intro m hm
  rw [flatWindow, Finset.mem_Ico] at hm
  have h1 : ((600 * (n : ℤ) * N : ℤ) : ℝ) ≤ m := by exact_mod_cast hm.1
  have h2 : (m : ℝ) < ((600 * (n : ℤ) * N + N : ℤ) : ℝ) := by exact_mod_cast hm.2
  push_cast at h1 h2
  have hden : (0 : ℝ) < 1200 * n * N := by positivity
  have e : (m : ℝ) / ((1200 * n * N : ℕ) : ℝ) - 1 / 2
      = ((m : ℝ) - 600 * n * N) / (1200 * n * N) := by
    push_cast
    field_simp
    ring
  rw [e, abs_le]
  constructor
  · rw [le_div_iff₀ hden]
    have : -(1 / (600 * (n : ℝ))) * (1200 * n * N) = -(2 * N) := by
      field_simp
      ring
    rw [this]
    linarith
  · rw [div_le_iff₀ hden]
    have : 1 / (600 * (n : ℝ)) * (1200 * n * N) = 2 * N := by
      field_simp
      ring
    rw [this]
    linarith

/-- ★★ **The flat packet ticks at least `n` times.** The instance of
`narrow_clock_packet_ticks` on the flat window of `N` modes, reference momentum `1/2`. -/
theorem flat_clock_packet_ticks {n N M : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2) :
    0 < vRel 1 1 (ringSigma (1200 * n * N) M (1 / 2))
    ∧ ∃ (g : ℝ) (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
          (flatWindow n N) (flatAmpN N)
          (-(Real.pi / (2 * ringRate (1200 * n * N) M (1 / 2) Δ))) ≠ 0) (N' : ℕ),
      n ≤ N'
      ∧ IsTickCount (tickReady M) (tickDisplay M)
          (fun t => clockPointerFlow M (ringHop (1200 * n * N) M) 1 (1 + Δ) g
            trainF_periodic contDiff_trainF t
            (clockArenaEquiv M (deviceRay _ hΨ),
              ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))))
          (2 * Real.pi * n / ringRate (1200 * n * N) M (1 / 2) Δ) N'
      ∧ |clockOpTime 1 (1 + Δ) N'
            - Real.sqrt (1 - (vRel 1 1 (ringSigma (1200 * n * N) M (1 / 2)) / 1) ^ 2)
              * (2 * Real.pi * n / ringRate (1200 * n * N) M (1 / 2) Δ)|
          ≤ 2 * Real.pi / Δ
            + Δ / dispE 1 (ringSigma (1200 * n * N) M (1 / 2))
              * (2 * Real.pi * n / ringRate (1200 * n * N) M (1 / 2) Δ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hK : 0 < 1200 * n * N := by positivity
  have hMr : (210000 : ℝ) * n ^ 2 * N ≤ M := by exact_mod_cast hM
  refine narrow_clock_packet_ticks (lo := 0) hn hK (by norm_num) (by norm_num) ?_
    (flatWindow_mem_range hn hM) (flatWindow_width hn hN) (flatAmpN N)
    (sum_norm_flatAmpN n hN) hΔ0 hΔ
  push_cast
  have hnsq : (n : ℝ) ≤ n ^ 2 := by nlinarith
  have : (n : ℝ) * N ≤ n ^ 2 * N := mul_le_mul_of_nonneg_right hnsq hN'.le
  nlinarith

/-- **The flat packet starts localised**: `1 − Re T(0) ≤ 1/N + 1/(4 K²)`, `K = 1200 n N`. -/
theorem flat_packet_start_le {n N M : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {μ : ℝ} (hμ : 1 ≤ μ) :
    1 - (transPhase (ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) (flatWindow n N)
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
  obtain ⟨hW, -⟩ := noWrap_distinct_of_window (L := M + 1) (flatWindow_mem_range hn hM)
  have hRe := re_transPhase_ringPacket_ge (L := M + 1) (c := 1) (μ := μ)
    (ℓ := ringLen (1200 * n * N)) hμ0 (ringLen_pos hK) hW
    (fun _ => 1 / Real.sqrt N) (fun _ => by positivity)
  rw [flatWindow, (flat_sums (600 * (n : ℤ) * N) hN).2] at hRe
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
  unfold flatWindow flatAmpN
  linarith

/-- **The flat packet's error rate**: non-negative and at most `1/(300 n K)`,
`K = 1200 n N`. -/
theorem flat_packet_limitErr_le {n N M : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {μ : ℝ} (hμ : 1 ≤ μ) :
    0 ≤ limitErr 1 μ (ringLen (1200 * n * N)) (1 / (600 * n)) (1 / 2)
          (ringLen (1200 * n * N) / (M + 1 : ℕ))
    ∧ limitErr 1 μ (ringLen (1200 * n * N)) (1 / (600 * n)) (1 / 2)
          (ringLen (1200 * n * N) / (M + 1 : ℕ))
      ≤ 1 / (1200 * (n : ℝ) * N) * (1 / (300 * n)) := by
  have hπ := Real.pi_pos
  have hπu : Real.pi < 3.15 := Real.pi_lt_d2
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hμ0 : 0 < μ := by linarith
  have hKr : ((1200 * n * N : ℕ) : ℝ) = 1200 * n * N := by push_cast; ring
  have hK0 : (0 : ℝ) < 1200 * n * N := by positivity
  have hLen : ringLen (1200 * n * N) = 2 * Real.pi * (1200 * n * N) := by rw [ringLen, hKr]
  have hMr : (210000 : ℝ) * n ^ 2 * N ≤ M := by exact_mod_cast hM
  have hM1 : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  have hM175 : 175 * n * (1200 * (n : ℝ) * N) ≤ ((M + 1 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  set a := ringLen (1200 * n * N) / ((M + 1 : ℕ) : ℝ) with had
  have ha0 : 0 ≤ a := by rw [had, hLen]; positivity
  have hale : a ≤ 1 / (27 * n) := by
    rw [had, hLen, div_le_div_iff₀ hM1 (by positivity)]
    have h1 : 2 * Real.pi * (1200 * (n : ℝ) * N) * (27 * n)
        = 54 * Real.pi * (n * (1200 * (n : ℝ) * N)) := by ring
    have h2 : 54 * Real.pi * (n * (1200 * (n : ℝ) * N))
        ≤ 54 * 3.15 * (n * (1200 * (n : ℝ) * N)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h3 : (0 : ℝ) ≤ n * (1200 * (n : ℝ) * N) := by positivity
    rw [h1, one_mul]
    nlinarith
  have ha2 : a ^ 2 ≤ 1 / (729 * n) := by
    have h := pow_le_pow_left₀ ha0 hale 2
    have e : (1 / (27 * (n : ℝ))) ^ 2 = 1 / (729 * n ^ 2) := by
      field_simp
      ring
    rw [e] at h
    refine h.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hinvμ : 1 / μ ≤ 1 := by rw [div_le_one hμ0]; exact hμ
  have hinvμ0 : 0 ≤ 1 / μ := by positivity
  have hinvK : 1 / (1200 * (n : ℝ) * N) ≤ 1 / (1200 * n) := by
    rw [div_le_div_iff₀ hK0 (by positivity)]
    nlinarith
  have hinvK0 : 0 ≤ 1 / (1200 * (n : ℝ) * N) := by positivity
  have hD : (0 : ℝ) ≤ 1 / (600 * n) := by positivity
  have herr : limitErr 1 μ (ringLen (1200 * n * N)) (1 / (600 * n)) (1 / 2) a
      = 1 / (1200 * (n : ℝ) * N) * (1 / μ * (1 / (600 * n) + 1 / (1200 * (n : ℝ) * N))
          + a ^ 2 * (1 / 8 + 1 / 48 * (1 / μ))) := by
    unfold limitErr
    rw [hLen]
    field_simp
    ring
  have ha20 : 0 ≤ a ^ 2 := sq_nonneg a
  have hc0 : 0 ≤ 1 / 8 + 1 / 48 * (1 / μ) := by linarith
  have hE0 : 0 ≤ 1 / μ * (1 / (600 * n) + 1 / (1200 * (n : ℝ) * N))
      + a ^ 2 * (1 / 8 + 1 / 48 * (1 / μ)) :=
    add_nonneg (mul_nonneg hinvμ0 (add_nonneg hD hinvK0)) (mul_nonneg ha20 hc0)
  have t1 : 1 / μ * (1 / (600 * n) + 1 / (1200 * (n : ℝ) * N))
      ≤ 1 * (1 / (600 * n) + 1 / (1200 * n)) :=
    mul_le_mul hinvμ (by linarith) (add_nonneg hD hinvK0) zero_le_one
  have t2 : a ^ 2 * (1 / 8 + 1 / 48 * (1 / μ)) ≤ 1 / (729 * n) * (1 / 8 + 1 / 48) :=
    mul_le_mul ha2 (by linarith) hc0 (by positivity)
  have e1 : (1 : ℝ) * (1 / (600 * n) + 1 / (1200 * n)) = 1 / (400 * n) := by
    field_simp
    ring
  have e2 : 1 / (729 * (n : ℝ)) * (1 / 8 + 1 / 48) = 7 / (34992 * n) := by
    field_simp
    ring
  have e3 : 1 / (400 * (n : ℝ)) + 7 / (34992 * n) ≤ 1 / (300 * n) := by
    have e4 : 1 / (400 * (n : ℝ)) + 7 / (34992 * n) = (1 / 400 + 7 / 34992) * (1 / n) := by
      field_simp
    have e5 : 1 / (300 * (n : ℝ)) = 1 / 300 * (1 / n) := by
      field_simp
    rw [e4, e5]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hE : 1 / μ * (1 / (600 * n) + 1 / (1200 * (n : ℝ) * N))
      + a ^ 2 * (1 / 8 + 1 / 48 * (1 / μ)) ≤ 1 / (300 * n) := by linarith
  rw [herr]
  exact ⟨mul_nonneg hinvK0 hE0, mul_le_mul_of_nonneg_left hE hinvK0⟩

/-- ★★ **The flat packet's budget.** For a level of rest energy `1 ≤ μ`, at every packet time
with `|t| ≤ 4π n/Δ`: `1 − Re T(0) + |t| · limitErr ≤ 1/N + 1/(20000 Δ n N)`. -/
theorem flat_packet_budget {n N M : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {μ : ℝ} (hμ : 1 ≤ μ) {Δ : ℝ} (hΔ0 : 0 < Δ)
    (hΔ : Δ ≤ 1 / 2) {t : ℝ} (ht : |t| ≤ 4 * Real.pi * n / Δ) :
    1 - (transPhase (ringPacket (L := M + 1) 1 μ (ringLen (1200 * n * N)) (flatWindow n N)
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
  have hstart := flat_packet_start_le hn hN hM hμ
  obtain ⟨hrate0, hrate⟩ := flat_packet_limitErr_le hn hN hM hμ
  have hdrift : |t| * limitErr 1 μ (ringLen (1200 * n * N)) (1 / (600 * n)) (1 / 2)
        (ringLen (1200 * n * N) / (M + 1 : ℕ))
      ≤ 4 * Real.pi * n / Δ * (1 / (1200 * (n : ℝ) * N) * (1 / (300 * n))) :=
    mul_le_mul ht hrate hrate0 (by positivity)
  -- in the unit `y = 1/(Δ n N)`
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

/-- ★★★ **The flat clock packet stays where it is predicted to be while it ticks.** For the
packet of `flat_clock_packet_ticks`, at every packet time `t` with `|t| ≤ 4π n/Δ` (which
covers the whole horizon of `n` ticks) and every region `B` whose sites lie at
`cos(2πk/L − Ω_i t) ≤ γ` from the predicted direction of each level, `Ω_i = v_i(1/2)/K`:

`(weight of the clock on B) · (1 − γ) ≤ 1/N + 1/(20000 Δ n N)`. -/
theorem flat_clock_packet_localised {n N M : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2)
    {B : Finset (ZMod (M + 1))} {γ t : ℝ} (ht : |t| ≤ 4 * Real.pi * n / Δ)
    (hB0 : ∀ k ∈ B, Real.cos (2 * Real.pi * k.val / (M + 1 : ℕ)
      - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 1 (1 / 2) * t) ≤ γ)
    (hB1 : ∀ k ∈ B, Real.cos (2 * Real.pi * k.val / (M + 1 : ℕ)
      - 2 * Real.pi / ringLen (1200 * n * N) * vRel 1 (1 + Δ) (1 / 2) * t) ≤ γ) :
    deviceRegionWeight (devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
        (flatWindow n N) (flatAmpN N) t) B * (1 - γ)
      ≤ 1 / N + 1 / (20000 * Δ * n * N) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : 0 < 1200 * n * N := by positivity
  have hWD : ∀ m ∈ flatWindow n N,
      |2 * Real.pi * m / ringLen (1200 * n * N) - 1 / 2| ≤ 1 / (600 * n) := by
    intro m hm
    have hK' : (0 : ℝ) < ((1200 * n * N : ℕ) : ℝ) := by exact_mod_cast hK
    have e : 2 * Real.pi * (m : ℝ) / ringLen (1200 * n * N)
        = (m : ℝ) / ((1200 * n * N : ℕ) : ℝ) := by
      rw [ringLen]
      have := Real.pi_pos
      field_simp
    rw [e]
    exact flatWindow_width hn hN m hm
  have h := deviceRegionWeight_devicePacket_le (L := M + 1) (c := 1) (μ₀ := 1) (μ₁ := 1 + Δ)
    (ℓ := ringLen (1200 * n * N)) (P := 1 / 2) (D := 1 / (600 * n)) (p₀ := 1 / 2) one_pos
    one_pos (by linarith) (ringLen_pos hK) (by rw [abs_of_pos (by norm_num)]) (by positivity)
    (flatWindow_mem_range hn hM) hWD (flatAmpN N) (sum_norm_flatAmpN n hN) (B := B) (γ := γ) t
    (fun k hk => by rw [one_mul]; exact hB0 k hk) (fun k hk => by rw [one_mul]; exact hB1 k hk)
  have b0 := flat_packet_budget hn hN hM (μ := 1) le_rfl hΔ0 hΔ ht
  have b1 := flat_packet_budget hn hN hM (μ := 1 + Δ) (by linarith) hΔ0 hΔ ht
  have hgoal : deviceRegionWeight (devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1
      (1 + Δ) (flatWindow n N) (flatAmpN N) t) B
      = deviceRegionWeight (devicePacket (L := M + 1)
        (scaledHop 1 (ringLen (1200 * n * N) / ((M + 1 : ℕ) : ℝ))) 1 (1 + Δ)
        (flatWindow n N) (flatAmpN N) t) B := rfl
  rw [hgoal]
  linarith

/-- The horizon of `n` ticks lies inside the range of `flat_clock_packet_localised`: a flow
time `s` in `[0, 2π n/R]` is the packet time `s − π/(2R)`, of size at most `4π n/Δ`. -/
theorem abs_sub_quarter_turn_le {n : ℕ} (hn : 0 < n) {R Δ s : ℝ} (hΔ0 : 0 < Δ)
    (hR : Δ / 2 ≤ R) (hs0 : 0 ≤ s) (hs : s ≤ 2 * Real.pi * n / R) :
    |s - Real.pi / (2 * R)| ≤ 4 * Real.pi * n / Δ := by
  have hπ := Real.pi_pos
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hR0 : 0 < R := by linarith
  have h1 : 2 * Real.pi * n / R ≤ 4 * Real.pi * n / Δ := by
    rw [div_le_div_iff₀ hR0 hΔ0]
    nlinarith [mul_pos hπ (lt_of_lt_of_le one_pos hn')]
  have h2 : Real.pi / (2 * R) ≤ 2 * Real.pi * n / R := by
    rw [div_le_div_iff₀ (by positivity) hR0]
    nlinarith [mul_pos hπ hR0, mul_nonneg (mul_pos hπ hR0).le (sub_nonneg.2 hn')]
  have h3 : 0 ≤ Real.pi / (2 * R) := by positivity
  rw [abs_le]
  constructor <;> linarith

end CSD.RecordLayer

end
