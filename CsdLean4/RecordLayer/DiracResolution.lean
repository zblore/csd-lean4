/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracMasslessTails

/-!
# The records' resolution: tails and encounters at any number of modes and any chord

**Category:** 7-SigmaLayer (the record layer). BACKLOG #280, lever (b), first four bricks;
lever (a), first three bricks.

#278's Lorentz map holds to `≈ 23%`, and #280's diagnosis traces that error to the localisation
bound: the only fact about where a massless packet is that the record chain uses is the mean of
its angle, `1 − Re transPhase = 1/N` for the flat profile over `N` modes, turned by Chebyshev into
a weight `≤ 2/(Nρ²)` off a chord-`ρ` arc. At `N = 2·10⁶` that forces chords of `1/100`–`1/5`.
This brick states the bound **at every `N`**, so the record chain can be re-run with the
resolution as a parameter.

## The tail

* ★ `re_transPhase_flat_zero` (**the flat massless packet over `N` modes has
  `Re transPhase = 1 − 1/N` at time `0`**);
* ★★ `flat_massless_tail` (**off the chord-`ρ` arc about its predicted angle, a flat massless
  packet over `N` modes has weight at most `2 (1/N + |t| · masslessErr) / (ρ − η)²`**);
* ★★ `flat_massless_tail_le` (**the chord law**: if `(ρ − η)² ≥ 4/(N ε)` and the drift
  `|t| · masslessErr` is at most `1/N`, the weight off the arc is at most `ε` — at a fixed tail `ε`
  the chord shrinks as `N^{−1/2}`).

## The devices' tails at any number of modes

* ★ `re_transPhase_flat_massive_ge` (**a flat massive packet over `N` modes has
  `Re transPhase ≥ 1 − 1/N − (π/(ℓμ))²`**, the second term the spin overlap's loss, `~10⁻²⁷` at the
  arenas' `ℓ`, `μ`);
* ★★ `flat_device_tail` (**a two-level device over `N` flat modes has weight off the chord-`ρ` arc
  at most `Σᵢ (1/N + (π/(ℓμᵢ))² + |t|·limitErrᵢ)/(ρ − η)²`**), ★★ `flat_device_tail_le` (**the
  devices' chord law**: `(ρ − η)² ≥ 4/(Nε)` and each level's loss plus drift `≤ 1/N` give tail
  `≤ ε`).

## The encounter law at any chord

* `exp_I_mul_star_exp_I` (the relative phase of two points on the circle);
* ★★ `encounter_near_of_tails`, ★★ `encounter_far_of_tails` (**two normalised states with tails
  `ε_A`, `ε_B` off chord-`ρ_A`, `ρ_B` arcs: if their predicted relative position is within
  `ρ − ρ_A − ρ_B` of `w`, the encounter weight with window chord `ρ` is at least
  `(1 − ε_A)(1 − ε_B)`; beyond `ρ + ρ_A + ρ_B`, at most `ε_A + ε_B`**);
* ★★ `encounter_near_angle`, ★★ `encounter_far_angle` (the same by the predicted angles: near for
  `|β − α| ≤ ρ − ρ_A − ρ_B`, far once `ρ + ρ_A + ρ_B < 2 sin(y/2)` for `y ≤ |β − α| ≤ 2π − y` — the
  encounter's window in time is the chord over the relative angular speed, and with the chord law
  every chord in it can shrink as `N^{−1/2}`).

## The record window law

* ★★★ `record_window` (**a threshold register whose rate is in `[0, M]`, which holds `P'`–`P` at
  `t₀`, whose rate vanishes until `a` and is at least `κ` from `c`: it is below `θ` before
  `a + (θ − P)/M` and has reached `θ` by `c + (θ − P')/κ`** — the record's window, its width the
  gap `c − a` plus the two fill times);
* ★★★ `encounter_record_window` (**the encounter record at any chord**: for two trajectories with
  tails `ε_A`, `ε_B` off chord-`ρ_A`, `ρ_B` arcs, relative angle `Ω (s − t_c)`, and a register at
  rate `max(relWeight 1 ρ − 1/2, 0)`, the record falls in
  `[t_c − y/Ω + 2θ, t_c − (ρ − ρ_A − ρ_B)/Ω + θ/κ]`, `κ = (1 − ε_A)(1 − ε_B) − 1/2`, `y` a far
  angle with `ρ + ρ_A + ρ_B < 2 sin(y/2)` — **the record's error is the chords over the relative
  angular speed plus the threshold's fill time**, every term of which the chord law shrinks).

## Lever (a): the quadratic drift

* ★★ `le_re_sum_phase` (**`Σ w_i e^{iΔ_i t}` with `w_i ≥ 0` and `|Δ_i − Ω| ≤ δ`, read against
  `e^{iΩt}`, keeps `(1 − (δt)²/2) Σ w_i` of its real part** — `cos x ≥ 1 − x²/2` where
  `norm_sum_phase_sub_le` uses `|e^{ix} − 1| ≤ |x|`);
* ★★★ `regionWeight_compl_chordArc_quad` (**a massive packet with real nonnegative amplitudes and
  nonnegative neighbour spin overlaps has weight off the chord-`ρ` arc about its group-velocity
  angle, times `(ρ − η)²/2`, at most `1 − Re transPhase(0) + (δ' t)²/2`** — the drift quadratic in
  `δ' t`, `δ' = vgLip · (2π/L)(δ + 2π/L)`; at the arenas' `δ' t ≈ 2.7·10⁻⁷` it is `~4·10⁻¹⁴`
  against the linear `2.7·10⁻⁷`, so the optimum number of modes moves up and the localisation
  floor is set by the profile's `1 − Re transPhase(0)`).

## Lever (a): the sine profile

* `sum_Ico_int_eq_sum_range` (an integer window's sum as a shifted `range` sum);
* ★★ `sine_neighbour_sum` (**the discrete box's ground state `g i = sin(π(i + 1)/(n + 1))`:
  `Σ g(i+1) g(i) = cos(π/(n + 1)) · Σ g(i)²`**, from `sin(x − h) + sin(x + h) = 2 sin x cos h` and
  the zero ends);
* `sineNorm`, `sineNorm_pos`, ★ `sineAmp` (the normalised sine profile on `[lo, lo + n)`),
  `sineAmp_nonneg`, `sineAmp_of_lt`, ★★ `sineAmp_sums` (**`Σ β² = 1`, `Σ β_{m+1} β_m =
  cos(π/(n + 1))`**);
* ★★★ `sine_packet_tail` (**a massive packet with the sine profile over `n` modes: tail
  `× (ρ − η)²/2 ≤ (π/(n + 1))²/2 + κ + (δ' t)²/2`** — the profile's floor `~π²/(2n²)` against the
  flat profile's `1/n`, the drift quadratic; at `μ = 3`, `T ≈ 8·10¹³` the optimum is near
  `n ≈ 1.5·10⁷` with floor `≈ 4·10⁻¹³` and a chord at a 1% tail of `≈ 10⁻⁵`, against `1.75·10⁻²`
  for the arenas' observers — estimates, the instance is not built);
* ★★★ `sine_massless_tail` (**the massless messenger with the sine profile: tail
  `× (ρ − η)²/2 ≤ (π/(n + 1))²/2 + (δ'' t)²/2`** — no spin loss, the drift quadratic).

## The resolution law, assembled

The chain is now generic end to end: a packet's tail (`sine_packet_tail`, `sine_massless_tail`:
floor `F ≈ (π/n)²/2 + (δ t)²/2`) gives a chord `ρ ≈ √(2F/ε)` at tail `ε`; two chords give an
encounter (`encounter_near_angle`, `encounter_far_angle`); an encounter gives a record whose
window is `≈ 2(ρ_A + ρ_B)/Ω` plus the threshold's fill time (`encounter_record_window`). **A
record's timing error therefore scales as `√F / Ω`**, and `F` is minimised where the profile's
`1/n²` meets the spreading `(δ t)²`, `δ ∝ n/μ` — the trade-off of the standard quantum limit
`√(T/μ)`. The absolute numbers depend on the arenas' arbitrary `μ`, splitting, ring size and
speeds; the scaling does not.

## Honest scope

⚠️ **Chebyshev only**: the bound uses the second moment of the angle; the flat profile's true
tail decays like `1/(Nρ)` (Dirichlet kernel, estimate), so this is lever (b) of #280, not (a).

⚠️ **Single encounters from an empty register**: the relay's pulse and echo, and `B`'s return
after its departure plateau (`record_window` with `P' ≤ P`), are applied in the next brick, an
instance at large `N`; the drift term grows with `|t|`, and
keeping it below `1/N` bounds the time span at a given lattice spacing.

References: `specs/BACKLOG.md` #280, #278, #248; `CV/DiracPacketLimit.lean` (`one_sub_le_spinCos`,
`re_transPhase_unitAmp_ge`, `filter_succ_Ico`); `CV/DiracPacket.lean` (`transPhase_packet`,
`transPhase_drift`, `abs_bandE_step_sub_le`, `norm_sum_phase_sub_le`);
`RecordLayer/DiracMasslessTails.lean` (`regionWeight_compl_chordArc_massless_le`,
`bMess_re_transPhase_zero`, `bMess_tail`);
`CV/DiracMassless.lean` (`re_transPhase_unitAmp_zero`, `masslessErr`); `CV/DiracPacketLimit.lean`
(`flat_sums`, `flat_packet_localised`); `RecordLayer/DiracTwoCharts.lean` (`lorentz_chart_bounds`);
`RecordLayer/DiracObservers.lean` (`le_relWeight`, `relWeight_le`, `two_sin_le_norm_exp_sub_one`);
`RecordLayer/DiracDoppler.lean` (`offset_mem_of_near_at`, `offset_not_mem_of_far_at`);
`RecordLayer/DiracRelayA.lean` (`aEncounter_near`, `aEncounter_far`, `rest_tail_fine`);
`RecordLayer/DiracArrival.lean` (`re_transPhase_ringPacket_ge`);
`RecordLayer/DiracObservers.lean` (`devRegionWeight_compl_chordArc_le`, `regDetector`,
`relWeight_le_mul`); `RecordLayer/DiracBRadar.lean` (`bEmission`, `bReturn`).
-/

@[expose] public section

open Set Complex CSD.CV CSD.SigmaLayer

namespace CSD.RecordLayer

variable {L : ℕ} [NeZero L] {ℓ D p₀ : ℝ} {lo : ℤ} {N : ℕ}

/-- ★ **The flat massless packet's angle at time `0`**: over `N` consecutive modes inside one
period of the ring and inside the right-moving window, `Re transPhase = 1 − 1/N`. -/
theorem re_transPhase_flat_zero (hN : 0 < N) (hℓ : 0 < ℓ)
    (hWin : ∀ m ∈ Finset.Ico lo (lo + N), lo ≤ m ∧ m + 1 < lo + L)
    (hR : RightWindow L (Finset.Ico lo (lo + N))) :
    (transPhase (ringPacket (L := L) 1 0 ℓ (Finset.Ico lo (lo + N))
      (fun _ => ((1 / Real.sqrt N : ℝ) : ℂ)) 0)).re = 1 - 1 / N := by
  obtain ⟨hW, -⟩ := noWrap_distinct_of_window (L := L) hWin
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hJ : 0 < scaledHop 1 (ℓ / L) := by
    unfold scaledHop
    positivity
  have h := re_transPhase_unitAmp_zero (L := L) (J := scaledHop 1 (ℓ / L)) hJ hR hW
    (fun _ => 1 / Real.sqrt N)
  obtain ⟨-, h2⟩ := flat_sums lo hN
  rw [ringPacket]
  exact h.trans h2

/-- ★★ **The flat massless packet's tail at any number of modes.** Off the chord-`ρ` arc about a
point `z` within `η` of its predicted angle at time `t`, a flat massless packet over `N` modes
(spread `D` about `p₀`) has weight at most `2 (1/N + |t| · masslessErr) / (ρ − η)²`. -/
theorem flat_massless_tail (hN : 0 < N) (hNL : N < L) (hℓ : 0 < ℓ) (hD0 : 0 ≤ D)
    (hWin : ∀ m ∈ Finset.Ico lo (lo + N), lo ≤ m ∧ m + 1 < lo + L)
    (hR : RightWindow L (Finset.Ico lo (lo + N)))
    (hWD : ∀ m ∈ Finset.Ico lo (lo + N), |2 * Real.pi * m / ℓ - p₀| ≤ D)
    {z : ℂ} {ρ η : ℝ} (hηρ : η < ρ) (t : ℝ)
    (hz : ‖exp (I * ((2 * Real.pi / ℓ * (1 * Real.cos (ℓ / L * p₀)) * t : ℝ) : ℂ)) - z‖ ≤ η) :
    regionWeight (ringPacket (L := L) 1 0 ℓ (Finset.Ico lo (lo + N))
        (fun _ => ((1 / Real.sqrt N : ℝ) : ℂ)) t) (chordArc z ρ)ᶜ
      ≤ 2 * (1 / N + |t| * masslessErr 1 ℓ D (ℓ / L)) / (ρ - η) ^ 2 := by
  have hβ := (flat_packet_localised (L := L) (c := 1) (μ := 1) (ℓ := ℓ) one_pos hℓ lo hN hNL).1
  have h := regionWeight_compl_chordArc_massless_le (L := L) (c := 1) (D := D) (p₀ := p₀) one_pos
    hℓ hD0 hWin hR hWD (fun _ => ((1 / Real.sqrt N : ℝ) : ℂ)) hβ hηρ.le t hz
  rw [re_transPhase_flat_zero hN hℓ hWin hR] at h
  have hpos : 0 < (ρ - η) ^ 2 := pow_pos (by linarith) 2
  rw [le_div_iff₀ hpos]
  linarith

/-- ★★ **The chord law.** If the chord clears `η` by `√(4/(N ε))` and the drift `|t| · masslessErr`
is at most `1/N`, the weight off the arc is at most `ε`: at a fixed tail the chord shrinks as
`N^{−1/2}`. -/
theorem flat_massless_tail_le (hN : 0 < N) (hNL : N < L) (hℓ : 0 < ℓ) (hD0 : 0 ≤ D)
    (hWin : ∀ m ∈ Finset.Ico lo (lo + N), lo ≤ m ∧ m + 1 < lo + L)
    (hR : RightWindow L (Finset.Ico lo (lo + N)))
    (hWD : ∀ m ∈ Finset.Ico lo (lo + N), |2 * Real.pi * m / ℓ - p₀| ≤ D)
    {z : ℂ} {ρ η ε : ℝ} (hε : 0 < ε) (hηρ : η < ρ) (hchord : 4 / (N * ε) ≤ (ρ - η) ^ 2) (t : ℝ)
    (hdrift : |t| * masslessErr 1 ℓ D (ℓ / L) ≤ 1 / N)
    (hz : ‖exp (I * ((2 * Real.pi / ℓ * (1 * Real.cos (ℓ / L * p₀)) * t : ℝ) : ℂ)) - z‖ ≤ η) :
    regionWeight (ringPacket (L := L) 1 0 ℓ (Finset.Ico lo (lo + N))
        (fun _ => ((1 / Real.sqrt N : ℝ) : ℂ)) t) (chordArc z ρ)ᶜ ≤ ε := by
  have h := flat_massless_tail hN hNL hℓ hD0 hWin hR hWD hηρ t hz
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 < (ρ - η) ^ 2 := pow_pos (by linarith) 2
  refine h.trans ?_
  rw [div_le_iff₀ hpos]
  have h4 : 4 / N ≤ ε * (ρ - η) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hchord hε.le
    rwa [show ε * (4 / (N * ε)) = 4 / N by field_simp] at this
  have : 2 * (1 / N + |t| * masslessErr 1 ℓ D (ℓ / L)) ≤ 4 / N := by
    rw [show (4 : ℝ) / N = 2 * (1 / N + 1 / N) by ring]
    linarith
  linarith

/-! ### The devices' tails at any number of modes -/

/-- ★ **A flat massive packet's angle at time `0`**: over `N` consecutive modes inside one period
of the ring, `Re transPhase ≥ 1 − 1/N − (π/(ℓμ))²` — the second term the spin overlap's loss. -/
theorem re_transPhase_flat_massive_ge {μ : ℝ} (hN : 0 < N) (hμ : 0 < μ) (hℓ : 0 < ℓ)
    (hWin : ∀ m ∈ Finset.Ico lo (lo + N), lo ≤ m ∧ m + 1 < lo + L) :
    1 - 1 / N - (Real.pi / (ℓ * μ)) ^ 2
      ≤ (transPhase (ringPacket (L := L) 1 μ ℓ (Finset.Ico lo (lo + N))
        (fun _ => ((1 / Real.sqrt N : ℝ) : ℂ)) 0)).re := by
  obtain ⟨hW, -⟩ := noWrap_distinct_of_window (L := L) hWin
  have hRe := re_transPhase_ringPacket_ge (L := L) (c := 1) (μ := μ) (ℓ := ℓ) hμ hℓ hW
    (fun _ => 1 / Real.sqrt N) (fun _ => by positivity)
  rw [(flat_sums lo hN).2, mul_one] at hRe
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hκ : 0 ≤ (Real.pi / (ℓ * μ)) ^ 2 / N := by positivity
  have e : (1 - (Real.pi / (ℓ * μ)) ^ 2) * (1 - 1 / N)
      = 1 - 1 / N - (Real.pi / (ℓ * μ)) ^ 2 + (Real.pi / (ℓ * μ)) ^ 2 / N := by ring
  linarith

/-- ★★ **A flat device's tail at any number of modes.** Off the chord-`ρ` arc about a point within
`η` of both levels' predicted angles, a device over `N` flat modes (rest energies `μ₀ ≤ μ₁`, spread
`D` about `p₀`, `|p₀| ≤ P`) has weight at most
`Σᵢ (1/N + (π/(ℓμᵢ))² + |t| · limitErrᵢ) / (ρ − η)²`. -/
theorem flat_device_tail {μ₀ μ₁ P : ℝ} (hN : 0 < N) (hNL : N < L) (h0 : 0 < μ₀) (h01 : μ₀ ≤ μ₁)
    (hℓ : 0 < ℓ) (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D)
    (hWin : ∀ m ∈ Finset.Ico lo (lo + N), lo ≤ m ∧ m + 1 < lo + L)
    (hWD : ∀ m ∈ Finset.Ico lo (lo + N), |2 * Real.pi * m / ℓ - p₀| ≤ D)
    {z : ℂ} {ρ η : ℝ} (hηρ : η < ρ) (t : ℝ)
    (hz₀ : ‖exp (I * ((2 * Real.pi / ℓ * vRel 1 μ₀ (1 * p₀) * t : ℝ) : ℂ)) - z‖ ≤ η)
    (hz₁ : ‖exp (I * ((2 * Real.pi / ℓ * vRel 1 μ₁ (1 * p₀) * t : ℝ) : ℂ)) - z‖ ≤ η) :
    devRegionWeight (devicePacket (L := L) (scaledHop 1 (ℓ / L)) μ₀ μ₁ (Finset.Ico lo (lo + N))
        (fun _ => ((1 / Real.sqrt N : ℝ) : ℂ)) t) (chordArc z ρ)ᶜ
      ≤ ((1 / N + (Real.pi / (ℓ * μ₀)) ^ 2 + |t| * limitErr 1 μ₀ ℓ D P (ℓ / L))
        + (1 / N + (Real.pi / (ℓ * μ₁)) ^ 2 + |t| * limitErr 1 μ₁ ℓ D P (ℓ / L)))
        / (ρ - η) ^ 2 := by
  have hβ := (flat_packet_localised (L := L) (c := 1) (μ := 1) (ℓ := ℓ) one_pos hℓ lo hN hNL).1
  have h := devRegionWeight_compl_chordArc_le (L := L) (c := 1) one_pos h0 h01 hℓ hp₀ hD0 hWin hWD
    (fun _ => ((1 / Real.sqrt N : ℝ) : ℂ)) hβ hηρ.le t hz₀ hz₁
  have r0 := re_transPhase_flat_massive_ge (L := L) hN h0 hℓ hWin
  have r1 := re_transPhase_flat_massive_ge (L := L) hN (h0.trans_le h01) hℓ hWin
  have hpos : 0 < (ρ - η) ^ 2 := pow_pos (by linarith) 2
  rw [le_div_iff₀ hpos]
  linarith

/-- ★★ **The devices' chord law.** If the chord clears `η` by `√(4/(N ε))` and, for each level,
the spin-overlap loss plus the drift is at most `1/N`, the device's weight off the arc is at most
`ε`. -/
theorem flat_device_tail_le {μ₀ μ₁ P : ℝ} (hN : 0 < N) (hNL : N < L) (h0 : 0 < μ₀)
    (h01 : μ₀ ≤ μ₁) (hℓ : 0 < ℓ) (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D)
    (hWin : ∀ m ∈ Finset.Ico lo (lo + N), lo ≤ m ∧ m + 1 < lo + L)
    (hWD : ∀ m ∈ Finset.Ico lo (lo + N), |2 * Real.pi * m / ℓ - p₀| ≤ D)
    {z : ℂ} {ρ η ε : ℝ} (hε : 0 < ε) (hηρ : η < ρ) (hchord : 4 / (N * ε) ≤ (ρ - η) ^ 2) (t : ℝ)
    (hb₀ : (Real.pi / (ℓ * μ₀)) ^ 2 + |t| * limitErr 1 μ₀ ℓ D P (ℓ / L) ≤ 1 / N)
    (hb₁ : (Real.pi / (ℓ * μ₁)) ^ 2 + |t| * limitErr 1 μ₁ ℓ D P (ℓ / L) ≤ 1 / N)
    (hz₀ : ‖exp (I * ((2 * Real.pi / ℓ * vRel 1 μ₀ (1 * p₀) * t : ℝ) : ℂ)) - z‖ ≤ η)
    (hz₁ : ‖exp (I * ((2 * Real.pi / ℓ * vRel 1 μ₁ (1 * p₀) * t : ℝ) : ℂ)) - z‖ ≤ η) :
    devRegionWeight (devicePacket (L := L) (scaledHop 1 (ℓ / L)) μ₀ μ₁ (Finset.Ico lo (lo + N))
        (fun _ => ((1 / Real.sqrt N : ℝ) : ℂ)) t) (chordArc z ρ)ᶜ ≤ ε := by
  have h := flat_device_tail hN hNL h0 h01 hℓ hp₀ hD0 hWin hWD hηρ t hz₀ hz₁
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 < (ρ - η) ^ 2 := pow_pos (by linarith) 2
  refine h.trans ?_
  rw [div_le_iff₀ hpos]
  have h4 : 4 / N ≤ ε * (ρ - η) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hchord hε.le
    rwa [show ε * (4 / (N * ε)) = 4 / N by field_simp] at this
  have : (1 / N + (Real.pi / (ℓ * μ₀)) ^ 2 + |t| * limitErr 1 μ₀ ℓ D P (ℓ / L))
      + (1 / N + (Real.pi / (ℓ * μ₁)) ^ 2 + |t| * limitErr 1 μ₁ ℓ D P (ℓ / L)) ≤ 4 / N := by
    rw [show (4 : ℝ) / N = 1 / N + 1 / N + 1 / N + 1 / N by ring]
    linarith
  linarith

/-! ### The encounter law at any chord -/

section Encounter

variable {ΨA ΨB : (ZMod L × Fin 2) × Fin 2 → ℂ} {uA uB w : ℂ} {ρA ρB ρ εA εB : ℝ}

/-- The relative phase of two points on the unit circle. -/
theorem exp_I_mul_star_exp_I (α β : ℝ) :
    exp (I * (β : ℂ)) * star (exp (I * (α : ℂ))) = exp (I * ((β - α : ℝ) : ℂ)) := by
  show exp (I * (β : ℂ)) * (starRingEnd ℂ) (exp (I * (α : ℂ))) = _
  rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- ★★ **Near, at any chord.** Two normalised states, each with weight at most `ε` off its
chord-`ρ_•` arc about a predicted point: if the predicted relative position is within
`ρ − ρ_A − ρ_B` of `w`, the encounter weight with window chord `ρ` is at least
`(1 − ε_A)(1 − ε_B)`. -/
theorem encounter_near_of_tails (huB : ‖uB‖ = 1) (hA1 : devRegionWeight ΨA Finset.univ = 1)
    (hB1 : devRegionWeight ΨB Finset.univ = 1)
    (htA : devRegionWeight ΨA (chordArc uA ρA)ᶜ ≤ εA)
    (htB : devRegionWeight ΨB (chordArc uB ρB)ᶜ ≤ εB) (hεB : εB ≤ 1)
    (h : ‖uB * star uA - w‖ + ρA + ρB ≤ ρ) :
    (1 - εA) * (1 - εB) ≤ relWeight w ρ ΨA ΨB := by
  have hX := devRegionWeight_add_compl ΨA (chordArc uA ρA)
  have hY := devRegionWeight_add_compl ΨB (chordArc uB ρB)
  rw [hA1] at hX
  rw [hB1] at hY
  have hle := le_relWeight (w := w) (ρ := ρ) (ΨA := ΨA) (ΨB := ΨB) (X := chordArc uA ρA)
    (Y := chordArc uB ρB) fun j hj k hk =>
      offset_mem_of_near_at huB (mem_chordArc.1 hj) (mem_chordArc.1 hk) h
  calc (1 - εA) * (1 - εB)
      ≤ devRegionWeight ΨA (chordArc uA ρA) * devRegionWeight ΨB (chordArc uB ρB) :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (devRegionWeight_nonneg _ _)
    _ ≤ _ := hle

/-- ★★ **Far, at any chord.** With the same tails, if the predicted relative position is more
than `ρ + ρ_A + ρ_B` from `w`, the encounter weight is at most `ε_A + ε_B`. -/
theorem encounter_far_of_tails (huB : ‖uB‖ = 1) (hA1 : devRegionWeight ΨA Finset.univ = 1)
    (hB1 : devRegionWeight ΨB Finset.univ = 1)
    (htA : devRegionWeight ΨA (chordArc uA ρA)ᶜ ≤ εA)
    (htB : devRegionWeight ΨB (chordArc uB ρB)ᶜ ≤ εB)
    (h : ρ + ρA + ρB < ‖uB * star uA - w‖) :
    relWeight w ρ ΨA ΨB ≤ εA + εB := by
  have hle := relWeight_le (w := w) (ρ := ρ) (ΨA := ΨA) (ΨB := ΨB) (X := chordArc uA ρA)
    (Y := chordArc uB ρB) fun j hj k hk =>
      offset_not_mem_of_far_at huB (mem_chordArc.1 hj) (mem_chordArc.1 hk) h
  rw [hA1, hB1, mul_one, one_mul] at hle
  linarith

/-- ★★ **Near, by the angle.** For predicted angles `α`, `β` of the two states, if
`|β − α| ≤ ρ − ρ_A − ρ_B` the encounter weight (window about `1`) is at least
`(1 − ε_A)(1 − ε_B)`: the near window in time is the chord margin over the relative angular
speed. -/
theorem encounter_near_angle {α β : ℝ} (hA1 : devRegionWeight ΨA Finset.univ = 1)
    (hB1 : devRegionWeight ΨB Finset.univ = 1)
    (htA : devRegionWeight ΨA (chordArc (exp (I * (α : ℂ))) ρA)ᶜ ≤ εA)
    (htB : devRegionWeight ΨB (chordArc (exp (I * (β : ℂ))) ρB)ᶜ ≤ εB) (hεB : εB ≤ 1)
    (h : |β - α| ≤ ρ - ρA - ρB) :
    (1 - εA) * (1 - εB) ≤ relWeight 1 ρ ΨA ΨB := by
  refine encounter_near_of_tails (norm_exp_I_mul_ofReal_eq_one β) hA1 hB1 htA htB hεB ?_
  have e := exp_I_mul_star_exp_I α β
  have h0 := norm_exp_sub_exp_le (β - α) 0
  rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_zero] at h0
  rw [e]
  linarith

/-- ★★ **Far, by the angle.** If the relative angle `β − α` is at least `y` from every multiple of
`2π` and `ρ + ρ_A + ρ_B < 2 sin(y/2)`, the encounter weight is at most `ε_A + ε_B`. -/
theorem encounter_far_angle {α β y : ℝ} (hA1 : devRegionWeight ΨA Finset.univ = 1)
    (hB1 : devRegionWeight ΨB Finset.univ = 1)
    (htA : devRegionWeight ΨA (chordArc (exp (I * (α : ℂ))) ρA)ᶜ ≤ εA)
    (htB : devRegionWeight ΨB (chordArc (exp (I * (β : ℂ))) ρB)ᶜ ≤ εB) (hy : 0 ≤ y)
    (h1 : y ≤ |β - α|) (h2 : |β - α| ≤ 2 * Real.pi - y)
    (hsin : ρ + ρA + ρB < 2 * Real.sin (y / 2)) :
    relWeight 1 ρ ΨA ΨB ≤ εA + εB := by
  refine encounter_far_of_tails (norm_exp_I_mul_ofReal_eq_one β) hA1 hB1 htA htB ?_
  have e := exp_I_mul_star_exp_I α β
  rw [e]
  exact hsin.trans_le (two_sin_le_norm_exp_sub_one hy h1 h2)

end Encounter


/-! ### The record window law -/

/-- ★★★ **The record window law.** A register whose rate `F` is continuous, nonnegative from `0`
on and at most `M`, which holds between `P'` and `P` at time `t₀`, whose rate vanishes from `t₀`
to `a` and is at least `κ` from `c` on: it stays below the threshold `θ > P` before
`a + (θ − P)/M`, and has reached it by `c + (θ − P')/κ`. These are the two hypotheses of a threshold
record (`regDetector`), so the record's window is `[a + (θ − P)/M, c + (θ − P')/κ]` — its width is
the gap `c − a` between the last zero and the first near time plus the two fill times. -/
theorem record_window {F : ℝ → ℝ} (hF : Continuous F) {M κ θ P P' t₀ a c : ℝ} (hM : 0 < M)
    (hκ : 0 < κ) (ht₀ : 0 ≤ t₀) (hta : t₀ ≤ a) (hac : a ≤ c)
    (hpos : ∀ s, 0 ≤ s → 0 ≤ F s) (hle : ∀ s, F s ≤ M)
    (hP : ∫ s in (0 : ℝ)..t₀, F s ≤ P) (hP' : P' ≤ ∫ s in (0 : ℝ)..t₀, F s) (hPθ : P < θ)
    (hzero : ∀ s, t₀ ≤ s → s ≤ a → F s = 0)
    (hnear : ∀ s, c ≤ s → s ≤ c + (θ - P') / κ → κ ≤ F s) :
    (∀ t, 0 ≤ t → t < a + (θ - P) / M → ∫ s in (0 : ℝ)..t, F s < θ)
    ∧ θ ≤ ∫ s in (0 : ℝ)..(c + (θ - P') / κ), F s := by
  have hi : ∀ x y : ℝ, IntervalIntegrable F MeasureTheory.volume x y :=
    fun x y => hF.intervalIntegrable x y
  have hnn : ∀ x y : ℝ, 0 ≤ x → x ≤ y → 0 ≤ ∫ s in x..y, F s := fun x y hx hxy =>
    intervalIntegral.integral_nonneg hxy fun s hs => hpos s (hx.trans hs.1)
  have hz : ∀ y, t₀ ≤ y → y ≤ a → ∫ s in t₀..y, F s = 0 := fun y h1 h2 => by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_]
    · exact intervalIntegral.integral_zero
    · rw [Set.uIcc_of_le h1] at hs
      exact hzero s hs.1 (hs.2.trans h2)
  have hup : ∀ x y : ℝ, x ≤ y → ∫ s in x..y, F s ≤ M * (y - x) := fun x y hxy => by
    have h := intervalIntegral.integral_mono_on hxy (hi x y)
      (intervalIntegrable_const (μ := MeasureTheory.volume) (c := M)) fun s _ => hle s
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    linarith
  have hfill : 0 ≤ (θ - P') / κ := div_nonneg (by linarith) hκ.le
  refine ⟨fun t ht0 ht => ?_, ?_⟩
  · rcases le_total t t₀ with h1 | h1
    · have e := intervalIntegral.integral_add_adjacent_intervals (hi 0 t) (hi t t₀)
      have := hnn t t₀ ht0 h1
      linarith
    rcases le_total t a with h2 | h2
    · rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 t₀) (hi t₀ t), hz t h1 h2]
      linarith
    · rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 t₀) (hi t₀ t),
        ← intervalIntegral.integral_add_adjacent_intervals (hi t₀ a) (hi a t), hz a hta le_rfl]
      have := hup a t h2
      have hlt : M * (t - a) < θ - P := by
        have h3 : t - a < (θ - P) / M := by linarith
        rw [lt_div_iff₀ hM] at h3
        linarith
      linarith
  · have hlow : κ * (c + (θ - P') / κ - c) ≤ ∫ s in c..(c + (θ - P') / κ), F s := by
      have h := intervalIntegral.integral_mono_on (by linarith) (intervalIntegrable_const
        (μ := MeasureTheory.volume) (c := κ)) (hi c (c + (θ - P') / κ))
        fun s hs => hnear s hs.1 hs.2
      rw [intervalIntegral.integral_const, smul_eq_mul] at h
      linarith
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 t₀) (hi t₀ (c + (θ - P') / κ)),
      ← intervalIntegral.integral_add_adjacent_intervals (hi t₀ c) (hi c (c + (θ - P') / κ))]
    have h1 := hnn t₀ c ht₀ (hta.trans hac)
    have e : κ * (c + (θ - P') / κ - c) = θ - P' := by field_simp; ring
    linarith

/-- ★★★ **The encounter record's window, at any chord.** Two normalised trajectories `ΨA s`,
`ΨB s` with tails `ε_A`, `ε_B` off chord-`ρ_A`, `ρ_B` arcs about predicted angles whose difference
is `Ω (s − t_c)`, `Ω > 0`, feed a register at rate `max(relWeight 1 ρ − 1/2, 0)`, from `0` at time
`0`. With `κ = (1 − ε_A)(1 − ε_B) − 1/2 > 0`, `ε_A + ε_B ≤ 1/2`, near half-width
`(ρ − ρ_A − ρ_B)/Ω` and a far angle `y` (`ρ + ρ_A + ρ_B < 2 sin(y/2)`, `Ω t_c ≤ 2π − y`): the
register stays below the threshold `θ > 0` before `t_c − y/Ω + 2θ` and has reached it by
`t_c − (ρ − ρ_A − ρ_B)/Ω + θ/κ`, provided `θ/κ ≤ 2(ρ − ρ_A − ρ_B)/Ω`. The record's window is set
by the chords over the relative angular speed and by the threshold. -/
theorem encounter_record_window {ΨA ΨB : ℝ → (ZMod L × Fin 2) × Fin 2 → ℂ} {α β : ℝ → ℝ}
    {ρA ρB ρ εA εB Ω t_c y θ T : ℝ}
    (hF : Continuous fun s => max (relWeight 1 ρ (ΨA s) (ΨB s) - 1 / 2) 0)
    (hA1 : ∀ s, devRegionWeight (ΨA s) Finset.univ = 1)
    (hB1 : ∀ s, devRegionWeight (ΨB s) Finset.univ = 1)
    (htA : ∀ s, 0 ≤ s → s ≤ T →
      devRegionWeight (ΨA s) (chordArc (exp (I * (α s : ℂ))) ρA)ᶜ ≤ εA)
    (htB : ∀ s, 0 ≤ s → s ≤ T →
      devRegionWeight (ΨB s) (chordArc (exp (I * (β s : ℂ))) ρB)ᶜ ≤ εB)
    (hrel : ∀ s, β s - α s = Ω * (s - t_c)) (hΩ : 0 < Ω) (hρA : 0 ≤ ρA) (hρB : 0 ≤ ρB)
    (hκ : 0 < (1 - εA) * (1 - εB) - 1 / 2) (hεB : εB ≤ 1) (hε : εA + εB ≤ 1 / 2)
    (hy : 0 ≤ y) (hsin : ρ + ρA + ρB < 2 * Real.sin (y / 2)) (hyc : Ω * t_c ≤ 2 * Real.pi - y)
    (hθ : 0 < θ) (hfar0 : 0 ≤ t_c - y / Ω)
    (hfill : θ / ((1 - εA) * (1 - εB) - 1 / 2) ≤ 2 * ((ρ - ρA - ρB) / Ω))
    (hT : t_c + (ρ - ρA - ρB) / Ω ≤ T) :
    (∀ t, 0 ≤ t → t < t_c - y / Ω + 2 * θ →
      ∫ s in (0 : ℝ)..t, max (relWeight 1 ρ (ΨA s) (ΨB s) - 1 / 2) 0 < θ)
    ∧ θ ≤ ∫ s in (0 : ℝ)..(t_c - (ρ - ρA - ρB) / Ω + θ / ((1 - εA) * (1 - εB) - 1 / 2)),
        max (relWeight 1 ρ (ΨA s) (ΨB s) - 1 / 2) 0 := by
  set κ := (1 - εA) * (1 - εB) - 1 / 2 with hκdef
  set hn := (ρ - ρA - ρB) / Ω with hhn
  have hfk : 0 ≤ θ / κ := div_nonneg hθ.le hκ.le
  have hn0 : 0 ≤ hn := by linarith
  have hyΩ : 0 ≤ y / Ω := div_nonneg hy hΩ.le
  have hsy : ρ - ρA - ρB ≤ y := by
    have := Real.sin_le (by linarith : (0 : ℝ) ≤ y / 2)
    linarith
  have hac : t_c - y / Ω ≤ t_c - hn := by
    have : hn ≤ y / Ω := div_le_div_of_nonneg_right hsy hΩ.le
    linarith
  have e0 : (θ - 0) / κ = θ / κ := by rw [sub_zero]
  have e1 : (θ - 0) / (1 / 2 : ℝ) = 2 * θ := by ring
  have hlim := record_window (F := fun s => max (relWeight 1 ρ (ΨA s) (ΨB s) - 1 / 2) 0) hF
    (M := 1 / 2) (κ := κ) (θ := θ) (P := 0) (P' := 0) (t₀ := 0) (a := t_c - y / Ω)
    (c := t_c - hn) (by norm_num) hκ le_rfl hfar0 hac (fun s _ => le_max_right _ _)
    (fun s => by
      have := relWeight_le_mul 1 ρ (ΨA s) (ΨB s)
      rw [hA1, hB1, one_mul] at this
      exact max_le (by linarith) (by norm_num))
    (by simp) (by simp) hθ
    (fun s hs1 hs2 => by
      refine max_eq_right ?_
      have hst : y ≤ Ω * (t_c - s) := by
        have : y / Ω ≤ t_c - s := by linarith
        rwa [div_le_iff₀' hΩ] at this
      have hfar := encounter_far_angle (ΨA := ΨA s) (ΨB := ΨB s) (ρ := ρ) (y := y) (hA1 s)
        (hB1 s) (htA s hs1 (by linarith)) (htB s hs1 (by linarith)) hy
        (by rw [hrel, abs_mul, abs_of_pos hΩ, abs_of_nonpos (by linarith)]; linarith)
        (by
          rw [hrel, abs_mul, abs_of_pos hΩ, abs_of_nonpos (by linarith)]
          nlinarith [mul_nonneg hΩ.le hs1])
        hsin
      linarith)
    (fun s hs1 hs2 => by
      rw [e0] at hs2
      have hnear := encounter_near_angle (ΨA := ΨA s) (ΨB := ΨB s) (ρ := ρ) (hA1 s) (hB1 s)
        (htA s (by linarith) (by linarith)) (htB s (by linarith) (by linarith)) hεB (by
          rw [hrel, abs_mul, abs_of_pos hΩ]
          have h1 : |s - t_c| ≤ hn := by
            rw [abs_le]
            constructor <;> linarith
          calc Ω * |s - t_c| ≤ Ω * hn := mul_le_mul_of_nonneg_left h1 hΩ.le
            _ = ρ - ρA - ρB := by rw [hhn]; field_simp)
      exact le_max_of_le_left (by linarith))
  obtain ⟨h1, h2⟩ := hlim
  rw [e0] at h2
  exact ⟨fun t ht0 ht => h1 t ht0 (by rw [e1]; exact ht), h2⟩

/-! ### Lever (a): the quadratic drift -/

/-- ★★ **The quadratic phase bound.** For nonnegative weights `w_i` and frequencies within `δ` of
`Ω`, the sum `Σ w_i e^{iΔ_i t}` read against `e^{iΩt}` keeps at least `(1 − (δt)²/2) Σ w_i` of its
real part: the drift is quadratic in `δt`, where `|e^{ix} − 1| ≤ |x|` gives only linear. -/
theorem le_re_sum_phase {ι : Type*} (s : Finset ι) (w Δ : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (Ω t δ : ℝ) (hδ : ∀ i ∈ s, |Δ i - Ω| ≤ δ) :
    (1 - (δ * t) ^ 2 / 2) * ∑ i ∈ s, w i
      ≤ (star (exp (I * ((Ω * t : ℝ) : ℂ)))
          * ∑ i ∈ s, (w i : ℂ) * exp (I * ((Δ i * t : ℝ) : ℂ))).re := by
  rw [Finset.mul_sum, Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have e : star (exp (I * ((Ω * t : ℝ) : ℂ))) * ((w i : ℂ) * exp (I * ((Δ i * t : ℝ) : ℂ)))
      = (w i : ℂ) * exp (I * ((Δ i * t - Ω * t : ℝ) : ℂ)) := by
    rw [← exp_I_mul_star_exp_I (Ω * t) (Δ i * t)]
    ring
  rw [e, Complex.re_ofReal_mul, show I * ((Δ i * t - Ω * t : ℝ) : ℂ)
    = ((Δ i * t - Ω * t : ℝ) : ℂ) * I by ring, Complex.exp_ofReal_mul_I_re]
  have hc := Real.one_sub_sq_div_two_le_cos (x := Δ i * t - Ω * t)
  have hsq : (Δ i * t - Ω * t) ^ 2 ≤ (δ * t) ^ 2 := by
    rw [show Δ i * t - Ω * t = (Δ i - Ω) * t by ring, mul_pow, mul_pow]
    have h1 : (Δ i - Ω) ^ 2 ≤ δ ^ 2 := by
      rw [← sq_abs (Δ i - Ω)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hδ i hi) 2
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg t)
  have hwi := hw i hi
  nlinarith

/-- ★★★ **A packet's tail with quadratic drift.** A massive packet with real nonnegative
amplitudes `β` (normalised), nonnegative spin overlaps between neighbours, and angles within `δ`
of `θ₀`: off the chord-`ρ` arc about a point within `η` of its group-velocity angle at time `t`,
its weight times `(ρ − η)²/2` is at most `1 − Re transPhase(0) + (δ' t)²/2`, with
`δ' = vgLip · (2π/L) · (δ + 2π/L)` the per-step frequency spread. The linear drift
`|t| · δ'` of `transPhase_drift` becomes quadratic. -/
theorem regionWeight_compl_chordArc_quad {J μ : ℝ} (hμ : 0 < μ) {W : Finset ℤ}
    (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L) (β : ℤ → ℝ) (hβ0 : ∀ m, 0 ≤ β m)
    (hβ : ∑ m ∈ W, β m ^ 2 = 1)
    (hspin : ∀ m, 0 ≤ spinCos J μ (angleZ L (m + 1)) (angleZ L m))
    {θ₀ δ : ℝ} (hδ : ∀ m ∈ W, |angleZ L m - θ₀| ≤ δ)
    {z : ℂ} {ρ η : ℝ} (hηρ : η ≤ ρ) (t : ℝ)
    (hz : ‖exp (I * ((2 * Real.pi / L * groupVel J μ θ₀ * t : ℝ) : ℂ)) - z‖ ≤ η) :
    regionWeight (packet (L := L) J μ W (unitAmp L J μ fun m => (β m : ℂ)) t) (chordArc z ρ)ᶜ
        * ((ρ - η) ^ 2 / 2)
      ≤ 1 - (transPhase (packet (L := L) J μ W (unitAmp L J μ fun m => (β m : ℂ)) 0)).re
        + (vgLip J μ * (2 * Real.pi / L) * (δ + 2 * Real.pi / L) * t) ^ 2 / 2 := by
  obtain ⟨hW, hDst⟩ := noWrap_distinct_of_window (L := L) hWin
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh : (0 : ℝ) < 2 * Real.pi / L := by positivity
  set ψ := fun t => packet (L := L) J μ W (unitAmp L J μ fun m => (β m : ℂ)) t with hψ
  set φ := 2 * Real.pi / L * groupVel J μ θ₀ * t with hφ
  set δ' := vgLip J μ * (2 * Real.pi / L) * (δ + 2 * Real.pi / L) with hδ'
  -- the normalisation
  have hn : ∀ s, chainInner (ψ s) (ψ s) = 1 := fun s => by
    rw [hψ, chainInner_packet_unitAmp hμ hDst]
    have : ∑ m ∈ W, ‖(β m : ℂ)‖ ^ 2 = ∑ m ∈ W, β m ^ 2 :=
      Finset.sum_congr rfl fun m _ => by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [this, hβ, Complex.ofReal_one]
  -- the weights
  set w : ℤ → ℝ := fun m => β (m + 1) * β m * spinCos J μ (angleZ L (m + 1)) (angleZ L m)
    with hw
  have hw0 : ∀ m, 0 ≤ w m := fun m => mul_nonneg (mul_nonneg (hβ0 _) (hβ0 _)) (hspin m)
  have hTP : ∀ s, transPhase (ψ s) = ∑ m ∈ W.filter (fun m => m + 1 ∈ W),
      (w m : ℂ) * exp (I * (((bandE J μ (angleZ L (m + 1)) - bandE J μ (angleZ L m)) * s : ℝ)
        : ℂ)) := fun s => by
    rw [hψ, transPhase_packet J μ hW _ s]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [transWeight_unitAmp hμ, Complex.star_def, Complex.conj_ofReal, hw]
    push_cast
    ring
  -- `Re T(0)` is the total weight, between `0` and `1`
  have hS : (transPhase (ψ 0)).re = ∑ m ∈ W.filter (fun m => m + 1 ∈ W), w m := by
    rw [hTP 0, Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, Complex.ofReal_re]
  have hS0 : 0 ≤ ∑ m ∈ W.filter (fun m => m + 1 ∈ W), w m := Finset.sum_nonneg fun m _ => hw0 m
  have hS1 : ∑ m ∈ W.filter (fun m => m + 1 ∈ W), w m ≤ 1 := by
    rw [← hS]
    have h := norm_transPhase_le (L := L) (J := J) hμ hW hDst
      (unitAmp L J μ fun m => (β m : ℂ)) 0
    rw [hn 0, norm_one] at h
    exact (Complex.re_le_norm _).trans h
  -- the quadratic drift
  have hq := le_re_sum_phase (W.filter (fun m => m + 1 ∈ W)) w
    (fun m => bandE J μ (angleZ L (m + 1)) - bandE J μ (angleZ L m))
    (fun m _ => hw0 m) (2 * Real.pi / L * groupVel J μ θ₀) t δ' fun m hm => by
      have hmW := (Finset.mem_filter.1 hm).1
      have h := abs_bandE_step_sub_le (J := J) hμ hh (angleZ L m) θ₀
      rw [← angleZ_succ] at h
      refine h.trans ?_
      rw [hδ', vgLip]
      have := hδ m hmW
      gcongr
  rw [← hTP t] at hq
  -- the tail
  have hu : ‖exp (I * (φ : ℂ))‖ = 1 := norm_exp_I_mul_ofReal_eq_one φ
  have hreg := regionWeight_mul_le (ψ t) hu (B := (chordArc z ρ)ᶜ) (γ := 1 - (ρ - η) ^ 2 / 2)
    fun k hk => by
      rw [Finset.mem_compl, mem_chordArc, not_le] at hk
      rw [re_star_mul_eq_chord (Circle.norm_coe _) hu]
      have hd : ρ - η ≤ ‖(ZMod.toCircle k : ℂ) - exp (I * (φ : ℂ))‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub (ZMod.toCircle k : ℂ) (exp (I * (φ : ℂ))) z
        linarith
      have hsq := pow_le_pow_left₀ (by linarith) hd 2
      linarith
  rw [show 1 - (1 - (ρ - η) ^ 2 / 2) = (ρ - η) ^ 2 / 2 by ring, hn t, Complex.one_re] at hreg
  have hφe : (φ : ℂ) = ((2 * Real.pi / L * groupVel J μ θ₀ * t : ℝ) : ℂ) := rfl
  rw [hφe] at hreg
  have hdq : (δ' * t) ^ 2 / 2 * ∑ m ∈ W.filter (fun m => m + 1 ∈ W), w m ≤ (δ' * t) ^ 2 / 2 := by
    have : 0 ≤ (δ' * t) ^ 2 / 2 := by positivity
    nlinarith
  rw [hS]
  nlinarith

/-! ### Lever (a): the sine profile -/

/-- A sum over the integer window `[lo, lo + n)` is the sum over `range n` shifted by `lo`. -/
theorem sum_Ico_int_eq_sum_range (F : ℤ → ℝ) (lo : ℤ) (n : ℕ) :
    ∑ m ∈ Finset.Ico lo (lo + n), F m = ∑ i ∈ Finset.range n, F (lo + i) := by
  have e : Finset.Ico lo (lo + n) = (Finset.range n).image fun i : ℕ => lo + i := by
    ext m
    simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · intro h
      exact ⟨(m - lo).toNat, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [e, Finset.sum_image fun a _ b _ h => by exact_mod_cast add_left_cancel h]

/-- ★★ **The discrete box's ground state.** With `g i = sin(h (i + 1))`, `h = π/(n + 1)`, the
neighbour sum is `cos h` times the squared sum: `Σ_{i < n−1} g(i+1) g(i) = cos h · Σ_{i < n} g(i)²`
— from `sin(x − h) + sin(x + h) = 2 sin x cos h` and the zero ends `sin 0 = sin π = 0`. -/
theorem sine_neighbour_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.range (n - 1), Real.sin (Real.pi / (n + 1) * ((i : ℝ) + 2))
        * Real.sin (Real.pi / (n + 1) * ((i : ℝ) + 1))
      = Real.cos (Real.pi / (n + 1))
        * ∑ i ∈ Finset.range n, Real.sin (Real.pi / (n + 1) * ((i : ℝ) + 1)) ^ 2 := by
  set h := Real.pi / (n + 1) with hh
  set g : ℕ → ℝ := fun i => Real.sin (h * ((i : ℝ) + 1)) with hg
  set P := ∑ i ∈ Finset.range (n - 1), Real.sin (h * ((i : ℝ) + 2)) * g i with hP
  have hend : g (n - 1 + 1) = 0 := by
    rw [hg]
    simp only
    rw [show ((n - 1 + 1 : ℕ) : ℝ) + 1 = n + 1 by rw [Nat.sub_add_cancel hn]]
    rw [hh, div_mul_cancel₀ _ (by positivity : (n : ℝ) + 1 ≠ 0), Real.sin_pi]
  -- the recurrence
  have hrec : ∀ i : ℕ, g i * (Real.sin (h * i) + Real.sin (h * ((i : ℝ) + 2)))
      = 2 * Real.cos h * g i ^ 2 := fun i => by
    rw [hg]
    simp only
    rw [show h * (i : ℝ) = h * ((i : ℝ) + 1) - h by ring,
      show h * ((i : ℝ) + 2) = h * ((i : ℝ) + 1) + h by ring, Real.sin_sub, Real.sin_add]
    ring
  have hsum : ∑ i ∈ Finset.range n, g i * Real.sin (h * i)
      + ∑ i ∈ Finset.range n, g i * Real.sin (h * ((i : ℝ) + 2))
      = 2 * Real.cos h * ∑ i ∈ Finset.range n, g i ^ 2 := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← mul_add]; exact hrec i
  -- the two halves are both `P`
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, (Nat.sub_add_cancel hn).symm⟩
  simp only [Nat.add_sub_cancel] at hP hend
  have h1 : ∑ i ∈ Finset.range (k + 1), g i * Real.sin (h * i) = P := by
    rw [Finset.sum_range_succ', hP]
    simp only [Nat.cast_zero, mul_zero, Real.sin_zero, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hg]
    simp only
    push_cast
    ring_nf
  have h2 : ∑ i ∈ Finset.range (k + 1), g i * Real.sin (h * ((i : ℝ) + 2)) = P := by
    rw [Finset.sum_range_succ, hP]
    have : Real.sin (h * ((k : ℝ) + 2)) = 0 := by
      have := hend
      rw [hg] at this
      simp only at this
      rw [← this]
      push_cast
      ring_nf
    rw [this, mul_zero, add_zero]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h1, h2] at hsum
  have hgs : ∑ i ∈ Finset.range (k + 1), g i ^ 2
      = ∑ i ∈ Finset.range (k + 1), Real.sin (h * ((i : ℝ) + 1)) ^ 2 := rfl
  linarith

/-- The sine profile's normalisation: `Σ_{i < n} sin²(π(i + 1)/(n + 1))`. -/
noncomputable def sineNorm (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, Real.sin (Real.pi / (n + 1) * ((i : ℝ) + 1)) ^ 2

theorem sineNorm_pos {n : ℕ} (hn : 1 ≤ n) : 0 < sineNorm n := by
  have hn1 : (1 : ℝ) < n + 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hs : 0 < Real.sin (Real.pi / (n + 1) * (((0 : ℕ) : ℝ) + 1)) := by
    rw [Nat.cast_zero, zero_add, mul_one]
    exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (div_lt_self Real.pi_pos hn1)
  calc (0 : ℝ) < Real.sin (Real.pi / (n + 1) * (((0 : ℕ) : ℝ) + 1)) ^ 2 := by positivity
    _ ≤ sineNorm n :=
      Finset.single_le_sum (f := fun i : ℕ => Real.sin (Real.pi / (n + 1) * ((i : ℝ) + 1)) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_range.2 (by omega))

/-- ★ **The sine profile** on the window `[lo, lo + n)`: `β_m ∝ sin(π(m − lo + 1)/(n + 1))`, the
ground state of the discrete box (clipped at `0` outside the window, where it is not used). -/
noncomputable def sineAmp (n : ℕ) (lo m : ℤ) : ℝ :=
  max (Real.sin (Real.pi / (n + 1) * (((m - lo : ℤ) : ℝ) + 1))) 0 / Real.sqrt (sineNorm n)

theorem sineAmp_nonneg (n : ℕ) (lo m : ℤ) : 0 ≤ sineAmp n lo m :=
  div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)

/-- Inside the window the clip is inactive. -/
theorem sineAmp_of_lt {n : ℕ} (lo : ℤ) {i : ℕ} (hi : i < n) :
    sineAmp n lo (lo + i)
      = Real.sin (Real.pi / (n + 1) * ((i : ℝ) + 1)) / Real.sqrt (sineNorm n) := by
  rw [sineAmp, show ((lo + i - lo : ℤ) : ℝ) = i by push_cast; ring]
  congr 1
  refine max_eq_left (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) ?_)
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
  nlinarith [Real.pi_pos]

/-- ★★ **The sine profile's sums**: `Σ β² = 1` and `Σ β_{m+1} β_m = cos(π/(n + 1))` on the
window. -/
theorem sineAmp_sums {n : ℕ} (hn : 1 ≤ n) (lo : ℤ) :
    ∑ m ∈ Finset.Ico lo (lo + n), sineAmp n lo m ^ 2 = 1
    ∧ ∑ m ∈ (Finset.Ico lo (lo + n)).filter (fun m => m + 1 ∈ Finset.Ico lo (lo + n)),
        sineAmp n lo (m + 1) * sineAmp n lo m = Real.cos (Real.pi / (n + 1)) := by
  have hS := sineNorm_pos hn
  have hsq : Real.sqrt (sineNorm n) ^ 2 = sineNorm n := Real.sq_sqrt hS.le
  have hsq0 : Real.sqrt (sineNorm n) ≠ 0 := (Real.sqrt_pos.2 hS).ne'
  constructor
  · rw [sum_Ico_int_eq_sum_range]
    have e : ∀ i ∈ Finset.range n, sineAmp n lo (lo + i) ^ 2
        = Real.sin (Real.pi / (n + 1) * ((i : ℝ) + 1)) ^ 2 / sineNorm n := fun i hi => by
      rw [sineAmp_of_lt lo (Finset.mem_range.1 hi), div_pow, hsq]
    rw [Finset.sum_congr rfl e, ← Finset.sum_div, ← sineNorm, div_self hS.ne']
  · rw [filter_succ_Ico, show lo + (n : ℤ) - 1 = lo + ((n - 1 : ℕ) : ℤ) by push_cast [hn]; ring,
      sum_Ico_int_eq_sum_range]
    have e : ∀ i ∈ Finset.range (n - 1), sineAmp n lo (lo + i + 1) * sineAmp n lo (lo + i)
        = Real.sin (Real.pi / (n + 1) * ((i : ℝ) + 2))
          * Real.sin (Real.pi / (n + 1) * ((i : ℝ) + 1)) / sineNorm n := fun i hi => by
      have hi' : i < n - 1 := Finset.mem_range.1 hi
      rw [show lo + (i : ℤ) + 1 = lo + ((i + 1 : ℕ) : ℤ) by push_cast; ring,
        sineAmp_of_lt lo (by omega : i + 1 < n), sineAmp_of_lt lo (by omega : i < n)]
      push_cast
      rw [div_mul_div_comm, ← sq, hsq]
      ring_nf
    rw [Finset.sum_congr rfl e, ← Finset.sum_div, sine_neighbour_sum n hn, ← sineNorm,
      mul_div_assoc, div_self hS.ne', mul_one]

/-- ★★★ **The sine packet's tail.** A massive packet with the sine profile over `n` modes, angles
within `δ` of `θ₀` and spin loss `κ = (2πJ/(Lμ))² ≤ 1`: off the chord-`ρ` arc about a point within
`η` of its group-velocity angle at time `t`, its weight times `(ρ − η)²/2` is at most
`(π/(n + 1))²/2 + κ + (δ' t)²/2` — the profile's floor `~π²/(2n²)` where the flat profile's is
`1/n`, and the drift quadratic. -/
theorem sine_packet_tail {J μ : ℝ} (hμ : 0 < μ) {n : ℕ} (hn : 1 ≤ n)
    (hWin : ∀ m ∈ Finset.Ico lo (lo + n), lo ≤ m ∧ m + 1 < lo + L)
    (hκ : (2 * Real.pi * J / (L * μ)) ^ 2 ≤ 1)
    {θ₀ δ : ℝ} (hδ : ∀ m ∈ Finset.Ico lo (lo + n), |angleZ L m - θ₀| ≤ δ)
    {z : ℂ} {ρ η : ℝ} (hηρ : η ≤ ρ) (t : ℝ)
    (hz : ‖exp (I * ((2 * Real.pi / L * groupVel J μ θ₀ * t : ℝ) : ℂ)) - z‖ ≤ η) :
    regionWeight (packet (L := L) J μ (Finset.Ico lo (lo + n))
        (unitAmp L J μ fun m => (sineAmp n lo m : ℂ)) t) (chordArc z ρ)ᶜ * ((ρ - η) ^ 2 / 2)
      ≤ (Real.pi / (n + 1)) ^ 2 / 2 + (2 * Real.pi * J / (L * μ)) ^ 2
        + (vgLip J μ * (2 * Real.pi / L) * (δ + 2 * Real.pi / L) * t) ^ 2 / 2 := by
  obtain ⟨hsum1, hsum2⟩ := sineAmp_sums hn lo
  obtain ⟨hW, -⟩ := noWrap_distinct_of_window (L := L) hWin
  have hspin : ∀ m, 0 ≤ spinCos J μ (angleZ L (m + 1)) (angleZ L m) := fun m => by
    have h := one_sub_le_spinCos (J := J) hμ (angleZ L (m + 1)) (angleZ L m)
    rw [angleZ_succ, show angleZ L m + 2 * Real.pi / L - angleZ L m = 2 * Real.pi / L by ring,
      show J * (2 * Real.pi / L) / μ = 2 * Real.pi * J / (L * μ) by ring] at h
    rw [angleZ_succ]
    linarith
  have h := regionWeight_compl_chordArc_quad (L := L) hμ hWin (sineAmp n lo)
    (sineAmp_nonneg n lo) hsum1 hspin hδ hηρ t hz
  have hRe := re_transPhase_unitAmp_ge (L := L) (J := J) hμ hW (sineAmp n lo)
    (sineAmp_nonneg n lo)
  rw [hsum2] at hRe
  have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.pi / (n + 1))
  have hc1 := Real.cos_le_one (Real.pi / (n + 1))
  have hκ0 : 0 ≤ (2 * Real.pi * J / (L * μ)) ^ 2 := sq_nonneg _
  nlinarith

/-- ★★★ **The massless sine packet's tail.** A massless packet with the sine profile over `n`
right-moving modes, angles within `δ` of `θ₀`: off the chord-`ρ` arc about a point within `η` of
its angle `(2π/L)(2J cos θ₀) t`, its weight times `(ρ − η)²/2` is at most
`(π/(n + 1))²/2 + (δ'' t)²/2`, `δ'' = 2J (2π/L)(δ + 2π/L)` — no spin loss (right-moving massless
spinors are parallel), the drift quadratic. -/
theorem sine_massless_tail {J : ℝ} (hJ : 0 < J) {n : ℕ} (hn : 1 ≤ n)
    (hWin : ∀ m ∈ Finset.Ico lo (lo + n), lo ≤ m ∧ m + 1 < lo + L)
    (hR : RightWindow L (Finset.Ico lo (lo + n)))
    {θ₀ δ : ℝ} (hδ : ∀ m ∈ Finset.Ico lo (lo + n), |angleZ L m - θ₀| ≤ δ)
    {z : ℂ} {ρ η : ℝ} (hηρ : η ≤ ρ) (t : ℝ)
    (hz : ‖exp (I * ((2 * Real.pi / L * (2 * J * Real.cos θ₀) * t : ℝ) : ℂ)) - z‖ ≤ η) :
    regionWeight (packet (L := L) J 0 (Finset.Ico lo (lo + n))
        (unitAmp L J 0 fun m => (sineAmp n lo m : ℂ)) t) (chordArc z ρ)ᶜ * ((ρ - η) ^ 2 / 2)
      ≤ (Real.pi / (n + 1)) ^ 2 / 2
        + (2 * J * (2 * Real.pi / L) * (δ + 2 * Real.pi / L) * t) ^ 2 / 2 := by
  set W := Finset.Ico lo (lo + n) with hWdef
  obtain ⟨hsum1, hsum2⟩ := sineAmp_sums hn lo
  obtain ⟨hW, hDst⟩ := noWrap_distinct_of_window (L := L) hWin
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh : (0 : ℝ) < 2 * Real.pi / L := by positivity
  set β := sineAmp n lo with hβdef
  set ψ := fun s => packet (L := L) J 0 W (unitAmp L J 0 fun m => (β m : ℂ)) s with hψ
  set φ := 2 * Real.pi / L * (2 * J * Real.cos θ₀) * t with hφ
  set δ'' := 2 * J * (2 * Real.pi / L) * (δ + 2 * Real.pi / L) with hδ''
  have hn1 : ∀ s, chainInner (ψ s) (ψ s) = 1 := fun s => by
    rw [hψ, chainInner_packet_unitAmp_zero hJ hR hDst]
    have : ∑ m ∈ W, ‖(β m : ℂ)‖ ^ 2 = ∑ m ∈ W, β m ^ 2 :=
      Finset.sum_congr rfl fun m _ => by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [this, hsum1, Complex.ofReal_one]
  set w : ℤ → ℝ := fun m => β (m + 1) * β m with hw
  have hw0 : ∀ m, 0 ≤ w m := fun m => mul_nonneg (sineAmp_nonneg _ _ _) (sineAmp_nonneg _ _ _)
  have hTP : ∀ s, transPhase (ψ s) = ∑ m ∈ W.filter (fun m => m + 1 ∈ W),
      (w m : ℂ) * exp (I * (((bandE J 0 (angleZ L (m + 1)) - bandE J 0 (angleZ L m)) * s : ℝ)
        : ℂ)) := fun s => by
    rw [hψ, transPhase_packet J 0 hW _ s]
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hmW, hm1W⟩ := Finset.mem_filter.1 hm
    obtain ⟨a0, aπ⟩ := hR m hmW
    obtain ⟨b0, bπ⟩ := hR (m + 1) hm1W
    rw [transWeight_unitAmp_zero hJ _ b0 bπ a0 aπ, Complex.star_def, Complex.conj_ofReal, hw]
    push_cast
    ring
  have hS : ∑ m ∈ W.filter (fun m => m + 1 ∈ W), w m = Real.cos (Real.pi / (n + 1)) := hsum2
  have hq := le_re_sum_phase (W.filter (fun m => m + 1 ∈ W)) w
    (fun m => bandE J 0 (angleZ L (m + 1)) - bandE J 0 (angleZ L m))
    (fun m _ => hw0 m) (2 * Real.pi / L * (2 * J * Real.cos θ₀)) t δ'' fun m hm => by
      obtain ⟨hmW, hm1W⟩ := Finset.mem_filter.1 hm
      obtain ⟨a0, -⟩ := hR m hmW
      obtain ⟨-, bπ⟩ := hR (m + 1) hm1W
      rw [angleZ_succ] at bπ ⊢
      have h := abs_bandE_zero_step_sub_le (J := J) (θ₀ := θ₀) hJ.le hh a0.le bπ.le
      refine h.trans ?_
      rw [hδ'']
      have := hδ m hmW
      have hJ2 : 0 ≤ 2 * J * (2 * Real.pi / L) := by positivity
      calc 2 * J * (2 * Real.pi / L) * (|angleZ L m - θ₀| + 2 * Real.pi / L)
          ≤ 2 * J * (2 * Real.pi / L) * (δ + 2 * Real.pi / L) := by gcongr
        _ = _ := rfl
  rw [← hTP t, hS] at hq
  have hu : ‖exp (I * (φ : ℂ))‖ = 1 := norm_exp_I_mul_ofReal_eq_one φ
  have hreg := regionWeight_mul_le (ψ t) hu (B := (chordArc z ρ)ᶜ) (γ := 1 - (ρ - η) ^ 2 / 2)
    fun k hk => by
      rw [Finset.mem_compl, mem_chordArc, not_le] at hk
      rw [re_star_mul_eq_chord (Circle.norm_coe _) hu]
      have hd : ρ - η ≤ ‖(ZMod.toCircle k : ℂ) - exp (I * (φ : ℂ))‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub (ZMod.toCircle k : ℂ) (exp (I * (φ : ℂ))) z
        linarith
      have hsq := pow_le_pow_left₀ (by linarith) hd 2
      linarith
  rw [show 1 - (1 - (ρ - η) ^ 2 / 2) = (ρ - η) ^ 2 / 2 by ring, hn1 t, Complex.one_re] at hreg
  have hφe : (φ : ℂ) = ((2 * Real.pi / L * (2 * J * Real.cos θ₀) * t : ℝ) : ℂ) := rfl
  rw [hφe] at hreg
  have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.pi / (n + 1))
  have hc1 := Real.cos_le_one (Real.pi / (n + 1))
  have hx : 0 ≤ (δ'' * t) ^ 2 / 2 := by positivity
  nlinarith

end CSD.RecordLayer
