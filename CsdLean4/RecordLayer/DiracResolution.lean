/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracMasslessTails

/-!
# The records' resolution: tails and encounters at any number of modes and any chord

**Category:** 7-SigmaLayer (the record layer). BACKLOG #280, lever (b), first three bricks.

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

## Honest scope

⚠️ **Chebyshev only**: the bound uses the second moment of the angle; the flat profile's true
tail decays like `1/(Nρ)` (Dirichlet kernel, estimate), so this is lever (b) of #280, not (a).

⚠️ **Tails and encounters only**: the registers and the records at a symbolic chord are the next
bricks of lever (b); the drift term grows with `|t|`, and
keeping it below `1/N` bounds the time span at a given lattice spacing.

References: `specs/BACKLOG.md` #280, #278, #248; `RecordLayer/DiracMasslessTails.lean`
(`regionWeight_compl_chordArc_massless_le`, `bMess_re_transPhase_zero`, `bMess_tail`);
`CV/DiracMassless.lean` (`re_transPhase_unitAmp_zero`, `masslessErr`); `CV/DiracPacketLimit.lean`
(`flat_sums`, `flat_packet_localised`); `RecordLayer/DiracTwoCharts.lean` (`lorentz_chart_bounds`);
`RecordLayer/DiracObservers.lean` (`le_relWeight`, `relWeight_le`, `two_sin_le_norm_exp_sub_one`);
`RecordLayer/DiracDoppler.lean` (`offset_mem_of_near_at`, `offset_not_mem_of_far_at`);
`RecordLayer/DiracRelayA.lean` (`aEncounter_near`, `aEncounter_far`, `rest_tail_fine`);
`RecordLayer/DiracArrival.lean` (`re_transPhase_ringPacket_ge`);
`RecordLayer/DiracObservers.lean` (`devRegionWeight_compl_chordArc_le`).
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


end CSD.RecordLayer
