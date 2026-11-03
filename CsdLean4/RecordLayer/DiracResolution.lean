/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracMasslessTails

/-!
# The records' resolution: the flat massless packet's tail at any number of modes

**Category:** 7-SigmaLayer (the record layer). BACKLOG #280, lever (b), first brick.

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

## Honest scope

⚠️ **Chebyshev only**: the bound uses the second moment of the angle; the flat profile's true
tail decays like `1/(Nρ)` (Dirichlet kernel, estimate), so this is lever (b) of #280, not (a).

⚠️ **The tail only**: the encounter windows, the registers and the records at a symbolic chord are
the next bricks of lever (b); the drift term grows with `|t|`, and keeping it below `1/N` bounds
the time span at a given lattice spacing.

References: `specs/BACKLOG.md` #280, #278, #248; `RecordLayer/DiracMasslessTails.lean`
(`regionWeight_compl_chordArc_massless_le`, `bMess_re_transPhase_zero`, `bMess_tail`);
`CV/DiracMassless.lean` (`re_transPhase_unitAmp_zero`, `masslessErr`); `CV/DiracPacketLimit.lean`
(`flat_sums`, `flat_packet_localised`); `RecordLayer/DiracTwoCharts.lean` (`lorentz_chart_bounds`).
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

end CSD.RecordLayer
