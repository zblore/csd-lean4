/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracObservers
public import CsdLean4.RecordLayer.DiracRateTicks

/-!
# Two observers on the Dirac chain, and their clocks compared

**Category:** 7-SigmaLayer (the record layer). BACKLOG #253 (residue of ~~#243~~), for the test
candidate (B).

~~#243~~ put two observers in one arena for the control (A), where the clocks agree whatever the
relative motion. Here two of #262's devices share **one Dirac chain**: one at rest, one moving at
`4/5`, each with its rate counter (~~#273~~), and the two record each other through **relational
encounter registers**. The moving observer goes once round the ring and comes back. Between the
records of its departure and its return the moving clock counts **69 to 73** ticks and the clock at
rest **116 to 122**: the ratio lies in `[69/122, 73/116]`, which contains `3/5 = √(1 − (4/5)²)` and
excludes `1`. **The dilation shows in the records.**

## The observers

* `twinAmp`, `restObserver` (rest energies `3` and `3 + 10⁻¹¹`, `2·10⁶` modes about momentum `0`),
  `movingObserver` (the same about momentum `4`), on a ring of length `2π·10¹³` with at least `10¹⁹`
  sites; `rest_spread`, `moving_spread`, `rest_win`, `moving_win`, `twin_norm`;
* ★ `twin_budget` (each level's budget below `1.1·10⁻⁶` up to `t = 8·10¹³`), `omega_twin`
  (`Ω = 8·10⁻¹⁴`); ★★ `rest_tail`, ★★ `moving_tail` — **each observer within chord `1/25` of its
  predicted point but for `1.4·10⁻³` of its weight, over the whole revolution**;
  `devRegionWeight_add_compl`, `rest_total`, `moving_total`.

## The encounters

* `rel_le_one`; ★ `rel_near` (**at the window, the encounter weight is at least `(1 − 1.4·10⁻³)²`**);
  ★ `rel_far` (**away from it, at most `2.8·10⁻³`**);
* `departure_near`, `returnMark` (the offset `e^{−i/5}`), `returnMark_eq`, ★ `return_far` (away
  from the return window for all but the last `0.39` radian of the revolution), `return_near`;
* `twinFlow` (both observers with their tick registers), `twinWeight` (the departure and return
  weights), `twinFlow_zero`, `twinFlow_add`, `measurable_twinFlow`, `continuous_twinWeight_twinFlow`,
  `twinPrep`, `twinWeight_twinFlow`, `continuous_twinWeight_prep`, `twinWeight_prep_nonneg`;
  `departure_before`, `departure_after`, `pi_lt_sixty_three_div_twenty`, `return_before`,
  `return_after`; ★★★ `twinDeparture`, ★★★ `twinReturn` — **the departure and the return as actual
  occurrences of one evolution**.

## The clocks

* `twin_rest_rate` (`10⁻¹¹`); ★★ `twin_moving_rate` — **the moving clock's splitting is in
  `[6·10⁻¹², 6.01·10⁻¹²]`**, three fifths of the rest splitting to the lattice's precision;
* `twinRestTick`, `twinMovingTick` (from `deviceRateTick`), `restTickBoth`, `movingTickBoth` — **both
  clocks' ticks in the arena of both**.

## The comparison

* ★★★ `dirac_two_observers` — one evolution carrying both observers; the encounter weight mutual;
  the departure written within `[2·10¹¹, 2.01·10¹¹]`, the return after one revolution; the clock at
  rest ticking within `10¹¹` of `n · 2π·10¹¹`, the moving one within `1.6·10¹¹` of `2πn/R`; the
  departure between ticks `0` and `1` of each clock, the return between ticks `117` and `122` of the
  clock at rest and `70` and `73` of the moving one; **the tick-count ratio in `[69/122, 73/116] ∋ 3/5`,
  below `1`**; the relative speed read by the observer at rest — the windows' centres over its ticks —
  in a bracket containing `4/5`, below `1`.

## The findings

1. **The moving clock runs slow, in the records.** Counted between the same two encounter records,
   the moving clock's ticks are three fifths of the resting clock's, within the tick resolution:
   `69/122 ≤ ratio ≤ 73/116`. The Galilean control (~~#243~~) has ratio `1`.
2. **The asymmetry is the ring's rest frame.** The observer at rest is at rest in the ring's frame,
   which is also the lattice's (~~#249~~); the moving one goes round and comes back. On a ring that
   frame is singled out in special relativity too, so the comparison is the twin comparison, not an
   artefact of the lattice.

## Honest scope

⚠️ **The encounter registers are a stated detector law**: each integrates a relational Born weight
over a window of offsets. The return window sits a fifth of a radian behind the observer at rest, so
that its register has no lobe at the departure; the observers are test devices that do not disturb
each other (#251).

⚠️ **The relative speed is read with the windows' centres**; their width (chord `1/10`) is not
propagated into the bracket.

⚠️ **The moving clock's period is computed from its splitting `R`**, bracketed in
`twin_moving_rate` and used only in the tick windows: the counters' thresholds `2gn|C₀|` hold no
rate (~~#273~~).

⚠️ **Reciprocity is not shown**: each observer seeing the other's clock slow needs signals exchanged
between moving observers (#256, #270).

References: `specs/BACKLOG.md` #253, #243, #262, #271, #272, #249, #251, #256, #270, #273, #39;
`RecordLayer/DiracObservers.lean`; `RecordLayer/DiracRateTicks.lean` (`deviceRateTick`,
`weightFlow`, `rateWeight`); `RecordLayer/DiracTicks.lean` (`tickMark`); `CV/DiracDevice.lean`
(`devicePacket`, `dirac_device`); `CV/DiracClockChain.lean` (`levelClockRate`, `clockRate_mem`);
`RecordLayer/TwoObservers.lean` (#243's control).
-/

@[expose] public section

open MeasureTheory Set CSD.CV Complex
open scoped Matrix

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {L : ℕ} [NeZero L]

/-! ### The two observers -/

/-- **The observers' amplitudes**: flat over `2·10⁶` modes. -/
noncomputable def twinAmp : ℤ → ℂ := fun _ => ((1 / Real.sqrt (2000000 : ℕ) : ℝ) : ℂ)

/-- **The observer at rest**: #262's device, rest energies `3` and `3 + 10⁻¹¹`, modes
`[−10⁶, 10⁶)` about momentum `0`, on a ring of length `2π·10¹³`. -/
noncomputable def restObserver (t : ℝ) : (ZMod L × Fin 2) × Fin 2 → ℂ :=
  devicePacket (L := L) (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 (3 + 1 / 10 ^ 11)
    (Finset.Ico (-1000000 : ℤ) (-1000000 + (2000000 : ℕ))) twinAmp t

/-- **The moving observer**: the same device, modes `[4·10¹³, 4·10¹³ + 2·10⁶)` about momentum `4`
— velocity `4/5`. -/
noncomputable def movingObserver (t : ℝ) : (ZMod L × Fin 2) × Fin 2 → ℂ :=
  devicePacket (L := L) (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 (3 + 1 / 10 ^ 11)
    (Finset.Ico (4 * 10 ^ 13 : ℤ) (4 * 10 ^ 13 + (2000000 : ℕ))) twinAmp t

omit [NeZero L] in
theorem rest_spread : ∀ m ∈ Finset.Ico (-1000000 : ℤ) (-1000000 + (2000000 : ℕ)),
    |2 * Real.pi * m / (2 * Real.pi * 10 ^ 13) - 0| ≤ 1 / 10 ^ 7 := by
  intro m hm
  rw [Finset.mem_Ico] at hm
  have hm' : (-1000000 : ℝ) ≤ m ∧ (m : ℝ) ≤ 999999 := by
    constructor <;> exact_mod_cast (by omega)
  rw [show 2 * Real.pi * m / (2 * Real.pi * 10 ^ 13) - 0 = m / 10 ^ 13 by field_simp; ring, abs_le]
  constructor
  · rw [le_div_iff₀ (by norm_num)]
    nlinarith [hm'.1]
  · rw [div_le_iff₀ (by norm_num)]
    nlinarith [hm'.2]

omit [NeZero L] in
theorem moving_spread : ∀ m ∈ Finset.Ico (4 * 10 ^ 13 : ℤ) (4 * 10 ^ 13 + (2000000 : ℕ)),
    |2 * Real.pi * m / (2 * Real.pi * 10 ^ 13) - 4| ≤ 2 / 10 ^ 7 := by
  intro m hm
  rw [Finset.mem_Ico] at hm
  have hm' : (4 * 10 ^ 13 : ℝ) ≤ m ∧ (m : ℝ) ≤ 4 * 10 ^ 13 + 1999999 := by
    constructor <;> exact_mod_cast (by omega)
  rw [show 2 * Real.pi * m / (2 * Real.pi * 10 ^ 13) = m / 10 ^ 13 by field_simp, abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ (by norm_num)]
    nlinarith [hm'.1]
  · rw [sub_le_iff_le_add, div_le_iff₀ (by norm_num)]
    nlinarith [hm'.2]

/-- The moving observer's predicted angular velocity: `Ω = (2π/ℓ)(4/5) = 8·10⁻¹⁴`. -/
theorem omega_twin : 2 * Real.pi / (2 * Real.pi * 10 ^ 13) * vRel 1 3 (1 * 4) = 8 / 10 ^ 14 := by
  rw [vRel_cross]
  field_simp
  norm_num

theorem devRegionWeight_add_compl (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) (A : Finset (ZMod L)) :
    devRegionWeight Ψ A + devRegionWeight Ψ Aᶜ = devRegionWeight Ψ Finset.univ :=
  Finset.sum_add_sum_compl A _

section Twin

variable (hL : 10 ^ 19 ≤ L)
include hL

omit [NeZero L] in
theorem rest_win : ∀ m ∈ Finset.Ico (-1000000 : ℤ) (-1000000 + (2000000 : ℕ)),
    -1000000 ≤ m ∧ m + 1 < -1000000 + L := by
  intro m hm
  rw [Finset.mem_Ico] at hm
  constructor <;> omega

omit [NeZero L] in
theorem moving_win : ∀ m ∈ Finset.Ico (4 * 10 ^ 13 : ℤ) (4 * 10 ^ 13 + (2000000 : ℕ)),
    4 * 10 ^ 13 ≤ m ∧ m + 1 < 4 * 10 ^ 13 + L := by
  intro m hm
  rw [Finset.mem_Ico] at hm
  constructor <;> omega

theorem twin_norm (lo : ℤ) : ∑ _m ∈ Finset.Ico lo (lo + (2000000 : ℕ)), ‖twinAmp _m‖ ^ 2 = 1 :=
  (flat_packet_localised (L := L) (c := 1) (μ := 3) (ℓ := 2 * Real.pi * 10 ^ 13) (by norm_num)
    (by positivity) lo (by norm_num) (by omega)).1

/-- **Each level's budget stays below `1.1·10⁻⁶`** for `0 ≤ t ≤ 8·10¹³`, for rest energy at least `3`,
spread at most `2·10⁻⁷` and momentum at most `4`. -/
theorem twin_budget {μ : ℝ} (hμ : 3 ≤ μ) (lo : ℤ) {D P t : ℝ} (hD0 : 0 ≤ D) (hD : D ≤ 2 / 10 ^ 7)
    (hP0 : 0 ≤ P) (hP : P ≤ 4) (ht0 : 0 ≤ t) (ht : t ≤ 8 * 10 ^ 13) :
    1 - (transPhase (ringPacket (L := L) 1 μ (2 * Real.pi * 10 ^ 13)
        (Finset.Ico lo (lo + (2000000 : ℕ))) twinAmp 0)).re
      + |t| * limitErr 1 μ (2 * Real.pi * 10 ^ 13) D P (2 * Real.pi * 10 ^ 13 / L)
      ≤ 11 / 10 ^ 7 := by
  have hπ := Real.pi_pos
  have hπ2 : Real.pi < 63 / 20 := by
    have := Real.pi_lt_d2
    norm_num at this ⊢
    linarith
  have hμ0 : 0 < μ := by linarith
  have hLr : (10 ^ 19 : ℝ) ≤ L := by exact_mod_cast hL
  obtain ⟨hW, -⟩ := noWrap_distinct_of_window (L := L) (W := Finset.Ico lo (lo + (2000000 : ℕ)))
    (lo := lo) (fun m hm => by
      rw [Finset.mem_Ico] at hm
      constructor <;> omega)
  have hRe := re_transPhase_ringPacket_ge (L := L) (c := 1) (μ := μ)
    (ℓ := 2 * Real.pi * 10 ^ 13) hμ0 (by positivity) hW (fun _ => 1 / Real.sqrt (2000000 : ℕ))
    (fun _ => by positivity)
  rw [(flat_sums lo (N := 2000000) (by norm_num)).2] at hRe
  have h6 : (Real.pi * 1 / (2 * Real.pi * 10 ^ 13 * μ)) ^ 2 ≤ 1 / 10 ^ 26 := by
    rw [show Real.pi * 1 / (2 * Real.pi * 10 ^ 13 * μ) = 1 / (2 * 10 ^ 13 * μ) by field_simp,
      div_pow, one_pow, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hRe' : 1 - 1 / 2000000 - 1 / 10 ^ 26 ≤ (transPhase (ringPacket (L := L) 1 μ
      (2 * Real.pi * 10 ^ 13) (Finset.Ico lo (lo + (2000000 : ℕ))) twinAmp 0)).re := by
    refine le_trans ?_ hRe
    have hq : (0 : ℝ) ≤ 1 - 1 / ((2000000 : ℕ) : ℝ) := by norm_num
    have hle : (1 - 1 / 10 ^ 26) * (1 - 1 / ((2000000 : ℕ) : ℝ))
        ≤ (1 - (Real.pi * 1 / (2 * Real.pi * 10 ^ 13 * μ)) ^ 2)
          * (1 - 1 / ((2000000 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) hq
    refine le_trans ?_ hle
    norm_num
  set a := 2 * Real.pi * 10 ^ 13 / L
  have ha0 : 0 ≤ a := by positivity
  have ha : a ≤ 63 / 10 ^ 7 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have herr : limitErr 1 μ (2 * Real.pi * 10 ^ 13) D P a
      = 1 / 10 ^ 13 * (1 / μ * (D + 1 / 10 ^ 13) + a ^ 2 * (P ^ 2 / 2 + P ^ 3 / (6 * μ))) := by
    unfold limitErr
    field_simp
  have hinv : 1 / μ ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hμ
  have hq1 : 1 / μ * (D + 1 / 10 ^ 13) ≤ 1 / 3 * (2 / 10 ^ 7 + 1 / 10 ^ 13) :=
    mul_le_mul hinv (by linarith) (by positivity) (by norm_num)
  have hP2 : P ^ 2 ≤ 16 := by nlinarith
  have hP3 : P ^ 3 ≤ 64 := by nlinarith [pow_le_pow_left₀ hP0 hP 3]
  have hq2 : P ^ 3 / (6 * μ) ≤ 64 / 18 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have ha2 : a ^ 2 ≤ (63 / 10 ^ 7) ^ 2 := pow_le_pow_left₀ ha0 ha 2
  have hq3 : a ^ 2 * (P ^ 2 / 2 + P ^ 3 / (6 * μ)) ≤ (63 / 10 ^ 7) ^ 2 * (16 / 2 + 64 / 18) :=
    mul_le_mul ha2 (by linarith) (by positivity) (by positivity)
  have herr0 : 0 ≤ limitErr 1 μ (2 * Real.pi * 10 ^ 13) D P a := by
    rw [herr]
    positivity
  have hle : limitErr 1 μ (2 * Real.pi * 10 ^ 13) D P a
      ≤ 1 / 10 ^ 13 * (1 / 3 * (2 / 10 ^ 7 + 1 / 10 ^ 13)
        + (63 / 10 ^ 7) ^ 2 * (16 / 2 + 64 / 18)) := by
    rw [herr]
    gcongr
  have hterm : |t| * limitErr 1 μ (2 * Real.pi * 10 ^ 13) D P a
      ≤ 8 * 10 ^ 13 * (1 / 10 ^ 13 * (1 / 3 * (2 / 10 ^ 7 + 1 / 10 ^ 13)
        + (63 / 10 ^ 7) ^ 2 * (16 / 2 + 64 / 18))) := by
    rw [abs_of_nonneg ht0]
    exact mul_le_mul ht hle herr0 (by positivity)
  have hnum : 8 * 10 ^ 13 * (1 / 10 ^ 13 * (1 / 3 * (2 / 10 ^ 7 + 1 / 10 ^ 13)
      + (63 / 10 ^ 7 : ℝ) ^ 2 * (16 / 2 + 64 / 18))) ≤ 6 / 10 ^ 7 := by norm_num
  linarith

/-- **Where the observer at rest is**: off the chord-`1/25` arc around `1`, at most `1.4·10⁻³` of
its weight, for `0 ≤ t ≤ 8·10¹³`. -/
theorem rest_tail {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 8 * 10 ^ 13) :
    devRegionWeight (restObserver (L := L) t) (chordArc 1 (1 / 25))ᶜ ≤ 14 / 10 ^ 4 := by
  have hz : ∀ μ : ℝ,
      ‖exp (I * ((2 * Real.pi / (2 * Real.pi * 10 ^ 13) * vRel 1 μ (1 * 0) * t : ℝ) : ℂ)) - 1‖
        ≤ 0 := fun μ => by
    simp [vRel]
  have h := devRegionWeight_compl_chordArc_le (L := L) (c := 1) (μ₀ := 3) (μ₁ := 3 + 1 / 10 ^ 11)
    (ℓ := 2 * Real.pi * 10 ^ 13) (P := 0) (D := 1 / 10 ^ 7) (p₀ := 0) one_pos (by norm_num)
    (by norm_num) (by positivity) (by simp) (by positivity) (rest_win hL) rest_spread twinAmp
    (twin_norm hL _) (z := 1) (ρ := 1 / 25) (η := 0) (by norm_num) t (hz 3) (hz _)
  have b0 := twin_budget (L := L) hL (μ := 3) le_rfl (-1000000) (D := 1 / 10 ^ 7) (P := 0)
    (by positivity) (by norm_num) le_rfl (by norm_num) ht0 ht
  have b1 := twin_budget (L := L) hL (μ := 3 + 1 / 10 ^ 11) (by norm_num) (-1000000)
    (D := 1 / 10 ^ 7) (P := 0) (by positivity) (by norm_num) le_rfl (by norm_num) ht0 ht
  have hnn := devRegionWeight_nonneg (restObserver (L := L) t) (chordArc 1 (1 / 25))ᶜ
  unfold restObserver at hnn ⊢
  rw [sub_zero] at h
  nlinarith

/-- **Where the moving observer is**: off the chord-`1/25` arc around `e^{iΩt}`, `Ω = 8·10⁻¹⁴`, at
most `1.4·10⁻³` of its weight, for `0 ≤ t ≤ 8·10¹³` — both levels, the upper one lagging by less
than `10⁻⁹`. -/
theorem moving_tail {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 8 * 10 ^ 13) :
    devRegionWeight (movingObserver (L := L) t)
        (chordArc (exp (I * ((8 / 10 ^ 14 * t : ℝ) : ℂ))) (1 / 25))ᶜ ≤ 14 / 10 ^ 4 := by
  have hz₀ : ‖exp (I * ((2 * Real.pi / (2 * Real.pi * 10 ^ 13) * vRel 1 3 (1 * 4) * t : ℝ) : ℂ))
      - exp (I * ((8 / 10 ^ 14 * t : ℝ) : ℂ))‖ ≤ 1 / 10 ^ 9 := by
    rw [omega_twin, sub_self, norm_zero]
    positivity
  have hz₁ : ‖exp (I * ((2 * Real.pi / (2 * Real.pi * 10 ^ 13) * vRel 1 (3 + 1 / 10 ^ 11) (1 * 4)
      * t : ℝ) : ℂ)) - exp (I * ((8 / 10 ^ 14 * t : ℝ) : ℂ))‖ ≤ 1 / 10 ^ 9 := by
    refine (norm_exp_sub_exp_le _ _).trans ?_
    have hv := abs_vRel_sub_le (c := 1) (μ₀ := 3) (μ₁ := 3 + 1 / 10 ^ 11) (by norm_num)
      (by norm_num) (by norm_num) (1 * 4)
    rw [vRel_cross] at hv
    have hk : 2 * Real.pi / (2 * Real.pi * 10 ^ 13) = 1 / 10 ^ 13 := by
      field_simp
    rw [hk, show 1 / 10 ^ 13 * vRel 1 (3 + 1 / 10 ^ 11) (1 * 4) * t - 8 / 10 ^ 14 * t
        = 1 / 10 ^ 13 * t * (vRel 1 (3 + 1 / 10 ^ 11) (1 * 4) - 4 / 5) by ring, abs_mul,
      abs_of_nonneg (by positivity)]
    calc 1 / 10 ^ 13 * t * |vRel 1 (3 + 1 / 10 ^ 11) (1 * 4) - 4 / 5|
        ≤ 1 / 10 ^ 13 * (8 * 10 ^ 13) * (1 * (3 + 1 / 10 ^ 11 - 3) / 3) := by gcongr
      _ ≤ 1 / 10 ^ 9 := by norm_num
  have h := devRegionWeight_compl_chordArc_le (L := L) (c := 1) (μ₀ := 3) (μ₁ := 3 + 1 / 10 ^ 11)
    (ℓ := 2 * Real.pi * 10 ^ 13) (P := 4) (D := 2 / 10 ^ 7) (p₀ := 4) one_pos (by norm_num)
    (by norm_num) (by positivity) (by norm_num) (by positivity) (moving_win hL) moving_spread
    twinAmp (twin_norm hL _) (z := exp (I * ((8 / 10 ^ 14 * t : ℝ) : ℂ))) (ρ := 1 / 25)
    (η := 1 / 10 ^ 9) (by norm_num) t hz₀ hz₁
  have b0 := twin_budget (L := L) hL (μ := 3) le_rfl (4 * 10 ^ 13) (D := 2 / 10 ^ 7) (P := 4)
    (by positivity) le_rfl (by norm_num) le_rfl ht0 ht
  have b1 := twin_budget (L := L) hL (μ := 3 + 1 / 10 ^ 11) (by norm_num) (4 * 10 ^ 13)
    (D := 2 / 10 ^ 7) (P := 4) (by positivity) le_rfl (by norm_num) le_rfl ht0 ht
  have hnn := devRegionWeight_nonneg (movingObserver (L := L) t)
    (chordArc (exp (I * ((8 / 10 ^ 14 * t : ℝ) : ℂ))) (1 / 25))ᶜ
  unfold movingObserver at hnn ⊢
  nlinarith

theorem rest_total (t : ℝ) : devRegionWeight (restObserver (L := L) t) Finset.univ = 1 :=
  devRegionWeight_univ (L := L) (c := 1) (P := 0) (D := 1 / 10 ^ 7) (p₀ := 0) one_pos
    (by norm_num) (by norm_num) (by positivity) (by simp) (by positivity) (rest_win hL)
    rest_spread twinAmp (twin_norm hL _) t

theorem moving_total (t : ℝ) : devRegionWeight (movingObserver (L := L) t) Finset.univ = 1 :=
  devRegionWeight_univ (L := L) (c := 1) (P := 4) (D := 2 / 10 ^ 7) (p₀ := 4) one_pos
    (by norm_num) (by norm_num) (by positivity) (by norm_num) (by positivity) (moving_win hL)
    moving_spread twinAmp (twin_norm hL _) t

/-- **The encounter weight is at most `1`.** -/
theorem rel_le_one (w : ℂ) (t : ℝ) :
    relWeight w (1 / 10) (restObserver (L := L) t) (movingObserver (L := L) t) ≤ 1 := by
  have h := relWeight_le_mul w (1 / 10) (restObserver (L := L) t) (movingObserver (L := L) t)
  rwa [rest_total hL, moving_total hL, one_mul] at h

/-- ★ **When the moving observer is at the window, the encounter weight is nearly `1`**: if its
predicted point is within `1/50` of the window's centre, the weight is at least `(1 − 1.4·10⁻³)²`. -/
theorem rel_near (w : ℂ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 8 * 10 ^ 13)
    (h : ‖exp (I * ((8 / 10 ^ 14 * t : ℝ) : ℂ)) - w‖ ≤ 1 / 50) :
    (1 - 14 / 10 ^ 4) ^ 2
      ≤ relWeight w (1 / 10) (restObserver (L := L) t) (movingObserver (L := L) t) := by
  have hX := devRegionWeight_add_compl (restObserver (L := L) t) (chordArc 1 (1 / 25))
  have hY := devRegionWeight_add_compl (movingObserver (L := L) t)
    (chordArc (exp (I * ((8 / 10 ^ 14 * t : ℝ) : ℂ))) (1 / 25))
  rw [rest_total hL] at hX
  rw [moving_total hL] at hY
  have tA := rest_tail hL ht0 ht
  have tB := moving_tail hL ht0 ht
  have hle := le_relWeight (w := w) (ρ := 1 / 10) (ΨA := restObserver (L := L) t)
    (ΨB := movingObserver (L := L) t) (X := chordArc 1 (1 / 25))
    (Y := chordArc (exp (I * ((8 / 10 ^ 14 * t : ℝ) : ℂ))) (1 / 25)) fun j hj k hk =>
      offset_mem_of_near (norm_exp_I_mul_ofReal_eq_one _) (mem_chordArc.1 hj) (mem_chordArc.1 hk)
        (by linarith)
  have hA : 1 - 14 / 10 ^ 4 ≤ devRegionWeight (restObserver (L := L) t) (chordArc 1 (1 / 25)) := by
    linarith
  have hB : 1 - 14 / 10 ^ 4 ≤ devRegionWeight (movingObserver (L := L) t)
      (chordArc (exp (I * ((8 / 10 ^ 14 * t : ℝ) : ℂ))) (1 / 25)) := by linarith
  calc (1 - 14 / 10 ^ 4 : ℝ) ^ 2 = (1 - 14 / 10 ^ 4) * (1 - 14 / 10 ^ 4) := sq _
    _ ≤ _ := mul_le_mul hA hB (by norm_num) (devRegionWeight_nonneg _ _)
    _ ≤ _ := hle

/-- ★ **When the moving observer is far from the window, the encounter weight is small**: if its
predicted point is more than `9/50` from the window's centre, the weight is at most `2.8·10⁻³`. -/
theorem rel_far (w : ℂ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 8 * 10 ^ 13)
    (h : 9 / 50 < ‖exp (I * ((8 / 10 ^ 14 * t : ℝ) : ℂ)) - w‖) :
    relWeight w (1 / 10) (restObserver (L := L) t) (movingObserver (L := L) t) ≤ 28 / 10 ^ 4 := by
  have tA := rest_tail hL ht0 ht
  have tB := moving_tail hL ht0 ht
  have hle := relWeight_le (w := w) (ρ := 1 / 10) (ΨA := restObserver (L := L) t)
    (ΨB := movingObserver (L := L) t) (X := chordArc 1 (1 / 25))
    (Y := chordArc (exp (I * ((8 / 10 ^ 14 * t : ℝ) : ℂ))) (1 / 25)) fun j hj k hk =>
      offset_not_mem_of_far (norm_exp_I_mul_ofReal_eq_one _) (mem_chordArc.1 hj) (mem_chordArc.1 hk)
        (by linarith)
  rw [rest_total hL, moving_total hL, mul_one, one_mul] at hle
  linarith

omit [NeZero L] hL in
/-- **At the start the moving observer is at the departure window**: `|e^{iΩt} − 1| ≤ 1/50` for
`0 ≤ t ≤ 2.5·10¹¹`. -/
theorem departure_near {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 25 * 10 ^ 10) :
    ‖exp (I * ((8 / 10 ^ 14 * t : ℝ) : ℂ)) - 1‖ ≤ 1 / 50 := by
  have h := norm_exp_sub_exp_le (8 / 10 ^ 14 * t) 0
  rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_zero,
    abs_of_nonneg (by positivity)] at h
  exact h.trans (by nlinarith)

/-- **The return window's centre**: the offset `e^{−i/5}`, a fifth of a radian behind. -/
noncomputable def returnMark : ℂ := exp (I * ((-(1 / 5) : ℝ) : ℂ))

omit [NeZero L] hL in
theorem returnMark_eq : returnMark = exp (I * ((2 * Real.pi - 1 / 5 : ℝ) : ℂ)) := by
  rw [returnMark, show I * ((2 * Real.pi - 1 / 5 : ℝ) : ℂ) = I * ((-(1 / 5) : ℝ) : ℂ)
    + 2 * Real.pi * I by push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

omit [NeZero L] hL in
/-- **Away from the return window for most of the revolution**: `|e^{iΩt} − e^{−i/5}| > 9/50` for
`0 ≤ t ≤ (2π − 0.39)·1.25·10¹³`. -/
theorem return_far {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ (2 * Real.pi - 39 / 100) * (125 * 10 ^ 11)) :
    9 / 50 < ‖exp (I * ((8 / 10 ^ 14 * t : ℝ) : ℂ)) - returnMark‖ := by
  have e : exp (I * ((8 / 10 ^ 14 * t : ℝ) : ℂ)) - returnMark
      = returnMark * (exp (I * ((8 / 10 ^ 14 * t + 1 / 5 : ℝ) : ℂ)) - 1) := by
    rw [returnMark, mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e, norm_mul, returnMark, norm_exp_I_mul_ofReal_eq_one, one_mul]
  have hz0 : 0 ≤ 8 / 10 ^ 14 * t + 1 / 5 := by positivity
  have h2 : 8 / 10 ^ 14 * t + 1 / 5 ≤ 2 * Real.pi - 19 / 100 := by nlinarith
  have hs := two_sin_le_norm_exp_sub_one (y := 19 / 100) (z := 8 / 10 ^ 14 * t + 1 / 5)
    (by norm_num) (by rw [abs_of_nonneg hz0]; linarith) (by rw [abs_of_nonneg hz0]; exact h2)
  have hsin := Real.sin_gt_sub_cube (x := 19 / 100 / 2) (by norm_num)
  have : (9 / 50 : ℝ) < 2 * (19 / 100 / 2 - (19 / 100 / 2) ^ 3 / 6) := by norm_num
  linarith

omit [NeZero L] hL in
/-- **At the return window near the end of the revolution**: `|e^{iΩt} − e^{−i/5}| ≤ 1/50` for
`(2π − 0.22)·1.25·10¹³ ≤ t ≤ (2π − 0.18)·1.25·10¹³`. -/
theorem return_near {t : ℝ} (ht1 : (2 * Real.pi - 11 / 50) * (125 * 10 ^ 11) ≤ t)
    (ht2 : t ≤ (2 * Real.pi - 9 / 50) * (125 * 10 ^ 11)) :
    ‖exp (I * ((8 / 10 ^ 14 * t : ℝ) : ℂ)) - returnMark‖ ≤ 1 / 50 := by
  rw [returnMark_eq]
  refine (norm_exp_sub_exp_le _ _).trans ?_
  rw [abs_le]
  constructor <;> nlinarith

/-! ### The arena of the two observers -/

/-- **The two observers, each with its tick register, side by side**: each device by
`e^{−itH_dev}` on the same chain, each register by its own tick weight. -/
noncomputable def twinFlow (t : ℝ) (x : TickArena L × TickArena L) : TickArena L × TickArena L :=
  (weightFlow (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 (3 + 1 / 10 ^ 11) 1
      (rateWeight (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 (3 + 1 / 10 ^ 11)
        (tickMark (restObserver (L := L) 0))) t x.1,
    weightFlow (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 (3 + 1 / 10 ^ 11) 1
      (rateWeight (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 (3 + 1 / 10 ^ 11)
        (tickMark (movingObserver (L := L) 0))) t x.2)

/-- **The encounter weights**: `false` the departure window (offset `1`), `true` the return window
(offset `e^{−i/5}`), each of chord `1/10`. -/
noncomputable def twinWeight (b : Bool) (x : TickArena L × TickArena L) : ℝ :=
  relWeight (if b then returnMark else 1) (1 / 10) x.1.1 x.2.1

omit hL in
theorem twinFlow_zero (x : TickArena L × TickArena L) : twinFlow 0 x = x :=
  Prod.ext (weightFlow_zero _ _ _ _ _ _) (weightFlow_zero _ _ _ _ _ _)

omit hL in
theorem twinFlow_add (s t : ℝ) (x : TickArena L × TickArena L) :
    twinFlow (s + t) x = twinFlow t (twinFlow s x) :=
  Prod.ext (weightFlow_add _ _ _ _ (continuous_rateWeight _ _ _ _) _ _ _)
    (weightFlow_add _ _ _ _ (continuous_rateWeight _ _ _ _) _ _ _)

omit hL in
theorem measurable_twinFlow (t : ℝ) : Measurable (twinFlow (L := L) t) :=
  ((measurable_weightFlow _ _ _ _ (continuous_rateWeight _ _ _ _) t).comp measurable_fst).prodMk
    ((measurable_weightFlow _ _ _ _ (continuous_rateWeight _ _ _ _) t).comp measurable_snd)

omit hL in
theorem continuous_twinWeight_twinFlow (b : Bool) :
    Continuous fun p : (TickArena L × TickArena L) × ℝ => twinWeight b (twinFlow p.2 p.1) := by
  have hA : Continuous fun p : (TickArena L × TickArena L) × ℝ =>
      deviceProp (L := L) (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 (3 + 1 / 10 ^ 11) p.2
        *ᵥ p.1.1.1 :=
    (continuous_deviceProp_mulVec _ _ _).comp (continuous_fst.fst.fst.prodMk continuous_snd)
  have hB : Continuous fun p : (TickArena L × TickArena L) × ℝ =>
      deviceProp (L := L) (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 (3 + 1 / 10 ^ 11) p.2
        *ᵥ p.1.2.1 :=
    (continuous_deviceProp_mulVec _ _ _).comp (continuous_fst.snd.fst.prodMk continuous_snd)
  have e : (fun p : (TickArena L × TickArena L) × ℝ => twinWeight b (twinFlow p.2 p.1))
      = fun p => relWeight (if b then returnMark else 1) (1 / 10)
        (deviceProp (L := L) (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 (3 + 1 / 10 ^ 11) p.2
          *ᵥ p.1.1.1)
        (deviceProp (L := L) (scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) 3 (3 + 1 / 10 ^ 11) p.2
          *ᵥ p.1.2.1) := by
    funext p
    simp only [twinWeight, twinFlow, state_weightFlow]
  rw [e]
  have h := continuous_relWeight_comp hA hB (if b then returnMark else 1) (1 / 10)
  exact h

/-- **The preparation**: both observers at time `0`, every register at `0`. -/
noncomputable def twinPrep : TickArena L × TickArena L :=
  ((restObserver (L := L) 0, 0), (movingObserver (L := L) 0, 0))

omit hL in
theorem twinWeight_twinFlow (b : Bool) (s : ℝ) :
    twinWeight b (twinFlow s (twinPrep (L := L)))
      = relWeight (if b then returnMark else 1) (1 / 10) (restObserver (L := L) s)
        (movingObserver (L := L) s) := by
  show relWeight _ _ (deviceProp _ _ _ s *ᵥ restObserver (L := L) 0)
    (deviceProp _ _ _ s *ᵥ movingObserver (L := L) 0) = _
  rw [restObserver, movingObserver, deviceProp_devicePacket, deviceProp_devicePacket]
  rfl

omit hL in
theorem continuous_twinWeight_prep (b : Bool) :
    Continuous fun s => twinWeight b (twinFlow s (twinPrep (L := L))) := by
  have h := (continuous_twinWeight_twinFlow (L := L) b).comp
    (continuous_const.prodMk continuous_id : Continuous fun s : ℝ => (twinPrep (L := L), s))
  exact h

omit hL in
theorem twinWeight_prep_nonneg (b : Bool) (s : ℝ) :
    0 ≤ twinWeight b (twinFlow s (twinPrep (L := L))) := by
  rw [twinWeight_twinFlow]
  exact relWeight_nonneg _ _ _ _

theorem departure_before {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 2 * 10 ^ 11) :
    ∫ s in (0 : ℝ)..t, twinWeight false (twinFlow s (twinPrep (L := L))) < 2 * 10 ^ 11 := by
  have h := integral_le_of_le_on (continuous_twinWeight_prep (L := L) false) (ε := 1) ht0 le_rfl
    fun s _ _ => by
      rw [twinWeight_twinFlow]
      exact rel_le_one hL _ s
  linarith

theorem departure_after :
    2 * 10 ^ 11 ≤ ∫ s in (0 : ℝ)..201 * 10 ^ 9, twinWeight false (twinFlow s (twinPrep (L := L))) := by
  have h := le_integral_of_ge_on (continuous_twinWeight_prep (L := L) false)
    (κ := (1 - 14 / 10 ^ 4) ^ 2) (tn := 0) (te := 25 * 10 ^ 10) (t := 201 * 10 ^ 9) le_rfl
    (by norm_num) (by norm_num) (fun s _ => twinWeight_prep_nonneg false s)
    fun s hs1 hs2 => by
      rw [twinWeight_twinFlow]
      exact rel_near hL _ hs1 (by linarith) (departure_near hs1 hs2)
  have : (2 * 10 ^ 11 : ℝ) ≤ (1 - 14 / 10 ^ 4) ^ 2 * (201 * 10 ^ 9 - 0) := by norm_num
  exact this.trans h

omit [NeZero L] hL in
theorem pi_lt_sixty_three_div_twenty : Real.pi < 63 / 20 := by
  have := Real.pi_lt_d2
  norm_num at this ⊢
  linarith

theorem return_before {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < (2 * Real.pi - 39 / 100) * (125 * 10 ^ 11) + 8 * 10 ^ 10) :
    ∫ s in (0 : ℝ)..t, twinWeight true (twinFlow s (twinPrep (L := L))) < 3 * 10 ^ 11 := by
  have hπ := Real.pi_pos
  have hπ1 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hπ2 := pi_lt_sixty_three_div_twenty
  have hF := continuous_twinWeight_prep (L := L) true
  have hfar : ∀ s, 0 ≤ s → s ≤ (2 * Real.pi - 39 / 100) * (125 * 10 ^ 11) →
      twinWeight true (twinFlow s (twinPrep (L := L))) ≤ 28 / 10 ^ 4 := fun s hs0 hs => by
    rw [twinWeight_twinFlow]
    exact rel_far hL _ hs0 (by nlinarith) (return_far hs0 hs)
  have htf : (28 / 10 ^ 4 : ℝ) * ((2 * Real.pi - 39 / 100) * (125 * 10 ^ 11)) + 8 * 10 ^ 10
      < 3 * 10 ^ 11 := by nlinarith
  rcases le_total t ((2 * Real.pi - 39 / 100) * (125 * 10 ^ 11)) with h | h
  · have h1 := integral_le_of_le_on hF ht0 h hfar
    have h2 : 28 / 10 ^ 4 * t ≤ 28 / 10 ^ 4 * ((2 * Real.pi - 39 / 100) * (125 * 10 ^ 11)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    linarith
  · have h1 := integral_le_of_le_on_then_one hF (by nlinarith) h hfar fun s => by
      rw [twinWeight_twinFlow]
      exact rel_le_one hL _ s
    linarith

theorem return_after :
    3 * 10 ^ 11 ≤ ∫ s in (0 : ℝ)..(2 * Real.pi - 11 / 50) * (125 * 10 ^ 11) + 301 * 10 ^ 9,
      twinWeight true (twinFlow s (twinPrep (L := L))) := by
  have hπ := Real.pi_pos
  have hπ1 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hπ2 := pi_lt_sixty_three_div_twenty
  have h := le_integral_of_ge_on (continuous_twinWeight_prep (L := L) true)
    (κ := (1 - 14 / 10 ^ 4) ^ 2) (tn := (2 * Real.pi - 11 / 50) * (125 * 10 ^ 11))
    (te := (2 * Real.pi - 9 / 50) * (125 * 10 ^ 11))
    (t := (2 * Real.pi - 11 / 50) * (125 * 10 ^ 11) + 301 * 10 ^ 9) (by nlinarith)
    (by linarith) (by nlinarith) (fun s _ => twinWeight_prep_nonneg true s)
    fun s hs1 hs2 => by
      rw [twinWeight_twinFlow]
      exact rel_near hL _ (by nlinarith) (by nlinarith) (return_near hs1 hs2)
  have : (3 * 10 ^ 11 : ℝ) ≤ (1 - 14 / 10 ^ 4) ^ 2
      * ((2 * Real.pi - 11 / 50) * (125 * 10 ^ 11) + 301 * 10 ^ 9
        - (2 * Real.pi - 11 / 50) * (125 * 10 ^ 11)) := by
    rw [add_sub_cancel_left]
    norm_num
  exact this.trans h

/-- ★★★ **The departure, recorded**: the encounter register of the departure window — the joint
weight of the moving observer at offset within chord `1/10` of `1` from the observer at rest, and so
of the observer at rest at offset within it of `1` from the moving one — reaches `2·10¹¹` within
`[2·10¹¹, 2.01·10¹¹]`. -/
noncomputable def twinDeparture {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence ((TickArena L × TickArena L) × (Bool → ℝ)) ℕ L :=
  regDetector twinFlow twinWeight twinFlow_zero twinFlow_add continuous_twinWeight_twinFlow
    measurable_twinFlow false (2 * 10 ^ 11) twinPrep Finset.univ (τ₀ := 2 * 10 ^ 11)
    (τ₁ := 201 * 10 ^ 9) (by positivity) (by norm_num) hw
    (fun s _ => twinWeight_prep_nonneg false s) (fun _ ht0 ht => departure_before hL ht0 ht)
    (departure_after hL)

/-- ★★★ **The return, recorded**: the encounter register of the return window — offset within chord
`1/10` of `e^{−i/5}`, a fifth of a radian behind — reaches `3·10¹¹` within
`[(2π − 0.39)·1.25·10¹³ + 8·10¹⁰, (2π − 0.22)·1.25·10¹³ + 3.01·10¹¹]`, after a revolution. -/
noncomputable def twinReturn {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence ((TickArena L × TickArena L) × (Bool → ℝ)) ℕ L :=
  regDetector twinFlow twinWeight twinFlow_zero twinFlow_add continuous_twinWeight_twinFlow
    measurable_twinFlow true (3 * 10 ^ 11) twinPrep Finset.univ
    (τ₀ := (2 * Real.pi - 39 / 100) * (125 * 10 ^ 11) + 8 * 10 ^ 10)
    (τ₁ := (2 * Real.pi - 11 / 50) * (125 * 10 ^ 11) + 301 * 10 ^ 9)
    (by nlinarith [Real.pi_gt_three]) (by nlinarith [Real.pi_gt_three]) hw
    (fun s _ => twinWeight_prep_nonneg true s) (fun _ ht0 ht => return_before hL ht0 ht)
    (return_after hL)

/-! ### The two clocks -/

omit [NeZero L] hL in
/-- The clock at rest turns at the rest splitting `10⁻¹¹`. -/
theorem twin_rest_rate :
    levelClockRate 3 (3 + 1 / 10 ^ 11)
      (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * 0))
      = 1 / 10 ^ 11 := by
  rw [mul_zero, Real.sin_zero, mul_zero, levelClockRate, dispE, dispE,
    show ((3 : ℝ) + 1 / 10 ^ 11) ^ 2 + 0 ^ 2 = (3 + 1 / 10 ^ 11) ^ 2 by ring,
    Real.sqrt_sq (by norm_num), show (3 : ℝ) ^ 2 + 0 ^ 2 = 3 ^ 2 by ring,
    Real.sqrt_sq (by norm_num)]
  ring

omit [NeZero L] in
/-- ★★ **The moving clock turns at `3/5` of the rest rate**: its splitting lies in
`[6·10⁻¹², 6.01·10⁻¹²]` — the dilation `√(1 − (4/5)²) = 3/5`, to the lattice's precision. -/
theorem twin_moving_rate :
    6 / 10 ^ 12 ≤ levelClockRate 3 (3 + 1 / 10 ^ 11)
        (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * 4))
    ∧ levelClockRate 3 (3 + 1 / 10 ^ 11)
        (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * 4))
      ≤ 601 / 10 ^ 14 := by
  have hπ := Real.pi_pos
  have hπ2 : Real.pi < 63 / 20 := by
    have := Real.pi_lt_d2
    norm_num at this ⊢
    linarith
  have hLr : (10 ^ 19 : ℝ) ≤ L := by exact_mod_cast hL
  set a := 2 * Real.pi * 10 ^ 13 / L
  have ha0 : 0 < a := by positivity
  have ha : a ≤ 63 / 10 ^ 7 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hs : 2 * scaledHop 1 a * Real.sin (a * 4) = Real.sin (4 * a) / a := by
    rw [scaledHop, mul_comm a 4]
    field_simp
  set s := 2 * scaledHop 1 a * Real.sin (a * 4)
  have hs_le : |s| ≤ 4 := by
    rw [hs, abs_div, abs_of_pos ha0, div_le_iff₀ ha0]
    have := Real.abs_sin_sub_sin_le (4 * a) 0
    rw [Real.sin_zero, sub_zero, sub_zero, abs_of_pos (show (0 : ℝ) < 4 * a by positivity)] at this
    linarith
  have hs_ge : 399 / 100 ≤ s := by
    rw [hs, le_div_iff₀ ha0]
    have := Real.sin_gt_sub_cube (x := 4 * a) (by positivity)
    have ha2 : a ^ 2 ≤ (63 / 10 ^ 7) ^ 2 := pow_le_pow_left₀ ha0.le ha 2
    nlinarith
  obtain ⟨hlo, hhi⟩ := clockRate_mem (μ₀ := 3) (μ₁ := 3 + 1 / 10 ^ 11) (by norm_num) (by norm_num) s
  have hE0 : dispE 3 s ≤ 5 := by
    rw [dispE, Real.sqrt_le_left (by norm_num)]
    have := sq_abs s
    nlinarith [abs_nonneg s]
  have hE1 : 4992 / 1000 ≤ dispE (3 + 1 / 10 ^ 11) s := by
    rw [dispE]
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith
  have hE0p := dispE_pos (μ := 3) (by norm_num) s
  constructor
  · refine le_trans ?_ hlo
    rw [show (3 + 1 / 10 ^ 11 - 3 : ℝ) = 1 / 10 ^ 11 by ring]
    have : (3 : ℝ) / 5 ≤ 3 / dispE 3 s := div_le_div_of_nonneg_left (by norm_num) hE0p hE0
    nlinarith
  · refine hhi.trans ?_
    rw [show (3 + 1 / 10 ^ 11 - 3 : ℝ) = 1 / 10 ^ 11 by ring]
    have : (3 + 1 / 10 ^ 11 : ℝ) / dispE (3 + 1 / 10 ^ 11) s ≤ (3 + 1 / 10 ^ 11) / (4992 / 1000) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hE1
    have hnum : (1 / 10 ^ 11 : ℝ) * ((3 + 1 / 10 ^ 11) / (4992 / 1000)) ≤ 601 / 10 ^ 14 := by
      norm_num
    nlinarith

/-- **Tick `n` of the observer at rest** (`n ≤ 130`): written within `10¹¹` of `n · 2π·10¹¹`. -/
noncomputable def twinRestTick (n : ℕ) (hn : n ≤ 130) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (TickArena L) ℕ L :=
  deviceRateTick (L := L) (c := 1) (μ₀ := 3) (μ₁ := 3 + 1 / 10 ^ 11) (ℓ := 2 * Real.pi * 10 ^ 13)
    (P := 0) (D := 1 / 10 ^ 7) (p₀ := 0) (W := Finset.Ico (-1000000 : ℤ) (-1000000 + (2000000 : ℕ)))
    (lo := -1000000) (g := 1) one_pos one_pos (by norm_num) (by norm_num) (by norm_num)
    (by positivity) (by simp) (by positivity) (rest_win hL) rest_spread twinAmp (twin_norm hL _) n
    (δ := 10 ^ 11) (by positivity) (by rw [twin_rest_rate]; norm_num)
    (by
      rw [twin_rest_rate]
      have hπ2 : Real.pi < 63 / 20 := by
        have := Real.pi_lt_d2
        norm_num at this ⊢
        linarith
      have hn' : (n : ℝ) ≤ 130 := by exact_mod_cast hn
      have hx0 : 0 ≤ 2 * Real.pi * n / (1 / 10 ^ 11) + 10 ^ 11 := by positivity
      have hx1 : 2 * Real.pi * n / (1 / 10 ^ 11) + 10 ^ 11 ≤ 10 ^ 14 := by
        rw [show 2 * Real.pi * n / (1 / 10 ^ 11) = 2 * Real.pi * n * 10 ^ 11 by field_simp]
        nlinarith [mul_le_mul hπ2.le hn' (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) ≤ 63 / 20),
          Real.pi_pos]
      have hsq := pow_le_pow_left₀ hx0 hx1 2
      have hd : deviceDrift 1 3 (3 + 1 / 10 ^ 11) (1 / 10 ^ 7) 0 = 1 / (36 * 10 ^ 25) := by
        simp only [deviceDrift, abs_zero]
        norm_num
      rw [hd]
      calc 1 / (36 * 10 ^ 25) * ((2 * Real.pi * n / (1 / 10 ^ 11) + 10 ^ 11) ^ 2
            + 2 * (2 * Real.pi * n / (1 / 10 ^ 11) + 10 ^ 11) / (1 / 10 ^ 11))
          ≤ 1 / (36 * 10 ^ 25) * ((10 ^ 14) ^ 2 + 2 * 10 ^ 14 / (1 / 10 ^ 11)) := by gcongr
        _ < _ := by norm_num)
    hw

/-- **Tick `n` of the moving observer** (`n ≤ 80`): written within `1.6·10¹¹` of `2πn/R`, its
splitting `R ∈ [6·10⁻¹², 6.01·10⁻¹²]`. -/
noncomputable def twinMovingTick (n : ℕ) (hn : n ≤ 80) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (TickArena L) ℕ L :=
  have hR := twin_moving_rate (L := L) hL
  deviceRateTick (L := L) (c := 1) (μ₀ := 3) (μ₁ := 3 + 1 / 10 ^ 11) (ℓ := 2 * Real.pi * 10 ^ 13)
    (P := 4) (D := 2 / 10 ^ 7) (p₀ := 4)
    (W := Finset.Ico (4 * 10 ^ 13 : ℤ) (4 * 10 ^ 13 + (2000000 : ℕ))) (lo := 4 * 10 ^ 13) (g := 1)
    one_pos one_pos (by norm_num) (by norm_num) (by norm_num) (by positivity) (by norm_num)
    (by positivity) (moving_win hL) moving_spread twinAmp (twin_norm hL _) n (δ := 16 * 10 ^ 10)
    (by positivity)
    (by
      rw [le_div_iff₀ (by linarith [hR.1])]
      nlinarith [hR.2])
    (by
      set R := levelClockRate 3 (3 + 1 / 10 ^ 11)
        (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * 4))
      have hR0 : 0 < R := by linarith [hR.1]
      have hπ2 : Real.pi < 63 / 20 := by
        have := Real.pi_lt_d2
        norm_num at this ⊢
        linarith
      have hn' : (n : ℝ) ≤ 80 := by exact_mod_cast hn
      have hx0 : 0 ≤ 2 * Real.pi * n / R + 16 * 10 ^ 10 := by positivity
      have hdiv : 2 * Real.pi * n / R ≤ 2 * Real.pi * n / (6 / 10 ^ 12) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hR.1
      have hx1 : 2 * Real.pi * n / R + 16 * 10 ^ 10 ≤ 9 * 10 ^ 13 := by
        rw [show 2 * Real.pi * n / (6 / 10 ^ 12) = 2 * Real.pi * n * (10 ^ 12 / 6) by
          field_simp] at hdiv
        nlinarith [mul_le_mul hπ2.le hn' (Nat.cast_nonneg n) (by norm_num : (0 : ℝ) ≤ 63 / 20),
          Real.pi_pos]
      have hsq := pow_le_pow_left₀ hx0 hx1 2
      have hd : deviceDrift 1 3 (3 + 1 / 10 ^ 11) (2 / 10 ^ 7) 4
          = 2 / 10 ^ 7 * (2 * 1 * 4 + 1 * (2 / 10 ^ 7)) * (1 / 10 ^ 11) / 36 := by
        simp only [deviceDrift, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
        norm_num
      rw [hd]
      have hR1 : 6 / 10 ^ 12 ≤ R := hR.1
      calc 2 / 10 ^ 7 * (2 * 1 * 4 + 1 * (2 / 10 ^ 7)) * (1 / 10 ^ 11) / 36
            * ((2 * Real.pi * n / R + 16 * 10 ^ 10) ^ 2 + 2 * (2 * Real.pi * n / R + 16 * 10 ^ 10) / R)
          ≤ 2 / 10 ^ 7 * (2 * 1 * 4 + 1 * (2 / 10 ^ 7)) * (1 / 10 ^ 11) / 36
            * ((9 * 10 ^ 13) ^ 2 + 2 * (9 * 10 ^ 13) / (6 / 10 ^ 12)) := by gcongr
        _ < _ := by norm_num)
    hw

/-- **The observer at rest's tick `n`, in the arena of both.** -/
noncomputable def restTickBoth (n : ℕ) (hn : n ≤ 130) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence ((TickArena L × TickArena L) × (Bool → ℝ)) ℕ L :=
  (twinRestTick hL n hn hw).pullback (regEvolve twinFlow twinWeight)
    (regEvolve_self twinFlow twinWeight twinFlow_zero)
    (regEvolve_comp twinFlow twinWeight twinFlow_add continuous_twinWeight_twinFlow)
    (fun s t => measurable_regFlow twinFlow twinWeight measurable_twinFlow
      continuous_twinWeight_twinFlow (t - s))
    (fun y => y.1.1) measurable_fst.fst (fun _ _ _ => rfl) (twinPrep, 0) rfl

/-- **The moving observer's tick `n`, in the arena of both.** -/
noncomputable def movingTickBoth (n : ℕ) (hn : n ≤ 80) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence ((TickArena L × TickArena L) × (Bool → ℝ)) ℕ L :=
  (twinMovingTick hL n hn hw).pullback (regEvolve twinFlow twinWeight)
    (regEvolve_self twinFlow twinWeight twinFlow_zero)
    (regEvolve_comp twinFlow twinWeight twinFlow_add continuous_twinWeight_twinFlow)
    (fun s t => measurable_regFlow twinFlow twinWeight measurable_twinFlow
      continuous_twinWeight_twinFlow (t - s))
    (fun y => y.1.2) measurable_fst.snd (fun _ _ _ => rfl) (twinPrep, 0) rfl

/-! ### The comparison -/

/-- ★★★ **Two observers on the Dirac chain, and their clocks compared** (BACKLOG #253). On a ring of
length `2π·10¹³` (`c = 1`), #262's device at rest and the same device moving at `4/5`, each with its
rate counter, and the encounter registers of a departure window (offset within chord `1/10` of `1`)
and a return window (within chord `1/10` of `e^{−i/5}`):

* **one evolution**: the departure record, the return record and the ticks of both clocks are actual
  occurrences of the same evolution from the same preparation, which carries both observers;
* **mutual**: the encounter weight of the moving observer seen from the one at rest at offset `w` is
  that of the one at rest seen from the moving one at offset `w̄`;
* **the records**: the departure is written within `[2·10¹¹, 2.01·10¹¹]`, the return — after one
  revolution — within `[(2π − 0.39)·1.25·10¹³ + 8·10¹⁰, (2π − 0.22)·1.25·10¹³ + 3.01·10¹¹]`;
* **the clocks**: the clock at rest ticks within `10¹¹` of `n·2π·10¹¹`; the moving one within
  `1.6·10¹¹` of `2πn/R`, its splitting `R ∈ [6·10⁻¹², 6.01·10⁻¹²]`, three fifths of the rest
  splitting `10⁻¹¹`;
* **the records between the ticks**: the departure lies between tick `0` and tick `1` of each clock;
  the return between ticks `117` and `122` of the clock at rest and ticks `70` and `73` of the moving
  one;
* **the dilation, read off the records**: the moving clock counts between `69` and `73` ticks while
  the clock at rest counts between `116` and `122`; the ratio lies in `[69/122, 73/116]`, which
  contains `3/5 = √(1 − (4/5)²)` and excludes `1`;
* **the relative speed, read by the observer at rest**: the windows' centres `(2π − 1/5)·10¹³` apart
  over `116` to `122` of its ticks gives a speed in a bracket containing `4/5` and below `1`. -/
theorem dirac_two_observers {w : ℝ} (hw : 0 ≤ w) :
    let dep := twinDeparture (L := L) hL hw
    let ret := twinReturn (L := L) hL hw
    let a := fun (n : ℕ) (hn : n ≤ 130) => restTickBoth (L := L) hL n hn hw
    let b := fun (n : ℕ) (hn : n ≤ 80) => movingTickBoth (L := L) hL n hn hw
    let R := levelClockRate 3 (3 + 1 / 10 ^ 11)
      (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * 4))
    let T : ℝ := 2 * Real.pi * 10 ^ 11
    (ret.evolve = dep.evolve ∧ ret.prep = dep.prep
      ∧ (∀ n hn, (a n hn).evolve = dep.evolve ∧ (a n hn).prep = dep.prep)
      ∧ (∀ n hn, (b n hn).evolve = dep.evolve ∧ (b n hn).prep = dep.prep))
    ∧ (∀ t, (dep.evolve 0 t dep.prep).1.1.1 = restObserver (L := L) t
      ∧ (dep.evolve 0 t dep.prep).1.2.1 = movingObserver (L := L) t)
    ∧ (∀ (z : ℂ) (ΨA ΨB : (ZMod L × Fin 2) × Fin 2 → ℂ),
        relWeight z (1 / 10) ΨA ΨB = relWeight (star z) (1 / 10) ΨB ΨA)
    ∧ (dep.writeStart = 2 * 10 ^ 11 ∧ dep.writeEnd = 201 * 10 ^ 9
      ∧ ret.writeStart = (2 * Real.pi - 39 / 100) * (125 * 10 ^ 11) + 8 * 10 ^ 10
      ∧ ret.writeEnd = (2 * Real.pi - 11 / 50) * (125 * 10 ^ 11) + 301 * 10 ^ 9)
    ∧ (∀ n hn, (a n hn).writeStart = max 0 ((n : ℝ) * T - 10 ^ 11)
      ∧ (a n hn).writeEnd = (n : ℝ) * T + 10 ^ 11)
    ∧ (6 / 10 ^ 12 ≤ R ∧ R ≤ 601 / 10 ^ 14
      ∧ ∀ n hn, (b n hn).writeStart = max 0 (2 * Real.pi * (n : ℝ) / R - 16 * 10 ^ 10)
        ∧ (b n hn).writeEnd = 2 * Real.pi * (n : ℝ) / R + 16 * 10 ^ 10)
    ∧ ((a 0 (by norm_num)).writeEnd ≤ dep.writeStart ∧ dep.writeEnd ≤ (a 1 (by norm_num)).writeStart
      ∧ (a 117 (by norm_num)).writeEnd ≤ ret.writeStart
      ∧ ret.writeEnd ≤ (a 122 (by norm_num)).writeStart)
    ∧ ((b 0 (by norm_num)).writeEnd ≤ dep.writeStart ∧ dep.writeEnd ≤ (b 1 (by norm_num)).writeStart
      ∧ (b 70 (by norm_num)).writeEnd ≤ ret.writeStart
      ∧ ret.writeEnd ≤ (b 73 (by norm_num)).writeStart)
    ∧ ((70 - 1 : ℝ) / (122 - 0) ≤ 3 / 5 ∧ (3 / 5 : ℝ) ≤ (73 - 0) / (117 - 1)
      ∧ (73 - 0 : ℝ) / (117 - 1) < 1 ∧ (3 / 5 : ℝ) = Real.sqrt (1 - (4 / 5) ^ 2))
    ∧ ((2 * Real.pi - 1 / 5) * 10 ^ 13 / ((122 - 0) * T) ≤ 4 / 5
      ∧ (4 / 5 : ℝ) ≤ (2 * Real.pi - 1 / 5) * 10 ^ 13 / ((117 - 1) * T)
      ∧ (2 * Real.pi - 1 / 5) * 10 ^ 13 / ((117 - 1) * T) < 1) := by
  intro dep ret a b R T
  have hπ := Real.pi_pos
  have hπ1 : (314 / 100 : ℝ) < Real.pi := by
    have := Real.pi_gt_d2
    norm_num at this ⊢
    linarith
  have hπ2 := pi_lt_sixty_three_div_twenty
  have hT : 0 < T := by positivity
  obtain ⟨hR1, hR2⟩ := twin_moving_rate (L := L) hL
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR1
  have hA : ∀ n hn, (a n hn).writeStart = max 0 ((n : ℝ) * T - 10 ^ 11)
      ∧ (a n hn).writeEnd = (n : ℝ) * T + 10 ^ 11 := fun n hn => by
    have e : 2 * Real.pi * (n : ℝ) / (1 / 10 ^ 11) = n * T := by
      simp only [T]
      field_simp
    refine ⟨?_, ?_⟩
    · show max 0 (2 * Real.pi * n / levelClockRate 3 (3 + 1 / 10 ^ 11)
        (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * 0))
          - 10 ^ 11) = _
      rw [twin_rest_rate, e]
    · show 2 * Real.pi * n / levelClockRate 3 (3 + 1 / 10 ^ 11)
        (2 * scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) * Real.sin (2 * Real.pi * 10 ^ 13 / L * 0))
          + 10 ^ 11 = _
      rw [twin_rest_rate, e]
  have hB : ∀ n hn, (b n hn).writeStart = max 0 (2 * Real.pi * (n : ℝ) / R - 16 * 10 ^ 10)
      ∧ (b n hn).writeEnd = 2 * Real.pi * (n : ℝ) / R + 16 * 10 ^ 10 := fun _ _ => ⟨rfl, rfl⟩
  have hdep0 : dep.writeStart = 2 * 10 ^ 11 := rfl
  have hdep1 : dep.writeEnd = 201 * 10 ^ 9 := rfl
  have hret0 : ret.writeStart = (2 * Real.pi - 39 / 100) * (125 * 10 ^ 11) + 8 * 10 ^ 10 := rfl
  have hret1 : ret.writeEnd = (2 * Real.pi - 11 / 50) * (125 * 10 ^ 11) + 301 * 10 ^ 9 := rfl
  have hdivlo : ∀ k : ℝ, 0 ≤ k → 2 * Real.pi * k / R ≤ 2 * Real.pi * k / (6 / 10 ^ 12) :=
    fun k hk => div_le_div_of_nonneg_left (by positivity) (by norm_num) hR1
  have hdivhi : ∀ k : ℝ, 0 ≤ k → 2 * Real.pi * k / (601 / 10 ^ 14) ≤ 2 * Real.pi * k / R :=
    fun k hk => div_le_div_of_nonneg_left (by positivity) hR0 hR2
  refine ⟨⟨rfl, rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩⟩, fun t => ⟨?_, ?_⟩,
    fun z ΨA ΨB => relWeight_swap z (1 / 10) ΨA ΨB, ⟨rfl, rfl, rfl, rfl⟩, hA,
    ⟨hR1, hR2, hB⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨by norm_num, by norm_num, by norm_num, ?_⟩,
    ⟨?_, ?_, ?_⟩⟩
  · show deviceProp _ _ _ (t - 0) *ᵥ restObserver (L := L) 0 = _
    rw [sub_zero, restObserver, restObserver, deviceProp_devicePacket]
  · show deviceProp _ _ _ (t - 0) *ᵥ movingObserver (L := L) 0 = _
    rw [sub_zero, movingObserver, movingObserver, deviceProp_devicePacket]
  · rw [(hA 0 _).2, hdep0]
    norm_num
  · rw [(hA 1 _).1, hdep1]
    refine le_max_of_le_right ?_
    simp only [T]
    push_cast
    nlinarith
  · rw [(hA 117 _).2, hret0]
    simp only [T]
    push_cast
    nlinarith
  · rw [(hA 122 _).1, hret1]
    refine le_max_of_le_right ?_
    simp only [T]
    push_cast
    nlinarith
  · rw [(hB 0 _).2, hdep0]
    norm_num
  · rw [(hB 1 _).1, hdep1]
    refine le_max_of_le_right ?_
    have h := hdivhi 1 zero_le_one
    rw [show 2 * Real.pi * 1 / (601 / 10 ^ 14) = Real.pi * (2 * 10 ^ 14 / 601) by ring] at h
    push_cast
    nlinarith
  · rw [(hB 70 _).2, hret0]
    have h := hdivlo 70 (by norm_num)
    rw [show 2 * Real.pi * 70 / (6 / 10 ^ 12) = Real.pi * (140 * 10 ^ 12 / 6) by ring] at h
    push_cast
    nlinarith
  · rw [(hB 73 _).1, hret1]
    refine le_max_of_le_right ?_
    have h := hdivhi 73 (by norm_num)
    rw [show 2 * Real.pi * 73 / (601 / 10 ^ 14) = Real.pi * (146 * 10 ^ 14 / 601) by ring] at h
    push_cast
    nlinarith
  · rw [show (1 : ℝ) - (4 / 5) ^ 2 = (3 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  · simp only [T]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · simp only [T]
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  · simp only [T]
    rw [div_lt_one (by positivity)]
    nlinarith

end Twin

end CSD.RecordLayer

end
