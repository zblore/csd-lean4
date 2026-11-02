/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracWorldline

/-!
# The lattice's preferred-frame corrections on the radar arena

**Category:** 7-SigmaLayer (the record layer). BACKLOG #279 (residue of ~~#259~~).

~~#259~~ read the moving clock's rate as the Lorentz dilation `√(1 − β²)` to `2.5·10⁻⁴`. The Dirac
chain is a lattice with a rest frame, and three bounds in the corpus say how it departs from
Lorentz: the moving clock's dilation defect (~~#249~~'s `lattice_dilation_defect`), the speed cap
below `c` of every massive species (~~#246~~'s `maxGroupVel`), and the chain's guaranteed cone
(~~#258~~'s `chainConeVel`). Here all three are evaluated at the radar arena's parameters — a ring
of physical length `2π·10¹³` with `L ≥ 10¹⁹` sites, spacing `a = 2π·10¹³/L ≤ 2π·10⁻⁶`, hop `J =
1/(2a)` (`c = 2Ja = 1`), rest energy `μ = 3` — in physical units.

## The arena

* `arenaSpacing` (`a`), `arenaSpacing_pos`, `arenaSpacing_le` (`a ≤ 2π·10⁻⁶`),
  `two_mul_scaledHop_mul` (`2Ja = 1`: `c = 1`).

## The three corrections

* `latticeDefect` (the difference of the squared dilation factors read from the group velocity and
  from the relativistic velocity, at lattice momentum `k`), ★ `latticeDefect_le_sq` — **between `0`
  and `k²`**;
* ★★ `defect_arena` — **at `B`'s momentum `9/4` at most `2.1·10⁻¹⁰`, at the messenger's `4` at most
  `6.4·10⁻¹⁰`** — more than five orders of magnitude below the records' rate resolution `2.5·10⁻⁴`;
* ★★ `speed_cap_arena` — **the fastest packet of the rest energy `3` moves between `1 − 3a` and
  `1`**, the deficit below `c` at most `1.9·10⁻⁵`;
* ★ `cone_arena` — **the chain's guaranteed cone is `4e(1 + 3a)`**, below `11 c`.

## The capstone

* ★★★ `dirac_lattice_corrections` — the three, with the comparison to the records' resolution.

## The finding

**The clocks' dilation is Lorentz's to far better than the records can tell**: the defect is
`≤ 6.4·10⁻¹⁰` against a rate resolution of `2.5·10⁻⁴`. The messengers' speed cap is `1.9·10⁻⁵`
below `c` (not compared here with a record-level speed resolution). The cone, `≈ 10.9 c`, is the
exponential series' bound for every state, not a propagation speed.

## Honest scope

⚠️ **Bounds at the arena's parameters**, not a limit statement; the defect is the squared-factor
difference of ~~#249~~ at the packets' central momenta, not over their momentum windows.

⚠️ **The cone is generous** (~~#258~~): it bounds what any state can do, not what the packets do.

References: `specs/BACKLOG.md` #279, #259, #249, #246, #258, #274, #277, #278;
`CV/DiracClockChain.lean` (`lattice_dilation_defect`, `vRel`); `RecordLayer/SignalCone.lean`
(`maxGroupVel`, `maxGroupVel_lt`, `abs_two_mul_sub_le_maxGroupVel`); `RecordLayer/DiracTiming.lean`
(`chainConeVel`); `CV/DiracContinuum.lean` (`scaledHop`); `RecordLayer/DiracWorldline.lean`
(`clock_rate_lorentz`, `dirac_lorentz_worldline`).
-/

@[expose] public section

open CSD.CV

namespace CSD.RecordLayer

/-! ### The arena -/

/-- **The radar arena's lattice spacing**: a ring of physical length `2π·10¹³` with `L` sites. -/
noncomputable def arenaSpacing (L : ℕ) : ℝ := 2 * Real.pi * 10 ^ 13 / L

theorem arenaSpacing_pos {L : ℕ} (hL : 10 ^ 19 ≤ L) : 0 < arenaSpacing L := by
  have : (0 : ℝ) < L := by
    have : (10 ^ 19 : ℝ) ≤ L := by exact_mod_cast hL
    linarith [show (0 : ℝ) < 10 ^ 19 by norm_num]
  unfold arenaSpacing
  positivity

/-- `a ≤ 2π·10⁻⁶`. -/
theorem arenaSpacing_le {L : ℕ} (hL : 10 ^ 19 ≤ L) :
    arenaSpacing L ≤ 2 * Real.pi / 10 ^ 6 := by
  have hLr : (10 ^ 19 : ℝ) ≤ L := by exact_mod_cast hL
  unfold arenaSpacing
  rw [div_le_div_iff₀ (by linarith [show (0 : ℝ) < 10 ^ 19 by norm_num]) (by norm_num)]
  nlinarith [Real.pi_pos]

/-- **`c = 2Ja = 1`.** -/
theorem two_mul_scaledHop_mul {a : ℝ} (ha : 0 < a) : 2 * scaledHop 1 a * a = 1 := by
  unfold scaledHop
  field_simp

/-! ### The three corrections -/

/-- **The dilation defect at lattice momentum `k`**: the squared dilation factor read from the group
velocity minus the one read from the relativistic velocity. -/
noncomputable def latticeDefect (J μ k : ℝ) : ℝ :=
  (1 - (vRel (2 * J) μ (2 * J * Real.sin k) * Real.cos k / (2 * J)) ^ 2)
    - (1 - (vRel (2 * J) μ (2 * J * Real.sin k) / (2 * J)) ^ 2)

/-- ★ **The defect lies between `0` and `k²`.** -/
theorem latticeDefect_le_sq {J μ : ℝ} (hJ : J ≠ 0) (hμ : 0 < μ) (k : ℝ) :
    0 ≤ latticeDefect J μ k ∧ latticeDefect J μ k ≤ k ^ 2 := by
  obtain ⟨h1, h2⟩ := lattice_dilation_defect hJ hμ k
  have hs : Real.sin k ^ 2 ≤ k ^ 2 := by
    have := Real.abs_sin_le_abs (x := k)
    nlinarith [abs_nonneg (Real.sin k), sq_abs (Real.sin k), sq_abs k]
  unfold latticeDefect
  rw [h1]
  exact ⟨by positivity, h2.trans hs⟩

/-- ★★ **The defect at the arena's momenta**: at most `2.1·10⁻¹⁰` at `B`'s momentum `9/4` and
`6.4·10⁻¹⁰` at the messenger's `4`. -/
theorem defect_arena {L : ℕ} (hL : 10 ^ 19 ≤ L) :
    let a := arenaSpacing L
    0 ≤ latticeDefect (scaledHop 1 a) 3 (a * (9 / 4))
    ∧ latticeDefect (scaledHop 1 a) 3 (a * (9 / 4)) ≤ 21 / 10 ^ 11
    ∧ 0 ≤ latticeDefect (scaledHop 1 a) 3 (a * 4)
    ∧ latticeDefect (scaledHop 1 a) 3 (a * 4) ≤ 64 / 10 ^ 11 := by
  intro a
  have ha := arenaSpacing_pos hL
  have ha2 := arenaSpacing_le hL
  have hJ : scaledHop 1 a ≠ 0 := by
    unfold scaledHop
    positivity
  have hπ : Real.pi < 315 / 100 := by linarith [Real.pi_lt_d2]
  have ha3 : a ≤ 63 / 10 ^ 7 := by
    calc a ≤ 2 * Real.pi / 10 ^ 6 := ha2
      _ ≤ 63 / 10 ^ 7 := by rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
  obtain ⟨hB0, hB1⟩ := latticeDefect_le_sq hJ (by norm_num : (0 : ℝ) < 3) (a * (9 / 4))
  obtain ⟨hM0, hM1⟩ := latticeDefect_le_sq hJ (by norm_num : (0 : ℝ) < 3) (a * 4)
  refine ⟨hB0, hB1.trans ?_, hM0, hM1.trans ?_⟩
  · nlinarith [mul_pos ha ha]
  · nlinarith [mul_pos ha ha]

/-- ★★ **The speed cap at the arena**: the fastest packet of rest energy `3`, in physical units,
moves between `1 − 3a` and `1`, and `3a ≤ 1.9·10⁻⁵`. -/
theorem speed_cap_arena {L : ℕ} (hL : 10 ^ 19 ≤ L) :
    let a := arenaSpacing L
    1 - 3 * a ≤ a * maxGroupVel (scaledHop 1 a) 3 ∧ a * maxGroupVel (scaledHop 1 a) 3 < 1
    ∧ 3 * a ≤ 19 / 10 ^ 6 := by
  intro a
  have ha := arenaSpacing_pos hL
  have ha2 := arenaSpacing_le hL
  have hc := two_mul_scaledHop_mul ha
  have hJ : 0 < scaledHop 1 a := by
    unfold scaledHop
    positivity
  have habs : |2 * scaledHop 1 a| = 2 * scaledHop 1 a := abs_of_pos (by positivity)
  have hlo := abs_two_mul_sub_le_maxGroupVel (scaledHop 1 a) 3
  have hhi := maxGroupVel_lt hJ.ne' (by norm_num : (0 : ℝ) < 3)
  rw [habs] at hlo hhi
  have hπ : Real.pi < 315 / 100 := by linarith [Real.pi_lt_d2]
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  calc 3 * a ≤ 3 * (2 * Real.pi / 10 ^ 6) := by linarith
    _ ≤ 19 / 10 ^ 6 := by nlinarith

/-- ★ **The chain's guaranteed cone at the arena**: `4e(1 + 3a)` in physical units, below `11`. -/
theorem cone_arena {L : ℕ} (hL : 10 ^ 19 ≤ L) :
    let a := arenaSpacing L
    a * chainConeVel (scaledHop 1 a) 3 = 4 * Real.exp 1 * (1 + 3 * a)
    ∧ a * chainConeVel (scaledHop 1 a) 3 < 11 := by
  intro a
  have ha := arenaSpacing_pos hL
  have ha2 := arenaSpacing_le hL
  have hc := two_mul_scaledHop_mul ha
  have hJ : 0 < scaledHop 1 a := by
    unfold scaledHop
    positivity
  have he := Real.exp_one_lt_d9
  have hπ : Real.pi < 315 / 100 := by linarith [Real.pi_lt_d2]
  have heq : a * chainConeVel (scaledHop 1 a) 3 = 4 * Real.exp 1 * (1 + 3 * a) := by
    unfold chainConeVel
    rw [abs_of_pos hJ, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    linear_combination (4 * Real.exp 1) * hc
  refine ⟨heq, ?_⟩
  rw [heq]
  have ha3 : a ≤ 63 / 10 ^ 7 := by
    calc a ≤ 2 * Real.pi / 10 ^ 6 := ha2
      _ ≤ 63 / 10 ^ 7 := by rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
  nlinarith [Real.exp_pos 1]

/-! ### The capstone -/

/-- ★★★ **The lattice's corrections where the records look (#279).** At the radar arena's
parameters (`L ≥ 10¹⁹` sites on a ring of length `2π·10¹³`, `c = 2Ja = 1`, rest energy `3`):

* the moving clock's dilation defect is at most `2.1·10⁻¹⁰` at `B`'s momentum and `6.4·10⁻¹⁰` at the
  messenger's — below the records' rate resolution `2.5·10⁻⁴`;
* the fastest packet moves between `1 − 3a` and `1`, the deficit `3a ≤ 1.9·10⁻⁵`;
* the chain's guaranteed cone is `4e(1 + 3a) < 11`. -/
theorem dirac_lattice_corrections {L : ℕ} (hL : 10 ^ 19 ≤ L) :
    let a := arenaSpacing L
    (2 * scaledHop 1 a * a = 1)
    ∧ (0 ≤ latticeDefect (scaledHop 1 a) 3 (a * (9 / 4))
      ∧ latticeDefect (scaledHop 1 a) 3 (a * (9 / 4)) ≤ 21 / 10 ^ 11
      ∧ 0 ≤ latticeDefect (scaledHop 1 a) 3 (a * 4)
      ∧ latticeDefect (scaledHop 1 a) 3 (a * 4) ≤ 64 / 10 ^ 11)
    ∧ (64 / 10 ^ 11 : ℝ) < 25 / 10 ^ 5
    ∧ (1 - 3 * a ≤ a * maxGroupVel (scaledHop 1 a) 3 ∧ a * maxGroupVel (scaledHop 1 a) 3 < 1
      ∧ 3 * a ≤ 19 / 10 ^ 6)
    ∧ (a * chainConeVel (scaledHop 1 a) 3 = 4 * Real.exp 1 * (1 + 3 * a)
      ∧ a * chainConeVel (scaledHop 1 a) 3 < 11) :=
  ⟨two_mul_scaledHop_mul (arenaSpacing_pos hL), defect_arena hL, by norm_num, speed_cap_arena hL,
    cone_arena hL⟩

end CSD.RecordLayer

end
