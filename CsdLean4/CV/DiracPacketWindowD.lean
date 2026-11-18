/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.DiracPacketLimitD

/-!
# The drift of a flat packet from the width of its window

**Category:** 3-Local (CV). BACKLOG #296, sixth part (Task 8 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream S; milestone
M7, obligation UO-17; remainder (b) of the row, closed here).

`CV/DiracPacketLimitD.lean` bounds a flat packet's weight outside its moving box with the
energy-step errors `Sm i` as a hypothesis. Here they are computed from the width of the
window, and the drift rate is put in physical units.

* `windowStepErrD`, `stepErrD_le_windowStepErrD`, `windowStepErrD_nonneg`;
* ★★ `two_pi_div_mul_windowStepErrD_scaled` (**the drift rate in physical units**: under
  `J = c L / (2 ℓ)` and half-widths `(ℓ/L) Δ_j`, the rate `(2π/L) · windowStepErrD_i` is
  `(2π c / ℓ)(ℓ Δ_i + 2π) / L + (2π c² / (ℓ² μ))(ℓ Δ_i + ℓ Σ_j Δ_j + 4π)`: a term of order
  `1/L` and a term with no `L` in it);
* ★★ `tendsto_two_pi_div_mul_windowStepErrD` (2026-11-19: along the family of lattices the
  rate tends to `(2π c² / (ℓ² μ))(ℓ Δ_i + ℓ Σ_j Δ_j + 4π)`);
* ★★★ `regionWeightD_flatPacket_compl_movedBoxD_le_window` (**the bound from the width of
  the window alone**: weight outside the moving box at most
  `Σ_i (1/N_i + (2π |J| / (L μ))² + |t| (2π/L) windowStepErrD_i) / (1 − γ_i)`).

## Honest scope

⚠️ **Free of `L`, not small in `L`.** With `alignDefect_scaled` the three terms are `1/N_i`,
`(π c / (ℓ μ))²`, and `|t|` times a rate that tends to
`(2π c² / (ℓ² μ))(ℓ Δ_i + ℓ Σ_j Δ_j + 4π)`. None of them shrinks as the lattice is refined;
they are small for many modes, a torus of many Compton wavelengths, and short times or a
narrow window.

⚠️ **`N_i` and `Δ_i` are tied.** `N_i` consecutive momenta spaced `2π/ℓ` have half-width about
`π N_i / ℓ`, so more modes mean a wider window: `1/N_i` and the drift pull against each
other, as on the ring. No choice of `N_i` is optimised here.

⚠️ **The window's half-widths `w j` are a hypothesis on the box** (`hw`). The limit
`tendsto_two_pi_div_mul_windowStepErrD` is of the rate alone; no limit is taken of the
packet or of the bound as a whole.

⚠️ **Not sharp, `μ > 0`, no record read**, as `CV/DiracPacketLimitD.lean`.

References: `specs/BACKLOG.md` #296; `specs/unified-record-spacetime-plan.md` (UO-17, UD-221,
UD-222); `CV/DiracPacketLimitD.lean` (`regionWeightD_flatPacket_compl_movedBoxD_le`,
`alignDefect_scaled`, `boxWindowD`); `CV/DiracPacketD.lean` (`stepErrD`);
`CV/DiracPacketLimit.lean` (`limitErr`, `dirac_packet_limit`); `specs/future-work.md`.
-/

@[expose] public section

open Complex Matrix

noncomputable section

namespace CSD.CV

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [DecidableEq S]
  {L : ℕ} [NeZero L]

/-- **The energy-step error on a window of half-widths `w`**: `stepErrD` with every
`|k_j − k₀_j|` replaced by `w j`. -/
def windowStepErrD (J μ : ℝ) (w : ι → ℝ) (i : ι) (h : ℝ) : ℝ :=
  2 * |J| * (w i + h) + 4 * J ^ 2 / μ * ((w i + h) + (∑ j, w j + h))

omit [DecidableEq ι] in
theorem stepErrD_le_windowStepErrD {J μ : ℝ} (hμ : 0 < μ) {k k₀ w : ι → ℝ}
    (hw : ∀ j, |k j - k₀ j| ≤ w j) (i : ι) (h : ℝ) :
    stepErrD J μ k k₀ i h ≤ windowStepErrD J μ w i h := by
  have h1 := hw i
  have h2 : ∑ j, |k j - k₀ j| ≤ ∑ j, w j := Finset.sum_le_sum fun j _ => hw j
  have c1 : 0 ≤ 2 * |J| := by positivity
  have c2 : 0 ≤ 4 * J ^ 2 / μ := by positivity
  unfold stepErrD windowStepErrD
  linarith only [mul_le_mul_of_nonneg_left (add_le_add_right h1 h) c1,
    mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add_right h1 h) (add_le_add_right h2 h)) c2]

omit [DecidableEq ι] in
theorem windowStepErrD_nonneg {J μ : ℝ} (hμ : 0 < μ) {w : ι → ℝ} (hw0 : ∀ j, 0 ≤ w j) (i : ι)
    {h : ℝ} (hh : 0 ≤ h) : 0 ≤ windowStepErrD J μ w i h := by
  have hs : 0 ≤ ∑ j, w j := Finset.sum_nonneg fun j _ => hw0 j
  have a1 : 0 ≤ w i + h := add_nonneg (hw0 i) hh
  have a2 : 0 ≤ ∑ j, w j + h := add_nonneg hs hh
  exact add_nonneg (mul_nonneg (by positivity) a1)
    (mul_nonneg (by positivity) (add_nonneg a1 a2))

omit [DecidableEq ι] [NeZero L] in
/-- ★★ **The drift rate in physical units.** Under `J = c L / (2 ℓ)` and a window of
half-widths `w j = (ℓ / L) Δ j` (momenta within `Δ j` of the centre in units of `1/ℓ`), the
rate `(2π/L) · windowStepErrD` is a term of order `1/L` plus a term with no `L` in it. -/
theorem two_pi_div_mul_windowStepErrD_scaled {c ℓ μ : ℝ} (hc : 0 ≤ c) (hℓ : 0 < ℓ)
    (hμ : 0 < μ) (hL : 0 < L) (Δ : ι → ℝ) (i : ι) :
    2 * Real.pi / L
        * windowStepErrD (c * L / (2 * ℓ)) μ (fun j => ℓ / L * Δ j) i (2 * Real.pi / L)
      = 2 * Real.pi * c / ℓ * (ℓ * Δ i + 2 * Real.pi) / L
        + 2 * Real.pi * c ^ 2 / (ℓ ^ 2 * μ) * (ℓ * Δ i + ℓ * ∑ j, Δ j + 4 * Real.pi) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  unfold windowStepErrD
  rw [abs_of_nonneg (by positivity), ← Finset.mul_sum]
  field_simp
  ring

omit [DecidableEq ι] [NeZero L] in
/-- ★★ **The drift rate has a limit along the family of lattices**: under `J = c L / (2 ℓ)`
and half-widths `(ℓ / L) Δ j`, as the number of sites `L` grows the rate
`(2π/L) · windowStepErrD` tends to `(2π c² / (ℓ² μ)) (ℓ Δ_i + ℓ Σ_j Δ_j + 4π)`. -/
theorem tendsto_two_pi_div_mul_windowStepErrD {c ℓ μ : ℝ} (hc : 0 ≤ c) (hℓ : 0 < ℓ)
    (hμ : 0 < μ) (Δ : ι → ℝ) (i : ι) :
    Filter.Tendsto
      (fun L : ℕ => 2 * Real.pi / L
        * windowStepErrD (c * L / (2 * ℓ)) μ (fun j => ℓ / L * Δ j) i (2 * Real.pi / L))
      Filter.atTop
      (nhds (2 * Real.pi * c ^ 2 / (ℓ ^ 2 * μ) * (ℓ * Δ i + ℓ * ∑ j, Δ j + 4 * Real.pi))) := by
  have h1 : Filter.Tendsto
      (fun L : ℕ => 2 * Real.pi * c / ℓ * (ℓ * Δ i + 2 * Real.pi) / (L : ℝ)
        + 2 * Real.pi * c ^ 2 / (ℓ ^ 2 * μ) * (ℓ * Δ i + ℓ * ∑ j, Δ j + 4 * Real.pi))
      Filter.atTop
      (nhds (0 + 2 * Real.pi * c ^ 2 / (ℓ ^ 2 * μ) * (ℓ * Δ i + ℓ * ∑ j, Δ j + 4 * Real.pi))) :=
    (tendsto_const_div_atTop_nhds_zero_nat _).add tendsto_const_nhds
  rw [zero_add] at h1
  refine h1.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with L hL
  exact (two_pi_div_mul_windowStepErrD_scaled hc hℓ hμ hL Δ i).symm

variable {α : ι → Matrix S S ℂ} {β : Matrix S S ℂ}

/-- ★★★ **A flat packet on a box of momenta stays in the box that moves with it, from the
width of its window alone.** As `regionWeightD_flatPacket_compl_movedBoxD_le`, with the
energy-step errors computed: if every momentum of the box is within `w j` of `k₀ j` on each
axis, the weight outside the moving box at the time `t` is at most

  `Σ_i (1/N_i + (2π |J| / (L μ))² + |t| (2π/L) windowStepErrD_i) / (1 − γ_i)`. -/
theorem regionWeightD_flatPacket_compl_movedBoxD_le_window (h : IsCliffordFamily α β)
    {e₀ : S → ℂ} (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1) {J μ : ℝ} (hμ : 0 < μ)
    (lo : ι → ℤ) {N : ι → ℕ} (hN : ∀ j, 0 < N j) (hNL : ∀ j, N j < L) (k₀ : ι → ℝ)
    {w : ι → ℝ} (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ m ∈ boxWindowD lo N, ∀ j, |angleZD L m j - k₀ j| ≤ w j) (t : ℝ)
    {γ : ι → ℝ} (hγ : ∀ i, γ i < 1) :
    regionWeightD (packetD (L := L) α β J μ e₀ (boxWindowD lo N)
        (unitAmpD L J μ (flatAmpD lo N)) t) (movedBoxD L J μ k₀ (fun _ => 1) γ t)ᶜ
      ≤ ∑ i, (1 / N i + alignDefect L J μ
          + |t| * (2 * Real.pi / L * windowStepErrD J μ w i (2 * Real.pi / L))) / (1 - γ i) :=
  regionWeightD_flatPacket_compl_movedBoxD_le (L := L) (J := J) h he hn hμ lo hN hNL k₀
    (fun i => windowStepErrD_nonneg hμ hw0 i (by positivity))
    (fun i m hm => stepErrD_le_windowStepErrD hμ (hw m hm) i _) t hγ

end CSD.CV

end
