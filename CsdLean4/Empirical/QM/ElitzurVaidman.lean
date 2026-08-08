/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.Metrology.Ramsey

/-!
# Empirical/QM/ElitzurVaidman: the bomb tester (interaction-free measurement)

The **Elitzur–Vaidman bomb tester**: a balanced Mach–Zehnder interferometer (two `50:50` beam
splitters `= H`) is tuned so a single photon *always* exits the bright port and *never* the dark
port — perfect destructive interference at the dark port. Placing a **live bomb** (a which-path
absorber that detonates if the photon takes that arm) in one arm destroys the coherence: now the
dark port fires with probability `1/4`. A dark-port click therefore certifies a live bomb **without
the photon ever hitting it** — an *interaction-free measurement*.

* `bomb_absent_dark_zero` — no bomb: dark-port Born probability `= 0` (full interference, `H·H = I`).
* `bomb_safe_prob` — the photon reaches the second beam splitter without detonating the bomb, `= 1/2`.
* `bomb_dark_given_safe` — conditioned on survival, the dark port fires with probability `1/2`.
* `bomb_present_dark` — live bomb: total dark-port probability `= 1/2 · 1/2 = 1/4`.
* `interaction_free` — `0 < 1/4`: the dark port fires **only** with a live bomb, so a dark click is a
  bomb certificate with no interaction (the surviving photon took the empty arm).

**Experimental verification:** Kwiat, Weinfurter, Herzog, Zeilinger, Kasevich 1995.
**CSD note:** the bomb is a which-path de-isolation that would form a record (detonation) on the
occupied arm; the dark-port click is the ontic signature that the record-forming interaction was
*available* on the other arm — information without interaction.

## References
`Empirical/CSD/MachZehnderVolume.lean` (the interferometer as `H·D(φ)·H`);
`Empirical/Metrology/Ramsey.lean` (the beam-splitter / `√2` amplitude machinery).
-/

@[expose] public section

namespace CSD.Empirical.QM.ElitzurVaidman

/-- `√2` as a complex scalar. -/
noncomputable def rt2 : ℂ := (Real.sqrt 2 : ℂ)

lemma norm_rt2 : ‖rt2‖ = Real.sqrt 2 := by
  rw [rt2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]

/-- `‖x/√2‖² = ‖x‖²/2`. -/
lemma norm_div_rt2_sq (x : ℂ) : ‖x / rt2‖ ^ 2 = ‖x‖ ^ 2 / 2 := by
  rw [norm_div, div_pow, norm_rt2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Input path states `|0⟩`, `|1⟩` (the two interferometer arms). -/
def ket0 : Fin 2 → ℂ := ![1, 0]
def ket1 : Fin 2 → ℂ := ![0, 1]

/-- The `50:50` beam splitter (Hadamard): `H(v) = ((v₀+v₁)/√2, (v₀−v₁)/√2)`. -/
noncomputable def bs (v : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![(v 0 + v 1) / rt2, (v 0 - v 1) / rt2]

/-- Born probability of the **dark port** (component `1`) of an amplitude vector. -/
noncomputable def darkProb (v : Fin 2 → ℂ) : ℝ := ‖v 1‖ ^ 2

/-- **No bomb: the dark port never fires.** The balanced interferometer is `H·H = I`, so the photon
returns to `|0⟩` and the dark-port probability is `0` — perfect destructive interference. -/
theorem bomb_absent_dark_zero : darkProb (bs (bs ket0)) = 0 := by
  have h : (bs (bs ket0)) 1 = 0 := by
    simp only [bs, ket0, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  simp [darkProb, h]

/-- **The photon survives** (does not detonate the bomb) with probability `1/2`: after the first beam
splitter `H|0⟩ = (|0⟩+|1⟩)/√2`, the amplitude on the empty (non-bomb) arm has weight `1/2`. -/
theorem bomb_safe_prob : darkProb (bs ket0) = 1 / 2 := by
  simp only [darkProb, bs, ket0, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [sub_zero, norm_div_rt2_sq, norm_one]; norm_num

/-- **Conditioned on survival**, the second beam splitter sends the photon to the dark port with
probability `1/2` (`H|1⟩ = (|0⟩−|1⟩)/√2`). -/
theorem bomb_dark_given_safe : darkProb (bs ket1) = 1 / 2 := by
  simp only [darkProb, bs, ket1, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [zero_sub, norm_div_rt2_sq, norm_neg, norm_one]; norm_num

/-- Total dark-port probability with a **live bomb**: survive (`1/2`) then reach the dark port
(`1/2`). -/
noncomputable def pDarkLive : ℝ := darkProb (bs ket0) * darkProb (bs ket1)

/-- **Live bomb: the dark port fires with probability `1/4`.** In contrast to the no-bomb case
(`0`), so a dark-port click certifies a live bomb. -/
theorem bomb_present_dark : pDarkLive = 1 / 4 := by
  rw [pDarkLive, bomb_safe_prob, bomb_dark_given_safe]; norm_num

/-- **Interaction-free measurement:** the dark port fires with probability `0` when there is no bomb
but `1/4` when there is — so a dark-port click detects a live bomb without the photon interacting
with it. -/
theorem interaction_free : darkProb (bs (bs ket0)) < pDarkLive := by
  rw [bomb_absent_dark_zero, bomb_present_dark]; norm_num

end CSD.Empirical.QM.ElitzurVaidman
