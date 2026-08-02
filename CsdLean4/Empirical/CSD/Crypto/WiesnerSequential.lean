/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.Crypto.WiesnerProtocol
public import CsdLean4.Empirical.CSD.Crypto.B92Sequential

/-!
# Empirical/CSD/Crypto: Wiesner money — the measure-resend counterfeit, dynamically

**Category:** CSD bridge (dynamical). An instantiation of the `BB84Sequential` engine on the
Wiesner mint/verify round — recorded as such: the counterfeit round is a genuine *sequential*
measurement (the forger's measurement collapses the note, the bank then verifies), and that is
exactly the calibrated-swap composition.

## The round

The mint (`Empirical/QM/Crypto/WiesnerProtocol.lean`) encodes a bit in one of two conjugate
carriers: `mint false = |0⟩`, `mint true = |+⟩` — **the same states** as the BB84/B92 layer
(`mint_false_eq`/`mint_true_eq` are `rfl`). Honest verification measures in the mint basis and
accepts with certainty. A counterfeiter who does not know the basis must measure to copy — and
the measurement is a de-isolation that collapses the note:

* `wiesner_honest_x_pass` / `wiesner_honest_z_pass` — honest verification accepts with
  probability `1`, as basin measures: the pass basin is *full* measure for the untouched note
  (`wiesner_rate_eq_verifyProb` ties the X-side rate to the QM module's `verifyProb`).
* ★ `wiesner_forge_x_pass_half` / `wiesner_forge_x_caught_half` — the forger Z-measures a `|+⟩`
  note (calibrated-swap dynamics) and resends; the bank's pass and reject basins each have
  probability `½`, **whatever the forger recorded**. The collapse that catches the counterfeit
  is a pushforward theorem.
* ★ `wiesner_forge_z_invisible` — on a matching-basis note the forger is exactly repeatability:
  the bank's pass basin keeps probability `1`. Measuring in the right basis copies for free —
  which is why the mint's *secret basis choice* is the entire security.
* `wiesner_forge_pass_avg` — averaging the two dynamical values over the mint's fair basis
  coin: the measure-resend counterfeit passes per-position verification with probability
  `¾ = ½·1 + ½·½` — the per-qubit value of the `(3/4)ⁿ` counterfeiting bound.

## ⚠️ Honest scope

Per-position analysis of the **Z-measure-resend** attack; the mint's basis coin and the `¾`
average are classical bookkeeping. That `¾` is also the *optimal* simple-counterfeit value
(Molina–Vidick–Watrous 2012) is **not** proved here — only that measure-resend attains it. The
unforgeability side (forgery ⟹ cloning) stays `wiesner_forge_impossible` / no-cloning on the QM
side. Inherits the calibrated-swap witness's scope notes.

## References

`Empirical/QM/Crypto/WiesnerProtocol.lean` (`mint`, `verifyProb`, `wiesner_verify_honest`,
`wiesner_forge_impossible`); `Empirical/QM/Crypto/QuantumMoney.lean` (the states);
`Empirical/CSD/Crypto/BB84Sequential.lean` (the engine); `Empirical/CSD/Crypto/B92Sequential.lean`
(`xContext_rate_ketPlus_plus`); Wiesner 1983; Molina–Vidick–Watrous 2012 (optimality, out of
scope); `specs/BACKLOG.md`.
-/

@[expose] public section

open MeasureTheory

namespace CSD.Empirical.CSDBridge.WiesnerSequential

open CSD.RecordLayer
open CSD.Empirical.BB84
open CSD.Empirical.QM.Wiesner
open CSD.Empirical.CSDBridge.SequentialMeasurement
open CSD.Empirical.CSDBridge.BB84Sequential
open CSD.Empirical.CSDBridge.B92Sequential

/-! ### The mint's carriers are the BB84/B92 states -/

lemma mint_false_eq : mint false = ket0 := rfl

lemma mint_true_eq : mint true = ketPlus := rfl

/-! ### Honest verification: the pass basin is full -/

/-- The X-side pass rate equals the QM module's `verifyProb` for an honest conjugate-basis
note — the ontic rate and the operational acceptance probability are the same number. -/
theorem wiesner_rate_eq_verifyProb :
    (basisContext xBasisON).rate (Projectivization.mk ℂ ketPlus ketPlus_ne_zero) 0
      = verifyProb (mint true) (mint true) := by
  rw [xContext_rate_ketPlus_plus, verifyProb_self_of_unit (mint_unit true)]

/-- **Honest verification is certain (conjugate-basis note).** The pass basin of an untouched
`|+⟩` note has full measure. -/
theorem wiesner_honest_x_pass :
    epistemicMeasure (Projectivization.mk ℂ ketPlus ketPlus_ne_zero)
        (globalBasin (basisContext xBasisON) 0) = 1 := by
  rw [globalBasin_prob, xContext_rate_ketPlus_plus, ENNReal.ofReal_one]

/-- **Honest verification is certain (computational-basis note).** -/
theorem wiesner_honest_z_pass (a : Fin 2) :
    epistemicMeasure (vertexPoint a) (globalBasin (momentContext 2) a) = 1 := by
  rw [globalBasin_prob, momentContext_rate, momentMap_vertex, if_pos rfl, ENNReal.ofReal_one]

/-! ### The counterfeit round -/

/-- **★ The counterfeit is caught half the time on conjugate-basis notes.** The forger
Z-measures a `|+⟩` note and resends; the bank's **pass** basin has probability `½` whatever the
forger recorded — the collapse is the calibrated-swap pushforward, not a posit. -/
theorem wiesner_forge_x_pass_half (i : Fin 2) :
    postEnsemble (readyPrep (Projectivization.mk ℂ ketPlus ketPlus_ne_zero)) i
        ((fun y : SwapArena (LF4.KSigma 2) 2 => y.1.1)
          ⁻¹' globalBasin (basisContext xBasisON) 0)
      = ENNReal.ofReal (1 / 2) :=
  bb84_wrong_basis_bob i 0

/-- …and the **reject** basin has the other `½`: the detection probability per conjugate
position. -/
theorem wiesner_forge_x_caught_half (i : Fin 2) :
    postEnsemble (readyPrep (Projectivization.mk ℂ ketPlus ketPlus_ne_zero)) i
        ((fun y : SwapArena (LF4.KSigma 2) 2 => y.1.1)
          ⁻¹' globalBasin (basisContext xBasisON) 1)
      = ENNReal.ofReal (1 / 2) :=
  bb84_wrong_basis_error i

/-- **★ On a matching-basis note the forger is invisible** — exactly repeatability: the bank's
pass basin keeps probability `1` after the forger's measure-and-resend. The mint's secret basis
choice is the entire security. -/
theorem wiesner_forge_z_invisible (a : Fin 2) :
    postEnsemble (readyPrep (vertexPoint a)) a
        ((fun y : SwapArena (LF4.KSigma 2) 2 => y.1.1)
          ⁻¹' globalBasin (momentContext 2) a)
      = 1 :=
  bb84_right_basis_faithful a

/-- **The `¾` per-position pass probability.** Averaging the two dynamical values
(`wiesner_forge_z_invisible`: `1`; `wiesner_forge_x_pass_half`: `½`) over the mint's fair basis
coin: the measure-resend counterfeit passes each position with probability `¾` — the per-qubit
value of the `(3/4)ⁿ` counterfeiting bound. Optimality of this value is out of scope (see the
module docstring). -/
theorem wiesner_forge_pass_avg : (1 / 2 : ℝ) * 1 + (1 / 2) * (1 / 2) = 3 / 4 := by
  norm_num

end CSD.Empirical.CSDBridge.WiesnerSequential
