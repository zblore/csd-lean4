/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.Crypto.BB84Sequential

/-!
# Empirical/CSD/Crypto: B92 — false conclusive clicks from a dynamical intercept

**Category:** CSD bridge (dynamical). An instantiation of the `BB84Sequential` engine on the
B92 unambiguous-discrimination round — recorded as such: the dynamical theorem is the same
calibrated-swap fact, re-read on B92's conclusive-click semantics.

## The round

B92 encodes bit `0` in `|0⟩` and bit `1` in `|+⟩`. Bob's conclusive detector for bit `0` is the
`|−⟩` click: honest carriers of bit `1` (`|+⟩`) can **never** trigger it (`⟨−|+⟩ = 0`,
`b92_unambiguous_zero` on the QM side). This module gives that unambiguity its ontic form and
then shows what an intercepting Eve does to it:

* `b92_honest_false_click_null` — the conclusive-bit-`0` basin is a **null set** for a `|+⟩`
  carrier: unambiguity is an ontic impossibility (a zero-width context-fixed basin), the same
  shape as the eraser's dark fringe. The Z-side counterpart `b92_honest_false_click_null_z`
  (a `|0⟩` carrier never triggers the conclusive-bit-`1` click) is `momentMap_vertex`.
* `b92_conclusive_basin_half` — the honest conclusive rate `½` (`b92_conclusive_rate_one`'s
  X-side counterpart) as a basin measure.
* ★ `b92_eve_false_click` — Eve Z-intercepts a `|+⟩` carrier (the calibrated-swap dynamics);
  Bob's conclusive-bit-`0` basin now has probability **`½`, whatever Eve recorded** — false
  conclusive clicks at rate `½` where honestly there is *nothing in `Σ`* to produce one.
* ★ `b92_eve_detectable` — the strict contrast: the intercept raises the false-click
  probability strictly above its honest value `0`. Eavesdropping announces itself in the
  conclusive statistics.

## ⚠️ Honest scope

One sifted round; the dynamical content is `bb84_wrong_basis_error` re-read (stated, not
hidden); Eve's basis choice stays classical bookkeeping. Inherits the calibrated-swap witness's
scope notes via `SequentialMeasurement.lean`. The unambiguous-discrimination *optimality*
(IDP bound) and full key-rate analysis remain on the QM side and the recorded QKD tranche.

## References

`Empirical/QM/Crypto/B92.lean` (`b92_unambiguous_zero`, `b92_conclusive_rate_one`,
`ketMinus_inner_ketPlus`, `ketPlus_unit`); `Empirical/CSD/Crypto/BB84Sequential.lean` (the
engine: `xBasisON`, `xContext_rate_vertex`, `bb84_wrong_basis_error`);
`SigmaLayer/RotatedContext.lean` (`basisContext_rate_mk`); Bennett 1992; `specs/BACKLOG.md`.
-/

@[expose] public section

open MeasureTheory

namespace CSD.Empirical.CSDBridge.B92Sequential

open CSD.RecordLayer
open CSD.Empirical.BB84
open CSD.Empirical.B92
open CSD.Empirical.CSDBridge.SequentialMeasurement
open CSD.Empirical.CSDBridge.BB84Sequential

/-! ### The honest X-context rates at the two carriers -/

lemma xContext_rate_ketPlus_plus :
    (basisContext xBasisON).rate (Projectivization.mk ℂ ketPlus ketPlus_ne_zero) 0 = 1 := by
  rw [basisContext_rate_mk xBasisON ketPlus ketPlus_ne_zero ketPlus_unit 0, xBasisON_apply]
  show ‖(inner ℂ ketPlus ketPlus : ℂ)‖ ^ 2 = 1
  rw [ketPlus_inner_self, norm_one, one_pow]

lemma xContext_rate_ketPlus_minus :
    (basisContext xBasisON).rate (Projectivization.mk ℂ ketPlus ketPlus_ne_zero) 1 = 0 := by
  rw [basisContext_rate_mk xBasisON ketPlus ketPlus_ne_zero ketPlus_unit 1, xBasisON_apply]
  show ‖(inner ℂ ketMinus ketPlus : ℂ)‖ ^ 2 = 0
  rw [ketMinus_inner_ketPlus, norm_zero]
  norm_num

/-! ### Unambiguity as a null basin -/

/-- **Unambiguity is an ontic impossibility.** For a `|+⟩` (bit-`1`) carrier, the
conclusive-bit-`0` basin (`|−⟩` click) is a **null set**: the context-fixed fibre arc has width
zero at that base point. No microstate of an honest bit-`1` carrier produces a false conclusive
click — the same shape as the eraser twin's dark fringe. -/
theorem b92_honest_false_click_null :
    epistemicMeasure (Projectivization.mk ℂ ketPlus ketPlus_ne_zero)
        (globalBasin (basisContext xBasisON) 1) = 0 := by
  rw [globalBasin_prob, xContext_rate_ketPlus_minus]
  simp

/-- The Z-side unambiguity: a `|0⟩` (bit-`0`) carrier never triggers the conclusive-bit-`1`
click (`|1⟩` in the computational basis) — `momentMap_vertex` at the off-index. -/
theorem b92_honest_false_click_null_z :
    epistemicMeasure (vertexPoint (0 : Fin 2)) (globalBasin (momentContext 2) 1) = 0 := by
  rw [globalBasin_prob, momentContext_rate, momentMap_vertex]
  simp

/-- The honest conclusive rate: a `|0⟩` carrier triggers the conclusive-bit-`0` click with
basin measure `½` — B92's `½` conclusive rate as a fibre-arc width. -/
theorem b92_conclusive_basin_half :
    epistemicMeasure (vertexPoint (0 : Fin 2)) (globalBasin (basisContext xBasisON) 1)
      = ENNReal.ofReal (1 / 2) := by
  rw [globalBasin_prob, xContext_rate_vertex 0 1]

/-! ### The intercepted round -/

/-- **★ Eve creates false conclusive clicks.** Alice sends `|+⟩` (bit `1`); Eve measures in the
computational basis and the calibrated-swap dynamics resends her eigenstate; Bob's
conclusive-bit-`0` basin now has probability `½` — **whatever Eve recorded**. The dynamical
fact is `bb84_wrong_basis_error`, re-read on B92's click semantics: where honestly no
microstate could produce this click, the intercept produces it half the time. -/
theorem b92_eve_false_click (i : Fin 2) :
    postEnsemble (readyPrep (Projectivization.mk ℂ ketPlus ketPlus_ne_zero)) i
        ((fun y : SwapArena (LF4.KSigma 2) 2 => y.1.1)
          ⁻¹' globalBasin (basisContext xBasisON) 1)
      = ENNReal.ofReal (1 / 2) :=
  bb84_wrong_basis_error i

/-- **★ The intercept is detectable in the conclusive statistics**: for every Eve outcome, the
false-click probability is strictly above its honest value (zero). -/
theorem b92_eve_detectable (i : Fin 2) :
    epistemicMeasure (Projectivization.mk ℂ ketPlus ketPlus_ne_zero)
        (globalBasin (basisContext xBasisON) 1)
      < postEnsemble (readyPrep (Projectivization.mk ℂ ketPlus ketPlus_ne_zero)) i
          ((fun y : SwapArena (LF4.KSigma 2) 2 => y.1.1)
            ⁻¹' globalBasin (basisContext xBasisON) 1) := by
  rw [b92_honest_false_click_null, b92_eve_false_click i]
  exact ENNReal.ofReal_pos.mpr (by norm_num)

end CSD.Empirical.CSDBridge.B92Sequential
