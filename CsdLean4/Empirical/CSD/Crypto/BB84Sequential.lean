/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.Crypto.BB84
public import CsdLean4.Empirical.QM.Crypto.B92
public import CsdLean4.Empirical.CSD.SequentialMeasurement
public import CsdLean4.RecordLayer.RotatedContext
public import CsdLean4.RecordLayer.RotatedSwap

/-!
# Empirical/CSD/Crypto: BB84 intercept-resend with a dynamical collapse step

**Category:** CSD bridge (dynamical). The second empirical entry consuming the measurement
dynamics, and the first with a **cross-basis** sequential read.

## The dissolved gate

`Empirical/QM/Crypto/BB84.lean` proves the intercept-resend QBER `¼` with an explicit scope
note: Eve's measurement is a *classical marginal over her outcomes*, because a
measurement-update (collapse) operator "remains out of scope — the same LF5 gate". That gate
predates the dynamical measurement layer. This module replaces the posited marginal with the
**calibrated-swap dynamics**: Eve's measure-and-resend step is `csd_sequential_born` — the
collapse is a pushforward theorem, not a modelling assumption.

## The round, and why it is the dual of the QM module's

The QM module's canonical sifted round is *Alice Z, Bob Z, Eve X*. Here we take the dual round
*Alice X (`|+⟩`), Bob X, Eve Z* — so that Eve's measurement is in the **computational** basis,
the calibrated-swap witness's native scope, and Bob's follow-up is the **rotated** (X-basis)
context `basisContext xBasisON` from `SigmaLayer/RotatedContext.lean`. The two rounds have the
same per-basis error values by the Z/X symmetry of the four states;
`bb84_dynamical_matches_marginal` records that the dynamically derived numbers coincide with
the QM module's classical-marginal ones.

*Addendum 2026-08-02 — the dual-round caveat is retired:* with the unitary-covariance law
(`SigmaLayer/RotatedSwap.lean`, `measurement_covariance`), the **primal** round is now directly
formalised too: `bb84_primal_wrong_basis` — Eve X-measures the Z-carrier `|a⟩` (rotated
selector, rotated bank), and whatever she records, Bob's Z-basin has probability exactly `½`.
Both rounds now run natively; neither needs the other's symmetry.

Unlike the eraser twin (`QuantumEraserVolume.lean`), where the cross-basis step was realised
kinematically, **both** measurements here are context-field reads of the dynamical layer: Eve's
via `momentContext`, Bob's via the rotated context — the sequential composition is end-to-end.

## What this file proves

* `bb84_eve_selector_born` — Eve's Z-outcome weights on `|+⟩` are `½, ½`: she learns a fair
  coin, uncorrelated with Alice's X-bit (the information side of the tradeoff).
* `bb84_eve_sector_pos` — the conditioning is licensed: each Eve outcome has nonzero sector
  measure, **proved** from the preparation (`prep_outcome_pos`), not carried as a hypothesis.
* ★ `bb84_wrong_basis_bob` — after Eve's Z-measurement outcome `i`, Bob's X-basin `j` has
  probability `½`, whatever `i` and `j`: the resent eigenstate is unbiased in the sifted basis,
  so Bob errs with probability `½` (`bb84_wrong_basis_error`). The disturbance side of the
  tradeoff, with the collapse a theorem.
* ★ `bb84_right_basis_no_disturbance` / `bb84_right_basis_faithful` — Eve in the matching basis
  is exactly repeatability: Bob's error basin is null, his correct basin has probability `1`.
  Eve learns the bit and disturbs nothing.
* `bb84_dynamical_matches_marginal` — the per-basis values `0` and `½` and the assembled QBER
  `¼` agree with the QM module's `irErrorZ0` marginal model (`bb84_qber`).

## ⚠️ Honest scope

One sifted round of the intercept-resend model, inheriting the calibrated-swap witness's scope
notes (calibration posit; Hamiltonian origin §2a-scoped). Eve's basis *choice* and the ¼
average over it are classical bookkeeping, taken from the QM side. Full composable finite-key
security remains the recorded QKD tranche (`specs/future-work.md`) — nothing beyond
intercept-resend is claimed, matching the QM module's own boundary.

## References

`Empirical/QM/Crypto/BB84.lean` (states, inner products, `irErrorZ0`, `bb84_qber`);
`Empirical/QM/Crypto/B92.lean` (`ketPlus_inner_self`, `ketPlus_unit`, `ketMinus_inner_ketPlus`,
`half` — reused, not re-proved);
`Empirical/CSD/SequentialMeasurement.lean` (`csd_sequential_born`, `csd_repeatability_*`,
`readyPrep`, `prep_outcome_pos`); `SigmaLayer/RotatedContext.lean` (`basisContext`,
`basisContext_rate_mk`); `SigmaLayer/SwapLuders.lean` (`swap_luders_born` — the engine);
`SigmaLayer/DegenerateLuders.lean` (`vertexPoint`, `momentMap_vertex`);
Bennett–Brassard 1984; `specs/BACKLOG.md`; `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory

namespace CSD.Empirical.CSDBridge.BB84Sequential

open CSD.RecordLayer
open CSD.Empirical.BB84
open CSD.Empirical.B92
open CSD.Empirical.CSDBridge.SequentialMeasurement

/-! ### The X basis as an orthonormal basis -/

/-- The missing conjugate-order inner products: `⟨+|1⟩ = (√2)⁻¹`. -/
lemma ketPlus_inner_ket1 : inner ℂ ketPlus ket1 = (Real.sqrt 2 : ℂ)⁻¹ := by
  rw [← inner_conj_symm, ket1_inner_ketPlus, map_inv₀, Complex.conj_ofReal]

/-- `⟨−|1⟩ = −(√2)⁻¹`. -/
lemma ketMinus_inner_ket1 : inner ℂ ketMinus ket1 = -(Real.sqrt 2 : ℂ)⁻¹ := by
  rw [← inner_conj_symm, ket1_inner_ketMinus, map_neg, map_inv₀, Complex.conj_ofReal]

lemma ketMinus_inner_ketMinus : (inner ℂ ketMinus ketMinus : ℂ) = 1 := by
  simp only [ketMinus, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
    EuclideanSpace.inner_single_left, PiLp.single_apply, map_inv₀, Complex.conj_ofReal, map_one]
  norm_num [Fin.ext_iff]
  linear_combination (2 : ℂ) * half

lemma ketPlus_inner_ketMinus : (inner ℂ ketPlus ketMinus : ℂ) = 0 := by
  simp only [ketPlus, ketMinus, inner_smul_left, inner_smul_right, inner_add_left,
    inner_sub_right, EuclideanSpace.inner_single_left, PiLp.single_apply, map_inv₀,
    Complex.conj_ofReal, map_one]
  norm_num [Fin.ext_iff]

/-- The X-basis vectors, indexed. -/
noncomputable def xVec : Fin 2 → EuclideanSpace ℂ (Fin 2)
  | 0 => ketPlus
  | 1 => ketMinus

lemma xVec_orthonormal : Orthonormal ℂ xVec := by
  rw [orthonormal_iff_ite]
  intro a b
  fin_cases a <;> fin_cases b
  · show (inner ℂ ketPlus ketPlus : ℂ) = _
    rw [ketPlus_inner_self]; norm_num
  · show (inner ℂ ketPlus ketMinus : ℂ) = _
    rw [ketPlus_inner_ketMinus]; norm_num
  · show (inner ℂ ketMinus ketPlus : ℂ) = _
    rw [ketMinus_inner_ketPlus]; norm_num
  · show (inner ℂ ketMinus ketMinus : ℂ) = _
    rw [ketMinus_inner_ketMinus]; norm_num

/-- **The X basis as an `OrthonormalBasis`** — Bob's sifted-basis apparatus. -/
noncomputable def xBasisON : OrthonormalBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)) := by
  refine OrthonormalBasis.mk xVec_orthonormal ?_
  have hcard : Fintype.card (Fin 2) = Module.finrank ℂ (EuclideanSpace ℂ (Fin 2)) := by
    rw [Fintype.card_fin, finrank_euclideanSpace_fin]
  rw [xVec_orthonormal.linearIndependent.span_eq_top_of_card_eq_finrank hcard]

lemma xBasisON_apply (j : Fin 2) : xBasisON j = xVec j := by
  unfold xBasisON
  rw [OrthonormalBasis.coe_mk]

/-! ### The preparation `|+⟩` -/

lemma ketPlus_ne_zero : ketPlus ≠ 0 := by
  intro h
  apply bb84_states_nonorthogonal
  rw [h, inner_zero_right]

/-- The Born weights of `|+⟩` in the computational basis are `½, ½` — the states are mutually
unbiased, transported from the QM module's inner products. -/
lemma momentMap_ketPlus (i : Fin 2) :
    LF4.momentMap (Projectivization.mk ℂ ketPlus ketPlus_ne_zero) i = 1 / 2 := by
  rw [LF4.momentMap_mk_eq_inner_sq ketPlus ketPlus_ne_zero ketPlus_unit i]
  fin_cases i
  · show ‖(inner ℂ ket0 ketPlus : ℂ)‖ ^ 2 = 1 / 2
    rw [ket0_inner_ketPlus]; exact norm_sq_invSqrt2
  · show ‖(inner ℂ ket1 ketPlus : ℂ)‖ ^ 2 = 1 / 2
    rw [ket1_inner_ketPlus]; exact norm_sq_invSqrt2

/-! ### Bob's rotated context -/

/-- **Bob's X-basis rate at Eve's resent eigenstate is `½`, all four ways.** The rotated
context's rate at a computational vertex is the cross-basis Born weight — mutual unbiasedness,
now as a context-field fact. -/
theorem xContext_rate_vertex (i j : Fin 2) :
    (basisContext xBasisON).rate (vertexPoint i) j = 1 / 2 := by
  unfold vertexPoint
  rw [basisContext_rate_mk xBasisON (EuclideanSpace.single i 1) (single_ne_zero' i)
    (by simp) j, xBasisON_apply]
  fin_cases i <;> fin_cases j
  · show ‖(inner ℂ ketPlus ket0 : ℂ)‖ ^ 2 = 1 / 2
    rw [ketPlus_inner_ket0]; exact norm_sq_invSqrt2
  · show ‖(inner ℂ ketMinus ket0 : ℂ)‖ ^ 2 = 1 / 2
    rw [ketMinus_inner_ket0]; exact norm_sq_invSqrt2
  · show ‖(inner ℂ ketPlus ket1 : ℂ)‖ ^ 2 = 1 / 2
    rw [ketPlus_inner_ket1]; exact norm_sq_invSqrt2
  · show ‖(inner ℂ ketMinus ket1 : ℂ)‖ ^ 2 = 1 / 2
    rw [ketMinus_inner_ket1, norm_neg]; exact norm_sq_invSqrt2

/-! ### The wrong-basis round: Alice X, Eve Z, Bob X -/

/-- **Eve's outcome weights are a fair coin.** Measuring `|+⟩` in the computational basis, each
outcome carries weight `½` — Eve's record is uncorrelated with Alice's X-bit. The information
side of the information–disturbance tradeoff, as basin measures. -/
theorem bb84_eve_selector_born (i : Fin 2) :
    epistemicMeasure (Projectivization.mk ℂ ketPlus ketPlus_ne_zero)
        (basinIndex (momentContext 2) ⁻¹' {i})
      = ENNReal.ofReal (1 / 2) := by
  rw [measure_basinIndex_fibre, globalBasin_prob, momentContext_rate, momentMap_ketPlus]

/-- The conditioning is licensed by the preparation: each of Eve's outcome sectors has nonzero
measure — a theorem (`prep_outcome_pos`), not a hypothesis. -/
theorem bb84_eve_sector_pos (i : Fin 2) :
    readyPrep (Projectivization.mk ℂ ketPlus ketPlus_ne_zero)
      ((shearProtocol (basinIndex (momentContext 2))
        (measurable_basinIndex (momentContext 2))).outcomeSector i) ≠ 0 :=
  prep_outcome_pos _ i (by rw [momentMap_ketPlus]; norm_num)

/-- **★ The disturbance, end-to-end dynamical.** Alice sends `|+⟩`; Eve measures in the
computational basis and the calibrated-swap dynamics resends her eigenstate; Bob reads the
rotated X-context. Whatever Eve's outcome `i`, each of Bob's basins has probability exactly
`½`: the resent state is unbiased in the sifted basis. Both measurements are context-field
reads of the dynamical layer — the collapse step is `csd_sequential_born`, not a classical
marginal. -/
theorem bb84_wrong_basis_bob (i j : Fin 2) :
    postEnsemble (readyPrep (Projectivization.mk ℂ ketPlus ketPlus_ne_zero)) i
        ((fun y : SwapArena (LF4.KSigma 2) 2 => y.1.1)
          ⁻¹' globalBasin (basisContext xBasisON) j)
      = ENNReal.ofReal (1 / 2) := by
  rw [csd_sequential_born _ i (bb84_eve_sector_pos i) (basisContext xBasisON) j,
    xContext_rate_vertex i j]

/-- **★ The wrong-basis error is `½`**: Alice's bit was `+` (X-outcome `0`), and Bob's `−` basin
has probability `½` after Eve's intercept — whichever outcome Eve recorded. -/
theorem bb84_wrong_basis_error (i : Fin 2) :
    postEnsemble (readyPrep (Projectivization.mk ℂ ketPlus ketPlus_ne_zero)) i
        ((fun y : SwapArena (LF4.KSigma 2) 2 => y.1.1)
          ⁻¹' globalBasin (basisContext xBasisON) 1)
      = ENNReal.ofReal (1 / 2) :=
  bb84_wrong_basis_bob i 1

/-! ### The right-basis round: repeatability = zero disturbance -/

/-- **★ Eve in the matching basis disturbs nothing.** Alice sends the computational vertex `a`;
Eve measures in the same basis; Bob's error basin `j ≠ a` is **null**. This is exactly
`csd_repeatability_other`, with `hpos` again a theorem. -/
theorem bb84_right_basis_no_disturbance (a : Fin 2) {j : Fin 2} (hj : j ≠ a) :
    postEnsemble (readyPrep (vertexPoint a)) a
        ((fun y : SwapArena (LF4.KSigma 2) 2 => y.1.1)
          ⁻¹' globalBasin (momentContext 2) j)
      = 0 :=
  csd_repeatability_other _ a
    (prep_outcome_pos _ a (by rw [momentMap_vertex]; simp)) hj

/-- …and Bob's correct basin has probability `1`: Eve learned the bit for free. -/
theorem bb84_right_basis_faithful (a : Fin 2) :
    postEnsemble (readyPrep (vertexPoint a)) a
        ((fun y : SwapArena (LF4.KSigma 2) 2 => y.1.1)
          ⁻¹' globalBasin (momentContext 2) a)
      = 1 :=
  csd_repeatability_same _ a
    (prep_outcome_pos _ a (by rw [momentMap_vertex]; simp))

/-! ### The bridge to the QM module's marginal model -/

/-- **The dynamical values reproduce the classical-marginal ones.** The QM module's
intercept-resend model posits Eve's collapse as a marginal; its per-basis error values — `0`
matching, `½` wrong — are the numbers derived dynamically above (in the dual round), and they
assemble to the same QBER `¼`. -/
theorem bb84_dynamical_matches_marginal :
    irErrorZ0 zBasis = 0 ∧ irErrorZ0 xBasis = 1 / 2 ∧
    (1 / 2) * irErrorZ0 zBasis + (1 / 2) * irErrorZ0 xBasis = 1 / 4 :=
  ⟨bb84_intercept_resend_right_basis, bb84_intercept_resend_wrong_basis, bb84_qber⟩

/-! ### The primal round, via the covariance law -/

/-- `⟨eⱼ, xᵢ⟩` has squared norm `½`, all four ways. -/
lemma normsq_inner_single_xVec (j i : Fin 2) :
    ‖(inner ℂ (EuclideanSpace.single j (1 : ℂ)) (xVec i) : ℂ)‖ ^ 2 = 1 / 2 := by
  fin_cases j <;> fin_cases i
  · show ‖(inner ℂ ket0 ketPlus : ℂ)‖ ^ 2 = 1 / 2
    rw [ket0_inner_ketPlus]; exact norm_sq_invSqrt2
  · show ‖(inner ℂ ket0 ketMinus : ℂ)‖ ^ 2 = 1 / 2
    rw [ket0_inner_ketMinus]; exact norm_sq_invSqrt2
  · show ‖(inner ℂ ket1 ketPlus : ℂ)‖ ^ 2 = 1 / 2
    rw [ket1_inner_ketPlus]; exact norm_sq_invSqrt2
  · show ‖(inner ℂ ket1 ketMinus : ℂ)‖ ^ 2 = 1 / 2
    rw [ket1_inner_ketMinus, norm_neg]; exact norm_sq_invSqrt2

/-- `⟨xᵢ, eₐ⟩` has squared norm `½`, all four ways. -/
lemma normsq_inner_xVec_single (i a : Fin 2) :
    ‖(inner ℂ (xVec i) (EuclideanSpace.single a (1 : ℂ)) : ℂ)‖ ^ 2 = 1 / 2 := by
  fin_cases i <;> fin_cases a
  · show ‖(inner ℂ ketPlus ket0 : ℂ)‖ ^ 2 = 1 / 2
    rw [ketPlus_inner_ket0]; exact norm_sq_invSqrt2
  · show ‖(inner ℂ ketPlus ket1 : ℂ)‖ ^ 2 = 1 / 2
    rw [ketPlus_inner_ket1]; exact norm_sq_invSqrt2
  · show ‖(inner ℂ ketMinus ket0 : ℂ)‖ ^ 2 = 1 / 2
    rw [ketMinus_inner_ket0]; exact norm_sq_invSqrt2
  · show ‖(inner ℂ ketMinus ket1 : ℂ)‖ ^ 2 = 1 / 2
    rw [ketMinus_inner_ket1, norm_neg]; exact norm_sq_invSqrt2

/-- **★ The primal round (Alice Z, Eve X, Bob Z) — the dual-round caveat retired.** Eve
measures the Z-carrier `|a⟩` in the X basis (rotated selector, rotated bank, via the
unitary-covariance law); whatever she records and the dynamics resends, Bob's Z-basin `j`
has probability exactly `½`. This is the QM module's own round, now end-to-end dynamical. -/
theorem bb84_primal_wrong_basis (a i j : Fin 2) :
    ((swapProtocol (basinIndex (basisContext xBasisON))
        (measurable_basinIndex (basisContext xBasisON))).postMeasure
      ((readyPrep (vertexPoint a)).prod (rotatedBank xBasisON)) i)
      ((fun y : SwapArena (LF4.KSigma 2) 2 => y.1.1) ⁻¹' globalBasin (momentContext 2) j)
      = ENNReal.ofReal (1 / 2) := by
  have hpos : ‖(inner ℂ (xBasisON i) (EuclideanSpace.single a (1 : ℂ)) : ℂ)‖ ^ 2 ≠ 0 := by
    rw [xBasisON_apply, normsq_inner_xVec_single]
    norm_num
  have hvp : vertexPoint a
      = Projectivization.mk ℂ (EuclideanSpace.single a (1 : ℂ)) (single_ne_zero' a) := rfl
  rw [hvp, rotated_swap_luders_born xBasisON (single_ne_zero' a) (by simp) i hpos
    (momentContext 2) j, momentContext_rate,
    show basisPoint xBasisON i
      = Projectivization.mk ℂ (xBasisON i) (xBasisON.orthonormal.ne_zero i) from rfl,
    LF4.momentMap_mk_eq_inner_sq (xBasisON i) (xBasisON.orthonormal.ne_zero i)
      (xBasisON.orthonormal.1 i) j, xBasisON_apply, normsq_inner_single_xVec]

end CSD.Empirical.CSDBridge.BB84Sequential
