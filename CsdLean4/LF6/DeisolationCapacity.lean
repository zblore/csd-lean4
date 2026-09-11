/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.HolevoBound
public import CsdLean4.Empirical.CSD.ChannelCapacity
public import CsdLean4.LF6.DecoherenceChannel
public import CsdLean4.Thermo.SigmaSecondLaw

/-!
# The single-letter Holevo capacity of the de-isolation channel is one bit

**Category:** 3-Local (W10 of `specs/qit-chain-scoping.md`).

`Empirical/CSD/ChannelCapacity.lean` computed, for the bare dephasing map, that the classical bit
ensemble carries a Holevo quantity of `log 2` and that a coherent input loses a bit of entropy: an
*example* of a capacity, on a posited map. With W5–W7 the de-isolation channel is a genuine
`QuantumInfo.Channel` produced by LF5's flow, and with W8 the Holevo bound is a theorem. This
module states the capacity as a theorem:

* `deisolationChannel_apply_eq_decohereReducedN` — on Hermitian inputs the de-isolation channel is
  the empirical dephasing map, so every computation of `ChannelCapacity.lean` transfers;
* `deisolationChannel_apply_single` — it fixes the computational-basis states;
* ★ `holevoChi_classicalBit_deisolation` — the classical bit ensemble has Holevo quantity `log 2`
  through it;
* ★★ `deisolationChannel_holevoCapacity` — **`log 2` is the greatest single-letter Holevo quantity
  any ensemble of qubit density matrices achieves through the de-isolation channel**
  (`IsGreatest (holevoRange (deisolationChannel 2)) (log 2)`): the Holevo bound caps every ensemble,
  the classical bit attains it. One classical bit, the pointer-basis bit, is what the channel
  transmits.

## Honest scope

Single-letter (one channel use). The regularised classical capacity is a limit over many uses with
an additivity question, not defined in the corpus. The channel is the environment marginal of LF5's
measurement flow (`LF6/MeasurementFlowChannel.lean`); that reading is inherited, with its
hypotheses (the flow projects to the measurement flow; the preparation is a product with the
apparatus ready).

References: `specs/qit-chain-scoping.md` (W10, W8); `Mathlib/QuantumInfo/HolevoBound.lean`;
`Empirical/CSD/ChannelCapacity.lean`; `LF6/DecoherenceChannel.lean`; `Thermo/SigmaSecondLaw.lean`
(`deisolationChannel_apply_eq_pinch`).
-/

@[expose] public section

open Matrix QuantumInfo
open scoped ComplexOrder

/-! ### The de-isolation channel's single-letter Holevo capacity is one bit -/

namespace CSD.LF6

open CSD.LF2 CSD.Empirical.CSDBridge.Einselection CSD.Empirical.CSDBridge.ChannelCapacity

variable {N : ℕ} [NeZero N]

/-- The de-isolation channel acts on Hermitian inputs as the empirical dephasing map
`decohereReducedN` (diagonal restriction). -/
theorem deisolationChannel_apply_eq_decohereReducedN {ρ : Matrix (Fin N) (Fin N) ℂ}
    (hρ : ρ.IsHermitian) : (deisolationChannel N).apply ρ = decohereReducedN ρ := by
  rw [Thermo.deisolationChannel_apply_eq_pinch hρ, decohereReducedN, Thermo.pinch]
  congr 1
  funext i
  exact Thermo.diag_ofReal_re_of_isHermitian hρ i

/-- The de-isolation channel fixes the computational-basis states. -/
theorem deisolationChannel_apply_single (i : Fin N) :
    (deisolationChannel N).apply (outerProduct (EuclideanSpace.single i (1 : ℂ)))
      = outerProduct (EuclideanSpace.single i (1 : ℂ)) := by
  rw [deisolationChannel_apply_eq_decohereReducedN (outerProduct_isHermitian _),
    dephasing_fixes_basis_state]

/-- The classical bit ensemble `{(½, |0⟩⟨0|), (½, |1⟩⟨1|)}`, as a `Fin 2`-indexed ensemble. -/
noncomputable def classicalBit : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun i => outerProduct (EuclideanSpace.single i (1 : ℂ))

theorem classicalBit_posSemidef (i : Fin 2) : (classicalBit i).PosSemidef := outerProduct_posSemidef _

theorem classicalBit_trace (i : Fin 2) : (classicalBit i).trace = 1 :=
  outerProduct_trace_of_unit_norm _ (compBasis_norm i)

/-- The equal-weight average of the classical bit ensemble is `½ I`. -/
theorem classicalBit_avg :
    (∑ i : Fin 2, (((fun _ : Fin 2 => (1 : ℝ) / 2) i : ℝ) : ℂ) • classicalBit i)
      = (↑((1 : ℝ) / 2) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Fin.sum_univ_two]
  exact classical_avg_eq_half_one

/-- ★ The Holevo quantity of the classical bit ensemble through the de-isolation channel is
`log 2`: the channel fixes the ensemble, its average is `½ I` with entropy `log 2`, and the
components are pure. -/
theorem holevoChi_classicalBit_deisolation :
    holevoChi (fun _ : Fin 2 => (1 : ℝ) / 2)
        (fun i => (deisolationChannel 2).apply_isHermitian (classicalBit_posSemidef i).1)
        (isHermitian_finset_sum_smul Finset.univ _
          fun i => (deisolationChannel 2).apply_isHermitian (classicalBit_posSemidef i).1)
      = Real.log 2 := by
  have hfix : ∀ i : Fin 2, (deisolationChannel 2).apply (classicalBit i) = classicalBit i :=
    fun i => deisolationChannel_apply_single i
  have havg : (∑ i : Fin 2, (((fun _ : Fin 2 => (1 : ℝ) / 2) i : ℝ) : ℂ)
      • (deisolationChannel 2).apply (classicalBit i))
      = (↑((1 : ℝ) / 2) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    simp_rw [hfix]; exact classicalBit_avg
  unfold holevoChi
  rw [QuantumInfo.vonNeumannEntropy_congr_of_eq _ (const_smul_one_isHermitian (N := 2) ((1 : ℝ) / 2))
    havg, vonNeumannEntropy_const_smul_one]
  have hzero : ∀ i : Fin 2, vonNeumannEntropy
      ((deisolationChannel 2).apply_isHermitian (classicalBit_posSemidef i).1) = 0 := fun i => by
    rw [QuantumInfo.vonNeumannEntropy_congr_of_eq _ (outerProduct_isHermitian _) (hfix i)]
    exact compBasis_entropy_zero i
  simp only [hzero, mul_zero, Finset.sum_const_zero, sub_zero, Real.negMulLog,
    show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ from by norm_num, Real.log_inv]
  push_cast; ring

/-- ★★ **The single-letter Holevo capacity of the de-isolation channel is one classical bit.**
`log 2` is the greatest single-letter Holevo quantity any ensemble of qubit density matrices
achieves through `deisolationChannel 2` — the Holevo bound caps every ensemble at `log 2`, and the
classical bit ensemble attains it. The channel is the environment marginal of LF5's de-isolation
flow (`LF6/MeasurementFlowChannel.lean`), so this is a statement about what a `Σ`-flow transmits:
the pointer-basis bit in full, and nothing more. -/
theorem deisolationChannel_holevoCapacity :
    IsGreatest (holevoRange (deisolationChannel 2)) (Real.log 2) := by
  refine ⟨⟨2, fun _ => (1 : ℝ) / 2, classicalBit, fun _ => by norm_num, by
    rw [Fin.sum_univ_two]; norm_num, classicalBit_posSemidef, classicalBit_trace,
    holevoChi_classicalBit_deisolation.symm⟩, fun x hx => ?_⟩
  have h := holevoRange_le_log_card (deisolationChannel 2) hx
  simpa [Fintype.card_fin] using h

end CSD.LF6
