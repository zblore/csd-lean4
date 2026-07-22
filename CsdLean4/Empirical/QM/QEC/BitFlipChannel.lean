/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Mathlib.QuantumInfo.CanonicalChannels
import CsdLean4.Empirical.QM.QEC.ThreeQubit

/-!
# Empirical/QM/QEC: the bit-flip error channel

**Category:** 3-Local.

The honest **error model** behind the three-qubit bit-flip code (`ThreeQubit.lean`): a
single-qubit error is not a coherent rotation but a **CPTP channel** — decoherence from
interaction with the environment. The canonical bit-flip channel is

  `Φ(ρ) = (1 − p) ρ + p · X ρ X`,

a `mixedUnitaryChannel` with Kraus operators `{√(1−p) · I, √p · X}` (channels phase C4 of
`specs/channels-plan.md`). With probability `p` the qubit suffers an `X` (bit-flip) error;
with probability `1 − p` it is left alone.

This is the **"error = decoherence"** statement made precise: the error is the
environment-averaged image of the joint system-environment flow (the channel's Stinespring
dilation, `QuantumInfo.Channel.stinespringIsom`). The *correction* — syndrome measurement
and recovery — is the discrete `X₁/X₂/X₃` recovery of `ThreeQubit.lean`; closing the loop
to a measurement-conditioned update is LF5 work.
-/

open Matrix QuantumInfo
open scoped ComplexOrder

-- The `fin_cases i <;> simp [...]` proofs below apply one simp set across both `Fin 2`
-- branches, which legitimately use disjoint lemma subsets; the unused-arg linter flags the
-- per-branch unused entries as false positives.
set_option linter.unusedSimpArgs false

namespace CSD
namespace Empirical
namespace QM
namespace QEC

/-- The Pauli `X` is self-adjoint. -/
@[simp] lemma pX_conjTranspose : pXᴴ = pX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pX, Matrix.conjTranspose_apply]

/-- The Pauli `X` is unitary: `Xᴴ X = 1`. -/
lemma pX_unitary : pXᴴ * pX = 1 := by rw [pX_conjTranspose, pX_mul_pX]

/-- The single-qubit **bit-flip channel** `Φ(ρ) = (1−p) ρ + p · X ρ X`, the canonical
decoherence / error model for a qubit: a `mixedUnitaryChannel` over `{I, X}` with
probabilities `{1−p, p}` (Kraus `{√(1−p) I, √p X}`). -/
noncomputable def bitFlipChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Channel (Fin 2) (Fin 2) (Fin 2) :=
  Channel.mixedUnitaryChannel ![1, pX]
    (by intro i; fin_cases i <;>
        simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, pX_unitary])
    ![1 - p, p]
    (by intro i; fin_cases i <;>
        simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> linarith)
    (by rw [Fin.sum_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; ring)

/-- **The bit-flip channel acts as advertised:** `Φ(ρ) = (1−p) ρ + p · X ρ X`. The
decoherence reading of a single-qubit error. -/
theorem bitFlipChannel_apply (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (bitFlipChannel p hp0 hp1).apply ρ
      = ((1 - p : ℝ) : ℂ) • ρ + ((p : ℝ) : ℂ) • (pX * ρ * pX) := by
  rw [bitFlipChannel, Channel.mixedUnitaryChannel_apply, Fin.sum_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, pX_conjTranspose]

end QEC
end QM
end Empirical
end CSD
