/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Subadditivity
public import CsdLean4.LF6.Decoherence

/-!
# Tests/EntropyWitness: committed non-vacuity witnesses for the entropy chain

**Category:** Special (test witness; CL-022 audit follow-up, 2026-08-06).

The 2026-08-06 specialist audit of the entropy chain (CL-022) found that the
validation ledger's non-vacuity evidence for `vonNeumannEntropy_subadditive`
referred to audit-session scratch probes that were never committed. This module
is the reproducible artifact:

* `corrState` — the classically-correlated two-qubit state
  `½(|00⟩⟨00| + |11⟩⟨11|) = diag(½, 0, 0, ½)`: PSD (not PD — rank 2), trace 1,
  both marginals `= ½·I` (PD). Subadditivity applies and is **strict**:
  `S(ρ_AB) = log 2 < 2·log 2 = S(ρ_A) + S(ρ_B)`
  (`corrState_subadditivity_strict`) — so the inequality is genuinely
  discriminating at a correlated non-product state, not a product-state
  identity.
* `corrStatePD` — the full-rank correlated state `diag(3/8, 1/8, 1/8, 3/8)`:
  PD, trace 1, marginals `= ½·I`. Witnesses that the **Araki–Lieb** form's
  `ρ_AB.PosDef` hypothesis is satisfiable at a correlated state
  (`corrStatePD_araki_lieb`).

Reuses `QuantumInfo.entropy_congr_of_eq` (from `Mathlib/QuantumInfo/Entropy.lean`) to
transport entropy along marginal equalities.
-/

@[expose] public section

open Matrix QuantumInfo
open scoped ComplexOrder

namespace CSD
namespace Tests

/-! ## The rank-two correlated witness: strict subadditivity -/

/-- Diagonal of the classically-correlated two-qubit state: `½` on the
correlated pairs `(0,0)`, `(1,1)`, zero elsewhere. -/
noncomputable def corrDiag (p : Fin 2 × Fin 2) : ℝ :=
  if p.1 = p.2 then 1 / 2 else 0

/-- `corrDiag` is nonnegative. -/
lemma corrDiag_nonneg (p : Fin 2 × Fin 2) : 0 ≤ corrDiag p := by
  unfold corrDiag; split <;> norm_num

/-- The classically-correlated two-qubit state `½(|00⟩⟨00| + |11⟩⟨11|)`. -/
noncomputable def corrState : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal fun p => (corrDiag p : ℂ)

lemma corrState_posSemidef : corrState.PosSemidef :=
  (Matrix.posSemidef_diagonal_iff).mpr fun p =>
    RCLike.ofReal_nonneg.mpr (corrDiag_nonneg p)

lemma corrState_trace_one : corrState.trace = 1 := by
  simp [corrState, Matrix.trace_diagonal, corrDiag, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  norm_num

/-- The right marginal (trace out the second qubit) is `½·I`, as a diagonal. -/
lemma corrState_traceRight :
    partialTraceRight corrState
      = Matrix.diagonal fun _ : Fin 2 => ((1 / 2 : ℝ) : ℂ) := by
  ext i j
  simp only [partialTraceRight_apply, corrState, Matrix.diagonal_apply, corrDiag]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_two, Prod.ext_iff]

/-- The left marginal (trace out the first qubit) is `½·I`, as a diagonal. -/
lemma corrState_traceLeft :
    partialTraceLeft corrState
      = Matrix.diagonal fun _ : Fin 2 => ((1 / 2 : ℝ) : ℂ) := by
  ext i j
  simp only [partialTraceLeft_apply, corrState, Matrix.diagonal_apply, corrDiag]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_two, Prod.ext_iff]

/-- The uniform qubit diagonal `½·I` is positive-definite. -/
lemma halfDiag_posDef :
    (Matrix.diagonal fun _ : Fin 2 => ((1 / 2 : ℝ) : ℂ)).PosDef :=
  (Matrix.posDef_diagonal_iff).mpr fun _ => RCLike.ofReal_pos.mpr one_half_pos

lemma corrState_marginalRight_posDef : (partialTraceRight corrState).PosDef :=
  corrState_traceRight ▸ halfDiag_posDef

lemma corrState_marginalLeft_posDef : (partialTraceLeft corrState).PosDef :=
  corrState_traceLeft ▸ halfDiag_posDef

/-- `S(½·I) = log 2` for the uniform qubit diagonal (via the general diagonal
entropy; `negMulLog ½ = ½·log 2`, twice). -/
lemma halfDiag_entropy :
    vonNeumannEntropy halfDiag_posDef.1 = Real.log 2 := by
  have h := vonNeumannEntropy_diagonal (d := fun _ : Fin 2 => (1 / 2 : ℝ))
    halfDiag_posDef.1
  rw [h, Fin.sum_univ_two, Real.negMulLog, one_div, Real.log_inv]
  ring

/-- `S(corrState) = log 2`: the correlated state's entropy is one bit. -/
lemma corrState_entropy :
    vonNeumannEntropy corrState_posSemidef.1 = Real.log 2 := by
  have heq : corrState = Matrix.diagonal fun p : Fin 2 × Fin 2 => ((corrDiag p : ℝ) : ℂ) :=
    rfl
  have hd : (Matrix.diagonal fun p : Fin 2 × Fin 2 => ((corrDiag p : ℝ) : ℂ)).IsHermitian :=
    heq ▸ corrState_posSemidef.1
  have h := vonNeumannEntropy_diagonal (d := corrDiag) hd
  rw [entropy_congr_of_eq heq corrState_posSemidef.1 hd, h]
  simp only [corrDiag, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num [Real.negMulLog_zero]
  rw [Real.negMulLog, one_div, Real.log_inv]
  ring

/-- **Subadditivity is applicable AND strict at the correlated state:**
`S(ρ_AB) = log 2 < 2·log 2 = S(ρ_A) + S(ρ_B)`. The committed non-vacuity
witness for `vonNeumannEntropy_subadditive` (CL-022 criterion 4): the
inequality genuinely discriminates at a correlated non-product state. -/
theorem corrState_subadditivity_strict :
    vonNeumannEntropy corrState_posSemidef.1
      < vonNeumannEntropy corrState_marginalRight_posDef.1
        + vonNeumannEntropy corrState_marginalLeft_posDef.1 := by
  have hA : vonNeumannEntropy corrState_marginalRight_posDef.1 = Real.log 2 := by
    rw [entropy_congr_of_eq corrState_traceRight
      corrState_marginalRight_posDef.1 halfDiag_posDef.1]
    exact halfDiag_entropy
  have hB : vonNeumannEntropy corrState_marginalLeft_posDef.1 = Real.log 2 := by
    rw [entropy_congr_of_eq corrState_traceLeft
      corrState_marginalLeft_posDef.1 halfDiag_posDef.1]
    exact halfDiag_entropy
  rw [corrState_entropy, hA, hB]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-- The subadditivity theorem itself applies at the witness (hypothesis
inhabitation check — the `≤` instance the strict form refines). -/
example :
    vonNeumannEntropy corrState_posSemidef.1
      ≤ vonNeumannEntropy corrState_marginalRight_posDef.1
        + vonNeumannEntropy corrState_marginalLeft_posDef.1 :=
  vonNeumannEntropy_subadditive corrState_posSemidef corrState_trace_one
    corrState_marginalRight_posDef corrState_marginalLeft_posDef

/-! ## The full-rank correlated witness: Araki–Lieb applicability -/

/-- Diagonal of a full-rank correlated two-qubit state: `3/8` on the
correlated pairs, `1/8` on the anti-correlated ones. -/
noncomputable def corrDiagPD (p : Fin 2 × Fin 2) : ℝ :=
  if p.1 = p.2 then 3 / 8 else 1 / 8

/-- The full-rank correlated two-qubit state `diag(3/8, 1/8, 1/8, 3/8)`. -/
noncomputable def corrStatePD : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal fun p => (corrDiagPD p : ℂ)

lemma corrDiagPD_pos (p : Fin 2 × Fin 2) : 0 < corrDiagPD p := by
  unfold corrDiagPD; split <;> norm_num

lemma corrStatePD_posDef : corrStatePD.PosDef :=
  (Matrix.posDef_diagonal_iff).mpr fun p => RCLike.ofReal_pos.mpr (corrDiagPD_pos p)

lemma corrStatePD_trace_one : corrStatePD.trace = 1 := by
  simp [corrStatePD, Matrix.trace_diagonal, corrDiagPD, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  norm_num

lemma corrStatePD_traceRight :
    partialTraceRight corrStatePD
      = Matrix.diagonal fun _ : Fin 2 => ((1 / 2 : ℝ) : ℂ) := by
  ext i j
  simp only [partialTraceRight_apply, corrStatePD, Matrix.diagonal_apply, corrDiagPD]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_two, Prod.ext_iff] <;> norm_num

lemma corrStatePD_traceLeft :
    partialTraceLeft corrStatePD
      = Matrix.diagonal fun _ : Fin 2 => ((1 / 2 : ℝ) : ℂ) := by
  ext i j
  simp only [partialTraceLeft_apply, corrStatePD, Matrix.diagonal_apply, corrDiagPD]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_two, Prod.ext_iff] <;> norm_num

lemma corrStatePD_marginalRight_posDef : (partialTraceRight corrStatePD).PosDef :=
  corrStatePD_traceRight ▸ halfDiag_posDef

lemma corrStatePD_marginalLeft_posDef : (partialTraceLeft corrStatePD).PosDef :=
  corrStatePD_traceLeft ▸ halfDiag_posDef

/-- **Araki–Lieb applies at a full-rank correlated state** (hypothesis
inhabitation for `vonNeumannEntropy_araki_lieb`'s `ρ_AB.PosDef` scope —
CL-022 audit follow-up). -/
theorem corrStatePD_araki_lieb :
    |vonNeumannEntropy corrStatePD_marginalRight_posDef.1
        - vonNeumannEntropy corrStatePD_marginalLeft_posDef.1|
      ≤ vonNeumannEntropy corrStatePD_posDef.1 :=
  vonNeumannEntropy_araki_lieb corrStatePD_posDef corrStatePD_trace_one
    corrStatePD_marginalRight_posDef corrStatePD_marginalLeft_posDef

end Tests
end CSD
