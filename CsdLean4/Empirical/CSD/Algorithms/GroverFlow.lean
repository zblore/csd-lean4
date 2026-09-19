/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.Algorithms.CircuitFlow
public import CsdLean4.Empirical.QM.Algorithms.Grover

/-!
# Empirical/CSD: Grover's search as a flow on `Σ`

**Category:** 3-Local (CSD-side twin of `Empirical/QM/Algorithms/Grover.lean`).

`Empirical/QM/Algorithms/Grover.lean` proves the search algorithm on the QM side: after `k` Grover
steps from the uniform superposition the marked item `w` is measured with probability
`sin²((2k+1)θ)` (`grover_success`). This file is the same algorithm on the CSD side. The Grover
step is a unitary matrix on the `n`-qubit register (the oracle and the diffusion operator are
reflections, `1 − 2|v⟩⟨v|`), so it is a `Circuit` and hence a **flow on the register's sector**
`Σ = ℂℙ^{2ⁿ − 1}` (`CircuitFlow.lean`); `k` runs are the flow iterated `k` times; and the readout
is the record basin of the outcome `w`. The headline reads the algorithm's success probability
off the basin's Born weight at the flowed ready point.

* `reflectionMatrix v = 1 − 2|v⟩⟨v|` — the reflection through a unit vector, with
  `reflectionMatrix_conjTranspose_mul` (unitary) and `toEuclideanLin_reflectionMatrix`
  (`ψ ↦ ψ − 2⟪v, ψ⟫ v`);
* `oracleMatrix w`, `diffusionMatrix n`, `groverMatrix w` — Grover's operators as matrices, with
  `toEuclideanLin_groverMatrix` : they act as `groverStep w`;
* `groverCircuit w : Circuit (Fin n → Fin 2)` — **the search as a circuit**, hence
  `(groverCircuit w).flow` is **the search as a `Σ`-flow**;
* `groverReady` — the uniform superposition as a point of the sector;
* ★★ `grover_flow_born` — **Grover on `Σ`**: at the point reached from the ready point by `k`
  runs of the flow, the record basin of the marked item has Born weight `sin²((2k+1)θ)`; and
  ★ `grover_flow_certain`, certainty at the optimal count.

⚠️ **Honest scope.** The QM-side theorem carries the mathematics; this file adds the ontic
reading (a flow on `Σ`, a basin as readout) and no new analysis of the algorithm. What the
`RegisterFlow.lean` note says applies: the flow is the time-one map of the projective action, no
Hamiltonian generating the step is modelled (`R-015`). The oracle is a reflection given as a
matrix; no query model is claimed, as in the QM file.

References: `Empirical/QM/Algorithms/Grover.lean`; `Empirical/CSD/Algorithms/CircuitFlow.lean`;
`specs/BACKLOG.md` #34; `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Matrix QuantumInfo
open scoped LinearAlgebra.Projectivization ComplexConjugate

namespace CSD
namespace Empirical
namespace CSDBridge
namespace Algorithms

open CSD.LF2 CSD.LF4 CSD.RecordLayer CSD.Empirical.QM.Grover

/-! ### Reflections as matrices -/

section Reflection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The reflection through a unit vector `v`, as a matrix: `1 − 2|v⟩⟨v|`. -/
noncomputable def reflectionMatrix (v : EuclideanSpace ℂ ι) : Matrix ι ι ℂ :=
  1 - (2 : ℂ) • outerProduct v

/-- A reflection is Hermitian. -/
theorem reflectionMatrix_conjTranspose (v : EuclideanSpace ℂ ι) :
    (reflectionMatrix v)ᴴ = reflectionMatrix v := by
  simp [reflectionMatrix, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    (outerProduct_isHermitian v).eq]

/-- A reflection through a unit vector is an involution. -/
theorem reflectionMatrix_mul_self (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    reflectionMatrix v * reflectionMatrix v = 1 := by
  simp only [reflectionMatrix, sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, outerProduct_mul_self_of_unit_norm v hv, smul_smul]
  module

/-- A reflection through a unit vector is unitary. -/
theorem reflectionMatrix_conjTranspose_mul (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    (reflectionMatrix v)ᴴ * reflectionMatrix v = 1 := by
  rw [reflectionMatrix_conjTranspose, reflectionMatrix_mul_self v hv]

/-- `|v⟩⟨v|` acts as `ψ ↦ ⟪v, ψ⟫ v`. -/
theorem toEuclideanLin_outerProduct (v ψ : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanLin (outerProduct v) ψ = inner ℂ v ψ • v := by
  ext i
  simp only [Matrix.toLpLin_apply, PiLp.toLp_apply, Matrix.mulVec, dotProduct, outerProduct,
    Matrix.vecMulVec_apply, PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply, RCLike.inner_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def]
  ring

/-- A reflection acts as `ψ ↦ ψ − 2⟪v, ψ⟫ v`. -/
theorem toEuclideanLin_reflectionMatrix (v ψ : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanLin (reflectionMatrix v) ψ = ψ - (2 * inner ℂ v ψ) • v := by
  rw [reflectionMatrix, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    toEuclideanLin_outerProduct, smul_smul]
  congr 1
  exact congrFun (congrArg DFunLike.coe (Matrix.toLpLin_one 2)) ψ

end Reflection

/-! ### Grover's operators as matrices -/

variable {n : ℕ}

/-- The oracle `1 − 2|w⟩⟨w|`, the reflection through the marked basis state. -/
noncomputable def oracleMatrix (w : Fin n → Fin 2) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  reflectionMatrix (basisState w)

/-- The diffusion operator `2|s⟩⟨s| − 1`, minus the reflection through the uniform
superposition. -/
noncomputable def diffusionMatrix (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  -reflectionMatrix (uniformState (n := n))

/-- One Grover step as a matrix: diffusion after the oracle. -/
noncomputable def groverMatrix (w : Fin n → Fin 2) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  diffusionMatrix n * oracleMatrix w

theorem toEuclideanLin_oracleMatrix (w : Fin n → Fin 2) (ψ : QReg n) :
    Matrix.toEuclideanLin (oracleMatrix w) ψ = oracle w ψ := by
  rw [oracleMatrix, toEuclideanLin_reflectionMatrix, oracle, basisState,
    EuclideanSpace.inner_single_left, map_one, one_mul]

theorem toEuclideanLin_diffusionMatrix (ψ : QReg n) :
    Matrix.toEuclideanLin (diffusionMatrix n) ψ = diffusion ψ := by
  rw [diffusionMatrix, map_neg, LinearMap.neg_apply, toEuclideanLin_reflectionMatrix, diffusion,
    neg_sub]

/-- **The Grover matrix acts as the Grover step.** -/
theorem toEuclideanLin_groverMatrix (w : Fin n → Fin 2) :
    ⇑(Matrix.toEuclideanLin (groverMatrix w)) = groverStep w := by
  funext ψ
  rw [groverMatrix, toEuclideanLin_mul_apply', toEuclideanLin_oracleMatrix,
    toEuclideanLin_diffusionMatrix]
  rfl

/-- The Grover matrix is unitary. -/
theorem groverMatrix_conjTranspose_mul (w : Fin n → Fin 2) :
    (groverMatrix w)ᴴ * groverMatrix w = 1 := by
  rw [groverMatrix, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (diffusionMatrix n)ᴴ, diffusionMatrix, Matrix.conjTranspose_neg,
    Matrix.neg_mul, Matrix.mul_neg, neg_neg,
    reflectionMatrix_conjTranspose_mul _ uniformState_norm, Matrix.one_mul, oracleMatrix,
    reflectionMatrix_conjTranspose_mul _ (basisState_norm w)]

/-! ### The search as a circuit and as a flow -/

/-- **Grover's search as a circuit** on the `n`-qubit register. -/
noncomputable def groverCircuit (w : Fin n → Fin 2) : Circuit (Fin n → Fin 2) :=
  ⟨groverMatrix w, groverMatrix_conjTranspose_mul w⟩

theorem groverCircuit_U (w : Fin n → Fin 2) : (groverCircuit w).U = groverMatrix w :=
  rfl

/-- The uniform superposition, enumerated. -/
noncomputable def uniformReady (n : ℕ) : EuclideanSpace ℂ (Fin (Fintype.card (Fin n → Fin 2))) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (idx (Fin n → Fin 2)) uniformState

theorem uniformReady_norm : ‖uniformReady n‖ = 1 := by
  rw [uniformReady, LinearIsometryEquiv.norm_map, uniformState_norm]

theorem uniformReady_ne_zero : uniformReady n ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [uniformReady_norm]; exact one_ne_zero)

/-- **The ready point**: the uniform superposition as a point of the register's sector. -/
noncomputable def groverReady (n : ℕ) : RegisterSector (Fin n → Fin 2) :=
  Projectivization.mk ℂ (uniformReady n) uniformReady_ne_zero

/-- ★★ **Grover on `Σ`.** At the point reached from the ready point by `k` runs of the search
flow, the record basin of the marked item `w` has Born weight `sin²((2k+1)θ)`, `sin θ = 1/√2ⁿ`:
the algorithm's success probability, read as the ontic typicality volume of the outcome's
basin at the flowed point. -/
theorem grover_flow_born (hn : 1 ≤ n) (w : Fin n → Fin 2) (k : ℕ) (θ : ℝ)
    (hsin : Real.sin θ = (Real.sqrt (2 ^ n))⁻¹)
    (hcos : Real.cos θ = Real.sqrt (2 ^ n - 1) / Real.sqrt (2 ^ n)) :
    epistemicMeasure ((groverCircuit w).flow^[k] (groverReady n))
        (globalBasin (momentContext (Fintype.card (Fin n → Fin 2))) (idx (Fin n → Fin 2) w))
      = ENNReal.ofReal (Real.sin ((2 * k + 1) * θ) ^ 2) := by
  rw [groverReady, Circuit.epistemicMeasure_globalBasin_flow_iterate _ _ _ _ uniformReady_norm,
    Circuit.coe_toUnitaryGroup_pow, uniformReady, toEuclideanLin_reindex_piLpCongrLeft,
    piLpCongrLeft_apply_apply, toEuclideanLin_pow_apply, groverCircuit_U, toEuclideanLin_groverMatrix,
    ← grover_success hn w k θ hsin hcos]
  rfl

/-- ★ **Certainty at the optimal count, on `Σ`**: when `(2k+1)θ = π/2` the marked item's basin
has full weight at the flowed ready point. -/
theorem grover_flow_certain (hn : 1 ≤ n) (w : Fin n → Fin 2) (k : ℕ) (θ : ℝ)
    (hsin : Real.sin θ = (Real.sqrt (2 ^ n))⁻¹)
    (hcos : Real.cos θ = Real.sqrt (2 ^ n - 1) / Real.sqrt (2 ^ n))
    (hopt : (2 * k + 1) * θ = Real.pi / 2) :
    epistemicMeasure ((groverCircuit w).flow^[k] (groverReady n))
        (globalBasin (momentContext (Fintype.card (Fin n → Fin 2))) (idx (Fin n → Fin 2) w)) = 1 := by
  rw [grover_flow_born hn w k θ hsin hcos, hopt, Real.sin_pi_div_two, one_pow, ENNReal.ofReal_one]

end Algorithms
end CSDBridge
end Empirical
end CSD
