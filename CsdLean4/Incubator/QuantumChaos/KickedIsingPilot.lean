/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Incubator.QuantumChaos.FloquetInterface
public import CsdLean4.Mathlib.QuantumInfo.PartialTrace

/-!
# The two-qubit kicked-Ising pilot model (quantum-chaos workstream, H3)

**Category:** Special (incubator — CSD-free; `upstream-candidate(physlib)`).

The concrete Floquet model of the §H3 pilot: one period of the kicked Ising
chain on two qubits,

  `U(J, b) = exp(-iJ σᶻ⊗σᶻ) · (exp(-ib σˣ) ⊗ exp(-ib σˣ))`,

built from EXPLICIT matrices (no matrix exponential needed: the Ising phase is
diagonal, the kick is the standard `x`-rotation), indexed by `Fin 2 × Fin 2` —
the composite index the corpus's partial-trace machinery consumes directly.

* `kickMat b` — the one-qubit kick `[[cos b, -i sin b], [-i sin b, cos b]]`,
  unitary (`kickMat_mem_unitaryGroup`, the `sin² + cos²` computation).
* `phaseMat J` — the Ising phase `diag(e^{-iJ}, e^{iJ}, e^{iJ}, e^{-iJ})`,
  unitary (unit-modulus diagonal).
* `kronecker_mem_unitaryGroup` — the Kronecker product of unitaries is
  unitary (generic; `upstream-candidate(mathlib)`).
* `kickedIsingU J b` — the Floquet unitary, assembled in the unitary GROUP
  (membership by group multiplication); `kickedIsingFloquet J b` — the model
  as a `FloquetEvolution` through the generic `ofUnitaryMatrix` seam.
* ★ `kickedIsing_changes_marginal` — the **accessibility-change witness** of
  the pilot statement: at kick angle `b = π/2` the step sends `|00⟩` to a
  phase times `|11⟩`, so the reduced (first-qubit) state flips
  `|0⟩⟨0| ↦ |1⟩⟨1|` — the restricted marginal genuinely changes — while the
  interface's `inner_iterate_iterate` says all global overlaps are exactly
  preserved. Together: global information intact, local accessibility moved.
-/

@[expose] public section

open Matrix
open Kronecker

namespace QuantumChaos

/-! ### The one-qubit kick -/

/-- The kick matrix `exp(-ib σˣ) = [[cos b, -i sin b], [-i sin b, cos b]]`. -/
noncomputable def kickMat (b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos b : ℂ), -(Complex.I * Real.sin b);
     -(Complex.I * Real.sin b), (Real.cos b : ℂ)]

/-- The kick is unitary: `sin² + cos² = 1`. -/
lemma kickMat_mem_unitaryGroup (b : ℝ) :
    kickMat b ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hc : (starRingEnd ℂ) (Complex.cos (b : ℂ)) = Complex.cos (b : ℂ) := by
    rw [← Complex.cos_conj, Complex.conj_ofReal]
  have hs : (starRingEnd ℂ) (Complex.sin (b : ℂ)) = Complex.sin (b : ℂ) := by
    rw [← Complex.sin_conj, Complex.conj_ofReal]
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [kickMat, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Matrix.empty_val', Matrix.one_apply, Fin.zero_eta, Fin.mk_one,
      Fin.isValue] <;>
    norm_num <;>
    simp only [hc, hs] <;>
    (first
      | linear_combination Complex.sin_sq_add_cos_sq (b : ℂ)
          - (Complex.sin (b : ℂ)) ^ 2 * Complex.I_sq
      | ring)

/-! ### The Ising phase -/

/-- The Ising-phase diagonal entry: `e^{-iJ}` on aligned spins, `e^{iJ}` on
anti-aligned. -/
noncomputable def phaseEntry (J : ℝ) (p : Fin 2 × Fin 2) : ℂ :=
  Complex.exp (Complex.I * J * (if p.1 = p.2 then -1 else 1))

/-- Each phase entry has unit modulus times its conjugate: `conj z * z = 1`. -/
lemma phaseEntry_star_mul_self (J : ℝ) (p : Fin 2 × Fin 2) :
    star (phaseEntry J p) * phaseEntry J p = 1 := by
  rw [phaseEntry, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  have : (starRingEnd ℂ) (Complex.I * J * (if p.1 = p.2 then -1 else 1))
      = -(Complex.I * J * (if p.1 = p.2 then -1 else 1)) := by
    split <;> simp [Complex.conj_I, Complex.conj_ofReal]
  rw [this, neg_add_cancel, Complex.exp_zero]

/-- The Ising phase `exp(-iJ σᶻ⊗σᶻ)` as a diagonal matrix. -/
noncomputable def phaseMat (J : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal (phaseEntry J)

/-- A unit-modulus diagonal is unitary. -/
lemma phaseMat_mem_unitaryGroup (J : ℝ) :
    phaseMat J ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [phaseMat, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  rw [show (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
      = Matrix.diagonal (fun _ => 1) from (Matrix.diagonal_one).symm]
  congr 1
  funext p
  exact phaseEntry_star_mul_self J p

/-! ### Kronecker products of unitaries -/

/-- The Kronecker product of unitaries is unitary
(`upstream-candidate(mathlib)`). -/
lemma kronecker_mem_unitaryGroup {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : A ∈ Matrix.unitaryGroup m ℂ) (hB : B ∈ Matrix.unitaryGroup n ℂ) :
    A ⊗ₖ B ∈ Matrix.unitaryGroup (m × n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hA hB ⊢
  rw [show star (A ⊗ₖ B) = (A ⊗ₖ B)ᴴ from rfl, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul]
  rw [show Aᴴ * A = 1 from hA, show Bᴴ * B = 1 from hB, Matrix.one_kronecker_one]

/-! ### The assembled Floquet operator -/

/-- The kicked-Ising Floquet unitary, as a unitary-group element (membership
by group multiplication). -/
noncomputable def kickedIsingU (J b : ℝ) :
    Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
  (⟨phaseMat J, phaseMat_mem_unitaryGroup J⟩ :
      Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ)
    * ⟨kickMat b ⊗ₖ kickMat b,
        kronecker_mem_unitaryGroup (kickMat_mem_unitaryGroup b)
          (kickMat_mem_unitaryGroup b)⟩

lemma kickedIsingU_val (J b : ℝ) :
    (kickedIsingU J b).val = phaseMat J * (kickMat b ⊗ₖ kickMat b) := rfl

/-- **The pilot model**: one kicked-Ising period as a `FloquetEvolution`,
through the generic matrix-dynamics seam. -/
noncomputable def kickedIsingFloquet (J b : ℝ) :
    FloquetEvolution (EuclideanSpace ℂ (Fin 2 × Fin 2)) :=
  FloquetEvolution.ofUnitaryMatrix (kickedIsingU J b)

/-! ### The accessibility-change witness at `b = π/2` -/

/-- The outer product `|v⟩⟨v|` on an arbitrary finite index (local pilot
helper; the staged `outerProduct` is `Fin N`-indexed). -/
noncomputable def pilotOuter {n : Type*} [Fintype n]
    (v : EuclideanSpace ℂ n) : Matrix n n ℂ :=
  Matrix.vecMulVec v.ofLp (star v.ofLp)

lemma pilotOuter_apply {n : Type*} [Fintype n]
    (v : EuclideanSpace ℂ n) (p q : n) :
    pilotOuter v p q = v.ofLp p * (starRingEnd ℂ) (v.ofLp q) := rfl

/-- Outer products are phase-invariant: `‖c‖ = 1` gives
`|cv⟩⟨cv| = |v⟩⟨v|`. -/
lemma pilotOuter_smul_of_norm_one {n : Type*} [Fintype n]
    {c : ℂ} (hc : ‖c‖ = 1) (v : EuclideanSpace ℂ n) :
    pilotOuter (c • v) = pilotOuter v := by
  ext p q
  rw [pilotOuter_apply, pilotOuter_apply]
  have hcv : ((c • v : EuclideanSpace ℂ n)).ofLp = c • v.ofLp := rfl
  rw [hcv]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  have hcc : c * (starRingEnd ℂ) c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  linear_combination v.ofLp p * (starRingEnd ℂ) (v.ofLp q) * hcc

/-- At `b = π/2` the kicked-Ising step sends `|00⟩` to a phase times `|11⟩`:
the kick flips both spins (up to `-i` each), the Ising phase multiplies by
`e^{-iJ}`. -/
lemma kickedIsing_step_e00 (J : ℝ) :
    (kickedIsingFloquet J (Real.pi / 2)).step
        (EuclideanSpace.single ((0 : Fin 2), (0 : Fin 2)) 1)
      = (-(phaseEntry J ((1 : Fin 2), (1 : Fin 2))))
          • EuclideanSpace.single ((1 : Fin 2), (1 : Fin 2)) 1 := by
  rw [kickedIsingFloquet, FloquetEvolution.ofUnitaryMatrix_step_apply]
  rw [Matrix.toLpLin_apply]
  congr 1
  ext p
  obtain ⟨p₁, p₂⟩ := p
  rw [kickedIsingU_val]
  fin_cases p₁ <;> fin_cases p₂ <;>
    simp [Matrix.mulVec, Matrix.mul_apply, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, phaseMat, Matrix.diagonal_apply, kickMat,
      Matrix.kroneckerMap_apply, PiLp.single_apply, Prod.ext_iff,
      Real.cos_pi_div_two, Real.sin_pi_div_two, Pi.smul_apply]

/-- The phase in `kickedIsing_step_e00` has unit modulus. -/
lemma kickedIsing_phase_norm (J : ℝ) :
    ‖-(phaseEntry J ((1 : Fin 2), (1 : Fin 2)))‖ = 1 := by
  rw [norm_neg, phaseEntry]
  rw [Complex.norm_exp]
  have : (Complex.I * J * (if ((1 : Fin 2), (1 : Fin 2)).1
      = ((1 : Fin 2), (1 : Fin 2)).2 then (-1 : ℂ) else 1)).re = 0 := by
    simp
  rw [this, Real.exp_zero]

/-- ★ **The accessibility-change witness.** At `b = π/2` the reduced
(first-qubit) state of the evolved `|00⟩` differs from that of `|00⟩`:
`Tr_B |ψ'⟩⟨ψ'| = |1⟩⟨1| ≠ |0⟩⟨0| = Tr_B |00⟩⟨00|`. Restricted accessibility
genuinely changes, while `inner_iterate_iterate` keeps every global overlap
exactly invariant — the pilot's "global information intact, local
accessibility moved" clause. -/
theorem kickedIsing_changes_marginal (J : ℝ) :
    QuantumInfo.partialTraceRight
        (pilotOuter ((kickedIsingFloquet J (Real.pi / 2)).step
          (EuclideanSpace.single ((0 : Fin 2), (0 : Fin 2)) 1)))
      ≠ QuantumInfo.partialTraceRight
          (pilotOuter (EuclideanSpace.single ((0 : Fin 2), (0 : Fin 2)) 1)) := by
  rw [kickedIsing_step_e00,
    pilotOuter_smul_of_norm_one (kickedIsing_phase_norm J)]
  intro h
  have h11 := congrFun (congrFun h (1 : Fin 2)) (1 : Fin 2)
  rw [QuantumInfo.partialTraceRight_apply, QuantumInfo.partialTraceRight_apply] at h11
  simp [pilotOuter_apply, PiLp.single_apply,
    Prod.ext_iff] at h11

/-! ### The `Fin 4` reindex: reaching the `Fin N` machinery -/

/-- Reindexing along an index equivalence preserves unitarity
(`upstream-candidate(mathlib)`). -/
lemma reindex_mem_unitaryGroup {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ≃ n) {M : Matrix m m ℂ}
    (hM : M ∈ Matrix.unitaryGroup m ℂ) :
    Matrix.reindex e e M ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hM ⊢
  rw [show star M = Mᴴ from rfl] at hM
  rw [show star (Matrix.reindex e e M) = (Matrix.reindex e e M)ᴴ from rfl,
    Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, hM, Matrix.submatrix_one_equiv]

/-- The kicked-Ising Floquet unitary reindexed to `Fin 4` along
`finProdFinEquiv`, so the concrete model reaches the `Fin N` ontic machinery
(`KSigma 4`, `floquetOnticStep`, the pilot closure) directly. -/
noncomputable def kickedIsingU₄ (J b : ℝ) : Matrix.unitaryGroup (Fin 4) ℂ :=
  ⟨Matrix.reindex (finProdFinEquiv (m := 2) (n := 2))
      (finProdFinEquiv (m := 2) (n := 2)) (kickedIsingU J b).val,
    reindex_mem_unitaryGroup _ (kickedIsingU J b).property⟩

end QuantumChaos
