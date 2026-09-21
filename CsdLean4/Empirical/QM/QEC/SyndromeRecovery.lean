/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.BitFlipChannel
public import CsdLean4.Empirical.QM.QEC.ErrorDiscretization
public import CsdLean4.Mathlib.QuantumInfo.ChannelComp

/-!
# Empirical/QM: syndrome-conditioned recovery as one channel

**Category:** 3-Local. QM-validity layer (matrix algebra over the K2 `Channel` layer, no CSD
content); companion of `ThreeQubit.lean` and `BitFlipChannel.lean`.

`ThreeQubit.lean` proves the bit-flip code corrects each single error *branch by branch*: the
syndrome identifies `Xⱼ`, and `Xⱼ` undoes it. The operational statement of error correction is
stronger: a **single CPTP map** — measure the syndrome, then apply the correction the outcome
names — returns every code state, mixed or pure, from the **mixed** post-error state. This file
builds that channel and proves it.

* `codeProj` — the projector onto the codespace `span{|000⟩, |111⟩}`, as `|000⟩⟨000| + |111⟩⟨111|`
  (`kron3` of the qubit projectors `q0`, `q1`; the `kron3` linearity of `ErrorDiscretization.lean`);
* `errorOp` — the four errors `{I, X₁, X₂, X₃}`; `syndromeProj k = Eₖ P₀ Eₖ` — the projector onto
  the `k`-th error subspace `Eₖ · C`. ★ `syndromeProj_mul_syndromeProj` (the four are pairwise
  orthogonal projectors) and ★ `sum_syndromeProj` (they sum to `1`): **the syndrome is a
  projective measurement on the register**;
* `syndromeProj_errorOp_logical`, `syndromeProj_errorOp_logical_of_ne` — the errored codeword
  `Eₖ ψ_L` lies in the `k`-th syndrome subspace and in no other;
* `recoveryChannel` — the **syndrome-conditioned recovery**, a `Channel` with Kraus operators
  `Eₖ Pₖ` ("if the syndrome is `k`, apply `Eₖ`"); trace preservation is `∑ₖ Pₖ = 1`;
* `singleFlipChannel q` — the mixed single-error channel `ρ ↦ ∑ₖ qₖ Eₖ ρ Eₖ` for any weights
  `qₖ ≥ 0`, `∑ qₖ = 1` (the discretised error, all four branches at once);
* ★★ `recoveryChannel_apply_singleFlipChannel_apply` — **recovery is exact on the code, as one
  channel on the mixed state**: for every operator `ρ` supported on the codespace
  (`P₀ ρ P₀ = ρ`, in particular every mixed code state), `R (N_q ρ) = ρ`; and
  `comp_recoveryChannel_singleFlipChannel_apply`, the same for the composite channel `R ∘ N_q`
  of `ChannelComp.lean`.

The proof is the Knill–Laflamme mechanism in its simplest instance: `Pⱼ Eₖ P₀ = δⱼₖ Pₖ Eₖ` (the
error `Eₖ` carries the code onto the `k`-th syndrome subspace and nowhere else), so the double
Kraus sum collapses to its diagonal, and on the diagonal `Eₖ Pₖ Eₖ = P₀`.

What is not here: errors outside the single-flip set (two flips are miscorrected — the code's
distance is 3). The independent-noise channel `(bit-flip_p)^{⊗3}`, whose double- and triple-flip
branches the code mis-corrects into the logical flip, is `IndependentNoise.lean`
(`recoveryChannel_apply_indepFlipChannel_apply`: the `3p² − 2p³` residual);
`singleFlipChannel` is its correctable part with free weights.

## Source

Shor 1995, *Phys. Rev. A* **52**, R2493; Knill–Laflamme 1997, *Phys. Rev. A* **55**, 900
(the correction conditions; the recovery channel `∑ₖ Eₖ Pₖ · Pₖ Eₖᴴ`).
-/

@[expose] public section

open Matrix QuantumInfo
open scoped ComplexOrder Kronecker

namespace CSD
namespace Empirical
namespace QM
namespace QEC

/-! ### The qubit projectors, the code projector, the errors -/

/-- `|0⟩⟨0|`. -/
def q0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- `|1⟩⟨1|`. -/
def q1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]

@[simp] lemma q0_mul_q0 : q0 * q0 = q0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [q0, Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma q1_mul_q1 : q1 * q1 = q1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [q1, Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma q0_mul_q1 : q0 * q1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [q0, q1, Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma q1_mul_q0 : q1 * q0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [q0, q1, Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma pX_mul_q0_mul_pX : pX * q0 * pX = q1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pX, q0, q1, Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma pX_mul_q1_mul_pX : pX * q1 * pX = q0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pX, q0, q1, Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma q0_conjTranspose : q0ᴴ = q0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [q0]
@[simp] lemma q1_conjTranspose : q1ᴴ = q1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [q1]
lemma q0_add_q1 : q0 + q1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [q0, q1]

lemma kron3_conjTranspose (M N P : Matrix (Fin 2) (Fin 2) ℂ) :
    (kron3 M N P)ᴴ = kron3 Mᴴ Nᴴ Pᴴ := by
  simp only [kron3, Matrix.conjTranspose_kronecker]

@[simp] lemma kron3_zero_left (N P : Matrix (Fin 2) (Fin 2) ℂ) : kron3 0 N P = 0 := by
  simp only [kron3, Matrix.zero_kronecker]

@[simp] lemma kron3_zero_mid (M P : Matrix (Fin 2) (Fin 2) ℂ) : kron3 M 0 P = 0 := by
  simp only [kron3, Matrix.zero_kronecker, Matrix.kronecker_zero]

@[simp] lemma kron3_zero_right (M N : Matrix (Fin 2) (Fin 2) ℂ) : kron3 M N 0 = 0 := by
  simp only [kron3, Matrix.kronecker_zero]

/-- **The code projector** `P₀ = |000⟩⟨000| + |111⟩⟨111|` onto the codespace `span{|000⟩, |111⟩}`. -/
def codeProj : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  kron3 q0 q0 q0 + kron3 q1 q1 q1

lemma codeProj_conjTranspose : codeProjᴴ = codeProj := by
  simp only [codeProj, Matrix.conjTranspose_add, kron3_conjTranspose, q0_conjTranspose,
    q1_conjTranspose]

/-- The four errors `{I, X₁, X₂, X₃}` as operators on the three-qubit register. -/
noncomputable def errorOp : Fin 4 → Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  ![1, X1, X2, X3]

@[simp] lemma errorOp_mul_self (k : Fin 4) : errorOp k * errorOp k = 1 := by
  fin_cases k <;> simp [errorOp]

lemma errorOp_conjTranspose (k : Fin 4) : (errorOp k)ᴴ = errorOp k := by
  fin_cases k <;> simp [errorOp, X1, X2, X3, kron3_conjTranspose]

/-- `Eₖ (Eₖ A Eₖ) Eₖ = A`: conjugating twice by a self-inverse error is the identity. -/
lemma errorOp_conj_conj (k : Fin 4) (A : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) :
    errorOp k * (errorOp k * A * errorOp k) * errorOp k = A := by
  have h : errorOp k * (errorOp k * A * errorOp k) * errorOp k
      = (errorOp k * errorOp k) * A * (errorOp k * errorOp k) := by
    simp only [Matrix.mul_assoc]
  rw [h, errorOp_mul_self, Matrix.one_mul, Matrix.mul_one]

/-! ### The syndrome projectors: a projective measurement on the register -/

/-- **The `k`-th syndrome projector** `Pₖ = Eₖ P₀ Eₖ`, the projector onto the error subspace
`Eₖ · C`. -/
noncomputable def syndromeProj (k : Fin 4) :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  errorOp k * codeProj * errorOp k

/-- The four syndrome projectors in closed form: each is the sum of two computational-basis
projectors, and the four pairs partition the eight basis states. -/
lemma syndromeProj_eq (k : Fin 4) :
    syndromeProj k
      = ![codeProj, kron3 q1 q0 q0 + kron3 q0 q1 q1, kron3 q0 q1 q0 + kron3 q1 q0 q1,
          kron3 q0 q0 q1 + kron3 q1 q1 q0] k := by
  fin_cases k <;>
    simp [syndromeProj, errorOp, codeProj, X1, X2, X3, Matrix.mul_add, Matrix.add_mul, kron3_mul]

lemma syndromeProj_conjTranspose (k : Fin 4) : (syndromeProj k)ᴴ = syndromeProj k := by
  simp only [syndromeProj, Matrix.conjTranspose_mul, errorOp_conjTranspose, codeProj_conjTranspose,
    Matrix.mul_assoc]

/-- ★ **The syndrome projectors are pairwise orthogonal projectors.** -/
theorem syndromeProj_mul_syndromeProj (j k : Fin 4) :
    syndromeProj j * syndromeProj k = if j = k then syndromeProj k else 0 := by
  fin_cases j <;> fin_cases k <;>
    simp [syndromeProj_eq, codeProj, Matrix.mul_add, Matrix.add_mul, kron3_mul]

lemma syndromeProj_mul_self (k : Fin 4) : syndromeProj k * syndromeProj k = syndromeProj k := by
  simp [syndromeProj_mul_syndromeProj]

lemma syndromeProj_mul_syndromeProj_of_ne {j k : Fin 4} (h : j ≠ k) :
    syndromeProj j * syndromeProj k = 0 := by
  simp [syndromeProj_mul_syndromeProj, h]

/-- ★ **The syndrome projectors sum to the identity**: the syndrome is a complete projective
measurement on the register. -/
theorem sum_syndromeProj : ∑ k, syndromeProj k = 1 := by
  have h1 : (1 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
      = kron3 (q0 + q1) (q0 + q1) (q0 + q1) := by rw [q0_add_q1, kron3_one_one_one]
  rw [Fin.sum_univ_four, h1]
  simp [syndromeProj_eq, codeProj, kron3_add_left, kron3_add_mid, kron3_add_right]
  abel

/-! ### The errored codewords lie in their syndrome subspaces -/

/-- `P₀ ψ_L = ψ_L`: the code projector fixes the logical states. -/
lemma codeProj_logical (a b : ℂ) : Matrix.toEuclideanLin codeProj (logical a b) = logical a b := by
  ext i
  simp only [Matrix.toLpLin_apply, logical, codeProj, kron3, q0, q1]
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      EuclideanSpace.single, Matrix.kroneckerMap_apply, Matrix.add_apply, Prod.ext_iff]

/-- The errored codeword `Eₖ ψ_L` lies in the `k`-th syndrome subspace. -/
theorem syndromeProj_errorOp_logical (k : Fin 4) (a b : ℂ) :
    Matrix.toEuclideanLin (syndromeProj k) (Matrix.toEuclideanLin (errorOp k) (logical a b))
      = Matrix.toEuclideanLin (errorOp k) (logical a b) := by
  rw [← tel_mul, syndromeProj, Matrix.mul_assoc, errorOp_mul_self, Matrix.mul_one, tel_mul,
    codeProj_logical]

/-- The errored codeword `Eₖ ψ_L` lies in no other syndrome subspace. -/
theorem syndromeProj_errorOp_logical_of_ne {j k : Fin 4} (h : j ≠ k) (a b : ℂ) :
    Matrix.toEuclideanLin (syndromeProj j) (Matrix.toEuclideanLin (errorOp k) (logical a b)) = 0 := by
  rw [← syndromeProj_errorOp_logical k a b, ← tel_mul, syndromeProj_mul_syndromeProj_of_ne h,
    map_zero, LinearMap.zero_apply]

/-! ### The recovery channel and the single-error channel -/

/-- **The syndrome-conditioned recovery, as one channel**: Kraus operators `Eₖ Pₖ` — project onto the
`k`-th syndrome subspace, then apply the correction `Eₖ` the syndrome names. Trace preservation is
`∑ₖ Pₖ Eₖ Eₖ Pₖ = ∑ₖ Pₖ = 1`. -/
noncomputable def recoveryChannel :
    Channel (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) (Fin 4) where
  kraus k := errorOp k * syndromeProj k
  tp := by
    simp only [Matrix.conjTranspose_mul, syndromeProj_conjTranspose, errorOp_conjTranspose]
    calc ∑ k, syndromeProj k * errorOp k * (errorOp k * syndromeProj k)
        = ∑ k, syndromeProj k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Matrix.mul_assoc, ← Matrix.mul_assoc (errorOp k), errorOp_mul_self, Matrix.one_mul,
            syndromeProj_mul_self]
      _ = 1 := sum_syndromeProj

@[simp] lemma recoveryChannel_kraus (k : Fin 4) :
    recoveryChannel.kraus k = errorOp k * syndromeProj k := rfl

/-- **The mixed single-error channel** `ρ ↦ ∑ₖ qₖ Eₖ ρ Eₖ`: the four discretised error branches at
once, with any weights `qₖ ≥ 0`, `∑ₖ qₖ = 1`. -/
noncomputable def singleFlipChannel (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) :
    Channel (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) (Fin 4) where
  kraus k := ((Real.sqrt (q k) : ℝ) : ℂ) • errorOp k
  tp := by
    have h : ∀ k, (((Real.sqrt (q k) : ℝ) : ℂ) • errorOp k)ᴴ * (((Real.sqrt (q k) : ℝ) : ℂ) • errorOp k)
        = ((q k : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) := by
      intro k
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        errorOp_conjTranspose, errorOp_mul_self, Complex.star_def, Complex.conj_ofReal,
        ← Complex.ofReal_mul, Real.mul_self_sqrt (hq0 k)]
    simp only [h, ← Finset.sum_smul, ← Complex.ofReal_sum, hq1, Complex.ofReal_one, one_smul]

lemma singleFlipChannel_apply (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1)
    (ρ : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) :
    (singleFlipChannel q hq0 hq1).apply ρ = ∑ k, ((q k : ℝ) : ℂ) • (errorOp k * ρ * errorOp k) := by
  simp only [Channel.apply_def, singleFlipChannel, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, errorOp_conjTranspose, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Real.mul_self_sqrt (hq0 k)]

/-! ### The Knill–Laflamme collapse -/

/-- `Eₖ P₀ = Pₖ Eₖ`: the error carries the code projector onto the `k`-th syndrome projector. -/
lemma errorOp_mul_codeProj (k : Fin 4) : errorOp k * codeProj = syndromeProj k * errorOp k := by
  rw [syndromeProj, Matrix.mul_assoc, errorOp_mul_self, Matrix.mul_one]

/-- `P₀ Eₖ = Eₖ Pₖ`. -/
lemma codeProj_mul_errorOp (k : Fin 4) : codeProj * errorOp k = errorOp k * syndromeProj k := by
  rw [syndromeProj, ← Matrix.mul_assoc, ← Matrix.mul_assoc, errorOp_mul_self, Matrix.one_mul]

/-- `Eₖ Pₖ Eₖ = P₀`. -/
lemma errorOp_mul_syndromeProj_mul_errorOp (k : Fin 4) :
    errorOp k * (syndromeProj k * errorOp k) = codeProj := by
  rw [syndromeProj, ← Matrix.mul_assoc, errorOp_conj_conj]

/-- The Kraus term of `R ∘ N_q` indexed by `(j, k)`, on a code-supported operator: it is the
identity for `j = k` and vanishes otherwise (`Pⱼ Eₖ P₀ = δⱼₖ Pₖ Eₖ`). -/
lemma recovery_term (j k : Fin 4) (ρ : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) :
    errorOp j * syndromeProj j * (errorOp k * (codeProj * ρ * codeProj) * errorOp k)
        * (syndromeProj j * errorOp j)
      = if j = k then codeProj * ρ * codeProj else 0 := by
  have hL : syndromeProj j * (errorOp k * codeProj)
      = (if j = k then syndromeProj k else 0) * errorOp k := by
    rw [errorOp_mul_codeProj, ← Matrix.mul_assoc, syndromeProj_mul_syndromeProj]
  have hR : (codeProj * errorOp k) * syndromeProj j
      = errorOp k * (if j = k then syndromeProj k else 0) := by
    rw [codeProj_mul_errorOp, Matrix.mul_assoc, syndromeProj_mul_syndromeProj k j]
    by_cases h : j = k
    · subst h; simp
    · simp [h, Ne.symm h]
  calc errorOp j * syndromeProj j * (errorOp k * (codeProj * ρ * codeProj) * errorOp k)
          * (syndromeProj j * errorOp j)
      = errorOp j * (syndromeProj j * (errorOp k * codeProj)) * ρ
          * ((codeProj * errorOp k) * syndromeProj j) * errorOp j := by
        simp only [Matrix.mul_assoc]
    _ = errorOp j * ((if j = k then syndromeProj k else 0) * errorOp k) * ρ
          * (errorOp k * (if j = k then syndromeProj k else 0)) * errorOp j := by
        rw [hL, hR]
    _ = if j = k then codeProj * ρ * codeProj else 0 := by
        by_cases h : j = k
        · subst h
          simp only [if_true]
          rw [show errorOp j * (syndromeProj j * errorOp j) * ρ * (errorOp j * syndromeProj j)
                * errorOp j
              = (errorOp j * (syndromeProj j * errorOp j)) * ρ
                * (errorOp j * (syndromeProj j * errorOp j)) by simp only [Matrix.mul_assoc],
            errorOp_mul_syndromeProj_mul_errorOp]
        · simp [h]

/-- ★★ **Syndrome-conditioned recovery is exact on the code, as one channel on the mixed state.**
For every operator `ρ` supported on the codespace (`P₀ ρ P₀ = ρ` — every code state, pure or mixed)
and every single-error mixture `N_q`, the recovery channel returns `ρ` from the mixed post-error
state: `R (N_q ρ) = ρ`. -/
theorem recoveryChannel_apply_singleFlipChannel_apply (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k)
    (hq1 : ∑ k, q k = 1) (ρ : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (hρ : codeProj * ρ * codeProj = ρ) :
    recoveryChannel.apply ((singleFlipChannel q hq0 hq1).apply ρ) = ρ := by
  conv_lhs => rw [← hρ]
  rw [singleFlipChannel_apply, Channel.apply_def]
  simp only [recoveryChannel_kraus, Matrix.conjTranspose_mul, syndromeProj_conjTranspose,
    errorOp_conjTranspose, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [Finset.sum_comm]
  simp only [recovery_term, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_smul, ← Complex.ofReal_sum, hq1, Complex.ofReal_one, one_smul, hρ]

/-- The composite channel `R ∘ N_q` (`Channel.comp`) is the identity on the code. -/
theorem comp_recoveryChannel_singleFlipChannel_apply (q : Fin 4 → ℝ) (hq0 : ∀ k, 0 ≤ q k)
    (hq1 : ∑ k, q k = 1) (ρ : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (hρ : codeProj * ρ * codeProj = ρ) :
    (recoveryChannel.comp (singleFlipChannel q hq0 hq1)).apply ρ = ρ := by
  rw [Channel.comp_apply, recoveryChannel_apply_singleFlipChannel_apply q hq0 hq1 ρ hρ]

end QEC
end QM
end Empirical
end CSD
