/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF2.QuantumChannel
public import CsdLean4.LF2.MixedEnsembleIx

/-!
# LF2/ChoiConverse: Choi's theorem, the converse direction (PSD Choi ⇒ Kraus)

**Category:** 2-LF2 (the operational / Born layer).

`LF2/QuantumChannel.lean` proves the **easy** direction of Choi's theorem: a Kraus-form
channel has a positive-semidefinite Choi matrix (`choiMatrix_posSemidef`) — the
Choi–Jamiołkowski witness of complete positivity. This module proves the **converse**:
*every* PSD matrix on the composite index `Fin M × Fin N` is the Choi matrix of some Kraus
family. Together they close Choi's theorem: **a matrix is a valid Choi matrix iff it is
positive semidefinite** (`choi_iff_posSemidef`), i.e. the CP maps `Fin N → Fin M` are
exactly the PSD Choi matrices.

The construction is the spectral one. A PSD Choi matrix `C = ∑ᵢ λᵢ |eᵢ⟩⟨eᵢ|` with `λᵢ ≥ 0`
(Hermitian spectral theorem, `eq_eigen_outer`, reusing `MixedEnsembleIx.outerProduct`); the
`i`-th Kraus operator is the eigenvector `eᵢ` scaled by `√λᵢ` and **uncurried** from a
vector on `Fin M × Fin N` to a matrix `Fin M ← Fin N` (`krausOfChoi`). Because the Choi
matrix is indexed by the *product* `Fin M × Fin N`, this "vectorisation / reshape iso" is
definitional — an eigenvector already *is* the data of a Kraus operator — so the content is
entirely the `√λᵢ · √λᵢ = λᵢ` bookkeeping.

## Main results

* `choiOfKraus` — the Choi matrix of a *bare* Kraus family (no trace-preservation
  constraint), agreeing with `QuantumChannel.choiMatrix` on channels (`choiMatrix_eq`).
* `IsHermitian.eq_eigen_outer` — the entrywise spectral decomposition
  `C = ∑ᵢ λᵢ |eᵢ⟩⟨eᵢ|` of a Hermitian matrix (the bare-matrix generalisation of
  `DensityOperatorIx.eq_eigen_ensemble`).
* `krausOfChoi` + `choiOfKraus_krausOfChoi` — **the converse:** from a PSD `C`, the family
  `Kᵢ = √λᵢ · unvec(eᵢ)` reconstructs `C` as its Choi matrix.
* `choi_iff_posSemidef` — **Choi's theorem:** `C` is a Choi matrix of some Kraus family iff
  `C` is positive semidefinite.

Trace preservation (`∑ₖ Kₖ† Kₖ = 1`) is the orthogonal condition distinguishing a *channel*
from a general CP map; it corresponds to the partial trace of `C` over the output index
being the identity, and is not imposed here (this is the complete-positivity converse).

References: `LF2/QuantumChannel.lean` (`choiMatrix`, `choiMatrix_posSemidef`, the easy
direction); `LF2/MixedEnsembleIx.lean` (`outerProduct`, `eq_eigen_ensemble` — the spectral
idiom this reuses); `specs/BACKLOG.md` (M-tier "Choi converse"); `specs/future-work.md`.
-/

@[expose] public section

open Matrix Unitary
open scoped ComplexOrder

namespace CSD.LF2

variable {ι : Type*} [Fintype ι] {N M : ℕ}

/-- **The Choi matrix of a bare Kraus family** (no trace-preservation constraint):
`C (m,n)(m',n') = ∑ₖ Kₖ(m,n) · conj(Kₖ(m',n'))`. This is `QuantumChannel.choiMatrix`
detached from the `QuantumChannel` bundle, so the converse can quantify over Kraus families
without carrying the channel's trace-preservation hypothesis. -/
noncomputable def choiOfKraus (kraus : ι → Matrix (Fin M) (Fin N) ℂ) :
    Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ :=
  ∑ k, Matrix.vecMulVec (fun p => kraus k p.1 p.2) (star fun p => kraus k p.1 p.2)

@[simp] theorem choiOfKraus_apply (kraus : ι → Matrix (Fin M) (Fin N) ℂ)
    (p q : Fin M × Fin N) :
    choiOfKraus kraus p q = ∑ k, kraus k p.1 p.2 * star (kraus k q.1 q.2) := by
  simp only [choiOfKraus, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply]

/-- `QuantumChannel.choiMatrix` is `choiOfKraus` of the channel's Kraus family. -/
theorem QuantumChannel.choiMatrix_eq (Φ : QuantumChannel ι N M) :
    Φ.choiMatrix = choiOfKraus Φ.kraus := rfl

/-- **A bare Kraus family always has a PSD Choi matrix** (the easy direction, stated for
`choiOfKraus`). Each `vec(Kₖ) vec(Kₖ)†` is a rank-one PSD outer product; PSD is closed under
sums. -/
theorem choiOfKraus_posSemidef (kraus : ι → Matrix (Fin M) (Fin N) ℂ) :
    (choiOfKraus kraus).PosSemidef :=
  Matrix.posSemidef_sum _ fun _ _ => Matrix.posSemidef_vecMulVec_self_star _

/-- **Entrywise spectral decomposition of a Hermitian matrix** as an eigenvalue-weighted sum
of rank-one eigenvector projectors: `C = ∑ᵢ λᵢ |eᵢ⟩⟨eᵢ|`. The bare-matrix generalisation of
`DensityOperatorIx.eq_eigen_ensemble` (identical proof: the Hermitian spectral theorem in
diagonalised form, expanded entrywise). -/
theorem IsHermitian.eq_eigen_outer {n : Type*} [Fintype n] [DecidableEq n]
    {C : Matrix n n ℂ} (hC : C.IsHermitian) :
    C = ∑ i, (hC.eigenvalues i : ℂ) • DensityOperatorIx.outerProduct (hC.eigenvectorBasis i) := by
  conv_lhs => rw [hC.spectral_theorem, conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
    DensityOperatorIx.outerProduct, Matrix.vecMulVec_apply, smul_eq_mul, Function.comp_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply]
  exact Finset.sum_congr rfl fun k _ => (mul_assoc _ _ _).trans (mul_left_comm _ _ _)

/-- **The reconstructed Kraus family of a PSD Choi matrix.** The `i`-th operator is the
`i`-th eigenvector `eᵢ` of `C` scaled by `√λᵢ` and uncurried into a matrix: since `eᵢ` is a
vector on `Fin M × Fin N`, `Kᵢ m n = √λᵢ · eᵢ(m,n)` is exactly its reshape into a Kraus
operator `Fin M ← Fin N`. -/
noncomputable def krausOfChoi {C : Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ}
    (hC : C.PosSemidef) : (Fin M × Fin N) → Matrix (Fin M) (Fin N) ℂ :=
  fun i m n => (Real.sqrt (hC.isHermitian.eigenvalues i) : ℂ) * hC.isHermitian.eigenvectorBasis i (m, n)

/-- **Choi's theorem, converse direction:** the reconstructed Kraus family `krausOfChoi hC`
has Choi matrix exactly `C`. So every PSD matrix on `Fin M × Fin N` is the Choi matrix of a
Kraus family — a completely positive map is realised by its PSD Choi witness. The `i`-th
term contributes `(√λᵢ · eᵢ(p))·conj(√λᵢ · eᵢ(q)) = λᵢ · eᵢ(p)·conj(eᵢ(q))`, matching the
`i`-th term `λᵢ |eᵢ⟩⟨eᵢ|` of the spectral decomposition. -/
theorem choiOfKraus_krausOfChoi {C : Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ}
    (hC : C.PosSemidef) : choiOfKraus (krausOfChoi hC) = C := by
  conv_rhs => rw [IsHermitian.eq_eigen_outer hC.isHermitian]
  ext p q
  rw [choiOfKraus_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpos : 0 ≤ hC.isHermitian.eigenvalues i := hC.eigenvalues_nonneg i
  have hsq : (Real.sqrt (hC.isHermitian.eigenvalues i) : ℂ)
        * (Real.sqrt (hC.isHermitian.eigenvalues i) : ℂ)
      = (hC.isHermitian.eigenvalues i : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpos]
  have hstar : star (Real.sqrt (hC.isHermitian.eigenvalues i) : ℂ)
      = (Real.sqrt (hC.isHermitian.eigenvalues i) : ℂ) := Complex.conj_ofReal _
  simp only [krausOfChoi, Prod.mk.eta, star_mul', hstar, Matrix.smul_apply,
    DensityOperatorIx.outerProduct, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [mul_mul_mul_comm, hsq]

/-- **Choi's theorem (finite dimensions).** A matrix `C` on the composite index
`Fin M × Fin N` is the Choi matrix of some Kraus family — equivalently, is the
Choi–Jamiołkowski image of some completely positive map `Fin N → Fin M` — **iff** it is
positive semidefinite. The forward direction is `choiOfKraus_posSemidef`; the converse is
`choiOfKraus_krausOfChoi`, which additionally exhibits the Kraus family explicitly. -/
theorem choi_iff_posSemidef (C : Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ) :
    (∃ (ι : Type) (_ : Fintype ι) (kraus : ι → Matrix (Fin M) (Fin N) ℂ),
        choiOfKraus kraus = C) ↔ C.PosSemidef := by
  constructor
  · rintro ⟨ι, _, kraus, rfl⟩
    exact choiOfKraus_posSemidef kraus
  · intro hC
    exact ⟨Fin M × Fin N, inferInstance, krausOfChoi hC, choiOfKraus_krausOfChoi hC⟩

end CSD.LF2
