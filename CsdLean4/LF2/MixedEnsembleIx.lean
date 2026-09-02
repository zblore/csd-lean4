/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF2.ReducedDensity
public import CsdLean4.SigmaLayer.MixedEnsemble

/-!
# LF2: Mixed-state Born rule and spectral ensemble on the indexed density type

**Category:** 2-Local (the operational density-operator layer).

The mixed-state ensemble content (`SigmaLayer/MixedEnsemble.lean`) was proved for
`DensityOperator N` (indexed by `Fin N`). This module ports it to the **composite
index-parametric** density type `DensityOperatorIx ι` (`LF2/ReducedDensity.lean`,
indexed by an arbitrary `[Fintype ι] [DecidableEq ι]`) — the type the bipartite /
composite interface (`SigmaLayer/CompositeInterface.lean`, target T9) uses via `reduced` /
`reducedLeft` partial traces. This closes the reported density-matrix gap: mixed-state
Born on the composite indexed type, not only on `Fin N`.

## Main results

* `DensityOperatorIx.traceForm` : the Born pairing `Tr(ρ E)` on the indexed type.
* `DensityOperatorIx.ensemble` + `traceForm_ensemble` : finite convex ensembles of
  indexed densities are indexed densities, with an **affine** Born rule.
* `DensityOperatorIx.eq_eigen_ensemble` + `eigenvalues_isProbability` : every indexed
  density is `∑ᵢ λᵢ |eᵢ⟩⟨eᵢ|` for a probability distribution `λ` (spectral theorem).
* `DensityOperatorIx.mixedEnsemble_capstone` : the mixed Born rule is the
  eigenvalue-weighted average of the pure Born rules — on the composite indexed type.

The proofs are the faithful `ι`-generalisation of the `Fin N` originals; every
underlying lemma (`Matrix.posSemidef_sum`, the Hermitian spectral theorem,
`trace_eq_sum_eigenvalues`, `eigenvalues_nonneg`) is stated for a general Fintype index.
-/

@[expose] public section

open Matrix Unitary
open scoped ComplexOrder

namespace CSD
namespace LF2
namespace DensityOperatorIx

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]

/-- **Born pairing on the indexed density type.** `Tr(ρ E)` as a real number. -/
noncomputable def traceForm (ρ : DensityOperatorIx ι) (E : Matrix ι ι ℂ) : ℝ :=
  RCLike.re ((ρ.M * E).trace)

/-! ### A — the affine convex ensemble -/

/-- **Finite convex ensemble of indexed densities.** For a probability distribution `w`
and indexed densities `ρ : κ → DensityOperatorIx ι`, the convex combination `∑ₖ wₖ ρₖ`
is an indexed density. -/
noncomputable def ensemble (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k, w k = 1)
    (ρ : κ → DensityOperatorIx ι) : DensityOperatorIx ι where
  M := ∑ k, (w k : ℂ) • (ρ k).M
  isHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun k _ =>
      (ρ k).isHermitian.smul (by rw [isSelfAdjoint_iff]; exact Complex.conj_ofReal (w k))
  nonneg := Matrix.posSemidef_sum _ fun k _ => (ρ k).nonneg.smul (by exact_mod_cast hw k)
  trace_one := by
    rw [Matrix.trace_sum]
    have h : ∀ k, ((w k : ℂ) • (ρ k).M).trace = (w k : ℂ) := fun k => by
      rw [Matrix.trace_smul, (ρ k).trace_one, smul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl fun k _ => h k, ← Complex.ofReal_sum, hsum, Complex.ofReal_one]

@[simp] theorem ensemble_M (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k, w k = 1)
    (ρ : κ → DensityOperatorIx ι) :
    (ensemble w hw hsum ρ).M = ∑ k, (w k : ℂ) • (ρ k).M := rfl

/-- **The Born rule is affine over the ensemble** (indexed type): mixing preparations
mixes the outcome probabilities, `Tr((∑ₖ wₖ ρₖ) E) = ∑ₖ wₖ Tr(ρₖ E)`. -/
theorem traceForm_ensemble (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k, w k = 1)
    (ρ : κ → DensityOperatorIx ι) (E : Matrix ι ι ℂ) :
    traceForm (ensemble w hw hsum ρ) E = ∑ k, w k * traceForm (ρ k) E := by
  have htr : ((ensemble w hw hsum ρ).M * E).trace = ∑ k, (w k : ℂ) * ((ρ k).M * E).trace := by
    simp only [ensemble_M, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
      smul_eq_mul]
  simp only [traceForm, htr, RCLike.re_to_complex, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Complex.mul_re]

/-! ### B — the spectral ensemble decomposition (mixed = ensemble of pure) -/

/-- **Rank-one (pure) indexed density** `|ψ⟩⟨ψ|` for a unit vector `ψ` — the
`DensityOperatorIx` twin of `rankOneDensity`, on the shared `outerProduct`
(`LF2/BornWrapper.lean`). -/
noncomputable def rankOne (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) : DensityOperatorIx ι where
  M           := outerProduct ψ
  isHermitian := outerProduct_isHermitian ψ
  nonneg      := outerProduct_posSemidef ψ
  trace_one   := outerProduct_trace_of_unit_norm ψ hψ

@[simp] theorem rankOne_M (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) :
    (rankOne ψ hψ).M = outerProduct ψ := rfl

/-- **The Born quadratic form on the indexed type:** at a pure preparation `|ψ⟩⟨ψ|` the trace
form of a rank-one projector `|φ⟩⟨φ|` is `|⟨ψ, φ⟩|²` — the `DensityOperatorIx` twin of
`born_quadratic`, from the shared matrix core `outerProduct_mul_outerProduct_trace`. -/
theorem traceForm_rankOne_outerProduct (ψ φ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) :
    (rankOne ψ hψ).traceForm (outerProduct φ) = ‖inner ℂ ψ φ‖ ^ 2 := by
  rw [traceForm, rankOne_M, outerProduct_mul_outerProduct_trace]
  exact Complex.ofReal_re _

/-- **Every indexed density is the eigenvalue-weighted sum of its eigenvector
projectors:** `ρ = ∑ᵢ λᵢ |eᵢ⟩⟨eᵢ|` — the `DensityOperatorIx` instance of
`IsHermitian.eq_eigen_outer` (the Hermitian spectral theorem, expanded entrywise). -/
theorem eq_eigen_ensemble (ρ : DensityOperatorIx ι) :
    ρ.M = ∑ i, (ρ.isHermitian.eigenvalues i : ℂ)
      • outerProduct (ρ.isHermitian.eigenvectorBasis i) :=
  IsHermitian.eq_eigen_outer ρ.isHermitian

/-- **The eigenvalues of an indexed density form a probability distribution.** -/
theorem eigenvalues_isProbability (ρ : DensityOperatorIx ι) :
    (∀ i, 0 ≤ ρ.isHermitian.eigenvalues i) ∧ (∑ i, ρ.isHermitian.eigenvalues i = 1) := by
  refine ⟨ρ.nonneg.eigenvalues_nonneg, ?_⟩
  have : (∑ i, (ρ.isHermitian.eigenvalues i : ℂ)) = 1 :=
    (ρ.isHermitian.trace_eq_sum_eigenvalues).symm.trans ρ.trace_one
  exact_mod_cast this

/-- **The mixed Born rule is the eigenvalue-weighted average of the pure Born rules**
(composite indexed type): `Tr(ρ E) = ∑ᵢ λᵢ Tr(|eᵢ⟩⟨eᵢ| E)`. Combines the spectral
decomposition with the affine Born rule — closing T9 on `DensityOperatorIx`. -/
theorem mixedEnsemble_capstone (ρ : DensityOperatorIx ι) (E : Matrix ι ι ℂ) :
    traceForm ρ E = ∑ i, ρ.isHermitian.eigenvalues i
      * RCLike.re ((outerProduct (ρ.isHermitian.eigenvectorBasis i) * E).trace) := by
  have htr : (ρ.M * E).trace
      = ∑ i, (ρ.isHermitian.eigenvalues i : ℂ)
          * ((outerProduct (ρ.isHermitian.eigenvectorBasis i)) * E).trace := by
    conv_lhs => rw [eq_eigen_ensemble ρ]
    simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  simp only [traceForm, htr, RCLike.re_to_complex, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]

end DensityOperatorIx
end LF2
end CSD
