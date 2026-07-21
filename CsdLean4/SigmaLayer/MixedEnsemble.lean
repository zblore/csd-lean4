import CsdLean4.SigmaLayer.MixedState

/-!
# SigmaLayer/MixedEnsemble: finite ensembles and the spectral ensemble decomposition (#8 A+B)

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)).

Extends the mixed-state layer (`SigmaLayer/MixedState.lean`, ledger T9) from the binary mixture `mix` to the two
missing pieces of the mixed-state / ensemble representation flagged as open in `specs/future-work.md`
(SL-T9 "remaining extensions"):

* **A — finite ensembles.** `ensemble w ρ = ∑ᵢ wᵢ ρᵢ` over a finite index type: a convex combination of
  arbitrarily many density operators is a density operator (`ensemble`), and the Born rule is affine over
  the whole ensemble, `Tr((∑ᵢ wᵢ ρᵢ) E) = ∑ᵢ wᵢ Tr(ρᵢ E)` (`traceForm_ensemble`) — the many-component
  generalisation of `traceForm_mix`.
* **B — the spectral ensemble decomposition.** Every density operator IS a convex ensemble of PURE states:
  `ρ = ∑ᵢ λᵢ |eᵢ⟩⟨eᵢ|` where the eigenvalues `λᵢ` form a probability distribution and the eigenvectors
  `eᵢ` are the pure components (`density_eq_eigen_ensemble`, `density_isPureEnsemble`). Hence the Born rule
  for any mixed state is the eigenvalue-weighted average of the pure Born rules
  (`traceForm_eq_pureEnsemble`) — the operational content of "mixed = classical mixture of pure".

Built on Mathlib's Hermitian spectral theorem (`Matrix.IsHermitian.spectral_theorem`,
`eigenvectorBasis`, `eigenvectorUnitary_apply`) and the repository's `LF2.DensityOperator` / `traceForm` /
`outerProduct` / `rankOneDensity`. This closes #8 pieces A and B (the statistical/QM-adapter side); the
ontic-side mixed representation on the unified model (#8 C) is separate.

References: `SigmaLayer/MixedState.lean` (`mix`, `traceForm_mix`, `IsPure`, `maximallyMixed`),
`LF2/BornWrapper.lean` (`DensityOperator`, `Effect`, `traceForm`, `outerProduct`, `rankOneDensity`,
`born_quadratic`); `specs/future-work.md` SL-T9.
-/

open Matrix Unitary
open scoped ComplexOrder

namespace CSD.SigmaLayer

open CSD.LF2

variable {N : ℕ} {ι : Type*} [Fintype ι]

/-! ### A — finite ensembles (many-component mixtures) -/

/-- **A finite ensemble of density operators.** For weights `w : ι → ℝ` forming a probability
distribution (`0 ≤ wᵢ`, `∑ wᵢ = 1`) and density operators `ρ : ι → DensityOperator N`, the convex
combination `∑ᵢ wᵢ ρᵢ` is a density operator: the classical mixture of arbitrarily many preparations. The
many-component generalisation of `mix`. -/
noncomputable def ensemble (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (ρ : ι → DensityOperator N) : DensityOperator N where
  M := ∑ i, (w i : ℂ) • (ρ i).M
  isHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun i _ =>
      (ρ i).isHermitian.smul (by rw [isSelfAdjoint_iff]; exact Complex.conj_ofReal (w i))
  nonneg := Matrix.posSemidef_sum _ fun i _ => (ρ i).nonneg.smul (by exact_mod_cast hw i)
  trace_one := by
    rw [Matrix.trace_sum]
    have h : ∀ i, ((w i : ℂ) • (ρ i).M).trace = (w i : ℂ) := fun i => by
      rw [Matrix.trace_smul, (ρ i).trace_one, smul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl fun i _ => h i, ← Complex.ofReal_sum, hsum, Complex.ofReal_one]

@[simp] theorem ensemble_M (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (ρ : ι → DensityOperator N) :
    (ensemble w hw hsum ρ).M = ∑ i, (w i : ℂ) • (ρ i).M := rfl

/-- **The Born rule is affine over the whole ensemble.** Mixing arbitrarily many preparations mixes the
outcome probabilities: `Tr((∑ᵢ wᵢ ρᵢ) E) = ∑ᵢ wᵢ Tr(ρᵢ E)`. The many-component `traceForm_mix`. -/
theorem traceForm_ensemble (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (ρ : ι → DensityOperator N) (E : Effect N) :
    traceForm (ensemble w hw hsum ρ) E = ∑ i, w i * traceForm (ρ i) E := by
  have htr : ((ensemble w hw hsum ρ).M * E.M).trace = ∑ i, (w i : ℂ) * ((ρ i).M * E.M).trace := by
    simp only [ensemble_M, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
      smul_eq_mul]
  simp only [traceForm, htr, RCLike.re_to_complex, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]

/-! ### B — the spectral ensemble decomposition (mixed = ensemble of pure) -/

/-- **Every density operator is the eigenvalue-weighted sum of its eigenvector projectors.**
`ρ = ∑ᵢ λᵢ |eᵢ⟩⟨eᵢ|` (`λᵢ` the eigenvalues, `eᵢ` the orthonormal eigenvectors). The matrix core of the
spectral ensemble decomposition, from the Hermitian spectral theorem. -/
theorem density_eq_eigen_ensemble (ρ : DensityOperator N) :
    ρ.M = ∑ i, (ρ.isHermitian.eigenvalues i : ℂ)
      • outerProduct (ρ.isHermitian.eigenvectorBasis i) := by
  set hA := ρ.isHermitian with hA_def
  conv_lhs => rw [hA.spectral_theorem, conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
    outerProduct, Matrix.vecMulVec_apply, smul_eq_mul, Function.comp_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply]
  exact Finset.sum_congr rfl fun k _ => (mul_assoc _ _ _).trans (mul_left_comm _ _ _)

/-- **The eigenvalues of a density operator form a probability distribution:** each is `≥ 0` and they sum
to `1` (nonnegativity from PSD, sum from trace one). So the spectral decomposition is a genuine convex
ensemble. -/
theorem eigenvalues_isProbability (ρ : DensityOperator N) :
    (∀ i, 0 ≤ ρ.isHermitian.eigenvalues i) ∧ (∑ i, ρ.isHermitian.eigenvalues i = 1) := by
  refine ⟨ρ.nonneg.eigenvalues_nonneg, ?_⟩
  have : (∑ i, (ρ.isHermitian.eigenvalues i : ℂ)) = 1 :=
    (ρ.isHermitian.trace_eq_sum_eigenvalues).symm.trans ρ.trace_one
  exact_mod_cast this

/-- The eigenvectors of a density operator are unit vectors (an orthonormal basis). -/
theorem eigenvectorBasis_norm_one (ρ : DensityOperator N) (i : Fin N) :
    ‖ρ.isHermitian.eigenvectorBasis i‖ = 1 :=
  ρ.isHermitian.eigenvectorBasis.orthonormal.norm_eq_one i

/-- **Every density operator is a convex ensemble of pure states.** There is a probability distribution
`w` and unit vectors `e` with `ρ = ∑ᵢ wᵢ |eᵢ⟩⟨eᵢ|` — the eigenvalues and eigenvectors. The precise sense
in which a mixed state is a classical mixture of pure preparations. -/
theorem density_isPureEnsemble (ρ : DensityOperator N) :
    ∃ (w : Fin N → ℝ) (e : Fin N → EuclideanSpace ℂ (Fin N)),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∀ i, ‖e i‖ = 1) ∧
      ρ.M = ∑ i, (w i : ℂ) • outerProduct (e i) :=
  ⟨ρ.isHermitian.eigenvalues, ρ.isHermitian.eigenvectorBasis,
    (eigenvalues_isProbability ρ).1, (eigenvalues_isProbability ρ).2,
    eigenvectorBasis_norm_one ρ, density_eq_eigen_ensemble ρ⟩

/-- **The Born rule of a mixed state is the eigenvalue-weighted average of the pure Born rules.** For any
effect `E`, `Tr(ρ E) = ∑ᵢ λᵢ Tr(|eᵢ⟩⟨eᵢ| E)` — measuring `E` on the mixture `ρ` gives the classical
average, over the eigen-ensemble, of measuring `E` on each pure eigenstate. Combines the spectral
decomposition (B) with the affine Born rule (A). -/
theorem traceForm_eq_pureEnsemble (ρ : DensityOperator N) (E : Effect N) :
    traceForm ρ E = ∑ i, ρ.isHermitian.eigenvalues i
      * traceForm (rankOneDensity (ρ.isHermitian.eigenvectorBasis i)
          (eigenvectorBasis_norm_one ρ i)) E := by
  have htr : (ρ.M * E.M).trace
      = ∑ i, (ρ.isHermitian.eigenvalues i : ℂ)
          * ((rankOneDensity (ρ.isHermitian.eigenvectorBasis i)
              (eigenvectorBasis_norm_one ρ i)).M * E.M).trace := by
    conv_lhs => rw [density_eq_eigen_ensemble ρ]
    simp only [rankOneDensity, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
      smul_eq_mul]
  simp only [traceForm, htr, RCLike.re_to_complex, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]

/-- **#8 A+B capstone: the mixed-state ensemble representation.** Finite convex ensembles of density
operators are density operators with an affine Born rule (`ensemble`, `traceForm_ensemble`); conversely
every density operator is a convex ensemble of pure states (`density_isPureEnsemble`), so its Born rule is
the eigenvalue-weighted average of pure Born rules (`traceForm_eq_pureEnsemble`). The pure Born rule
(`born_quadratic`) is the single-component extreme case. -/
theorem mixedEnsemble_capstone (ρ : DensityOperator N) (E : Effect N) :
    traceForm ρ E = ∑ i, ρ.isHermitian.eigenvalues i
      * traceForm (rankOneDensity (ρ.isHermitian.eigenvectorBasis i)
          (eigenvectorBasis_norm_one ρ i)) E :=
  traceForm_eq_pureEnsemble ρ E

end CSD.SigmaLayer
