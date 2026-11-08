/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpacePoissonBracket
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# Eigenstates are the critical points of an expectation value on `ℂℙⁿ`

**TERM-SCOPE(Hamiltonian)** — this module uses the vector-field sense of "Hamiltonian";
`specs/TERMS.md` records what is backed.

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold.Instances`).
BACKLOG #326 (geometric QM, item 3 of the 2026-11-08 plan).

In geometric quantum mechanics the spectrum of an observable is read off its expectation value:
`⟨A⟩` is a smooth function on `ℂℙⁿ`, its critical points are exactly the eigenlines of `A`, the
value at a critical point is the eigenvalue, and the maximum and minimum of `⟨A⟩` are the largest
and smallest eigenvalues.

## Zeros of a Hamiltonian vector field

* ★ `IsHamiltonianVectorField.eq_zero_iff_mfderiv_eq_zero` — for a symplectic form, **`X_H`
  vanishes exactly where `dH` does**.

## The Schrödinger field vanishes on the eigenlines

* `insertZeroCLM_injective`; ★ `schrodingerChartField_eq_zero_iff` — in a chart, the field of `A`
  vanishes at `w` exactly when `insertOne i w` is an eigenvector of `A`;
* ★★ `schrodingerField_eq_zero_iff` — **`X_A(p) = 0` exactly when `p` is an eigenline of `A`**
  (any matrix `A`).

## Critical points and critical values

* `expectation_eq_of_eigen` — at an eigenline with real eigenvalue `μ`, `⟨A⟩ = μ`;
  `eigen_eq_expectation_smul` — for Hermitian `A`, the eigenvalue at an eigenline is `⟨A⟩`;
* ★★ `mfderiv_expectation_eq_zero_iff_schrodingerField` — `d⟨A⟩_p = 0 ⟺ X_A(p) = 0`;
* ★★★ `mfderiv_expectation_eq_zero_iff` — **`d⟨A⟩_p = 0 ⟺ A ψ = ⟨A⟩_p ψ`** for a representative
  `ψ` of `p`: the critical points are the eigenlines, with the eigenvalue as critical value;
* ★★★ `criticalValues_eq_eigenvalues` — **the critical values of `⟨A⟩` are exactly the real
  eigenvalues of `A` with an eigenline**.

## Mathlib's eigenvalues (#334)

* ★★ `setOf_eigenline_eq_range_eigenvalues` — **the eigenvalues with an eigenline are
  `Set.range hA.eigenvalues`** (through `spectrum_eq_image_range` one way, the orthonormal
  eigenvector basis the other);
* ★★ `criticalValues_eq_range_eigenvalues`, ★★ `exists_isGreatest_range_eigenvalues`,
  ★★ `exists_isLeast_range_eigenvalues` — the critical values, maximum and minimum of `⟨A⟩` in
  Mathlib's terms.

## Maximum and minimum

* ★ `mfderiv_expectation_eq_zero_of_isMaxOn`, `mfderiv_expectation_eq_zero_of_isMinOn` — Fermat's
  rule on `ℂℙⁿ`, through the chart Hamiltonian;
* ★★★ `exists_isGreatest_eigenvalues`, ★★★ `exists_isLeast_eigenvalues` — **`⟨A⟩` attains its
  maximum (minimum) at an eigenline, and the value is the largest (smallest) eigenvalue**.

## Honest scope

⚠️ **Eigenvalues with an eigenline.** The eigenvalue sets here are
`{μ : ℝ | ∃ p, A p.rep = μ p.rep}`; for Hermitian `A`, `setOf_eigenline_eq_range_eigenvalues`
(#334) identifies the set with `Set.range hA.eigenvalues`, Mathlib's eigenvalues. A set does not
see multiplicities.

⚠️ **Critical points, not their indices.** Morse theory of `⟨A⟩` (the Hessian at an eigenline and
its index, the count of eigenvalues below) is not here.

## References

T. W. B. Kibble, Commun. Math. Phys. 65 (1979) 189, § 3; A. Ashtekar, T. A. Schilling, in *On
Einstein's Path* (1999) 23, § 3.2 (eigenstates as critical points of expectation functions);
`Instances/ProjectiveSpacePoissonBracket.lean` (#325),
`Instances/ProjectiveSpaceSchrodingerFlow.lean` (G13); `specs/BACKLOG.md` #326;
`specs/future-work.md`.
-/

@[expose] public section

open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix Matrix.Norms.L2Operator
open Kahler DifferentialForm

noncomputable section

namespace DifferentialForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  {β : DifferentialForm (𝓘(ℝ, E)) M ∞ (Fin 2) ℝ}

omit [FiniteDimensional ℝ E] in
/-- ★ **For a symplectic form, a Hamiltonian vector field vanishes exactly where `dH` does.** -/
theorem IsHamiltonianVectorField.eq_zero_iff_mfderiv_eq_zero
    {X : ∀ x : M, TangentSpace (𝓘(ℝ, E)) x} {H : M → ℝ}
    (h : IsHamiltonianVectorField (fun x => β x) X H) (hβ : β.IsSymplectic) (x : M) :
    X x = 0 ↔ mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) H x = 0 := by
  constructor
  · intro hX
    ext v
    rw [← h x v, hX]
    exact apply_zero_left (fun x => β x) x v
  · intro hd
    by_contra hX
    obtain ⟨w, hw⟩ := hβ.nondegenerate x (X x) hX
    apply hw
    rw [h x w, hd]
    rfl

end DifferentialForm

namespace Projectivization

variable {n : ℕ}

/-! ### The Schrödinger field vanishes on the eigenlines -/

theorem insertZeroCLM_injective (i : Fin (n + 1)) :
    Function.Injective (insertZeroCLM (n := n) i) := by
  intro u u' h
  funext j
  have := congrArg (fun v : Ambient n => v (i.succAbove j)) h
  simpa [insertZeroCLM_apply] using this

/-- ★ **In a chart, the Schrödinger field of `A` vanishes exactly at the eigenvectors of `A`.** -/
theorem schrodingerChartField_eq_zero_iff (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) (w : Fin n → ℂ) :
    schrodingerChartField A i w = 0
      ↔ ∃ c : ℂ, Matrix.toEuclideanLin A (insertOne i w) = c • insertOne i w := by
  have hlift : schrodingerChartField A i w = 0
      ↔ Matrix.toEuclideanLin A (insertOne i w)
          = (A *ᵥ (insertOne i w).ofLp) i • insertOne i w := by
    rw [← (insertZeroCLM_injective i).eq_iff, map_zero, insertZeroCLM_schrodingerChartField,
      smul_eq_zero, sub_eq_zero]
    simp [Complex.I_ne_zero]
  rw [hlift]
  refine ⟨fun h => ⟨_, h⟩, fun ⟨c, hc⟩ => ?_⟩
  have hi : (A *ᵥ (insertOne i w).ofLp) i = c := by
    have := congrArg (fun v : Ambient n => v i) hc
    simpa using this
  rw [hi, hc]

/-- ★★ **The Schrödinger field of `A` vanishes exactly on the eigenlines of `A`.** -/
theorem schrodingerField_eq_zero_iff (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (p : ℙ ℂ (Ambient n)) :
    schrodingerField A p = 0 ↔ ∃ c : ℂ, Matrix.toEuclideanLin A p.rep = c • p.rep := by
  have hp := idx_spec p
  show schrodingerChartField A (idx p) (chartFun (idx p) p) = 0 ↔ _
  rw [schrodingerChartField_eq_zero_iff, insertOne_chartFun _ _ hp]
  have ha : (p.rep (idx p))⁻¹ ≠ 0 := inv_ne_zero hp
  refine exists_congr fun c => ?_
  rw [map_smul, smul_comm c]
  exact (smul_right_injective _ ha).eq_iff

/-! ### Critical points and critical values -/

/-- At an eigenline with real eigenvalue `μ`, `⟨A⟩ = μ`. -/
theorem expectation_eq_of_eigen {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {p : ℙ ℂ (Ambient n)}
    {μ : ℝ} (h : Matrix.toEuclideanLin A p.rep = (μ : ℂ) • p.rep) : expectation A p = μ := by
  have hψ : ‖p.rep‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (rep_nonzero p))
  unfold expectation
  rw [h, inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.re_ofReal_mul]
  norm_cast
  rw [← RCLike.re_to_complex, RCLike.ofReal_re, mul_div_assoc, div_self hψ, mul_one]

/-- For Hermitian `A`, the eigenvalue at an eigenline is the expectation value. -/
theorem eigen_eq_expectation_smul {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : A.IsHermitian)
    {p : ℙ ℂ (Ambient n)} {c : ℂ} (h : Matrix.toEuclideanLin A p.rep = c • p.rep) :
    Matrix.toEuclideanLin A p.rep = (expectation A p : ℂ) • p.rep := by
  have hT := Matrix.isSymmetric_toEuclideanLin_iff.2 hA
  have hψ : (‖p.rep‖ ^ 2 : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 (rep_nonzero p))
  -- `c` is real
  have hreal : (starRingEnd ℂ) c = c := by
    have hs := hT p.rep p.rep
    rw [h, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K] at hs
    exact mul_right_cancel₀ hψ hs
  have hc : c = (c.re : ℂ) := (Complex.conj_eq_iff_re.1 hreal).symm
  rw [hc] at h
  rw [expectation_eq_of_eigen h, ← hc, h, ← hc]

/-- ★★ **`d⟨A⟩_p = 0` exactly where the Schrödinger field of `A` vanishes.** -/
theorem mfderiv_expectation_eq_zero_iff_schrodingerField {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) (p : ℙ ℂ (Ambient n)) :
    mfderiv (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ ℝ) (expectation A) p = 0
      ↔ schrodingerField A p = 0 := by
  rw [← (expectation_isHamiltonianVectorField hA).eq_zero_iff_mfderiv_eq_zero
    (fsForm_isSymplectic n) p, smul_eq_zero]
  norm_num

/-- ★★★ **The critical points of `⟨A⟩` are the eigenlines of `A`, and the critical value is the
eigenvalue**: `d⟨A⟩_p = 0 ⟺ A ψ = ⟨A⟩_p ψ` for the representative `ψ` of `p`. -/
theorem mfderiv_expectation_eq_zero_iff {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) (p : ℙ ℂ (Ambient n)) :
    mfderiv (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ ℝ) (expectation A) p = 0
      ↔ Matrix.toEuclideanLin A p.rep = (expectation A p : ℂ) • p.rep := by
  rw [mfderiv_expectation_eq_zero_iff_schrodingerField hA, schrodingerField_eq_zero_iff]
  exact ⟨fun ⟨_, hc⟩ => eigen_eq_expectation_smul hA hc, fun h => ⟨_, h⟩⟩

/-- ★★★ **The critical values of `⟨A⟩` are exactly the real eigenvalues of `A`** (with an
eigenline). -/
theorem criticalValues_eq_eigenvalues {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) :
    {μ : ℝ | ∃ p : ℙ ℂ (Ambient n), mfderiv (modelWithCornersSelf ℝ (Fin n → ℂ))
        (modelWithCornersSelf ℝ ℝ) (expectation A) p = 0 ∧ expectation A p = μ}
      = {μ : ℝ | ∃ p : ℙ ℂ (Ambient n), Matrix.toEuclideanLin A p.rep = (μ : ℂ) • p.rep} := by
  ext μ
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (mfderiv_expectation_eq_zero_iff hA p).1 hp⟩
  · rintro ⟨p, hp⟩
    have he := expectation_eq_of_eigen hp
    refine ⟨p, (mfderiv_expectation_eq_zero_iff hA p).2 ?_, he⟩
    rw [he]
    exact hp

/-- ★★ **The eigenvalues with an eigenline are Mathlib's eigenvalues**: for Hermitian `A`,
`{μ | ∃ p, A p = μ p} = Set.range hA.eigenvalues`. -/
theorem setOf_eigenline_eq_range_eigenvalues {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) :
    {μ : ℝ | ∃ p : ℙ ℂ (Ambient n), Matrix.toEuclideanLin A p.rep = (μ : ℂ) • p.rep}
      = Set.range hA.eigenvalues := by
  ext μ
  constructor
  · rintro ⟨p, hp⟩
    have hev : Module.End.HasEigenvalue (Matrix.toEuclideanLin A) (μ : ℂ) :=
      Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.2 hp, rep_nonzero p⟩
    have hs := Module.End.hasEigenvalue_iff_mem_spectrum.1 hev
    rw [Matrix.spectrum_toLpLin, hA.spectrum_eq_image_range] at hs
    obtain ⟨μ', hμ', he⟩ := hs
    rwa [← Complex.ofReal_injective he]
  · rintro ⟨j, rfl⟩
    have hv : hA.eigenvectorBasis j ≠ 0 := hA.eigenvectorBasis.orthonormal.ne_zero j
    have hAv : Matrix.toEuclideanLin A (hA.eigenvectorBasis j)
        = ((hA.eigenvalues j : ℝ) : ℂ) • hA.eigenvectorBasis j := by
      have hk := hA.mulVec_eigenvectorBasis j
      ext k
      have h := congrFun hk k
      simp only [Pi.smul_apply] at h
      rw [Matrix.toLpLin_apply]
      simp only [PiLp.smul_apply]
      rw [h, Complex.real_smul]
      rfl
    refine ⟨mk ℂ _ hv, ?_⟩
    obtain ⟨c, hc⟩ := (mk_eq_mk_iff ℂ (mk ℂ _ hv).rep _ (rep_nonzero _) hv).mp (mk_rep _)
    rw [← hc, Units.smul_def, map_smul, hAv, smul_comm]

/-! ### Maximum and minimum -/

/-- `dH_A = 0` at a point where the chart Hamiltonian has a local extremum. -/
theorem mfderiv_schrodingerHamiltonian_eq_zero_of_isLocalExtr
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) {p : ℙ ℂ (Ambient n)}
    (h : IsLocalExtr (schrodingerChartHam A (idx p)) (chartFun (idx p) p)) :
    mfderiv (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ ℝ)
      (schrodingerHamiltonian A) p = 0 := by
  rw [(hasMFDerivAt_schrodingerHamiltonian A p).mfderiv]
  exact h.hasFDerivAt_eq_zero (hasFDerivAt_schrodingerChartHam A _ _)

/-- The chart Hamiltonian is `-2⟨A⟩` along the chart's inverse, with value `-2⟨A⟩_p` at `p`. -/
theorem schrodingerChartHam_eq (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (p : ℙ ℂ (Ambient n))
    (w : Fin n → ℂ) :
    schrodingerChartHam A (idx p) w = -2 * expectation A (chartInv (idx p) w) :=
  (schrodingerHamiltonian_chartInv A (idx p) w).symm

theorem chartInv_idx_chartFun (p : ℙ ℂ (Ambient n)) : chartInv (idx p) (chartFun (idx p) p) = p :=
  chartInv_chartFun _ _ (idx_spec p)

/-- ★ **Fermat's rule at a maximum of `⟨A⟩`.** -/
theorem mfderiv_expectation_eq_zero_of_isMaxOn {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) {p : ℙ ℂ (Ambient n)} (h : ∀ q, expectation A q ≤ expectation A p) :
    mfderiv (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ ℝ) (expectation A) p
      = 0 := by
  rw [mfderiv_expectation_eq_zero_iff_schrodingerField hA,
    (schrodingerField_isHamiltonianVectorField hA).eq_zero_iff_mfderiv_eq_zero
      (fsForm_isSymplectic n) p]
  refine mfderiv_schrodingerHamiltonian_eq_zero_of_isLocalExtr A (Or.inl ?_)
  refine Filter.Eventually.of_forall fun w => ?_
  rw [schrodingerChartHam_eq, schrodingerChartHam_eq, chartInv_idx_chartFun]
  linarith [h (chartInv (idx p) w)]

/-- ★ **Fermat's rule at a minimum of `⟨A⟩`.** -/
theorem mfderiv_expectation_eq_zero_of_isMinOn {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) {p : ℙ ℂ (Ambient n)} (h : ∀ q, expectation A p ≤ expectation A q) :
    mfderiv (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ ℝ) (expectation A) p
      = 0 := by
  rw [mfderiv_expectation_eq_zero_iff_schrodingerField hA,
    (schrodingerField_isHamiltonianVectorField hA).eq_zero_iff_mfderiv_eq_zero
      (fsForm_isSymplectic n) p]
  refine mfderiv_schrodingerHamiltonian_eq_zero_of_isLocalExtr A (Or.inr ?_)
  refine Filter.Eventually.of_forall fun w => ?_
  rw [schrodingerChartHam_eq, schrodingerChartHam_eq, chartInv_idx_chartFun]
  linarith [h (chartInv (idx p) w)]

/-- ★★★ **`⟨A⟩` attains its maximum at an eigenline, and the maximum is the largest
eigenvalue.** -/
theorem exists_isGreatest_eigenvalues {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) :
    ∃ p : ℙ ℂ (Ambient n), (∀ q, expectation A q ≤ expectation A p) ∧
      IsGreatest {μ : ℝ | ∃ q : ℙ ℂ (Ambient n), Matrix.toEuclideanLin A q.rep = (μ : ℂ) • q.rep}
        (expectation A p) := by
  obtain ⟨p, -, hp⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (continuous_expectation (n := n) A).continuousOn
  have hmax : ∀ q, expectation A q ≤ expectation A p := fun q => hp (Set.mem_univ q)
  refine ⟨p, hmax, ⟨p, (mfderiv_expectation_eq_zero_iff hA p).1
    (mfderiv_expectation_eq_zero_of_isMaxOn hA hmax)⟩, ?_⟩
  rintro μ ⟨q, hq⟩
  rw [← expectation_eq_of_eigen hq]
  exact hmax q

/-- ★★★ **`⟨A⟩` attains its minimum at an eigenline, and the minimum is the smallest
eigenvalue.** -/
theorem exists_isLeast_eigenvalues {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) :
    ∃ p : ℙ ℂ (Ambient n), (∀ q, expectation A p ≤ expectation A q) ∧
      IsLeast {μ : ℝ | ∃ q : ℙ ℂ (Ambient n), Matrix.toEuclideanLin A q.rep = (μ : ℂ) • q.rep}
        (expectation A p) := by
  obtain ⟨p, -, hp⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
    (continuous_expectation (n := n) A).continuousOn
  have hmin : ∀ q, expectation A p ≤ expectation A q := fun q => hp (Set.mem_univ q)
  refine ⟨p, hmin, ⟨p, (mfderiv_expectation_eq_zero_iff hA p).1
    (mfderiv_expectation_eq_zero_of_isMinOn hA hmin)⟩, ?_⟩
  rintro μ ⟨q, hq⟩
  rw [← expectation_eq_of_eigen hq]
  exact hmin q

/-! ### The same statements against Mathlib's eigenvalues -/

/-- ★★ **The critical values of `⟨A⟩` are Mathlib's eigenvalues of `A`.** -/
theorem criticalValues_eq_range_eigenvalues {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) :
    {μ : ℝ | ∃ p : ℙ ℂ (Ambient n), mfderiv (modelWithCornersSelf ℝ (Fin n → ℂ))
        (modelWithCornersSelf ℝ ℝ) (expectation A) p = 0 ∧ expectation A p = μ}
      = Set.range hA.eigenvalues := by
  rw [criticalValues_eq_eigenvalues hA, setOf_eigenline_eq_range_eigenvalues hA]

/-- ★★ **The maximum of `⟨A⟩` is the largest of Mathlib's eigenvalues of `A`.** -/
theorem exists_isGreatest_range_eigenvalues {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) :
    ∃ p : ℙ ℂ (Ambient n), (∀ q, expectation A q ≤ expectation A p) ∧
      IsGreatest (Set.range hA.eigenvalues) (expectation A p) := by
  rw [← setOf_eigenline_eq_range_eigenvalues hA]
  exact exists_isGreatest_eigenvalues hA

/-- ★★ **The minimum of `⟨A⟩` is the smallest of Mathlib's eigenvalues of `A`.** -/
theorem exists_isLeast_range_eigenvalues {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) :
    ∃ p : ℙ ℂ (Ambient n), (∀ q, expectation A p ≤ expectation A q) ∧
      IsLeast (Set.range hA.eigenvalues) (expectation A p) := by
  rw [← setOf_eigenline_eq_range_eigenvalues hA]
  exact exists_isLeast_eigenvalues hA

end Projectivization
