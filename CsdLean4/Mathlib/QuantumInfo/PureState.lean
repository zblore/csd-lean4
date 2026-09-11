/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Entropy
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Zero von Neumann entropy characterises pure states

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

`vonNeumannEntropy_eq_zero_of_pure` (`Entropy.lean`) gives `S(ρ) = 0` for a rank-one projector.
This file gives the converse and packages the equivalence:

* `negMulLog_eq_zero_iff` — on `[0, 1]`, `negMulLog x = 0` iff `x ∈ {0, 1}`;
* `isHermitian_eq_sum_eigenvalues_smul_vecMulVec` — the spectral theorem in projector form,
  `ρ = ∑ₖ λₖ |vₖ⟩⟨vₖ|` over the orthonormal eigenbasis;
* ★ `vonNeumannEntropy_eq_zero_iff` — for a density matrix (positive semidefinite, trace one),
  `S(ρ) = 0` iff `ρ = |ψ⟩⟨ψ|` for a unit vector `ψ`. The eigenvalues lie in `[0, 1]` and sum to
  one; each `negMulLog` term is non-negative, so a zero sum forces each eigenvalue into `{0, 1}`,
  and the unit sum then forces exactly one eigenvalue to be `1`; the projector form finishes it.

Consumer: `CsdLean4/LF2/PreparationPurity.lean` (a preparation on `Σ` has zero entropy iff it is
pure).
-/

@[expose] public section

open Matrix
open scoped ComplexOrder

/-! ### Zero entropy characterises pure states (matrix level) -/

namespace QuantumInfo

theorem negMulLog_eq_zero_iff {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.negMulLog x = 0 ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have hx0 : 0 < x := lt_of_le_of_ne h0 (Ne.symm hne.1)
    have hx1 : x < 1 := lt_of_le_of_ne h1 hne.2
    have hlog : Real.log x < 0 := Real.log_neg hx0 hx1
    have : 0 < Real.negMulLog x := by
      rw [Real.negMulLog]; nlinarith
    exact absurd h this.ne'
  · rintro (rfl | rfl) <;> simp

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A Hermitian matrix is the sum of its eigenvalues times the rank-one projectors onto an
orthonormal eigenbasis. -/
theorem isHermitian_eq_sum_eigenvalues_smul_vecMulVec {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    ρ = ∑ k, (RCLike.ofReal (hρ.eigenvalues k) : ℂ)
      • vecMulVec (⇑(hρ.eigenvectorBasis k)) (star ⇑(hρ.eigenvectorBasis k)) := by
  conv_lhs => rw [hρ.spectral_theorem, Unitary.conjStarAlgAut_apply]
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply,
    smul_eq_mul, Matrix.star_apply, Pi.star_apply, Function.comp_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- ★ **Zero entropy characterises pure states.** For a density matrix (positive semidefinite,
trace one), `S(ρ) = 0` iff `ρ = |ψ⟩⟨ψ|` for a unit vector `ψ`. -/
theorem vonNeumannEntropy_eq_zero_iff {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    vonNeumannEntropy hρ.1 = 0
      ↔ ∃ ψ : n → ℂ, star ψ ⬝ᵥ ψ = 1 ∧ ρ = vecMulVec ψ (star ψ) := by
  constructor
  · intro hS
    -- eigenvalues in [0, 1], summing to 1, each with negMulLog = 0, hence each 0 or 1
    have hsum : ∑ i, hρ.1.eigenvalues i = 1 := by
      have h := hρ.1.trace_eq_sum_eigenvalues
      rw [htr] at h
      have h2 : ((∑ i, hρ.1.eigenvalues i : ℝ) : ℂ) = 1 := by
        push_cast; exact h.symm
      exact_mod_cast h2
    have hnn : ∀ i, 0 ≤ hρ.1.eigenvalues i := hρ.eigenvalues_nonneg
    have hle : ∀ i, hρ.1.eigenvalues i ≤ 1 := fun i =>
      hsum ▸ Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
    have hzero : ∀ i, Real.negMulLog (hρ.1.eigenvalues i) = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Real.negMulLog_nonneg (hnn i) (hle i))).mp hS
      exact fun i => this i (Finset.mem_univ i)
    have h01 : ∀ i, hρ.1.eigenvalues i = 0 ∨ hρ.1.eigenvalues i = 1 := fun i =>
      (negMulLog_eq_zero_iff (hnn i) (hle i)).mp (hzero i)
    -- exactly one eigenvalue is 1
    obtain ⟨i₀, hi₀⟩ : ∃ i, hρ.1.eigenvalues i = 1 := by
      by_contra h
      push Not at h
      have : ∑ i, hρ.1.eigenvalues i = 0 :=
        Finset.sum_eq_zero fun i _ => (h01 i).resolve_right (h i)
      rw [hsum] at this
      exact one_ne_zero this
    have hother : ∀ i, i ≠ i₀ → hρ.1.eigenvalues i = 0 := by
      intro i hi
      by_contra h
      have h1 : hρ.1.eigenvalues i = 1 := (h01 i).resolve_left h
      have : 2 ≤ ∑ j, hρ.1.eigenvalues j := by
        calc (2 : ℝ) = hρ.1.eigenvalues i + hρ.1.eigenvalues i₀ := by rw [h1, hi₀]; norm_num
          _ = ∑ j ∈ {i, i₀}, hρ.1.eigenvalues j := by
              rw [Finset.sum_pair hi]
          _ ≤ ∑ j, hρ.1.eigenvalues j :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => hnn j
      rw [hsum] at this
      norm_num at this
    refine ⟨⇑(hρ.1.eigenvectorBasis i₀), ?_, ?_⟩
    · have hn : ‖hρ.1.eigenvectorBasis i₀‖ = 1 := hρ.1.eigenvectorBasis.orthonormal.1 i₀
      have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (hρ.1.eigenvectorBasis i₀)
      rw [EuclideanSpace.inner_eq_star_dotProduct, hn] at h
      rw [dotProduct_comm]
      simpa using h
    · conv_lhs => rw [isHermitian_eq_sum_eigenvalues_smul_vecMulVec hρ.1]
      rw [Finset.sum_eq_single i₀]
      · rw [hi₀]; simp
      · intro i _ hi; rw [hother i hi]; simp
      · intro h; exact absurd (Finset.mem_univ _) h
  · rintro ⟨ψ, hψ, rfl⟩
    refine vonNeumannEntropy_eq_zero_of_projection hρ.1 ?_
    rw [Matrix.vecMulVec_mul_vecMulVec, hψ, one_smul]

end QuantumInfo
