/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF2.BornWrapper
public import CsdLean4.SigmaLayer.CompositeInterface
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# SigmaLayer/MixedState: mixed-state representation and statistical mixtures

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)).

Ledger target **T9**, the mixed-state representation. The repository already carries the Born rule on
density operators (`LF2.BornWrapper.traceForm`, `Tr(ρ E)`), the pure-state density
(`rankOneDensity ψ = |ψ⟩⟨ψ|`), and the pure Born quadratic form (`born_quadratic`). The gap this module
closes is the **statistical mixture / ensemble** structure: convex combinations of density operators and
the affine dependence of the Born rule on the state, together with a purity predicate.

* `mix p ρ₁ ρ₂` — the convex combination `p ρ₁ + (1-p) ρ₂` is a genuine density operator (Hermitian, PSD,
  trace one): the classical mixture of two preparations.
* `traceForm_mix` — the Born rule is affine in the state: mixing preparations mixes the outcome
  probabilities, `Tr((p ρ₁ + (1-p) ρ₂) E) = p Tr(ρ₁ E) + (1-p) Tr(ρ₂ E)`. This is the defining property
  of a statistical mixture and the reason density operators, not just state vectors, are the right state
  space.
* `IsPure` / `rankOneDensity_isPure` / `isPure_iff_trace_sq_one` — the purity predicate (`ρ² = ρ`), the
  fact that rank-one densities are pure, and the full purity characterisation `IsPure ρ ↔ Tr(ρ²) = 1`
  (the converse `isPure_of_trace_sq_one` via the spectral theorem: `∑λᵢ = ∑λᵢ² = 1`, `λᵢ ≥ 0` forces
  `λᵢ ∈ {0,1}`).
* `maximallyMixed` / `maximallyMixed_not_isPure` — a genuinely mixed state: `I/N` is a density operator
  and, for `N ≥ 2`, is not pure, so the mixture structure is not vacuous.

This is the mixed-state layer Mathlib does not supply (no density-matrix type upstream); it is built on
the repository's `LF2.DensityOperator`/`Effect` and `traceForm`.
-/

@[expose] public section

open Matrix Unitary
open scoped ComplexOrder

namespace CSD.SigmaLayer

open CSD.LF2

variable {N : ℕ}

/-- `(r : ℂ)` is self-adjoint for real `r` (its conjugate is itself). -/
theorem isSelfAdjoint_ofReal (r : ℝ) : IsSelfAdjoint ((r : ℂ)) := by
  rw [isSelfAdjoint_iff]; exact Complex.conj_ofReal r

/-- A nonnegative real multiple of a positive semidefinite complex matrix is positive semidefinite. -/
theorem posSemidef_real_smul {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.PosSemidef)
    {p : ℝ} (hp : 0 ≤ p) : ((p : ℂ) • A).PosSemidef :=
  hA.smul (by exact_mod_cast hp)

/-! ### The convex mixture of density operators -/

/-- **The statistical mixture of two density operators.** The convex combination
`p ρ₁ + (1-p) ρ₂` (with `0 ≤ p ≤ 1`) is itself a density operator: the classical mixture of two
quantum preparations. -/
noncomputable def mix (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ₁ ρ₂ : DensityOperator N) :
    DensityOperator N where
  M := (p : ℂ) • ρ₁.M + ((1 - p : ℝ) : ℂ) • ρ₂.M
  isHermitian :=
    (ρ₁.isHermitian.smul (isSelfAdjoint_ofReal p)).add (ρ₂.isHermitian.smul (isSelfAdjoint_ofReal _))
  nonneg := (posSemidef_real_smul ρ₁.nonneg hp0).add (posSemidef_real_smul ρ₂.nonneg (by linarith))
  trace_one := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, ρ₁.trace_one, ρ₂.trace_one,
      smul_eq_mul, smul_eq_mul, mul_one, mul_one]
    push_cast; ring

@[simp] theorem mix_M (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ₁ ρ₂ : DensityOperator N) :
    (mix p hp0 hp1 ρ₁ ρ₂).M = (p : ℂ) • ρ₁.M + ((1 - p : ℝ) : ℂ) • ρ₂.M := rfl

/-- **The Born rule is affine in the state.** Mixing preparations mixes the outcome probabilities:
`Tr((p ρ₁ + (1-p) ρ₂) E) = p Tr(ρ₁ E) + (1-p) Tr(ρ₂ E)`. The defining property of a statistical
mixture, and the reason density operators are the right state space. -/
theorem traceForm_mix (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ₁ ρ₂ : DensityOperator N) (E : Effect N) :
    traceForm (mix p hp0 hp1 ρ₁ ρ₂) E = p * traceForm ρ₁ E + (1 - p) * traceForm ρ₂ E := by
  simp only [traceForm, mix_M, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul]
  push_cast [RCLike.re_to_complex]
  simp

/-! ### Purity -/

/-- **A density operator is pure iff it is a projector** (`ρ² = ρ`, hence rank one given trace one);
otherwise it is a genuine statistical mixture. -/
def IsPure (ρ : DensityOperator N) : Prop := ρ.M * ρ.M = ρ.M

/-- **Rank-one densities are pure.** The pure-state density `|ψ⟩⟨ψ|` (unit `ψ`) is a projector. -/
theorem rankOneDensity_isPure (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1) :
    IsPure (rankOneDensity ψ hψ) :=
  outerProduct_mul_self_of_unit_norm ψ hψ

/-- **Purity witness.** A pure state has `Tr(ρ²) = 1`. -/
theorem IsPure.trace_sq_one {ρ : DensityOperator N} (h : IsPure ρ) : (ρ.M * ρ.M).trace = 1 := by
  have h' : ρ.M * ρ.M = ρ.M := h
  rw [h']; exact ρ.trace_one

/-- **Purity from the trace witness (the converse).** A density operator with `Tr(ρ²) = 1` is pure.
Via the spectral theorem: the eigenvalues `λᵢ ≥ 0` satisfy `∑λᵢ = ∑λᵢ² = 1`, forcing each `λᵢ ∈ {0,1}`
(so `λᵢ² = λᵢ`), whence `ρ² = ρ` by diagonalisation. -/
theorem isPure_of_trace_sq_one {ρ : DensityOperator N} (h : (ρ.M * ρ.M).trace = 1) : IsPure ρ := by
  classical
  have hA := ρ.isHermitian
  have hspec := hA.spectral_theorem
  have hsq : ρ.M * ρ.M
      = conjStarAlgAut ℂ _ hA.eigenvectorUnitary
          (diagonal (RCLike.ofReal ∘ hA.eigenvalues) * diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := by
    conv_lhs => rw [hspec]
    rw [← map_mul]
  have htr1 : (∑ i, (hA.eigenvalues i : ℂ)) = 1 :=
    (hA.trace_eq_sum_eigenvalues).symm.trans ρ.trace_one
  have htr2 : (∑ i, ((hA.eigenvalues i : ℂ)) ^ 2) = 1 := by
    rw [← h, hsq, conjStarAlgAut_apply, trace_mul_cycle, coe_star_mul_self, one_mul,
      diagonal_mul_diagonal, trace_diagonal]
    exact Finset.sum_congr rfl (fun i _ => by simp [Function.comp_apply, pow_two])
  have hr1 : (∑ i, hA.eigenvalues i) = 1 := by exact_mod_cast htr1
  have hr2 : (∑ i, (hA.eigenvalues i) ^ 2) = 1 := by exact_mod_cast htr2
  have hnn : ∀ i, 0 ≤ hA.eigenvalues i := ρ.nonneg.eigenvalues_nonneg
  have hle1 : ∀ i, hA.eigenvalues i ≤ 1 := fun i => by
    rw [← hr1]; exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  have hzero : ∀ i, hA.eigenvalues i ^ 2 = hA.eigenvalues i := by
    have hsum : (∑ i, (hA.eigenvalues i - hA.eigenvalues i ^ 2)) = 0 := by
      rw [Finset.sum_sub_distrib, hr1, hr2]; ring
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin N)), 0 ≤ hA.eigenvalues i - hA.eigenvalues i ^ 2 :=
      fun i _ => by nlinarith [hnn i, hle1 i]
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsum i (Finset.mem_univ i)
    linarith
  have hDD : diagonal (RCLike.ofReal ∘ hA.eigenvalues) * diagonal (RCLike.ofReal ∘ hA.eigenvalues)
      = diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hA.eigenvalues) := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Function.comp_apply]
    rw [← RCLike.ofReal_mul, ← pow_two, hzero i]
  show ρ.M * ρ.M = ρ.M
  rw [hsq, hDD, ← hspec]

/-- **Purity characterisation.** A density operator is pure iff `Tr(ρ²) = 1`. -/
theorem isPure_iff_trace_sq_one {ρ : DensityOperator N} : IsPure ρ ↔ (ρ.M * ρ.M).trace = 1 :=
  ⟨IsPure.trace_sq_one, isPure_of_trace_sq_one⟩

/-! ### A genuinely mixed state -/

/-- **The maximally mixed state `I/N`.** A density operator representing complete ignorance; the
canonical genuinely-mixed preparation. -/
noncomputable def maximallyMixed (N : ℕ) [NeZero N] : DensityOperator N where
  M := (Complex.ofReal ((N : ℝ)⁻¹)) • (1 : Matrix (Fin N) (Fin N) ℂ)
  isHermitian := Matrix.isHermitian_one.smul (isSelfAdjoint_ofReal _)
  nonneg := posSemidef_real_smul Matrix.PosSemidef.one (by positivity)
  trace_one := by
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    push_cast
    exact inv_mul_cancel₀ (by exact_mod_cast NeZero.ne N)

/-- **The maximally mixed state is genuinely mixed.** For `N ≥ 2`, `I/N` is not pure: the mixture
structure is not vacuous, there exist states that are not rank-one projectors. -/
theorem maximallyMixed_not_isPure [NeZero N] (hN : 2 ≤ N) : ¬ IsPure (maximallyMixed N) := by
  intro h
  have h' : (maximallyMixed N).M * (maximallyMixed N).M = (maximallyMixed N).M := h
  have hMM : (maximallyMixed N).M * (maximallyMixed N).M
      = (Complex.ofReal ((N : ℝ)⁻¹) * Complex.ofReal ((N : ℝ)⁻¹)) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    simp only [maximallyMixed, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  rw [hMM] at h'
  simp only [maximallyMixed] at h'
  have e00 := congrFun (congrFun h' ⟨0, by omega⟩) ⟨0, by omega⟩
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e00
  have hc : Complex.ofReal ((N : ℝ)⁻¹) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]; exact_mod_cast NeZero.ne N
  have hc1 : Complex.ofReal ((N : ℝ)⁻¹) = 1 := by
    have hz : Complex.ofReal ((N : ℝ)⁻¹) * (Complex.ofReal ((N : ℝ)⁻¹) - 1) = 0 := by
      ring_nf; linear_combination e00
    rcases mul_eq_zero.mp hz with h0 | h1
    · exact absurd h0 hc
    · exact sub_eq_zero.mp h1
  rw [Complex.ofReal_eq_one, inv_eq_one] at hc1
  have : (2 : ℝ) ≤ 1 := hc1 ▸ (by exact_mod_cast hN)
  norm_num at this

/-! ### T9 capstone -/

/-- **T9: the mixed-state representation.** Density operators are the right state space: convex mixtures
of density operators are density operators (`mix`), the Born rule is affine in the state (`traceForm_mix`
-- mixing preparations mixes probabilities), pure states are the rank-one projectors
(`rankOneDensity_isPure`), and there are genuinely mixed states (`maximallyMixed_not_isPure`). The pure
Born rule (`born_quadratic`) is the extreme-point case. -/
theorem mixedState_capstone (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ₁ ρ₂ : DensityOperator N)
    (E : Effect N) :
    traceForm (mix p hp0 hp1 ρ₁ ρ₂) E = p * traceForm ρ₁ E + (1 - p) * traceForm ρ₂ E :=
  traceForm_mix p hp0 hp1 ρ₁ ρ₂ E

end CSD.SigmaLayer
