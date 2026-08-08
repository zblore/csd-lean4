/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Incubator.QuantumChaos.FloquetInterface
public import CsdLean4.Mathlib.Analysis.Matrix.L2OpNormEntry

/-!
# Chaos diagnostics: the spectral form factor (quantum-chaos workstream, §H)

**Category:** Special (incubator — CSD-free; `upstream-candidate(physlib)`).

The second chaos diagnostic behind the interface: the **spectral form
factor**

  `SFF(n) = |Tr(Uⁿ)|² / N²`,

the normalized modulus-squared trace of the `n`-period propagator — the
standard probe of spectral statistics (its time profile distinguishes
Poissonian from random-matrix level correlations).

What is delivered at this level is the *object and its exact structure*, not
RMT statistics: `sff` is well-defined from the unitary alone, normalized
(`sff_zero`), bounded (`sff_le_one` — every entry of a unitary power is
bounded by the operator norm `1`, via the staged
`Matrix.norm_entry_le_l2_opNorm`), **basis-independent** (`sff_conj` —
conjugation invariance, so the diagnostic is a property of the dynamics,
not a matrix presentation), and **explicitly computable for diagonal
drives** (`sff_diagonal` — the exponential-sum form; the free field's SFF
is an instance, `CV/ChaosBounds.lean`).

The CSD reading, as for the Loschmidt echo: the propagator preserves every
global overlap exactly, so SFF structure never signals information loss —
it is a fingerprint of *where* the preserved information sits in the
spectrum. Honest scope: no random-matrix or level-statistics claims; those
are the thread's recorded continuation, not stated here.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator

namespace QuantumChaos

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The spectral form factor**: the normalized modulus-squared trace of
the `n`-period propagator, `|Tr(Uⁿ)|² / N²`. -/
noncomputable def sff (U : Matrix.unitaryGroup ι ℂ) (n : ℕ) : ℝ :=
  ‖Matrix.trace (U ^ n).val‖ ^ 2 / (Fintype.card ι : ℝ) ^ 2

/-- At `n = 0` the form factor is exactly `1` — the normalization. -/
@[simp] lemma sff_zero [Nonempty ι] (U : Matrix.unitaryGroup ι ℂ) :
    sff U 0 = 1 := by
  rw [sff, pow_zero,
    show ((1 : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) = 1 from rfl,
    Matrix.trace_one]
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [show ‖(Fintype.card ι : ℂ)‖ = (Fintype.card ι : ℝ) from by
    rw [Complex.norm_natCast]]
  field_simp

/-- The form factor is nonnegative. -/
lemma sff_nonneg (U : Matrix.unitaryGroup ι ℂ) (n : ℕ) : 0 ≤ sff U n :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- ★ **The form factor is at most `1`**: every entry of a unitary power is
bounded by the operator norm `1`, so the trace is at most `N`. -/
theorem sff_le_one [Nonempty ι] (U : Matrix.unitaryGroup ι ℂ) (n : ℕ) :
    sff U n ≤ 1 := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hU : ‖(U ^ n).val‖ = 1 := CStarRing.norm_of_mem_unitary (U ^ n).property
  have htr : ‖Matrix.trace (U ^ n).val‖ ≤ (Fintype.card ι : ℝ) := by
    calc ‖Matrix.trace (U ^ n).val‖
        = ‖∑ i, (U ^ n).val i i‖ := rfl
      _ ≤ ∑ i, ‖(U ^ n).val i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← hU]
          exact Matrix.norm_entry_le_l2_opNorm _ i i
      _ = (Fintype.card ι : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [sff, div_le_one (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) htr 2

/-- ★ **Basis independence**: the form factor is conjugation-invariant —
a property of the dynamics, not of a matrix presentation. -/
theorem sff_conj (V U : Matrix.unitaryGroup ι ℂ) (n : ℕ) :
    sff (V * U * V⁻¹) n = sff U n := by
  rw [sff, sff, conj_pow,
    show ((V * U ^ n * V⁻¹ : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ)
      = V.val * (U ^ n).val * (V⁻¹).val from rfl,
    Matrix.trace_mul_cycle,
    show (V⁻¹ : Matrix.unitaryGroup ι ℂ).val * V.val
      = ((V⁻¹ * V : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) from rfl,
    inv_mul_cancel,
    show ((1 : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) = 1 from rfl,
    one_mul]

/-- **The diagonal (integrable) case is an explicit exponential sum**:
`Tr(Uⁿ) = ∑ₓ (u x)ⁿ` for a diagonal drive. The free field's SFF is an
instance (`CV/ChaosBounds.lean`). -/
theorem sff_diagonal {u : ι → ℂ} {U : Matrix.unitaryGroup ι ℂ}
    (hU : U.val = Matrix.diagonal u) (n : ℕ) :
    sff U n = ‖∑ x, u x ^ n‖ ^ 2 / (Fintype.card ι : ℝ) ^ 2 := by
  rw [sff, show (U ^ n).val = U.val ^ n from rfl, hU, Matrix.diagonal_pow,
    Matrix.trace_diagonal]
  rfl

end QuantumChaos
