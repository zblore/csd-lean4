/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF3.Singlet.Expectations

/-!
# LF6-6: the partial-Schmidt (non-maximally-entangled) two-qubit correlation

**Category:** 6-Local (extends the LF6-D entangled tier beyond the maximally-entangled family).

LF6-D's non-factorisation runs on the maximally-entangled state `Ψ_d` (equal Schmidt coefficients),
whose two-qubit sector is the Bell `Φ⁺`. This module takes the first step **beyond** maximal
entanglement: the general real-Schmidt two-qubit state `Ψ(c,s) = c|00⟩ + s|11⟩` (`c² + s² = 1`), and
derives its Hilbert-space Pauli correlation in closed form:

    ⟨Ψ(c,s) | σ·a ⊗ σ·b | Ψ(c,s)⟩ = a_z b_z + 2cs·(a_x b_x − a_y b_y).

The coefficient `2cs` is the **concurrence** (the entanglement measure): it is `1` exactly at the
maximally-entangled point `c = s = 1/√2`, where the correlation collapses to `Φ⁺`'s
`a_x b_x − a_y b_y + a_z b_z` (`psQubit_pauli_correlation_maximal`), and `0` for a product state
(`c` or `s` `= 0`). So this makes explicit **where maximal entanglement enters** the LF6-D correlation.

## Honest scope

* **Delivered (the correlation, general partial-Schmidt):** the Hilbert-space Pauli correlation of an
  arbitrary real-Schmidt two-qubit state, `psQubit_pauli_correlation`, computed from the Hilbert space
  (`psExpectation_formula` + the `pauliDot` entries), with the maximal-entanglement reduction to `Φ⁺`
  (`psQubit_pauli_correlation_maximal`). This extends the LF6 correlation content past equal Schmidt
  coefficients.
* **The non-factorisation witness (now discharged in `LF6/GisinTheorem.lean`):** forcing
  non-factorisation for **unequal** Schmidt coefficients (`c ≠ s`) needs a Bell violation for a
  non-maximally-entangled state. The LF6-D `reflectXZ → singlet` CHSH reduction is specific to `Φ⁺`
  (equal weights) and the CGLMP Dirichlet-kernel closed form to the equal diagonal amplitudes `(√d)⁻¹`;
  neither ports. The general witness is **Gisin's theorem** — `GisinTheorem.gisin_chsh_violation` builds
  it directly on the `psQubit_pauli_correlation` computed here: from the state-dependence, the concurrence
  `2cs > 0` yields explicit detector settings with CHSH value `2√(1+(2cs)²) > 2`.

Reference: `specs/future-work.md` (LF6-6); `LF6/GisinTheorem.lean` (`gisin_chsh_violation`, the witness).
-/

@[expose] public section

open scoped BigOperators ComplexConjugate
open Matrix

namespace CSD
namespace LF6

open CSD.LF3

/-- **The partial-Schmidt two-qubit state** `Ψ(c,s) = c|00⟩ + s|11⟩` (real Schmidt coefficients) on
`EuclideanSpace ℂ (Fin 2 × Fin 2)`. Maximally entangled at `c = s = 1/√2` (`= Φ⁺`), a product state at
`c = 0` or `s = 0`. -/
noncomputable def psQubit (c s : ℝ) : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  WithLp.toLp 2 (fun w => if w = (0, 0) then (c : ℂ) else if w = (1, 1) then (s : ℂ) else 0)

lemma psQubit_apply (c s : ℝ) (w : Fin 2 × Fin 2) :
    psQubit c s w = if w = (0, 0) then (c : ℂ) else if w = (1, 1) then (s : ℂ) else 0 := rfl

lemma psQubit_apply_00 (c s : ℝ) : psQubit c s (0, 0) = (c : ℂ) := by
  rw [psQubit_apply, if_pos rfl]
lemma psQubit_apply_01 (c s : ℝ) : psQubit c s (0, 1) = 0 := by
  rw [psQubit_apply, if_neg (by decide), if_neg (by decide)]
lemma psQubit_apply_10 (c s : ℝ) : psQubit c s (1, 0) = 0 := by
  rw [psQubit_apply, if_neg (by decide), if_neg (by decide)]
lemma psQubit_apply_11 (c s : ℝ) : psQubit c s (1, 1) = (s : ℂ) := by
  rw [psQubit_apply, if_neg (by decide), if_pos rfl]

/-- Expectation `⟨Ψ(c,s) | M | Ψ(c,s)⟩` for a `(Fin 2 × Fin 2)`-indexed matrix `M`. -/
noncomputable def psExpectation (c s : ℝ) (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℂ :=
  inner ℂ (psQubit c s) ((Matrix.toEuclideanLin M) (psQubit c s))

/-- **The partial-Schmidt expectation formula.** On `Ψ(c,s)` the expectation of an arbitrary
`(Fin 2 × Fin 2)`-indexed matrix reduces to the four diagonal-support entries weighted by the Schmidt
products `c², cs, sc, s²`. The 12 of 16 double-sum terms vanish (each has a `Ψ(0,1) = 0` or
`Ψ(1,0) = 0` factor); the `c, s` are real, so `star` acts trivially. Mirrors
`phiPlus_expectation_formula` with the two unequal amplitudes `c, s`. -/
theorem psExpectation_formula (c s : ℝ) (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    psExpectation c s M
      = (c : ℂ) ^ 2 * M (0, 0) (0, 0) + (c : ℂ) * (s : ℂ) * M (0, 0) (1, 1)
        + (s : ℂ) * (c : ℂ) * M (1, 1) (0, 0) + (s : ℂ) ^ 2 * M (1, 1) (1, 1) := by
  unfold psExpectation
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin,
      dotProduct, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Pi.star_apply]
  simp only [show (psQubit c s).ofLp (0, 0) = (c : ℂ) from psQubit_apply_00 c s,
             show (psQubit c s).ofLp (0, 1) = (0 : ℂ) from psQubit_apply_01 c s,
             show (psQubit c s).ofLp (1, 0) = (0 : ℂ) from psQubit_apply_10 c s,
             show (psQubit c s).ofLp (1, 1) = (s : ℂ) from psQubit_apply_11 c s,
             star_zero, Complex.star_def, Complex.conj_ofReal]
  ring

/-- The raw (pre-normalisation) partial-Schmidt Pauli correlation:
`⟨Ψ(c,s)|σ·a ⊗ σ·b|Ψ(c,s)⟩ = (c²+s²)·a_z b_z + 2cs·(a_x b_x − a_y b_y)`. -/
lemma psExpectation_sigmaDotJoint (c s : ℝ) (a b : DetectorSetting) :
    psExpectation c s (sigmaDotJoint a b)
      = ((c ^ 2 + s ^ 2 : ℝ) : ℂ) * ((a.vec 2 : ℂ) * (b.vec 2 : ℂ))
        + 2 * (c : ℂ) * (s : ℂ) * ((a.vec 0 : ℂ) * (b.vec 0 : ℂ) - (a.vec 1 : ℂ) * (b.vec 1 : ℂ)) := by
  rw [psExpectation_formula]
  simp only [sigmaDotJoint, Matrix.kroneckerMap_apply, pauliDot_apply_00, pauliDot_apply_01,
             pauliDot_apply_10, pauliDot_apply_11]
  push_cast
  ring_nf
  rw [show (Complex.I ^ 2 : ℂ) = -1 from Complex.I_sq]
  ring

/-- **The partial-Schmidt two-qubit Pauli correlation** (the genuine Hilbert-space computation,
generalising `phiPlus_pauli_correlation` beyond maximal entanglement). For `c² + s² = 1`:

`⟨Ψ(c,s) | σ·a ⊗ σ·b | Ψ(c,s)⟩ = a_z b_z + 2cs·(a_x b_x − a_y b_y)`.

The coefficient `2cs` is the concurrence: `1` at maximal entanglement (`c = s = 1/√2`), `0` at a product
state. This makes explicit where the Schmidt spectrum enters the LF6-D `Φ⁺` correlation. -/
theorem psQubit_pauli_correlation (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (a b : DetectorSetting) :
    psExpectation c s (sigmaDotJoint a b)
      = ((a.vec 2 * b.vec 2 + 2 * c * s * (a.vec 0 * b.vec 0 - a.vec 1 * b.vec 1) : ℝ) : ℂ) := by
  rw [psExpectation_sigmaDotJoint, hcs]
  push_cast
  ring

/-- **Maximal-entanglement reduction: `Ψ(1/√2, 1/√2) = Φ⁺`.** At the maximally-entangled point the
partial-Schmidt correlation collapses to `Φ⁺`'s `a_x b_x − a_y b_y + a_z b_z` (concurrence `2cs = 1`),
recovering `phiPlus_pauli_correlation`. So `Φ⁺` is the equal-Schmidt-coefficient special case. -/
theorem psQubit_pauli_correlation_maximal (a b : DetectorSetting) :
    psExpectation (Real.sqrt 2)⁻¹ (Real.sqrt 2)⁻¹ (sigmaDotJoint a b)
      = ((a.vec 0 * b.vec 0 - a.vec 1 * b.vec 1 + a.vec 2 * b.vec 2 : ℝ) : ℂ) := by
  have hhalf : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have hcs : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 + ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 := by rw [hhalf]; norm_num
  have h2cs : 2 * ((Real.sqrt 2)⁻¹ : ℝ) * ((Real.sqrt 2)⁻¹ : ℝ) = 1 := by
    have : ((Real.sqrt 2)⁻¹ : ℝ) * ((Real.sqrt 2)⁻¹ : ℝ) = 1 / 2 := by
      rw [← sq]; exact hhalf
    rw [mul_assoc, this]; norm_num
  rw [psQubit_pauli_correlation _ _ hcs, h2cs]
  push_cast
  ring

end LF6
end CSD

