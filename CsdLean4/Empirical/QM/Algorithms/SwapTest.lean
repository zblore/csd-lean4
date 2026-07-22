/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Mathlib.QuantumInfo.Hadamard

/-!
# The swap test (overlap / fidelity estimator)

**Category:** 3-Local (QM-validity).

The swap test opens the **ancilla-interferometry** algorithm family (beside the
Hadamard-oracle family Deutsch–Jozsa / Simon / Bernstein–Vazirani). One ancilla qubit
interferes two system copies `ψ, φ` through a controlled swap:

  `H_anc ∘ cSWAP ∘ H_anc`  on  `|0⟩ ⊗ ψ ⊗ φ`.

Tracking the ancilla:

* `H_anc`  : `|0⟩⊗ψ⊗φ ↦ (|0⟩+|1⟩)/√2 ⊗ ψ⊗φ`;
* `cSWAP`  : `↦ (|0⟩⊗ψ⊗φ + |1⟩⊗φ⊗ψ)/√2`;
* `H_anc`  : `↦ (1/2)[ |0⟩⊗(ψ⊗φ + φ⊗ψ) + |1⟩⊗(ψ⊗φ − φ⊗ψ) ]`.

The ancilla-`0` marginal (`swapTestProb0`) is the headline:

  `P(0) = (1/4)‖ψ⊗φ + φ⊗ψ‖² = (1 + |⟨ψ,φ⟩|²)/2`   (`swap_test_prob`),

using the key tensor identity `⟨ψ⊗φ, φ⊗ψ⟩ = ⟨ψ,φ⟩·⟨φ,ψ⟩ = |⟨ψ,φ⟩|²`. Hence
`P(0) = 1` when `ψ = φ` (`swap_test_equal`) and `P(0) = 1/2` when `⟨ψ,φ⟩ = 0`
(`swap_test_orthogonal`): the test reads off `|⟨ψ,φ⟩|²`, the squared overlap / fidelity.

**Model.** Combined space `EuclideanSpace ℂ (Fin 2 × ι × ι)` for an arbitrary `Fintype ι`
(the system index — any finite dimension). The two system states `ψ φ : EuclideanSpace ℂ ι`
enter as the product amplitude `(a,i,j) ↦ [a=0]·ψ i·φ j` (`swapInit`). The two gates
(`hadAnc` on the ancilla factor via `hadEntry`, `cSwap` swapping the two `ι` factors on
ancilla `1`) are amplitude functions; the two-Hadamard collapse (`hadEntry` orthogonality)
gives the explicit ancilla-`0` amplitude `(1/2)(ψ i φ j + φ i ψ j)` (`swapTest_apply`).

**Honest scope.** This is the **exact single-shot output-probability identity** — the
inner-product-geometry (QM-validity) statement. The *estimation* (repeating the test to
resolve `|⟨ψ,φ⟩|²` to a target precision) is the statistical wrapper, noted but not
formalised here. No tensor caveats beyond the explicit `Fin 2 × ι × ι` model.

(For `ι = Empty` the unit hypotheses `‖ψ‖ = 1` are unsatisfiable, so the headlines hold
vacuously there; non-vacuous content needs an inhabited system `ι`.)
-/

open scoped ComplexConjugate
open QuantumInfo

namespace CSD
namespace Empirical
namespace QM
namespace SwapTest

variable {ι : Type*} [Fintype ι]
variable (ψ φ : EuclideanSpace ℂ ι)

/-! ## Definitions -/

/-- `|0⟩ ⊗ ψ ⊗ φ`: the product amplitude `(a,i,j) ↦ [a=0]·ψ i·φ j`. -/
noncomputable def swapInit : Fin 2 × ι × ι → ℂ :=
  fun p => if p.1 = 0 then ψ p.2.1 * φ p.2.2 else 0

/-- Hadamard on the ancilla (`Fin 2`) factor only: `(a,i,j) ↦ ∑_b H(a,b)·state(b,i,j)`. -/
noncomputable def hadAnc (s : Fin 2 × ι × ι → ℂ) : Fin 2 × ι × ι → ℂ :=
  fun p => ∑ b : Fin 2, hadEntry p.1 b * s (b, p.2.1, p.2.2)

/-- Controlled swap of the two system factors, controlled on ancilla `= 1`:
`(a,i,j) ↦ state(a,j,i)` if `a = 1`, else `state(a,i,j)`. -/
noncomputable def cSwap (s : Fin 2 × ι × ι → ℂ) : Fin 2 × ι × ι → ℂ :=
  fun p => if p.1 = 1 then s (p.1, p.2.2, p.2.1) else s (p.1, p.2.1, p.2.2)

/-- The **swap-test circuit** `H_anc ∘ cSWAP ∘ H_anc` on `|0⟩ ⊗ ψ ⊗ φ`. -/
noncomputable def swapTest : Fin 2 × ι × ι → ℂ :=
  hadAnc (cSwap (hadAnc (swapInit ψ φ)))

/-- The **ancilla-`0` marginal probability** `P(0) = ∑_{i,j} ‖swapTest(0,i,j)‖²`. -/
noncomputable def swapTestProb0 : ℝ :=
  ∑ i, ∑ j, ‖swapTest ψ φ (0, i, j)‖ ^ 2

/-! ## Amplitude lemmas -/

omit [Fintype ι] in
lemma swapInit_apply (b : Fin 2) (i j : ι) :
    swapInit ψ φ (b, i, j) = if b = 0 then ψ i * φ j else 0 := rfl

omit [Fintype ι] in
lemma hadAnc_apply (s : Fin 2 × ι × ι → ℂ) (a : Fin 2) (i j : ι) :
    hadAnc s (a, i, j) = ∑ b : Fin 2, hadEntry a b * s (b, i, j) := rfl

omit [Fintype ι] in
lemma cSwap_apply (s : Fin 2 × ι × ι → ℂ) (a : Fin 2) (i j : ι) :
    cSwap s (a, i, j) = if a = 1 then s (a, j, i) else s (a, i, j) := rfl

/-- `H(0,b) = (√2)⁻¹` (the all-zero ancilla row). -/
lemma hadEntry_zero_left (b : Fin 2) : hadEntry (0 : Fin 2) b = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [hadEntry]

omit [Fintype ι] in
/-- After the **first** Hadamard the ancilla is in a uniform superposition over the
unchanged product: `hadAnc (swapInit ψ φ) (a,i,j) = (√2)⁻¹·ψ i·φ j` for every `a`. -/
lemma had1_apply (a : Fin 2) (i j : ι) :
    hadAnc (swapInit ψ φ) (a, i, j) = (Real.sqrt 2 : ℂ)⁻¹ * (ψ i * φ j) := by
  rw [hadAnc_apply, Fin.sum_univ_two, swapInit_apply, swapInit_apply, if_pos rfl,
      if_neg (by decide : ¬ (1 : Fin 2) = 0), hadEntry_zero_right, mul_zero, add_zero]

omit [Fintype ι] in
/-- After the controlled swap the two pointer branches carry the two orderings:
ancilla `1` swaps `i,j`. -/
lemma cswap_had1_apply (a : Fin 2) (i j : ι) :
    cSwap (hadAnc (swapInit ψ φ)) (a, i, j)
      = if a = 1 then (Real.sqrt 2 : ℂ)⁻¹ * (ψ j * φ i)
        else (Real.sqrt 2 : ℂ)⁻¹ * (ψ i * φ j) := by
  rw [cSwap_apply]
  split
  · rw [had1_apply]
  · rw [had1_apply]

omit [Fintype ι] in
/-- **The ancilla-`0` amplitude after the full circuit.** The two-Hadamard collapse on the
ancilla (`hadEntry` orthogonality) leaves the symmetric combination:

  `swapTest ψ φ (0,i,j) = (1/2)(ψ i φ j + φ i ψ j)`. -/
lemma swapTest_apply (i j : ι) :
    swapTest ψ φ (0, i, j) = (1 / 2 : ℂ) * (ψ i * φ j + φ i * ψ j) := by
  rw [swapTest, hadAnc_apply, Fin.sum_univ_two, cswap_had1_apply, cswap_had1_apply,
      if_neg (by decide : ¬ (0 : Fin 2) = 1), if_pos rfl, hadEntry_zero_left,
      hadEntry_zero_left]
  have h2 : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, sqrt2_mul_self]; norm_num
  linear_combination (ψ i * φ j + ψ j * φ i) * h2

/-! ## Inner-product infrastructure -/

/-- The Euclidean inner product in coordinates: `⟨x,y⟩ = ∑ i, conj (x i) · y i`. -/
lemma inner_eq_sum (x y : EuclideanSpace ℂ ι) :
    inner ℂ x y = ∑ i, conj (x i) * y i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm]; rfl

/-- `z · conj z = ‖z‖²` (the `Complex.ofReal` form, used to keep the cast atom canonical). -/
lemma mul_conj_eq (z : ℂ) : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-! ## The headline -/

/-- **Swap test (output-probability identity).** For unit states `ψ, φ`, the ancilla-`0`
marginal probability is `(1 + |⟨ψ,φ⟩|²)/2`. The cross terms factor through the tensor
identity `⟨ψ⊗φ, φ⊗ψ⟩ = ⟨ψ,φ⟩·⟨φ,ψ⟩ = ‖⟨ψ,φ⟩‖²` (conjugate-linearity in the first
argument fixes the order). -/
theorem swap_test_prob (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    swapTestProb0 ψ φ = (1 + ‖inner ℂ ψ φ‖ ^ 2) / 2 := by
  have hpp : inner ℂ ψ ψ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  have hqq : inner ℂ φ φ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hφ]; norm_num
  -- per-cell expansion of `swapTest · conj swapTest` into four `(conj·)·(conj·)` products
  have hsum : ∀ i j, swapTest ψ φ (0, i, j) * conj (swapTest ψ φ (0, i, j))
      = (1 / 4 : ℂ) * ( (conj (ψ i) * ψ i) * (conj (φ j) * φ j)
                + (conj (φ i) * ψ i) * (conj (ψ j) * φ j)
                + (conj (ψ i) * φ i) * (conj (φ j) * ψ j)
                + (conj (φ i) * φ i) * (conj (ψ j) * ψ j) ) := by
    intro i j
    rw [swapTest_apply]
    simp only [map_mul, map_add, map_div₀, map_one, map_ofNat]
    ring
  -- the whole computation, cast to ℂ
  have hcast : ((swapTestProb0 ψ φ : ℝ) : ℂ)
      = (1 + ((‖inner ℂ ψ φ‖ ^ 2 : ℝ) : ℂ)) / 2 := by
    rw [swapTestProb0, Complex.ofReal_sum]
    have hinner : ∀ i, ((∑ j, ‖swapTest ψ φ (0, i, j)‖ ^ 2 : ℝ) : ℂ)
        = ∑ j, swapTest ψ φ (0, i, j) * conj (swapTest ψ φ (0, i, j)) := by
      intro i
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun j _ => (mul_conj_eq _).symm)
    simp only [hinner, hsum]
    simp only [← Finset.mul_sum]
    simp only [Finset.sum_add_distrib]
    simp only [← Finset.sum_mul_sum]
    simp only [← inner_eq_sum]
    rw [hpp, hqq,
        show inner ℂ φ ψ = conj (inner ℂ ψ φ) from (inner_conj_symm φ ψ).symm,
        mul_comm (conj (inner ℂ ψ φ)) (inner ℂ ψ φ), mul_conj_eq]
    ring
  exact_mod_cast hcast

/-- **Equal states:** `P(0) = 1` (overlap `1`). -/
theorem swap_test_equal (hψ : ‖ψ‖ = 1) : swapTestProb0 ψ ψ = 1 := by
  rw [swap_test_prob ψ ψ hψ hψ]
  have h : inner ℂ ψ ψ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  rw [h, norm_one]; norm_num

/-- **Orthogonal states:** `P(0) = 1/2` (overlap `0`). -/
theorem swap_test_orthogonal (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (h : inner ℂ ψ φ = 0) :
    swapTestProb0 ψ φ = 1 / 2 := by
  rw [swap_test_prob ψ φ hψ hφ, h, norm_zero]; norm_num

end SwapTest
end QM
end Empirical
end CSD
