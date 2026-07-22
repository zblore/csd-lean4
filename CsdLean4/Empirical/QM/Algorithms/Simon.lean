/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Mathlib.QuantumInfo.Hadamard

/-!
# Simon's algorithm

**Category:** 3-Local (QM-validity).

Simon's problem: given `f : {0,1}ⁿ → {0,1}ⁿ` with the promise `f x = f x' ↔ x' = x ⊕ s`
for a hidden nonzero period `s`, find `s`. After querying `U_f` once and measuring the
*second* register, the first register collapses to a **coset state**

  `|x₀⟩ + |x₀ ⊕ s⟩`  (up to normalisation)

for some `x₀` (the measured second-register value's preimage). Applying `H^⊗n` to this coset
state and measuring yields, by the Born rule, an outcome `y` whose amplitude is

  `simon_amplitude : (1/√2)^{n+1} · (-1)^{⟨x₀,y⟩} · (1 + (-1)^{⟨s,y⟩})`.

The factor `1 + (-1)^{⟨s,y⟩}` vanishes when `⟨s,y⟩` is odd, so:

* `simon_orthogonal`: every measured `y` satisfies `⟨s,y⟩ ≡ 0 (mod 2)` — i.e. `y ⊥ s` — the
  **Simon promise**; outcomes non-orthogonal to the hidden `s` have probability `0`;
* `simon_uniform`: every `y ∈ s^⊥` carries the **same** probability `2/2ⁿ`. (What is proved in
  Lean is this per-outcome *equal value*; the distributional reading — that these are `2^{n-1}`
  outcomes whose probabilities sum to `1` for `s ≠ 0`, i.e. genuine uniformity on `s^⊥` — rests
  on `|s^⊥| = 2^{n-1}`, which is the classical remark below, not a Lean theorem here.)

**Honest scope.** This is the single-register *reduced* analysis: the second register is
measured (or traced out) first, which is the standard textbook reduction; we do not model the
full two-register tensor circuit `H^⊗n ∘ U_f ∘ H^⊗n` nor the classical post-processing.
The classical recovery is a remark: the valid-outcome set `{y : ⟨s,y⟩ even}` is the
hyperplane `s^⊥ ⊆ 𝔽₂ⁿ`, so `n-1` independent uniform samples from it determine `s` by
Gaussian elimination over `𝔽₂` with high probability. This file captures the quantum core
(promise + uniformity), needing only the Hadamard action on basis states — not `Hn`
unitarity.

The hypothesis `s ≠ 0` is *not* load-bearing for `simon_uniform` (the amplitude formula and
hence the probability `2/2ⁿ` hold for every `s`, including `s = 0` where the coset state is
the unnormalised `√2 |x₀⟩`); it is retained for the physical reading (a genuine 2-element
coset). It *is* load-bearing for `cosetState_normalized` (norm `1` requires the two basis
states to be distinct).
-/

open scoped ComplexConjugate
open QuantumInfo

namespace CSD
namespace Empirical
namespace QM
namespace Simon

variable {n : ℕ}

/-- The **bitwise inner product** `⟨x,y⟩ = ∑ᵢ xᵢ yᵢ` of two bitstrings, as a natural number
(its parity is all that matters for the sign `(-1)^{⟨x,y⟩}`). -/
def bitInner (x y : Fin n → Fin 2) : ℕ := ∑ i, (x i).val * (y i).val

/-- **Bitwise XOR** `(x ⊕ s)ᵢ = xᵢ + sᵢ` (addition in `Fin 2` is XOR). -/
def bxor (x s : Fin n → Fin 2) : Fin n → Fin 2 := fun i => x i + s i

/-- The bitwise inner product is symmetric. -/
lemma bitInner_comm (x y : Fin n → Fin 2) : bitInner x y = bitInner y x :=
  Finset.sum_congr rfl fun i _ => Nat.mul_comm (x i).val (y i).val

/-- **General Hadamard entry as a sign over a single denominator:**
`Hn x y = (-1)^{⟨x,y⟩} / (√2)ⁿ`. The per-qubit signs collect into one parity sign and the
per-qubit `√2` factors into `(√2)ⁿ`. -/
lemma Hn_apply_inner (x y : Fin n → Fin 2) :
    Hn x y = (-1) ^ (bitInner x y) / (Real.sqrt 2 : ℂ) ^ n := by
  simp only [bitInner, Hn_apply, hadEntry]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_pow_eq_pow_sum]

/-- **XOR sign-additivity:** `(-1)^{⟨x₀ ⊕ s, y⟩} = (-1)^{⟨x₀,y⟩} · (-1)^{⟨s,y⟩}`.
Per qubit, `(x₀ᵢ + sᵢ)·yᵢ ≡ x₀ᵢ·yᵢ + sᵢ·yᵢ (mod 2)`; summing and using that `(-1)^·`
depends only on parity gives the identity. -/
lemma neg_one_bitInner_bxor (x₀ s y : Fin n → Fin 2) :
    (-1 : ℂ) ^ (bitInner (bxor x₀ s) y)
      = (-1) ^ (bitInner x₀ y) * (-1) ^ (bitInner s y) := by
  rw [← pow_add, neg_one_pow_eq_pow_mod_two,
      neg_one_pow_eq_pow_mod_two (bitInner x₀ y + bitInner s y)]
  congr 1
  simp only [bitInner, bxor]
  rw [← Finset.sum_add_distrib,
      Finset.sum_nat_mod _ 2 (fun i => (x₀ i + s i).val * (y i).val),
      Finset.sum_nat_mod _ 2 (fun i => (x₀ i).val * (y i).val + (s i).val * (y i).val)]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have key : ∀ a b c : Fin 2,
      ((a + b).val * c.val) % 2 = (a.val * c.val + b.val * c.val) % 2 := by decide
  exact key (x₀ i) (s i) (y i)

/-- The **coset state** `(1/√2)(|x₀⟩ + |x₀ ⊕ s⟩)`: the first-register state after the oracle
query and the second-register measurement. -/
noncomputable def cosetState (x₀ s : Fin n → Fin 2) : QReg n :=
  (Real.sqrt 2 : ℂ)⁻¹ • (basisState x₀ + basisState (bxor x₀ s))

/-- **Simon's circuit (reduced):** apply `H^⊗n` to the coset state, then measure. -/
noncomputable def simonCircuit (x₀ s : Fin n → Fin 2) : QReg n :=
  applyHn (cosetState x₀ s)

/-- `H^⊗n` is additive (it is the linear map `Matrix.toEuclideanLin Hn`). -/
lemma applyHn_add (ψ φ : QReg n) : applyHn (ψ + φ) = applyHn ψ + applyHn φ := by
  simp only [applyHn, map_add]

/-- `H^⊗n` is `ℂ`-homogeneous. -/
lemma applyHn_smul (c : ℂ) (ψ : QReg n) : applyHn (c • ψ) = c • applyHn ψ := by
  simp only [applyHn, map_smul]

/-- `H^⊗n` of a basis state picks out a Hadamard column: `applyHn |x⟩ y = Hn y x`. -/
lemma applyHn_basisState (x y : Fin n → Fin 2) : applyHn (basisState x) y = Hn y x := by
  rw [applyHn_apply, Finset.sum_eq_single x]
  · rw [basisState_apply, if_pos rfl, mul_one]
  · intro x' _ hx'; rw [basisState_apply, if_neg hx', mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The Simon amplitude.** Measuring outcome `y` after `H^⊗n` on the coset state has
amplitude `(1/√2)^{n+1} · (-1)^{⟨x₀,y⟩} · (1 + (-1)^{⟨s,y⟩})`. -/
theorem simon_amplitude (x₀ s y : Fin n → Fin 2) :
    simonCircuit x₀ s y
      = ((Real.sqrt 2 : ℂ)⁻¹) ^ (n + 1) * (-1) ^ (bitInner x₀ y)
          * (1 + (-1) ^ (bitInner s y)) := by
  rw [simonCircuit, cosetState, applyHn_smul, applyHn_add, PiLp.smul_apply, PiLp.add_apply,
      applyHn_basisState, applyHn_basisState, smul_eq_mul, Hn_apply_inner, Hn_apply_inner,
      bitInner_comm y x₀, bitInner_comm y (bxor x₀ s), neg_one_bitInner_bxor]
  rw [pow_succ', inv_pow]
  ring

/-- **Simon's promise:** if `⟨s,y⟩` is odd, then `y` is *never* measured — `prob = 0`.
Every outcome is orthogonal to the hidden period `s` over `𝔽₂`. -/
theorem simon_orthogonal (x₀ s y : Fin n → Fin 2) (hodd : Odd (bitInner s y)) :
    prob (simonCircuit x₀ s) y = 0 := by
  rw [prob, simon_amplitude, hodd.neg_one_pow, add_neg_cancel, mul_zero, norm_zero]
  norm_num

/-- **Uniformity on `s^⊥`:** if `⟨s,y⟩` is even (so `y ⊥ s`), the outcome `y` has probability
`2/2ⁿ`. The valid outcomes are uniform over the `2^{n-1}`-element hyperplane `s^⊥`.

`hs : s ≠ 0` is *not* load-bearing here (the formula holds for all `s`); see the module
docstring. -/
theorem simon_uniform (x₀ s y : Fin n → Fin 2) (hs : s ≠ 0)
    (heven : Even (bitInner s y)) :
    prob (simonCircuit x₀ s) y = 2 / 2 ^ n := by
  rw [prob, simon_amplitude, heven.neg_one_pow, show (1 + (1 : ℂ)) = 2 from by norm_num]
  have hn1 : ‖((Real.sqrt 2 : ℂ)⁻¹)‖ = (Real.sqrt 2)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]
  have hsq : ((Real.sqrt 2)⁻¹) ^ 2 = (2 : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [norm_mul, norm_mul, norm_pow, hn1, norm_pow, norm_neg, norm_one, one_pow,
      Complex.norm_ofNat, mul_one, mul_pow, ← pow_mul, Nat.mul_comm (n + 1) 2, pow_mul, hsq,
      eq_div_iff (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)), inv_pow, pow_succ]
  field_simp

/-- **The coset state is normalised** (when `s ≠ 0`): the two computational-basis components
are distinct, hence orthonormal, so `‖|x₀⟩ + |x₀ ⊕ s⟩‖ = √2` and the `(1/√2)` prefactor gives
norm `1`. -/
theorem cosetState_normalized (x₀ s : Fin n → Fin 2) (hs : s ≠ 0) :
    ‖cosetState x₀ s‖ = 1 := by
  have hne : bxor x₀ s ≠ x₀ := by
    intro h
    apply hs
    funext i
    have hi : x₀ i + s i = x₀ i := by
      have := congrFun h i; simpa only [bxor] using this
    have h2 : x₀ i + s i = x₀ i + 0 := by rw [add_zero]; exact hi
    simpa only [Pi.zero_apply] using add_left_cancel h2
  have hnorm : ‖basisState x₀ + basisState (bxor x₀ s)‖ = Real.sqrt 2 := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    have hpt : ∀ z : Fin n → Fin 2,
        ‖(basisState x₀ + basisState (bxor x₀ s)) z‖ ^ 2
          = (if z = x₀ then (1 : ℝ) else 0) + (if z = bxor x₀ s then 1 else 0) := by
      intro z
      rw [PiLp.add_apply, basisState_apply, basisState_apply]
      by_cases h1 : z = x₀
      · by_cases h2 : z = bxor x₀ s
        · exact absurd (h1.symm.trans h2) (fun hc => hne hc.symm)
        · simp only [if_pos h1, if_neg h2]; norm_num
      · by_cases h2 : z = bxor x₀ s
        · simp only [if_neg h1, if_pos h2]; norm_num
        · simp only [if_neg h1, if_neg h2]; norm_num
    simp only [hpt, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq' Finset.univ x₀ (fun _ => (1 : ℝ)),
        Finset.sum_ite_eq' Finset.univ (bxor x₀ s) (fun _ => (1 : ℝ))]
    simp only [Finset.mem_univ, if_true]
    norm_num
  rw [cosetState, norm_smul, hnorm, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2),
      inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num))]

end Simon
end QM
end Empirical
end CSD
