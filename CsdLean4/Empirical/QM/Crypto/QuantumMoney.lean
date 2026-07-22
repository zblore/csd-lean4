/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Empirical.QM.NoCloning
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Empirical/QM: Wiesner quantum money (unforgeability)

**Category:** 3-Local (promotion-ready to 2-Framework on demand).

Wiesner's quantum money (Wiesner 1983): a banknote carries qubits each
prepared in one of the four BB84 states, secret to the bank. A forger
who could duplicate an unknown banknote would, in particular, clone a
single unknown qubit drawn from two non-orthogonal alternatives — which
the no-cloning theorem forbids. Unforgeability is therefore a corollary
of no-cloning.

This file makes the witness **concrete**: the two non-orthogonal money
states `|0⟩` and `|+⟩` in `EuclideanSpace ℂ (Fin 2)` satisfy
`⟨0|+⟩ = 1/√2 ∉ {0, 1}`, so `no_universal_cloner_of_witness`
(`Empirical/QM/NoCloning.lean`) rules out any forging isometry that
clones both against a fixed blank. The result is not a reworded alias of
no-cloning: the content is the proved non-orthogonality of a named,
operationally meaningful state pair.

## Source

Wiesner 1983, *SIGACT News* **15**(1), 78 ("Conjugate Coding");
unforgeability via Wootters-Zurek 1982 / Dieks 1982 no-cloning.
-/

open ComplexConjugate

namespace CSD
namespace Empirical
namespace QuantumMoney

/-- Money state `|0⟩ = e₀`. -/
noncomputable def ket0 : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 (1 : ℂ)

/-- Money state `|+⟩ = (e₀ + e₁)/√2`. -/
noncomputable def ketPlus : EuclideanSpace ℂ (Fin 2) :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (EuclideanSpace.single 0 (1 : ℂ) + EuclideanSpace.single 1 (1 : ℂ))

/-- `(√2⁻¹)² = ½`, the only nonalgebraic fact used below. -/
private lemma half : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- `⟨0|0⟩ = 1`, used to get `‖|0⟩‖ = 1`. -/
private lemma ket0_inner_self : inner ℂ ket0 ket0 = (1 : ℂ) := by
  simp only [ket0, EuclideanSpace.inner_single_left, PiLp.single_apply, map_one]
  norm_num [Fin.ext_iff]

/-- `‖|0⟩‖ = 1`. -/
lemma ket0_unit : ‖ket0‖ = 1 := by
  have hsq : ‖ket0‖ ^ 2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) ket0, ket0_inner_self]; simp
  calc ‖ket0‖ = Real.sqrt (‖ket0‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt 1 := by rw [hsq]
    _ = 1 := Real.sqrt_one

/-- `⟨0|+⟩ = 1/√2`. -/
lemma wiesner_inner : inner ℂ ket0 ketPlus = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp only [ket0, ketPlus, inner_smul_right, inner_add_right,
    EuclideanSpace.inner_single_left, PiLp.single_apply, map_one]
  norm_num [Fin.ext_iff]

/-- `⟨+|+⟩ = 1`, used to get `‖|+⟩‖ = 1`. -/
private lemma ketPlus_inner_self : inner ℂ ketPlus ketPlus = (1 : ℂ) := by
  simp only [ketPlus, inner_smul_left, inner_smul_right, inner_add_left,
    inner_add_right, EuclideanSpace.inner_single_left, PiLp.single_apply,
    map_inv₀, Complex.conj_ofReal, map_one]
  norm_num [Fin.ext_iff]
  linear_combination (2 : ℂ) * half

/-- `‖|+⟩‖ = 1`. -/
lemma ketPlus_unit : ‖ketPlus‖ = 1 := by
  have hsq : ‖ketPlus‖ ^ 2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) ketPlus, ketPlus_inner_self]; simp
  calc ‖ketPlus‖ = Real.sqrt (‖ketPlus‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt 1 := by rw [hsq]
    _ = 1 := Real.sqrt_one

/-- The Wiesner states are non-orthogonal and not equal up to phase:
`⟨0|+⟩ ∉ {0, 1}`. This is the witness that drives unforgeability. -/
lemma wiesner_nonorthogonal :
    inner ℂ ket0 ketPlus ≠ 0 ∧ inner ℂ ket0 ketPlus ≠ 1 := by
  rw [wiesner_inner]
  -- `√2 ≠ 1` (since `√2·√2 = 2 ≠ 1`), and `√2 ≠ 0`.
  have hsqrt_ne_one : Real.sqrt 2 ≠ 1 := by
    intro h
    have : (Real.sqrt 2) * (Real.sqrt 2) = 2 :=
      Real.mul_self_sqrt (by norm_num)
    rw [h] at this
    norm_num at this
  have hsqrt_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  constructor
  · -- `(↑√2)⁻¹ ≠ 0`
    have : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hsqrt_pos
    exact inv_ne_zero this
  · -- `(↑√2)⁻¹ ≠ 1`
    intro h
    apply hsqrt_ne_one
    have : (Real.sqrt 2 : ℂ) = 1 := inv_eq_one.mp h
    exact_mod_cast this

/-- **Quantum money unforgeability (Wiesner).** Over any tensor structure
with the inner-product factorisation `⟨tensor a b, tensor c d⟩ =
⟨a,c⟩·⟨b,d⟩` and a fixed unit blank `e0 : Htensor`-side input space, no
isometry can forge (clone) both Wiesner money states `|0⟩` and `|+⟩`
against the same blank. Immediate from `no_universal_cloner_of_witness`
applied to the proved non-orthogonality witness `wiesner_nonorthogonal`.

`H := EuclideanSpace ℂ (Fin 2)` is the single-qubit money space; the
tensor target `Htensor` and the factorising `tensor` are supplied by the
caller (e.g. the Kronecker product on `EuclideanSpace ℂ (Fin 2 × Fin 2)`),
exactly as in `no_cloning_two_state`. -/
theorem quantum_money_unforgeable
    {Htensor : Type*} [NormedAddCommGroup Htensor] [InnerProductSpace ℂ Htensor]
    (tensor : EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2) → Htensor)
    (h_tensor_inner : ∀ a b c d : EuclideanSpace ℂ (Fin 2),
      inner ℂ (tensor a b) (tensor c d) = inner ℂ a c * inner ℂ b d)
    (e0 : EuclideanSpace ℂ (Fin 2)) (he0 : ‖e0‖ = 1) :
    ¬ ∃ U : Htensor → Htensor,
        (∀ x y, inner ℂ (U x) (U y) = inner ℂ x y) ∧
        U (tensor ket0 e0) = tensor ket0 ket0 ∧
        U (tensor ketPlus e0) = tensor ketPlus ketPlus :=
  NoCloning.no_universal_cloner_of_witness tensor h_tensor_inner e0 he0
    ket0 ketPlus ket0_unit ketPlus_unit wiesner_nonorthogonal

end QuantumMoney
end Empirical
end CSD
