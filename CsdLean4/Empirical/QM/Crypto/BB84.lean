/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.Protocols.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Empirical/QM: BB84 quantum-key-distribution security (intercept-resend QBER)

**Category:** 3-Local (QM-validity content, no CSD ontology).

BB84 (Bennett-Brassard 1984) encodes each bit in one of four states drawn from
two **mutually-unbiased** bases:

* Z basis: `|0⟩`, `|1⟩`;
* X basis: `|+⟩ = (|0⟩+|1⟩)/√2`, `|−⟩ = (|0⟩−|1⟩)/√2`.

An eavesdropper (Eve) who intercepts, measures, and **resends** cannot avoid
disturbing the channel whenever she guesses the basis wrong, because the Z and X
states are non-orthogonal. This is the information-disturbance tradeoff that makes
eavesdropping detectable.

## What this delivers (all Born-grounded)

The Born transition probability is `bornProb a b = ‖⟨a|b⟩‖²`, a genuine
probability for unit vectors. On the canonical sifted round (Alice sends `|0⟩` in
Z, Bob reads Z, Bob's error is the `|1⟩` outcome):

* `bb84_intercept_resend_right_basis` — Eve in the **matching** (Z) basis injects
  **no** error: `irErrorZ0 zBasis = 0` (`1·0 + 0·1`). She learns the bit for free.
* `bb84_intercept_resend_wrong_basis` — Eve in the **wrong** (X) basis injects
  error **½**: `irErrorZ0 xBasis = 1/2` (`(½)(½) + (½)(½)`).
* `bb84_qber` — **the headline QBER**: averaging over Eve's uniformly random basis
  choice, `(½)·0 + (½)·(½) = 1/4`. This is the ¼ sifted-key error rate that
  reveals intercept-resend eavesdropping.
* `bb84_no_eavesdrop_error_zero` — the honest baseline `bornProb |1⟩ |0⟩ = 0`:
  with no Eve, Bob's sifted bit equals Alice's.
* `bb84_eavesdropping_detectable` — `1/4 > 0`: the QBER strictly rises under
  intercept-resend, so eavesdropping is detectable.
* `bb84_states_nonorthogonal` — `⟨0|+⟩ = (√2)⁻¹ ≠ 0`: the root cause. Non-orthogonal
  states cannot be perfectly distinguished, so Eve cannot measure without disturbing.

## Honest scope

This proves the **intercept-resend QBER, its detectability, and the
non-orthogonality disturbance root**, all Born-grounded via `‖⟨a|b⟩‖²`. The
intercept-resend error is modelled as a **classical marginal over Eve's
measurement outcome** (Eve gets outcome `k` with Born probability
`bornProb (E k) |0⟩`, resends the eigenstate `E k`, and Bob then errs with Born
probability `bornProb |1⟩ (E k)`); no measurement-update / collapse operator is
needed for this content.

The **full composable finite-key security**, phrased via a measurement-*update*
(collapse) operator, remains **out of scope** — the same LF5 gate noted in
`Empirical/QM/Resources/Teleportation.lean` (the measurement step proper: collapse
of a superposition to a single classical outcome). This mirrors the E91 tranche,
which obtained finite-key confidence via CHSH **concentration**
(`Crypto/E91FiniteKey.lean`) rather than a collapse operator. Nothing beyond the
intercept-resend model is claimed here.

## References

* Bennett, Brassard 1984, *Proc. IEEE Int. Conf. Computers, Systems and Signal
  Processing*, 175 ("Quantum cryptography: Public key distribution and coin
  tossing"). The ¼ intercept-resend QBER is the standard eavesdropping signature.
* Cross-links: `Empirical/QM/Crypto/E91KeyRate.lean` (device-independent key rate),
  `Empirical/QM/Crypto/E91FiniteKey.lean` (finite-key via concentration),
  `Empirical/QM/Crypto/QuantumMoney.lean` (the same single-qubit BB84-state idiom),
  `Empirical/QM/QuantumEraser.lean` (Born probability from an amplitude),
  `Empirical/QM/Protocols/Basic.lean` (`SecurityBound`).
* `specs/future-work.md` — QKD security-model tranche (composable finite-key).
-/

@[expose] public section

open ComplexConjugate

namespace CSD
namespace Empirical
namespace BB84

/-! ### The four BB84 states -/

/-- Z-basis state `|0⟩ = e₀`. -/
noncomputable def ket0 : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 (1 : ℂ)

/-- Z-basis state `|1⟩ = e₁`. -/
noncomputable def ket1 : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 1 (1 : ℂ)

/-- X-basis state `|+⟩ = (e₀ + e₁)/√2`. -/
noncomputable def ketPlus : EuclideanSpace ℂ (Fin 2) :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (EuclideanSpace.single 0 (1 : ℂ) + EuclideanSpace.single 1 (1 : ℂ))

/-- X-basis state `|−⟩ = (e₀ − e₁)/√2`. -/
noncomputable def ketMinus : EuclideanSpace ℂ (Fin 2) :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (EuclideanSpace.single 0 (1 : ℂ) - EuclideanSpace.single 1 (1 : ℂ))

/-- **The Born transition probability** `bornProb a b = ‖⟨a|b⟩‖²`. A genuine
probability for unit vectors (`= |⟨a|b⟩|²`). -/
noncomputable def bornProb (a b : EuclideanSpace ℂ (Fin 2)) : ℝ :=
  ‖(inner ℂ a b : ℂ)‖ ^ 2

/-- `(√2⁻¹)² = ½`: `‖(√2:ℂ)⁻¹‖² = 1/2`. The only nonalgebraic fact used below. -/
lemma norm_sq_invSqrt2 : ‖((Real.sqrt 2 : ℂ)⁻¹)‖ ^ 2 = 1 / 2 := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2),
    inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- **Born probability is symmetric**: `bornProb a b = bornProb b a`. From
`inner_conj_symm` (`⟨a,b⟩ = conj ⟨b,a⟩`) and `Complex.norm_conj`. -/
theorem bornProb_comm (a b : EuclideanSpace ℂ (Fin 2)) : bornProb a b = bornProb b a := by
  have h : ‖(inner ℂ a b : ℂ)‖ = ‖(inner ℂ b a : ℂ)‖ := by
    rw [← inner_conj_symm a b, Complex.norm_conj]
  rw [bornProb, bornProb, h]

/-! ### Inner products of the BB84 states -/

/-- `⟨0|0⟩ = 1`. -/
lemma ket0_inner_ket0 : inner ℂ ket0 ket0 = (1 : ℂ) := by
  simp only [ket0, EuclideanSpace.inner_single_left, PiLp.single_apply, map_one]
  norm_num [Fin.ext_iff]

/-- `⟨1|1⟩ = 1`. -/
lemma ket1_inner_ket1 : inner ℂ ket1 ket1 = (1 : ℂ) := by
  simp only [ket1, EuclideanSpace.inner_single_left, PiLp.single_apply, map_one]
  norm_num [Fin.ext_iff]

/-- `⟨0|1⟩ = 0` (Z orthonormality). -/
lemma ket0_inner_ket1 : inner ℂ ket0 ket1 = (0 : ℂ) := by
  simp only [ket0, ket1, EuclideanSpace.inner_single_left, PiLp.single_apply, map_one]
  norm_num [Fin.ext_iff]

/-- `⟨1|0⟩ = 0` (Z orthonormality). -/
lemma ket1_inner_ket0 : inner ℂ ket1 ket0 = (0 : ℂ) := by
  simp only [ket1, ket0, EuclideanSpace.inner_single_left, PiLp.single_apply, map_one]
  norm_num [Fin.ext_iff]

/-- `⟨0|+⟩ = (√2)⁻¹` (mutually unbiased). -/
lemma ket0_inner_ketPlus : inner ℂ ket0 ketPlus = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp only [ket0, ketPlus, inner_smul_right, inner_add_right,
    EuclideanSpace.inner_single_left, PiLp.single_apply, map_one]
  norm_num [Fin.ext_iff]

/-- `⟨0|−⟩ = (√2)⁻¹` (mutually unbiased). -/
lemma ket0_inner_ketMinus : inner ℂ ket0 ketMinus = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp only [ket0, ketMinus, inner_smul_right, inner_sub_right,
    EuclideanSpace.inner_single_left, PiLp.single_apply, map_one]
  norm_num [Fin.ext_iff]

/-- `⟨1|+⟩ = (√2)⁻¹` (mutually unbiased). -/
lemma ket1_inner_ketPlus : inner ℂ ket1 ketPlus = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp only [ket1, ketPlus, inner_smul_right, inner_add_right,
    EuclideanSpace.inner_single_left, PiLp.single_apply, map_one]
  norm_num [Fin.ext_iff]

/-- `⟨1|−⟩ = −(√2)⁻¹` (mutually unbiased). -/
lemma ket1_inner_ketMinus : inner ℂ ket1 ketMinus = -(Real.sqrt 2 : ℂ)⁻¹ := by
  simp only [ket1, ketMinus, inner_smul_right, inner_sub_right,
    EuclideanSpace.inner_single_left, PiLp.single_apply, map_one]
  norm_num [Fin.ext_iff]

/-- `⟨+|0⟩ = (√2)⁻¹`. -/
lemma ketPlus_inner_ket0 : inner ℂ ketPlus ket0 = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp only [ketPlus, ket0, inner_smul_left, inner_add_left,
    EuclideanSpace.inner_single_left, PiLp.single_apply, map_inv₀, Complex.conj_ofReal, map_one]
  norm_num [Fin.ext_iff]

/-- `⟨−|0⟩ = (√2)⁻¹`. -/
lemma ketMinus_inner_ket0 : inner ℂ ketMinus ket0 = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp only [ketMinus, ket0, inner_smul_left, inner_sub_left,
    EuclideanSpace.inner_single_left, PiLp.single_apply, map_inv₀, Complex.conj_ofReal, map_one]
  norm_num [Fin.ext_iff]

/-! ### Born transition probabilities -/

/-- `bornProb |0⟩ |0⟩ = 1`. -/
lemma bornProb_ket0_ket0 : bornProb ket0 ket0 = 1 := by
  rw [bornProb, ket0_inner_ket0, norm_one, one_pow]

/-- `bornProb |1⟩ |1⟩ = 1`. -/
lemma bornProb_ket1_ket1 : bornProb ket1 ket1 = 1 := by
  rw [bornProb, ket1_inner_ket1, norm_one, one_pow]

/-- `bornProb |0⟩ |1⟩ = 0` (Z orthonormality). -/
lemma bornProb_ket0_ket1 : bornProb ket0 ket1 = 0 := by
  rw [bornProb, ket0_inner_ket1, norm_zero]; norm_num

/-- `bornProb |1⟩ |0⟩ = 0` (Z orthonormality). -/
lemma bornProb_ket1_ket0 : bornProb ket1 ket0 = 0 := by
  rw [bornProb, ket1_inner_ket0, norm_zero]; norm_num

/-- `bornProb |0⟩ |+⟩ = 1/2` (mutually unbiased). -/
lemma bornProb_ket0_ketPlus : bornProb ket0 ketPlus = 1 / 2 := by
  rw [bornProb, ket0_inner_ketPlus]; exact norm_sq_invSqrt2

/-- `bornProb |0⟩ |−⟩ = 1/2` (mutually unbiased). -/
lemma bornProb_ket0_ketMinus : bornProb ket0 ketMinus = 1 / 2 := by
  rw [bornProb, ket0_inner_ketMinus]; exact norm_sq_invSqrt2

/-- `bornProb |1⟩ |+⟩ = 1/2` (mutually unbiased). -/
lemma bornProb_ket1_ketPlus : bornProb ket1 ketPlus = 1 / 2 := by
  rw [bornProb, ket1_inner_ketPlus]; exact norm_sq_invSqrt2

/-- `bornProb |1⟩ |−⟩ = 1/2` (mutually unbiased). -/
lemma bornProb_ket1_ketMinus : bornProb ket1 ketMinus = 1 / 2 := by
  rw [bornProb, ket1_inner_ketMinus, norm_neg]; exact norm_sq_invSqrt2

/-- `bornProb |+⟩ |0⟩ = 1/2`. -/
lemma bornProb_ketPlus_ket0 : bornProb ketPlus ket0 = 1 / 2 := by
  rw [bornProb, ketPlus_inner_ket0]; exact norm_sq_invSqrt2

/-- `bornProb |−⟩ |0⟩ = 1/2`. -/
lemma bornProb_ketMinus_ket0 : bornProb ketMinus ket0 = 1 / 2 := by
  rw [bornProb, ketMinus_inner_ket0]; exact norm_sq_invSqrt2

/-! ### The intercept-resend eavesdropping model -/

/-- Eve's two measurement bases as `Fin 2 → EuclideanSpace ℂ (Fin 2)`. -/
noncomputable def zBasis : Fin 2 → EuclideanSpace ℂ (Fin 2) := ![ket0, ket1]

/-- Eve's X-basis eigenstates. -/
noncomputable def xBasis : Fin 2 → EuclideanSpace ℂ (Fin 2) := ![ketPlus, ketMinus]

/-- **Intercept-resend error probability** on the canonical sifted round (Alice
sends `|0⟩` in Z, Bob reads Z, error = the `|1⟩` outcome). A *classical marginal*
over Eve's outcome `k`: Eve gets `k` with Born probability `bornProb (E k) |0⟩`,
resends the eigenstate `E k`, and Bob then errs with Born probability
`bornProb |1⟩ (E k)`. -/
noncomputable def irErrorZ0 (E : Fin 2 → EuclideanSpace ℂ (Fin 2)) : ℝ :=
  ∑ k, bornProb (E k) ket0 * bornProb ket1 (E k)

/-- **Eve in the matching (Z) basis injects no error.** `irErrorZ0 zBasis = 0`
(`1·0 + 0·1`): guessing Alice's basis, Eve learns the bit and disturbs nothing. -/
theorem bb84_intercept_resend_right_basis : irErrorZ0 zBasis = 0 := by
  simp only [irErrorZ0, Fin.sum_univ_two, zBasis, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [bornProb_ket0_ket0, bornProb_ket1_ket0, bornProb_ket1_ket1]
  ring

/-- **Eve in the wrong (X) basis injects error ½.** `irErrorZ0 xBasis = 1/2`
(`(½)(½) + (½)(½)`): the information-disturbance tradeoff. -/
theorem bb84_intercept_resend_wrong_basis : irErrorZ0 xBasis = 1 / 2 := by
  simp only [irErrorZ0, Fin.sum_univ_two, xBasis, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [bornProb_ketPlus_ket0, bornProb_ket1_ketPlus, bornProb_ketMinus_ket0,
    bornProb_ket1_ketMinus]
  norm_num

/-- **The BB84 sifted-key QBER: ¼.** Averaging over Eve's uniformly random basis
choice, `(½)·irErrorZ0 zBasis + (½)·irErrorZ0 xBasis = 1/4`. This is the quantum
bit-error rate that reveals intercept-resend eavesdropping. -/
theorem bb84_qber :
    (1 / 2) * irErrorZ0 zBasis + (1 / 2) * irErrorZ0 xBasis = 1 / 4 := by
  rw [bb84_intercept_resend_right_basis, bb84_intercept_resend_wrong_basis]
  norm_num

/-- **Honest baseline: no eavesdropping, zero error.** With no Eve, Bob's sifted
bit equals Alice's: `bornProb |1⟩ |0⟩ = 0`. -/
theorem bb84_no_eavesdrop_error_zero : bornProb ket1 ket0 = 0 :=
  bornProb_ket1_ket0

/-- **Eavesdropping is detectable.** The QBER strictly rises above the honest
baseline under intercept-resend: `1/4 > 0`. -/
theorem bb84_eavesdropping_detectable :
    (1 / 2) * irErrorZ0 zBasis + (1 / 2) * irErrorZ0 xBasis > bornProb ket1 ket0 := by
  rw [bb84_intercept_resend_right_basis, bb84_intercept_resend_wrong_basis, bornProb_ket1_ket0]
  norm_num

/-- **The non-orthogonality disturbance root.** The Z and X states are
non-orthogonal, `⟨0|+⟩ = (√2)⁻¹ ≠ 0`. This is *why* Eve cannot measure without
disturbing: non-orthogonal states cannot be perfectly distinguished. -/
theorem bb84_states_nonorthogonal : (inner ℂ ket0 ketPlus : ℂ) ≠ 0 := by
  rw [ket0_inner_ketPlus]
  have hsqrt_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hsqrt_pos
  exact inv_ne_zero this

/-! ### `Protocols.SecurityBound` tie -/

/-- The per-signal disturbance rate Eve induces in the mismatched (X) basis,
recorded as a `Protocols.SecurityBound` with `ε = 1/2`. The honest reading:
"in the mismatched case Eve's tampering flips the sifted bit with probability
`½`" (equivalently, her per-signal guessing advantage saturates at `½`). A minimal
stand-in, not a min-entropy / composable accounting. -/
noncomputable def bb84Security : Protocols.SecurityBound where
  ε := 1 / 2
  ε_nonneg := by norm_num
  ε_le_one := by norm_num

/-- **The mismatched-basis intercept-resend error equals the declared security
bound.** `irErrorZ0 xBasis = bb84Security.ε = 1/2`. This makes `SecurityBound`
load-bearing: its `ε` is the *proved* mismatched-basis disturbance rate, not a
decorative constant. -/
theorem bb84_mismatched_error_eq_security : irErrorZ0 xBasis = bb84Security.ε := by
  rw [bb84_intercept_resend_wrong_basis]; rfl

end BB84
end Empirical
end CSD
