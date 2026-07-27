/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.NoCloning
public import CsdLean4.Empirical.QM.Crypto.BB84

/-!
# Empirical/QM: B92 quantum-key-distribution security (two-state protocol)

**Category:** 3-Local (QM-validity content, no CSD ontology).

B92 (Bennett 1992) is the minimal QKD protocol: Alice encodes each bit in one of
just **two non-orthogonal** states,

* bit `0` → `|0⟩`,
* bit `1` → `|+⟩ = (|0⟩+|1⟩)/√2`,

and Bob performs **unambiguous state discrimination**. Because the two encodings
are non-orthogonal they cannot be perfectly cloned or distinguished, so an
eavesdropper cannot copy the signal without disturbance — the security root is
exactly no-cloning, reused verbatim from `Empirical/QM/NoCloning.lean` (the two
B92 encoding states *are* the Wiesner pair `|0⟩`, `|+⟩`).

Bob's discrimination is **error-free on conclusive events** thanks to two
zero-overlaps:

* Bob measures `Z`; the outcome `|1⟩` is impossible from `|0⟩`
  (`|⟨1|0⟩|² = 0`), so a `|1⟩` click conclusively signals **bit 1**.
* Bob measures `X`; the outcome `|−⟩` is impossible from `|+⟩`
  (`|⟨−|+⟩|² = 0`), so a `|−⟩` click conclusively signals **bit 0**.

A conclusive click occurs, per matched round, with Born probability `½`
(`bornProb |1⟩ |+⟩ = ½`, `bornProb |−⟩ |0⟩ = ½`); the complementary events are
inconclusive and discarded, never wrong.

This module reuses the Born layer of `Crypto/BB84.lean` (`ket0, ket1, ketPlus,
ketMinus, bornProb, bornProb_comm`, and the proved transition values). The only
new inner product it establishes is the `X`-basis orthogonality
`⟨−|+⟩ = 0`, which BB84 did not need.

## What this delivers (all Born-grounded)

* `b92_encode` — the encoding map `Bool → EuclideanSpace ℂ (Fin 2)`
  (`false ↦ |0⟩`, `true ↦ |+⟩`): the states have a genuine protocol consumer.
* `b92_nonorthogonal` — `⟨0|+⟩ ≠ 0`: the resource (reuses BB84).
* `b92_unambiguous_one` — `bornProb |1⟩ |0⟩ = 0`: a `|1⟩` (`Z`) click excludes
  the bit-0 state `|0⟩`, so it is conclusive for bit 1.
* `b92_unambiguous_zero` — `bornProb |−⟩ |+⟩ = 0`: a `|−⟩` (`X`) click excludes
  the bit-1 state `|+⟩`, so it is conclusive for bit 0.
* `b92_conclusive_rate_one` — `bornProb |1⟩ |+⟩ = ½`: matched-round conclusive
  rate for bit 1.
* `b92_conclusive_rate_zero` — `bornProb |−⟩ |0⟩ = ½`: matched-round conclusive
  rate for bit 0.
* `b92_no_perfect_eavesdrop` — the security capstone: no universal cloner can
  copy both encoding states `|0⟩` and `|+⟩` against a fixed blank, an exact
  instance of `NoCloning.no_universal_cloner_of_witness` (same shape as
  `quantum_money_unforgeable`).

## Honest scope

This proves the B92 **unambiguous-discrimination structure** (error-free
conclusive events + `½` conclusive rates) and the **no-cloning security root**,
all Born-grounded via `‖⟨a|b⟩‖²`. The conclusive events are modelled as Born
zero-overlaps; no measurement-update / collapse operator is used.

The **full composable finite-key security** — phrased via a measurement-*update*
(collapse) operator turning an unambiguous-discrimination POVM into a sifted key
with a min-entropy accounting — stays **out of scope**, the same LF5 gate noted in
`Crypto/BB84.lean` and `Empirical/QM/Resources/Teleportation.lean`. Nothing beyond
the unambiguous-discrimination model and no-cloning is claimed here.

## References

* Bennett 1992, *Phys. Rev. Lett.* **68**, 3121 ("Quantum cryptography using any
  two nonorthogonal states"): the two-state protocol and its unambiguous-
  discrimination reading.
* Cross-links: `Empirical/QM/Crypto/BB84.lean` (the reused Born layer and
  intercept-resend QBER), `Empirical/QM/Crypto/QuantumMoney.lean` (the same
  no-cloning witness idiom on the `|0⟩`, `|+⟩` pair),
  `Empirical/QM/NoCloning.lean` (`no_universal_cloner_of_witness`).
* `specs/future-work.md` — QKD security-model tranche (composable finite-key).
-/

@[expose] public section

open ComplexConjugate
open CSD.Empirical.BB84

namespace CSD
namespace Empirical
namespace B92

/-! ### The B92 encoding map -/

/-- **The B92 encoding map.** Alice encodes bit `false` as `|0⟩` and bit `true`
as `|+⟩`; the two encodings are non-orthogonal (`b92_nonorthogonal`). -/
noncomputable def b92_encode : Bool → EuclideanSpace ℂ (Fin 2)
  | false => ket0
  | true => ketPlus

@[simp] lemma b92_encode_false : b92_encode false = ket0 := rfl

@[simp] lemma b92_encode_true : b92_encode true = ketPlus := rfl

/-! ### Supporting facts on the two encoding states -/

/-- `(√2⁻¹)² = ½`, the only nonalgebraic fact used below. -/
lemma half : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- `‖|0⟩‖ = 1` (from BB84's `⟨0|0⟩ = 1`). -/
lemma ket0_unit : ‖ket0‖ = 1 := by
  have hsq : ‖ket0‖ ^ 2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) ket0, ket0_inner_ket0]; simp
  calc ‖ket0‖ = Real.sqrt (‖ket0‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt 1 := by rw [hsq]
    _ = 1 := Real.sqrt_one

/-- `⟨+|+⟩ = 1`, used to get `‖|+⟩‖ = 1`. -/
lemma ketPlus_inner_self : inner ℂ ketPlus ketPlus = (1 : ℂ) := by
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

/-- **`X`-basis orthogonality** `⟨−|+⟩ = 0`. Not needed by BB84; it is the second
zero-overlap that makes a `|−⟩` click conclusive for bit 0. -/
lemma ketMinus_inner_ketPlus : inner ℂ ketMinus ketPlus = (0 : ℂ) := by
  simp only [ketMinus, ketPlus, inner_smul_left, inner_smul_right, inner_sub_left,
    inner_add_right, EuclideanSpace.inner_single_left, PiLp.single_apply,
    map_inv₀, Complex.conj_ofReal, map_one]
  norm_num [Fin.ext_iff]

/-- The B92 encoding pair is non-orthogonal and not equal up to phase:
`⟨0|+⟩ ∉ {0, 1}`. This is the witness that drives `b92_no_perfect_eavesdrop`. -/
lemma b92_encoding_witness :
    inner ℂ ket0 ketPlus ≠ 0 ∧ inner ℂ ket0 ketPlus ≠ 1 := by
  rw [ket0_inner_ketPlus]
  have hsqrt_ne_one : Real.sqrt 2 ≠ 1 := by
    intro h
    have : (Real.sqrt 2) * (Real.sqrt 2) = 2 := Real.mul_self_sqrt (by norm_num)
    rw [h] at this
    norm_num at this
  have hsqrt_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨inv_ne_zero (by exact_mod_cast ne_of_gt hsqrt_pos), ?_⟩
  intro h
  exact hsqrt_ne_one (by exact_mod_cast (inv_eq_one.mp h))

/-! ### The B92 security theorems -/

/-- **The non-orthogonality resource.** The two B92 encoding states are
non-orthogonal, `⟨0|+⟩ ≠ 0` (reuses BB84). This is *why* Bob's discrimination is
only ever conclusive with probability `< 1`, and *why* Eve cannot clone. -/
theorem b92_nonorthogonal : (inner ℂ ket0 ketPlus : ℂ) ≠ 0 :=
  bb84_states_nonorthogonal

/-- **Conclusive detection of bit 1 is error-free.** A `|1⟩` (`Z`) click is
impossible from the bit-0 state `|0⟩`: `bornProb |1⟩ |0⟩ = 0`. So whenever Bob
reads `|1⟩` he conclusively knows Alice sent bit 1. -/
theorem b92_unambiguous_one : bornProb ket1 ket0 = 0 :=
  bornProb_ket1_ket0

/-- **Conclusive detection of bit 0 is error-free.** A `|−⟩` (`X`) click is
impossible from the bit-1 state `|+⟩`: `bornProb |−⟩ |+⟩ = 0`. So whenever Bob
reads `|−⟩` he conclusively knows Alice sent bit 0. -/
theorem b92_unambiguous_zero : bornProb ketMinus ketPlus = 0 := by
  rw [bornProb, ketMinus_inner_ketPlus, norm_zero]; norm_num

/-- **Matched-round conclusive rate for bit 1.** When Alice sends bit 1 (`|+⟩`)
and Bob measures `Z`, he gets the conclusive `|1⟩` click with Born probability
`½`: `bornProb |1⟩ |+⟩ = ½`. -/
theorem b92_conclusive_rate_one : bornProb ket1 ketPlus = 1 / 2 :=
  bornProb_ket1_ketPlus

/-- **Matched-round conclusive rate for bit 0.** When Alice sends bit 0 (`|0⟩`)
and Bob measures `X`, he gets the conclusive `|−⟩` click with Born probability
`½`: `bornProb |−⟩ |0⟩ = ½`. -/
theorem b92_conclusive_rate_zero : bornProb ketMinus ket0 = 1 / 2 :=
  bornProb_ketMinus_ket0

/-- **B92 no-perfect-eavesdropping (security capstone).** Over any tensor
structure with the inner-product factorisation `⟨tensor a b, tensor c d⟩ =
⟨a,c⟩·⟨b,d⟩` and a fixed unit blank `e0`, no isometry can clone both B92 encoding
states `|0⟩` and `|+⟩` against the same blank. Because the two encodings are
non-orthogonal (`b92_encoding_witness`), Eve cannot copy Alice's signal — she
cannot eavesdrop without disturbance. An exact instance of
`NoCloning.no_universal_cloner_of_witness`, the same shape as
`quantum_money_unforgeable`. -/
theorem b92_no_perfect_eavesdrop
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
    ket0 ketPlus ket0_unit ketPlus_unit b92_encoding_witness

end B92
end Empirical
end CSD
