/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneRecovery
public import CsdLean4.Mathlib.Probability.CodeCapacityThreshold

/-!
# The Steane code under independent noise: the code-capacity failure bound and the threshold

**Category:** 3-Local (Empirical, QM twin). BACKLOG #51, the part (c) of row 14 (`R-003`): the sentence
link 12 of `docs/FROM-POSTULATES-TO-QUANTUM-COMPUTERS.md` lacked.

Each of the seven qubits independently suffers an error with probability at most `p` — any
per-qubit noise alphabet, read through a map to the single-qubit Paulis — and the recovery channel
of `SteaneRecovery.lean` is applied. The recovery undoes every single-qubit Pauli
(`exists_steane_recovery`), so the encoded state is restored unless **two or more** qubits are hit;
by the union bound over pairs (`measure_pi_two_or_more_le`) that has probability at most
`C(7, 2) p² = 21 p²`. Concatenation replaces `p` by `21 p²` at every level
(`concatMeasure_concatBad_le`), so `k` levels give `(21 p)^{2^k} / 21`: below `p` when
`p ≤ 1/21`, and tending to `0` when `p < 1/21` — **the code-capacity threshold of the Steane
code**.

* `patA`, `patB`, `patErr` — the Pauli labels and the error operator of an error pattern;
* `exists_singleErr_of_card_le_one` — a pattern with at most one error is a single-qubit Pauli;
* ★★ `steane_codeCapacity_failure_le` — **the failure bound**: for every code state `ρ`, the
  probability that the recovery does not return `ρ` is at most `21 p²`;
* ★ `steane_concatBad_le` — the bad patterns of the `k`-fold concatenated Steane code have
  probability at most `(21 p)^{2^k} / 21`; ★ `steane_threshold` — below `p < 1/21` that bound
  tends to `0`.

## Honest scope

⚠️ **Code capacity, level one quantum.** The quantum statement is at level `1`: an encoded block
whose pattern has at most one error is restored exactly. At higher levels the theorem is the
pattern recursion of the code-capacity argument (the probability that two or more sub-blocks are
bad); the concatenated *quantum* recovery — decode each block, correct the resulting block errors
with the next level's code, which corrects an arbitrary error on one block because the Paulis
span the operators of a qubit — is BACKLOG #61. The circuit-level threshold theorem (faulty
gates, error propagation through gadgets, extended rectangles) is not attempted: BACKLOG #62.

References: A. Steane, *Error correcting codes in quantum theory*, PRL 77 (1996); E. Knill,
R. Laflamme, W. Zurek, Science 279 (1998); `Empirical/QM/QEC/SteaneRecovery.lean`;
`Mathlib/Probability/CodeCapacityThreshold.lean`; `specs/BACKLOG.md` #51; `specs/steane-plan.md`.
-/

@[expose] public section

open Matrix QuantumInfo MeasureTheory Filter Topology
open scoped ENNReal

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

section Patterns

variable {α : Type*}

/-- The `X`-label of an error pattern: `1` at the qubits carrying `X` or `XZ`. -/
def patA (err : α → Option (Fin 3)) (x : Fin 7 → α) : Fin 7 → Fin 2 := fun i =>
  match err (x i) with
  | none => 0
  | some t => if t = 1 then 0 else 1

/-- The `Z`-label of an error pattern: `1` at the qubits carrying `Z` or `XZ`. -/
def patB (err : α → Option (Fin 3)) (x : Fin 7 → α) : Fin 7 → Fin 2 := fun i =>
  match err (x i) with
  | none => 0
  | some t => if t = 0 then 0 else 1

/-- The error operator of a pattern: the Pauli with the pattern's labels. -/
noncomputable def patErr (err : α → Option (Fin 3)) (x : Fin 7 → α) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  pauliMat (patA err x) (patB err x)

/-- A pattern with at most one error is a single-qubit Pauli (or the identity). -/
theorem exists_singleErr_of_card_le_one (err : α → Option (Fin 3)) (x : Fin 7 → α)
    (hx : (Finset.univ.filter fun i => err (x i) ≠ none).card ≤ 1) :
    ∃ e : SingleErr, patA err x = errA e ∧ patB err x = errB e := by
  by_cases h : ∀ i, err (x i) = none
  · refine ⟨none, ?_, ?_⟩
    · funext i
      simp [patA, errA, h i]
    · funext i
      simp [patB, errB, h i]
  · push Not at h
    obtain ⟨j, hj⟩ := h
    obtain ⟨t, ht⟩ := Option.ne_none_iff_exists.mp hj
    have huniq : ∀ i, i ≠ j → err (x i) = none := by
      intro i hij
      by_contra hi
      have hsub : ({i, j} : Finset (Fin 7)) ⊆ Finset.univ.filter fun l => err (x l) ≠ none := by
        intro l hl
        rw [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hij] at this
      omega
    refine ⟨some (j, t), ?_, ?_⟩
    · funext i
      by_cases hij : i = j
      · subst hij
        simp only [patA, ← ht, errA]
        split_ifs <;> simp [unitErr_apply]
      · simp only [patA, huniq i hij, errA]
        split_ifs <;> simp [unitErr_apply, hij]
    · funext i
      by_cases hij : i = j
      · subst hij
        simp only [patB, ← ht, errB]
        split_ifs <;> simp [unitErr_apply]
      · simp only [patB, huniq i hij, errB]
        split_ifs <;> simp [unitErr_apply, hij]

end Patterns

section Failure

variable {α : Type*} [MeasurableSpace α]

/-- ★★ **The code-capacity failure bound for the Steane code.** Under independent per-qubit noise
of rate at most `p` (any alphabet, read through `err` to the single-qubit Paulis), for every
code state `ρ` the probability that the recovery channel does not return `ρ` is at most
`C(7, 2) p² = 21 p²`: the recovery undoes every pattern with at most one error, and two or more
errors strike with probability at most `21 p²`. -/
theorem steane_codeCapacity_failure_le (ν : Measure α) [IsProbabilityMeasure ν]
    (err : α → Option (Fin 3)) {p : ℝ≥0∞} (hν : ν {a | err a ≠ none} ≤ p) :
    ∃ R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr),
      ∀ ρ, ρ = steaneProj * ρ * steaneProj →
        Measure.pi (fun _ : Fin 7 => ν)
          {x | R.apply (patErr err x * ρ * (patErr err x)ᴴ) ≠ ρ} ≤ 21 * p ^ 2 := by
  obtain ⟨R, hR⟩ := exists_steane_recovery
  refine ⟨R, fun ρ hρ => ?_⟩
  have hsub : {x : Fin 7 → α | R.apply (patErr err x * ρ * (patErr err x)ᴴ) ≠ ρ}
      ⊆ {x | 2 ≤ (Finset.univ.filter fun i => err (x i) ≠ none).card} := by
    intro x hx
    by_contra hcard
    have hlt : ¬ (2 ≤ (Finset.univ.filter fun i => err (x i) ≠ none).card) := hcard
    obtain ⟨e, hA, hB⟩ := exists_singleErr_of_card_le_one err x (by omega)
    apply hx
    rw [patErr, hA, hB]
    exact hR ρ hρ e
  calc Measure.pi (fun _ : Fin 7 => ν) {x | R.apply (patErr err x * ρ * (patErr err x)ᴴ) ≠ ρ}
      ≤ Measure.pi (fun _ : Fin 7 => ν)
          {x | 2 ≤ (Finset.univ.filter fun i => err (x i) ≠ none).card} := measure_mono hsub
    _ ≤ ((Fintype.card (Fin 7)).choose 2 : ℝ≥0∞) * p ^ 2 :=
        measure_pi_two_or_more_le ν (fun a => err a ≠ none) hν
    _ = 21 * p ^ 2 := by
        rw [Fintype.card_fin, show Nat.choose 7 2 = 21 from by decide]
        norm_num

/-- ★ **The concatenated Steane code**: the bad patterns of `k` levels have probability at most
`(21 p)^{2^k} / 21` under independent per-qubit noise of rate at most `p`. -/
theorem steane_concatBad_le (ν : Measure Bool) [IsProbabilityMeasure ν] {p : ℝ} (hp : 0 ≤ p)
    (hν : ν {b | b = true} ≤ ENNReal.ofReal p) (k : ℕ) :
    (concatMeasure 7 ν k).1 (concatBad 7 k) ≤ ENNReal.ofReal ((21 * p) ^ (2 ^ k) / 21) := by
  have h := concatMeasure_concatBad_le 7 ν hp hν k
  have h21 : ((Nat.choose 7 2 : ℕ) : ℝ) = 21 := by
    rw [show Nat.choose 7 2 = 21 from by decide]
    norm_num
  rwa [h21, codeCapacityBound_eq (by norm_num)] at h

/-- ★ **The threshold of the Steane code, code-capacity form**: below `p < 1/21`, the bound on
the bad patterns of the `k`-fold concatenated code tends to `0` as `k → ∞`. -/
theorem steane_threshold {p : ℝ} (hp : 0 ≤ p) (h : p < 1 / 21) :
    Tendsto (fun k : ℕ => (21 * p) ^ (2 ^ k) / 21) atTop (𝓝 0) := by
  have h1 := tendsto_codeCapacityBound (c := 21) (p := p) (by norm_num) hp (by linarith)
  exact h1.congr fun k => codeCapacityBound_eq (by norm_num) p k

end Failure

end Steane
end QEC
end QM
end Empirical
end CSD

end
