/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.Steane
public import CsdLean4.Mathlib.QuantumInfo.SyndromeExtraction

/-!
# Empirical/QM: the Steane code's syndrome extraction, as a circuit

**Category:** 3-Local. QM-validity layer (matrix algebra, no CSD content).
BACKLOG #94, the instance; the generic gadget is
[`Mathlib/QuantumInfo/SyndromeExtraction.lean`](../../../Mathlib/QuantumInfo/SyndromeExtraction.lean).

`Steane.lean` has the `X`-syndrome as a *function* on error patterns,
`syndrome e = fun i => bdot (hammingRow i) e`, and uses it to prove the distance-3 mechanism. This
file runs the generic extraction gadget at that check map, so the syndrome the corpus reasons with is
the one a `CNOT` ladder into a three-qubit ancilla block actually produces.

## What is proved

* ★ `steane_syndrome_add_self` — the only arithmetic the gadget needs: `syndrome z + syndrome z = 0`,
  characteristic two;
* `steaneExtract` — the extraction circuit for the Steane `X`-checks, with
  ★ `steaneExtract_mem_unitaryGroup`;
* ★★ `steaneExtract_tags_syndrome` — the circuit sends the data word `z` with a fresh ancilla to
  `(z, syndrome z)`: the ancilla block ends up holding the Hamming syndrome;
* ★★★ `steaneExtract_reads_syndrome` — **reading the ancilla is projecting the data onto the syndrome
  subspace**: the circuit implements the projective measurement, as an operator identity;
* ★★★ `steaneExtract_code_state` — **a Steane code state is returned unchanged**, ancilla included,
  and ★★ `steaneExtract_code_state_syndrome_zero`: the all-zero outcome is then certain;
* ★ `syndrome_add` and ★★ `steane_extract_detects_single` — **a single-qubit error changes what the
  ancilla reads**, since its syndrome is nonzero (`steane_syndrome_single_ne_zero`), and
  ★★ `steane_extract_names_single` — **distinct single errors read differently**, so the ancilla
  *names* the faulty qubit (`steane_syndrome_single_injective`). This is the circuit form of the
  distance-3 mechanism `Steane.lean` proves about the syndrome function.

## Honest scope

⚠️ **No faults, and therefore no fault tolerance.** Every statement is about the gadget running
correctly. A fault in the `CNOT` ladder, or in the ancilla, is BACKLOG #95 and #96; nothing here says
this gadget is fault-*tolerant*, only what it computes when it works.

⚠️ **One unverified ancilla block.** The ancilla is prepared in the all-zero state and read; there is
no cat state, no verification, and so no bound on a single ancilla fault spreading into the data. That
is #95's subject.

⚠️ **`X`-checks only.** The Steane code is CSS and its `Z`-checks are the same statement in the
conjugate basis; that half is **not** done here, and nothing combines the two bases.

⚠️ **The syndrome is produced, not decoded.** Nothing here maps a syndrome to a correction: the
recovery maps of `SteaneRecovery.lean` and `SteaneArbitrary.lean` are neither re-derived nor connected
to this circuit.

⚠️ **The register is the error-pattern basis.** The data index is `Fin 7 → Fin 2`, i.e. the
computational basis of seven qubits; this is the same labelling `Steane.lean` uses, and no claim is
made about the encoded logical state beyond its membership in the syndrome-`0` subspace.

## References

`Mathlib/QuantumInfo/SyndromeExtraction.lean` (the generic gadget);
`Empirical/QM/QEC/Steane.lean` (`syndrome`, `steane_syndrome_single_ne_zero`,
`steane_syndrome_single_injective`); `Empirical/QM/QEC/SyndromeRecovery.lean` (the
projective-measurement form); `specs/BACKLOG.md` #94, #95, #96, #62; `specs/future-work.md`.
-/

@[expose] public section

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

open QuantumInfo Matrix

/-! ### The Steane check map in characteristic two -/

/-- ★ **The only arithmetic the gadget needs.** The syndrome lands in `Fin 3 → Fin 2`, where every
element is its own inverse. -/
theorem steane_syndrome_add_self (z : Fin 7 → Fin 2) : syndrome z + syndrome z = 0 := by
  funext i
  exact (by decide : ∀ x : Fin 2, x + x = 0) (syndrome z i)

/-- The syndrome is additive, because `bdot` is. -/
theorem syndrome_add (e f : Fin 7 → Fin 2) : syndrome (e + f) = syndrome e + syndrome f := by
  funext i
  exact bdot_add_right (hammingRow i) e f

/-! ### The extraction circuit -/

/-- **The Steane `X`-syndrome extraction circuit**: the `CNOT` ladder from the seven data qubits into
a three-qubit ancilla block, as the matrix of its basis relabelling. -/
noncomputable def steaneExtract :
    Matrix ((Fin 7 → Fin 2) × (Fin 3 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 3 → Fin 2)) ℂ :=
  extractMat syndrome

/-- ★ The circuit is unitary. -/
theorem steaneExtract_mem_unitaryGroup :
    steaneExtract ∈ Matrix.unitaryGroup ((Fin 7 → Fin 2) × (Fin 3 → Fin 2)) ℂ :=
  extractMat_mem_unitaryGroup steane_syndrome_add_self

theorem steaneExtract_mul_self : steaneExtract * steaneExtract = 1 :=
  extractMat_mul_self steane_syndrome_add_self

/-- ★★ **The ancilla ends up holding the Hamming syndrome.** -/
theorem steaneExtract_tags_syndrome (p : (Fin 7 → Fin 2) × (Fin 3 → Fin 2)) (z : Fin 7 → Fin 2) :
    (steaneExtract * (ancInit : Matrix ((Fin 7 → Fin 2) × (Fin 3 → Fin 2)) (Fin 7 → Fin 2) ℂ)) p z
      = if p = (z, syndrome z) then 1 else 0 :=
  extractMat_mul_ancInit_apply steane_syndrome_add_self p z

/-- ★★★ **Reading the ancilla is projecting the data onto the syndrome subspace.** The circuit
implements the projective syndrome measurement the corpus reasons with, as an operator identity. -/
theorem steaneExtract_reads_syndrome (s : Fin 3 → Fin 2) :
    ancProj (α := Fin 7 → Fin 2) s
        * (steaneExtract
            * (ancInit : Matrix ((Fin 7 → Fin 2) × (Fin 3 → Fin 2)) (Fin 7 → Fin 2) ℂ))
      = (steaneExtract
            * (ancInit : Matrix ((Fin 7 → Fin 2) × (Fin 3 → Fin 2)) (Fin 7 → Fin 2) ℂ))
          * synProj syndrome s :=
  ancProj_mul_extractMat_mul_ancInit steane_syndrome_add_self s

/-- ★★★ **A Steane code state is returned unchanged, ancilla included.** -/
theorem steaneExtract_code_state {ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hρ : synProj syndrome (0 : Fin 3 → Fin 2) * ρ * synProj syndrome (0 : Fin 3 → Fin 2) = ρ) :
    steaneExtract
        * ((ancInit : Matrix ((Fin 7 → Fin 2) × (Fin 3 → Fin 2)) (Fin 7 → Fin 2) ℂ) * ρ * ancInitᴴ)
        * steaneExtractᴴ
      = (ancInit : Matrix ((Fin 7 → Fin 2) × (Fin 3 → Fin 2)) (Fin 7 → Fin 2) ℂ) * ρ * ancInitᴴ :=
  extractMat_conj_codeState steane_syndrome_add_self hρ

/-- ★★ **And the all-zero syndrome is certain on the code.** -/
theorem steaneExtract_code_state_syndrome_zero
    {ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ}
    (hρ : synProj syndrome (0 : Fin 3 → Fin 2) * ρ * synProj syndrome (0 : Fin 3 → Fin 2) = ρ) :
    ancProj (α := Fin 7 → Fin 2) (0 : Fin 3 → Fin 2)
        * (steaneExtract
            * ((ancInit : Matrix ((Fin 7 → Fin 2) × (Fin 3 → Fin 2)) (Fin 7 → Fin 2) ℂ) * ρ
              * ancInitᴴ)
            * steaneExtractᴴ)
      = steaneExtract
          * ((ancInit : Matrix ((Fin 7 → Fin 2) × (Fin 3 → Fin 2)) (Fin 7 → Fin 2) ℂ) * ρ
            * ancInitᴴ)
          * steaneExtractᴴ :=
  ancProj_zero_mul_extractMat_conj_codeState steane_syndrome_add_self hρ

/-! ### The distance-3 mechanism, read off the ancilla -/

/-- ★★ **A single-qubit error changes what the ancilla reads.** The circuit form of
`steane_syndrome_single_ne_zero`: extraction *detects* every single-qubit `X` error. -/
theorem steane_extract_detects_single (z : Fin 7 → Fin 2) (j : Fin 7) :
    syndrome (z + unitErr j) ≠ syndrome z := by
  rw [syndrome_add]
  intro h
  exact steane_syndrome_single_ne_zero j (by
    have := add_left_cancel (a := syndrome z) (by simpa [add_comm] using h.trans (add_zero _).symm)
    simpa using this)

/-- ★★ **Distinct single-qubit errors read differently**, so the ancilla block *names* the faulty
qubit. The circuit form of `steane_syndrome_single_injective`. -/
theorem steane_extract_names_single (z : Fin 7 → Fin 2) (j j' : Fin 7)
    (h : syndrome (z + unitErr j) = syndrome (z + unitErr j')) : j = j' := by
  rw [syndrome_add, syndrome_add] at h
  exact steane_syndrome_single_injective j j' (add_left_cancel h)

end Steane
end QEC
end QM
end Empirical
end CSD

end
