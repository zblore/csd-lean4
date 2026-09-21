/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.Steane
public import CsdLean4.Mathlib.QuantumInfo.StabilizerRecovery

/-!
# The Steane code corrects every single-qubit Pauli error

**Category:** 3-Local (QM-validity). BACKLOG #14(b).

`Steane.lean` exhibits the code space and the distance mechanism (single-qubit errors have
nonzero, pairwise-distinct syndromes); `Mathlib/QuantumInfo/StabilizerRecovery.lean` turns a
detected Pauli error family on a stabiliser code into a recovery channel through the
Knill–Laflamme theorem. This file instantiates it:

* `SingleErr` — the twenty-two single-qubit Paulis (`I`, and `X`, `Z`, `XZ` on each of the seven
  qubits), with labels `errA`, `errB`; `steaneProj` — the code projector as a matrix;
* ★ `syndrome_pair_ne_zero` — **the distance-3 mechanism for pairs**: two distinct single-qubit
  Paulis have a product whose `X`-part or `Z`-part carries a nonzero syndrome (a `𝔽₂`
  computation over the `22 × 22` pairs, kernel-checked by `decide`); `steane_detects_pair` reads it
  as anticommutation with one of the six generators (`steaneX`, `steaneZ`);
* ★★ `steane_knillLaflamme` — the Steane code satisfies **Knill–Laflamme with `c = 1`** for the
  single-qubit Paulis: `P Eᵢᴴ Eⱼ P = δᵢⱼ P`;
* ★★★ `exists_steane_recovery` — **the recovery channel**: one channel `R` with
  `R (E ρ Eᴴ) = ρ` for every single-qubit Pauli `E` and every code state `ρ = P ρ P`;
* `steaneProj_mulVec_steaneZero` / `_steaneOne` — the logical states are code states, and
  ★★★ `steane_recovery_logical` — **every single-qubit Pauli error on an encoded qubit
  `a|0̄⟩ + b|1̄⟩` is undone**: `R (E |ψ̄⟩⟨ψ̄| Eᴴ) = |ψ̄⟩⟨ψ̄|`.

## Honest scope

⚠️ Pauli errors only: the extension to an arbitrary operator on one qubit (its Pauli expansion,
`ErrorDiscretization.lean`'s three-qubit pattern on seven qubits) is not stated, and neither is
any two-qubit error (the Steane code does not correct them). The recovery is the channel the
Knill–Laflamme construction produces, not the syndrome-measurement circuit; the `Σ`-side twin
(a `Σ`-flow whose environment marginal is the single-qubit Pauli channel, as
`Empirical/CSD/QEC/RegisterFlow.lean` does for three qubits) is BACKLOG #53.

References: A. Steane, *Error correcting codes in quantum theory*, PRL 77 (1996) 793;
Nielsen–Chuang §10.4.2; `Empirical/QM/QEC/Steane.lean`;
`Mathlib/QuantumInfo/StabilizerRecovery.lean`; `specs/steane-plan.md`; `specs/BACKLOG.md` #14.
-/

@[expose] public section

open Matrix QuantumInfo

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-! ### The single-qubit Paulis and the code projector -/

/-- The single-qubit Pauli errors on seven qubits: `none` is the identity, `some (j, 0)` the `X`
on qubit `j`, `some (j, 1)` the `Z`, `some (j, 2)` the `XZ` (proportional to `Y`). -/
abbrev SingleErr := Option (Fin 7 × Fin 3)

/-- The `X`-label of a single-qubit Pauli. -/
def errA : SingleErr → Fin 7 → Fin 2
  | none => 0
  | some (j, t) => if t = 1 then 0 else unitErr j

/-- The `Z`-label of a single-qubit Pauli. -/
def errB : SingleErr → Fin 7 → Fin 2
  | none => 0
  | some (j, t) => if t = 0 then 0 else unitErr j

/-- The Steane code projector as a matrix on the register's coordinates. -/
noncomputable def steaneProj : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  stabMat steaneA steaneB fun _ => 0

/-- The `X`-type generator `X^{hammingRow r}` as a label of the family. -/
def steaneX (r : Fin 3) : Fin 6 → Fin 2 :=
  fun k => if (k : ℕ) = (r : ℕ) then 1 else 0

/-- The `Z`-type generator `Z^{hammingRow r}` as a label of the family. -/
def steaneZ (r : Fin 3) : Fin 6 → Fin 2 :=
  fun k => if (k : ℕ) = (r : ℕ) + 3 then 1 else 0

lemma steaneA_steaneX (r : Fin 3) : steaneA (steaneX r) = hammingRow r := by
  revert r
  decide

lemma steaneB_steaneX (r : Fin 3) : steaneB (steaneX r) = 0 := by
  revert r
  decide

lemma steaneA_steaneZ (r : Fin 3) : steaneA (steaneZ r) = 0 := by
  revert r
  decide

lemma steaneB_steaneZ (r : Fin 3) : steaneB (steaneZ r) = hammingRow r := by
  revert r
  decide

/-! ### The distance mechanism for pairs -/

/-- ★ **Two distinct single-qubit Paulis are told apart by the syndromes**: the product's `X`-part
or its `Z`-part has a nonzero syndrome. A `𝔽₂` computation over the `22 × 22` pairs. -/
theorem syndrome_pair_ne_zero (i j : SingleErr) (h : i ≠ j) :
    syndrome (errB i + errB j) ≠ 0 ∨ syndrome (errA i + errA j) ≠ 0 := by
  revert i j
  decide

lemma fin2_eq_one_of_ne_zero {v : Fin 2} (h : v ≠ 0) : v = 1 := by
  revert v
  decide

/-- A nonzero syndrome names a row pairing to `1`. -/
lemma exists_row_of_syndrome_ne_zero {e : Fin 7 → Fin 2} (h : syndrome e ≠ 0) :
    ∃ r : Fin 3, bdot (hammingRow r) e = 1 := by
  obtain ⟨r, hr⟩ := Function.ne_iff.mp h
  exact ⟨r, fin2_eq_one_of_ne_zero hr⟩

/-- **Detection as anticommutation**: for distinct single-qubit Paulis, some generator pairs to
`1` with the product's labels — the hypothesis of `stabMat_knillLaflamme`. -/
theorem steane_detects_pair (i j : SingleErr) (h : i ≠ j) :
    ∃ x, bdot (steaneA x) (errB i + errB j) + bdot (steaneB x) (errA i + errA j) = 1 := by
  rcases syndrome_pair_ne_zero i j h with hB | hA
  · obtain ⟨r, hr⟩ := exists_row_of_syndrome_ne_zero hB
    exact ⟨steaneX r, by rw [steaneA_steaneX, steaneB_steaneX, hr, bdot_zero_left, add_zero]⟩
  · obtain ⟨r, hr⟩ := exists_row_of_syndrome_ne_zero hA
    exact ⟨steaneZ r, by rw [steaneA_steaneZ, steaneB_steaneZ, hr, bdot_zero_left, zero_add]⟩

/-! ### Knill–Laflamme and the recovery -/

/-- ★★ **The Steane code satisfies Knill–Laflamme with `c = 1` for the single-qubit Paulis**:
`P Eᵢᴴ Eⱼ P = δᵢⱼ P`. -/
theorem steane_knillLaflamme :
    KnillLaflamme steaneProj (fun i : SingleErr => pauliMat (errA i) (errB i)) 1 :=
  stabMat_knillLaflamme steaneA_add steaneB_add steane_sigma_coherent errA errB
    steane_detects_pair

/-- ★★★ **The Steane code corrects every single-qubit Pauli error**: one recovery channel `R`
undoes each of the twenty-two errors on every code state. -/
theorem exists_steane_recovery :
    ∃ R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr),
      ∀ ρ, ρ = steaneProj * ρ * steaneProj →
        ∀ i : SingleErr,
          R.apply (pauliMat (errA i) (errB i) * ρ * (pauliMat (errA i) (errB i))ᴴ) = ρ :=
  exists_recovery_stabMat steaneA_add steaneB_add steane_sigma_coherent steane_labels_injective
    errA errB steane_detects_pair

/-! ### The logical states are code states -/

theorem isCodeProjector_steaneProj : IsCodeProjector steaneProj :=
  isCodeProjector_stabMat steaneA_add steaneB_add steane_sigma_coherent

/-- The group average fixes a state fixed by every generator. -/
theorem stabProjector_steane_of_stabilised (ψ : QReg 7)
    (hψ : ∀ x, pauliOp (steaneA x) (steaneB x) ψ = ψ) :
    stabProjector steaneA steaneB (fun _ => 0) ψ = ψ := by
  rw [stabProjector]
  simp only [signChar_zero, one_smul, hψ, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num

theorem steaneProj_mulVec_steaneZero :
    steaneProj *ᵥ WithLp.ofLp steaneZero = WithLp.ofLp steaneZero := by
  rw [steaneProj, stabMat_mulVec, WithLp.toLp_ofLp,
    stabProjector_steane_of_stabilised steaneZero steaneZero_stabilised]

theorem steaneProj_mulVec_steaneOne :
    steaneProj *ᵥ WithLp.ofLp steaneOne = WithLp.ofLp steaneOne := by
  rw [steaneProj, stabMat_mulVec, WithLp.toLp_ofLp,
    stabProjector_steane_of_stabilised steaneOne steaneOne_stabilised]

/-- The encoded qubit `a|0̄⟩ + b|1̄⟩`, as a coordinate vector. -/
noncomputable def logicalVec (a b : ℂ) : (Fin 7 → Fin 2) → ℂ :=
  WithLp.ofLp (a • steaneZero + b • steaneOne)

theorem steaneProj_mulVec_logicalVec (a b : ℂ) :
    steaneProj *ᵥ logicalVec a b = logicalVec a b := by
  rw [logicalVec, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_smul, mulVec_add, mulVec_smul,
    mulVec_smul, steaneProj_mulVec_steaneZero, steaneProj_mulVec_steaneOne]

/-- The density operator of the encoded qubit is a code state: `ρ = P ρ P`. -/
theorem logical_density_eq (a b : ℂ) :
    vecMulVec (logicalVec a b) (star (logicalVec a b))
      = steaneProj * vecMulVec (logicalVec a b) (star (logicalVec a b)) * steaneProj := by
  rw [mul_vecMulVec, vecMulVec_mul, steaneProj_mulVec_logicalVec]
  congr 1
  conv_rhs => rw [← isCodeProjector_steaneProj.conjTranspose_eq]
  rw [← star_mulVec, steaneProj_mulVec_logicalVec]

/-- ★★★ **Every single-qubit Pauli error on an encoded qubit is undone**: for
`|ψ̄⟩ = a|0̄⟩ + b|1̄⟩` and every single-qubit Pauli `E`, the recovery channel returns
`|ψ̄⟩⟨ψ̄|` from `E |ψ̄⟩⟨ψ̄| Eᴴ`. -/
theorem steane_recovery_logical :
    ∃ R : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (Option SingleErr),
      ∀ (a b : ℂ) (i : SingleErr),
        R.apply (pauliMat (errA i) (errB i) * vecMulVec (logicalVec a b) (star (logicalVec a b))
            * (pauliMat (errA i) (errB i))ᴴ)
          = vecMulVec (logicalVec a b) (star (logicalVec a b)) := by
  obtain ⟨R, hR⟩ := exists_steane_recovery
  exact ⟨R, fun a b i => hR _ (logical_density_eq a b) i⟩

end Steane
end QEC
end QM
end Empirical
end CSD

end
