/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.PhaseFlip

/-!
# Empirical/QM: discretization of errors (why correcting four Paulis corrects a continuum)

**Category:** 3-Local. QM-validity layer.

A quantum error is an arbitrary operator — a continuum of them, parameterised by four complex
numbers per qubit. A code corrects only finitely many. The reason quantum error correction works
at all is **discretization**: every single-qubit operator is a `ℂ`-combination of the four Paulis
`{I, X, Z, XZ}`, so an arbitrary error carries a corrupted codeword nowhere outside the span of
the four *correctable* ones. Handling four discrete errors therefore handles the continuum.

This is the conceptual content that makes `QEC/ThreeQubit.lean` (bit flips) and
`QEC/PhaseFlip.lean` (phase flips) into a general error-correction claim rather than a pair of
special cases, and it is what Shor's 9-qubit code turns into a full single-qubit code.

## What this file proves

* `pauli_decomposition` — **the discretization itself**: every `2 × 2` complex matrix is
  `c₀·I + c₁·X + c₂·Z + c₃·XZ`, with the coefficients given explicitly in terms of its entries
  (`(M₀₀ ± M₁₁)/2` and `(M₀₁ ± M₁₀)/2`). Four numbers, no analysis, no choice.
* `pauli_span_top` — the same fact as a spanning statement: `span ℂ {I, X, Z, XZ} = ⊤`. The
  Pauli set is not merely *sufficient* for the errors a code happens to face; it exhausts the
  single-qubit operator space.
* `error_discretization_qubit₁ / ₂ / ₃` — the consequence on the three-qubit code: an arbitrary
  single-qubit error on **any** of the three qubits is the corresponding combination of the four
  discrete errors on that qubit, as operators on `H3`.
* `errored_codeword_eq` — and hence on states: the corrupted codeword `(E ⊗ I ⊗ I)·v` is that
  same combination of the four correctable corrupted codewords, for every `v`.

## Scope — what this does and does not give

This is the **discretization** half of the argument, and it is exact and dimension-free. It says
an arbitrary error produces no state outside the span of the four discrete ones.

It is *not* by itself a proof that the three-qubit code corrects arbitrary errors — that code
corrects bit flips only (`{I, X₁, X₂, X₃}`), and `Z` errors are outside its correctable set, as
`PhaseFlip.lean` exists to complement. Completing the argument to "any single-qubit error" needs
the **concatenated** Shor 9-qubit code, whose correctable set spans all four Paulis on each
qubit; that is an open item (`specs/BACKLOG.md`) blocked on 9-qubit (512-dimensional)
infrastructure, not on this file. The other half — that measuring the syndrome collapses a
superposition of error branches onto one correctable branch — likewise needs the orthogonality of
the error subspaces and ~~is not claimed here~~ **is delivered in
`QEC/SyndromeCollapse.lean`** (`errored_pairwise_orthogonal`,
`three_qubit_corrects_span_error`). *Corrected 2026-08-04 (codebase audit).* — it read as open beside the genuinely-open Shor-9
item, and this file's References never pointed at its own sequel.

## References

`QEC/ThreeQubit.lean` (`pX`, `pZ`, `kron3`, `X1`/`X2`/`X3`, `logical`);
`QEC/PhaseFlip.lean` (the `Z`-error half); `specs/BACKLOG.md` (Shor-9 / concatenation);
`specs/future-work.md`. Shor 1995; Nielsen–Chuang §10.2 (discretization of errors).
-/

@[expose] public section

open Matrix
open scoped Kronecker

namespace CSD
namespace Empirical
namespace QM
namespace QEC

/-! ### The fourth Pauli -/

/-- The fourth Pauli `XZ = !![0,−1;1,0]` (`= −i·Y`; the global phase is irrelevant to error
correction, and staying phase-free keeps the coefficients rational in the entries). -/
def pXZ : Matrix (Fin 2) (Fin 2) ℂ := pX * pZ

theorem pXZ_eq : pXZ = !![0, -1; 1, 0] := by
  rw [pXZ, pX, pZ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-! ### Discretization: the four Paulis span every single-qubit operator -/

/-- **Discretization of errors.** Every single-qubit operator is a `ℂ`-combination of the four
Paulis `{I, X, Z, XZ}`, with coefficients read off its entries. A continuum of possible errors
collapses to four discrete ones — the fact that makes quantum error correction possible. -/
theorem pauli_decomposition (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M = ((M 0 0 + M 1 1) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      + ((M 0 1 + M 1 0) / 2) • pX
      + ((M 0 0 - M 1 1) / 2) • pZ
      + ((M 1 0 - M 0 1) / 2) • pXZ := by
  rw [pXZ_eq, pX, pZ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- **The Paulis exhaust the single-qubit operator space**: `span ℂ {I, X, Z, XZ} = ⊤`. So the
Pauli set is not merely adequate for the errors a particular code faces — there is no
single-qubit error outside it. -/
theorem pauli_span_top :
    Submodule.span ℂ ({1, pX, pZ, pXZ} : Set (Matrix (Fin 2) (Fin 2) ℂ)) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun M => ?_
  rw [pauli_decomposition M]
  have h1 : (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈
      Submodule.span ℂ ({1, pX, pZ, pXZ} : Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
    Submodule.subset_span (by simp)
  have hX : pX ∈ Submodule.span ℂ ({1, pX, pZ, pXZ} : Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
    Submodule.subset_span (by simp)
  have hZ : pZ ∈ Submodule.span ℂ ({1, pX, pZ, pXZ} : Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
    Submodule.subset_span (by simp)
  have hXZ : pXZ ∈ Submodule.span ℂ ({1, pX, pZ, pXZ} : Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
    Submodule.subset_span (by simp)
  exact Submodule.add_mem _
    (Submodule.add_mem _
      (Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ hX))
      (Submodule.smul_mem _ _ hZ))
    (Submodule.smul_mem _ _ hXZ)

/-! ### Lifting the decomposition to the three-qubit code -/

/-- `(XZ)₁ = XZ ⊗ I ⊗ I`. The `Z₁`/`Z₂`/`Z₃` lifts are `QEC/PhaseFlip.lean`'s, reused. -/
def XZ1 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ := kron3 pXZ 1 1
/-- `(XZ)₂ = I ⊗ XZ ⊗ I`. -/
def XZ2 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ := kron3 1 pXZ 1
/-- `(XZ)₃ = I ⊗ I ⊗ XZ`. -/
def XZ3 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ := kron3 1 1 pXZ

theorem kron3_one_one_one :
    kron3 1 1 1 = (1 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) := by
  simp only [kron3, Matrix.one_kronecker_one]

/-! `kron3` is `ℂ`-linear in each slot, so the Pauli decomposition lifts verbatim. -/

theorem kron3_add_left (M N P Q : Matrix (Fin 2) (Fin 2) ℂ) :
    kron3 (M + N) P Q = kron3 M P Q + kron3 N P Q := by
  simp only [kron3, Matrix.add_kronecker]

theorem kron3_smul_left (c : ℂ) (M P Q : Matrix (Fin 2) (Fin 2) ℂ) :
    kron3 (c • M) P Q = c • kron3 M P Q := by
  simp only [kron3, Matrix.smul_kronecker]

theorem kron3_add_mid (M N P Q : Matrix (Fin 2) (Fin 2) ℂ) :
    kron3 P (M + N) Q = kron3 P M Q + kron3 P N Q := by
  simp only [kron3, Matrix.add_kronecker, Matrix.kronecker_add]

theorem kron3_smul_mid (c : ℂ) (M P Q : Matrix (Fin 2) (Fin 2) ℂ) :
    kron3 P (c • M) Q = c • kron3 P M Q := by
  simp only [kron3, Matrix.smul_kronecker, Matrix.kronecker_smul]

theorem kron3_add_right (M N P Q : Matrix (Fin 2) (Fin 2) ℂ) :
    kron3 P Q (M + N) = kron3 P Q M + kron3 P Q N := by
  simp only [kron3, Matrix.kronecker_add]

theorem kron3_smul_right (c : ℂ) (M P Q : Matrix (Fin 2) (Fin 2) ℂ) :
    kron3 P Q (c • M) = c • kron3 P Q M := by
  simp only [kron3, Matrix.kronecker_smul]

/-- **An arbitrary error on qubit 1 is a combination of the four discrete errors on qubit 1.** -/
theorem error_discretization_qubit₁ (E : Matrix (Fin 2) (Fin 2) ℂ) :
    kron3 E 1 1
      = ((E 0 0 + E 1 1) / 2)
          • (1 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
        + ((E 0 1 + E 1 0) / 2) • X1
        + ((E 0 0 - E 1 1) / 2) • Z1
        + ((E 1 0 - E 0 1) / 2) • XZ1 := by
  conv_lhs => rw [pauli_decomposition E]
  rw [kron3_add_left, kron3_add_left, kron3_add_left, kron3_smul_left, kron3_smul_left,
    kron3_smul_left, kron3_smul_left, kron3_one_one_one, X1, Z1, XZ1]

/-- **An arbitrary error on qubit 2 is a combination of the four discrete errors on qubit 2.** -/
theorem error_discretization_qubit₂ (E : Matrix (Fin 2) (Fin 2) ℂ) :
    kron3 1 E 1
      = ((E 0 0 + E 1 1) / 2)
          • (1 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
        + ((E 0 1 + E 1 0) / 2) • X2
        + ((E 0 0 - E 1 1) / 2) • Z2
        + ((E 1 0 - E 0 1) / 2) • XZ2 := by
  conv_lhs => rw [pauli_decomposition E]
  rw [kron3_add_mid, kron3_add_mid, kron3_add_mid, kron3_smul_mid, kron3_smul_mid,
    kron3_smul_mid, kron3_smul_mid, kron3_one_one_one, X2, Z2, XZ2]

/-- **An arbitrary error on qubit 3 is a combination of the four discrete errors on qubit 3.** -/
theorem error_discretization_qubit₃ (E : Matrix (Fin 2) (Fin 2) ℂ) :
    kron3 1 1 E
      = ((E 0 0 + E 1 1) / 2)
          • (1 : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
        + ((E 0 1 + E 1 0) / 2) • X3
        + ((E 0 0 - E 1 1) / 2) • Z3
        + ((E 1 0 - E 0 1) / 2) • XZ3 := by
  conv_lhs => rw [pauli_decomposition E]
  rw [kron3_add_right, kron3_add_right, kron3_add_right, kron3_smul_right, kron3_smul_right,
    kron3_smul_right, kron3_smul_right, kron3_one_one_one, X3, Z3, XZ3]

/-- **The corrupted codeword stays in the span of the four correctable ones.** For every state
`v` — codeword or not — an arbitrary single-qubit error on qubit 1 produces exactly the
corresponding combination of the four discrete corrupted states. So no continuum of *outcomes*
accompanies the continuum of *errors*. -/
theorem errored_codeword_eq (E : Matrix (Fin 2) (Fin 2) ℂ)
    (v : (Fin 2 × Fin 2 × Fin 2) → ℂ) :
    (kron3 E 1 1).mulVec v
      = ((E 0 0 + E 1 1) / 2) • v
        + ((E 0 1 + E 1 0) / 2) • X1.mulVec v
        + ((E 0 0 - E 1 1) / 2) • Z1.mulVec v
        + ((E 1 0 - E 0 1) / 2) • XZ1.mulVec v := by
  rw [error_discretization_qubit₁ E]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

end QEC
end QM
end Empirical
end CSD
