/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Incubator.QuantumChaos.FloquetInterface
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Chaos diagnostics: the out-of-time-order commutator (§H)

**Category:** Special (incubator — CSD-free; `upstream-candidate(physlib)`).

The third chaos diagnostic: the **OTOC in commutator-norm form**,

  `C(n) = ‖[A(n), B]‖`,   `A(n) = (Uⁿ)† A (Uⁿ)`,

the growth of the commutator between a Heisenberg-evolved observable and a
static one. Scrambling is `C(n)` becoming large for initially commuting
`A, B`; the state-resolved form `⟨[A(n),B]†[A(n),B]⟩` is a refinement over
this operator-norm envelope, not stated here.

* `heisenberg U A = U† A U` — Heisenberg conjugation over any finite index
  (the CV-6 `CSD.CV.heisenberg` is the `FieldConfig` instance, definitional
  bridge in `CV/ChaosBounds.lean`).
* `otoc` — the commutator-norm diagnostic; `otoc_eq_zero_iff` (vanishing =
  exact commutation), `otoc_le` (the a-priori envelope `≤ 2‖A‖‖B‖`:
  conjugation by unitaries never grows the norm).

The teeth are in the instantiation: for the CV interacting drive the
coupling-graph light cone forces `otoc = 0` until the evolving observable's
cone reaches the static probe's support (`CV/ChaosBounds.lean`,
`otoc_graphInteractingU_eq_zero`) — scrambling provably cannot begin
before causal contact. Honest scope: no
exponential-growth (Lyapunov) claims; growth *rates* are the thread's
recorded continuation.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator

namespace QuantumChaos

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Heisenberg conjugation** over any finite index: `A ↦ U† A U`. -/
noncomputable def heisenberg (U : Matrix.unitaryGroup ι ℂ)
    (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  star U.val * A * U.val

/-- **The OTOC, commutator-norm form**: `‖[A(n), B]‖` with
`A(n) = (Uⁿ)† A (Uⁿ)`. -/
noncomputable def otoc (U : Matrix.unitaryGroup ι ℂ)
    (A B : Matrix ι ι ℂ) (n : ℕ) : ℝ :=
  ‖heisenberg (U ^ n) A * B - B * heisenberg (U ^ n) A‖

/-- The OTOC vanishes exactly when the evolved observable still commutes
with the probe. -/
lemma otoc_eq_zero_iff (U : Matrix.unitaryGroup ι ℂ)
    (A B : Matrix ι ι ℂ) (n : ℕ) :
    otoc U A B n = 0
      ↔ heisenberg (U ^ n) A * B = B * heisenberg (U ^ n) A := by
  rw [otoc, norm_eq_zero, sub_eq_zero]

/-- Conjugation by a unitary never grows the L2 operator norm. -/
lemma l2_opNorm_heisenberg_le [Nonempty ι] (U : Matrix.unitaryGroup ι ℂ)
    (A : Matrix ι ι ℂ) : ‖heisenberg U A‖ ≤ ‖A‖ := by
  have hU : ‖U.val‖ = 1 := CStarRing.norm_of_mem_unitary U.property
  have hUs : ‖star U.val‖ = 1 := by
    rw [Matrix.star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose]
    exact hU
  calc ‖star U.val * A * U.val‖
      ≤ ‖star U.val * A‖ * ‖U.val‖ := norm_mul_le _ _
    _ ≤ ‖star U.val‖ * ‖A‖ * ‖U.val‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖A‖ := by rw [hUs, hU, one_mul, mul_one]

/-- **The a-priori OTOC envelope**: `C(n) ≤ 2‖A‖‖B‖` at every period —
scrambling is bounded by the observables themselves. -/
theorem otoc_le [Nonempty ι] (U : Matrix.unitaryGroup ι ℂ)
    (A B : Matrix ι ι ℂ) (n : ℕ) :
    otoc U A B n ≤ 2 * ‖A‖ * ‖B‖ := by
  have h1 : ‖heisenberg (U ^ n) A * B‖ ≤ ‖A‖ * ‖B‖ :=
    (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (l2_opNorm_heisenberg_le _ A)
        (norm_nonneg B))
  have h2 : ‖B * heisenberg (U ^ n) A‖ ≤ ‖B‖ * ‖A‖ :=
    (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left (l2_opNorm_heisenberg_le _ A)
        (norm_nonneg B))
  calc otoc U A B n
      ≤ ‖heisenberg (U ^ n) A * B‖ + ‖B * heisenberg (U ^ n) A‖ :=
        norm_sub_le _ _
    _ ≤ ‖A‖ * ‖B‖ + ‖B‖ * ‖A‖ := add_le_add h1 h2
    _ = 2 * ‖A‖ * ‖B‖ := by ring

end QuantumChaos
