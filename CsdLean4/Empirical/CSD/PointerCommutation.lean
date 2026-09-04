/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.Einselection
public import CsdLean4.Mathlib.Analysis.Matrix.StoneC1

/-!
# Empirical/CSD: the einselection commutation criterion (`[P, H_int] = 0`)

**Category:** 6-Local (the open-system / decoherence stratum of D1 — the
Hamiltonian-level einselection criterion on the LF6-B machinery).

Build 15a (`Empirical/CSD/Einselection.lean`) proved decoherence is
basis-**selective**: the de-isolation channel's output is diagonal in exactly one
basis (up to degeneracy). What it deliberately did not model — its honest-scope
note says so — is the **Hamiltonian-level** account of *which* observable an
interaction leaves intact. That is Zurek's einselection criterion: the pointer
observable is the one the interaction Hamiltonian **commutes** with, hence does
not disturb. This module proves the criterion.

## The criterion

For an interaction `H_int` (Hermitian) with unitary flow
`U(t) = exp (t • (−i • H_int))` (`intFlow`), commutation `[P, H_int] = 0` makes
`P` a **constant of the interaction motion**:

* ★ `pointer_invariant_of_commute` — Heisenberg invariance `U(t)ᴴ P U(t) = P`;
* `pointer_population_conserved` — `tr (P · U ρ Uᴴ) = tr (P · ρ)` for **every**
  state `ρ` and every time: pointer records do not degrade under the interaction;
* `compress_conj_comm` / `sector_state_invariant` — compressing to the `P`-sector
  commutes with the flow, so a state in a pointer sector stays in it;
* ★★ `pointer_basis_of_commuting` — the packaged criterion, for a family
  `P : ι → Matrix _ _ ℂ` with `∀ i, Commute (P i) H_int`: all three conclusions,
  every member, every time. **Commutation alone is load-bearing** — no projection
  or positivity hypothesis is needed for any of the three (stronger than the
  textbook phrasing, which states the criterion for projection-valued pointer
  observables).

## The class of interactions, and coherence survival under the flow

* `single_commute_diagonal` — every computational projection `|eᵢ⟩⟨eᵢ| =
  Matrix.single i i 1` (`outerProduct_single`, `LF5/DilationFromFlow.lean`)
  commutes with **every** pointer-diagonal interaction: the criterion holds for
  the whole class `H_int = diagonal (real spectrum)`, not one instance
  (`pointer_basis_of_diagonal`).
* `intFlow_diagonal` — the flow of a diagonal interaction is the diagonal-phase
  unitary, computed via `Matrix.exp_diagonal`.
* ★ `coherence_modulus_preserved` — under that flow **every coherence modulus is
  exactly preserved**: `‖(U ρ Uᴴ) i j‖ = ‖ρ i j‖`. The interaction flow alone
  never dephases the pointer basis; the dephasing of `LF6/Decoherence.lean` is
  the unmonitored-environment **trace**, not the flow. Flow preserves, trace
  selects — the two halves of einselection, now both theorems.

## The contrast: a non-commuting observable is disturbed

Reusing Build 15a's rotated-basis contrast (the Hadamard `qmH`):
`rotatedProj = qmH · |e₀⟩⟨e₀| · qmH` is a genuine projection
(`rotatedProj_mul_self`) that **fails** the criterion
(`rotatedProj_not_commute`, against `contrastH = diagonal (0, π)`), and the flow
punishes it maximally: its population in its own eigenstate falls `1 → 0` in one
stroke (`noncommuting_population_disturbed`). ★★
`einselection_commutation_contrast` bundles the two sides: commuting ⟹ conserved,
non-commuting ⟹ disturbed. The pointer basis is the one the interaction does not
disturb — computed, not narrated.

## Honest scope and residue

The criterion einselects the basis **given** the interaction: `H_int` is the
measurement context and remains an **input**, exactly as it is for Bohm and for
Everett — no interpretation derives the apparatus Hamiltonian from first
principles, and this module does not either. That is a boundary of the
formal claim by design, not a gap in it (⚠️ RESIDUE(R-015)). What is discharged is the
Hamiltonian-level *criterion* (parity with the field's accepted einselection
answer, machine-checked); what remains is the D1 obligation, untouched here
(`RecordLayer/MomentMapRace.lean`, `specs/q12-fibre-mechanism-scoping.md`).
This supersedes in part the Build 15a honest-scope note ("the basis is the
de-isolation's by construction"): given `H_int`, the basis is now the
commutation-selected one, a theorem; the interaction itself is still posited.

## References

`specs/future-work.md`; `Empirical/CSD/Einselection.lean` (Build 15a — the
channel-level basis selectivity this completes); `LF6/Decoherence.lean`
(`decohereReduced`, the trace half); `Mathlib/Analysis/Matrix/StoneC1.lean`
(`Matrix.StoneC1.exp_smul_unitary`); `LF5/DilationFromFlow.lean`
(`outerProduct_single`). All exports are foundational-triple-only.
-/

@[expose] public section

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
open CSD.LF6 CSD.Empirical.QM.Gates

namespace CSD
namespace Empirical
namespace CSDBridge
namespace Einselection

variable {N : ℕ}

/-! ### The interaction flow -/

/-- **The interaction flow** of a (Hermitian) interaction `Hint`:
`U(t) = exp (t • (−i • Hint))`, the one-parameter unitary group `Hint` generates. -/
noncomputable def intFlow (Hint : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  exp (t • ((-Complex.I) • Hint))

lemma intFlow_def (Hint : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    intFlow Hint t = exp (t • ((-Complex.I) • Hint)) := rfl

/-- For Hermitian `Hint` the generator `−i • Hint` is skew-Hermitian. -/
lemma neg_I_smul_skew {Hint : Matrix (Fin N) (Fin N) ℂ} (hH : Hint.IsHermitian) :
    star ((-Complex.I) • Hint) = -((-Complex.I) • Hint) := by
  have h1 : star (-Complex.I) = Complex.I := by simp
  rw [star_smul, h1, Matrix.star_eq_conjTranspose, hH.eq, neg_smul, neg_neg]

/-- For Hermitian `Hint` the full generator `t • (−i • Hint)` is skew-Hermitian. -/
lemma smul_neg_I_skew {Hint : Matrix (Fin N) (Fin N) ℂ} (hH : Hint.IsHermitian) (t : ℝ) :
    (t • ((-Complex.I) • Hint))ᴴ = -(t • ((-Complex.I) • Hint)) := by
  rw [Matrix.conjTranspose_smul, star_trivial, ← Matrix.star_eq_conjTranspose,
    neg_I_smul_skew hH, smul_neg]

/-- The flow at time zero is the identity. -/
lemma intFlow_zero (Hint : Matrix (Fin N) (Fin N) ℂ) : intFlow Hint 0 = 1 := by
  rw [intFlow_def, zero_smul, exp_zero]

/-- **The interaction flow is unitary** (left inverse): `U(t)ᴴ U(t) = 1`.
Via `Matrix.StoneC1.exp_smul_unitary` on the skew generator. -/
theorem intFlow_conjTranspose_mul {Hint : Matrix (Fin N) (Fin N) ℂ}
    (hH : Hint.IsHermitian) (t : ℝ) :
    (intFlow Hint t)ᴴ * intFlow Hint t = 1 := by
  rw [intFlow_def]
  exact Matrix.StoneC1.exp_smul_unitary _ (neg_I_smul_skew hH) t

/-- **The interaction flow is unitary** (right inverse): `U(t) U(t)ᴴ = 1`. -/
theorem intFlow_mul_conjTranspose {Hint : Matrix (Fin N) (Fin N) ℂ}
    (hH : Hint.IsHermitian) (t : ℝ) :
    intFlow Hint t * (intFlow Hint t)ᴴ = 1 := by
  rw [intFlow_def, ← Matrix.exp_conjTranspose, smul_neg_I_skew hH,
    ← Matrix.exp_add_of_commute _ _
      ((Commute.refl (t • ((-Complex.I) • Hint))).neg_right),
    add_neg_cancel, exp_zero]

/-- Commutation with the generator transfers to the flow:
`[P, Hint] = 0 ⟹ [P, U(t)] = 0` (via `Commute.exp_right`). -/
theorem commute_intFlow {P Hint : Matrix (Fin N) (Fin N) ℂ}
    (hcomm : Commute P Hint) (t : ℝ) : Commute P (intFlow Hint t) := by
  rw [intFlow_def]
  exact ((hcomm.smul_right (-Complex.I)).smul_right t).exp_right

/-- Commutation with the generator also transfers to the adjoint flow:
`[P, Hint] = 0 ⟹ [P, U(t)ᴴ] = 0` (the adjoint is the reversed flow). -/
theorem commute_intFlow_conjTranspose {P Hint : Matrix (Fin N) (Fin N) ℂ}
    (hH : Hint.IsHermitian) (hcomm : Commute P Hint) (t : ℝ) :
    Commute P ((intFlow Hint t)ᴴ) := by
  rw [intFlow_def, ← Matrix.exp_conjTranspose, smul_neg_I_skew hH]
  exact (((hcomm.smul_right (-Complex.I)).smul_right t).neg_right).exp_right

/-! ### The criterion: commuting pointer observables are constants of the motion -/

/-- ★ **Heisenberg invariance (the einselection criterion).** A pointer observable
commuting with the interaction is a constant of the interaction motion:
`U(t)ᴴ P U(t) = P` at every time. The interaction does not disturb `P` — Zurek's
criterion for the preferred (pointer) observable, as a theorem. -/
theorem pointer_invariant_of_commute {P Hint : Matrix (Fin N) (Fin N) ℂ}
    (hH : Hint.IsHermitian) (hcomm : Commute P Hint) (t : ℝ) :
    (intFlow Hint t)ᴴ * P * intFlow Hint t = P := by
  rw [Matrix.mul_assoc, (commute_intFlow hcomm t).eq, ← Matrix.mul_assoc,
    intFlow_conjTranspose_mul hH, Matrix.one_mul]

/-- Trace bookkeeping: a Heisenberg-fixed observable has conserved expectation
under the corresponding Schrödinger conjugation, by trace cyclicity alone. -/
lemma trace_conj_of_heisenberg_fixed {U P ρ : Matrix (Fin N) (Fin N) ℂ}
    (hfix : Uᴴ * P * U = P) :
    (P * (U * ρ * Uᴴ)).trace = (P * ρ).trace := by
  calc (P * (U * ρ * Uᴴ)).trace
      = ((P * U * ρ) * Uᴴ).trace := by simp only [Matrix.mul_assoc]
    _ = (Uᴴ * (P * U * ρ)).trace := Matrix.trace_mul_comm _ _
    _ = ((Uᴴ * P * U) * ρ).trace := by simp only [Matrix.mul_assoc]
    _ = (P * ρ).trace := by rw [hfix]

/-- **Pointer populations are exactly conserved.** For every state `ρ` and every
time, `tr (P · U(t) ρ U(t)ᴴ) = tr (P · ρ)`: the record weight in a commuting
pointer observable does not degrade under the interaction flow. -/
theorem pointer_population_conserved {P Hint : Matrix (Fin N) (Fin N) ℂ}
    (hH : Hint.IsHermitian) (hcomm : Commute P Hint)
    (ρ : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    (P * (intFlow Hint t * ρ * (intFlow Hint t)ᴴ)).trace = (P * ρ).trace :=
  trace_conj_of_heisenberg_fixed (pointer_invariant_of_commute hH hcomm t)

/-- **Sector compression commutes with the interaction flow:**
`P (U ρ Uᴴ) P = U (P ρ P) Uᴴ`. Compressing to the pointer sector before or after
the interaction is the same operation. -/
theorem compress_conj_comm {P Hint : Matrix (Fin N) (Fin N) ℂ}
    (hH : Hint.IsHermitian) (hcomm : Commute P Hint)
    (ρ : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    P * (intFlow Hint t * ρ * (intFlow Hint t)ᴴ) * P
      = intFlow Hint t * (P * ρ * P) * (intFlow Hint t)ᴴ := by
  calc P * (intFlow Hint t * ρ * (intFlow Hint t)ᴴ) * P
      = P * intFlow Hint t * ρ * ((intFlow Hint t)ᴴ * P) := by
        simp only [Matrix.mul_assoc]
    _ = intFlow Hint t * P * ρ * (P * (intFlow Hint t)ᴴ) := by
        rw [(commute_intFlow hcomm t).eq,
          ← (commute_intFlow_conjTranspose hH hcomm t).eq]
    _ = intFlow Hint t * (P * ρ * P) * (intFlow Hint t)ᴴ := by
        simp only [Matrix.mul_assoc]

/-- **Pointer-sector states stay in their sector.** If `ρ` is supported in the
`P`-sector (`P ρ P = ρ`), so is its image under the interaction flow. -/
theorem sector_state_invariant {P Hint ρ : Matrix (Fin N) (Fin N) ℂ}
    (hH : Hint.IsHermitian) (hcomm : Commute P Hint) (t : ℝ)
    (hρ : P * ρ * P = ρ) :
    P * (intFlow Hint t * ρ * (intFlow Hint t)ᴴ) * P
      = intFlow Hint t * ρ * (intFlow Hint t)ᴴ := by
  rw [compress_conj_comm hH hcomm ρ t, hρ]

/-- ★★ **The einselection commutation criterion, packaged.** For an interaction
`Hint` (Hermitian) and a family of pointer observables `P i` each commuting with
`Hint` (`[P i, H_int] = 0`):

1. every `P i` is a constant of the interaction motion, `U(t)ᴴ (P i) U(t) = P i`
   (`pointer_invariant_of_commute`);
2. every pointer population is exactly conserved in every state,
   `tr (P i · U ρ Uᴴ) = tr (P i · ρ)` (`pointer_population_conserved`);
3. every pointer-sector state stays in its sector (`sector_state_invariant`).

Coherences in the `P`-basis survive the `H_int` flow; a non-commuting observable
does not enjoy this (see `einselection_commutation_contrast`). Commutation alone
is load-bearing: no projection hypothesis is required. **Residue:** the criterion
selects the basis *given* the interaction — `H_int` is the measurement context
and remains an input. -/
theorem pointer_basis_of_commuting {ι : Type*}
    (Hint : Matrix (Fin N) (Fin N) ℂ) (hH : Hint.IsHermitian)
    (P : ι → Matrix (Fin N) (Fin N) ℂ)
    (hcomm : ∀ i, Commute (P i) Hint) :
    (∀ (i : ι) (t : ℝ), (intFlow Hint t)ᴴ * P i * intFlow Hint t = P i)
    ∧ (∀ (i : ι) (t : ℝ) (ρ : Matrix (Fin N) (Fin N) ℂ),
        (P i * (intFlow Hint t * ρ * (intFlow Hint t)ᴴ)).trace = (P i * ρ).trace)
    ∧ (∀ (i : ι) (t : ℝ) (ρ : Matrix (Fin N) (Fin N) ℂ), P i * ρ * P i = ρ →
        P i * (intFlow Hint t * ρ * (intFlow Hint t)ᴴ) * P i
          = intFlow Hint t * ρ * (intFlow Hint t)ᴴ) :=
  ⟨fun i t => pointer_invariant_of_commute hH (hcomm i) t,
   fun i t ρ => pointer_population_conserved hH (hcomm i) ρ t,
   fun i t _ρ hρ => sector_state_invariant hH (hcomm i) t hρ⟩

/-! ### The converse: invariance forces commutation — the criterion is a characterisation -/

/-- Heisenberg invariance at a time transfers to plain commutation with the flow at that time:
`U(t)ᴴ P U(t) = P ⟹ P U(t) = U(t) P` (left-multiply by `U(t)` and cancel `U Uᴴ = 1`). -/
lemma commute_intFlow_of_invariant {P Hint : Matrix (Fin N) (Fin N) ℂ}
    (hH : Hint.IsHermitian) {t : ℝ}
    (hinv : (intFlow Hint t)ᴴ * P * intFlow Hint t = P) :
    P * intFlow Hint t = intFlow Hint t * P := by
  have h := congrArg (fun M => intFlow Hint t * M) hinv
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, intFlow_mul_conjTranspose hH,
    Matrix.one_mul] at h
  exact h

/-- The derivative of the interaction flow at time zero is its generator `−i • Hint`. -/
lemma hasDerivAt_intFlow_zero (Hint : Matrix (Fin N) (Fin N) ℂ) :
    HasDerivAt (fun t : ℝ => intFlow Hint t) ((-Complex.I) • Hint) 0 := by
  simp only [intFlow_def]
  have h := hasDerivAt_exp_smul_const ((-Complex.I) • Hint) (0 : ℝ)
  rwa [zero_smul, exp_zero, one_mul] at h

/-- ★ **The converse of the criterion.** An observable that is a constant of the interaction
motion at every time commutes with the interaction: differentiate `P · U(t) = U(t) · P` at
`t = 0` to recover `[P, H_int] = 0`. -/
theorem commute_of_pointer_invariant {P Hint : Matrix (Fin N) (Fin N) ℂ}
    (hH : Hint.IsHermitian)
    (hinv : ∀ t : ℝ, (intFlow Hint t)ᴴ * P * intFlow Hint t = P) :
    Commute P Hint := by
  have hcomm : (fun t : ℝ => P * intFlow Hint t) = fun t : ℝ => intFlow Hint t * P :=
    funext fun t => commute_intFlow_of_invariant hH (hinv t)
  have hf : HasDerivAt (fun t : ℝ => P * intFlow Hint t) (P * ((-Complex.I) • Hint)) 0 :=
    (hasDerivAt_intFlow_zero Hint).const_mul P
  have hg : HasDerivAt (fun t : ℝ => intFlow Hint t * P) (((-Complex.I) • Hint) * P) 0 :=
    (hasDerivAt_intFlow_zero Hint).mul_const P
  have hf' : HasDerivAt (fun t : ℝ => intFlow Hint t * P) (P * ((-Complex.I) • Hint)) 0 := by
    rw [← hcomm]; exact hf
  have hAP : P * ((-Complex.I) • Hint) = ((-Complex.I) • Hint) * P := hf'.unique hg
  have h2 : Commute P (Complex.I • ((-Complex.I) • Hint)) :=
    Commute.smul_right hAP Complex.I
  rwa [smul_smul, show Complex.I * -Complex.I = 1 by
      rw [mul_neg, Complex.I_mul_I, neg_neg],
    one_smul] at h2

/-- ★★ **The einselection criterion is a characterisation.** A pointer observable is a constant of
the interaction motion at every time **iff** it commutes with the interaction: the pointer
observables of `H_int` are *exactly* the commuting ones. Forward: differentiate at `t = 0`
(`commute_of_pointer_invariant`); backward: `pointer_invariant_of_commute`. This upgrades the
criterion from sufficient to characterising, which is the form the einselection literature
intends. -/
theorem pointer_invariant_iff_commute {P Hint : Matrix (Fin N) (Fin N) ℂ}
    (hH : Hint.IsHermitian) :
    (∀ t : ℝ, (intFlow Hint t)ᴴ * P * intFlow Hint t = P) ↔ Commute P Hint :=
  ⟨commute_of_pointer_invariant hH, fun hcomm t => pointer_invariant_of_commute hH hcomm t⟩

/-- Trace separation: distinct matrices are told apart by some trace pairing. The existence form of
Mathlib's `Matrix.ext_iff_trace_mul_right` (whose witness is the matrix unit `single j i 1`, reading
entry `(i, j)`); `ρ` is a matrix, not necessarily a state — the state-level witness is the `N = 2`
contrast below. -/
lemma exists_trace_mul_ne {X Y : Matrix (Fin N) (Fin N) ℂ} (hXY : X ≠ Y) :
    ∃ ρ : Matrix (Fin N) (Fin N) ℂ, (X * ρ).trace ≠ (Y * ρ).trace := by
  by_contra h
  push Not at h
  exact hXY (Matrix.ext_iff_trace_mul_right.mpr h)

/-- ★ **A non-commuting observable is disturbed.** If `[P, H_int] ≠ 0` then at some time some
trace-functional detects the change: `tr (P · U ρ Uᴴ) ≠ tr (P · ρ)`. (The witness `ρ` is a
matrix; the concrete state-level disturbance is `noncommuting_population_disturbed`.) With
`pointer_population_conserved` this separates the commuting from the non-commuting observables
at the population level. -/
theorem exists_population_ne_of_not_commute {P Hint : Matrix (Fin N) (Fin N) ℂ}
    (hH : Hint.IsHermitian) (hnc : ¬ Commute P Hint) :
    ∃ (t : ℝ) (ρ : Matrix (Fin N) (Fin N) ℂ),
      (P * (intFlow Hint t * ρ * (intFlow Hint t)ᴴ)).trace ≠ (P * ρ).trace := by
  have hinv : ¬ ∀ t : ℝ, (intFlow Hint t)ᴴ * P * intFlow Hint t = P :=
    fun h => hnc (commute_of_pointer_invariant hH h)
  push Not at hinv
  obtain ⟨t, ht⟩ := hinv
  obtain ⟨ρ, hρ⟩ := exists_trace_mul_ne ht
  refine ⟨t, ρ, ?_⟩
  calc (P * (intFlow Hint t * ρ * (intFlow Hint t)ᴴ)).trace
      = ((P * intFlow Hint t * ρ) * (intFlow Hint t)ᴴ).trace := by
        simp only [Matrix.mul_assoc]
    _ = ((intFlow Hint t)ᴴ * (P * intFlow Hint t * ρ)).trace := Matrix.trace_mul_comm _ _
    _ = (((intFlow Hint t)ᴴ * P * intFlow Hint t) * ρ).trace := by
        simp only [Matrix.mul_assoc]
    _ ≠ (P * ρ).trace := hρ

/-! ### The class: pointer-diagonal interactions -/

/-- Every computational pointer projection `|eᵢ⟩⟨eᵢ| = Matrix.single i i 1`
commutes with every diagonal interaction. -/
theorem single_commute_diagonal (i : Fin N) (d : Fin N → ℂ) :
    Commute (Matrix.single i i (1 : ℂ)) (Matrix.diagonal d) := by
  show Matrix.single i i (1 : ℂ) * Matrix.diagonal d
      = Matrix.diagonal d * Matrix.single i i 1
  ext a b
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  by_cases h : i = a ∧ i = b
  · rw [if_pos h, one_mul, mul_one, ← h.2, ← h.1]
  · rw [if_neg h, zero_mul, mul_zero]

/-- The computational pointer projections are idempotent. -/
theorem single_mul_self (i : Fin N) :
    Matrix.single i i (1 : ℂ) * Matrix.single i i 1 = Matrix.single i i 1 := by
  rw [Matrix.single_mul_single_same, one_mul]

/-- A real-spectrum diagonal is Hermitian. -/
lemma diagonal_ofReal_isHermitian (d : Fin N → ℝ) :
    (Matrix.diagonal fun i => ((d i : ℝ) : ℂ)).IsHermitian := by
  refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
  rw [isSelfAdjoint_iff]
  funext i
  rw [Pi.star_apply]
  exact star_ofReal' (d i)

/-- ★ **The criterion holds for the whole class of pointer-diagonal
interactions.** For every real spectrum `d`, every computational projection
commutes with `H_int = diagonal d` and is a constant of its flow — the
class-level statement of einselection for the computational pointer basis. -/
theorem pointer_basis_of_diagonal (d : Fin N → ℝ) (i : Fin N) :
    Commute (Matrix.single i i (1 : ℂ)) (Matrix.diagonal fun j => ((d j : ℝ) : ℂ))
    ∧ ∀ t : ℝ,
        (intFlow (Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) t)ᴴ
            * Matrix.single i i 1
            * intFlow (Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) t
          = Matrix.single i i 1 :=
  ⟨single_commute_diagonal i _,
   fun t => pointer_invariant_of_commute (diagonal_ofReal_isHermitian d)
     (single_commute_diagonal i _) t⟩

/-- The flow of a diagonal interaction is the diagonal-phase unitary
`diag (e^{−i t d(j)})` (via `Matrix.exp_diagonal`). -/
theorem intFlow_diagonal (d : Fin N → ℝ) (t : ℝ) :
    intFlow (Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) t
      = Matrix.diagonal fun j => Complex.exp (-(Complex.I * ((t * d j : ℝ) : ℂ))) := by
  rw [intFlow_def, ← Matrix.diagonal_smul, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext j
  rw [Pi.exp_def]
  show exp (t • ((-Complex.I) • ((d j : ℝ) : ℂ)))
      = Complex.exp (-(Complex.I * ((t * d j : ℝ) : ℂ)))
  rw [← Complex.exp_eq_exp_ℂ, Complex.real_smul, smul_eq_mul]
  congr 1
  push_cast
  ring

/-- Each diagonal phase has unit modulus. -/
lemma norm_diagonal_phase (r : ℝ) :
    ‖Complex.exp (-(Complex.I * ((r : ℝ) : ℂ)))‖ = 1 := by
  rw [show -(Complex.I * ((r : ℝ) : ℂ)) = ((-r : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- ★ **Every coherence modulus survives the interaction flow.** Under the flow
of any pointer-diagonal interaction, `‖(U ρ Uᴴ) i j‖ = ‖ρ i j‖` for every entry:
the flow rotates coherences by phases and destroys none of them. The dephasing of
`LF6/Decoherence.lean` is the unmonitored-environment *trace*, not the flow —
flow preserves, trace selects. -/
theorem coherence_modulus_preserved (d : Fin N → ℝ) (t : ℝ)
    (ρ : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    ‖(intFlow (Matrix.diagonal fun k => ((d k : ℝ) : ℂ)) t * ρ
        * (intFlow (Matrix.diagonal fun k => ((d k : ℝ) : ℂ)) t)ᴴ) i j‖
      = ‖ρ i j‖ := by
  rw [intFlow_diagonal, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Pi.star_apply, norm_mul, norm_mul, norm_star,
    norm_diagonal_phase, norm_diagonal_phase, one_mul, mul_one]

/-! ### The contrast: a non-commuting observable is disturbed

The other half of einselection, concrete at `N = 2`, reusing Build 15a's
rotated-basis contrast. The interaction `contrastH = diag (0, π)` is
pointer-diagonal; the Hadamard-rotated projection `rotatedProj = qmH |e₀⟩⟨e₀| qmH`
(the `|+⟩⟨+|` projector) does **not** commute with it, and its population in its
own eigenstate is driven `1 → 0` by the time-one flow — maximal disturbance,
against exact conservation for the commuting pointer projections. -/

/-- The contrast interaction `diag (0, π)`: pointer-diagonal, Hermitian,
generating the time-one flow `diag (1, −1)` (the Pauli-`Z` stroke). -/
noncomputable def contrastH : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun j => ((![0, Real.pi] j : ℝ) : ℂ)

lemma contrastH_isHermitian : contrastH.IsHermitian :=
  diagonal_ofReal_isHermitian ![0, Real.pi]

/-- The Hadamard-rotated pointer projection `qmH |e₀⟩⟨e₀| qmH` — the `|+⟩⟨+|`
projector, Build 15a's rotated basis. -/
noncomputable def rotatedProj : Matrix (Fin 2) (Fin 2) ℂ :=
  qmH * Matrix.single 0 0 1 * qmH

/-- The rotated projection, computed: `|+⟩⟨+| = (1/2) !![1,1;1,1]`. -/
theorem rotatedProj_eq : rotatedProj = (1 / 2 : ℂ) • !![1, 1; 1, 1] := by
  have hsingle : (Matrix.single 0 0 1 : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; 0, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp
  have hA : !![(1 : ℂ), 1; 1, -1] * !![1, 0; 0, 0] * !![(1 : ℂ), 1; 1, -1]
      = !![1, 1; 1, 1] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [rotatedProj, qmH, hsingle, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, sqrt_two_inv_sq, hA]

/-- The rotated observable is a genuine projection (idempotent): non-vacuity that
the disturbed observable is a legitimate pointer candidate. -/
theorem rotatedProj_mul_self : rotatedProj * rotatedProj = rotatedProj := by
  show qmH * Matrix.single 0 0 1 * qmH * (qmH * Matrix.single 0 0 1 * qmH)
      = qmH * Matrix.single 0 0 1 * qmH
  have h : qmH * Matrix.single 0 0 1 * qmH * (qmH * Matrix.single 0 0 1 * qmH)
      = qmH * Matrix.single 0 0 1 * (qmH * qmH * Matrix.single 0 0 1 * qmH) := by
    simp only [Matrix.mul_assoc]
  rw [h, qmH_mul_self, Matrix.one_mul]
  have h2 : qmH * Matrix.single 0 0 1 * (Matrix.single 0 0 1 * qmH)
      = qmH * (Matrix.single 0 0 1 * Matrix.single 0 0 1) * qmH := by
    simp only [Matrix.mul_assoc]
  rw [h2, single_mul_self]

/-- **The rotated projection fails the commutation criterion:**
`[rotatedProj, contrastH] ≠ 0`. The failing entry is `(0,1)`, where the products
differ by `π/2 ≠ 0`. -/
theorem rotatedProj_not_commute : ¬ Commute rotatedProj contrastH := by
  intro h
  have h01 : (rotatedProj * contrastH) 0 1 = (contrastH * rotatedProj) 0 1 := by
    rw [h.eq]
  rw [rotatedProj_eq,
    show contrastH = Matrix.diagonal (fun j => ((![0, Real.pi] j : ℝ) : ℂ)) from rfl]
    at h01
  simp only [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.ofReal_zero, zero_mul] at h01
  rw [show (!![(1 : ℂ), 1; 1, 1]) 0 1 = 1 from rfl] at h01
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  apply hπ
  linear_combination 2 * h01

/-- The time-one flow of the contrast interaction is the Pauli-`Z` stroke
`diag (1, −1)` (via `intFlow_diagonal`, `Complex.exp_pi_mul_I`). -/
theorem intFlow_contrastH_one :
    intFlow contrastH 1 = Matrix.diagonal ![1, -1] := by
  rw [show contrastH = Matrix.diagonal (fun j => ((![0, Real.pi] j : ℝ) : ℂ)) from rfl,
    intFlow_diagonal]
  congr 1
  funext j
  fin_cases j
  · show Complex.exp (-(Complex.I * ((1 * (0 : ℝ) : ℝ) : ℂ))) = 1
    norm_num [Complex.exp_zero]
  · show Complex.exp (-(Complex.I * ((1 * Real.pi : ℝ) : ℂ))) = -1
    rw [show -(Complex.I * ((1 * Real.pi : ℝ) : ℂ)) = -((Real.pi : ℂ) * Complex.I) by
      push_cast; ring]
    rw [Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num

/-- **The non-commuting observable is maximally disturbed.** In its own
eigenstate (`ρ = rotatedProj`, population `1`), one stroke of the contrast flow
drives the `rotatedProj`-population to `0`: `tr (Q · U Q Uᴴ) = 0` while
`tr (Q · Q) = 1`. Compare `pointer_population_conserved`: a commuting observable
is conserved in **every** state, at **every** time. -/
theorem noncommuting_population_disturbed :
    (rotatedProj * rotatedProj).trace = 1
    ∧ (rotatedProj
        * (intFlow contrastH 1 * rotatedProj * (intFlow contrastH 1)ᴴ)).trace = 0 := by
  have hUH : (Matrix.diagonal (![1, -1] : Fin 2 → ℂ))ᴴ = Matrix.diagonal ![1, -1] := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext k
    fin_cases k <;> simp
  have hDMD : Matrix.diagonal (![1, -1] : Fin 2 → ℂ) * !![(1 : ℂ), 1; 1, 1]
      * Matrix.diagonal ![1, -1] = !![1, -1; -1, 1] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hMM : !![(1 : ℂ), 1; 1, 1] * !![1, 1; 1, 1] = !![2, 2; 2, 2] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
        norm_num
  have hM0 : !![(1 : ℂ), 1; 1, 1] * !![1, -1; -1, 1] = 0 := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · rw [rotatedProj_eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.trace_smul, hMM, Matrix.trace_fin_two_of]
    norm_num
  · rw [intFlow_contrastH_one, rotatedProj_eq, hUH]
    have hconj : Matrix.diagonal (![1, -1] : Fin 2 → ℂ) * ((1 / 2 : ℂ) • !![1, 1; 1, 1])
        * Matrix.diagonal ![1, -1] = (1 / 2 : ℂ) • !![1, -1; -1, 1] := by
      rw [Matrix.mul_smul, Matrix.smul_mul, hDMD]
    rw [hconj, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hM0, smul_zero,
      Matrix.trace_zero]

/-- ★★ **The einselection commutation contrast: the criterion separates.** For
the pointer-diagonal contrast interaction `contrastH = diag (0, π)`:

1. **commuting ⟹ conserved** — every computational pointer projection is a
   constant of the flow, `U(t)ᴴ |eᵢ⟩⟨eᵢ| U(t) = |eᵢ⟩⟨eᵢ|`
   (`pointer_basis_of_diagonal`);
2. **the rotated observable fails the criterion** — `[rotatedProj, contrastH] ≠ 0`
   (`rotatedProj_not_commute`), though it is a genuine projection
   (`rotatedProj_mul_self`);
3. **and is maximally disturbed** — its population in its own eigenstate is
   driven `1 → 0` by one stroke (`noncommuting_population_disturbed`).

The pointer basis is the one the interaction does not disturb — the field's
einselection answer to "why this basis", machine-checked. **Residue:** the
interaction `H_int` is the measurement context and remains an input. -/
theorem einselection_commutation_contrast :
    (∀ (i : Fin 2) (t : ℝ),
        (intFlow contrastH t)ᴴ * Matrix.single i i 1 * intFlow contrastH t
          = Matrix.single i i 1)
    ∧ ¬ Commute rotatedProj contrastH
    ∧ rotatedProj * rotatedProj = rotatedProj
    ∧ (rotatedProj * rotatedProj).trace = 1
    ∧ (rotatedProj
        * (intFlow contrastH 1 * rotatedProj * (intFlow contrastH 1)ᴴ)).trace = 0 :=
  ⟨fun i t => (pointer_basis_of_diagonal ![0, Real.pi] i).2 t,
   rotatedProj_not_commute,
   rotatedProj_mul_self,
   (noncommuting_population_disturbed).1,
   (noncommuting_population_disturbed).2⟩

end Einselection
end CSDBridge
end Empirical
end CSD
