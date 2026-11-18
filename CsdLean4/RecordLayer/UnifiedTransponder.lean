/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedCompositeCarrier
public import CsdLean4.Mathlib.Analysis.Matrix.DuhamelSector

/-!
# The transponder: no launch without a meeting

**Category:** 7-SigmaLayer. BACKLOG #437, fourth brick (the return caused at the event;
obligation UO-26, item (1); assumption UA-19 (a), (b)).

UA-19 puts a second carrier with two levels at the event, coupled to the messenger by a
contact term that swaps its level. Here the first of UO-26's five items is shown for that
structure: the second level is not populated before the free orbit has weight where the
contact term acts.

* `levelProj` (the projector on one level), `levelProj_mul_blockDiagonal` (a Hamiltonian with
  one block for each level commutes with it), `blockDiagonal_isHermitian`,
  `one_kronecker_mul_compositeH` (so does the composite's);
* ★★★ `transponder_launch_le` — for a messenger and a transponder whose Hamiltonian has one
  block for each level, coupled by `g G` with `G` Hermitian, and a prepared subspace with the
  transponder in its first level: at `t ≥ 0` the part with the transponder in its second
  level is at most `‖Q‖ |g| ∫₀ᵗ ‖G e^{−isH₀} X‖ ds`, `H₀` the uncoupled Hamiltonian.

## Honest scope

⚠️ **The causal half only.** No launch is shown: the integral is an upper bound and the
first-order term of `Mathlib/Analysis/Matrix/DuhamelFirstOrder.lean` is not evaluated for a
contact term. Items (2) to (5) of UO-26 are open.

⚠️ **`G` is any Hermitian matrix.** The coincidence projector times the level swap of UA-19
(b) (`gateOp` with `levelSwap`) is one such `G`, but it is not substituted, and the integrand
is not expressed as the free orbit's weight at a meeting.

⚠️ **On the carriers' Hilbert space, not on the arena.** By UA-19 (b) the contact term is
present on the fibres where a pointer's profile does not vanish; the pointer's own motion
there is not treated.

⚠️ **`‖Q‖` is not evaluated** (it is at most `1`; that is not shown here).

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-18, UA-19,
UO-26, UD-211, UD-212, UD-216, UD-224); `Mathlib/Analysis/Matrix/DuhamelSector.lean`
(`norm_mul_exp_neg_I_add_smul_mul_le_of_commute`); `RecordLayer/UnifiedCompositeCarrier.lean`
(`compositeH`, `compositeH_isHermitian`); `RecordLayer/UnifiedCoincidence.lean` (`gateOp`);
`RecordLayer/UnifiedDiracClock.lean` (`levelSwap`); `CV/DiracDevice.lean` (`deviceHam`);
`specs/unified-m7-feasibility.md` (§7); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker
open NormedSpace

namespace CSD.RecordLayer

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

/-- **The projector on one level** of a carrier with a two-level internal degree of freedom. -/
def levelProj (n : Type*) [DecidableEq n] (l : Fin 2) : Matrix (n × Fin 2) (n × Fin 2) ℂ :=
  Matrix.diagonal fun x => if x.2 = l then 1 else 0

/-- A Hamiltonian with one block for each level commutes with the level projectors. -/
theorem levelProj_mul_blockDiagonal (T : Fin 2 → Matrix n n ℂ) (l : Fin 2) :
    levelProj n l * Matrix.blockDiagonal T = Matrix.blockDiagonal T * levelProj n l := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [levelProj, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.blockDiagonal_apply']
  by_cases hij : i = j
  · subst hij
    ring
  · simp [hij]

omit [Fintype n] [DecidableEq n] in
theorem blockDiagonal_isHermitian {T : Fin 2 → Matrix n n ℂ} (hT : ∀ l, (T l).IsHermitian) :
    (Matrix.blockDiagonal T).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.blockDiagonal_conjTranspose]
  congr 1
  funext l
  exact (hT l).eq

/-- An operator on the second carrier that commutes with its Hamiltonian commutes with the
composite's. -/
theorem one_kronecker_mul_compositeH (A₀ : Matrix ι ι ℂ) {C₀ P : Matrix n n ℂ}
    (h : P * C₀ = C₀ * P) :
    ((1 : Matrix ι ι ℂ) ⊗ₖ P) * compositeH A₀ C₀
      = compositeH A₀ C₀ * ((1 : Matrix ι ι ℂ) ⊗ₖ P) := by
  unfold compositeH
  rw [mul_add, add_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [one_mul, mul_one, h]

variable [Nonempty ι] [Nonempty n]

/-- ★★★ **No launch without a meeting.** A messenger with Hamiltonian `M₀` and a transponder
whose Hamiltonian has one block for each of its two levels, coupled by `g G` for a Hermitian
`G` (UA-19: the coincidence projector times the transponder's level swap). If the prepared
subspace `X` has the transponder in its first level, then at the time `t ≥ 0` the part of the
state with the transponder in its second level is at most

  `‖Q‖ |g| ∫₀ᵗ ‖G e^{−i s H₀} X‖ ds`,

`Q` the projector on the second level and `H₀` the uncoupled Hamiltonian: the accumulated
action of the contact term on the free orbit. -/
theorem transponder_launch_le {M₀ : Matrix ι ι ℂ} (hM : M₀.IsHermitian)
    {T : Fin 2 → Matrix n n ℂ} (hT : ∀ l, (T l).IsHermitian)
    {G : Matrix (ι × (n × Fin 2)) (ι × (n × Fin 2)) ℂ} (hG : G.IsHermitian) (g : ℝ)
    (X : Matrix (ι × (n × Fin 2)) (ι × (n × Fin 2)) ℂ)
    (hX : ((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1) * X = 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖((1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1)
        * exp (t • ((-Complex.I) • (compositeH M₀ (Matrix.blockDiagonal T) + (g : ℂ) • G)))
        * X‖
      ≤ ‖(1 : Matrix ι ι ℂ) ⊗ₖ levelProj n 1‖
        * (|g| * ∫ s in (0 : ℝ)..t,
            ‖G * exp (s • ((-Complex.I) • compositeH M₀ (Matrix.blockDiagonal T))) * X‖) :=
  Matrix.norm_mul_exp_neg_I_add_smul_mul_le_of_commute _ G X _ g
    (compositeH_isHermitian hM (blockDiagonal_isHermitian hT)) hG ht
    (one_kronecker_mul_compositeH M₀ (levelProj_mul_blockDiagonal T 1)) hX

end CSD.RecordLayer

end
