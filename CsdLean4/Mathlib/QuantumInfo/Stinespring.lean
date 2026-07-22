/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Mathlib.QuantumInfo.Channel
import CsdLean4.Mathlib.LinearAlgebra.Matrix.PartialTrace

/-!
# Stinespring dilation of a Kraus-form quantum channel

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

This file (phase C2 of `specs/channels-plan.md`) gives the **Stinespring / dilation form**
of a finite-dimensional quantum channel and the Kraus ↔ Stinespring bridge. A channel
`Φ : Matrix n n ℂ → Matrix m m ℂ` is realised as

  `Φ(ρ) = traceRight (V * ρ * Vᴴ)`,    `V : Matrix (m × e) n ℂ`,   `Vᴴ V = 1`,

i.e. an isometric embedding `V` into `system ⊗ environment` followed by tracing out the
environment `e`. Operationally: dilate to a closed (isometric) evolution on the enlarged
state space, then average over the environment.

The whole bridge rests on a single block-algebra identity. For *any* `V : Matrix (m × e) n ℂ`,
its **environment blocks** `krausBlock V i := (a, j) ↦ V (a, i) j` satisfy

* `sum_krausBlock_conjTranspose_mul`: `∑ᵢ (krausBlock V i)ᴴ * (krausBlock V i) = Vᴴ * V`
  — so `V` is an **isometry** iff the blocks are **trace-preserving Kraus operators**;
* `traceRight_conj_eq_sum_krausBlock`: `traceRight (V * ρ * Vᴴ) = ∑ᵢ (krausBlock V i) ρ (krausBlock V i)ᴴ`
  — so the **environment-averaged joint conjugation is exactly the Kraus action**.

From these:

* `Channel.ofIsometry V hV` — the channel whose Kraus operators are the env-blocks of an
  isometry `V` (`kraus_of_isometry` direction), with `ofIsometry_apply` identifying its
  action with `traceRight (V ρ Vᴴ)`;
* `Channel.stinespringIsom Φ` — the stacked-Kraus isometry of a channel
  (`dilation_exists` direction), `stinespringIsom_isom : (stinespringIsom Φ)ᴴ (stinespringIsom Φ) = 1`,
  and `apply_eq_traceRight_stinespring : Φ.apply ρ = traceRight (stinespringIsom Φ * ρ * (stinespringIsom Φ)ᴴ)`.

**CSD reading (see `specs/channels-plan.md` §3).** The Stinespring isometry is a
measure-preserving joint flow on `Σ_sys × Σ_env` and `traceRight` is the environment
average, so a channel *is* the environment-marginal of a genuine `Φ ≠ id` flow — the
structural on-ramp to the dynamics frontier (decoherence = environment volume flow).
-/

open Matrix
open scoped ComplexOrder

-- The block lemmas are stated for a fixed index/scalar setup; several use only a subset
-- of the section's `Fintype`/`DecidableEq` instances, which trips the section-var linter
-- without indicating any real issue.
set_option linter.unusedSectionVars false

namespace QuantumInfo

variable {n m e ι : Type*} [Fintype n] [Fintype m] [Fintype e] [Fintype ι]
  [DecidableEq n]

/-- The **environment block** `i` of a matrix `V : Matrix (m × e) n ℂ`: the operator
`ℂⁿ → ℂᵐ` selecting the `i`-th environment slot, `(krausBlock V i) a j = V (a, i) j`. -/
def krausBlock (V : Matrix (m × e) n ℂ) (i : e) : Matrix m n ℂ :=
  Matrix.of fun a j => V (a, i) j

@[simp] lemma krausBlock_apply (V : Matrix (m × e) n ℂ) (i : e) (a : m) (j : n) :
    krausBlock V i a j = V (a, i) j := rfl

/-- The defining block identity: `∑ᵢ (krausBlock V i)ᴴ (krausBlock V i) = Vᴴ V`. So `V` is
an isometry exactly when its environment blocks are trace-preserving Kraus operators. -/
lemma sum_krausBlock_conjTranspose_mul (V : Matrix (m × e) n ℂ) :
    ∑ i, (krausBlock V i)ᴴ * (krausBlock V i) = Vᴴ * V := by
  ext j j'
  rw [Matrix.sum_apply]
  conv_rhs => rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Matrix.conjTranspose_apply]

/-- The action identity: the environment-averaged joint conjugation of `V` is the Kraus
action of its environment blocks, `traceRight (V ρ Vᴴ) = ∑ᵢ (krausBlock V i) ρ (krausBlock V i)ᴴ`. -/
lemma traceRight_conj_eq_sum_krausBlock (V : Matrix (m × e) n ℂ) (ρ : Matrix n n ℂ) :
    Matrix.traceRight (V * ρ * Vᴴ) = ∑ i, krausBlock V i * ρ * (krausBlock V i)ᴴ := by
  ext a b
  rw [Matrix.traceRight_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mul_apply, krausBlock_apply, Matrix.conjTranspose_apply]

namespace Channel

/-- **Kraus ⇐ isometry** (`kraus_of_isometry`). The channel whose Kraus operators are the
environment blocks of an isometry `V : Matrix (m × e) n ℂ` (`Vᴴ V = 1`). Its action is the
Stinespring form `ρ ↦ traceRight (V ρ Vᴴ)` (see `ofIsometry_apply`). -/
noncomputable def ofIsometry (V : Matrix (m × e) n ℂ) (hV : Vᴴ * V = 1) :
    Channel n m e where
  kraus := krausBlock V
  tp := by rw [sum_krausBlock_conjTranspose_mul]; exact hV

/-- The action of `ofIsometry V hV` is the Stinespring form: dilate by `V`, then trace out
the environment. -/
lemma ofIsometry_apply (V : Matrix (m × e) n ℂ) (hV : Vᴴ * V = 1) (ρ : Matrix n n ℂ) :
    (ofIsometry V hV).apply ρ = Matrix.traceRight (V * ρ * Vᴴ) := by
  rw [apply_def, traceRight_conj_eq_sum_krausBlock]
  rfl

/-- **Isometry ⇐ Kraus** (`dilation_exists`). The Stinespring isometry of a channel, stacking
its Kraus operators along the environment index `ι`: `(stinespringIsom Φ) (a, i) j = (Φ.kraus i) a j`. -/
def stinespringIsom (Φ : Channel n m ι) : Matrix (m × ι) n ℂ :=
  Matrix.of fun p j => Φ.kraus p.2 p.1 j

@[simp] lemma krausBlock_stinespringIsom (Φ : Channel n m ι) (i : ι) :
    krausBlock (Φ.stinespringIsom) i = Φ.kraus i := by
  ext a j; rfl

/-- The Stinespring dilation `stinespringIsom Φ` is a genuine **isometry**:
`(stinespringIsom Φ)ᴴ (stinespringIsom Φ) = 1`, exactly the trace-preserving constraint. -/
lemma stinespringIsom_isom (Φ : Channel n m ι) :
    (Φ.stinespringIsom)ᴴ * Φ.stinespringIsom = 1 := by
  rw [← sum_krausBlock_conjTranspose_mul (Φ.stinespringIsom)]
  simp_rw [krausBlock_stinespringIsom]
  exact Φ.tp

/-- **Stinespring = Kraus.** The channel action is the dilate-then-trace form for the
stacked-Kraus isometry: `Φ(ρ) = traceRight (V ρ Vᴴ)` with `V = stinespringIsom Φ`. -/
lemma apply_eq_traceRight_stinespring (Φ : Channel n m ι) (ρ : Matrix n n ℂ) :
    Φ.apply ρ =
      Matrix.traceRight (Φ.stinespringIsom * ρ * (Φ.stinespringIsom)ᴴ) := by
  rw [traceRight_conj_eq_sum_krausBlock]
  simp_rw [krausBlock_stinespringIsom]
  rw [apply_def]

end Channel
end QuantumInfo
