import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Matrix.PosDef

/-!
# Finite-dimensional quantum channels (Kraus form)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

A **quantum channel** `Φ : Matrix n n ℂ → Matrix m m ℂ` in **Kraus form**: a finite family
of Kraus operators `Kᵢ : Matrix m n ℂ` with the **trace-preserving** constraint
`∑ᵢ Kᵢᴴ Kᵢ = 1`, acting by `Φ(ρ) = ∑ᵢ Kᵢ ρ Kᵢᴴ`.

This file (phase C1 of `specs/channels-plan.md`) establishes the type and the core
properties: the action is linear, **trace-preserving** (`apply_trace`), **positive**
(`apply_posSemidef`), and **Hermiticity-preserving** (`apply_isHermitian`) — so a channel
maps density operators to density operators. Complete positivity is automatic from the
Kraus form (each `Kᵢ ρ Kᵢᴴ` is positive); the Stinespring dilation (the
"unitary-on-system⊗environment then trace the environment" form) and the canonical channels
are later phases.

The Kraus index `ι` is an arbitrary `Fintype` (matching `CSD.LF2.POVM`'s convention).
-/

open Matrix
open scoped ComplexOrder

namespace QuantumInfo

/-- A finite-dimensional **quantum channel** in Kraus form: Kraus operators `kraus i` with
the trace-preserving (TP) constraint `∑ᵢ (kraus i)ᴴ (kraus i) = 1`. The action is
`apply ρ = ∑ᵢ (kraus i) ρ (kraus i)ᴴ`. -/
structure Channel (n m ι : Type*) [Fintype n] [Fintype m] [Fintype ι] [DecidableEq n] where
  /-- The Kraus operators `Kᵢ : ℂⁿ → ℂᵐ`. -/
  kraus : ι → Matrix m n ℂ
  /-- Trace preservation: `∑ᵢ Kᵢᴴ Kᵢ = 1`. -/
  tp : (∑ i : ι, (kraus i)ᴴ * (kraus i) : Matrix n n ℂ) = 1

namespace Channel

variable {n m ι : Type*} [Fintype n] [Fintype m] [Fintype ι] [DecidableEq n]

/-- The action of a channel on an operator: `Φ(ρ) = ∑ᵢ Kᵢ ρ Kᵢᴴ`. -/
noncomputable def apply (Φ : Channel n m ι) (ρ : Matrix n n ℂ) : Matrix m m ℂ :=
  ∑ i : ι, Φ.kraus i * ρ * (Φ.kraus i)ᴴ

@[simp] lemma apply_def (Φ : Channel n m ι) (ρ : Matrix n n ℂ) :
    Φ.apply ρ = ∑ i : ι, Φ.kraus i * ρ * (Φ.kraus i)ᴴ := rfl

/-- The channel action is additive. -/
lemma apply_add (Φ : Channel n m ι) (ρ σ : Matrix n n ℂ) :
    Φ.apply (ρ + σ) = Φ.apply ρ + Φ.apply σ := by
  simp only [apply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

/-- The channel action commutes with scalar multiplication. -/
lemma apply_smul (Φ : Channel n m ι) (c : ℂ) (ρ : Matrix n n ℂ) :
    Φ.apply (c • ρ) = c • Φ.apply ρ := by
  simp only [apply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

/-- **Trace preservation.** `Tr(Φ ρ) = Tr ρ` — the defining TP property, from
`∑ᵢ Kᵢᴴ Kᵢ = 1` and trace cyclicity. -/
lemma apply_trace (Φ : Channel n m ι) (ρ : Matrix n n ℂ) :
    (Φ.apply ρ).trace = ρ.trace := by
  simp only [apply, Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (Φ.kraus _) ρ (Φ.kraus _)ᴴ]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, Φ.tp, Matrix.one_mul]

/-- **Positivity.** A channel maps positive-semidefinite operators to positive-semidefinite
operators: each `Kᵢ ρ Kᵢᴴ` is PSD, and PSD is closed under finite sums. -/
lemma apply_posSemidef (Φ : Channel n m ι) {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    (Φ.apply ρ).PosSemidef := by
  rw [apply]
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
    Matrix.PosSemidef.zero (fun i _ => ?_)
  exact hρ.mul_mul_conjTranspose_same (Φ.kraus i)

/-- A channel preserves Hermiticity. -/
lemma apply_isHermitian (Φ : Channel n m ι) {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    (Φ.apply ρ).IsHermitian := by
  unfold Matrix.IsHermitian apply
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hρ.eq, Matrix.mul_assoc]

/-- The **identity channel** (a single Kraus operator `1`). -/
def id (n : Type*) [Fintype n] [DecidableEq n] : Channel n n PUnit where
  kraus _ := 1
  tp := by simp

@[simp] lemma id_apply (n : Type*) [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ) :
    (Channel.id n).apply ρ = ρ := by
  simp [apply, Channel.id]

end Channel
end QuantumInfo
