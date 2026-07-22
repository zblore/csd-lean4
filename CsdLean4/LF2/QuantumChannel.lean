/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF2.BornWrapper
public import CsdLean4.Mathlib.QuantumInfo.PartialTrace
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# LF2/QuantumChannel: quantum channels (CPTP maps) — Kraus form + CPTP-forward (tranche 1)

**Category:** 2-LF2 (the operational / Born layer).

The general open-system dynamics pillar: a quantum channel is a completely-positive trace-preserving (CPTP)
map on density operators. We take the operational **Kraus** definition — a finite family of operators
`Kₖ` with `∑ₖ Kₖ† Kₖ = 1` — and prove the CPTP-forward content: a channel maps density operators to
density operators (this tranche). Later tranches add the Stinespring dilation and the Choi matrix.

* `QuantumChannel ι N M` — a Kraus family `kraus : ι → Matrix (Fin M) (Fin N) ℂ` with the
  trace-preservation constraint `∑ₖ Kₖ† Kₖ = 1`;
* `apply Φ ρ = ∑ₖ Kₖ ρ Kₖ†` — the channel action, and `channelApply` its action on `DensityOperator`s;
* `apply_posSemidef` / `apply_trace` — positivity and trace preservation, so `channelApply` lands in
  `DensityOperator M` (the CPTP-forward theorem);
* `unitaryChannel` — unitary conjugation `ρ ↦ U ρ U†` is a channel (closed dynamics as a special case);
* `comp` — channels compose (`κ × ι` Kraus family), so the channels form a composition monoid.

Built on `LF2.DensityOperator` and Mathlib's `Matrix.PosSemidef.mul_mul_conjTranspose_same`,
`Matrix.posSemidef_sum`, `Matrix.trace_mul_comm`.

References: `LF2/BornWrapper.lean` (`DensityOperator`, `traceForm`); `LF2/ReducedDensity.lean`
(`partialTrace*`, for the forthcoming Stinespring tranche); `specs/future-work.md`.
-/

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace CSD.LF2

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {N M P : ℕ}

/-- **A quantum channel in Kraus form.** A finite family of Kraus operators `Kₖ : Fin M ← Fin N` with the
trace-preservation constraint `∑ₖ Kₖ† Kₖ = 1`. The operational definition of a CPTP map from an
`N`-dimensional to an `M`-dimensional system. -/
structure QuantumChannel (ι : Type*) [Fintype ι] (N M : ℕ) where
  /-- The Kraus operators. -/
  kraus : ι → Matrix (Fin M) (Fin N) ℂ
  /-- Trace preservation: `∑ₖ Kₖ† Kₖ = 1`. -/
  isTracePreserving : ∑ k, (kraus k)ᴴ * kraus k = 1

namespace QuantumChannel

/-- **The channel action** `Φ(ρ) = ∑ₖ Kₖ ρ Kₖ†`. -/
noncomputable def apply (Φ : QuantumChannel ι N M) (ρ : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin M) (Fin M) ℂ :=
  ∑ k, Φ.kraus k * ρ * (Φ.kraus k)ᴴ

/-- **Complete positivity (forward, single copy):** the channel preserves positive semidefiniteness. Each
Kraus term `Kₖ ρ Kₖ†` is PSD when `ρ` is (`mul_mul_conjTranspose_same`), and PSD is closed under sums. -/
theorem apply_posSemidef (Φ : QuantumChannel ι N M) {ρ : Matrix (Fin N) (Fin N) ℂ}
    (hρ : ρ.PosSemidef) : (Φ.apply ρ).PosSemidef :=
  Matrix.posSemidef_sum _ fun k _ => hρ.mul_mul_conjTranspose_same (Φ.kraus k)

/-- **Trace preservation:** `Tr(Φ(ρ)) = Tr(ρ)`. Trace cyclicity turns each `Tr(Kₖ ρ Kₖ†)` into
`Tr(Kₖ† Kₖ ρ)`, and the constraint `∑ₖ Kₖ† Kₖ = 1` collapses the sum to `Tr(ρ)`. -/
theorem apply_trace (Φ : QuantumChannel ι N M) (ρ : Matrix (Fin N) (Fin N) ℂ) :
    (Φ.apply ρ).trace = ρ.trace := by
  rw [apply, Matrix.trace_sum]
  have hcyc : ∀ k, (Φ.kraus k * ρ * (Φ.kraus k)ᴴ).trace = ((Φ.kraus k)ᴴ * Φ.kraus k * ρ).trace :=
    fun k => by rw [Matrix.trace_mul_comm (Φ.kraus k * ρ) (Φ.kraus k)ᴴ, ← Matrix.mul_assoc]
  rw [Finset.sum_congr rfl fun k _ => hcyc k, ← Matrix.trace_sum, ← Finset.sum_mul,
    Φ.isTracePreserving, Matrix.one_mul]

/-- **CPTP-forward: a channel maps density operators to density operators.** `Φ(ρ)` is Hermitian, PSD, and
trace one — a genuine density operator on the output system. This is the operational content that quantum
channels are the right notion of general (open-system) dynamics. -/
noncomputable def channelApply (Φ : QuantumChannel ι N M) (ρ : DensityOperator N) : DensityOperator M where
  M := Φ.apply ρ.M
  isHermitian := (Φ.apply_posSemidef ρ.nonneg).isHermitian
  nonneg := Φ.apply_posSemidef ρ.nonneg
  trace_one := by rw [Φ.apply_trace, ρ.trace_one]

@[simp] theorem channelApply_M (Φ : QuantumChannel ι N M) (ρ : DensityOperator N) :
    (Φ.channelApply ρ).M = Φ.apply ρ.M := rfl

/-- **Unitary conjugation is a channel** `ρ ↦ U ρ U†` (closed, reversible dynamics as the single-Kraus
special case). -/
noncomputable def unitaryChannel (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1) :
    QuantumChannel (Fin 1) N N where
  kraus := fun _ => U
  isTracePreserving := by rw [Fin.sum_univ_one]; exact hU

@[simp] theorem unitaryChannel_apply (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1)
    (ρ : Matrix (Fin N) (Fin N) ℂ) : (unitaryChannel U hU).apply ρ = U * ρ * Uᴴ := by
  simp only [apply, unitaryChannel, Fin.sum_univ_one]

/-- **Channels compose:** the composite `Ψ ∘ Φ` has Kraus family `{Ψₐ Φₖ}`. The constraint follows by
inserting `∑ₐ Ψₐ† Ψₐ = 1` into `∑ₖ Φₖ† (∑ₐ Ψₐ† Ψₐ) Φₖ = ∑ₖ Φₖ† Φₖ = 1`. -/
noncomputable def comp (Ψ : QuantumChannel κ M P) (Φ : QuantumChannel ι N M) :
    QuantumChannel (κ × ι) N P where
  kraus := fun p => Ψ.kraus p.1 * Φ.kraus p.2
  isTracePreserving := by
    rw [← Φ.isTracePreserving]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    calc ∑ a, (Ψ.kraus a * Φ.kraus k)ᴴ * (Ψ.kraus a * Φ.kraus k)
        = ∑ a, (Φ.kraus k)ᴴ * ((Ψ.kraus a)ᴴ * Ψ.kraus a) * Φ.kraus k := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = (Φ.kraus k)ᴴ * (∑ a, (Ψ.kraus a)ᴴ * Ψ.kraus a) * Φ.kraus k := by
          rw [← Matrix.sum_mul, ← Matrix.mul_sum]
      _ = (Φ.kraus k)ᴴ * Φ.kraus k := by rw [Ψ.isTracePreserving, Matrix.mul_one]

/-- **CPTP-forward capstone (tranche 1).** A quantum channel (Kraus form) sends density operators to
density operators; unitary conjugation is a channel; channels compose. So CPTP maps are a genuine
composition monoid of state transformations extending unitary evolution. -/
theorem cptp_capstone (Φ : QuantumChannel ι N M) (ρ : DensityOperator N) :
    (Φ.apply ρ.M).PosSemidef ∧ (Φ.apply ρ.M).trace = 1 :=
  ⟨Φ.apply_posSemidef ρ.nonneg, by rw [Φ.apply_trace, ρ.trace_one]⟩

/-! ### Tranche 2 — Stinespring dilation

Every channel is "a unitary/isometric embedding into a larger system + environment, then trace out the
environment". The Kraus operators stack into an isometry `V : Fin N → Fin M × ι`, and the channel is
`Φ(ρ) = Tr_E(V ρ V†)`. -/

/-- **The Stinespring dilation isometry.** The Kraus family stacked into one operator
`V : Fin N → Fin M × ι`, `V(m,k) n = Kₖ m n` (the environment `ι` records which Kraus branch). -/
noncomputable def dilation (Φ : QuantumChannel ι N M) : Matrix (Fin M × ι) (Fin N) ℂ :=
  fun a n => Φ.kraus a.2 a.1 n

@[simp] theorem dilation_apply (Φ : QuantumChannel ι N M) (a : Fin M × ι) (n : Fin N) :
    Φ.dilation a n = Φ.kraus a.2 a.1 n := rfl

/-- **The dilation is an isometry:** `V† V = 1`. Exactly the trace-preservation constraint
`∑ₖ Kₖ† Kₖ = 1` reindexed over the stacked output `Fin M × ι`. -/
theorem dilation_isometry (Φ : QuantumChannel ι N M) : (Φ.dilation)ᴴ * Φ.dilation = 1 := by
  ext n n'
  rw [Matrix.mul_apply, ← Φ.isTracePreserving, Matrix.sum_apply]
  simp only [Matrix.conjTranspose_apply, dilation_apply, Matrix.mul_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- **Stinespring dilation:** `Φ(ρ) = Tr_E(V ρ V†)`. The channel is unitary/isometric evolution into
system ⊗ environment followed by tracing out the environment — the structural statement that open-system
dynamics is closed dynamics on a larger space. -/
theorem stinespring [DecidableEq ι] (Φ : QuantumChannel ι N M) (ρ : Matrix (Fin N) (Fin N) ℂ) :
    QuantumInfo.partialTraceRight (Φ.dilation * ρ * (Φ.dilation)ᴴ) = Φ.apply ρ := by
  ext m m'
  rw [QuantumInfo.partialTraceRight_apply, apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.mul_apply, dilation_apply, Matrix.conjTranspose_apply]

/-! ### Tranche 3 — the Choi matrix (complete-positivity witness)

The Choi matrix `C_Φ = ∑ₖ vec(Kₖ) vec(Kₖ)†` is positive semidefinite — the Choi–Jamiołkowski witness of
complete positivity (the "easy" direction of Choi's theorem: a Kraus-form channel has PSD Choi matrix). -/

/-- **The Choi matrix** `C_Φ ∈ Matrix (Fin M × Fin N)`, `C_Φ (m,n)(m',n') = ∑ₖ Kₖ(m,n) · conj(Kₖ(m',n'))`
— the sum of the rank-one outer products of the vectorised Kraus operators. -/
noncomputable def choiMatrix (Φ : QuantumChannel ι N M) :
    Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ :=
  ∑ k, Matrix.vecMulVec (fun p => Φ.kraus k p.1 p.2) (star fun p => Φ.kraus k p.1 p.2)

@[simp] theorem choiMatrix_apply (Φ : QuantumChannel ι N M) (p q : Fin M × Fin N) :
    Φ.choiMatrix p q = ∑ k, Φ.kraus k p.1 p.2 * star (Φ.kraus k q.1 q.2) := by
  simp only [choiMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply]

/-- **Complete positivity: the Choi matrix is positive semidefinite.** Each term `vec(Kₖ) vec(Kₖ)†` is a
rank-one PSD outer product, and PSD is closed under sums. This is the Choi–Jamiołkowski witness that a
Kraus-form channel is completely positive. -/
theorem choiMatrix_posSemidef (Φ : QuantumChannel ι N M) : (Φ.choiMatrix).PosSemidef :=
  Matrix.posSemidef_sum _ fun _ _ => Matrix.posSemidef_vecMulVec_self_star _

end QuantumChannel

end CSD.LF2
