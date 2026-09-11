/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Channel

/-!
# Composition of quantum channels

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

`Channel.comp Ψ Φ` is the composite channel with Kraus family `{Ψₐ Φₖ}` indexed by `κ × ι`; the
trace-preserving constraint follows by inserting `∑ₐ Ψₐᴴ Ψₐ = 1` into `∑ₖ Φₖᴴ (·) Φₖ`, and
`comp_apply` says the action composes. Index-generic; the `Fin`-indexed `CSD.LF2.QuantumChannel.comp`
is its image under `CSD.LF2.QuantumChannel.toChannel` (`LF2/ChannelBridge.lean`).
-/

@[expose] public section

open Matrix
open scoped ComplexOrder

/-! ### Composition of `QuantumInfo.Channel` (index-generic) -/

namespace QuantumInfo.Channel

variable {n m p ι κ : Type*} [Fintype n] [Fintype m] [Fintype p] [Fintype ι] [Fintype κ]
  [DecidableEq n] [DecidableEq m]

/-- **Channels compose**: the composite `Ψ ∘ Φ` has Kraus family `{Ψₐ Φₖ}` indexed by `κ × ι`. -/
noncomputable def comp (Ψ : Channel m p κ) (Φ : Channel n m ι) : Channel n p (κ × ι) where
  kraus q := Ψ.kraus q.1 * Φ.kraus q.2
  tp := by
    rw [← Φ.tp, Fintype.sum_prod_type]
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun k _ => ?_)
    calc ∑ a, (Ψ.kraus a * Φ.kraus k)ᴴ * (Ψ.kraus a * Φ.kraus k)
        = ∑ a, (Φ.kraus k)ᴴ * ((Ψ.kraus a)ᴴ * Ψ.kraus a) * Φ.kraus k := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = (Φ.kraus k)ᴴ * (∑ a, (Ψ.kraus a)ᴴ * Ψ.kraus a) * Φ.kraus k := by
          rw [← Matrix.sum_mul, ← Matrix.mul_sum]
      _ = (Φ.kraus k)ᴴ * Φ.kraus k := by rw [Ψ.tp, Matrix.mul_one]

@[simp] theorem comp_kraus (Ψ : Channel m p κ) (Φ : Channel n m ι) (q : κ × ι) :
    (Ψ.comp Φ).kraus q = Ψ.kraus q.1 * Φ.kraus q.2 := rfl

/-- The composite acts by composing the actions. -/
theorem comp_apply (Ψ : Channel m p κ) (Φ : Channel n m ι) (ρ : Matrix n n ℂ) :
    (Ψ.comp Φ).apply ρ = Ψ.apply (Φ.apply ρ) := by
  simp only [Channel.apply_def, comp_kraus, Fintype.sum_prod_type, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

end QuantumInfo.Channel
