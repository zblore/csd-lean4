/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.ODE.FlowDerivative
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Unitary propagators of a time-dependent anti-Hermitian generator

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #160/#161 (out of ~~#88~~): the common core of the adiabatic intertwiner and of the two
propagators of Kato's adiabatic theorem.

For a continuous `G : ℝ → Matrix (Fin N) (Fin N) ℂ`, a **propagator** of `G` on `[0, T]` is a
solution `U` of `U' = G U`, `U 0 = 1` (one-sided derivatives at the ends). This file proves what
the adiabatic theorem uses about such solutions when `G` is anti-Hermitian, all by one device —
the derivative of `U† Y` vanishes whenever `Y' = G Y`, so `U† Y` is constant:

* `eq_of_hasDerivWithinAt_zero_Icc` — a function with zero derivative within `[0, T]` is constant;
* `conjTransposeCLM`, `HasDerivWithinAt.matrixConjTranspose` — the conjugate transpose is a
  continuous `ℝ`-linear map, so it commutes with derivatives;
* `IsPropagator G T U` — the solution property;
* ★ `exists_isPropagator` — **a propagator exists** for every continuous `G` and every `T > 0`
  (`exists_linearODE_solution_Icc` with the coefficient `ContinuousLinearMap.mul ℝ _ (G s)`);
* `IsPropagator.conjTranspose_mul_eq` — **the Heisenberg constancy**: `U† Y ≡ Y 0` for every
  solution `Y' = G Y`;
* ★ `IsPropagator.conjTranspose_mul_self`, `mul_conjTranspose`, `mem_unitaryGroup` — **the
  propagator of an anti-Hermitian generator is unitary**;
* `IsPropagator.eq_mul_init` — **uniqueness**: every solution of `Y' = G Y` is `U · Y 0`;
  `IsPropagator.unique` — two propagators agree;
* ★ `IsPropagator.mul_eq_of_hasDerivWithinAt_comm` — **the Heisenberg intertwining**: if
  `Q' = [G, Q]` then `U(s) Q(0) = Q(s) U(s)`.

## Honest scope

Finite dimensions, `L2Operator` norm scope, one-sided derivatives on `Icc 0 T`. Anti-Hermitian
means `(G s)ᴴ = −G s` on `[0, T]`; nothing is assumed off the interval.

References: T. Kato, "On the adiabatic theorem of quantum mechanics", J. Phys. Soc. Japan 5 (1950);
`Analysis/ODE/FlowDerivative.lean` (`exists_linearODE_solution_Icc`); `specs/BACKLOG.md` #160,
#161, ~~#88~~.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Matrix Topology
open Matrix Metric Set Filter

noncomputable section

/-! ### A derivative-free family is constant on `[0, T]` -/

section Constant

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A function with zero (one-sided) derivative within `[0, T]` at every point of `[0, T]` is
constant there. -/
theorem eq_of_hasDerivWithinAt_zero_Icc {f : ℝ → F} {T : ℝ}
    (hf : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt f 0 (Icc 0 T) s) :
    ∀ s ∈ Icc (0 : ℝ) T, f s = f 0 :=
  constant_of_has_deriv_right_zero (fun s hs => (hf s hs).continuousWithinAt) fun s hs =>
    (hf s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1))

end Constant

namespace Matrix

variable {N : ℕ}

/-! ### The conjugate transpose as a continuous `ℝ`-linear map -/

/-- The conjugate transpose, as a continuous `ℝ`-linear map. -/
def conjTransposeCLM : Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Aᴴ
      map_add' := fun A B => conjTranspose_add A B
      map_smul' := fun r A => by simp [conjTranspose_smul] }

@[simp] theorem conjTransposeCLM_apply (A : Matrix (Fin N) (Fin N) ℂ) :
    conjTransposeCLM A = Aᴴ := rfl

/-- The derivative of the conjugate transpose is the conjugate transpose of the derivative. -/
theorem HasDerivWithinAt.matrixConjTranspose {A : ℝ → Matrix (Fin N) (Fin N) ℂ}
    {A' : Matrix (Fin N) (Fin N) ℂ} {s : Set ℝ} {t : ℝ} (h : HasDerivWithinAt A A' s t) :
    HasDerivWithinAt (fun u => (A u)ᴴ) A'ᴴ s t :=
  conjTransposeCLM.hasFDerivAt.comp_hasDerivWithinAt t h

theorem HasDerivAt.matrixConjTranspose {A : ℝ → Matrix (Fin N) (Fin N) ℂ}
    {A' : Matrix (Fin N) (Fin N) ℂ} {t : ℝ} (h : HasDerivAt A A' t) :
    HasDerivAt (fun u => (A u)ᴴ) A'ᴴ t :=
  conjTransposeCLM.hasFDerivAt.comp_hasDerivAt t h

/-! ### Propagators -/

/-- `U` is a **propagator** of the generator `G` on `[0, T]`: `U 0 = 1` and `U' = G U` there. -/
structure IsPropagator (G : ℝ → Matrix (Fin N) (Fin N) ℂ) (T : ℝ)
    (U : ℝ → Matrix (Fin N) (Fin N) ℂ) : Prop where
  init : U 0 = 1
  hasDerivWithinAt : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt U (G s * U s) (Icc 0 T) s

/-- ★ **A propagator exists** for every generator continuous on `[0, T]`, `T > 0`. -/
theorem exists_isPropagator {G : ℝ → Matrix (Fin N) (Fin N) ℂ} {T : ℝ} (hT : 0 < T)
    (hG : ContinuousOn G (Icc 0 T)) : ∃ U : ℝ → Matrix (Fin N) (Fin N) ℂ, IsPropagator G T U := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hG
  obtain ⟨U, hU0, hUd⟩ := exists_linearODE_solution_Icc
    (fun s => ContinuousLinearMap.mul ℝ (Matrix (Fin N) (Fin N) ℂ) (G s)) hT
    (le_max_right C 0)
    (fun Y => by
      show ContinuousOn (fun t => G t * Y) (Icc 0 T)
      exact hG.mul continuousOn_const)
    (fun t ht => (ContinuousLinearMap.opNorm_mul_apply_le ℝ _ _).trans
      ((hC t ht).trans (le_max_left C 0)))
    (1 : Matrix (Fin N) (Fin N) ℂ)
  exact ⟨U, ⟨hU0, hUd⟩⟩

namespace IsPropagator

variable {G : ℝ → Matrix (Fin N) (Fin N) ℂ} {T : ℝ} {U V Y : ℝ → Matrix (Fin N) (Fin N) ℂ}

/-- **The Heisenberg constancy**: for an anti-Hermitian generator, `U† Y` is constant along every
solution `Y' = G Y`. -/
theorem conjTranspose_mul_eq (hU : IsPropagator G T U) (hG : ∀ s ∈ Icc (0 : ℝ) T, (G s)ᴴ = -G s)
    (hY : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt Y (G s * Y s) (Icc 0 T) s) :
    ∀ s ∈ Icc (0 : ℝ) T, (U s)ᴴ * Y s = Y 0 := by
  have h0 : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun u => (U u)ᴴ * Y u) 0 (Icc 0 T) s := by
    intro s hs
    refine ((hU.hasDerivWithinAt s hs).matrixConjTranspose.mul (hY s hs)).congr_deriv ?_
    rw [conjTranspose_mul, hG s hs, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc,
      neg_add_cancel]
  intro s hs
  rw [eq_of_hasDerivWithinAt_zero_Icc h0 s hs, hU.init, conjTranspose_one, Matrix.one_mul]

/-- ★ **The propagator of an anti-Hermitian generator is unitary**: `U† U = 1` on `[0, T]`. -/
theorem conjTranspose_mul_self (hU : IsPropagator G T U)
    (hG : ∀ s ∈ Icc (0 : ℝ) T, (G s)ᴴ = -G s) : ∀ s ∈ Icc (0 : ℝ) T, (U s)ᴴ * U s = 1 := by
  intro s hs
  rw [hU.conjTranspose_mul_eq hG hU.hasDerivWithinAt s hs, hU.init]

/-- `U U† = 1` on `[0, T]`. -/
theorem mul_conjTranspose (hU : IsPropagator G T U) (hG : ∀ s ∈ Icc (0 : ℝ) T, (G s)ᴴ = -G s) :
    ∀ s ∈ Icc (0 : ℝ) T, U s * (U s)ᴴ = 1 := fun s hs =>
  mul_eq_one_comm.1 (hU.conjTranspose_mul_self hG s hs)

theorem mem_unitaryGroup (hU : IsPropagator G T U) (hG : ∀ s ∈ Icc (0 : ℝ) T, (G s)ᴴ = -G s) :
    ∀ s ∈ Icc (0 : ℝ) T, U s ∈ Matrix.unitaryGroup (Fin N) ℂ := fun s hs =>
  Matrix.mem_unitaryGroup_iff.2 (hU.mul_conjTranspose hG s hs)

/-- **Uniqueness**: every solution of `Y' = G Y` on `[0, T]` is `U · Y 0`. -/
theorem eq_mul_init (hU : IsPropagator G T U) (hG : ∀ s ∈ Icc (0 : ℝ) T, (G s)ᴴ = -G s)
    (hY : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt Y (G s * Y s) (Icc 0 T) s) :
    ∀ s ∈ Icc (0 : ℝ) T, Y s = U s * Y 0 := by
  intro s hs
  rw [← hU.conjTranspose_mul_eq hG hY s hs, ← Matrix.mul_assoc, hU.mul_conjTranspose hG s hs,
    Matrix.one_mul]

/-- Two propagators of the same anti-Hermitian generator agree on `[0, T]`. -/
theorem unique (hU : IsPropagator G T U) (hV : IsPropagator G T V)
    (hG : ∀ s ∈ Icc (0 : ℝ) T, (G s)ᴴ = -G s) : ∀ s ∈ Icc (0 : ℝ) T, U s = V s := by
  intro s hs
  rw [hU.eq_mul_init hG hV.hasDerivWithinAt s hs, hV.init, Matrix.mul_one]

/-- ★ **The Heisenberg intertwining**: if `Q' = [G, Q]` on `[0, T]`, then `U(s) Q(0) = Q(s) U(s)`
there. -/
theorem mul_eq_of_hasDerivWithinAt_comm (hU : IsPropagator G T U)
    (hG : ∀ s ∈ Icc (0 : ℝ) T, (G s)ᴴ = -G s) {Q : ℝ → Matrix (Fin N) (Fin N) ℂ}
    (hQ : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt Q (G s * Q s - Q s * G s) (Icc 0 T) s) :
    ∀ s ∈ Icc (0 : ℝ) T, U s * Q 0 = Q s * U s := by
  have h0 : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun u => (U u)ᴴ * Q u * U u) 0 (Icc 0 T) s := by
    intro s hs
    have hd := hU.hasDerivWithinAt s hs
    refine ((hd.matrixConjTranspose.mul (hQ s hs)).mul hd).congr_deriv ?_
    simp only [Pi.mul_apply]
    rw [conjTranspose_mul, hG s hs]
    noncomm_ring
  intro s hs
  have h1 : (U s)ᴴ * Q s * U s = Q 0 := by
    rw [eq_of_hasDerivWithinAt_zero_Icc h0 s hs, hU.init, conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one]
  rw [← h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU.mul_conjTranspose hG s hs, Matrix.one_mul]

end IsPropagator

end Matrix

end

end
