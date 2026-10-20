/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.RieszProjectorSmooth
public import CsdLean4.Mathlib.Analysis.ODE.FlowDerivative
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Operator.Mul

/-!
# The adiabatic intertwiner and Kato's intertwining identity

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #160 (out of ~~#88~~, the third brick of Kato's adiabatic theorem).

Along a gapped path `Γ` (`RieszProjectorSmooth.lean`) with eigenprojector `P s`, Kato's
**adiabatic generator** is the commutator `K s = [Ṗ s, P s] = Ṗ P − P Ṗ`, and the **adiabatic
intertwiner** `A` is the solution of `A' = K A`, `A 0 = 1`. This file constructs `A` on `[0, T]`
and proves the two facts the adiabatic theorem rests on: `A` is unitary, and it carries the initial
eigenspace exactly onto the instantaneous one.

* `GappedPath.K`, `continuous_K`, ★ `conjTranspose_K` — the generator is continuous and
  **anti-Hermitian**, because the derivative of a Hermitian family is Hermitian
  (`conjTranspose_deriv_proj`, through the continuous `ℝ`-linear map `conjTransposeCLM`);
* `GappedPath.IsIntertwiner Γ T A` — `A 0 = 1` and `A' = K A` on `[0, T]` (one-sided derivatives
  at the ends);
* ★ `exists_isIntertwiner` — **the intertwiner exists**: the linear ODE `A' = K A` with a continuous
  bounded coefficient has a global solution on `[0, T]` (`exists_linearODE_solution_Icc`, with the
  coefficient `ContinuousLinearMap.mul ℝ _ (K s)`);
* ★ `IsIntertwiner.conjTranspose_mul_self`, `mul_conjTranspose`, `mem_unitaryGroup` — **`A` is
  unitary**: `(A†A)' = A†(K† + K)A = 0`, so `A†A ≡ 1`; finite dimension gives `AA† = 1`;
* ★★ `IsIntertwiner.conjTranspose_mul_proj_mul`, ★★ `IsIntertwiner.mul_proj_zero` — **Kato's
  intertwining identity** `A(s) P(0) = P(s) A(s)`: `(A† P A)' = A†(Ṗ − [K, P])A`, and
  `Ṗ − [K, P] = Ṗ − (ṖP + PṖ) + 2 PṖP = 0` by `deriv_proj_eq` and `proj_mul_deriv_mul_proj`
  (#159). So `A† P A ≡ P(0)`;
* `IsIntertwiner.proj_mulVec` — a vector in the initial eigenspace is carried into the instantaneous
  one, exactly;
* `IsIntertwiner.unique` — any two intertwiners agree on `[0, T]`: `(A†B)' = 0`, so `A†B ≡ 1`.

## Honest scope

* `A` is defined on `[0, T]` by one-sided derivatives at the ends (`HasDerivWithinAt` on `Icc 0 T`),
  as the corpus linear-ODE lemma delivers it; `T > 0` is arbitrary.
* The path is `C¹` (`1 ≤ n`); nothing is rescaled yet — the propagators at speed `T` are #161.
* Everything is finite-dimensional and under the `L2Operator` norm scope.

References: T. Kato, "On the adiabatic theorem of quantum mechanics", J. Phys. Soc. Japan 5
(1950), §2 (the operator `A(s)` and `A P(0) = P A`); Kato, *Perturbation Theory for Linear
Operators*, II §4.2; S. Teufel, *Adiabatic Perturbation Theory in Quantum Dynamics*, §2.1;
`RieszProjectorSmooth.lean` (#159), `Analysis/ODE/FlowDerivative.lean`
(`exists_linearODE_solution_Icc`, from the Darboux work #60); `specs/BACKLOG.md` #160, ~~#88~~.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Matrix ContDiff Topology
open Matrix Metric Set Complex Real Filter

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

namespace GappedPath

variable (Γ : GappedPath N)

/-! ### The adiabatic generator -/

/-- **Kato's adiabatic generator** `K s = [Ṗ s, P s]`. -/
def K (s : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  deriv Γ.proj s * Γ.proj s - Γ.proj s * deriv Γ.proj s

theorem continuous_K {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) : Continuous Γ.K := by
  have hP : Continuous Γ.proj := (Γ.contDiff_proj hH).continuous
  have hd : Continuous (deriv Γ.proj) := (Γ.contDiff_proj hH).continuous_deriv (by exact_mod_cast hn)
  exact (hd.mul hP).sub (hP.mul hd)

/-- The derivative of the (Hermitian) eigenprojector is Hermitian. -/
theorem conjTranspose_deriv_proj {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) (s : ℝ) :
    (deriv Γ.proj s)ᴴ = deriv Γ.proj s := by
  have h1 : HasDerivAt (fun u => (Γ.proj u)ᴴ) (deriv Γ.proj s)ᴴ s :=
    (Γ.hasDerivAt_proj hn hH s).matrixConjTranspose
  have h2 : (fun u => (Γ.proj u)ᴴ) = Γ.proj := funext fun u => Γ.proj_isHermitian u
  rw [h2] at h1
  exact h1.unique (Γ.hasDerivAt_proj hn hH s)

/-- ★ **The adiabatic generator is anti-Hermitian.** -/
theorem conjTranspose_K {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) (s : ℝ) :
    (Γ.K s)ᴴ = -Γ.K s := by
  unfold K
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Γ.conjTranspose_deriv_proj hn hH,
    Γ.proj_isHermitian s, neg_sub]

/-- `Ṗ − [K, P] = 0`: the identity behind the intertwining. -/
theorem deriv_proj_sub_comm_K {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) (s : ℝ) :
    -(Γ.K s * Γ.proj s) + deriv Γ.proj s + Γ.proj s * Γ.K s = 0 := by
  have hP := Γ.proj_mul_self s
  have hd := Γ.deriv_proj_eq hn hH s
  have hz := Γ.proj_mul_deriv_mul_proj hn hH s
  have e : -(Γ.K s * Γ.proj s) + deriv Γ.proj s + Γ.proj s * Γ.K s
      = (deriv Γ.proj s - (deriv Γ.proj s * Γ.proj s + Γ.proj s * deriv Γ.proj s))
        + (Γ.proj s * deriv Γ.proj s * Γ.proj s + Γ.proj s * deriv Γ.proj s * Γ.proj s)
        + (deriv Γ.proj s * Γ.proj s - deriv Γ.proj s * (Γ.proj s * Γ.proj s))
        + (Γ.proj s * deriv Γ.proj s - (Γ.proj s * Γ.proj s) * deriv Γ.proj s) := by
    unfold K
    noncomm_ring
  rw [e, hP]
  simp only [sub_self, hz, add_zero]
  rw [← hd, sub_self]

/-! ### The intertwiner -/

/-- `A` is an **adiabatic intertwiner** of `Γ` on `[0, T]`: `A 0 = 1` and `A' = K A` there. -/
structure IsIntertwiner (T : ℝ) (A : ℝ → Matrix (Fin N) (Fin N) ℂ) : Prop where
  init : A 0 = 1
  hasDerivWithinAt : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt A (Γ.K s * A s) (Icc 0 T) s

/-- ★ **The adiabatic intertwiner exists** on every `[0, T]`. -/
theorem exists_isIntertwiner {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) {T : ℝ} (hT : 0 < T) :
    ∃ A : ℝ → Matrix (Fin N) (Fin N) ℂ, Γ.IsIntertwiner T A := by
  have hK := Γ.continuous_K hn hH
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hK.continuousOn (s := Icc 0 T))
  obtain ⟨A, hA0, hAd⟩ := exists_linearODE_solution_Icc
    (fun s => ContinuousLinearMap.mul ℝ (Matrix (Fin N) (Fin N) ℂ) (Γ.K s)) hT
    (le_max_right C 0)
    (fun Y => by
      show ContinuousOn (fun t => Γ.K t * Y) (Icc 0 T)
      exact hK.continuousOn.mul continuousOn_const)
    (fun t ht => (ContinuousLinearMap.opNorm_mul_apply_le ℝ _ _).trans
      ((hC t ht).trans (le_max_left C 0)))
    (1 : Matrix (Fin N) (Fin N) ℂ)
  exact ⟨A, ⟨hA0, hAd⟩⟩

namespace IsIntertwiner

variable {Γ} {T : ℝ} {A B : ℝ → Matrix (Fin N) (Fin N) ℂ}

/-- ★ **The intertwiner is unitary**: `A† A = 1` on `[0, T]`. -/
theorem conjTranspose_mul_self (hA : Γ.IsIntertwiner T A) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) : ∀ s ∈ Icc (0 : ℝ) T, (A s)ᴴ * A s = 1 := by
  have h0 : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun u => (A u)ᴴ * A u) 0 (Icc 0 T) s := by
    intro s hs
    refine ((hA.hasDerivWithinAt s hs).matrixConjTranspose.mul (hA.hasDerivWithinAt s hs)).congr_deriv ?_
    rw [conjTranspose_mul, Γ.conjTranspose_K hn hH, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_assoc, neg_add_cancel]
  intro s hs
  rw [eq_of_hasDerivWithinAt_zero_Icc h0 s hs, hA.init, conjTranspose_one, Matrix.one_mul]

/-- `A A† = 1` on `[0, T]`. -/
theorem mul_conjTranspose (hA : Γ.IsIntertwiner T A) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) : ∀ s ∈ Icc (0 : ℝ) T, A s * (A s)ᴴ = 1 := fun s hs =>
  mul_eq_one_comm.1 (hA.conjTranspose_mul_self hn hH s hs)

theorem mem_unitaryGroup (hA : Γ.IsIntertwiner T A) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) : ∀ s ∈ Icc (0 : ℝ) T, A s ∈ Matrix.unitaryGroup (Fin N) ℂ :=
  fun s hs => Matrix.mem_unitaryGroup_iff.2 (hA.mul_conjTranspose hn hH s hs)

/-- ★★ `A† P A` is constant: `A(s)† P(s) A(s) = P(0)` on `[0, T]`. -/
theorem conjTranspose_mul_proj_mul (hA : Γ.IsIntertwiner T A) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) : ∀ s ∈ Icc (0 : ℝ) T, (A s)ᴴ * Γ.proj s * A s = Γ.proj 0 := by
  have h0 : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun u => (A u)ᴴ * Γ.proj u * A u) 0 (Icc 0 T) s := by
    intro s hs
    have hd := hA.hasDerivWithinAt s hs
    refine ((hd.matrixConjTranspose.mul (Γ.hasDerivAt_proj hn hH s).hasDerivWithinAt).mul
      hd).congr_deriv ?_
    have key := Γ.deriv_proj_sub_comm_K hn hH s
    have e : ((Γ.K s * A s)ᴴ * Γ.proj s + (A s)ᴴ * deriv Γ.proj s) * A s
        + (A s)ᴴ * Γ.proj s * (Γ.K s * A s)
        = (A s)ᴴ * (-(Γ.K s * Γ.proj s) + deriv Γ.proj s + Γ.proj s * Γ.K s) * A s := by
      rw [conjTranspose_mul, Γ.conjTranspose_K hn hH]
      noncomm_ring
    simp only [Pi.mul_apply]
    rw [e, key, Matrix.mul_zero, Matrix.zero_mul]
  intro s hs
  rw [eq_of_hasDerivWithinAt_zero_Icc h0 s hs, hA.init, conjTranspose_one, Matrix.one_mul,
    Matrix.mul_one]

/-- ★★ **Kato's intertwining identity**: `A(s) P(0) = P(s) A(s)` on `[0, T]`. The intertwiner
carries the initial eigenspace exactly onto the instantaneous one. -/
theorem mul_proj_zero (hA : Γ.IsIntertwiner T A) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) : ∀ s ∈ Icc (0 : ℝ) T, A s * Γ.proj 0 = Γ.proj s * A s := by
  intro s hs
  rw [← hA.conjTranspose_mul_proj_mul hn hH s hs, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    hA.mul_conjTranspose hn hH s hs, Matrix.one_mul]

/-- A vector in the initial eigenspace is carried into the instantaneous eigenspace. -/
theorem proj_mulVec (hA : Γ.IsIntertwiner T A) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) {v : Fin N → ℂ}
    (hv : Γ.proj 0 *ᵥ v = v) : Γ.proj s *ᵥ (A s *ᵥ v) = A s *ᵥ v := by
  rw [mulVec_mulVec, ← hA.mul_proj_zero hn hH s hs, ← mulVec_mulVec, hv]

/-- Any two intertwiners agree on `[0, T]`. -/
theorem unique (hA : Γ.IsIntertwiner T A) (hB : Γ.IsIntertwiner T B) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) : ∀ s ∈ Icc (0 : ℝ) T, A s = B s := by
  have h0 : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun u => (A u)ᴴ * B u) 0 (Icc 0 T) s := by
    intro s hs
    refine ((hA.hasDerivWithinAt s hs).matrixConjTranspose.mul (hB.hasDerivWithinAt s hs)).congr_deriv ?_
    rw [conjTranspose_mul, Γ.conjTranspose_K hn hH, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_assoc, neg_add_cancel]
  intro s hs
  have h1 : (A s)ᴴ * B s = 1 := by
    rw [eq_of_hasDerivWithinAt_zero_Icc h0 s hs, hA.init, hB.init, conjTranspose_one,
      Matrix.one_mul]
  calc A s = A s * ((A s)ᴴ * B s) := by rw [h1, Matrix.mul_one]
    _ = B s := by rw [← Matrix.mul_assoc, hA.mul_conjTranspose hn hH s hs, Matrix.one_mul]

end IsIntertwiner

end GappedPath

end Matrix

end

end
