/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.RieszProjectorSmooth
public import CsdLean4.Mathlib.Analysis.Matrix.UnitaryPropagator

/-!
# The adiabatic intertwiner and Kato's intertwining identity

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #160 (out of ~~#88~~, the third brick of Kato's adiabatic theorem).

Along a gapped path `Γ` (`RieszProjectorSmooth.lean`) with eigenprojector `P s`, Kato's
**adiabatic generator** is the commutator `K s = [Ṗ s, P s] = Ṗ P − P Ṗ`, and the **adiabatic
intertwiner** `A` is the propagator of `K` (`UnitaryPropagator.lean`): `A' = K A`, `A 0 = 1`.
This file shows `K` is anti-Hermitian and derives, from the general propagator theory, that `A`
exists, is unitary, and carries the initial eigenspace exactly onto the instantaneous one.

* `GappedPath.K`, `continuous_K`, ★ `conjTranspose_K` — the generator is continuous and
  **anti-Hermitian**, because the derivative of a Hermitian family is Hermitian
  (`conjTranspose_deriv_proj`);
* `deriv_proj_sub_comm_K`, `hasDerivWithinAt_proj_comm` — **`Ṗ = [K, P]`**: by `deriv_proj_eq`
  and `proj_mul_deriv_mul_proj` (#159), `Ṗ − [K, P] = Ṗ − (ṖP + PṖ) + 2 PṖP = 0`;
* `GappedPath.IsIntertwiner Γ T A` — `A` is a propagator of `K` on `[0, T]`;
* ★ `exists_isIntertwiner` — **the intertwiner exists**;
* ★ `IsIntertwiner.conjTranspose_mul_self`, `mul_conjTranspose`, `mem_unitaryGroup` — **`A` is
  unitary**;
* ★★ `IsIntertwiner.mul_proj_zero` — **Kato's intertwining identity** `A(s) P(0) = P(s) A(s)`,
  the Heisenberg intertwining for `Q = P`; `IsIntertwiner.conjTranspose_mul_proj_mul` is the form
  `A† P A ≡ P(0)`;
* `IsIntertwiner.proj_mulVec` — a vector in the initial eigenspace is carried into the instantaneous
  one, exactly;
* `IsIntertwiner.unique` — any two intertwiners agree on `[0, T]`.

## Honest scope

* `A` is defined on `[0, T]` by one-sided derivatives at the ends, as the corpus linear-ODE lemma
  delivers it; `T > 0` is arbitrary.
* The path is `C¹` (`1 ≤ n`); nothing is rescaled yet — the propagators at speed `T` are #161.
* Everything is finite-dimensional and under the `L2Operator` norm scope.

References: T. Kato, "On the adiabatic theorem of quantum mechanics", J. Phys. Soc. Japan 5
(1950), §2 (the operator `A(s)` and `A P(0) = P A`); Kato, *Perturbation Theory for Linear
Operators*, II §4.2; S. Teufel, *Adiabatic Perturbation Theory in Quantum Dynamics*, §2.1;
`RieszProjectorSmooth.lean` (#159), `UnitaryPropagator.lean`; `specs/BACKLOG.md` #160, ~~#88~~.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Matrix ContDiff Topology
open Matrix Metric Set Complex Real Filter

noncomputable section

namespace Matrix.GappedPath

variable {N : ℕ} (Γ : GappedPath N)

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

/-- `Ṗ = [K, P]`, as a derivative statement on `[0, T]`. -/
theorem hasDerivWithinAt_proj_comm {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) (T : ℝ) :
    ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt Γ.proj (Γ.K s * Γ.proj s - Γ.proj s * Γ.K s) (Icc 0 T) s := by
  intro s _
  refine (Γ.hasDerivAt_proj hn hH s).hasDerivWithinAt.congr_deriv ?_
  have key := Γ.deriv_proj_sub_comm_K hn hH s
  rw [← sub_eq_zero, ← key]
  abel

/-! ### The intertwiner -/

/-- `A` is an **adiabatic intertwiner** of `Γ` on `[0, T]`: a propagator of `K`, i.e. `A 0 = 1`
and `A' = K A` there. -/
abbrev IsIntertwiner (T : ℝ) (A : ℝ → Matrix (Fin N) (Fin N) ℂ) : Prop := IsPropagator Γ.K T A

/-- ★ **The adiabatic intertwiner exists** on every `[0, T]`. -/
theorem exists_isIntertwiner {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) {T : ℝ} (hT : 0 < T) :
    ∃ A : ℝ → Matrix (Fin N) (Fin N) ℂ, Γ.IsIntertwiner T A :=
  exists_isPropagator hT (Γ.continuous_K hn hH).continuousOn

namespace IsIntertwiner

variable {Γ} {T : ℝ} {A B : ℝ → Matrix (Fin N) (Fin N) ℂ}

/-- ★ **The intertwiner is unitary**: `A† A = 1` on `[0, T]`. -/
theorem conjTranspose_mul_self (hA : Γ.IsIntertwiner T A) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) : ∀ s ∈ Icc (0 : ℝ) T, (A s)ᴴ * A s = 1 :=
  IsPropagator.conjTranspose_mul_self hA fun s _ => Γ.conjTranspose_K hn hH s

/-- `A A† = 1` on `[0, T]`. -/
theorem mul_conjTranspose (hA : Γ.IsIntertwiner T A) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) : ∀ s ∈ Icc (0 : ℝ) T, A s * (A s)ᴴ = 1 :=
  IsPropagator.mul_conjTranspose hA fun s _ => Γ.conjTranspose_K hn hH s

theorem mem_unitaryGroup (hA : Γ.IsIntertwiner T A) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) : ∀ s ∈ Icc (0 : ℝ) T, A s ∈ Matrix.unitaryGroup (Fin N) ℂ :=
  IsPropagator.mem_unitaryGroup hA fun s _ => Γ.conjTranspose_K hn hH s

/-- ★★ **Kato's intertwining identity**: `A(s) P(0) = P(s) A(s)` on `[0, T]`. The intertwiner
carries the initial eigenspace exactly onto the instantaneous one. -/
theorem mul_proj_zero (hA : Γ.IsIntertwiner T A) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) : ∀ s ∈ Icc (0 : ℝ) T, A s * Γ.proj 0 = Γ.proj s * A s :=
  IsPropagator.mul_eq_of_hasDerivWithinAt_comm hA (fun s _ => Γ.conjTranspose_K hn hH s)
    (Γ.hasDerivWithinAt_proj_comm hn hH T)

/-- ★★ `A† P A` is constant: `A(s)† P(s) A(s) = P(0)` on `[0, T]`. -/
theorem conjTranspose_mul_proj_mul (hA : Γ.IsIntertwiner T A) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) : ∀ s ∈ Icc (0 : ℝ) T, (A s)ᴴ * Γ.proj s * A s = Γ.proj 0 := by
  intro s hs
  rw [Matrix.mul_assoc, ← hA.mul_proj_zero hn hH s hs, ← Matrix.mul_assoc,
    hA.conjTranspose_mul_self hn hH s hs, Matrix.one_mul]

/-- A vector in the initial eigenspace is carried into the instantaneous eigenspace. -/
theorem proj_mulVec (hA : Γ.IsIntertwiner T A) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) {v : Fin N → ℂ}
    (hv : Γ.proj 0 *ᵥ v = v) : Γ.proj s *ᵥ (A s *ᵥ v) = A s *ᵥ v := by
  rw [mulVec_mulVec, ← hA.mul_proj_zero hn hH s hs, ← mulVec_mulVec, hv]

/-- Any two intertwiners agree on `[0, T]`. -/
theorem unique (hA : Γ.IsIntertwiner T A) (hB : Γ.IsIntertwiner T B) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) : ∀ s ∈ Icc (0 : ℝ) T, A s = B s :=
  IsPropagator.unique hA hB fun s _ => Γ.conjTranspose_K hn hH s

end IsIntertwiner

end Matrix.GappedPath

end

end
