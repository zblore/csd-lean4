/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.AdiabaticIntertwiner
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The two propagators at speed `T`

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #161 (out of ~~#88~~, the fourth brick of Kato's adiabatic theorem).

In the rescaled time `s = t/T` along a gapped path `Γ` with Hamiltonian `H s`, eigenprojector
`P s` and adiabatic generator `K s = [Ṗ, P]`:

* the **physical propagator** `U_T` solves `U' = −iT·H(s) U`, `U 0 = 1` — the Schrödinger
  evolution traversed at speed `T`;
* the **adiabatic propagator** `U_A` solves `U' = (−iT·H(s) + K(s)) U`, `U 0 = 1`.

Both are propagators of anti-Hermitian generators (`UnitaryPropagator.lean`), so both exist on
`[0, 1]` and are unitary. The adiabatic one intertwines the eigenprojections exactly, and on the
initial eigenspace it is the intertwiner `A` of #160 times a dynamical phase.

* `GappedPath.physGen`, `adGen`, `conjTranspose_physGen`, `conjTranspose_adGen` — the two
  generators, anti-Hermitian; `IsPhysPropagator Γ T U`, `IsAdPropagator Γ T U`;
* ★ `exists_isPhysPropagator`, ★ `exists_isAdPropagator`, and the unitarity of both
  (`IsPhysPropagator.conjTranspose_mul_self`, …, `IsAdPropagator.mem_unitaryGroup`);
* ★★ `IsAdPropagator.mul_proj_zero` — **`U_A(s) P(0) = P(s) U_A(s)`**: `P` commutes with `H`, so
  `[adGen, P] = [K, P] = Ṗ` and the Heisenberg intertwining applies;
* `GappedPath.dynPhase T s = exp(−iT ∫₀ˢ lam)` — the **dynamical phase**;
* ★★ `IsAdPropagator.mul_proj_zero_eq` — **on the initial eigenspace, `U_A` is the dynamical phase
  times the intertwiner**: `U_A(s) P(0) = e^{−iT∫₀ˢ lam} · A(s) P(0)`. The rescaled
  `Z = e^{+iT∫lam} U_A P(0)` solves `Z' = K Z` with `Z 0 = P(0)`, because `H U_A P(0) = lam · U_A P(0)`
  by the intertwining; uniqueness for the propagator `A` of `K` finishes. **No multiplicity
  assumption**: the identity holds for a degenerate branch as well.

## Honest scope

* `T : ℝ` is any real (the speed); the physical content is `T → ∞`, which is #162.
* The interval is `[0, 1]`, one-sided at the ends; the path is `C¹` for the adiabatic propagator and
  merely continuous for the physical one.
* Finite dimensions, `L2Operator` norm scope.

References: T. Kato, J. Phys. Soc. Japan 5 (1950), §2; S. Teufel, *Adiabatic Perturbation Theory
in Quantum Dynamics*, §2.1 (`U^ε_a`, the adiabatic evolution); `AdiabaticIntertwiner.lean` (#160),
`UnitaryPropagator.lean`, `QuantumInfo/RotatingFrame.lean` (the constant-generator and rigidly rotated
propagators that preceded these); `specs/BACKLOG.md` #161, ~~#88~~.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Matrix ContDiff Topology
open Matrix Metric Set Complex Real Filter intervalIntegral

noncomputable section

namespace Matrix.GappedPath

variable {N : ℕ} (Γ : GappedPath N)

/-! ### The two generators -/

/-- The physical generator at speed `T`: `−iT·H(s)`. -/
def physGen (T : ℝ) (s : ℝ) : Matrix (Fin N) (Fin N) ℂ := (-I * (T : ℂ)) • Γ.H s

/-- The adiabatic generator at speed `T`: `−iT·H(s) + K(s)`. -/
def adGen (T : ℝ) (s : ℝ) : Matrix (Fin N) (Fin N) ℂ := Γ.physGen T s + Γ.K s

theorem continuous_physGen {n : ℕ∞} (hH : ContDiff ℝ n Γ.H) (T : ℝ) :
    Continuous (Γ.physGen T) := by
  unfold physGen
  exact hH.continuous.const_smul (-I * (T : ℂ))

theorem continuous_adGen {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) (T : ℝ) :
    Continuous (Γ.adGen T) :=
  (Γ.continuous_physGen hH T).add (Γ.continuous_K hn hH)

theorem conjTranspose_physGen (T s : ℝ) : (Γ.physGen T s)ᴴ = -Γ.physGen T s := by
  unfold physGen
  rw [conjTranspose_smul, (Γ.isHermitian s).eq, ← neg_smul]
  congr 1
  simp

theorem conjTranspose_adGen {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) (T s : ℝ) :
    (Γ.adGen T s)ᴴ = -Γ.adGen T s := by
  unfold adGen
  rw [conjTranspose_add, Γ.conjTranspose_physGen, Γ.conjTranspose_K hn hH, neg_add]

/-- `[adGen, P] = [K, P]`: the Hamiltonian commutes with its eigenprojector. -/
theorem adGen_mul_proj_sub (T s : ℝ) :
    Γ.adGen T s * Γ.proj s - Γ.proj s * Γ.adGen T s = Γ.K s * Γ.proj s - Γ.proj s * Γ.K s := by
  unfold adGen physGen
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Γ.H_mul_proj, Γ.proj_mul_H]
  abel

/-! ### The propagators -/

/-- `U` is the **physical propagator** at speed `T` on `[0, 1]`: `U 0 = 1`, `U' = −iT·H U`. -/
abbrev IsPhysPropagator (T : ℝ) (U : ℝ → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  IsPropagator (Γ.physGen T) 1 U

/-- `U` is the **adiabatic propagator** at speed `T` on `[0, 1]`: `U 0 = 1`,
`U' = (−iT·H + K) U`. -/
abbrev IsAdPropagator (T : ℝ) (U : ℝ → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  IsPropagator (Γ.adGen T) 1 U

/-- ★ **The physical propagator exists.** -/
theorem exists_isPhysPropagator {n : ℕ∞} (hH : ContDiff ℝ n Γ.H) (T : ℝ) :
    ∃ U : ℝ → Matrix (Fin N) (Fin N) ℂ, Γ.IsPhysPropagator T U :=
  exists_isPropagator one_pos (Γ.continuous_physGen hH T).continuousOn

/-- ★ **The adiabatic propagator exists.** -/
theorem exists_isAdPropagator {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) (T : ℝ) :
    ∃ U : ℝ → Matrix (Fin N) (Fin N) ℂ, Γ.IsAdPropagator T U :=
  exists_isPropagator one_pos (Γ.continuous_adGen hn hH T).continuousOn

namespace IsPhysPropagator

variable {Γ} {T : ℝ} {U : ℝ → Matrix (Fin N) (Fin N) ℂ}

/-- **The physical propagator is unitary.** -/
theorem conjTranspose_mul_self (hU : Γ.IsPhysPropagator T U) :
    ∀ s ∈ Icc (0 : ℝ) 1, (U s)ᴴ * U s = 1 :=
  IsPropagator.conjTranspose_mul_self hU fun s _ => Γ.conjTranspose_physGen T s

theorem mul_conjTranspose (hU : Γ.IsPhysPropagator T U) :
    ∀ s ∈ Icc (0 : ℝ) 1, U s * (U s)ᴴ = 1 :=
  IsPropagator.mul_conjTranspose hU fun s _ => Γ.conjTranspose_physGen T s

theorem mem_unitaryGroup (hU : Γ.IsPhysPropagator T U) :
    ∀ s ∈ Icc (0 : ℝ) 1, U s ∈ Matrix.unitaryGroup (Fin N) ℂ :=
  IsPropagator.mem_unitaryGroup hU fun s _ => Γ.conjTranspose_physGen T s

end IsPhysPropagator

/-! ### The dynamical phase -/

/-- The **dynamical phase** `exp(−iT ∫₀ˢ lam)`. -/
def dynPhase (T s : ℝ) : ℂ := Complex.exp (-I * (T : ℂ) * ((∫ t in (0 : ℝ)..s, Γ.lam t : ℝ) : ℂ))

/-- The inverse dynamical phase `exp(+iT ∫₀ˢ lam)`. -/
def invDynPhase (T s : ℝ) : ℂ := Complex.exp (I * (T : ℂ) * ((∫ t in (0 : ℝ)..s, Γ.lam t : ℝ) : ℂ))

theorem dynPhase_mul_invDynPhase (T s : ℝ) : Γ.dynPhase T s * Γ.invDynPhase T s = 1 := by
  unfold dynPhase invDynPhase
  rw [← Complex.exp_add]
  convert Complex.exp_zero using 2
  ring

theorem invDynPhase_zero (T : ℝ) : Γ.invDynPhase T 0 = 1 := by
  unfold invDynPhase
  simp

theorem hasDerivAt_invDynPhase (T s : ℝ) :
    HasDerivAt (Γ.invDynPhase T) (Γ.invDynPhase T s * (I * (T : ℂ) * (Γ.lam s : ℂ))) s := by
  have h1 : HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, Γ.lam t) (Γ.lam s) s :=
    (Γ.continuous_lam.integral_hasStrictDerivAt 0 s).hasDerivAt
  have h2 : HasDerivAt (fun u => I * (T : ℂ) * ((∫ t in (0 : ℝ)..u, Γ.lam t : ℝ) : ℂ))
      (I * (T : ℂ) * (Γ.lam s : ℂ)) s := h1.ofReal_comp.const_mul _
  exact h2.cexp

namespace IsAdPropagator

variable {Γ} {T : ℝ} {U A : ℝ → Matrix (Fin N) (Fin N) ℂ}

/-- **The adiabatic propagator is unitary.** -/
theorem conjTranspose_mul_self (hU : Γ.IsAdPropagator T U) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) : ∀ s ∈ Icc (0 : ℝ) 1, (U s)ᴴ * U s = 1 :=
  IsPropagator.conjTranspose_mul_self hU fun s _ => Γ.conjTranspose_adGen hn hH T s

theorem mul_conjTranspose (hU : Γ.IsAdPropagator T U) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) : ∀ s ∈ Icc (0 : ℝ) 1, U s * (U s)ᴴ = 1 :=
  IsPropagator.mul_conjTranspose hU fun s _ => Γ.conjTranspose_adGen hn hH T s

theorem mem_unitaryGroup (hU : Γ.IsAdPropagator T U) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) : ∀ s ∈ Icc (0 : ℝ) 1, U s ∈ Matrix.unitaryGroup (Fin N) ℂ :=
  IsPropagator.mem_unitaryGroup hU fun s _ => Γ.conjTranspose_adGen hn hH T s

/-- ★★ **The adiabatic propagator intertwines the eigenprojections exactly**:
`U_A(s) P(0) = P(s) U_A(s)` on `[0, 1]`. -/
theorem mul_proj_zero (hU : Γ.IsAdPropagator T U) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) : ∀ s ∈ Icc (0 : ℝ) 1, U s * Γ.proj 0 = Γ.proj s * U s :=
  IsPropagator.mul_eq_of_hasDerivWithinAt_comm hU (fun s _ => Γ.conjTranspose_adGen hn hH T s)
    fun s hs => by
      rw [Γ.adGen_mul_proj_sub]
      exact Γ.hasDerivWithinAt_proj_comm hn hH 1 s hs

/-- A vector in the initial eigenspace is carried into the instantaneous eigenspace. -/
theorem proj_mulVec (hU : Γ.IsAdPropagator T U) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {v : Fin N → ℂ}
    (hv : Γ.proj 0 *ᵥ v = v) : Γ.proj s *ᵥ (U s *ᵥ v) = U s *ᵥ v := by
  rw [mulVec_mulVec, ← hU.mul_proj_zero hn hH s hs, ← mulVec_mulVec, hv]

/-- `H(s) · U_A(s) P(0) = lam s · U_A(s) P(0)`: the propagated eigenspace is still the
`lam s`-eigenspace. -/
theorem H_mul_mul_proj_zero (hU : Γ.IsAdPropagator T U) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Γ.H s * (U s * Γ.proj 0) = (Γ.lam s : ℂ) • (U s * Γ.proj 0) := by
  rw [hU.mul_proj_zero hn hH s hs, ← Matrix.mul_assoc, Γ.H_mul_proj, Matrix.smul_mul]

/-- ★★ **On the initial eigenspace, the adiabatic propagator is the dynamical phase times the
intertwiner**: `U_A(s) P(0) = e^{−iT∫₀ˢ lam} · A(s) P(0)` on `[0, 1]`, for any multiplicity. -/
theorem mul_proj_zero_eq (hU : Γ.IsAdPropagator T U) (hA : Γ.IsIntertwiner 1 A) {n : ℕ∞}
    (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) :
    ∀ s ∈ Icc (0 : ℝ) 1, U s * Γ.proj 0 = Γ.dynPhase T s • (A s * Γ.proj 0) := by
  -- the rescaled family `Z = e^{+iT∫lam} U_A P(0)` solves `Z' = K Z`, `Z 0 = P(0)`
  set Z : ℝ → Matrix (Fin N) (Fin N) ℂ := fun s => Γ.invDynPhase T s • (U s * Γ.proj 0) with hZ
  have hZ0 : Z 0 = Γ.proj 0 := by
    simp only [hZ, Γ.invDynPhase_zero, hU.init, Matrix.one_mul, one_smul]
  have hZd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt Z (Γ.K s * Z s) (Icc 0 1) s := by
    intro s hs
    have hW : HasDerivWithinAt (fun u => U u * Γ.proj 0) (Γ.adGen T s * U s * Γ.proj 0)
        (Icc 0 1) s := (hU.hasDerivWithinAt s hs).mul_const _
    refine ((Γ.hasDerivAt_invDynPhase T s).hasDerivWithinAt.smul hW).congr_deriv ?_
    have hHW := hU.H_mul_mul_proj_zero hn hH hs
    have e1 : Γ.adGen T s * U s * Γ.proj 0
        = (-I * (T : ℂ) * (Γ.lam s : ℂ)) • (U s * Γ.proj 0) + Γ.K s * (U s * Γ.proj 0) := by
      rw [Matrix.mul_assoc, adGen, physGen, Matrix.add_mul, Matrix.smul_mul, hHW, smul_smul]
    have e2 : Γ.invDynPhase T s * (-I * (T : ℂ) * (Γ.lam s : ℂ))
        + Γ.invDynPhase T s * (I * (T : ℂ) * (Γ.lam s : ℂ)) = 0 := by ring
    rw [e1, smul_add, smul_smul, add_right_comm, ← add_smul, e2, zero_smul, zero_add]
    simp only [hZ, Matrix.mul_smul]
  intro s hs
  have h1 : Z s = A s * Γ.proj 0 := by
    rw [hA.eq_mul_init (fun s _ => Γ.conjTranspose_K hn hH s) hZd s hs, hZ0]
  calc U s * Γ.proj 0 = (Γ.dynPhase T s * Γ.invDynPhase T s) • (U s * Γ.proj 0) := by
        rw [Γ.dynPhase_mul_invDynPhase, one_smul]
    _ = Γ.dynPhase T s • Z s := by rw [← smul_smul]
    _ = Γ.dynPhase T s • (A s * Γ.proj 0) := by rw [h1]

end IsAdPropagator

end Matrix.GappedPath

end

end
