/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# A continuous projective one-parameter unitary group lifts

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

**Glossary:** https://glossary.constraintsurfacedynamics.com/bargmann/
Plain-language and CSD-role statements of the Bargmann invariant and of the theorem this
file makes unnecessary for the one-parameter case.

A family `U : ℝ → U(N)` that is a homomorphism only **up to phase**,

  `U (s + t) = c s t • (U s * U t)`,

is a projective representation of `ℝ`. This file shows that when `U` is continuous the
phase cocycle `c` is a **coboundary**: there is a continuous unit-modulus `b : ℝ → ℂ`
with

  `c s t * b (s + t) = b s * b t`   (`exists_continuous_phase_trivialisation`),

so `t ↦ b t • U t` is a genuine unitary group. Equivalently: a continuous projective
one-parameter unitary group in finite dimensions lifts to an honest one.

## Why this needs no Bargmann theorem

For a general group the obstruction is a class in `H²(G, U(1))` and killing it is
Bargmann's theorem. For `G = ℝ` there is no obstruction to kill — `Λ²(ℝ) = 0` — and the
proof is elementary:

* **Determinants reduce `N` phases to one.** `det (c • A) = c ^ N * det A`, so with
  `d t := det (U t)` the cocycle becomes `d (s + t) = c s t ^ N * d s * d t`, a statement
  about the *circle*, where `d` is continuous with `‖d t‖ = 1`.
* **`ℝ` is simply connected, so `d` lifts.** `Circle.exp` is a covering map
  (`Circle.isCoveringMap_exp`), and a continuous map from a simply-connected,
  locally-path-connected space lifts through it
  (`IsCoveringMap.existsUnique_continuousMap_lifts`), giving continuous `θ : ℝ → ℝ`
  with `d t = exp (θ t · i)`.
* **`b₀ t := exp (−θ t · i / N)` trivialises up to a root of unity.** By construction
  `b₀ t ^ N = (d t)⁻¹`, so the residual `μ s t := c s t * b₀ (s + t) / (b₀ s * b₀ t)`
  satisfies `μ ^ N = 1`.
* **A continuous map into the `N`-th roots of unity on a connected domain is constant.**
  `ℝ × ℝ` is preconnected and the roots of unity are finite, so `μ` is a constant `κ`,
  and rescaling `b := κ • b₀` makes it `1`.

## Honest scope

`ℝ` only, and finite dimensions only — both are load-bearing (`Λ²(ℝ) = 0` is what makes
the cocycle die, and `det` is what reduces to the circle). Nothing here is Bargmann's
theorem for a general topological group, which stays out of scope and out of Mathlib.
MATHLIB-ABSENT(Bargmann)

Reference: Bargmann, *Ann. Math.* **59** (1954) 1 (the general theorem this deliberately
avoids); Simms, *Lie Groups and Quantum Mechanics* §3 (the one-parameter case).
-/

@[expose] public section

open Set Matrix

namespace Matrix.ProjectiveLift

variable {N : ℕ}

/-! ### Two general engines -/

/-- A continuous complex-valued function with **finite range** on a preconnected space is
constant: the range is a preconnected subset of a finite set, hence a subsingleton. -/
theorem const_of_finite_range {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {f : X → ℂ} (hf : Continuous f) (hfin : (Set.range f).Finite) (x y : X) :
    f x = f y := by
  have : Finite (Set.range f) := hfin
  let g : X → Set.range f := fun z => ⟨f z, mem_range_self z⟩
  have hg : Continuous g := hf.subtype_mk _
  have hlc : IsLocallyConstant g := (IsLocallyConstant.iff_continuous g).mpr hg
  have h := hlc.apply_eq_of_isPreconnected (s := Set.univ) isPreconnected_univ
    (mem_univ x) (mem_univ y)
  exact congrArg Subtype.val h

/-- The `N`-th roots of unity in `ℂ` form a finite set (`N > 0`). -/
theorem nthRoots_finite (hN : 0 < N) : {z : ℂ | z ^ N = 1}.Finite := by
  refine Set.Finite.subset (Multiset.toFinset (Polynomial.nthRoots N (1:ℂ))).finite_toSet ?_
  intro z hz
  simp only [Multiset.mem_toFinset, Finset.mem_coe]
  exact (Polynomial.mem_nthRoots hN).mpr hz

/-- A complex number with `star z * z = 1` has unit norm. -/
theorem norm_eq_one_of_star_mul_self {z : ℂ} (h : star z * z = 1) : ‖z‖ = 1 := by
  have h1 : ‖star z * z‖ = 1 := by rw [h]; simp
  rw [norm_mul, norm_star] at h1
  nlinarith [norm_nonneg z]

/-- The determinant of a unitary matrix has unit norm. -/
theorem norm_det_eq_one {U : Matrix (Fin N) (Fin N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) : ‖U.det‖ = 1 :=
  norm_eq_one_of_star_mul_self (Matrix.det_of_mem_unitary hU).1

/-! ### The trivialisation -/

/-- A nonnegative real with `x ^ N = 1` (`N > 0`) is `1`. -/
theorem eq_one_of_pow_eq_one_of_nonneg (hN : 0 < N) {x : ℝ} (hx : 0 ≤ x) (h : x ^ N = 1) :
    x = 1 := by
  rcases (pow_eq_one_iff_of_ne_zero hN.ne').mp h with h1 | ⟨h1, -⟩
  · exact h1
  · exact absurd h1 (by intro hc; rw [hc] at hx; linarith)

/-- ★★ **A continuous projective one-parameter unitary group has a coboundary cocycle.**

If `U : ℝ → U(N)` is continuous and satisfies `U (s + t) = c s t • (U s * U t)`, then the
phase cocycle `c` is trivialised by a continuous unit-modulus `b`, so `t ↦ b t • U t` is a
genuine unitary group. See the module docstring for why `ℝ` needs no Bargmann theorem. -/
theorem exists_continuous_phase_trivialisation (hN : 0 < N)
    (U : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (hUmem : ∀ t, U t ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hUcont : Continuous U)
    (c : ℝ → ℝ → ℂ)
    (hc : ∀ s t, U (s + t) = c s t • (U s * U t)) :
    ∃ b : ℝ → ℂ, Continuous b ∧ (∀ t, ‖b t‖ = 1) ∧
      (∀ s t, c s t * b (s + t) = b s * b t) := by
  have hNne : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  -- `c` in closed form: multiply the cocycle by `star (U s * U t)` and take the trace.
  have hstar : ∀ s t, U s * U t * star (U s * U t) = 1 := fun s t =>
    ((Submonoid.mul_mem _ (hUmem s) (hUmem t)).2)
  have hcform : ∀ s t, c s t = (U (s + t) * star (U s * U t)).trace / N := by
    intro s t
    have h := congrArg (· * star (U s * U t)) (hc s t)
    simp only [smul_mul_assoc] at h
    rw [hstar s t] at h
    have htr : (U (s + t) * star (U s * U t)).trace = c s t * N := by
      rw [h, Matrix.trace_smul, Matrix.trace_one]
      simp
    rw [htr]
    field_simp
  have hccont : Continuous fun p : ℝ × ℝ => c p.1 p.2 := by
    have hrw : (fun p : ℝ × ℝ => c p.1 p.2)
        = fun p : ℝ × ℝ => (U (p.1 + p.2) * star (U p.1 * U p.2)).trace / N := by
      funext p; exact hcform p.1 p.2
    rw [hrw]; fun_prop
  -- the determinant, as a continuous map into the circle
  have hdnorm : ∀ t, ‖(U t).det‖ = 1 := fun t => norm_det_eq_one (hUmem t)
  have hdne : ∀ t, (U t).det ≠ 0 := fun t h => by
    have := hdnorm t; rw [h] at this; simp at this
  let dC : C(ℝ, Circle) :=
    ⟨fun t => ⟨(U t).det, by
        simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using hdnorm t⟩, by
      apply Continuous.subtype_mk; fun_prop⟩
  obtain ⟨e₀, he₀⟩ := Circle.exp_surjective (dC 0)
  obtain ⟨θ, ⟨-, hθlift⟩, -⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts dC 0 e₀ he₀
  have hdθ : ∀ t, (U t).det = Complex.exp ((θ t : ℂ) * Complex.I) := by
    intro t
    have h1 : Circle.exp (θ t) = dC t := congrFun hθlift t
    have h2 := congrArg Subtype.val h1
    rw [Circle.coe_exp] at h2
    exact h2.symm
  -- the candidate phase
  let b₀ : ℝ → ℂ := fun t => Complex.exp (-(θ t : ℂ) * Complex.I / N)
  have hb₀def : ∀ t, b₀ t = Complex.exp (-(θ t : ℂ) * Complex.I / N) := fun _ => rfl
  have hb₀norm : ∀ t, ‖b₀ t‖ = 1 := by
    intro t
    rw [hb₀def, Complex.norm_exp]
    have hre : (-(θ t : ℂ) * Complex.I / N).re = 0 := by
      simp [Complex.div_re, Complex.normSq_apply]
    rw [hre, Real.exp_zero]
  have hb₀ne : ∀ t, b₀ t ≠ 0 := fun t h => by
    have := hb₀norm t; rw [h] at this; simp at this
  have hb₀pow : ∀ t, b₀ t ^ N = Complex.exp (-(θ t : ℂ) * Complex.I) := by
    intro t
    rw [hb₀def, ← Complex.exp_nat_mul]
    congr 1
    field_simp
  -- determinants turn the cocycle into a circle identity
  have hdet : ∀ s t, (U (s + t)).det = c s t ^ N * ((U s).det * (U t).det) := by
    intro s t
    rw [hc s t, Matrix.det_smul, Matrix.det_mul]
    simp
  have hcNexp : ∀ s t, c s t ^ N
      = Complex.exp (((θ (s + t) : ℂ) - (θ s : ℂ) - (θ t : ℂ)) * Complex.I) := by
    intro s t
    have hd := hdet s t
    rw [hdθ (s + t), hdθ s, hdθ t] at hd
    have hq : c s t ^ N = Complex.exp ((θ (s + t) : ℂ) * Complex.I)
        / (Complex.exp ((θ s : ℂ) * Complex.I) * Complex.exp ((θ t : ℂ) * Complex.I)) := by
      rw [hd]
      field_simp
    rw [hq, ← Complex.exp_add, ← Complex.exp_sub]
    congr 1
    ring
  -- the residual phase is an N-th root of unity, hence constant
  have hnum : ∀ s t, c s t ^ N * b₀ (s + t) ^ N = b₀ s ^ N * b₀ t ^ N := by
    intro s t
    rw [hcNexp, hb₀pow, hb₀pow, hb₀pow, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have hμpow : ∀ s t, (c s t * b₀ (s + t) / (b₀ s * b₀ t)) ^ N = 1 := by
    intro s t
    rw [div_pow, mul_pow, mul_pow, hnum]
    exact div_self (mul_ne_zero (pow_ne_zero _ (hb₀ne s)) (pow_ne_zero _ (hb₀ne t)))
  have hμcont : Continuous fun p : ℝ × ℝ => c p.1 p.2 * b₀ (p.1 + p.2) / (b₀ p.1 * b₀ p.2) := by
    have hbc : Continuous b₀ := by
      have : Continuous fun t : ℝ => (θ t : ℝ) := θ.continuous
      fun_prop
    exact (hccont.mul (by fun_prop)).div (by fun_prop)
      (fun p => mul_ne_zero (hb₀ne p.1) (hb₀ne p.2))
  have hμrange :
      (Set.range fun p : ℝ × ℝ => c p.1 p.2 * b₀ (p.1 + p.2) / (b₀ p.1 * b₀ p.2)).Finite := by
    refine Set.Finite.subset (nthRoots_finite hN) ?_
    rintro z ⟨p, rfl⟩
    exact hμpow p.1 p.2
  set κ : ℂ := c 0 0 * b₀ (0 + 0) / (b₀ 0 * b₀ 0) with hκdef
  have hμconst : ∀ s t, c s t * b₀ (s + t) / (b₀ s * b₀ t) = κ := fun s t =>
    const_of_finite_range hμcont hμrange (s, t) (0, 0)
  have hκpow : κ ^ N = 1 := hμpow 0 0
  have hκnorm : ‖κ‖ = 1 :=
    eq_one_of_pow_eq_one_of_nonneg hN (norm_nonneg κ) (by rw [← norm_pow, hκpow, norm_one])
  refine ⟨fun t => κ * b₀ t, ?_, ?_, ?_⟩
  · have hbc : Continuous b₀ := by
      have : Continuous fun t : ℝ => (θ t : ℝ) := θ.continuous
      fun_prop
    fun_prop
  · intro t; rw [norm_mul, hκnorm, hb₀norm t, one_mul]
  · intro s t
    have h := hμconst s t
    have hden : b₀ s * b₀ t ≠ 0 := mul_ne_zero (hb₀ne s) (hb₀ne t)
    rw [div_eq_iff hden] at h
    calc c s t * (κ * b₀ (s + t)) = κ * (c s t * b₀ (s + t)) := by ring
      _ = κ * (κ * (b₀ s * b₀ t)) := by rw [h]
      _ = κ * b₀ s * (κ * b₀ t) := by ring

end Matrix.ProjectiveLift
