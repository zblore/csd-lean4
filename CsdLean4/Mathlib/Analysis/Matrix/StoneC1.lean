/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.Tactic.Module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Finite-dimensional Stone's theorem (C¹ and continuity-only forms)

**Category:** 1-Mathlib (Finite-dimensional Stone's theorem).

A one-parameter unitary group of `N x N` complex matrices is `t ↦ exp (t • A)` for its
skew-Hermitian generator `A`. This is the load-bearing content of Stone's theorem in finite
dimensions: the group IS the exponential of its generator.

Mathlib has no Stone theorem (the `Stone*` names there are Stone-Weierstrass /
Stone-Cech / Stone separation). This file supplies the forward direction, first under a
smoothness hypothesis (`stone_c1`), then — **the full-continuity strengthening
(`stone_continuous`, 2026-07-23)** — for a merely *strongly continuous* group, deriving the
differentiability rather than assuming it (integral averaging + Fundamental Theorem of Calculus +
invertibility of `∫₀ˢ U` near `0`). Together they close the CSD dynamics-spine residue W5-S2.

## Main results

* `CSD.StoneC1.eq_exp_of_hasDeriv` : ODE-uniqueness core. If `U' t = U t * A` and
  `U 0 = 1`, then `U t = exp (t • A)`. This recovers the generator from the group.
* `CSD.StoneC1.exp_smul_unitary` : skew-Hermitian `A` gives each `exp (t • A)`
  unitary (`(exp (t • A))ᴴ * exp (t • A) = 1`).
* `CSD.StoneC1.stone_c1` : the packaged C^1 Stone theorem. From `star A = -A`,
  `∀ t, HasDerivAt U (U t * A) t`, `U 0 = 1`, conclude `∀ t, U t = exp (t • A)` and
  each `U t` is unitary.
* `CSD.StoneC1.stone_continuous` : the **continuity-only** Stone theorem. From continuity of `U`,
  `U 0 = 1`, the group law `U (s+t) = U s * U t`, and each `U t` unitary, conclude `∃ A`
  skew-Hermitian with `∀ t, U t = exp (t • A)` — no differentiability assumed.
* `CSD.StoneC1.trivial_group`, `CSD.StoneC1.skew_witness` : non-vacuity round-trips.

## Implementation notes

`NormedSpace.exp` is field-independent in current Mathlib (a single-argument
`exp (x : 𝔸)`), so it is written unqualified-by-field as `NormedSpace.exp (t • A)`.

The route is ODE uniqueness (`ODE_solution_unique_univ`, Gronwall) against the
reference solution `t ↦ exp (t • A)` whose derivative is `hasDerivAt_exp_smul_const`.
No integral averaging, no continuity-to-differentiability step.

The matrix norm is the `C^*`-algebra L2-operator norm (`open scoped
Matrix.Norms.L2Operator`), NOT the plain operator or Frobenius norm. This is
load-bearing: `hasDerivAt_exp_smul_const` needs `CompleteSpace (Matrix ...)`, and
under the plain operator / Frobenius scopes the finite-dimensional completeness
instance does not unify with the scoped `NormedAddCommGroup` (an instance diamond),
so synthesis fails. The `C^*`-algebra norm carries completeness by definition, so
`CompleteSpace` is automatic with no diamond, and `norm_mul_le` (submultiplicativity)
still holds.

The scalar-action side conditions (`0 • A = 0`, `t • (-A) = -(t • A)`) are discharged
with `module`, not the generic `zero_smul` / `smul_neg` rewrites: under the scoped
matrix-norm the `SMul ℝ (Matrix ...)` instance path defeats those rewrites, while
`module` normalises through the correct instance.

Declarations use dotted `CSD.StoneC1.*` names at top level rather than a
`namespace ... end` block (a namespace block can select a spurious `SMul` diamond).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Matrix
open MeasureTheory intervalIntegral Filter Topology

noncomputable section

variable {N : ℕ}

/-- ODE-uniqueness core. A `C^1` curve solving `Y' = Y * A` with `Y 0 = 1` is the
matrix exponential `t ↦ exp (t • A)`. Reuses `ODE_solution_unique_univ` (Gronwall)
with the `‖A‖`-Lipschitz linear field `Y ↦ Y * A` and `hasDerivAt_exp_smul_const`
for the reference solution. -/
theorem CSD.StoneC1.eq_exp_of_hasDeriv (A : Matrix (Fin N) (Fin N) ℂ)
    (U : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (hderiv : ∀ t, HasDerivAt U (U t * A) t) (hU0 : U 0 = 1) :
    ∀ t, U t = NormedSpace.exp (t • A) := by
  have key : U = fun t => NormedSpace.exp (t • A) := by
    apply ODE_solution_unique_univ (v := fun _ Y => Y * A) (s := fun _ => Set.univ)
        (K := ‖A‖₊) (t₀ := 0)
    · intro t
      apply LipschitzOnWith.of_dist_le_mul
      intro Y1 _ Y2 _
      rw [dist_eq_norm, dist_eq_norm, ← sub_mul]
      calc ‖(Y1 - Y2) * A‖ ≤ ‖Y1 - Y2‖ * ‖A‖ := norm_mul_le _ _
        _ = ‖A‖₊ * ‖Y1 - Y2‖ := by rw [coe_nnnorm]; ring
    · intro t; exact ⟨hderiv t, Set.mem_univ _⟩
    · intro t; exact ⟨hasDerivAt_exp_smul_const A t, Set.mem_univ _⟩
    · rw [hU0, show ((0 : ℝ) • A) = 0 from by module, NormedSpace.exp_zero]
  intro t; exact congrFun key t

/-- For a skew-Hermitian generator `A` (`star A = -A`), each `exp (t • A)` is unitary.
Reuses `Matrix.exp_conjTranspose` and `Matrix.exp_add_of_commute`. -/
theorem CSD.StoneC1.exp_smul_unitary (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : star A = -A) (t : ℝ) :
    (NormedSpace.exp (t • A))ᴴ * NormedSpace.exp (t • A) = 1 := by
  have hAH : Aᴴ = -A := by rw [← Matrix.star_eq_conjTranspose]; exact hA
  have hskew : (t • A)ᴴ = -(t • A) := by
    rw [Matrix.conjTranspose_smul, star_trivial, hAH]; module
  have hcomm : Commute (-(t • A)) (t • A) := (Commute.refl (t • A)).neg_left
  rw [← Matrix.exp_conjTranspose, hskew, ← Matrix.exp_add_of_commute _ _ hcomm,
    neg_add_cancel, NormedSpace.exp_zero]

/-- **C^1 finite-dimensional Stone theorem.** A differentiable one-parameter unitary
group with skew-Hermitian generator `A` is `t ↦ exp (t • A)`, and every `U t` is
unitary. The generator is recovered from the group. -/
theorem CSD.StoneC1.stone_c1 (A : Matrix (Fin N) (Fin N) ℂ)
    (U : ℝ → Matrix (Fin N) (Fin N) ℂ) (hA : star A = -A)
    (hderiv : ∀ t, HasDerivAt U (U t * A) t) (hU0 : U 0 = 1) :
    (∀ t, U t = NormedSpace.exp (t • A)) ∧
      (∀ t, (U t)ᴴ * U t = 1) := by
  have hexp := CSD.StoneC1.eq_exp_of_hasDeriv A U hderiv hU0
  refine ⟨hexp, fun t => ?_⟩
  rw [hexp t]
  exact CSD.StoneC1.exp_smul_unitary A hA t

/-- Non-vacuity: the trivial group. `A = 0` gives the constant unit curve, whose
generator is recovered as `0` and `U t = exp (t • 0) = 1`. -/
theorem CSD.StoneC1.trivial_group :
    ∀ t : ℝ, (fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) t
      = NormedSpace.exp (t • (0 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  apply CSD.StoneC1.eq_exp_of_hasDeriv
  · intro t; simpa using hasDerivAt_const t (1 : Matrix (Fin 2) (Fin 2) ℂ)
  · rfl

/-- Non-vacuity: a concrete skew-Hermitian generator `A = I • 1` on `Fin 2`. The
skew-Hermitian hypothesis holds, so `exp (t • A)` is a genuine unitary group. -/
theorem CSD.StoneC1.skew_witness :
    star (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ))
        = -(Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
      ∀ t : ℝ, (NormedSpace.exp (t • (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ))))ᴴ
          * NormedSpace.exp (t • (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ))) = 1 := by
  have hI : star Complex.I = -Complex.I := by simp
  have hskew : star (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      = -(Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [star_smul, star_one, hI]; module
  exact ⟨hskew, fun t => CSD.StoneC1.exp_smul_unitary _ hskew t⟩


/-- **Continuity-only finite-dimensional Stone theorem.** A *strongly continuous* one-parameter
unitary group `U : ℝ → Matrix N N ℂ` is `t ↦ exp (t • A)` for a skew-Hermitian generator `A`.
No differentiability is assumed — it is derived by the integral-averaging argument (FTC +
invertibility of `∫₀ˢ U` near `0`) and fed to the C¹ core `eq_exp_of_hasDeriv`. -/
theorem CSD.StoneC1.stone_continuous (U : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (hcont : Continuous U) (hU0 : U 0 = 1) (hgroup : ∀ s t, U (s + t) = U s * U t)
    (hunit : ∀ t, (U t)ᴴ * U t = 1) :
    ∃ A : Matrix (Fin N) (Fin N) ℂ, star A = -A ∧ ∀ t, U t = NormedSpace.exp (t • A) := by
  set G : ℝ → Matrix (Fin N) (Fin N) ℂ := fun u => ∫ x in (0:ℝ)..u, U x with hG
  have hGderiv : ∀ t, HasDerivAt G (U t) t := fun t =>
    integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  have hG0 : G 0 = 0 := by simp [hG]
  have hlim : Tendsto (fun s => s⁻¹ • G s) (𝓝[≠] 0) (𝓝 (1 : Matrix (Fin N) (Fin N) ℂ)) := by
    have hs := hasDerivAt_iff_tendsto_slope.mp (hGderiv 0)
    rw [hU0] at hs
    exact Filter.Tendsto.congr
      (fun s => by rw [slope_def_module, hG0, sub_zero, sub_zero]) hs
  obtain ⟨s₀, hs₀ne, hs₀unit⟩ : ∃ s₀ : ℝ, s₀ ≠ 0 ∧ IsUnit (G s₀) := by
    have hT : {s : ℝ | IsUnit (s⁻¹ • G s)} ∈ 𝓝[≠] (0:ℝ) :=
      hlim (Units.isOpen.mem_nhds isUnit_one)
    obtain ⟨s₀, hu, hne0⟩ := Filter.nonempty_of_mem (Filter.inter_mem hT self_mem_nhdsWithin)
    have hne0' : s₀ ≠ 0 := hne0
    obtain ⟨V, hV⟩ := hu
    have hGs : G s₀ = s₀ • (↑V : Matrix (Fin N) (Fin N) ℂ) := by
      rw [hV, smul_smul, mul_inv_cancel₀ hne0', one_smul]
    refine ⟨s₀, hne0', ⟨⟨G s₀, s₀⁻¹ • (↑V⁻¹ : Matrix (Fin N) (Fin N) ℂ), ?_, ?_⟩, rfl⟩⟩
    · rw [hGs, smul_mul_smul_comm, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        mul_inv_cancel₀ hne0', one_smul]
    · rw [hGs, smul_mul_smul_comm, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        inv_mul_cancel₀ hne0', one_smul]
  -- change of variables: `U t * G s₀ = G (t+s₀) - G t`
  have hCoV : ∀ t, U t * G s₀ = G (t + s₀) - G t := by
    intro t
    have hf : IntervalIntegrable U volume 0 s₀ := hcont.intervalIntegrable _ _
    have hpull : U t * G s₀ = ∫ x in (0:ℝ)..s₀, U t * U x :=
      calc U t * G s₀
          = (ContinuousLinearMap.mul ℝ _ (U t)) (∫ x in (0:ℝ)..s₀, U x) := rfl
        _ = ∫ x in (0:ℝ)..s₀, (ContinuousLinearMap.mul ℝ _ (U t)) (U x) :=
              ((ContinuousLinearMap.mul ℝ _ (U t)).intervalIntegral_comp_comm hf).symm
        _ = ∫ x in (0:ℝ)..s₀, U t * U x := rfl
    rw [hpull,
      show (∫ x in (0:ℝ)..s₀, U t * U x) = ∫ x in (0:ℝ)..s₀, U (t + x) from
        intervalIntegral.integral_congr (fun x _ => (hgroup t x).symm),
      intervalIntegral.integral_comp_add_left U t, add_zero, hG, eq_sub_iff_add_eq, add_comm,
      intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  set C : Matrix (Fin N) (Fin N) ℂ := ↑hs₀unit.unit⁻¹ with hC
  have hGC : G s₀ * C = 1 := by rw [hC]; exact hs₀unit.mul_val_inv
  have hUC : ∀ t, U t = (G (t + s₀) - G t) * C := fun t => by
    rw [← hCoV, mul_assoc, hGC, mul_one]
  set A : Matrix (Fin N) (Fin N) ℂ := (U s₀ - 1) * C with hA
  have hIderiv : ∀ t, HasDerivAt (fun t => G (t + s₀) - G t) (U (t + s₀) - U t) t := by
    intro t
    exact ((hGderiv (t + s₀)).comp_add_const t s₀).sub (hGderiv t)
  have hUderiv : ∀ t, HasDerivAt U (U t * A) t := by
    intro t
    have hd : HasDerivAt U ((U (t + s₀) - U t) * C) t :=
      ((hIderiv t).mul_const C).congr_of_eventuallyEq (Filter.Eventually.of_forall hUC)
    have hval : (U (t + s₀) - U t) * C = U t * A := by
      rw [hA, hgroup t s₀]; noncomm_ring
    rwa [hval] at hd
  have hexp : ∀ t, U t = NormedSpace.exp (t • A) :=
    CSD.StoneC1.eq_exp_of_hasDeriv A U hUderiv hU0
  refine ⟨A, ?_, hexp⟩
  -- skew-Hermitian: differentiate `star (U t) * U t = 1` at `0`
  have hstar : HasDerivAt (fun t => star (U t) * U t)
      (star (U 0 * A) * U 0 + star (U 0) * (U 0 * A)) 0 :=
    ((hUderiv 0).star).mul (hUderiv 0)
  have hconst : HasDerivAt (fun t => star (U t) * U t) 0 0 := by
    have he : (fun t => star (U t) * U t) = fun _ => (1 : Matrix (Fin N) (Fin N) ℂ) := by
      funext t; rw [Matrix.star_eq_conjTranspose]; exact hunit t
    rw [he]; exact hasDerivAt_const _ _
  have hAA : star (U 0 * A) * U 0 + star (U 0) * (U 0 * A) = 0 := hstar.unique hconst
  rw [hU0] at hAA
  simp only [one_mul, mul_one, star_one] at hAA
  exact eq_neg_of_add_eq_zero_left hAA

end

end
