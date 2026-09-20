/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Semigroup.BoundedPerturbation
public import CsdLean4.Mathlib.Analysis.Matrix.DysonSeries
public import CsdLean4.Mathlib.Analysis.Matrix.TrotterProduct
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The matrix propagator as an instance of the bounded-perturbation engine

**Category:** 1-Mathlib (CSD-free; staged for upstream).

The rule-of-two test of `Analysis/Semigroup/BoundedPerturbation.lean` (BACKLOG #40, FC-1′): the
engine, instantiated on `ℂᵐ` with the free group `S(t) = exp (t A)` of a skew-Hermitian matrix `A`
and the bounded perturbation `B`, must give back the matrix theorems of
`Analysis/Matrix/DysonSeries.lean` and `Analysis/Matrix/TrotterProduct.lean` as corollaries. It
does, and it gives them back **with the skewness of `B` dropped**: the matrix modules assumed
`Bᴴ = −B` to keep every exponential factor unitary, the engine only needs `B` bounded.

* **The dictionary.** `Matrix.toEuclideanCLM` is an isometry for the L2 operator norm
  (`cstar_norm_def` is `rfl`), so it is continuous, commutes with `exp`
  (`toEuclideanCLM_exp`) and with interval integrals (`toEuclideanCLM_mul_integral_apply`);
  `evalCLM ψ : M ↦ M ψ` is the evaluation as a continuous linear map on matrices.
* `expGroup A t = toEuclideanCLM (exp (t A))`, a group; for `Aᴴ = −A` a group of contractions,
  so `freeSemigroup A` (the identity for `t < 0`) is an `IsContractionSemigroup`
  (`isContractionSemigroup_freeSemigroup`, through `of_group`).
* `engine_dysonTerm_eq` — **the engine's Dyson terms are the matrix Dyson terms applied to `ψ`**,
  `Dₙ^{engine}(t) ψ = Dₙ(t) ψ`, by the group law `exp (t A) exp (−s A) = exp ((t − s) A)` under
  the integral.
* ★ `perturbed_eq_exp` — **the engine's perturbed semigroup is the matrix propagator**,
  `𝒮(t) = exp (t (A + B))`: the matrix Duhamel identity (`exp_add_sub_exp_eq`, the one analytic
  input) applied to `ψ` is the engine's Duhamel equation, and the engine's uniqueness
  (`eq_dysonSum_of_duhamel`) does the rest.
* ★★ `hasSum_dysonTerm_of_engine` — `Matrix.hasSum_dysonTerm` back from the engine, for **any**
  `B`: `∑ₙ Dₙ(t) = exp (t (A + B))` in the L2 operator norm; `hasSum_dysonTerm_apply` is the
  vector form.
* ★★ `tendsto_trotter_of_engine` — the matrix Trotter formula
  `(exp ((t/n) A) exp ((t/n) B))ⁿ → exp (t (A + B))` from the engine's, for any `B` and `0 ≤ t`;
  ★★ `trotter_skew_of_engine` is `TrotterProduct.trotter_skew` verbatim (`t = 1`), the engine's
  strong convergence upgraded to norm convergence by finite dimension
  (`tendsto_of_forall_tendsto_apply`).

## Honest scope

⚠️ **No rates.** `TrotterProduct.lean` proves the `O(1/n)` rate; the engine's Trotter formula is a
strong limit without a rate, so the rate is not recovered — only the limit. The matrix modules stay
as they are; this module shows they are the engine's instance, it does not replace them.

References: `Analysis/Semigroup/BoundedPerturbation.lean` (FC-1); `Analysis/Matrix/DysonSeries.lean`,
`Analysis/Matrix/TrotterProduct.lean` (row 36 (b)); `specs/feynman-continuum-scoping.md` §7 (the
rule-of-two test named there); `specs/BACKLOG.md` #40; `specs/future-work.md` FP-1.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Nat Topology
open NormedSpace Filter intervalIntegral

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Euclidean space `ℂᵐ`. -/
local notation "E" => EuclideanSpace ℂ m

/-- `Matrix.toEuclideanCLM` on `Matrix m m ℂ`. -/
local notation "𝓣" => toEuclideanCLM (𝕜 := ℂ) (n := m)

/-! ### The dictionary -/

theorem norm_toEuclideanCLM (M : Matrix m m ℂ) : ‖𝓣 M‖ = ‖M‖ :=
  (cstar_norm_def M).symm

theorem isometry_toEuclideanCLM : Isometry (toEuclideanCLM (𝕜 := ℂ) (n := m)) :=
  AddMonoidHomClass.isometry_of_norm _ norm_toEuclideanCLM

theorem continuous_toEuclideanCLM : Continuous (toEuclideanCLM (𝕜 := ℂ) (n := m)) :=
  isometry_toEuclideanCLM.continuous

theorem continuous_toEuclideanCLM_symm :
    Continuous (toEuclideanCLM (𝕜 := ℂ) (n := m)).symm :=
  (AddMonoidHomClass.isometry_of_norm _ fun T => by
    rw [← norm_toEuclideanCLM, StarAlgEquiv.apply_symm_apply]).continuous

/-- `toEuclideanCLM` commutes with the exponential. -/
theorem toEuclideanCLM_exp (M : Matrix m m ℂ) :
    𝓣 (exp M) = exp (𝓣 M) :=
  map_exp_of_mem_ball (𝕂 := ℂ) (toEuclideanCLM (𝕜 := ℂ) (n := m)) continuous_toEuclideanCLM M
    ((expSeries_radius_eq_top ℂ (Matrix m m ℂ)).symm ▸ edist_lt_top _ _)

theorem toEuclideanCLM_mul_apply (M N : Matrix m m ℂ) (ψ : E) :
    𝓣 (M * N) ψ = 𝓣 M (𝓣 N ψ) := by
  rw [map_mul, mul_apply_eq_comp]

/-- `toEuclideanCLM` as a continuous linear map. -/
noncomputable def toEuclideanCLMₗ : Matrix m m ℂ →L[ℂ] (E →L[ℂ] E) :=
  LinearMap.mkContinuous (toEuclideanCLM (𝕜 := ℂ) (n := m)).toAlgEquiv.toLinearMap 1 fun M => by
    rw [one_mul, AlgEquiv.toLinearMap_apply, StarAlgEquiv.coe_toAlgEquiv, norm_toEuclideanCLM]

theorem toEuclideanCLMₗ_apply (M : Matrix m m ℂ) : toEuclideanCLMₗ M = 𝓣 M := rfl

/-- Evaluation `M ↦ M ψ` as a continuous linear map on matrices. -/
noncomputable def evalCLM (ψ : E) : Matrix m m ℂ →L[ℂ] E :=
  (ContinuousLinearMap.apply ℂ E ψ).comp toEuclideanCLMₗ

theorem evalCLM_apply (ψ : E) (M : Matrix m m ℂ) : evalCLM ψ M = 𝓣 M ψ := rfl

omit [DecidableEq m] in
/-- The operator norm on `ℂᵐ` is bounded by the sum of the norms of the images of the standard
basis. -/
theorem opNorm_le_sum_norm_apply (T : E →L[ℂ] E) :
    ‖T‖ ≤ ∑ i, ‖T (EuclideanSpace.basisFun m ℂ i)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _ => norm_nonneg _)
    fun x => ?_
  calc ‖T x‖ = ‖∑ i, x i • T (EuclideanSpace.basisFun m ℂ i)‖ := by
        conv_lhs => rw [← (EuclideanSpace.basisFun m ℂ).sum_repr x]
        rw [map_sum]
        simp only [map_smul, EuclideanSpace.basisFun_repr]
    _ ≤ ∑ i, ‖x i • T (EuclideanSpace.basisFun m ℂ i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖x i‖ * ‖T (EuclideanSpace.basisFun m ℂ i)‖ := by simp only [norm_smul]
    _ ≤ ∑ i, ‖x‖ * ‖T (EuclideanSpace.basisFun m ℂ i)‖ := by
        gcongr with i
        exact PiLp.norm_apply_le x i
    _ = (∑ i, ‖T (EuclideanSpace.basisFun m ℂ i)‖) * ‖x‖ := by rw [← Finset.mul_sum, mul_comm]

/-- **Strong convergence is norm convergence in finite dimension**: a net of matrices converges in
the L2 operator norm as soon as it converges on every vector. -/
theorem tendsto_of_forall_tendsto_apply {ι : Type*} {l : Filter ι} {T : ι → Matrix m m ℂ}
    {L : Matrix m m ℂ}
    (h : ∀ ψ : E, Tendsto (fun i => 𝓣 (T i) ψ) l (𝓝 (𝓣 L ψ))) :
    Tendsto T l (𝓝 L) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun i => ∑ j, ‖𝓣 (T i) (EuclideanSpace.basisFun m ℂ j)
    - 𝓣 L (EuclideanSpace.basisFun m ℂ j)‖) (fun i => norm_nonneg _) (fun i => ?_) ?_
  · rw [← norm_toEuclideanCLM, map_sub]
    exact le_trans (opNorm_le_sum_norm_apply _) (le_of_eq rfl)
  · have := tendsto_finsetSum Finset.univ fun j _ =>
      tendsto_iff_norm_sub_tendsto_zero.mp (h (EuclideanSpace.basisFun m ℂ j))
    simpa using this

/-! ### The free group `exp (t A)` as a contraction semigroup -/

/-- The one-parameter group `t ↦ exp (t A)` of a matrix `A`, as operators on `ℂᵐ`. -/
noncomputable def expGroup (A : Matrix m m ℂ) (t : ℝ) : E →L[ℂ] E := 𝓣 (exp (t • A))

theorem expGroup_zero (A : Matrix m m ℂ) : expGroup A 0 = 1 := by
  rw [expGroup, zero_smul, exp_zero, map_one]

theorem expGroup_add (A : Matrix m m ℂ) (s t : ℝ) : expGroup A (s + t) = expGroup A s * expGroup A t := by
  rw [expGroup, expGroup, expGroup, add_smul,
    Matrix.exp_add_of_commute _ _ (((Commute.refl A).smul_left s).smul_right t), map_mul]

theorem continuous_expGroup_apply (A : Matrix m m ℂ) (ψ : E) :
    Continuous fun t => expGroup A t ψ := by
  show Continuous fun t => 𝓣 (exp (t • A)) ψ
  exact (continuous_toEuclideanCLM.comp (continuous_exp_smul A)).clm_apply continuous_const

/-- The free semigroup `exp (t A)` for `t ≥ 0`, the identity for `t < 0`. -/
noncomputable def freeSemigroup (A : Matrix m m ℂ) (t : ℝ) : E →L[ℂ] E :=
  if 0 ≤ t then expGroup A t else 1

theorem freeSemigroup_of_nonneg (A : Matrix m m ℂ) {t : ℝ} (ht : 0 ≤ t) :
    freeSemigroup A t = expGroup A t :=
  if_pos ht

/-! ### The Dyson terms and the propagator -/

/-- `exp (s A) · ∫₀ˢ F`, applied to `ψ`, is the integral of the operators applied to `ψ`. -/
theorem toEuclideanCLM_mul_integral_apply (A : Matrix m m ℂ) {F : ℝ → Matrix m m ℂ}
    (hF : Continuous F) (s : ℝ) (ψ : E) :
    𝓣 (exp (s • A) * ∫ r in (0 : ℝ)..s, F r) ψ
      = ∫ r in (0 : ℝ)..s, 𝓣 (exp (s • A)) (evalCLM ψ (F r)) := by
  have hint : IntervalIntegrable (fun r => evalCLM ψ (F r)) MeasureTheory.volume 0 s :=
    ((evalCLM ψ).continuous.comp hF).intervalIntegrable _ _
  rw [map_mul, mul_apply_eq_comp,
    show 𝓣 (∫ r in (0 : ℝ)..s, F r) ψ = evalCLM ψ (∫ r in (0 : ℝ)..s, F r) from rfl,
    ← (evalCLM ψ).intervalIntegral_comp_comm (hF.intervalIntegrable _ _),
    ← (𝓣 (exp (s • A))).intervalIntegral_comp_comm hint]

/-- The kernel identity behind both Duhamel forms: for `r ≤ s`,
`exp (s A) · (exp (−r A) · B · M) ψ = S(s − r) (B (M ψ))`. -/
theorem expGroup_mul_apply (A B M : Matrix m m ℂ) {r s : ℝ} (hrs : r ≤ s) (ψ : E) :
    𝓣 (exp (s • A)) (evalCLM ψ (exp ((-r) • A) * B * M))
      = freeSemigroup A (s - r) (𝓣 B (𝓣 M ψ)) := by
  rw [freeSemigroup_of_nonneg A (sub_nonneg.mpr hrs), expGroup, evalCLM_apply,
    ← toEuclideanCLM_mul_apply, ← toEuclideanCLM_mul_apply, ← toEuclideanCLM_mul_apply]
  have hx : exp (s • A) * exp ((-r) • A) = exp ((s - r) • A) := by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl A).smul_left s).smul_right (-r)),
      neg_smul, ← sub_eq_add_neg, ← sub_smul]
  congr 2
  simp only [← mul_assoc]
  rw [hx]

theorem continuous_dysonIntegrand (A B : Matrix m m ℂ) (n : ℕ) :
    Continuous fun s => exp ((-s) • A) * B * dysonTerm A B n s :=
  ((continuous_exp_neg_smul A).mul continuous_const).mul (continuous_dysonTerm A B n)

/-- **The engine's Dyson terms are the matrix Dyson terms applied to `ψ`**, for `t ≥ 0`. -/
theorem engine_dysonTerm_eq (A B : Matrix m m ℂ) (n : ℕ) :
    ∀ {t : ℝ}, 0 ≤ t → ∀ ψ : E,
      ContractionSemigroup.dysonTerm (freeSemigroup A) (𝓣 B) n t ψ
        = 𝓣 (dysonTerm A B n t) ψ := by
  induction n with
  | zero =>
    intro t ht ψ
    rw [ContractionSemigroup.dysonTerm_zero, dysonTerm_zero, freeSemigroup_of_nonneg A ht, expGroup]
  | succ n ih =>
    intro t ht ψ
    rw [ContractionSemigroup.dysonTerm_succ, dysonTerm_succ,
      toEuclideanCLM_mul_integral_apply A (continuous_dysonIntegrand A B n) t ψ]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht] at hs
    rw [ih hs.1 ψ, expGroup_mul_apply A B _ hs.2 ψ]

/-- The matrix Duhamel identity, applied to `ψ`, is the engine's Duhamel equation. -/
theorem exp_apply_eq_add_integral (A B : Matrix m m ℂ) {t : ℝ} (ht : 0 ≤ t) (ψ : E) :
    𝓣 (exp (t • (A + B))) ψ
      = freeSemigroup A t ψ + ∫ s in (0 : ℝ)..t,
          freeSemigroup A (t - s) (𝓣 B (𝓣 (exp (s • (A + B))) ψ)) := by
  have h := exp_add_sub_exp_eq A B t
  rw [sub_eq_iff_eq_add] at h
  have hcont : Continuous fun s : ℝ => exp ((-s) • A) * B * exp (s • (A + B)) :=
    ((continuous_exp_neg_smul A).mul continuous_const).mul (continuous_exp_smul (A + B))
  rw [h, map_add, _root_.add_apply, freeSemigroup_of_nonneg A ht, expGroup,
    toEuclideanCLM_mul_integral_apply A hcont t ψ, add_comm]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le ht] at hs
  exact expGroup_mul_apply A B _ hs.2 ψ

/-- The Trotter step of the engine is the matrix Trotter step `exp (h A) · exp (h B)`. -/
theorem trotterStep_eq (A B : Matrix m m ℂ) {h : ℝ} (hh : 0 ≤ h) :
    ContractionSemigroup.trotterStep (freeSemigroup A) (𝓣 B) h
      = 𝓣 (exp (h • A) * exp (h • B)) := by
  rw [ContractionSemigroup.trotterStep, freeSemigroup_of_nonneg A hh, expGroup, map_mul]
  congr 1
  rw [toEuclideanCLM_exp, RCLike.real_smul_eq_coe_smul (K := ℂ) h (𝓣 B),
    RCLike.real_smul_eq_coe_smul (K := ℂ) h B, map_smul]

/-! ### The contraction semigroup, and the propagator -/

variable [Nonempty m]

theorem norm_expGroup_le {A : Matrix m m ℂ} (hA : Aᴴ = -A) (t : ℝ) : ‖expGroup A t‖ ≤ 1 := by
  rw [expGroup, norm_toEuclideanCLM, l2_opNorm_exp_smul_skew A hA t]

/-- ★ The unitary group of a skew-Hermitian matrix is a strongly continuous contraction semigroup
in the sense of `BoundedPerturbation.lean`. -/
theorem isContractionSemigroup_freeSemigroup {A : Matrix m m ℂ} (hA : Aᴴ = -A) :
    IsContractionSemigroup (freeSemigroup A) :=
  IsContractionSemigroup.of_group _ (expGroup_zero A) (expGroup_add A) (norm_expGroup_le hA)
    (continuous_expGroup_apply A)

/-- ★ **The engine's perturbed semigroup is the matrix propagator**: for `Aᴴ = −A`, any `B` and
`0 ≤ t`, the Dyson series of `BoundedPerturbation.lean` around `exp (t A)` with interaction `B` is
`exp (t (A + B))`. The matrix Duhamel identity is the only analytic input; the engine's uniqueness
theorem does the rest. -/
theorem perturbed_eq_exp {A : Matrix m m ℂ} (hA : Aᴴ = -A) (B : Matrix m m ℂ) {t : ℝ}
    (ht : 0 ≤ t) :
    (isContractionSemigroup_freeSemigroup hA).perturbed (𝓣 B) t
      = 𝓣 (exp (t • (A + B))) :=
  ContinuousLinearMap.ext fun ψ => by
    rw [ContractionSemigroup.perturbed_apply]
    refine (ContractionSemigroup.eq_dysonSum_of_duhamel (𝓣 B)
      (isContractionSemigroup_freeSemigroup hA) (T := t)
      (X := fun s => 𝓣 (exp (s • (A + B))) ψ) ?_ ψ ?_ t ⟨ht, le_rfl⟩).symm
    · exact ((ContinuousLinearMap.apply ℂ E ψ).continuous.comp
        (continuous_toEuclideanCLM.comp (continuous_exp_smul (A + B)))).continuousOn
    · intro s hs
      exact exp_apply_eq_add_integral A B hs.1 ψ

/-! ### The matrix theorems, back from the engine -/

/-- ★★ **The matrix Dyson series, vector form, from the engine**: for `Aᴴ = −A`, any `B` and
`0 ≤ t`, `∑ₙ Dₙ(t) ψ = exp (t (A + B)) ψ`. -/
theorem hasSum_dysonTerm_apply {A : Matrix m m ℂ} (hA : Aᴴ = -A) (B : Matrix m m ℂ) {t : ℝ}
    (ht : 0 ≤ t) (ψ : E) :
    HasSum (fun n => 𝓣 (dysonTerm A B n t) ψ)
      (𝓣 (exp (t • (A + B))) ψ) := by
  have h := ContractionSemigroup.hasSum_dysonTerm (𝓣 B)
    (isContractionSemigroup_freeSemigroup hA) ht ψ
  rw [← ContractionSemigroup.perturbed_apply _ (isContractionSemigroup_freeSemigroup hA),
    perturbed_eq_exp hA B ht] at h
  have hfun : (fun n => 𝓣 (dysonTerm A B n t) ψ)
      = fun n => ContractionSemigroup.dysonTerm (freeSemigroup A) (𝓣 B) n t ψ :=
    funext fun n => (engine_dysonTerm_eq A B n ht ψ).symm
  rw [hfun]
  exact h

/-- ★★ **`Matrix.hasSum_dysonTerm`, back from the engine — and for any `B`**: for `Aᴴ = −A` and
`0 ≤ t`, `∑ₙ Dₙ(t) = exp (t (A + B))` in the L2 operator norm. The engine's term bound gives
summability in operator norm; the vector form identifies the sum. -/
theorem hasSum_dysonTerm_of_engine {A : Matrix m m ℂ} (hA : Aᴴ = -A) (B : Matrix m m ℂ) {t : ℝ}
    (ht : 0 ≤ t) : HasSum (fun n => dysonTerm A B n t) (exp (t • (A + B))) := by
  have hbound : ∀ n, ‖dysonTerm A B n t‖ ≤ (‖𝓣 B‖ * t) ^ n / n ! := by
    intro n
    rw [← norm_toEuclideanCLM]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ψ => ?_
    rw [← engine_dysonTerm_eq A B n ht ψ]
    exact ContractionSemigroup.norm_dysonTerm_le _ (isContractionSemigroup_freeSemigroup hA) n ht ψ
  have hsum : Summable fun n => dysonTerm A B n t :=
    Summable.of_norm_bounded (Real.summable_pow_div_factorial _) hbound
  have hX : ∑' n, dysonTerm A B n t = exp (t • (A + B)) := by
    refine (toEuclideanCLM (𝕜 := ℂ) (n := m)).injective (ContinuousLinearMap.ext fun ψ => ?_)
    have h1 := hsum.hasSum.map (evalCLM ψ) (evalCLM ψ).continuous
    exact h1.unique (hasSum_dysonTerm_apply hA B ht ψ)
  rw [← hX]
  exact hsum.hasSum

/-- ★★ **The matrix Trotter formula, vector form, from the engine**: for `Aᴴ = −A`, any `B` and
`0 ≤ t`, `(exp ((t/n) A) · exp ((t/n) B))ⁿ ψ → exp (t (A + B)) ψ`. -/
theorem tendsto_trotter_apply {A : Matrix m m ℂ} (hA : Aᴴ = -A) (B : Matrix m m ℂ)
    {t : ℝ} (ht : 0 ≤ t) (ψ : E) :
    Tendsto (fun n : ℕ => 𝓣 ((exp ((t / n) • A) * exp ((t / n) • B)) ^ n) ψ) atTop
      (𝓝 (𝓣 (exp (t • (A + B))) ψ)) := by
  have h := ContractionSemigroup.tendsto_trotterStep_pow_apply (𝓣 B)
    (isContractionSemigroup_freeSemigroup hA) ht ψ
  rw [← ContractionSemigroup.perturbed_apply _ (isContractionSemigroup_freeSemigroup hA),
    perturbed_eq_exp hA B ht] at h
  refine h.congr fun n => ?_
  rw [trotterStep_eq A B (div_nonneg ht n.cast_nonneg), map_pow]

/-- ★★ **The matrix Trotter formula, from the engine — and for any `B`**: for `Aᴴ = −A` and
`0 ≤ t`, `(exp ((t/n) A) · exp ((t/n) B))ⁿ → exp (t (A + B))` in the L2 operator norm. -/
theorem tendsto_trotter_of_engine {A : Matrix m m ℂ} (hA : Aᴴ = -A)
    (B : Matrix m m ℂ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => (exp ((t / n) • A) * exp ((t / n) • B)) ^ n) atTop
      (𝓝 (exp (t • (A + B)))) :=
  tendsto_of_forall_tendsto_apply fun ψ => tendsto_trotter_apply hA B ht ψ

/-- ★★ `TrotterProduct.trotter_skew` back from the engine, verbatim (`t = 1`), with the skewness of
`B` no longer needed: `(exp (A/n) · exp (B/n))ⁿ → exp (A + B)`. -/
theorem trotter_skew_of_engine {A : Matrix m m ℂ} (hA : Aᴴ = -A)
    (B : Matrix m m ℂ) :
    Tendsto (fun n : ℕ => (exp ((n : ℝ)⁻¹ • A) * exp ((n : ℝ)⁻¹ • B)) ^ n) atTop
      (𝓝 (exp (A + B))) := by
  have h := tendsto_trotter_of_engine hA B zero_le_one
  simp only [one_div, one_smul] at h
  exact h

end Matrix
