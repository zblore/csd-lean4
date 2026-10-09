/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Fourier.WeylComposition
public import CsdLean4.Mathlib.Analysis.Fourier.SchwartzSlice
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The Weyl operators of Schwartz kernels form a non-unital algebra

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #127, out of #126.

~~#126~~ proved `Op(K₁) ∘ Op(K₂) = Op(K₁ ⋆ K₂)` and claimed nothing about the structure. This is the
structure, and the keystone is a theorem the row did not have:

* ★★★ `weylOpK_injective` — **the kernel is determined by the operator.** `Op` is *faithful* on the
  Schwartz kernel class, so a statement about operators can be pulled back to a statement about
  kernels;
* ★★★ `weylCompKernel_assoc` — `⋆` is **associative**, and ★★ `weylCompKernel_add_left`/`_right`,
  `_smul_left`/`_right` — it is **bilinear**. All four are corollaries of faithfulness and the
  corresponding fact about operators, which is where the work went;
* ★★★ `not_weylOpK_eq_id` and ★★★ `weylCLM_ne_one` — **there is no unit.** No Schwartz kernel
  represents the identity operator, so this is a genuinely non-unital algebra.

## The correction this row records

#127's own entry said associativity would follow from "associativity of operator composition *and*
the injectivity of `weylKernelCLM`". **That route does not close.** `weylKernelCLM` is the *change of
coordinates* `(x, y) ↦ ((x+y)/2, x − y)`, and its injectivity says nothing about whether two
different kernels can give the same operator — which is exactly what is needed to turn an identity
between operators into an identity between kernels. The ingredient is faithfulness of `Op`, and that
is a theorem rather than bookkeeping: ★★★ `weylOpK_injective` is proved by feeding the operator the
**conjugate of its own kernel slice** (`SchwartzMap.conjCLM` of #121(i)'s `slice`), which turns the
pairing into `∫ ‖k(x, y)‖² dy`; that vanishes only if the slice vanishes almost everywhere, and a
continuous function vanishing almost everywhere for Lebesgue measure vanishes.

## Honest scope

⚠️ **No `Mul` instance, deliberately.** Declaring `⋆` as the `Mul` of `𝓢(ℝ × ℝ, ℂ)` would commit the
type globally to the Weyl product, when the pointwise product is at least as natural a choice and a
`NonUnitalAlgebra` instance would then fix which one every downstream file means. The facts are
stated as theorems; a bundled `NonUnitalAlgHom` is one `letI` away for a consumer who wants it, and
nothing in the corpus does.

⚠️ **Nothing about the symbol product.** Faithfulness here is of `K ↦ Op(K)` on *kernels*; that the
*symbol* composes by the Moyal star product still needs #121(ii), and the `ℏ²` expansion is #64.

⚠️ **The non-unitality is stated for this class only.** That no *Schwartz* kernel gives the identity
is proved; a wider class (distributional kernels, where the identity's kernel is a delta) is a
different setting and is not formalised.

References: [`WeylComposition.lean`](WeylComposition.lean) (#126, `weylCompKernel`, `weylCLM_comp`),
[`SchwartzSlice.lean`](SchwartzSlice.lean) (#121(i), `slice`),
[`WeylSmooth.lean`](WeylSmooth.lean) (#122, `weylCLM`); `specs/BACKLOG.md` #127, #126, #122, #64.
-/

@[expose] public section

open MeasureTheory SchwartzMap

open scoped ComplexConjugate

noncomputable section

/-! ### Conjugation on Schwartz space

Needed to feed the operator the conjugate of its own kernel slice. Conjugation is `ℝ`-linear and not
`ℂ`-linear, which is why this is a map over `ℝ`; only its *values* matter below. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Complex conjugation on Schwartz space, as a continuous `ℝ`-linear map. -/
noncomputable def SchwartzMap.conjCLM : 𝓢(E, ℂ) →L[ℝ] 𝓢(E, ℂ) :=
  postcompCLM (𝕜 := ℝ) Complex.conjLIE.toLinearIsometry.toContinuousLinearMap

@[simp]
theorem SchwartzMap.conjCLM_apply (f : 𝓢(E, ℂ)) (x : E) :
    SchwartzMap.conjCLM f x = conj (f x) := by
  rw [SchwartzMap.conjCLM, SchwartzMap.postcompCLM_apply]
  rfl

namespace WignerFunction

/-! ### The Weyl operator is linear in its kernel -/

theorem weylOpK_add_kernel (K₁ K₂ : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    weylOpK (K₁ + K₂) ψ x = weylOpK K₁ ψ x + weylOpK K₂ ψ x := by
  rw [weylOpK, weylOpK, weylOpK,
    ← integral_add (integrable_weylOpK_integrand K₁ ψ x) (integrable_weylOpK_integrand K₂ ψ x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show (K₁ + K₂) ((x + y) / 2, x - y) * ψ y
      = K₁ ((x + y) / 2, x - y) * ψ y + K₂ ((x + y) / 2, x - y) * ψ y
  rw [add_apply, add_mul]

theorem weylOpK_sub_kernel (K₁ K₂ : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    weylOpK (K₁ - K₂) ψ x = weylOpK K₁ ψ x - weylOpK K₂ ψ x := by
  rw [weylOpK, weylOpK, weylOpK,
    ← integral_sub (integrable_weylOpK_integrand K₁ ψ x) (integrable_weylOpK_integrand K₂ ψ x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show (K₁ - K₂) ((x + y) / 2, x - y) * ψ y
      = K₁ ((x + y) / 2, x - y) * ψ y - K₂ ((x + y) / 2, x - y) * ψ y
  rw [sub_apply, sub_mul]

theorem weylOpK_smul_kernel (c : ℂ) (K : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    weylOpK (c • K) ψ x = c * weylOpK K ψ x := by
  rw [weylOpK, weylOpK, ← smul_eq_mul, ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show (c • K) ((x + y) / 2, x - y) * ψ y = c • (K ((x + y) / 2, x - y) * ψ y)
  rw [smul_apply, smul_eq_mul, smul_eq_mul]
  ring

/-! ### Faithfulness: the kernel is determined by the operator -/

/-- The change of coordinates, in the form the injectivity argument uses. -/
theorem weylKernelCLM_apply' (K : 𝓢(ℝ × ℝ, ℂ)) (p : ℝ × ℝ) :
    weylKernelCLM K p = K (weylCoords p) := rfl

/-- The change of coordinates is injective, because it is composition with a surjection. -/
theorem weylKernelCLM_injective : Function.Injective (weylKernelCLM) := by
  intro K₁ K₂ h
  refine SchwartzMap.ext fun z => ?_
  have h1 : weylKernelCLM K₁ (weylCoords.symm z) = weylKernelCLM K₂ (weylCoords.symm z) := by
    rw [h]
  rwa [weylKernelCLM_apply', weylKernelCLM_apply',
    ContinuousLinearEquiv.apply_symm_apply] at h1

/-- The squared modulus of a Schwartz function is integrable, which is what the pairing below
produces. -/
theorem integrable_norm_sq (f : 𝓢(ℝ, ℂ)) : Integrable (fun y : ℝ => ‖f y‖ ^ 2) volume := by
  obtain ⟨D, hD0, hD⟩ : ∃ D : ℝ, 0 ≤ D ∧ ∀ y, ‖f y‖ ≤ D :=
    ⟨SchwartzMap.seminorm ℂ 0 0 f, le_trans (norm_nonneg _) (norm_le_seminorm ℂ f 0),
      fun y => norm_le_seminorm ℂ f y⟩
  refine (f.integrable.norm.const_mul D).mono' (f.continuous.norm.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_two]
  exact mul_le_mul_of_nonneg_right (hD y) (norm_nonneg _)

/-- ★★★ **The kernel is determined by the operator.** A kernel whose operator annihilates every
state is zero — fed the conjugate of its own slice, the operator returns `∫ ‖k(x, y)‖² dy`, which
vanishes only if the slice does. This is what #127's entry was missing, and it is a theorem rather
than bookkeeping. -/
theorem eq_zero_of_weylOpK_eq_zero {K : 𝓢(ℝ × ℝ, ℂ)}
    (h : ∀ (ψ : 𝓢(ℝ, ℂ)) (x : ℝ), weylOpK K ψ x = 0) : K = 0 := by
  refine weylKernelCLM_injective (SchwartzMap.ext fun p => ?_)
  obtain ⟨x, y⟩ := p
  -- the slice at `x`, and the state that is its conjugate
  set s : 𝓢(ℝ, ℂ) := SchwartzMap.slice (weylKernelCLM K) x with hs
  have hsapply : ∀ w : ℝ, s w = K ((x + w) / 2, x - w) := by
    intro w
    rw [hs, SchwartzMap.slice_apply, weylKernelCLM_apply]
  -- the pairing is the integral of the squared modulus
  have hpair : (∫ w : ℝ, ((‖s w‖ ^ 2 : ℝ) : ℂ)) = 0 := by
    rw [← h (SchwartzMap.conjCLM s) x, weylOpK]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    show ((‖s w‖ ^ 2 : ℝ) : ℂ) = K ((x + w) / 2, x - w) * SchwartzMap.conjCLM s w
    rw [SchwartzMap.conjCLM_apply, ← hsapply w, RCLike.mul_conj]
    exact_mod_cast rfl
  -- hence the slice vanishes almost everywhere, hence everywhere
  have hreal : (∫ w : ℝ, ‖s w‖ ^ 2) = 0 := by
    rw [← Complex.ofReal_eq_zero, ← integral_complex_ofReal]
    exact hpair
  have hae : (fun w : ℝ => ‖s w‖ ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun w => by positivity) (integrable_norm_sq s)).1 hreal
  have hzero : (s : ℝ → ℂ) = fun _ => 0 := by
    refine MeasureTheory.Measure.eq_of_ae_eq (μ := (volume : Measure ℝ)) ?_ s.continuous
      continuous_const
    filter_upwards [hae] with w hw
    have : ‖s w‖ = 0 := by
      have h2 : ‖s w‖ ^ 2 = 0 := hw
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
    rwa [norm_eq_zero] at this
  rw [weylKernelCLM_apply, ← hsapply y, show (s : ℝ → ℂ) y = (fun _ : ℝ => (0 : ℂ)) y from by
    rw [hzero]]
  rfl

/-- ★★★ **`Op` is faithful on the Schwartz kernel class.** -/
theorem weylOpK_injective {K₁ K₂ : 𝓢(ℝ × ℝ, ℂ)}
    (h : ∀ (ψ : 𝓢(ℝ, ℂ)) (x : ℝ), weylOpK K₁ ψ x = weylOpK K₂ ψ x) : K₁ = K₂ := by
  have hzero : K₁ - K₂ = 0 := by
    refine eq_zero_of_weylOpK_eq_zero fun ψ x => ?_
    rw [weylOpK_sub_kernel, h ψ x, sub_self]
  rwa [sub_eq_zero] at hzero

/-- ★★ The same, for the packaged operators of #122. -/
theorem weylCLM_injective : Function.Injective (weylCLM) := by
  intro K₁ K₂ h
  refine weylOpK_injective fun ψ x => ?_
  have h1 : weylCLM K₁ ψ x = weylCLM K₂ ψ x := by rw [h]
  rwa [weylCLM_apply, weylCLM_apply] at h1

/-! ### The algebra laws -/

/-- ★★★ **`⋆` is associative.** Operator composition is associative and `Op` is faithful, so the
identity descends to the kernels. -/
theorem weylCompKernel_assoc (K₁ K₂ K₃ : 𝓢(ℝ × ℝ, ℂ)) :
    weylCompKernel (weylCompKernel K₁ K₂) K₃ = weylCompKernel K₁ (weylCompKernel K₂ K₃) := by
  refine weylCLM_injective ?_
  rw [← weylCLM_comp, ← weylCLM_comp, ← weylCLM_comp, ← weylCLM_comp,
    ContinuousLinearMap.comp_assoc]

/-- ★★ `⋆` is additive in its left argument. -/
theorem weylCompKernel_add_left (K₁ K₂ K₃ : 𝓢(ℝ × ℝ, ℂ)) :
    weylCompKernel (K₁ + K₂) K₃ = weylCompKernel K₁ K₃ + weylCompKernel K₂ K₃ := by
  refine weylOpK_injective fun ψ x => ?_
  rw [weylOpK_add_kernel, ← weylOpK_comp, ← weylOpK_comp, ← weylOpK_comp, weylOpK_add_kernel]

/-- ★★ `⋆` is additive in its right argument. The right slot is the *inner* operator, so this one
goes through the operators' action rather than through linearity in the kernel alone. -/
theorem weylCompKernel_add_right (K₁ K₂ K₃ : 𝓢(ℝ × ℝ, ℂ)) :
    weylCompKernel K₁ (K₂ + K₃) = weylCompKernel K₁ K₂ + weylCompKernel K₁ K₃ := by
  refine weylOpK_injective fun ψ x => ?_
  rw [weylOpK_add_kernel, ← weylOpK_comp, ← weylOpK_comp, ← weylOpK_comp]
  have hinner : (weylCLM (K₂ + K₃)) ψ = (weylCLM K₂) ψ + (weylCLM K₃) ψ := by
    refine SchwartzMap.ext fun z => ?_
    rw [add_apply, weylCLM_apply, weylCLM_apply, weylCLM_apply, weylOpK_add_kernel]
  rw [hinner]
  show weylOpK K₁ ((weylCLM K₂) ψ + (weylCLM K₃) ψ) x
      = weylOpK K₁ ((weylCLM K₂) ψ) x + weylOpK K₁ ((weylCLM K₃) ψ) x
  rw [weylOpK, weylOpK, weylOpK,
    ← integral_add (integrable_weylOpK_integrand K₁ ((weylCLM K₂) ψ) x)
      (integrable_weylOpK_integrand K₁ ((weylCLM K₃) ψ) x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show K₁ ((x + y) / 2, x - y) * ((weylCLM K₂) ψ + (weylCLM K₃) ψ) y
      = K₁ ((x + y) / 2, x - y) * ((weylCLM K₂) ψ) y
        + K₁ ((x + y) / 2, x - y) * ((weylCLM K₃) ψ) y
  rw [add_apply, mul_add]

/-- ★★ `⋆` is homogeneous in its left argument. -/
theorem weylCompKernel_smul_left (c : ℂ) (K₁ K₂ : 𝓢(ℝ × ℝ, ℂ)) :
    weylCompKernel (c • K₁) K₂ = c • weylCompKernel K₁ K₂ := by
  refine weylOpK_injective fun ψ x => ?_
  rw [weylOpK_smul_kernel, ← weylOpK_comp, ← weylOpK_comp, weylOpK_smul_kernel]

/-- ★★ `⋆` is homogeneous in its right argument. -/
theorem weylCompKernel_smul_right (c : ℂ) (K₁ K₂ : 𝓢(ℝ × ℝ, ℂ)) :
    weylCompKernel K₁ (c • K₂) = c • weylCompKernel K₁ K₂ := by
  refine weylOpK_injective fun ψ x => ?_
  rw [weylOpK_smul_kernel, ← weylOpK_comp, ← weylOpK_comp]
  have hinner : (weylCLM (c • K₂)) ψ = c • (weylCLM K₂) ψ := by
    refine SchwartzMap.ext fun z => ?_
    rw [smul_apply, weylCLM_apply, weylCLM_apply, weylOpK_smul_kernel, smul_eq_mul]
  rw [hinner]
  show weylOpK K₁ (c • (weylCLM K₂) ψ) x = c * weylOpK K₁ ((weylCLM K₂) ψ) x
  rw [weylOpK, weylOpK, ← smul_eq_mul, ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show K₁ ((x + y) / 2, x - y) * (c • (weylCLM K₂) ψ) y
      = c • (K₁ ((x + y) / 2, x - y) * ((weylCLM K₂) ψ) y)
  rw [smul_apply, smul_eq_mul, smul_eq_mul]
  ring


/-! ### There is no unit

The identity operator is not the Weyl operator of any Schwartz kernel. A unit would have to reproduce
every state's value at every point from an integral against a *bounded* kernel, and a shrinking bump
has value `1` at the centre while its integral against anything integrable tends to `0`. -/

/-- A bump at `0` of outer radius `2/(n+1)`, as a complex Schwartz function: value `1` at `0` for
every `n`, supported in a ball that shrinks to nothing. -/
noncomputable def shrinkBump (n : ℕ) : 𝓢(ℝ, ℂ) :=
  letI b : ContDiffBump (0 : ℝ) :=
    ⟨1 / (n + 1), 2 / (n + 1), by positivity, by
      rw [div_lt_div_iff_of_pos_right (by positivity)]
      norm_num⟩
  HasCompactSupport.toSchwartzMap
    (f := fun y : ℝ => ((b y : ℝ) : ℂ))
    (b.hasCompactSupport.comp_left (g := fun r : ℝ => ((r : ℝ) : ℂ)) Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp b.contDiff)

theorem shrinkBump_apply (n : ℕ) (y : ℝ) :
    shrinkBump n y = ((ContDiffBump.toFun
      (⟨1 / (n + 1), 2 / (n + 1), by positivity, by
        rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩ :
          ContDiffBump (0 : ℝ)) y : ℝ) : ℂ) := rfl

theorem shrinkBump_zero (n : ℕ) : shrinkBump n 0 = 1 := by
  rw [shrinkBump_apply]
  norm_cast
  refine ContDiffBump.one_of_mem_closedBall _ ?_
  simp only [Metric.mem_closedBall, dist_self]
  positivity

theorem norm_shrinkBump_le_one (n : ℕ) (y : ℝ) : ‖shrinkBump n y‖ ≤ 1 := by
  rw [shrinkBump_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ContDiffBump.nonneg' _ y)]
  exact ContDiffBump.le_one _

theorem shrinkBump_eq_zero_of_ne (n : ℕ) {y : ℝ} (hy : 2 / (n + 1) ≤ |y|) :
    shrinkBump n y = 0 := by
  rw [shrinkBump_apply]
  norm_cast
  refine ContDiffBump.zero_of_le_dist _ ?_
  rw [Real.dist_eq, sub_zero]
  push_cast
  exact hy

theorem tendsto_shrinkBump (y : ℝ) (hy : y ≠ 0) :
    Filter.Tendsto (fun n : ℕ => shrinkBump n y) Filter.atTop (nhds 0) := by
  have habs : 0 < |y| := abs_pos.2 hy
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / |y|)
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  refine (shrinkBump_eq_zero_of_ne n ?_).symm
  have h1 : 2 / |y| < (n : ℝ) + 1 := by
    have : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
    linarith
  rw [div_le_iff₀ (by positivity)]
  rw [div_lt_iff₀ habs] at h1
  linarith

/-- ★★★ **No Schwartz kernel represents the identity**, so the algebra of #126 is genuinely
non-unital. The witness is the shrinking bump: it keeps the value `1` at the origin while its
pairing with the kernel's slice tends to `0`. -/
theorem not_weylOpK_eq_id (K : 𝓢(ℝ × ℝ, ℂ)) :
    ¬ ∀ (ψ : 𝓢(ℝ, ℂ)) (x : ℝ), weylOpK K ψ x = ψ x := by
  intro h
  -- the slice at the origin
  obtain ⟨s, hs⟩ : ∃ s : 𝓢(ℝ, ℂ), ∀ y : ℝ, s y = K ((0 + y) / 2, 0 - y) :=
    ⟨SchwartzMap.slice (weylKernelCLM K) 0, fun y => by
      rw [SchwartzMap.slice_apply, weylKernelCLM_apply]⟩
  -- each pairing is `1`
  have hone : ∀ n : ℕ, (∫ y : ℝ, s y * shrinkBump n y) = 1 := by
    intro n
    have h1 : weylOpK K (shrinkBump n) 0 = shrinkBump n 0 := h (shrinkBump n) 0
    rw [shrinkBump_zero, weylOpK] at h1
    rw [← h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show s y * shrinkBump n y = K ((0 + y) / 2, 0 - y) * shrinkBump n y
    rw [hs y]
  -- but the pairings tend to `0`
  have hlim : Filter.Tendsto (fun n : ℕ => ∫ y : ℝ, s y * shrinkBump n y) Filter.atTop
      (nhds (∫ y : ℝ, (0 : ℂ))) := by
    refine tendsto_integral_of_dominated_convergence (fun y => ‖s y‖)
      (fun n => (s.continuous.mul (shrinkBump n).continuous).aestronglyMeasurable)
      s.integrable.norm (fun n => Filter.Eventually.of_forall fun y => ?_) ?_
    · rw [norm_mul]
      calc ‖s y‖ * ‖shrinkBump n y‖ ≤ ‖s y‖ * 1 :=
            mul_le_mul_of_nonneg_left (norm_shrinkBump_le_one n y) (norm_nonneg _)
        _ = ‖s y‖ := mul_one _
    · filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with y hy
      have hy' : y ≠ 0 := hy
      have := (tendsto_shrinkBump y hy').const_mul (s y)
      simp at this
      exact this
  rw [integral_zero] at hlim
  have : (1 : ℂ) = 0 := tendsto_nhds_unique (by simp [hone]) hlim
  exact one_ne_zero this

/-- ★★★ **The same, for the packaged operator**: no `K` has `weylCLM K = 1`. -/
theorem weylCLM_ne_one (K : 𝓢(ℝ × ℝ, ℂ)) :
    weylCLM K ≠ ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ) := by
  intro h
  refine not_weylOpK_eq_id K fun ψ x => ?_
  have h1 : weylCLM K ψ = ψ := by rw [h]; rfl
  rw [← weylCLM_apply, h1]

end WignerFunction

end

end
