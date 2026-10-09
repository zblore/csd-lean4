/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Fourier.WeylSmooth
public import CsdLean4.Mathlib.Analysis.Fourier.SchwartzTensor
public import CsdLean4.Mathlib.Analysis.Fourier.SchwartzPartialIntegral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The composition of two Weyl operators is a Weyl operator

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #126(iii)(iv), the close of #126.

★★★ `weylCLM_comp` — **`Op(K₁) ∘ Op(K₂) = Op(K₁ ⋆ K₂)`** on the jointly Schwartz kernel class, with
★★★ `weylCompKernel` the composite kernel and ★★ `weylCompKernel_apply` its formula
`∫ w, k₁(x, w)·k₂(w, z)`. #122 made `Op(K)` an operator on `𝓢(ℝ, ℂ)`; this is the first thing a
*calculus* needs, and the first statement in which the operators compose rather than the integrals.

## The reframing that makes it short

A Weyl operator **is** an integral operator with a Schwartz kernel: `x` and `y` enter `K` through the
linear isomorphism `(x, y) ↦ ((x+y)/2, x − y)`, so ★ `weylKernelCLM` (composition with it, which
`SchwartzMap.compCLMOfContinuousLinearEquiv` makes a continuous linear map) turns the symbol-kernel
into the integral kernel and back. In those coordinates composition is the classical kernel product,
and the content is that the product is again Schwartz:

* ★ `compAffineCLM` — composition with an **injective affine** map on the right, as a CLM on Schwartz
  space. `SchwartzMap.compCLMOfAntilipschitz` wants an antilipschitz constant; ★
  `antilipschitzWith_affine_of_leftInverse` supplies it from an explicit linear **left inverse**, which is what a
  concrete coordinate map always has;
* `compPair` — `((x, z), w) ↦ ((x, w), (w, z))`, injective, so #126(i)'s tensor product composed with
  it is Schwartz on `(ℝ × ℝ) × ℝ`, and #126(ii)'s `integralLastCLM` integrates `w` out;
* ★★ `weylCompKernel_apply` — the formula, and ★★★ `weylCLM_comp` the operator identity, by
  `integral_integral_swap` with the integrability supplied by the same tensor construction at a
  fixed first argument.

## Honest scope

⚠️ **The symbol-level statement is not here.** That the composite's *symbol* is the Moyal star
product `a ♯ b` needs the joint partial Fourier transform of #121(ii), and the `ℏ²` expansion of the
bracket is #64. This row is the operator identity with the kernel named, which is what is reachable
without them.

⚠️ **One kernel class**, as in #122: jointly Schwartz kernels. Composition for a wider symbol class
is a different theorem and is not proved here.

⚠️ **No algebra structure is claimed.** That `⋆` is associative, or that the Weyl operators of
Schwartz kernels form an algebra, follows from this identity and the injectivity of
`weylKernelCLM` — but neither is stated, and nothing needs them.

References: [`WeylSmooth.lean`](WeylSmooth.lean) (#122, `weylCLM`),
[`SchwartzTensor.lean`](SchwartzTensor.lean) (#126(i)),
[`SchwartzPartialIntegral.lean`](SchwartzPartialIntegral.lean) (#126(ii));
`specs/BACKLOG.md` #126, #122, #121, #64.
-/

@[expose] public section

open MeasureTheory SchwartzMap

noncomputable section

namespace WignerFunction

/-! ### Composition with an injective affine map -/

section Affine

variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedSpace ℂ F] [SMulCommClass ℝ ℂ F]

omit [FiniteDimensional ℝ D] in
/-- ★ **An injective affine map is antilipschitz**, with the constant read off an explicit linear
left inverse. This is what `SchwartzMap.compCLMOfAntilipschitz` asks for, in the form a concrete
coordinate map can supply. -/
theorem antilipschitzWith_affine_of_leftInverse (L : D →L[ℝ] E) (S : E →L[ℝ] D) (hS : ∀ x, S (L x) = x) (c : E) :
    AntilipschitzWith ‖S‖₊ fun x => c + L x := by
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  have h1 : dist x y = ‖S (L x - L y)‖ := by
    rw [map_sub, hS x, hS y, dist_eq_norm]
  have h2 : dist (c + L x) (c + L y) = ‖L x - L y‖ := by
    rw [dist_eq_norm]
    congr 1
    abel
  rw [h1, h2, coe_nnnorm]
  exact S.le_opNorm _

/-- ★ **Composition with an injective affine map, as a continuous linear map on Schwartz space.** -/
noncomputable def compAffineCLM (L : D →L[ℝ] E) (S : E →L[ℝ] D) (hS : ∀ x, S (L x) = x) (c : E) :
    𝓢(E, F) →L[ℂ] 𝓢(D, F) :=
  compCLMOfAntilipschitz ℂ (g := fun x => c + L x) (by fun_prop)
    (antilipschitzWith_affine_of_leftInverse L S hS c)

omit [FiniteDimensional ℝ D] in
@[simp]
theorem compAffineCLM_apply (L : D →L[ℝ] E) (S : E →L[ℝ] D) (hS : ∀ x, S (L x) = x) (c : E)
    (f : 𝓢(E, F)) (x : D) : compAffineCLM L S hS c f x = f (c + L x) := rfl

end Affine

/-! ### A Weyl operator is the integral operator of a Schwartz kernel -/

/-- The Weyl change of variables `(x, y) ↦ ((x+y)/2, x − y)`, as a linear equivalence. -/
def weylCoordsEquiv : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun p := ((p.1 + p.2) / 2, p.1 - p.2)
  invFun q := (q.1 + q.2 / 2, q.1 - q.2 / 2)
  map_add' p q := by
    obtain ⟨a, b⟩ := p
    obtain ⟨c, d⟩ := q
    simp only [Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> ring
  map_smul' r p := by
    obtain ⟨a, b⟩ := p
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq, RingHom.id_apply]
    constructor <;> ring
  left_inv p := by
    obtain ⟨a, b⟩ := p
    simp only [Prod.mk.injEq]
    constructor <;> ring
  right_inv q := by
    obtain ⟨a, b⟩ := q
    simp only [Prod.mk.injEq]
    constructor <;> ring

/-- The same, as a continuous linear equivalence. -/
noncomputable def weylCoords : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  weylCoordsEquiv.toContinuousLinearEquiv

@[simp]
theorem weylCoords_apply (p : ℝ × ℝ) : weylCoords p = ((p.1 + p.2) / 2, p.1 - p.2) := rfl

/-- ★ **The integral kernel of a Weyl operator**, as a continuous linear map of the symbol-kernel —
and an invertible one, so every Schwartz kernel is the Weyl kernel of exactly one symbol-kernel. -/
noncomputable def weylKernelCLM : 𝓢(ℝ × ℝ, ℂ) →L[ℂ] 𝓢(ℝ × ℝ, ℂ) :=
  compCLMOfContinuousLinearEquiv ℂ weylCoords

@[simp]
theorem weylKernelCLM_apply (K : 𝓢(ℝ × ℝ, ℂ)) (p : ℝ × ℝ) :
    weylKernelCLM K p = K ((p.1 + p.2) / 2, p.1 - p.2) := rfl

/-- ★ **A Weyl operator is the integral operator of its kernel.** -/
theorem weylOpK_eq_integral_kernel (K : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    weylOpK K ψ x = ∫ y, weylKernelCLM K (x, y) * ψ y := rfl

/-! ### The composite kernel -/

/-- `((x, z), w) ↦ ((x, w), (w, z))`: the map that turns a pair of kernels into the integrand of
their composition. It is injective, which is the only property needed. -/
def compPairMap : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ((ℝ × ℝ) × (ℝ × ℝ)) where
  toFun r := ((r.1.1, r.2), (r.2, r.1.2))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Its linear left inverse, which is what makes it antilipschitz. -/
def compPairInvMap : ((ℝ × ℝ) × (ℝ × ℝ)) →ₗ[ℝ] ((ℝ × ℝ) × ℝ) where
  toFun s := ((s.1.1, s.2.2), s.1.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `compPairMap` as a continuous linear map. -/
noncomputable def compPair : ((ℝ × ℝ) × ℝ) →L[ℝ] ((ℝ × ℝ) × (ℝ × ℝ)) :=
  compPairMap.toContinuousLinearMap

/-- `compPairInvMap` as a continuous linear map. -/
noncomputable def compPairInv : ((ℝ × ℝ) × (ℝ × ℝ)) →L[ℝ] ((ℝ × ℝ) × ℝ) :=
  compPairInvMap.toContinuousLinearMap

@[simp]
theorem compPair_apply (r : (ℝ × ℝ) × ℝ) : compPair r = ((r.1.1, r.2), (r.2, r.1.2)) := rfl

theorem compPairInv_compPair (r : (ℝ × ℝ) × ℝ) : compPairInv (compPair r) = r := rfl

/-- The integrand of the composition, as a Schwartz function of `((x, z), w)`: the tensor product of
the two kernels, composed with the injective `compPair`. -/
noncomputable def weylCompIntegrand (K₁ K₂ : 𝓢(ℝ × ℝ, ℂ)) : 𝓢((ℝ × ℝ) × ℝ, ℂ) :=
  compAffineCLM compPair compPairInv compPairInv_compPair 0
    (SchwartzMap.tensorProd (weylKernelCLM K₁) (weylKernelCLM K₂))

@[simp]
theorem weylCompIntegrand_apply (K₁ K₂ : 𝓢(ℝ × ℝ, ℂ)) (x z w : ℝ) :
    weylCompIntegrand K₁ K₂ ((x, z), w)
      = weylKernelCLM K₁ (x, w) * weylKernelCLM K₂ (w, z) := by
  simp [weylCompIntegrand]

/-- ★★★ **The composite kernel.** Jointly Schwartz, which is the whole content of #126: the
integrand above is Schwartz on `(ℝ × ℝ) × ℝ` by #126(i) and the injectivity of `compPair`, #126(ii)
integrates `w` out, and the Weyl change of variables carries the result back to a symbol-kernel. -/
noncomputable def weylCompKernel (K₁ K₂ : 𝓢(ℝ × ℝ, ℂ)) : 𝓢(ℝ × ℝ, ℂ) :=
  compCLMOfContinuousLinearEquiv ℂ weylCoords.symm
    (SchwartzMap.integralLastCLM (weylCompIntegrand K₁ K₂))

/-- ★★ **The composite kernel is the classical kernel product.** -/
theorem weylCompKernel_apply (K₁ K₂ : 𝓢(ℝ × ℝ, ℂ)) (x z : ℝ) :
    weylKernelCLM (weylCompKernel K₁ K₂) (x, z)
      = ∫ w, weylKernelCLM K₁ (x, w) * weylKernelCLM K₂ (w, z) := by
  have h : weylKernelCLM (weylCompKernel K₁ K₂) (x, z)
      = SchwartzMap.integralLastCLM (weylCompIntegrand K₁ K₂) (x, z) := by
    simp only [weylKernelCLM, weylCompKernel, compCLMOfContinuousLinearEquiv_apply,
      Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [h, SchwartzMap.integralLastCLM_apply]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun w => weylCompIntegrand_apply K₁ K₂ x z w)


/-! ### The operator identity -/

/-- `(w, z) ↦ ((0, w), (w, z))`: the integration-variable part of the composition's integrand, at a
fixed output point. -/
def slicePairMap : (ℝ × ℝ) →ₗ[ℝ] ((ℝ × ℝ) × (ℝ × ℝ)) where
  toFun r := (((0 : ℝ), r.1), (r.1, r.2))
  map_add' r s := by simp [Prod.ext_iff]
  map_smul' c r := by simp [Prod.ext_iff]

/-- Its linear left inverse. -/
def slicePairInvMap : ((ℝ × ℝ) × (ℝ × ℝ)) →ₗ[ℝ] (ℝ × ℝ) where
  toFun s := (s.1.2, s.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `slicePairMap` as a continuous linear map. -/
noncomputable def slicePair : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) × (ℝ × ℝ)) :=
  slicePairMap.toContinuousLinearMap

/-- `slicePairInvMap` as a continuous linear map. -/
noncomputable def slicePairInv : ((ℝ × ℝ) × (ℝ × ℝ)) →L[ℝ] (ℝ × ℝ) :=
  slicePairInvMap.toContinuousLinearMap

theorem slicePairInv_slicePair (r : ℝ × ℝ) : slicePairInv (slicePair r) = r := rfl

/-- The composition's integrand at a fixed output point, as a Schwartz function of the two
integration variables. This is what supplies Fubini's integrability hypothesis. -/
noncomputable def weylCompSlice (K₁ K₂ : 𝓢(ℝ × ℝ, ℂ)) (x : ℝ) : 𝓢(ℝ × ℝ, ℂ) :=
  compAffineCLM slicePair slicePairInv slicePairInv_slicePair ((x, (0 : ℝ)), ((0 : ℝ), (0 : ℝ)))
    (SchwartzMap.tensorProd (weylKernelCLM K₁) (weylKernelCLM K₂))

@[simp]
theorem weylCompSlice_apply (K₁ K₂ : 𝓢(ℝ × ℝ, ℂ)) (x w z : ℝ) :
    weylCompSlice K₁ K₂ x (w, z)
      = weylKernelCLM K₁ (x, w) * weylKernelCLM K₂ (w, z) := by
  simp [weylCompSlice, slicePair, slicePairMap]

/-- The composition's integrand is integrable on the two integration variables jointly, which is
what `integral_integral_swap` needs. -/
theorem integrable_weylCompIntegrand (K₁ K₂ : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Integrable (Function.uncurry fun w z : ℝ =>
      weylKernelCLM K₁ (x, w) * (weylKernelCLM K₂ (w, z) * ψ z)) (volume.prod volume) := by
  rw [← Measure.volume_eq_prod]
  obtain ⟨D, hD0, hD⟩ : ∃ D : ℝ, 0 ≤ D ∧ ∀ z, ‖ψ z‖ ≤ D :=
    ⟨SchwartzMap.seminorm ℂ 0 0 ψ, le_trans (norm_nonneg _) (norm_le_seminorm ℂ ψ 0),
      fun z => norm_le_seminorm ℂ ψ z⟩
  refine ((weylCompSlice K₁ K₂ x).integrable.norm.const_mul D).mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    exact ((weylKernelCLM K₁).continuous.comp (continuous_const.prodMk continuous_fst)).mul
      (((weylKernelCLM K₂).continuous.comp (continuous_fst.prodMk continuous_snd)).mul
        (ψ.continuous.comp continuous_snd))
  · filter_upwards with r
    obtain ⟨w, z⟩ := r
    rw [Function.uncurry_apply_pair, weylCompSlice_apply, norm_mul, norm_mul, norm_mul]
    calc ‖weylKernelCLM K₁ (x, w)‖ * (‖weylKernelCLM K₂ (w, z)‖ * ‖ψ z‖)
        ≤ ‖weylKernelCLM K₁ (x, w)‖ * (‖weylKernelCLM K₂ (w, z)‖ * D) := by
          gcongr
          exact hD z
      _ = D * (‖weylKernelCLM K₁ (x, w)‖ * ‖weylKernelCLM K₂ (w, z)‖) := by ring

/-- ★★★ **The composition of two Weyl operators is the Weyl operator of the composite kernel.**
In integral-kernel coordinates this is the classical kernel product, and the content is that the
product is again a *Schwartz* kernel, which is what `weylCompKernel` is. -/
theorem weylOpK_comp (K₁ K₂ : 𝓢(ℝ × ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    weylOpK K₁ (weylCLM K₂ ψ) x = weylOpK (weylCompKernel K₁ K₂) ψ x := by
  calc weylOpK K₁ (weylCLM K₂ ψ) x
      = ∫ w, ∫ z, weylKernelCLM K₁ (x, w) * (weylKernelCLM K₂ (w, z) * ψ z) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        show weylKernelCLM K₁ (x, w) * (weylCLM K₂ ψ) w
            = ∫ z, weylKernelCLM K₁ (x, w) * (weylKernelCLM K₂ (w, z) * ψ z)
        rw [integral_const_mul]
        rfl
    _ = ∫ z, ∫ w, weylKernelCLM K₁ (x, w) * (weylKernelCLM K₂ (w, z) * ψ z) :=
        integral_integral_swap (integrable_weylCompIntegrand K₁ K₂ ψ x)
    _ = ∫ z, weylKernelCLM (weylCompKernel K₁ K₂) (x, z) * ψ z := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        show (∫ w, weylKernelCLM K₁ (x, w) * (weylKernelCLM K₂ (w, z) * ψ z))
            = weylKernelCLM (weylCompKernel K₁ K₂) (x, z) * ψ z
        rw [weylCompKernel_apply, ← integral_mul_const]
        congr 1
        funext w
        ring
    _ = weylOpK (weylCompKernel K₁ K₂) ψ x := rfl

/-- ★★★ **`Op(K₁) ∘ Op(K₂) = Op(K₁ ⋆ K₂)`**, as continuous linear maps of Schwartz space — row
126's statement. -/
theorem weylCLM_comp (K₁ K₂ : 𝓢(ℝ × ℝ, ℂ)) :
    (weylCLM K₁).comp (weylCLM K₂) = weylCLM (weylCompKernel K₁ K₂) := by
  ext ψ x
  exact weylOpK_comp K₁ K₂ ψ x

end WignerFunction

end

end
