/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Semigroup.FreeHamiltonian

/-!
# The phase group's generator is its multiplication operator

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #64(iii), and a **correction to that row**: it said it waits on Stone's theorem. It does not.

★★★ `hasDerivAt_phaseGroup_apply` — **`d/dt e^{−itκ} f = −i·κ·e^{−itκ} f` in `L²`**, for every `f`
with `κ·f ∈ L²`. The group was already in hand explicitly and self-adjointness of the generator came
from #64(i)+(ii); what was missing is only that the two are *related*, and that is this file:

* ★★★ `hasDerivAt_phaseGroup_apply` — the derivative, on the natural domain;
* ★★★ `hasDerivAt_phaseGroup_freeSymbolOp` — **the Schrödinger equation for the free particle**,
  `i ∂_t ψ_t = H₀ ψ_t` with `H₀` the *self-adjoint operator* of #64(i), in the momentum
  representation, and ★★★ `hasDerivAt_fourierGroup_freePositionOp` the same in the position
  representation, where the generator is `freePositionOp` — transferred through #64(i)'s unitary
  conjugation rather than recomputed;
* ★ `phaseGroup_mem_mulDomain` — the group **preserves the domain**, which is what an interacting
  version would need next, and which is free here because a phase commutes with a multiplication.

## Why this is not Stone's theorem

Stone's theorem is an *existence* statement: every self-adjoint operator generates a unitary group.
Here the group is already explicit (`phaseGroup`, with its group law, unitarity and strong continuity
all proved in `SchrodingerGroup.lean`), so nothing has to be constructed — the content is the
identification of its derivative with a given operator. The corpus does have Stone's theorem in
**finite dimensions** (`Analysis/Matrix/StoneC1.lean`, both the `C¹` and the continuity-only forms);
the infinite-dimensional existence theorem is still absent and is **not needed by #64**.

## The proof in one line

The difference between the slope and the claimed derivative is multiplication by
`ω_h(x) = (e^{−ihκ(x)} − 1)/h + iκ(x)`, so its squared `L²` norm is the *scalar* integral
`∫ ‖f x‖²·‖ω_h(x)‖²`. That integrand tends to `0` pointwise (the scalar exponential's derivative) and
is dominated by `4‖κ(x)f(x)‖²` — which is integrable precisely because `f` is in the domain. So the
domain hypothesis is not a technical convenience: it *is* the dominating function.

## Honest scope

⚠️ **The interacting generator is not here.** `SchrodingerGroup.schrodinger` already exists as a
unitary propagator for a bounded potential (Dyson series, Duhamel, Trotter, in
`Semigroup/BoundedPerturbation.lean`), and #64(ii) made `H₀ + V` self-adjoint, but differentiating the
Duhamel integral — showing the *mild* solution is a *classical* one — needs more than the domain
invariance proved here. That is **#129**.

⚠️ **One derivative, not a flow statement.** Nothing here says the orbit is the unique solution of
the Cauchy problem; uniqueness for the free equation would follow from unitarity by the standard
energy argument and is not stated.

References: [`SchrodingerGroup.lean`](SchrodingerGroup.lean) (`phaseGroup`, `fourierGroup`,
`schrodinger`), [`FreeHamiltonian.lean`](FreeHamiltonian.lean) (#64(i)(ii), `freeSymbolOp`,
`freePositionOp`), [`InnerProductSpace/LinearPMapConj.lean`](../InnerProductSpace/LinearPMapConj.lean)
(the conjugation the position form rides on), [`Matrix/StoneC1.lean`](../Matrix/StoneC1.lean)
(finite-dimensional Stone); `specs/BACKLOG.md` #64, #129.
-/

@[expose] public section

open scoped ENNReal NNReal Topology ComplexConjugate LinearPMap

open MeasureTheory Filter

noncomputable section

namespace SchrodingerGroup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-! ### The squared norm as a scalar integral -/

theorem norm_sq_eq_integral (u : L2) : ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
  have hptw : ∀ x, (inner ℂ (u x) (u x) : ℂ) = ((‖u x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hA : (inner ℂ u u : ℂ) = ((∫ x, ‖u x‖ ^ 2 : ℝ) : ℂ) := by
    rw [L2.inner_def, integral_congr_ae (Eventually.of_forall hptw), integral_complex_ofReal]
  have hB : (inner ℂ u u : ℂ) = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hA] at hB
  exact_mod_cast hB.symm

/-! ### The scalar phase, differentiated -/

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- The phase moves by at most `|t|·|κ|`, globally — the estimate that makes the dominating
function the domain condition. -/
theorem norm_phaseFun_sub_one_le (κ : E → ℝ) (t : ℝ) (x : E) :
    ‖phaseFun κ t x - 1‖ ≤ |t| * |κ x| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(t * κ x))
  rw [phaseFun, show ((-(t * κ x) : ℝ) : ℂ) * Complex.I
      = Complex.I * ((-(t * κ x) : ℝ) : ℂ) from by ring]
  refine le_trans h ?_
  rw [Real.norm_eq_abs, abs_neg, abs_mul]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- The scalar derivative at the identity: `d/dh e^{−ihκ(x)} = −iκ(x)`. -/
theorem hasDerivAt_phaseFun (κ : E → ℝ) (x : E) (t : ℝ) :
    HasDerivAt (fun h : ℝ => phaseFun κ h x) (-Complex.I * (κ x : ℂ) * phaseFun κ t x) t := by
  have hpt : ∀ h : ℝ, phaseFun κ h x
      = Complex.exp ((-Complex.I * (κ x : ℂ)) * (h : ℂ)) := by
    intro h
    rw [phaseFun]
    congr 1
    push_cast
    ring
  have hcast : HasDerivAt (fun h : ℝ => ((h : ℝ) : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have hmul := hcast.const_mul (-Complex.I * (κ x : ℂ))
  rw [mul_one] at hmul
  have hexp := hmul.cexp
  rw [funext hpt]
  refine hexp.congr_deriv ?_
  rw [← hpt t]
  ring

/-! ### The group's derivative -/

variable {κ : E → ℝ} (hκ : Measurable κ)

/-- The defect between the slope and the claimed derivative, as a scalar multiplier. -/
noncomputable def phaseDefect (κ : E → ℝ) (h : ℝ) (x : E) : ℂ :=
  h⁻¹ • (phaseFun κ h x - 1) + Complex.I * (κ x : ℂ)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
theorem norm_phaseDefect_le {h : ℝ} (hh : h ≠ 0) (x : E) :
    ‖phaseDefect κ h x‖ ≤ 2 * |κ x| := by
  have h1 : ‖h⁻¹ • (phaseFun κ h x - 1)‖ ≤ |κ x| := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv]
    rw [← div_eq_inv_mul, div_le_iff₀ (abs_pos.2 hh)]
    rw [mul_comm]
    exact norm_phaseFun_sub_one_le κ h x
  have h2 : ‖Complex.I * (κ x : ℂ)‖ = |κ x| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖phaseDefect κ h x‖ ≤ ‖h⁻¹ • (phaseFun κ h x - 1)‖ + ‖Complex.I * (κ x : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ |κ x| + |κ x| := by rw [h2]; linarith [h1]
    _ = 2 * |κ x| := by ring

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
include hκ in
theorem measurable_phaseDefect (h : ℝ) : Measurable (phaseDefect κ h) := by
  unfold phaseDefect
  refine Measurable.add ?_ (measurable_const.mul (Complex.measurable_ofReal.comp hκ))
  exact (((measurable_phaseFun hκ h).sub measurable_const).const_smul (h⁻¹ : ℝ))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
theorem tendsto_phaseDefect (κ : E → ℝ) (x : E) :
    Tendsto (fun h : ℝ => phaseDefect κ h x) (𝓝[≠] 0) (𝓝 0) := by
  have hslope := (hasDerivAt_phaseFun κ x 0).tendsto_slope
  have heq : ∀ h : ℝ, h ≠ 0 → slope (fun h : ℝ => phaseFun κ h x) 0 h
      = h⁻¹ • (phaseFun κ h x - 1) := by
    intro h _
    rw [slope_def_module, phaseFun_zero, sub_zero]
  have hslope' : Tendsto (fun h : ℝ => h⁻¹ • (phaseFun κ h x - 1)) (𝓝[≠] 0)
      (𝓝 (-Complex.I * (κ x : ℂ) * phaseFun κ 0 x)) := by
    refine hslope.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact heq h hh
  rw [phaseFun_zero, mul_one] at hslope'
  have hsum := hslope'.add (tendsto_const_nhds (x := Complex.I * (κ x : ℂ)))
  rw [show -Complex.I * (κ x : ℂ) + Complex.I * (κ x : ℂ) = 0 from by ring] at hsum
  exact hsum


/-! ### The group's derivative on the domain

`f` is in the domain when `κ·f` is again in `L²`, and that product is taken as data: the hypothesis
`hg` says `g` *is* the product. The dominating function of the convergence below is `4‖g‖²`, so the
domain hypothesis is not a convenience — it is what makes the dominated convergence available. -/

/-- The slope of the group, as multiplication by the defect. -/
theorem coeFn_slope_phaseGroup (f : L2) (t s : ℝ) :
    ((slope (fun r => phaseGroup hκ r f) t s : L2) : E → ℂ)
      =ᵐ[volume] fun x => phaseFun κ t x * f x * ((s - t)⁻¹ • (phaseFun κ (s - t) x - 1)) := by
  rw [slope_def_module]
  filter_upwards [Lp.coeFn_smul ((s - t)⁻¹ : ℝ) (phaseGroup hκ s f - phaseGroup hκ t f),
    Lp.coeFn_sub (phaseGroup hκ s f) (phaseGroup hκ t f),
    coeFn_phaseGroup hκ s f, coeFn_phaseGroup hκ t f] with x e1 e2 e3 e4
  rw [e1, Pi.smul_apply, e2, Pi.sub_apply, e3, e4,
    show s = t + (s - t) from by ring, phaseFun_add]
  rw [show t + (s - t) - t = s - t from by ring]
  rw [Complex.real_smul, Complex.real_smul]
  ring

/-- ★★★ **The generator of the phase group is multiplication by its symbol**: on the natural domain,
`d/dt e^{−itκ} f = −i·κ·e^{−itκ} f` in `L²`. -/
theorem hasDerivAt_phaseGroup_apply (f g : L2)
    (hg : (g : E → ℂ) =ᵐ[volume] fun x => (κ x : ℂ) * f x) (t : ℝ) :
    HasDerivAt (fun s => phaseGroup hκ s f) ((-Complex.I) • phaseGroup hκ t g) t := by
  rw [hasDerivAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  have hdefect : ∀ s ≠ t, ((slope (fun r => phaseGroup hκ r f) t s
        - (-Complex.I) • phaseGroup hκ t g : L2) : E → ℂ)
      =ᵐ[volume] fun x => phaseFun κ t x * f x * phaseDefect κ (s - t) x := by
    intro s hs
    filter_upwards [Lp.coeFn_sub (slope (fun r => phaseGroup hκ r f) t s)
        ((-Complex.I) • phaseGroup hκ t g),
      coeFn_slope_phaseGroup hκ f t s,
      Lp.coeFn_smul (-Complex.I) (phaseGroup hκ t g), coeFn_phaseGroup hκ t g, hg]
      with x e1 e2 e3 e4 e5
    rw [e1, Pi.sub_apply, e2, e3, Pi.smul_apply, e4, e5, phaseDefect, smul_eq_mul]
    ring
  have hnorm : ∀ s ≠ t, ‖slope (fun r => phaseGroup hκ r f) t s
        - (-Complex.I) • phaseGroup hκ t g‖ ^ 2
      = ∫ x, ‖f x‖ ^ 2 * ‖phaseDefect κ (s - t) x‖ ^ 2 := by
    intro s hs
    rw [norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hdefect s hs] with x hx
    rw [hx, norm_mul, norm_mul, norm_phaseFun, one_mul, mul_pow]
  have hbound : Integrable (fun x => 4 * ‖g x‖ ^ 2) volume := by
    have h : Integrable (fun x => ‖g x‖ ^ 2) volume := by
      exact_mod_cast (Lp.memLp g).integrable_norm_pow (p := 2) two_ne_zero
    exact h.const_mul 4
  have hsub : Tendsto (fun s : ℝ => s - t) (𝓝[≠] t) (𝓝 0) := by
    have h0 : Tendsto (fun s : ℝ => s) (𝓝[≠] t) (𝓝 t) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have h := h0.sub_const t
    simpa using h
  have hsq : Tendsto (fun s => ∫ x, ‖f x‖ ^ 2 * ‖phaseDefect κ (s - t) x‖ ^ 2) (𝓝[≠] t)
      (𝓝 0) := by
    have hzero : (0 : ℝ) = ∫ _x : E, (0 : ℝ) := by rw [integral_zero]
    rw [hzero]
    refine tendsto_integral_filter_of_dominated_convergence (fun x => 4 * ‖g x‖ ^ 2)
      (Eventually.of_forall fun s => ?_) ?_ hbound ?_
    · refine AEStronglyMeasurable.mul ?_ ?_
      · have h := (Lp.aestronglyMeasurable f).norm
        simpa [pow_two, Pi.mul_def] using h.mul h
      · have h : AEStronglyMeasurable (fun x : E => ‖phaseDefect κ (s - t) x‖)
            (volume : Measure E) :=
          ((measurable_phaseDefect hκ (s - t)).norm).aestronglyMeasurable
        simpa [pow_two, Pi.mul_def] using h.mul h
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hst : s - t ≠ 0 := sub_ne_zero_of_ne hs
      filter_upwards [hg] with x hx
      have hst' := hst
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 : ‖phaseDefect κ (s - t) x‖ ^ 2 ≤ (2 * |κ x|) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_phaseDefect_le hst x) 2
      have h2 : ‖g x‖ = |κ x| * ‖f x‖ := by
        rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc ‖f x‖ ^ 2 * ‖phaseDefect κ (s - t) x‖ ^ 2
          ≤ ‖f x‖ ^ 2 * (2 * |κ x|) ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 4 * (|κ x| * ‖f x‖) ^ 2 := by ring
        _ = 4 * ‖g x‖ ^ 2 := by rw [h2]
    · filter_upwards with x
      have h1 : Tendsto (fun s : ℝ => phaseDefect κ (s - t) x) (𝓝[≠] t) (𝓝 0) := by
        refine (tendsto_phaseDefect κ x).comp ?_
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hsub ?_
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact sub_ne_zero_of_ne hs
      have h2 := (h1.norm.pow 2).const_mul (‖f x‖ ^ 2)
      simpa using h2
  have hsq' : Tendsto (fun s => ‖slope (fun r => phaseGroup hκ r f) t s
      - (-Complex.I) • phaseGroup hκ t g‖ ^ 2) (𝓝[≠] t) (𝓝 0) := by
    refine hsq.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hnorm s hs).symm
  have h := hsq'.sqrt
  rw [Real.sqrt_zero] at h
  exact h.congr fun s => Real.sqrt_sq (norm_nonneg _)


/-! ### The group preserves the domain

A phase commutes with a multiplication, so this is free — and it is what an interacting version
would need, since the Duhamel integrand has to stay in the domain. -/

theorem phaseGroup_mem_mulDomain (f : (MeasureTheory.L2.mulOp (μ := (volume : Measure E)) κ).domain)
    (t : ℝ) :
    (phaseGroup hκ t (f : L2)) ∈ (MeasureTheory.L2.mulOp (μ := (volume : Measure E)) κ).domain := by
  refine MeasureTheory.L2.mem_mulDomain_iff.2 ?_
  refine MemLp.mono' (g := fun x => ‖(MeasureTheory.L2.mulOp κ f : L2) x‖)
    (Lp.memLp _).norm ?_ ?_
  · exact ((Complex.measurable_ofReal.comp hκ).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable _)
  · filter_upwards [coeFn_phaseGroup hκ t (f : L2), MeasureTheory.L2.coeFn_mulOp f] with x h1 h2
    rw [h1, h2, norm_mul, norm_mul, norm_mul, norm_phaseFun, one_mul]

end SchrodingerGroup

namespace SchrodingerGroup

open MeasureTheory Filter

/-! ### The free Schrödinger equation, in both representations

The generator is the **self-adjoint operator** of #64(i), not a fresh object: these two theorems are
what make "`H₀` generates the free dynamics" a statement rather than a name. -/

/-- ★★★ **The free Schrödinger equation in the momentum representation**: the phase group's
derivative is `−i` times the free Hamiltonian, which is `freeSymbolOp` — self-adjoint by #64(i). -/
theorem hasDerivAt_phaseGroup_freeSymbolOp (f : freeSymbolOp.domain) (t : ℝ) :
    HasDerivAt (fun s => phaseGroup (measurable_freeSymbol (E := ℝ)) s (f : Lp ℂ 2 (volume : Measure ℝ)))
      ((-Complex.I) • phaseGroup (measurable_freeSymbol (E := ℝ)) t (freeSymbolOp f)) t :=
  hasDerivAt_phaseGroup_apply (measurable_freeSymbol (E := ℝ)) (f : Lp ℂ 2 (volume : Measure ℝ))
    (freeSymbolOp f) (MeasureTheory.L2.coeFn_mulOp f) t

/-- The conjugated generator at an image point, in the vocabulary this file uses. -/
theorem freePositionOp_apply_fourierL2 (f : freeSymbolOp.domain)
    (h : fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ)) ∈ freePositionOp.domain) :
    freePositionOp ⟨fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ)), h⟩
      = fourierL2.symm (freeSymbolOp f) :=
  LinearPMap.conjIsometry_apply_of_eq _ _ f _ rfl

/-- ★★★ **The free Schrödinger equation in the position representation**, `i ∂_t ψ = H₀ψ` with `H₀`
the conjugated self-adjoint operator `freePositionOp` of #64(i). The proof applies the Fourier
isometry to the momentum form — the conjugation does the work, nothing is recomputed. -/
theorem hasDerivAt_fourierGroup_freePositionOp (f : freeSymbolOp.domain)
    (h : fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ)) ∈ freePositionOp.domain) (t : ℝ) :
    HasDerivAt (fun s => fourierGroup (measurable_freeSymbol (E := ℝ)) s
        (fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ))))
      ((-Complex.I) • fourierGroup (measurable_freeSymbol (E := ℝ)) t
        (freePositionOp ⟨fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ)), h⟩)) t := by
  have hmom := hasDerivAt_phaseGroup_freeSymbolOp f t
  have hL : HasFDerivAt (fun u : Lp ℂ 2 (volume : Measure ℝ) => fourierL2.symm u)
      ((fourierL2.symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ)
      (phaseGroup (measurable_freeSymbol (E := ℝ)) t
        (f : Lp ℂ 2 (volume : Measure ℝ))) :=
    ((fourierL2.symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars
      ℝ).hasFDerivAt
  have hcomp := HasFDerivAt.comp_hasDerivAt (x := t) hL hmom
  have hfun : (fun s => fourierGroup (measurable_freeSymbol (E := ℝ)) s
        (fourierL2.symm (f : Lp ℂ 2 (volume : Measure ℝ))))
      = (fun u : Lp ℂ 2 (volume : Measure ℝ) => fourierL2.symm u)
        ∘ fun s => phaseGroup (measurable_freeSymbol (E := ℝ)) s
            (f : Lp ℂ 2 (volume : Measure ℝ)) := by
    funext s
    rw [Function.comp_apply, fourierGroup_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [hfun]
  refine hcomp.congr_deriv ?_
  rw [freePositionOp_apply_fourierL2 f h]
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, fourierGroup_apply,
    LinearIsometryEquiv.apply_symm_apply, map_smul]

end SchrodingerGroup

end

end
