/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Semigroup.BoundedPerturbation
public import CsdLean4.Mathlib.Probability.BrownianVec
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.Normed.Operator.Mul

/-!
# The heat semigroup on `L²(ℝᵈ)` as Gaussian convolution

**Category:** 1-Mathlib (CSD-free; staged for upstream).

The heat semigroup `P_t f = γ_t * f`, `γ_t` the centred Gaussian of variance `t`, on `L²(ℝ, ℂ)`,
built as the Bochner integral of translates: `P_t f = ∫ τ_y f dγ_t(y)` in `L²`, where `τ_y f = f (· + y)`
is the translation isometry. Every property then comes from the isometry and the probability
measure, with no kernel estimate: `‖P_t‖ ≤ 1`, `P_s P_t = P_{s+t}` (Gaussian convolution of
measures), strong continuity (the translates move continuously in `L²`, and `γ_t` concentrates at
`0`), and `P_0 = 1`. It is a strongly continuous contraction semigroup in the sense of
`BoundedPerturbation.lean`, so the Dyson series, the Duhamel equation and the Trotter product
formula of that module apply to `P_t` perturbed by a bounded potential.

The Wiener side: the pointwise formula `(P_t f)(x) = ∫ f (x + y) dγ_t(y)` a.e., and for a
pre-Brownian motion `B` this is `E[f (x + B_t)]`. No generator is written: `−½Δ` never appears.

* `gaussian t` — the Gaussian of variance `t` (the Dirac mass at `0` for `t ≤ 0`);
  `gaussian_conv_gaussian` — `γ_s ∗ γ_t = γ_{s+t}`;
* `translate y : L² →L[ℂ] L²` — the translation isometry, `continuous_translate_apply`,
  `translate_translate`;
* `heatSemigroup t : L² →L[ℂ] L²` — `∫ τ_y f dγ_t(y)`; `norm_heatSemigroup_le`,
  `heatSemigroup_of_nonpos`, ★ `heatSemigroup_add` (the semigroup law),
  ★ `continuous_heatSemigroup_apply` (strong continuity);
* ★★ `isContractionSemigroup_heatSemigroup` — the heat semigroup is an `IsContractionSemigroup`;
* ★ `heatSemigroup_apply_ae_eq` — **the pointwise formula** `P_t f =ᵐ x ↦ ∫ f (x + y) dγ_t(y)`, by
  pairing with indicators of finite-measure sets and Fubini;
* ★ `heatConv_eq_integral_brownian` — `∫ f (x + y) dγ_t(y) = E[f (x + B_t)]` for a pre-Brownian
  motion;
* `potential V` — multiplication by a bounded potential `V ∈ L^∞` (Mathlib's Hölder pairing);
  `perturbedHeat V t` — **`e^{−t(H₀+V)}`** as the Dyson series around `P_t` with interaction `−V`,
  a semigroup (`perturbedHeat_add`) satisfying the Duhamel equation (★ `perturbedHeat_eq`);
* ★★ `tendsto_trotter_perturbedHeat` — **the Trotter product formula**
  `(P_{t/n} · exp (−(t/n) V))ⁿ f → e^{−t(H₀+V)} f`: the time-sliced Euclidean path integral in
  operator form. Feynman–Kac (FC-4) identifies the left side with the Wiener functional.

**The wider picture.** The same operator `e^{−t(H₀+V)}` is reached from the Dyson series
(perturbation theory), from the Duhamel equation (the evolution equation), and from the Trotter
limit (time slicing); with FC-3/FC-4 it is also the Wiener functional (the path integral). One
object, four formulations of the same quantum dynamics, each a theorem at the pin.

## Honest scope

⚠️ **`L²(ℝᵈ)`, `ℝᵈ = EuclideanSpace ℝ ι`.** The Gaussian is the product Gaussian `gaussianVec`
of `Probability/BrownianVec.lean` (its convolution and scaling laws are read off characteristic
functions, `Measure.ext_of_charFun`), and the Brownian motion is `IsPreBrownianVec`, `d` jointly
independent real ones (BACKLOG #41, 2026-09-20; one dimension before). Pointwise statements are
almost-everywhere statements about `L²` classes.

References: M. Kac, Trans. AMS 65, 1 (1949); B. Simon, *Functional Integration and Quantum Physics*,
Ch. 1; `Analysis/Semigroup/BoundedPerturbation.lean` (FC-1); `specs/feynman-continuum-scoping.md`
(FC-2); `specs/BACKLOG.md` #36(c).
-/

@[expose] public section

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter

namespace HeatSemigroup

/-! ### Multiplication operators on `L²(E)` -/

section Multiplier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `L²(E, ℂ)` with Lebesgue measure, `E` a finite-dimensional inner product space. -/
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-- **Multiplication by a bounded potential** `V ∈ L^∞` as an operator on `L²(E)`, Mathlib's Hölder
pairing `L^∞ × L² → L²`. -/
noncomputable def potential (V : Lp ℂ ∞ (volume : Measure E)) : L2 →L[ℂ] L2 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2 V

theorem coeFn_potential (V : Lp ℂ ∞ (volume : Measure E)) (f : L2) :
    potential V f =ᵐ[volume] fun x => V x * f x := by
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) V f] with x hx
  rw [potential, ContinuousLinearMap.holderL_apply_apply]
  exact hx

theorem norm_potential_le (V : Lp ℂ ∞ (volume : Measure E)) : ‖potential V‖ ≤ ‖V‖ := by
  refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
  calc ‖(ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2‖ * ‖V‖
      ≤ ‖ContinuousLinearMap.mul ℂ ℂ‖ * ‖V‖ := by
        gcongr
        exact ContinuousLinearMap.norm_holderL_le _
    _ ≤ 1 * ‖V‖ := by
        gcongr
        exact ContinuousLinearMap.opNorm_mul_le ℂ ℂ
    _ = ‖V‖ := one_mul _

/-- `L²(E)` is nontrivial: the indicator of the unit ball. -/
instance instNontrivialL2 : Nontrivial L2 := by
  refine ⟨⟨indicatorConstLp 2 (Metric.isOpen_ball (x := (0 : E)) (ε := 1)).measurableSet
    measure_ball_lt_top.ne (1 : ℂ), 0, fun h => ?_⟩⟩
  have hn := congrArg norm h
  rw [norm_indicatorConstLp (by norm_num) (by norm_num), norm_zero, norm_one, one_mul] at hn
  have hpos : 0 < (volume : Measure E).real (Metric.ball (0 : E) 1) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos
      (Metric.isOpen_ball.measure_pos volume ⟨0, Metric.mem_ball_self one_pos⟩).ne'
      measure_ball_lt_top.ne
  have := Real.rpow_pos_of_pos hpos (1 / (2 : ℝ≥0∞).toReal)
  rw [hn] at this
  exact lt_irrefl _ this

end Multiplier

variable {ι : Type*} [Fintype ι]

/-- Euclidean space `ℝᵈ`. -/
local notation "E" => EuclideanSpace ℝ ι

/-- `L²(ℝᵈ, ℂ)` with Lebesgue measure. -/
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-! ### The Gaussians -/

/-- The centred Gaussian of variance `t` in every coordinate; the Dirac mass at `0` for `t ≤ 0`. -/
noncomputable def gaussian (t : ℝ) : Measure E := gaussianVec ι (Real.toNNReal t)

instance (t : ℝ) : IsProbabilityMeasure (gaussian (ι := ι) t) := by
  unfold gaussian
  infer_instance

theorem charFun_gaussian (t : ℝ) (ξ : E) :
    charFun (gaussian t) ξ = Complex.exp (-(Real.toNNReal t : ℝ) * ‖ξ‖ ^ 2 / 2) :=
  charFun_gaussianVec _ ξ

theorem gaussian_of_nonpos {t : ℝ} (ht : t ≤ 0) : gaussian (ι := ι) t = Measure.dirac 0 := by
  refine Measure.ext_of_charFun (funext fun ξ => ?_)
  rw [charFun_gaussian, charFun_dirac, Real.toNNReal_of_nonpos ht]
  simp

/-- The Gaussians convolve: `γ_s ∗ γ_t = γ_{s+t}` (characteristic functions). -/
theorem gaussian_conv_gaussian {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    gaussian (ι := ι) s ∗ gaussian t = gaussian (s + t) := by
  refine Measure.ext_of_charFun (funext fun ξ => ?_)
  rw [charFun_conv, charFun_gaussian, charFun_gaussian, charFun_gaussian, ← Complex.exp_add,
    Real.toNNReal_add hs ht]
  congr 1
  push_cast
  ring

/-- The Gaussian of variance `t ≥ 0` is the standard Gaussian scaled by `√t`. -/
theorem gaussian_eq_map {t : ℝ} (ht : 0 ≤ t) :
    gaussian (ι := ι) t = (gaussian 1).map (Real.sqrt t • ·) := by
  refine Measure.ext_of_charFun (funext fun ξ => ?_)
  rw [charFun_map_smul, charFun_gaussian, charFun_gaussian, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg t), Real.coe_toNNReal _ ht, Real.toNNReal_one]
  congr 1
  norm_cast
  rw [mul_pow, Real.sq_sqrt ht]
  ring

/-- The Gaussian of positive variance is absolutely continuous with respect to Lebesgue measure. -/
theorem gaussian_absolutelyContinuous {t : ℝ} (ht : 0 < t) :
    gaussian (ι := ι) t ≪ (volume : Measure E) :=
  gaussianVec_absolutelyContinuous (Real.toNNReal_pos.mpr ht).ne'

/-! ### Translation on `L²` -/

/-- Translation `f ↦ f (· + y)` as a continuous linear isometry of `L²(ℝᵈ)`. -/
noncomputable def translate (y : E) : L2 →L[ℂ] L2 :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x => x + y) (measurePreserving_add_right (volume : Measure E) y))
    |>.toContinuousLinearMap

theorem translate_apply (y : E) (f : L2) :
    translate y f = Lp.compMeasurePreserving (fun x => x + y) (measurePreserving_add_right (volume : Measure E) y) f :=
  rfl

theorem coeFn_translate (y : E) (f : L2) :
    translate y f =ᵐ[volume] fun x => f (x + y) :=
  Lp.coeFn_compMeasurePreserving f _

theorem norm_translate_apply (y : E) (f : L2) :
    ‖translate y f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f _

theorem translate_zero (f : L2) : translate 0 f = f := by
  rw [translate_apply]
  simp only [add_zero]
  exact congrArg (fun g : L2 →+ L2 => g f) (Lp.compMeasurePreserving_id (p := 2)
    (μb := (volume : Measure E)))

/-- The translates of an `L²` function move continuously. -/
theorem continuous_translate_apply (f : L2) :
    Continuous fun y => translate y f := by
  have hg : Continuous fun y : E => (ContinuousMap.mk (fun x : E => x + y) (by fun_prop) : C(E, E)) :=
    ContinuousMap.continuous_of_continuous_uncurry _ (continuous_snd.add continuous_fst)
  exact continuous_const.compMeasurePreservingLp hg
    (fun y => measurePreserving_add_right (volume : Measure E) y) ENNReal.ofNat_ne_top

/-- Translations compose: `τ_y (τ_z f) = τ_{z+y} f`. -/
theorem translate_translate (y z : E) (f : L2) : translate y (translate z f) = translate (z + y) f := by
  refine Lp.ext ?_
  have h1 := coeFn_translate y (translate z f)
  have h2 := (measurePreserving_add_right (volume : Measure E) y).quasiMeasurePreserving.ae_eq_comp
    (coeFn_translate z f)
  have h3 := coeFn_translate (z + y) f
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  rw [hx1, hx3]
  simp only [Function.comp] at hx2
  rw [hx2]
  congr 1
  abel

/-! ### The heat semigroup -/

/-- The heat operator as the `L²`-valued Bochner integral of the translates. -/
noncomputable def heatIntegral (t : ℝ) (f : L2) : L2 := ∫ y, translate y f ∂gaussian t

theorem integrable_translate (t : ℝ) (f : L2) :
    Integrable (fun y => translate y f) (gaussian t) :=
  Integrable.of_bound (continuous_translate_apply f).aestronglyMeasurable ‖f‖
    (Eventually.of_forall fun y => (norm_translate_apply y f).le)

theorem norm_heatIntegral_le (t : ℝ) (f : L2) : ‖heatIntegral t f‖ ≤ ‖f‖ := by
  refine le_trans (norm_integral_le_of_norm_le (integrable_const ‖f‖)
    (Eventually.of_forall fun y => (norm_translate_apply y f).le)) ?_
  simp

theorem heatIntegral_add (t : ℝ) (f g : L2) :
    heatIntegral t (f + g) = heatIntegral t f + heatIntegral t g := by
  simp only [heatIntegral, map_add]
  exact integral_add (integrable_translate t f) (integrable_translate t g)

theorem heatIntegral_smul (t : ℝ) (c : ℂ) (f : L2) : heatIntegral t (c • f) = c • heatIntegral t f := by
  simp only [heatIntegral, map_smul]
  exact integral_smul c _

/-- **The heat semigroup** `P_t f = ∫ τ_y f dγ_t(y)` as a continuous linear map on `L²(ℝᵈ)`. -/
noncomputable def heatSemigroup (t : ℝ) : L2 →L[ℂ] L2 :=
  LinearMap.mkContinuous
    { toFun := heatIntegral t
      map_add' := heatIntegral_add t
      map_smul' := fun c f => heatIntegral_smul t c f }
    1 fun f => by simpa using norm_heatIntegral_le t f

theorem heatSemigroup_apply (t : ℝ) (f : L2) : heatSemigroup t f = ∫ y, translate y f ∂gaussian t :=
  rfl

theorem norm_heatSemigroup_le (t : ℝ) : ‖heatSemigroup (ι := ι) t‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem norm_heatSemigroup_apply_le (t : ℝ) (f : L2) : ‖heatSemigroup t f‖ ≤ ‖f‖ :=
  norm_heatIntegral_le t f

theorem heatSemigroup_of_nonpos {t : ℝ} (ht : t ≤ 0) : heatSemigroup (ι := ι) t = 1 := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [heatSemigroup_apply, gaussian_of_nonpos ht, integral_dirac, translate_zero, one_apply_eq_self]

theorem heatSemigroup_max (t : ℝ) : heatSemigroup (ι := ι) t = heatSemigroup (max t 0) := by
  rcases le_or_gt 0 t with ht | ht
  · rw [max_eq_left ht]
  · rw [max_eq_right ht.le, heatSemigroup_of_nonpos ht.le, heatSemigroup_of_nonpos le_rfl]

/-- ★ **The semigroup law**: `P_{s+t} = P_s P_t` for `s, t ≥ 0`, by Gaussian convolution. -/
theorem heatSemigroup_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    heatSemigroup (ι := ι) (s + t) = heatSemigroup s * heatSemigroup t := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [mul_apply_eq_comp, heatSemigroup_apply, heatSemigroup_apply, heatSemigroup_apply,
    ← gaussian_conv_gaussian hs ht, Measure.conv,
    integral_map (by fun_prop : Measurable fun p : E × E => p.1 + p.2).aemeasurable
      (continuous_translate_apply f).aestronglyMeasurable,
    integral_prod (fun p : E × E => translate (p.1 + p.2) f) (Integrable.of_bound
      ((continuous_translate_apply f).comp
        (by fun_prop : Continuous fun p : E × E => p.1 + p.2)).aestronglyMeasurable
      ‖f‖ (Eventually.of_forall fun p => (norm_translate_apply _ f).le))]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [← (translate y).integral_comp_comm (integrable_translate t f)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [translate_translate, add_comm]

/-! ### Strong continuity -/

theorem heatSemigroup_apply_sub_eq (t : ℝ) (f : L2) :
    heatSemigroup t f - f = ∫ y, (translate y f - f) ∂gaussian t := by
  rw [integral_sub (integrable_translate t f) (integrable_const f), integral_const,
    heatSemigroup_apply]
  simp

theorem norm_heatSemigroup_apply_sub_le (t : ℝ) (f : L2) :
    ‖heatSemigroup t f - f‖ ≤ ∫ y, ‖translate y f - f‖ ∂gaussian t := by
  rw [heatSemigroup_apply_sub_eq]
  exact norm_integral_le_integral_norm _

/-- The Gaussians concentrate at `0`: `∫ ‖τ_y f − f‖ dγ_t(y) → 0` as `t → 0⁺`. -/
theorem tendsto_integral_norm_translate_sub (f : L2) :
    Tendsto (fun t => ∫ y, ‖translate y f - f‖ ∂gaussian t) (𝓝[≥] 0) (𝓝 0) := by
  set G : E → ℝ := fun y => ‖translate y f - f‖ with hG
  have hGc : Continuous G := ((continuous_translate_apply f).sub continuous_const).norm
  have hrw : ∀ t ∈ Set.Ici (0 : ℝ),
      ∫ y, G y ∂gaussian t = ∫ z, G (Real.sqrt t • z) ∂gaussian 1 := by
    intro t ht
    rw [gaussian_eq_map ht, integral_map (by fun_prop) hGc.aestronglyMeasurable]
  have hbound : ∀ y, ‖G y‖ ≤ 2 * ‖f‖ := by
    intro y
    rw [hG, Real.norm_eq_abs, abs_norm]
    calc ‖translate y f - f‖ ≤ ‖translate y f‖ + ‖f‖ := norm_sub_le _ _
      _ = 2 * ‖f‖ := by rw [norm_translate_apply]; ring
  have key : Tendsto (fun t => ∫ z, G (Real.sqrt t • z) ∂gaussian 1) (𝓝[≥] 0)
      (𝓝 (∫ z, G (Real.sqrt 0 • z) ∂gaussian 1)) := by
    have hm : ∀ t : ℝ, Continuous fun z : E => G (Real.sqrt t • z) := fun t => by fun_prop
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * ‖f‖)
      (Eventually.of_forall fun t => (hm t).aestronglyMeasurable)
      (Eventually.of_forall fun t => Eventually.of_forall fun z => hbound _)
      (integrable_const _) (Eventually.of_forall fun z => ?_)
    have hz : Tendsto (fun t : ℝ => Real.sqrt t • z) (𝓝 0) (𝓝 (Real.sqrt 0 • z)) :=
      (Real.continuous_sqrt.tendsto 0).smul_const z
    have hGz : Tendsto (fun t : ℝ => G (Real.sqrt t • z)) (𝓝 0) (𝓝 (G (Real.sqrt 0 • z))) :=
      (hGc.tendsto _).comp hz
    exact hGz.mono_left nhdsWithin_le_nhds
  have h0 : ∫ z, G (Real.sqrt 0 • z) ∂gaussian 1 = 0 := by
    simp [hG, translate_zero]
  rw [h0] at key
  exact key.congr' (eventually_nhdsWithin_of_forall fun t ht => (hrw t ht).symm)

/-- For `0 ≤ a ≤ b`, `‖P_a f − P_b f‖ ≤ ‖P_{b−a} f − f‖`. -/
theorem norm_heatSemigroup_apply_sub_apply_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (f : L2) :
    ‖heatSemigroup a f - heatSemigroup b f‖ ≤ ‖heatSemigroup (b - a) f - f‖ := by
  have hb : heatSemigroup (ι := ι) b = heatSemigroup a * heatSemigroup (b - a) := by
    rw [← heatSemigroup_add ha (sub_nonneg.mpr hab), add_sub_cancel]
  rw [hb, mul_apply_eq_comp, ← map_sub]
  exact le_trans (norm_heatSemigroup_apply_le _ _) (le_of_eq (norm_sub_rev _ _))

/-- ★ **Strong continuity**: `t ↦ P_t f` is continuous for every `f ∈ L²`. -/
theorem continuous_heatSemigroup_apply (f : L2) : Continuous fun t => heatSemigroup t f := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hle : ∀ t, ‖heatSemigroup t f - heatSemigroup t₀ f‖
      ≤ ∫ y, ‖translate y f - f‖ ∂gaussian |max t 0 - max t₀ 0| := by
    intro t
    refine le_trans ?_ (norm_heatSemigroup_apply_sub_le _ f)
    rw [heatSemigroup_max t, heatSemigroup_max t₀]
    rcases le_total (max t 0) (max t₀ 0) with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
      exact norm_heatSemigroup_apply_sub_apply_le (le_max_right _ _) h f
    · rw [abs_of_nonneg (sub_nonneg.mpr h), norm_sub_rev]
      exact norm_heatSemigroup_apply_sub_apply_le (le_max_right _ _) h f
  have hlim : Tendsto (fun t => |max t 0 - max t₀ 0|) (𝓝 t₀) (𝓝[≥] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun t => Set.mem_Ici.mpr (abs_nonneg _)⟩
    have : Tendsto (fun t => |max t 0 - max t₀ 0|) (𝓝 t₀) (𝓝 |max t₀ 0 - max t₀ 0|) :=
      ((continuous_id.max continuous_const).sub continuous_const).abs.tendsto t₀
    simpa using this
  exact squeeze_zero (fun t => norm_nonneg _) hle
    ((tendsto_integral_norm_translate_sub f).comp hlim)

/-- ★★ **The heat semigroup is a strongly continuous contraction semigroup** in the sense of
`BoundedPerturbation.lean`: the Dyson series, the Duhamel equation and the Trotter product formula
apply to it perturbed by any bounded operator. -/
theorem isContractionSemigroup_heatSemigroup : IsContractionSemigroup (heatSemigroup (ι := ι)) where
  eq_one_of_nonpos _ ht := heatSemigroup_of_nonpos ht
  map_add _ _ hs ht := heatSemigroup_add hs ht
  norm_le_one := norm_heatSemigroup_le
  continuous_apply := continuous_heatSemigroup_apply

/-! ### The pointwise formula -/

/-- The Wiener functional `x ↦ ∫ f (x + y) dγ_t(y)`. -/
noncomputable def heatConv (t : ℝ) (f : E → ℂ) (x : E) : ℂ := ∫ y, f (x + y) ∂gaussian t

theorem aestronglyMeasurable_shift (f : L2) (t : ℝ) :
    AEStronglyMeasurable (fun p : E × E => f (p.1 + p.2))
      ((volume : Measure E).prod (gaussian t)) := by
  have h := (Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving
    (quasiMeasurePreserving_add_swap (μ := (volume : Measure E)) (ν := gaussian t))
  refine h.congr (Eventually.of_forall fun p => ?_)
  simp [Function.comp, add_comm]

theorem integrable_shift_prod (f : L2) (t : ℝ) {s : Set E} (hμs : volume s < ∞) :
    Integrable (fun p : E × E => f (p.1 + p.2))
      (((volume : Measure E).restrict s).prod (gaussian t)) := by
  have : IsFiniteMeasure ((volume : Measure E).restrict s) :=
    ⟨by simpa [Measure.restrict_apply_univ] using hμs⟩
  have hmeas : AEStronglyMeasurable (fun p : E × E => f (p.1 + p.2))
      (((volume : Measure E).restrict s).prod (gaussian t)) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact (aestronglyMeasurable_shift f t).restrict
  rw [integrable_prod_iff' hmeas]
  have hsec : ∀ y : E, MemLp (fun x => f (x + y)) 2 ((volume : Measure E).restrict s) := fun y =>
    ((Lp.memLp f).comp_measurePreserving (measurePreserving_add_right (volume : Measure E) y)).restrict s
  refine ⟨Eventually.of_forall fun y => (hsec y).integrable one_le_two, ?_⟩
  set M : ℝ := ∫ x, ‖f x‖ ^ 2 with hM
  have hMint : Integrable (fun x => ‖f x‖ ^ 2) (volume : Measure E) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  refine Integrable.of_bound (hmeas.norm.prod_swap.integral_prod_right') ((volume.real s + M) / 2)
    (Eventually.of_forall fun y => ?_)
  have hsq : Integrable (fun x => ‖f (x + y)‖ ^ 2) ((volume : Measure E).restrict s) :=
    (memLp_two_iff_integrable_sq_norm (hsec y).1).mp (hsec y)
  have h1 : ∫ x in s, ‖f (x + y)‖ ≤ ∫ x in s, (1 + ‖f (x + y)‖ ^ 2) / 2 := by
    refine integral_mono ((hsec y).integrable one_le_two).norm ((integrable_const 1).add hsq |>.div_const 2)
      fun x => ?_
    simp only
    nlinarith [sq_nonneg (‖f (x + y)‖ - 1)]
  have h2 : ∫ x in s, (1 + ‖f (x + y)‖ ^ 2) / 2 = (volume.real s + ∫ x in s, ‖f (x + y)‖ ^ 2) / 2 := by
    rw [integral_div, integral_add (integrable_const 1) hsq, setIntegral_const, smul_eq_mul, mul_one]
  have h3 : ∫ x in s, ‖f (x + y)‖ ^ 2 ≤ M := by
    refine le_trans (setIntegral_le_integral ?_ (Eventually.of_forall fun x => by positivity)) ?_
    · exact (memLp_two_iff_integrable_sq_norm
        ((Lp.memLp f).comp_measurePreserving (measurePreserving_add_right _ y)).1).mp
        ((Lp.memLp f).comp_measurePreserving (measurePreserving_add_right _ y))
    · rw [hM, integral_add_right_eq_self (fun x => ‖f x‖ ^ 2) y]
  rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
  calc ∫ x in s, ‖f (x + y)‖ ≤ (volume.real s + ∫ x in s, ‖f (x + y)‖ ^ 2) / 2 := h1.trans h2.le
    _ ≤ (volume.real s + M) / 2 := by gcongr

theorem integrableOn_heatConv (f : L2) (t : ℝ) {s : Set E} (hμs : volume s < ∞) :
    IntegrableOn (heatConv t f) s volume :=
  (integrable_shift_prod f t hμs).integral_prod_left

/-- ★ **The pointwise formula**: `P_t f =ᵐ x ↦ ∫ f (x + y) dγ_t(y)`. The `L²`-valued Bochner integral
of the translates and the Wiener functional agree almost everywhere, by pairing with the
indicators of finite-measure sets and Fubini. -/
theorem heatSemigroup_apply_ae_eq (t : ℝ) (f : L2) :
    heatSemigroup t f =ᵐ[volume] heatConv t f := by
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s hs hμs => ?_)
    (fun s _ hμs => integrableOn_heatConv f t hμs) (fun s hs hμs => ?_)
  · have : IsFiniteMeasure ((volume : Measure E).restrict s) :=
      ⟨by simpa [Measure.restrict_apply_univ] using hμs⟩
    exact ((Lp.memLp (heatSemigroup t f)).restrict s).integrable one_le_two
  · rw [← L2.inner_indicatorConstLp_one hs hμs.ne (heatSemigroup t f), heatSemigroup_apply,
      ← innerSL_apply_apply, ← (innerSL ℂ (indicatorConstLp 2 hs hμs.ne (1 : ℂ))).integral_comp_comm
        (integrable_translate t f)]
    simp_rw [innerSL_apply_apply, L2.inner_indicatorConstLp_one hs hμs.ne]
    have hswap := integral_integral_swap (μ := (volume : Measure E).restrict s) (ν := gaussian t)
      (f := fun x y => (f : E → ℂ) (x + y)) (integrable_shift_prod f t hμs)
    simp only [heatConv]
    rw [hswap]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    exact integral_congr_ae (ae_restrict_of_ae (coeFn_translate y f))

/-! ### The Wiener side -/

/-- ★ For a pre-Brownian motion `B` in `ℝᵈ` and `t > 0`, the Wiener functional is the expectation
`∫ f (x + y) dγ_t(y) = E[f (x + B_t)]`. -/
theorem heatConv_eq_integral_brownian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → E} (hB : IsPreBrownianVec B P) (hBm : ∀ t, Measurable (B t)) {t : ℝ}
    (ht : 0 < t) {f : E → ℂ} (hf : AEStronglyMeasurable f volume) (x : E) :
    heatConv t f x = ∫ ω, f (x + B (Real.toNNReal t) ω) ∂P := by
  have hlaw := hB.hasLaw_eval hBm (Real.toNNReal t)
  have hmeas : AEStronglyMeasurable (fun y => f (x + y)) (gaussianVec ι (Real.toNNReal t)) :=
    (hf.comp_measurePreserving (measurePreserving_add_left volume x)).mono_ac
      (gaussianVec_absolutelyContinuous (Real.toNNReal_pos.mpr ht).ne')
  rw [heatConv, gaussian, ← hlaw.integral_comp hmeas]
  rfl

/-! ### Bounded potentials and the perturbed heat semigroup -/

/-- **The perturbed heat semigroup** `e^{−t(H₀ + V)}` for a bounded potential `V`: the Dyson series
of `BoundedPerturbation.lean` around `P_t` with interaction `−V`. No generator is written. -/
noncomputable def perturbedHeat (V : Lp ℂ ∞ (volume : Measure E)) (t : ℝ) : L2 →L[ℂ] L2 :=
  (isContractionSemigroup_heatSemigroup (ι := ι)).perturbed (-potential V) t

theorem perturbedHeat_apply (V : Lp ℂ ∞ (volume : Measure E)) (t : ℝ) (f : L2) :
    perturbedHeat V t f = ContractionSemigroup.dysonSum heatSemigroup (-potential V) t f :=
  rfl

/-- The perturbed heat semigroup is a semigroup. -/
theorem perturbedHeat_add (V : Lp ℂ ∞ (volume : Measure E)) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    perturbedHeat V (t + s) = perturbedHeat V t * perturbedHeat V s :=
  ContractionSemigroup.perturbed_add _ isContractionSemigroup_heatSemigroup hs ht

/-- ★ The Duhamel equation of the perturbed heat semigroup:
`e^{−t(H₀+V)} f = P_t f − ∫₀ᵗ P_{t−s} (V · e^{−s(H₀+V)} f) ds`. -/
theorem perturbedHeat_eq (V : Lp ℂ ∞ (volume : Measure E)) {t : ℝ} (ht : 0 ≤ t) (f : L2) :
    perturbedHeat V t f
      = heatSemigroup t f - ∫ s in (0 : ℝ)..t, heatSemigroup (t - s) (potential V (perturbedHeat V s f)) := by
  rw [perturbedHeat_apply, ContractionSemigroup.dysonSum_eq_add_integral _
    isContractionSemigroup_heatSemigroup ht f, sub_eq_add_neg, ← intervalIntegral.integral_neg]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp [perturbedHeat_apply]

/-- ★★ **The Trotter product formula for the heat semigroup with a bounded potential**:
`(P_{t/n} · exp (−(t/n) V))ⁿ f → e^{−t(H₀+V)} f`. This is the time-sliced Euclidean path integral in
operator form; Feynman–Kac (FC-4) identifies the left side with a Wiener functional. -/
theorem tendsto_trotter_perturbedHeat (V : Lp ℂ ∞ (volume : Measure E)) {t : ℝ} (ht : 0 ≤ t)
    (f : L2) :
    Tendsto (fun n : ℕ =>
        (ContractionSemigroup.trotterStep heatSemigroup (-potential V) (t / n) ^ n) f) atTop
      (𝓝 (perturbedHeat V t f)) :=
  ContractionSemigroup.tendsto_trotterStep_pow_apply _ isContractionSemigroup_heatSemigroup ht f

end HeatSemigroup
