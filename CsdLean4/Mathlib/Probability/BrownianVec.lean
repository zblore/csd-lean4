/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Brownian motion in `ℝᵈ` as independent real coordinates

**Category:** 1-Mathlib (CSD-free; staged for upstream).

The Brownian motion of the Mathlib pin is real-valued (`IsPreBrownianReal`, `IsBrownianReal`). A
`d`-dimensional one is `d` jointly independent real ones, and this module packages exactly what the
Euclidean path-integral chain (`HeatSemigroup.lean`, `TimeSlicedWiener.lean`, `FeynmanKac.lean`)
needs of it, on `EuclideanSpace ℝ ι`:

* `IsPreBrownianVec B P` — the coordinates `B t ω i` are pre-Brownian and the coordinate paths
  are jointly independent (`iIndepFun`); `IsBrownianVec` adds almost surely continuous paths;
* ★ `indepFun_pi_of_iIndepFun` — **independent vectors of independent pairs**: if `F i` are jointly
  independent and, for each `i`, `x i (F i)` and `y i (F i)` are independent, then the vectors
  `(x i (F i))ᵢ` and `(y i (F i))ᵢ` are independent. The joint law of the pairs is a product of
  products, and Mathlib's `measurePreserving_arrowProdEquivProdArrow` regroups it as a product
  of two product measures;
* `IsPreBrownianVec.hasLaw_eval` — `B t` has the product Gaussian law
  `(Measure.pi fun _ ↦ gaussianReal 0 t).map (toLp 2)`;
* `IsPreBrownianVec.shift` and ★ `IsPreBrownianVec.indepFun_shift` — the weak Markov property:
  the process shifted by `t₀` is pre-Brownian and independent of `B t₀`, from the coordinate
  statements and `indepFun_pi_of_iIndepFun`.

Everything is conditional: no `d`-dimensional (or one-dimensional) Brownian motion is constructed,
as in `FeynmanKac.lean`.

References: `Mathlib/Probability/BrownianMotion/Basic.lean`; `specs/BACKLOG.md` #41;
`specs/feynman-continuum-scoping.md` §8 D1.
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory

/-! ### Products of absolutely continuous measures -/

namespace MeasureTheory.Measure

universe u

theorem pi_absolutelyContinuous_pi_fin : ∀ (n : ℕ) {X : Fin n → Type u} [∀ i, MeasurableSpace (X i)]
    (μ ν : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)],
    (∀ i, μ i ≪ ν i) → Measure.pi μ ≪ Measure.pi ν
  | 0, _, _, μ, ν, _, _, _ => by
    rw [Measure.pi_of_empty μ, Measure.pi_of_empty ν]
  | n + 1, _, _, μ, ν, _, _, h => by
    have hμ := (measurePreserving_piFinSuccAbove μ 0).symm
    have hν := (measurePreserving_piFinSuccAbove ν 0).symm
    rw [← hμ.map_eq, ← hν.map_eq]
    exact ((h 0).prod (pi_absolutelyContinuous_pi_fin n _ _ fun j => h _)).map
      (MeasurableEquiv.piFinSuccAbove _ 0).symm.measurable

/-- A product of absolutely continuous measures is absolutely continuous. -/
theorem pi_absolutelyContinuous_pi {ι : Type*} [Fintype ι] {X : ι → Type u}
    [∀ i, MeasurableSpace (X i)] {μ ν : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    [∀ i, SigmaFinite (ν i)] (h : ∀ i, μ i ≪ ν i) : Measure.pi μ ≪ Measure.pi ν := by
  have hμ := measurePreserving_piCongrLeft μ (Fintype.equivFin ι).symm
  have hν := measurePreserving_piCongrLeft ν (Fintype.equivFin ι).symm
  rw [← hμ.map_eq, ← hν.map_eq]
  exact (pi_absolutelyContinuous_pi_fin _ _ _ fun i' => h _).map
    (MeasurableEquiv.piCongrLeft X (Fintype.equivFin ι).symm).measurable

end MeasureTheory.Measure

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*} [Fintype ι]

/-! ### Independent vectors of independent pairs -/

/-- ★ **Independent vectors of independent pairs.** If `F i` are jointly independent and, for each
`i`, `x i (F i)` and `y i (F i)` are independent, then the vectors `(x i (F i))ᵢ` and
`(y i (F i))ᵢ` are independent. -/
theorem indepFun_pi_of_iIndepFun [IsProbabilityMeasure P] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {F : ∀ i, Ω → α i} (hF : iIndepFun F P) (hFm : ∀ i, Measurable (F i))
    {x : ∀ i, α i → β} {y : ∀ i, α i → γ} (hx : ∀ i, Measurable (x i)) (hy : ∀ i, Measurable (y i))
    (hxy : ∀ i, IndepFun (fun ω => x i (F i ω)) (fun ω => y i (F i ω)) P) :
    IndepFun (fun ω i => x i (F i ω)) (fun ω i => y i (F i ω)) P := by
  have hxm : ∀ i, Measurable fun ω => x i (F i ω) := fun i => (hx i).comp (hFm i)
  have hym : ∀ i, Measurable fun ω => y i (F i ω) := fun i => (hy i).comp (hFm i)
  have hXm : Measurable fun ω i => x i (F i ω) := measurable_pi_lambda _ hxm
  have hYm : Measurable fun ω i => y i (F i ω) := measurable_pi_lambda _ hym
  rw [indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable hYm.aemeasurable]
  -- the joint law of the pairs is a product of products
  have hpair : iIndepFun (fun i ω => (x i (F i ω), y i (F i ω))) P :=
    hF.comp (fun i a => (x i a, y i a)) fun i => (hx i).prodMk (hy i)
  have hZm : ∀ i, Measurable fun ω => (x i (F i ω), y i (F i ω)) := fun i =>
    ((hx i).prodMk (hy i)).comp (hFm i)
  have hZ := hpair.map_fun_eq_pi_map fun i => (hZm i).aemeasurable
  have hpair_law : ∀ i, P.map (fun ω => (x i (F i ω), y i (F i ω)))
      = (P.map fun ω => x i (F i ω)).prod (P.map fun ω => y i (F i ω)) := fun i =>
    (indepFun_iff_map_prod_eq_prod_map_map (hxm i).aemeasurable (hym i).aemeasurable).mp (hxy i)
  have hX := (hF.comp x hx).map_fun_eq_pi_map fun i => (hxm i).aemeasurable
  have hY := (hF.comp y hy).map_fun_eq_pi_map fun i => (hym i).aemeasurable
  -- regroup
  have hE : (fun ω => ((fun i => x i (F i ω)), (fun i => y i (F i ω))))
      = (MeasurableEquiv.arrowProdEquivProdArrow β γ ι) ∘ fun ω i => (x i (F i ω), y i (F i ω)) := by
    funext ω
    rfl
  show P.map (fun ω => ((fun i => x i (F i ω)), (fun i => y i (F i ω)))) = _
  rw [hE, ← Measure.map_map (MeasurableEquiv.arrowProdEquivProdArrow β γ ι).measurable
    (measurable_pi_lambda _ hZm), hZ]
  simp_rw [hpair_law]
  rw [(measurePreserving_arrowProdEquivProdArrow β γ ι _ _).map_eq, hX, hY]

/-! ### Brownian motion in `ℝᵈ` -/

/-- **A pre-Brownian motion in `ℝᵈ`**: the coordinate processes are real pre-Brownian motions and
the coordinate paths are jointly independent. -/
structure IsPreBrownianVec (B : ℝ≥0 → Ω → EuclideanSpace ℝ ι) (P : Measure Ω) : Prop where
  coord : ∀ i, IsPreBrownianReal (fun t ω => B t ω i) P
  iIndep : iIndepFun (fun i ω (t : ℝ≥0) => B t ω i) P

/-- **A Brownian motion in `ℝᵈ`**: pre-Brownian with almost surely continuous paths. -/
structure IsBrownianVec (B : ℝ≥0 → Ω → EuclideanSpace ℝ ι) (P : Measure Ω) : Prop
    extends IsPreBrownianVec B P where
  cont : ∀ᵐ ω ∂P, Continuous fun t => B t ω

/-- The product Gaussian on `EuclideanSpace ℝ ι` with variance `v` in every coordinate. -/
noncomputable def gaussianVec (ι : Type*) [Fintype ι] (v : ℝ≥0) : Measure (EuclideanSpace ℝ ι) :=
  (Measure.pi fun _ : ι => gaussianReal 0 v).map (WithLp.toLp 2)

instance (v : ℝ≥0) : IsProbabilityMeasure (gaussianVec ι v) :=
  Measure.isProbabilityMeasure_map (WithLp.measurable_toLp 2 _).aemeasurable

/-- The characteristic function of the product Gaussian: `e^{−v‖ξ‖²/2}`. -/
theorem charFun_gaussianVec (v : ℝ≥0) (ξ : EuclideanSpace ℝ ι) :
    charFun (gaussianVec ι v) ξ = Complex.exp (-(v : ℝ) * ‖ξ‖ ^ 2 / 2) := by
  rw [gaussianVec, charFun_pi]
  simp_rw [charFun_gaussianReal, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub, ← Complex.exp_sum,
    ← Complex.ofReal_pow, EuclideanSpace.real_norm_sq_eq]
  congr 1
  push_cast
  simp [Finset.mul_sum, Finset.sum_div, neg_div]

/-- The product Gaussian of positive variance is absolutely continuous with respect to Lebesgue
measure. -/
theorem gaussianVec_absolutelyContinuous {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianVec ι v ≪ (volume : Measure (EuclideanSpace ℝ ι)) := by
  have hpi : (Measure.pi fun _ : ι => gaussianReal 0 v) ≪ Measure.pi fun _ : ι => (volume : Measure ℝ) :=
    Measure.pi_absolutelyContinuous_pi fun _ => gaussianReal_absolutelyContinuous 0 hv
  rw [gaussianVec, ← (PiLp.volume_preserving_toLp (ι := ι)).map_eq]
  exact hpi.map (WithLp.measurable_toLp 2 _)

omit [Fintype ι] in
theorem measurable_coord (i : ι) : Measurable fun x : EuclideanSpace ℝ ι => x i :=
  (measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)

namespace IsPreBrownianVec

variable {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} (hB : IsPreBrownianVec B P)
include hB

/-- Almost surely `B 0 = 0`. -/
theorem eval_zero_ae_eq_zero : ∀ᵐ ω ∂P, B 0 ω = 0 := by
  have h : ∀ᵐ ω ∂P, ∀ i, B 0 ω i = 0 := ae_all_iff.mpr fun i => (hB.coord i).eval_zero_ae_eq_zero
  filter_upwards [h] with ω hω
  ext i
  exact hω i

/-- `B t` has the product Gaussian law. -/
theorem hasLaw_eval (hBm : ∀ t, Measurable (B t)) (t : ℝ≥0) :
    HasLaw (B t) (gaussianVec ι t) P where
  aemeasurable := (hBm t).aemeasurable
  map_eq := by
    have hcoord : iIndepFun (fun i ω => B t ω i) P :=
      hB.iIndep.comp (fun _ p => p t) fun _ => measurable_pi_apply t
    have hmap := hcoord.map_fun_eq_pi_map fun i => ((measurable_coord i).comp (hBm t)).aemeasurable
    have hlaw : ∀ i, P.map (fun ω => B t ω i) = gaussianReal 0 t := fun i =>
      ((hB.coord i).hasLaw_eval t).map_eq
    simp only [Function.comp_def] at hmap
    have hmap' : P.map (fun ω i => B t ω i) = Measure.pi fun _ : ι => gaussianReal 0 t := by
      rw [hmap]
      congr 1
      funext i
      exact hlaw i
    have hF : Measurable fun ω (i : ι) => B t ω i :=
      measurable_pi_lambda _ fun i => (measurable_coord i).comp (hBm t)
    rw [gaussianVec, ← hmap', Measure.map_map (WithLp.measurable_toLp 2 _) hF]
    congr 1

omit [Fintype ι] in
/-- The process shifted by `t₀` is pre-Brownian. -/
theorem shift (t₀ : ℝ≥0) : IsPreBrownianVec (fun t ω => B (t₀ + t) ω - B t₀ ω) P where
  coord i := (hB.coord i).shift t₀
  iIndep :=
    hB.iIndep.comp (fun _ (p : ℝ≥0 → ℝ) => fun t => p (t₀ + t) - p t₀) fun _ =>
      measurable_pi_lambda _ fun t => (measurable_pi_apply (t₀ + t)).sub (measurable_pi_apply t₀)

/-- ★ **The weak Markov property**: the process shifted by `t₀` is independent of `B t₀`. -/
theorem indepFun_shift [IsProbabilityMeasure P] (hBm : ∀ t, Measurable (B t)) (t₀ : ℝ≥0) :
    IndepFun (B t₀) (fun ω t => B (t₀ + t) ω - B t₀ ω) P := by
  have hFm : ∀ i, Measurable fun ω (t : ℝ≥0) => B t ω i := fun i =>
    measurable_pi_lambda _ fun t => (measurable_coord i).comp (hBm t)
  have hpair : ∀ i, IndepFun (fun ω => (fun t : ℝ≥0 => B t ω i) t₀)
      (fun ω => (fun t => (fun t : ℝ≥0 => B t ω i) (t₀ + t) - (fun t : ℝ≥0 => B t ω i) t₀)) P := by
    intro i
    have h := ((hB.coord i).indepFun_shift t₀).comp measurable_id
      (measurable_pi_apply (⟨t₀, Set.mem_Iic.mpr le_rfl⟩ : Set.Iic t₀))
    exact h.symm
  have h := indepFun_pi_of_iIndepFun hB.iIndep hFm (x := fun _ (p : ℝ≥0 → ℝ) => p t₀)
    (y := fun _ (p : ℝ≥0 → ℝ) => fun t => p (t₀ + t) - p t₀) (fun _ => measurable_pi_apply t₀)
    (fun _ => measurable_pi_lambda _ fun t =>
      (measurable_pi_apply (t₀ + t)).sub (measurable_pi_apply t₀))
    hpair
  have h2 := h.comp (WithLp.measurable_toLp 2 (ι → ℝ))
    (measurable_pi_lambda (fun (g : ι → ℝ≥0 → ℝ) (t : ℝ≥0) => WithLp.toLp 2 fun i => g i t)
      fun t => (WithLp.measurable_toLp 2 _).comp
        (measurable_pi_lambda _ fun i => (measurable_pi_apply t).comp (measurable_pi_apply i)))
  refine h2.congr (Filter.EventuallyEq.of_eq (funext fun ω => rfl))
    (Filter.EventuallyEq.of_eq (funext fun ω => funext fun t => ?_))
  ext i
  rfl

end IsPreBrownianVec

/-- Jointly independent real Brownian coordinates form a Brownian motion in `ℝᵈ`. -/
theorem IsBrownianVec.of_coord {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι}
    (hcoord : ∀ i, IsBrownianReal (fun t ω => B t ω i) P)
    (hind : iIndepFun (fun i ω (t : ℝ≥0) => B t ω i) P) : IsBrownianVec B P where
  coord i := (hcoord i).toIsPreBrownianReal
  iIndep := hind
  cont := by
    have h : ∀ᵐ ω ∂P, ∀ i, Continuous fun t => B t ω i :=
      ae_all_iff.mpr fun i => (hcoord i).cont
    filter_upwards [h] with ω hω
    have : (fun t => B t ω) = fun t => WithLp.toLp 2 (fun i => B t ω i) := by
      funext t
      rfl
    rw [this]
    exact (PiLp.continuous_toLp (p := 2) (β := fun _ : ι => ℝ)).comp (continuous_pi hω)

end ProbabilityTheory
