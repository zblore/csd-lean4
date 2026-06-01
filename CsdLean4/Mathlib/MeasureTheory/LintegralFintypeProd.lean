import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Mathlib upstream candidate: Tonelli for a product over a finite index (`lintegral`)

The `lintegral` (`ℝ≥0∞`-valued) analogue of `MeasureTheory.integral_fintype_prod_eq_prod`:
on a finite product of `σ`-finite measure spaces, the lower integral of a product
of single-coordinate functions is the product of the lower integrals,

```
∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i).
```

Mathlib has the Bochner version (`Integral/Pi.lean`) but no `lintegral` form. The
proof mirrors the Bochner one: induct on `Fin n` via `measurePreserving_piFinSuccAbove`
+ `lintegral_prod_mul`, then transfer to a general finite index by `equivFin` +
`measurePreserving_piCongrLeft`.

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib upstream candidate).

## Provenance

Needed for the general-N Duistermaat–Heckman / Dirichlet computation
(`CsdLean4/LF4/MomentRatioUniformN.lean`, Slice D.5): the joint `Exp(1/2)^{⊗N}`
density is a product of single-coordinate densities, and exposing it requires this
lower-integral Fubini fact (and the `pi`-`withDensity` bridge built on it). See
`specs/general-n-dh-plan.md` Slice D.5a.

## Tags

lintegral, Fubini, Tonelli, product measure, pi
-/

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} [Fintype ι]

/-- **Tonelli for a product over `Fin n` (`lintegral`).** The lower integral of a
product of single-coordinate functions over `Measure.pi` is the product of the
lower integrals. Proved by induction on `n` (`measurePreserving_piFinSuccAbove`
splits off the `0`-th coordinate; `lintegral_prod_mul` factors the resulting
product). -/
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      -- Split off coordinate 0 via the measure-preserving equiv `ℝ^{n+1} ≃ ℝ × ℝ^n`.
      rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
        (MeasurableEquiv.measurableEmbedding _)]
      simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
        Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      -- Now: ∫⁻ (x : E 0 × …), f 0 x.1 * ∏ i, f i.succ (x.2 i). Factor by Tonelli.
      have hmul := lintegral_prod_mul (μ := μ 0) (ν := Measure.pi fun j => μ j.succ)
        (f := f 0) (g := fun y : (j : Fin n) → E j.succ => ∏ i, f i.succ (y i))
        (hf 0).aemeasurable
        ((Finset.measurable_prod _ (fun i _ => (hf _).comp (measurable_pi_apply i))).aemeasurable)
      simp only at hmul
      -- `hmul : LHS = (∫⁻ f 0) * ∫⁻ ∏ f i.succ`; close by IH + `Fin.prod_univ_succ`.
      rw [n_ih (fun i => f i.succ) (fun i => hf _)] at hmul
      exact hmul

/-- **Tonelli for a product over a finite index (`lintegral`).** The general-index
version, transferred from `lintegral_fin_nat_prod_eq_prod` via `equivFin`. -/
theorem lintegral_fintype_prod_eq_prod {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod_eq_prod (fun i => f (e i)) (fun i => hf _)

/-- **The `pi`-`withDensity` bridge.** A finite product of measures, each given a
density, is the product measure with the product density:
`Measure.pi (fun i => (μ i).withDensity (g i))
  = (Measure.pi μ).withDensity (fun x => ∏ i, g i (x i))`.
The `pi` analogue of `MeasureTheory.prod_withDensity`. Proved by `Measure.pi_eq`
on rectangles, using `lintegral_fintype_prod_eq_prod` (D.5a) to factor the
product-density integral over the rectangle. -/
theorem pi_withDensity {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} (μ : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (g : (i : ι) → E i → ℝ≥0∞) (hg : ∀ i, Measurable (g i))
    [∀ i, SigmaFinite ((μ i).withDensity (g i))] :
    Measure.pi (fun i => (μ i).withDensity (g i))
      = (Measure.pi μ).withDensity (fun x => ∏ i, g i (x i)) := by
  refine Measure.pi_eq (μ := fun i => (μ i).withDensity (g i)) (fun s hs => ?_)
  -- LHS on the rectangle: ∏ᵢ ((μ i).withDensity gᵢ) (s i) = ∏ᵢ ∫⁻_{sᵢ} gᵢ.
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  -- Set-integral over the rectangle = ∫⁻ of the indicator-times-density.
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
  -- The integrand `(pi s).indicator (∏ g)` equals `∏ᵢ (sᵢ.indicator gᵢ)(xᵢ)`.
  have hint : ((Set.univ.pi s).indicator (fun x => ∏ i, g i (x i)))
      = fun x => ∏ i, (s i).indicator (g i) (x i) := by
    classical
    funext x
    rw [Set.indicator_apply]
    split_ifs with hx
    · refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [Set.indicator_of_mem (Set.mem_univ_pi.mp hx i)]
    · rw [Set.mem_univ_pi, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i)
        (Set.indicator_of_notMem hi _)).symm
  rw [hint, lintegral_fintype_prod_eq_prod (μ := μ)
    (fun i => (s i).indicator (g i)) (fun i => (hg i).indicator (hs i))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

end MeasureTheory
