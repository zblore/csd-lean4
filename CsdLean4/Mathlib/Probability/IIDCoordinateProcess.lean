import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

/-!
# Mathlib upstream candidate: the canonical i.i.d. coordinate process

For a probability measure `μ` on `α`, the coordinate evaluations on the
countable product `(ι → α, Measure.infinitePi (fun _ => μ))` form a canonical
i.i.d. process with common law `μ`. Mathlib's `Measure.infinitePi` provides the
product measure, `Measure.infinitePi_map_eval` the marginal law, and
`ProbabilityTheory.iIndepFun_infinitePi` joint independence; this file adds the
two glue lemmas a strong-law consumer needs:

* `ProbabilityTheory.iIndepFun_eval_infinitePi` — the coordinate evaluations of
  a constant-family `infinitePi` are jointly independent (the `X i = id`
  specialisation of `iIndepFun_infinitePi`);
* `ProbabilityTheory.iIndepFun.pairwise_indepFun_indicator_preimage` — from
  joint independence of a process, the per-trial outcome-region indicators
  `Set.indicator (X n ⁻¹' S i) 1` are pairwise independent, for any family of
  measurable regions `S` (composition with the measurable indicator via
  `IndepFun.comp`).

Together with `Measure.infinitePi_map_eval` these inhabit the standard
i.i.d.-trial hypothesis bundle `(Ω, Pr, X, hX, hlaw, hindep)` of SLLN-style
frequency theorems.

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib upstream candidate).

## Provenance

Needed for the CSD trial-witness tranche (`CsdLean4/LF4/TrialWitness.lean`):
the volume-frequency capstones (`born_frequency_convergence_N_uncond`,
`measurement_flow_born_frequency`, …) quantify over an abstract i.i.d. trial
bundle; the canonical coordinate process instantiates it, so the capstones'
hypothesis sets are Lean-inhabited rather than merely classically satisfiable.

## Tags

independence, product measure, iid, indicator, coordinate process
-/

open MeasureTheory

/-- The indicator of a preimage `X ⁻¹' s` with constant value `c` is the
indicator of `s` composed with `X`. Function-level form of
`Set.indicator_comp_right` for constant-valued indicators. -/
theorem Set.indicator_const_preimage_comp {Ω α M : Type*} [Zero M]
    (X : Ω → α) (s : Set α) (c : M) :
    Set.indicator (X ⁻¹' s) (fun _ => c) = Set.indicator s (fun _ => c) ∘ X :=
  funext fun _ => Set.indicator_comp_right (g := fun _ => c) X

namespace ProbabilityTheory

/-- The coordinate evaluations on a constant-family infinite product
`Measure.infinitePi (fun _ => μ)` are jointly independent. The `X i = id`
specialisation of `iIndepFun_infinitePi`. -/
theorem iIndepFun_eval_infinitePi {ι α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] :
    iIndepFun (fun (n : ι) (ω : ι → α) => ω n)
      (Measure.infinitePi (fun _ : ι => μ)) :=
  iIndepFun_infinitePi (𝓧 := fun _ : ι => α) (X := fun _ => id)
    (fun _ => measurable_id)

/-- **Indicator independence from joint independence.** If the process `X` is
jointly independent, then for every family of measurable outcome regions
`S : ι → Set α`, the per-trial indicators of `X n ⁻¹' S i` are pairwise
independent — the exact hypothesis shape consumed by SLLN-style frequency
theorems. No measurability of `X` is needed: pairwise independence composes
with the measurable indicator (`IndepFun.comp`). -/
theorem iIndepFun.pairwise_indepFun_indicator_preimage
    {Ω α κ ι : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace α]
    {Pr : Measure Ω} {X : κ → Ω → α}
    (hXindep : iIndepFun X Pr)
    (S : ι → Set α) (hS : ∀ i, MeasurableSet (S i)) :
    ∀ i, Pairwise
      (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' S i) (fun _ => (1 : ℝ)))) := by
  intro i n m hnm
  show IndepFun (Set.indicator ((X n) ⁻¹' S i) (fun _ => (1 : ℝ)))
      (Set.indicator ((X m) ⁻¹' S i) (fun _ => (1 : ℝ))) Pr
  rw [Set.indicator_const_preimage_comp (X n) (S i) (1 : ℝ),
    Set.indicator_const_preimage_comp (X m) (S i) (1 : ℝ)]
  exact (hXindep.indepFun hnm).comp
    (measurable_const.indicator (hS i)) (measurable_const.indicator (hS i))

end ProbabilityTheory
