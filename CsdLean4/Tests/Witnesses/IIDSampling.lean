/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF1.MainTheorem
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Witness infrastructure: the honest i.i.d. trial model

**Category:** Special (validation-hardening witness suite,
`specs/validation-hardening-plan.md` WS-C shared infrastructure).

The LF1 repeated-preparation theorems (`LF1_main_theorem_ae`,
`freq_tendsto_of_iid`) take their trials abstractly: any `TrialModel` (or any
sample family) with the right law and pairwise-independent indicators. Until
now every in-tree consumer either carried those hypotheses abstractly
(`Tests/Examples.lean`'s coin smoke test) or received them from a caller. This
module supplies the **honest inhabitant**: the infinite product measure
`Measure.infinitePi` on `ℕ → σ` with coordinate-evaluation trials, whose law
and independence facts are Mathlib theorems (`measurePreserving_eval_infinitePi`,
`ProbabilityTheory.iIndepFun_infinitePi`), not assumptions.

`iidTrialModel` builds the model for **every** `OnticSetup`, and
`iidTrialModel_frequency_convergence` fires `LF1_main_theorem_ae` on it with
**no abstract hypotheses left**: the caller supplies an ontic setup and an
outcome region, nothing else. This discharges the standing Examples caveat
("constructing the honest i.i.d. product on `ℕ → Bool` is Mathlib-substantial")
— the Mathlib machinery landed upstream, so the construction is now a wiring
job, done here once for all setups.

**Anti-duplication scope.** Nothing here restates a production theorem: the
LF1 chain is *applied* (`LF1_main_theorem_ae` cited as-is), and the law /
independence content is *imported* from Mathlib. The only new content is the
glue identifying the LF1 hypothesis shapes with the Mathlib product-measure
facts. Consumers: `Witnesses/LF1Trial.lean` (WS-C), `Witnesses/Dynamics.lean`
(WS-J), `Witnesses/SingletBell.lean` (WS-E/H).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter

namespace CSD
namespace Tests
namespace Witnesses

variable {σ : Type*} [MeasurableSpace σ]

/-! ## Generic layer: coordinate trials on the infinite product -/

/-- Any measurable per-trial statistic of coordinate evaluations on the
infinite product `Measure.infinitePi (fun _ : ℕ => μ)` is pairwise
independent across trials — the exact `hindep` shape the LF1 theorems
consume. Wraps `ProbabilityTheory.iIndepFun_infinitePi` (coordinates are
jointly independent) with `IndepFun.comp` (independence survives measurable
post-composition). -/
theorem pairwise_indepFun_comp_eval (μ : Measure σ) [IsProbabilityMeasure μ]
    (f : ℕ → σ → ℝ) (hf : ∀ n, Measurable (f n)) :
    Pairwise
      (Function.onFun
        (fun g h : (ℕ → σ) → ℝ => IndepFun g h (Measure.infinitePi fun _ : ℕ => μ))
        (fun n => fun ω : ℕ → σ => f n (ω n))) := by
  intro i j hij
  have hIndep : iIndepFun (fun n (ω : ℕ → σ) => ω n)
      (Measure.infinitePi fun _ : ℕ => μ) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  exact (hIndep.indepFun hij).comp (hf i) (hf j)

/-! ## The honest trial model for every `OnticSetup` -/

variable [Nonempty σ]

/-- **The honest i.i.d. trial model, for every ontic setup.** Sample space
`ℕ → σ`, law the infinite product of the setup's own preparation measure
`S.prepMeasure`, `n`-th trial the `n`-th coordinate. The `hLaw` field is
Mathlib's `measurePreserving_eval_infinitePi` — a theorem, not a posit. This
is the inhabitant whose absence `Tests/Examples.lean` recorded as the LF1
smoke-test limitation. -/
noncomputable def iidTrialModel (S : CSD.LF1.OnticSetup σ) :
    S.TrialModel (ℕ → σ) where
  P := ⟨Measure.infinitePi fun _ : ℕ =>
          ((S.prepMeasure : ProbabilityMeasure σ) : Measure σ), inferInstance⟩
  X := fun n ω => ω n
  hX_measurable := fun n => measurable_pi_apply n
  hLaw := fun n => (measurePreserving_eval_infinitePi _ n).map_eq

/-- The outcome indicator of the honest model is a fixed measurable statistic
of the `n`-th coordinate (the shape `pairwise_indepFun_comp_eval` consumes). -/
theorem iidTrialModel_indicatorRV_eq (S : CSD.LF1.OnticSetup σ)
    (O : S.OutcomeRegion) (n : ℕ) :
    (iidTrialModel S).indicatorRV (S := S) O n
      = fun ω : ℕ → σ =>
          Set.indicator (O.preEvent (S := S)) (fun _ => (1 : ℝ)) (ω n) := by
  funext ω
  simp only [CSD.LF1.OnticSetup.TrialModel.indicatorRV,
    CSD.LF1.OnticSetup.TrialModel.trialEvent, iidTrialModel]
  by_cases h : ω n ∈ O.preEvent (S := S)
  · rw [Set.indicator_of_mem
        (show ω ∈ (fun ω' : ℕ → σ => ω' n) ⁻¹' O.preEvent (S := S) from h),
      Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem
        (show ω ∉ (fun ω' : ℕ → σ => ω' n) ⁻¹' O.preEvent (S := S) from h),
      Set.indicator_of_notMem h]

/-- **The LF1 independence hypothesis is a theorem on the honest model.**
Pairwise independence of the outcome indicators across trials, discharged by
Mathlib's product-measure independence — the hypothesis every LF1 caller has
had to carry abstractly until now. -/
theorem iidTrialModel_hindep (S : CSD.LF1.OnticSetup σ) (O : S.OutcomeRegion) :
    Pairwise
      (Function.onFun
        (fun f g : (ℕ → σ) → ℝ => IndepFun f g ((iidTrialModel S).trialMeasure))
        (fun n => (iidTrialModel S).indicatorRV (S := S) O n)) := by
  have h := pairwise_indepFun_comp_eval
    ((S.prepMeasure : ProbabilityMeasure σ) : Measure σ)
    (fun _ => Set.indicator (O.preEvent (S := S)) (fun _ => (1 : ℝ)))
    (fun _ => measurable_const.indicator (O.measurable_preEvent (S := S)))
  intro i j hij
  show IndepFun ((iidTrialModel S).indicatorRV (S := S) O i)
    ((iidTrialModel S).indicatorRV (S := S) O j) ((iidTrialModel S).trialMeasure)
  rw [iidTrialModel_indicatorRV_eq S O i, iidTrialModel_indicatorRV_eq S O j]
  -- The trial measure of the honest model IS the infinite product (definitional).
  show IndepFun _ _
    (Measure.infinitePi fun _ : ℕ => ((S.prepMeasure : ProbabilityMeasure σ) : Measure σ))
  exact h hij

/-- **LF1 with no abstract hypotheses left.** On the honest i.i.d. trial
model, empirical frequencies converge almost surely to the ontic volume
weight, for **every** ontic setup and outcome region. `LF1_main_theorem_ae`
is cited, not re-proved; the independence hypothesis is discharged by
`iidTrialModel_hindep`. -/
theorem iidTrialModel_frequency_convergence
    (S : CSD.LF1.OnticSetup σ) (O : S.OutcomeRegion) :
    ∀ᵐ ω ∂ (iidTrialModel S).trialMeasure,
      Tendsto
        (fun n : ℕ => (iidTrialModel S).empiricalFreq (S := S) O n ω)
        atTop
        (nhds (O.weightReal (S := S))) :=
  CSD.LF1.OnticSetup.LF1_main_theorem_ae S (iidTrialModel S) O (iidTrialModel_hindep S O)

end Witnesses
end Tests
end CSD
