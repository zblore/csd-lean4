/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Tests.Witnesses.IIDSampling
public import CsdLean4.Tests.Examples

/-!
# WS-C witness: the honest LF1 repeated-preparation model, fully concrete

**Category:** Special (validation-hardening witness suite,
`specs/validation-hardening-plan.md` WS-C).

`Tests/Examples.lean`'s LF1 smoke test constructs the concrete coin-toss
`OnticSetup` but takes the `TrialModel` abstractly, recording: "constructing
the honest i.i.d. product on `ℕ → Bool` is Mathlib-substantial and orthogonal
to the LF1 API check." The Mathlib machinery has since landed upstream
(`Measure.infinitePi` + `ProbabilityTheory.iIndepFun_infinitePi`), and
`Witnesses/IIDSampling.lean` wires it to the LF1 interface once for all
setups. This module instantiates it on the coin:

* `coinTrialModel` — the **explicit** trial model on `Ω = ℕ → Bool`: infinite
  product of the coin's own preparation law, coordinate-evaluation trials.
  Every `TrialModel` field is proved, none posited.
* `headsOutcome_weightReal` — the outcome weight is **`1/2`**, computed from
  the Liouville volumes via the production `weight_eq_prepEvent_div`.
* `coin_witness_nontrivial` — nontriviality: the weight is neither `0` nor
  `1`, so the convergence target is not a degenerate certainty; and the
  sample space genuinely varies (both outcomes carry positive weight).
* `coin_frequency_convergence` — **`LF1_main_theorem_ae` fired on the fully
  concrete model with zero abstract hypotheses**: empirical heads-frequencies
  converge a.s. to `1/2`.

**Anti-duplication scope.** `coinSetup`/`headsOutcome` are reused from
`Tests/Examples.lean` (not rebuilt); LF1 is applied through
`iidTrialModel_frequency_convergence`, not re-proved.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter

namespace CSD
namespace Tests
namespace Witnesses

open CSD.Tests.Examples.LF1Coin

/-- **The honest, fully concrete LF1 trial model on the coin.** Sample space
`ℕ → Bool`, law = the infinite product of the coin's preparation measure,
`n`-th trial = `n`-th coordinate. Discharges the `Tests/Examples.lean` caveat
that the `TrialModel` "stays abstract". -/
noncomputable def coinTrialModel : coinSetup.TrialModel (ℕ → Bool) :=
  iidTrialModel coinSetup

/-- The heads pre-event is `{true}` (identity flow, so the pullback is the
region itself). -/
theorem headsOutcome_preEvent :
    (headsOutcome.preEvent (S := coinSetup)) = {true} := rfl

/-- The coin's Liouville measure of the heads event is `1` (the `dirac true`
summand fires, the `dirac false` summand misses). -/
theorem μ_coin_heads : (μ_coin : Measure Bool) {true} = 1 := by
  show (Measure.dirac true + Measure.dirac false) {true} = 1
  rw [Measure.add_apply, Measure.dirac_apply' _ (by trivial),
    Measure.dirac_apply' _ (by trivial)]
  simp

/-- **The heads weight is `1/2`**, computed from the ontic volumes via the
production volume-interpretation lemma `weight_eq_prepEvent_div`:
`weight = μL(Ω0 ∩ Φ⁻¹{true}) / μL(Ω0) = 1/2`. -/
theorem headsOutcome_weight :
    headsOutcome.weight (S := coinSetup) = 1 / 2 := by
  rw [CSD.LF1.OnticSetup.OutcomeRegion.weight_eq_prepEvent_div]
  show (μ_coin : Measure Bool) (Set.univ ∩ headsOutcome.preEvent (S := coinSetup))
      / (μ_coin : Measure Bool) Set.univ = 1 / 2
  rw [Set.univ_inter, headsOutcome_preEvent, μ_coin_heads, μ_coin_univ]

/-- The heads weight, as the real number `1/2`. -/
theorem headsOutcome_weightReal :
    headsOutcome.weightReal (S := coinSetup) = 1 / 2 := by
  rw [CSD.LF1.OnticSetup.OutcomeRegion.weightReal, headsOutcome_weight]
  simp

/-- **Nontriviality.** The witness outcome is neither impossible nor certain:
the convergence statement below has a genuinely stochastic target, not a
degenerate `0`/`1` limit realisable by a constant model. -/
theorem coin_witness_nontrivial :
    headsOutcome.weightReal (S := coinSetup) ≠ 0
      ∧ headsOutcome.weightReal (S := coinSetup) ≠ 1 := by
  rw [headsOutcome_weightReal]
  norm_num

/-- **WS-C headline: LF1 on a fully concrete model, no abstract hypotheses.**
Empirical heads-frequencies of the honest i.i.d. coin model converge almost
surely to `1/2`. Every ingredient is explicit: the ontic setup
(`Tests/Examples.lean`'s `coinSetup`), the trial model (`coinTrialModel`,
built on `Measure.infinitePi`), the independence (a Mathlib theorem via
`iidTrialModel_hindep`), and the limit (`headsOutcome_weightReal`). -/
theorem coin_frequency_convergence :
    ∀ᵐ ω ∂ coinTrialModel.trialMeasure,
      Tendsto
        (fun n : ℕ => coinTrialModel.empiricalFreq (S := coinSetup) headsOutcome n ω)
        atTop
        (nhds (1 / 2 : ℝ)) := by
  have h := iidTrialModel_frequency_convergence coinSetup headsOutcome
  rw [headsOutcome_weightReal] at h
  exact h

end Witnesses
end Tests
end CSD
