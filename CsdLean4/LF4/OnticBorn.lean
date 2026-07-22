/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF1.GeneralFrequency
import CsdLean4.LF2.BornWrapper
import CsdLean4.LF2.EffectGleason

/-!
# LF4: pure-state ontic Born rule as a frequency limit

**Category:** 3-Local.

Composes the law-agnostic frequency theorem `freq_tendsto_of_iid` (LF1) with the
operational Born derivation `pure_state_born_weights_of_certainty` (LF2, via the
Busch axiom) to obtain the **pure-state ontic Born rule**: empirical frequencies of
a measurement outcome converge almost surely to `|⟨ψ,φ⟩|²`.

## Posits and honest scope

The preparation law `μψ` is the **posited fibre measure** over the pure state `[ψ]`
(Paper A / Σ0, revised: pure-state preparation is the conditional measure on the
fibre, posited ontic structure, *not* an ambient `μL`-conditional). The theorem is
**conditional** on:

- `OP` + `h_certain` — operational consistency, the package being certain at `ψ`
  (Paper B Def 5.1; Born form then follows by the Busch/Gleason axiom);
- `h_bridge` — the eq-12 identification of the ontic outcome weight `(μψ O).toReal`
  with the operational weight `OP.p (rankOneEffect φ)`.

These are exactly Paper B's posits. The Born *form* `|⟨ψ,φ⟩|²` is **derived**
(`pure_state_born_weights_of_certainty`), not assumed.

**Non-vacuity.** Because `μψ` is a posited probability measure (the trial law),
*not* a `μL`-conditional on a `μL`-null fibre, the hypotheses are jointly
satisfiable. This repairs the inhabitability defect of the LF3
`PureSingletPreparation` bundle, whose `push_dirac`-via-`μL`-conditional form is
incompatible with the continuous measure bridge `π∗μL = c·μFS` (a single quantum
state's fibre is `μL`-null). See `LF4-todo §8`.
-/

open MeasureTheory ProbabilityTheory Set Filter

namespace CSD
namespace LF4

/-- **Pure-state ontic Born rule (conditional, non-vacuous).** For i.i.d. trials
with preparation law `μψ`, an outcome region `O` whose ontic weight equals the
operational Born weight (`h_bridge`), and an operational package `OP` certain at the
pure state `ψ`, the empirical frequencies converge almost surely to `|⟨ψ,φ⟩|²`. -/
theorem ontic_born_frequency
    {N : ℕ} (hN : 2 ≤ N)
    {SigmaSpace Ω : Type*} [MeasurableSpace SigmaSpace] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → SigmaSpace} (hX : ∀ n, Measurable (X n))
    {μψ : Measure SigmaSpace} (hlaw : ∀ n, Measure.map (X n) P = μψ)
    {O : Set SigmaSpace} (hO : MeasurableSet O)
    (hindep :
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g P)
          (fun n => Set.indicator (X n ⁻¹' O) (fun _ => (1 : ℝ)))))
    (OP : LF2.OperationalPackage N)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ‖ψ‖ = 1)
    (h_certain : OP.p (LF2.rankOneEffect ψ hψ) = 1)
    {φ : EuclideanSpace ℂ (Fin N)} (hφ : ‖φ‖ = 1)
    (h_bridge : (μψ O).toReal = OP.p (LF2.rankOneEffect φ hφ)) :
    ∀ᵐ ω ∂ P,
      Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator (X i ⁻¹' O) (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        atTop
        (nhds (‖inner ℂ ψ φ‖ ^ 2)) := by
  have hborn : OP.p (LF2.rankOneEffect φ hφ) = ‖inner ℂ ψ φ‖ ^ 2 :=
    LF2.pure_state_born_weights_of_certainty hN OP ψ hψ h_certain φ hφ
  have hfreq := LF1.freq_tendsto_of_iid hX hlaw hO hindep
  rwa [h_bridge, hborn] at hfreq

end LF4
end CSD
