import CsdLean4.LF1.MainTheorem
import CsdLean4.LF2.BornWrapper
import CsdLean4.LF2.Interface
import CsdLean4.LF3.Interface
import CsdLean4.LF3.PurePreparation

/-!
# Examples and API smoke tests

**Category:** Special (cross-layer worked examples and API-shape smoke tests).

Concrete worked examples and type-level smoke tests for the LF1, LF2,
LF3 exported theorems. Build-fails if a signature changes incompatibly,
catching API drift without requiring axiom inspection.

## What is and is not here

**LF1.** A concrete `OnticSetup Bool` instantiates the abstract layer
against a coin-toss state space (two outcomes, deterministic identity
flow, uniform Liouville measure). The `TrialModel` is taken as a
parameter rather than constructed; building an honest i.i.d. infinite
product on `ℕ → Bool` is Mathlib-substantial work that does not change
on the LF1 side and would only obscure the API check.

**LF2.** Concrete edge cases for `born_quadratic`: orthogonal vectors
give probability 0, identical vectors give probability 1. These are
worked calculations on `EuclideanSpace ℂ (Fin 2)` using
`EuclideanSpace.single` basis vectors.

**LF3.** API smoke for `LF3_singlet_frequency_convergence` and its
Born / bra-ket variants. A genuinely concrete LF3 example requires a
constructed `SectorData` plus a structural `PureSingletPreparation`,
which is LF4 territory (see the "What is needed" note at the end of
this file).

Three-category posture for this module:
- **Proved internally.** All `example`s, all concrete LF2 edge-case
  computations.
- **Imported from upstream.** All theorem applications route through
  `CsdLean4` exports.
- **Axiomatised at an explicit boundary.** None new. The audit lives
  in `CsdLean4/Tests/AxiomAudit.lean`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace CSD.Tests.Examples

/-! ## LF1: coin toss

A concrete two-outcome deterministic system. -/

namespace LF1Coin

/-- Discrete `MeasurableSpace` on `Bool` (every subset measurable). -/
instance : MeasurableSpace Bool := ⊤

/-- A Liouville-style measure on `Bool`: unit weight on each outcome
    (total mass `2`). The corpus uses the normalised conditional measure
    `prepMeasure` internally, so the absolute scale of `μL` does not
    matter here, only its relative weights. -/
noncomputable def μ_coin : FiniteMeasure Bool :=
  ⟨Measure.dirac true + Measure.dirac false, inferInstance⟩

/-- Total mass on the universal set is `2`. -/
lemma μ_coin_univ : (μ_coin : Measure Bool) Set.univ = 2 := by
  show (Measure.dirac true + Measure.dirac false) Set.univ = 2
  rw [Measure.add_apply, Measure.dirac_apply' _ MeasurableSet.univ,
      Measure.dirac_apply' _ MeasurableSet.univ]
  simp; norm_num

/-- The concrete coin-toss `OnticSetup`. Two outcomes, identity flow
    (the deterministic content is: outcome is fully determined by the
    initial microstate, no time evolution needed), full preparation
    region, uniform measure. -/
noncomputable def coinSetup : CSD.LF1.OnticSetup Bool where
  μL          := μ_coin
  Φ           := id
  hΦ_pres     := MeasurePreserving.id _
  Ω0          := Set.univ
  hΩ0_meas    := MeasurableSet.univ
  hΩ0_nonzero := by rw [μ_coin_univ]; exact two_ne_zero

/-- The "heads" outcome region. -/
noncomputable def headsOutcome : coinSetup.OutcomeRegion where
  Ω       := {true}
  hΩ_meas := trivial

/-- **Smoke test.** Given a `TrialModel` over the coin setup and
    pairwise independence of the heads-indicator across trials, LF1's
    main theorem applies and the empirical frequency converges almost
    surely to the real-valued weight of the heads outcome. The
    `TrialModel` itself stays abstract: constructing the honest i.i.d.
    product on `ℕ → Bool` is Mathlib-substantial and orthogonal to the
    LF1 API check. -/
example
    {Ω : Type*} [MeasurableSpace Ω]
    (T : coinSetup.TrialModel Ω)
    (hindep :
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => IndepFun f g T.trialMeasure)
          (fun n => T.indicatorRV (S := coinSetup) headsOutcome n))) :
    ∀ᵐ ω ∂ T.trialMeasure,
      Tendsto
        (fun n : ℕ => T.empiricalFreq (S := coinSetup) headsOutcome n ω)
        atTop
        (nhds headsOutcome.weightReal) :=
  T.main_theorem_ae (S := coinSetup) headsOutcome hindep

end LF1Coin

/-! ## LF2: Born quadratic form, edge cases

Three checks on `born_quadratic`:
- **Smoke:** the theorem applies to arbitrary unit vectors.
- **Orthogonal edge:** `|⟨e_0, e_1⟩|² = 0`.
- **Same-state edge:** `|⟨e_0, e_0⟩|² = 1`. -/

namespace LF2Born

open CSD.LF2

/-- Smoke test: born_quadratic applies to any two unit vectors. -/
example {N : ℕ} (ψ φ : EuclideanSpace ℂ (Fin N))
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    traceForm (rankOneDensity ψ hψ) (rankOneEffect φ hφ) = ‖inner ℂ ψ φ‖ ^ 2 :=
  born_quadratic ψ φ hψ hφ

/-- The first basis vector `|0⟩ = e_0` in `EuclideanSpace ℂ (Fin 2)`,
    using `EuclideanSpace.single`. -/
noncomputable def e0 : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 1

/-- The second basis vector `|1⟩ = e_1`. -/
noncomputable def e1 : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 1 1

lemma e0_unit : ‖e0‖ = 1 := by
  simp [e0, PiLp.norm_single]

lemma e1_unit : ‖e1‖ = 1 := by
  simp [e1, PiLp.norm_single]

/-- Inner product of distinct standard basis vectors is `0`. -/
lemma inner_e0_e1 : inner ℂ e0 e1 = (0 : ℂ) := by
  simp [e0, e1, EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.single]

/-- Inner product of a standard basis vector with itself is `1`. -/
lemma inner_e0_e0 : inner ℂ e0 e0 = (1 : ℂ) := by
  simp [e0, EuclideanSpace.single]

/-- **Orthogonal edge case.** The Born form gives `0` between distinct
    standard basis vectors. -/
example : traceForm (rankOneDensity e0 e0_unit) (rankOneEffect e1 e1_unit) = 0 := by
  rw [born_quadratic, inner_e0_e1]
  simp

/-- **Same-state edge case.** The Born form gives `1` between a vector
    and itself. -/
example : traceForm (rankOneDensity e0 e0_unit) (rankOneEffect e0 e0_unit) = 1 := by
  rw [born_quadratic, inner_e0_e0]
  simp

end LF2Born

/-! ## LF3: chain capstone API smoke

Type-level check that the three `LF3_singlet_frequency_convergence*`
capstones can be applied. A genuinely concrete LF3 example requires
constructing the underlying `SectorData` and a structural
`PureSingletPreparation`, both of which are LF4 work. The smoke tests
here verify only the API surface. -/

namespace LF3Chain

open CSD.LF3

/-- **Smoke: pre-Born chain capstone.** Given a sector structure, a
    trial model, a measurement context, a `PureSingletPreparation`, and
    pairwise independence, the LF3 chain capstone produces convergence
    of empirical frequencies to `P_st`. -/
example
    {SigmaSpace P G : Type*}
    [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
    [MeasurableSpace P] [Group G]
    (D : CSD.LF2.SectorData SigmaSpace P G)
    {Ω : Type*} [MeasurableSpace Ω]
    (T : D.toOntic.TrialModel Ω)
    (ctx : MeasurementContext)
    (prep : PureSingletPreparation D ctx)
    (hindep : ∀ s t,
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => IndepFun f g T.trialMeasure)
          (fun n => T.indicatorRV (S := D.toOntic) (prep.O_region s t) n))) :
    ∀ s t, ∀ᵐ ω ∂ T.trialMeasure,
      Tendsto
        (fun n : ℕ => T.empiricalFreq (S := D.toOntic) (prep.O_region s t) n ω)
        atTop
        (nhds (P_st ctx.a ctx.b s t)) :=
  LF3_singlet_frequency_convergence D T ctx prep hindep

/-- **Smoke: Born-form chain capstone.** Same as above, landing on
    `‖cAmp s t (a, b)‖²` rather than `P_st`. -/
example
    {SigmaSpace P G : Type*}
    [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
    [MeasurableSpace P] [Group G]
    (D : CSD.LF2.SectorData SigmaSpace P G)
    {Ω : Type*} [MeasurableSpace Ω]
    (T : D.toOntic.TrialModel Ω)
    (ctx : MeasurementContext)
    (prep : PureSingletPreparation D ctx)
    (hindep : ∀ s t,
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => IndepFun f g T.trialMeasure)
          (fun n => T.indicatorRV (S := D.toOntic) (prep.O_region s t) n))) :
    ∀ s t, ∀ᵐ ω ∂ T.trialMeasure,
      Tendsto
        (fun n : ℕ => T.empiricalFreq (S := D.toOntic) (prep.O_region s t) n ω)
        atTop
        (nhds (‖cAmp ctx.a ctx.b s t‖ ^ 2)) :=
  LF3_singlet_frequency_convergence_born D T ctx prep hindep

end LF3Chain

end CSD.Tests.Examples
