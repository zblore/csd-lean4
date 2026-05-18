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

/-! ## LF2: Schrödinger cat

A two-state superposition `ψ = α|alive⟩ + β|dead⟩` where `|alive⟩ = e_0`
and `|dead⟩ = e_1`. The Born quadratic form gives `|α|²` for the alive
projector and `|β|²` for the dead projector — the canonical Born
probabilities for a single qubit in superposition.

This namespace adds the Schrödinger-cat scenario as a worked Born-form
example alongside the orthogonal / same-state edge cases above. Three
checks:

- **Smoke:** Born quadratic applies to any unit two-level superposition.
- **Equal-superposition norm:** `‖(|0⟩+|1⟩)/√2‖ = 1`.
- **Equal-superposition Born probabilities:** alive-prob = dead-prob = 1/2.
-/

namespace LF2Cat

open CSD.LF2 LF2Born

/-- **Smoke: Born form on an arbitrary unit superposition.**
    For any unit `ψ : EuclideanSpace ℂ (Fin 2)`, the alive-outcome
    Born probability is `‖⟨ψ, |alive⟩⟩‖²` and the dead-outcome Born
    probability is `‖⟨ψ, |dead⟩⟩‖²`. -/
example (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : ‖ψ‖ = 1) :
    traceForm (rankOneDensity ψ hψ) (rankOneEffect e0 e0_unit)
      = ‖inner ℂ ψ e0‖ ^ 2 :=
  born_quadratic ψ e0 hψ e0_unit

example (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : ‖ψ‖ = 1) :
    traceForm (rankOneDensity ψ hψ) (rankOneEffect e1 e1_unit)
      = ‖inner ℂ ψ e1‖ ^ 2 :=
  born_quadratic ψ e1 hψ e1_unit

/-! ### Equal-superposition cat: worked Born computation

`|cat⟩ = (|alive⟩ + |dead⟩) / √2` with `α := 1/√2` as the shared
coefficient. Demonstrates that the Born form lands on `‖α‖² = 1/2`
for both outcomes, using the orthogonal Pythagorean form
`‖α•e₀ + α•e₁‖² = ‖α•e₀‖² + ‖α•e₁‖²` (avoiding inner-product
expansion of the full norm-squared). -/

/-- Equal-superposition coefficient `α = 1/√2` cast to `ℂ`. -/
noncomputable def α : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ)

/-- The equal-superposition cat state. -/
noncomputable def catEqual : EuclideanSpace ℂ (Fin 2) := α • e0 + α • e1

/-- `(1/√2)² = 1/2` in `ℝ`. -/
lemma α_sq_real : ((1 / Real.sqrt 2 : ℝ))^2 = 1/2 := by
  rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- `‖α‖² = 1/2` in `ℂ`. -/
lemma α_norm_sq : ‖α‖^2 = 1/2 := by
  unfold α
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact α_sq_real

/-- `(starRingEnd ℂ) α = α` since `α` is real. -/
lemma α_star : (starRingEnd ℂ) α = α := by
  unfold α
  exact Complex.conj_ofReal _

/-- Symmetric companion to `inner_e0_e1`: inner product is conjugate
    symmetric, so swapping arguments preserves the zero value. -/
lemma inner_e1_e0 : inner ℂ e1 e0 = (0 : ℂ) := by
  rw [← inner_conj_symm, inner_e0_e1, map_zero]

/-- Inner product of `e₁` with itself is `1` (basis-vector unitarity). -/
lemma inner_e1_e1 : inner ℂ e1 e1 = (1 : ℂ) := by
  simp [e1, EuclideanSpace.single]

/-- The equal-superposition cat is unit-norm. Uses orthogonal
    Pythagorean: `‖α•e₀ + α•e₁‖² = ‖α‖² + ‖α‖² = 1/2 + 1/2 = 1`.
    Mathlib's Pythagorean lemma is stated in `mul_self` form, so this
    proof routes through `‖x‖ * ‖x‖` rather than `‖x‖^2`. -/
lemma catEqual_unit : ‖catEqual‖ = 1 := by
  have h_ortho : inner ℂ (α • e0) (α • e1) = (0 : ℂ) := by
    rw [inner_smul_left, inner_smul_right, inner_e0_e1]
    ring
  have h_mul : ‖catEqual‖ * ‖catEqual‖ = 1 := by
    show ‖α • e0 + α • e1‖ * ‖α • e0 + α • e1‖ = 1
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h_ortho,
        norm_smul, norm_smul, e0_unit, e1_unit, mul_one]
    have hα : ‖α‖ * ‖α‖ = 1/2 := by rw [← sq]; exact α_norm_sq
    linarith
  have h_nn : 0 ≤ ‖catEqual‖ := norm_nonneg _
  calc ‖catEqual‖
      = Real.sqrt (‖catEqual‖ * ‖catEqual‖) := (Real.sqrt_mul_self h_nn).symm
    _ = Real.sqrt 1 := by rw [h_mul]
    _ = 1 := Real.sqrt_one

/-- **Alive Born probability = 1/2** for the equal-superposition cat.
    The classic "either-or" outcome on a balanced superposition. -/
example : traceForm (rankOneDensity catEqual catEqual_unit)
                    (rankOneEffect e0 e0_unit) = 1/2 := by
  rw [born_quadratic]
  have h_inner : inner ℂ catEqual e0 = α := by
    show inner ℂ (α • e0 + α • e1) e0 = α
    rw [inner_add_left, inner_smul_left, inner_smul_left,
        inner_e0_e0, inner_e1_e0, mul_one, mul_zero, add_zero]
    exact α_star
  rw [h_inner]
  exact α_norm_sq

/-- **Dead Born probability = 1/2** for the equal-superposition cat. -/
example : traceForm (rankOneDensity catEqual catEqual_unit)
                    (rankOneEffect e1 e1_unit) = 1/2 := by
  rw [born_quadratic]
  have h_inner : inner ℂ catEqual e1 = α := by
    show inner ℂ (α • e0 + α • e1) e1 = α
    rw [inner_add_left, inner_smul_left, inner_smul_left,
        inner_e0_e1, inner_e1_e1, mul_zero, mul_one, zero_add]
    exact α_star
  rw [h_inner]
  exact α_norm_sq

/-! ### Parametric cat: cos(θ)|alive⟩ + sin(θ)|dead⟩

Generalises the equal-superposition cat to arbitrary angle `θ : ℝ`. The
Born probabilities are `cos²(θ)` for alive and `sin²(θ)` for dead, summing
to 1 by the Pythagorean trig identity. The equal-superposition case
corresponds to `θ = π/4`. -/

/-- Parametric cat coefficient `cos(θ) : ℂ`. -/
noncomputable def catCos (θ : ℝ) : ℂ := ((Real.cos θ : ℝ) : ℂ)

/-- Parametric cat coefficient `sin(θ) : ℂ`. -/
noncomputable def catSin (θ : ℝ) : ℂ := ((Real.sin θ : ℝ) : ℂ)

/-- Parametric cat state `cos(θ)|alive⟩ + sin(θ)|dead⟩`. -/
noncomputable def catParam (θ : ℝ) : EuclideanSpace ℂ (Fin 2) :=
  catCos θ • e0 + catSin θ • e1

/-- `‖cos(θ) : ℂ‖² = cos²(θ)`. -/
lemma catCos_norm_sq (θ : ℝ) : ‖catCos θ‖^2 = (Real.cos θ)^2 := by
  unfold catCos
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact sq_abs _

/-- `‖sin(θ) : ℂ‖² = sin²(θ)`. -/
lemma catSin_norm_sq (θ : ℝ) : ‖catSin θ‖^2 = (Real.sin θ)^2 := by
  unfold catSin
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact sq_abs _

/-- `(starRingEnd ℂ) (cos θ : ℂ) = (cos θ : ℂ)` since `cos θ` is real. -/
lemma catCos_star (θ : ℝ) : (starRingEnd ℂ) (catCos θ) = catCos θ := by
  unfold catCos; exact Complex.conj_ofReal _

/-- `(starRingEnd ℂ) (sin θ : ℂ) = (sin θ : ℂ)` since `sin θ` is real. -/
lemma catSin_star (θ : ℝ) : (starRingEnd ℂ) (catSin θ) = catSin θ := by
  unfold catSin; exact Complex.conj_ofReal _

/-- The parametric cat is unit-norm. Uses the Pythagorean trig identity
    `cos²(θ) + sin²(θ) = 1`. -/
lemma catParam_unit (θ : ℝ) : ‖catParam θ‖ = 1 := by
  have h_ortho : inner ℂ (catCos θ • e0) (catSin θ • e1) = (0 : ℂ) := by
    rw [inner_smul_left, inner_smul_right, inner_e0_e1]
    ring
  have h_mul : ‖catParam θ‖ * ‖catParam θ‖ = 1 := by
    show ‖catCos θ • e0 + catSin θ • e1‖ * ‖catCos θ • e0 + catSin θ • e1‖ = 1
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h_ortho]
    simp only [norm_smul, e0_unit, e1_unit, mul_one]
    have hcos : ‖catCos θ‖ * ‖catCos θ‖ = (Real.cos θ)^2 := by
      rw [← sq]; exact catCos_norm_sq θ
    have hsin : ‖catSin θ‖ * ‖catSin θ‖ = (Real.sin θ)^2 := by
      rw [← sq]; exact catSin_norm_sq θ
    rw [hcos, hsin]
    exact Real.cos_sq_add_sin_sq θ
  have h_nn : 0 ≤ ‖catParam θ‖ := norm_nonneg _
  calc ‖catParam θ‖
      = Real.sqrt (‖catParam θ‖ * ‖catParam θ‖) := (Real.sqrt_mul_self h_nn).symm
    _ = Real.sqrt 1 := by rw [h_mul]
    _ = 1 := Real.sqrt_one

/-- **Alive Born probability = cos²(θ)** for the parametric cat. -/
example (θ : ℝ) :
    traceForm (rankOneDensity (catParam θ) (catParam_unit θ))
              (rankOneEffect e0 e0_unit) = (Real.cos θ)^2 := by
  rw [born_quadratic]
  have h_inner : inner ℂ (catParam θ) e0 = catCos θ := by
    show inner ℂ (catCos θ • e0 + catSin θ • e1) e0 = catCos θ
    rw [inner_add_left, inner_smul_left, inner_smul_left,
        inner_e0_e0, inner_e1_e0, mul_one, mul_zero, add_zero]
    exact catCos_star θ
  rw [h_inner]
  exact catCos_norm_sq θ

/-- **Dead Born probability = sin²(θ)** for the parametric cat. -/
example (θ : ℝ) :
    traceForm (rankOneDensity (catParam θ) (catParam_unit θ))
              (rankOneEffect e1 e1_unit) = (Real.sin θ)^2 := by
  rw [born_quadratic]
  have h_inner : inner ℂ (catParam θ) e1 = catSin θ := by
    show inner ℂ (catCos θ • e0 + catSin θ • e1) e1 = catSin θ
    rw [inner_add_left, inner_smul_left, inner_smul_left,
        inner_e0_e1, inner_e1_e1, mul_zero, mul_one, zero_add]
    exact catSin_star θ
  rw [h_inner]
  exact catSin_norm_sq θ

end LF2Cat

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
    [MulAction G SigmaSpace] [MulAction G P]
    [MulAction.IsPretransitive G P]
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
    [MulAction G SigmaSpace] [MulAction G P]
    [MulAction.IsPretransitive G P]
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
