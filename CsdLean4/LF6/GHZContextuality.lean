/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF6.ForcedContextuality
public import CsdLean4.Empirical.QM.Multipartite.GHZ
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# LF6-C.1: Forced contextuality of the GHZ state (the multipartite tier crux)

**Category:** 6-Local (the first general-N-tier instance of CSD's D1 entangled
frontier; the multipartite analogue of LF6-A.1's singlet forced-contextuality
crux).

## The idea

LF6-A.1 (`ForcedContextuality.lean`) showed: a *product* (setting-local,
non-contextual) outcome-partition of the ontic space on a shared probability
space `(Λ, μ)` is a deterministic local-hidden-variable model, and by Bell/CHSH
no such partition reproduces the singlet correlations; so any de-isolation carve
realising the singlet is jointly contextual. The forcing there is **statistical**:
the LHV CHSH cap `|S| <= 2` versus the singlet `2 sqrt 2`.

This file is the GHZ analogue. The three-qubit GHZ state forces contextuality
**deterministically**: the four perfect correlations

```
<XXX> = +1,  <XYY> = -1,  <YXY> = -1,  <YYX> = -1
```

admit NO consistent local plus/minus 1 value assignment at all (Mermin's
all-or-nothing paradox), because the product of the four constraints forces
`+1 = -1` once each squared plus/minus 1 value is `1`. There is no inequality and
no statistics in the contradiction: a single shared assignment is already
impossible. This is a qualitatively stronger and structurally different forcing
than the singlet's CHSH bound.

## What is reused (no GHZ re-proof, no Bell/kernel reinvention)

- `CSD.Empirical.GHZ.no_lhv_assignment_for_ghz`: the deterministic all-or-nothing
  no-go (no plus/minus 1 assignment satisfies the four Mermin product
  constraints). `no_product_partition_realises_ghz` routes through it; it does
  NOT re-prove the GHZ paradox.
- `CSD.Empirical.GHZ.ghz_expectation_xxx` (= +1) and `ghz_expectation_formula`
  (the half-sum corner reducer), for the engine non-factorisation / marginal pair.

## The deterministic forcing mechanism (the genuine increment over A.1)

A product partition is a triple of setting-local plus/minus 1 responses on a
shared `(Λ, μ)`, one per wing. If it *reproduces* the GHZ correlations (the four
perfect expectations above), then each plus/minus 1 valued product integrand has
expectation exactly plus/minus 1 on a probability space, which forces it to equal
that value `mu`-almost-everywhere. Intersecting the four full-measure sets yields
a single microstate `l0` carrying a deterministic plus/minus 1 value for every
wing-and-axis setting, satisfying all four Mermin constraints simultaneously:
exactly the assignment `no_lhv_assignment_for_ghz` forbids. The contradiction is
reached at one point, not through an inequality.

## Conceptual ledger (honest)

- **Deterministic, not statistical.** Contrast A.1's `|S| <= 2` versus `2 sqrt 2`
  margin. Here the contradiction is single-shot and algebraic: no LHV at all.
- **plus/minus 1 AND locality both load-bearing.** `ReproducesGHZ` is stated
  statistically (expectations), so the plus/minus 1 hypothesis is what upgrades
  "expectation = plus/minus 1" to "pointwise determinism": with unconstrained real
  responses an expectation of plus/minus 1 does not force a definite value.
  Locality (a single shared assignment across the four contexts) is the other
  load-bearing leg: `ghz_each_correlation_locally_realisable` shows each of the
  four correlations is individually realisable by a local plus/minus 1 assignment;
  only realising all four with ONE assignment fails. So the impossibility is the
  non-contextual locality plus the two-valuedness, not any single correlation.
- **One engine, two outputs.** The Born weights (LF4/LF5 moment-map volume,
  imported, not re-derived) and the non-factorisation (this file) are two readings
  of the same Sigma-volume engine. `ghz_engine_marginal_factorises` (each
  single-wing marginal = 0, maximally mixed, no-signalling) holds even though the
  joint `<XXX>` does not factor (`ghz_engine_joint_nonfactorises`).
- **Residue: A5.** This realises the GHZ correlations MODULO **A5**: the GHZ
  entangled sector / preparation region is posited, not derived from deterministic
  dynamics (SO-1: the sector origin, distinct from Paper C Axiom A5). Same posture as the singlet (A.1).
- **Scope: C.1 only.** THIS file is the forced-contextuality crux. The full GHZ
  de-isolation FLOW on the dilated three-qubit space (a deterministic
  FS-measure-preserving `Phi != id` whose pointer-block volumes are the GHZ Born
  weights, mirroring A.2/A.3) is **LF6-C.2, deferred**.

All exports are foundational-triple-only (the machinery is measure-theoretic; no
Busch, no decide on the headline).
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace CSD
namespace LF6

open CSD.LF3 CSD.Empirical CSD.Empirical.Bell CSD.Empirical.GHZ

/-! ### plus/minus 1 arithmetic and integrability helpers -/

/-- A product of two plus/minus 1 reals is plus/minus 1. -/
lemma pm_mul {a b : ℝ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

/-- A plus/minus 1 valued measurable function is integrable on a probability
space (it is bounded by 1). -/
private lemma pm_integrable {Λ : Type*} [MeasurableSpace Λ] (μ : Measure Λ)
    [IsProbabilityMeasure μ] {f : Λ → ℝ} (hf : Measurable f)
    (hpm : ∀ l, f l = 1 ∨ f l = -1) : Integrable f μ := by
  refine Integrable.of_bound hf.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun l => ?_)
  rcases hpm l with h | h <;> rw [h] <;> norm_num

/-- **Perfect correlation forces pointwise determinism.** A plus/minus 1 valued
measurable function whose integral over a probability measure equals a value
`v in {1, -1}` is `mu`-a.e. equal to `v`. This is the step that turns a perfect
expectation into a definite local value; it is where the plus/minus 1 hypothesis
becomes load-bearing. -/
private lemma pm_ae_eq {Λ : Type*} [MeasurableSpace Λ] (μ : Measure Λ)
    [IsProbabilityMeasure μ] {f : Λ → ℝ} (hf : Measurable f)
    (hpm : ∀ l, f l = 1 ∨ f l = -1) {v : ℝ} (hv : v = 1 ∨ v = -1)
    (hint : ∫ l, f l ∂μ = v) : ∀ᵐ l ∂μ, f l = v := by
  have hfint : Integrable f μ := pm_integrable μ hf hpm
  rcases hv with rfl | rfl
  · -- v = 1: g := 1 - f is nonnegative with integral 0.
    have hg_nonneg : (0 : Λ → ℝ) ≤ fun l => (1 : ℝ) - f l := by
      intro l; show (0 : ℝ) ≤ 1 - f l
      rcases hpm l with h | h <;> rw [h] <;> norm_num
    have hgint : Integrable (fun l => (1 : ℝ) - f l) μ :=
      (integrable_const 1).sub hfint
    have hz : ∫ l, ((1 : ℝ) - f l) ∂μ = 0 := by
      rw [integral_sub (integrable_const 1) hfint, hint]
      simp [integral_const]
    have hae := (integral_eq_zero_iff_of_nonneg hg_nonneg hgint).mp hz
    filter_upwards [hae] with l hl
    have h2 : (1 : ℝ) - f l = 0 := by simpa using hl
    linarith
  · -- v = -1: g := f + 1 is nonnegative with integral 0.
    have hg_nonneg : (0 : Λ → ℝ) ≤ fun l => f l + 1 := by
      intro l; show (0 : ℝ) ≤ f l + 1
      rcases hpm l with h | h <;> rw [h] <;> norm_num
    have hgint : Integrable (fun l => f l + 1) μ :=
      hfint.add (integrable_const 1)
    have hz : ∫ l, (f l + 1) ∂μ = 0 := by
      rw [integral_add hfint (integrable_const 1), hint]
      simp [integral_const]
    have hae := (integral_eq_zero_iff_of_nonneg hg_nonneg hgint).mp hz
    filter_upwards [hae] with l hl
    have h2 : f l + 1 = 0 := by simpa using hl
    linarith

/-! ### The product-partition predicate (three-wing analogue of A.1) -/

/-- `R` is a **product (non-contextual) partition** of the shared ontic space
`(Λ, μ)` for the three-party GHZ scenario: `R i ax` is the plus/minus 1 measurable
response of wing `i in Fin 3` measuring Pauli axis `ax in {x, y}`, a function of
that wing's own axis and the shared microstate alone. The setting-locality on a
shared `Λ` is exactly the non-contextual local-hidden-variable assumption. -/
def IsProductPartitionGHZ {Λ : Type*} [MeasurableSpace Λ]
    (R : Fin 3 → PauliAxis → Λ → ℝ) : Prop :=
  (∀ i ax, Measurable (R i ax)) ∧ (∀ i ax l, R i ax l = 1 ∨ R i ax l = -1)

/-- A product partition **reproduces the GHZ correlations** if its four
factorisable wing-product expectations match the four GHZ perfect correlations
`<XXX> = +1`, `<XYY> = <YXY> = <YYX> = -1`. -/
def ReproducesGHZ {Λ : Type*} [MeasurableSpace Λ] (μ : Measure Λ)
    (R : Fin 3 → PauliAxis → Λ → ℝ) : Prop :=
  (∫ l, R 0 PauliAxis.x l * R 1 PauliAxis.x l * R 2 PauliAxis.x l ∂μ = 1) ∧
  (∫ l, R 0 PauliAxis.x l * R 1 PauliAxis.y l * R 2 PauliAxis.y l ∂μ = -1) ∧
  (∫ l, R 0 PauliAxis.y l * R 1 PauliAxis.x l * R 2 PauliAxis.y l ∂μ = -1) ∧
  (∫ l, R 0 PauliAxis.y l * R 1 PauliAxis.y l * R 2 PauliAxis.x l ∂μ = -1)

/-! ### The deterministic forced-contextuality no-go (THE headline) -/

/-- **`no_product_partition_realises_ghz` (LF6-C.1, load-bearing).** There is NO
product (setting-local, non-contextual) partition of any shared probability space
`(Λ, μ)` whose factorisable wing-product expectations reproduce the four GHZ
perfect correlations.

Proof (DETERMINISTIC, all-or-nothing): each of the four plus/minus 1 valued
product integrands has expectation exactly plus/minus 1, so by `pm_ae_eq` it
equals that value `mu`-a.e.; the four full-measure sets intersect (probability
measure), giving a single microstate `l0`. Reading off the plus/minus 1 value of
every wing-and-axis response at `l0` yields a deterministic assignment
`Fin 3 -> PauliAxis -> Z` satisfying all four Mermin constraints, which
`no_lhv_assignment_for_ghz` forbids. The contradiction is at one point, not a
statistical inequality (contrast A.1's `2 < 2 sqrt 2`).

Routes through `CSD.Empirical.GHZ.no_lhv_assignment_for_ghz`; it does NOT re-prove
the GHZ paradox. -/
theorem no_product_partition_realises_ghz {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure Λ) [IsProbabilityMeasure μ] (R : Fin 3 → PauliAxis → Λ → ℝ)
    (hPP : IsProductPartitionGHZ R) (hRep : ReproducesGHZ μ R) : False := by
  obtain ⟨hmeas, hpm⟩ := hPP
  obtain ⟨hxxx, hxyy, hyxy, hyyx⟩ := hRep
  -- Each plus/minus 1 product is a.e. its perfect-correlation value.
  have hae_xxx : ∀ᵐ l ∂μ,
      R 0 PauliAxis.x l * R 1 PauliAxis.x l * R 2 PauliAxis.x l = 1 :=
    pm_ae_eq μ (((hmeas 0 PauliAxis.x).mul (hmeas 1 PauliAxis.x)).mul
        (hmeas 2 PauliAxis.x))
      (fun l => pm_mul (pm_mul (hpm 0 PauliAxis.x l) (hpm 1 PauliAxis.x l))
        (hpm 2 PauliAxis.x l)) (Or.inl rfl) hxxx
  have hae_xyy : ∀ᵐ l ∂μ,
      R 0 PauliAxis.x l * R 1 PauliAxis.y l * R 2 PauliAxis.y l = -1 :=
    pm_ae_eq μ (((hmeas 0 PauliAxis.x).mul (hmeas 1 PauliAxis.y)).mul
        (hmeas 2 PauliAxis.y))
      (fun l => pm_mul (pm_mul (hpm 0 PauliAxis.x l) (hpm 1 PauliAxis.y l))
        (hpm 2 PauliAxis.y l)) (Or.inr rfl) hxyy
  have hae_yxy : ∀ᵐ l ∂μ,
      R 0 PauliAxis.y l * R 1 PauliAxis.x l * R 2 PauliAxis.y l = -1 :=
    pm_ae_eq μ (((hmeas 0 PauliAxis.y).mul (hmeas 1 PauliAxis.x)).mul
        (hmeas 2 PauliAxis.y))
      (fun l => pm_mul (pm_mul (hpm 0 PauliAxis.y l) (hpm 1 PauliAxis.x l))
        (hpm 2 PauliAxis.y l)) (Or.inr rfl) hyxy
  have hae_yyx : ∀ᵐ l ∂μ,
      R 0 PauliAxis.y l * R 1 PauliAxis.y l * R 2 PauliAxis.x l = -1 :=
    pm_ae_eq μ (((hmeas 0 PauliAxis.y).mul (hmeas 1 PauliAxis.y)).mul
        (hmeas 2 PauliAxis.x))
      (fun l => pm_mul (pm_mul (hpm 0 PauliAxis.y l) (hpm 1 PauliAxis.y l))
        (hpm 2 PauliAxis.x l)) (Or.inr rfl) hyyx
  -- One microstate where all four perfect correlations hold simultaneously.
  obtain ⟨l₀, e1, e2, e3, e4⟩ :=
    (hae_xxx.and (hae_xyy.and (hae_yxy.and hae_yyx))).exists
  -- The deterministic plus/minus 1 assignment read off at l₀.
  set lam : Fin 3 → PauliAxis → ℤ :=
    fun i ax => if R i ax l₀ = 1 then (1 : ℤ) else -1 with hlam_def
  have key : ∀ i ax, ((lam i ax : ℤ) : ℝ) = R i ax l₀ := by
    intro i ax
    rcases hpm i ax l₀ with h | h
    · have : lam i ax = 1 := by rw [hlam_def]; simp [h]
      rw [this]; push_cast; rw [h]
    · have hne : R i ax l₀ ≠ 1 := by rw [h]; norm_num
      have : lam i ax = -1 := by rw [hlam_def]; simp [hne]
      rw [this]; push_cast; rw [h]
  have hpmlam : ∀ i ax, lam i ax = 1 ∨ lam i ax = -1 := by
    intro i ax; rw [hlam_def]; by_cases h : R i ax l₀ = 1 <;> simp [h]
  have c1 : lam 0 PauliAxis.x * lam 1 PauliAxis.x * lam 2 PauliAxis.x = 1 := by
    have h : ((lam 0 PauliAxis.x * lam 1 PauliAxis.x * lam 2 PauliAxis.x : ℤ) : ℝ)
        = 1 := by
      push_cast; rw [key 0 PauliAxis.x, key 1 PauliAxis.x, key 2 PauliAxis.x]
      exact e1
    exact_mod_cast h
  have c2 : lam 0 PauliAxis.x * lam 1 PauliAxis.y * lam 2 PauliAxis.y = -1 := by
    have h : ((lam 0 PauliAxis.x * lam 1 PauliAxis.y * lam 2 PauliAxis.y : ℤ) : ℝ)
        = -1 := by
      push_cast; rw [key 0 PauliAxis.x, key 1 PauliAxis.y, key 2 PauliAxis.y]
      exact e2
    exact_mod_cast h
  have c3 : lam 0 PauliAxis.y * lam 1 PauliAxis.x * lam 2 PauliAxis.y = -1 := by
    have h : ((lam 0 PauliAxis.y * lam 1 PauliAxis.x * lam 2 PauliAxis.y : ℤ) : ℝ)
        = -1 := by
      push_cast; rw [key 0 PauliAxis.y, key 1 PauliAxis.x, key 2 PauliAxis.y]
      exact e3
    exact_mod_cast h
  have c4 : lam 0 PauliAxis.y * lam 1 PauliAxis.y * lam 2 PauliAxis.x = -1 := by
    have h : ((lam 0 PauliAxis.y * lam 1 PauliAxis.y * lam 2 PauliAxis.x : ℤ) : ℝ)
        = -1 := by
      push_cast; rw [key 0 PauliAxis.y, key 1 PauliAxis.y, key 2 PauliAxis.x]
      exact e4
    exact_mod_cast h
  exact no_lhv_assignment_for_ghz ⟨lam, hpmlam, c1, c2, c3, c4⟩

/-- **Non-vacuity of the no-go.** Product partitions exist: the all-plus 1
responses form a product partition. Its `<XXX>` correlation integral is `1`,
matching the GHZ value, so the predicate is inhabited and reproduces SOME of the
GHZ data; but it cannot meet the three `-1` constraints (its products are
constantly `1`), so `no_product_partition_realises_ghz` is a genuine separation,
not a vacuous predicate. -/
theorem productPartition_ghz_nonvacuous {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure Λ) [IsProbabilityMeasure μ] :
    IsProductPartitionGHZ
        (Λ := Λ) (fun (_ : Fin 3) (_ : PauliAxis) (_ : Λ) => (1 : ℝ)) ∧
      (∫ _ : Λ, (1 : ℝ) * 1 * 1 ∂μ = 1) := by
  refine ⟨⟨fun _ _ => measurable_const, fun _ _ _ => Or.inl rfl⟩, ?_⟩
  simp [integral_const]

/-- **Locality is load-bearing.** Each of the four GHZ correlations is, on its
own, realisable by a local plus/minus 1 assignment: the `+1` constraint by the
all-plus 1 assignment, each `-1` constraint by flipping wing `0`. Only realising
all four with ONE shared (non-contextual) assignment is impossible. This isolates
the load-bearing structure in `no_product_partition_realises_ghz`: the
contradiction is the non-contextual locality plus the two-valuedness, not any
individual correlation value being unattainable. -/
theorem ghz_each_correlation_locally_realisable :
    (∃ l : Fin 3 → PauliAxis → ℤ, (∀ i ax, l i ax = 1 ∨ l i ax = -1) ∧
        l 0 PauliAxis.x * l 1 PauliAxis.x * l 2 PauliAxis.x = 1) ∧
    (∃ l : Fin 3 → PauliAxis → ℤ, (∀ i ax, l i ax = 1 ∨ l i ax = -1) ∧
        l 0 PauliAxis.x * l 1 PauliAxis.y * l 2 PauliAxis.y = -1) ∧
    (∃ l : Fin 3 → PauliAxis → ℤ, (∀ i ax, l i ax = 1 ∨ l i ax = -1) ∧
        l 0 PauliAxis.y * l 1 PauliAxis.x * l 2 PauliAxis.y = -1) ∧
    (∃ l : Fin 3 → PauliAxis → ℤ, (∀ i ax, l i ax = 1 ∨ l i ax = -1) ∧
        l 0 PauliAxis.y * l 1 PauliAxis.y * l 2 PauliAxis.x = -1) := by
  refine ⟨⟨fun _ _ => 1, fun _ _ => Or.inl rfl, by decide⟩,
          ⟨fun i _ => if i = 0 then -1 else 1, ?_, by decide⟩,
          ⟨fun i _ => if i = 0 then -1 else 1, ?_, by decide⟩,
          ⟨fun i _ => if i = 0 then -1 else 1, ?_, by decide⟩⟩ <;>
    · intro i ax; by_cases h : i = 0 <;> simp [h]

/-! ### The engine's non-factorising joint / factorising marginal pair

The GHZ analogue of A.1's `engine_joint_nonfactorises` / `engine_marginal_factorises`.
The single-wing marginal observables (one Pauli, two identities) all have GHZ
expectation `0`: the marginals factor (each wing maximally mixed, no-signalling),
while the joint `<XXX> = 1` does not factor. -/

/-- Single-wing marginal observable `(sigma . a) tensor I tensor I` (wing 0). -/
noncomputable def margWing0 (a : DetectorSetting) :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  Matrix.kroneckerMap (· * ·) (pauliDot a)
    (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ)
      (1 : Matrix (Fin 2) (Fin 2) ℂ))

/-- Single-wing marginal observable `I tensor (sigma . a) tensor I` (wing 1). -/
noncomputable def margWing1 (a : DetectorSetting) :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ)
    (Matrix.kroneckerMap (· * ·) (pauliDot a) (1 : Matrix (Fin 2) (Fin 2) ℂ))

/-- Single-wing marginal observable `I tensor I tensor (sigma . a)` (wing 2). -/
noncomputable def margWing2 (a : DetectorSetting) :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ)
    (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) (pauliDot a))

/-- Wing-0 marginal of GHZ vanishes for any axis with `a_z = 0` (X or Y). -/
lemma ghz_marginal_wing0 (a : DetectorSetting) (haz : a.vec 2 = 0) :
    Complex.re (inner ℂ ghzState (Matrix.toEuclideanLin (margWing0 a) ghzState)) = 0 := by
  rw [ghz_expectation_formula]
  simp only [margWing0, Matrix.kroneckerMap_apply, Matrix.one_apply,
             pauliDot_apply_00, pauliDot_apply_01, pauliDot_apply_10,
             pauliDot_apply_11, haz]
  simp

/-- Wing-1 marginal of GHZ vanishes for any axis with `a_z = 0` (X or Y). -/
lemma ghz_marginal_wing1 (a : DetectorSetting) (haz : a.vec 2 = 0) :
    Complex.re (inner ℂ ghzState (Matrix.toEuclideanLin (margWing1 a) ghzState)) = 0 := by
  rw [ghz_expectation_formula]
  simp only [margWing1, Matrix.kroneckerMap_apply, Matrix.one_apply,
             pauliDot_apply_00, pauliDot_apply_01, pauliDot_apply_10,
             pauliDot_apply_11, haz]
  simp

/-- Wing-2 marginal of GHZ vanishes for any axis with `a_z = 0` (X or Y). -/
lemma ghz_marginal_wing2 (a : DetectorSetting) (haz : a.vec 2 = 0) :
    Complex.re (inner ℂ ghzState (Matrix.toEuclideanLin (margWing2 a) ghzState)) = 0 := by
  rw [ghz_expectation_formula]
  simp only [margWing2, Matrix.kroneckerMap_apply, Matrix.one_apply,
             pauliDot_apply_00, pauliDot_apply_01, pauliDot_apply_10,
             pauliDot_apply_11, haz]
  simp

/-- **`ghz_engine_joint_nonfactorises`.** The GHZ joint correlation `<XXX> = 1`
does NOT factor into the product of the single-wing X-marginals (each `0`):
`1 != 0 * 0 * 0`. The Sigma-volume engine's non-factorising joint. -/
theorem ghz_engine_joint_nonfactorises :
    Complex.re (inner ℂ ghzState
        (Matrix.toEuclideanLin (sigmaDotTriple chshA chshA chshA) ghzState))
      ≠ Complex.re (inner ℂ ghzState (Matrix.toEuclideanLin (margWing0 chshA) ghzState))
        * Complex.re (inner ℂ ghzState (Matrix.toEuclideanLin (margWing1 chshA) ghzState))
        * Complex.re (inner ℂ ghzState (Matrix.toEuclideanLin (margWing2 chshA) ghzState)) := by
  rw [ghz_expectation_xxx, ghz_marginal_wing0 chshA chshA_vec_ofLp_2,
      ghz_marginal_wing1 chshA chshA_vec_ofLp_2,
      ghz_marginal_wing2 chshA chshA_vec_ofLp_2]
  norm_num

/-- **`ghz_engine_marginal_factorises` (no-signalling).** Each single-wing marginal
of GHZ is `0` (maximally mixed), for both the X and Y axes on every wing,
independent of the other wings' settings. The marginals factor even though the
joint does not. -/
theorem ghz_engine_marginal_factorises :
    (Complex.re (inner ℂ ghzState (Matrix.toEuclideanLin (margWing0 chshA) ghzState)) = 0) ∧
    (Complex.re (inner ℂ ghzState (Matrix.toEuclideanLin (margWing1 chshA) ghzState)) = 0) ∧
    (Complex.re (inner ℂ ghzState (Matrix.toEuclideanLin (margWing2 chshA) ghzState)) = 0) ∧
    (Complex.re (inner ℂ ghzState (Matrix.toEuclideanLin (margWing0 chshA') ghzState)) = 0) ∧
    (Complex.re (inner ℂ ghzState (Matrix.toEuclideanLin (margWing1 chshA') ghzState)) = 0) ∧
    (Complex.re (inner ℂ ghzState (Matrix.toEuclideanLin (margWing2 chshA') ghzState)) = 0) :=
  ⟨ghz_marginal_wing0 chshA chshA_vec_ofLp_2, ghz_marginal_wing1 chshA chshA_vec_ofLp_2,
   ghz_marginal_wing2 chshA chshA_vec_ofLp_2, ghz_marginal_wing0 chshA' chshA'_vec_ofLp_2,
   ghz_marginal_wing1 chshA' chshA'_vec_ofLp_2, ghz_marginal_wing2 chshA' chshA'_vec_ofLp_2⟩

/-- **Capstone (LF6-C.1).** The forced-contextuality crux for GHZ: no product
(non-contextual, three-wing-local) partition reproduces the GHZ correlations
(deterministic all-or-nothing forcing), product partitions exist, and the joint
`<XXX>` does not factor into the single-wing marginals. -/
theorem ghz_forced_contextuality_capstone {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure Λ) [IsProbabilityMeasure μ] :
    (∀ R : Fin 3 → PauliAxis → Λ → ℝ,
        IsProductPartitionGHZ R → ¬ ReproducesGHZ μ R) ∧
      IsProductPartitionGHZ
        (Λ := Λ) (fun (_ : Fin 3) (_ : PauliAxis) (_ : Λ) => (1 : ℝ)) ∧
      Complex.re (inner ℂ ghzState
          (Matrix.toEuclideanLin (sigmaDotTriple chshA chshA chshA) ghzState))
        ≠ Complex.re (inner ℂ ghzState (Matrix.toEuclideanLin (margWing0 chshA) ghzState))
          * Complex.re (inner ℂ ghzState (Matrix.toEuclideanLin (margWing1 chshA) ghzState))
          * Complex.re (inner ℂ ghzState (Matrix.toEuclideanLin (margWing2 chshA) ghzState)) :=
  ⟨fun R hPP hRep => no_product_partition_realises_ghz μ R hPP hRep,
   (productPartition_ghz_nonvacuous μ).1,
   ghz_engine_joint_nonfactorises⟩

end LF6
end CSD
