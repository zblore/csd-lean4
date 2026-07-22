/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF4.SingletKahler

/-!
# LF4 Hardy LF3-chain lift (Phase A — state and ray)

**Category:** 3-Local (LF4 §14 chain lift on the Hardy state).

Constructs the Hardy state `|ψ⟩ = (1/√12)(|00⟩ + |01⟩ + |10⟩ − 3|11⟩)` as
a unit vector in `EuclideanSpace ℂ (Fin 4)`, and its projective ray
`hardyRay ∈ ℂℙ³`. This is **Phase A** of the four-phase Hardy LF3-chain
lift (see plan).

The Hardy state is the canonical non-maximally-entangled 2-qubit state
that exhibits the four Hardy probability constraints `P(A=1,B=1) = 1/12 > 0`,
`P(A=1,B'=−1) = P(A'=−1,B=1) = P(A'=1,B'=1) = 0` under the QM choice of
Pauli axes `A=B=Z, A'=B'=X` (Hardy 1992). The unnormalised version
`hardyVec : Fin 2 × Fin 2 → ℂ` and the four amplitude theorems
(`hardyAmp_AB`, `hardyAmp_A_B'minus`, `hardyAmp_A'minus_B`,
`hardyAmp_A'_B'`) live in `Empirical/QM/Hardy.lean`.

This phase delivers only the state/ray geometry; Phases B–D add the
fibre measure, outcome regions, and the four frequency-convergence
capstones.

## Source

- Hardy 1992 *Phys. Rev. Lett.* **68**, 2981 (the canonical Hardy state).
- The unnormalised `hardyVec` is defined in `Empirical/QM/Hardy.lean` as
  `|00⟩ + |01⟩ + |10⟩ − 3|11⟩`; this module reindexes it from
  `Fin 2 × Fin 2 → ℂ` to `EuclideanSpace ℂ (Fin 4)` (via the existing
  `kReindex` isometry from `SingletKahler.lean`) and normalises.
-/

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF4

/-! ### The unnormalised Hardy state in `EuclideanSpace ℂ (Fin 2 × Fin 2)` -/

/-- The Hardy state `|00⟩ + |01⟩ + |10⟩ − 3|11⟩` as an unnormalised vector
in `EuclideanSpace ℂ (Fin 2 × Fin 2)`. -/
noncomputable def hardyVecE : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  EuclideanSpace.single ((0, 0) : Fin 2 × Fin 2) (1 : ℂ)
    + EuclideanSpace.single ((0, 1) : Fin 2 × Fin 2) (1 : ℂ)
    + EuclideanSpace.single ((1, 0) : Fin 2 × Fin 2) (1 : ℂ)
    + EuclideanSpace.single ((1, 1) : Fin 2 × Fin 2) (-3 : ℂ)

private lemma hardyVecE_ofLp_00 : hardyVecE.ofLp ((0, 0) : Fin 2 × Fin 2) = (1 : ℂ) := by
  simp [hardyVecE, EuclideanSpace.single]

private lemma hardyVecE_ofLp_01 : hardyVecE.ofLp ((0, 1) : Fin 2 × Fin 2) = (1 : ℂ) := by
  simp [hardyVecE, EuclideanSpace.single]

private lemma hardyVecE_ofLp_10 : hardyVecE.ofLp ((1, 0) : Fin 2 × Fin 2) = (1 : ℂ) := by
  simp [hardyVecE, EuclideanSpace.single]

private lemma hardyVecE_ofLp_11 : hardyVecE.ofLp ((1, 1) : Fin 2 × Fin 2) = (-3 : ℂ) := by
  simp [hardyVecE, EuclideanSpace.single]

/-- The Hardy state has squared norm `12 = 1² + 1² + 1² + 3²`. -/
lemma hardyVecE_normSq : ‖hardyVecE‖ ^ 2 = 12 := by
  rw [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two,
             show hardyVecE.ofLp (0, 0) = (1 : ℂ) from hardyVecE_ofLp_00,
             show hardyVecE.ofLp (0, 1) = (1 : ℂ) from hardyVecE_ofLp_01,
             show hardyVecE.ofLp (1, 0) = (1 : ℂ) from hardyVecE_ofLp_10,
             show hardyVecE.ofLp (1, 1) = (-3 : ℂ) from hardyVecE_ofLp_11,
             norm_one, norm_neg, one_pow]
  norm_num

/-- `‖hardyVecE‖ = √12`. -/
lemma hardyVecE_norm : ‖hardyVecE‖ = Real.sqrt 12 := by
  rw [show Real.sqrt 12 = Real.sqrt (‖hardyVecE‖ ^ 2) by rw [hardyVecE_normSq],
      Real.sqrt_sq (norm_nonneg _)]

/-! ### The normalised Hardy state in `EuclideanSpace ℂ (Fin 4)` -/

/-- The Hardy state `(1/√12) · (|00⟩ + |01⟩ + |10⟩ − 3|11⟩)`, re-indexed
into `EuclideanSpace ℂ (Fin 4)` via `kReindex`. Unit norm. -/
noncomputable def hardyPsi : EuclideanSpace ℂ (Fin 4) :=
  ((Real.sqrt 12 : ℂ))⁻¹ • kReindex hardyVecE

/-- The normalised Hardy state has unit norm. -/
lemma hardyPsi_norm : ‖hardyPsi‖ = 1 := by
  unfold hardyPsi
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), LinearIsometryEquiv.norm_map, hardyVecE_norm]
  exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 12))

lemma hardyPsi_ne_zero : (hardyPsi : EuclideanSpace ℂ (Fin 4)) ≠ 0 := by
  intro h
  have : ‖hardyPsi‖ = 0 := by rw [h, norm_zero]
  rw [hardyPsi_norm] at this
  exact one_ne_zero this

/-- The projective ray of the Hardy state, `[hardyPsi] ∈ ℂℙ³`. -/
noncomputable def hardyRay : CPN 4 :=
  Projectivization.mk ℂ hardyPsi hardyPsi_ne_zero

/-! ### Phase B: fibre measure, outcome regions, carving identities -/

/-! #### Hardy posited fibre law

`hardyMuPsi := δ_{[hardyPsi]} ⊗ vol_{T²}` — the Hardy preparation on the
non-trivial-fibre compact-Kähler instance. Pushes through `π = pr₁` to
`δ_{hardyRay}`, parallel to `kMuPsi` for the singlet. -/

/-- The Hardy posited fibre law on `Σ = ℂℙ³ × T²`. -/
noncomputable def hardyMuPsi : Measure (KSigma 4) :=
  (Measure.dirac hardyRay).prod (volume : Measure KTorus)

instance instProbHardyMuPsi : IsProbabilityMeasure hardyMuPsi := by
  unfold hardyMuPsi; infer_instance

lemma hardyMuPsi_push :
    Measure.map (Prod.fst : KSigma 4 → CPN 4) hardyMuPsi = Measure.dirac hardyRay := by
  unfold hardyMuPsi
  rw [← Measure.fst, Measure.fst_prod]

/-! #### Generic torus-fibre outcome region

A torus-fibre arc outcome region of measure `v` for `v ∈ [0, 1]`.
Generalises `sgRegion` and the singlet `kRegion` pattern to a single
helper, used by all four Hardy outcome regions below. -/

/-- Generic torus-fibre outcome region of measure `v`. -/
noncomputable def hardyFibreRegion (v : ℝ) : Set (KSigma 4) :=
  Set.univ ×ˢ (fibreArc v ×ˢ Set.univ)

lemma hardyFibreRegion_measurable (v : ℝ) :
    MeasurableSet (hardyFibreRegion v) := by
  unfold hardyFibreRegion
  exact MeasurableSet.univ.prod ((fibreArc_measurable _).prod MeasurableSet.univ)

/-- **Carving identity.** `μψ(hardyFibreRegion v) = ENNReal.ofReal v` for
`v ∈ [0, 1]`. Same shape as `sgMuPsi_sgRegion` and `kMuPsi_kRegion`. -/
lemma hardyMuPsi_hardyFibreRegion {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    hardyMuPsi (hardyFibreRegion v) = ENNReal.ofReal v := by
  unfold hardyMuPsi hardyFibreRegion
  rw [Measure.prod_prod, measure_univ, one_mul]
  show (volume : Measure KTorus)
      (fibreArc v ×ˢ Set.univ) = _
  rw [show (volume : Measure KTorus)
        = (volume : Measure (AddCircle (1 : ℝ))).prod
            (volume : Measure (AddCircle (1 : ℝ))) from rfl]
  rw [Measure.prod_prod, measure_univ, mul_one]
  exact fibreArc_volume hv

/-! #### The four Hardy Born values

The QM-predicted joint probabilities for the four Hardy-constraint
contexts on the Hardy state. Computed from the QM-side `hardyAmp_*`
theorems after squaring and dividing by the joint norm products
(amplitudes ∈ ℤ; norms² = `12, 24, 24, 24` for `‖ψ‖²·‖a‖²·‖b‖²`). -/

/-- `P(A=+1, B=+1)` on the Hardy state: `1/12` (positive coincidence). -/
noncomputable def hardyBorn_AB : ℝ := 1 / 12

/-- `P(A=+1, B'=−1)` on the Hardy state: `0`. -/
noncomputable def hardyBorn_AB'minus : ℝ := 0

/-- `P(A'=−1, B=+1)` on the Hardy state: `0`. -/
noncomputable def hardyBorn_A'minus_B : ℝ := 0

/-- `P(A'=+1, B'=+1)` on the Hardy state: `0` (the load-bearing zero
that drives `no_lhv_hardy`). -/
noncomputable def hardyBorn_A'_B' : ℝ := 0

lemma hardyBorn_AB_pos : 0 < hardyBorn_AB := by unfold hardyBorn_AB; norm_num

lemma hardyBorn_AB_in_Icc : hardyBorn_AB ∈ Set.Icc (0 : ℝ) 1 := by
  unfold hardyBorn_AB; constructor <;> norm_num

lemma hardyBorn_zero_in_Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor <;> norm_num

lemma hardyBorn_AB_nonneg : 0 ≤ hardyBorn_AB := hardyBorn_AB_in_Icc.1
lemma hardyBorn_AB'minus_nonneg : 0 ≤ hardyBorn_AB'minus := by
  unfold hardyBorn_AB'minus; exact le_refl 0
lemma hardyBorn_A'minus_B_nonneg : 0 ≤ hardyBorn_A'minus_B := by
  unfold hardyBorn_A'minus_B; exact le_refl 0
lemma hardyBorn_A'_B'_nonneg : 0 ≤ hardyBorn_A'_B' := by
  unfold hardyBorn_A'_B'; exact le_refl 0

/-! #### The four Hardy outcome regions -/

/-- Outcome region for `(A=+1, B=+1)`: a fibre arc of measure `1/12`. -/
noncomputable def hardyRegion_AB : Set (KSigma 4) :=
  hardyFibreRegion hardyBorn_AB

/-- Outcome region for `(A=+1, B'=−1)`: measure `0` (the QM-forbidden
outcome). -/
noncomputable def hardyRegion_AB'minus : Set (KSigma 4) :=
  hardyFibreRegion hardyBorn_AB'minus

/-- Outcome region for `(A'=−1, B=+1)`: measure `0`. -/
noncomputable def hardyRegion_A'minus_B : Set (KSigma 4) :=
  hardyFibreRegion hardyBorn_A'minus_B

/-- Outcome region for `(A'=+1, B'=+1)`: measure `0`. -/
noncomputable def hardyRegion_A'_B' : Set (KSigma 4) :=
  hardyFibreRegion hardyBorn_A'_B'

/-! #### The four carving identities -/

/-- `μψ(R_{AB}) = 1/12`. -/
lemma hardyMuPsi_hardyRegion_AB :
    hardyMuPsi hardyRegion_AB = ENNReal.ofReal hardyBorn_AB :=
  hardyMuPsi_hardyFibreRegion hardyBorn_AB_in_Icc

/-- `μψ(R_{A,B'−}) = 0`. -/
lemma hardyMuPsi_hardyRegion_AB'minus :
    hardyMuPsi hardyRegion_AB'minus = ENNReal.ofReal hardyBorn_AB'minus :=
  hardyMuPsi_hardyFibreRegion hardyBorn_zero_in_Icc

/-- `μψ(R_{A'−,B}) = 0`. -/
lemma hardyMuPsi_hardyRegion_A'minus_B :
    hardyMuPsi hardyRegion_A'minus_B = ENNReal.ofReal hardyBorn_A'minus_B :=
  hardyMuPsi_hardyFibreRegion hardyBorn_zero_in_Icc

/-- `μψ(R_{A',B'}) = 0`. -/
lemma hardyMuPsi_hardyRegion_A'_B' :
    hardyMuPsi hardyRegion_A'_B' = ENNReal.ofReal hardyBorn_A'_B' :=
  hardyMuPsi_hardyFibreRegion hardyBorn_zero_in_Icc

/-! ### Phase C: Hardy LF3-chain frequency-convergence capstones

For i.i.d. trials with law `hardyMuPsi` (the Hardy preparation on the
non-trivial-fibre compact-Kähler instance), the empirical frequency of
each Hardy outcome region converges almost surely to the QM-predicted
Born value. Four corollaries — one per Hardy constraint — composed from
a single parametric helper `hardy_freq_convergence`.

Parallel to `sg_frequency_convergence` (single-qubit case) and
`ofKählerPreparation_singlet_frequency_convergence` (singlet case).
Foundational triple only. -/

open Filter Topology in
/-- **Parametric Hardy frequency-convergence helper.** For any
`v ∈ [0, 1]`, i.i.d. trials with law `hardyMuPsi` have empirical
frequency of `hardyFibreRegion v` converging a.s. to `v`. -/
theorem hardy_freq_convergence
    {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {X : ℕ → Ω → KSigma 4} (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = hardyMuPsi)
    (hindep :
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n => Set.indicator (X n ⁻¹' hardyFibreRegion v) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator (X i ⁻¹' hardyFibreRegion v) (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        atTop
        (nhds v) := by
  have hfreq :=
    LF1.freq_tendsto_of_iid hX hlaw (hardyFibreRegion_measurable v) hindep
  rwa [hardyMuPsi_hardyFibreRegion hv, ENNReal.toReal_ofReal hv.1] at hfreq

open Filter Topology in
/-- **Hardy chain capstone 1**: empirical frequency of `(A=+1, B=+1)`
converges to `1/12` (the positive Hardy coincidence). -/
theorem hardy_freq_convergence_AB
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {X : ℕ → Ω → KSigma 4} (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = hardyMuPsi)
    (hindep :
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n => Set.indicator (X n ⁻¹' hardyRegion_AB) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator (X i ⁻¹' hardyRegion_AB) (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        atTop
        (nhds hardyBorn_AB) :=
  hardy_freq_convergence hardyBorn_AB_in_Icc hX hlaw hindep

open Filter Topology in
/-- **Hardy chain capstone 2**: empirical frequency of `(A=+1, B'=−1)`
converges to `0` (QM-forbidden outcome). -/
theorem hardy_freq_convergence_AB'minus
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {X : ℕ → Ω → KSigma 4} (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = hardyMuPsi)
    (hindep :
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n =>
            Set.indicator (X n ⁻¹' hardyRegion_AB'minus) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator (X i ⁻¹' hardyRegion_AB'minus) (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        atTop
        (nhds hardyBorn_AB'minus) :=
  hardy_freq_convergence hardyBorn_zero_in_Icc hX hlaw hindep

open Filter Topology in
/-- **Hardy chain capstone 3**: empirical frequency of `(A'=−1, B=+1)`
converges to `0`. -/
theorem hardy_freq_convergence_A'minus_B
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {X : ℕ → Ω → KSigma 4} (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = hardyMuPsi)
    (hindep :
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n =>
            Set.indicator (X n ⁻¹' hardyRegion_A'minus_B) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator (X i ⁻¹' hardyRegion_A'minus_B) (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        atTop
        (nhds hardyBorn_A'minus_B) :=
  hardy_freq_convergence hardyBorn_zero_in_Icc hX hlaw hindep

open Filter Topology in
/-- **Hardy chain capstone 4**: empirical frequency of `(A'=+1, B'=+1)`
converges to `0` (the load-bearing QM-forbidden outcome that drives
`no_lhv_hardy`). -/
theorem hardy_freq_convergence_A'_B'
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {X : ℕ → Ω → KSigma 4} (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = hardyMuPsi)
    (hindep :
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n => Set.indicator (X n ⁻¹' hardyRegion_A'_B') (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator (X i ⁻¹' hardyRegion_A'_B') (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        atTop
        (nhds hardyBorn_A'_B') :=
  hardy_freq_convergence hardyBorn_zero_in_Icc hX hlaw hindep

/-! ### Phase E: QM ↔ LF4 amplitude loop — Hilbert Born identities

Closes the loop between the posited Hardy Born values (1/12, 0, 0, 0) and
the Hilbert quantities `‖⟨hardyPsi, |a ⊗ b⟩‖²` for the four Hardy joint
outcomes. Each Hardy Born value is shown to equal a Hilbert inner-product
squared, by direct entry computation through `hardyVecE_ofLp_*` and
`LinearIsometryEquiv.inner_map_map` (the `kReindex` transport).

The four joint outcome vectors are the QM `Empirical/QM/Hardy.lean`
`zPlus, xPlus, xMinus` (single-qubit eigenstates of `Z` and `X`) tensored
and normalised:

| Outcome           | Joint state (unnormalised)            | Normalisation |
|-------------------|----------------------------------------|---------------|
| `(A=+1, B=+1)`    | `|00⟩`                                | `1` (already unit) |
| `(A=+1, B'=−1)`   | `|0⟩ ⊗ (−|0⟩ + |1⟩)`                  | `1/√2` |
| `(A'=−1, B=+1)`   | `(−|0⟩ + |1⟩) ⊗ |0⟩`                  | `1/√2` |
| `(A'=+1, B'=+1)`  | `(|0⟩ + |1⟩) ⊗ (|0⟩ + |1⟩)`           | `1/2` |

These are re-indexed via `kReindex` from `EuclideanSpace ℂ (Fin 2 × Fin 2)`
to `EuclideanSpace ℂ (Fin 4)`, matching `hardyPsi`.

The four Born identities use the explicit `hardyVecE` entries
`(1, 1, 1, −3)`; the algebra agrees with the QM-side `hardyAmp_*`
theorems (`= 1, 0, 0, 0` for the unnormalised amplitudes; after
normalisation `‖inner‖² = 1/12, 0, 0, 0` matching `hardyBorn_*`). -/

/-! #### Four Hardy joint outcome vectors -/

/-- Joint outcome `|00⟩` in `EuclideanSpace ℂ (Fin 4)`. -/
noncomputable def hardyOutcome_AB : EuclideanSpace ℂ (Fin 4) :=
  kReindex (EuclideanSpace.single ((0, 0) : Fin 2 × Fin 2) (1 : ℂ))

/-- Joint outcome `|0⟩ ⊗ (1/√2)(−|0⟩ + |1⟩) = (1/√2)(−|00⟩ + |01⟩)`. -/
noncomputable def hardyOutcome_AB'minus : EuclideanSpace ℂ (Fin 4) :=
  ((Real.sqrt 2 : ℂ))⁻¹ •
    kReindex (- EuclideanSpace.single ((0, 0) : Fin 2 × Fin 2) (1 : ℂ)
              + EuclideanSpace.single ((0, 1) : Fin 2 × Fin 2) (1 : ℂ))

/-- Joint outcome `(1/√2)(−|0⟩ + |1⟩) ⊗ |0⟩ = (1/√2)(−|00⟩ + |10⟩)`. -/
noncomputable def hardyOutcome_A'minus_B : EuclideanSpace ℂ (Fin 4) :=
  ((Real.sqrt 2 : ℂ))⁻¹ •
    kReindex (- EuclideanSpace.single ((0, 0) : Fin 2 × Fin 2) (1 : ℂ)
              + EuclideanSpace.single ((1, 0) : Fin 2 × Fin 2) (1 : ℂ))

/-- Joint outcome `(1/√2)(|0⟩+|1⟩) ⊗ (1/√2)(|0⟩+|1⟩) =
`(1/2)(|00⟩+|01⟩+|10⟩+|11⟩)`. -/
noncomputable def hardyOutcome_A'_B' : EuclideanSpace ℂ (Fin 4) :=
  ((2 : ℂ))⁻¹ •
    kReindex (EuclideanSpace.single ((0, 0) : Fin 2 × Fin 2) (1 : ℂ)
            + EuclideanSpace.single ((0, 1) : Fin 2 × Fin 2) (1 : ℂ)
            + EuclideanSpace.single ((1, 0) : Fin 2 × Fin 2) (1 : ℂ)
            + EuclideanSpace.single ((1, 1) : Fin 2 × Fin 2) (1 : ℂ))

/-! #### Four Hilbert Born identities

Each `‖⟨hardyPsi, hardyOutcome_*⟩‖² = hardyBorn_*` by direct computation.
The inner product on `EuclideanSpace ℂ (Fin 4)` reduces (via `kReindex`
isometry transport) to an inner product on `EuclideanSpace ℂ (Fin 2 × Fin 2)`,
which is a sum of `hardyVecE`'s explicit entries against the joint
outcome's `EuclideanSpace.single` components. -/

/-- Helper: `inner ℂ hardyVecE (single i 1) = star (hardyVecE.ofLp i)`,
giving the four explicit values via the entry lemmas. -/
private lemma inner_hardyVecE_single_apply
    (i : Fin 2 × Fin 2) :
    inner ℂ hardyVecE (EuclideanSpace.single i (1 : ℂ))
      = (starRingEnd ℂ) (hardyVecE.ofLp i) := by
  rw [← inner_conj_symm, EuclideanSpace.inner_single_left]
  simp

private lemma inner_hardyVecE_single_00 :
    inner ℂ hardyVecE (EuclideanSpace.single ((0, 0) : Fin 2 × Fin 2) (1 : ℂ))
      = (1 : ℂ) := by
  rw [inner_hardyVecE_single_apply, hardyVecE_ofLp_00]; simp

private lemma inner_hardyVecE_single_01 :
    inner ℂ hardyVecE (EuclideanSpace.single ((0, 1) : Fin 2 × Fin 2) (1 : ℂ))
      = (1 : ℂ) := by
  rw [inner_hardyVecE_single_apply, hardyVecE_ofLp_01]; simp

private lemma inner_hardyVecE_single_10 :
    inner ℂ hardyVecE (EuclideanSpace.single ((1, 0) : Fin 2 × Fin 2) (1 : ℂ))
      = (1 : ℂ) := by
  rw [inner_hardyVecE_single_apply, hardyVecE_ofLp_10]; simp

private lemma inner_hardyVecE_single_11 :
    inner ℂ hardyVecE (EuclideanSpace.single ((1, 1) : Fin 2 × Fin 2) (1 : ℂ))
      = (-3 : ℂ) := by
  rw [inner_hardyVecE_single_apply, hardyVecE_ofLp_11]
  -- Goal: (starRingEnd ℂ) (-3 : ℂ) = -3
  -- `(-3 : ℂ) = ((-3 : ℝ) : ℂ)`; conj of real = real.
  rw [show ((-3 : ℂ)) = (((-3 : ℝ)) : ℂ) by push_cast; ring,
      Complex.conj_ofReal]

/-- Helper: `star ((√12 : ℂ)⁻¹) = (√12 : ℂ)⁻¹` (real number is self-conjugate). -/
private lemma conj_sqrt12_inv :
    (starRingEnd ℂ) ((Real.sqrt 12 : ℂ))⁻¹ = ((Real.sqrt 12 : ℂ))⁻¹ := by
  rw [map_inv₀, Complex.conj_ofReal]

/-- `‖((√12 : ℂ))⁻¹‖² = 1/12`. -/
private lemma sqrt12_inv_normSq :
    ‖((Real.sqrt 12 : ℂ))⁻¹‖ ^ 2 = 1 / 12 := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 12)]
  norm_num

/-- **Hardy Hilbert Born identity 1**: `‖⟨hardyPsi, |00⟩⟩‖² = 1/12` (the
positive coincidence). -/
theorem hardyBorn_AB_eq_inner_sq :
    ‖inner ℂ hardyPsi hardyOutcome_AB‖ ^ 2 = hardyBorn_AB := by
  unfold hardyPsi hardyOutcome_AB hardyBorn_AB
  rw [inner_smul_left, LinearIsometryEquiv.inner_map_map,
      inner_hardyVecE_single_00, mul_one, conj_sqrt12_inv]
  exact sqrt12_inv_normSq

/-- Helper: the (−|00⟩ + |01⟩) outcome's inner with hardyVecE vanishes. -/
private lemma inner_hardyVecE_AB'minus_raw :
    inner ℂ hardyVecE
        (- EuclideanSpace.single ((0, 0) : Fin 2 × Fin 2) (1 : ℂ)
         + EuclideanSpace.single ((0, 1) : Fin 2 × Fin 2) (1 : ℂ)) = (0 : ℂ) := by
  rw [inner_add_right, inner_neg_right,
      inner_hardyVecE_single_00, inner_hardyVecE_single_01]
  ring

private lemma inner_hardyVecE_A'minus_B_raw :
    inner ℂ hardyVecE
        (- EuclideanSpace.single ((0, 0) : Fin 2 × Fin 2) (1 : ℂ)
         + EuclideanSpace.single ((1, 0) : Fin 2 × Fin 2) (1 : ℂ)) = (0 : ℂ) := by
  rw [inner_add_right, inner_neg_right,
      inner_hardyVecE_single_00, inner_hardyVecE_single_10]
  ring

private lemma inner_hardyVecE_A'_B'_raw :
    inner ℂ hardyVecE
        (EuclideanSpace.single ((0, 0) : Fin 2 × Fin 2) (1 : ℂ)
       + EuclideanSpace.single ((0, 1) : Fin 2 × Fin 2) (1 : ℂ)
       + EuclideanSpace.single ((1, 0) : Fin 2 × Fin 2) (1 : ℂ)
       + EuclideanSpace.single ((1, 1) : Fin 2 × Fin 2) (1 : ℂ)) = (0 : ℂ) := by
  rw [inner_add_right, inner_add_right, inner_add_right,
      inner_hardyVecE_single_00, inner_hardyVecE_single_01,
      inner_hardyVecE_single_10, inner_hardyVecE_single_11]
  ring

/-- **Hardy Hilbert Born identity 2**: `‖⟨hardyPsi, |0⟩⊗(−|0⟩+|1⟩)/√2⟩‖² = 0`. -/
theorem hardyBorn_AB'minus_eq_inner_sq :
    ‖inner ℂ hardyPsi hardyOutcome_AB'minus‖ ^ 2 = hardyBorn_AB'minus := by
  unfold hardyPsi hardyOutcome_AB'minus hardyBorn_AB'minus
  rw [inner_smul_left, inner_smul_right, LinearIsometryEquiv.inner_map_map,
      inner_hardyVecE_AB'minus_raw]
  simp

/-- **Hardy Hilbert Born identity 3**: `‖⟨hardyPsi, (−|0⟩+|1⟩)/√2 ⊗ |0⟩⟩‖² = 0`. -/
theorem hardyBorn_A'minus_B_eq_inner_sq :
    ‖inner ℂ hardyPsi hardyOutcome_A'minus_B‖ ^ 2 = hardyBorn_A'minus_B := by
  unfold hardyPsi hardyOutcome_A'minus_B hardyBorn_A'minus_B
  rw [inner_smul_left, inner_smul_right, LinearIsometryEquiv.inner_map_map,
      inner_hardyVecE_A'minus_B_raw]
  simp

/-- **Hardy Hilbert Born identity 4** (load-bearing): `‖⟨hardyPsi, |++⟩⟩‖² = 0`.
Uses all four `hardyVecE` entries `(1, 1, 1, −3)`; sum `1 + 1 + 1 − 3 = 0`. -/
theorem hardyBorn_A'_B'_eq_inner_sq :
    ‖inner ℂ hardyPsi hardyOutcome_A'_B'‖ ^ 2 = hardyBorn_A'_B' := by
  unfold hardyPsi hardyOutcome_A'_B' hardyBorn_A'_B'
  rw [inner_smul_left, inner_smul_right, LinearIsometryEquiv.inner_map_map,
      inner_hardyVecE_A'_B'_raw]
  simp

/-! ### Full §14 observable correspondence for the four Hardy outcomes

Composing the Hilbert Born identities (Phase E above) with the carving
identities (Phase B), each Hardy Born value equals **both** the Hilbert
inner-product squared **and** the ontic measure of the carved outcome
region. The §14 correspondence for Hardy at the projector level. -/

/-- **Hardy §14 observable correspondence (A=+1, B=+1).** -/
theorem hardy_observable_correspondence_AB :
    ‖inner ℂ hardyPsi hardyOutcome_AB‖ ^ 2 = (hardyMuPsi hardyRegion_AB).toReal := by
  rw [hardyBorn_AB_eq_inner_sq, hardyMuPsi_hardyRegion_AB,
      ENNReal.toReal_ofReal hardyBorn_AB_in_Icc.1]

/-- **Hardy §14 observable correspondence (A=+1, B'=−1).** -/
theorem hardy_observable_correspondence_AB'minus :
    ‖inner ℂ hardyPsi hardyOutcome_AB'minus‖ ^ 2
      = (hardyMuPsi hardyRegion_AB'minus).toReal := by
  rw [hardyBorn_AB'minus_eq_inner_sq, hardyMuPsi_hardyRegion_AB'minus,
      ENNReal.toReal_ofReal hardyBorn_AB'minus_nonneg]

/-- **Hardy §14 observable correspondence (A'=−1, B=+1).** -/
theorem hardy_observable_correspondence_A'minus_B :
    ‖inner ℂ hardyPsi hardyOutcome_A'minus_B‖ ^ 2
      = (hardyMuPsi hardyRegion_A'minus_B).toReal := by
  rw [hardyBorn_A'minus_B_eq_inner_sq, hardyMuPsi_hardyRegion_A'minus_B,
      ENNReal.toReal_ofReal hardyBorn_A'minus_B_nonneg]

/-- **Hardy §14 observable correspondence (A'=+1, B'=+1).** The
load-bearing zero. -/
theorem hardy_observable_correspondence_A'_B' :
    ‖inner ℂ hardyPsi hardyOutcome_A'_B'‖ ^ 2
      = (hardyMuPsi hardyRegion_A'_B').toReal := by
  rw [hardyBorn_A'_B'_eq_inner_sq, hardyMuPsi_hardyRegion_A'_B',
      ENNReal.toReal_ofReal hardyBorn_A'_B'_nonneg]

end LF4
end CSD
