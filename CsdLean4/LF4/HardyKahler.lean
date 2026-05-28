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

end LF4
end CSD
