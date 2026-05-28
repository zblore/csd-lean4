import CsdLean4.LF4.SpectralExpansion
import CsdLean4.LF4.KahlerInstance

/-!
# LF4 §14.2 multi-region spectral carving (N-arc partition of the fibre)

**Category:** 3-Local (LF4 §14.2 ontic-side multi-region carving — the
infrastructure to lift the Hilbert-side spectral expansion
`⟨ψ, A ψ⟩ = ∑ᵢ λᵢ · ‖⟨uᵢ, ψ⟩‖²` (proved in `SpectralExpansion.lean`) to a
full ontic ↔ Hilbert observable correspondence for any Hermitian
observable of any finite dimension).

The existing `fibreArc ℓ = (0, ℓ]` primitive (`SingletKahler.lean`) is
**anchored at zero**: distinct `fibreArc w₁`, `fibreArc w₂` are nested,
not disjoint. The existing Hardy four-region setup is "disjoint" only
because three of its four arcs are vacuous (zero-length). For a genuine
N-arc partition with weights summing to one we need a shifted primitive,
plus cumulative-sum index arithmetic.

## Module contents

- **Phase A** — `fibreShiftedArc c ℓ := (0,1]⁻¹ preimage of (c, c+ℓ]`.
  Measurability, volume `= ENNReal.ofReal ℓ` when `[c, c+ℓ] ⊆ [0,1]`,
  and pairwise disjointness when the underlying ℝ-intervals are disjoint.

- **Phase B** — cumulative-sum prefixes `cumWeights w : Fin (N+1) → ℝ`
  with `cumWeights w 0 = 0`, `cumWeights w i.succ = cumWeights w i.castSucc
  + w i`, monotone for nonnegative `w`, and the bound
  `cumWeights w i.castSucc + w i ≤ ∑ w`. Built on a `ℕ`-recursive
  `cumWeightsAux` for a clean inductive structure.

- **Phase C** — N-region spectral carving on the existing Kähler instance
  `KSigma M`: `spectralRegion w i := univ ×ˢ (fibreShiftedArc (cumWeights w
  i.castSucc) (w i) ×ˢ univ)`. Measurability, the carving identity
  `(Dirac p₀ ⊗ vol_T²) (spectralRegion w i) = ENNReal.ofReal (w i)`
  (for `w` nonnegative with `∑ w ≤ 1`), and pairwise disjointness.

## Tier-2 posture (unchanged)

The fibre arcs are carved to the Born values **by construction**
(the shifted-arc length equals the prescribed weight). What's new is
that the resulting N-arc partition is genuinely disjoint, and the
per-region carving identity composes through `Finset.sum` to give an
ontic spectral observable whose integral against the preparation
measure equals the Hilbert expectation value.

## Axiom posture

Foundational triple only.
-/

open MeasureTheory Set
open Matrix Finset

namespace CSD
namespace LF4

/-! ### Phase A — shifted fibre arc primitive -/

/-- The shifted fibre arc `(c, c+ℓ]` on `AddCircle 1`, the preimage of the
`ℝ`-interval `Ioc c (c+ℓ)` under the chart `equivIoc 1 0 : AddCircle 1 ≃
Ioc 0 1`. Concretely a subset of the unit circle of arc length `ℓ` shifted
to start at parameter `c`. -/
noncomputable def fibreShiftedArc (c ℓ : ℝ) : Set (AddCircle (1 : ℝ)) :=
  (AddCircle.equivIoc (1 : ℝ) 0) ⁻¹' (Subtype.val ⁻¹' Set.Ioc c (c + ℓ))

lemma fibreShiftedArc_measurable (c ℓ : ℝ) :
    MeasurableSet (fibreShiftedArc c ℓ) :=
  (AddCircle.measurableEquivIoc (1 : ℝ) 0).measurable
    (measurable_subtype_coe measurableSet_Ioc)

/-- The shifted fibre arc has Haar volume `ℓ` when `[c, c+ℓ] ⊆ [0, 1]`. -/
lemma fibreShiftedArc_volume {c ℓ : ℝ}
    (hc : 0 ≤ c) (hcℓ : c + ℓ ≤ 1) :
    (volume : Measure (AddCircle (1 : ℝ))) (fibreShiftedArc c ℓ)
      = ENNReal.ofReal ℓ := by
  unfold fibreShiftedArc
  rw [(AddCircle.measurePreserving_equivIoc (T := 1)).measure_preimage
        (measurable_subtype_coe measurableSet_Ioc).nullMeasurableSet,
      Measure.comap_apply _ Subtype.val_injective
        (fun _ ↦ measurableSet_Ioc.subtype_image)
        _ (measurable_subtype_coe measurableSet_Ioc),
      Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype, zero_add]
  show (volume : Measure ℝ) (Set.Ioc c (c + ℓ) ∩ Set.Ioc 0 1) = ENNReal.ofReal ℓ
  rw [Set.Ioc_inter_Ioc, max_eq_left hc, min_eq_left hcℓ, Real.volume_Ioc]
  ring_nf

/-- Two shifted arcs whose `ℝ`-intervals satisfy `c₁ + ℓ₁ ≤ c₂` are
disjoint as subsets of `AddCircle 1`. -/
lemma fibreShiftedArc_disjoint {c₁ ℓ₁ c₂ ℓ₂ : ℝ}
    (h : c₁ + ℓ₁ ≤ c₂) :
    Disjoint (fibreShiftedArc c₁ ℓ₁) (fibreShiftedArc c₂ ℓ₂) := by
  unfold fibreShiftedArc
  refine Disjoint.preimage _ ?_
  refine Disjoint.preimage _ ?_
  exact Set.Ioc_disjoint_Ioc_of_le h

/-! ### Phase B — cumulative weights (Finset.filter form) -/

/-- Cumulative-sum prefixes of a weight vector `w : Fin N → ℝ`,
indexed by `Fin (N+1)`. `cumWeights w k = ∑_{j.val < k.val} w j`.
The Finset.filter form gives clean direct proofs of the key lemmas
(succ-castSucc step, monotonicity, last-index sum) via
`Finset.sum_insert` / `Finset.sum_le_sum_of_subset_of_nonneg`. -/
noncomputable def cumWeights {N : ℕ} (w : Fin N → ℝ) (k : Fin (N + 1)) : ℝ :=
  ∑ j ∈ (Finset.univ : Finset (Fin N)).filter (·.val < k.val), w j

lemma cumWeights_zero {N : ℕ} (w : Fin N → ℝ) :
    cumWeights w 0 = 0 := by
  unfold cumWeights
  simp

lemma cumWeights_succ_castSucc {N : ℕ} (w : Fin N → ℝ) (i : Fin N) :
    cumWeights w i.succ = cumWeights w i.castSucc + w i := by
  unfold cumWeights
  have hfilter :
      (Finset.univ : Finset (Fin N)).filter (·.val < i.succ.val)
        = insert i ((Finset.univ : Finset (Fin N)).filter (·.val < i.castSucc.val)) := by
    ext j
    simp only [Fin.val_succ, Fin.val_castSucc, Finset.mem_filter,
               Finset.mem_insert, Finset.mem_univ, true_and]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp h) with h' | h'
      · exact Or.inr h'
      · exact Or.inl (Fin.ext h')
    · rcases h with rfl | h'
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt h'
  rw [hfilter, Finset.sum_insert]
  · ring
  · simp [Fin.val_castSucc]

lemma cumWeights_last {N : ℕ} (w : Fin N → ℝ) :
    cumWeights w (Fin.last N) = ∑ j : Fin N, w j := by
  unfold cumWeights
  rw [show ((Finset.univ : Finset (Fin N)).filter (·.val < (Fin.last N).val))
        = (Finset.univ : Finset (Fin N)) from by
        ext j
        simp [Fin.val_last]]

lemma cumWeights_mono {N : ℕ} {w : Fin N → ℝ} (hw : ∀ i, 0 ≤ w i) :
    Monotone (cumWeights w) := by
  intro i j hij
  unfold cumWeights
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact lt_of_lt_of_le hk (Fin.le_iff_val_le_val.mp hij)
  · intros k _ _; exact hw k

lemma cumWeights_nonneg {N : ℕ} {w : Fin N → ℝ} (hw : ∀ i, 0 ≤ w i)
    (i : Fin (N + 1)) : 0 ≤ cumWeights w i := by
  rw [← cumWeights_zero w]
  exact cumWeights_mono hw (Fin.zero_le _)

lemma cumWeights_succ_le_sum {N : ℕ} {w : Fin N → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ j : Fin N, w j ≤ 1) (i : Fin N) :
    cumWeights w i.castSucc + w i ≤ 1 := by
  rw [← cumWeights_succ_castSucc]
  calc cumWeights w i.succ
      ≤ cumWeights w (Fin.last N) := cumWeights_mono hw (Fin.le_last _)
    _ = ∑ j : Fin N, w j := cumWeights_last w
    _ ≤ 1 := hsum

/-! ### Phase C — N-region spectral carving on `KSigma M` -/

/-- Multi-region fibre carving: the i-th spectral region on `KSigma M`,
indexed by `Fin N`, with weights `w : Fin N → ℝ`. The fibre arc spans
`(cumWeights w i.castSucc, cumWeights w i.succ]` (length `w i` by
`cumWeights_succ_castSucc`). Independent of the base preparation. -/
noncomputable def spectralRegion {N M : ℕ} (w : Fin N → ℝ) (i : Fin N) :
    Set (KSigma M) :=
  Set.univ ×ˢ (fibreShiftedArc (cumWeights w i.castSucc) (w i) ×ˢ Set.univ)

lemma spectralRegion_measurable {N M : ℕ} (w : Fin N → ℝ) (i : Fin N) :
    MeasurableSet (spectralRegion (M := M) w i) :=
  MeasurableSet.univ.prod
    ((fibreShiftedArc_measurable _ _).prod MeasurableSet.univ)

/-- The N-arc spectral carving identity on any Dirac-on-base × T² preparation:
the `i`-th region has measure `w i`, for nonnegative `w` with `∑ w ≤ 1`. -/
lemma diracProd_spectralRegion {N M : ℕ} (p₀ : CPN M)
    {w : Fin N → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ j : Fin N, w j ≤ 1) (i : Fin N) :
    ((Measure.dirac p₀).prod (volume : Measure KTorus))
        (spectralRegion w i) = ENNReal.ofReal (w i) := by
  unfold spectralRegion
  rw [Measure.prod_prod, measure_univ, one_mul]
  show (volume : Measure KTorus)
      (fibreShiftedArc (cumWeights w i.castSucc) (w i) ×ˢ Set.univ) = _
  rw [show (volume : Measure KTorus)
        = (volume : Measure (AddCircle (1 : ℝ))).prod
            (volume : Measure (AddCircle (1 : ℝ))) from rfl]
  rw [Measure.prod_prod, measure_univ, mul_one]
  exact fibreShiftedArc_volume (cumWeights_nonneg hw _)
    (cumWeights_succ_le_sum hw hsum i)

/-- Pairwise disjointness of the N-arc spectral regions. -/
lemma spectralRegion_pairwise_disjoint {N M : ℕ} {w : Fin N → ℝ}
    (hw : ∀ i, 0 ≤ w i) :
    Pairwise (Function.onFun Disjoint (spectralRegion (M := M) w)) := by
  intro i j hij
  show Disjoint (spectralRegion (M := M) w i) (spectralRegion (M := M) w j)
  unfold spectralRegion
  rw [Set.disjoint_left]
  rintro σ ⟨-, hi_arc, -⟩ ⟨-, hj_arc, -⟩
  -- hi_arc, hj_arc place σ.2.1 in both spectral arcs; these are disjoint by
  -- the cumulative-weight gap (Phase B's `cumWeights_succ_castSucc` + monotonicity).
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have harc : Disjoint
        (fibreShiftedArc (cumWeights w i.castSucc) (w i))
        (fibreShiftedArc (cumWeights w j.castSucc) (w j)) := by
      apply fibreShiftedArc_disjoint
      rw [← cumWeights_succ_castSucc]
      apply cumWeights_mono hw
      simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
      omega
    exact Set.disjoint_left.mp harc hi_arc hj_arc
  · have harc : Disjoint
        (fibreShiftedArc (cumWeights w j.castSucc) (w j))
        (fibreShiftedArc (cumWeights w i.castSucc) (w i)) := by
      apply fibreShiftedArc_disjoint
      rw [← cumWeights_succ_castSucc]
      apply cumWeights_mono hw
      simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
      omega
    exact Set.disjoint_left.mp harc hj_arc hi_arc

/-! ### Phase D — Born weights, spectral observable, and integration identity -/

/-- **Born weights** of a Hermitian matrix `A` on a state `ψ`: the squared
moduli `‖⟨uᵢ, ψ⟩‖²` of the projections onto the eigenvectors of `A`. These
sum to `‖ψ‖²` (Parseval / `OrthonormalBasis.sum_sq_norm_inner_right`). -/
noncomputable def bornWeights {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.IsHermitian) (ψ : EuclideanSpace ℂ (Fin N)) : Fin N → ℝ :=
  fun i => ‖inner ℂ (hA.eigenvectorBasis i) ψ‖ ^ 2

lemma bornWeights_nonneg {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.IsHermitian) (ψ : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    0 ≤ bornWeights hA ψ i := sq_nonneg _

lemma bornWeights_sum_eq_norm_sq {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.IsHermitian) (ψ : EuclideanSpace ℂ (Fin N)) :
    ∑ i : Fin N, bornWeights hA ψ i = ‖ψ‖ ^ 2 :=
  hA.eigenvectorBasis.sum_sq_norm_inner_right ψ

lemma bornWeights_sum_eq_one {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.IsHermitian) {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ‖ψ‖ = 1) :
    ∑ i : Fin N, bornWeights hA ψ i = 1 := by
  rw [bornWeights_sum_eq_norm_sq, hψ]; norm_num

/-- **Ontic spectral observable**: the eigenvalue-weighted indicator sum
over the N spectral outcome regions. Each region `spectralRegion (bornWeights
hA ψ) i` has fibre measure `‖⟨uᵢ, ψ⟩‖²` under the Dirac × T² preparation,
and the indicator-weighted sum represents the ontic counterpart of `A`. -/
noncomputable def spectralOntic {N M : ℕ} {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.IsHermitian) (ψ : EuclideanSpace ℂ (Fin N)) :
    KSigma M → ℝ := fun σ =>
  ∑ i : Fin N, hA.eigenvalues i *
    (spectralRegion (M := M) (bornWeights hA ψ) i).indicator (fun _ => (1 : ℝ)) σ

lemma spectralOntic_measurable {N M : ℕ} {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.IsHermitian) (ψ : EuclideanSpace ℂ (Fin N)) :
    Measurable (spectralOntic (M := M) hA ψ) := by
  apply Finset.measurable_sum
  intros i _
  exact (measurable_const.indicator (spectralRegion_measurable _ _)).const_mul _

lemma spectralOntic_integrable {N M : ℕ} {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.IsHermitian) (ψ : EuclideanSpace ℂ (Fin N)) (p₀ : CPN M) :
    Integrable (spectralOntic (M := M) hA ψ)
      ((Measure.dirac p₀).prod (volume : Measure KTorus)) := by
  unfold spectralOntic
  -- The Dirac-product measure is a probability measure (Dirac and Haar T² both are).
  haveI : IsProbabilityMeasure ((Measure.dirac p₀).prod (volume : Measure KTorus)) :=
    inferInstance
  apply integrable_finset_sum
  intros i _
  refine Integrable.const_mul ?_ _
  exact MeasureTheory.Integrable.indicator (integrable_const (1 : ℝ))
    (spectralRegion_measurable _ _)

/-- **§14.2 ontic-Hilbert observable correspondence at the integration level**:
for any Hermitian `A : Matrix (Fin N) (Fin N) ℂ` and unit state
`ψ : EuclideanSpace ℂ (Fin N)`, on any Kähler instance `KSigma M` with
preparation `(Dirac p₀) × vol_T²`, the ontic spectral observable integrates
to the real part of the Hilbert expectation value. Composes the Phase C
multi-region carving identity (`diracProd_spectralRegion`) with the
`SpectralExpansion.hermitian_inner_spectral_expansion_re` identity. -/
theorem integral_spectralOntic_eq_inner_re {N M : ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ : ‖ψ‖ = 1) (p₀ : CPN M) :
    ∫ σ, spectralOntic (M := M) hA ψ σ ∂((Measure.dirac p₀).prod (volume : Measure KTorus))
      = RCLike.re (inner ℂ ψ (A.toEuclideanLin ψ)) := by
  unfold spectralOntic
  haveI : IsProbabilityMeasure ((Measure.dirac p₀).prod (volume : Measure KTorus)) :=
    inferInstance
  rw [MeasureTheory.integral_finset_sum]
  · -- Step 1: per-term integral = λᵢ * (μ(R_i)).toReal = λᵢ * bornWeights i.
    have h_each : ∀ i : Fin N,
        ∫ σ, hA.eigenvalues i *
          (spectralRegion (M := M) (bornWeights hA ψ) i).indicator
            (fun _ => (1 : ℝ)) σ ∂((Measure.dirac p₀).prod (volume : Measure KTorus))
          = hA.eigenvalues i * bornWeights hA ψ i := by
      intro i
      rw [integral_const_mul]
      congr 1
      -- Normalise `(fun _ => 1) = 1` (Pi.one) so `integral_indicator_one` fires.
      change ∫ σ, (spectralRegion (M := M) (bornWeights hA ψ) i).indicator 1 σ
        ∂((Measure.dirac p₀).prod (volume : Measure KTorus)) = _
      -- `integral_indicator_one` returns `μ.real s`; convert to `(μ s).toReal`
      -- via `measureReal_def` before applying the carving identity.
      rw [MeasureTheory.integral_indicator_one (spectralRegion_measurable _ _),
          measureReal_def,
          diracProd_spectralRegion p₀ (bornWeights_nonneg hA ψ)
            (le_of_eq (bornWeights_sum_eq_one hA hψ)) i,
          ENNReal.toReal_ofReal (bornWeights_nonneg hA ψ i)]
    simp_rw [h_each]
    -- Step 2: ∑ λᵢ * bornWeights = re ⟨ψ, A ψ⟩ by the SpectralExpansion identity.
    rw [hermitian_inner_spectral_expansion_re hA ψ]
    rfl
  · -- Integrability of each summand (same shape as `spectralOntic_integrable`).
    intros i _
    refine Integrable.const_mul ?_ _
    exact MeasureTheory.Integrable.indicator (integrable_const (1 : ℝ))
      (spectralRegion_measurable _ _)

end LF4
end CSD
