import CsdLean4.LF4.SingletKahler

/-!
# LF4 §14: observable correspondence for single-qubit Stern-Gerlach

**Category:** 3-Local (LF4 §14 discharge — projector-level observable
correspondence on the single-qubit `N = 2` Kähler instance).

Discharges `LF4-todo §14` (observable correspondence) **for projector
observables** on the single-qubit Kähler instance `Σ = ℂℙ¹ × T²`, and
lifts the Stern-Gerlach Born predictions from `Empirical/CSD/SternGerlach.lean`
(bridge bundle) to a real **LF3-chain frequency-convergence capstone**
(`sg_frequency_convergence`), parallel to
`ofKählerPreparation_singlet_frequency_convergence` but at `N = 2`.

## What §14 means for projector observables

For a single-qubit projector observable `P = spinProj s a` (the `s`-eigen
projector of `σ·a`) and the `|+_z⟩` preparation, the §14 claim is:

```
⟨zPlus, (toEuclideanLin P) zPlus⟩ = ∫ 1_{sgRegion s a} dμψ
                                 = (μψ (sgRegion s a)).toReal.
```

Both sides equal `sgBorn s a := (1 + s · a_z) / 2`. The Hilbert side is
the (0,0) entry of `P` (since `zPlus = e_0`); the ontic side is the
volume of the carved fibre arc.

**Generality.** This discharges §14 for **projector** observables on
`|+z⟩`. The general self-adjoint case follows by spectral decomposition
`A = ∑ λᵢ Pᵢ` (linearity of integration in `μψ` + Hilbert linearity in
the Pᵢ); not formalised here.

## What `sg_frequency_convergence` gives

For i.i.d. trials with the posited fibre law `sgMuPsi`, the empirical
frequency of the `(s, a)` SG outcome converges a.s. to `(1 + s · a_z)/2`.
For `a = ẑ`: frequencies → `1` (`s = +`) or `0` (`s = −`). For `a = x̂`:
frequencies → `1/2` either way. The four SG Born identities
(`Empirical/QM/SternGerlach.lean`'s `born_zPlus_zPlus` etc.) are exactly
the corresponding values of `sgBorn`.

## Tier-2 honesty (unchanged from ofKählerPreparation)

`sgRegion s a` is **carved to volume `sgBorn s a`** by construction, so
the §14 equation `Hilbert = ontic` holds because both sides equal
`sgBorn s a` by separate routes (one via spinProj's `(0,0)` entry, one
via the carving). This is the same eq-12-by-construction realisation
as the singlet capstone: faithful concrete realisation on a compact
Kähler `Σ`, not a derivation of Born from independent geometry.

## Axiom posture

Foundational triple only. No Busch, no `invariant_measure_uniqueness`.
The `kBridge` constructor for `N = 2` is the same axiom-free marginal
bridge as for `N = 4`.

## Source

- Stern, Gerlach 1922 (the SG Born identities).
- The §14 observable correspondence framing is new with this corpus.
-/

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization
open CSD.LF3

namespace CSD
namespace LF4

/-! ### The single-qubit `|+z⟩` state -/

/-- The `|+z⟩` state vector in `EuclideanSpace ℂ (Fin 2)`. -/
noncomputable def zPlusVec : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 (1 : ℂ)

private lemma zPlusVec_ofLp_zero : zPlusVec.ofLp 0 = (1 : ℂ) := by
  simp [zPlusVec, EuclideanSpace.single]

private lemma zPlusVec_ofLp_one : zPlusVec.ofLp 1 = (0 : ℂ) := by
  simp [zPlusVec, EuclideanSpace.single]

lemma zPlusVec_norm : ‖zPlusVec‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two,
             show zPlusVec.ofLp 0 = (1 : ℂ) from zPlusVec_ofLp_zero,
             show zPlusVec.ofLp 1 = (0 : ℂ) from zPlusVec_ofLp_one,
             norm_one, norm_zero, one_pow, ne_eq, OfNat.ofNat_ne_zero,
             not_false_eq_true, zero_pow, add_zero]
  exact Real.sqrt_one

lemma zPlusVec_ne_zero : (zPlusVec : EuclideanSpace ℂ (Fin 2)) ≠ 0 := by
  intro h
  have : ‖zPlusVec‖ = 0 := by rw [h, norm_zero]
  rw [zPlusVec_norm] at this
  exact one_ne_zero this

/-! ### Stern-Gerlach Born value and bounds -/

/-- **Stern-Gerlach Born value.** For `|+z⟩` preparation, measurement axis
`a`, outcome `s ∈ {+, −}`: `P(s | a, |+z⟩) = (1 + s · a_z) / 2`. -/
noncomputable def sgBorn (s : Sign) (a : DetectorSetting) : ℝ :=
  (1 + s.val * a.vec 2) / 2

lemma sgBorn_nonneg (s : Sign) (a : DetectorSetting) : 0 ≤ sgBorn s a := by
  unfold sgBorn
  have habs := a.sum_sq_components_eq_one
  have hz : a.vec 2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (a.vec 0), sq_nonneg (a.vec 1)]
  have hz_abs : -1 ≤ a.vec 2 ∧ a.vec 2 ≤ 1 := by
    constructor <;> nlinarith [sq_abs (a.vec 2), abs_nonneg (a.vec 2)]
  cases s <;> simp [Sign.val] <;> linarith [hz_abs.1, hz_abs.2]

lemma sgBorn_le_one (s : Sign) (a : DetectorSetting) : sgBorn s a ≤ 1 := by
  unfold sgBorn
  have habs := a.sum_sq_components_eq_one
  have hz : a.vec 2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (a.vec 0), sq_nonneg (a.vec 1)]
  have hz_abs : -1 ≤ a.vec 2 ∧ a.vec 2 ≤ 1 := by
    constructor <;> nlinarith [sq_abs (a.vec 2), abs_nonneg (a.vec 2)]
  cases s <;> simp [Sign.val] <;> linarith [hz_abs.1, hz_abs.2]

/-! ### Single-qubit expectation identity (the Hilbert side of §14) -/

/-- **Single-qubit expectation formula.** The expectation of a 2×2 matrix
`M` on `|+z⟩` is just its `(0,0)` entry, since `zPlus = e_0`. -/
lemma zPlus_expectation (M : Matrix (Fin 2) (Fin 2) ℂ) :
    inner ℂ zPlusVec (toEuclideanLin M zPlusVec) = M 0 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin,
      dotProduct, Fin.sum_univ_two]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.star_apply,
             show zPlusVec.ofLp 0 = (1 : ℂ) from zPlusVec_ofLp_zero,
             show zPlusVec.ofLp 1 = (0 : ℂ) from zPlusVec_ofLp_one,
             star_zero, star_one, mul_zero, mul_one, add_zero]

/-- **Single-qubit Born identity for the spin projector.** For the `|+z⟩`
preparation, the expectation of `spinProj s a` equals `(1 + s · a_z)/2`. -/
lemma zPlus_spinProj_expectation (s : Sign) (a : DetectorSetting) :
    inner ℂ zPlusVec (toEuclideanLin (spinProj s a) zPlusVec) = (sgBorn s a : ℂ) := by
  rw [zPlus_expectation, spinProj_apply_00]
  unfold sgBorn
  push_cast
  ring

/-! ### Single-qubit Kähler outcome regions and fibre measure -/

/-- The projective ray `[|+z⟩] ∈ ℂℙ¹`. -/
noncomputable def zRay : CPN 2 :=
  Projectivization.mk ℂ zPlusVec zPlusVec_ne_zero

/-- The Stern-Gerlach outcome region for sign `s` and direction `a`:
a fibre arc of measure `sgBorn s a` (carved by construction). -/
noncomputable def sgRegion (s : Sign) (a : DetectorSetting) : Set (KSigma 2) :=
  Set.univ ×ˢ (fibreArc (sgBorn s a) ×ˢ Set.univ)

lemma sgRegion_measurable (s : Sign) (a : DetectorSetting) :
    MeasurableSet (sgRegion s a) := by
  unfold sgRegion
  exact MeasurableSet.univ.prod ((fibreArc_measurable _).prod MeasurableSet.univ)

/-- The single-qubit posited fibre law for `|+z⟩`: Dirac at the
`|+z⟩` ray, tensored with the torus volume. Pushes through `π = pr₁`
to a Dirac at `zRay`. -/
noncomputable def sgMuPsi : Measure (KSigma 2) :=
  (Measure.dirac zRay).prod (volume : Measure KTorus)

instance instProbSgMuPsi : IsProbabilityMeasure sgMuPsi := by
  unfold sgMuPsi; infer_instance

lemma sgMuPsi_push :
    Measure.map (Prod.fst : KSigma 2 → CPN 2) sgMuPsi = Measure.dirac zRay := by
  unfold sgMuPsi
  rw [← Measure.fst, Measure.fst_prod]

/-- **The carving identity: `μψ(sgRegion s a) = sgBorn s a`**. -/
lemma sgMuPsi_sgRegion (s : Sign) (a : DetectorSetting) :
    sgMuPsi (sgRegion s a) = ENNReal.ofReal (sgBorn s a) := by
  unfold sgMuPsi sgRegion
  rw [Measure.prod_prod, measure_univ, one_mul]
  show (volume : Measure KTorus)
      (fibreArc (sgBorn s a) ×ˢ Set.univ) = _
  rw [show (volume : Measure KTorus)
        = (volume : Measure (AddCircle (1:ℝ))).prod
            (volume : Measure (AddCircle (1:ℝ))) from rfl]
  rw [Measure.prod_prod, measure_univ, mul_one]
  exact fibreArc_volume ⟨sgBorn_nonneg s a, sgBorn_le_one s a⟩

/-! ### §14 observable correspondence and SG frequency capstone -/

/-- **§14 observable correspondence for the SG projectors.** For the
single-qubit spin projector `spinProj s a` and the `|+z⟩` preparation,
the Hilbert expectation equals the ontic measure of the outcome region
(as a real number, coerced back to `ℂ`):

```
⟨zPlus, (toEuclideanLin (spinProj s a)) zPlus⟩
  = ((μψ (sgRegion s a)).toReal : ℂ).
```

Both sides equal `(sgBorn s a : ℂ)`: the Hilbert side via the
`(0,0)`-entry of `spinProj s a` (`zPlus_spinProj_expectation`), the
ontic side via the carving identity (`sgMuPsi_sgRegion`). -/
theorem sg_observable_correspondence (s : Sign) (a : DetectorSetting) :
    inner ℂ zPlusVec (toEuclideanLin (spinProj s a) zPlusVec)
      = ((sgMuPsi (sgRegion s a)).toReal : ℂ) := by
  rw [zPlus_spinProj_expectation, sgMuPsi_sgRegion,
      ENNReal.toReal_ofReal (sgBorn_nonneg s a)]

open Filter Topology in
/-- **CSD Stern-Gerlach frequency convergence (LF3-chain lift, §14
discharge applied).** For i.i.d. trials drawing microstates from the
posited fibre law `sgMuPsi` (the `|+z⟩` preparation on the single-qubit
Kähler instance `Σ = ℂℙ¹ × T²`), the empirical frequency of the SG
outcome at sign `s` and direction `a` converges almost surely to the QM
Born value `(1 + s · a_z) / 2`.

This is the **non-vacuous LF3-chain Stern-Gerlach capstone**, parallel
to `LF4.ofKählerPreparation_singlet_frequency_convergence` but at the
single-qubit level. Foundational triple only (no Busch, no
invariant-measure-uniqueness). -/
theorem sg_frequency_convergence
    (s : Sign) (a : DetectorSetting)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {X : ℕ → Ω → KSigma 2} (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = sgMuPsi)
    (hindep :
      Pairwise
        (Function.onFun
          (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n => Set.indicator (X n ⁻¹' sgRegion s a) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator (X i ⁻¹' sgRegion s a) (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        atTop
        (nhds (sgBorn s a)) := by
  have hfreq :=
    LF1.freq_tendsto_of_iid hX hlaw (sgRegion_measurable s a) hindep
  rwa [sgMuPsi_sgRegion, ENNReal.toReal_ofReal (sgBorn_nonneg s a)] at hfreq

/-! ### §14.2 single-qubit Pauli observable

Beyond the §14.1 projector case. The Pauli observable `σ·a` has eigenvalues
`±1` and the spectral decomposition `σ·a = (+1)·spinProj(+a) + (−1)·spinProj(−a)`.
Its ontic counterpart is the signed indicator `2·1_{R_+(a)} − 1`, which equals
`+1` on the `+`-outcome region and `−1` everywhere else (which is the
`−`-outcome region by measurable partition). The integral against `μψ` matches
the Hilbert expectation `⟨zPlus, σ·a · zPlus⟩ = a_z`.

This is the **first concrete §14.2 step beyond projectors**, demonstrating
the spectral-decomposition pattern at single-qubit level. Generalisation to
arbitrary bounded self-adjoint via Mathlib's spectral theorem is mechanical
on top. -/

/-- **Ontic counterpart of `pauliDot a`** on the `|+z⟩` preparation: `+1` on
the `+`-outcome region `sgRegion + a`, `−1` elsewhere (the `−`-outcome region
by measurable partition). The signed-indicator decomposition
`2·1_{R_+} − 1` is the simplest two-eigenvalue spectral-decomposition form. -/
noncomputable def pauliDotOntic (a : DetectorSetting) : KSigma 2 → ℝ :=
  fun σ => 2 * Set.indicator (sgRegion Sign.plus a) (fun _ => (1 : ℝ)) σ - 1

lemma pauliDotOntic_measurable (a : DetectorSetting) :
    Measurable (pauliDotOntic a) := by
  unfold pauliDotOntic
  refine Measurable.sub ?_ measurable_const
  refine Measurable.const_mul ?_ 2
  exact (measurable_const : Measurable (fun _ : KSigma 2 => (1 : ℝ))).indicator
    (sgRegion_measurable Sign.plus a)

/-- **Integral of the Pauli ontic counterpart.** `∫ pauliDotOntic a dμψ = a_z`,
matching `⟨zPlus, pauliDot a zPlus⟩ = a_z` (the Hilbert expectation). -/
lemma pauliDotOntic_integral (a : DetectorSetting) :
    ∫ σ, pauliDotOntic a σ ∂sgMuPsi = a.vec 2 := by
  unfold pauliDotOntic
  have hint_R : Integrable
      (Set.indicator (sgRegion Sign.plus a) (fun _ : KSigma 2 => (1 : ℝ))) sgMuPsi :=
    (integrable_const (1 : ℝ)).indicator (sgRegion_measurable Sign.plus a)
  have hint_2R : Integrable
      (fun σ => 2 * Set.indicator (sgRegion Sign.plus a)
        (fun _ : KSigma 2 => (1 : ℝ)) σ) sgMuPsi :=
    hint_R.const_mul 2
  have hint_1 : Integrable (fun _ : KSigma 2 => (1 : ℝ)) sgMuPsi := integrable_const _
  rw [integral_sub hint_2R hint_1, integral_const_mul,
      integral_indicator (sgRegion_measurable Sign.plus a),
      setIntegral_const, integral_const, smul_eq_mul, smul_eq_mul,
      Measure.real, Measure.real, sgMuPsi_sgRegion, measure_univ,
      ENNReal.toReal_ofReal (sgBorn_nonneg Sign.plus a), ENNReal.toReal_one]
  unfold sgBorn
  simp [Sign.val]
  ring

/-- **§14.2 observable correspondence for `pauliDot a`** (first non-projector
case). The Hilbert expectation of `σ·a` on `|+z⟩` equals the `μψ`-integral
of its ontic counterpart. Both sides equal `a_z`: the Hilbert side via the
`(0,0)` entry of `pauliDot a` (`pauliDot_apply_00`), the ontic side via the
signed-indicator integration (`pauliDotOntic_integral`). -/
theorem pauliDot_observable_correspondence (a : DetectorSetting) :
    inner ℂ zPlusVec (toEuclideanLin (pauliDot a) zPlusVec)
      = ((∫ σ, pauliDotOntic a σ ∂sgMuPsi : ℝ) : ℂ) := by
  rw [zPlus_expectation, pauliDot_apply_00, pauliDotOntic_integral]

end LF4
end CSD
