/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.QuantumChaos.CouplingWitness
public import CsdLean4.LF4.ObservableFlow

/-!
# Q1: the derived coupling — operator norm → flip measure

**Category:** 3-Local (CSD-ontic record layer; `specs/BACKLOG.md` §Q Q1, the
H7 residue).

Every record-coupling measure in the §H thread so far was **posited** (the
`fibreTrigger` quarter-arc: exactly `1/2`). This module derives one: the
trigger is the region where a perturbation `W` **actually moves the state**
— the overlap-deficit region — and its measure is bounded by the operator
norm `‖W − 1‖` through Markov's inequality over the typicality measure. The
same `‖W − 1‖` that prices the carrier at the operator level
(`CV/CarrierPersistence.lean`, `carrier_persistence_window`) now prices the
ontic flip probability: one knob, both levels.

* `overlapDeficit W p` — `1 − Re⟨u, Wu⟩/‖u‖²` on the ray `p`: how far `W`
  moves the state, ray-well-defined (`overlapDeficit_mk`), continuous
  (`continuous_overlapDeficit` — quotient descent, the `momentMap` route),
  valued in `[0, ‖W − 1‖]` (`overlapDeficit_nonneg`, `overlapDeficit_le` —
  the **pointwise operator-norm bound**, Cauchy–Schwarz).
* ★ `measure_deficitTrigger_le` — **the Markov bridge**: the trigger region
  `{δ ≤ overlapDeficit W}` has typicality measure at most `‖W − 1‖/δ`
  (stated multiplicatively in `ℝ≥0∞`). An operator norm has become a
  measure.
* `deficitTriggeredKick` — the record-coupled ontic step: the perturbed
  drive's projective flow, record kicked exactly on the trigger
  (`triggeredRecordKick` instantiated; measure-preserving by the skew
  product).
* ★★ `deficitKick_record_halfLife` — **the derived half-life bound**:
  `δ · μ((intact n)ᶜ) ≤ n · ‖W − 1‖` — the §H5 record half-life with `ε`
  DERIVED from the drive data rather than posited. The H7 residue,
  discharged.
* `deficitKick_persists_of_id` — the sanity anchor: at `W = 1` the deficit
  vanishes identically, the trigger is empty, and persistence is
  almost-sure at every period count — *no perturbation, no erosion*,
  derived rather than assumed.

## Scope

Stated on the corpus's Fin-indexed projective sector (`CPN M`,
`fubiniStudyMeasure`), where the typicality measure lives; the CV chain's
`FieldConfig`-indexed drives connect by re-indexing (bookkeeping, not
mathematics — recorded, not done here). The trigger thresholds at a free
`δ`; the threshold-free sharp version (flip measure = the deficit
distribution itself) would need the distribution's law, not just its
Markov bound — a recorded refinement, not claimed.
-/

@[expose] public section

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization Matrix.Norms.L2Operator

namespace CSD.Empirical.QuantumChaos

open CSD.LF4

variable {M : ℕ}

/-! ### The overlap deficit -/

/-- **The overlap deficit**: how far the unitary `W` moves the ray `p`,
measured by the normalised expectation gap `1 − Re⟨u, Wu⟩/‖u‖²`. Zero iff
`W` fixes the state's expectation; ray-well-defined (`overlapDeficit_mk`);
at most `‖W − 1‖` (`overlapDeficit_le`). -/
noncomputable def overlapDeficit (W : Matrix.unitaryGroup (Fin M) ℂ)
    (p : CPN M) : ℝ :=
  1 - RCLike.re (inner ℂ p.rep (Matrix.toEuclideanLin W.val p.rep))
        / ‖p.rep‖ ^ 2

/-- The deficit computed on any representative. -/
lemma overlapDeficit_mk (W : Matrix.unitaryGroup (Fin M) ℂ)
    (v : EuclideanSpace ℂ (Fin M)) (hv : v ≠ 0) :
    overlapDeficit W (Projectivization.mk ℂ v hv)
      = 1 - RCLike.re (inner ℂ v (Matrix.toEuclideanLin W.val v)) / ‖v‖ ^ 2 := by
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff ℂ (Projectivization.mk ℂ v hv).rep v
        (Projectivization.rep_nonzero _) hv).mp (Projectivization.mk_rep _)
  rw [overlapDeficit, ← ha, Units.smul_def]
  have hsmul : Matrix.toEuclideanLin W.val ((a : ℂ) • v)
      = (a : ℂ) • Matrix.toEuclideanLin W.val v := map_smul _ _ _
  rw [hsmul, inner_smul_left, inner_smul_right, norm_smul]
  have hmod : (starRingEnd ℂ) (a : ℂ) * ((a : ℂ)
        * inner ℂ v (Matrix.toEuclideanLin W.val v))
      = ((‖(a : ℂ)‖ ^ 2 : ℝ) : ℂ)
        * inner ℂ v (Matrix.toEuclideanLin W.val v) := by
    rw [← mul_assoc, mul_comm ((starRingEnd ℂ) (a : ℂ)) ((a : ℂ)),
      Complex.mul_conj']
    norm_cast
  rw [hmod, mul_pow]
  have hre : RCLike.re (((‖(a : ℂ)‖ ^ 2 : ℝ) : ℂ)
        * inner ℂ v (Matrix.toEuclideanLin W.val v))
      = ‖(a : ℂ)‖ ^ 2
        * RCLike.re (inner ℂ v (Matrix.toEuclideanLin W.val v)) := by
    rw [show ((‖(a : ℂ)‖ ^ 2 : ℝ) : ℂ)
        = (RCLike.ofReal (‖(a : ℂ)‖ ^ 2) : ℂ) from rfl,
      RCLike.re_ofReal_mul]
  rw [hre]
  have ha0 : ‖(a : ℂ)‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (Units.ne_zero a))
  rw [mul_div_mul_left _ _ ha0]

/-- The deficit descends continuously (the `continuous_momentMap` route). -/
theorem continuous_overlapDeficit (W : Matrix.unitaryGroup (Fin M) ℂ) :
    Continuous (overlapDeficit W) := by
  rw [Projectivization.continuous_iff_continuous_comp_mk']
  have hcomp : (overlapDeficit W ∘ (Projectivization.mk' ℂ))
      = fun v : { v : EuclideanSpace ℂ (Fin M) // v ≠ 0 } =>
          1 - RCLike.re (inner ℂ (v : EuclideanSpace ℂ (Fin M))
                (Matrix.toEuclideanLin W.val (v : EuclideanSpace ℂ (Fin M))))
              / ‖(v : EuclideanSpace ℂ (Fin M))‖ ^ 2 := by
    funext v
    exact overlapDeficit_mk W (v : EuclideanSpace ℂ (Fin M)) v.2
  rw [hcomp]
  have hlin : Continuous fun v : { v : EuclideanSpace ℂ (Fin M) // v ≠ 0 } =>
      (Matrix.toEuclideanLin W.val (v : EuclideanSpace ℂ (Fin M))
        : EuclideanSpace ℂ (Fin M)) :=
    (Matrix.toEuclideanLin W.val).continuous_of_finiteDimensional.comp
      continuous_subtype_val
  have hnum : Continuous fun v : { v : EuclideanSpace ℂ (Fin M) // v ≠ 0 } =>
      RCLike.re (inner ℂ (v : EuclideanSpace ℂ (Fin M))
        (Matrix.toEuclideanLin W.val (v : EuclideanSpace ℂ (Fin M)))) :=
    (RCLike.continuous_re.comp
      (continuous_inner.comp (continuous_subtype_val.prodMk hlin)))
  have hden : Continuous fun v : { v : EuclideanSpace ℂ (Fin M) // v ≠ 0 } =>
      ‖(v : EuclideanSpace ℂ (Fin M))‖ ^ 2 :=
    (continuous_subtype_val.norm).pow 2
  exact continuous_const.sub
    (hnum.div hden fun v => pow_ne_zero _ (norm_ne_zero_iff.mpr v.2))

/-- The deficit is nonnegative: a unitary cannot raise the normalised
expectation above one (Cauchy–Schwarz + norm preservation). -/
theorem overlapDeficit_nonneg (W : Matrix.unitaryGroup (Fin M) ℂ)
    (p : CPN M) : 0 ≤ overlapDeficit W p := by
  set u := p.rep with hu
  have hu0 : u ≠ 0 := Projectivization.rep_nonzero p
  have hWnorm : ‖(Matrix.toEuclideanLin W.val u : EuclideanSpace ℂ (Fin M))‖
      = ‖u‖ := by
    have h1 := Projectivization.inner_toEuclideanLin_unitary W u u
    have h2 : ‖(Matrix.toEuclideanLin W.val u : EuclideanSpace ℂ (Fin M))‖ ^ 2
        = ‖u‖ ^ 2 := by
      have h3 := congrArg RCLike.re h1
      rwa [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
        ← RCLike.ofReal_pow, ← RCLike.ofReal_pow,
        RCLike.ofReal_re, RCLike.ofReal_re] at h3
    have h4 : (0:ℝ) ≤ ‖(Matrix.toEuclideanLin W.val u : EuclideanSpace ℂ (Fin M))‖ :=
      norm_nonneg _
    nlinarith [norm_nonneg u]
  have hcs : RCLike.re (inner ℂ u (Matrix.toEuclideanLin W.val u)) ≤ ‖u‖ ^ 2 := by
    calc RCLike.re (inner ℂ u (Matrix.toEuclideanLin W.val u))
        ≤ ‖inner ℂ u (Matrix.toEuclideanLin W.val u)‖ := RCLike.re_le_norm _
      _ ≤ ‖u‖ * ‖(Matrix.toEuclideanLin W.val u : EuclideanSpace ℂ (Fin M))‖ :=
          norm_inner_le_norm _ _
      _ = ‖u‖ ^ 2 := by rw [hWnorm]; ring
  have hpos : (0:ℝ) < ‖u‖ ^ 2 := by
    have := norm_pos_iff.mpr hu0
    positivity
  rw [overlapDeficit, sub_nonneg, div_le_one hpos]
  exact hcs

/-- ★ **The pointwise operator-norm bound**: the deficit never exceeds
`‖W − 1‖`. -/
theorem overlapDeficit_le (W : Matrix.unitaryGroup (Fin M) ℂ) (p : CPN M) :
    overlapDeficit W p ≤ ‖W.val - 1‖ := by
  have hu0 : p.rep ≠ 0 := Projectivization.rep_nonzero p
  have hpos : (0:ℝ) < ‖p.rep‖ ^ 2 := by
    have := norm_pos_iff.mpr hu0
    positivity
  have hkey : ‖p.rep‖ ^ 2
        - RCLike.re (inner ℂ p.rep (Matrix.toEuclideanLin W.val p.rep))
      ≤ ‖W.val - 1‖ * ‖p.rep‖ ^ 2 := by
    have hdiff : (inner ℂ p.rep p.rep : ℂ)
          - inner ℂ p.rep (Matrix.toEuclideanLin W.val p.rep)
        = inner ℂ p.rep (Matrix.toEuclideanLin
            ((1 : Matrix (Fin M) (Fin M) ℂ) - W.val) p.rep) := by
      rw [map_sub, LinearMap.sub_apply, inner_sub_right,
        show Matrix.toEuclideanLin (1 : Matrix (Fin M) (Fin M) ℂ)
          = LinearMap.id from Matrix.toLpLin_one 2, LinearMap.id_apply]
    have hre : ‖p.rep‖ ^ 2
          - RCLike.re (inner ℂ p.rep (Matrix.toEuclideanLin W.val p.rep))
        = RCLike.re (inner ℂ p.rep (Matrix.toEuclideanLin
            ((1 : Matrix (Fin M) (Fin M) ℂ) - W.val) p.rep)) := by
      rw [← hdiff, map_sub]
      congr 1
      rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    rw [hre]
    calc RCLike.re (inner ℂ p.rep (Matrix.toEuclideanLin
            ((1 : Matrix (Fin M) (Fin M) ℂ) - W.val) p.rep))
        ≤ ‖inner ℂ p.rep (Matrix.toEuclideanLin
            ((1 : Matrix (Fin M) (Fin M) ℂ) - W.val) p.rep)‖ := RCLike.re_le_norm _
      _ ≤ ‖p.rep‖ * ‖(Matrix.toEuclideanLin ((1 : Matrix (Fin M) (Fin M) ℂ)
            - W.val) p.rep : EuclideanSpace ℂ (Fin M))‖ := norm_inner_le_norm _ _
      _ ≤ ‖p.rep‖ * (‖(1 : Matrix (Fin M) (Fin M) ℂ) - W.val‖ * ‖p.rep‖) := by
          gcongr
          rw [show (Matrix.toEuclideanLin ((1 : Matrix (Fin M) (Fin M) ℂ)
                - W.val) p.rep : EuclideanSpace ℂ (Fin M))
              = (EuclideanSpace.equiv (Fin M) ℂ).symm
                  (((1 : Matrix (Fin M) (Fin M) ℂ) - W.val) *ᵥ p.rep.ofLp) from
            rfl]
          exact Matrix.l2_opNorm_mulVec _ _
      _ = ‖(1 : Matrix (Fin M) (Fin M) ℂ) - W.val‖ * ‖p.rep‖ ^ 2 := by ring
      _ = ‖W.val - 1‖ * ‖p.rep‖ ^ 2 := by rw [norm_sub_rev]
  rw [overlapDeficit,
    show (1:ℝ) - RCLike.re (inner ℂ p.rep
          (Matrix.toEuclideanLin W.val p.rep)) / ‖p.rep‖ ^ 2
        = (‖p.rep‖ ^ 2 - RCLike.re (inner ℂ p.rep
            (Matrix.toEuclideanLin W.val p.rep))) / ‖p.rep‖ ^ 2 from by
      rw [sub_div, div_self hpos.ne'],
    div_le_iff₀ hpos]
  linarith [hkey]

/-! ### The Markov bridge -/

variable (r : Fin M → ℝ)

/-- The trigger: the region the perturbation genuinely moves. -/
noncomputable def deficitTrigger (W : Matrix.unitaryGroup (Fin M) ℂ)
    (δ : ℝ) : Set (CPN M) :=
  {p | δ ≤ overlapDeficit W p}

lemma measurableSet_deficitTrigger (W : Matrix.unitaryGroup (Fin M) ℂ)
    (δ : ℝ) : MeasurableSet (deficitTrigger W δ) :=
  measurableSet_le measurable_const (continuous_overlapDeficit W).measurable

/-- ★ **The Markov bridge**: the trigger's typicality measure is bounded by
the operator norm — `δ · μ_FS(trigger) ≤ ‖W − 1‖`. An operator quantity has
become a measure bound. -/
theorem measure_deficitTrigger_le (W : Matrix.unitaryGroup (Fin M) ℂ)
    {δ : ℝ} (p₀ : CPN M) :
    ENNReal.ofReal δ * fubiniStudyMeasure p₀ (deficitTrigger W δ)
      ≤ ENNReal.ofReal ‖W.val - 1‖ := by
  have hmeas : AEMeasurable
      (fun p => ENNReal.ofReal (overlapDeficit W p)) (fubiniStudyMeasure p₀) :=
    (ENNReal.measurable_ofReal.comp
      (continuous_overlapDeficit W).measurable).aemeasurable
  have hset : deficitTrigger W δ
      = {p | ENNReal.ofReal δ ≤ ENNReal.ofReal (overlapDeficit W p)} := by
    ext p
    rw [deficitTrigger, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
      ENNReal.ofReal_le_ofReal_iff (overlapDeficit_nonneg W p)]
  calc ENNReal.ofReal δ * fubiniStudyMeasure p₀ (deficitTrigger W δ)
      = ENNReal.ofReal δ * fubiniStudyMeasure p₀
          {p | ENNReal.ofReal δ ≤ ENNReal.ofReal (overlapDeficit W p)} := by
        rw [hset]
    _ ≤ ∫⁻ p, ENNReal.ofReal (overlapDeficit W p) ∂(fubiniStudyMeasure p₀) :=
        mul_meas_ge_le_lintegral₀ hmeas (ENNReal.ofReal δ)
    _ ≤ ∫⁻ _, ENNReal.ofReal ‖W.val - 1‖ ∂(fubiniStudyMeasure p₀) :=
        lintegral_mono fun p =>
          ENNReal.ofReal_le_ofReal (overlapDeficit_le W p)
    _ = ENNReal.ofReal ‖W.val - 1‖ := by
        rw [lintegral_const, measure_univ, mul_one]

/-! ### The record-coupled ontic step, and the derived half-life -/

/-- **The deficit-triggered kick**: the perturbed drive's projective flow on
the sector, with the record kicked exactly where the perturbation genuinely
moves the state. -/
noncomputable def deficitTriggeredKick (V W : Matrix.unitaryGroup (Fin M) ℂ)
    (δ : ℝ) (kick : RecordCircle) : CPN M × RecordCircle → CPN M × RecordCircle :=
  triggeredRecordKick (fun p => V • p) (deficitTrigger W δ) kick

theorem deficitTriggeredKick_measurePreserving
    (V W : Matrix.unitaryGroup (Fin M) ℂ) (δ : ℝ) (kick : RecordCircle)
    (p₀ : CPN M) :
    MeasurePreserving (deficitTriggeredKick V W δ kick)
      ((fubiniStudyMeasure p₀).prod volume)
      ((fubiniStudyMeasure p₀).prod volume) :=
  triggeredRecordKick_measurePreserving
    ⟨(continuous_const_smul V).measurable,
      fubiniStudyMeasure_smul_invariant V p₀⟩
    (measurableSet_deficitTrigger W δ) kick

/-- ★★ **The derived half-life bound — the H7 residue, discharged.** A
formed record survives `n` periods of the deficit-triggered dynamics except
on a set whose measure is priced by the *operator norm of the
perturbation*: `δ · μ((intact n)ᶜ) ≤ n · ‖W − 1‖`. The same `‖W − 1‖` that
bounds the carrier's operator-level deviation (`carrier_persistence_window`)
now bounds the ontic flip probability — `ε` derived, not posited. -/
theorem deficitKick_record_halfLife
    (V W : Matrix.unitaryGroup (Fin M) ℂ) (δ : ℝ)
    {kick : RecordCircle} (hkick : kick ≠ 0) (p₀ : CPN M) (n : ℕ) :
    ENNReal.ofReal δ
        * ((fubiniStudyMeasure p₀).prod volume)
            (recordIntact (deficitTriggeredKick V W δ kick) Prod.snd n)ᶜ
      ≤ n * ENNReal.ofReal ‖W.val - 1‖ := by
  have hflip : ((fubiniStudyMeasure p₀).prod volume)
      (recordFlip (deficitTriggeredKick V W δ kick) Prod.snd)
      = fubiniStudyMeasure p₀ (deficitTrigger W δ) := by
    rw [deficitTriggeredKick]
    exact measure_recordFlip_triggeredRecordKick _ _ hkick
  have hflip_meas : MeasurableSet
      (recordFlip (deficitTriggeredKick V W δ kick) Prod.snd) := by
    rw [deficitTriggeredKick, recordFlip_triggeredRecordKick _ _ hkick]
    exact (measurableSet_deficitTrigger W δ).prod MeasurableSet.univ
  have hhalf := recordIntact_compl_measure_le
    (deficitTriggeredKick_measurePreserving V W δ kick p₀) hflip_meas n
  calc ENNReal.ofReal δ
        * ((fubiniStudyMeasure p₀).prod volume)
            (recordIntact (deficitTriggeredKick V W δ kick) Prod.snd n)ᶜ
      ≤ ENNReal.ofReal δ
          * (n • ((fubiniStudyMeasure p₀).prod volume)
              (recordFlip (deficitTriggeredKick V W δ kick) Prod.snd)) := by
        gcongr
    _ = n * (ENNReal.ofReal δ
          * fubiniStudyMeasure p₀ (deficitTrigger W δ)) := by
        rw [hflip, nsmul_eq_mul]
        ring
    _ ≤ n * ENNReal.ofReal ‖W.val - 1‖ := by
        gcongr
        exact measure_deficitTrigger_le W p₀

/-! ### The sanity anchor: no perturbation, no erosion -/

/-- The identity perturbation has zero deficit everywhere. -/
theorem overlapDeficit_one (p : CPN M) :
    overlapDeficit (1 : Matrix.unitaryGroup (Fin M) ℂ) p = 0 := by
  have hu0 : p.rep ≠ 0 := Projectivization.rep_nonzero p
  have hpos : (0:ℝ) < ‖p.rep‖ ^ 2 := by
    have := norm_pos_iff.mpr hu0
    positivity
  rw [overlapDeficit,
    show ((1 : Matrix.unitaryGroup (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ)
      = (1 : Matrix (Fin M) (Fin M) ℂ) from rfl,
    show Matrix.toEuclideanLin (1 : Matrix (Fin M) (Fin M) ℂ)
      = LinearMap.id from Matrix.toLpLin_one 2, LinearMap.id_apply,
    inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re,
    div_self hpos.ne']
  ring

/-- **No perturbation, no erosion — derived**: at `W = 1` the trigger is
empty, the coupling is null, and a formed record persists almost surely at
every period count. -/
theorem deficitKick_persists_of_id
    (V : Matrix.unitaryGroup (Fin M) ℂ) {δ : ℝ} (hδ : 0 < δ)
    {kick : RecordCircle} (hkick : kick ≠ 0) (p₀ : CPN M) (n : ℕ) :
    ((fubiniStudyMeasure p₀).prod volume)
        (recordIntact (deficitTriggeredKick V 1 δ kick) Prod.snd n)ᶜ = 0 := by
  have hempty : deficitTrigger (1 : Matrix.unitaryGroup (Fin M) ℂ) δ = ∅ := by
    ext p
    rw [deficitTrigger, Set.mem_ofPred_eq, overlapDeficit_one]
    simp only [Set.mem_empty_iff_false, iff_false, not_le]
    exact hδ
  have hflip_meas : MeasurableSet
      (recordFlip (deficitTriggeredKick V 1 δ kick) Prod.snd) := by
    rw [deficitTriggeredKick, recordFlip_triggeredRecordKick _ _ hkick]
    exact (measurableSet_deficitTrigger 1 δ).prod MeasurableSet.univ
  refine recordIntact_compl_null_of_flip_null
    (deficitTriggeredKick_measurePreserving V 1 δ kick p₀) hflip_meas ?_ n
  rw [deficitTriggeredKick, measure_recordFlip_triggeredRecordKick _ _ hkick,
    hempty]
  exact measure_empty

end CSD.Empirical.QuantumChaos
