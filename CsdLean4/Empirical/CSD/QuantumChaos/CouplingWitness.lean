/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.QuantumChaos.RecordDegradation

/-!
# The small-coupling witness: the half-life bound bites (§H continuation)

**Category:** 6-Empirical-CSD (the CSD reading of stroboscopic dynamics).

`RecordDegradation.lean` priced coupled post-record driving by the record
half-life bound `μ (intact n)ᶜ ≤ n · ε`. This module shows the bound is not
vacuous: a concrete weakly coupled drive with coupling strength strictly
between `0` and `1`.

* `triggeredRecordKick F C δ` — the drive: the system evolves by `F`; the
  record (a circle coordinate) is kicked by `δ` exactly when the system lies
  in the trigger region `C`. Measure-preserving whenever `F` is, by the
  skew-product theorem (each record slice is a rotation).
* `recordFlip_triggeredRecordKick` — for `δ ≠ 0` the coupling set IS the
  trigger cylinder `C ×ˢ univ`, so the coupling strength is exactly `μ C`:
  the geometry of the trigger region *is* the record-degradation rate.
* ★ `fibreTriggeredKick` and its lemmas — the CSD instantiation on
  `(KSigma N) × S¹`: the trigger is a fibre-arc cylinder (first torus angle
  in a quarter-radius ball), giving coupling strength **exactly `1/2`**
  (`AddCircle.volume_closedBall`): `0 < ε < 1`, and the half-life bound reads
  "a formed record survives `n` periods of this drive except on measure at
  most `n/2`" — a bound that genuinely bites.

Honest scope: the witness shows the PRICE is non-trivial; whether the bound
is attained (actual erasure rate) is a dynamics question beyond the pilot,
sitting with the thread's diagnostics work. Cross-references:
`specs/external-library-map.md` §H, `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Metric
open scoped Classical

namespace CSD.Empirical.QuantumChaos

open _root_.QuantumChaos CSD.LF4

/-! ### The triggered record kick, generically -/

section Generic

variable {A : Type*} [MeasurableSpace A]

/-- The circle-valued record coordinate. -/
abbrev RecordCircle : Type := AddCircle (1 : ℝ)

/-- **The triggered record kick**: the system evolves by `F`; the record is
kicked by `δ` exactly when the system lies in the trigger region `C`. -/
noncomputable def triggeredRecordKick (F : A → A) (C : Set A)
    (δ : RecordCircle) : A × RecordCircle → A × RecordCircle :=
  fun x => (F x.1, x.2 + if x.1 ∈ C then δ else 0)

/-- The triggered kick is measure-preserving whenever the system step is:
skew product with rotation slices. -/
theorem triggeredRecordKick_measurePreserving
    {F : A → A} {μ : Measure A} [SFinite μ] (hF : MeasurePreserving F μ μ)
    {C : Set A} (hC : MeasurableSet C) (δ : RecordCircle) :
    MeasurePreserving (triggeredRecordKick F C δ)
      (μ.prod volume) (μ.prod volume) := by
  have hmap : ∀ c : RecordCircle,
      Measure.map (fun r : RecordCircle => r + c) volume = volume := fun c => by
    rw [show (fun r : RecordCircle => r + c) = (fun r => c + r) from
      funext fun r => add_comm r c]
    exact map_add_left_eq_self volume c
  have h := hF.skew_product
    (g := fun (a : A) (r : RecordCircle) => r + if a ∈ C then δ else 0)
    (measurable_snd.add
      (Measurable.ite (measurable_fst hC) measurable_const measurable_const))
    (Filter.Eventually.of_forall fun a => by
      rcases Classical.em (a ∈ C) with h | h
      · simp only [if_pos h]
        exact hmap δ
      · simp only [if_neg h]
        exact hmap 0)
  exact h

omit [MeasurableSpace A] in
/-- For `δ ≠ 0` the coupling set of the triggered kick is exactly the
trigger cylinder: the trigger geometry IS the coupling. -/
theorem recordFlip_triggeredRecordKick
    (F : A → A) (C : Set A) {δ : RecordCircle} (hδ : δ ≠ 0) :
    recordFlip (triggeredRecordKick F C δ) Prod.snd = C ×ˢ Set.univ := by
  ext ⟨a, r⟩
  simp only [recordFlip, triggeredRecordKick, Set.mem_ofPred_eq, Set.mem_prod,
    Set.mem_univ, and_true]
  by_cases h : a ∈ C
  · simp only [h, if_true, iff_true]
    intro heq
    exact hδ (add_left_cancel (show r + δ = r + 0 by rw [add_zero]; exact heq))
  · simp [h]

/-- The coupling strength of the triggered kick is the trigger region's
measure. -/
theorem measure_recordFlip_triggeredRecordKick
    (F : A → A) {μ : Measure A} (C : Set A) {δ : RecordCircle} (hδ : δ ≠ 0) :
    (μ.prod volume) (recordFlip (triggeredRecordKick F C δ) Prod.snd)
      = μ C := by
  rw [recordFlip_triggeredRecordKick F C hδ, Measure.prod_prod, measure_univ,
    mul_one]

end Generic

/-! ### The CSD instantiation: a fibre-triggered kick with `ε = 1/2` -/

variable {N : ℕ}

/-- The fibre-arc trigger: the first torus angle lies within a quarter
radius of `0`. A context-style region read off the ontic fibre alone. -/
noncomputable def fibreTrigger (N : ℕ) : Set (KSigma N) :=
  {x | x.2.1 ∈ closedBall (0 : AddCircle (1 : ℝ)) (1 / 4)}

lemma fibreTrigger_measurableSet : MeasurableSet (fibreTrigger N) :=
  (measurable_fst.comp measurable_snd) measurableSet_closedBall

/-- The trigger's Liouville measure is exactly `1/2`:
`vol(closedBall 0 (1/4)) = min 1 (2·(1/4)) = 1/2` on the unit circle. -/
lemma kMuL_fibreTrigger [NeZero N] (p₀ : CPN N) :
    kMuL p₀ (fibreTrigger N) = ENNReal.ofReal (1 / 2) := by
  rw [show fibreTrigger N
      = (Set.univ : Set (CPN N)) ×ˢ
          ((closedBall (0 : AddCircle (1 : ℝ)) (1 / 4)) ×ˢ
            (Set.univ : Set (AddCircle (1 : ℝ)))) from by
    ext ⟨p, θ⟩; simp [fibreTrigger]]
  rw [kMuL, Measure.prod_prod, measure_univ, one_mul, Measure.volume_eq_prod,
    Measure.prod_prod, measure_univ, mul_one, AddCircle.volume_closedBall]
  norm_num

/-- **The fibre-triggered kick**: the Floquet ontic step, with the record
kicked whenever the first fibre angle lies in the quarter-ball arc. -/
noncomputable def fibreTriggeredKick (U : Matrix.unitaryGroup (Fin N) ℂ)
    (δ : RecordCircle) : KSigma N × RecordCircle → KSigma N × RecordCircle :=
  triggeredRecordKick (floquetOnticStep U) (fibreTrigger N) δ

/-- The fibre-triggered kick preserves `kMuL ⊗ vol`. -/
theorem fibreTriggeredKick_measurePreserving [NeZero N]
    (U : Matrix.unitaryGroup (Fin N) ℂ) (p₀ : CPN N) (δ : RecordCircle) :
    MeasurePreserving (fibreTriggeredKick U δ)
      ((kMuL p₀).prod volume) ((kMuL p₀).prod volume) :=
  triggeredRecordKick_measurePreserving
    (floquetOnticStep_measurePreserving U p₀) fibreTrigger_measurableSet δ

/-- ★ **The coupling strength is exactly `1/2`** — strictly between `0` and
`1`: the half-life bound genuinely bites. -/
theorem fibreTriggeredKick_coupling [NeZero N]
    (U : Matrix.unitaryGroup (Fin N) ℂ) (p₀ : CPN N) {δ : RecordCircle}
    (hδ : δ ≠ 0) :
    ((kMuL p₀).prod volume)
        (recordFlip (fibreTriggeredKick U δ) Prod.snd)
      = ENNReal.ofReal (1 / 2) := by
  rw [fibreTriggeredKick,
    measure_recordFlip_triggeredRecordKick (floquetOnticStep U)
      (fibreTrigger N) hδ,
    kMuL_fibreTrigger p₀]

/-- ★ **The half-life bound, bitten**: under the fibre-triggered kick a
formed record survives `n` periods except on measure at most `n/2`. -/
theorem fibreTriggeredKick_record_halfLife [NeZero N]
    (U : Matrix.unitaryGroup (Fin N) ℂ) (p₀ : CPN N) {δ : RecordCircle}
    (hδ : δ ≠ 0) (n : ℕ) :
    ((kMuL p₀).prod volume)
        (recordIntact (fibreTriggeredKick U δ) Prod.snd n)ᶜ
      ≤ n • ENNReal.ofReal (1 / 2) := by
  rw [← fibreTriggeredKick_coupling U p₀ hδ]
  refine recordIntact_compl_measure_le
    (fibreTriggeredKick_measurePreserving U p₀ δ) ?_ n
  rw [fibreTriggeredKick,
    recordFlip_triggeredRecordKick (floquetOnticStep U) (fibreTrigger N) hδ]
  exact fibreTrigger_measurableSet.prod MeasurableSet.univ

end CSD.Empirical.QuantumChaos
