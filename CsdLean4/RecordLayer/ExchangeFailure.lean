/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.OperationalGeometry
public import CsdLean4.RecordLayer.MacrostateStability

/-!
# Failure of the exchange, and the retention window

**Category:** 7-SigmaLayer (the record layer — robustness of the clock-and-echo capstone).
BACKLOG #189 (out of #39; the seventh of #183–#189).

#184 bounded the *deterministic* timing error. This file bounds the *probability* that the complete
exchange is invalid — some record failing to display the message — and states the retention
condition under which the records are all alive when the coordinates are read.

**Failure.** The exchange is **valid** for message `b` when all three registers display `b` at their
readout times. A register fails only if it was **not ready** or the exchange state it read **did not
carry the message**: `recordFailure ⊆ notReady ∪ messageFailure` (★ `recordFailure_subset_union`),
because a ready register reading `b` is written with `b` (`register_at_readout`). Hence, for *any*
preparation measure, by the **union bound** over the three writes — no independence is proved and
none is used —

  `μ {invalid} ≤ Σ_i μ (recordFailure i) ≤ Σ_i (μ (notReady i) + μ (messageFailure i))`

(★★ `measure_invalid_le`, `measure_invalid_le'`), and for a probability measure
`μ {valid} ≥ 1 − Σ_i μ (recordFailure i)` (`prob_valid_ge`). The exact witness never fails
(`exchangeValid_xPrep`). The quantitative input for a register prepared off the ready arc is the band
bound of #103 — the Haar measure of a `rep`-band is at most its width (`volume_band_le`, consuming
`volume_rep_preimage_Ioc_le`) — and the write has **no tolerance**: a register just past the ready
arc misses the pointer arc by exactly its excess (★ `pshift_shearAmt_notMem_pointerArc`). That is a
finding about the arc mechanism of `ShearWitness.lean`, not a defect of this file.

**Retention.** A record lifetime `τ_R ≥ 2 τ_hop` is sufficient: every record is alive at the return
readout, where the radar coordinates are formed (★★ `retention_sufficient`, `records_at_return`),
through the corpus's `record_persists_on_interval`. Here it is also *exact*: after its readout a
register is frozen (`register_frozen`), so the window is unbounded.

## Honest scope

* ⚠️ `carrier_persistence_window` (`CV/CarrierPersistence.lean`) is **not consumed**: it bounds the
  drift of a *field-mode* readout under a periodic unitary perturbation, and this arena's records are
  torus arcs with no perturbation model. Where a perturbed carrier is the record, that theorem is the
  quantitative retention statement; here retention is exact and needs no rate.
* The failure bound is a union bound. Independence of the three writes is neither claimed nor
  needed, and a product bound would require a product preparation measure, which is not assumed.
* `messageFailure` is the exchange state at a readout time not reading the message. For the exact
  message point it is empty; for a perturbed exchange state its measure is the input, not an output.

References: `specs/BACKLOG.md` #189, #184, #186, #187, #39; `RecordLayer/RecordedExchange.lean`,
`RecordLayer/MacrostateStability.lean` (`volume_rep_preimage_Ioc_le`, #103),
`RecordLayer/RecordPersistence.lean`, `CV/CarrierPersistence.lean`.
-/

@[expose] public section

open MeasureTheory Set CSD.CV

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {K : ℕ}

/-! ### Validity and the failure events -/

/-- **The exchange is valid for message `b`**: all three registers display `b` at their readout
times. -/
def ExchangeValid (J ħ T : ℝ) (b : Fin 2) (x : XArena K) : Prop :=
  ∀ i : Fin 3, (xEvolve J ħ T (-1) (readTime J ħ i) x).2.2 i ∈ pointerArc 2 b

/-- Register `i` fails: it does not display `b` at its readout time. -/
def recordFailure (J ħ T : ℝ) (b : Fin 2) (i : Fin 3) : Set (XArena K) :=
  {x | (xEvolve J ħ T (-1) (readTime J ħ i) x).2.2 i ∉ pointerArc 2 b}

/-- Register `i` was not ready. -/
def notReady (i : Fin 3) : Set (XArena K) := {x | x.2.2 i ∉ readyArc 2}

/-- The exchange state register `i` reads does not carry the message. -/
def messageFailure (J ħ : ℝ) (b : Fin 2) (i : Fin 3) : Set (XArena K) :=
  {x | readAt J ħ i (-1) x.1 ≠ b}

/-- At its readout time, register `i` is the ready register shifted by the bit it read. -/
theorem register_at_readout {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (x : XArena K) (i : Fin 3) :
    (xEvolve J ħ T (-1) (readTime J ħ i) x).2.2 i
      = pshift (shearAmt 2 (readAt J ħ i (-1) x.1)) (x.2.2 i) := by
  rw [xEvolve_register, arrived_of_le le_rfl,
    arrived_of_lt (show (-1 : ℝ) < readTime J ħ i by linarith [readTime_nonneg hJ hħ i]),
    sub_zero, one_mul]

/-- ★ **A register fails only if it was not ready or read the wrong message.** -/
theorem recordFailure_subset_union {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (b : Fin 2) (i : Fin 3) :
    recordFailure (K := K) J ħ T b i ⊆ notReady i ∪ messageFailure J ħ b i := by
  intro x hx
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  have hready : x.2.2 i ∈ readyArc 2 := not_not.mp hcon.1
  have hread : readAt J ħ i (-1) x.1 = b := not_not.mp hcon.2
  apply hx
  rw [register_at_readout hJ hħ, hread]
  exact pshift_shearAmt_mem_pointerArc b hready

theorem not_exchangeValid_iff (J ħ T : ℝ) (b : Fin 2) (x : XArena K) :
    ¬ ExchangeValid J ħ T b x ↔ ∃ i, x ∈ recordFailure J ħ T b i := by
  exact not_forall

theorem invalid_eq_iUnion (J ħ T : ℝ) (b : Fin 2) :
    {x : XArena K | ¬ ExchangeValid J ħ T b x} = ⋃ i, recordFailure J ħ T b i := by
  ext x
  rw [Set.mem_ofPred_eq, not_exchangeValid_iff, Set.mem_iUnion]

theorem measurableSet_recordFailure (J ħ T : ℝ) (b : Fin 2) (i : Fin 3) :
    MeasurableSet (recordFailure (K := K) J ħ T b i) :=
  (((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)).comp
    (measurable_xEvolve J ħ T (-1) (readTime J ħ i))) (measurableSet_pointerArc b).compl

theorem measurableSet_invalid (J ħ T : ℝ) (b : Fin 2) :
    MeasurableSet {x : XArena K | ¬ ExchangeValid J ħ T b x} := by
  rw [invalid_eq_iUnion]
  exact MeasurableSet.iUnion fun i => measurableSet_recordFailure J ħ T b i

/-! ### The union bound -/

/-- ★★ **The union bound over the three writes**, for any preparation measure. -/
theorem measure_invalid_le (μ : Measure (XArena K)) (J ħ T : ℝ) (b : Fin 2) :
    μ {x | ¬ ExchangeValid J ħ T b x} ≤ ∑ i : Fin 3, μ (recordFailure J ħ T b i) := by
  rw [invalid_eq_iUnion]
  exact measure_iUnion_fintype_le μ _

/-- The union bound with the two failure sources separated: not ready, or wrong message. -/
theorem measure_invalid_le' (μ : Measure (XArena K)) {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ)
    (b : Fin 2) :
    μ {x | ¬ ExchangeValid J ħ T b x}
      ≤ ∑ i : Fin 3, (μ (notReady i) + μ (messageFailure J ħ b i)) := by
  refine (measure_invalid_le μ J ħ T b).trans (Finset.sum_le_sum fun i _ => ?_)
  exact (measure_mono (recordFailure_subset_union hJ hħ b i)).trans (measure_union_le _ _)

/-- For a probability measure, the exchange is valid with probability at least
`1 − Σ_i μ (recordFailure i)`. -/
theorem prob_valid_ge (μ : Measure (XArena K)) [IsProbabilityMeasure μ] (J ħ T : ℝ) (b : Fin 2) :
    1 - ∑ i : Fin 3, μ (recordFailure J ħ T b i) ≤ μ {x | ExchangeValid J ħ T b x} := by
  have h : {x : XArena K | ExchangeValid J ħ T b x} = {x | ¬ ExchangeValid J ħ T b x}ᶜ := by
    ext x
    simp
  rw [h, prob_compl_eq_one_sub (measurableSet_invalid J ħ T b)]
  exact tsub_le_tsub_left (measure_invalid_le μ J ħ T b) 1

/-! ### The exact witness never fails -/

/-- Every ready register reading the message point is written: the exact preparation is valid. -/
theorem exchangeValid_xPrep {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (c : ClockArena K)
    {r : Fin 3 → LF4.KTorus} (hr : ∀ i, r i ∈ readyArc 2) (b : Fin 2) :
    ExchangeValid J ħ T b (xPrep b c r) :=
  fun i => register_written hJ hħ hr b i le_rfl

/-- The invalid set misses every exact preparation: a Dirac preparation fails with probability `0`. -/
theorem dirac_invalid_eq_zero {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (c : ClockArena K)
    {r : Fin 3 → LF4.KTorus} (hr : ∀ i, r i ∈ readyArc 2) (b : Fin 2) :
    Measure.dirac (xPrep b c r) {x : XArena K | ¬ ExchangeValid J ħ T b x} = 0 := by
  rw [Measure.dirac_apply' _ (measurableSet_invalid J ħ T b)]
  exact Set.indicator_of_notMem (fun h => absurd (exchangeValid_xPrep hJ hħ c hr b) h) _

/-! ### The quantitative input: bands, and no tolerance -/

/-- **The band bound** (#103, transported to the register torus): the Haar measure of the registers
whose `rep` lies in `(a, b]` is at most `b − a`. -/
theorem volume_band_le (a b : ℝ) :
    (volume : Measure LF4.KTorus) {q | rep q.1 ∈ Ioc a b} ≤ ENNReal.ofReal (b - a) := by
  have h : {q : LF4.KTorus | rep q.1 ∈ Ioc a b}
      = (rep ⁻¹' Ioc a b) ×ˢ (univ : Set (AddCircle (1 : ℝ))) := by
    ext q
    simp
  rw [h, Measure.volume_eq_prod, Measure.prod_prod, circleFibre_volume_univ, mul_one]
  exact volume_rep_preimage_Ioc_le a b

/-- ★ **The write has no tolerance**: a register whose `rep` exceeds the ready width, shifted by the
message's amount without wrapping, misses the pointer arc. The arcs of `ShearWitness.lean` are
exactly as wide as the ready arc, so any preparation error past it is a record failure. -/
theorem pshift_shearAmt_notMem_pointerArc {K' : ℕ} (i : Fin K') {q : LF4.KTorus}
    (hq : shearWidth K' < rep q.1) (hq' : rep q.1 + shearAmt K' i ≤ 1) :
    pshift (shearAmt K' i) q ∉ pointerArc K' i := by
  intro h
  change rep (pshift (shearAmt K' i) q).1 ∈ Ioc (shearAmt K' i) (shearAmt K' i + shearWidth K') at h
  have hpos := shearAmt_pos (K := K') i
  rw [rep_pshift_of_mem _ _ ⟨by linarith [rep_pos q.1], hq'⟩] at h
  linarith [h.2]

/-! ### Retention -/

/-- ★★ **A record lifetime of at least the round trip is sufficient**: every record is alive at
every time from its readout to the return readout, where the radar coordinates are formed. -/
theorem retention_sufficient {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {c : ClockArena K}
    {r : Fin 3 → LF4.KTorus} (hr : ∀ i, r i ∈ readyArc 2) (b : Fin 2) {τR : ℝ}
    (hτR : roundTrip J ħ ≤ τR) (i : Fin 3) {t : OnticTime} (ht₁ : readTime J ħ i ≤ t)
    (ht₂ : t ≤ roundTrip J ħ) :
    (xEvolve J ħ T (-1) t (xPrep b c r)).2.2 i ∈ pointerArc 2 b :=
  record_persists hJ hħ hr b i (τR := τR) ht₁
    (by linarith [readTime_nonneg hJ hħ i])

/-- At the return readout all three records display the message: emission and return, the two
readings the radar coordinates are formed from, and reception. -/
theorem records_at_return {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {c : ClockArena K}
    {r : Fin 3 → LF4.KTorus} (hr : ∀ i, r i ∈ readyArc 2) (b : Fin 2) (i : Fin 3) :
    (xEvolve J ħ T (-1) (roundTrip J ħ) (xPrep b c r)).2.2 i ∈ pointerArc 2 b := by
  refine register_written hJ hħ hr b i ?_
  fin_cases i
  · exact (roundTrip_pos hJ hħ).le
  · show hopTime J ħ ≤ roundTrip J ħ
    unfold roundTrip
    linarith [hopTime_pos hJ hħ]
  · exact le_rfl

/-! ### The package -/

/-- ★★ **Failure and retention.** For any preparation measure the probability of an invalid exchange
is at most the sum over the three writes of (not ready) + (wrong message); the exact preparation is
valid; a record lifetime of at least the round trip keeps every record alive through the return
readout; and the write mechanism tolerates no preparation error past the ready arc. -/
theorem exchange_failure {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {c : ClockArena K}
    {r : Fin 3 → LF4.KTorus} (hr : ∀ i, r i ∈ readyArc 2) (b : Fin 2) :
    (∀ μ : Measure (XArena K), μ {x | ¬ ExchangeValid J ħ T b x}
        ≤ ∑ i : Fin 3, (μ (notReady i) + μ (messageFailure J ħ b i)))
      ∧ ExchangeValid J ħ T b (xPrep b c r)
      ∧ (∀ τR : ℝ, roundTrip J ħ ≤ τR → ∀ (i : Fin 3) (t : OnticTime), readTime J ħ i ≤ t →
          t ≤ roundTrip J ħ → (xEvolve J ħ T (-1) t (xPrep b c r)).2.2 i ∈ pointerArc 2 b)
      ∧ (∀ (i : Fin 2) (q : LF4.KTorus), shearWidth 2 < rep q.1 → rep q.1 + shearAmt 2 i ≤ 1 →
          pshift (shearAmt 2 i) q ∉ pointerArc 2 i) :=
  ⟨fun μ => measure_invalid_le' μ hJ hħ b, exchangeValid_xPrep hJ hħ c hr b,
    fun _ hτR i _ ht₁ ht₂ => retention_sufficient hJ hħ hr b hτR i ht₁ ht₂,
    fun i _ hq hq' => pshift_shearAmt_notMem_pointerArc i hq hq'⟩

end CSD.RecordLayer

end
