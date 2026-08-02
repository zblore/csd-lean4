/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.HongOuMandel
public import CsdLean4.SigmaLayer.Measurement

/-!
# Empirical/CSD: the Hong–Ou–Mandel dip as an ontic typicality measure

**Category:** CSD bridge (the ontic reading of `Empirical/QM/HongOuMandel.lean`).

The QM module proves the coincidence *probability* is zero. This module gives that zero its
ontic content: the coincidence outcome's **typicality measure on `Σ` is exactly `0`**, so the
set of microstates producing a coincidence is null. Hong–Ou–Mandel is not a cancellation of
frequencies over many runs — **no microstate whatsoever yields a coincidence**.

## Why this twin uses the record layer, not the Duistermaat–Heckman machinery

Every earlier `…Volume` twin (`BellVolume`, `MalusVolume`, `ElitzurVaidmanVolume`, …) reads Born
as a **Fubini–Study volume** of a moment-map region, via `fs_born_volume_ratio_N` /
`fsMeasure_bornRegionN`. That route is **unavailable here**, and for an instructive reason: those
theorems carry the hypothesis

  `hpos : ∀ j, 0 < ‖⟨e_j, ψ⟩‖²`

— *strictly positive* Born weights. It is not decorative. The region for index `i` is
`replaceMap b i '' openSimplexFree`, and `replaceMap_det b i = b i` (Cramer): a zero Born weight
makes the vertex-replacement map **singular**, `b` sits on the simplex *boundary* rather than its
interior (`b ∈ openSimplexFree` fails), and the image is no longer open, so the measurability and
volume-scaling steps of that proof both break.

So the projective/DH machinery covers exactly the non-degenerate states — and HOM's defining
feature is a **vanishing** amplitude. Extending those lemmas to the simplex boundary is a real
piece of work, recorded in `specs/BACKLOG.md`.

⚠️ *Correction 2026-08-02 (external review):* the boundary extension had in fact **already
landed 2026-06-11** — `fs_born_volume_ratio_N_uncond` / `born_frequency_convergence_N_uncond`
(`LF4/BornRegionUncond.lean`) are hpos-free for every unit state, vanishing weights included,
and the empirical volume engine routes through them. The paragraph above was written without
noticing this, and its impossibility reading is **withdrawn**: the DH route *can* state HOM's
zero. The record-layer route below stands as this module's **chosen** architecture — for the
foundational reasons given — not as a necessity.

The **record layer** (`SigmaLayer/{BornFibrePartition,DeIsolationFlow,FibreRecord,Measurement}`)
has no such restriction: `volume_cdfCell` carries *no* positivity hypothesis, because a zero rate
simply gives a zero-width CDF cell — a degenerate cell is still a cell. So the record layer
expresses the degenerate case the DH route cannot, which is a concrete architectural argument for
it beyond the foundational one.

## What this file proves

* `homOut_eq_bsTwo_bosonIn` — the occupation-basis state is *derived* from the QM module's output
  amplitude matrix `bsTwo bosonIn`, not asserted: `|20⟩` and `|02⟩` from the diagonal entries,
  and the symmetrised `|11⟩` amplitude `(S₀₁ + S₁₀)/√2` from the off-diagonal ones.
* `homOut_norm` — it is a unit state, so the record layer applies.
* ★ `hom_coincidence_typicality_zero` — the coincidence cell has fibre typicality **exactly `0`**.
* ★ `hom_coincidence_record_null` — the same at the level of the **record**: the P5 record event
  "this context recorded a coincidence" is a null set of `Σ`.
* ★ `hom_coincidence_measurement_zero` — and as a `Measurement`: the coincidence outcome has
  probability `0` for a.e. microstate.
* `hom_bunch_typicality_half` — the two bunched outcomes carry typicality `½` each, so the
  vanishing is a genuine redistribution, not a normalisation artefact.

## References

`Empirical/QM/HongOuMandel.lean` (`bsTwo_bosonIn`, `hom_coincidence_zero`);
`SigmaLayer/BornFibrePartition.lean` (`cdfCell`, `volume_cdfCell`, `bornRate`);
`SigmaLayer/DeIsolationFlow.lean` (`fibreTypicality`, `fibreTypicality_bornCell`);
`SigmaLayer/FibreRecord.lean` (`fibreTypicality_bornRecord` — the P5 record event);
`SigmaLayer/Measurement.lean` (`bornMeasurement_prob`);
`LF4/ObservableCorrespondenceN.lean` (`fsMeasure_bornRegionN` — the DH route, and its `hpos`);
`LF4/BornVolume.lean` (`replaceMap_det` — why `hpos` is load-bearing);
`specs/record-layer-plan.md`; `specs/BACKLOG.md`; `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Set
open CSD.RecordLayer

namespace CSD.Empirical.CSDBridge.HongOuMandelVolume

open CSD.Empirical.HOM

/-! ### The HOM output in the occupation basis -/

/-- The Hong–Ou–Mandel output state in the **occupation basis** `{|2,0⟩, |1,1⟩, |0,2⟩}`:
amplitude `1/√2` for both photons in mode `0`, **zero** for one in each, `−1/√2` for both in
mode `1`. Index `1` is the coincidence outcome. -/
noncomputable def homOut : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 ![rt2inv, 0, -rt2inv]

@[simp] lemma homOut_zero : homOut 0 = rt2inv := by simp [homOut, WithLp.ofLp_toLp]

@[simp] lemma homOut_one : homOut 1 = 0 := by simp [homOut, WithLp.ofLp_toLp]

@[simp] lemma homOut_two : homOut 2 = -rt2inv := by simp [homOut, WithLp.ofLp_toLp]

/-- **The occupation amplitudes are the QM module's output**, not a re-assertion: `|2,0⟩` and
`|0,2⟩` are the diagonal entries of `bsTwo bosonIn`, and the `|1,1⟩` amplitude is the symmetrised
off-diagonal combination `(S₀₁ + S₁₀)/√2` — which is where the cancellation lives. -/
theorem homOut_eq_bsTwo_bosonIn :
    homOut 0 = bsTwo bosonIn 0 0 ∧
    homOut 1 = (bsTwo bosonIn 0 1 + bsTwo bosonIn 1 0) * rt2inv ∧
    homOut 2 = bsTwo bosonIn 1 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [bsTwo_bosonIn] <;> simp

lemma homOut_normsq : ∑ i, ‖homOut i‖ ^ 2 = 1 := by
  rw [Fin.sum_univ_three, homOut_zero, homOut_one, homOut_two, norm_neg, norm_rt2inv_sq]
  norm_num

theorem homOut_norm : ‖homOut‖ = 1 := by
  rw [EuclideanSpace.norm_eq, homOut_normsq, Real.sqrt_one]

/-! ### The dip as a null set of microstates -/

/-- **★ The Hong–Ou–Mandel dip is an ontic impossibility.** The coincidence outcome's Born cell
has fibre typicality **exactly zero** — the set of microstates that would produce a coincidence
is null. The dip is not a statistical cancellation across runs; there is nothing in `Σ` to
cancel. -/
theorem hom_coincidence_typicality_zero :
    fibreTypicality (cdfCell (bornRate homOut) 1) = 0 := by
  rw [fibreTypicality_bornCell homOut homOut_norm 1, homOut_one]
  simp

/-- **★ The same statement at the level of the record.** The postulate-P5 record event "this
context recorded outcome `1` (a coincidence)" is a null subset of `Σ`: no record of a
coincidence is ever laid down. -/
theorem hom_coincidence_record_null (t : CSD.SigmaLayer.OnticTime) :
    fibreTypicality
        ((fibreRecordSemantics 3).event ⟨bornContext homOut, (1 : Fin 3), t⟩) = 0 := by
  rw [fibreTypicality_bornRecord homOut homOut_norm 1 t, homOut_one]
  simp

/-- **★ And as a measurement.** The coincidence outcome of the HOM measurement has probability
`0`: for a.e. microstate the deterministic context-plus-microstate map lands in another basin. -/
theorem hom_coincidence_measurement_zero (t : CSD.SigmaLayer.OnticTime) :
    (Measurement.bornMeasurement homOut t).prob 1 = 0 := by
  rw [Measurement.bornMeasurement_prob homOut homOut_norm 1 t, homOut_one]
  simp

/-- The two **bunched** outcomes carry typicality `½` each — so the coincidence weight has been
redistributed to them, and the vanishing above is genuine rather than a normalisation artefact. -/
theorem hom_bunch_typicality_half :
    fibreTypicality (cdfCell (bornRate homOut) 0) = ENNReal.ofReal (1 / 2) ∧
    fibreTypicality (cdfCell (bornRate homOut) 2) = ENNReal.ofReal (1 / 2) := by
  refine ⟨?_, ?_⟩
  · rw [fibreTypicality_bornCell homOut homOut_norm 0, homOut_zero, norm_rt2inv_sq]
  · rw [fibreTypicality_bornCell homOut homOut_norm 2, homOut_two, norm_neg, norm_rt2inv_sq]

end CSD.Empirical.CSDBridge.HongOuMandelVolume
