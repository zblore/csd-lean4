/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.CircleFibre
public import CsdLean4.RecordLayer.Measurement

/-!
# SigmaLayer/CircleRecord: the record layer, re-plumbed onto the compact fibre

**Category:** 7-SigmaLayer (the record layer — A1 compactness).

`CircleFibre.lean` moved the Born *partition* onto a compact fibre. This moves the rest of the
record layer with it: the postulate-P5 record semantics, the isolation-is-conditioning reading,
measurement-as-`context + unknown microstate → record`, the Born probabilities, and the
almost-everywhere totality of the readout — all on `CircleFibre = AddCircle 1` instead of `ℝ`.

The point is that **nothing physical changes**. The record signature is reused *verbatim*
(`fibreSignature`: contexts are non-negative rate vectors, outcomes are `Fin n`) — it never
mentioned the fibre — so only the *semantics*, the assignment of ontic events, is different. Every
Born weight comes out identical (`volume_circleCell`), which is the content of the swap.

## What this gives

* `circleRecordSemantics` — a postulate-P5 `RecordSemantics` on the **compact** `CircleFibre`:
  events are the circle Born arcs, measurable and mutually exclusive within a context.
* `compatibleSet_circle_single` — isolation is conditioning: the states compatible with one record
  are exactly that record's arc (the P6 reading).
* `circleOutcome_eq_record` — the ontic selection *is* the record: reading which arc the microstate
  occupies agrees with testing membership of the record event.
* `CircleMeasurement` / `prob` / `circleBornMeasurement` — measurement as context-plus-microstate,
  with `circleBornMeasurement_prob : prob i = ‖ψ i‖²`.
* `circleBornMeasurement_ae_total` — the arcs cover the circle up to a null set, so a.e. microstate
  yields a record. On `ℝ` this was stated on `[0,1)`; on the circle it is about the whole space.
  ⚠️ The `ℝ` restriction was **not forced** — see `fibreTypicality_uncovered_univ`. What compactness
  buys is stated precisely at `circleBornMeasurement_ae_total`.

## What is still not claimed

Compactness and a genuine Haar probability measure, yes. **A1 in full, no** — and ⚠️ **not for the
reason an earlier version of this docstring gave.** It said `dω = 0` was blocked on Mathlib's absent
manifold exterior calculus. The real obstruction is **dimension parity**: `ℂℙⁿ⁻¹ × AddCircle 1` has
real dimension `2n-1`, which is odd, and no odd-dimensional manifold admits a symplectic — hence a
Kähler — structure. More tooling would not fix it. The successor construction moves to
`KSigma = ℂℙⁿ⁻¹ × T²` (real dimension `2n`, even), putting the Born arcs on one torus coordinate;
see `CircleFibre.lean`'s scope note and the ★★ `BACKLOG.md` row. The fibre measure is also exhibited
as Haar, not shown to be a Liouville measure.

⚠️ **AND THIS IS A PARALLEL CONSTRUCTION, NOT A MIGRATION (corrected 2026-07-30).** The commit that
landed this file was headlined "the record layer now runs on the compact fibre", and the ★★ BACKLOG
row recorded the re-plumbing as DONE. **Both overstated it.** What exists is a *compact counterpart*
of the record semantics, proved in full. The corpus's actual capstones — `Measurement.lean`,
`RecordLayerClosure.lean`, `FiniteQMClosure.lean`, `KSigmaRecord.lean` — still run on the `ℝ` fibre
with `fibreTypicality`, and nothing outside `AxiomAudit.lean` imports this module. Retiring the `ℝ`
closure is future work.

And this is the *fibre* half: the general-`N` A7 question of whether context-fixed regions exist at
all is ⏸ parked, not settled (`specs/sigma-fibre-contextuality.md`).

## References

`SigmaLayer/CircleFibre.lean` (the compact fibre and its Born arcs);
`SigmaLayer/FibreRecord.lean`, `SigmaLayer/Measurement.lean` (the `ℝ` originals this mirrors);
`SigmaLayer/RecordedFact.lean` (`RecordSemantics`, and the warning that it is trivially inhabited —
the content is in the non-vacuity results, of which `circleBornMeasurement_ae_total` is one);
`specs/BACKLOG.md` (the ★★ fibre/A1 row).
-/

@[expose] public section

open MeasureTheory Set
open CSD.SigmaLayer

namespace CSD.RecordLayer

variable {n : ℕ}

/-! ### The P5 record semantics on the compact fibre -/

/-- **The circle record semantics (P5) on the compact `Σ`-fibre.** The ontic event of "context `c`
recorded outcome `i`" is the Born arc `circleCell c.rate i` — measurable, and within one context at
one time distinct outcomes are mutually exclusive.

The *signature* is `fibreSignature`, reused unchanged: it only ever mentioned rate vectors and
outcome indices, never the fibre. Swapping `ℝ` for the circle touches the semantics alone. -/
noncomputable def circleRecordSemantics (n : ℕ) :
    RecordSemantics CircleFibre (fibreSignature n) where
  event := fun r => circleCell r.context.rate r.outcome
  measurable_event := fun r => measurableSet_circleCell r.context.rate r.outcome
  exclusive := fun c a b t x hxa hxb => by
    by_contra hab
    exact Set.disjoint_left.mp (circleCell_pairwiseDisjoint c.rate c.rate_nonneg hab) hxa hxb

@[simp] theorem circleRecordSemantics_event (c : FibreContext n) (i : Fin n) (t : OnticTime) :
    (circleRecordSemantics n).event ⟨c, i, t⟩ = circleCell c.rate i := rfl

/-- **Isolation is conditioning (P6).** The ontic states compatible with the single record
"context `c` recorded `i` at `t`" are exactly that record's arc. -/
theorem compatibleSet_circle_single (c : FibreContext n) (i : Fin n) (t : OnticTime) :
    compatibleSet (circleRecordSemantics n) [⟨c, i, t⟩] = circleCell c.rate i := by
  simp [compatibleSet]

/-! ### The ontic selection is the record -/

/-- The outcome the unknown microstate selects on the circle: the arc it occupies. -/
noncomputable def circleOutcome (r : Fin n → ℝ) (x : CircleFibre) : Option (Fin n) :=
  open Classical in
  if h : ∃ i, x ∈ circleCell r i then some h.choose else none

/-- **Reading the outcome and testing the record event agree.** For non-negative rates the arcs are
disjoint, so "the microstate occupies arc `i`" and "the record says `i`" are the same statement. -/
theorem circleOutcome_eq_some_iff (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (x : CircleFibre)
    (i : Fin n) : circleOutcome r x = some i ↔ x ∈ circleCell r i := by
  classical
  constructor
  · intro h
    by_cases hex : ∃ j, x ∈ circleCell r j
    · rw [circleOutcome, dif_pos hex] at h
      have : hex.choose = i := by simpa using h
      exact this ▸ hex.choose_spec
    · rw [circleOutcome, dif_neg hex] at h; exact absurd h (by simp)
  · intro hx
    have hex : ∃ j, x ∈ circleCell r j := ⟨i, hx⟩
    rw [circleOutcome, dif_pos hex]
    -- Disjointness forces the chosen index to be `i`.
    by_cases hij : hex.choose = i
    · rw [hij]
    · exact absurd hx (Set.disjoint_left.mp (circleCell_pairwiseDisjoint r hr hij) hex.choose_spec)

/-- **The ontic selection is the record**, at the record-layer level. -/
theorem circleOutcome_eq_record (c : FibreContext n) (i : Fin n) (t : OnticTime)
    (x : CircleFibre) :
    circleOutcome c.rate x = some i ↔ x ∈ (circleRecordSemantics n).event ⟨c, i, t⟩ := by
  rw [circleRecordSemantics_event]
  exact circleOutcome_eq_some_iff c.rate c.rate_nonneg x i

/-! ### Measurement on the compact fibre -/

/-- A **measurement** on the compact fibre: a context awaiting an unknown microstate. -/
structure CircleMeasurement (n : ℕ) where
  /-- The measurement context — fixes the arcs, hence the probabilities. -/
  context : FibreContext n
  /-- The ontic time at which the record is established. -/
  time : OnticTime

namespace CircleMeasurement

variable (m : CircleMeasurement n)

/-- The **basin** of outcome `i`: the arc the context assigns to it. -/
def basin (i : Fin n) : Set CircleFibre :=
  (circleRecordSemantics n).event ⟨m.context, i, m.time⟩

/-- The **probability** of outcome `i`: the Haar measure of its basin. -/
noncomputable def prob (i : Fin n) : ENNReal := volume (m.basin i)

theorem basin_eq (i : Fin n) : m.basin i = circleCell m.context.rate i := rfl

end CircleMeasurement

/-- The **Born measurement** on the compact fibre for a prepared state `ψ`. -/
noncomputable def circleBornMeasurement (ψ : EuclideanSpace ℂ (Fin n)) (t : OnticTime) :
    CircleMeasurement n :=
  ⟨bornContext ψ, t⟩

/-- **★ The Born rule on the compact fibre.** The outcome-`i` probability of the Born measurement is
`‖ψ i‖²` — the same weight the `ℝ` fibre gave. Compactifying changed nothing. -/
theorem circleBornMeasurement_prob (ψ : EuclideanSpace ℂ (Fin n)) (hψ : ‖ψ‖ = 1) (i : Fin n)
    (t : OnticTime) :
    (circleBornMeasurement ψ t).prob i = ENNReal.ofReal (‖ψ i‖ ^ 2) := by
  have hrate : (circleBornMeasurement ψ t).context.rate = bornRate ψ := rfl
  rw [CircleMeasurement.prob, CircleMeasurement.basin_eq, hrate]
  exact volume_circleBornCell ψ hψ i

/-- **A.e. every microstate yields a record.** The arcs cover the circle up to a null set, so there
is no positive-measure "no outcome" set.

**On the comparison with `ℝ` — CORRECTED 2026-08-11.** This module previously said the `ℝ`
statement "had to be restricted to `[0,1)` by hand, because Lebesgue measure on the line is
infinite". **Both halves were wrong.** `fibreTypicality` is not Lebesgue measure on the line but
`volume.restrict (Ico 0 1)`, a *probability* measure; and the restriction was not forced —
`fibreTypicality_uncovered_univ` proves the identical `univ`-form statement on `ℝ`.

The real difference is not which sets the statement ranges over but **where the mass one comes
from**. On `ℝ` it is imposed by fiat: `fibreTypicality_Ici_one` shows the fibre's complement, of
infinite Lebesgue measure, is assigned typicality zero, so an uncovered point off `[0,1)` is
*excused by the measure* rather than covered by a cell. Here mass one is Haar mass on a compact
group (`circleFibre_volume_univ`), every nonempty open set has positive measure, and there is
nowhere for an uncovered point to hide. That is the improvement — genuine, but a different one. -/
theorem circleBornMeasurement_ae_total (ψ : EuclideanSpace ℂ (Fin n)) (hψ : ‖ψ‖ = 1)
    (t : OnticTime) :
    volume (univ \ ⋃ i, (circleBornMeasurement ψ t).basin i) = 0 := by
  classical
  have hrate : (circleBornMeasurement ψ t).context.rate = bornRate ψ := rfl
  have hdisj : Pairwise (Function.onFun Disjoint fun i => (circleBornMeasurement ψ t).basin i) := by
    intro i j hij
    simp only [CircleMeasurement.basin_eq, hrate]
    exact circleCell_pairwiseDisjoint (bornRate ψ) (bornRate_nonneg ψ) hij
  have hmeas : ∀ i, MeasurableSet ((circleBornMeasurement ψ t).basin i) := by
    intro i
    rw [CircleMeasurement.basin_eq]
    exact measurableSet_circleCell _ i
  have hb : ∀ i, volume ((circleBornMeasurement ψ t).basin i) = ENNReal.ofReal (‖ψ i‖ ^ 2) :=
    fun i => circleBornMeasurement_prob ψ hψ i t
  have hsum : ∑ i, ‖ψ i‖ ^ 2 = 1 := by
    have := sum_bornRate_unit ψ hψ
    simpa [bornRate] using this
  have hcover : volume (⋃ i, (circleBornMeasurement ψ t).basin i) = 1 := by
    rw [measure_iUnion hdisj hmeas, tsum_fintype,
      Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hb i,
      ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity), hsum, ENNReal.ofReal_one]
  rw [measure_sdiff (subset_univ _) (MeasurableSet.iUnion hmeas).nullMeasurableSet
      (by rw [hcover]; exact ENNReal.one_ne_top),
    circleFibre_volume_univ, hcover, tsub_self]

end CSD.RecordLayer
