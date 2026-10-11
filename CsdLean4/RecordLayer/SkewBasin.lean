/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.SkewFibrePartition
public import CsdLean4.RecordLayer.GlobalBasin

/-!
# The skew basin: option I3 coupled to the base

**Category:** 7-SigmaLayer (the record layer — Paper C A7).
BACKLOG #135, out of ~~#134~~; `specs/POSITS.md` **Posit 10**.

[`SkewFibrePartition.lean`](SkewFibrePartition.lean) is **kinematic**: its joint rate table is an
argument, so nothing there is attached to a base point, and the construction the author chose on
~~#134~~ was therefore recorded rather than implemented. This file closes that gap. It is to
`SkewFibrePartition` exactly what [`GlobalBasin.lean`](GlobalBasin.lean) is to
[`TorusFibre.lean`](TorusFibre.lean): the rates become a **field over the base**, the cells become
**basins in `Σ`**, and the Born weight is read in `epistemicMeasure` rather than in the fibre's Haar
measure.

## What is proved

* `JointContextField N m n` — a **joint** context field: the joint outcome probabilities as a
  measurable function of the ontic base point, with every A-marginal positive so the conditional law
  exists. `JointContextField.rates` evaluates it to a `JointRates` at a base point, which is what
  every statement below goes through;
* `skewBasin c s t` — **the basin of the joint outcome `(s, t)`**: the microstates whose *fibre
  point* lies in the skew cell of the rate table **at their own base point**. Both torus coordinates
  are read, which is the whole content of I3;
* `measurableSet_skewBasin` — and the work in it is `measurable_condRate`, the measurability of the
  **quotient** `rate / rowSum`, which is the one new regularity obligation I3 incurs over I1;
* ★★★ `skewBasin_prob` — **the Born weight**, `epistemicMeasure p (skewBasin c s t) = c.rate p s t`.
  This is the statement `LF6`'s Born clause is written in, so I3 now reaches the level I1 was
  already at;
* ★★★ `wingABasin_prob` and ★★★ `wingBBasin_prob` — the two wing marginals on `Σ`, `rowSum` and
  `colSum`. As on the fibre, B's is the non-trivial one: the construction never mentions `colSum`;
* ★★★ `wingBBasin_prob_eq_of_colSum_eq` — **operational no-signalling with its premise named**, in
  the I3 setting: B's basin weight is unchanged between two joint context fields that agree on B's
  marginal at that base point. The premise is a property of the rate fields and is therefore
  checkable, exactly as in `TwoWingCoarsening`;
* `skewBasin_pairwiseDisjoint`, `skewBasin_ae_total` — it is a partition of `Σ` up to a null set;
* `constJointContext` — **non-vacuity**: for *every* joint rate table, including every correlated
  one, there is a joint context field realising it. So nothing above is empty.

## Honest scope

⚠️ **This does not give a wing-local record, and must not be read as doing so.** Under I3 the
`θ₂` arc is conditioned on A's cell *by construction*, so "B's record reads only B" is **false**
here and is not claimed. What `CV/TwoWingCone.lean` proves about wing-local *field observables* is
still a different statement about a different object; #131's obligation (3) asked for the bridge and
this is not it. The honest record-side counterpart of unsteerability remains the *marginal*
statement — `wingBBasin_prob_eq_of_colSum_eq` here, and
`LF6.toReal_measure_preimage_wingAEvent_eq_of_setting` for I1.

⚠️ **The corpus still runs on I1.** `globalBasin`, `outcomeCode`, `recordString`, `LF6`'s capstone
and everything #131 has landed read `θ₁` alone. This file supplies the I3 alternative *at the same
level*; it does not retire the I1 construction, and no theorem here replaces one there. Posit 10
records the decision; this file makes it available.

✅ **No positivity restriction** (BACKLOG #136, 2026-10-11). An earlier version of `JointRates`
demanded a strictly positive A-marginal, which a joint context field would have had to satisfy at
**every** base point — and a `momentMap`-derived block marginal vanishes on rays whose block has
zero amplitude, so `momentContext` could have had no I3 analogue. The hypothesis turned out to be
removable, so that obstacle is gone. ⚠️ What remains of #136 is the **field itself**: this
file still exhibits only `constJointContext`, whose table does not move with the ontic point, and
building the `momentMap`-derived one is the open half.

⚠️ **No `P_st`, no Bell, no dynamics.** The rate field is an argument; the singlet is not mentioned;
nothing here concerns a flow, so this says nothing about record writes or stability.

References: [`SkewFibrePartition.lean`](SkewFibrePartition.lean) (`JointRates`, `skewCell`,
`volume_skewCell`, `wingAFibre`, `volume_wingBFibre`),
[`GlobalBasin.lean`](GlobalBasin.lean) (`ContextField`, `globalBasin`, `globalBasin_prob`,
`epistemicMeasure` — the I1 construction this parallels),
[`CircleFibre.lean`](CircleFibre.lean) (`rep`, `circleCell`),
[`TwoWingCoarsening.lean`](TwoWingCoarsening.lean) (option I1's wings);
`specs/POSITS.md` Posit 10; `specs/BACKLOG.md` #135, ~~#134~~, ~~#132~~, #131.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace CSD.RecordLayer

variable {N m n : ℕ}

/-! ### A joint context field -/

/-- **A joint measurement context, as a field over the base**: the joint outcome probabilities at
each ontic base point. No positivity of the A-marginals is required (BACKLOG #136), so a
`momentMap`-derived field is not excluded by a ray whose block has zero amplitude. -/
structure JointContextField (N m n : ℕ) where
  /-- The joint probability of the outcome pair at a base point. -/
  rate : LF4.CPN N → Fin m → Fin n → ℝ
  /-- Each joint coordinate is measurable — the regularity that makes the basins measurable. -/
  measurable_rate : ∀ s t, Measurable fun p => rate p s t
  /-- Joint probabilities are non-negative. -/
  nonneg : ∀ p s t, 0 ≤ rate p s t
  /-- The table is normalised at every base point. -/
  sum_one : ∀ p, ∑ s, ∑ t, rate p s t = 1

namespace JointContextField

variable (c : JointContextField N m n)

/-- **The joint rate table at a base point.** Every statement about the skew basin goes through
this, so the fibre theorems of `SkewFibrePartition.lean` apply unchanged. -/
def rates (p : LF4.CPN N) : JointRates m n where
  rate := c.rate p
  nonneg := c.nonneg p
  sum_one := c.sum_one p

@[simp] theorem rates_rate (p : LF4.CPN N) : (c.rates p).rate = c.rate p := rfl

/-! ### Regularity: the quotient is the new obligation -/

theorem measurable_rowSum (s : Fin m) : Measurable fun p => (c.rates p).rowSum s :=
  Finset.measurable_sum Finset.univ fun t _ => c.measurable_rate s t

/-- **The one new regularity obligation I3 incurs over I1**: the conditional rate is a *quotient*,
measurable because the denominator is measurable and nowhere zero. -/
theorem measurable_condRate (s : Fin m) (t : Fin n) :
    Measurable fun p => (c.rates p).condRate s t :=
  (c.measurable_rate s t).div (c.measurable_rowSum s)

theorem measurable_loSum_rowSum (s : Fin m) :
    Measurable fun p => loSum (c.rates p).rowSum s := by
  classical
  simpa [loSum] using
    Finset.measurable_sum (Finset.univ.filter fun k : Fin m => (k : ℕ) < (s : ℕ))
      fun k _ => c.measurable_rowSum k

theorem measurable_loSum_condRate (s : Fin m) (t : Fin n) :
    Measurable fun p => loSum ((c.rates p).condRate s) t := by
  classical
  simpa [loSum] using
    Finset.measurable_sum (Finset.univ.filter fun k : Fin n => (k : ℕ) < (t : ℕ))
      fun k _ => c.measurable_condRate s k

end JointContextField

/-! ### The basin -/

/-- **The skew basin of the joint outcome `(s, t)`.** A point of `Σ = ℂℙⁿ⁻¹ × T²` is in it when its
**fibre point** — both coordinates — lies in the skew cell of the rate table at its **own base
point**. The I3 counterpart of `globalBasin`, which reads the first torus coordinate only. -/
def skewBasin (c : JointContextField N m n) (s : Fin m) (t : Fin n) : Set (LF4.KSigma N) :=
  {x | x.2 ∈ skewCell (c.rates x.1) s t}

@[simp] theorem mem_skewBasin_iff (c : JointContextField N m n) (s : Fin m) (t : Fin n)
    (x : LF4.KSigma N) : x ∈ skewBasin c s t ↔ x.2 ∈ skewCell (c.rates x.1) s t := Iff.rfl

theorem measurableSet_skewBasin (c : JointContextField N m n) (s : Fin m) (t : Fin n) :
    MeasurableSet (skewBasin c s t) := by
  have hrep1 : Measurable fun x : LF4.KSigma N => rep x.2.1 :=
    measurable_rep.comp (measurable_fst.comp measurable_snd)
  have hrep2 : Measurable fun x : LF4.KSigma N => rep x.2.2 :=
    measurable_rep.comp (measurable_snd.comp measurable_snd)
  have hbase : Measurable fun x : LF4.KSigma N => x.1 := measurable_fst
  have hlo1 : Measurable fun x : LF4.KSigma N => loSum (c.rates x.1).rowSum s :=
    (c.measurable_loSum_rowSum s).comp hbase
  have hhi1 : Measurable fun x : LF4.KSigma N =>
      loSum (c.rates x.1).rowSum s + (c.rates x.1).rowSum s :=
    hlo1.add ((c.measurable_rowSum s).comp hbase)
  have hlo2 : Measurable fun x : LF4.KSigma N => loSum ((c.rates x.1).condRate s) t :=
    (c.measurable_loSum_condRate s t).comp hbase
  have hhi2 : Measurable fun x : LF4.KSigma N =>
      loSum ((c.rates x.1).condRate s) t + (c.rates x.1).condRate s t :=
    hlo2.add ((c.measurable_condRate s t).comp hbase)
  exact ((measurableSet_lt hlo1 hrep1).inter (measurableSet_le hrep1 hhi1)).inter
    ((measurableSet_lt hlo2 hrep2).inter (measurableSet_le hrep2 hhi2))

/-- **The slice of a skew basin over its own base point is a skew cell** — the bridge to every
fibre theorem of `SkewFibrePartition.lean`. -/
theorem preimage_skewBasin (c : JointContextField N m n) (s : Fin m) (t : Fin n)
    (p : LF4.CPN N) : Prod.mk p ⁻¹' skewBasin c s t = skewCell (c.rates p) s t := rfl

/-- ★★★ **The Born weight of the skew basin.** Conditioning the epistemic state on the preparation
returns the joint rate — which is the statement `LF6`'s Born clause is written in, so option I3 now
reaches the level option I1 was already at. -/
theorem skewBasin_prob (c : JointContextField N m n) (s : Fin m) (t : Fin n) (p : LF4.CPN N) :
    epistemicMeasure p (skewBasin c s t) = ENNReal.ofReal (c.rate p s t) := by
  rw [epistemicMeasure, Measure.prod_apply (measurableSet_skewBasin c s t),
    lintegral_dirac' _ (measurable_measure_prodMk_left (measurableSet_skewBasin c s t)),
    preimage_skewBasin]
  exact volume_skewCell (c.rates p) s t

/-- **Distinct outcome pairs are mutually exclusive on `Σ`.** Fibrewise from
`skewCell_pairwiseDisjoint`, since both conditions are evaluated at the same base point. -/
theorem skewBasin_pairwiseDisjoint (c : JointContextField N m n) :
    Pairwise (Function.onFun Disjoint fun st : Fin m × Fin n => skewBasin c st.1 st.2) := by
  intro st st' hne
  refine Set.disjoint_left.mpr fun x hx hx' => ?_
  exact Set.disjoint_left.mp (skewCell_pairwiseDisjoint (c.rates x.1) hne) hx hx'

/-- **A.e. microstate lands in some joint basin**, so the two-wing readout is a.e. total. -/
theorem skewBasin_ae_total (c : JointContextField N m n) (p : LF4.CPN N) :
    epistemicMeasure p (univ \ ⋃ st : Fin m × Fin n, skewBasin c st.1 st.2) = 0 := by
  classical
  have hmeas : ∀ st : Fin m × Fin n, MeasurableSet (skewBasin c st.1 st.2) :=
    fun st => measurableSet_skewBasin c st.1 st.2
  have hcover : epistemicMeasure p (⋃ st : Fin m × Fin n, skewBasin c st.1 st.2) = 1 := by
    rw [measure_iUnion (skewBasin_pairwiseDisjoint c) hmeas, tsum_fintype,
      Finset.sum_congr rfl fun st (_ : st ∈ Finset.univ) => skewBasin_prob c st.1 st.2 p,
      ← ENNReal.ofReal_sum_of_nonneg fun st _ => c.nonneg p st.1 st.2]
    rw [show ∑ st : Fin m × Fin n, c.rate p st.1 st.2 = ∑ s, ∑ t, c.rate p s t from
      Fintype.sum_prod_type' _, c.sum_one p, ENNReal.ofReal_one]
  rw [measure_sdiff (subset_univ _) (MeasurableSet.iUnion hmeas).nullMeasurableSet
      (by rw [hcover]; exact ENNReal.one_ne_top),
    measure_univ, hcover, tsub_self]

/-! ### The two wing basins -/

/-- **A's record basin on `Σ`**: A recorded `s`, whatever B recorded. -/
def wingABasin (c : JointContextField N m n) (s : Fin m) : Set (LF4.KSigma N) :=
  ⋃ t, skewBasin c s t

/-- **B's record basin on `Σ`**: B recorded `t`, whatever A recorded. -/
def wingBBasin (c : JointContextField N m n) (t : Fin n) : Set (LF4.KSigma N) :=
  ⋃ s, skewBasin c s t

theorem measurableSet_wingABasin (c : JointContextField N m n) (s : Fin m) :
    MeasurableSet (wingABasin c s) :=
  MeasurableSet.iUnion fun t => measurableSet_skewBasin c s t

theorem measurableSet_wingBBasin (c : JointContextField N m n) (t : Fin n) :
    MeasurableSet (wingBBasin c t) :=
  MeasurableSet.iUnion fun s => measurableSet_skewBasin c s t

theorem preimage_wingABasin (c : JointContextField N m n) (s : Fin m) (p : LF4.CPN N) :
    Prod.mk p ⁻¹' wingABasin c s = wingAFibre (c.rates p) s := by
  rw [wingABasin, Set.preimage_iUnion, wingAFibre]
  exact Set.iUnion_congr fun t => preimage_skewBasin c s t p

theorem preimage_wingBBasin (c : JointContextField N m n) (t : Fin n) (p : LF4.CPN N) :
    Prod.mk p ⁻¹' wingBBasin c t = wingBFibre (c.rates p) t := by
  rw [wingBBasin, Set.preimage_iUnion, wingBFibre]
  exact Set.iUnion_congr fun s => preimage_skewBasin c s t p

/-- ★★★ **A's marginal on `Σ`.** -/
theorem wingABasin_prob (c : JointContextField N m n) (s : Fin m) (p : LF4.CPN N) :
    epistemicMeasure p (wingABasin c s) = ENNReal.ofReal ((c.rates p).rowSum s) := by
  rw [epistemicMeasure, Measure.prod_apply (measurableSet_wingABasin c s),
    lintegral_dirac' _ (measurable_measure_prodMk_left (measurableSet_wingABasin c s)),
    preimage_wingABasin]
  exact volume_wingAFibre (c.rates p) s

/-- ★★★ **B's marginal on `Σ` — and this is the non-trivial one.** The construction never mentions
`colSum`: B's cells are built from the *conditional* rates, and summing them over A's basins returns
B's marginal because `rowSum · condRate = rate`. Nothing was arranged to make it come out. -/
theorem wingBBasin_prob (c : JointContextField N m n) (t : Fin n) (p : LF4.CPN N) :
    epistemicMeasure p (wingBBasin c t) = ENNReal.ofReal ((c.rates p).colSum t) := by
  rw [epistemicMeasure, Measure.prod_apply (measurableSet_wingBBasin c t),
    lintegral_dirac' _ (measurable_measure_prodMk_left (measurableSet_wingBBasin c t)),
    preimage_wingBBasin]
  exact volume_wingBFibre (c.rates p) t

/-- ★★★ **Operational no-signalling, with its premise named, in the I3 setting.** B's basin weight
agrees between two joint context fields exactly when their B-marginals agree at that base point.
The construction supplies the identity; whether the premise holds is a checkable property of the
rate fields — for the singlet, of `P_st` — and not something smuggled. -/
theorem wingBBasin_prob_eq_of_colSum_eq {c c' : JointContextField N m n} {t : Fin n}
    {p : LF4.CPN N} (h : (c.rates p).colSum t = (c'.rates p).colSum t) :
    epistemicMeasure p (wingBBasin c t) = epistemicMeasure p (wingBBasin c' t) := by
  rw [wingBBasin_prob, wingBBasin_prob, h]

/-- ★★★ **The A-side twin.** -/
theorem wingABasin_prob_eq_of_rowSum_eq {c c' : JointContextField N m n} {s : Fin m}
    {p : LF4.CPN N} (h : (c.rates p).rowSum s = (c'.rates p).rowSum s) :
    epistemicMeasure p (wingABasin c s) = epistemicMeasure p (wingABasin c' s) := by
  rw [wingABasin_prob, wingABasin_prob, h]

/-! ### Non-vacuity -/

/-- **Every joint rate table is realised by a joint context field** — the base-independent one. So
nothing above is vacuous, and in particular a *correlated* table is realisable, which is what
`SkewFibrePartition.not_exists_sndSet_of_condRate_ne` then applies to.

⚠️ Base-independent rates are the degenerate case of a context field: the record is still
contextual in the sense that matters (the cells are those of the chosen table), but the table does
not move with the ontic point. A field whose table varies — the analogue of `momentContext` — is
the open half of BACKLOG #136; nothing in the structure stands in its way any more. -/
def constJointContext (q : JointRates m n) : JointContextField N m n where
  rate := fun _ => q.rate
  measurable_rate := fun _ _ => measurable_const
  nonneg := fun _ => q.nonneg
  sum_one := fun _ => q.sum_one

@[simp] theorem constJointContext_rate (q : JointRates m n) (p : LF4.CPN N) :
    (constJointContext (N := N) q).rate p = q.rate := rfl

/-- ★ **The Born weight at the base-independent field is the table's own entry**, so the basin
really does carry the prescribed joint law — including a correlated one. -/
theorem skewBasin_prob_constJointContext (q : JointRates m n) (s : Fin m) (t : Fin n)
    (p : LF4.CPN N) :
    epistemicMeasure p (skewBasin (constJointContext (N := N) q) s t)
      = ENNReal.ofReal (q.rate s t) :=
  skewBasin_prob _ s t p

end CSD.RecordLayer

end

end
