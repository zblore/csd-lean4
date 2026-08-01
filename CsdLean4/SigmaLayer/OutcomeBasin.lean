/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.OutcomeField

/-!
# SigmaLayer/OutcomeBasin: basins for a `K`-outcome field

**Category:** 7-SigmaLayer (the record layer — generalisation bridge).

`OutcomeField.lean` decoupled the outcome count from the dimension but left the bridge unbuilt:
`globalBasin` still consumed a `ContextField`, so a `K`-outcome field could not drive the record
layer. This file builds that bridge, so **degenerate projective measurements reach the basins**.

The construction is the same one — the rate field is read at the ontic point, and the basin is the
CDF arc it determines — with `Fin K` in place of `Fin N`.

## What is proved

* `outcomeBasin` — `Bᵢ(c) = {x | x.2.1 ∈ circleCell (c.rate x.1) i}` for `c : OutcomeField N K`.
* `measurableSet_outcomeBasin`, `outcomeBasin_pairwiseDisjoint`.
* `outcomeBasin_prob` — conditioning on `p` returns `rate p i`.
* `outcomeBasin_ae_total`.
* `outcomeBasin_toOutcomeField` — ★ **conservativity**: for a `ContextField` this is *definitionally*
  `globalBasin`. The generalisation adds cases without changing any existing one.

## ⚠️ Scope

Still kinematic, and `δ_p ⊗ Haar` is still the epistemic measure taken as a definition rather than a
disintegration — inherited unchanged from `GlobalBasin.lean`. Driving the *dynamical* layer with a
`K`-outcome field additionally needs the shear witness's index function generalised, which is not
done here.

## References

`SigmaLayer/OutcomeField.lean` (`OutcomeField`, `blockField`); `SigmaLayer/GlobalBasin.lean` (the
`K = N` original this generalises).
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

variable {N K : ℕ}

namespace OutcomeField

variable (c : OutcomeField N K)

theorem loSum_le_one (p : LF4.CPN N) (i : Fin K) : loSum (c.rate p) i + c.rate p i ≤ 1 :=
  loSum_add_self_le_one _ (c.nonneg p) (c.sum_one p) i

theorem measurable_loSum (i : Fin K) : Measurable fun p : LF4.CPN N => loSum (c.rate p) i := by
  classical
  simpa [loSum] using
    Finset.measurable_sum (Finset.univ.filter fun k : Fin K => (k : ℕ) < (i : ℕ))
      fun k _ => c.measurable_rate k

end OutcomeField

/-- **The basin of outcome `i`** for a `K`-outcome field. -/
noncomputable def outcomeBasin (c : OutcomeField N K) (i : Fin K) : Set (LF4.KSigma N) :=
  {x | x.2.1 ∈ circleCell (c.rate x.1) i}

/-- ★ **Conservativity**: for a `ContextField` the generalised basin *is* `globalBasin`,
definitionally. -/
theorem outcomeBasin_toOutcomeField (c : ContextField N) (i : Fin N) :
    outcomeBasin c.toOutcomeField i = globalBasin c i := rfl

theorem measurableSet_outcomeBasin (c : OutcomeField N K) (i : Fin K) :
    MeasurableSet (outcomeBasin c i) := by
  have hrep : Measurable fun x : LF4.KSigma N => rep x.2.1 :=
    measurable_rep.comp (measurable_fst.comp measurable_snd)
  have hlo : Measurable fun x : LF4.KSigma N => loSum (c.rate x.1) i :=
    (c.measurable_loSum i).comp measurable_fst
  have hhi : Measurable fun x : LF4.KSigma N => loSum (c.rate x.1) i + c.rate x.1 i :=
    hlo.add ((c.measurable_rate i).comp measurable_fst)
  exact (measurableSet_lt hlo hrep).inter (measurableSet_le hrep hhi)

theorem outcomeBasin_pairwiseDisjoint (c : OutcomeField N K) :
    Pairwise (Function.onFun Disjoint (outcomeBasin c)) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun x hxi hxj => ?_
  exact Set.disjoint_left.mp
    (circleCell_pairwiseDisjoint (c.rate x.1) (c.nonneg x.1) hij) hxi hxj

theorem preimage_outcomeBasin (c : OutcomeField N K) (i : Fin K) (p : LF4.CPN N) :
    Prod.mk p ⁻¹' outcomeBasin c i = torusCell (c.rate p) i := by
  ext θ
  simp [outcomeBasin, torusCell, mem_prod]

/-- **Conditioning on the preparation returns the rate**, for any number of outcomes. -/
theorem outcomeBasin_prob (c : OutcomeField N K) (i : Fin K) (p : LF4.CPN N) :
    epistemicMeasure p (outcomeBasin c i) = ENNReal.ofReal (c.rate p i) := by
  rw [epistemicMeasure, Measure.prod_apply (measurableSet_outcomeBasin c i),
    lintegral_dirac' _ (measurable_measure_prodMk_left (measurableSet_outcomeBasin c i)),
    preimage_outcomeBasin]
  exact volume_torusCell _ (c.nonneg p) (c.loSum_le_one p) i

theorem outcomeBasin_ae_total (c : OutcomeField N K) (p : LF4.CPN N) :
    epistemicMeasure p (univ \ ⋃ i, outcomeBasin c i) = 0 := by
  classical
  have hmeas : ∀ i, MeasurableSet (outcomeBasin c i) := measurableSet_outcomeBasin c
  have hcover : epistemicMeasure p (⋃ i, outcomeBasin c i) = 1 := by
    rw [measure_iUnion (outcomeBasin_pairwiseDisjoint c) hmeas, tsum_fintype,
      Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => outcomeBasin_prob c i p,
      ← ENNReal.ofReal_sum_of_nonneg (fun i _ => c.nonneg p i), c.sum_one p, ENNReal.ofReal_one]
  rw [measure_diff (subset_univ _) (MeasurableSet.iUnion hmeas).nullMeasurableSet
      (by rw [hcover]; exact ENNReal.one_ne_top),
    measure_univ, hcover, tsub_self]

end CSD.RecordLayer
