/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TorusFibre
public import CsdLean4.LF4.MomentMap

/-!
# SigmaLayer/GlobalBasin: context-fixed measurement basins on `Σ = ℂℙⁿ⁻¹ × T²`

**Category:** 7-SigmaLayer (the record layer — Paper C A7).

**Glossary:** https://glossary.constraintsurfacedynamics.com/outcome-region/ and
https://glossary.constraintsurfacedynamics.com/epistemic-measure/
Plain-language, CSD-role and formal statements of the outcome regions and the
epistemic measure, with this module as their Lean anchor. Kept symmetric by
`scripts/check-glossary.sh`.

## The problem this addresses

Paper C A7 asks for measurement regions `Ωᵢ(M)` **fixed by the apparatus alone**. The corpus's
record layer does not supply that: its partition is `cdfCell (bornRate ψ)`, built from the
*preparation*. `LF4/QubitBorn.lean` discharges the genuine context-fixed form at `N = 2`, and the
general-`N` **base-only** question is ⏸ parked (`specs/sigma-fibre-contextuality.md`) — the
`ContextFixedA7*` chain shows a base-only density is heavily constrained, without settling it in
either direction.

This file takes the *fibred* route that chain points at. The construction is due to an external
review of `29c6afd`:

> `Bᵢ(M) = {(p, θ₁, θ₂) : θ₁ ∈ circleCell (m_M p) i}`

with the rate vector read off **at the ontic point `p`**, not at the preparation. No `ψ` appears
anywhere in the definition, so the basin is a function of the context alone — which is what A7 asks.

★ **Why this is not circular.** One might object that the Born weights are being *put in* by using
the moment map. They are not put in by hand: `bornRate_eq_momentMap` (`RecordLayer/MomentMapRace.lean`)
already identifies the record-layer rates with the Fubini–Study torus moment map, forced by the
Kähler structure and the `Tⁿ` action rather than carved to a target.

★ **Why it does not collide with the parked `N ≥ 3` chain.** That chain constrains **base-only**
densities. This partition is genuinely *fibred* — the cell is an arc in `θ₁` — which is exactly where
`sigma-fibre-contextuality.md` concluded contextuality has to live at `N ≥ 3`.

## What is proved

* `ContextField` — a measurement context as a **rate field on the base**: a measurable, simplex-valued
  function `LF4.CPN N → Fin N → ℝ`. The apparatus fixes the field; the preparation plays no part.
* `globalBasin` — the basin, and `measurableSet_globalBasin`.
* `globalBasin_pairwiseDisjoint` — distinct outcomes are mutually exclusive.
* `epistemicMeasure` — the isolation-conditioned epistemic state `δ_p ⊗ Haar`.
* `globalBasin_prob` — **conditioning on the preparation returns the rate**:
  `epistemicMeasure p (globalBasin c i) = ENNReal.ofReal (c.rate p i)`.
* `momentContext` — the canonical context field, `rate := momentMap`, whose regularity is
  `LF4.measurable_momentMap`.
* `globalBasin_born` — **the headline.** At preparation `ψ`, the basin's epistemic probability is
  `‖⟨eᵢ, ψ⟩‖²`. The Born rule, from a partition that never mentions `ψ`.
* `globalBasin_ae_total` — a.e. microstate lands in some basin.

## Scope — read before citing

⚠️ **`δ_p ⊗ Haar` is the EPISTEMIC measure, not the sector's Liouville measure.** Conditioning on a
preparation means conditioning on `p = [ψ]`, a **null set** for `μ_FS`; the isolation-conditioned
state is taken to be the Dirac product outright — the corpus's "isolation is conditioning" reading
(P6). ~~a modelling choice stated as a definition, not a theorem~~ **SUPERSEDED 2026-08-21 (Q26)**:
the choice is now the theorem `epistemicMeasure_eq_disintegration`
(`RecordLayer/EpistemicDisintegration.lean`) — `kMuL` disintegrates along the base projection and
its disintegration kernel is `μ_FS`-a.e. the constant Haar kernel, so `δ_p ⊗ Haar` is the fibre of
the arena's own disintegration, planted at its base point. `kMuL = μ_FS ⊗ vol` remains the
Liouville measure, and nothing here claims `δ_p ⊗ Haar` is one.

⚠️ **This is KINEMATIC.** No interaction Hamiltonian `H_int(M)` generating these basins is
constructed — that is the open Paper D obligation (`RecordLayer/DeIsolationFlow.lean`), and it is
untouched here. A context-fixed partition is not a dynamical account of measurement.

⚠️ ~~A7 at general `N` is not thereby closed~~ **ANSWERED 2026-08-02 (author decision): the fibred
reading is canonical, so this construction — with the dynamical layer of v0.7.0 on top — DOES
discharge A7 at every `N`.** The parked `ContextFixedA7` chain now characterises whether a
*base-only* realisation also exists (the qubit-special-case question); it no longer gates the
axiom. See `reconstruction-status.md` §2.

⚠️ `KSigma` is still not proved Kähler, and the fibre measure is still exhibited as Haar rather than
shown Liouville. See the ★★ `specs/BACKLOG.md` row.

## References

`RecordLayer/TorusFibre.lean` (`torusCell`, `volume_torusCell`, `loSum_add_self_le_one`);
`LF4/MomentMap.lean` (`momentMap`, `measurable_momentMap`, `momentMap_mk_eq_inner_sq`);
`RecordLayer/MomentMapRace.lean` (`bornRate_eq_momentMap` — the rates are forced, not carved);
`LF4/KahlerInstance.lean` (`KSigma`, `KTorus`); `specs/BACKLOG.md` (the ★★ row's successor target);
`specs/sigma-fibre-contextuality.md`.
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

variable {N : ℕ}

/-! ### A measurement context as a rate field on the base -/

/-- **A measurement context**, as the data it actually contributes: a *rate field* on the ontic base.
The apparatus assigns to each base point `p` a probability vector over outcomes; the preparation
plays no part in the assignment.

This is the object Paper C A7 needs and the corpus's `bornContext ψ` is not: `rate` is a function of
the ontic point, so any region built from it depends on the context alone. -/
structure ContextField (N : ℕ) where
  /-- The rate assigned to each ontic base point. -/
  rate : LF4.CPN N → Fin N → ℝ
  /-- Each coordinate is measurable — the regularity that makes the basins measurable. -/
  measurable_rate : ∀ i, Measurable fun p => rate p i
  /-- The rates are non-negative. -/
  nonneg : ∀ p i, 0 ≤ rate p i
  /-- The rates are normalised: the field lands in the simplex. -/
  sum_one : ∀ p, ∑ i, rate p i = 1

namespace ContextField

variable (c : ContextField N)

theorem loSum_le_one (p : LF4.CPN N) (i : Fin N) : loSum (c.rate p) i + c.rate p i ≤ 1 :=
  loSum_add_self_le_one _ (c.nonneg p) (c.sum_one p) i

/-- `p ↦ loSum (rate p) i` is measurable: a finite sum of measurable coordinates. -/
theorem measurable_loSum (i : Fin N) : Measurable fun p : LF4.CPN N => loSum (c.rate p) i := by
  classical
  simpa [loSum] using
    Finset.measurable_sum (Finset.univ.filter fun k : Fin N => (k : ℕ) < (i : ℕ))
      fun k _ => c.measurable_rate k

end ContextField

/-! ### The basin -/

/-- **The context-fixed basin of outcome `i`.** A point of `Σ = ℂℙⁿ⁻¹ × T²` is in the basin when its
*first torus coordinate* lies in the CDF arc determined by the rate field **at its own base point**.

The definition mentions no preparation. That is the whole point: `Bᵢ` is fixed by `c`, i.e. by the
apparatus. -/
noncomputable def globalBasin (c : ContextField N) (i : Fin N) : Set (LF4.KSigma N) :=
  {x | x.2.1 ∈ circleCell (c.rate x.1) i}

/-- **The basin is measurable.** The three ingredients are the measurability of the canonical
representative (`measurable_rep`), of the rate field (`ContextField.measurable_rate`), and of its
partial sums — combined by `measurableSet_lt` / `measurableSet_le`, since the basin is cut out by
two inequalities between measurable real functions.

⚠️ This is where `LF4.measurable_momentMap` is needed for the canonical instance; before it was
proved, `momentMap`'s definition through the choice-based `Projectivization.rep` blocked this step. -/
theorem measurableSet_globalBasin (c : ContextField N) (i : Fin N) :
    MeasurableSet (globalBasin c i) := by
  have hbase : Measurable fun x : LF4.KSigma N => x.1 := measurable_fst
  have hrep : Measurable fun x : LF4.KSigma N => rep x.2.1 :=
    measurable_rep.comp (measurable_fst.comp measurable_snd)
  have hlo : Measurable fun x : LF4.KSigma N => loSum (c.rate x.1) i :=
    (c.measurable_loSum i).comp hbase
  have hhi : Measurable fun x : LF4.KSigma N => loSum (c.rate x.1) i + c.rate x.1 i :=
    hlo.add ((c.measurable_rate i).comp hbase)
  exact (measurableSet_lt hlo hrep).inter (measurableSet_le hrep hhi)

/-- **Distinct outcomes are mutually exclusive.** Fibrewise from `circleCell_pairwiseDisjoint`: at a
fixed base point the two arcs are disjoint, and both basins read the same base point. -/
theorem globalBasin_pairwiseDisjoint (c : ContextField N) :
    Pairwise (Function.onFun Disjoint (globalBasin c)) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun x hxi hxj => ?_
  exact Set.disjoint_left.mp
    (circleCell_pairwiseDisjoint (c.rate x.1) (c.nonneg x.1) hij) hxi hxj

/-! ### Conditioning on the preparation -/

/-- **The isolation-conditioned epistemic state at preparation `p`**: the base is known to be `p`,
the fibre microstate is unknown and Haar-distributed.

⚠️ This is the **epistemic** measure, not the Liouville measure `kMuL = μ_FS ⊗ vol`. Conditioning on
`p` conditions on a `μ_FS`-null set, so the Dirac product is taken as the definition rather than
obtained by disintegration. -/
noncomputable def epistemicMeasure (p : LF4.CPN N) : Measure (LF4.KSigma N) :=
  (Measure.dirac p).prod (volume : Measure LF4.KTorus)

instance (p : LF4.CPN N) : IsProbabilityMeasure (epistemicMeasure p) := by
  unfold epistemicMeasure; infer_instance

/-- **The slice of a basin over its own base point is a torus cell.** The bridge between the global
basin and `TorusFibre`'s fibrewise statements. -/
theorem preimage_globalBasin (c : ContextField N) (i : Fin N) (p : LF4.CPN N) :
    Prod.mk p ⁻¹' globalBasin c i = torusCell (c.rate p) i := by
  ext θ
  simp [globalBasin, torusCell, mem_prod]

/-- **★ Conditioning on the preparation returns the rate.** The basin was defined without reference
to any preparation; conditioning the epistemic state on `p` gives it probability `rate p i`. -/
theorem globalBasin_prob (c : ContextField N) (i : Fin N) (p : LF4.CPN N) :
    epistemicMeasure p (globalBasin c i) = ENNReal.ofReal (c.rate p i) := by
  rw [epistemicMeasure, Measure.prod_apply (measurableSet_globalBasin c i),
    lintegral_dirac' _ (by
      exact (measurable_measure_prodMk_left (measurableSet_globalBasin c i))),
    preimage_globalBasin]
  exact volume_torusCell _ (c.nonneg p) (c.loSum_le_one p) i

/-- **A.e. microstate lands in some basin**, so the readout is a.e. total. -/
theorem globalBasin_ae_total (c : ContextField N) (p : LF4.CPN N) :
    epistemicMeasure p (univ \ ⋃ i, globalBasin c i) = 0 := by
  classical
  have hmeas : ∀ i, MeasurableSet (globalBasin c i) := measurableSet_globalBasin c
  have hcover : epistemicMeasure p (⋃ i, globalBasin c i) = 1 := by
    rw [measure_iUnion (globalBasin_pairwiseDisjoint c) hmeas, tsum_fintype,
      Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => globalBasin_prob c i p,
      ← ENNReal.ofReal_sum_of_nonneg (fun i _ => c.nonneg p i), c.sum_one p, ENNReal.ofReal_one]
  rw [measure_sdiff (subset_univ _) (MeasurableSet.iUnion hmeas).nullMeasurableSet
      (by rw [hcover]; exact ENNReal.one_ne_top),
    measure_univ, hcover, tsub_self]

/-! ### The canonical context: the torus moment map -/

/-- **The canonical measurement context**: the Fubini–Study torus moment map. Its regularity is
`LF4.measurable_momentMap`, its simplex constraints `LF4.momentMap_nonneg` and
`LF4.momentMap_sum_eq_one`.

This is the context for a measurement in the standard basis; a general apparatus enters by
transporting the base point with the corresponding unitary. -/
noncomputable def momentContext (N : ℕ) : ContextField N where
  rate := LF4.momentMap
  measurable_rate := LF4.measurable_momentMap
  nonneg := LF4.momentMap_nonneg
  sum_one := LF4.momentMap_sum_eq_one

@[simp] theorem momentContext_rate (p : LF4.CPN N) : (momentContext N).rate p = LF4.momentMap p := rfl

/-- **★★ The Born rule from a partition that never mentions the preparation.**

At preparation `ψ`, the epistemic probability of the context-fixed basin `Bᵢ` is exactly the Born
weight `‖⟨eᵢ, ψ⟩‖²`. The basin is a function of the apparatus context alone (`momentContext`), the
preparation enters only through *which point of `Σ`'s base the system is at*, and the probability is
the Haar measure of an arc in the fibre.

This is the fibred form of Paper C A7, at every `N`. ⚠️ It is **kinematic**: no `H_int(M)` generating
these basins is constructed. -/
theorem globalBasin_born (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) (i : Fin N) :
    epistemicMeasure (Projectivization.mk ℂ ψ hψ0) (globalBasin (momentContext N) i)
      = ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2) := by
  rw [globalBasin_prob, momentContext_rate, LF4.momentMap_mk_eq_inner_sq ψ hψ0 hψ i]

end CSD.RecordLayer
