/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.FibreRecord
public import CsdLean4.LF4.MomentMap
public import CsdLean4.Mathlib.MeasureTheory.CellPointer
public import CsdLean4.Mathlib.Probability.CompetingExponentials

/-!
# SigmaLayer/MomentMapRace: the record-layer rates are the Kähler moment map (MD-1, step 2b′)

**Category:** 7-SigmaLayer (the record layer — grounding the rates in the Kähler geometry).

This attacks the **wall** of step 2b′ (`specs/record-layer-plan.md` §3c): the first-passage race that
carves the fibre has rates `rᵢ`, and the CSD-native requirement is that those rates come from the
*Kähler geometry of the state* — the torus moment map — not from an injected/hand-picked probability
vector. That is **feature (2)** of the §3c decomposition, and it is what this file grounds in Lean.

## What is proved (feature 2, the rates are forced by geometry)

* `bornRate_eq_momentMap` — for a unit state the record-layer rate `bornRate ψ i = ‖ψ i‖²` is exactly
  the `i`-th coordinate of the Fubini–Study **torus moment map** at `[ψ]` (corpus `LF4/MomentMap.lean`,
  `momentMap`). So the fibre-partition rates are the moment map — forced by the Kähler structure and the
  `Tⁿ` action, no carving and no operational posit (`momentMap_mk`).
* `bornRate_eq_inner_sq` — hence the rate equals the corpus's Born weight `‖⟨eᵢ, ψ⟩‖²`
  (`momentMap_mk_eq_inner_sq`), the exact target of `FiniteQMClosure.born_frequency`. This ties the
  whole record-layer ladder to the established Born number.
* `fibreTypicality_bornCell_eq_momentMap` — the fibre typicality of the record event of outcome `i`
  equals the moment-map weight: the record-layer Born rule stated in Kähler/moment-map terms.
* ★★ `cdfDeIsolationInteraction` (Q12-a, 2026-08-23) — **a witness**: every unit state admits a
  `DeIsolationInteraction`, so `DeIsolationInteraction.born` is a conditional with a *populated*
  antecedent. Until this was built the structure had **no instance anywhere in the corpus** — an
  interface whose satisfiability was never exhibited, the defect `E5` closed for `E4`.
* ★★ `raceDeIsolationInteraction` (Q12-b′, 2026-08-23) — the **order-free** witness. The interface
  now takes an arbitrary fibre `(F, ν)` rather than the hard-wired `ℝ`, which is what lets the
  competing-clock race (on `Fin (n+1) → ℝ`, the dimension `record-layer-plan.md` §3b requires)
  instantiate it. Unlike the CDF witness this privileges no outcome.
  ⚠️ **Neither witness is the dynamical result.** The CDF cells are stacked in index order; the race
  cells are symmetric but their clock law is *posited*, and **no flow carves either family**. See
  `specs/q12-fibre-mechanism-scoping.md` (`Q12-c`, and `Q12-d` which is blocked).

## The STATISTICAL residual is not a wall — it is LLN over the unknown microstate

`DeIsolationInteraction` packages the interface a de-isolation flow presents to the fibre: a measurable
pointer whose basins carry the (moment-map) rates. From it the Born outcome distribution is a
**theorem** (`DeIsolationInteraction.born`), and its basins carry the moment-map weights
(`DeIsolationInteraction.basin_momentMap`). *Given the basins*, no extra stochastic postulate is
needed: the de-isolation flow is the deterministic microstate→basin map (which is what a measurement
*context* is), and the probabilistic content is the plain **law of large numbers over the unknown
initial microstate** (`SigmaLayer/Measurement.lean`, `bornMeasurement_frequency`) — randomness is
ignorance of the initial condition, the standard Papers A/D typicality story. This file grounds the
rates in the Kähler moment map; the statistics are LLN. Foundational-triple, no `sorry`.

⚠️ **CORRECTION 2026-07-30.** This section previously read "there is **no separate dynamical problem
to solve**". That was wrong, and it contradicted `DeIsolationFlow.lean`, which states the obligation
correctly. What is dissolved is the *statistical* residual — the need for a stochastic postulate on
top of the basins. What is **not** dissolved is the **dynamical** one: `basin_rate` is a *hypothesis
field*, and no interaction Hamiltonian `H_int(M)` whose flow generates those basins is constructed
anywhere in the corpus. That is the open Paper D obligation (`DeIsolationFlow.lean`, plan §3c, step
2b′), and this file does not touch it. Reading "the rates are the moment map" as "the dynamics are
solved" is exactly the inference this note exists to block.

## References
`specs/record-layer-plan.md` §3c (the first-passage race; step 2b′, feature 2); `LF4/MomentMap.lean`
(`momentMap`, `momentMap_mk`, `momentMap_mk_eq_inner_sq`); `SigmaLayer/DeIsolationFlow.lean`
(`fibreTypicality`, `map_pointer_apply`); `SigmaLayer/BornFibrePartition.lean` (`bornRate`, `cdfCell`);
`SigmaLayer/FiniteQMClosure.lean` (`born_frequency`, whose `‖⟨eᵢ,ψ⟩‖²` target this matches).
-/

@[expose] public section

open MeasureTheory Set
open CSD.LF4

namespace CSD.RecordLayer

variable {n : ℕ}

/-- **The record-layer rates are the torus moment map.** For a unit state the fibre-partition rate
`bornRate ψ i = ‖ψ i‖²` equals the `i`-th Fubini–Study moment-map coordinate at `[ψ]`. The rates are
*forced by the Kähler structure* (`momentMap_mk`), not an injected probability vector — feature (2) of
the §3c decomposition. -/
theorem bornRate_eq_momentMap (ψ : EuclideanSpace ℂ (Fin n)) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) (i : Fin n) :
    bornRate ψ i = momentMap (Projectivization.mk ℂ ψ hψ0) i := by
  unfold bornRate
  rw [momentMap_mk ψ hψ0 i, hψ, one_pow, div_one]

/-- The record-layer rate equals the corpus's Born weight `‖⟨eᵢ, ψ⟩‖²` — the exact target of
`FiniteQMClosure.born_frequency`. Via the moment map (`momentMap_mk_eq_inner_sq`). -/
theorem bornRate_eq_inner_sq (ψ : EuclideanSpace ℂ (Fin n)) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) (i : Fin n) :
    bornRate ψ i = ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 := by
  rw [bornRate_eq_momentMap ψ hψ0 hψ i, momentMap_mk_eq_inner_sq ψ hψ0 hψ i]

/-- **The record-layer Born rule in moment-map terms.** The fibre typicality of the record event of
outcome `i` equals the `i`-th moment-map weight at `[ψ]`. Combines `fibreTypicality_bornCell` (the
record-layer Born rule) with `bornRate_eq_momentMap` (the rate = the moment map). -/
theorem fibreTypicality_bornCell_eq_momentMap (ψ : EuclideanSpace ℂ (Fin n)) (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (i : Fin n) :
    fibreTypicality (cdfCell (bornRate ψ) i)
      = ENNReal.ofReal (momentMap (Projectivization.mk ℂ ψ hψ0) i) := by
  rw [fibreTypicality_bornCell ψ hψ i]
  congr 1
  exact bornRate_eq_momentMap ψ hψ0 hψ i

/-- **A de-isolation interaction (the residual kinematic input for step 2b′).** The data a
measurement's de-isolation dynamics must present to the fibre: a measurable pointer `F → Fin n` (the
flow's readout) whose basins carry the (moment-map) rates `bornRate ψ`. The Born outcome distribution
is then a theorem (`born`), not a posit.

⚠️ The `basin_rate` field is a **hypothesis field** — the open dynamical obligation, not a settled
specification (see the 2026-07-30 correction in the file header, which this docstring previously
contradicted). *Given* the basins no stochastic postulate remains: the probabilities are the law of
large numbers over the unknown initial microstate (`Measurement.bornMeasurement_frequency`). What
is **not** supplied is the dynamics — no interaction Hamiltonian `H_int(M)` whose flow generates
these basins is constructed anywhere in the corpus (`DeIsolationFlow.lean`, plan §3c, step 2b′).
The witnesses below (`cdfDeIsolationInteraction`, `raceDeIsolationInteraction`) discharge
`basin_rate` from *defined* cells — satisfiability, not a flow. -/
structure DeIsolationInteraction {F : Type*} [MeasurableSpace F] (ν : Measure F)
    (ψ : EuclideanSpace ℂ (Fin n)) where
  /-- The de-isolation flow's pointer readout on the fibre. -/
  pointer : F → Fin n
  /-- The pointer is measurable. -/
  measurable_pointer : Measurable pointer
  /-- The pointer's basins carry the moment-map/Born rates (the dynamical requirement). -/
  basin_rate : ∀ i, ν (pointer ⁻¹' {i}) = ENNReal.ofReal (bornRate ψ i)

/-- **A de-isolation interaction reproduces Born.** Its pointer pushes the fibre typicality forward to
the Born distribution: outcome `i` has probability `‖ψ i‖²`. This is the Born conclusion *given* the
kinematic interface; the open part is realising the interface from a Hamiltonian. -/
theorem DeIsolationInteraction.born {F : Type*} [MeasurableSpace F] {ν : Measure F}
    {ψ : EuclideanSpace ℂ (Fin n)} (D : DeIsolationInteraction ν ψ) (i : Fin n) :
    (ν.map D.pointer) {i} = ENNReal.ofReal (‖ψ i‖ ^ 2) :=
  map_pointer_apply D.measurable_pointer ψ i (D.basin_rate i)

/-- A de-isolation interaction's basins carry the Kähler moment-map weights. -/
theorem DeIsolationInteraction.basin_momentMap {F : Type*} [MeasurableSpace F] {ν : Measure F}
    {ψ : EuclideanSpace ℂ (Fin n)} (D : DeIsolationInteraction ν ψ) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (i : Fin n) :
    ν (D.pointer ⁻¹' {i})
      = ENNReal.ofReal (momentMap (Projectivization.mk ℂ ψ hψ0) i) := by
  rw [D.basin_rate i, bornRate_eq_momentMap ψ hψ0 hψ i]

/-! ### ★ Q12-a: the interface is populated

`DeIsolationInteraction` had **no instance** anywhere in the corpus — an interface whose antecedent
was never shown satisfiable, the same defect the equilibration arc's `E5` closed for `E4`. It is
satisfiable, and the pieces were already landed in `BornFibrePartition`; this section assembles
them.

⚠️ **What this is and is not.** It witnesses *satisfiability*, so the Born conclusion
`DeIsolationInteraction.born` is not vacuous. It is **not** the canonical mechanism: CDF stacking
imposes an arbitrary **outcome order**, whereas the mechanism §3b asks for is order-free (the
symmetric race). And no *dynamics* carves these cells — they are defined, not flowed to. Deriving
them from a de-isolation flow is `Q12-d`, which `specs/q12-fibre-mechanism-scoping.md` records as
blocked: the mixing hypothesis it needs is unsatisfiable by any flow the corpus defines. -/

/-- ★★ **The CDF witness.** Every unit state admits a `DeIsolationInteraction` on the fibre `ℝ`, so
`DeIsolationInteraction.born` is a conditional with a **populated** antecedent. The pointer is the
generic `cellPointer` of the Born cells; the cells are disjoint (`cdfCell_pairwiseDisjoint`) and
carry the Born weights (`fibreTypicality_bornCell`), which is all `measure_cellPointer_preimage`
needs.

See the section note above for what this does *not* settle. -/
noncomputable def cdfDeIsolationInteraction (ψ : EuclideanSpace ℂ (Fin n)) (hψ : ‖ψ‖ = 1)
    (i₀ : Fin n) : DeIsolationInteraction fibreTypicality ψ where
  pointer := cellPointer (cdfCell (bornRate ψ)) i₀
  measurable_pointer :=
    measurable_cellPointer (measurableSet_cdfCell _)
      (cdfCell_pairwiseDisjoint _ (bornRate_nonneg ψ)) i₀
  basin_rate := fun i =>
    measure_cellPointer_preimage (measurableSet_cdfCell _)
      (cdfCell_pairwiseDisjoint _ (bornRate_nonneg ψ)) (bornRate_nonneg ψ)
      (fun j => fibreTypicality_bornCell ψ hψ j) (sum_bornRate_unit ψ hψ) i₀ i

/-! ### ★★ Q12-b′: the **order-free** witness, on an `n`-dimensional fibre

`Q12-b` proved the competing-clock race reproduces Born without privileging any outcome
(`ProbabilityTheory.measure_raceCell_of_sum_eq_one`), but the race lives on `Fin (n+1) → ℝ` while
the interface above was written for the fibre `ℝ`. That mismatch is now gone: the interface takes
an arbitrary fibre `(F, ν)`, so the race supplies a **second, symmetric** witness.

⚠️ Still not the dynamical result. No flow carves these cells either — the clocks' law is posited,
not derived. That is `Q12-c` (is the exponential law forced?) and `Q12-d` (blocked; see
`specs/q12-fibre-mechanism-scoping.md`). -/

/-- ★★ **The race witness.** For a unit state with every amplitude nonzero, the competing-clock
race is a `DeIsolationInteraction` on the fibre `Fin (n+1) → ℝ`.

Unlike `cdfDeIsolationInteraction` this privileges no outcome: the cells are "clock `i` fires
strictly first", and relabelling the clocks merely permutes them. This is the mechanism
`record-layer-plan.md` §3b asks for.

The positivity hypothesis is real, not technical: an exponential clock needs a positive rate, so a
zero amplitude — a clock that never fires — is outside the construction. -/
noncomputable def raceDeIsolationInteraction {m : ℕ} (ψ : EuclideanSpace ℂ (Fin (m + 1)))
    (hψ : ‖ψ‖ = 1) (hpos : ∀ j, 0 < bornRate ψ j) (i₀ : Fin (m + 1)) :
    DeIsolationInteraction
      (Measure.pi (fun j => ProbabilityTheory.expMeasure (bornRate ψ j))) ψ where
  pointer := cellPointer ProbabilityTheory.raceCell i₀
  measurable_pointer :=
    measurable_cellPointer ProbabilityTheory.measurableSet_raceCell
      ProbabilityTheory.raceCell_pairwiseDisjoint i₀
  basin_rate := fun i => by
    have hprob : ∀ j : Fin (m + 1),
        IsProbabilityMeasure (ProbabilityTheory.expMeasure (bornRate ψ j)) :=
      fun j => ProbabilityTheory.isProbabilityMeasure_expMeasure (hpos j)
    exact measure_cellPointer_preimage ProbabilityTheory.measurableSet_raceCell
      ProbabilityTheory.raceCell_pairwiseDisjoint (bornRate_nonneg ψ)
      (fun j => ProbabilityTheory.measure_raceCell_of_sum_eq_one _ hpos
        (sum_bornRate_unit ψ hψ) j)
      (sum_bornRate_unit ψ hψ) i₀ i

end CSD.RecordLayer
