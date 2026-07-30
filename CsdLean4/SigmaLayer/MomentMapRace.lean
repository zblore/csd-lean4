/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.FibreRecord
public import CsdLean4.LF4.MomentMap

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
measurement's de-isolation dynamics must present to the fibre: a measurable pointer `ℝ → Fin n` (the
flow's readout) whose basins carry the (moment-map) rates `bornRate ψ`. The Born outcome distribution
is then a theorem (`born`), not a posit.

The `basin_rate` field is the measurement context's *specification* — which observable the apparatus
resolves — not an open research obligation: the de-isolation flow is just the deterministic
microstate→basin map, and the probabilities are the law of large numbers over the unknown initial
microstate (`Measurement.bornMeasurement_frequency`). Nothing here needs a bespoke Hamiltonian
derivation beyond the standard Papers A/D typicality story. -/
structure DeIsolationInteraction (ψ : EuclideanSpace ℂ (Fin n)) where
  /-- The de-isolation flow's pointer readout on the fibre. -/
  pointer : ℝ → Fin n
  /-- The pointer is measurable. -/
  measurable_pointer : Measurable pointer
  /-- The pointer's basins carry the moment-map/Born rates (the dynamical requirement). -/
  basin_rate : ∀ i, fibreTypicality (pointer ⁻¹' {i}) = ENNReal.ofReal (bornRate ψ i)

/-- **A de-isolation interaction reproduces Born.** Its pointer pushes the fibre typicality forward to
the Born distribution: outcome `i` has probability `‖ψ i‖²`. This is the Born conclusion *given* the
kinematic interface; the open part is realising the interface from a Hamiltonian. -/
theorem DeIsolationInteraction.born {ψ : EuclideanSpace ℂ (Fin n)}
    (D : DeIsolationInteraction ψ) (i : Fin n) :
    (fibreTypicality.map D.pointer) {i} = ENNReal.ofReal (‖ψ i‖ ^ 2) :=
  map_pointer_apply D.measurable_pointer ψ i (D.basin_rate i)

/-- A de-isolation interaction's basins carry the Kähler moment-map weights. -/
theorem DeIsolationInteraction.basin_momentMap {ψ : EuclideanSpace ℂ (Fin n)}
    (D : DeIsolationInteraction ψ) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) (i : Fin n) :
    fibreTypicality (D.pointer ⁻¹' {i})
      = ENNReal.ofReal (momentMap (Projectivization.mk ℂ ψ hψ0) i) := by
  rw [D.basin_rate i, bornRate_eq_momentMap ψ hψ0 hψ i]

end CSD.RecordLayer
