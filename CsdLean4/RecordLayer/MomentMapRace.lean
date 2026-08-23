/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.FibreRecord
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
* ★★ `cdfDeIsolationInteraction` (Q12-a, 2026-08-23) — **a witness**: every unit state admits a
  `DeIsolationInteraction`, so `DeIsolationInteraction.born` is a conditional with a *populated*
  antecedent. Until this was built the structure had **no instance anywhere in the corpus** — an
  interface whose satisfiability was never exhibited, the defect `E5` closed for `E4`.
  ⚠️ It witnesses satisfiability only: CDF stacking imposes an arbitrary outcome **order** (the
  mechanism `record-layer-plan.md` §3b wants is order-free), and **no dynamics carves these cells**.
  See `specs/q12-fibre-mechanism-scoping.md`.

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

/-- The **CDF pointer**: read the outcome off the fibre point, sending the leftover (a null set)
to a default outcome so that the pointer is total, as the interface requires. -/
noncomputable def cdfPointer (r : Fin n → ℝ) (i₀ : Fin n) (ξ : ℝ) : Fin n :=
  (fibreOutcome r ξ).getD i₀

lemma cdfPointer_preimage (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (i₀ i : Fin n) :
    cdfPointer r i₀ ⁻¹' {i}
      = cdfCell r i ∪ (if i = i₀ then (⋃ j, cdfCell r j)ᶜ else ∅) := by
  ext ξ
  simp only [Set.mem_preimage, Set.mem_singleton_iff, cdfPointer, Set.mem_union]
  cases hopt : fibreOutcome r ξ with
  | none =>
      have hnone : ∀ j, ξ ∉ cdfCell r j := (fibreOutcome_eq_none_iff r ξ).mp hopt
      simp only [Option.getD_none]
      constructor
      · rintro rfl
        refine Or.inr ?_
        rw [if_pos rfl, Set.mem_compl_iff, Set.mem_iUnion]
        rintro ⟨j, hj⟩
        exact hnone j hj
      · rintro (hmem | hmem)
        · exact absurd hmem (hnone i)
        · by_cases hii : i = i₀
          · exact hii.symm
          · rw [if_neg hii] at hmem
            exact absurd hmem (by simp)
  | some j =>
      have hj : ξ ∈ cdfCell r j := (fibreOutcome_eq_some_iff r hr ξ j).mp hopt
      have hin : ξ ∈ ⋃ k, cdfCell r k := Set.mem_iUnion.mpr ⟨j, hj⟩
      simp only [Option.getD_some]
      constructor
      · rintro rfl
        exact Or.inl hj
      · rintro (hmem | hmem)
        · have hsome := (fibreOutcome_eq_some_iff r hr ξ i).mpr hmem
          rw [hopt, Option.some_inj] at hsome
          exact hsome
        · by_cases hii : i = i₀
          · rw [if_pos hii, Set.mem_compl_iff] at hmem
            exact absurd hin hmem
          · rw [if_neg hii] at hmem
            exact absurd hmem (by simp)

lemma measurable_cdfPointer (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (i₀ : Fin n) :
    Measurable (cdfPointer r i₀) := by
  refine measurable_to_countable' (fun i => ?_)
  rw [cdfPointer_preimage r hr i₀ i]
  refine (measurableSet_cdfCell r i).union ?_
  by_cases hii : i = i₀
  · rw [if_pos hii]
    exact (MeasurableSet.iUnion (fun j => measurableSet_cdfCell r j)).compl
  · rw [if_neg hii]
    exact MeasurableSet.empty

/-- The leftover — the fibre points lying in no cell — is `fibreTypicality`-null for a unit state,
because the cells sit inside `[0,1)` (`iUnion_bornCell_subset_Ico01`) and already carry its whole
measure (`fibreTypicality_iUnion_bornCell`). -/
lemma fibreTypicality_compl_iUnion_bornCell (ψ : EuclideanSpace ℂ (Fin n)) (hψ : ‖ψ‖ = 1) :
    fibreTypicality ((⋃ j, cdfCell (bornRate ψ) j)ᶜ) = 0 := by
  have hmeas : MeasurableSet (⋃ j, cdfCell (bornRate ψ) j) :=
    MeasurableSet.iUnion (fun j => measurableSet_cdfCell _ j)
  have htot : fibreTypicality (⋃ j, cdfCell (bornRate ψ) j) = 1 :=
    fibreTypicality_iUnion_bornCell ψ hψ
  rw [measure_compl hmeas (by rw [htot]; exact ENNReal.one_ne_top), htot, measure_univ, tsub_self]

/-- ★★ **The witness.** Every unit state admits a `DeIsolationInteraction`, so
`DeIsolationInteraction.born` is a conditional with a **populated** antecedent. The pointer is the
CDF readout; its basins are the Born cells, whose fibre typicality is the Born weight
(`fibreTypicality_bornCell`), and the leftover is null
(`fibreTypicality_compl_iUnion_bornCell`).

See the section note above for what this does *not* settle. -/
noncomputable def cdfDeIsolationInteraction (ψ : EuclideanSpace ℂ (Fin n)) (hψ : ‖ψ‖ = 1)
    (i₀ : Fin n) : DeIsolationInteraction ψ where
  pointer := cdfPointer (bornRate ψ) i₀
  measurable_pointer := measurable_cdfPointer _ (bornRate_nonneg ψ) i₀
  basin_rate := by
    intro i
    have hcell : fibreTypicality (cdfCell (bornRate ψ) i) = ENNReal.ofReal (bornRate ψ i) :=
      fibreTypicality_bornCell ψ hψ i
    rw [cdfPointer_preimage _ (bornRate_nonneg ψ) i₀ i]
    by_cases hii : i = i₀
    · rw [if_pos hii]
      refine le_antisymm ?_ ?_
      · refine le_trans (measure_union_le _ _) ?_
        rw [hcell, fibreTypicality_compl_iUnion_bornCell ψ hψ, add_zero]
      · rw [← hcell]
        exact measure_mono Set.subset_union_left
    · rw [if_neg hii, Set.union_empty, hcell]

end CSD.RecordLayer
