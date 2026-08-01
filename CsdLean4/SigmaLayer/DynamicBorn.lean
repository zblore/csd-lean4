/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.ShearWitness

/-!
# SigmaLayer/DynamicBorn: the shear witness driven by the context-fixed basins (item 4)

**Category:** 7-SigmaLayer (the record layer — the dynamical Born rule).

`ShearWitness` proves the correlation for an *abstract* measurable index `ι`. This file supplies the
index the architecture actually intends — the one read off the **context-fixed basins** — so that the
dynamical outcome sectors carry the **Born weights**.

## What is proved

* `basinIndex` — the outcome index read off `globalBasin`, and `measurable_basinIndex`.
  The fibre over `i` is `globalBasin c i`, except over the default index where it also picks up the
  (null) set of points in no basin at all.
* `measure_basinIndex_fibre` — that null set costs nothing: the fibre has exactly the basin's
  measure.
* `shear_selector_born` — the selector-and-ready sectors carry the Born weights.

## ⚠️ Scope

Unchanged from `ShearWitness`: the propagator is explicit and every property is proved *of* it, but
**the Hamiltonian generation is stated, not formalised** (Mathlib has no manifold Hamiltonian-flow
API). This file closes the *Born* half of item 4, not item 3.

## References

`SigmaLayer/ShearWitness.lean`; `SigmaLayer/GlobalBasin.lean` (`globalBasin`, `globalBasin_born`,
`globalBasin_ae_total`); `SigmaLayer/MeasurementProtocol.lean`
(`measure_outcomeSector_eq_of_correlates`).
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {N : ℕ} [NeZero N]

/-! ### The index read off the basins -/

/-- **The outcome index of a point of `Σ_sel`**, read off the context-fixed basins. Points in no
basin — a null set — are sent to the default index. -/
noncomputable def basinIndex (c : ContextField N) (x : LF4.KSigma N) : Fin N :=
  open Classical in
  if h : ∃ i, x ∈ globalBasin c i then h.choose else 0

theorem basinIndex_eq_of_mem {c : ContextField N} {x : LF4.KSigma N} {i : Fin N}
    (hx : x ∈ globalBasin c i) : basinIndex c x = i := by
  classical
  have hex : ∃ j, x ∈ globalBasin c j := ⟨i, hx⟩
  unfold basinIndex
  rw [dif_pos hex]
  by_contra hne
  exact Set.disjoint_left.mp (globalBasin_pairwiseDisjoint c hne) hex.choose_spec hx

theorem measurable_basinIndex (c : ContextField N) : Measurable (basinIndex c) := by
  classical
  refine measurable_to_countable' fun i => ?_
  by_cases hi : i = 0
  · have hset : basinIndex c ⁻¹' {i} = globalBasin c i ∪ (⋃ j, globalBasin c j)ᶜ := by
      subst hi
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_compl_iff,
        Set.mem_iUnion, not_exists]
      constructor
      · intro hb
        by_cases hex : ∃ j, x ∈ globalBasin c j
        · obtain ⟨j, hj⟩ := hex
          have hj0 : j = 0 := by rw [← basinIndex_eq_of_mem hj]; exact hb
          exact Or.inl (hj0 ▸ hj)
        · exact Or.inr (by simpa [not_exists] using hex)
      · rintro (h | h)
        · exact basinIndex_eq_of_mem h
        · unfold basinIndex
          rw [dif_neg (by simpa [not_exists] using h)]
    rw [hset]
    exact (measurableSet_globalBasin c i).union
      (MeasurableSet.iUnion fun j => measurableSet_globalBasin c j).compl
  · have hset : basinIndex c ⁻¹' {i} = globalBasin c i := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hb
        by_cases hex : ∃ j, x ∈ globalBasin c j
        · obtain ⟨j, hj⟩ := hex
          have : basinIndex c x = j := basinIndex_eq_of_mem hj
          rw [this] at hb
          exact hb ▸ hj
        · exfalso
          apply hi
          unfold basinIndex at hb
          rw [dif_neg hex] at hb
          exact hb.symm
      · exact basinIndex_eq_of_mem
    rw [hset]
    exact measurableSet_globalBasin c i

/-- **The default index's extra fibre costs nothing.** The points in no basin form a null set
(`globalBasin_ae_total`), so every fibre of `basinIndex` carries exactly its basin's measure. -/
theorem measure_basinIndex_fibre (c : ContextField N) (p : LF4.CPN N) (i : Fin N) :
    epistemicMeasure p (basinIndex c ⁻¹' {i}) = epistemicMeasure p (globalBasin c i) := by
  classical
  have hsub1 : globalBasin c i ⊆ basinIndex c ⁻¹' {i} := fun _ hx => basinIndex_eq_of_mem hx
  have hsub2 : basinIndex c ⁻¹' {i} ⊆ globalBasin c i ∪ (⋃ j, globalBasin c j)ᶜ := by
    intro x hx
    by_cases hex : ∃ j, x ∈ globalBasin c j
    · obtain ⟨j, hj⟩ := hex
      have hji : basinIndex c x = j := basinIndex_eq_of_mem hj
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
      rw [hji] at hx
      exact Or.inl (hx ▸ hj)
    · exact Or.inr (by simpa [Set.mem_iUnion] using hex)
  have hnull : epistemicMeasure p ((⋃ j, globalBasin c j)ᶜ) = 0 := by
    have h := globalBasin_ae_total c p
    rwa [Set.compl_eq_univ_diff]
  refine le_antisymm ?_ (measure_mono hsub1)
  calc epistemicMeasure p (basinIndex c ⁻¹' {i})
      ≤ epistemicMeasure p (globalBasin c i ∪ (⋃ j, globalBasin c j)ᶜ) := measure_mono hsub2
    _ ≤ epistemicMeasure p (globalBasin c i) + epistemicMeasure p ((⋃ j, globalBasin c j)ᶜ) :=
        measure_union_le _ _
    _ = epistemicMeasure p (globalBasin c i) := by rw [hnull, add_zero]

/-- **★ The selector-and-ready sectors carry the Born weights.**

At preparation `ψ`, the sector "the hidden selector reads `i` and the apparatus is ready" has measure
`‖⟨eᵢ,ψ⟩‖²` under the initial product measure. Composed with `shear_correlates` and
`measure_outcomeSector_eq_of_correlates`, this is what makes the *dynamical* outcome weight the Born
weight — the probability is transported by the interaction, not posited for it. -/
theorem shear_selector_born (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (i : Fin N) :
    epistemicMeasure (Projectivization.mk ℂ ψ hψ0)
        (basinIndex (momentContext N) ⁻¹' {i})
      = ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2) := by
  rw [measure_basinIndex_fibre]
  exact globalBasin_born ψ hψ0 hψ i

end CSD.RecordLayer
