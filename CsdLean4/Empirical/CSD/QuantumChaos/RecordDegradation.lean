/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.QuantumChaos.RecordPersistence

/-!
# Record degradation under coupled post-record driving (§H continuation)

**Category:** 6-Empirical-CSD (the CSD reading of stroboscopic dynamics).

The pilot (`RecordPersistence.lean`) covered the UNCOUPLED regime: driving that
does not touch the record factor preserves every record cylinder surely. This
module prices the COUPLED regime — post-record driving that CAN move the
record — with the record-half-life bound.

## The right degradation quantity

For a measure-preserving coupled step `Φ`, the bare probability of a record
event never changes (`μ (Φ⁻¹ R) = μ R` is exactly measure preservation), so
"the record probability decays" is NOT the honest statement. What degrades is
**stability**: whether the trajectory's readout still shows the original
value. Accordingly:

* `recordFlip Φ ρ` — the per-step coupling set: points whose readout `ρ`
  changes in one step. Its measure `ε := μ (recordFlip Φ ρ)` is the
  **coupling strength**.
* `recordIntact Φ ρ n` — trajectories whose readout survives `n` periods
  unchanged.
* `exists_flip_of_ne` — a readout change within `n` periods forces a visit to
  the coupling set (the least-change argument, in induction form).
* ★★ `recordIntact_compl_measure_le` — **the record half-life bound**:
  `μ (recordIntact Φ ρ n)ᶜ ≤ n • ε`. A formed record survives `n` periods of
  coupled driving except on a set of measure at most `n · ε` — degradation is
  at most linear in time, at rate the per-step record-sector coupling.
* `recordIntact_compl_null_of_flip_null` — null coupling gives almost-sure
  persistence at every period count.
* `recordFlip_postRecordStep` / `recordIntact_postRecordStep` — the pilot
  recovered: uncoupled driving has EMPTY coupling set, and the half-life
  bound collapses to the pilot's sure persistence (`ε = 0`).
* `floquetRecordStep_recordFlip` — the CSD instantiation: the pilot's
  uncoupled Floquet record step has `ε = 0`; any measure-preserving coupled
  step on `(KSigma N) × Rec` is priced by the generic bound.

This is the discrete-time sibling of the record-erasure pricing the corpus
carries elsewhere (`collapse_accuracy_bound`'s spirit: touching records costs,
and the cost is quantified). Honest scope: the bound is an inequality in the
coupling measure, with no claim it is attained; exhibiting a small-coupling
witness with `0 < ε < 1` (a weakly record-coupled drive) is the thread's next
brick, recorded in BACKLOG §H. Cross-references:
`specs/external-library-map.md` §H, `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory

namespace CSD.Empirical.QuantumChaos

open _root_.QuantumChaos CSD.LF4

section Generic

variable {A V : Type*}

/-- The per-step coupling set: points whose readout changes in one step.
Empty exactly when the step does not couple to the record sector. -/
def recordFlip (Φ : A → A) (ρ : A → V) : Set A :=
  {a | ρ (Φ a) ≠ ρ a}

/-- Trajectories whose readout survives `n` periods unchanged. -/
def recordIntact (Φ : A → A) (ρ : A → V) (n : ℕ) : Set A :=
  {a | ∀ k ≤ n, ρ (Φ^[k] a) = ρ a}

/-- A readout change within `n` steps forces a visit to the coupling set
strictly earlier (the least-change argument, induction form). -/
lemma exists_flip_of_ne {Φ : A → A} {ρ : A → V} {a : A} {k : ℕ}
    (hk : ρ (Φ^[k] a) ≠ ρ a) :
    ∃ j < k, Φ^[j] a ∈ recordFlip Φ ρ := by
  induction k with
  | zero => exact absurd rfl hk
  | succ k ih =>
    by_cases hlast : ρ (Φ^[k + 1] a) = ρ (Φ^[k] a)
    · have hk' : ρ (Φ^[k] a) ≠ ρ a := by
        intro h
        exact hk (hlast.trans h)
      obtain ⟨j, hj, hmem⟩ := ih hk'
      exact ⟨j, Nat.lt_succ_of_lt hj, hmem⟩
    · refine ⟨k, Nat.lt_succ_self k, ?_⟩
      rw [Function.iterate_succ_apply'] at hlast
      exact hlast

/-- The unstable set is covered by the pulled-back coupling sets. -/
lemma compl_recordIntact_subset (Φ : A → A) (ρ : A → V) (n : ℕ) :
    (recordIntact Φ ρ n)ᶜ ⊆ ⋃ k ∈ Finset.range n, Φ^[k] ⁻¹' recordFlip Φ ρ := by
  intro a ha
  simp only [recordIntact, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at ha
  obtain ⟨k, hkn, hk⟩ := ha
  obtain ⟨j, hjk, hmem⟩ := exists_flip_of_ne hk
  exact Set.mem_biUnion (Finset.mem_range.mpr (lt_of_lt_of_le hjk hkn)) hmem

variable [MeasurableSpace A] {μ : Measure A}

/-- ★★ **The record half-life bound.** Under a measure-preserving (possibly
record-coupled) step, a formed record survives `n` periods except on a set of
measure at most `n · ε`, where `ε` is the measure of the per-step coupling
set: degradation is at most linear in time, at rate the record-sector
coupling. -/
theorem recordIntact_compl_measure_le {Φ : A → A} {ρ : A → V}
    (hΦ : MeasurePreserving Φ μ μ) (hD : MeasurableSet (recordFlip Φ ρ))
    (n : ℕ) :
    μ (recordIntact Φ ρ n)ᶜ ≤ n • μ (recordFlip Φ ρ) := by
  calc μ (recordIntact Φ ρ n)ᶜ
      ≤ μ (⋃ k ∈ Finset.range n, Φ^[k] ⁻¹' recordFlip Φ ρ) :=
        measure_mono (compl_recordIntact_subset Φ ρ n)
    _ ≤ ∑ k ∈ Finset.range n, μ (Φ^[k] ⁻¹' recordFlip Φ ρ) :=
        measure_biUnion_finset_le _ _
    _ = ∑ _k ∈ Finset.range n, μ (recordFlip Φ ρ) :=
        Finset.sum_congr rfl fun k _ =>
          (hΦ.iterate k).measure_preimage hD.nullMeasurableSet
    _ = n • μ (recordFlip Φ ρ) := by
        rw [Finset.sum_const, Finset.card_range]

/-- Null coupling gives almost-sure record persistence at every period
count. -/
theorem recordIntact_compl_null_of_flip_null {Φ : A → A} {ρ : A → V}
    (hΦ : MeasurePreserving Φ μ μ) (hD : MeasurableSet (recordFlip Φ ρ))
    (h0 : μ (recordFlip Φ ρ) = 0) (n : ℕ) :
    μ (recordIntact Φ ρ n)ᶜ = 0 :=
  by
    have h := recordIntact_compl_measure_le hΦ hD n
    rw [h0, smul_zero] at h
    exact le_zero_iff.mp h

end Generic

/-! ### The uncoupled case: the pilot recovered as `ε = 0` -/

section Uncoupled

variable {X R : Type*}

/-- Uncoupled driving has EMPTY coupling set: the readout never changes. -/
@[simp] lemma recordFlip_postRecordStep (f : X → X) :
    recordFlip (postRecordStep (R := R) f) Prod.snd = ∅ := by
  ext ⟨x, r⟩
  simp [recordFlip, postRecordStep]

/-- Under uncoupled driving every trajectory is record-intact at every period
count — the pilot's sure persistence, recovered as the `ε = 0` case of the
half-life bound. -/
lemma recordIntact_postRecordStep (f : X → X) (n : ℕ) :
    recordIntact (postRecordStep (R := R) f) Prod.snd n = Set.univ := by
  ext ⟨x, r⟩
  simp only [recordIntact, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  intro k _
  rw [prodMap_iterate]
  rfl

end Uncoupled

/-! ### The CSD instantiation -/

variable {N : ℕ}

/-- The pilot's Floquet record step has zero coupling: `ε = 0`. Any
measure-preserving COUPLED step on the same arena is priced by
`recordIntact_compl_measure_le` instead. -/
@[simp] lemma floquetRecordStep_recordFlip
    (U : Matrix.unitaryGroup (Fin N) ℂ) (Rec : Type*) :
    recordFlip (floquetRecordStep U Rec) Prod.snd = ∅ :=
  recordFlip_postRecordStep (floquetOnticStep U)

end CSD.Empirical.QuantumChaos
