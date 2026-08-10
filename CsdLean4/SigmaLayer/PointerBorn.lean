/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.PointerProtocol

/-!
# SigmaLayer/PointerBorn: the ε-Born sandwich and the smooth-horn closure (brick 4b)

**Category:** dynamical measurement — the smooth-Hamiltonian witness route
(`specs/pointer-witness-plan.md` brick 4, Born half; closes brick 4).

The preparation is honest about what the smooth witness offers: the epistemic state at base
point `p` on the sector, and the pointer **conditioned on the ready region** —

  `pointerPrep p q₀ δ = epistemicMeasure p ⊗ (μ_FS[| readyRegion δ])`,

a probability measure because the ready region has **positive FS measure** (`readyRegion_pos`)
— no Dirac calibration posit anywhere, unlike the swap witness, whose exact collapse forced
one (`collapse_accuracy_bound`).

★ **The ε-Born sandwich** (`pointer_born_lower` / `pointer_born_upper`): for every context
with continuous rates, every preparation, every outcome,

  `rⱼ − 2ε  ≤  pointerPrep(outcomeSector j)  ≤  rⱼ + 2(N−1)ε`,

with `rⱼ = c.rate p j` the context rate at the base point. The lower bound is the sector
measure `= rⱼ − 2ε` **exactly** (`pointerPrep_sector_measure`, via the brick-3 slice volume)
plus the correlation; the upper bound needs **no cell geometry at all** — the outcome sectors
are pairwise disjoint and the lower bounds of the other `N − 1` outcomes crowd out everything
above `rⱼ + 2(N−1)ε` in a probability space.

★★ **The smooth-horn closure** (*strengthened 2026-08-04: `evolve_eq`/`stroke_eq` fields
added, so the continuity and Liouville claims are now about the bundled `protocol` rather
than about globally-named maps that merely coincided with it*) (`SmoothWitnessClosure` / `smoothWitnessClosure`, instantiated
on the canonical moment-map context by `smoothWitnessClosureCanonical`): one witness carries,
simultaneously — the protocol (two-time law = exponential group property), **joint time–state
continuity**, Liouville preservation, a positive-measure ready state, record creation with
the ontic sector selecting the outcome (correlation), structural persistence, and Born up to
the stated `ε`. This is the smooth horn of the `no_everywhere_correlation` trade-off, exactly
as `specs/pointer-witness-plan.md` scoped it: the piecewise witnesses keep exact records and
exact Born at the price of discontinuity; this witness keeps continuity (and the papers'
smooth-Hamiltonian architecture, at the formalisable level) at the price of `ε`.

⚠️ **Honest scope.** `ε` is a free parameter of the witness — the bounds hold for every
`ε > 0`, but no limit statement is made here, and the corridor mass (up to `2Nε`) genuinely
receives no record. The Hamiltonian-generation statement for the **full modulated** coupling
and the Lüders composition remain brick 5; the closure's `born` fields are sector-measure
bounds, not an LLN frequency statement (the LLN layer can consume them exactly as
`arena_mixed_born_frequency` consumed exact weights, a recorded extension).

## References

`specs/pointer-witness-plan.md` (bricks 4, 5); `specs/BACKLOG.md` (the ★ L row);
`specs/future-work.md`. Reused corpus API: `epistemicMeasure`/`globalBasin_prob` slice
pattern (`SigmaLayer/GlobalBasin.lean`), `volume_shrunkCell_slice`
(`SigmaLayer/PointerLanding.lean`), `pointerProtocol` + correlation/invariance
(`SigmaLayer/PointerProtocol.lean`), `ProbabilityTheory.cond` (Mathlib +
`CsdLean4/Mathlib/Probability/ConditionalProbability.lean` staging).
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory Matrix Matrix.UnitaryGroup ProbabilityTheory
open scoped ProbabilityTheory ENNReal

variable {N : ℕ} [NeZero N]

/-! ### The preparation -/

/-- **The smooth witness's preparation**: epistemic state at `p` on the sector, FS
conditioned on the ready region on the pointer. Conditioning is legitimate — the ready
region has positive measure (`readyRegion_pos`) — so no Dirac calibration posit enters. -/
noncomputable def pointerPrep (p : LF4.CPN N) (q₀ : Pointer N) (δ : ℝ) :
    Measure (PointerArena N N) :=
  (epistemicMeasure p).prod ((fubiniStudyMeasure q₀)[|readyRegion (K := N) δ])

omit [NeZero N] in
theorem isProbabilityMeasure_pointerPrep (p : LF4.CPN N) (q₀ : Pointer N) {δ : ℝ}
    (hδpos : 0 < δ) : IsProbabilityMeasure (pointerPrep p q₀ δ) := by
  have := ProbabilityTheory.cond_isProbabilityMeasure
    (μ := fubiniStudyMeasure q₀) (readyRegion_pos q₀ hδpos)
  unfold pointerPrep
  infer_instance

omit [NeZero N] in
/-- **The sector carries exactly its shrunk-slice mass**:
`pointerPrep (pointerSector j) = rⱼ − 2ε`. The base-point slice is the brick-3 volume; the
ready conditioning contributes the factor `1`. -/
theorem pointerPrep_sector_measure (c : ContextField N) {ε δ : ℝ} (hε : 0 ≤ ε)
    (hδpos : 0 < δ) (p : LF4.CPN N) (q₀ : Pointer N) (j : Fin N) :
    pointerPrep p q₀ δ (pointerSector c ε δ j)
      = ENNReal.ofReal (c.rate p j - 2 * ε) := by
  have := ProbabilityTheory.cond_isProbabilityMeasure
    (μ := fubiniStudyMeasure q₀) (readyRegion_pos q₀ hδpos)
  rw [pointerPrep, pointerSector, Measure.prod_prod,
    ProbabilityTheory.cond_apply_self (readyRegion_pos q₀ hδpos) (measure_ne_top _ _),
    mul_one, epistemicMeasure, Measure.prod_apply (measurableSet_shrunkCell c ε j),
    lintegral_dirac' _ (measurable_measure_prodMk_left (measurableSet_shrunkCell c ε j))]
  exact volume_shrunkCell_slice c hε p j

/-! ### The ε-Born sandwich -/

omit [NeZero N] in
/-- ★ **The lower Born bound**: the outcome sector carries at least the shrunk-cell mass
`rⱼ − 2ε` — sector containment (the landing theorem) plus the exact sector measure. -/
theorem pointer_born_lower (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) {ε δ : ℝ} (hε : 0 < ε) (hδpos : 0 < δ)
    (hδ : δ ≤ 1 / 2) (p : LF4.CPN N) (q₀ : Pointer N) (j : Fin N) :
    ENNReal.ofReal (c.rate p j - 2 * ε)
      ≤ pointerPrep p q₀ δ ((pointerProtocol c hc ε hδ).outcomeSector j) := by
  rw [← pointerPrep_sector_measure c hε.le hδpos p q₀ j]
  exact measure_mono (pointerProtocol_correlatesOn c hc hε hδ j)

/-- `ofReal` is subadditive over finite sums. -/
lemma ofReal_finset_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

/-- ★ **The upper Born bound** — with **no upper-bound cell geometry**: the sectors are
pairwise disjoint, the other `N − 1` lower bounds crowd out everything above
`rⱼ + 2(N−1)ε` in a probability space. -/
theorem pointer_born_upper (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) {ε δ : ℝ} (hε : 0 < ε) (hδpos : 0 < δ)
    (hδ : δ ≤ 1 / 2) (p : LF4.CPN N) (q₀ : Pointer N) (i : Fin N) :
    pointerPrep p q₀ δ ((pointerProtocol c hc ε hδ).outcomeSector i)
      ≤ ENNReal.ofReal (c.rate p i + 2 * ((N : ℝ) - 1) * ε) := by
  classical
  have := isProbabilityMeasure_pointerPrep p q₀ hδpos
  set P := pointerProtocol c hc ε hδ with hP
  set μ := pointerPrep p q₀ δ with hμ
  have hunion : μ (⋃ j ∈ (Finset.univ : Finset (Fin N)), P.outcomeSector j)
      = ∑ j, μ (P.outcomeSector j) :=
    measure_biUnion_finset (fun a _ b _ hab => P.outcomeSector_pairwiseDisjoint hab)
      (fun j _ => P.outcomeSector_measurable j)
  have hsum : (∑ j, μ (P.outcomeSector j)) ≤ 1 := hunion ▸ prob_le_one
  have hsplit : μ (P.outcomeSector i) + ∑ j ∈ Finset.univ.erase i, μ (P.outcomeSector j)
      = ∑ j, μ (P.outcomeSector j) :=
    Finset.add_sum_erase Finset.univ (fun j => μ (P.outcomeSector j)) (Finset.mem_univ i)
  have herase : ENNReal.ofReal (∑ j ∈ Finset.univ.erase i, (c.rate p j - 2 * ε))
      ≤ ∑ j ∈ Finset.univ.erase i, μ (P.outcomeSector j) := by
    refine (ofReal_finset_sum_le _ _).trans ?_
    exact Finset.sum_le_sum fun j _ => pointer_born_lower c hc hε hδpos hδ p q₀ j
  have hval : ∑ j ∈ Finset.univ.erase i, (c.rate p j - 2 * ε)
      = 1 - (c.rate p i + 2 * ((N : ℝ) - 1) * ε) := by
    have h1 : c.rate p i + ∑ j ∈ Finset.univ.erase i, c.rate p j = ∑ j, c.rate p j :=
      Finset.add_sum_erase Finset.univ (fun j => c.rate p j) (Finset.mem_univ i)
    have h2 : ∑ _j ∈ Finset.univ.erase i, (2 * ε : ℝ) = ((N : ℝ) - 1) * (2 * ε) := by
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub NeZero.one_le,
        Nat.cast_one]
    have h3 := c.sum_one p
    rw [Finset.sum_sub_distrib, h2]
    have h4 : ∑ j ∈ Finset.univ.erase i, c.rate p j = 1 - c.rate p i := by linarith
    rw [h4]
    ring
  rcases le_or_gt 1 (c.rate p i + 2 * ((N : ℝ) - 1) * ε) with hcase | hcase
  · calc μ (P.outcomeSector i) ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hcase
  · have hy0 : (0 : ℝ) ≤ 1 - (c.rate p i + 2 * ((N : ℝ) - 1) * ε) := by linarith
    have hkey : μ (P.outcomeSector i)
        + ENNReal.ofReal (1 - (c.rate p i + 2 * ((N : ℝ) - 1) * ε)) ≤ 1 := by
      calc μ (P.outcomeSector i)
            + ENNReal.ofReal (1 - (c.rate p i + 2 * ((N : ℝ) - 1) * ε))
          = μ (P.outcomeSector i)
            + ENNReal.ofReal (∑ j ∈ Finset.univ.erase i, (c.rate p j - 2 * ε)) := by
            rw [hval]
        _ ≤ μ (P.outcomeSector i) + ∑ j ∈ Finset.univ.erase i, μ (P.outcomeSector j) :=
            add_le_add le_rfl herase
        _ = ∑ j, μ (P.outcomeSector j) := hsplit
        _ ≤ 1 := hsum
    have h1 := ENNReal.le_sub_of_add_le_right ENNReal.ofReal_ne_top hkey
    have h2 : (1 : ℝ≥0∞) - ENNReal.ofReal (1 - (c.rate p i + 2 * ((N : ℝ) - 1) * ε))
        = ENNReal.ofReal (c.rate p i + 2 * ((N : ℝ) - 1) * ε) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hy0]
      congr 1
      ring
    rw [h2] at h1
    exact h1

/-! ### The smooth-horn closure -/

/-- ★★ **The smooth-horn closure**: one witness carrying, simultaneously — the protocol
(two-time law = exponential group property), joint time–state continuity, Liouville
preservation, a positive-measure ready state, record creation with the ontic sector
selecting the outcome, structural persistence, and Born up to the stated `ε`. The smooth
horn of the `no_everywhere_correlation` trade-off, complementing (never displacing) the
exact-record piecewise closures. -/
structure SmoothWitnessClosure (c : ContextField N) (ε δ : ℝ) where
  /-- The measurement protocol (ramped exponential of the modulated coupling). -/
  protocol : MeasurementProtocol (PointerArena N N) N
  /-- Joint time–state continuity of the ramped propagator (definitionally the protocol's
  `evolve` — `pointerRampedEvolve_eq_protocol`). -/
  jointly_continuous : ∀ s : ℝ, Continuous (pointerRampedEvolve c ε s)
  /-- Liouville preservation of the measurement stroke. -/
  liouville : ∀ (p₀ : LF4.CPN N) (q₀ : Pointer N),
    MeasurePreserving (pointerEvolve c ε) (pointerLiouville p₀ q₀) (pointerLiouville p₀ q₀)
  /-- The apparatus-ready state has positive Liouville measure. -/
  ready_pos : ∀ (p₀ : LF4.CPN N) (q₀ : Pointer N),
    pointerLiouville p₀ q₀ (arenaReady N δ) ≠ 0
  /-- Record creation: every pointer sector lands in its outcome's record cylinder. -/
  correlates : protocol.CorrelatesOn (pointerSector c ε δ)
  /-- Structural persistence: the pointer regions are invariant on the record window. -/
  invariant : protocol.PointerInvariantOn
  /-- The lower Born bound `rⱼ − 2ε`. -/
  born_lower : ∀ (p : LF4.CPN N) (q₀ : Pointer N) (j : Fin N),
    ENNReal.ofReal (c.rate p j - 2 * ε) ≤ pointerPrep p q₀ δ (protocol.outcomeSector j)
  /-- The upper Born bound `rⱼ + 2(N−1)ε`. -/
  born_upper : ∀ (p : LF4.CPN N) (q₀ : Pointer N) (j : Fin N),
    pointerPrep p q₀ δ (protocol.outcomeSector j)
      ≤ ENNReal.ofReal (c.rate p j + 2 * ((N : ℝ) - 1) * ε)
  /-- **The continuity and Liouville fields are about THIS protocol.** Added 2026-08-04
  (codebase audit): `jointly_continuous` and `liouville` are statements about the global
  maps `pointerRampedEvolve`/`pointerEvolve`, and nothing in the type previously tied them
  to `protocol`. That mattered because `MeasurementCapstone` exposes this closure
  existentially (`Nonempty`), which erases *which* protocol it is — so "the witness is
  jointly continuous" did not follow from the bundle. These two identifications close the
  gap: with them, the continuity and measure-preservation claims transfer to `protocol`. -/
  evolve_eq : ∀ (s : ℝ) (z : ℝ × PointerArena N N),
    pointerRampedEvolve c ε s z = protocol.evolve s z.1 z.2
  /-- The measurement stroke `Φ_{0→1}` of this protocol is the propagator `liouville`
  speaks about. -/
  stroke_eq : protocol.evolve 0 1 = pointerEvolve c ε

/-- ★★ **The smooth-horn closure is inhabited**, for every context with continuous rates
and every `0 < ε`, `0 < δ ≤ 1/2`. -/
noncomputable def smoothWitnessClosure (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) {ε δ : ℝ} (hε : 0 < ε) (hδpos : 0 < δ)
    (hδ : δ ≤ 1 / 2) : SmoothWitnessClosure c ε δ where
  protocol := pointerProtocol c hc ε hδ
  jointly_continuous s := continuous_pointerRampedEvolve c hc ε s
  liouville p₀ q₀ := pointerEvolve_measurePreserving c hc ε p₀ q₀
  ready_pos p₀ q₀ := arenaReady_pos p₀ q₀ hδpos
  correlates := pointerProtocol_correlatesOn c hc hε hδ
  invariant := pointerProtocol_pointerInvariantOn c hc ε hδ
  evolve_eq s z := pointerRampedEvolve_eq_protocol c hc ε hδ s z
  stroke_eq := pointerProtocol_evolve_stroke c hc ε hδ
  born_lower p q₀ j := pointer_born_lower c hc hε hδpos hδ p q₀ j
  born_upper p q₀ j := pointer_born_upper c hc hε hδpos hδ p q₀ j

/-- The closure on the **canonical context** — the Fubini–Study moment map, whose rates are
continuous by `LF4.continuous_momentMap`. -/
noncomputable def smoothWitnessClosureCanonical {ε δ : ℝ} (hε : 0 < ε) (hδpos : 0 < δ)
    (hδ : δ ≤ 1 / 2) : SmoothWitnessClosure (momentContext N) ε δ :=
  smoothWitnessClosure (momentContext N) (fun j => LF4.continuous_momentMap j) hε hδpos hδ

end CSD.RecordLayer
