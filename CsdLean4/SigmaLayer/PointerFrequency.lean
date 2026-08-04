/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.PointerBorn
public import CsdLean4.LF1.GeneralFrequency

/-!
# SigmaLayer/PointerFrequency: the `ε`-Born frequency layer

**Category:** dynamical measurement — `specs/BACKLOG.md` **B3a** (the small half of the
recorded "smooth-witness Lüders composition + `ε`-Born LLN" row).

The smooth horn proves a **single-shot** sandwich: the outcome sector of the
ready-conditioned preparation carries mass between `rⱼ − 2ε` and `rⱼ + 2(N−1)ε`
(`pointer_born_lower`/`pointer_born_upper`). What it did not say is what an *experimenter*
sees — that repeated independent trials produce these numbers as **frequencies**. The exact
horns have had that since LF1 (`freq_tendsto_of_iid`); the smooth horn did not.

★ `pointer_born_frequency` closes it: for i.i.d. trials of the smooth witness's
preparation, the relative frequency of outcome `j` converges almost surely, and its limit
lies in the `ε`-window

  `rⱼ − 2ε  ≤  lim  ≤  rⱼ + 2(N−1)ε`.

The proof is short because nothing new is needed: `freq_tendsto_of_iid` is already generic
over (measurable space, probability measure, measurable event), and the smooth witness
supplies all three — `pointerPrep` is a probability measure
(`isProbabilityMeasure_pointerPrep`), the outcome sector is measurable
(`outcomeSector_measurable`). The only real work is carrying the `ℝ≥0∞` sandwich across
`ENNReal.toReal`, which is safe because a probability measure's sector mass is finite.

⚠️ **Honest scope.** (i) The limit is bracketed, not pinned: that is the `ε`-horn's price,
and the bracket is exactly as wide as the single-shot sandwich. Sending `ε → 0` sharpens
the window but not within a fixed witness — each `ε` is a different propagator. (ii) The
independence hypothesis is the LLN's, taken in the same indicator form the corpus uses
everywhere (`freq_tendsto_of_iid`); no new probabilistic content is claimed. (iii) This is
about the *statistics* of repeated preparations, not about repeated measurement of one
system — sequential measurement on a single system is the swap/join witnesses' territory
(`csd_sequential_born`).

## References

`specs/BACKLOG.md` B3a; `LF1/GeneralFrequency.lean` (`freq_tendsto_of_iid`, the generic
strong law used unchanged); `SigmaLayer/PointerBorn.lean` (`pointerPrep`, the sandwich);
`SigmaLayer/JointFlowTransfer.lean` (A1, which transports the sandwich to joint flows —
and hence transports this too).
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory Filter Topology

variable {N : ℕ} [NeZero N]

/-- The sector mass of the smooth witness's preparation, as a real number. -/
noncomputable def pointerSectorProb (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) (ε : ℝ) {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (p : LF4.CPN N) (q₀ : Pointer N) (j : Fin N) : ℝ :=
  (pointerPrep p q₀ δ ((pointerProtocol c hc ε hδ).outcomeSector j)).toReal

/-- The `ε`-sandwich, transported to real numbers. Safe because `pointerPrep` is a
probability measure, so the sector mass is finite. -/
theorem pointerSectorProb_mem_window (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) {ε δ : ℝ} (hε : 0 < ε) (hδpos : 0 < δ)
    (hδ : δ ≤ 1 / 2) (p : LF4.CPN N) (q₀ : Pointer N) (j : Fin N) :
    c.rate p j - 2 * ε ≤ pointerSectorProb c hc ε hδ p q₀ j ∧
      pointerSectorProb c hc ε hδ p q₀ j ≤ c.rate p j + 2 * ((N : ℝ) - 1) * ε := by
  haveI := isProbabilityMeasure_pointerPrep p q₀ hδpos
  have hfin : pointerPrep p q₀ δ ((pointerProtocol c hc ε hδ).outcomeSector j) ≠ ⊤ :=
    measure_ne_top _ _
  constructor
  · have hlow := pointer_born_lower c hc hε hδpos hδ p q₀ j
    have := (ENNReal.ofReal_le_iff_le_toReal hfin).mp hlow
    exact this
  · have hup := pointer_born_upper c hc hε hδpos hδ p q₀ j
    have hNpos : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    have hBnn : 0 ≤ c.rate p j + 2 * ((N : ℝ) - 1) * ε := by
      have h1 : 0 ≤ c.rate p j := c.nonneg p j
      have h2 : 0 ≤ 2 * ((N : ℝ) - 1) * ε := by
        have hN1 : (0 : ℝ) ≤ (N : ℝ) - 1 := by linarith
        positivity
      linarith
    exact ENNReal.toReal_le_of_le_ofReal hBnn hup

/-- ★ **The `ε`-Born frequency layer.** For i.i.d. trials of the smooth witness's
preparation, the relative frequency of outcome `j` converges almost surely, and the limit
sits inside the single-shot `ε`-window. This is what an experimenter running the smooth
horn would actually measure. -/
theorem pointer_born_frequency (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) {ε δ : ℝ} (hε : 0 < ε) (hδpos : 0 < δ)
    (hδ : δ ≤ 1 / 2) (p : LF4.CPN N) (q₀ : Pointer N) (j : Fin N)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → PointerArena N N) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = pointerPrep p q₀ δ)
    (hindep : Pairwise (Function.onFun (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
      (fun n => Set.indicator
        (X n ⁻¹' (pointerProtocol c hc ε hδ).outcomeSector j) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator (X k ⁻¹' (pointerProtocol c hc ε hδ).outcomeSector j)
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop (nhds (pointerSectorProb c hc ε hδ p q₀ j)) :=
  CSD.LF1.freq_tendsto_of_iid hX hlaw
    ((pointerProtocol c hc ε hδ).outcomeSector_measurable j) hindep

end CSD.RecordLayer
