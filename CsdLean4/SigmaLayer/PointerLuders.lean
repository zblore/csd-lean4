/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.PointerBorn
public import CsdLean4.SigmaLayer.SwapWitness

/-!
# SigmaLayer/PointerLuders: the smooth stroke and the relocation on one arena (B3b, brick 1)

**Category:** dynamical measurement — `specs/BACKLOG.md` **B3b**, first brick.

## Why this module has to exist

The smooth witness **provably does not collapse**: `pointerEvolve_base_marginal_unchanged`
says the measurement stroke leaves every initial measure's sector marginal untouched. That
is a *feature* — records without back-reaction — but it means the smooth horn on its own
delivers records and Born and no state update. The update lives on the swap/join witnesses,
which are triggered by a **torus arc**.

Composing the two therefore needs an arena carrying the pointer *and* a bank, and a
relocation triggered by the **pointer's record region** rather than by a register arc. That
is what this brick builds.

## What is proved here

* `PointerLudersArena` — `(Σ × ℂℙ^N) × (bank of N slots)`: the smooth witness's arena with
  the swap witness's bank attached.
* `pointerIndex` — the readout, straight off the record regions. Well defined because
  distinct record regions are disjoint (`recordRegion_pairwiseDisjoint`).
* `pointerRelocate` — swap the system with bank slot `j` when the pointer displays `j`, and
  do nothing when it displays nothing. The pointer is never moved
  (`pointerRelocate_pointer`), so the record survives its own relocation — the property the
  torus-triggered version needed too.
* ★ `pointerBankSwap_measurePreserving` — the **slot swap** preserves the composed arena
  measure, by the same conjugation the torus version uses; that the register measure is
  Fubini–Study rather than Haar plays no part in the argument.
* `pointerLudersStroke` — the two-stroke composite (record, then relocate), defined.

~~⚠️ Deliberately **not** claimed here: measure preservation of `pointerRelocate`
*itself*.~~ **Discharged 2026-08-05** (`SigmaLayer/PointerLudersMarginal.lean`,
`pointerRelocate_measurePreserving`): exactly the predicted partition argument — the
`swapG` route with record cylinders in place of register arcs.

~~⚠️ **Honest scope — this is brick 1 of B3b, not B3b.**~~ **Brick 2 landed 2026-08-05**
(`SigmaLayer/PointerLudersMarginal.lean`): the conditioned post-measurement system marginal
is now a theorem (`pointer_luders_marginal`), so the smooth horn claims a Lüders update —
records (ε-Born) *and* collapse-as-relocation on one arena. **B3b is closed.** Nothing in
brick 2 weakens `pointerEvolve_base_marginal_unchanged`: the relocation is a *second*
stroke, so the first still does not collapse — that division of labour is now load-bearing
rather than aspirational.

## What brick 2 owed — delivered 2026-08-05

The conditioned post-measurement system marginal (`pointer_luders_marginal`, with the CSD
forms `pointer_luders_born`/`pointer_luders_born_prep`) and the piecewise invariance
(`pointerRelocate_measurePreserving`, plus the full-composite
`pointerLudersStroke_measurePreserving`). See `SigmaLayer/PointerLudersMarginal.lean`.

## References

`specs/BACKLOG.md` B3b; `SigmaLayer/PointerBorn.lean` (the smooth stroke and its arena);
`SigmaLayer/SwapWitness.lean` (`bankSwap`, `measurePreserving_bankSwap` — the torus-
triggered original this mirrors); `SigmaLayer/PointerGeneration.lean`
(`pointerEvolve_base_marginal_unchanged`, the theorem that makes this module necessary).
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory Matrix.UnitaryGroup

variable {N : ℕ} [NeZero N]

/-- The composed arena: the smooth witness's `(Σ × pointer)` with a bank of `N` slots. -/
abbrev PointerLudersArena (N : ℕ) : Type :=
  (LF4.KSigma N × Pointer N) × (Fin N → LF4.KSigma N)

/-- **The pointer readout**: which record region the pointer occupies, if any. Well defined
because distinct record regions are disjoint. -/
noncomputable def pointerIndex (q : Pointer N) : Option (Fin N) := by
  classical
  exact if h : ∃ j, q ∈ recordRegion j then some h.choose else none

omit [NeZero N] in
theorem pointerIndex_eq_some_of_mem {q : Pointer N} {j : Fin N} (hq : q ∈ recordRegion j) :
    pointerIndex q = some j := by
  classical
  have hex : ∃ j, q ∈ recordRegion j := ⟨j, hq⟩
  rw [pointerIndex, dif_pos hex]
  congr 1
  by_contra hne
  exact Set.disjoint_left.mp (recordRegion_pairwiseDisjoint (Ne.symm hne)) hq hex.choose_spec

/-- The slot swap on the composed arena: exchange the system with bank slot `j`, leaving the
pointer alone. -/
def pointerBankSwap (j : Fin N) (y : PointerLudersArena N) : PointerLudersArena N :=
  ((y.2 j, y.1.2), Function.update y.2 j y.1.1)

/-- **The record-triggered relocation**: if the pointer displays `j`, exchange the system
with bank slot `j`; otherwise do nothing. Triggered by the **pointer's record**, which is
what makes this composable with the smooth stroke. -/
noncomputable def pointerRelocate (y : PointerLudersArena N) : PointerLudersArena N :=
  match pointerIndex y.1.2 with
  | none => y
  | some j => pointerBankSwap j y

omit [NeZero N] in
/-- ★ **The relocation never moves the pointer** — so the record survives its own
relocation, exactly as in the torus-triggered version. -/
theorem pointerRelocate_pointer (y : PointerLudersArena N) :
    (pointerRelocate y).1.2 = y.1.2 := by
  unfold pointerRelocate
  rcases h : pointerIndex y.1.2 with _ | j <;> simp [pointerBankSwap]

omit [NeZero N] in
theorem pointerRelocate_of_record {y : PointerLudersArena N} {j : Fin N}
    (h : y.1.2 ∈ recordRegion j) : pointerRelocate y = pointerBankSwap j y := by
  unfold pointerRelocate
  rw [pointerIndex_eq_some_of_mem h]

/-- **The two-stroke composite**: run the smooth record stroke on the system-and-pointer
factor, then relocate against the record it created. This is the map whose conditioned
marginal brick 2 must compute; it is *defined* here so that the arena and the dynamics are
pinned down before the analysis. -/
noncomputable def pointerLudersStroke (c : ContextField N) (ε : ℝ) :
    PointerLudersArena N → PointerLudersArena N :=
  fun y => pointerRelocate (pointerEvolve c ε y.1, y.2)

omit [NeZero N] in
/-- The composite leaves the bank's *slot count* and the pointer's record intact: the record
that triggers the relocation is the one the stroke just created. -/
theorem pointerLudersStroke_pointer (c : ContextField N) (ε : ℝ)
    (y : PointerLudersArena N) :
    (pointerLudersStroke c ε y).1.2 = (pointerEvolve c ε y.1).2 :=
  pointerRelocate_pointer _

/-! ### The arena measure and its invariance -/

/-- The composed arena measure: system ⊗ pointer ⊗ calibrated bank. -/
noncomputable def pointerLudersMeasure (μs : Measure (LF4.KSigma N)) (q₀ : Pointer N) :
    Measure (PointerLudersArena N) :=
  (μs.prod (fubiniStudyMeasure q₀)).prod (Measure.pi fun _ : Fin N => μs)

instance (μs : Measure (LF4.KSigma N)) [IsProbabilityMeasure μs] (q₀ : Pointer N) :
    IsProbabilityMeasure (pointerLudersMeasure μs q₀) := by
  unfold pointerLudersMeasure
  infer_instance

omit [NeZero N] in
/-- ★ **The slot swap preserves the arena measure** — the same conjugation the torus
version uses (`measurePreserving_bankSwap`); that the register measure is Fubini–Study
rather than Haar plays no part in the argument. -/
theorem pointerBankSwap_measurePreserving (μs : Measure (LF4.KSigma N))
    [IsProbabilityMeasure μs] (q₀ : Pointer N) (j : Fin N) :
    MeasurePreserving (pointerBankSwap (N := N) j)
      (pointerLudersMeasure μs q₀) (pointerLudersMeasure μs q₀) := by
  unfold pointerLudersMeasure
  have hR := (measurePreserving_prodAssoc (fubiniStudyMeasure q₀) μs
      (Measure.pi fun _ : Fin N => μs)).comp
    ((Measure.measurePreserving_swap (μ := μs) (ν := fubiniStudyMeasure q₀)).prod
      (MeasurePreserving.id (Measure.pi fun _ : Fin N => μs)))
  have hmid := (MeasurePreserving.id (fubiniStudyMeasure q₀)).prod
    (measurePreserving_swapSlot μs j)
  have hL := ((measurePreserving_prodAssoc (fubiniStudyMeasure q₀) μs
      (Measure.pi fun _ : Fin N => μs)).symm).comp hmid
  have := (((Measure.measurePreserving_swap (μ := fubiniStudyMeasure q₀) (ν := μs)).prod
      (MeasurePreserving.id (Measure.pi fun _ : Fin N => μs))).comp hL).comp hR
  exact this

end CSD.RecordLayer
