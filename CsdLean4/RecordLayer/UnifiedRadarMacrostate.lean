/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedRadarPreparation
public import CsdLean4.RecordLayer.MacroProjection

/-!
# The macroscopic projection of tick records

**Category:** 7-SigmaLayer. BACKLOG #439, first brick (Task 3 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream R; obligation
UO-25, item (3)).

`RecordLayer/MacroProjection.lean` (#99) defines a macroscopic coordinate as a measurable map
to a finite set and asks that the record events factor through it.
`RecordLayer/RecordMacrostate.lean` (#102) builds one for the cell-law records of the Kähler
arena. Here the same frame is instantiated for tick records of any `TickReadout`, without a
new definition of a macrostate.

* `TickReadout.countEvent`, `countEvent_eq_event`, `measurableSet_countEvent` — the starts
  whose pointer `i` has counted `N` at `T`; it is the event of the recorded fact;
* `tickCode`, `tickCode_eq_castSucc_iff`, `tickCode_eq_last_iff`, `measurable_tickCode` — the
  count capped at `B`, as a value of `Fin (B + 2)`: the count if it exists and is at most
  `B`, the last value otherwise;
* ★★ `tickMacro` — for a finite indexed family of readings (pointer, time), the capped counts
  of all of them, as a `MacroProjection`;
* ★★ `countEvent_eq_preimage`, `factorsThrough_countEvent` — every record event of the family
  factors through it;
* ★★★ `compatibleSet_eq_preimage_singleton` — **a record history of the family is one
  macrostate**: the compatible region of the history that records a count at every reading
  is exactly the cell of the projection at that string of counts;
* ★★ `map_tickMacro_singleton` (2026-11-19) — the pushed-forward measure of a string is the
  arena measure of its history's compatible region;
* ★★★ `csd_radar_macrostate` (2026-11-19) — the radar's instance: for the family of
  `csd_radar_history_preparation` there are five counts, a cap and a string such that the cell
  of the projection of the five readings is the compatible region of the radar's history, has
  non-zero `μ_FS ⊗ vol⁵` measure, and its counts satisfy the Lorentz comparisons.

## Honest scope

⚠️ **The construction, not the physics.** A coordinate is macroscopic when its cells are
stable under the flow and shared by overwhelmingly many microstates. Neither is shown here.
The cells are defined from the flow up to the reading times, so they are fixed at the
start; nothing says a later reading returns the same string.

⚠️ **The radar's cell is not named.** `csd_radar_macrostate` inherits the counts of
`csd_radar_history_preparation`, which exist by a covering argument; the cap is the largest of
them. Non-zero measure, with no value.

⚠️ **The cap `B` is a parameter.** Counts above `B`, and starts with no count, share the last
value. No canonical `B` or family of readings is claimed.

⚠️ **A set of labels.** No order, geometry or causal relation on the macrostates. The law of
the pushed-forward measure is identified with the measure of compatible regions
(`map_tickMacro_singleton`) and is not computed.

References: `specs/BACKLOG.md` #439, ~~#438~~, ~~#436~~, ~~#99~~, ~~#102~~;
`specs/unified-record-spacetime-plan.md` (UO-25, UD-208, UD-219, UD-223);
`RecordLayer/MacroProjection.lean` (`MacroProjection`, `FactorsThrough`);
`RecordLayer/RecordMacrostate.lean` (`recordMacro`, `outcomeCode`);
`RecordLayer/UnifiedRecordHistoryBridge.lean` (`TickReadout`, `startFact`,
`mem_event_startFact`); `RecordLayer/UnifiedDiracClockTicks.lean` (`IsTickCount.unique`);
`specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.SigmaLayer MeasureTheory Set

namespace CSD.RecordLayer

universe u w

variable {X : Type w} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

namespace TickReadout

variable {D : ConstraintDynamics X} {ι : Type u} (A : TickReadout D ι)

/-- **The starts whose pointer `i` has counted `N` at the time `T`.** -/
def countEvent (i : ι) (T : ℝ) (N : ℕ) : Set X :=
  {x | IsTickCount (A.rest i) (A.disp i) (fun s => D.flow s x) T N}

theorem countEvent_eq_event (i : ι) (T : ℝ) (N : ℕ) :
    A.countEvent i T N = A.semantics.event (startFact i T N) := by
  ext x
  exact (A.mem_event_startFact i T N x).symm

theorem measurableSet_countEvent (i : ι) (T : ℝ) (N : ℕ) :
    MeasurableSet (A.countEvent i T N) := by
  rw [countEvent_eq_event]
  exact A.semantics.measurable_event _

open Classical in
/-- **The count of pointer `i` at `T`, capped at `B`**, as a value of a finite type: the
count if it exists and is at most `B`, and the last value otherwise. -/
def tickCode (B : ℕ) (i : ι) (T : ℝ) (x : X) : Fin (B + 2) :=
  if h : ∃ N : Fin (B + 1), x ∈ A.countEvent i T N then Fin.castSucc h.choose
  else Fin.last (B + 1)

omit [OpensMeasurableSpace X] in
theorem tickCode_eq_castSucc_iff (B : ℕ) (i : ι) (T : ℝ) (x : X) (N : Fin (B + 1)) :
    A.tickCode B i T x = Fin.castSucc N ↔ x ∈ A.countEvent i T N := by
  classical
  constructor
  · intro h
    unfold tickCode at h
    split_ifs at h with hex
    · rw [← Fin.castSucc_injective _ h]
      exact hex.choose_spec
    · exact absurd h.symm (Fin.castSucc_lt_last N).ne
  · intro hx
    have hex : ∃ N : Fin (B + 1), x ∈ A.countEvent i T N := ⟨N, hx⟩
    simp only [tickCode, hex, ↓reduceDIte]
    congr 1
    exact Fin.ext (IsTickCount.unique hex.choose_spec hx)

omit [OpensMeasurableSpace X] in
theorem tickCode_eq_last_iff (B : ℕ) (i : ι) (T : ℝ) (x : X) :
    A.tickCode B i T x = Fin.last (B + 1) ↔ x ∉ ⋃ N : Fin (B + 1), A.countEvent i T N := by
  classical
  rw [Set.mem_iUnion]
  constructor
  · intro h hex
    simp only [tickCode, hex, ↓reduceDIte] at h
    exact (Fin.castSucc_lt_last _).ne h
  · intro h
    simp only [tickCode, h, ↓reduceDIte]

theorem measurable_tickCode (B : ℕ) (i : ι) (T : ℝ) : Measurable (A.tickCode B i T) := by
  refine measurable_to_countable' fun v => ?_
  refine Fin.lastCases ?_ (fun N => ?_) v
  · have e : A.tickCode B i T ⁻¹' {Fin.last (B + 1)}
        = (⋃ N : Fin (B + 1), A.countEvent i T N)ᶜ := by
      ext x
      exact A.tickCode_eq_last_iff B i T x
    rw [e]
    exact (MeasurableSet.iUnion fun N : Fin (B + 1) =>
      A.measurableSet_countEvent i T N).compl
  · have e : A.tickCode B i T ⁻¹' {Fin.castSucc N} = A.countEvent i T N := by
      ext x
      exact A.tickCode_eq_castSucc_iff B i T x N
    rw [e]
    exact A.measurableSet_countEvent i T N

/-- ★★ **The macroscopic projection of a finite family of readings**: for readings
`ctx j = (pointer, time)`, the capped counts of all of them, as a `MacroProjection` onto a
finite set. -/
def tickMacro {k : ℕ} (ctx : Fin k → ι × ℝ) (B : ℕ) : MacroProjection X (Fin k → Fin (B + 2)) where
  toFun x := fun j => A.tickCode B (ctx j).1 (ctx j).2 x
  measurable_toFun := measurable_pi_iff.2 fun j => A.measurable_tickCode B (ctx j).1 (ctx j).2

/-- ★★ **Every record event of the family factors through the projection.** -/
theorem countEvent_eq_preimage {k : ℕ} (ctx : Fin k → ι × ℝ) (B : ℕ) (j : Fin k)
    (N : Fin (B + 1)) :
    A.countEvent (ctx j).1 (ctx j).2 N
      = (A.tickMacro ctx B).toFun ⁻¹' {v : Fin k → Fin (B + 2) | v j = Fin.castSucc N} := by
  ext x
  exact (A.tickCode_eq_castSucc_iff B (ctx j).1 (ctx j).2 x N).symm

theorem factorsThrough_countEvent {k : ℕ} (ctx : Fin k → ι × ℝ) (B : ℕ) (j : Fin k)
    (N : Fin (B + 1)) :
    FactorsThrough (A.tickMacro ctx B).toFun (A.countEvent (ctx j).1 (ctx j).2 N) :=
  ⟨_, A.countEvent_eq_preimage ctx B j N⟩

/-- ★★★ **A record history of the family is one macrostate.** For counts `c j ≤ B`, the
compatible region of the history that records the count `c j` at every reading `ctx j` is
the cell of the macroscopic projection at the string `c`. -/
theorem compatibleSet_eq_preimage_singleton {k : ℕ} (ctx : Fin k → ι × ℝ) (B : ℕ)
    (c : Fin k → Fin (B + 1)) :
    compatibleSet A.semantics
        (List.ofFn fun j => startFact (ctx j).1 (ctx j).2 (c j))
      = (A.tickMacro ctx B).toFun ⁻¹' {fun j => Fin.castSucc (c j)} := by
  ext x
  rw [mem_compatibleSet, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    funext j
    refine (A.tickCode_eq_castSucc_iff B (ctx j).1 (ctx j).2 x (c j)).2 ?_
    rw [countEvent_eq_event]
    exact h _ (List.mem_ofFn.2 ⟨j, rfl⟩)
  · intro h f hf
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hf
    rw [← countEvent_eq_event]
    exact (A.tickCode_eq_castSucc_iff B (ctx j).1 (ctx j).2 x (c j)).1 (congrFun h j)

/-- ★★ **The macroscopic law of a string is the measure of its history's compatible region.**
For counts `c j ≤ B`, the measure pushed forward by the macroscopic projection gives the
string `c` the arena measure of the compatible region of the history that records `c j` at
every reading. -/
theorem map_tickMacro_singleton {k : ℕ} (ctx : Fin k → ι × ℝ) (B : ℕ)
    (c : Fin k → Fin (B + 1)) :
    Measure.map (A.tickMacro ctx B).toFun (D.muL : Measure X) {fun j => Fin.castSucc (c j)}
      = (D.muL : Measure X) (compatibleSet A.semantics
          (List.ofFn fun j => startFact (ctx j).1 (ctx j).2 (c j))) := by
  rw [Measure.map_apply (A.tickMacro ctx B).measurable_toFun (measurableSet_singleton _),
    compatibleSet_eq_preimage_singleton]

end TickReadout

/-! ### The radar's macrostate -/

section Family

open CSD.LF4 CSD.CV

set_option synthInstance.maxSize 4096 in
/-- ★★★ **The radar's record history is a macrostate of non-zero measure.** For `k ≥ 100` and
a ring with an even number `M + 1 = 2H` of sites, `M ≥ 210000 N³`: there are strengths such
that for every labelling, every reference point of the measure and every choice of flow
times in the five reading windows there are five counts, a cap `B` and a string `v` of
capped counts for which

* the cell of the macroscopic projection of the five readings at `v` is the compatible
  region of the history of the five recorded facts;
* that cell has non-zero `μ_FS ⊗ vol⁵` measure; and
* the counts satisfy the comparisons of `RadarCountBounds` within `152 K/k` and `53 K/k`. -/
theorem csd_radar_macrostate {k : ℕ} (hk : 100 ≤ k) {M H : ℕ}
    (hM : 210000 * wallN k ^ 2 * wallN k ≤ M) (hH : M + 1 = 2 * H) :
    ∃ gA gB : ℝ, 0 < gA ∧ 0 < gB
      ∧ ∀ (D : ℕ) (e : (ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
          × ((ZMod (M + 1) × Fin 2) × Fin 2)) ≃ Fin (D + 1)) (p₀ : CPN (D + 1)),
        ∀ se, famTb k ≤ se → se ≤ famT3 k → ∀ sr, famT4 k ≤ sr → sr ≤ famT5 k →
        ∀ sμ, famTbM k M ≤ sμ → sμ ≤ famTcM k M → ∀ sρ, famTbR k M ≤ sρ → sρ ≤ famTcR k M →
        ∀ sm, famTbM k M ≤ sm → sm ≤ famTcM k M →
        ∃ (Ne Nr Nμ Nρ Nm B : ℕ) (v : Fin 5 → Fin (B + 2)),
          ((wallReadout (wallN k) (wallN k) M (wallMu k) (wallGap k) (3 * wallDelta k)
              gA gB e p₀).tickMacro (fun j : Fin 5 => (j, ![se, sr, sμ, sρ, sm] j)) B).toFun
              ⁻¹' {v}
            = compatibleSet
              (wallReadout (wallN k) (wallN k) M (wallMu k) (wallGap k) (3 * wallDelta k)
                gA gB e p₀).semantics (radarHistory se sr sμ sρ sm Ne Nr Nμ Nρ Nm)
          ∧ pentaMuL p₀
              (((wallReadout (wallN k) (wallN k) M (wallMu k) (wallGap k) (3 * wallDelta k)
                gA gB e p₀).tickMacro (fun j : Fin 5 => (j, ![se, sr, sμ, sρ, sm] j)) B).toFun
                ⁻¹' {v}) ≠ 0
          ∧ RadarCountBounds (ringRate (1200 * wallN k * wallN k) M 0 (wallGap k))
              (vRel 1 1 (1 / 2)) (152 * (wallK k / k)) (152 * (wallK k / k))
              (Real.pi * wallK k - Real.pi * wallK k / vRel 1 1 (1 / 2))
              (53 * (wallK k / k)) Ne Nr Nμ Nρ Nm := by
  obtain ⟨gA, gB, hA, hB, hall⟩ := csd_radar_history_preparation hk hM hH
  refine ⟨gA, gB, hA, hB, ?_⟩
  intro D e p₀ se h1 h2 sr h3 h4 sμ h5 h6 sρ h7 h8 sm h9 h10
  obtain ⟨Ne, Nr, Nμ, Nρ, Nm, HP, hH', hb⟩ :=
    hall D e p₀ se h1 h2 sr h3 h4 sμ h5 h6 sρ h7 h8 sm h9 h10
  have hcell := (wallReadout (wallN k) (wallN k) M (wallMu k) (wallGap k) (3 * wallDelta k)
      gA gB e p₀).compatibleSet_eq_preimage_singleton
    (fun j : Fin 5 => (j, ![se, sr, sμ, sρ, sm] j))
    (Finset.univ.sup ![Ne, Nr, Nμ, Nρ, Nm])
    (fun j => ⟨![Ne, Nr, Nμ, Nρ, Nm] j,
      Nat.lt_succ_of_le (Finset.le_sup (f := ![Ne, Nr, Nμ, Nρ, Nm]) (Finset.mem_univ j))⟩)
  have hlist : radarHistory se sr sμ sρ sm Ne Nr Nμ Nρ Nm
      = List.ofFn (fun j : Fin 5 => TickReadout.startFact j (![se, sr, sμ, sρ, sm] j)
          (![Ne, Nr, Nμ, Nρ, Nm] j)) := rfl
  have hnz := HP.nonzero_compatible
  rw [hH'] at hnz
  refine ⟨Ne, Nr, Nμ, Nρ, Nm, Finset.univ.sup ![Ne, Nr, Nμ, Nρ, Nm],
    (fun j => Fin.castSucc (⟨![Ne, Nr, Nμ, Nρ, Nm] j, Nat.lt_succ_of_le
      (Finset.le_sup (f := ![Ne, Nr, Nμ, Nρ, Nm]) (Finset.mem_univ j))⟩ :
        Fin (Finset.univ.sup ![Ne, Nr, Nμ, Nρ, Nm] + 1))), ?_, ?_, hb⟩
  · rw [hlist]
    exact hcell.symm
  · rw [← hcell]
    rw [hlist] at hnz
    exact hnz

end Family

end CSD.RecordLayer

end
