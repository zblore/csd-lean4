/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedRadarEvents
public import CsdLean4.RecordLayer.UnifiedRadarMacrostate

/-!
# The radar's five events are the five coordinates of its macrostate

**Category:** 7-SigmaLayer. BACKLOG #442, third brick (Task 4 of the author's plan "Unified
records, quantum measurement and emergent spacetime", the causal bridge;
`specs/unified-records-spacetime-task-plans.md` §2, the plan's *radar_macrostate_causal*).

`RecordLayer/UnifiedRadarEvents.lean` gives each of the radar's five readings a region of the
ring and a flow time. `RecordLayer/UnifiedRadarMacrostate.lean` makes the five capped counts
of the run a macroscopic projection, for any flow times in the five reading windows. Here the
two are joined: the projection is taken at the times of the five events.

* `radarCoord`, `radarCoord_bijective` — coordinate `j` of the macrostate (pointer `j` of the
  run) is the reading `radarCoord j`: emission, return, the meeting on the moving clock, the
  relay, the meeting on the clock at rest; the correspondence is one to one;
* `radarEventTime_mem_window` — the time of each event is in its reading window;
* ★★★ `csd_radar_macrostate_events` — **for the family of `csd_radar_macrostate`, with the
  five readings taken at the times of the five events: there are five counts, a cap and a
  string such that the cell of the macroscopic projection at that string is the compatible
  region of the history of the five recorded facts, has non-zero measure, and its counts
  satisfy the Lorentz comparisons.**

## Honest scope

⚠️ **An instance of `csd_radar_macrostate` at five chosen times.** Nothing new is proved
about the run. What is new is that the macrostate's coordinates are indexed by events that
carry a region and a time, so the relations of `UnifiedRadarEvents.lean` are relations
between the coordinates.

⚠️ **The regions play no part in the macrostate.** The projection reads the five pointers;
it does not read the sites of the ring. That a reading is "at" its region is the assignment
of `radarEvent`, not a consequence of this theorem.

⚠️ **No relation on macrostates.** The graph's relations are between the five coordinates of
one macrostate. No order or causal relation between two macrostates is defined.

⚠️ **The cell is not named** and its measure has no value, as in `csd_radar_macrostate`.

References: `specs/BACKLOG.md` #442, #439; `specs/unified-record-spacetime-plan.md` (UD-223,
UD-248, UD-249); `specs/unified-records-spacetime-task-plans.md` (§2);
`RecordLayer/UnifiedRadarEvents.lean` (`RadarReading`, `radarEvent`, `radarEventTime`);
`RecordLayer/UnifiedRadarMacrostate.lean` (`tickMacro`, `csd_radar_macrostate`);
`RecordLayer/UnifiedWallIntervals.lean` (`radar_gate_times`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.SigmaLayer CSD.LF4 CSD.CV MeasureTheory Set

namespace CSD.RecordLayer

/-- **The reading of each coordinate of the macrostate**: pointer `0` reads the emission,
`1` the return, `2` the meeting on the moving clock, `3` the relay, `4` the meeting on the
clock at rest. -/
def radarCoord : Fin 5 → RadarReading :=
  ![.emission, .ret, .meetMoving, .relay, .meetRest]

/-- The five coordinates are the five readings, one to one. -/
theorem radarCoord_bijective : Function.Bijective radarCoord := by
  constructor
  · intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by simp [radarCoord])
  · intro r
    cases r
    · exact ⟨0, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨4, rfl⟩

/-- **The time of each event is in its reading window.** -/
theorem radarEventTime_mem_window {k : ℕ} (hk : 100 ≤ k) (M : ℕ) :
    famTb k ≤ famT3 k ∧ famT4 k ≤ famT5 k ∧ famTbM k M ≤ famTcM k M
      ∧ famTbR k M ≤ famTcR k M := by
  obtain ⟨c_b₂, c_21, c_2a, c_fast, c_τ, c_δ, c_δπ, c_start, c_η, c_lev⟩ :=
    radar_family_gate_conditions hk M
  obtain ⟨⟨-, -, o3, -, o5⟩, ⟨-, -, p3⟩, ⟨-, -, q3⟩, -⟩ :=
    radar_gate_times c_b₂ c_21 c_2a c_fast c_τ c_δ c_δπ c_start c_η c_lev
  exact ⟨o3, o5, q3, p3⟩

set_option synthInstance.maxSize 4096 in
/-- ★★★ **The radar's macrostate, read at the times of its five events.** For `k ≥ 100` and a
ring with an even number `M + 1 = 2H` of sites, `M ≥ 210000 N³`: there are strengths such
that for every labelling and every reference point of the measure there are five counts, a
cap `B` and a string `v` of capped counts for which

* the cell at `v` of the macroscopic projection whose coordinate `j` is the capped count of
  pointer `j` at the time of the event `radarEvent k M (radarCoord j)` is the compatible
  region of the history of the five recorded facts at those times;
* that cell has non-zero `μ_FS ⊗ vol⁵` measure; and
* the counts satisfy the comparisons of `RadarCountBounds` within `152 K/k` and `53 K/k`. -/
theorem csd_radar_macrostate_events {k : ℕ} (hk : 100 ≤ k) {M H : ℕ}
    (hM : 210000 * wallN k ^ 2 * wallN k ≤ M) (hH : M + 1 = 2 * H) :
    ∃ gA gB : ℝ, 0 < gA ∧ 0 < gB
      ∧ ∀ (D : ℕ) (e : (ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
          × ((ZMod (M + 1) × Fin 2) × Fin 2)) ≃ Fin (D + 1)) (p₀ : CPN (D + 1)),
        ∃ (Ne Nr Nμ Nρ Nm B : ℕ) (v : Fin 5 → Fin (B + 2)),
          ((wallReadout (wallN k) (wallN k) M (wallMu k) (wallGap k) (3 * wallDelta k)
              gA gB e p₀).tickMacro
                (fun j : Fin 5 => (j, (radarEvent k M (radarCoord j)).time)) B).toFun ⁻¹' {v}
            = compatibleSet
              (wallReadout (wallN k) (wallN k) M (wallMu k) (wallGap k) (3 * wallDelta k)
                gA gB e p₀).semantics
              (List.ofFn fun j : Fin 5 => TickReadout.startFact j
                (radarEvent k M (radarCoord j)).time (![Ne, Nr, Nμ, Nρ, Nm] j))
          ∧ pentaMuL p₀
              (((wallReadout (wallN k) (wallN k) M (wallMu k) (wallGap k) (3 * wallDelta k)
                gA gB e p₀).tickMacro
                  (fun j : Fin 5 => (j, (radarEvent k M (radarCoord j)).time)) B).toFun
                ⁻¹' {v}) ≠ 0
          ∧ RadarCountBounds (ringRate (1200 * wallN k * wallN k) M 0 (wallGap k))
              (vRel 1 1 (1 / 2)) (152 * (wallK k / k)) (152 * (wallK k / k))
              (Real.pi * wallK k - Real.pi * wallK k / vRel 1 1 (1 / 2))
              (53 * (wallK k / k)) Ne Nr Nμ Nρ Nm := by
  obtain ⟨gA, gB, hA, hB, hall⟩ := csd_radar_macrostate hk hM hH
  obtain ⟨w1, w2, w3, w4⟩ := radarEventTime_mem_window hk M
  refine ⟨gA, gB, hA, hB, fun D e p₀ => ?_⟩
  obtain ⟨Ne, Nr, Nμ, Nρ, Nm, B, v, h1, h2, h3⟩ := hall D e p₀ (famTb k) le_rfl w1
    (famT4 k) le_rfl w2 (famTbM k M) le_rfl w3 (famTbR k M) le_rfl w4 (famTbM k M) le_rfl w3
  have hctx : (fun j : Fin 5 => (j, ![famTb k, famT4 k, famTbM k M, famTbR k M, famTbM k M] j))
      = fun j : Fin 5 => (j, (radarEvent k M (radarCoord j)).time) := by
    funext j
    fin_cases j <;> rfl
  have hlist : radarHistory (famTb k) (famT4 k) (famTbM k M) (famTbR k M) (famTbM k M)
        Ne Nr Nμ Nρ Nm
      = List.ofFn fun j : Fin 5 => TickReadout.startFact j
          (radarEvent k M (radarCoord j)).time (![Ne, Nr, Nμ, Nρ, Nm] j) := rfl
  rw [hctx] at h1 h2
  rw [hlist] at h1
  exact ⟨Ne, Nr, Nμ, Nρ, Nm, B, v, h1, h2, h3⟩

end CSD.RecordLayer

end
