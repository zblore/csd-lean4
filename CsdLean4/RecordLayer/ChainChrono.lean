/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.ChronoPrecedes
public import CsdLean4.RecordLayer.ClockCalibration
public import CsdLean4.RecordLayer.ChainClocks

/-!
# The chain and the exchange under chronological precedence: where the inflation comes from

**Category:** 7-SigmaLayer (the record layer — the witness half of #192).
BACKLOG #192 (out of #39; the second of #191–#197).

`CV/ChronoPrecedes.lean` bounds the longest chrono chain by the elapsed periods. This file runs the
two inflated witnesses of the programme through it and shows exactly which steps the inflation used.

* **The chain of #190.** ★ `not_chronoPrecedes_pairEvent` — the inserted step
  `pairEvent k → siteEvent (k+1)` of `two_mul_le_causalDist` is **not** a chrono step: both events sit
  at period `k + 1`. The site steps are (`siteEvent_strictChrono_succ`), so
  ★★ `chronoDist_siteEvents` — **the chrono distance from the emission to the reception at site `m` is
  exactly `m`**, the clock's elapsed ticks under `T = τ_hop` (#190), while ★ `chronoDist_lt_causalDist`
  — the causal distance is strictly larger for every `m ≥ 1`; `two_mul_le_causalDist` is untouched.
* **The exchange of #186/#188.** `exchange_chrono_chain` — `emission ⪯ reception ⪯ return` are chrono
  steps; ★ `not_chronoPrecedes_bothSites_reception` — the inserted `bothSitesAtOne → reception` step of
  `three_le_causalDist` is not; ★★ `chronoDist_exchange = 2` — the chrono distance from emission to
  return is the two elapsed ticks (`elapsed_ticks_emission_return`), against `three_le_causalDist`.
* ★★★ `chain_chrono` — the package.

## What this says and does not say

The longest-chain quantity `causalDist` counts strict steps of **permitted influence**, and a region
inclusion at an unchanged period is such a step; so it measures the depth of the influence order, not
time. The clock measures ticks of a calibrated register. On these two witnesses the chrono distance
coincides with the clock, because each hop is one period and the schedule gives one hop per period; the
general statement is the inequality `chronoDist_le_elapsed`, and the coincidence is the witness's.
`CausalPrecedes` and both inflation theorems keep their names and their content.

References: `specs/BACKLOG.md` #192, #188, #190, #39; `CV/ChronoPrecedes.lean`,
`RecordLayer/ChainClocks.lean` (`siteEvent`, `pairEvent`, `two_mul_le_causalDist`),
`RecordLayer/ClockCalibration.lean` (`bothSitesAtOne`, `three_le_causalDist`).
-/

@[expose] public section

open MeasureTheory Set CSD.CV

open scoped SetRel

namespace CSD.RecordLayer

variable {n K : ℕ}

/-! ### The chain -/

theorem siteEvent_time_lt_succ (k : Fin n) :
    (siteEvent (n := n) (Fin.castSucc k)).time < (siteEvent (Fin.succ k)).time := by
  show (Fin.castSucc k).val < (Fin.succ k).val
  rw [Fin.val_castSucc, Fin.val_succ]
  exact Nat.lt_succ_self _

/-- Consecutive site events are chrono-ordered. -/
theorem siteEvent_chrono_succ (k : Fin n) :
    ChronoPrecedes (pathGraph n) (siteEvent (Fin.castSucc k)) (siteEvent (Fin.succ k)) :=
  chronoPrecedes_of_causalPrecedes_of_lt (siteEvent_precedes_succ k) (siteEvent_time_lt_succ k)

/-- A site step is a strict chrono step. -/
theorem siteEvent_strictChrono_succ (k : Fin n) :
    siteEvent (Fin.castSucc k) ~[strictChrono (pathGraph n)] siteEvent (Fin.succ k) :=
  strictChrono_of_causalPrecedes_of_lt (siteEvent_precedes_succ k) (siteEvent_time_lt_succ k)

/-- The emission chrono-precedes every site event. -/
theorem siteEvent_zero_chrono (j : Fin (n + 1)) :
    ChronoPrecedes (pathGraph n) (siteEvent 0) (siteEvent j) := by
  by_cases hj : j = 0
  · subst hj
    exact chronoPrecedes_refl _ _
  · refine chronoPrecedes_of_causalPrecedes_of_lt (siteEvent_zero_precedes j) ?_
    show (0 : Fin (n + 1)).val < j.val
    rw [Fin.val_zero]
    exact Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))

/-- ★ **The inserted step of the inflation is not a chrono step**: `pairEvent k` and
`siteEvent (k+1)` sit at the same period `k + 1`, so the region inclusion that
`two_mul_le_causalDist` counts has no elapsed period. -/
theorem not_chronoPrecedes_pairEvent (k : Fin n) :
    ¬ ChronoPrecedes (pathGraph n) (pairEvent k) (siteEvent (Fin.succ k)) :=
  not_chronoPrecedes_of_time_eq (by show k.val + 1 = (Fin.succ k).val; rw [Fin.val_succ])
    (pairEvent_ne_siteEvent k)

/-- The site chain gives `chronoDist ≥ m`. -/
theorem le_chronoDist_siteEvents :
    ∀ m (hm : m ≤ n),
      m ≤ chronoDist (pathGraph n) (siteEvent 0) (siteEvent ⟨m, Nat.lt_succ_of_le hm⟩) := by
  intro m
  induction m with
  | zero => intro _; exact Nat.zero_le _
  | succ m ih =>
      intro hm
      have hlt : m < n := hm
      have hcast : (⟨m, Nat.lt_succ_of_le (Nat.le_of_lt hlt)⟩ : Fin (n + 1))
          = Fin.castSucc ⟨m, hlt⟩ := rfl
      have hsucc : (⟨m + 1, Nat.lt_succ_of_le hm⟩ : Fin (n + 1)) = Fin.succ ⟨m, hlt⟩ := rfl
      have h1 := ih (Nat.le_of_lt hlt)
      rw [hcast] at h1
      have h2 := chronoDist_pos_iff.mpr
        ⟨siteEvent_chrono_succ (⟨m, hlt⟩ : Fin n), siteEvent_ne_succ ⟨m, hlt⟩⟩
      have h3 := chronoDist_add_le (siteEvent_zero_chrono (Fin.castSucc ⟨m, hlt⟩))
        (siteEvent_chrono_succ ⟨m, hlt⟩)
      rw [hsucc]
      omega

/-- ★★ **The chrono distance from the emission to the reception at site `m` is exactly `m`** — the
elapsed periods, which under `T = τ_hop` are the clock's elapsed ticks (#190). -/
theorem chronoDist_siteEvents (m : ℕ) (hm : m ≤ n) :
    chronoDist (pathGraph n) (siteEvent 0) (siteEvent ⟨m, Nat.lt_succ_of_le hm⟩) = m := by
  refine le_antisymm ?_ (le_chronoDist_siteEvents m hm)
  have h := chronoDist_le_elapsed (pathGraph n) (siteEvent 0) (siteEvent ⟨m, Nat.lt_succ_of_le hm⟩)
  simpa [siteEvent] using h

/-- ★ **The causal distance is strictly larger than the chrono distance** for every site `m ≥ 1`: the
inflation of `two_mul_le_causalDist` is entirely in same-period steps. -/
theorem chronoDist_lt_causalDist {m : ℕ} (hm : m ≤ n) (hm1 : 1 ≤ m) :
    chronoDist (pathGraph n) (siteEvent 0) (siteEvent ⟨m, Nat.lt_succ_of_le hm⟩)
      < causalDist (pathGraph n) (siteEvent 0) (siteEvent ⟨m, Nat.lt_succ_of_le hm⟩) := by
  rw [chronoDist_siteEvents m hm]
  exact clock_time_lt_causalDist hm hm1

/-! ### The exchange -/

/-- The events of the exchange under the calibration `T = τ_hop`: emission, reception, return. -/
theorem exchange_causal_steps :
    CausalPrecedes hopGraph (⟨{0}, 0⟩ : RecordEvent 2) ⟨{1}, 1⟩
      ∧ CausalPrecedes hopGraph (⟨{1}, 1⟩ : RecordEvent 2) ⟨{0}, 2⟩ := by
  refine ⟨⟨Nat.zero_le _, ?_⟩, ⟨by norm_num, ?_⟩⟩
  · show ({1} : Finset (Fin 2)) ⊆ graphBall hopGraph {0} (1 - 0)
    decide
  · show ({0} : Finset (Fin 2)) ⊆ graphBall hopGraph {1} (2 - 1)
    decide

/-- **The exchange's chain is a chrono chain**: each step moves one period. -/
theorem exchange_chrono_chain :
    ChronoPrecedes hopGraph (⟨{0}, 0⟩ : RecordEvent 2) ⟨{1}, 1⟩
      ∧ ChronoPrecedes hopGraph (⟨{1}, 1⟩ : RecordEvent 2) ⟨{0}, 2⟩
      ∧ ChronoPrecedes hopGraph (⟨{0}, 0⟩ : RecordEvent 2) ⟨{0}, 2⟩ := by
  obtain ⟨h01, h12⟩ := exchange_causal_steps
  have c01 := chronoPrecedes_of_causalPrecedes_of_lt h01 (by decide)
  have c12 := chronoPrecedes_of_causalPrecedes_of_lt h12 (by decide)
  exact ⟨c01, c12, chronoPrecedes_trans c01 c12⟩

/-- ★ **The inserted step of #188's inflation is not a chrono step**: `bothSitesAtOne` and the
reception both sit at period `1`. -/
theorem not_chronoPrecedes_bothSites_reception :
    ¬ ChronoPrecedes hopGraph bothSitesAtOne (⟨{1}, 1⟩ : RecordEvent 2) :=
  not_chronoPrecedes_of_time_eq rfl bothSites_ne_reception

/-- ★★ **The chrono distance from emission to return is the two elapsed ticks**, against
`three_le_causalDist`. -/
theorem chronoDist_exchange :
    chronoDist hopGraph (⟨{0}, 0⟩ : RecordEvent 2) ⟨{0}, 2⟩ = 2 := by
  obtain ⟨c01, c12, _⟩ := exchange_chrono_chain
  refine le_antisymm (chronoDist_le_elapsed _ _ _) ?_
  have h1 := chronoDist_pos_iff.mpr ⟨c01, emission_ne_reception⟩
  have h2 := chronoDist_pos_iff.mpr ⟨c12, reception_ne_return⟩
  have h3 := chronoDist_add_le c01 c12
  omega

/-- The chrono distance of the exchange is strictly below its causal distance. -/
theorem chronoDist_exchange_lt_causalDist {J ħ T : ℝ} (hJ : 0 < J) (hħ : 0 < ħ)
    (hT : T = hopTime J ħ) (hK : 2 ≤ K) {x : XArena K} (hx : x ∈ XReady K) (b : Fin 2) :
    chronoDist hopGraph (eventOf J ħ T x (emission b)) (eventOf J ħ T x (returnOcc J ħ b))
      < causalDist hopGraph (eventOf J ħ T x (emission b)) (eventOf J ħ T x (returnOcc J ħ b)) := by
  have h3 := three_le_causalDist hJ hħ hT hK hx b
  rw [eventOf_emission hJ hħ hT (by omega) hx b, eventOf_return hJ hħ hT hK hx b] at h3 ⊢
  rw [chronoDist_exchange]
  omega

/-! ### The package -/

/-- ★★★ **Where the inflation comes from.** On the path graph the chrono distance from the emission to
site `m` is exactly `m` and the inserted pair step is not a chrono step; on the exchange the chrono
distance from emission to return is `2` and the inserted both-sites step is not a chrono step; in both
cases the causal distance is strictly larger, and in general the chrono distance is bounded by the
elapsed periods and by the causal distance. -/
theorem chain_chrono :
    (∀ m (hm : m ≤ n),
        chronoDist (pathGraph n) (siteEvent 0) (siteEvent ⟨m, Nat.lt_succ_of_le hm⟩) = m)
      ∧ (∀ k : Fin n, ¬ ChronoPrecedes (pathGraph n) (pairEvent k) (siteEvent (Fin.succ k)))
      ∧ (∀ m (hm : m ≤ n), 1 ≤ m →
          chronoDist (pathGraph n) (siteEvent 0) (siteEvent ⟨m, Nat.lt_succ_of_le hm⟩)
            < causalDist (pathGraph n) (siteEvent 0) (siteEvent ⟨m, Nat.lt_succ_of_le hm⟩))
      ∧ chronoDist hopGraph (⟨{0}, 0⟩ : RecordEvent 2) ⟨{0}, 2⟩ = 2
      ∧ ¬ ChronoPrecedes hopGraph bothSitesAtOne (⟨{1}, 1⟩ : RecordEvent 2)
      ∧ (∀ (E : Finset (Fin K × Fin K)) (e₁ e₂ : RecordEvent K),
          chronoDist E e₁ e₂ ≤ e₂.time - e₁.time ∧ chronoDist E e₁ e₂ ≤ causalDist E e₁ e₂) :=
  ⟨chronoDist_siteEvents, not_chronoPrecedes_pairEvent, fun _ hm hm1 => chronoDist_lt_causalDist hm hm1,
    chronoDist_exchange, not_chronoPrecedes_bothSites_reception,
    fun E e₁ e₂ => ⟨chronoDist_le_elapsed E e₁ e₂, chronoDist_le_causalDist E e₁ e₂⟩⟩

end CSD.RecordLayer

end
