/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedGateTimes

/-!
# The seven gate intervals of the walled chain, from straight motion

**Category:** 7-SigmaLayer (the record layer). BACKLOG #424 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Task 4 of the research delivery
plan of 2026-11-16 (the event intervals, for the angles the wall states actually have). No
new assumption; real arithmetic only.

`tri_wall_radar_lorentz` (#423) takes seven conditions on predicted angles, each over an
interval of flow times. The predicted angles are linear in the flow time: the messenger's
is `a (t₀ + s)`, the two levels of the moving clock have `b₁ (−τ + s)` and `b₂ (−τ + s)`
(the clock is prepared at the packet time `−τ`), and the clock at rest is at the angle `π`.
This module proves all seven from finitely many inequalities between the rates and the ends
of the intervals.

**The geometry this forces.** The moving clock is prepared at a negative packet time, so at
the start of the run it is at the angle `−b τ`: before the wall at `0` and moving into it.
On the walled chain that is a carrier at the distance `b τ` from the wall, moving toward it.
The messenger is started at the mirror place, the angle `+b₁ τ`, moving away from the wall
(`a t₀ = b₁ τ`). So the emission is a coincidence with the clock's *mirror image*, and the
clock is reflected at the wall at the flow time `τ` before it sets out for the other wall.
A messenger started at the clock's own angle and moving with it would overtake it, be
reflected, and meet it a second time at once.

* `cos_le_cos_of_abs_sub_two_pi_le` — the cosine near a whole turn;
* ★★★ `radar_gate_intervals` — the seven conditions.

## Exact scope

* **Arithmetic about three linear functions of the flow time.** No packet, no flow.
* **The clock at rest is at the angle `π` exactly.**
* **The messenger starts at the mirror image of the first level's place** (`a t₀ = b₁ τ`).
  The second level starts `(b₁ − b₂) τ` nearer the wall; the conditions carry that term.
* **The kinematic times are shifted by the start.** The relay is at `a s + b₁ τ = π`, the
  return at `(a + b) s = 2π`, the meeting at `b (s − τ) = π`: against the times of #412 for
  the distance `π`, the relay is early by `b₁ τ/a` and the meeting late by `τ`. Those
  differences are not bounded here.
* **Sufficient conditions, not necessary ones.**

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-183, UD-188, UD-193, UD-194); `RecordLayer/UnifiedWallRadar.lean` (#423:
`tri_wall_radar_lorentz`, whose hypotheses these are); `RecordLayer/UnifiedGateTimes.lean`
(#414: `cos_lt_cos_of_lt_abs`); `RecordLayer/UnifiedEmissionValues.lean` (#397:
`cos_le_cos_of_abs_le`, `cos_lt_cos_of_between`); `RecordLayer/UnifiedEventTimes.lean`
(#418: the same intervals for one speed and a start at the wall).
-/

@[expose] public section

noncomputable section

namespace CSD.RecordLayer

/-- The cosine near a whole turn: if `|x − 2π| ≤ y ≤ π` then `cos y ≤ cos x`. -/
theorem cos_le_cos_of_abs_sub_two_pi_le {x y : ℝ} (h : |x - 2 * Real.pi| ≤ y)
    (hy : y ≤ Real.pi) : Real.cos y ≤ Real.cos x := by
  rw [← Real.cos_sub_two_pi x]
  exact cos_le_cos_of_abs_le h hy

/-- A nonnegative rate keeps the order of two times. -/
theorem mul_mem_of_mem {r s lo hi : ℝ} (hr : 0 ≤ r) (h1 : lo ≤ s) (h2 : s ≤ hi) :
    r * lo ≤ r * s ∧ r * s ≤ r * hi :=
  ⟨mul_le_mul_of_nonneg_left h1 hr, mul_le_mul_of_nonneg_left h2 hr⟩

/-- ★★★ **The seven gate intervals from straight motion.** Rates `0 < b₂ ≤ b₁ < a`, the
clock prepared at the packet time `−τ ≤ 0`, the messenger started at the mirror image of the
first level's place (`a t₀ = b₁ τ`), the clock at rest at the angle `π`. With `σ = w − 2δ`
and `Σ = w + 2δ`, suppose:

* `(a + b₁) t_E + (b₁ − b₂) τ ≤ σ` (the emission);
* `Σ < (a − b₁) t_b`, `(a + b₁) t₃ + (b₁ − b₂) τ < 2π − Σ` and
  `(a − b₂) t₃ + 2 b₁ τ < 2π − Σ` (the messenger away);
* `2π − σ ≤ (a + b₂) t₄` and `(a + b₁) t₅ + (b₁ − b₂) τ ≤ 2π + σ` (the return);
* `a t_R + b₁ τ < π − Σ`, `π − σ ≤ a t_bR + b₁ τ`, `a t_cR + b₁ τ ≤ π + σ` (the relay);
* `b₁ τ < π − Σ`, `b₁ (t_M − τ) < π − Σ`, `π − σ ≤ b₂ (t_bM − τ)`,
  `b₁ (t_cM − τ) ≤ π + σ` (the meeting).

Then the seven conditions of `tri_wall_radar_lorentz` hold on their intervals. -/
theorem radar_gate_intervals {a b₁ b₂ t₀ τ w δ : ℝ} (hb₂ : 0 < b₂) (h21 : b₂ ≤ b₁)
    (h1a : b₁ < a) (hτ : 0 ≤ τ) (ht₀ : a * t₀ = b₁ * τ) (hδ0 : 0 ≤ δ) (hw : 2 * δ ≤ w)
    (hwπ : w + 2 * δ ≤ Real.pi) {tE tb t3 t4 t5 tR tbR tcR tM tbM tcM : ℝ}
    (htb : 0 ≤ tb) (ht4 : 0 ≤ t4) (hτM : τ ≤ tM) (hMb : tM ≤ tbM)
    (hE : (a + b₁) * tE + (b₁ - b₂) * τ ≤ w - 2 * δ)
    (hb : w + 2 * δ < (a - b₁) * tb)
    (h3 : (a + b₁) * t3 + (b₁ - b₂) * τ < 2 * Real.pi - (w + 2 * δ))
    (h3' : (a - b₂) * t3 + 2 * b₁ * τ < 2 * Real.pi - (w + 2 * δ))
    (h4 : 2 * Real.pi - (w - 2 * δ) ≤ (a + b₂) * t4)
    (h5 : (a + b₁) * t5 + (b₁ - b₂) * τ ≤ 2 * Real.pi + (w - 2 * δ))
    (hR : a * tR + b₁ * τ < Real.pi - (w + 2 * δ))
    (hbR : Real.pi - (w - 2 * δ) ≤ a * tbR + b₁ * τ)
    (hcR : a * tcR + b₁ * τ ≤ Real.pi + (w - 2 * δ))
    (hτπ : b₁ * τ < Real.pi - (w + 2 * δ))
    (hM : b₁ * (tM - τ) < Real.pi - (w + 2 * δ))
    (hbM : Real.pi - (w - 2 * δ) ≤ b₂ * (tbM - τ))
    (hcM : b₁ * (tcM - τ) ≤ Real.pi + (w - 2 * δ)) :
    (∀ s, 0 ≤ s → s ≤ tE →
      Real.cos (w - 2 * δ) ≤ Real.cos (a * (t₀ + s) + b₁ * (-τ + s))
        ∧ Real.cos (w - 2 * δ) ≤ Real.cos (a * (t₀ + s) + b₂ * (-τ + s)))
    ∧ (∀ s, tb ≤ s → s ≤ t3 →
      Real.cos (a * (t₀ + s) - b₁ * (-τ + s)) < Real.cos (w + 2 * δ)
        ∧ Real.cos (a * (t₀ + s) + b₁ * (-τ + s)) < Real.cos (w + 2 * δ)
        ∧ Real.cos (a * (t₀ + s) - b₂ * (-τ + s)) < Real.cos (w + 2 * δ)
        ∧ Real.cos (a * (t₀ + s) + b₂ * (-τ + s)) < Real.cos (w + 2 * δ))
    ∧ (∀ s, t4 ≤ s → s ≤ t5 →
      Real.cos (w - 2 * δ) ≤ Real.cos (a * (t₀ + s) + b₁ * (-τ + s))
        ∧ Real.cos (w - 2 * δ) ≤ Real.cos (a * (t₀ + s) + b₂ * (-τ + s)))
    ∧ (∀ s, 0 ≤ s → s ≤ tR →
      Real.cos (a * (t₀ + s) - Real.pi) < Real.cos (w + 2 * δ)
        ∧ Real.cos (a * (t₀ + s) + Real.pi) < Real.cos (w + 2 * δ))
    ∧ (∀ s, tbR ≤ s → s ≤ tcR →
      Real.cos (w - 2 * δ) ≤ Real.cos (a * (t₀ + s) - Real.pi))
    ∧ (∀ s, 0 ≤ s → s ≤ tM →
      Real.cos (Real.pi - b₁ * (-τ + s)) < Real.cos (w + 2 * δ)
        ∧ Real.cos (Real.pi + b₁ * (-τ + s)) < Real.cos (w + 2 * δ)
        ∧ Real.cos (Real.pi - b₂ * (-τ + s)) < Real.cos (w + 2 * δ)
        ∧ Real.cos (Real.pi + b₂ * (-τ + s)) < Real.cos (w + 2 * δ))
    ∧ (∀ s, tbM ≤ s → s ≤ tcM →
      Real.cos (w - 2 * δ) ≤ Real.cos (Real.pi - b₁ * (-τ + s))
        ∧ Real.cos (w - 2 * δ) ≤ Real.cos (Real.pi - b₂ * (-τ + s))) := by
  have hb₁ : 0 < b₁ := hb₂.trans_le h21
  have ha : 0 < a := hb₁.trans h1a
  have hS : 0 ≤ w + 2 * δ := by linarith only [hw, hδ0]
  have hσπ : w - 2 * δ ≤ Real.pi := by linarith only [hwπ, hδ0]
  have hτ1 : 0 ≤ b₁ * τ := mul_nonneg hb₁.le hτ
  have hτ2 : 0 ≤ b₂ * τ := mul_nonneg hb₂.le hτ
  have hτ21 : b₂ * τ ≤ b₁ * τ := mul_le_mul_of_nonneg_right h21 hτ
  have hπ := Real.pi_pos
  refine ⟨fun s h0 h1 => ?_, fun s h0 h1 => ?_, fun s h0 h1 => ?_, fun s h0 h1 => ?_,
    fun s h0 h1 => ?_, fun s h0 h1 => ?_, fun s h0 h1 => ?_⟩
  · -- the emission
    obtain ⟨-, a1⟩ := mul_mem_of_mem ha.le h0 h1
    obtain ⟨-, a2⟩ := mul_mem_of_mem hb₁.le h0 h1
    have a3 : 0 ≤ a * s := mul_nonneg ha.le h0
    have a4 : 0 ≤ b₂ * s := mul_nonneg hb₂.le h0
    have a5 : b₂ * s ≤ b₁ * s := mul_le_mul_of_nonneg_right h21 h0
    constructor
    · exact cos_le_cos_of_abs_le
        (abs_le.2 ⟨by linarith only [a3, a4, a5, ht₀, hE, a1, a2, hτ21, hσπ, hS, hw],
          by linarith only [a3, a4, a5, ht₀, hE, a1, a2, hτ21]⟩) hσπ
    · exact cos_le_cos_of_abs_le
        (abs_le.2 ⟨by linarith only [a3, a4, a5, ht₀, hE, a1, a2, hτ21, hσπ, hS, hw],
          by linarith only [a3, a4, a5, ht₀, hE, a1, a2, hτ21]⟩) hσπ
  · -- the messenger away
    have hs0 : 0 ≤ s := htb.trans h0
    obtain ⟨a1, -⟩ := mul_mem_of_mem (sub_nonneg.2 h1a.le) h0 h1
    obtain ⟨-, a2⟩ := mul_mem_of_mem (sub_nonneg.2 (h21.trans h1a.le)) h0 h1
    obtain ⟨-, a3⟩ := mul_mem_of_mem (add_nonneg ha.le hb₁.le) h0 h1
    have a4 : 0 ≤ b₂ * s := mul_nonneg hb₂.le hs0
    have a5 : b₂ * s ≤ b₁ * s := mul_le_mul_of_nonneg_right h21 hs0
    have a6 : b₁ * s ≤ a * s := mul_le_mul_of_nonneg_right h1a.le hs0
    refine ⟨cos_lt_cos_of_between hS ?_ ?_, cos_lt_cos_of_between hS ?_ ?_,
      cos_lt_cos_of_between hS ?_ ?_, cos_lt_cos_of_between hS ?_ ?_⟩
    · linarith only [a1, a4, a5, a6, ht₀, hb, hτ1]
    · linarith only [a2, a4, a5, a6, ht₀, h3', hτ1, hτ21]
    · linarith only [a1, a4, a5, a6, ht₀, hb, hτ1]
    · linarith only [a3, a4, a5, a6, ht₀, h3, hτ21]
    · linarith only [a1, a4, a5, a6, ht₀, hb, hτ1, hτ2]
    · linarith only [a2, a4, a5, a6, ht₀, h3', hτ1, hτ21]
    · linarith only [a1, a4, a5, a6, ht₀, hb, hτ1, hτ21]
    · linarith only [a3, a4, a5, a6, ht₀, h3, hτ21]
  · -- the return
    have hs0 : 0 ≤ s := ht4.trans h0
    obtain ⟨a1, -⟩ := mul_mem_of_mem (add_nonneg ha.le hb₂.le) h0 h1
    obtain ⟨-, a3⟩ := mul_mem_of_mem (add_nonneg ha.le hb₁.le) h0 h1
    have a5 : b₂ * s ≤ b₁ * s := mul_le_mul_of_nonneg_right h21 hs0
    constructor
    · exact cos_le_cos_of_abs_sub_two_pi_le
        (abs_le.2 ⟨by linarith only [a1, a5, ht₀, h4], by linarith only [a3, a5, ht₀, h5, hτ21]⟩)
        hσπ
    · exact cos_le_cos_of_abs_sub_two_pi_le
        (abs_le.2 ⟨by linarith only [a1, a5, ht₀, h4, hτ21],
          by linarith only [a3, a5, ht₀, h5, hτ21]⟩) hσπ
  · -- the messenger away from the clock at rest
    obtain ⟨-, a1⟩ := mul_mem_of_mem ha.le h0 h1
    have a3 : 0 ≤ a * s := mul_nonneg ha.le h0
    constructor
    · refine cos_lt_cos_of_lt_abs hS
        (abs_le.2 ⟨by linarith only [a3, ht₀, hτ1], by linarith only [a1, ht₀, hR, hS, hπ]⟩) ?_
      exact lt_of_lt_of_le (by linarith only [a1, ht₀, hR]) (neg_le_abs _)
    · exact cos_lt_cos_of_between hS (by linarith only [a3, a1, ht₀, hτ1, hR])
        (by linarith only [a1, ht₀, hR])
  · -- the messenger at the clock at rest
    obtain ⟨a1, a2⟩ := mul_mem_of_mem ha.le h0 h1
    exact cos_le_cos_of_abs_le
      (abs_le.2 ⟨by linarith only [a1, ht₀, hbR], by linarith only [a2, ht₀, hcR]⟩) hσπ
  · -- the two clocks apart
    have key : ∀ b, 0 < b → b ≤ b₁ →
        -(Real.pi - (w + 2 * δ)) < b * (-τ + s) ∧ b * (-τ + s) < Real.pi - (w + 2 * δ) := by
      intro b hb0 hb1
      have c1 : b * τ ≤ b₁ * τ := mul_le_mul_of_nonneg_right hb1 hτ
      have c2 : 0 ≤ b * s := mul_nonneg hb0.le h0
      obtain ⟨-, c3⟩ := mul_mem_of_mem hb0.le (le_refl (-τ + s))
        (by linarith only [h1] : -τ + s ≤ tM - τ)
      have c4 : b * (tM - τ) ≤ b₁ * (tM - τ) :=
        mul_le_mul_of_nonneg_right hb1 (sub_nonneg.2 hτM)
      exact ⟨by linarith only [c1, c2, hτπ], by linarith only [c3, c4, hM]⟩
    obtain ⟨k1, k2⟩ := key b₁ hb₁ le_rfl
    obtain ⟨k3, k4⟩ := key b₂ hb₂ h21
    refine ⟨cos_lt_cos_of_between hS ?_ ?_, cos_lt_cos_of_between hS ?_ ?_,
      cos_lt_cos_of_between hS ?_ ?_, cos_lt_cos_of_between hS ?_ ?_⟩
    · linarith only [k2]
    · linarith only [k1]
    · linarith only [k1]
    · linarith only [k2]
    · linarith only [k4]
    · linarith only [k3]
    · linarith only [k3]
    · linarith only [k4]
  · -- the two clocks together
    have hτb : τ ≤ tbM := hτM.trans hMb
    have key : ∀ b, b₂ ≤ b → b ≤ b₁ → 0 < b →
        Real.pi - (w - 2 * δ) ≤ b * (-τ + s) ∧ b * (-τ + s) ≤ Real.pi + (w - 2 * δ) := by
      intro b hb2 hb1 hb0
      obtain ⟨c1, c2⟩ := mul_mem_of_mem hb0.le (by linarith only [h0] : tbM - τ ≤ -τ + s)
        (by linarith only [h1] : -τ + s ≤ tcM - τ)
      have c3 : b₂ * (tbM - τ) ≤ b * (tbM - τ) :=
        mul_le_mul_of_nonneg_right hb2 (sub_nonneg.2 hτb)
      have c4 : b * (tcM - τ) ≤ b₁ * (tcM - τ) :=
        mul_le_mul_of_nonneg_right hb1 (by linarith only [hτb, h0, h1])
      exact ⟨by linarith only [c1, c3, hbM], by linarith only [c2, c4, hcM]⟩
    obtain ⟨k1, k2⟩ := key b₁ h21 le_rfl hb₁
    obtain ⟨k3, k4⟩ := key b₂ le_rfl h21 hb₂
    exact ⟨cos_le_cos_of_abs_le
        (abs_le.2 ⟨by linarith only [k2], by linarith only [k1]⟩) hσπ,
      cos_le_cos_of_abs_le (abs_le.2 ⟨by linarith only [k4], by linarith only [k3]⟩) hσπ⟩

end CSD.RecordLayer

end
