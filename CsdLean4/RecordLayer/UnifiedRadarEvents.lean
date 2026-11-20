/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.FlowEventCone
public import CsdLean4.RecordLayer.UnifiedRadarFamily
public import CsdLean4.RecordLayer.UnifiedRingShift

/-!
# The radar's five readings as events at flow times, and what the ring permits between them

**Category:** 7-SigmaLayer. BACKLOG #442, second brick (Task 4 of the author's plan "Unified
records, quantum measurement and emergent spacetime", the causal bridge;
`specs/unified-records-spacetime-task-plans.md` §2, item 1; the author's decision of
2026-11-19: the events keep their real flow times).

`RecordLayer/FlowEventCone.lean` states the graph relation for an event with a real flow
time. Here the five readings of the family's radar run (`radar_family_lorentz`) are given a
region of the ring and a flow time, and the relations the ring's graph gives them are proved.

## Arcs of the ring and the growth of the graph

* `cos_add_lt_cos_sub` — `cos δ₁ < cos u` and `cos δ₂ ≤ cos v` give
  `cos (δ₁ + δ₂) < cos (u − v)` when `δ₁ + δ₂ ≤ π`;
* `growG_mono`, `growIterG_subset_of_subset`, `growIterG_union_subset` — growth is monotone
  and the growth of a union is in the union of the growths;
* ★★ `growIterG_ringArc_subset` — `d` steps of growth from the arc of half-angle `δ` stay in
  the arc of half-angle `δ + d · 2π/L`;
* `disjoint_ringArc` — two arcs whose centres are farther apart than the sum of their
  half-angles are disjoint;
* ★★ `hopSeparated_wallArc_pi` — the double arc about `x` is `d` hops from the double arc
  about `π` when `|x| ≤ π − 2δ − d · 2π/L`.

## The radar's events

* `RadarReading` — emission, relay, return, and the meeting read on each clock;
* `radarEventPlace`, `radarEventTime`, `radarEvent` — the angle of the wall each is read
  at, the flow time its reading window opens, and the event: the double arc of half-angle
  `3δ` (the width of the gates) about the place, at that time;
* `radar_window_starts_ordered`, ★★ `radarEventTime_le` — **the order of the flow parameter**: the
  emission's window opens before the relay's, the relay's before the return's, the return's
  before the meeting's;
* `mem_wallArc_pi`, ★★ `radarEvent_permitted_farWall` — **permitted by the graph**: the relay
  and the two meeting readings are at the same sites, so each is permitted within any number
  of hops to the later one;
* ★★★ `radarEvent_hopSeparated_farWall`, `radar_emission_hopSeparated_relay` — **what the
  graph does not permit at short range**: an event at the place `x` is `d` hops from the far
  wall when `|x| ≤ π − 6δ − d · 2π/(M + 1)`; the emission is, for every `d` with
  `d · 2π/(M + 1) ≤ 3π/4`;
* ★★★ `radar_emission_kick_response_le` — **permitted against demonstrated**: a kick on the
  emission's sites at its time changes an observable on the relay's sites, read at the
  relay's time, by at most `2 (2 ‖S‖ (t_bR − t_b))^d / d! · ‖D‖` for those `d`.

## Honest scope

⚠️ **The regions and the times are assigned, not derived.** The place of a reading is the
angle at which the kinematics of UD-194 puts the coincidence its gate reads; the time is the
flow time its reading window opens, from which its count stands. Nothing here shows that a
carrier is at those sites then: that is the content of the histories of UD-196, which this
module does not use.

⚠️ **The time is the window's opening, not its end.** The plan's §2 said the end. With the
ends the emission would not precede the relay: the emission's window stays open until
shortly before the return.

⚠️ **Three notions, kept apart.** `radarEventTime_le` is the order of the flow parameter (UA-7);
`radarEvent_permitted_farWall` and the two separation statements are relations of the ring's
graph; `radar_emission_kick_response_le` bounds a response from above. No influence is
demonstrated.

⚠️ **The return's place is not bounded here.** Its separation from the far wall is the
conditional statement `radarEvent_hopSeparated_farWall`; the hypothesis is not checked for
it. The hop count from the emission to the return is not computed.

⚠️ **The kick is on a carrier's sites**, not on a pointer's record, and the bound is a
factorial tail with the generator's norm as its rate, not a sharp cone.

⚠️ **The graph is assumed** (the ring). Hop distance counts links; it is not a metric of
spacetime. The five events are not yet the coordinates of the macrostate of Task 3.

References: `specs/BACKLOG.md` #442; `specs/unified-record-spacetime-plan.md` (UA-7, UD-194,
UD-196, UD-239, UD-248); `specs/unified-records-spacetime-task-plans.md` (§2);
`RecordLayer/FlowEventCone.lean` (`FlowEvent`, `HopSeparated`, `FlowEvent.PermittedWithin`,
`FlowEvent.kick_response_le`); `RecordLayer/GraphCone.lean` (`ringAdj`, `growIterG`);
`RecordLayer/UnifiedGateRegions.lean` (`ringArc`, `mem_ringArc`);
`RecordLayer/UnifiedWallGate.lean` (`wallArc`); `RecordLayer/UnifiedRingShift.lean`
(`cos_site_sub`); `RecordLayer/UnifiedRadarFamily.lean` (`famTb`, `famTbR`, `famT4`,
`famTbM`, `radar_family_gate_conditions`); `RecordLayer/UnifiedWallIntervals.lean`
(`radar_gate_times`); `RecordLayer/UnifiedRadarRun.lean` (`radar_family_lorentz`);
`specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Matrix NormedSpace Set
open scoped Matrix.Norms.L2Operator

namespace CSD.RecordLayer

/-! ### Arcs of the ring and the growth of the graph -/

/-- Two angles within `δ₁` and `δ₂` of zero, in cosine, differ by less than `δ₁ + δ₂`, in
cosine. -/
theorem cos_add_lt_cos_sub {u v δ₁ δ₂ : ℝ} (h1 : Real.cos δ₁ < Real.cos u)
    (h2 : Real.cos δ₂ ≤ Real.cos v) (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (hπ : δ₁ + δ₂ ≤ Real.pi) : Real.cos (δ₁ + δ₂) < Real.cos (u - v) := by
  have hcu : Real.cos (Real.arccos (Real.cos u)) = Real.cos u :=
    Real.cos_arccos (Real.neg_one_le_cos u) (Real.cos_le_one u)
  have hcv : Real.cos (Real.arccos (Real.cos v)) = Real.cos v :=
    Real.cos_arccos (Real.neg_one_le_cos v) (Real.cos_le_one v)
  have hsu : Real.sin (Real.arccos (Real.cos u)) = |Real.sin u| := by
    rw [Real.sin_arccos, ← Real.sqrt_sq_eq_abs, Real.sin_sq]
  have hsv : Real.sin (Real.arccos (Real.cos v)) = |Real.sin v| := by
    rw [Real.sin_arccos, ← Real.sqrt_sq_eq_abs, Real.sin_sq]
  have hα0 := Real.arccos_nonneg (Real.cos u)
  have hαπ := Real.arccos_le_pi (Real.cos u)
  have hβ0 := Real.arccos_nonneg (Real.cos v)
  have hβπ := Real.arccos_le_pi (Real.cos v)
  have hα : Real.arccos (Real.cos u) < δ₁ := by
    by_contra hn
    rw [not_lt] at hn
    have := Real.cos_le_cos_of_nonneg_of_le_pi hδ₁ hαπ hn
    rw [hcu] at this
    linarith
  have hβ : Real.arccos (Real.cos v) ≤ δ₂ := by
    by_contra hn
    rw [not_le] at hn
    have := Real.cos_lt_cos_of_nonneg_of_le_pi hδ₂ hβπ hn
    rw [hcv] at this
    linarith
  have hlt := Real.cos_lt_cos_of_nonneg_of_le_pi (add_nonneg hα0 hβ0) hπ
    (add_lt_add_of_lt_of_le hα hβ)
  rw [Real.cos_add (Real.arccos (Real.cos u)) (Real.arccos (Real.cos v)), hcu, hcv, hsu,
    hsv] at hlt
  have hab := neg_abs_le (Real.sin u * Real.sin v)
  rw [abs_mul] at hab
  rw [Real.cos_sub]
  linarith

section Graph

variable {V : Type*}

/-- Growth is monotone in the set. -/
theorem growG_mono (adj : V → V → Prop) {X Y : Set V} (h : X ⊆ Y) :
    growG adj X ⊆ growG adj Y := by
  rintro a (ha | ⟨b, hb, hab⟩)
  · exact Or.inl (h ha)
  · exact Or.inr ⟨b, h hb, hab⟩

/-- If one step of growth from `A i` stays in `A (i + 1)`, `d` steps from `A 0` stay in
`A d`. -/
theorem growIterG_subset_of_subset (adj : V → V → Prop) (A : ℕ → Set V) (d : ℕ)
    (h : ∀ i, i < d → growG adj (A i) ⊆ A (i + 1)) : growIterG adj (A 0) d ⊆ A d := by
  induction d with
  | zero => exact subset_rfl
  | succ d ih =>
    exact (growG_mono adj (ih fun i hi => h i (Nat.lt_succ_of_lt hi))).trans
      (h d (Nat.lt_succ_self d))

/-- The growth of a union is in the union of the growths. -/
theorem growIterG_union_subset (adj : V → V → Prop) (X Y : Set V) (d : ℕ) :
    growIterG adj (X ∪ Y) d ⊆ growIterG adj X d ∪ growIterG adj Y d := by
  induction d with
  | zero => exact subset_rfl
  | succ d ih =>
    refine (growG_mono adj ih).trans ?_
    rintro a (ha | ⟨b, hb, hab⟩)
    · exact ha.imp (fun h => Or.inl h) fun h => Or.inl h
    · exact hb.imp (fun h => Or.inr ⟨b, h, hab⟩) fun h => Or.inr ⟨b, h, hab⟩

/-- Two sets that share a site are not `d` hops apart, for any `d`. -/
theorem not_hopSeparated_of_mem (adj : V → V → Prop) (d : ℕ) {X Y : Set V} {a : V}
    (hX : a ∈ X) (hY : a ∈ Y) : ¬ HopSeparated adj d X Y := fun h =>
  Set.disjoint_left.1 (h.mono (Nat.zero_le d)) hX hY

end Graph

section Ring

variable {L : ℕ} [NeZero L]

omit [NeZero L] in
/-- The angle of the site `1` has cosine at least `cos (2π/L)`. -/
theorem cos_two_pi_div_le_cos_site_one (hπ : 2 * Real.pi / L ≤ Real.pi) :
    Real.cos (2 * Real.pi / L) ≤ Real.cos (2 * Real.pi * (1 : ZMod L).val / L) := by
  have hv : (1 : ZMod L).val ≤ 1 := by
    rw [ZMod.val_one_eq_one_mod]
    exact Nat.mod_le 1 L
  have hvr : (((1 : ZMod L).val : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hv
  refine cos_le_cos_of_abs_le ?_ hπ
  rw [abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) (Nat.cast_nonneg L)

/-- A site next to an arc is in the arc with the half-angle enlarged by `2π/L`. -/
theorem sub_one_mem_ringArc {x δ : ℝ} (hδ : 0 ≤ δ) (hπ : δ + 2 * Real.pi / L ≤ Real.pi)
    {b : ZMod L} (hb : b ∈ ringArc L x δ) : b - 1 ∈ ringArc L x (δ + 2 * Real.pi / L) := by
  have hη : 0 ≤ 2 * Real.pi / (L : ℝ) := by positivity
  rw [mem_ringArc, cos_site_sub b 1 x,
    show 2 * Real.pi * b.val / L - 2 * Real.pi * (1 : ZMod L).val / L - x
      = (2 * Real.pi * b.val / L - x) - 2 * Real.pi * (1 : ZMod L).val / L by ring]
  exact cos_add_lt_cos_sub (mem_ringArc.1 hb)
    (cos_two_pi_div_le_cos_site_one (by linarith)) hδ hη hπ

/-- The same for the other neighbour. -/
theorem add_one_mem_ringArc {x δ : ℝ} (hδ : 0 ≤ δ) (hπ : δ + 2 * Real.pi / L ≤ Real.pi)
    {b : ZMod L} (hb : b ∈ ringArc L x δ) : b + 1 ∈ ringArc L x (δ + 2 * Real.pi / L) := by
  have hη : 0 ≤ 2 * Real.pi / (L : ℝ) := by positivity
  have hb' : (b + 1) - 1 ∈ ringArc L x δ := by rwa [add_sub_cancel_right]
  have h1 := mem_ringArc.1 hb'
  rw [cos_site_sub (b + 1) 1 x] at h1
  have h2 : Real.cos (2 * Real.pi / L)
      ≤ Real.cos (-(2 * Real.pi * (1 : ZMod L).val / L)) := by
    rw [Real.cos_neg]
    exact cos_two_pi_div_le_cos_site_one (by linarith)
  have key := cos_add_lt_cos_sub h1 h2 hδ hη hπ
  rw [mem_ringArc]
  rwa [show 2 * Real.pi * (b + 1).val / L - 2 * Real.pi * (1 : ZMod L).val / L - x
      - -(2 * Real.pi * (1 : ZMod L).val / L) = 2 * Real.pi * (b + 1).val / L - x by ring]
    at key

/-- A larger half-angle gives a larger arc. -/
theorem ringArc_subset_of_le {x δ δ' : ℝ} (hδ : 0 ≤ δ) (h : δ ≤ δ')
    (hπ : δ' ≤ Real.pi) : (ringArc L x δ : Set (ZMod L)) ⊆ ringArc L x δ' := fun k hk => by
  have h1 := mem_ringArc.1 (Finset.mem_coe.1 hk)
  exact Finset.mem_coe.2 (mem_ringArc.2
    ((Real.cos_le_cos_of_nonneg_of_le_pi hδ hπ h).trans_lt h1))

/-- One step of growth from an arc. -/
theorem growG_ringArc_subset {x δ : ℝ} (hδ : 0 ≤ δ) (hπ : δ + 2 * Real.pi / L ≤ Real.pi) :
    growG (ringAdj (L := L)) (ringArc L x δ : Set (ZMod L))
      ⊆ ringArc L x (δ + 2 * Real.pi / L) := by
  have hη : 0 ≤ 2 * Real.pi / (L : ℝ) := by positivity
  rintro a (ha | ⟨b, hb, (h | h) | (h | h)⟩)
  · exact ringArc_subset_of_le hδ (by linarith) hπ ha
  · have : a = b - 1 := by rw [h, add_sub_cancel_right]
    rw [this]
    exact Finset.mem_coe.2 (sub_one_mem_ringArc hδ hπ (Finset.mem_coe.1 hb))
  · have : a = b + 1 := by rw [h, sub_add_cancel]
    rw [this]
    exact Finset.mem_coe.2 (add_one_mem_ringArc hδ hπ (Finset.mem_coe.1 hb))
  · rw [h]
    exact Finset.mem_coe.2 (add_one_mem_ringArc hδ hπ (Finset.mem_coe.1 hb))
  · rw [h]
    exact Finset.mem_coe.2 (sub_one_mem_ringArc hδ hπ (Finset.mem_coe.1 hb))

/-- ★★ **Growth from an arc.** `d` steps of growth along the ring from the arc of half-angle
`δ` about `x` stay in the arc of half-angle `δ + d · 2π/L`. -/
theorem growIterG_ringArc_subset {x δ : ℝ} (hδ : 0 ≤ δ) (d : ℕ)
    (hπ : δ + d * (2 * Real.pi / L) ≤ Real.pi) :
    growIterG (ringAdj (L := L)) (ringArc L x δ : Set (ZMod L)) d
      ⊆ ringArc L x (δ + d * (2 * Real.pi / L)) := by
  have hη : 0 ≤ 2 * Real.pi / (L : ℝ) := by positivity
  have key := growIterG_subset_of_subset (ringAdj (L := L))
    (fun i : ℕ => (ringArc L x (δ + i * (2 * Real.pi / L)) : Set (ZMod L))) d
    (fun i hi => by
      have hid : ((i : ℝ) + 1) * (2 * Real.pi / L) ≤ d * (2 * Real.pi / L) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hη
      have h := growG_ringArc_subset (L := L) (x := x) (δ := δ + i * (2 * Real.pi / L))
        (add_nonneg hδ (mul_nonneg (Nat.cast_nonneg i) hη)) (by linarith)
      have e : δ + i * (2 * Real.pi / L) + 2 * Real.pi / L
          = δ + ((i + 1 : ℕ) : ℝ) * (2 * Real.pi / L) := by
        push_cast
        ring
      rwa [e] at h)
  simpa using key

/-- Two arcs whose centres are farther apart than the sum of their half-angles are
disjoint. -/
theorem disjoint_ringArc {x y δ₁ δ₂ : ℝ} (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (hπ : δ₁ + δ₂ ≤ Real.pi) (h : Real.cos (x - y) ≤ Real.cos (δ₁ + δ₂)) :
    Disjoint (ringArc L x δ₁ : Set (ZMod L)) (ringArc L y δ₂) := by
  rw [Set.disjoint_left]
  intro k hk hk'
  have h1 := mem_ringArc.1 (Finset.mem_coe.1 hk')
  have h2 := mem_ringArc.1 (Finset.mem_coe.1 hk)
  have key := cos_add_lt_cos_sub h2 h1.le hδ₁ hδ₂ hπ
  rw [show 2 * Real.pi * k.val / L - x - (2 * Real.pi * k.val / L - y) = -(x - y) by ring,
    Real.cos_neg] at key
  linarith

/-- ★★ **An arc and the far wall.** The double arc of half-angle `δ` about `x` is `d` hops
from the double arc about `π` when `|x| ≤ π − 2δ − d · 2π/L`. -/
theorem hopSeparated_wallArc_pi {x δ : ℝ} (hδ : 0 ≤ δ) (d : ℕ)
    (hx : |x| ≤ Real.pi - 2 * δ - d * (2 * Real.pi / L)) :
    HopSeparated (ringAdj (L := L)) d (wallArc L x δ : Set (ZMod L))
      (wallArc L Real.pi δ) := by
  have hη : 0 ≤ (d : ℝ) * (2 * Real.pi / (L : ℝ)) := by positivity
  have hx0 := abs_nonneg x
  have hc : -Real.cos x ≤ Real.cos (δ + d * (2 * Real.pi / L) + δ) := by
    have h1 := cos_le_cos_of_abs_le hx (by linarith)
    rw [show Real.pi - 2 * δ - d * (2 * Real.pi / L)
      = Real.pi - (δ + d * (2 * Real.pi / L) + δ) by ring, Real.cos_pi_sub] at h1
    linarith
  have c1 : Real.cos (x - Real.pi) = -Real.cos x := Real.cos_sub_pi x
  have c2 : Real.cos (x - -Real.pi) = -Real.cos x := by rw [sub_neg_eq_add, Real.cos_add_pi]
  have c3 : Real.cos (-x - Real.pi) = -Real.cos x := by rw [Real.cos_sub_pi, Real.cos_neg]
  have c4 : Real.cos (-x - -Real.pi) = -Real.cos x := by
    rw [sub_neg_eq_add, Real.cos_add_pi, Real.cos_neg]
  have hdis : ∀ a b : ℝ, Real.cos (a - b) = -Real.cos x →
      Disjoint (growIterG (ringAdj (L := L)) (ringArc L a δ : Set (ZMod L)) d)
        (ringArc L b δ : Set (ZMod L)) := fun a b hab =>
    Set.disjoint_of_subset_left (growIterG_ringArc_subset hδ d (by linarith))
      (disjoint_ringArc (add_nonneg hδ hη) hδ (by linarith) (by rw [hab]; exact hc))
  unfold HopSeparated
  rw [wallArc, wallArc, Finset.coe_union, Finset.coe_union]
  refine Set.disjoint_of_subset_left (growIterG_union_subset _ _ _ d) ?_
  rw [Set.disjoint_union_left, Set.disjoint_union_right, Set.disjoint_union_right]
  exact ⟨⟨hdis _ _ c1, hdis _ _ c2⟩, hdis _ _ c3, hdis _ _ c4⟩

end Ring

/-! ### The radar's events -/

/-- **The five readings of the radar run**: the emission and the return on the moving clock,
the relay on the clock at rest, and the meeting read on each clock. -/
inductive RadarReading
  | emission
  | relay
  | ret
  | meetMoving
  | meetRest

/-- **The angle of the wall a reading is read at**, by the kinematics of UD-194: the moving
clock's start for the emission, its place when the return window opens for the return, the
far wall for the relay and the two meeting readings. -/
def radarEventPlace (k M : ℕ) : RadarReading → ℝ
  | .emission => radarRateB k * radarTau k M
  | .relay => Real.pi
  | .ret => radarRateB k * (famT4 k - radarTau k M)
  | .meetMoving => Real.pi
  | .meetRest => Real.pi

/-- **The flow time a reading's window opens**: from it the reading's count stands. -/
def radarEventTime (k M : ℕ) : RadarReading → ℝ
  | .emission => famTb k
  | .relay => famTbR k M
  | .ret => famT4 k
  | .meetMoving => famTbM k M
  | .meetRest => famTbM k M

/-- **A reading as an event at a flow time**: the double arc of half-angle `3δ` (the width of
the gates) about its place, at the time its window opens. -/
def radarEvent (k M : ℕ) (r : RadarReading) : FlowEvent (ZMod (M + 1)) where
  region := (wallArc (M + 1) (radarEventPlace k M r) (3 * wallDelta k) : Set (ZMod (M + 1)))
  time := radarEventTime k M r

/-- **The window openings in order** (real arithmetic), under four of the conditions of
`radar_gate_times`. -/
theorem radar_window_starts_ordered {a b₁ b₂ τ δ : ℝ} (hb₂ : 0 < b₂) (h21 : b₂ ≤ b₁)
    (h2a : 2 * b₁ ≤ a) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδπ : 24 * δ ≤ Real.pi)
    (hstart : 4 * (b₁ * τ) ≤ Real.pi - 24 * δ) :
    6 * δ / (a - b₁) ≤ (Real.pi - δ - b₁ * τ) / a
      ∧ (Real.pi - δ - b₁ * τ) / a ≤ (2 * Real.pi - δ) / (a + b₂)
      ∧ (2 * Real.pi - δ) / (a + b₂) ≤ τ + (Real.pi - δ) / b₂ := by
  have hb₁ : 0 < b₁ := hb₂.trans_le h21
  have ha : 0 < a := by linarith
  have hab : 0 < a - b₁ := by linarith
  have hp2 : 0 < a + b₂ := by linarith
  have hτ1 : 0 ≤ b₁ * τ := mul_nonneg hb₁.le hτ
  have da : 0 < δ * a := mul_pos hδ ha
  have πa : 0 < Real.pi * a := mul_pos Real.pi_pos ha
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ hab ha]
    have h1 : 23 * δ * (a / 2) ≤ (Real.pi - δ - b₁ * τ) * (a - b₁) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    nlinarith
  · rw [div_le_div_iff₀ ha hp2]
    have h1 : (Real.pi - δ - b₁ * τ) * (a + b₂) ≤ (Real.pi - δ) * (3 * a / 2) :=
      mul_le_mul (by linarith) (by linarith) hp2.le (by linarith)
    nlinarith
  · have h1 : (2 * Real.pi - δ) / (a + b₂) ≤ (Real.pi - δ) / b₂ := by
      rw [div_le_div_iff₀ hp2 hb₂]
      have h2 : (Real.pi - δ) * (2 * b₂) ≤ (Real.pi - δ) * a :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith [mul_pos hδ hb₂, mul_pos Real.pi_pos hb₂,
        mul_le_mul_of_nonneg_right hδπ hb₂.le]
    linarith

/-- ★★ **The order of the flow parameter for the radar's readings.** For every `k ≥ 100` and
every ring: the emission's window opens before the relay's, the relay's before the return's,
and the return's before the meeting's. -/
theorem radarEventTime_le {k : ℕ} (hk : 100 ≤ k) (M : ℕ) :
    radarEventTime k M .emission ≤ radarEventTime k M .relay
      ∧ radarEventTime k M .relay ≤ radarEventTime k M .ret
      ∧ radarEventTime k M .ret ≤ radarEventTime k M .meetMoving
      ∧ radarEventTime k M .ret ≤ radarEventTime k M .meetRest := by
  obtain ⟨c_b₂, c_21, c_2a, -, c_τ, c_δ, c_δπ, c_start, -, -⟩ :=
    radar_family_gate_conditions hk M
  obtain ⟨h1, h2, h3⟩ := radar_window_starts_ordered c_b₂ c_21 c_2a c_τ c_δ c_δπ c_start
  exact ⟨h1, h2, h3, h3⟩

/-- On a ring of `2H` sites the site `H` is in the double arc about `π`. -/
theorem mem_wallArc_pi {M H : ℕ} (hH : M + 1 = 2 * H) {δ : ℝ} (hδ : 0 < δ)
    (hδπ : δ ≤ Real.pi) : (H : ZMod (M + 1)) ∈ wallArc (M + 1) Real.pi δ := by
  have hH0 : 0 < H := by omega
  have hval : ((H : ZMod (M + 1)).val : ℝ) = H := by
    rw [ZMod.val_cast_of_lt (by omega)]
  have hL : ((M + 1 : ℕ) : ℝ) = 2 * H := by rw [hH]; push_cast; ring
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH0
  refine mem_wallArc.2 (Or.inl (mem_ringArc.2 ?_))
  have e : 2 * Real.pi * ((H : ZMod (M + 1)).val : ℝ) / ((M + 1 : ℕ) : ℝ) - Real.pi = 0 := by
    rw [hval, hL]
    field_simp
    ring
  rw [e]
  have habs : |δ| ≤ Real.pi := by rwa [abs_of_pos hδ]
  exact cos_lt_cos_of_lt_abs le_rfl habs (by rwa [abs_of_pos hδ])

/-- ★★ **Permitted by the graph: the readings at the far wall.** The relay and the two
meeting readings are at the same sites; each is permitted, within any number of hops, to the
later one, and the two meeting readings to each other. -/
theorem radarEvent_permitted_farWall {k : ℕ} (hk : 100 ≤ k) {M H : ℕ} (hH : M + 1 = 2 * H)
    (d : ℕ) :
    FlowEvent.PermittedWithin (ringAdj (L := M + 1)) d (radarEvent k M .relay)
        (radarEvent k M .meetMoving)
      ∧ FlowEvent.PermittedWithin (ringAdj (L := M + 1)) d (radarEvent k M .relay)
        (radarEvent k M .meetRest)
      ∧ FlowEvent.PermittedWithin (ringAdj (L := M + 1)) d (radarEvent k M .meetMoving)
        (radarEvent k M .meetRest)
      ∧ FlowEvent.PermittedWithin (ringAdj (L := M + 1)) d (radarEvent k M .meetRest)
        (radarEvent k M .meetMoving) := by
  obtain ⟨-, -, -, -, -, c_δ, c_δπ, -, -, -⟩ := radar_family_gate_conditions hk M
  obtain ⟨-, t2, t3, -⟩ := radarEventTime_le hk M
  have hmem : (H : ZMod (M + 1))
      ∈ (wallArc (M + 1) Real.pi (3 * wallDelta k) : Set (ZMod (M + 1))) :=
    Finset.mem_coe.2 (mem_wallArc_pi hH (by linarith) (by linarith [Real.pi_pos]))
  have hns : ¬ HopSeparated (ringAdj (L := M + 1)) d
      (wallArc (M + 1) Real.pi (3 * wallDelta k) : Set (ZMod (M + 1)))
      (wallArc (M + 1) Real.pi (3 * wallDelta k)) := not_hopSeparated_of_mem _ d hmem hmem
  exact ⟨⟨t2.trans t3, hns⟩, ⟨t2.trans t3, hns⟩, ⟨le_rfl, hns⟩, ⟨le_rfl, hns⟩⟩

/-- ★★★ **What the graph does not permit at short range.** A reading whose place `x` has
`|x| ≤ π − 6δ − d · 2π/(M + 1)` is `d` hops from the relay's sites, which are also the
sites of the two meeting readings. -/
theorem radarEvent_hopSeparated_farWall (k M : ℕ) (hδ : 0 ≤ wallDelta k) (r : RadarReading)
    (d : ℕ)
    (hx : |radarEventPlace k M r|
      ≤ Real.pi - 6 * wallDelta k - d * (2 * Real.pi / ((M + 1 : ℕ) : ℝ))) :
    HopSeparated (ringAdj (L := M + 1)) d (radarEvent k M r).region
      (radarEvent k M .relay).region :=
  hopSeparated_wallArc_pi (L := M + 1) (by linarith) d (by linarith)

/-- ★★★ **The emission and the relay are far apart on the ring.** For every `k ≥ 100`, every
ring, and every `d` with `d · 2π/(M + 1) ≤ 3π/4`: the emission's sites are `d` hops from the
relay's. -/
theorem radar_emission_hopSeparated_relay {k : ℕ} (hk : 100 ≤ k) (M : ℕ) {d : ℕ}
    (hd : (d : ℝ) * (2 * Real.pi / ((M + 1 : ℕ) : ℝ)) ≤ 3 * Real.pi / 4) :
    HopSeparated (ringAdj (L := M + 1)) d (radarEvent k M .emission).region
      (radarEvent k M .relay).region := by
  obtain ⟨c_b₂, c_21, -, -, c_τ, c_δ, -, c_start, -, -⟩ := radar_family_gate_conditions hk M
  have h0 : 0 ≤ radarRateB k * radarTau k M := mul_nonneg (c_b₂.trans_le c_21).le c_τ
  refine radarEvent_hopSeparated_farWall k M c_δ.le .emission d ?_
  show |radarRateB k * radarTau k M| ≤ _
  rw [abs_of_nonneg h0]
  linarith

/-- ★★★ **Permitted against demonstrated, for the emission and the relay.** A carrier with any
index over the ring's sites moves by `exp (u S)`, `S` hopping along the ring. A kick `W`, the
identity off the emission's sites, at the flow time the emission's window opens, changes an
observable `D` on the relay's sites, read when the relay's window opens, by at most
`2 (2 ‖S‖ (t_bR − t_b))^d / d! · ‖D‖`, for every `d` with `d · 2π/(M + 1) ≤ 3π/4`. -/
theorem radar_emission_kick_response_le {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {k : ℕ} (hk : 100 ≤ k) (M : ℕ) {σ : n → ZMod (M + 1)} {S : Matrix n n ℂ}
    (hS : Sᴴ = -S) (hhop : HopsG (ringAdj (L := M + 1)) σ S) {d : ℕ}
    (hd : (d : ℝ) * (2 * Real.pi / ((M + 1 : ℕ) : ℝ)) ≤ 3 * Real.pi / 4)
    {D : Matrix n n ℂ} (hD : SiteSuppG σ (radarEvent k M .relay).region D)
    {W : Matrix.unitaryGroup n ℂ} (hW : IdOffG σ (radarEvent k M .emission).region W.val)
    {U₁ U : Matrix.unitaryGroup n ℂ}
    (hU : U.val = exp (((radarEvent k M .relay).time - (radarEvent k M .emission).time) • S))
    (p : GenArena n) :
    |arenaObs D (arenaKick U (arenaKick W (arenaKick U₁ p)))
        - arenaObs D (arenaKick U (arenaKick U₁ p))|
      ≤ 2 * ((2 * ‖S‖ * ((radarEvent k M .relay).time - (radarEvent k M .emission).time)) ^ d
        / d.factorial) * ‖D‖ :=
  FlowEvent.kick_response_le hS hhop (radarEventTime_le hk M).1
    (radar_emission_hopSeparated_relay hk M hd) hD hW hU p

end CSD.RecordLayer

end
