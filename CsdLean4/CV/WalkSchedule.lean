/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.ChainExchange

/-!
# Walk schedules: exact transfer along any route, with waiting stages

**Category:** 3-Local (CV; the network witness of the third operational-geometry brief).
BACKLOG #203 (out of #39).

#190 transferred an excitation along a path graph with the schedule that switches on edge
`(m, m+1)` during stage `m`. A network with several stations and several routes needs more: a route
may hop along any edge, and a station may hold the excitation for a while — a relay's delay, a
detector's response, a deliberate wait. This module builds the schedule of an arbitrary list of
**steps**, each a hop along one edge or a wait, and proves what it transmits along a legal walk.

* `Step L` — `hop a b` or `wait`; `Step.flow` — the edge flow of `ChainExchange.lean` on `(a, b)`, or
  nothing switched on; `walkSchedule J ħ w` — **the schedule of the list `w`**, stage `m` the flow of
  the `m`-th step, nothing after the list;
* `IsWalk k w` — every hop starts where the excitation is and moves it; `walkPos k w` — where the
  excitation is after the list; `hopCount w` — the number of hops;
* ★★★ `walk_transfer` — **exact transfer along a legal walk**: after `m` completed stages the
  excitation prepared at `k` is `(−i)^{hops}` times the excitation at the walk's position after its
  first `m` steps; `walkReadout` — at `m τ_hop` the readout at `j` is `1` exactly at that position;
* ★★ `isWalk_append`, `walkPos_append`, `hopCount_append`, `walk_transfer_append` — **routes
  compose**: a route followed by a wait followed by a route is a route, its length the sum, its
  arrival the second route's;
* ★★ `isWalk_cycles`, `walkPos_take_cycle` — **a closed walk repeated reads the same in
  every cycle**: at stage `j |W| + m` the excitation is where it was at stage `m`;
  `walkReadout_cycle`;
* ★ `isWalk_map`, `walkPos_map`, `hopCount_map`, `length_map` — **relabelling the stations
  relabels the walk and nothing else**: a re-description of the same transfers.

## Honest scope

* The schedule is a modelling input, as in #190: which edge is on in which stage is data, and every
  stage lasts one hop time `τ_hop`, so every travel time here is a whole number of hop times.
* One excitation and exact transfer: a route is the schedule's choice, not a race between paths.
  Comparing routes means comparing schedules.

References: `specs/BACKLOG.md` #203, #190, #39; `CV/ChainExchange.lean` (`edgeFlow_transfer`,
`Schedule`, `occAt`, `chainReadout_one`).
-/

@[expose] public section

open Matrix

namespace CSD.CV

variable {L : ℕ}

/-! ### Steps and walks -/

/-- A stage of a route: a hop along the edge `(a, b)`, or a wait with nothing switched on. -/
inductive Step (L : ℕ) where
  /-- Hop the excitation from site `a` to site `b`. -/
  | hop (a b : Fin L)
  /-- Hold: nothing is switched on for one stage. -/
  | wait

namespace Step

/-- Where the excitation is after the step, from `k`. -/
def next : Fin L → Step L → Fin L
  | _, hop _ b => b
  | k, wait => k

/-- Whether the step is a hop. -/
def isHop : Step L → Bool
  | hop _ _ => true
  | wait => false

/-- The flow switched on during the step. -/
noncomputable def flow (J ħ : ℝ) : Step L → FieldStructuredFlow L 2
  | hop a b => edgeFlow J ħ a b
  | wait => FieldStructuredFlow.off L 2

/-- Relabel the sites of a step. -/
def map (σ : Fin L ≃ Fin L) : Step L → Step L
  | hop a b => hop (σ a) (σ b)
  | wait => wait

end Step

/-- Where the excitation is after the list of steps, from `k`. -/
def walkPos (k : Fin L) (w : List (Step L)) : Fin L := w.foldl Step.next k

@[simp] theorem walkPos_nil (k : Fin L) : walkPos k ([] : List (Step L)) = k := rfl

@[simp] theorem walkPos_cons (k : Fin L) (s : Step L) (w : List (Step L)) :
    walkPos k (s :: w) = walkPos (s.next k) w := rfl

theorem walkPos_append (k : Fin L) (w₁ w₂ : List (Step L)) :
    walkPos k (w₁ ++ w₂) = walkPos (walkPos k w₁) w₂ := List.foldl_append

/-- The number of hops in a list of steps. -/
def hopCount (w : List (Step L)) : ℕ := w.countP Step.isHop

@[simp] theorem hopCount_nil : hopCount ([] : List (Step L)) = 0 := rfl

@[simp] theorem hopCount_cons_hop (a b : Fin L) (w : List (Step L)) :
    hopCount (Step.hop a b :: w) = hopCount w + 1 := by
  rw [hopCount, hopCount, List.countP_cons]
  rfl

@[simp] theorem hopCount_cons_wait (w : List (Step L)) :
    hopCount (Step.wait :: w) = hopCount w := by
  rw [hopCount, hopCount, List.countP_cons]
  rfl

theorem hopCount_append (w₁ w₂ : List (Step L)) :
    hopCount (w₁ ++ w₂) = hopCount w₁ + hopCount w₂ := List.countP_append

/-- **A legal walk from `k`**: every hop starts where the excitation is and moves it. -/
def IsWalk : Fin L → List (Step L) → Prop
  | _, [] => True
  | k, Step.hop a b :: w => a = k ∧ a ≠ b ∧ IsWalk b w
  | k, Step.wait :: w => IsWalk k w

@[simp] theorem isWalk_nil (k : Fin L) : IsWalk k ([] : List (Step L)) := trivial

theorem isWalk_cons_hop {k a b : Fin L} {w : List (Step L)} :
    IsWalk k (Step.hop a b :: w) ↔ a = k ∧ a ≠ b ∧ IsWalk b w := Iff.rfl

theorem isWalk_cons_wait {k : Fin L} {w : List (Step L)} :
    IsWalk k (Step.wait :: w) ↔ IsWalk k w := Iff.rfl

/-- ★ **Routes compose**: a concatenation is a legal walk iff the first part is, and the second part
is from where the first leaves the excitation. -/
theorem isWalk_append : ∀ (k : Fin L) (w₁ w₂ : List (Step L)),
    IsWalk k (w₁ ++ w₂) ↔ IsWalk k w₁ ∧ IsWalk (walkPos k w₁) w₂
  | k, [], w₂ => by simp
  | k, Step.hop a b :: w₁, w₂ => by
      rw [List.cons_append, isWalk_cons_hop, isWalk_cons_hop, isWalk_append b w₁ w₂, walkPos_cons]
      exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩, fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩⟩
  | k, Step.wait :: w₁, w₂ => by
      rw [List.cons_append, isWalk_cons_wait, isWalk_cons_wait, isWalk_append k w₁ w₂, walkPos_cons]
      rfl

/-- Waiting is a legal walk that leaves the excitation where it is, with no hops. -/
theorem isWalk_replicate_wait (k : Fin L) : ∀ n, IsWalk k (List.replicate n (Step.wait : Step L))
  | 0 => trivial
  | n + 1 => isWalk_replicate_wait k n

theorem walkPos_replicate_wait (k : Fin L) : ∀ n,
    walkPos k (List.replicate n (Step.wait : Step L)) = k
  | 0 => rfl
  | n + 1 => walkPos_replicate_wait k n

theorem hopCount_replicate_wait : ∀ n, hopCount (List.replicate n (Step.wait : Step L)) = 0
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, hopCount_cons_wait, hopCount_replicate_wait n]

/-! ### The schedule of a list of steps -/

/-- **The schedule of a list of steps**: stage `m` switches on the flow of the `m`-th step for one hop
time; after the list nothing is on. -/
noncomputable def walkSchedule (J ħ : ℝ) (w : List (Step L)) : Schedule L 2 where
  stage m := match w[m]? with
    | some s => s.flow J ħ
    | none => FieldStructuredFlow.off L 2
  τ := hopTime J ħ

theorem walkSchedule_τ (J ħ : ℝ) (w : List (Step L)) : (walkSchedule J ħ w).τ = hopTime J ħ := rfl

theorem walkSchedule_stage_cons_zero (J ħ : ℝ) (s : Step L) (w : List (Step L)) :
    (walkSchedule J ħ (s :: w)).stage 0 = s.flow J ħ := rfl

theorem walkSchedule_stage_cons_succ (J ħ : ℝ) (s : Step L) (w : List (Step L)) (m : ℕ) :
    (walkSchedule J ħ (s :: w)).stage (m + 1) = (walkSchedule J ħ w).stage m := rfl

/-- **Prepending a stage**: a schedule whose stages after the first are another schedule's stages
completes as that schedule after its own first stage. -/
theorem Schedule.completed_succ_of_shift {K N : ℕ} (s t : Schedule K N) (hτ : s.τ = t.τ)
    (h : ∀ m, s.stage (m + 1) = t.stage m) :
    ∀ m, s.completed (m + 1) = t.completed m * (s.stage 0).flow s.τ
  | 0 => by rw [Schedule.completed_succ, Schedule.completed_zero, Schedule.completed_zero, mul_one,
      one_mul]
  | m + 1 => by
      rw [Schedule.completed_succ, Schedule.completed_succ_of_shift s t hτ h m, h,
        Schedule.completed_succ t, hτ, mul_assoc]

theorem walkSchedule_completed_cons (J ħ : ℝ) (s : Step L) (w : List (Step L)) (m : ℕ) :
    (walkSchedule J ħ (s :: w)).completed (m + 1)
      = (walkSchedule J ħ w).completed m * (s.flow J ħ).flow (hopTime J ħ) :=
  Schedule.completed_succ_of_shift (walkSchedule J ħ (s :: w)) (walkSchedule J ħ w) rfl
    (walkSchedule_stage_cons_succ J ħ s w) m

/-- The flow of one step on the excitation at the step's start. -/
theorem toEuclideanLin_step_flow {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {k : Fin L} {s : Step L}
    {w : List (Step L)} (hw : IsWalk k (s :: w)) :
    Matrix.toEuclideanLin ((s.flow J ħ).flow (hopTime J ħ)).val (eVec (excAt k))
      = (-Complex.I) ^ (hopCount [s]) • eVec (excAt (s.next k)) := by
  cases s with
  | hop a b =>
      obtain ⟨rfl, hab, -⟩ := hw
      show Matrix.toEuclideanLin ((edgeFlow J ħ a b).flow (hopTime J ħ)).val (eVec (excAt a)) = _
      rw [edgeFlow_transfer hJ hħ hab]
      simp [hopCount, Step.isHop, Step.next]
  | wait =>
      show Matrix.toEuclideanLin ((FieldStructuredFlow.off L 2).flow (hopTime J ħ)).val
        (eVec (excAt k)) = _
      rw [FieldStructuredFlow.off_flow, OneMemClass.coe_one, toEuclideanLin_one_apply]
      simp [hopCount, Step.isHop, Step.next]

/-- ★★★ **Exact transfer along a legal walk**: after `m ≤ |w|` completed stages, the excitation
prepared at `k` is `(−i)^{h}` times the excitation at the walk's position after its first `m` steps,
`h` the number of hops among them. -/
theorem walk_transfer {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) :
    ∀ (w : List (Step L)) (k : Fin L), IsWalk k w → ∀ m ≤ w.length,
      Matrix.toEuclideanLin ((walkSchedule J ħ w).completed m).val (eVec (excAt k))
        = (-Complex.I) ^ (hopCount (w.take m)) • eVec (excAt (walkPos k (w.take m)))
  | [], k, _, m, hm => by
      obtain rfl : m = 0 := Nat.le_zero.1 hm
      rw [Schedule.completed_zero, OneMemClass.coe_one, toEuclideanLin_one_apply]
      simp
  | s :: w, k, hw, 0, _ => by
      rw [Schedule.completed_zero, OneMemClass.coe_one, toEuclideanLin_one_apply]
      simp
  | s :: w, k, hw, m + 1, hm => by
      have hw' : IsWalk (s.next k) w := by
        cases s with
        | hop a b => exact hw.2.2
        | wait => exact hw
      have hm' : m ≤ w.length := Nat.le_of_succ_le_succ hm
      rw [walkSchedule_completed_cons, Submonoid.coe_mul, toEuclideanLin_mul_apply,
        toEuclideanLin_step_flow hJ hħ hw, map_smul, walk_transfer hJ hħ w (s.next k) hw' m hm',
        smul_smul, ← pow_add, List.take_succ_cons, walkPos_cons]
      congr 2
      rw [show s :: w.take m = [s] ++ w.take m from rfl, hopCount_append, add_comm]

/-! ### Readouts -/

/-- The scheduled flow of a list of steps on the arena, from switch-on. -/
noncomputable def walkArenaFlow (J ħ : ℝ) (w : List (Step L)) (t : ℝ) (p : FieldArena L 2) :
    FieldArena L 2 :=
  arenaKick ((walkSchedule J ħ w).propagator t) p

/-- The arena point of an excitation at `k`. -/
noncomputable def excPoint (k : Fin L) : FieldArena L 2 :=
  Projectivization.mk ℂ (eVec (excAt k)) (eVec_ne_zero _)

/-- ★★ **The readout along a walk**: at `m τ_hop` (`m ≤ |w|`) the receiver at `j` reads `1` if the
walk has brought the excitation to `j` by its `m`-th step, `0` otherwise. -/
theorem walkReadout {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {w : List (Step L)} {k : Fin L}
    (hw : IsWalk k w) {m : ℕ} (hm : m ≤ w.length) (j : Fin L) :
    arenaObs (occAt j) (walkArenaFlow J ħ w (m * hopTime J ħ) (excPoint k))
      = if j = walkPos k (w.take m) then 1 else 0 := by
  have hst := Schedule.propagator_at_stage (walkSchedule J ħ w) (hopTime_pos hJ hħ) m
  rw [walkSchedule_τ] at hst
  rw [walkArenaFlow, excPoint, arenaKick_mk, occAt, arenaObs_single_mk, hst,
    walk_transfer hJ hħ w k hw m hm, norm_pow_neg_I_smul_eVec, one_pow, div_one, PiLp.smul_apply,
    smul_eq_mul, norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul]
  by_cases hj : j = walkPos k (w.take m)
  · rw [hj, eVec_apply_self, norm_one, one_pow, ite_eq_left rfl]
  · rw [eVec_apply_of_ne (fun h => hj (excAt_injective h)), norm_zero, ite_eq_right hj]
    norm_num

/-- **Arrival**: at the end of a legal walk the receiver at its end point reads `1`. -/
theorem walkReadout_arrival {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {w : List (Step L)} {k : Fin L}
    (hw : IsWalk k w) :
    arenaObs (occAt (walkPos k w)) (walkArenaFlow J ħ w (w.length * hopTime J ħ) (excPoint k)) = 1 := by
  rw [walkReadout hJ hħ hw le_rfl, List.take_length, ite_eq_left rfl]

/-! ### Routes compose -/

/-- ★★ **Composition, with a wait between**: a route, a wait of `ρ` stages, a route is a legal walk
when the second route starts where the first ends; its length, hops and arrival add up. -/
theorem walk_compose {k : Fin L} {w₁ w₂ : List (Step L)} (h₁ : IsWalk k w₁)
    (h₂ : IsWalk (walkPos k w₁) w₂) (ρ : ℕ) :
    IsWalk k (w₁ ++ List.replicate ρ Step.wait ++ w₂)
      ∧ (w₁ ++ List.replicate ρ Step.wait ++ w₂).length = w₁.length + ρ + w₂.length
      ∧ hopCount (w₁ ++ List.replicate ρ Step.wait ++ w₂) = hopCount w₁ + hopCount w₂
      ∧ walkPos k (w₁ ++ List.replicate ρ Step.wait ++ w₂) = walkPos (walkPos k w₁) w₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [isWalk_append, isWalk_append, walkPos_append, walkPos_replicate_wait]
    exact ⟨⟨h₁, isWalk_replicate_wait _ ρ⟩, h₂⟩
  · simp only [List.length_append, List.length_replicate]
  · rw [hopCount_append, hopCount_append, hopCount_replicate_wait, add_zero]
  · rw [walkPos_append, walkPos_append, walkPos_replicate_wait]

/-- ★★ **Transfer along a composed route, at its arrival**: the excitation reaches the second
route's end at stage `|w₁| + ρ + |w₂|` with phase `(−i)^{h₁ + h₂}`. -/
theorem walk_transfer_append {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {k : Fin L}
    {w₁ w₂ : List (Step L)} (h₁ : IsWalk k w₁) (h₂ : IsWalk (walkPos k w₁) w₂) (ρ : ℕ) :
    Matrix.toEuclideanLin ((walkSchedule J ħ (w₁ ++ List.replicate ρ Step.wait ++ w₂)).completed
        (w₁.length + ρ + w₂.length)).val (eVec (excAt k))
      = (-Complex.I) ^ (hopCount w₁ + hopCount w₂)
          • eVec (excAt (walkPos (walkPos k w₁) w₂)) := by
  obtain ⟨hw, hlen, hhop, hpos⟩ := walk_compose h₁ h₂ ρ
  rw [walk_transfer hJ hħ _ k hw _ hlen.ge, ← hlen, List.take_length, hhop, hpos]

/-! ### Repetition: every cycle reads the same -/

/-- A closed walk repeated `r` times. -/
def cycles (r : ℕ) (W : List (Step L)) : List (Step L) := (List.replicate r W).flatten

theorem cycles_succ (r : ℕ) (W : List (Step L)) : cycles (r + 1) W = W ++ cycles r W := by
  simp [cycles, List.replicate_succ]

theorem length_cycles (r : ℕ) (W : List (Step L)) : (cycles r W).length = r * W.length := by
  induction r with
  | zero => simp [cycles]
  | succ r ih => rw [cycles_succ, List.length_append, ih]; ring

/-- ★★ **A closed walk repeated is a legal walk** that returns to its start after every cycle. -/
theorem isWalk_cycles {k : Fin L} {W : List (Step L)} (hW : IsWalk k W) (hcl : walkPos k W = k) :
    ∀ r, IsWalk k (cycles r W) ∧ walkPos k (cycles r W) = k
  | 0 => ⟨trivial, rfl⟩
  | r + 1 => by
      obtain ⟨h1, h2⟩ := isWalk_cycles hW hcl r
      rw [cycles_succ, isWalk_append, walkPos_append, hcl]
      exact ⟨⟨hW, h1⟩, h2⟩

/-- The first `j |W| + m` steps of `r > j` cycles are `j` cycles followed by the first `m` steps. -/
theorem take_cycles {W : List (Step L)} {j r m : ℕ} (hjr : j < r) (hm : m ≤ W.length) :
    (cycles r W).take (j * W.length + m) = cycles j W ++ W.take m := by
  induction j generalizing r with
  | zero =>
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      rw [zero_mul, zero_add, cycles_succ, List.take_append_of_le_length hm]
      simp [cycles]
  | succ j ih =>
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      have hj : j < r' := by omega
      rw [cycles_succ, cycles_succ, show (j + 1) * W.length + m = W.length + (j * W.length + m) by
        ring, List.take_length_add_append, ih hj, List.append_assoc]

/-- ★★ **Every cycle reads the same**: at stage `j |W| + m` of `r > j` cycles the excitation is where
the single walk puts it at stage `m`. -/
theorem walkPos_take_cycle {k : Fin L} {W : List (Step L)} (hW : IsWalk k W)
    (hcl : walkPos k W = k) {j r m : ℕ} (hjr : j < r) (hm : m ≤ W.length) :
    walkPos k ((cycles r W).take (j * W.length + m)) = walkPos k (W.take m) := by
  rw [take_cycles hjr hm, walkPos_append, (isWalk_cycles hW hcl j).2]

/-- ★★ **Reproducibility of the readings**: in the `j`-th of `r` repetitions of a closed walk, the
receiver at every site reads at offset `m` what it read at offset `m` of the first cycle. -/
theorem walkReadout_cycle {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) {k : Fin L} {W : List (Step L)}
    (hW : IsWalk k W) (hcl : walkPos k W = k) {j r m : ℕ} (hjr : j < r) (hm : m ≤ W.length)
    (s : Fin L) :
    arenaObs (occAt s) (walkArenaFlow J ħ (cycles r W) ((j * W.length + m : ℕ) * hopTime J ħ)
        (excPoint k))
      = arenaObs (occAt s) (walkArenaFlow J ħ W (m * hopTime J ħ) (excPoint k)) := by
  have hlen : j * W.length + m ≤ (cycles r W).length := by
    rw [length_cycles]
    have : (j + 1) * W.length ≤ r * W.length := Nat.mul_le_mul_right _ hjr
    nlinarith
  rw [walkReadout hJ hħ (isWalk_cycles hW hcl r).1 hlen, walkReadout hJ hħ hW hm,
    walkPos_take_cycle hW hcl hjr hm]

/-! ### Re-description: relabelling the stations -/

theorem Step.next_map (σ : Fin L ≃ Fin L) (k : Fin L) (s : Step L) :
    (s.map σ).next (σ k) = σ (s.next k) := by
  cases s <;> rfl

theorem walkPos_map (σ : Fin L ≃ Fin L) : ∀ (k : Fin L) (w : List (Step L)),
    walkPos (σ k) (w.map (Step.map σ)) = σ (walkPos k w)
  | _, [] => rfl
  | k, s :: w => by rw [List.map_cons, walkPos_cons, Step.next_map, walkPos_map σ _ w, walkPos_cons]

theorem hopCount_map (σ : Fin L ≃ Fin L) : ∀ w : List (Step L),
    hopCount (w.map (Step.map σ)) = hopCount w
  | [] => rfl
  | Step.hop a b :: w => by
      rw [List.map_cons, show Step.map σ (Step.hop a b) = Step.hop (σ a) (σ b) from rfl,
        hopCount_cons_hop, hopCount_cons_hop, hopCount_map σ w]
  | Step.wait :: w => by
      rw [List.map_cons, show Step.map σ (Step.wait : Step L) = Step.wait from rfl,
        hopCount_cons_wait, hopCount_cons_wait, hopCount_map σ w]

/-- ★ **Relabelling preserves legality**: a walk from `k` relabels to a walk from `σ k`. -/
theorem isWalk_map (σ : Fin L ≃ Fin L) : ∀ (k : Fin L) (w : List (Step L)),
    IsWalk (σ k) (w.map (Step.map σ)) ↔ IsWalk k w
  | _, [] => Iff.rfl
  | k, Step.hop a b :: w => by
      rw [List.map_cons, show Step.map σ (Step.hop a b) = Step.hop (σ a) (σ b) from rfl,
        isWalk_cons_hop, isWalk_cons_hop, isWalk_map σ b w, σ.injective.eq_iff,
        σ.injective.ne_iff]
  | k, Step.wait :: w => by
      rw [List.map_cons, show Step.map σ (Step.wait : Step L) = Step.wait from rfl,
        isWalk_cons_wait, isWalk_cons_wait, isWalk_map σ k w]

theorem length_map_step (σ : Fin L ≃ Fin L) (w : List (Step L)) :
    (w.map (Step.map σ)).length = w.length := List.length_map _

/-- ★★★ **Walk schedules**, in one statement: exact transfer along a legal walk; composition with a
wait between; every cycle of a repeated closed walk reads the same; relabelling the stations
relabels the walk and preserves its length, hops and legality. -/
theorem walk_schedules {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) :
    (∀ (w : List (Step L)) (k : Fin L), IsWalk k w → ∀ m ≤ w.length,
        Matrix.toEuclideanLin ((walkSchedule J ħ w).completed m).val (eVec (excAt k))
          = (-Complex.I) ^ (hopCount (w.take m)) • eVec (excAt (walkPos k (w.take m))))
      ∧ (∀ (k : Fin L) (w₁ w₂ : List (Step L)), IsWalk k w₁ → IsWalk (walkPos k w₁) w₂ → ∀ ρ,
          IsWalk k (w₁ ++ List.replicate ρ Step.wait ++ w₂)
            ∧ (w₁ ++ List.replicate ρ Step.wait ++ w₂).length = w₁.length + ρ + w₂.length)
      ∧ (∀ (k : Fin L) (W : List (Step L)), IsWalk k W → walkPos k W = k → ∀ j r m, j < r →
          m ≤ W.length → walkPos k ((cycles r W).take (j * W.length + m)) = walkPos k (W.take m))
      ∧ (∀ (σ : Fin L ≃ Fin L) (k : Fin L) (w : List (Step L)),
          (IsWalk (σ k) (w.map (Step.map σ)) ↔ IsWalk k w)
            ∧ walkPos (σ k) (w.map (Step.map σ)) = σ (walkPos k w)
            ∧ hopCount (w.map (Step.map σ)) = hopCount w) :=
  ⟨walk_transfer hJ hħ, fun _ _ _ h₁ h₂ ρ => ⟨(walk_compose h₁ h₂ ρ).1, (walk_compose h₁ h₂ ρ).2.1⟩,
    fun _ _ hW hcl _ _ _ hjr hm => walkPos_take_cycle hW hcl hjr hm,
    fun σ k w => ⟨isWalk_map σ k w, walkPos_map σ k w, hopCount_map σ w⟩⟩

end CSD.CV

end
