/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.WalkSchedule

/-!
# Geometry across several paths: three stations, two routes

**Category:** 3-Local (CV; the third operational-geometry brief, §3). BACKLOG #203 (out of #39).

Radar separation between two stations is read off a round trip: the travel out, the far station's
response, the travel back, the near station's recording. Whether such separations form a geometry —
symmetric, and obeying the triangle inequality — is not automatic, and this file says exactly when.

**The general part** (`TravelData`): one-way travel times `travel a b` (in hop times), each station's
response delay `resp` and recording delay `recDelay`.

* `rawSep a b = (travel a b + resp b + travel b a + recDelay a)/2` — what a radar reads;
  `correctedSep a b = (travel a b + travel b a)/2` — the same with the known detector delays removed;
  ★ `rawSep_eq_correctedSep_add`;
* ★★ `correctedSep_comm` — **the corrected separation is always symmetric**, reciprocal or not: a
  round trip averages the two directions; ★★ `rawSep_comm_iff` — **the raw separation is symmetric
  exactly when the stations' net detector delays agree**, `resp a − recDelay a = resp b − recDelay b`;
* `RelayBound relay` — the travel times are those of the fastest available route, a relay through
  `b` costing `relay b`; ★★ `correctedSep_triangle` — **the triangle inequality holds up to the relay
  delay**, `D(a,c) ≤ D(a,b) + D(b,c) + relay b`; exact when relays cost nothing;
* ★ `correctedSep_eq_travel_of_reciprocal` — under reciprocity the corrected separation **is** the
  one-way travel time; ★★★ `correctedSep_metric` — **with no self-travel, positive travel between
  distinct stations and free relays, the corrected separation satisfies the metric axioms**;
* ★ `correctedSep_comap`, `rawSep_comap` — **re-describing the stations leaves every separation
  unchanged**.

**The witness** (`ThreeStation`): three stations, a direct route between every ordered pair (with
its own waiting stages — direction dependence), and a relay route through the third station (with
that station's relay delay), both realised as walk schedules (`CV/WalkSchedule.lean`).

* `directRoute`, `relayRoute`, `route` (the faster), ★★ `route_spec` — **the route is a legal walk
  arriving at its target after exactly `travel a c` hop times**; ★★ `route_arrival` — the receiver
  there reads `1`;
* ★★★ `relayBound` — **the operational travel times satisfy the relay bound**, so the triangle
  inequality up to the relay delay is a theorem about this network; `triangle_of_free_relays`,
  `metric_of_free_relays`;
* `roundTripWalk`, ★★ `roundTrip_spec` (a closed walk of length `rawRoundTrip`),
  ★★ `roundTrip_reception`, `roundTrip_return` — **the round trip passes the far station at
  `travel a c` and is back at `travel a c + resp c + travel c a`**; ★★★ `roundTrip_reproducible` —
  **repeated round trips read the same in every cycle**.

**Where it is not a metric**, as theorems with explicit networks:

* ★★ `rawSep_not_symmetric` — unequal net detector delays make the raw separation asymmetric;
* ★★ `fixedRoute_not_triangle` — the radar read along a fixed route (the direct one) violates the
  triangle inequality when the direct route is slow;
* ★★ `relayDelay_breaks_triangle` — a relay delay left uncorrected breaks the exact triangle
  inequality, by no more than that delay (`relayDelay_within_bound`).

## Honest scope

* Every travel time is a whole number of hop times, because every stage of a walk schedule lasts
  `τ_hop` (`CV/WalkSchedule.lean`); separations are in units of `τ_hop`. No universal `c`, no
  Lorentz invariance, no metric on a continuum: three stations and their travel-time table.
* "Fastest available route" is a property of the schedules offered (direct and through the third
  station), not a race; a network with more routes needs `RelayBound` re-proved for them.
* The detector delays are inputs here; #199–#204 derive them for the activated writes.

References: `specs/BACKLOG.md` #203, #190, #193, #187, #204, #39; `CV/WalkSchedule.lean`,
`CV/ChainExchange.lean`, `CV/RadarCoordinates.lean`.
-/

@[expose] public section

namespace CSD.CV

/-! ### Travel-time data and radar separations -/

/-- **Travel-time data** on a set of stations: one-way travel times in hop times, and each station's
response and recording delays. -/
structure TravelData (S : Type*) where
  /-- One-way travel time from `a` to `b`, in hop times. -/
  travel : S → S → ℕ
  /-- The response delay of a station receiving a signal before it answers. -/
  resp : S → ℕ
  /-- The recording delay of a station registering a returned signal. -/
  recDelay : S → ℕ

namespace TravelData

variable {S : Type*} (D : TravelData S)

/-- The raw round trip from `a` to `b` and back, as recorded at `a`. -/
def rawRoundTrip (a b : S) : ℕ := D.travel a b + D.resp b + D.travel b a + D.recDelay a

/-- **The raw radar separation**: half the recorded round trip. -/
noncomputable def rawSep (a b : S) : ℝ := (D.rawRoundTrip a b : ℝ) / 2

/-- **The corrected radar separation**: half the round trip with the known detector delays removed. -/
noncomputable def correctedSep (a b : S) : ℝ := ((D.travel a b + D.travel b a : ℕ) : ℝ) / 2

/-- ★ The raw separation is the corrected one plus half the two detector delays it contains. -/
theorem rawSep_eq_correctedSep_add (a b : S) :
    D.rawSep a b = D.correctedSep a b + ((D.resp b + D.recDelay a : ℕ) : ℝ) / 2 := by
  unfold rawSep correctedSep rawRoundTrip
  push_cast
  ring

theorem correctedSep_nonneg (a b : S) : 0 ≤ D.correctedSep a b := by
  unfold correctedSep
  positivity

/-- ★★ **The corrected separation is always symmetric**: the round trip averages the two directions,
whether or not they take the same time. -/
theorem correctedSep_comm (a b : S) : D.correctedSep a b = D.correctedSep b a := by
  unfold correctedSep
  rw [Nat.add_comm]

/-- ★★ **The raw separation is symmetric exactly when the net detector delays agree.** -/
theorem rawSep_comm_iff (a b : S) :
    D.rawSep a b = D.rawSep b a ↔ D.resp b + D.recDelay a = D.resp a + D.recDelay b := by
  unfold rawSep rawRoundTrip
  rw [div_left_inj' two_ne_zero, Nat.cast_inj]
  constructor <;> intro h <;> omega

theorem correctedSep_self {a : S} (h : D.travel a a = 0) : D.correctedSep a a = 0 := by
  unfold correctedSep
  rw [h]
  simp

theorem correctedSep_pos {a b : S} (h : 0 < D.travel a b) : 0 < D.correctedSep a b := by
  unfold correctedSep
  have : (0 : ℝ) < ((D.travel a b + D.travel b a : ℕ) : ℝ) := by exact_mod_cast (by omega)
  positivity

/-- ★ **Under reciprocity the corrected separation is the one-way travel time.** -/
theorem correctedSep_eq_travel_of_reciprocal {a b : S} (h : D.travel a b = D.travel b a) :
    D.correctedSep a b = D.travel a b := by
  unfold correctedSep
  rw [← h]
  push_cast
  ring

/-- **The relay bound**: no travel time exceeds a relay through any station `b`, at the relay cost
`relay b` — the travel times are those of the fastest available route. -/
def RelayBound (relay : S → ℕ) : Prop :=
  ∀ a b c, D.travel a c ≤ D.travel a b + relay b + D.travel b c

/-- ★★ **The triangle inequality, up to the relay delay**: `D(a,c) ≤ D(a,b) + D(b,c) + relay b`. -/
theorem correctedSep_triangle {relay : S → ℕ} (h : D.RelayBound relay) (a b c : S) :
    D.correctedSep a c ≤ D.correctedSep a b + D.correctedSep b c + relay b := by
  have h1 := h a b c
  have h2 := h c b a
  have hn : D.travel a c + D.travel c a
      ≤ (D.travel a b + D.travel b a) + (D.travel b c + D.travel c b) + 2 * relay b := by omega
  have hr : ((D.travel a c + D.travel c a : ℕ) : ℝ)
      ≤ ((D.travel a b + D.travel b a : ℕ) : ℝ) + ((D.travel b c + D.travel c b : ℕ) : ℝ)
        + 2 * (relay b : ℝ) := by exact_mod_cast hn
  unfold correctedSep
  linarith

/-- With free relays the triangle inequality is exact. -/
theorem correctedSep_triangle_of_free (h : D.RelayBound fun _ => 0) (a b c : S) :
    D.correctedSep a c ≤ D.correctedSep a b + D.correctedSep b c := by
  have := D.correctedSep_triangle h a b c
  simpa using this

/-- ★★★ **When the corrected separation is a metric**: no self-travel, positive travel between
distinct stations, and free relays give the metric axioms. -/
theorem correctedSep_metric (h0 : ∀ a, D.travel a a = 0)
    (hpos : ∀ a b, a ≠ b → 0 < D.travel a b) (hrel : D.RelayBound fun _ => 0) :
    (∀ a b, D.correctedSep a b = 0 ↔ a = b)
      ∧ (∀ a b, D.correctedSep a b = D.correctedSep b a)
      ∧ (∀ a b c, D.correctedSep a c ≤ D.correctedSep a b + D.correctedSep b c) := by
  refine ⟨fun a b => ⟨fun h => ?_, fun h => h ▸ D.correctedSep_self (h0 a)⟩, D.correctedSep_comm,
    D.correctedSep_triangle_of_free hrel⟩
  by_contra hab
  exact (D.correctedSep_pos (hpos a b hab)).ne' h

/-- Re-describe the stations through a relabelling. -/
def comap {S' : Type*} (σ : S' ≃ S) : TravelData S' :=
  ⟨fun a b => D.travel (σ a) (σ b), fun a => D.resp (σ a), fun a => D.recDelay (σ a)⟩

/-- ★ **Re-describing the stations leaves the corrected separation unchanged.** -/
theorem correctedSep_comap {S' : Type*} (σ : S' ≃ S) (a b : S') :
    (D.comap σ).correctedSep a b = D.correctedSep (σ a) (σ b) := rfl

/-- **Re-describing the stations leaves the raw separation unchanged.** -/
theorem rawSep_comap {S' : Type*} (σ : S' ≃ S) (a b : S') :
    (D.comap σ).rawSep a b = D.rawSep (σ a) (σ b) := rfl

end TravelData

/-! ### Three stations, two routes -/

/-- The third of three stations. -/
def third : Fin 3 → Fin 3 → Fin 3
  | 0, 1 => 2
  | 1, 0 => 2
  | 0, 2 => 1
  | 2, 0 => 1
  | 1, 2 => 0
  | 2, 1 => 0
  | a, _ => a

theorem third_ne_left {a c : Fin 3} (h : a ≠ c) : third a c ≠ a := by
  fin_cases a <;> fin_cases c <;> simp_all [third]

theorem third_ne_right {a c : Fin 3} (h : a ≠ c) : third a c ≠ c := by
  fin_cases a <;> fin_cases c <;> simp_all [third]

/-- **A three-station network**: the waiting stages before each direct hop (direction-dependent),
each station's relay delay, response delay and recording delay. -/
structure ThreeStation where
  /-- Waiting stages before the direct hop from `a` to `c`. -/
  dir : Fin 3 → Fin 3 → ℕ
  /-- Waiting stages at a station relaying a signal. -/
  relay : Fin 3 → ℕ
  /-- A station's response delay. -/
  resp : Fin 3 → ℕ
  /-- A station's recording delay. -/
  recDelay : Fin 3 → ℕ

namespace ThreeStation

variable (N : ThreeStation)

/-- The direct route from `a` to `c`: wait, then hop. -/
def directRoute (a c : Fin 3) : List (Step 3) :=
  List.replicate (N.dir a c) Step.wait ++ [Step.hop a c]

/-- The direct route's length. -/
def directLen (a c : Fin 3) : ℕ := N.dir a c + 1

/-- The relay route from `a` to `c`: the direct route to the third station, its relay delay, the
direct route on. -/
def relayRoute (a c : Fin 3) : List (Step 3) :=
  N.directRoute a (third a c) ++ List.replicate (N.relay (third a c)) Step.wait
    ++ N.directRoute (third a c) c

/-- The relay route's length. -/
def relayLen (a c : Fin 3) : ℕ :=
  N.directLen a (third a c) + N.relay (third a c) + N.directLen (third a c) c

/-- **The operational travel time**: the faster of the two routes. -/
def travel (a c : Fin 3) : ℕ := if a = c then 0 else min (N.directLen a c) (N.relayLen a c)

/-- **The route the schedule offers**: the faster of the two. -/
def route (a c : Fin 3) : List (Step 3) :=
  if a = c then [] else if N.directLen a c ≤ N.relayLen a c then N.directRoute a c
  else N.relayRoute a c

theorem directRoute_spec {a c : Fin 3} (h : a ≠ c) :
    IsWalk a (N.directRoute a c) ∧ walkPos a (N.directRoute a c) = c
      ∧ (N.directRoute a c).length = N.directLen a c := by
  refine ⟨?_, ?_, ?_⟩
  · rw [directRoute, isWalk_append, walkPos_replicate_wait]
    exact ⟨isWalk_replicate_wait a _, ⟨rfl, h, trivial⟩⟩
  · rw [directRoute, walkPos_append, walkPos_replicate_wait]
    rfl
  · simp [directRoute, directLen]

theorem relayRoute_spec {a c : Fin 3} (h : a ≠ c) :
    IsWalk a (N.relayRoute a c) ∧ walkPos a (N.relayRoute a c) = c
      ∧ (N.relayRoute a c).length = N.relayLen a c := by
  obtain ⟨h1, p1, l1⟩ := N.directRoute_spec (Ne.symm (third_ne_left h))
  obtain ⟨h2, p2, l2⟩ := N.directRoute_spec (third_ne_right h)
  obtain ⟨hw, hlen, -, hpos⟩ := walk_compose h1 (by rw [p1]; exact h2) (N.relay (third a c))
  refine ⟨hw, ?_, ?_⟩
  · rw [relayRoute, hpos, p1, p2]
  · rw [relayRoute, hlen, l1, l2, relayLen]

/-- ★★ **The offered route is a legal walk arriving at its target after `travel a c` hop times.** -/
theorem route_spec (a c : Fin 3) :
    IsWalk a (N.route a c) ∧ walkPos a (N.route a c) = c ∧ (N.route a c).length = N.travel a c := by
  by_cases hac : a = c
  · subst hac
    simp [route, travel]
  · by_cases hd : N.directLen a c ≤ N.relayLen a c
    · obtain ⟨h1, h2, h3⟩ := N.directRoute_spec hac
      simp only [route, travel, hac, hd, ite_false, ite_true, min_eq_left hd]
      exact ⟨h1, h2, h3⟩
    · obtain ⟨h1, h2, h3⟩ := N.relayRoute_spec hac
      simp only [route, travel, hac, hd, ite_false, min_eq_right (show N.relayLen a c ≤ N.directLen a c by omega)]
      exact ⟨h1, h2, h3⟩

/-- ★★ **Arrival**: after `travel a c` hop times the receiver at `c` reads `1`. -/
theorem route_arrival {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (a c : Fin 3) :
    arenaObs (occAt c) (walkArenaFlow J ħ (N.route a c) (N.travel a c * hopTime J ħ) (excPoint a))
      = 1 := by
  obtain ⟨hw, hp, hl⟩ := N.route_spec a c
  have h := walkReadout_arrival hJ hħ hw
  rw [hp, hl] at h
  exact h

/-- The travel-time data of the network. -/
def toTravelData : TravelData (Fin 3) := ⟨N.travel, N.resp, N.recDelay⟩

theorem travel_self (a : Fin 3) : N.travel a a = 0 := by simp [travel]

theorem travel_pos {a c : Fin 3} (h : a ≠ c) : 0 < N.travel a c := by
  simp only [travel, h, ite_false, directLen, relayLen]
  omega

/-- ★★★ **The operational travel times satisfy the relay bound**: no travel time exceeds a relay
through any station at that station's relay delay. -/
theorem relayBound : N.toTravelData.RelayBound N.relay := by
  intro a b c
  show N.travel a c ≤ N.travel a b + N.relay b + N.travel b c
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [travel, relayLen, directLen, third] <;> omega

/-- **With free relays the triangle inequality is exact** on this network. -/
theorem triangle_of_free_relays (h : ∀ b, N.relay b = 0) (a b c : Fin 3) :
    N.toTravelData.correctedSep a c
      ≤ N.toTravelData.correctedSep a b + N.toTravelData.correctedSep b c := by
  have := N.toTravelData.correctedSep_triangle N.relayBound a b c
  rw [h b] at this
  simpa using this

/-- ★★★ **With free relays the corrected separation of the three-station network is a metric.** -/
theorem metric_of_free_relays (h : ∀ b, N.relay b = 0) :
    (∀ a b, N.toTravelData.correctedSep a b = 0 ↔ a = b)
      ∧ (∀ a b, N.toTravelData.correctedSep a b = N.toTravelData.correctedSep b a)
      ∧ (∀ a b c, N.toTravelData.correctedSep a c
          ≤ N.toTravelData.correctedSep a b + N.toTravelData.correctedSep b c) := by
  refine N.toTravelData.correctedSep_metric N.travel_self (fun a b => N.travel_pos) ?_
  have hb := N.relayBound
  intro a b c
  have := hb a b c
  rw [h b] at this
  exact this

/-! ### Round trips and reproducibility -/

/-- **The round trip** from `a` to `c` and back: the route out, `c`'s response, the route back, `a`'s
recording. -/
def roundTripWalk (a c : Fin 3) : List (Step 3) :=
  N.route a c ++ (List.replicate (N.resp c) Step.wait
    ++ (N.route c a ++ List.replicate (N.recDelay a) Step.wait))

/-- ★★ **The round trip is a closed legal walk of length `rawRoundTrip`.** -/
theorem roundTrip_spec (a c : Fin 3) :
    IsWalk a (N.roundTripWalk a c) ∧ walkPos a (N.roundTripWalk a c) = a
      ∧ (N.roundTripWalk a c).length = N.toTravelData.rawRoundTrip a c := by
  obtain ⟨h1, p1, l1⟩ := N.route_spec a c
  obtain ⟨h2, p2, l2⟩ := N.route_spec c a
  refine ⟨?_, ?_, ?_⟩
  · rw [roundTripWalk, isWalk_append, isWalk_append, isWalk_append, p1, walkPos_replicate_wait, p2]
    exact ⟨h1, isWalk_replicate_wait c _, h2, isWalk_replicate_wait a _⟩
  · rw [roundTripWalk, walkPos_append, p1, walkPos_append, walkPos_replicate_wait, walkPos_append, p2,
      walkPos_replicate_wait]
  · simp only [roundTripWalk, List.length_append, List.length_replicate, l1, l2,
      TravelData.rawRoundTrip, toTravelData]
    ring

/-- ★★ **Reception**: after `travel a c` hop times the round trip is at the far station. -/
theorem roundTrip_reception (a c : Fin 3) :
    walkPos a ((N.roundTripWalk a c).take (N.travel a c)) = c := by
  obtain ⟨-, p1, l1⟩ := N.route_spec a c
  rw [roundTripWalk, ← l1, List.take_left' rfl, p1]

/-- ★★ **Return**: after `travel a c + resp c + travel c a` hop times it is back at `a`, before `a`'s
recording delay. -/
theorem roundTrip_return (a c : Fin 3) :
    walkPos a ((N.roundTripWalk a c).take (N.travel a c + N.resp c + N.travel c a)) = a := by
  obtain ⟨-, p1, l1⟩ := N.route_spec a c
  obtain ⟨-, p2, l2⟩ := N.route_spec c a
  have hsplit : (N.roundTripWalk a c).take (N.travel a c + N.resp c + N.travel c a)
      = N.route a c ++ (List.replicate (N.resp c) Step.wait ++ N.route c a) := by
    rw [roundTripWalk, show N.travel a c + N.resp c + N.travel c a
        = (N.route a c).length + ((List.replicate (N.resp c) (Step.wait : Step 3)).length
          + (N.route c a).length) by rw [l1, l2, List.length_replicate]; ring,
      List.take_length_add_append, List.take_length_add_append, List.take_left' rfl]
  rw [hsplit, walkPos_append, p1, walkPos_append, walkPos_replicate_wait, p2]

/-- ★★★ **Repeated round trips read the same in every cycle**: in the `j`-th of `r` repetitions, at
offset `m`, every receiver reads what it read at offset `m` of the first. -/
theorem roundTrip_reproducible {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (a c : Fin 3) {j r m : ℕ}
    (hjr : j < r) (hm : m ≤ (N.roundTripWalk a c).length) (s : Fin 3) :
    arenaObs (occAt s) (walkArenaFlow J ħ (cycles r (N.roundTripWalk a c))
        ((j * (N.roundTripWalk a c).length + m : ℕ) * hopTime J ħ) (excPoint a))
      = arenaObs (occAt s) (walkArenaFlow J ħ (N.roundTripWalk a c) (m * hopTime J ħ)
          (excPoint a)) := by
  obtain ⟨hw, hp, -⟩ := N.roundTrip_spec a c
  exact walkReadout_cycle hJ hħ hw hp hjr hm s

end ThreeStation

/-! ### Where it is not a metric -/

/-- A network with free relays and no waiting, where station `0` alone takes two stages to respond. -/
def slowResponder : ThreeStation := ⟨fun _ _ => 0, fun _ => 0, ![2, 0, 0], fun _ => 0⟩

/-- ★★ **Unequal net detector delays make the raw separation asymmetric.** -/
theorem rawSep_not_symmetric :
    slowResponder.toTravelData.rawSep 0 1 ≠ slowResponder.toTravelData.rawSep 1 0 := by
  rw [Ne, TravelData.rawSep_comm_iff]
  simp [slowResponder, ThreeStation.toTravelData]

/-- A network whose direct route between `0` and `2` waits four stages; everything else is
immediate and relays are free. -/
def slowDirect : ThreeStation :=
  ⟨fun a c => if (a = 0 ∧ c = 2) ∨ (a = 2 ∧ c = 0) then 4 else 0, fun _ => 0, fun _ => 0,
    fun _ => 0⟩

/-- **The radar read along a fixed route**: always the direct one. -/
def ThreeStation.fixedData (N : ThreeStation) : TravelData (Fin 3) :=
  ⟨fun a c => if a = c then 0 else N.directLen a c, N.resp, N.recDelay⟩

/-- ★★ **A fixed-route radar violates the triangle inequality**: on `slowDirect` the direct route
reads `5` between `0` and `2`, while `0 → 1` and `1 → 2` read `1` each. The operational (fastest
route) separation on the same network is a metric (`ThreeStation.metric_of_free_relays`). -/
theorem fixedRoute_not_triangle :
    slowDirect.fixedData.correctedSep 0 1 + slowDirect.fixedData.correctedSep 1 2
      < slowDirect.fixedData.correctedSep 0 2 := by
  simp only [TravelData.correctedSep, ThreeStation.fixedData, ThreeStation.directLen, slowDirect]
  norm_num

/-- A network whose direct route between `0` and `2` waits nine stages and whose relay at `1` costs
three. -/
def slowRelay : ThreeStation :=
  ⟨fun a c => if (a = 0 ∧ c = 2) ∨ (a = 2 ∧ c = 0) then 9 else 0, ![0, 3, 0], fun _ => 0,
    fun _ => 0⟩

/-- ★★ **An uncorrected relay delay breaks the exact triangle inequality**: on `slowRelay` the
fastest route from `0` to `2` goes through `1` and reads `5`, while `0 → 1` and `1 → 2` read `1`
each. -/
theorem relayDelay_breaks_triangle :
    slowRelay.toTravelData.correctedSep 0 1 + slowRelay.toTravelData.correctedSep 1 2
      < slowRelay.toTravelData.correctedSep 0 2 := by
  simp only [TravelData.correctedSep, ThreeStation.toTravelData, ThreeStation.travel,
    ThreeStation.directLen, ThreeStation.relayLen, slowRelay, third]
  norm_num

/-- **…by no more than the relay delay**: the bound `D(0,2) ≤ D(0,1) + D(1,2) + relay 1` holds. -/
theorem relayDelay_within_bound :
    slowRelay.toTravelData.correctedSep 0 2
      ≤ slowRelay.toTravelData.correctedSep 0 1 + slowRelay.toTravelData.correctedSep 1 2
        + slowRelay.relay 1 :=
  slowRelay.toTravelData.correctedSep_triangle slowRelay.relayBound 0 1 2

/-! ### The package -/

/-- ★★★ **Geometry across several paths.** On any three-station network realised by walk schedules:
the offered route arrives after the operational travel time; round trips are closed walks of the raw
round-trip length, read the same in every cycle, and pass the far station at the travel time; the
corrected separation is symmetric, obeys the triangle inequality up to the relay delay, and is a
metric when relays are free; the raw separation is symmetric exactly when the net detector delays
agree; re-describing the stations changes no separation. And it is not a metric in general: raw
separations can be asymmetric, a fixed-route radar can violate the triangle inequality, and an
uncorrected relay delay breaks it. -/
theorem three_station_geometry (N : ThreeStation) {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) :
    (∀ a c, IsWalk a (N.route a c) ∧ walkPos a (N.route a c) = c
        ∧ (N.route a c).length = N.travel a c)
      ∧ (∀ a c, arenaObs (occAt c)
          (walkArenaFlow J ħ (N.route a c) (N.travel a c * hopTime J ħ) (excPoint a)) = 1)
      ∧ (∀ a c, IsWalk a (N.roundTripWalk a c) ∧ walkPos a (N.roundTripWalk a c) = a
          ∧ (N.roundTripWalk a c).length = N.toTravelData.rawRoundTrip a c)
      ∧ (∀ a c, walkPos a ((N.roundTripWalk a c).take (N.travel a c)) = c)
      ∧ (∀ a c, N.toTravelData.correctedSep a c = N.toTravelData.correctedSep c a)
      ∧ (∀ a b c, N.toTravelData.correctedSep a c
          ≤ N.toTravelData.correctedSep a b + N.toTravelData.correctedSep b c + N.relay b)
      ∧ (∀ a c, N.toTravelData.rawSep a c = N.toTravelData.rawSep c a
          ↔ N.resp c + N.recDelay a = N.resp a + N.recDelay c)
      ∧ (∀ σ : Fin 3 ≃ Fin 3, ∀ a c,
          (N.toTravelData.comap σ).correctedSep a c = N.toTravelData.correctedSep (σ a) (σ c))
      ∧ slowResponder.toTravelData.rawSep 0 1 ≠ slowResponder.toTravelData.rawSep 1 0
      ∧ slowDirect.fixedData.correctedSep 0 1 + slowDirect.fixedData.correctedSep 1 2
          < slowDirect.fixedData.correctedSep 0 2
      ∧ slowRelay.toTravelData.correctedSep 0 1 + slowRelay.toTravelData.correctedSep 1 2
          < slowRelay.toTravelData.correctedSep 0 2 :=
  ⟨N.route_spec, N.route_arrival hJ hħ, N.roundTrip_spec, N.roundTrip_reception,
    N.toTravelData.correctedSep_comm, N.toTravelData.correctedSep_triangle N.relayBound,
    N.toTravelData.rawSep_comm_iff, N.toTravelData.correctedSep_comap, rawSep_not_symmetric,
    fixedRoute_not_triangle, relayDelay_breaks_triangle⟩

end CSD.CV

end
