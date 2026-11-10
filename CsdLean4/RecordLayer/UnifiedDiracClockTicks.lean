/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedDiracClock
public import CsdLean4.RecordLayer.DiracPointerRecord
public import CsdLean4.RecordLayer.DiracRateTicks

/-!
# Ticks of the clock inside the common Hamiltonian of `Σ_*`: records, a count, operational time

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 7-SigmaLayer (the record layer). BACKLOG #358 — milestone **M4, part B** of the
author's programme "From `Σ` to physical spacetime". Part A (#357,
`RecordLayer/UnifiedDiracClock.lean`) put the two-level clock in the joint energy and proved that
the pointer's displacement follows the clock's hand. Its statements were in the flow parameter
and gave no record. This part reads the same pointer of the same flow through a threshold. It
adds no dynamics, no coupling and no degree of freedom.

**The tick.** The pointer of `clockPointerFlow` swings: it follows `A (1 − cos R t)` within a
stated error (`abs_clockPointerShift_sub_swing_le`). Read against the ready arc and the displayed
arc of the M2 readout (`tickReady`, `tickDisplay`), the history rests at every whole turn of the
phase and displays around every half turn (`isSwing_clockPointerFlow`). A **tick** is one passage
from resting to displaying. Each tick is a record write in the sense of `IsRecordWrite`
(`IsSwing.isRecordWrite`) and an `ActualOccurrence` whose `evolve` field is the joint flow
(`clockTickRecord`). Every tick record of a run reads the one history
(`clockTickRecord_history`).

**The count.** `HasTicks rest disp γ T n` says the history `γ` has `n` successive passages by
`T`, and `IsTickCount` that `n` is the largest such number. The count is a fact about the order
of events: it is unchanged when the history is reparametrised, with the terminal event carried
along (`isTickCount_comp_orderIso`). It holds no value of the flow parameter. For a swing at the
rate `R` the count at `T` satisfies `|2π N − R T| ≤ 2π` (`IsSwing.abs_tickCount_sub_le`).

**Operational time.** `clockOpTime μ₀ μ₁ N = 2π N/(μ₁ − μ₀)`: one period of the clock at rest
for each tick. It is a function of the count and of the two rest energies. For the device of
`dirac_device`, prepared a quarter turn early (`clock_tick_device`):

  `|2π N/(μ₁ − μ₀) − √(1 − (v/c)²) T| ≤ 2π/(μ₁ − μ₀) + ((μ₁ − μ₀)/E₀) T`.

The first term is the detector's resolution, one tick. The second is the finite splitting of the
two levels. The localisation error `ε = deviceDrift` does not enter this inequality. It enters
the hypotheses under which the history is a swing: through `clockSwingErr`, the pointer's error
against the ideal swing, and through the phase of the prepared coherence.

**The count is not held by the state.** Each tick record is erased within its turn
(`IsSwing.notMem_disp_of_cos_eq_one`). No measurable real function of the arena state gains at
least one along a step of the flow almost everywhere (`not_ae_count_advances_clockPointerFlow`).
The count of a run is a function of its tick records and of no state at one time.

## Ticks of a history

For any history `γ : ℝ → X` and any two sets. Nothing here uses a flow.

* `HasTicks`, `hasTicks_zero`, `HasTicks.mono_count`, `HasTicks.mono_time`;
* ★★ `hasTicks_comp_orderIso` — reparametrisation carries ticks to ticks;
* `IsTickCount`, `IsTickCount.unique`, ★ `isTickCount_comp_orderIso`.

## A swing

For any history read against a phase `R t`. Nothing here uses a flow.

* `cos_le_max_cos`, `IsSwing`, ★ `IsSwing.hasTicks`, ★★ `IsSwing.sub_one_mul_le`;
* ★★★ `IsSwing.abs_tickCount_sub_le` — the count against the phase, within one turn;
* ★ `IsSwing.exists_tickCount`, `IsSwing.notMem_disp_of_mem_rest`;
* ★★ `IsSwing.isRecordWrite` — each tick is a record write;
* ★ `IsSwing.notMem_disp_of_cos_eq_one` — each record is erased at the next whole turn;
* `clockOpTime`, ★★ `IsSwing.abs_clockOpTime_sub_le`,
  ★★★ `IsSwing.abs_clockOpTime_sub_dilated_le` — operational time against the relativistic
  clock law.

## The readout on the clock arena

* `tickReady`, `measurableSet_tickReady`, `tickDisplay`, `measurableSet_tickDisplay`,
  `tickShown`, `measurable_tickShown`, `tickShown_eq_true_iff`;
* `pshift_mem_readyArc_iff`, `pshift_mem_displayArc_iff`;
* ★★ `isSwing_of_abs_shift_sub_le` — a pointer within `δ` of `A (1 − cos R t)`, started inside
  the ready arc by more than `δ` and reaching the displayed arc, is a swing.

## The clock's pointer is a swing

* `clockPointerFlow_snd`, `clockSwingAmp`, `clockSwingErr`, `clockSwingErr_nonneg`;
* ★★ `abs_clockPointerShift_sub_swing_le` — the hand of part A as a swing, with its error;
* ★★★ `isSwing_clockPointerFlow` — **the tick law**: the readout history of the joint flow is a
  swing at the device's rate, under four inequalities on the start, the amplitude and the error.

## One mode: the exact tick

* `deviceNorm_devicePacket`, `devicePacket_single_ne_zero`,
  `deviceCoherence_devicePacket_zero_im`, `le_deviceCoherence_devicePacket_zero_re`,
  `deviceCoherence_single_im`, `deviceCoherence_single_re_pos`, `exp_I_neg_mul_quarter`,
  `deviceCoherence_single_quarter`;
* ★★★ `isSwing_clockPointerFlow_single` — one mode on a fibre where the profile vanishes: no
  error term, every horizon;
* ★★ `isSwing_clockPointerFlow_train` — the instance: the hypotheses are met.

## A localised packet: the tick law with its three errors

* ★★ `norm_deviceCoherence_shift_sub_le` — the coherence of the packet from any start, within
  `|s| deviceDrift` of a uniform turn;
* ★★★ `clock_tick_device` — the packet of `dirac_device`: the prepared coherence, the swing, and
  operational time against `√(1 − (v/c)²) T`.

## Each tick as an actual occurrence of the joint flow

* `IsSwing.mem_rest_turn`, `continuous_clockPointerFlow`, `measurable_clockPointerFlow`,
  `clockPointerEvolve`, `clockPointerEvolve_self`, `clockPointerEvolve_comp`,
  `measurable_clockPointerEvolve`;
* ★★★ `clockTickRecord`, ★★ `clockTickRecord_history`.

## No function of the arena state holds the count

* ★★ `ae_comp_eq_of_ae_le_comp`, ★★ `not_ae_add_one_le_comp` — for any map preserving a finite
  measure;
* ★★★ `not_ae_count_advances_clockPointerFlow`.

## Honest scope

* **One tick per full turn.** The unit is `2π/(μ₁ − μ₀)`, and the resolution is one unit. The
  rectified register of #271 counted half turns, in a stated law. This pointer is not rectified.
* **What is exact and what is bounded.** The combinatorics of ticks and the record write of a
  swing are exact. `|2π N − R T| ≤ 2π` and the two operational-time inequalities are upper
  bounds, and they are not shown to be attained. The tick law for the flow is exact, with no
  error term and for every horizon, for one mode on the fibres where `f(θ₂) = 0`
  (`isSwing_clockPointerFlow_single`). That set of fibres is null for a generic profile.
* **Elsewhere the swing is a hypothesis met up to a horizon.** For `f(θ₂) ≠ 0` or a packet of
  positive width, `isSwing_clockPointerFlow` and `clock_tick_device` take four inequalities
  between the start, the amplitude `A` and the error `δ = clockSwingErr`. The error grows as
  `T²`, so the inequalities hold up to a horizon at most. No packet of positive width and no
  fibre with `f(θ₂) ≠ 0` is shown to meet them. Only the one-mode instance is exhibited.
* **Flow times that stay (UA-7).** The horizon `T` at which the count is taken, and the start,
  write interval and window of each tick record, are values of the flow parameter. They locate
  the events. The count and `clockOpTime` do not use them. In the operational-time inequalities
  `T` is the quantity the count is compared with. No theorem selects the terminal event from
  inside the model.
* **The count is in the history, not in a register.** Operational time is a function of the
  number of tick records of a run. No degree of freedom of the arena holds that number, and by
  `not_ae_count_advances_clockPointerFlow` no real function of the state can. The statement is
  about real-valued functions. A register that holds the count modulo a fixed number, an angle,
  is not excluded by it and is not built here.
* **The obstruction does not use the Hamiltonian.** `not_ae_add_one_le_comp` holds for every
  map preserving a finite measure. By test 4 of the contract's §6 it is conditional on the
  preserved measure (UA-2) and passes no gate.
* **The generic layer does not use the flow.** The sections on ticks and on swings are about any
  history. By test 3 of §6 they are tools. The flow enters at `isSwing_clockPointerFlow`.
* **Which fibres tick is not a clock datum.** The amplitude `clockSwingAmp` and the thresholds
  depend on the hidden angle `θ₂`, on `g` and on the pointer's start. The rate, and so the
  count, do not.
* **The preparation.** The device is prepared a quarter turn early, so that the pointer rests at
  whole turns of the phase. The pointer starts in the ready arc. Both are apparatus input (UA-4).
* **A global readout.** `levelSwap` acts at every site. Each tick record has the whole ring as
  its site. It is not a detector at a place.
* **One pointer.** The pointer of #349 is coupled to a site projector on another arena. No
  theorem has a position record and a tick record in one run. One flow carries both pointers in
  `RecordLayer/UnifiedTwoPointer.lean` (#359), and no record is read there. Both records are
  read off that flow in `RecordLayer/UnifiedClockSiteRecords.lean` (#360).
* **The dilation is the free device's.** The clause on `√(1 − (v/c)²)` is
  `abs_clockRate_div_sub_le`, for the level splitting of the uncoupled device. It is reused.
* **What is assumed** (`specs/unified-record-spacetime-plan.md`, Register 1): the arena (UA-1),
  the flow parameter (UA-7), the propagation law (UA-8), the clock's level and its coupling
  (UA-12). The profile, the coupling strength, the readout arcs, the pointer's start and the
  device's prepared state are apparatus input (UA-4). The measure (UA-2) enters only in the last
  section. No probability of a tick is stated, and UA-6 is not used.

References: `specs/BACKLOG.md` #358, #357, #353, #352, #349, #271, #262, #249;
`specs/future-work.md`; `specs/unified-record-spacetime-plan.md` (UO-14; UA-2, UA-4, UA-7,
UA-12; UD-58 to UD-65); `RecordLayer/UnifiedDiracClock.lean` (`clockPointerFlow_apply`,
`abs_clockPointerShift_sub_hand_le`, `kMuL_map_clockPointerFlow`);
`RecordLayer/RecordOccurrence.lean` (`IsRecordWrite`, `ActualOccurrence`);
`RecordLayer/DiracPointerRecord.lean` (`diracPointerRecord`, the pattern followed);
`RecordLayer/ShearWitness.lean` (`readyArc`, `pshift`); `RecordLayer/ActivatedWrite.lean`
(`displayArc`); `RecordLayer/DiracRateTicks.lean` (`levelWeight_mul_rate_le`,
`deviceProp_devicePacket_shift`); `RecordLayer/DiracDeviceTicks.lean` (`deviceDrift`);
`CV/DiracDevice.lean` (`dirac_device`, `device_observables`, `levelWeight_unitAmp_bounds`);
`CV/DiracClockChain.lean` (`abs_clockRate_div_sub_le`, `levelClockRate`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ## Ticks of a history: a count that is a fact about the order of events -/

section Ticks

variable {X : Type*} {rest disp : Set X} {γ : ℝ → X}

/-- **A history has `n` ticks by the parameter value `T`**: there are `n` successive passages
from the resting set to the displaying set, each strictly after the one before, all inside
`[0, T]`. Only the order of the events enters (`hasTicks_comp_orderIso`). -/
def HasTicks (rest disp : Set X) (γ : ℝ → X) (T : ℝ) (n : ℕ) : Prop :=
  ∃ a b : ℕ → ℝ,
    (∀ i, i < n → 0 ≤ a i ∧ a i < b i ∧ b i ≤ T ∧ γ (a i) ∈ rest ∧ γ (b i) ∈ disp)
      ∧ ∀ i, i + 1 < n → b i < a (i + 1)

/-- Every history has zero ticks. -/
theorem hasTicks_zero (rest disp : Set X) (γ : ℝ → X) (T : ℝ) : HasTicks rest disp γ T 0 :=
  ⟨fun _ => 0, fun _ => 0, fun i h => absurd h (Nat.not_lt_zero i),
    fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- A history with `n` ticks has every smaller number of ticks. -/
theorem HasTicks.mono_count {T : ℝ} {m n : ℕ} (h : HasTicks rest disp γ T n) (hmn : m ≤ n) :
    HasTicks rest disp γ T m := by
  obtain ⟨a, b, h1, h2⟩ := h
  exact ⟨a, b, fun i hi => h1 i (hi.trans_le hmn), fun i hi => h2 i (hi.trans_le hmn)⟩

/-- Ticks are kept as the history gets longer. -/
theorem HasTicks.mono_time {T T' : ℝ} {n : ℕ} (h : HasTicks rest disp γ T n) (hT : T ≤ T') :
    HasTicks rest disp γ T' n := by
  obtain ⟨a, b, h1, h2⟩ := h
  refine ⟨a, b, fun i hi => ?_, h2⟩
  obtain ⟨ha, hab, hb, hr, hd⟩ := h1 i hi
  exact ⟨ha, hab, hb.trans hT, hr, hd⟩

/-- ★★ **The ticks do not see the parameter.** Relabelling the parameter by any increasing
bijection of the line that fixes the start leaves the ticks as they were: a history has `n`
ticks by `T` in the new label exactly when it has `n` ticks by the relabelled `T`. So the
number of ticks before an event is a fact about the order of events and holds no value of the
flow parameter. -/
theorem hasTicks_comp_orderIso (σ : ℝ ≃o ℝ) (h0 : σ 0 = 0) (T : ℝ) (n : ℕ) :
    HasTicks rest disp (γ ∘ σ) T n ↔ HasTicks rest disp γ (σ T) n := by
  constructor
  · rintro ⟨a, b, h1, h2⟩
    refine ⟨fun i => σ (a i), fun i => σ (b i), fun i hi => ?_, fun i hi => ?_⟩
    · obtain ⟨ha, hab, hb, hr, hd⟩ := h1 i hi
      have ha' := σ.monotone ha
      rw [h0] at ha'
      exact ⟨ha', σ.strictMono hab, σ.monotone hb, hr, hd⟩
    · exact σ.strictMono (h2 i hi)
  · rintro ⟨a, b, h1, h2⟩
    have h0' : σ.symm 0 = 0 := σ.symm_apply_eq.2 h0.symm
    refine ⟨fun i => σ.symm (a i), fun i => σ.symm (b i), fun i hi => ?_, fun i hi => ?_⟩
    · obtain ⟨ha, hab, hb, hr, hd⟩ := h1 i hi
      have ha' := σ.symm.monotone ha
      rw [h0'] at ha'
      refine ⟨ha', σ.symm.strictMono hab, σ.symm_apply_le.2 hb, ?_, ?_⟩
      · show γ (σ (σ.symm (a i))) ∈ rest
        rw [σ.apply_symm_apply]
        exact hr
      · show γ (σ (σ.symm (b i))) ∈ disp
        rw [σ.apply_symm_apply]
        exact hd
    · exact σ.symm.strictMono (h2 i hi)

/-- **The count of a history at `T`**: it has `N` ticks by `T` and does not have `N + 1`. -/
def IsTickCount (rest disp : Set X) (γ : ℝ → X) (T : ℝ) (N : ℕ) : Prop :=
  HasTicks rest disp γ T N ∧ ¬ HasTicks rest disp γ T (N + 1)

/-- The count of a history is unique. -/
theorem IsTickCount.unique {T : ℝ} {N N' : ℕ} (h : IsTickCount rest disp γ T N)
    (h' : IsTickCount rest disp γ T N') : N = N' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact h.2 (h'.1.mono_count hlt)
  · exact h'.2 (h.1.mono_count hlt)

/-- ★ **The count does not see the parameter**: `hasTicks_comp_orderIso` for the count. -/
theorem isTickCount_comp_orderIso (σ : ℝ ≃o ℝ) (h0 : σ 0 = 0) (T : ℝ) (N : ℕ) :
    IsTickCount rest disp (γ ∘ σ) T N ↔ IsTickCount rest disp γ (σ T) N := by
  unfold IsTickCount
  rw [hasTicks_comp_orderIso σ h0, hasTicks_comp_orderIso σ h0]

end Ticks

/-! ## A swing: the count against the phase -/

section Swing

variable {X : Type*} {rest disp : Set X} {γ : ℝ → X}

/-- Between two points of one turn the cosine is at most its larger end value. -/
theorem cos_le_max_cos {x y z : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hz : z ≤ 2 * Real.pi) : Real.cos y ≤ max (Real.cos x) (Real.cos z) := by
  rcases le_or_gt y Real.pi with hy | hy
  · exact le_max_of_le_left (Real.cos_le_cos_of_nonneg_of_le_pi hx hy hxy)
  · refine le_max_of_le_right ?_
    rw [← Real.cos_two_pi_sub y, ← Real.cos_two_pi_sub z]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)

/-- **A swing history** up to the horizon `T`: a history read against a phase `R t`, resting
where the phase is a whole number of turns, displaying wherever the cosine of the phase is below
`d`, and separated by the threshold `c`: resting only where the cosine is at least `c`,
displaying only where it is below `c`. Nothing is said about the history between `d` and `c`. -/
structure IsSwing (rest disp : Set X) (γ : ℝ → X) (R c d T : ℝ) : Prop where
  /-- The phase advances. -/
  rate_pos : 0 < R
  /-- The displaying threshold is reached at the half turn. -/
  neg_one_lt : -1 < d
  /-- The displaying threshold is below the separating one. -/
  thresh_le : d ≤ c
  /-- The history rests at every whole turn. -/
  rest_of_cos : ∀ t, 0 ≤ t → t ≤ T → Real.cos (R * t) = 1 → γ t ∈ rest
  /-- The history displays wherever the cosine is below `d`. -/
  disp_of_cos : ∀ t, 0 ≤ t → t ≤ T → Real.cos (R * t) < d → γ t ∈ disp
  /-- The history rests only where the cosine is at least `c`. -/
  le_cos_of_rest : ∀ t, 0 ≤ t → t ≤ T → γ t ∈ rest → c ≤ Real.cos (R * t)
  /-- The history displays only where the cosine is below `c`. -/
  cos_lt_of_disp : ∀ t, 0 ≤ t → t ≤ T → γ t ∈ disp → Real.cos (R * t) < c

/-- ★ **A swing ticks once in every turn it completes half of**: if the phase has reached
`2π (n − 1) + π` by `T`, the history has `n` ticks by `T`. -/
theorem IsSwing.hasTicks {R c d T : ℝ} (h : IsSwing rest disp γ R c d T) {n : ℕ}
    (hn : ((n : ℝ) - 1) * (2 * Real.pi) + Real.pi ≤ R * T) : HasTicks rest disp γ T n := by
  have hR := h.rate_pos
  have hπ := Real.pi_pos
  refine ⟨fun i => (i : ℝ) * (2 * Real.pi) / R,
    fun i => ((i : ℝ) * (2 * Real.pi) + Real.pi) / R, fun i hi => ?_, fun i _ => ?_⟩
  · have hin : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
    have ha : (0 : ℝ) ≤ (i : ℝ) * (2 * Real.pi) / R := by positivity
    have hab : (i : ℝ) * (2 * Real.pi) / R < ((i : ℝ) * (2 * Real.pi) + Real.pi) / R :=
      div_lt_div_of_pos_right (by linarith) hR
    have hb : ((i : ℝ) * (2 * Real.pi) + Real.pi) / R ≤ T := by
      rw [div_le_iff₀ hR]
      nlinarith [mul_le_mul_of_nonneg_right hin (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    have ea : R * ((i : ℝ) * (2 * Real.pi) / R) = (i : ℝ) * (2 * Real.pi) := by field_simp
    have eb : R * (((i : ℝ) * (2 * Real.pi) + Real.pi) / R)
        = (i : ℝ) * (2 * Real.pi) + Real.pi := by field_simp
    refine ⟨ha, hab, hb, h.rest_of_cos _ ha (hab.le.trans hb) ?_,
      h.disp_of_cos _ (ha.trans hab.le) hb ?_⟩
    · rw [ea]
      exact Real.cos_nat_mul_two_pi i
    · rw [eb, Real.cos_nat_mul_two_pi_add_pi]
      exact h.neg_one_lt
  · show ((i : ℝ) * (2 * Real.pi) + Real.pi) / R < ((i + 1 : ℕ) : ℝ) * (2 * Real.pi) / R
    push_cast
    exact div_lt_div_of_pos_right (by linarith) hR

/-- ★★ **A swing ticks at most once a turn**: a swing history with `n` ticks by `T` has turned
its phase through at least `n − 1` whole turns. Between two displays there is a rest, and within
one turn the cosine cannot be below the threshold, then at least the threshold, then below it
again. -/
theorem IsSwing.sub_one_mul_le {R c d T : ℝ} (h : IsSwing rest disp γ R c d T) (hT : 0 ≤ T)
    {n : ℕ} (hn : HasTicks rest disp γ T n) : ((n : ℝ) - 1) * (2 * Real.pi) ≤ R * T := by
  have hR := h.rate_pos
  have hπ := Real.pi_pos
  obtain ⟨a, b, h1, h2⟩ := hn
  have key : ∀ i, i < n → (i : ℝ) * (2 * Real.pi) ≤ R * b i := by
    intro i
    induction i with
    | zero =>
      intro hi
      obtain ⟨ha, hab, -, -, -⟩ := h1 0 hi
      have : 0 ≤ R * b 0 := mul_nonneg hR.le (ha.trans hab.le)
      simpa using this
    | succ i ih =>
      intro hi
      have hi' : i < n := Nat.lt_of_succ_lt hi
      have hI := ih hi'
      obtain ⟨ha0, hab0, hb0, -, hd0⟩ := h1 i hi'
      obtain ⟨ha1, hab1, hb1, hr1, hd1⟩ := h1 (i + 1) hi
      have hba := h2 i hi
      by_contra hlt
      rw [not_le] at hlt
      push_cast at hlt
      have hk1 : (⌊R * b i / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) ≤ R * b i := by
        have := Int.floor_le (R * b i / (2 * Real.pi))
        rwa [le_div_iff₀ (by positivity)] at this
      have hik : (i : ℝ) ≤ (⌊R * b i / (2 * Real.pi)⌋ : ℝ) := by
        have : (i : ℤ) ≤ ⌊R * b i / (2 * Real.pi)⌋ :=
          Int.le_floor.2 (by rw [Int.cast_natCast, le_div_iff₀ (by positivity)]; exact hI)
        exact_mod_cast this
      have hx := h.cos_lt_of_disp (b i) (ha0.trans hab0.le) hb0 hd0
      have hy := h.le_cos_of_rest (a (i + 1)) ha1 (hab1.le.trans hb1) hr1
      have hz := h.cos_lt_of_disp (b (i + 1)) (ha1.trans hab1.le) hb1 hd1
      have hRab : R * b i < R * a (i + 1) := mul_lt_mul_of_pos_left hba hR
      have hRab1 : R * a (i + 1) < R * b (i + 1) := mul_lt_mul_of_pos_left hab1 hR
      have hmax := cos_le_max_cos
        (x := R * b i - (⌊R * b i / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi))
        (y := R * a (i + 1) - (⌊R * b i / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi))
        (z := R * b (i + 1) - (⌊R * b i / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi))
        (by linarith) (by linarith) (by linarith)
        (by nlinarith [mul_le_mul_of_nonneg_right hik (by positivity : (0 : ℝ) ≤ 2 * Real.pi)])
      rw [Real.cos_sub_int_mul_two_pi, Real.cos_sub_int_mul_two_pi,
        Real.cos_sub_int_mul_two_pi] at hmax
      exact absurd (hy.trans hmax) (not_le.2 (max_lt hx hz))
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have : 0 ≤ R * T := mul_nonneg hR.le hT
    rw [Nat.cast_zero]
    linarith
  · obtain ⟨-, -, hb, -, -⟩ := h1 (n - 1) (Nat.sub_lt hpos one_pos)
    have hk := key (n - 1) (Nat.sub_lt hpos one_pos)
    rw [Nat.cast_sub (show 1 ≤ n from hpos), Nat.cast_one] at hk
    exact hk.trans (mul_le_mul_of_nonneg_left hb hR.le)

/-- ★★★ **The count of a swing is the phase, within one turn**: a swing history whose count at
`T` is `N` has `|2π N − R T| ≤ 2π`. The error is one tick: the count is a whole number. -/
theorem IsSwing.abs_tickCount_sub_le {R c d T : ℝ} (h : IsSwing rest disp γ R c d T)
    (hT : 0 ≤ T) {N : ℕ} (hN : IsTickCount rest disp γ T N) :
    |(N : ℝ) * (2 * Real.pi) - R * T| ≤ 2 * Real.pi := by
  have hπ := Real.pi_pos
  have h1 := h.sub_one_mul_le hT hN.1
  have h2 : R * T < (N : ℝ) * (2 * Real.pi) + Real.pi := by
    by_contra hge
    rw [not_lt] at hge
    exact hN.2 (h.hasTicks (by push_cast; linarith))
  rw [abs_le]
  constructor <;> linarith

/-- ★ **A swing has a count**: at every `T ≥ 0` there is a (unique, `IsTickCount.unique`)
number of ticks. -/
theorem IsSwing.exists_tickCount {R c d T : ℝ} (h : IsSwing rest disp γ R c d T)
    (hT : 0 ≤ T) : ∃ N, IsTickCount rest disp γ T N := by
  by_contra hno
  have hall : ∀ n, HasTicks rest disp γ T n := by
    intro n
    induction n with
    | zero => exact hasTicks_zero rest disp γ T
    | succ n ih =>
      by_contra hn
      exact hno ⟨n, ih, hn⟩
  have hπ := Real.pi_pos
  obtain ⟨n, hn⟩ := exists_nat_gt (R * T / (2 * Real.pi) + 1)
  have hb := h.sub_one_mul_le hT (hall n)
  have : R * T / (2 * Real.pi) + 1 < R * T / (2 * Real.pi) + 1 := by
    refine hn.trans_le ?_
    rw [← sub_le_iff_le_add, le_div_iff₀ (by positivity)]
    exact hb
  exact lt_irrefl _ this

/-- A swing history rests and displays at no common time. -/
theorem IsSwing.notMem_disp_of_mem_rest {R c d T : ℝ} (h : IsSwing rest disp γ R c d T)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (hr : γ t ∈ rest) : γ t ∉ disp := fun hd =>
  absurd (h.le_cos_of_rest t ht0 htT hr) (not_le.2 (h.cos_lt_of_disp t ht0 htT hd))

/-- ★★ **Each tick of a swing is a record write.** In turn `k` the readout history does not
display from the whole turn `2πk` until the phase `2πk + arccos c`, and displays through the
window of phases `[2πk + arccos d', 2πk + 2π − arccos d']` around the half turn, for every `d'`
below the displaying threshold. The start, the write interval and the window are those of
`IsRecordWrite`, in the parameter of the history. -/
theorem IsSwing.isRecordWrite {R c d T : ℝ} (h : IsSwing rest disp γ R c d T) {hist : ℝ → Bool}
    (hhist : ∀ t, hist t = true ↔ γ t ∈ disp) (k : ℕ) {d' : ℝ} (hd'1 : -1 ≤ d') (hd' : d' < d)
    (hk : ((k : ℝ) * (2 * Real.pi) + (2 * Real.pi - Real.arccos d')) / R ≤ T) :
    IsRecordWrite hist ((k : ℝ) * (2 * Real.pi) / R)
      (((k : ℝ) * (2 * Real.pi) + Real.arccos c) / R)
      (((k : ℝ) * (2 * Real.pi) + Real.arccos d') / R)
      (2 * (Real.pi - Real.arccos d') / R) true := by
  have hR := h.rate_pos
  have hπ := Real.pi_pos
  have hk0 : (0 : ℝ) ≤ (k : ℝ) * (2 * Real.pi) := by positivity
  have hac := Real.arccos_nonneg c
  have had := Real.arccos_nonneg d'
  have hadπ := Real.arccos_le_pi d'
  have hacd : Real.arccos c ≤ Real.arccos d' :=
    Real.arccos_le_arccos (hd'.le.trans h.thresh_le)
  have hT : 0 ≤ T := (div_nonneg (by linarith) hR.le).trans hk
  have hc1 : c ≤ 1 := by
    have h1 := h.le_cos_of_rest 0 le_rfl hT (h.rest_of_cos 0 le_rfl hT (by simp))
    simpa using h1
  have hcm1 : -1 ≤ c := (hd'1.trans hd'.le).trans h.thresh_le
  have hd'le1 : d' ≤ 1 := (hd'.le.trans h.thresh_le).trans hc1
  have hend : ((k : ℝ) * (2 * Real.pi) + Real.arccos d') / R
      + 2 * (Real.pi - Real.arccos d') / R
      = ((k : ℝ) * (2 * Real.pi) + (2 * Real.pi - Real.arccos d')) / R := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact div_le_div_of_nonneg_right (by linarith) hR.le
  · exact div_le_div_of_nonneg_right (by linarith) hR.le
  · exact div_nonneg (by linarith) hR.le
  · intro t ht0 ht1 hv
    have ht : 0 ≤ t := (div_nonneg hk0 hR.le).trans ht0
    have htT : t ≤ T :=
      ht1.le.trans ((div_le_div_of_nonneg_right (by linarith) hR.le).trans hk)
    rw [div_le_iff₀ hR] at ht0
    rw [lt_div_iff₀ hR] at ht1
    have hcos := h.cos_lt_of_disp t ht htT ((hhist t).1 hv)
    have hge : c ≤ Real.cos (R * t) :=
      calc c = Real.cos (Real.arccos c) := (Real.cos_arccos hcm1 hc1).symm
        _ ≤ Real.cos (R * t - (k : ℝ) * (2 * Real.pi)) :=
          Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (Real.arccos_le_pi c) (by linarith)
        _ = Real.cos (R * t) := Real.cos_sub_nat_mul_two_pi _ _
    exact absurd hge (not_le.2 hcos)
  · intro t ht1 ht2
    rw [hend] at ht2
    have ht : 0 ≤ t := (div_nonneg (by linarith) hR.le).trans ht1
    have htT := ht2.trans hk
    rw [div_le_iff₀ hR] at ht1
    rw [le_div_iff₀ hR] at ht2
    refine (hhist t).2 (h.disp_of_cos t ht htT (lt_of_le_of_lt ?_ hd'))
    rw [← Real.cos_sub_nat_mul_two_pi (R * t) k]
    rcases le_or_gt (R * t - (k : ℝ) * (2 * Real.pi)) Real.pi with hθ | hθ
    · calc Real.cos (R * t - (k : ℝ) * (2 * Real.pi)) ≤ Real.cos (Real.arccos d') :=
            Real.cos_le_cos_of_nonneg_of_le_pi had hθ (by linarith)
        _ = d' := Real.cos_arccos hd'1 hd'le1
    · rw [← Real.cos_two_pi_sub]
      calc Real.cos (2 * Real.pi - (R * t - (k : ℝ) * (2 * Real.pi)))
            ≤ Real.cos (Real.arccos d') :=
            Real.cos_le_cos_of_nonneg_of_le_pi had (by linarith) (by linarith)
        _ = d' := Real.cos_arccos hd'1 hd'le1

/-- ★ **Each record of a swing is erased**: at every whole turn the history rests, so it does
not display. A tick record lasts less than one turn. -/
theorem IsSwing.notMem_disp_of_cos_eq_one {R c d T : ℝ} (h : IsSwing rest disp γ R c d T)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (hcos : Real.cos (R * t) = 1) : γ t ∉ disp :=
  h.notMem_disp_of_mem_rest ht0 htT (h.rest_of_cos t ht0 htT hcos)

/-! ### Operational time: the count against the rest splitting -/

/-- **The operational time of `N` ticks**: `2π N / (μ₁ − μ₀)`, one period of the clock at rest
for each tick. It is a function of the count and of the two rest energies, and of nothing
else. -/
noncomputable def clockOpTime (μ₀ μ₁ : ℝ) (N : ℕ) : ℝ := (N : ℝ) * (2 * Real.pi) / (μ₁ - μ₀)

/-- ★★ **Operational time against the rate, with the detector's resolution**: for a swing at the
rate `R` whose count at `T` is `N`, the operational time is within one rest period
`2π/(μ₁ − μ₀)` of `(R/(μ₁ − μ₀)) T`. The error is the resolution of a readout that counts whole
turns. -/
theorem IsSwing.abs_clockOpTime_sub_le {μ₀ μ₁ R c d T : ℝ} (h : IsSwing rest disp γ R c d T)
    (h01 : μ₀ < μ₁) (hT : 0 ≤ T) {N : ℕ} (hN : IsTickCount rest disp γ T N) :
    |clockOpTime μ₀ μ₁ N - R / (μ₁ - μ₀) * T| ≤ 2 * Real.pi / (μ₁ - μ₀) := by
  have hΔ : 0 < μ₁ - μ₀ := sub_pos.2 h01
  have e : clockOpTime μ₀ μ₁ N - R / (μ₁ - μ₀) * T
      = ((N : ℝ) * (2 * Real.pi) - R * T) / (μ₁ - μ₀) := by
    unfold clockOpTime
    ring
  rw [e, abs_div, abs_of_pos hΔ]
  exact div_le_div_of_nonneg_right (h.abs_tickCount_sub_le hT hN) hΔ.le

/-- ★★★ **Operational time against the relativistic clock law.** For a swing at the level
splitting `E₁ − E₀` of the momentum scale `s`, whose count at `T` is `N`:

`|2π N/(μ₁ − μ₀) − √(1 − (v/c)²) T| ≤ 2π/(μ₁ − μ₀) + ((μ₁ − μ₀)/E₀) T`.

The first term is the detector's resolution (one tick), the second the finite splitting of the
two levels (`abs_clockRate_div_sub_le`, ~~#249~~). `T` is the flow parameter of the event the
count is taken at: it is the quantity compared with, and the count does not hold it
(`isTickCount_comp_orderIso`). -/
theorem IsSwing.abs_clockOpTime_sub_dilated_le {c μ₀ μ₁ s κ d T : ℝ}
    (h : IsSwing rest disp γ (levelClockRate μ₀ μ₁ s) κ d T) (hc : c ≠ 0) (h0 : 0 < μ₀)
    (h01 : μ₀ < μ₁) (hT : 0 ≤ T) {N : ℕ} (hN : IsTickCount rest disp γ T N) :
    |clockOpTime μ₀ μ₁ N - Real.sqrt (1 - (vRel c μ₀ s / c) ^ 2) * T|
      ≤ 2 * Real.pi / (μ₁ - μ₀) + (μ₁ - μ₀) / dispE μ₀ s * T := by
  have h1 := h.abs_clockOpTime_sub_le h01 hT hN
  have h2 := abs_clockRate_div_sub_le hc h0 h01 s
  have h3 : |(levelClockRate μ₀ μ₁ s / (μ₁ - μ₀) - Real.sqrt (1 - (vRel c μ₀ s / c) ^ 2)) * T|
      ≤ (μ₁ - μ₀) / dispE μ₀ s * T := by
    rw [abs_mul, abs_of_nonneg hT]
    exact mul_le_mul_of_nonneg_right h2 hT
  have e : clockOpTime μ₀ μ₁ N - Real.sqrt (1 - (vRel c μ₀ s / c) ^ 2) * T
      = (clockOpTime μ₀ μ₁ N - levelClockRate μ₀ μ₁ s / (μ₁ - μ₀) * T)
        + (levelClockRate μ₀ μ₁ s / (μ₁ - μ₀) - Real.sqrt (1 - (vRel c μ₀ s / c) ^ 2)) * T := by
    ring
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add h1 h3)

end Swing

/-! ## The readout on the clock arena -/

section Readout

variable (M : ℕ)

/-- **The resting set** on the clock arena: the pointer is in its ready arc. -/
noncomputable def tickReady : Set (KSigma (4 * M + 3 + 1)) := {x | x.2 ∈ readyArc 2}

/-- The resting set is measurable. -/
theorem measurableSet_tickReady : MeasurableSet (tickReady M) :=
  measurable_snd (measurableSet_readyArc (K := 2))

/-- **The displaying set** on the clock arena: the pointer is in its displayed arc. -/
noncomputable def tickDisplay : Set (KSigma (4 * M + 3 + 1)) := {x | x.2 ∈ displayArc}

/-- The displaying set is measurable. -/
theorem measurableSet_tickDisplay : MeasurableSet (tickDisplay M) :=
  measurable_snd measurableSet_displayArc

open Classical in
/-- **The tick readout**: whether the pointer is in its displayed arc. A function of the pointer
angle `θ₁` alone. -/
noncomputable def tickShown (x : KSigma (4 * M + 3 + 1)) : Bool :=
  if x.2 ∈ displayArc then true else false

/-- The tick readout is measurable. -/
theorem measurable_tickShown : Measurable (tickShown M) := by
  unfold tickShown
  exact Measurable.ite (measurable_snd measurableSet_displayArc) measurable_const measurable_const

/-- The readout is `true` exactly on the displaying set. -/
theorem tickShown_eq_true_iff (x : KSigma (4 * M + 3 + 1)) :
    tickShown M x = true ↔ x ∈ tickDisplay M := by
  unfold tickShown tickDisplay
  simp

variable {M}

/-- A pointer turned without wrapping is in the ready arc exactly when it is within `1/6`. -/
theorem pshift_mem_readyArc_iff {q : KTorus} {a : ℝ} (h0 : 0 < rep q.1 + a)
    (h1 : rep q.1 + a ≤ 1) : pshift a q ∈ readyArc 2 ↔ rep q.1 + a ≤ 1 / 6 := by
  have e := rep_pshift_of_mem q a ⟨h0, h1⟩
  show rep (pshift a q).1 ∈ Ioc (0 : ℝ) (shearWidth 2) ↔ _
  rw [shearWidth_two, e]
  exact ⟨fun h => h.2, fun h => ⟨h0, h⟩⟩

/-- A pointer turned without wrapping, to at most `5/6`, is in the displayed arc exactly when it
is beyond `1/3`. -/
theorem pshift_mem_displayArc_iff {q : KTorus} {a : ℝ} (h0 : 0 < rep q.1 + a)
    (h1 : rep q.1 + a ≤ 5 / 6) : pshift a q ∈ displayArc ↔ 1 / 3 < rep q.1 + a := by
  have e := rep_pshift_of_mem q a ⟨h0, by linarith⟩
  show rep (pshift a q).1 ∈ Ioc (2 * shearWidth 2) (1 - shearWidth 2) ↔ _
  rw [shearWidth_two, e]
  constructor
  · intro h
    have := h.1
    linarith
  · intro h
    exact ⟨by linarith, by linarith⟩

/-- ★★ **A pointer that follows `A (1 − cos R t)` within `δ` is a swing.** For a history on the
clock arena whose pointer pair is the start `q` turned by `σ t`, with
`|σ t − A (1 − cos R t)| ≤ δ` up to `T`, a start inside the ready arc by more than `δ`
(`δ < θ₁ ≤ 1/6 − δ`) and a swing that reaches the displayed arc and stays in it
(`1/3 < θ₁ + 2A − δ`, `θ₁ + 2A + δ ≤ 5/6`): the history is a swing at the rate `R`, with the
separating threshold `1 − (1/3 − θ₁ − δ)/A` and the displaying threshold
`1 − (1/3 − θ₁ + δ)/A`. -/
theorem isSwing_of_abs_shift_sub_le {γ : ℝ → KSigma (4 * M + 3 + 1)} {q : KTorus} {σ : ℝ → ℝ}
    {R A δ T : ℝ} (hR : 0 < R) (hA : 0 < A) (hδ : 0 ≤ δ)
    (hγ : ∀ t, 0 ≤ t → t ≤ T → (γ t).2 = pshift (σ t) q)
    (hσ : ∀ t, 0 ≤ t → t ≤ T → |σ t - A * (1 - Real.cos (R * t))| ≤ δ)
    (h₁ : δ < rep q.1) (h₂ : rep q.1 + δ ≤ 1 / 6) (h₃ : 1 / 3 < rep q.1 + 2 * A - δ)
    (h₄ : rep q.1 + 2 * A + δ ≤ 5 / 6) :
    IsSwing (tickReady M) (tickDisplay M) γ R (1 - (1 / 3 - rep q.1 - δ) / A)
      (1 - (1 / 3 - rep q.1 + δ) / A) T := by
  have key : ∀ t, 0 ≤ t → t ≤ T → (0 < rep q.1 + σ t ∧ rep q.1 + σ t ≤ 5 / 6)
      ∧ (σ t - A * (1 - Real.cos (R * t)) ≤ δ ∧ -δ ≤ σ t - A * (1 - Real.cos (R * t))) := by
    intro t ht0 htT
    have hs := abs_le.1 (hσ t ht0 htT)
    have hc1 := Real.cos_le_one (R * t)
    have hc2 := Real.neg_one_le_cos (R * t)
    have hlo : 0 ≤ A * (1 - Real.cos (R * t)) := mul_nonneg hA.le (by linarith)
    have hhi : A * (1 - Real.cos (R * t)) ≤ A * 2 := mul_le_mul_of_nonneg_left (by linarith) hA.le
    exact ⟨⟨by linarith, by linarith⟩, hs.2, hs.1⟩
  refine ⟨hR, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : (1 / 3 - rep q.1 + δ) / A < 2 := by
      rw [div_lt_iff₀ hA]
      linarith
    linarith
  · have h : (1 / 3 - rep q.1 - δ) / A ≤ (1 / 3 - rep q.1 + δ) / A :=
      div_le_div_of_nonneg_right (by linarith) hA.le
    linarith
  · intro t ht0 htT hcos
    obtain ⟨⟨hp0, hp1⟩, hs1, hs2⟩ := key t ht0 htT
    rw [hcos] at hs1
    show (γ t).2 ∈ readyArc 2
    rw [hγ t ht0 htT, pshift_mem_readyArc_iff hp0 (by linarith)]
    linarith
  · intro t ht0 htT hcos
    obtain ⟨⟨hp0, hp1⟩, hs1, hs2⟩ := key t ht0 htT
    rw [lt_sub_comm, div_lt_iff₀ hA] at hcos
    show (γ t).2 ∈ displayArc
    rw [hγ t ht0 htT, pshift_mem_displayArc_iff hp0 hp1]
    linarith
  · intro t ht0 htT hr
    obtain ⟨⟨hp0, hp1⟩, hs1, hs2⟩ := key t ht0 htT
    have hr' : (γ t).2 ∈ readyArc 2 := hr
    rw [hγ t ht0 htT, pshift_mem_readyArc_iff hp0 (by linarith)] at hr'
    rw [sub_le_comm, le_div_iff₀ hA]
    linarith
  · intro t ht0 htT hd
    obtain ⟨⟨hp0, hp1⟩, hs1, hs2⟩ := key t ht0 htT
    have hd' : (γ t).2 ∈ displayArc := hd
    rw [hγ t ht0 htT, pshift_mem_displayArc_iff hp0 hp1] at hd'
    rw [lt_sub_comm, div_lt_iff₀ hA]
    linarith

end Readout

/-! ## The clock's pointer is a swing -/

section ClockTicks

variable {M : ℕ} {f : ℝ → ℝ} (J μ₀ μ₁ g : ℝ) (hf : Function.Periodic f 1)

/-- The pointer pair of the clock flow is the start turned by the displacement. -/
theorem clockPointerFlow_snd (hc : ContDiff ℝ ∞ f) (t : ℝ)
    (p : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) (q : KTorus) :
    (clockPointerFlow M J μ₀ μ₁ g hf hc t (clockArenaEquiv M p, q)).2
      = pshift (clockPointerShift J μ₀ μ₁ g hf q.2 p t) q := by
  rw [clockPointerFlow_apply]
  rfl

/-- **The swing's half amplitude** on the fibre `φ`, for a device of squared norm `n` whose
coherence turns as `e^{−iRs} C₀`: `−4 g f'(φ) Im C₀ / (R n)`. The pointer's displacement is this
times `1 − cos R t`, up to `clockSwingErr`. -/
noncomputable def clockSwingAmp (φ : AddCircle (1 : ℝ)) (R n : ℝ) (C₀ : ℂ) : ℝ :=
  -(4 * g) * hf.deriv_periodic.lift φ * C₀.im / (R * n)

/-- **The swing's error up to `T`**: the back-reaction term `2 |f'| g² |f| T²`, the localisation
term `2 |f'| |g| ε T² / n`, and the phase term `4 |g f'| |Re C₀| / (R n)` of a device not started
at a turning point of its coherence. -/
noncomputable def clockSwingErr (φ : AddCircle (1 : ℝ)) (R n : ℝ) (C₀ : ℂ) (ε T : ℝ) : ℝ :=
  2 * |hf.deriv_periodic.lift φ| * (g ^ 2 * |hf.lift φ| * T ^ 2 + |g| * (ε * T ^ 2 / n))
    + 4 * |g * hf.deriv_periodic.lift φ| * |C₀.re| / (R * n)

/-- The swing's error is not negative. -/
theorem clockSwingErr_nonneg (φ : AddCircle (1 : ℝ)) {R n : ℝ} (hR : 0 < R) (hn : 0 < n)
    (C₀ : ℂ) {ε : ℝ} (hε : 0 ≤ ε) (T : ℝ) : 0 ≤ clockSwingErr g hf φ R n C₀ ε T := by
  unfold clockSwingErr
  positivity

/-- ★★ **The pointer against the swing**, from the clock law of ~~#357~~
(`abs_clockPointerShift_sub_hand_le`): on every fibre, for a device whose coherence stays within
`|s| ε` of `e^{−iRs} C₀`, the pointer's displacement up to `T` is within `clockSwingErr` of
`clockSwingAmp` times `1 − cos R t`. -/
theorem abs_clockPointerShift_sub_swing_le (φ : AddCircle (1 : ℝ))
    {Ψ₀ : (ZMod (M + 1) × Fin 2) × Fin 2 → ℂ} (hΨ : Ψ₀ ≠ 0) {R : ℝ} (hR : 0 < R) {C₀ : ℂ}
    {ε : ℝ}
    (hdrift : ∀ s : ℝ, ‖deviceCoherence (deviceProp J μ₀ μ₁ s *ᵥ Ψ₀)
        - Complex.exp (Complex.I * (((-R : ℝ) : ℂ) * s)) * C₀‖ ≤ |s| * ε)
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    |clockPointerShift J μ₀ μ₁ g hf φ (deviceRay Ψ₀ hΨ) t
        - clockSwingAmp g hf φ R (deviceNorm Ψ₀).re C₀ * (1 - Real.cos (R * t))|
      ≤ clockSwingErr g hf φ R (deviceNorm Ψ₀).re C₀ ε T := by
  have hn := deviceNorm_re_pos hΨ
  have hRn := mul_pos hR hn
  have hε : 0 ≤ ε := by
    have h1 := (norm_nonneg _).trans (hdrift 1)
    rwa [abs_one, one_mul] at h1
  have hA := abs_clockPointerShift_sub_hand_le J μ₀ μ₁ g hf φ hΨ hR.ne' hdrift ht
  have hT2 : t ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ ht htT 2
  have hmono : 2 * |hf.deriv_periodic.lift φ|
        * (g ^ 2 * |hf.lift φ| * t ^ 2 + |g| * (ε * t ^ 2 / (deviceNorm Ψ₀).re))
      ≤ 2 * |hf.deriv_periodic.lift φ|
        * (g ^ 2 * |hf.lift φ| * T ^ 2 + |g| * (ε * T ^ 2 / (deviceNorm Ψ₀).re)) := by
    gcongr
  have hsin : |-(4 * (g * hf.deriv_periodic.lift φ)) * C₀.re * Real.sin (R * t)
        / (R * (deviceNorm Ψ₀).re)|
      ≤ 4 * |g * hf.deriv_periodic.lift φ| * |C₀.re| / (R * (deviceNorm Ψ₀).re) := by
    rw [abs_div, abs_of_pos hRn, abs_mul, abs_mul, abs_neg, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    refine div_le_div_of_nonneg_right ?_ hRn.le
    calc 4 * |g * hf.deriv_periodic.lift φ| * |C₀.re| * |Real.sin (R * t)|
        ≤ 4 * |g * hf.deriv_periodic.lift φ| * |C₀.re| * 1 := by
          gcongr
          exact Real.abs_sin_le_one _
      _ = 4 * |g * hf.deriv_periodic.lift φ| * |C₀.re| := mul_one _
  have e : clockPointerShift J μ₀ μ₁ g hf φ (deviceRay Ψ₀ hΨ) t
        - clockSwingAmp g hf φ R (deviceNorm Ψ₀).re C₀ * (1 - Real.cos (R * t))
      = (clockPointerShift J μ₀ μ₁ g hf φ (deviceRay Ψ₀ hΨ) t
          - -(4 * g) * hf.deriv_periodic.lift φ * clockHand R C₀ t / (deviceNorm Ψ₀).re)
        + -(4 * (g * hf.deriv_periodic.lift φ)) * C₀.re * Real.sin (R * t)
          / (R * (deviceNorm Ψ₀).re) := by
    unfold clockSwingAmp clockHand
    field_simp
    ring
  rw [e]
  unfold clockSwingErr
  exact (abs_add_le _ _).trans (add_le_add (hA.trans hmono) hsin)

/-- ★★★ **The clock's pointer is a swing: the tick law on the shared arena.** Under the joint
flow `clockPointerFlow`, for a device whose coherence stays within `|s| ε` of `e^{−iRs} C₀`, with
the swing's half amplitude `A` and its error `δ` up to `T` (back-reaction, localisation and
phase), a pointer started inside the ready arc by more than `δ` whose swing reaches the displayed
arc and stays in it is a swing history at the rate `R`. Its ticks are counted by
`IsSwing.abs_tickCount_sub_le`, written as records by `IsSwing.isRecordWrite`, and turned into
operational time by `IsSwing.abs_clockOpTime_sub_dilated_le`. The horizon `T` enters through
`δ`, which grows as `T²` unless the profile vanishes on the fibre and the device is one mode. -/
theorem isSwing_clockPointerFlow (hc : ContDiff ℝ ∞ f)
    {Ψ₀ : (ZMod (M + 1) × Fin 2) × Fin 2 → ℂ} (hΨ : Ψ₀ ≠ 0) {R : ℝ} (hR : 0 < R) {C₀ : ℂ}
    {ε : ℝ}
    (hdrift : ∀ s : ℝ, ‖deviceCoherence (deviceProp J μ₀ μ₁ s *ᵥ Ψ₀)
        - Complex.exp (Complex.I * (((-R : ℝ) : ℂ) * s)) * C₀‖ ≤ |s| * ε)
    (q : KTorus) {T A δ : ℝ}
    (hAe : A = clockSwingAmp g hf q.2 R (deviceNorm Ψ₀).re C₀)
    (hδe : δ = clockSwingErr g hf q.2 R (deviceNorm Ψ₀).re C₀ ε T)
    (hA : 0 < A) (h₁ : δ < rep q.1) (h₂ : rep q.1 + δ ≤ 1 / 6)
    (h₃ : 1 / 3 < rep q.1 + 2 * A - δ) (h₄ : rep q.1 + 2 * A + δ ≤ 5 / 6) :
    IsSwing (tickReady M) (tickDisplay M)
      (fun t => clockPointerFlow M J μ₀ μ₁ g hf hc t (clockArenaEquiv M (deviceRay Ψ₀ hΨ), q))
      R (1 - (1 / 3 - rep q.1 - δ) / A) (1 - (1 / 3 - rep q.1 + δ) / A) T := by
  have hε : 0 ≤ ε := by
    have h1 := (norm_nonneg _).trans (hdrift 1)
    rwa [abs_one, one_mul] at h1
  have hδ : 0 ≤ δ := by
    rw [hδe]
    exact clockSwingErr_nonneg g hf q.2 hR (deviceNorm_re_pos hΨ) C₀ hε T
  refine isSwing_of_abs_shift_sub_le hR hA hδ
    (fun t _ _ => clockPointerFlow_snd J μ₀ μ₁ g hf hc t _ q) (fun t ht htT => ?_) h₁ h₂ h₃ h₄
  rw [hAe, hδe]
  exact abs_clockPointerShift_sub_swing_le J μ₀ μ₁ g hf q.2 hΨ hR hdrift ht htT

end ClockTicks

/-! ### One mode: the exact tick -/

section OneMode

variable {L : ℕ} [NeZero L]

/-- **The squared norm of the device's packet** on a window of distinct modes: the sum of the
squared amplitudes, at every time. -/
theorem deviceNorm_devicePacket {J μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h1 : 0 < μ₁) {W : Finset ℤ}
    (hD : Distinct L W) (β : ℤ → ℂ) (t : ℝ) :
    deviceNorm (devicePacket (L := L) J μ₀ μ₁ W β t) = ((∑ m ∈ W, ‖β m‖ ^ 2 : ℝ) : ℂ) := by
  rw [(device_observables J μ₀ μ₁ W β t).1, chainInner_packet_unitAmp h0 hD,
    chainInner_packet_unitAmp h1 hD]
  ring

/-- A device in one mode with a nonzero amplitude is not the zero vector, at any time. -/
theorem devicePacket_single_ne_zero {J μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h1 : 0 < μ₁) (m : ℤ)
    {β : ℤ → ℂ} (hβ : β m ≠ 0) (t : ℝ) : devicePacket (L := L) J μ₀ μ₁ {m} β t ≠ 0 := by
  intro h
  have hn := deviceNorm_devicePacket (L := L) (J := J) h0 h1 (distinct_singleton m) β t
  rw [h, Finset.sum_singleton] at hn
  have h2 : deviceNorm (0 : (ZMod L × Fin 2) × Fin 2 → ℂ) = 0 := by simp [deviceNorm]
  rw [h2] at hn
  have h3 : ‖β m‖ ^ 2 = 0 := by exact_mod_cast hn.symm
  exact hβ (by simpa using h3)

/-- **The device's packet starts with a real coherence**: the weight of the two levels at each
momentum is real, so the coherence at the packet time `0` has no imaginary part. -/
theorem deviceCoherence_devicePacket_zero_im {J μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h1 : 0 < μ₁)
    {W : Finset ℤ} (hD : Distinct L W) (β : ℤ → ℂ) :
    (deviceCoherence (devicePacket (L := L) J μ₀ μ₁ W β 0)).im = 0 := by
  rw [(device_observables J μ₀ μ₁ W β 0).2.2, levelCoherence_eq J μ₀ μ₁ hD]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  have hz : ∑ m ∈ W,
      (levelWeight (L := L) J μ₀ μ₁ (unitAmp L J μ₀ β) (unitAmp L J μ₁ β) m).im = 0 :=
    Finset.sum_eq_zero fun m _ => by rw [levelWeight_unitAmp h0 h1, Complex.ofReal_im]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.im_ofReal_mul,
    Complex.im_sum, hz, mul_zero]

/-- **… and one bounded below**: for `μ₀ ≤ μ₁` its real part is at least
`(1 − ((μ₁ − μ₀)/μ₀)²)/2` times the sum of the squared amplitudes. -/
theorem le_deviceCoherence_devicePacket_zero_re {J μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ ≤ μ₁)
    {W : Finset ℤ} (hD : Distinct L W) (β : ℤ → ℂ) :
    (1 - ((μ₁ - μ₀) / μ₀) ^ 2) / 2 * ∑ m ∈ W, ‖β m‖ ^ 2
      ≤ (deviceCoherence (devicePacket (L := L) J μ₀ μ₁ W β 0)).re := by
  rw [(device_observables J μ₀ μ₁ W β 0).2.2, levelCoherence_eq J μ₀ μ₁ hD]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul,
    Complex.re_sum]
  have hs : ∑ m ∈ W, (1 - ((μ₁ - μ₀) / μ₀) ^ 2) * ‖β m‖ ^ 2
      ≤ ∑ m ∈ W,
        (levelWeight (L := L) J μ₀ μ₁ (unitAmp L J μ₀ β) (unitAmp L J μ₁ β) m).re :=
    Finset.sum_le_sum fun m _ => (levelWeight_unitAmp_bounds h0 h01 β m).1
  rw [← Finset.mul_sum] at hs
  rw [show (1 - ((μ₁ - μ₀) / μ₀) ^ 2) / 2 * ∑ m ∈ W, ‖β m‖ ^ 2
      = 1 / 2 * ((1 - ((μ₁ - μ₀) / μ₀) ^ 2) * ∑ m ∈ W, ‖β m‖ ^ 2) by ring]
  exact mul_le_mul_of_nonneg_left hs (by norm_num)

/-- **A device in one mode starts with a real coherence**
(`deviceCoherence_devicePacket_zero_im` on one mode). -/
theorem deviceCoherence_single_im {J μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h1 : 0 < μ₁) (m : ℤ)
    (β : ℤ → ℂ) : (deviceCoherence (devicePacket (L := L) J μ₀ μ₁ {m} β 0)).im = 0 :=
  deviceCoherence_devicePacket_zero_im h0 h1 (distinct_singleton m) β

/-- **… and a positive one**, for `μ₀ ≤ μ₁ < 2μ₀` and a nonzero amplitude
(`deviceCoherence_single_ne_zero`, ~~#271~~, with the sign kept). -/
theorem deviceCoherence_single_re_pos {J μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ ≤ μ₁)
    (h10 : μ₁ < 2 * μ₀) (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) :
    0 < (deviceCoherence (devicePacket (L := L) J μ₀ μ₁ {m} β 0)).re := by
  have hw := le_deviceCoherence_devicePacket_zero_re (L := L) (J := J) h0 h01
    (distinct_singleton m) β
  rw [Finset.sum_singleton] at hw
  have hq : 0 < 1 - ((μ₁ - μ₀) / μ₀) ^ 2 := by
    have h1 : (μ₁ - μ₀) / μ₀ < 1 := (div_lt_one h0).2 (by linarith)
    have h2 : 0 ≤ (μ₁ - μ₀) / μ₀ := div_nonneg (by linarith) h0.le
    nlinarith
  have hb : 0 < ‖β m‖ ^ 2 := by positivity
  exact (mul_pos (half_pos hq) hb).trans_le hw

/-- **A quarter turn back**: `e^{i(−R)(−π/(2R))} = i`. -/
theorem exp_I_neg_mul_quarter {R : ℝ} (hR : R ≠ 0) :
    Complex.exp (Complex.I * (((-R : ℝ) : ℂ) * ((-(Real.pi / (2 * R)) : ℝ) : ℂ)))
      = Complex.I := by
  have e : -R * -(Real.pi / (2 * R)) = Real.pi / 2 := by
    rw [neg_mul_neg, ← mul_div_assoc, mul_comm R Real.pi, mul_div_mul_right _ _ hR]
  rw [← Complex.ofReal_mul, e, mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- ★★ **A device in one mode started a quarter turn early**: prepared at the packet time
`−π/(2R)`, its coherence turns through `−R s` from `i C(0)`, exactly. The start of its swing is
then a turning point of the pointer. -/
theorem deviceCoherence_single_quarter (J μ₀ μ₁ : ℝ) (m : ℤ) (β : ℤ → ℂ) {R : ℝ}
    (hRe : R = levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ L m))) (hR : R ≠ 0) (s : ℝ) :
    deviceCoherence (deviceProp (L := L) J μ₀ μ₁ s
        *ᵥ devicePacket J μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
      = Complex.exp (Complex.I * (((-R : ℝ) : ℂ) * s))
        * (Complex.I * deviceCoherence (devicePacket (L := L) J μ₀ μ₁ {m} β 0)) := by
  have hI := exp_I_neg_mul_quarter hR
  have hsplit : Complex.I * (((-R : ℝ) : ℂ) * ((-(Real.pi / (2 * R)) + s : ℝ) : ℂ))
      = Complex.I * (((-R : ℝ) : ℂ) * (s : ℂ))
        + Complex.I * (((-R : ℝ) : ℂ) * ((-(Real.pi / (2 * R)) : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [deviceProp_devicePacket_shift,
    ← deviceProp_devicePacket J μ₀ μ₁ {m} β (-(Real.pi / (2 * R)) + s), deviceCoherence_single,
    ← hRe, hsplit, Complex.exp_add, hI]
  ring

end OneMode

section OneModeTick

variable {M : ℕ} {f : ℝ → ℝ} (J μ₀ μ₁ g : ℝ) (hf : Function.Periodic f 1)

/-- ★★★ **The exact tick: one mode on a fibre where the profile vanishes.** The device is one
mode of the ring, prepared a quarter turn early, and the fibre has `f(θ₂) = 0`. Then there is no
back-reaction, no localisation and no phase error: with the half amplitude
`A = −4 g f'(θ₂) Re C(0) / (R ‖β m‖²)`, a pointer started in the ready arc whose swing reaches
the displayed arc and stays in it is a swing history at the rate `R`, **for every horizon `T`**,
with one threshold `cos R t < 1 − (1/3 − rep θ₁)/A` for displaying. -/
theorem isSwing_clockPointerFlow_single (hc : ContDiff ℝ ∞ f) (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
    (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) {R : ℝ}
    (hRe : R = levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ (M + 1) m)))
    (q : KTorus) (hq : hf.lift q.2 = 0) {A : ℝ}
    (hAe : A = -(4 * g) * hf.deriv_periodic.lift q.2
      * (deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ {m} β 0)).re / (R * ‖β m‖ ^ 2))
    (hA : 0 < A) (h₂ : rep q.1 ≤ 1 / 6) (h₃ : 1 / 3 < rep q.1 + 2 * A)
    (h₄ : rep q.1 + 2 * A ≤ 5 / 6) (T : ℝ) :
    IsSwing (tickReady M) (tickDisplay M)
      (fun t => clockPointerFlow M J μ₀ μ₁ g hf hc t
        (clockArenaEquiv M (deviceRay (devicePacket (L := M + 1) J μ₀ μ₁ {m} β
          (-(Real.pi / (2 * R)))) (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _)), q))
      R (1 - (1 / 3 - rep q.1) / A) (1 - (1 / 3 - rep q.1) / A) T := by
  have h1 : 0 < μ₁ := h0.trans h01
  have hR : 0 < R := by
    rw [hRe]
    exact levelClockRate_pos h0 h01 _
  have hdrift : ∀ s : ℝ, ‖deviceCoherence (deviceProp J μ₀ μ₁ s
        *ᵥ devicePacket (L := M + 1) J μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
      - Complex.exp (Complex.I * (((-R : ℝ) : ℂ) * s))
        * (Complex.I * deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ {m} β 0))‖
      ≤ |s| * 0 := by
    intro s
    rw [deviceCoherence_single_quarter J μ₀ μ₁ m β hRe hR.ne' s, sub_self, norm_zero, mul_zero]
  have hn : (deviceNorm (devicePacket (L := M + 1) J μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))).re
      = ‖β m‖ ^ 2 := by
    rw [deviceNorm_devicePacket h0 h1 (distinct_singleton m), Finset.sum_singleton,
      Complex.ofReal_re]
  have hre : (Complex.I * deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ {m} β 0)).re
      = 0 := by
    rw [Complex.I_mul_re, deviceCoherence_single_im h0 h1, neg_zero]
  have hAe' : A = clockSwingAmp g hf q.2 R
      (deviceNorm (devicePacket (L := M + 1) J μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))).re
      (Complex.I * deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ {m} β 0)) := by
    rw [hAe, clockSwingAmp, hn, Complex.I_mul_im]
  have hδe : (0 : ℝ) = clockSwingErr g hf q.2 R
      (deviceNorm (devicePacket (L := M + 1) J μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))).re
      (Complex.I * deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ {m} β 0)) 0 T := by
    unfold clockSwingErr
    rw [hq, hre]
    simp
  have hsw := isSwing_clockPointerFlow J μ₀ μ₁ g hf hc
    (devicePacket_single_ne_zero h0 h1 m hβ _) hR hdrift q hAe' hδe hA (rep_pos q.1)
    (by linarith) (by linarith) (by linarith)
  simpa only [sub_zero, add_zero] using hsw

end OneModeTick

section Train

variable {M : ℕ}

/-- ★★ **The exact tick is not vacuous**: the profile `trainF` on the fibre `θ₂ = 0`, where it
vanishes with slope `−1`; one mode with `μ₀ < μ₁ < 2μ₀`; the coupling chosen so that the half
amplitude is `1/4`; the pointer started at `1/12`. The pointer is then a swing history for every
horizon, displaying exactly while `cos R t < 0`: half of every turn. -/
theorem isSwing_clockPointerFlow_train (J : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
    (h10 : μ₁ < 2 * μ₀) (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) {R : ℝ}
    (hRe : R = levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ (M + 1) m))) {g : ℝ}
    (hg : g = R * ‖β m‖ ^ 2
      / (16 * (deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ {m} β 0)).re)) (T : ℝ) :
    IsSwing (tickReady M) (tickDisplay M)
      (fun t => clockPointerFlow M J μ₀ μ₁ g trainF_periodic contDiff_trainF t
        (clockArenaEquiv M (deviceRay (devicePacket (L := M + 1) J μ₀ μ₁ {m} β
          (-(Real.pi / (2 * R)))) (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _)),
          ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))))
      R 0 0 T := by
  have hR : 0 < R := by
    rw [hRe]
    exact levelClockRate_pos h0 h01 _
  have hC := deviceCoherence_single_re_pos (L := M + 1) (J := J) h0 h01.le h10 m hβ
  have hb : 0 < ‖β m‖ ^ 2 := by positivity
  have hrep : rep (((1 / 12 : ℝ) : CircleFibre)) = 1 / 12 :=
    rep_coe_of_mem_Ioc ⟨by norm_num, by norm_num⟩
  have hAe : (1 / 4 : ℝ) = -(4 * g) * trainF_periodic.deriv_periodic.lift (0 : AddCircle (1 : ℝ))
      * (deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ {m} β 0)).re / (R * ‖β m‖ ^ 2) := by
    rw [trainF_deriv_lift_zero, hg]
    field_simp
    ring
  have e : (1 : ℝ) - (1 / 3 - 1 / 12) / (1 / 4) = 0 := by norm_num
  have hsw := isSwing_clockPointerFlow_single J μ₀ μ₁ g trainF_periodic contDiff_trainF h0 h01
    m hβ hRe ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))) trainF_lift_zero hAe
    (by norm_num) (by rw [hrep]; norm_num) (by rw [hrep]; norm_num) (by rw [hrep]; norm_num) T
  simp only [hrep, e] at hsw
  exact hsw

end Train

/-! ### A localised packet: the tick law with its three errors -/

section PacketDrift

variable {L : ℕ} [NeZero L]

/-- ★★ **The coherence of #262's device from any start**: at `t₁ + s` it is within `|s|` times
the sharp drift `deviceDrift` of `e^{−iRs} C(t₁)`, at the rate `R` of the lattice momentum. The
bound of `dirac_device` is the case `t₁ = 0`; a device prepared a quarter turn early needs it
from `t₁ = −π/(2R)`. -/
theorem norm_deviceCoherence_shift_sub_le {c μ₀ μ₁ ℓ D p₀ : ℝ} (hc : 0 < c) (h0 : 0 < μ₀)
    (h01 : μ₀ ≤ μ₁) (hℓ : 0 < ℓ) {W : Finset ℤ} (hD : Distinct L W)
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D) (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) (t₁ s : ℝ) :
    ‖deviceCoherence (deviceProp (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ s
          *ᵥ devicePacket (scaledHop c (ℓ / L)) μ₀ μ₁ W β t₁)
        - Complex.exp (Complex.I * (((-levelClockRate μ₀ μ₁
            (2 * scaledHop c (ℓ / L) * Real.sin (ℓ / L * p₀)) : ℝ) : ℂ) * s))
          * deviceCoherence (devicePacket (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ W β t₁)‖
      ≤ |s| * deviceDrift c μ₀ μ₁ D p₀ := by
  set J := scaledHop c (ℓ / L)
  set R := levelClockRate μ₀ μ₁ (2 * J * Real.sin (ℓ / L * p₀))
  set w := levelWeight (L := L) J μ₀ μ₁ (unitAmp L J μ₀ β) (unitAmp L J μ₁ β)
  set Rm : ℤ → ℝ := fun m => levelClockRate μ₀ μ₁ (2 * J * Real.sin (angleZ L m))
  have hΔ : ∀ m, ((bandE J μ₀ (angleZ L m) - bandE J μ₁ (angleZ L m) : ℝ) : ℂ)
      = ((-Rm m : ℝ) : ℂ) := fun m => by
    simp only [Rm, levelClockRate, bandE]
    push_cast
    ring
  rw [deviceProp_devicePacket_shift, (device_observables J μ₀ μ₁ W β (t₁ + s)).2.2,
    (device_observables J μ₀ μ₁ W β t₁).2.2, levelCoherence_eq J μ₀ μ₁ hD,
    levelCoherence_eq J μ₀ μ₁ hD]
  simp only [hΔ]
  have e : (1 / 2 : ℂ) * ∑ m ∈ W, w m
        * Complex.exp (Complex.I * (((-Rm m : ℝ) : ℂ) * ((t₁ + s : ℝ) : ℂ)))
      - Complex.exp (Complex.I * (((-R : ℝ) : ℂ) * (s : ℂ)))
        * ((1 / 2 : ℂ) * ∑ m ∈ W, w m
          * Complex.exp (Complex.I * (((-Rm m : ℝ) : ℂ) * (t₁ : ℂ))))
      = (1 / 2 : ℂ) * ∑ m ∈ W, w m * Complex.exp (Complex.I * (((-Rm m : ℝ) : ℂ) * (t₁ : ℂ)))
          * (Complex.exp (Complex.I * (((-Rm m : ℝ) : ℂ) * (s : ℂ)))
            - Complex.exp (Complex.I * (((-R : ℝ) : ℂ) * (s : ℂ)))) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    have : Complex.exp (Complex.I * (((-Rm m : ℝ) : ℂ) * ((t₁ + s : ℝ) : ℂ)))
        = Complex.exp (Complex.I * (((-Rm m : ℝ) : ℂ) * (t₁ : ℂ)))
          * Complex.exp (Complex.I * (((-Rm m : ℝ) : ℂ) * (s : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [this]
    ring
  rw [e, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  have hterm : ∀ m ∈ W, ‖w m * Complex.exp (Complex.I * (((-Rm m : ℝ) : ℂ) * (t₁ : ℂ)))
      * (Complex.exp (Complex.I * (((-Rm m : ℝ) : ℂ) * (s : ℂ)))
        - Complex.exp (Complex.I * (((-R : ℝ) : ℂ) * (s : ℂ))))‖
      ≤ |s| * (‖β m‖ ^ 2 * (c * D * (2 * c * |p₀| + c * D) * (μ₁ - μ₀) / (2 * μ₀ ^ 2))) := by
    intro m hm
    have hb := levelWeight_mul_rate_le (L := L) hc h0 h01 hℓ (hWD m hm) β
    rw [norm_mul, norm_mul, norm_exp_I_mul_ofReal_mul, mul_one]
    have h1 := norm_exp_I_mul_sub_le (-Rm m) (-R) s
    rw [show -Rm m - -R = -(Rm m - R) by ring, abs_neg] at h1
    refine (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans ?_
    rw [show ‖w m‖ * (|s| * |Rm m - R|) = |s| * (‖w m‖ * |Rm m - R|) by ring]
    exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  refine (mul_le_mul_of_nonneg_left
    ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm)) (by norm_num)).trans_eq ?_
  rw [← Finset.mul_sum, ← Finset.sum_mul, hβ, deviceDrift]
  ring

end PacketDrift

section PacketTick

variable {M : ℕ} {f : ℝ → ℝ}

/-- ★★★ **The tick law for the localised packet of #262's device, with its three errors.** On
a ring of `M + 1` sites, the packet of `dirac_device` prepared a quarter turn early, coupled to
the pointer through `clockPointerFlow`:

* **the start is a turning point, within the localisation error**: its coherence `C₀` has
  `|Re C₀| ≤ (π/(2R)) ε` and `Im C₀ ≥ (1 − ((μ₁ − μ₀)/μ₀)²)/2 − (π/(2R)) ε`, with
  `ε = deviceDrift` and `R` the level splitting at the lattice momentum;
* **the pointer is a swing**: for every fibre `q`, horizon `T`, half amplitude
  `A = clockSwingAmp` and error `δ = clockSwingErr` (back-reaction, localisation through `ε`,
  and the phase of the start) meeting the four threshold conditions, the readout history is an
  `IsSwing` at the rate `R`;
* **operational time obeys the relativistic clock law**: every tick count `N` at `T ≥ 0` has
  `|2π N/(μ₁ − μ₀) − √(1 − (v/c)²) T| ≤ 2π/(μ₁ − μ₀) + ((μ₁ − μ₀)/E₀) T`, the detector's
  resolution and the finite splitting.

The threshold conditions are hypotheses: `δ` grows as `T²`, so for a packet of positive width
they hold on a bounded horizon at most, and no packet of positive width is shown here to meet
them. The one-mode case meets them at every horizon (`isSwing_clockPointerFlow_single`,
`isSwing_clockPointerFlow_train`). `T` is the flow parameter (UA-7); the count does not hold
it. -/
theorem clock_tick_device (hf : Function.Periodic f 1) (hcf : ContDiff ℝ ∞ f)
    {c μ₀ μ₁ ℓ D p₀ : ℝ} (hc : 0 < c) (h0 : 0 < μ₀) (h01 : μ₀ < μ₁) (hℓ : 0 < ℓ)
    {W : Finset ℤ} {lo : ℤ} (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + (M + 1 : ℕ))
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D) (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) (g : ℝ) :
    let J := scaledHop c (ℓ / (M + 1 : ℕ))
    let σ := 2 * J * Real.sin (ℓ / (M + 1 : ℕ) * p₀)
    let R := levelClockRate μ₀ μ₁ σ
    let ε := deviceDrift c μ₀ μ₁ D p₀
    let Ψ₀ := devicePacket (L := M + 1) J μ₀ μ₁ W β (-(Real.pi / (2 * R)))
    let C₀ := deviceCoherence Ψ₀
    ∃ hΨ : Ψ₀ ≠ 0,
      |C₀.re| ≤ Real.pi / (2 * R) * ε
      ∧ (1 - ((μ₁ - μ₀) / μ₀) ^ 2) / 2 - Real.pi / (2 * R) * ε ≤ C₀.im
      ∧ ∀ (q : KTorus) (T A δ : ℝ), A = clockSwingAmp g hf q.2 R 1 C₀ →
          δ = clockSwingErr g hf q.2 R 1 C₀ ε T → 0 < A → δ < rep q.1 →
          rep q.1 + δ ≤ 1 / 6 → 1 / 3 < rep q.1 + 2 * A - δ → rep q.1 + 2 * A + δ ≤ 5 / 6 →
          IsSwing (tickReady M) (tickDisplay M)
              (fun t => clockPointerFlow M J μ₀ μ₁ g hf hcf t
                (clockArenaEquiv M (deviceRay Ψ₀ hΨ), q))
              R (1 - (1 / 3 - rep q.1 - δ) / A) (1 - (1 / 3 - rep q.1 + δ) / A) T
            ∧ ∀ N : ℕ, 0 ≤ T →
              IsTickCount (tickReady M) (tickDisplay M)
                (fun t => clockPointerFlow M J μ₀ μ₁ g hf hcf t
                  (clockArenaEquiv M (deviceRay Ψ₀ hΨ), q)) T N →
              |clockOpTime μ₀ μ₁ N - Real.sqrt (1 - (vRel c μ₀ σ / c) ^ 2) * T|
                ≤ 2 * Real.pi / (μ₁ - μ₀) + (μ₁ - μ₀) / dispE μ₀ σ * T := by
  intro J σ R ε Ψ₀ C₀
  have h1 : 0 < μ₁ := h0.trans h01
  have hR : 0 < R := levelClockRate_pos h0 h01 σ
  have hD := (noWrap_distinct_of_window (L := M + 1) hWin).2
  have hn : ∀ t, deviceNorm (devicePacket (L := M + 1) J μ₀ μ₁ W β t) = 1 := fun t => by
    rw [deviceNorm_devicePacket h0 h1 hD, hβ, Complex.ofReal_one]
  have hΨ : Ψ₀ ≠ 0 := ne_zero_of_deviceNorm_eq_one (hn _)
  have hdr : ∀ t₁ s : ℝ,
      ‖deviceCoherence (deviceProp (L := M + 1) J μ₀ μ₁ s *ᵥ devicePacket J μ₀ μ₁ W β t₁)
        - Complex.exp (Complex.I * (((-R : ℝ) : ℂ) * s))
          * deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ W β t₁)‖ ≤ |s| * ε :=
    norm_deviceCoherence_shift_sub_le (L := M + 1) hc h0 h01.le hℓ hD hWD β hβ
  have hq := hdr 0 (-(Real.pi / (2 * R)))
  have hπ : |-(Real.pi / (2 * R))| = Real.pi / (2 * R) := by
    rw [abs_neg, abs_of_pos (div_pos Real.pi_pos (mul_pos two_pos hR))]
  rw [deviceProp_devicePacket_shift, zero_add, exp_I_neg_mul_quarter hR.ne', hπ] at hq
  have him := deviceCoherence_devicePacket_zero_im (L := M + 1) (J := J) h0 h1 hD β
  have hre := le_deviceCoherence_devicePacket_zero_re (L := M + 1) (J := J) h0 h01.le hD β
  rw [hβ, mul_one] at hre
  have hb1 : |(deviceCoherence
      (devicePacket (L := M + 1) J μ₀ μ₁ W β (-(Real.pi / (2 * R))))).re|
      ≤ Real.pi / (2 * R) * ε := by
    have h := (Complex.abs_re_le_norm _).trans hq
    rwa [Complex.sub_re, Complex.I_mul_re, him, neg_zero, sub_zero] at h
  have hb2 : (1 - ((μ₁ - μ₀) / μ₀) ^ 2) / 2 - Real.pi / (2 * R) * ε
      ≤ (deviceCoherence (devicePacket (L := M + 1) J μ₀ μ₁ W β (-(Real.pi / (2 * R))))).im := by
    have h := (Complex.abs_im_le_norm _).trans hq
    rw [Complex.sub_im, Complex.I_mul_im] at h
    have h' := (abs_le.1 h).1
    linarith
  refine ⟨hΨ, hb1, hb2, fun q T A δ hAe hδe hA h₁ h₂ h₃ h₄ => ?_⟩
  have hn1 : (deviceNorm Ψ₀).re = 1 :=
    (congrArg Complex.re (hn (-(Real.pi / (2 * R))))).trans Complex.one_re
  have hAe' : A = clockSwingAmp g hf q.2 R (deviceNorm Ψ₀).re C₀ := by
    rw [hn1]
    exact hAe
  have hδe' : δ = clockSwingErr g hf q.2 R (deviceNorm Ψ₀).re C₀ ε T := by
    rw [hn1]
    exact hδe
  have hdrift : ∀ s : ℝ, ‖deviceCoherence (deviceProp J μ₀ μ₁ s *ᵥ Ψ₀)
      - Complex.exp (Complex.I * (((-R : ℝ) : ℂ) * s)) * C₀‖ ≤ |s| * ε :=
    hdr (-(Real.pi / (2 * R)))
  have hsw := isSwing_clockPointerFlow J μ₀ μ₁ g hf hcf hΨ hR hdrift q hAe' hδe' hA h₁ h₂ h₃ h₄
  exact ⟨hsw, fun N hT hN =>
    IsSwing.abs_clockOpTime_sub_dilated_le (s := σ) hsw hc.ne' h0 h01 hT hN⟩

end PacketTick

/-! ### Each tick as an actual occurrence of the joint flow -/

section TickRecord

variable {M : ℕ} {f : ℝ → ℝ} (J μ₀ μ₁ g : ℝ) (hf : Function.Periodic f 1)

/-- A swing history rests at every whole turn inside the horizon. -/
theorem IsSwing.mem_rest_turn {X : Type*} {rest disp : Set X} {γ : ℝ → X} {R c d T : ℝ}
    (h : IsSwing rest disp γ R c d T) (k : ℕ) (hk : (k : ℝ) * (2 * Real.pi) / R ≤ T) :
    γ ((k : ℝ) * (2 * Real.pi) / R) ∈ rest := by
  have hR := h.rate_pos
  have e : R * ((k : ℝ) * (2 * Real.pi) / R) = (k : ℝ) * (2 * Real.pi) := by
    field_simp
  refine h.rest_of_cos _ (div_nonneg (by positivity) hR.le) hk ?_
  rw [e, Real.cos_nat_mul_two_pi]

/-- The clock flow is continuous at each time. -/
theorem continuous_clockPointerFlow (hc : ContDiff ℝ ∞ f) (t : ℝ) :
    Continuous (clockPointerFlow M J μ₀ μ₁ g hf hc t) :=
  (arenaForm_isSymplectic (4 * M + 3)).continuous_hamiltonianFlow
    (contMDiff_clockPointerEnergy J μ₀ μ₁ g hf hc) t

/-- The clock flow is measurable at each time. -/
theorem measurable_clockPointerFlow (hc : ContDiff ℝ ∞ f) (t : ℝ) :
    Measurable (clockPointerFlow M J μ₀ μ₁ g hf hc t) :=
  (continuous_clockPointerFlow J μ₀ μ₁ g hf hc t).measurable

/-- **The two-time propagator** of the clock's joint dynamics: autonomous, so only the elapsed
time enters. It is `clockPointerFlow` and nothing else. -/
noncomputable def clockPointerEvolve (hc : ContDiff ℝ ∞ f) (s t : ℝ) :
    KSigma (4 * M + 3 + 1) → KSigma (4 * M + 3 + 1) :=
  clockPointerFlow M J μ₀ μ₁ g hf hc (t - s)

/-- Nothing happens in no time. -/
theorem clockPointerEvolve_self (hc : ContDiff ℝ ∞ f) (t : ℝ) :
    clockPointerEvolve J μ₀ μ₁ g hf hc t t = (id : KSigma (4 * M + 3 + 1) → _) := by
  funext x
  rw [clockPointerEvolve, sub_self, clockPointerFlow_zero]
  rfl

/-- **The two-time law.** -/
theorem clockPointerEvolve_comp (hc : ContDiff ℝ ∞ f) (s t u : ℝ) :
    clockPointerEvolve J μ₀ μ₁ g hf hc t u ∘ clockPointerEvolve J μ₀ μ₁ g hf hc s t
      = clockPointerEvolve (M := M) J μ₀ μ₁ g hf hc s u := by
  funext x
  show clockPointerFlow M J μ₀ μ₁ g hf hc (u - t) (clockPointerFlow M J μ₀ μ₁ g hf hc (t - s) x)
    = clockPointerFlow M J μ₀ μ₁ g hf hc (u - s) x
  rw [← clockPointerFlow_add J μ₀ μ₁ g hf hc, sub_add_sub_cancel]

/-- Each step of the propagator is measurable. -/
theorem measurable_clockPointerEvolve (hc : ContDiff ℝ ∞ f) (s t : ℝ) :
    Measurable (clockPointerEvolve (M := M) J μ₀ μ₁ g hf hc s t) :=
  measurable_clockPointerFlow J μ₀ μ₁ g hf hc (t - s)

/-- ★★★ **Tick `k` as an actual occurrence on the shared arena.** For a swing history of the
joint flow `clockPointerFlow`, the `k`-th tick is an `ActualOccurrence`: its `evolve` is the
flow over the elapsed time, its readout is `tickShown`, its preparation is the flow's own state
at the whole turn `2πk/R` (a ready state, by the swing), and its write is
`IsSwing.isRecordWrite`. The start, the write interval and the window are flow times (UA-7):
they locate the occurrence, and the count does not use them. The readout acts at every site of
the ring, so the site is the whole ring. -/
noncomputable def clockTickRecord (hc : ContDiff ℝ ∞ f) {x₀ : KSigma (4 * M + 3 + 1)}
    {R c d T : ℝ}
    (h : IsSwing (tickReady M) (tickDisplay M)
      (fun t => clockPointerFlow M J μ₀ μ₁ g hf hc t x₀) R c d T)
    (k : ℕ) {d' : ℝ} (hd'1 : -1 ≤ d') (hd' : d' < d)
    (hk : ((k : ℝ) * (2 * Real.pi) + (2 * Real.pi - Real.arccos d')) / R ≤ T) :
    ActualOccurrence (KSigma (4 * M + 3 + 1)) Bool (M + 1) where
  evolve := clockPointerEvolve J μ₀ μ₁ g hf hc
  evolve_self := clockPointerEvolve_self J μ₀ μ₁ g hf hc
  evolve_comp := clockPointerEvolve_comp J μ₀ μ₁ g hf hc
  measurable_evolve := measurable_clockPointerEvolve J μ₀ μ₁ g hf hc
  readout := tickShown M
  measurable_readout := measurable_tickShown M
  ready := tickReady M
  measurableSet_ready := measurableSet_tickReady M
  prep := clockPointerFlow M J μ₀ μ₁ g hf hc ((k : ℝ) * (2 * Real.pi) / R) x₀
  prep_mem := h.mem_rest_turn k ((div_le_div_of_nonneg_right
    (by linarith [Real.arccos_le_pi d', Real.pi_pos]) h.rate_pos.le).trans hk)
  site := Finset.univ
  start := (k : ℝ) * (2 * Real.pi) / R
  value := true
  writeStart := ((k : ℝ) * (2 * Real.pi) + Real.arccos c) / R
  writeEnd := ((k : ℝ) * (2 * Real.pi) + Real.arccos d') / R
  window := 2 * (Real.pi - Real.arccos d') / R
  isWrite := h.isRecordWrite (fun t => by
    show tickShown M (clockPointerFlow M J μ₀ μ₁ g hf hc (t - (k : ℝ) * (2 * Real.pi) / R)
        (clockPointerFlow M J μ₀ μ₁ g hf hc ((k : ℝ) * (2 * Real.pi) / R) x₀)) = true
      ↔ clockPointerFlow M J μ₀ μ₁ g hf hc t x₀ ∈ tickDisplay M
    rw [← clockPointerFlow_add J μ₀ μ₁ g hf hc, sub_add_cancel]
    exact tickShown_eq_true_iff M _) k hd'1 hd' hk

/-- ★★ **Every tick record reads the one flow**: the readout history of tick `k` is `tickShown`
along `clockPointerFlow` from the one start `x₀`, whatever `k` is. The tick records of a run are
occurrences of one history, not of one history each. -/
theorem clockTickRecord_history (hc : ContDiff ℝ ∞ f) {x₀ : KSigma (4 * M + 3 + 1)}
    {R c d T : ℝ}
    (h : IsSwing (tickReady M) (tickDisplay M)
      (fun t => clockPointerFlow M J μ₀ μ₁ g hf hc t x₀) R c d T)
    (k : ℕ) {d' : ℝ} (hd'1 : -1 ≤ d') (hd' : d' < d)
    (hk : ((k : ℝ) * (2 * Real.pi) + (2 * Real.pi - Real.arccos d')) / R ≤ T) (t : ℝ) :
    (clockTickRecord J μ₀ μ₁ g hf hc h k hd'1 hd' hk).history t
      = tickShown M (clockPointerFlow M J μ₀ μ₁ g hf hc t x₀) := by
  show tickShown M (clockPointerFlow M J μ₀ μ₁ g hf hc (t - (k : ℝ) * (2 * Real.pi) / R)
      (clockPointerFlow M J μ₀ μ₁ g hf hc ((k : ℝ) * (2 * Real.pi) / R) x₀))
    = tickShown M (clockPointerFlow M J μ₀ μ₁ g hf hc t x₀)
  rw [← clockPointerFlow_add J μ₀ μ₁ g hf hc, sub_add_cancel]

end TickRecord

/-! ### No function of the arena state holds the count -/

section NoCounter

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {φ : α → α}

/-- ★★ **A state function that never falls along a measure-preserving step does not rise.** For
a finite measure `μ`, a map `φ` preserving it and a measurable `N`: if `N x ≤ N (φ x)` almost
everywhere, then `N (φ x) = N x` almost everywhere. No integrability of `N` is assumed (the
proof integrates `arctan ∘ N`).

This holds for every flow preserving a finite measure: the Hamiltonian is not used. By test 4 of
the contract (`specs/unified-record-spacetime-plan.md` §6) it is conditional on the preserved
measure and passes no gate. -/
theorem ae_comp_eq_of_ae_le_comp (hφ : MeasurePreserving φ μ μ) {N : α → ℝ} (hN : Measurable N)
    (h : ∀ᵐ x ∂μ, N x ≤ N (φ x)) : ∀ᵐ x ∂μ, N (φ x) = N x := by
  have hFm : Measurable fun x => Real.arctan (N x) := Real.continuous_arctan.measurable.comp hN
  have hFi : Integrable (fun x => Real.arctan (N x)) μ :=
    Integrable.of_bound hFm.aestronglyMeasurable (Real.pi / 2) (Filter.Eventually.of_forall
      fun x => by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩)
  have hFφi : Integrable (fun x => Real.arctan (N (φ x))) μ :=
    (hφ.integrable_comp hFm.aestronglyMeasurable).2 hFi
  have hint : ∫ x, Real.arctan (N (φ x)) ∂μ = ∫ x, Real.arctan (N x) ∂μ := by
    rw [← integral_map hφ.measurable.aemeasurable hFm.aestronglyMeasurable, hφ.map_eq]
  have hnn : 0 ≤ᵐ[μ] fun x => Real.arctan (N (φ x)) - Real.arctan (N x) := by
    filter_upwards [h] with x hx
    exact sub_nonneg.2 (Real.arctan_strictMono.monotone hx)
  have hz : ∫ x, (Real.arctan (N (φ x)) - Real.arctan (N x)) ∂μ = 0 := by
    rw [integral_sub hFφi hFi, hint, sub_self]
  have h0 := (integral_eq_zero_iff_of_nonneg_ae hnn (hFφi.sub hFi)).1 hz
  filter_upwards [h0] with x hx
  exact Real.arctan_injective (sub_eq_zero.1 hx)

/-- ★★ **No state function is a counter**: on a nonzero finite measure preserved by `φ`, no
measurable `N` gains at least one along `φ` almost everywhere. -/
theorem not_ae_add_one_le_comp [NeZero μ] (hφ : MeasurePreserving φ μ μ) {N : α → ℝ}
    (hN : Measurable N) : ¬ ∀ᵐ x ∂μ, N x + 1 ≤ N (φ x) := by
  intro h
  have h1 : ∀ᵐ x ∂μ, N x ≤ N (φ x) := h.mono fun x hx => by linarith
  have h2 := ae_comp_eq_of_ae_le_comp hφ hN h1
  have h3 : ∀ᵐ x ∂μ, False := by
    filter_upwards [h, h2] with x hx hx2
    linarith
  exact h3.exists.elim fun _ hF => hF

end NoCounter

section ClockNoCounter

variable {M : ℕ} {f : ℝ → ℝ} (J μ₀ μ₁ g : ℝ) (hf : Function.Periodic f 1)

/-- ★★★ **No function of the clock arena's state holds the tick count.** For the ontic measure
`kMuL p₀` and any step `τ` of the joint flow `clockPointerFlow` (one turn of the clock, say), no
measurable function of the arena state gains at least one along the step almost everywhere. The
count of a run is a function of its tick records (`IsTickCount`) and of no state at one time:
each record is erased within its turn (`IsSwing.notMem_disp_of_cos_eq_one`), and the arena has no
register that keeps the number. An instance of `not_ae_add_one_le_comp`, so it uses only that
the flow preserves `kMuL`. -/
theorem not_ae_count_advances_clockPointerFlow (hc : ContDiff ℝ ∞ f)
    (p₀ : CPN (4 * M + 3 + 1)) (τ : ℝ) {N : KSigma (4 * M + 3 + 1) → ℝ} (hN : Measurable N) :
    ¬ ∀ᵐ x ∂kMuL p₀, N x + 1 ≤ N (clockPointerFlow M J μ₀ μ₁ g hf hc τ x) :=
  not_ae_add_one_le_comp ⟨measurable_clockPointerFlow J μ₀ μ₁ g hf hc τ,
    kMuL_map_clockPointerFlow J μ₀ μ₁ g hf hc p₀ τ⟩ hN

end ClockNoCounter

end CSD.RecordLayer

end
