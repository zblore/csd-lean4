/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracTwoCharts

/-!
# Frame covariance of the radar records

**Category:** 7-SigmaLayer (the record layer). BACKLOG #285, parts (i) and (iii); #287.

#285 asks whether the ontic time's frame is hidden from records. Part (i): a preparation and its
boost should give record laws related by the Lorentz map. On the radar exchange this splits into
three facts, none of which needs a boost operator on the lattice.

## Radar in any frame

* `lorentzRelVel`, `velAdd` (relative velocity and relativistic addition), `one_sub_mul_pos`,
  `one_add_mul_pos`, `one_sub_lorentzRelVel_sq`, `abs_velAdd_lt`;
* ★★★ `radar_lorentz_covariant` (**in any frame, with `A` moving at `v_A` and `B` at `v_B`, `B`'s
  radar coordinates of `A`'s event — `B`'s proper time, relative to the meeting — are the Lorentz
  boost, at the relative velocity `w = (v_A − v_B)/(1 − v_A v_B)`, of `A`'s proper-time chart**:
  the record relation depends on the frame only through `w`; `radar_lorentz_exact` is `v_A = 0`).

## A common boost changes nothing

* ★★ `lorentzRelVel_velAdd` (**boosting both observers by `u` leaves their relative velocity
  unchanged**);
* ★★★ `radar_frame_covariant` (**a preparation and its boost give the same radar record relation:
  the Lorentz boost at the same `w`**).

## Boosted preparations on the chain

* ★★ `vRel_boost` (**the chain's relativistic mode velocity under a momentum boost
  `s' = γ_u (s + u E)` is `velAdd u (vRel s)`**) — so a boosted packet is a packet at a boosted
  momentum, and `dirac_packet_limit`, which holds at every centre momentum, moves it at the boosted
  velocity within its error at the boosted momentum bound.

## The lattice residue (#285 (iii))

* ★★ `abs_lorentzRelVel_sub_le` (**the relative velocity is Lipschitz**: `2(|Δa| + |Δb|)/(1 − V²)²`
  on velocities bounded by `V < 1`), `latticeVelErr` (`a²(P²/2 + P³/(6μ))`, the lattice's
  departure from the relativistic velocity, `abs_scaledV_sub_le`);
* ★★★ `lattice_frame_residue` (**how far the lattice frame shows up**: the lattice's relative
  velocity in a boosted frame differs from that in the original frame by at most
  `4 (latticeVelErr P + latticeVelErr P')/(1 − V²)²` — order `a²`, growing with the boosted momentum
  bound `P'`, vanishing as `a → 0`; the exact relative velocity is the same in both frames).

## Every encounter record (#287)

* ★★ `lorentzBoost_worldline_vel` (a worldline segment of velocity `v`, boosted by `u`, has velocity
  `(v − u)/(1 − v u)`);
* ★★★ `proper_time_boost` (**proper time along a worldline is the same in every frame**);
* ★★★ `encounter_reading_covariant` (**a reading of an encounter, within `ε` of its ideal reading in
  one frame and `ε'` in the boosted preparation, is frame independent to `ε + ε'`**);
* ★★★ `record_statistic_covariant` (**every statistic of encounter readings with
  `|F a − F b| ≤ K Σ |a_k − b_k|` is frame independent to `K Σ (ε_k + ε'_k)`**). The reading errors
  are each record's window (`abs_record_sub_le`, `encounter_record_window`) and its clock's reading
  error (`clock_reading_error`), in each frame.

## What is by construction, and what is earned

The Dirac chain was chosen with a relativistic continuum limit, so light speed and clock dilation
are inputs, and the kinematic theorems here (`radar_lorentz_exact`, `radar_lorentz_covariant`,
`proper_time_boost`) are special relativity checked in Lean. What the corpus earns is that the
chain's own matter realises those kinematics in its records with explicit errors (#274, #278,
#280, #283, #284). The untested case is entangled spacelike records under Σ's ontic selection, where
individual outcomes may depend on the ontic slicing while their statistics provably do not (#288).

## Honest scope

⚠️ **Kinematic records**: the covariance is of the radar relation — light at speed `1`, clocks at
`√(1 − v²)`, which hold on the chain to `dirac_massless_limit`'s `O((ap)²)` and
`clock_rate_lorentz`'s error. A boost raises the momenta, so its lattice error grows with the
boosted momentum bound: `lattice_frame_residue` states it, and exact covariance is a continuum-limit
statement (~~#279~~).

⚠️ **The radar relation, not every record statistic**: slicing independence of spacelike joint
record laws is #285 (ii).

References: `specs/BACKLOG.md` #285, #39, ~~#278~~, ~~#279~~, ~~#280~~;
`RecordLayer/DiracTwoCharts.lean` (`radar_lorentz_exact`, `radar_lorentz_error`);
`RecordLayer/GalileanTransformation.lean` (`lorentzBoost`); `CV/DiracClockChain.lean` (`vRel`,
`dispE`); `CV/DiracPacketLimit.lean` (`dirac_packet_limit`, `limitErr`).
-/

@[expose] public section

open CSD.CV

namespace CSD.RecordLayer

/-- The velocity of `a` relative to `b`: `(a − b)/(1 − a b)`. -/
noncomputable def lorentzRelVel (a b : ℝ) : ℝ := (a - b) / (1 - a * b)

/-- Relativistic addition of velocities: `(u + v)/(1 + u v)`. -/
noncomputable def velAdd (u v : ℝ) : ℝ := (u + v) / (1 + u * v)

theorem one_sub_mul_pos {a b : ℝ} (ha : |a| < 1) (hb : |b| < 1) : 0 < 1 - a * b := by
  have h : |a * b| < 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg a, abs_nonneg b]
  linarith [le_abs_self (a * b)]

theorem one_add_mul_pos {a b : ℝ} (ha : |a| < 1) (hb : |b| < 1) : 0 < 1 + a * b := by
  have h : |a * b| < 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg a, abs_nonneg b]
  linarith [neg_abs_le (a * b)]

/-- `1 − w²` for the relative velocity: `(1 − a²)(1 − b²)/(1 − a b)²`. -/
theorem one_sub_lorentzRelVel_sq {a b : ℝ} (ha : |a| < 1) (hb : |b| < 1) :
    1 - lorentzRelVel a b ^ 2 = (1 - a ^ 2) * (1 - b ^ 2) / (1 - a * b) ^ 2 := by
  have h := (one_sub_mul_pos ha hb).ne'
  rw [lorentzRelVel]
  field_simp
  ring

/-- ★★★ **Radar in any frame.** `A` moves at `v_A`, `B` at `v_B` (`|v_A|, |v_B| < 1`), both
through the meeting at `t_M`; `B`'s messenger leaves at `t_E`, travels left at speed `1` and
reaches `A` at `t_R`; the echo travels right and reaches `B` at `t_Ret`. With proper-time rates
`s_A = √(1 − v_A²)`, `s_B = √(1 − v_B²)`, `B`'s radar coordinates of `A`'s event relative to the
meeting are the Lorentz boost at `−w`, `w = lorentzRelVel v_A v_B`, of `A`'s proper-time chart
`(s_A (t_R − t_M), 0)`. -/
theorem radar_lorentz_covariant {vA vB tE tR tRet tM : ℝ} (hA : |vA| < 1) (hB : |vB| < 1)
    (hE : vB * (tE - tM) - (tR - tE) = vA * (tR - tM))
    (hRet : vA * (tR - tM) + (tRet - tR) = vB * (tRet - tM)) :
    lorentzBoost 1 (-lorentzRelVel vA vB) (Real.sqrt (1 - vA ^ 2) * (tR - tM), 0)
      = (Real.sqrt (1 - vB ^ 2) * ((tE + tRet) / 2) - Real.sqrt (1 - vB ^ 2) * tM,
        -(Real.sqrt (1 - vB ^ 2) * ((tRet - tE) / 2))) := by
  have hA2 : 0 < 1 - vA ^ 2 := by nlinarith [sq_abs vA, abs_nonneg vA]
  have hB2 : 0 < 1 - vB ^ 2 := by nlinarith [sq_abs vB, abs_nonneg vB]
  have hAB := one_sub_mul_pos hA hB
  have hpB : 0 < 1 + vB := by linarith [neg_abs_le vB]
  have hmB : 0 < 1 - vB := by linarith [le_abs_self vB]
  set sA := Real.sqrt (1 - vA ^ 2) with hsA
  set sB := Real.sqrt (1 - vB ^ 2) with hsB
  have hsA2 : sA ^ 2 = 1 - vA ^ 2 := Real.sq_sqrt hA2.le
  have hsB2 : sB ^ 2 = 1 - vB ^ 2 := Real.sq_sqrt hB2.le
  have hsA0 : 0 < sA := Real.sqrt_pos.2 hA2
  have hsB0 : 0 < sB := Real.sqrt_pos.2 hB2
  -- the Lorentz factor at the relative velocity
  have hw : Real.sqrt (1 - (-lorentzRelVel vA vB) ^ 2 / 1 ^ 2) = sA * sB / (1 - vA * vB) := by
    rw [show (1 : ℝ) - (-lorentzRelVel vA vB) ^ 2 / 1 ^ 2 = 1 - lorentzRelVel vA vB ^ 2 by ring,
      one_sub_lorentzRelVel_sq hA hB, ← hsA2, ← hsB2,
      show sA ^ 2 * sB ^ 2 / (1 - vA * vB) ^ 2 = (sA * sB / (1 - vA * vB)) ^ 2 by
        field_simp]
    exact Real.sqrt_sq (by positivity)
  -- the emission and the return, relative to the meeting
  have he : tE - tM = (tR - tM) * (1 + vA) / (1 + vB) := by
    field_simp
    linarith
  have hr : tRet - tM = (tR - tM) * (1 - vA) / (1 - vB) := by
    field_simp
    linarith
  simp only [lorentzBoost, hw, Prod.mk.injEq]
  constructor
  · rw [show sB * ((tE + tRet) / 2) - sB * tM = sB * ((tE - tM) + (tRet - tM)) / 2 by ring,
      he, hr]
    field_simp
    rw [lorentzRelVel]
    field_simp
    rw [hsB2]
    ring
  · rw [show tRet - tE = (tRet - tM) - (tE - tM) by ring, he, hr]
    field_simp
    rw [lorentzRelVel]
    field_simp
    rw [hsB2]
    ring

/-- ★★ **A common boost leaves the relative velocity unchanged.** -/
theorem lorentzRelVel_velAdd {u a b : ℝ} (hu : |u| < 1) (ha : |a| < 1) (hb : |b| < 1) :
    lorentzRelVel (velAdd u a) (velAdd u b) = lorentzRelVel a b := by
  have h1 := (one_add_mul_pos hu ha).ne'
  have h2 := (one_add_mul_pos hu hb).ne'
  have h3 := (one_sub_mul_pos ha hb).ne'
  have hu2 : 0 < 1 - u ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]
  rw [lorentzRelVel, lorentzRelVel, velAdd, velAdd]
  have hden : 1 - (u + a) / (1 + u * a) * ((u + b) / (1 + u * b))
      = (1 - u ^ 2) * (1 - a * b) / ((1 + u * a) * (1 + u * b)) := by
    field_simp
    ring
  have hnum : (u + a) / (1 + u * a) - (u + b) / (1 + u * b)
      = (1 - u ^ 2) * (a - b) / ((1 + u * a) * (1 + u * b)) := by
    field_simp
    ring
  rw [hnum, hden]
  field_simp

/-- The boosted velocity is a velocity: `|velAdd u v| < 1`. -/
theorem abs_velAdd_lt {u v : ℝ} (hu : |u| < 1) (hv : |v| < 1) : |velAdd u v| < 1 := by
  have hpos := one_add_mul_pos hu hv
  rw [velAdd, abs_div, abs_of_pos hpos, div_lt_one hpos, abs_lt]
  have hu' := abs_lt.1 hu
  have hv' := abs_lt.1 hv
  constructor <;> nlinarith

/-- ★★★ **Frame covariance of the radar record relation.** For observers at `v_A`, `v_B` and the
same exchange seen in a frame boosted by `u`, both radar record relations are the Lorentz boost of
`A`'s proper-time chart at one and the same relative velocity: the records do not single out the
frame. -/
theorem radar_frame_covariant {u vA vB : ℝ} (hu : |u| < 1) (hA : |vA| < 1) (hB : |vB| < 1)
    {tE tR tRet tM tE' tR' tRet' tM' : ℝ}
    (hE : vB * (tE - tM) - (tR - tE) = vA * (tR - tM))
    (hRet : vA * (tR - tM) + (tRet - tR) = vB * (tRet - tM))
    (hE' : velAdd u vB * (tE' - tM') - (tR' - tE') = velAdd u vA * (tR' - tM'))
    (hRet' : velAdd u vA * (tR' - tM') + (tRet' - tR') = velAdd u vB * (tRet' - tM')) :
    lorentzRelVel (velAdd u vA) (velAdd u vB) = lorentzRelVel vA vB
    ∧ lorentzBoost 1 (-lorentzRelVel vA vB) (Real.sqrt (1 - vA ^ 2) * (tR - tM), 0)
      = (Real.sqrt (1 - vB ^ 2) * ((tE + tRet) / 2) - Real.sqrt (1 - vB ^ 2) * tM,
        -(Real.sqrt (1 - vB ^ 2) * ((tRet - tE) / 2)))
    ∧ lorentzBoost 1 (-lorentzRelVel vA vB)
        (Real.sqrt (1 - velAdd u vA ^ 2) * (tR' - tM'), 0)
      = (Real.sqrt (1 - velAdd u vB ^ 2) * ((tE' + tRet') / 2)
          - Real.sqrt (1 - velAdd u vB ^ 2) * tM',
        -(Real.sqrt (1 - velAdd u vB ^ 2) * ((tRet' - tE') / 2))) := by
  have hw := lorentzRelVel_velAdd hu hA hB
  refine ⟨hw, radar_lorentz_covariant hA hB hE hRet, ?_⟩
  rw [← hw]
  exact radar_lorentz_covariant (abs_velAdd_lt hu hA) (abs_velAdd_lt hu hB) hE' hRet'

/-- ★★ **A momentum boost adds velocities.** For rest energy `μ > 0`, a mode term `s` with energy
`E = √(μ² + s²)`, and a boost `u` (`|u| < 1`, `γ = 1/√(1 − u²)`), the boosted term
`s' = γ (s + u E)` has relativistic velocity `velAdd u (vRel s)`. -/
theorem vRel_boost {μ s u : ℝ} (hμ : 0 < μ) (hu : |u| < 1) :
    vRel 1 μ ((s + u * dispE μ s) / Real.sqrt (1 - u ^ 2)) = velAdd u (vRel 1 μ s) := by
  have hu2 : 0 < 1 - u ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]
  have hg0 : 0 < Real.sqrt (1 - u ^ 2) := Real.sqrt_pos.2 hu2
  have hg2 : Real.sqrt (1 - u ^ 2) ^ 2 = 1 - u ^ 2 := Real.sq_sqrt hu2.le
  set E := dispE μ s with hEdef
  have hE2 : E ^ 2 = μ ^ 2 + s ^ 2 := Real.sq_sqrt (by positivity)
  have hE0 : 0 < E := Real.sqrt_pos.2 (by positivity)
  have hsE : |s| < E := by
    rw [← abs_of_pos hE0]
    exact sq_lt_sq.1 (by rw [hE2]; nlinarith)
  have hus : |u * s| < E := by
    rw [abs_mul]
    calc |u| * |s| ≤ 1 * |s| := mul_le_mul_of_nonneg_right hu.le (abs_nonneg s)
      _ < E := by rw [one_mul]; exact hsE
  have hEus : 0 < E + u * s := by linarith [neg_abs_le (u * s)]
  have hE' : dispE μ ((s + u * E) / Real.sqrt (1 - u ^ 2))
      = (E + u * s) / Real.sqrt (1 - u ^ 2) := by
    rw [dispE]
    rw [show μ ^ 2 + ((s + u * E) / Real.sqrt (1 - u ^ 2)) ^ 2
      = ((E + u * s) / Real.sqrt (1 - u ^ 2)) ^ 2 by
        field_simp
        rw [hg2]
        nlinarith [hE2]]
    exact Real.sqrt_sq (by positivity)
  rw [vRel, hE', vRel, velAdd, ← hEdef]
  field_simp
  ring

/-! ### The lattice residue (#285 (iii)) -/

/-- **The relative velocity is Lipschitz** on velocities bounded by `V < 1`:
`|w(a, b) − w(a', b')| ≤ 2 (|a − a'| + |b − b'|)/(1 − V²)²`. -/
theorem abs_lorentzRelVel_sub_le {a b a' b' V : ℝ} (hV : V < 1) (ha : |a| ≤ V) (hb : |b| ≤ V)
    (ha' : |a'| ≤ V) (hb' : |b'| ≤ V) :
    |lorentzRelVel a b - lorentzRelVel a' b'| ≤ 2 * (|a - a'| + |b - b'|) / (1 - V ^ 2) ^ 2 := by
  have hV0 : 0 ≤ V := (abs_nonneg a).trans ha
  have hV2 : 0 < 1 - V ^ 2 := by nlinarith
  have hab : |a * b| ≤ V ^ 2 := by
    rw [abs_mul, sq]; exact mul_le_mul ha hb (abs_nonneg _) hV0
  have hab' : |a' * b'| ≤ V ^ 2 := by
    rw [abs_mul, sq]; exact mul_le_mul ha' hb' (abs_nonneg _) hV0
  have hd1 : 1 - V ^ 2 ≤ 1 - a * b := by linarith [le_abs_self (a * b)]
  have hd2 : 1 - V ^ 2 ≤ 1 - a' * b' := by linarith [le_abs_self (a' * b')]
  have hD : (1 - V ^ 2) ^ 2 ≤ (1 - a * b) * (1 - a' * b') := by
    rw [sq]; exact mul_le_mul hd1 hd2 hV2.le (by linarith)
  have hDpos : 0 < (1 - a * b) * (1 - a' * b') := lt_of_lt_of_le (by positivity) hD
  have hnum : lorentzRelVel a b - lorentzRelVel a' b'
      = ((a - a') * (1 - b * b') - (b - b') * (1 - a * a')) / ((1 - a * b) * (1 - a' * b')) := by
    rw [lorentzRelVel, lorentzRelVel, div_sub_div _ _ (by linarith) (by linarith)]
    congr 1
    ring
  have hbb : |1 - b * b'| ≤ 2 := by
    have : |b * b'| ≤ 1 := by
      rw [abs_mul]; nlinarith [abs_nonneg b, abs_nonneg b']
    calc |1 - b * b'| ≤ |1| + |b * b'| := abs_sub _ _
      _ ≤ 2 := by rw [abs_one]; linarith
  have haa : |1 - a * a'| ≤ 2 := by
    have : |a * a'| ≤ 1 := by
      rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg a']
    calc |1 - a * a'| ≤ |1| + |a * a'| := abs_sub _ _
      _ ≤ 2 := by rw [abs_one]; linarith
  have hN : |(a - a') * (1 - b * b') - (b - b') * (1 - a * a')| ≤ 2 * (|a - a'| + |b - b'|) := by
    calc |(a - a') * (1 - b * b') - (b - b') * (1 - a * a')|
        ≤ |(a - a') * (1 - b * b')| + |(b - b') * (1 - a * a')| := abs_sub _ _
      _ = |a - a'| * |1 - b * b'| + |b - b'| * |1 - a * a'| := by rw [abs_mul, abs_mul]
      _ ≤ |a - a'| * 2 + |b - b'| * 2 :=
          add_le_add (mul_le_mul_of_nonneg_left hbb (abs_nonneg _))
            (mul_le_mul_of_nonneg_left haa (abs_nonneg _))
      _ = 2 * (|a - a'| + |b - b'|) := by ring
  rw [hnum, abs_div, abs_of_pos hDpos]
  calc |(a - a') * (1 - b * b') - (b - b') * (1 - a * a')| / ((1 - a * b) * (1 - a' * b'))
      ≤ 2 * (|a - a'| + |b - b'|) / ((1 - a * b) * (1 - a' * b')) :=
        div_le_div_of_nonneg_right hN hDpos.le
    _ ≤ 2 * (|a - a'| + |b - b'|) / (1 - V ^ 2) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hD

/-- The lattice's departure from the relativistic velocity at momenta up to `P`:
`a² (P²/2 + P³/(6μ))` (`abs_scaledV_sub_le` at `c = 1`). -/
noncomputable def latticeVelErr (μ a P : ℝ) : ℝ := a ^ 2 * (P ^ 2 / 2 + P ^ 3 / (6 * μ))

/-- ★★★ **The lattice residue: how far the lattice frame shows up.** Two packets at momenta
`p_A`, `p_B` (`|p| ≤ P`) and their boosts by `u` (`|p'| ≤ P'`), on a lattice of spacing `a`, with
all velocities bounded by `V < 1`. The exact relative velocity is the same in both frames
(`lorentzRelVel_velAdd`, `vRel_boost`); the lattice's relative velocity in the boosted frame differs
from that in the original frame by at most `4 (latticeVelErr P + latticeVelErr P')/(1 − V²)²` —
order `a²`, growing with the boosted momentum bound `P'`, vanishing as `a → 0`. -/
theorem lattice_frame_residue {μ a P P' u V pA pB : ℝ} (hμ : 0 < μ) (ha : 0 < a) (hu : |u| < 1)
    (hV : V < 1) (hpA : |pA| ≤ P) (hpB : |pB| ≤ P)
    (hpA' : |(pA + u * dispE μ pA) / Real.sqrt (1 - u ^ 2)| ≤ P')
    (hpB' : |(pB + u * dispE μ pB) / Real.sqrt (1 - u ^ 2)| ≤ P')
    (hvA : |vRel 1 μ pA| ≤ V) (hvB : |vRel 1 μ pB| ≤ V)
    (hvA' : |velAdd u (vRel 1 μ pA)| ≤ V) (hvB' : |velAdd u (vRel 1 μ pB)| ≤ V)
    (hlA : |scaledV 1 μ a pA| ≤ V) (hlB : |scaledV 1 μ a pB| ≤ V)
    (hlA' : |scaledV 1 μ a ((pA + u * dispE μ pA) / Real.sqrt (1 - u ^ 2))| ≤ V)
    (hlB' : |scaledV 1 μ a ((pB + u * dispE μ pB) / Real.sqrt (1 - u ^ 2))| ≤ V) :
    |lorentzRelVel (scaledV 1 μ a ((pA + u * dispE μ pA) / Real.sqrt (1 - u ^ 2)))
        (scaledV 1 μ a ((pB + u * dispE μ pB) / Real.sqrt (1 - u ^ 2)))
      - lorentzRelVel (scaledV 1 μ a pA) (scaledV 1 μ a pB)|
      ≤ 4 * (latticeVelErr μ a P + latticeVelErr μ a P') / (1 - V ^ 2) ^ 2 := by
  have hV0 : 0 ≤ V := (abs_nonneg _).trans hvA
  have hV2 : 0 < 1 - V ^ 2 := by nlinarith
  have hvAlt : |vRel 1 μ pA| < 1 := lt_of_le_of_lt hvA hV
  have hvBlt : |vRel 1 μ pB| < 1 := lt_of_le_of_lt hvB hV
  -- the lattice velocities against the exact ones
  have eA := abs_scaledV_sub_le (c := 1) one_pos hμ ha hpA
  have eB := abs_scaledV_sub_le (c := 1) one_pos hμ ha hpB
  have eA' := abs_scaledV_sub_le (c := 1) one_pos hμ ha hpA'
  have eB' := abs_scaledV_sub_le (c := 1) one_pos hμ ha hpB'
  simp only [one_mul, one_pow] at eA eB eA' eB'
  rw [vRel_boost hμ hu] at eA' eB'
  have hE : ∀ Q, a ^ 2 * (Q ^ 2 / 2 + Q ^ 3 / (6 * μ)) = latticeVelErr μ a Q := fun Q => rfl
  rw [hE] at eA eB eA' eB'
  -- the exact relative velocity is the same in both frames
  have hw := lorentzRelVel_velAdd hu hvAlt hvBlt
  have l1 := abs_lorentzRelVel_sub_le hV hlA' hlB' hvA' hvB'
  have l2 := abs_lorentzRelVel_sub_le hV hvA hvB hlA hlB
  rw [hw] at l1
  have hsum : |lorentzRelVel (scaledV 1 μ a ((pA + u * dispE μ pA) / Real.sqrt (1 - u ^ 2)))
        (scaledV 1 μ a ((pB + u * dispE μ pB) / Real.sqrt (1 - u ^ 2)))
      - lorentzRelVel (scaledV 1 μ a pA) (scaledV 1 μ a pB)|
      ≤ 2 * (latticeVelErr μ a P' + latticeVelErr μ a P') / (1 - V ^ 2) ^ 2
        + 2 * (latticeVelErr μ a P + latticeVelErr μ a P) / (1 - V ^ 2) ^ 2 := by
    refine (abs_sub_le _ (lorentzRelVel (vRel 1 μ pA) (vRel 1 μ pB)) _).trans (add_le_add ?_ ?_)
    · refine l1.trans (div_le_div_of_nonneg_right ?_ (by positivity))
      linarith
    · refine l2.trans (div_le_div_of_nonneg_right ?_ (by positivity))
      rw [abs_sub_comm (vRel 1 μ pA), abs_sub_comm (vRel 1 μ pB)]
      linarith
  refine hsum.trans (le_of_eq ?_)
  field_simp
  ring

/-! ### Every encounter record is frame independent -/

/-- ★★ **A worldline in a boosted frame.** A segment `(Δt, v Δt)` of a worldline of velocity `v`,
boosted by `u`, is a segment of a worldline of velocity `lorentzRelVel v u = (v − u)/(1 − v u)`. -/
theorem lorentzBoost_worldline_vel {u v : ℝ} (hu : |u| < 1) (hv : |v| < 1) (Δt : ℝ) :
    (lorentzBoost 1 u (Δt, v * Δt)).2 = lorentzRelVel v u * (lorentzBoost 1 u (Δt, v * Δt)).1 := by
  have h := (one_sub_mul_pos hv hu).ne'
  simp only [lorentzBoost, lorentzRelVel]
  field_simp

/-- ★★★ **Proper time is the same in every frame.** The proper time along a segment `(Δt, v Δt)`
of a worldline, `√(1 − v²) Δt`, equals the proper time computed in the frame boosted by `u` —
`√(1 − w²) Δt'` with the boosted velocity `w` and the boosted duration `Δt'`. -/
theorem proper_time_boost {u v : ℝ} (hu : |u| < 1) (hv : |v| < 1) (Δt : ℝ) :
    Real.sqrt (1 - lorentzRelVel v u ^ 2) * (lorentzBoost 1 u (Δt, v * Δt)).1
      = Real.sqrt (1 - v ^ 2) * Δt := by
  have hu2 : 0 < 1 - u ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]
  have hv2 : 0 < 1 - v ^ 2 := by nlinarith [sq_abs v, abs_nonneg v]
  have hvu := one_sub_mul_pos hv hu
  have hsu0 : 0 < Real.sqrt (1 - u ^ 2) := Real.sqrt_pos.2 hu2
  have hsq : Real.sqrt (1 - lorentzRelVel v u ^ 2)
      = Real.sqrt (1 - v ^ 2) * Real.sqrt (1 - u ^ 2) / (1 - v * u) := by
    rw [one_sub_lorentzRelVel_sq hv hu, Real.sqrt_div' _ (sq_nonneg _),
      Real.sqrt_sq hvu.le, Real.sqrt_mul hv2.le]
  have hs : Real.sqrt (1 - u ^ 2 / 1 ^ 2) = Real.sqrt (1 - u ^ 2) := by
    rw [one_pow, div_one]
  rw [hsq]
  simp only [lorentzBoost, hs]
  field_simp

/-- ★★★ **A reading of an encounter is frame independent, within the records' errors.** The ideal
reading of an encounter is the observer's proper time from its clock's origin to the encounter,
`√(1 − v²) Δt` in one frame; by `proper_time_boost` it is the same number in the boosted frame. A
record read within `ε` of the ideal reading in the first frame, and within `ε'` in the boosted
preparation, gives readings within `ε + ε'` of each other. -/
theorem encounter_reading_covariant {u v Δt r r' ε ε' : ℝ} (hu : |u| < 1) (hv : |v| < 1)
    (hr : |r - Real.sqrt (1 - v ^ 2) * Δt| ≤ ε)
    (hr' : |r' - Real.sqrt (1 - lorentzRelVel v u ^ 2) * (lorentzBoost 1 u (Δt, v * Δt)).1| ≤ ε') :
    |r - r'| ≤ ε + ε' := by
  rw [proper_time_boost hu hv] at hr'
  calc |r - r'| ≤ |r - Real.sqrt (1 - v ^ 2) * Δt| + |r' - Real.sqrt (1 - v ^ 2) * Δt| := by
        rw [abs_sub_comm r' _]; exact abs_sub_le _ _ _
    _ ≤ ε + ε' := add_le_add hr hr'

/-- ★★★ **Every statistic of encounter records is frame independent, within the records' errors.**
`n` encounter readings, each read within `ε_k` of its ideal reading in one preparation and within
`ε'_k` in the boosted preparation, and any statistic `F` with `|F a − F b| ≤ K Σ |a_k − b_k|`: the
statistic differs between the two frames by at most `K Σ (ε_k + ε'_k)`. -/
theorem record_statistic_covariant {n : ℕ} {u : ℝ} (hu : |u| < 1) {v Δt r r' ε ε' : Fin n → ℝ}
    (hv : ∀ k, |v k| < 1)
    (hr : ∀ k, |r k - Real.sqrt (1 - v k ^ 2) * Δt k| ≤ ε k)
    (hr' : ∀ k, |r' k - Real.sqrt (1 - lorentzRelVel (v k) u ^ 2)
      * (lorentzBoost 1 u (Δt k, v k * Δt k)).1| ≤ ε' k)
    {F : (Fin n → ℝ) → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hF : ∀ a b : Fin n → ℝ, |F a - F b| ≤ K * ∑ k, |a k - b k|) :
    |F r - F r'| ≤ K * ∑ k, (ε k + ε' k) :=
  (hF r r').trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun k _ => encounter_reading_covariant hu (hv k) (hr k) (hr' k)) hK)

end CSD.RecordLayer
