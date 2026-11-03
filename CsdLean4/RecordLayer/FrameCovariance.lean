/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracTwoCharts

/-!
# Frame covariance of the radar records

**Category:** 7-SigmaLayer (the record layer). BACKLOG #285, part (i).

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

* ★★ `lorentzRelVel_velAdd` (**boosting both observers by `u` leaves their relative velocity unchanged**);
* ★★★ `radar_frame_covariant` (**a preparation and its boost give the same radar record relation:
  the Lorentz boost at the same `w`**).

## Boosted preparations on the chain

* ★★ `vRel_boost` (**the chain's relativistic mode velocity under a momentum boost
  `s' = γ_u (s + u E)` is `velAdd u (vRel s)`**) — so a boosted packet is a packet at a boosted
  momentum, and `dirac_packet_limit`, which holds at every centre momentum, moves it at the boosted
  velocity within its error at the boosted momentum bound.

## Honest scope

⚠️ **Kinematic records**: the covariance is of the radar relation — light at speed `1`, clocks at
`√(1 − v²)`, which hold on the chain to `dirac_massless_limit`'s `O((ap)²)` and
`clock_rate_lorentz`'s error. A boost raises the momenta, so its lattice error grows with the
boosted momentum bound (`limitErr`'s `a² P³` term): exact covariance is a continuum-limit statement
(#285 (iii), ~~#279~~).

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

end CSD.RecordLayer
