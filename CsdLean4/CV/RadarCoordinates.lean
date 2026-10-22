/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.SignalExchange

/-!
# Radar coordinates from two clock readings, and their error bounds

**Category:** 3-Local (CV; the interface in which the clock-and-echo capstone states its
conclusion). BACKLOG #184 (out of #39; the second of #183–#189).

A single radar exchange is a pair of clock readings at `A`: the emission reading `τ₋` and the return
reading `τ₊`, with `τ₋ ≤ τ₊` as the **domain** of the assignment. From them

  `T_A = (τ₊ + τ₋) / 2`,   `D_A = (τ₊ − τ₋) / 2`,   `R_A = c₀ · D_A`,

the radar time, the radar separation in time units, and the radar distance once a **calibration
constant** `c₀ > 0` converts time units to length units.

* `RadarReadings` — the two readings with their domain; `radarTime`, `radarSep`, `radarDist`;
* `emit_le_radarTime`, `radarTime_le_ret`, `radarSep_nonneg`, `radarSep_eq_zero_iff` — the
  elementary bounds;
* ★ `radarTime_sub_radarSep`, `radarTime_add_radarSep`, `ext_of_radar` — **the readings and the
  coordinates determine each other**: equal readings give equal coordinates (by `congrArg`), and
  equal coordinates give equal readings;
* ★ `radarTime_shift`, `radarSep_shift`, `radarDist_shift` — **a clock-origin shift moves `T_A` and
  fixes `D_A`** and `R_A`;
* ★ `radarTime_rescale`, `radarSep_rescale`, `radarDist_rescale`, `radarDist_rescale_eq` — **a
  positive rescaling of the clock unit scales both coordinates**, and the calibration constant
  absorbs it: unit `λ` with constant `c₀` is unit `1` with constant `c₀ λ`;
* ★★ `abs_radarTime_sub_le`, `abs_radarSep_sub_le`, `abs_radarDist_sub_le` — **bounded endpoint
  errors give bounded coordinate errors**: `|T̂ − T| ≤ δ`, `|D̂ − D| ≤ δ`, `|R̂ − R| ≤ c₀ δ`;
* `radarSep_eq_of_duration_eq` — two exchanges of equal duration have equal separation;
  `radarSep_roundTrip` — an exchange lasting #183's round trip `2 τ_hop` has separation `τ_hop`;
* ★★ `radar_coordinates` — the package.

## Honest scope

* ⚠️ **Algebra with a stated domain.** Nothing here is a record: the readings are real numbers, not
  tick counts of a physical clock, and the association of the two readings with *one* exchange
  (which emission, which reflection) is part of the input. The record-level statement — that the
  readings are physical clock records of the constructed experiment and that the association is
  unambiguous — is #186's, and this module is honest only once #186 consumes it. It says so here.
* `c₀` is a calibration constant and nothing in this file makes it a signal speed; `radarDist_rescale_eq`
  is exactly the statement that it absorbs the choice of time unit.
* Deterministic endpoint error only (`|τ̂ − τ| ≤ δ`); probabilistic failure of a write is #189.
* Zero processing delay at `B`; a reflection protocol with delay is a later extension of #186.
* `radarSep_roundTrip` is the *arithmetic* of #183's witness, not its record: it says what number a
  clock reading the hop exactly would produce.

References: `specs/BACKLOG.md` #184, #183, #186, #187, #39; `specs/records-to-spacetime-scoping.md`
§4 (constants are constraints, not outputs); `CV/SignalExchange.lean` (`hopTime`, `roundTrip`).
-/

@[expose] public section

namespace CSD.CV

/-! ### Readings and coordinates -/

/-- **One radar exchange as read at `A`**: the emission reading `τ₋` and the return reading `τ₊`,
with `τ₋ ≤ τ₊` as the domain of the assignment. -/
@[ext]
structure RadarReadings where
  /-- The clock reading at emission. -/
  emit : ℝ
  /-- The clock reading at return. -/
  ret : ℝ
  /-- The domain: the return is read no earlier than the emission. -/
  emit_le_ret : emit ≤ ret

namespace RadarReadings

variable (r : RadarReadings)

/-- The radar time `T_A = (τ₊ + τ₋) / 2`. -/
noncomputable def radarTime : ℝ := (r.ret + r.emit) / 2

/-- The radar separation in time units, `D_A = (τ₊ − τ₋) / 2`. -/
noncomputable def radarSep : ℝ := (r.ret - r.emit) / 2

/-- The radar distance `R_A = c₀ · D_A`, with `c₀` a calibration constant converting time units to
length units. -/
noncomputable def radarDist (c₀ : ℝ) : ℝ := c₀ * r.radarSep

/-! ### Elementary bounds -/

theorem emit_le_radarTime : r.emit ≤ r.radarTime := by
  unfold radarTime
  linarith [r.emit_le_ret]

theorem radarTime_le_ret : r.radarTime ≤ r.ret := by
  unfold radarTime
  linarith [r.emit_le_ret]

theorem radarSep_nonneg : 0 ≤ r.radarSep := by
  unfold radarSep
  linarith [r.emit_le_ret]

theorem radarSep_eq_zero_iff : r.radarSep = 0 ↔ r.emit = r.ret := by
  unfold radarSep
  constructor <;> intro h <;> linarith

theorem radarDist_nonneg {c₀ : ℝ} (hc : 0 ≤ c₀) : 0 ≤ r.radarDist c₀ :=
  mul_nonneg hc r.radarSep_nonneg

/-! ### The readings and the coordinates determine each other -/

/-- `τ₋ = T_A − D_A`. -/
theorem radarTime_sub_radarSep : r.radarTime - r.radarSep = r.emit := by
  unfold radarTime radarSep
  ring

/-- `τ₊ = T_A + D_A`. -/
theorem radarTime_add_radarSep : r.radarTime + r.radarSep = r.ret := by
  unfold radarTime radarSep
  ring

/-- ★ **Equal coordinates give equal readings** (the converse, equal readings give equal
coordinates, is `congrArg`). -/
theorem ext_of_radar {r r' : RadarReadings} (hT : r.radarTime = r'.radarTime)
    (hD : r.radarSep = r'.radarSep) : r = r' := by
  ext
  · rw [← r.radarTime_sub_radarSep, ← r'.radarTime_sub_radarSep, hT, hD]
  · rw [← r.radarTime_add_radarSep, ← r'.radarTime_add_radarSep, hT, hD]

/-! ### A clock-origin shift -/

/-- Shift the clock origin by `s`: both readings move by `s`. -/
def shift (s : ℝ) : RadarReadings :=
  ⟨r.emit + s, r.ret + s, by linarith [r.emit_le_ret]⟩

/-- ★ A clock-origin shift moves the radar time by the shift. -/
theorem radarTime_shift (s : ℝ) : (r.shift s).radarTime = r.radarTime + s := by
  unfold radarTime shift
  simp only
  ring

/-- ★ A clock-origin shift leaves the radar separation unchanged. -/
theorem radarSep_shift (s : ℝ) : (r.shift s).radarSep = r.radarSep := by
  unfold radarSep shift
  simp only
  ring

theorem radarDist_shift (c₀ s : ℝ) : (r.shift s).radarDist c₀ = r.radarDist c₀ := by
  unfold radarDist
  rw [radarSep_shift]

/-! ### A positive rescaling of the clock unit -/

/-- Rescale the clock unit by `λ > 0`: both readings are multiplied by `λ`. -/
def rescale (lam : ℝ) (hlam : 0 < lam) : RadarReadings :=
  ⟨lam * r.emit, lam * r.ret, mul_le_mul_of_nonneg_left r.emit_le_ret hlam.le⟩

theorem radarTime_rescale (lam : ℝ) (hlam : 0 < lam) :
    (r.rescale lam hlam).radarTime = lam * r.radarTime := by
  unfold radarTime rescale
  simp only
  ring

theorem radarSep_rescale (lam : ℝ) (hlam : 0 < lam) :
    (r.rescale lam hlam).radarSep = lam * r.radarSep := by
  unfold radarSep rescale
  simp only
  ring

/-- ★ The coordinates transform consistently under a change of clock unit. -/
theorem radarDist_rescale (c₀ lam : ℝ) (hlam : 0 < lam) :
    (r.rescale lam hlam).radarDist c₀ = lam * r.radarDist c₀ := by
  unfold radarDist
  rw [radarSep_rescale]
  ring

/-- **The calibration constant absorbs the unit**: clock unit `λ` with constant `c₀` gives the same
distance as clock unit `1` with constant `c₀ λ`. Nothing fixes `c₀` on its own. -/
theorem radarDist_rescale_eq (c₀ lam : ℝ) (hlam : 0 < lam) :
    (r.rescale lam hlam).radarDist c₀ = r.radarDist (c₀ * lam) := by
  rw [radarDist_rescale]
  unfold radarDist
  ring

/-! ### Bounded endpoint errors give bounded coordinate errors -/

/-- ★★ `|T̂_A − T_A| ≤ δ` when each endpoint reading is off by at most `δ`. -/
theorem abs_radarTime_sub_le {r r' : RadarReadings} {δ : ℝ} (he : |r'.emit - r.emit| ≤ δ)
    (hr : |r'.ret - r.ret| ≤ δ) : |r'.radarTime - r.radarTime| ≤ δ := by
  unfold radarTime
  rw [abs_le] at he hr ⊢
  constructor <;> linarith [he.1, he.2, hr.1, hr.2]

/-- ★★ `|D̂_A − D_A| ≤ δ` when each endpoint reading is off by at most `δ`. -/
theorem abs_radarSep_sub_le {r r' : RadarReadings} {δ : ℝ} (he : |r'.emit - r.emit| ≤ δ)
    (hr : |r'.ret - r.ret| ≤ δ) : |r'.radarSep - r.radarSep| ≤ δ := by
  unfold radarSep
  rw [abs_le] at he hr ⊢
  constructor <;> linarith [he.1, he.2, hr.1, hr.2]

/-- ★★ `|R̂_A − R_A| ≤ c₀ δ` for a fixed nonnegative calibration constant. -/
theorem abs_radarDist_sub_le {r r' : RadarReadings} {δ c₀ : ℝ} (hc : 0 ≤ c₀)
    (he : |r'.emit - r.emit| ≤ δ) (hr : |r'.ret - r.ret| ≤ δ) :
    |r'.radarDist c₀ - r.radarDist c₀| ≤ c₀ * δ := by
  unfold radarDist
  rw [← mul_sub, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (abs_radarSep_sub_le he hr) hc

/-! ### Reproducibility, and the arithmetic of #183's witness -/

/-- Two exchanges of equal duration have equal separation, whatever their emission readings. -/
theorem radarSep_eq_of_duration_eq {r r' : RadarReadings} (h : r.ret - r.emit = r'.ret - r'.emit) :
    r.radarSep = r'.radarSep := by
  unfold radarSep
  rw [h]

/-- The readings of an exchange emitted at `τ` and lasting `d ≥ 0`. -/
def ofDuration (τ d : ℝ) (hd : 0 ≤ d) : RadarReadings := ⟨τ, τ + d, by linarith⟩

theorem radarSep_ofDuration (τ d : ℝ) (hd : 0 ≤ d) : (ofDuration τ d hd).radarSep = d / 2 := by
  unfold radarSep ofDuration
  simp only
  ring

/-- **The arithmetic of #183's witness**: an exchange lasting the round trip `2 τ_hop` has radar
separation `τ_hop`, whatever the emission reading. This is what a clock reading the hop exactly
would produce; that the readings *are* such records is #186. -/
theorem radarSep_roundTrip {J ħ : ℝ} (hJ : 0 < J) (hħ : 0 < ħ) (τ : ℝ) :
    (ofDuration τ (roundTrip J ħ) (roundTrip_pos hJ hħ).le).radarSep = hopTime J ħ := by
  rw [radarSep_ofDuration, roundTrip]
  ring

/-! ### The package -/

/-- ★★ **Radar coordinates.** On the domain `τ₋ ≤ τ₊`: `τ₋ ≤ T_A ≤ τ₊`, `D_A ≥ 0`; the readings
are recovered from the coordinates; a clock-origin shift moves `T_A` by the shift and fixes `D_A`;
a positive rescaling of the clock unit scales both; endpoint errors `≤ δ` give coordinate errors
`≤ δ` and a distance error `≤ c₀ δ`. -/
theorem radar_coordinates (r : RadarReadings) :
    (r.emit ≤ r.radarTime ∧ r.radarTime ≤ r.ret)
      ∧ 0 ≤ r.radarSep
      ∧ (r.radarTime - r.radarSep = r.emit ∧ r.radarTime + r.radarSep = r.ret)
      ∧ (∀ s : ℝ, (r.shift s).radarTime = r.radarTime + s ∧ (r.shift s).radarSep = r.radarSep)
      ∧ (∀ (lam : ℝ) (hlam : 0 < lam),
          (r.rescale lam hlam).radarTime = lam * r.radarTime
            ∧ (r.rescale lam hlam).radarSep = lam * r.radarSep)
      ∧ (∀ (r' : RadarReadings) (δ c₀ : ℝ), 0 ≤ c₀ →
          |r'.emit - r.emit| ≤ δ → |r'.ret - r.ret| ≤ δ →
            |r'.radarTime - r.radarTime| ≤ δ ∧ |r'.radarSep - r.radarSep| ≤ δ
              ∧ |r'.radarDist c₀ - r.radarDist c₀| ≤ c₀ * δ) :=
  ⟨⟨r.emit_le_radarTime, r.radarTime_le_ret⟩, r.radarSep_nonneg,
    ⟨r.radarTime_sub_radarSep, r.radarTime_add_radarSep⟩,
    fun s => ⟨r.radarTime_shift s, r.radarSep_shift s⟩,
    fun lam hlam => ⟨r.radarTime_rescale lam hlam, r.radarSep_rescale lam hlam⟩,
    fun _ _ _ hc he hr =>
      ⟨abs_radarTime_sub_le he hr, abs_radarSep_sub_le he hr, abs_radarDist_sub_le hc he hr⟩⟩

end RadarReadings

end CSD.CV

end
