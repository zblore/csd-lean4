/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedClockPacket

/-!
# Narrow clock packets tick as often as wanted

**Category:** 7-SigmaLayer (the record layer). BACKLOG #391 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; step (2) of the plan of
2026-11-14, the probe of the moving observer, Remainder (a) of #388. No new assumption.

#388 (`clock_packet_ticks`) bounds every tick count of a clock packet under three conditions
that are hypotheses, shows no packet of more than one mode meeting them, and shows no tick.
This module discharges the conditions for every sufficiently narrow window of modes and shows
that the count is at least any wanted number.

* ★★ `clock_packet_count_ge` — under the hypotheses of `clock_packet_ticks`, if the phase
  `R T` has reached `2π (n − 1) + π` the count at `T` exists and is at least `n`;
* `half_le_levelClockRate`, `levelClockRate_le_gap` — the clock with levels `1` and `1 + Δ`
  runs at a rate in `[Δ/2, Δ]` wherever the momentum term has `s² ≤ 3`;
* `ringLen`, `ringHop`, `ringSigma`, `ringRate`, `ringLen_pos`, `two_ringHop`,
  `abs_ringSigma_le`, `ringSigma_pos`, `ringSigma_sq_le`, `two_ringHop_mul_sin_angleZ`,
  `dispE_one_le_two`, `two_div_pi_mul_le_ringSigma`, ★ `div_pi_le_vRel_ringSigma` (in the
  lower half of the band `p/π ≤ σ/E₀`), `abs_div_horizon_sub_le`;
* ★★★ `narrow_clock_packet_ticks` — on a ring of length `2π K`: reference momentum
  `0 ≤ p₀ ≤ 9/10` with `6 K p₀ ≤ M + 1`, any window of modes within `1/(600 n)` of `p₀` or
  of `−p₀` (#409), any
  normalised amplitudes, any gap `0 < Δ ≤ 1/2`. For some strength of the coupling, at
  `T = 2π n/R` the count `N` exists, `N ≥ n`,
  `|2π N/Δ − √(1 − v²) T| ≤ 2π/Δ + (Δ/E₀) T`, the same as a rate
  `|2π N/(Δ T) − √(1 − v²)| ≤ 1/n + Δ`, and `v ≥ p₀/π`;
* `modeWindow`, `flatAmp`, `sum_norm_flatAmp`, ★★ `exists_clock_packet_ticks` — the `2 w + 1`
  modes centred on `600 n (w + 1)` of the ring of length `2π · 1200 n (w + 1)`, with equal
  amplitudes, meet those hypotheses, for every `n ≥ 1` and every `w`.

## Exact scope

* **A clock, not an observer.** As #388: the clock carrier and its own pointer. No messenger,
  no detector, no meeting, no second observer. What a moving observer is in `Σ` is not
  settled by this module.
* **One flow time.** The count is taken at the single flow time `T = 2π n/R`. The rate form
  divides that one count by that one time.
* **More ticks need a narrower packet.** `n` ticks are shown for momentum width at most
  `1/(600 n)`. For a fixed window the number of ticks shown is bounded; nothing here says
  what happens after the horizon.
* **Localisation in space is not shown.** A window of `2 w + 1` modes is a statement about
  momenta. That such a packet occupies about a fraction `1/(2 w + 1)` of the ring is a
  calculation, not in Lean; no occupancy of the clock carrier is bounded here. `w = 0` is
  one mode and is allowed. #392 (`RecordLayer/UnifiedClockPacketLocalised.lean`) bounds the
  weight away from the predicted position for a flat window.
* **Whether the dilation is resolved depends on the choice of `n` and `Δ`.** The error
  `1/n + Δ` is to be compared with `1 − √(1 − v²) ≥ v²/2`. No instance in this module makes
  that comparison; #392 does (`flat_clock_packet_rate_lt`).
* **`v` is `σ/E₀`, not a velocity shown of the packet.** `σ` is the lattice momentum term at
  the reference momentum. The band's group velocity is `v cos(a p₀)` with
  `a p₀ ≤ π/3` under the hypothesis, so at least `v/2` (a calculation, not in Lean). That
  the packet moves at any velocity is not shown here, and no position is recorded.
* **The strength is not in the statement.** The three main theorems say "for some strength";
  the proof uses `R/(16 Im C₀)`, tuned to the packet (UA-4). `clock_packet_count_ge` keeps
  the equation as a hypothesis.
* **One fibre and one start**, as #388: profile `trainF` on the fibre `0`, where the pointer
  does not act back on the clock; pointer starting at `1/12`; packet prepared a quarter turn
  early. A null set of starts.
* **The count is compared with the flow time** (UA-7). No record holds `T`, and `T` is chosen
  as `2π n/R`, which uses the rate.
* **Units.** Speed `1` and lower level `1`; the numbers `600`, `9/10`, `1/2` are not sharp.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-4,
UA-7, UA-12, UO-16, UD-137, UD-138, UD-141, UD-142); `RecordLayer/UnifiedClockPacket.lean`
(#388: `clock_packet_ticks`, `modeRate`); `RecordLayer/UnifiedDiracClockTicks.lean` (#358:
`IsSwing.hasTicks`, `IsSwing.exists_tickCount`, `HasTicks.mono_count`, `IsTickCount`);
`CV/DiracClockChain.lean` (`clockRate_mem`, `dispE`, `vRel`, `levelClockRate`);
`RecordLayer/DiracDeviceTicks.lean` (`deviceDrift`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### A count of at least `n` inside the horizon -/

section Count

variable {M : ℕ}

/-- ★★ **A clock packet whose horizon holds `n` half-completed turns has a count of at least
`n`.** Under the hypotheses of `clock_packet_ticks`, if the phase `R T` has reached
`2π (n − 1) + π`, the pointer's history has a tick count `N ≥ n` at `T`, and that count obeys
the dilated clock bound. -/
theorem clock_packet_count_ge {c μ₀ μ₁ ℓ D p₀ : ℝ} (hc : 0 < c) (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
    (hℓ : 0 < ℓ) {W : Finset ℤ} {lo : ℤ}
    (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + (M + 1 : ℕ))
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D ∨ |2 * Real.pi * m / ℓ + p₀| ≤ D)
    (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) {J σ R ε : ℝ} (hJ : J = scaledHop c (ℓ / (M + 1 : ℕ)))
    (hσ : σ = 2 * J * Real.sin (ℓ / (M + 1 : ℕ) * p₀)) (hR : R = levelClockRate μ₀ μ₁ σ)
    (hε : ε = deviceDrift c μ₀ μ₁ D p₀) {ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hρm : ∀ m ∈ W, ρ ≤ modeRate M J μ₀ μ₁ m) {g : ℝ}
    (hg : g = R / (16 * (deviceCoherence
      (devicePacket (L := M + 1) J μ₀ μ₁ W β (-(Real.pi / (2 * R))))).im))
    (hκ : 0 < (1 - ((μ₁ - μ₀) / μ₀) ^ 2) / 2 - Real.pi / (2 * R) * ε) {T : ℝ} (hT : 0 ≤ T)
    (hsmall : R * ε * (2 * T / ρ + 3 / ρ ^ 2 + Real.pi / (2 * R ^ 2))
      < ((1 - ((μ₁ - μ₀) / μ₀) ^ 2) / 2 - Real.pi / (2 * R) * ε) / 3)
    {n : ℕ} (hn : ((n : ℝ) - 1) * (2 * Real.pi) + Real.pi ≤ R * T) :
    ∃ (hΨ : devicePacket (L := M + 1) J μ₀ μ₁ W β (-(Real.pi / (2 * R))) ≠ 0) (N : ℕ),
      n ≤ N
      ∧ IsTickCount (tickReady M) (tickDisplay M)
          (fun t => clockPointerFlow M J μ₀ μ₁ g trainF_periodic contDiff_trainF t
            (clockArenaEquiv M (deviceRay _ hΨ),
              ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))))) T N
      ∧ |clockOpTime μ₀ μ₁ N - Real.sqrt (1 - (vRel c μ₀ σ / c) ^ 2) * T|
          ≤ 2 * Real.pi / (μ₁ - μ₀) + (μ₁ - μ₀) / dispE μ₀ σ * T := by
  obtain ⟨hΨ, δ, -, -, hsw, hall⟩ := clock_packet_ticks hc h0 h01 hℓ hWin hWD β hβ hJ hσ hR hε
    hρ hρR hρm hg hκ hT hsmall
  obtain ⟨N, hN⟩ := hsw.exists_tickCount hT
  refine ⟨hΨ, N, ?_, hN, hall N hN⟩
  by_contra hlt
  rw [not_le] at hlt
  exact hN.2 ((hsw.hasTicks hn).mono_count hlt)

end Count

/-! ### The rate of the clock with levels `1` and `1 + Δ` -/

/-- The clock with levels `1` and `1 + Δ` runs at a rate of at least `Δ/2` at a lattice
momentum term `s` with `s² ≤ 3`. -/
theorem half_le_levelClockRate {Δ s : ℝ} (hΔ : 0 ≤ Δ) (hs : s ^ 2 ≤ 3) :
    Δ / 2 ≤ levelClockRate 1 (1 + Δ) s := by
  have h := (clockRate_mem (μ₀ := 1) (μ₁ := 1 + Δ) one_pos (by linarith) s).1
  rw [add_sub_cancel_left] at h
  have hpos := dispE_pos (μ := 1) one_pos s
  have hle : dispE 1 s ≤ 2 := by
    rw [dispE, show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have h2 : (1 : ℝ) / 2 ≤ 1 / dispE 1 s := by
    rw [le_div_iff₀ hpos]
    linarith
  have h3 : Δ * (1 / 2) ≤ Δ * (1 / dispE 1 s) := mul_le_mul_of_nonneg_left h2 hΔ
  linarith

/-- The clock with levels `1` and `1 + Δ` runs at a rate of at most `Δ`. -/
theorem levelClockRate_le_gap {Δ : ℝ} (hΔ : 0 ≤ Δ) (s : ℝ) :
    levelClockRate 1 (1 + Δ) s ≤ Δ := by
  have h := (clockRate_mem (μ₀ := 1) (μ₁ := 1 + Δ) one_pos (by linarith) s).2
  rw [add_sub_cancel_left] at h
  have hpos := dispE_pos (μ := 1 + Δ) (by linarith) s
  have h2 : (1 + Δ) / dispE (1 + Δ) s ≤ 1 := by
    rw [div_le_one hpos]
    exact le_dispE _ s
  have h3 : Δ * ((1 + Δ) / dispE (1 + Δ) s) ≤ Δ * 1 := mul_le_mul_of_nonneg_left h2 hΔ
  linarith

/-! ### Any narrow packet on a ring of length `2π K` -/

/-- **The ring's length**: `2π K`, so that mode `m` has momentum `m/K`. -/
def ringLen (K : ℕ) : ℝ := 2 * Real.pi * K

/-- **The hopping**: speed `1` on a ring of length `ringLen K` with `M + 1` sites. -/
def ringHop (K M : ℕ) : ℝ := scaledHop 1 (ringLen K / (M + 1 : ℕ))

/-- **The lattice momentum term at the momentum `p`.** -/
def ringSigma (K M : ℕ) (p : ℝ) : ℝ :=
  2 * ringHop K M * Real.sin (ringLen K / (M + 1 : ℕ) * p)

/-- **The reference rate**: the splitting of the levels `1` and `1 + Δ` at the momentum
`p`. -/
def ringRate (K M : ℕ) (p Δ : ℝ) : ℝ := levelClockRate 1 (1 + Δ) (ringSigma K M p)

theorem ringLen_pos {K : ℕ} (hK : 0 < K) : 0 < ringLen K := by
  have : (0 : ℝ) < K := by exact_mod_cast hK
  have := Real.pi_pos
  rw [ringLen]
  positivity

theorem two_ringHop {K : ℕ} (hK : 0 < K) (M : ℕ) :
    2 * ringHop K M = ((M + 1 : ℕ) : ℝ) / ringLen K := by
  have hL := ringLen_pos hK
  have hM : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  rw [ringHop, scaledHop]
  field_simp

/-- A lattice momentum term is at most the momentum in size. -/
theorem abs_ringSigma_le {K : ℕ} (hK : 0 < K) (M : ℕ) (x : ℝ) : |ringSigma K M x| ≤ |x| := by
  have hL := ringLen_pos hK
  have hM : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  rw [ringSigma, two_ringHop hK, abs_mul, abs_of_pos (div_pos hM hL)]
  calc ((M + 1 : ℕ) : ℝ) / ringLen K * |Real.sin (ringLen K / (M + 1 : ℕ) * x)|
      ≤ ((M + 1 : ℕ) : ℝ) / ringLen K * |ringLen K / (M + 1 : ℕ) * x| :=
        mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (div_pos hM hL).le
    _ = |x| := by
        rw [abs_mul, abs_of_pos (div_pos hL hM)]
        field_simp

/-- The momentum term is positive at a positive momentum below the band's edge. -/
theorem ringSigma_pos {K M : ℕ} (hK : 0 < K) {p : ℝ} (hp : 0 < p)
    (hM : 2 * K * p < ((M + 1 : ℕ) : ℝ)) : 0 < ringSigma K M p := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hM1 : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  have hπ := Real.pi_pos
  have harg : ringLen K / (M + 1 : ℕ) * p = Real.pi * (2 * K * p / ((M + 1 : ℕ) : ℝ)) := by
    rw [ringLen]
    field_simp
  have hfr0 : (0 : ℝ) < 2 * K * p / ((M + 1 : ℕ) : ℝ) := by positivity
  have hfr1 : 2 * K * p / ((M + 1 : ℕ) : ℝ) < 1 := (div_lt_one hM1).2 hM
  rw [ringSigma, two_ringHop hK, harg]
  refine mul_pos (div_pos hM1 (ringLen_pos hK)) (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_)
  calc Real.pi * (2 * K * p / ((M + 1 : ℕ) : ℝ)) < Real.pi * 1 :=
        mul_lt_mul_of_pos_left hfr1 hπ
    _ = Real.pi := mul_one _

theorem ringSigma_sq_le {K : ℕ} (hK : 0 < K) (M : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    ringSigma K M x ^ 2 ≤ 3 := by
  have h1 : |ringSigma K M x| ≤ 1 := (abs_ringSigma_le hK M x).trans hx
  have h2 : ringSigma K M x ^ 2 ≤ 1 ^ 2 :=
    sq_le_sq' (by linarith [(abs_le.1 h1).1]) (abs_le.1 h1).2
  linarith

/-- The momentum term of mode `m` is the momentum term at the momentum `m/K`. -/
theorem two_ringHop_mul_sin_angleZ {K : ℕ} (hK : 0 < K) (M : ℕ) (m : ℤ) :
    2 * ringHop K M * Real.sin (angleZ (M + 1) m) = ringSigma K M ((m : ℝ) / K) := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hM1 : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  have harg : angleZ (M + 1) m = ringLen K / (M + 1 : ℕ) * ((m : ℝ) / K) := by
    rw [angleZ, ringLen]
    field_simp
  rw [ringSigma, harg]

/-- The band energy at rest energy `1` is at most `2` where the momentum term has `s² ≤ 3`. -/
theorem dispE_one_le_two {s : ℝ} (hs : s ^ 2 ≤ 3) : dispE 1 s ≤ 2 := by
  rw [dispE, show (2 : ℝ) = Real.sqrt 4 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by linarith)

/-- **The momentum term is at least `2/π` of the momentum** in the lower half of the band
(`4 K p ≤ M + 1`). -/
theorem two_div_pi_mul_le_ringSigma {K M : ℕ} (hK : 0 < K) {p : ℝ} (hp : 0 ≤ p)
    (hM : 4 * K * p ≤ ((M + 1 : ℕ) : ℝ)) : 2 / Real.pi * p ≤ ringSigma K M p := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hM1 : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  have hπ := Real.pi_pos
  have hL := ringLen_pos hK
  have hx0 : 0 ≤ ringLen K / (M + 1 : ℕ) * p := mul_nonneg (div_pos hL hM1).le hp
  have hx1 : ringLen K / (M + 1 : ℕ) * p ≤ Real.pi / 2 := by
    rw [ringLen, div_mul_eq_mul_div, div_le_div_iff₀ hM1 (by norm_num)]
    nlinarith
  have h := Real.mul_le_sin hx0 hx1
  rw [ringSigma, two_ringHop hK]
  calc 2 / Real.pi * p
      = ((M + 1 : ℕ) : ℝ) / ringLen K * (2 / Real.pi * (ringLen K / (M + 1 : ℕ) * p)) := by
        field_simp
    _ ≤ ((M + 1 : ℕ) : ℝ) / ringLen K * Real.sin (ringLen K / (M + 1 : ℕ) * p) :=
        mul_le_mul_of_nonneg_left h (div_pos hM1 hL).le

/-- ★ **A lower bound of the velocity that goes with the momentum term**: `p/π ≤ σ/E₀` in
the lower half of the band, for `0 ≤ p ≤ 1`. -/
theorem div_pi_le_vRel_ringSigma {K M : ℕ} (hK : 0 < K) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hM : 4 * K * p ≤ ((M + 1 : ℕ) : ℝ)) : p / Real.pi ≤ vRel 1 1 (ringSigma K M p) := by
  have hπ := Real.pi_pos
  have hσ := two_div_pi_mul_le_ringSigma hK hp hM
  have hσ0 : 0 ≤ ringSigma K M p := le_trans (by positivity) hσ
  have hE := dispE_pos (μ := 1) one_pos (ringSigma K M p)
  have hE2 := dispE_one_le_two (ringSigma_sq_le hK M (by rw [abs_of_nonneg hp]; exact hp1))
  rw [vRel, one_mul, le_div_iff₀ hE]
  have e : p / Real.pi = 2 / Real.pi * p / 2 := by ring
  have h1 : p / Real.pi * dispE 1 (ringSigma K M p) ≤ p / Real.pi * 2 :=
    mul_le_mul_of_nonneg_left hE2 (by positivity)
  rw [e] at h1 ⊢
  linarith

/-- **The count bound as a rate.** If `|A − s T| ≤ 2π/Δ + (Δ/E) T` at the horizon
`T = 2π n/R`, with `R ≤ Δ` and `E ≥ 1`, then `|A/T − s| ≤ 1/n + Δ`. -/
theorem abs_div_horizon_sub_le {A s Δ E R n : ℝ} (hn : 0 < n) (hΔ0 : 0 < Δ) (hR0 : 0 < R)
    (hRΔ : R ≤ Δ) (hE : 1 ≤ E)
    (h : |A - s * (2 * Real.pi * n / R)| ≤ 2 * Real.pi / Δ + Δ / E * (2 * Real.pi * n / R)) :
    |A / (2 * Real.pi * n / R) - s| ≤ 1 / n + Δ := by
  have hπ := Real.pi_pos
  have hTpos : 0 < 2 * Real.pi * n / R := by positivity
  have e : A / (2 * Real.pi * n / R) - s
      = (A - s * (2 * Real.pi * n / R)) / (2 * Real.pi * n / R) := by
    field_simp
  rw [e, abs_div, abs_of_pos hTpos, div_le_iff₀ hTpos]
  have e2 : 1 / n * (2 * Real.pi * n / R) = 2 * Real.pi / R := by
    field_simp
  have h1 : 2 * Real.pi / Δ ≤ 1 / n * (2 * Real.pi * n / R) := by
    rw [e2]
    exact div_le_div_of_nonneg_left (by positivity) hR0 hRΔ
  have h2 : Δ / E * (2 * Real.pi * n / R) ≤ Δ * (2 * Real.pi * n / R) := by
    refine mul_le_mul_of_nonneg_right ?_ hTpos.le
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have e3 : (1 / n + Δ) * (2 * Real.pi * n / R)
      = 1 / n * (2 * Real.pi * n / R) + Δ * (2 * Real.pi * n / R) := by ring
  rw [e3]
  linarith

/-- ★★★ **Every narrow clock packet ticks at least `n` times inside its horizon.** On a ring
of length `2π K` with `M + 1` sites, take a reference momentum `0 ≤ p₀ ≤ 9/10` in the lower
part of the band (`6 K p₀ ≤ M + 1`), any window of modes whose momenta `m/K` lie within
`1/(600 n)` of `p₀` or of `−p₀`, any normalised amplitudes on it, and a level gap `0 < Δ ≤ 1/2`. For the
clock with levels `1` and `1 + Δ`, prepared as the device's packet, there is a strength of
the coupling to a pointer of profile `trainF` starting at `1/12` on the fibre `0` for which
the pointer's history has at the flow time `T = 2π n/R` a tick count `N ≥ n`, with

`|2π N/Δ − √(1 − v²) T| ≤ 2π/Δ + (Δ/E₀) T` and `|2π N/(Δ T) − √(1 − v²)| ≤ 1/n + Δ`.

Here `σ = ringSigma K M p₀`, `E₀ = dispE 1 σ`, `v = vRel 1 1 σ = σ/E₀ ≥ p₀/π`, and
`R = ringRate K M p₀ Δ` is the level splitting at `σ`. Every hypothesis of
`clock_packet_ticks` is discharged. The proof uses the strength `R/(16 Im C₀)`; the
statement does not record it. -/
theorem narrow_clock_packet_ticks {n K M : ℕ} (hn : 0 < n) (hK : 0 < K) {p₀ : ℝ}
    (hp0 : 0 ≤ p₀) (hp1 : p₀ ≤ 9 / 10) (hM : 6 * K * p₀ ≤ ((M + 1 : ℕ) : ℝ))
    {W : Finset ℤ} {lo : ℤ} (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + (M + 1 : ℕ))
    (hWD : ∀ m ∈ W, |(m : ℝ) / K - p₀| ≤ 1 / (600 * n) ∨ |(m : ℝ) / K + p₀| ≤ 1 / (600 * n))
    (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2) :
    p₀ / Real.pi ≤ vRel 1 1 (ringSigma K M p₀)
    ∧ ∃ (g : ℝ) (hΨ : devicePacket (L := M + 1) (ringHop K M) 1 (1 + Δ) W β
          (-(Real.pi / (2 * ringRate K M p₀ Δ))) ≠ 0) (N : ℕ),
      n ≤ N
      ∧ IsTickCount (tickReady M) (tickDisplay M)
          (fun t => clockPointerFlow M (ringHop K M) 1 (1 + Δ) g trainF_periodic
            contDiff_trainF t
            (clockArenaEquiv M (deviceRay _ hΨ),
              ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))))
          (2 * Real.pi * n / ringRate K M p₀ Δ) N
      ∧ |clockOpTime 1 (1 + Δ) N
            - Real.sqrt (1 - (vRel 1 1 (ringSigma K M p₀) / 1) ^ 2)
              * (2 * Real.pi * n / ringRate K M p₀ Δ)|
          ≤ 2 * Real.pi / Δ
            + Δ / dispE 1 (ringSigma K M p₀) * (2 * Real.pi * n / ringRate K M p₀ Δ)
      ∧ |clockOpTime 1 (1 + Δ) N / (2 * Real.pi * n / ringRate K M p₀ Δ)
            - Real.sqrt (1 - (vRel 1 1 (ringSigma K M p₀) / 1) ^ 2)| ≤ 1 / n + Δ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1n : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hπ := Real.pi_pos
  have hπu : Real.pi < 3.15 := Real.pi_lt_d2
  have hD1 : (1 : ℝ) / (600 * n) ≤ 1 / 600 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hD0 : (0 : ℝ) < 1 / (600 * n) := by positivity
  have hσsq : ringSigma K M p₀ ^ 2 ≤ 3 :=
    ringSigma_sq_le hK M (by rw [abs_of_nonneg hp0]; linarith)
  have hRlo : Δ / 2 ≤ ringRate K M p₀ Δ := half_le_levelClockRate hΔ0.le hσsq
  have hRhi : ringRate K M p₀ Δ ≤ Δ := levelClockRate_le_gap hΔ0.le _
  have hR0 : 0 < ringRate K M p₀ Δ := by linarith
  set R := ringRate K M p₀ Δ with hRd
  -- the modes
  have hWD' : ∀ m ∈ W, |2 * Real.pi * m / ringLen K - p₀| ≤ 1 / (600 * n)
      ∨ |2 * Real.pi * m / ringLen K + p₀| ≤ 1 / (600 * n) := by
    intro m hm
    have e : 2 * Real.pi * (m : ℝ) / ringLen K = (m : ℝ) / K := by
      rw [ringLen]
      field_simp
    rw [e]
    exact hWD m hm
  have hρm : ∀ m ∈ W, Δ / 2 ≤ modeRate M (ringHop K M) 1 (1 + Δ) m := by
    intro m hm
    have hm1 : |(m : ℝ) / K| ≤ 1 := by
      rcases hWD m hm with h | h
      · have h := abs_le.1 h
        rw [abs_le]
        constructor <;> linarith [h.1, h.2]
      · have h := abs_le.1 h
        rw [abs_le]
        constructor <;> linarith [h.1, h.2]
    rw [modeRate, two_ringHop_mul_sin_angleZ hK]
    exact half_le_levelClockRate hΔ0.le (ringSigma_sq_le hK M hm1)
  -- the drift is `Δ u`
  set u := 1 / (600 * (n : ℝ)) * (2 * p₀ + 1 / (600 * n)) / 4 with hud
  have hεeq : deviceDrift 1 1 (1 + Δ) (1 / (600 * n)) p₀ = Δ * u := by
    rw [hud, deviceDrift, abs_of_nonneg hp0]
    ring
  have hu0 : 0 ≤ u := by
    rw [hud]
    positivity
  have hun : u * n ≤ 1 / 800 := by
    have hb : 2 * p₀ + 1 / (600 * n) ≤ 3 := by linarith
    have hDn : 1 / (600 * (n : ℝ)) * n = 1 / 600 := by field_simp
    calc u * n = 1 / (600 * n) * n * (2 * p₀ + 1 / (600 * n)) / 4 := by
          rw [hud]; ring
      _ = 1 / 600 * (2 * p₀ + 1 / (600 * n)) / 4 := by rw [hDn]
      _ ≤ 1 / 600 * 3 / 4 := by linarith
      _ = 1 / 800 := by norm_num
  have hule : u ≤ 1 / 800 := by nlinarith
  -- κ
  have hinv : Real.pi / (2 * R) * Δ ≤ Real.pi := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hprod : Real.pi / (2 * R) * (Δ * u) ≤ 1 / 100 := by
    calc Real.pi / (2 * R) * (Δ * u) = Real.pi / (2 * R) * Δ * u := by ring
      _ ≤ Real.pi * (1 / 800) := mul_le_mul hinv hule hu0 hπ.le
      _ ≤ 1 / 100 := by linarith
  have hΔe : ((1 + Δ - 1) / 1 : ℝ) = Δ := by ring
  have hΔsq : Δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hκ : 0 < (1 - ((1 + Δ - 1) / 1) ^ 2) / 2 - Real.pi / (2 * R) * (Δ * u) := by
    rw [hΔe]
    linarith
  -- the horizon
  set T := 2 * Real.pi * n / R with hTd
  have hT0 : 0 ≤ T := by positivity
  have hRT : R * T = 2 * Real.pi * n := by
    rw [hTd]
    field_simp
  have hsmall : R * (Δ * u) * (2 * T / (Δ / 2) + 3 / (Δ / 2) ^ 2 + Real.pi / (2 * R ^ 2))
      < ((1 - ((1 + Δ - 1) / 1) ^ 2) / 2 - Real.pi / (2 * R) * (Δ * u)) / 3 := by
    have e : R * (Δ * u) * (2 * T / (Δ / 2) + 3 / (Δ / 2) ^ 2 + Real.pi / (2 * R ^ 2))
        = 8 * Real.pi * (u * n) + 12 * (R / Δ) * u + Real.pi / (2 * R) * (Δ * u) := by
      rw [hTd]
      field_simp
      ring
    have hrΔ : R / Δ ≤ 1 := (div_le_one hΔ0).2 hRhi
    have hrΔ0 : 0 ≤ R / Δ := by positivity
    have t1 : 8 * Real.pi * (u * n) ≤ 8 * 3.15 * (1 / 800) :=
      mul_le_mul (by linarith) hun (mul_nonneg hu0 hn'.le) (by norm_num)
    have t2 : 12 * (R / Δ) * u ≤ 12 * 1 * (1 / 800) :=
      mul_le_mul (by linarith) hule hu0 (by norm_num)
    rw [e, hΔe]
    norm_num at t1 t2
    linarith
  have hticks : ((n : ℝ) - 1) * (2 * Real.pi) + Real.pi ≤ R * T := by
    rw [hRT]
    linarith
  refine ⟨?_, ?_⟩
  · refine div_pi_le_vRel_ringSigma hK hp0 (by linarith) ?_
    nlinarith [mul_nonneg hK'.le hp0]
  · obtain ⟨hΨ, N, hnN, hN, hbound⟩ := clock_packet_count_ge (M := M) (c := 1) (μ₀ := 1)
      (μ₁ := 1 + Δ) (ℓ := ringLen K) (D := 1 / (600 * n)) (p₀ := p₀) one_pos one_pos
      (by linarith) (ringLen_pos hK) hWin hWD' β hβ (J := ringHop K M)
      (σ := ringSigma K M p₀) (R := R) (ε := Δ * u) rfl rfl rfl hεeq.symm (ρ := Δ / 2)
      (by positivity) hRlo hρm rfl hκ hT0 hsmall hticks
    rw [add_sub_cancel_left] at hbound
    have hrate := abs_div_horizon_sub_le hn' hΔ0 hR0 hRhi (le_dispE 1 (ringSigma K M p₀))
      hbound
    exact ⟨_, hΨ, N, hnN, hN, hbound, hrate⟩

/-! ### A window that meets the hypotheses -/

/-- **A window of `2 w + 1` modes** centred on the mode `c`. -/
def modeWindow (c : ℤ) (w : ℕ) : Finset ℤ := Finset.Icc (c - w) (c + w)

/-- **Equal amplitudes on a window of `2 w + 1` modes.** -/
def flatAmp (w : ℕ) : ℤ → ℂ := fun _ => (((Real.sqrt (2 * w + 1))⁻¹ : ℝ) : ℂ)

theorem sum_norm_flatAmp (c : ℤ) (w : ℕ) : ∑ m ∈ modeWindow c w, ‖flatAmp w m‖ ^ 2 = 1 := by
  have h2 : (0 : ℝ) < 2 * w + 1 := by positivity
  have hs : (0 : ℝ) < Real.sqrt (2 * w + 1) := Real.sqrt_pos.2 h2
  have hcard : ((modeWindow c w).card : ℝ) = 2 * w + 1 := by
    rw [modeWindow, Int.card_Icc]
    have : (c + w + 1 - (c - w)).toNat = 2 * w + 1 := by omega
    rw [this]
    push_cast
    ring
  simp only [flatAmp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs), inv_pow,
    Real.sq_sqrt h2.le, Finset.sum_const, nsmul_eq_mul]
  rw [hcard]
  field_simp

/-- ★★ **A clock packet of `2 w + 1` modes that ticks at least `n` times.** For every
`n ≥ 1` and every `w`: on the ring of length `2π · 1200 n (w + 1)`, the `2 w + 1` modes
centred on the mode `600 n (w + 1)` (reference momentum `1/2`, each within `1/(600 n)` of
it), with equal amplitudes, any ring of more than `3600 n (w + 1) + w + 1` sites and any gap
`0 < Δ ≤ 1/2`, satisfy `narrow_clock_packet_ticks`: the count at `T = 2π n/R` is at least
`n` and obeys the dilated clock bound, with `v ≥ 1/(2π)`. No hypothesis is left but the
sizes. -/
theorem exists_clock_packet_ticks {n : ℕ} (hn : 0 < n) (w : ℕ) {M : ℕ}
    (hM : 3600 * n * (w + 1) + w + 1 ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2) :
    1 / 2 / Real.pi ≤ vRel 1 1 (ringSigma (1200 * n * (w + 1)) M (1 / 2))
    ∧ ∃ (g : ℝ) (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * (w + 1)) M) 1 (1 + Δ)
          (modeWindow (600 * n * (w + 1)) w) (flatAmp w)
          (-(Real.pi / (2 * ringRate (1200 * n * (w + 1)) M (1 / 2) Δ))) ≠ 0) (N : ℕ),
      n ≤ N
      ∧ IsTickCount (tickReady M) (tickDisplay M)
          (fun t => clockPointerFlow M (ringHop (1200 * n * (w + 1)) M) 1 (1 + Δ) g
            trainF_periodic contDiff_trainF t
            (clockArenaEquiv M (deviceRay _ hΨ),
              ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))))
          (2 * Real.pi * n / ringRate (1200 * n * (w + 1)) M (1 / 2) Δ) N
      ∧ |clockOpTime 1 (1 + Δ) N
            - Real.sqrt (1 - (vRel 1 1 (ringSigma (1200 * n * (w + 1)) M (1 / 2)) / 1) ^ 2)
              * (2 * Real.pi * n / ringRate (1200 * n * (w + 1)) M (1 / 2) Δ)|
          ≤ 2 * Real.pi / Δ
            + Δ / dispE 1 (ringSigma (1200 * n * (w + 1)) M (1 / 2))
              * (2 * Real.pi * n / ringRate (1200 * n * (w + 1)) M (1 / 2) Δ)
      ∧ |clockOpTime 1 (1 + Δ) N / (2 * Real.pi * n / ringRate (1200 * n * (w + 1)) M (1 / 2) Δ)
            - Real.sqrt (1 - (vRel 1 1 (ringSigma (1200 * n * (w + 1)) M (1 / 2)) / 1) ^ 2)|
          ≤ 1 / n + Δ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : 0 < 1200 * n * (w + 1) := by positivity
  have hKr : ((1200 * n * (w + 1) : ℕ) : ℝ) = 1200 * n * (w + 1) := by push_cast; ring
  have hMr : (3600 : ℝ) * n * (w + 1) + w + 1 ≤ M := by exact_mod_cast hM
  refine narrow_clock_packet_ticks (lo := 0) hn hK (by norm_num) (by norm_num) ?_ ?_ ?_
    (flatAmp w) (sum_norm_flatAmp _ w) hΔ0 hΔ
  · rw [hKr]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) w]
  · intro m hm
    rw [modeWindow, Finset.mem_Icc] at hm
    have hpos : (0 : ℤ) < 600 * n * (w + 1) := by positivity
    constructor
    · nlinarith [hm.1, mul_pos (show (0 : ℤ) < 600 * n by positivity)
        (show (0 : ℤ) < (w : ℤ) + 1 by positivity)]
    · have hMz : (3600 : ℤ) * n * (w + 1) + w + 1 ≤ M := by exact_mod_cast hM
      push_cast
      nlinarith [hm.2]
  · intro m hm
    left
    rw [modeWindow, Finset.mem_Icc] at hm
    have h1 : ((600 * n * (w + 1) : ℤ) : ℝ) - w ≤ m := by exact_mod_cast hm.1
    have h2 : (m : ℝ) ≤ ((600 * n * (w + 1) : ℤ) : ℝ) + w := by exact_mod_cast hm.2
    push_cast at h1 h2
    have hw : (0 : ℝ) ≤ w := Nat.cast_nonneg w
    have hden : (0 : ℝ) < 1200 * n * (w + 1) := by positivity
    have e : (m : ℝ) / ((1200 * n * (w + 1) : ℕ) : ℝ) - 1 / 2
        = ((m : ℝ) - 600 * n * (w + 1)) / (1200 * n * (w + 1)) := by
      rw [hKr]
      field_simp
      ring
    rw [e, abs_le]
    constructor
    · rw [le_div_iff₀ hden]
      have : -(1 / (600 * (n : ℝ))) * (1200 * n * (w + 1)) = -(2 * (w + 1)) := by
        field_simp
        ring
      rw [this]
      linarith
    · rw [div_le_iff₀ hden]
      have : 1 / (600 * (n : ℝ)) * (1200 * n * (w + 1)) = 2 * (w + 1) := by
        field_simp
        ring
      rw [this]
      linarith

end CSD.RecordLayer

end
