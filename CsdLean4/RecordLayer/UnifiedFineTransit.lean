/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedTransitCertificate

/-!
# A family of packets: far-half occupancy at most `1/(2n)` before, at least `1 − 1/(2n)` after

**Category:** 7-SigmaLayer (the record layer). BACKLOG #375 — the author's programme "From `Σ` to
physical spacetime", obligation UO-16; Remainder (b) of #373.

The crossing packet of #265 has `16` modes. Its weight on the far half of the ring is at most
`1/4` before the transit and at least `3/4` after.
#268 (`RecordLayer/DiracTiming.lean`) sharpened that for one packet of `10⁴` modes and a narrow
arc, with bounds `1/60` and `9/10`, for the free packet and a test detector. This module has a
family of packets indexed by `n ≥ 1` with bounds that tend to `0` and `1`, and states them, at
each flow time of two stated intervals, for the carrier coupled to the two region pointers.

## The family

`finePacket n` has `8n` neighbouring momenta from `p₀ = 4` upward (spread `1/(125 n)`) with
flat amplitudes, on a ring of
physical length `2000π n²` with at least `640000 n³` sites; `c = 1`, rest energy `3`, velocity
`4/5`. Its predicted angular position on the ring at flow time `t` is `t/(1250 n²)`.

* `finePacket`, `fineHop`, `omega_fine`, `fine_spread`, `fine_modes_lt`, `fine_sites`,
  `fine_win`, `fine_norm`; ★ `fine_budget` — **the error budget is at most `1/(6n)`** up to
  the flow time `1875π n²`;
* ★★ `regionWeight_fine_far` — **while the predicted position is at an angle at least `δ`
  short of the far half, the far half's weight times `1 − cos δ` is at most `1/(6n)`**;
* ★★ `regionWeight_fine_near` — **while it is at least `δ` inside the far half, the weight
  outside the far half times `1 − cos δ` is at most `1/(6n)`**;
* `regionWeight_fine_far_third`, `regionWeight_fine_near_third` — at `δ = π/3`: at most
  `1/(3n)` for `t ≤ (625π/3) n²`, at least `1 − 1/(3n)` for
  `(3125π/3) n² ≤ t ≤ (4375π/3) n²`;
* ★★ `exists_fine_transit` — **for every `ε > 0` and every margin `0 < δ ≤ π/2` there is an
  `n` with far-half weight at most `ε` before the angle `π/2 − δ` and at least `1 − ε` between
  the angles `π/2 + δ` and `3π/2 − δ`**, on every ring of at least `640000 n³` sites.

## The coupled carrier, at each flow time

* `abs_arenaObs_regionProj_two_sub_free_le` — at each flow time `s` the two detectors move
  the expectation of a region projector by at most `2|s|(|g₁ f(θ₂)| + |g₂ h(ψ₂)|)`;
* `fine_chainInner`, `chainProp_finePacket`, `finePacket_ne_zero`,
  `arenaObs_farHalf_free_finePacket`; `fineCarrier` (the carrier of `regionTwoFlow` started
  on `finePacket n`), `regionTwoFlow_fineCarrier`;
* `fineFibres` (`17500 π n³ (|g₁ f(θ₂)| + |g₂ h(ψ₂)|) < 1`), `isOpen_fineFibres`,
  `zero_mem_fineFibres_trainF`, `volume_fineFibres_trainF_pos`;
* ★ `abs_arenaObs_fineCarrier_sub_le` — the coupled carrier's far-half occupancy is within
  `2|t|(|g₁ f| + |g₂ h|)` of the free packet's weight, at each flow time;
  `fine_backReaction_le`;
* ★★ `fineCarrier_far_before`, `fineCarrier_far_after` — **on a fine fibre the coupled
  carrier's far-half occupancy is at most `1/(2n)` at every flow time in `[0, (625π/3) n²]` and
  at least `1 − 1/(2n)` at every flow time in `[(3125π/3) n², (4375π/3) n²]`**.

## Exact scope

* **A larger system for a sharper bound.** The ring's length grows as `n²`, the number of sites
  as `n³`, the number of modes as `n` and the flow times as `n²`. The bound `1/(2n)` is bought
  with all four. The hop `fineHop n L` changes with `n` as well, so this is a family of
  generators and not one system with different starts. For `n ≤ 2` the coupled bounds are no
  sharper than #265's `1/4` and `3/4`.
* **Two intervals.** The coupled bounds hold on `[0, (625π/3) n²]` and on
  `[(3125π/3) n², (4375π/3) n²]`. Nothing is stated between them or after the second: the
  packet goes on round the ring and leaves the far half.
* **The allowed back-reaction shrinks as `n⁻³`.** The fine fibres are open and of positive
  measure for the profile `trainF` and any strengths, and they shrink with `n`. Nothing is
  proved off them.
* **For the coupled carrier the window is not narrowed; for the free packet it is narrowed in
  angle only.** In angle the change is placed between `π/2 − δ` and `π/2 + δ` for any margin
  `δ`, at the price `1/(6n(1 − cos δ))`. In flow time the window
  `[(625π/3) n², (3125π/3) n²]` at `δ = π/3` is the old one scaled by `n²`.
  `exists_fine_transit` narrows `δ` for the free packet only, and there the unlocated window
  in flow time is `2500 n² δ`; with the `n` its proof supplies, that grows as `δ → 0`. No
  theorem here shows a window in flow time shrinking.
* **Occupancies, not records.** The statements are about the carrier's expectation of the far
  half's projector. No pointer inequality and no `IsRecordWrite` is stated here; the write times
  of #367 are not relocated.
* **Flow times.** Every time is a value of the flow parameter (UA-7).
* **The detector law is the drift coupling of UA-5**, the two region pointers are those of
  UA-13 and the carrier's generator is UA-8. The profiles and strengths are apparatus input
  (UA-4); the measure of the fine fibres is Haar on the pair of conserved angles (UA-2, through
  UA-13 (b)). No new assumption.
* **The back-reaction estimate is not new.** `abs_arenaObs_regionProj_two_sub_free_le` composes
  `abs_arenaObs_arenaKick_sub_le` with `norm_idxTwoCarrierU_sub_idxFreeU_le` (#367), as #357 did
  for one pointer.
* **Not a light-cone statement.** Little weight, not none: no bound vanishes outside a cone.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-2,
UA-4, UA-5, UA-7, UA-8, UA-13, UO-16, UD-108, UD-109); `RecordLayer/DiracArrival.lean`
(`regionWeight_ringPacket_le`, `farHalf`, `angle_farHalf`, `chainProp_packet`);
`CV/DiracPacketLimit.lean` (`dirac_packet_limit`, `ringPacket`, `limitErr`,
`flat_packet_localised`, `flat_sums`); `RecordLayer/UnifiedDepartureArrival.lean`
(`regionTwoFlow`, `regionTwoFlow_apply`, `norm_idxTwoCarrierU_sub_idxFreeU_le`);
`RecordLayer/UnifiedArrivalRecord.lean` (`arenaObs_regionProj_free_chainRay`);
`RecordLayer/DiracPointerWrite.lean` (`abs_arenaObs_arenaKick_sub_le`);
`RecordLayer/UnifiedTransitCertificate.lean` (#373); `RecordLayer/DiracTiming.lean`
(#268: `cos_le_cos_of_abs`, the one-instance sharp packet); R. Resta, PRL 80 (1998) 1800 (the
position on a ring as a phase).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### The family of packets -/

section Packet

variable {L : ℕ} [NeZero L]

/-- **The fine packet of index `n`**: the `8n` momenta `m/(1000 n²)`,
`4000 n² ≤ m < 4000 n² + 8n`, of a ring of physical length `2000π n²`, with `c = 1`, rest
energy `3` and flat amplitudes: momentum about `p₀ = 4`, velocity `4/5`. -/
noncomputable def finePacket (n : ℕ) (t : ℝ) : ZMod L × Fin 2 → ℂ :=
  ringPacket (L := L) 1 3 (2000 * Real.pi * (n : ℝ) ^ 2)
    (Finset.Ico (4000 * (n : ℤ) ^ 2) (4000 * (n : ℤ) ^ 2 + ((8 * n : ℕ) : ℤ)))
    (fun _ => ((1 / Real.sqrt ((8 * n : ℕ) : ℝ) : ℝ) : ℂ)) t

/-- Its hop on `L` sites: `J = c/(2a)`, `a = 2000π n²/L`. -/
noncomputable def fineHop (n L : ℕ) : ℝ := scaledHop 1 (2000 * Real.pi * (n : ℝ) ^ 2 / L)

variable {n : ℕ} (hn : 0 < n)
include hn

omit [NeZero L] in
/-- The packet's predicted angular velocity on the ring: `1/(1250 n²)`. -/
theorem omega_fine :
    2 * Real.pi / (2000 * Real.pi * (n : ℝ) ^ 2) * vRel 1 3 (1 * 4) = 1 / (1250 * (n : ℝ) ^ 2) := by
  have hr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [vRel_cross]
  field_simp
  norm_num

omit [NeZero L] in
theorem fine_spread :
    ∀ m ∈ Finset.Ico (4000 * (n : ℤ) ^ 2 : ℤ) (4000 * (n : ℤ) ^ 2 + ((8 * n : ℕ) : ℤ)),
      |2 * Real.pi * (m : ℝ) / (2000 * Real.pi * (n : ℝ) ^ 2) - 4| ≤ 1 / (125 * (n : ℝ)) := by
  intro m hm
  rw [Finset.mem_Ico] at hm
  have hr : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (4000 : ℝ) * (n : ℝ) ^ 2 ≤ m := by exact_mod_cast hm.1
  have h2 : (m : ℝ) ≤ 4000 * (n : ℝ) ^ 2 + 8 * n := by
    have := hm.2.le
    exact_mod_cast this
  have e : 2 * Real.pi * m / (2000 * Real.pi * (n : ℝ) ^ 2) - 4
      = (m - 4000 * (n : ℝ) ^ 2) / (1000 * (n : ℝ) ^ 2) := by
    field_simp
    ring
  rw [e, abs_of_nonneg (div_nonneg (by linarith) (by positivity)),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

variable (hL : 640000 * n ^ 3 ≤ L)
include hL

omit [NeZero L] in
theorem fine_modes_lt : 8 * n < L := by
  have h3 : n ≤ n ^ 3 := Nat.le_self_pow (by norm_num) n
  omega

omit [NeZero L] in
theorem fine_sites : 640000 ≤ L := by
  have h3 : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ hn
  omega

omit [NeZero L] in
theorem fine_win :
    ∀ m ∈ Finset.Ico (4000 * (n : ℤ) ^ 2 : ℤ) (4000 * (n : ℤ) ^ 2 + ((8 * n : ℕ) : ℤ)),
      4000 * (n : ℤ) ^ 2 ≤ m ∧ m + 1 < 4000 * (n : ℤ) ^ 2 + L := by
  intro m hm
  rw [Finset.mem_Ico] at hm
  have h8 := fine_modes_lt hn hL
  constructor <;> omega

theorem fine_norm :
    ∑ _m ∈ Finset.Ico (4000 * (n : ℤ) ^ 2) (4000 * (n : ℤ) ^ 2 + ((8 * n : ℕ) : ℤ)),
      ‖((1 / Real.sqrt ((8 * n : ℕ) : ℝ) : ℝ) : ℂ)‖ ^ 2 = 1 :=
  (flat_packet_localised (L := L) (c := 1) (μ := 3) (ℓ := 2000 * Real.pi * (n : ℝ) ^ 2)
    (by norm_num) (by positivity) (4000 * (n : ℤ) ^ 2) (N := 8 * n) (by omega)
    (fine_modes_lt hn hL)).1

/-- ★ **The fine packet's error budget is at most `1/(6n)`** up to the flow time `1875π n²`:
`1 − Re T(0) + t · limitErr ≤ 1/(6n)`. -/
theorem fine_budget {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1875 * Real.pi * (n : ℝ) ^ 2) :
    1 - (transPhase (finePacket (L := L) n 0)).re
      + |t| * limitErr 1 3 (2000 * Real.pi * (n : ℝ) ^ 2) (1 / (125 * (n : ℝ))) 4
          (2000 * Real.pi * (n : ℝ) ^ 2 / L) ≤ 1 / (6 * (n : ℝ)) := by
  have hπ := Real.pi_pos
  have hπ2 : Real.pi < 63 / 20 := by
    have := Real.pi_lt_d2
    norm_num at this ⊢
    linarith
  have hr1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (0 : ℝ) < n := by linarith
  have hLr : 640000 * (n : ℝ) ^ 3 ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le (by positivity) hLr
  -- everything is measured in `u = 1/n`
  set u : ℝ := 1 / (n : ℝ) with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := by
    rw [hu, div_le_one hr]
    exact hr1
  have hu2 : u ^ 2 ≤ u := by nlinarith
  have hu4 : u ^ 4 ≤ u := by nlinarith [sq_nonneg u, sq_nonneg (u ^ 2)]
  -- the initial localisation
  obtain ⟨hW, -⟩ := noWrap_distinct_of_window (L := L) (fine_win hn hL)
  have hRe := re_transPhase_ringPacket_ge (L := L) (c := 1) (μ := 3)
    (ℓ := 2000 * Real.pi * (n : ℝ) ^ 2) (by norm_num) (by positivity) hW
    (fun _ => 1 / Real.sqrt ((8 * n : ℕ) : ℝ)) (fun _ => by positivity)
  rw [(flat_sums (4000 * (n : ℤ) ^ 2) (N := 8 * n) (by omega)).2] at hRe
  have h6 : Real.pi * 1 / (2000 * Real.pi * (n : ℝ) ^ 2 * 3) = u ^ 2 / 6000 := by
    rw [hu]
    field_simp
    ring
  have h8 : (1 : ℝ) / ((8 * n : ℕ) : ℝ) = u / 8 := by
    rw [hu]
    push_cast
    field_simp
  rw [h6, h8] at hRe
  have hRe' : 1 - u / 8 - u / 36000000 ≤ (transPhase (finePacket (L := L) n 0)).re := by
    refine le_trans ?_ hRe
    have e : (u ^ 2 / 6000) ^ 2 = u ^ 4 / 36000000 := by ring
    rw [e]
    nlinarith [mul_nonneg (pow_nonneg hu0.le 4) hu0.le]
  -- the lattice spacing
  set a := 2000 * Real.pi * (n : ℝ) ^ 2 / L with ha
  have ha0 : 0 ≤ a := by positivity
  have hale : a ≤ 63 / 6400 * u := by
    rw [ha, hu, div_le_iff₀ hLpos]
    have e : 63 / 6400 * (1 / (n : ℝ)) * L = 63 / 6400 * L / n := by ring
    rw [e, le_div_iff₀ hr]
    have h3 : Real.pi * (n : ℝ) ^ 3 ≤ 63 / 20 * (n : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right hπ2.le (by positivity)
    nlinarith
  have ha2 : a ^ 2 ≤ (63 / 6400) ^ 2 * u := by
    have h := pow_le_pow_left₀ ha0 hale 2
    have e : (63 / 6400 * u) ^ 2 = (63 / 6400) ^ 2 * u ^ 2 := by ring
    rw [e] at h
    nlinarith
  -- the error rate
  have herr : limitErr 1 3 (2000 * Real.pi * (n : ℝ) ^ 2) (1 / (125 * (n : ℝ))) 4 a
      = u ^ 2 / 1000 * (1 / 3 * (u / 125 + u ^ 2 / 1000) + 104 / 9 * a ^ 2) := by
    unfold limitErr
    rw [hu]
    field_simp
    ring
  set E := 1 / 3 * (u / 125 + u ^ 2 / 1000) + 104 / 9 * a ^ 2 with hE
  have hE0 : 0 ≤ E := by positivity
  have hEle : E ≤ 1 / 3 * (u / 125 + u / 1000) + 104 / 9 * ((63 / 6400) ^ 2 * u) := by
    rw [hE]
    nlinarith
  have htu : t * (u ^ 2 / 1000) ≤ 189 / 32 := by
    have e : (n : ℝ) ^ 2 * u ^ 2 = 1 := by
      rw [hu]
      field_simp
    have h1 := mul_le_mul_of_nonneg_right ht (by positivity : (0 : ℝ) ≤ u ^ 2 / 1000)
    have e2 : 1875 * Real.pi * (n : ℝ) ^ 2 * (u ^ 2 / 1000)
        = 15 / 8 * Real.pi * ((n : ℝ) ^ 2 * u ^ 2) := by ring
    rw [e2, e] at h1
    linarith
  have hterm : |t| * limitErr 1 3 (2000 * Real.pi * (n : ℝ) ^ 2) (1 / (125 * (n : ℝ))) 4 a
      ≤ 189 / 32 * (1 / 3 * (u / 125 + u / 1000) + 104 / 9 * ((63 / 6400) ^ 2 * u)) := by
    rw [herr, abs_of_nonneg ht0, ← mul_assoc]
    calc t * (u ^ 2 / 1000) * E ≤ 189 / 32 * E := mul_le_mul_of_nonneg_right htu hE0
      _ ≤ _ := mul_le_mul_of_nonneg_left hEle (by norm_num)
  have e6 : 1 / (6 * (n : ℝ)) = u / 6 := by
    rw [hu]
    field_simp
  rw [e6]
  linarith

/-- ★★ **Before the predicted position is within the angle `δ` of the far half, the far half's
weight times `1 − cos δ` is at most `1/(6n)`**: for `0 ≤ t ≤ 1250 n² (π/2 − δ)`. -/
theorem regionWeight_fine_far {δ t : ℝ} (hδ0 : 0 ≤ δ) (ht0 : 0 ≤ t)
    (ht : t ≤ 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - δ)) :
    regionWeight (finePacket (L := L) n t) (farHalf L) * (1 - Real.cos δ)
      ≤ 1 / (6 * (n : ℝ)) := by
  have hπ := Real.pi_pos
  have hr : (0 : ℝ) < n := by exact_mod_cast hn
  have hθ0 : 0 ≤ 1 / (1250 * (n : ℝ) ^ 2) * t := by positivity
  have hθ : 1 / (1250 * (n : ℝ) ^ 2) * t ≤ Real.pi / 2 - δ := by
    rw [one_div, inv_mul_le_iff₀ (by positivity)]
    exact ht
  have h := regionWeight_ringPacket_le (L := L) (c := 1) (μ := 3)
    (ℓ := 2000 * Real.pi * (n : ℝ) ^ 2) (P := 4) (D := 1 / (125 * (n : ℝ))) (p₀ := 4)
    (by norm_num) (by norm_num) (by positivity) (by norm_num) (by positivity)
    (fine_win hn hL) (fine_spread hn) _ (fine_norm hn hL) (B := farHalf L)
    (γ := Real.cos δ) t
    (fun k hk => by
      rw [omega_fine hn]
      obtain ⟨h1, h2⟩ := (angle_farHalf (fine_sites hn hL) k).1 hk
      apply cos_le_cos_of_abs hδ0 <;> rw [abs_of_nonneg (by linarith)] <;> linarith)
  have hδr := mul_nonneg (sq_nonneg (n : ℝ)) hδ0
  have hπr := mul_pos hπ (pow_pos hr 2)
  have hb := fine_budget hn hL ht0 (by nlinarith)
  unfold finePacket at hb h ⊢
  linarith

/-- ★★ **Once the predicted position is at least the angle `δ` inside the far half, the weight
outside the far half times `1 − cos δ` is at most `1/(6n)`**: for
`1250 n² (π/2 + δ) ≤ t ≤ 1250 n² (3π/2 − δ)`. -/
theorem regionWeight_fine_near {δ t : ℝ} (hδ0 : 0 ≤ δ)
    (ht0 : 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + δ) ≤ t)
    (ht : t ≤ 1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 - δ)) :
    (1 - regionWeight (finePacket (L := L) n t) (farHalf L)) * (1 - Real.cos δ)
      ≤ 1 / (6 * (n : ℝ)) := by
  have hπ := Real.pi_pos
  have hr : (0 : ℝ) < n := by exact_mod_cast hn
  have hr2 : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos hr 2
  have hθ0 : Real.pi / 2 + δ ≤ 1 / (1250 * (n : ℝ) ^ 2) * t := by
    rw [one_div, le_inv_mul_iff₀ (by positivity)]
    exact ht0
  have hθ : 1 / (1250 * (n : ℝ) ^ 2) * t ≤ 3 * Real.pi / 2 - δ := by
    rw [one_div, inv_mul_le_iff₀ (by positivity)]
    exact ht
  have h := regionWeight_ringPacket_le (L := L) (c := 1) (μ := 3)
    (ℓ := 2000 * Real.pi * (n : ℝ) ^ 2) (P := 4) (D := 1 / (125 * (n : ℝ))) (p₀ := 4)
    (by norm_num) (by norm_num) (by positivity) (by norm_num) (by positivity)
    (fine_win hn hL) (fine_spread hn) _ (fine_norm hn hL) (B := (farHalf L)ᶜ)
    (γ := Real.cos δ) t
    (fun k hk => by
      rw [omega_fine hn]
      rcases (angle_farHalf (fine_sites hn hL) k).2 (Finset.mem_compl.1 hk) with
        ⟨h1, h2⟩ | ⟨h1, h2⟩
      · apply cos_le_cos_of_abs hδ0 <;> rw [abs_of_neg (by linarith)] <;> linarith
      · apply cos_le_cos_of_abs hδ0 <;> rw [abs_of_pos (by linarith)] <;> linarith)
  have ht0' : 0 ≤ t := le_trans (by positivity) ht0
  have hδr := mul_nonneg hr2.le hδ0
  have hπr := mul_pos hπ hr2
  have hb := fine_budget hn hL ht0' (by nlinarith)
  have hsum := regionWeight_add_compl (finePacket (L := L) n t) (farHalf L)
  have hnorm := (dirac_packet_limit (L := L) (c := 1) (μ := 3)
    (ℓ := 2000 * Real.pi * (n : ℝ) ^ 2) (P := 4) (D := 1 / (125 * (n : ℝ))) (p₀ := 4)
    (by norm_num) (by norm_num) (by positivity) (by norm_num) (by positivity)
    (fine_win hn hL) (fine_spread hn) _ (fine_norm hn hL)).1 t
  unfold finePacket at hb h hsum ⊢
  rw [hnorm, Complex.one_re] at hsum
  have e : 1 - regionWeight (ringPacket (L := L) 1 3 (2000 * Real.pi * (n : ℝ) ^ 2)
      (Finset.Ico (4000 * (n : ℤ) ^ 2) (4000 * (n : ℤ) ^ 2 + ((8 * n : ℕ) : ℤ)))
      (fun _ => ((1 / Real.sqrt ((8 * n : ℕ) : ℝ) : ℝ) : ℂ)) t) (farHalf L)
      = regionWeight (ringPacket (L := L) 1 3 (2000 * Real.pi * (n : ℝ) ^ 2)
      (Finset.Ico (4000 * (n : ℤ) ^ 2) (4000 * (n : ℤ) ^ 2 + ((8 * n : ℕ) : ℤ)))
      (fun _ => ((1 / Real.sqrt ((8 * n : ℕ) : ℝ) : ℝ) : ℂ)) t) (farHalf L)ᶜ := by linarith
  rw [e]
  linarith

/-- At the margin `π/3`: the far half holds at most `1/(3n)` of the weight for
`0 ≤ t ≤ (625π/3) n²`. -/
theorem regionWeight_fine_far_third {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ 625 * Real.pi / 3 * (n : ℝ) ^ 2) :
    regionWeight (finePacket (L := L) n t) (farHalf L) ≤ 1 / (3 * (n : ℝ)) := by
  have hr : (0 : ℝ) < n := by exact_mod_cast hn
  have h := regionWeight_fine_far (L := L) hn hL (δ := Real.pi / 3) (t := t) (by positivity) ht0
    (by linarith)
  rw [Real.cos_pi_div_three] at h
  have e : 1 / (3 * (n : ℝ)) = 2 * (1 / (6 * (n : ℝ))) := by
    field_simp
    norm_num
  rw [e]
  linarith

/-- At the margin `π/3`: the far half holds at least `1 − 1/(3n)` of the weight for
`(3125π/3) n² ≤ t ≤ (4375π/3) n²`. -/
theorem regionWeight_fine_near_third {t : ℝ} (ht0 : 3125 * Real.pi / 3 * (n : ℝ) ^ 2 ≤ t)
    (ht : t ≤ 4375 * Real.pi / 3 * (n : ℝ) ^ 2) :
    1 - 1 / (3 * (n : ℝ)) ≤ regionWeight (finePacket (L := L) n t) (farHalf L) := by
  have hr : (0 : ℝ) < n := by exact_mod_cast hn
  have h := regionWeight_fine_near (L := L) hn hL (δ := Real.pi / 3) (t := t) (by positivity)
    (by linarith) (by linarith)
  rw [Real.cos_pi_div_three] at h
  have e : 1 / (3 * (n : ℝ)) = 2 * (1 / (6 * (n : ℝ))) := by
    field_simp
    norm_num
  rw [e]
  linarith

end Packet

/-- ★★ **A transit located as finely as wanted in angle, for the free packet.** For every
`ε > 0` and every margin `0 < δ ≤ π/2` there is an index `n ≥ 1` such that, on every ring of at
least `640000 n³` sites, the far half holds at most `ε` of the fine packet's weight while the
predicted angle is at most `π/2 − δ`, and at least `1 − ε` while it is between `π/2 + δ` and
`3π/2 − δ`. The predicted angle at flow time `t` is `t/(1250 n²)`. -/
theorem exists_fine_transit {ε δ : ℝ} (hε : 0 < ε) (hδ0 : 0 < δ) (hδ : δ ≤ Real.pi / 2) :
    ∃ n : ℕ, 0 < n ∧ ∀ (L : ℕ) [NeZero L], 640000 * n ^ 3 ≤ L →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - δ) →
        regionWeight (finePacket (L := L) n t) (farHalf L) ≤ ε)
      ∧ (∀ t : ℝ, 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + δ) ≤ t →
        t ≤ 1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 - δ) →
        1 - ε ≤ regionWeight (finePacket (L := L) n t) (farHalf L)) := by
  have hcos : Real.cos δ < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (le_refl (0 : ℝ)) hδ hδ0
    rwa [Real.cos_zero] at h
  have hc : 0 < 1 - Real.cos δ := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (6 * ε * (1 - Real.cos δ)))
  have hpos : (0 : ℝ) < 1 / (6 * ε * (1 - Real.cos δ)) := by positivity
  have hr : (0 : ℝ) < n := hpos.trans hn
  have hn0 : 0 < n := by exact_mod_cast hr
  have hkey : 1 / (6 * (n : ℝ)) ≤ ε * (1 - Real.cos δ) := by
    rw [div_lt_iff₀ (by positivity)] at hn
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨n, hn0, fun L _ hL => ⟨fun t ht0 ht => ?_, fun t ht0 ht => ?_⟩⟩
  · have h := regionWeight_fine_far (L := L) hn0 hL hδ0.le ht0 ht
    exact le_of_mul_le_mul_right (h.trans hkey) hc
  · have h := regionWeight_fine_near (L := L) hn0 hL hδ0.le ht0 ht
    have h' := le_of_mul_le_mul_right (h.trans hkey) hc
    linarith

/-! ### The coupled carrier, at each flow time -/

section Pointwise

variable {M : ℕ} {f h : ℝ → ℝ} (J μ g₁ g₂ : ℝ) (A B : Finset (ZMod (M + 1)))
  (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)

/-- **At each flow time the two detectors move the expectation of a region projector by at
most `2|s|(|g₁ f(θ₂)| + |g₂ h(ψ₂)|)`.** -/
theorem abs_arenaObs_regionProj_two_sub_free_le (C : Finset (ZMod (M + 1)))
    (φ χ : AddCircle (1 : ℝ)) (p : GenArena (ZMod (M + 1) × Fin 2)) (s : ℝ) :
    |arenaObs (regionProj C)
          (arenaKick (idxTwoCarrierU (diracHam_isHermitian J μ)
            (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B) hf hh
            φ χ s) p)
        - arenaObs (regionProj C)
          (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1) J μ) s) p)|
      ≤ 2 * |s| * (|g₁ * hf.lift φ| + |g₂ * hh.lift χ|) := by
  have h0 := abs_arenaObs_arenaKick_sub_le
    (idxTwoCarrierU (diracHam_isHermitian J μ) (regionProj_smul_isHermitian g₁ A)
      (regionProj_smul_isHermitian g₂ B) hf hh φ χ s)
    (idxFreeU (diracHam_isHermitian (L := M + 1) J μ) s) (regionProj C) p
  have hn := norm_idxTwoCarrierU_sub_idxFreeU_le (diracHam_isHermitian J μ)
    (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B) hf hh φ χ s
  have h1 : ‖(g₁ : ℂ) • regionProj A‖ ≤ |g₁| := norm_ofReal_smul_le g₁ (norm_regionProj_le A)
  have h2 : ‖(g₂ : ℂ) • regionProj B‖ ≤ |g₂| := norm_ofReal_smul_le g₂ (norm_regionProj_le B)
  have hb : |hf.lift φ| * ‖(g₁ : ℂ) • regionProj A‖ + |hh.lift χ| * ‖(g₂ : ℂ) • regionProj B‖
      ≤ |g₁ * hf.lift φ| + |g₂ * hh.lift χ| := by
    rw [abs_mul, abs_mul, mul_comm |g₁|, mul_comm |g₂|]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
  have hn' := hn.trans (mul_le_mul_of_nonneg_left hb (abs_nonneg s))
  have hC := norm_regionProj_le C
  have hd := norm_nonneg ((idxTwoCarrierU (diracHam_isHermitian J μ)
      (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B) hf hh φ χ s).val
      - (idxFreeU (diracHam_isHermitian (L := M + 1) J μ) s).val)
  have h3 := mul_le_mul_of_nonneg_right hC hd
  linarith

end Pointwise

section Run

variable {M : ℕ} {f h : ℝ → ℝ} (g₁ g₂ : ℝ) (hf : Function.Periodic f 1)
  (hh : Function.Periodic h 1) {n : ℕ}

/-- **The fine fibres of index `n`**: the pairs of conserved angles `(θ₂, ψ₂)` at which the
back-reaction of the two detectors is small, `17500 π n³ (|g₁ f(θ₂)| + |g₂ h(ψ₂)|) < 1`. -/
def fineFibres (n : ℕ) : Set (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) :=
  {x | 17500 * Real.pi * (n : ℝ) ^ 3 * (|g₁ * hf.lift x.1| + |g₂ * hh.lift x.2|) < 1}

/-- The fine fibres are open. -/
theorem isOpen_fineFibres (n : ℕ) (hf1 : ContDiff ℝ 1 f) (hh1 : ContDiff ℝ 1 h) :
    IsOpen (fineFibres g₁ g₂ hf hh n) := by
  have hb : Continuous fun x : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
      17500 * Real.pi * (n : ℝ) ^ 3 * (|g₁ * hf.lift x.1| + |g₂ * hh.lift x.2|) :=
    continuous_const.mul ((continuous_const.mul
        ((continuous_periodicLift hf hf1.continuous).comp continuous_fst)).abs.add
      (continuous_const.mul
        ((continuous_periodicLift hh hh1.continuous).comp continuous_snd)).abs)
  exact isOpen_lt hb continuous_const

/-- For both profiles `trainF` and any strengths the pair `(0, 0)` is a fine fibre. -/
theorem zero_mem_fineFibres_trainF (n : ℕ) :
    ((0 : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ)))
      ∈ fineFibres g₁ g₂ trainF_periodic trainF_periodic n := by
  show 17500 * Real.pi * (n : ℝ) ^ 3 * (|g₁ * trainF_periodic.lift 0|
    + |g₂ * trainF_periodic.lift 0|) < 1
  rw [trainF_lift_zero]
  simp

/-- ★ **The fine fibres have positive measure** for both profiles `trainF` and any
strengths. -/
theorem volume_fineFibres_trainF_pos (n : ℕ) :
    0 < volume (fineFibres g₁ g₂ trainF_periodic trainF_periodic n) :=
  (isOpen_fineFibres g₁ g₂ trainF_periodic trainF_periodic n
    (contDiff_trainF.of_le (by simp)) (contDiff_trainF.of_le (by simp))).measure_pos volume
    ⟨(0, 0), zero_mem_fineFibres_trainF g₁ g₂ n⟩

variable (hn : 0 < n) (hL : 640000 * n ^ 3 ≤ M + 1)
include hn hL

/-- The fine packet is normalised at every flow time. -/
theorem fine_chainInner (t : ℝ) :
    chainInner (finePacket (L := M + 1) n t) (finePacket (L := M + 1) n t) = 1 :=
  (dirac_packet_limit (L := M + 1) (c := 1) (μ := 3)
    (ℓ := 2000 * Real.pi * (n : ℝ) ^ 2) (P := 4) (D := 1 / (125 * (n : ℝ))) (p₀ := 4)
    (by norm_num) (by norm_num) (by positivity) (by norm_num) (by positivity)
    (fine_win hn hL) (fine_spread hn) _ (fine_norm hn hL)).1 t

omit hn hL in
/-- The whole chain carries the fine packet. -/
theorem chainProp_finePacket (n : ℕ) (t : ℝ) :
    chainProp (L := M + 1) (fineHop n (M + 1)) 3 t *ᵥ finePacket (L := M + 1) n 0
      = finePacket n t := by
  unfold finePacket ringPacket fineHop
  exact chainProp_packet _ _ _ _ t

/-- The fine packet is not zero. -/
theorem finePacket_ne_zero : finePacket (L := M + 1) n 0 ≠ 0 := fun h0 => by
  have h1 := fine_chainInner hn hL 0
  rw [h0] at h1
  simp [chainInner] at h1

/-- ★ **Along the uncoupled carrier the expectation of the far half's projector is the fine
packet's weight on the far half.** -/
theorem arenaObs_farHalf_free_finePacket (s : ℝ) :
    arenaObs (regionProj (farHalf (M + 1)))
        (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1) (fineHop n (M + 1)) 3) s)
          (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)))
      = regionWeight (finePacket (L := M + 1) n s) (farHalf (M + 1)) := by
  rw [arenaObs_regionProj_free_chainRay, chainProp_finePacket, fine_chainInner hn hL 0,
    Complex.one_re, div_one]

/-- **The carrier of `regionTwoFlow` started on the fine packet**, on the fibre `(φ, χ)`, at
flow time `s`: the first pointer is coupled to the near half of the ring and the second to the
far half. -/
noncomputable def fineCarrier (φ χ : AddCircle (1 : ℝ)) (s : ℝ) :
    GenArena (ZMod (M + 1) × Fin 2) :=
  arenaKick (idxTwoCarrierU (diracHam_isHermitian (L := M + 1) (fineHop n (M + 1)) 3)
      (regionProj_smul_isHermitian g₁ (farHalf (M + 1))ᶜ)
      (regionProj_smul_isHermitian g₂ (farHalf (M + 1))) hf hh φ χ s)
    (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL))

/-- **The carrier component of the joint flow is `fineCarrier`**, on the fibre of the two
pointers' conserved angles. -/
theorem regionTwoFlow_fineCarrier (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (θ ψ : KTorus) (t : ℝ) :
    (regionTwoFlow (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) hf hh hc
        hch t ((idxArenaEquiv (diracIdx M)
          (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)), θ), ψ)).1.1
      = idxArenaEquiv (diracIdx M) (fineCarrier g₁ g₂ hf hh hn hL θ.2 ψ.2 t) := by
  rw [regionTwoFlow_apply]
  rfl

/-- ★ **The coupled carrier's far-half occupancy is within the back-reaction of the free
packet's weight, at each flow time.** -/
theorem abs_arenaObs_fineCarrier_sub_le (φ χ : AddCircle (1 : ℝ)) (t : ℝ) :
    |arenaObs (regionProj (farHalf (M + 1))) (fineCarrier g₁ g₂ hf hh hn hL φ χ t)
        - regionWeight (finePacket (L := M + 1) n t) (farHalf (M + 1))|
      ≤ 2 * |t| * (|g₁ * hf.lift φ| + |g₂ * hh.lift χ|) := by
  have h0 := abs_arenaObs_regionProj_two_sub_free_le (fineHop n (M + 1)) 3 g₁ g₂
    (farHalf (M + 1))ᶜ (farHalf (M + 1)) hf hh (farHalf (M + 1)) φ χ
    (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)) t
  rw [arenaObs_farHalf_free_finePacket hn hL] at h0
  exact h0

omit hL in
/-- On a fine fibre the back-reaction up to `(4375π/3) n²` is at most `1/(6n)`. -/
theorem fine_backReaction_le {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ fineFibres g₁ g₂ hf hh n) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ 4375 * Real.pi / 3 * (n : ℝ) ^ 2) :
    2 * |t| * (|g₁ * hf.lift φ| + |g₂ * hh.lift χ|) ≤ 1 / (6 * (n : ℝ)) := by
  have hb' : 17500 * Real.pi * (n : ℝ) ^ 3 * (|g₁ * hf.lift φ| + |g₂ * hh.lift χ|) < 1 := hx
  have hr : (0 : ℝ) < n := by exact_mod_cast hn
  set b := |g₁ * hf.lift φ| + |g₂ * hh.lift χ| with hbdef
  have hb0 : 0 ≤ b := by positivity
  rw [abs_of_nonneg ht0, le_div_iff₀ (by positivity)]
  have h1 := mul_le_mul_of_nonneg_right ht (mul_nonneg hb0 hr.le)
  nlinarith

/-- ★★ **Before the transit the coupled carrier's far-half occupancy is at most `1/(2n)`**, at
every flow time in `[0, (625π/3) n²]`, on a fine fibre. -/
theorem fineCarrier_far_before {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ fineFibres g₁ g₂ hf hh n) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ 625 * Real.pi / 3 * (n : ℝ) ^ 2) :
    arenaObs (regionProj (farHalf (M + 1))) (fineCarrier g₁ g₂ hf hh hn hL φ χ t)
      ≤ 1 / (2 * (n : ℝ)) := by
  have hπ := Real.pi_pos
  have hr : (0 : ℝ) < n := by exact_mod_cast hn
  have hr2 : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos hr 2
  have h1 := abs_le.1 (abs_arenaObs_fineCarrier_sub_le g₁ g₂ hf hh hn hL φ χ t)
  have h2 := fine_backReaction_le g₁ g₂ hf hh hn hx ht0
    (by nlinarith [mul_pos hπ hr2])
  have h3 := regionWeight_fine_far_third (L := M + 1) hn hL ht0 ht
  have e : 1 / (2 * (n : ℝ)) = 1 / (3 * (n : ℝ)) + 1 / (6 * (n : ℝ)) := by
    field_simp
    norm_num
  rw [e]
  linarith

/-- ★★ **After the transit the coupled carrier's far-half occupancy is at least
`1 − 1/(2n)`**, at every flow time in `[(3125π/3) n², (4375π/3) n²]`, on a fine fibre. -/
theorem fineCarrier_far_after {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ fineFibres g₁ g₂ hf hh n) {t : ℝ}
    (ht0 : 3125 * Real.pi / 3 * (n : ℝ) ^ 2 ≤ t) (ht : t ≤ 4375 * Real.pi / 3 * (n : ℝ) ^ 2) :
    1 - 1 / (2 * (n : ℝ))
      ≤ arenaObs (regionProj (farHalf (M + 1))) (fineCarrier g₁ g₂ hf hh hn hL φ χ t) := by
  have hπ := Real.pi_pos
  have hr : (0 : ℝ) < n := by exact_mod_cast hn
  have ht0' : 0 ≤ t := le_trans (by positivity) ht0
  have h1 := abs_le.1 (abs_arenaObs_fineCarrier_sub_le g₁ g₂ hf hh hn hL φ χ t)
  have h2 := fine_backReaction_le g₁ g₂ hf hh hn hx ht0' ht
  have h3 := regionWeight_fine_near_third (L := M + 1) hn hL ht0 ht
  have e : 1 / (2 * (n : ℝ)) = 1 / (3 * (n : ℝ)) + 1 / (6 * (n : ℝ)) := by
    field_simp
    norm_num
  rw [e]
  linarith

end Run

end CSD.RecordLayer

end
