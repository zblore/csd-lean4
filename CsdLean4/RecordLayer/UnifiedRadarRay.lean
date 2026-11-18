/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedRadarRun
public import CsdLean4.RecordLayer.UnifiedWallRay

/-!
# The family's run from turned rays

**Category:** 7-SigmaLayer. BACKLOG #438, fourth brick (Task 2 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream R; obligation
UO-25, item (2)).

`radar_family_lorentz` (`RecordLayer/UnifiedRadarRun.lean`) is the plan's M6 theorem from the
family's product ray and pointer angles within `1/(12000 k²)` of the start. Here the same
from that ray turned by any unitary of the composite within `1/(12000 k²)` of the identity.

* `ray_error_of_radius` — arithmetic: the radius condition of the pointer angles gives the
  one of the rays;
* ★★★ `radar_family_lorentz_ray` — for every `k ≥ 100` and every even ring with
  `M ≥ 210000 N³`: for some strengths, from the product ray turned by any `W` with
  `‖W − 1‖ ≤ 1/(12000 k²)` and every five pointer angles within `1/(24000 k²)` of
  `(1/12, 0)`, the five pointers of `wallRunRay` have counts in the five reading windows and
  the counts satisfy both components of the Lorentz statement within `152 K/k`, and the
  interval comparison within `53 K/k`.

## Honest scope

⚠️ **A product set of starts, not yet a set of positive measure in the arena.** The rays are
those of `turnedRays` (`RecordLayer/UnifiedTurnedRays.lean`), which have positive
Fubini–Study measure in the composite's projective space. Their image under the labelling of
the basis, the product with the box of angles under `μ_FS ⊗ vol⁵`, the five record events
containing it, and the `HistoryPreparation` are not here.

⚠️ **The strengths are those of this theorem**, as in `tri_wall_radar_lorentz_ray`: not stated
to be the ones of `radar_family_lorentz`.

⚠️ **Both radii shrink like `1/k²`**, as the radius of the angles already did. One family, one
velocity, one distance, `1 + 1`. The Lorentz statement is that of #402 about five tick
counts in flow-time windows.

References: `specs/BACKLOG.md` #438, ~~#426~~, ~~#435~~;
`specs/unified-record-spacetime-plan.md` (UO-25, UD-201, UD-205, UD-214, UD-215, UD-218);
`RecordLayer/UnifiedRadarRun.lean` (`radar_family_lorentz`, `radar_radius_A`,
`radar_radius_B`, `radar_error_le`); `RecordLayer/UnifiedWallRay.lean`
(`tri_wall_radar_lorentz_ray`, `wallRunRay`); `RecordLayer/UnifiedTurnedRays.lean`
(`fsMeasure_turnedRays_pos`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV
open scoped Matrix Matrix.Norms.L2Operator

namespace CSD.RecordLayer

/-- From the radius condition of the pointer angles to the one of the rays: if
`ρ C K ≤ ϵ` with `C = 20 γ² T + 14 γ`, then `4 γ ρ K ≤ ϵ`, whatever the sign of `K`. -/
theorem ray_error_of_radius {ρ γ T KK ϵ : ℝ} (hρ : 0 ≤ ρ) (hγ : 0 ≤ γ) (hT : 0 ≤ T)
    (hϵ : 0 ≤ ϵ) (h : ρ * ((20 * γ ^ 2 * 1 ^ 2 * T + 14 * γ * 1) * KK) ≤ ϵ) :
    4 * γ * 1 * ρ * KK ≤ ϵ := by
  have e : ρ * ((20 * γ ^ 2 * 1 ^ 2 * T + 14 * γ * 1) * KK)
      = 20 * (ρ * γ ^ 2 * T * KK) + 14 * (ρ * γ * KK) := by ring
  have e2 : 4 * γ * 1 * ρ * KK = 4 * (ρ * γ * KK) := by ring
  rcases le_total 0 KK with hK | hK
  · have h1 : 0 ≤ ρ * γ * KK := by positivity
    have h2 : 0 ≤ ρ * γ ^ 2 * T * KK := by positivity
    linarith only [e, e2, h, h1, h2]
  · have h1 : ρ * γ * KK ≤ 0 := by
      nlinarith only [mul_nonneg (mul_nonneg hρ hγ) (neg_nonneg.2 hK)]
    linarith only [e2, h1, hϵ]

section Run

open CSD.LF4 Projectivization

/-- ★★★ **The family's run from turned rays and nearby pointer angles.** For every `k ≥ 100`
and every ring with an even number `M + 1 = 2H` of sites, `M ≥ 210000 N³`, with the carriers,
gates and times of `radar_family_lorentz`: for some strengths `0 < g_A ≤ R₀/5` and
`0 < g_B ≤ R_B/5`, from the product ray of the three carriers turned by any unitary `W` of
their composite with `‖W − 1‖ ≤ 1/(12000 k²)`, and from every five pointer angles within
`1/(24000 k²)` of `(1/12, 0)`, the five pointers of `wallRunRay` have counts at every choice
of flow times in the five reading windows, and the counts satisfy both components of the
Lorentz statement of #402 for `v = vRel 1 1 (1/2)` within `152 K/k`. -/
theorem radar_family_lorentz_ray {k : ℕ} (hk : 100 ≤ k) {M H : ℕ}
    (hM : 210000 * wallN k ^ 2 * wallN k ≤ M) (hH : M + 1 = 2 * H) :
    ∃ (hψ : oddWall (L := M + 1) 1 (wallMu k) (ringLen (1200 * wallN k * wallN k))
          (Finset.Ico (600 * (wallN k : ℤ) * wallN k) (600 * (wallN k : ℤ) * wallN k + wallN k))
          (flatAmpN (wallN k)) (radarRateB k * radarTau k M / radarRateA k) ≠ 0)
      (gA gB : ℝ)
      (hΨA : devicePacket (L := M + 1) (ringHop (1200 * wallN k * wallN k) M) 1
        (1 + wallGap k) (wallWindow (wallN k) ∪ negWin (wallWindow (wallN k)))
        (oddExt (wallWindow (wallN k)) (flatAmpN (wallN k)))
        (-(Real.pi / (2 * ringRate (1200 * wallN k * wallN k) M 0 (wallGap k)))) ≠ 0)
      (hΨB : devicePacket (L := M + 1) (ringHop (1200 * wallN k * wallN k) M) 1
        (1 + wallGap k) (flatWindow (wallN k) (wallN k) ∪ negWin (flatWindow (wallN k) (wallN k)))
        (oddExt (flatWindow (wallN k) (wallN k)) (flatAmpN (wallN k)))
        (-(Real.pi / (2 * ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k)))) ≠ 0),
      0 < gA ∧ gA ≤ ringRate (1200 * wallN k * wallN k) M 0 (wallGap k) / 5
      ∧ 0 < gB ∧ gB ≤ ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k) / 5
      ∧ ∀ W : Matrix.unitaryGroup ((ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
          × ((ZMod (M + 1) × Fin 2) × Fin 2))) ℂ,
        ‖W.val - 1‖ ≤ 1 / (12000 * (k : ℝ) ^ 2) →
        ∀ θ ψ χ ξ ζ : KTorus, NearStart (1 / (24000 * (k : ℝ) ^ 2)) θ →
        NearStart (1 / (24000 * (k : ℝ) ^ 2)) ψ → NearStart (1 / (24000 * (k : ℝ) ^ 2)) χ →
        NearStart (1 / (24000 * (k : ℝ) ^ 2)) ξ → NearStart (1 / (24000 * (k : ℝ) ^ 2)) ζ →
        WallRadarLorentz M
          (fun e => wallRunRay (wallN k) (wallN k) M (wallMu k) (wallGap k) (3 * wallDelta k)
            gA gB e
            (arenaKick W (prodRay (chainRay _ hψ)
              (prodRay (deviceRay (deviceShift (H : ZMod (M + 1)) _)
                (deviceShift_ne_zero (H : ZMod (M + 1)) hΨA)) (deviceRay _ hΨB))))
            θ ψ χ ξ ζ)
          (ringRate (1200 * wallN k * wallN k) M 0 (wallGap k)) (vRel 1 1 (1 / 2))
          (famTb k) (famT3 k) (famT4 k) (famT5 k) (famTbM k M) (famTcM k M) (famTbR k M)
          (famTcR k M) (152 * (wallK k / k)) (152 * (wallK k / k))
          (Real.pi * wallK k - Real.pi * wallK k / vRel 1 1 (1 / 2))
          (53 * (wallK k / k)) := by
  have hk1 : 1 ≤ k := by omega
  have hX : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have hX0 : (0 : ℝ) < k := by linarith only [hX]
  have hπ := Real.pi_gt_three
  obtain ⟨hK0, hKX, hΔK, ha1, ha2, hb1, hb2, hb3, hb4, hR1, hR2⟩ := radar_family_rates hk M
  obtain ⟨c_b₂, c_21, c_2a, c_fast, c_τ, c_δ, c_δπ, c_start, c_η, c_lev⟩ :=
    radar_family_gate_conditions hk M
  obtain ⟨s5, sR, sM, sτ, st₀, sHB, sHA, sclB, sclA, sband⟩ := radar_family_all_conditions hk M
  unfold famT5 at s5
  unfold famTcR at sR
  unfold famTcM at sM
  unfold famTE famTb famT3 at sband
  unfold famTb famT3 famT4 famT5 famTbM famTcM famTbR famTcR
  obtain ⟨⟨o1, o2, o3, o4, o5⟩, ⟨p1, p2, p3⟩, ⟨q1, q2, q3⟩, i1, i2, i3, i4, i5, i6, i7, i8,
    i9, i10, i11, i12, i13⟩ := radar_gate_times c_b₂ c_21 c_2a c_fast c_τ c_δ c_δπ c_start
      c_η c_lev
  have hb₁0 : 0 < radarRateB k := c_b₂.trans_le c_21
  have ha0 : 0 < radarRateA k := by linarith only [c_2a, hb₁0]
  have ht₀ : radarRateA k * (radarRateB k * radarTau k M / radarRateA k)
      = radarRateB k * radarTau k M := mul_div_cancel₀ _ ha0.ne'
  have I := radar_gate_intervals (t₀ := radarRateB k * radarTau k M / radarRateA k)
    (w := 3 * wallDelta k) c_b₂ c_21 (by linarith only [c_2a, hb₁0]) c_τ ht₀ c_δ.le
    (by linarith only [c_δ]) (by linarith only [c_δπ, c_δ]) (o1.trans o2)
    ((o1.trans o2).trans (o3.trans o4)) q1 q2 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13
  obtain ⟨I1, I2, I3, I4, I5, I6, I7⟩ := I
  -- the carriers
  have hNpos : 0 < wallN k := by
    rw [wallN]
    positivity
  have hkN : k ≤ wallN k := by
    rw [wallN]
    calc k ≤ k ^ 4 := Nat.le_self_pow (by norm_num) k
      _ ≤ 10 ^ 16 * k ^ 4 := Nat.le_mul_of_pos_left _ (by positivity)
  obtain ⟨-, -, -, -, ⟨hμ0, hμ1⟩, ⟨hΔ0, hΔ12⟩⟩ := wall_values hk1 (t := 0) (t' := 0)
    (by rw [abs_zero]; linarith only [hK0]) (by rw [abs_zero]; linarith only [hK0])
  have hMz : (210000 : ℤ) * (wallN k : ℤ) ^ 2 * wallN k ≤ M := by exact_mod_cast hM
  have hn1 : (1 : ℤ) ≤ wallN k := by exact_mod_cast hNpos
  have hnN : (0 : ℤ) ≤ (wallN k : ℤ) * wallN k := by positivity
  have hsq : (wallN k : ℤ) * wallN k ≤ (wallN k : ℤ) ^ 2 * wallN k := by
    nlinarith only [hn1, hnN]
  have hNle : (wallN k : ℤ) ≤ (wallN k : ℤ) * wallN k := by nlinarith only [hn1]
  have hlo : (0 : ℤ) < 600 * (wallN k : ℤ) * wallN k := by nlinarith only [hn1]
  have hhi : 2 * (600 * (wallN k : ℤ) * wallN k + wallN k) ≤ M := by
    linarith only [hMz, hsq, hNle, hnN]
  have hp₀ : |(1 / 2 : ℝ)| ≤ 1 / 2 := by rw [abs_of_pos (by norm_num)]
  have hWD : ∀ m ∈ Finset.Ico (600 * (wallN k : ℤ) * wallN k)
      (600 * (wallN k : ℤ) * wallN k + wallN k),
      |2 * Real.pi * m / ringLen (1200 * wallN k * wallN k) - 1 / 2|
        ≤ 1 / (600 * (wallN k : ℕ)) := by
    intro m hm
    have hK' : (0 : ℝ) < ((1200 * wallN k * wallN k : ℕ) : ℝ) := by
      exact_mod_cast (by positivity : 0 < 1200 * wallN k * wallN k)
    have e : 2 * Real.pi * (m : ℝ) / ringLen (1200 * wallN k * wallN k)
        = (m : ℝ) / ((1200 * wallN k * wallN k : ℕ) : ℝ) := by
      rw [ringLen]
      field_simp
    rw [e]
    exact flatWindow_width hNpos hNpos m hm
  have hψ : oddWall (L := M + 1) 1 (wallMu k) (ringLen (1200 * wallN k * wallN k))
      (Finset.Ico (600 * (wallN k : ℤ) * wallN k) (600 * (wallN k : ℤ) * wallN k + wallN k))
      (flatAmpN (wallN k)) (radarRateB k * radarTau k M / radarRateA k) ≠ 0 := by
    have hnorm := chainInner_icoWall (M := M) hNpos hNpos hμ0 hlo hhi hp₀ hWD
      (radarRateB k * radarTau k M / radarRateA k)
    intro h0
    rw [h0] at hnorm
    simp [chainInner] at hnorm
  -- the far wall
  have hφ : (0 : ℝ) + 2 * Real.pi * (ZMod.val (H : ZMod (M + 1))) / ((M + 1 : ℕ) : ℝ)
      = Real.pi := by
    have hHpos : 0 < H := by omega
    have hlt : H < M + 1 := by omega
    have hH' : (0 : ℝ) < H := by exact_mod_cast hHpos
    rw [ZMod.val_natCast_of_lt hlt, hH]
    push_cast
    field_simp
    ring
  -- sizes
  have hRB0 : 0 < ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k) := by
    linarith only [hR1, hΔ0]
  have hRA : ringRate (1200 * wallN k * wallN k) M 0 (wallGap k) = wallGap k :=
    ringRate_zero _ _ hΔ0.le
  have hδ1 : wallDelta k ≤ 1 := by linarith only [c_δπ, c_δ, Real.pi_lt_four]
  have hcos : Real.cos (wallDelta k) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl
      (by linarith only [c_δπ, c_δ] : wallDelta k ≤ Real.pi) c_δ
    rw [Real.cos_zero] at h
    exact h
  have h24 : 1 / (24 * (k : ℝ)) ≤ 1 / 2400 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith only [hX]
  have hLB : ∀ (μ t : ℝ), 0 < μ → 0 ≤ lightBudget (wallN k) (wallN k) μ t := by
    intro μ t hμ
    unfold lightBudget
    positivity
  have hτA0 : 0 ≤ Real.pi / (2 * ringRate (1200 * wallN k * wallN k) M 0 (wallGap k)) := by
    rw [hRA]
    exact div_nonneg Real.pi_pos.le (by linarith only [hΔ0])
  have hτAK : Real.pi / (2 * ringRate (1200 * wallN k * wallN k) M 0 (wallGap k))
      ≤ wallK k := by
    rw [hRA, div_le_iff₀ (by linarith only [hΔ0])]
    nlinarith only [hΔK, hX, Real.pi_lt_four]
  have ht₀0 : 0 ≤ radarRateB k * radarTau k M / radarRateA k :=
    div_nonneg (mul_nonneg hb₁0.le c_τ) ha0.le
  have hbud : ∀ s, 0 ≤ s → s ≤ 8 * wallK k →
      4 * lightBudget (wallN k) (wallN k) (wallMu k)
          (radarRateB k * radarTau k M / radarRateA k + s)
        ≤ 1 / (500 * (k : ℝ)) * (1 - Real.cos (wallDelta k)) / 2
      ∧ 4 * lightBudget (wallN k) (wallN k) 1
          (-(Real.pi / (2 * ringRate (1200 * wallN k * wallN k) M 0 (wallGap k))) + s)
        ≤ 1 / (500 * (k : ℝ)) * (1 - Real.cos (wallDelta k)) / 2
      ∧ 4 * lightBudget (wallN k) (wallN k) 1
          (-(Real.pi / (2 * ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k))) + s)
        ≤ 1 / (500 * (k : ℝ)) * (1 - Real.cos (wallDelta k)) / 2 := by
    intro s hs0 hs
    have e : 1 / (500 * (k : ℝ)) * (1 - Real.cos (wallDelta k)) / 2
        = 1 / (1000 * (k : ℝ)) * (1 - Real.cos (wallDelta k)) := by
      field_simp
      ring
    rw [e]
    have b1 : |radarRateB k * radarTau k M / radarRateA k + s| ≤ 10 * wallK k := by
      rw [abs_of_nonneg (by linarith only [ht₀0, hs0])]
      linarith only [st₀, hs, hK0]
    have b2 : |-(Real.pi / (2 * ringRate (1200 * wallN k * wallN k) M 0 (wallGap k))) + s|
        ≤ 10 * wallK k := by
      rw [abs_le]
      constructor <;> linarith only [hτA0, hτAK, hs0, hs, hK0]
    have b3 : |-(Real.pi / (2 * ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k)))
        + s| ≤ 10 * wallK k := by
      have h1 : 0 ≤ radarTau k M := c_τ
      have h2 : radarTau k M ≤ wallK k := sτ
      unfold radarTau at h1 h2
      rw [abs_le]
      constructor <;> linarith only [h1, h2, hs0, hs, hK0]
    have b0 : |(0 : ℝ)| ≤ 10 * wallK k := by rw [abs_zero]; linarith only [hK0]
    have v1 := (wall_values hk1 b1 b0).1
    have v2 := (wall_values hk1 b0 b2).1
    have v3 := (wall_values hk1 b0 b3).1
    have n1 := hLB 1 0 one_pos
    have n2 := hLB (wallMu k) 0 hμ0
    exact ⟨by linarith only [v1, n1], by linarith only [v2, n2], by linarith only [v3, n2]⟩
  -- the theorem of #423
  have t30 : 0 ≤ 6 * wallDelta k / (radarRateA k - radarRateB k) := o1.trans o2
  have t40 : 0 ≤ (2 * Real.pi - wallDelta k) / (radarRateA k + radarRateB' k) :=
    t30.trans (o3.trans o4)
  have tM0 : 0 ≤ radarTau k M + (Real.pi - 6 * wallDelta k) / radarRateB k := c_τ.trans q1
  have R := tri_wall_radar_lorentz_ray (j := k) (n := wallN k) (N := wallN k) (M := M)
    (Δ := wallGap k) (μ := wallMu k) (p₀ := 1 / 2) (w := 3 * wallDelta k) (δ := wallDelta k)
    (ε := 1 / (500 * (k : ℝ))) (T := 8 * wallK k) (d := Real.pi * wallK k)
    (by omega) hkN hNpos hM hμ0 hμ1 hΔ0 hΔ12 hlo hhi hp₀ hWD
    (radarRateB k * radarTau k M / radarRateA k) (H : ZMod (M + 1)) hψ c_δ.le hcos
    (by linarith only [c_δ]) (by linarith only [c_δπ, c_δ]) (by positivity) hbud
    o1 o2 o3 o4 o5 s5 ((o4.trans o5).trans (s5.trans sHB)) I1 I2 I3
    ((sclB _ (by linarith only [o4, o5, s5, t30])).trans_lt (by norm_num))
    ((sclB _ (by linarith only [s5, t40])).trans_lt (by norm_num)) sband
    p1 p2 p3 sR ((p2.trans p3).trans (sR.trans sHA))
    (fun s h0 h1 => by rw [hφ]; exact I4 s h0 h1)
    (fun s h0 h1 => by rw [hφ]; exact I5 s h0 h1)
    (by
      have := sclA _ ((p2.trans p3).trans sR)
      linarith only [this, h24])
    ((sclA _ (by linarith only [sR, p1, p2])).trans_lt (by norm_num))
    tM0 q2 q3 sM ((q2.trans q3).trans (sM.trans sHB)) ((q2.trans q3).trans (sM.trans sHA))
    (fun s h0 h1 => by rw [hφ]; exact I6 s h0 h1)
    (fun s h0 h1 => by rw [hφ]; exact I7 s h0 h1)
    (by
      have := sclB _ ((q2.trans q3).trans sM)
      linarith only [this, h24])
    ((sclB _ (by linarith only [sM, tM0, q2])).trans_lt (by norm_num))
    (by
      have := sclA _ ((q2.trans q3).trans sM)
      linarith only [this, h24])
    ((sclA _ (by linarith only [sM, tM0, q2])).trans_lt (by norm_num))
  obtain ⟨gA, gB, hΨA, hΨB, a1, a2, a3, a4, Wray⟩ := R
  refine ⟨hψ, gA, gB, hΨA, hΨB, a1, a2, a3, a4, ?_⟩
  -- the error
  have hv := vRel_half_one
  have hs : 89 / 100 ≤ Real.sqrt (1 - vRel 1 1 (1 / 2) ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [hv.1, hv.2])
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := radar_error_pieces hK0 hX hKX hΔK ha1 ha2 hb1 hb2
    hb3 hb4 c_τ (by
      have h1 : radarTau k M * wallGap k
          = Real.pi * (wallGap k / (2 * ringRate (1200 * wallN k * wallN k) M (1 / 2)
            (wallGap k))) := by
        rw [radarTau]
        ring
      rw [h1]
      have h2 : wallGap k / (2 * ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k))
          ≤ 1 := by
        rw [div_le_one (by linarith only [hRB0])]
        linarith only [hR1]
      nlinarith only [h2, Real.pi_pos]) (radarRateB_mul_wallK hk1) (δ := wallDelta k) rfl
  -- the rate tolerance
  have hκ0 : 0 ≤ wallGap k
      + (ringLen (1200 * wallN k * wallN k) / (M + 1 : ℕ)) ^ 2 * (1 / 2) ^ 3 / 6 := by
    have := hΔ0
    positivity
  have hκ : (wallGap k
      + (ringLen (1200 * wallN k * wallN k) / (M + 1 : ℕ)) ^ 2 * (1 / 2) ^ 3 / 6)
        * (8 * wallK k) ≤ 8 * (k : ℝ) + 1 := by
    have hN1 : (1 : ℝ) ≤ wallN k := by exact_mod_cast hNpos
    have hKc : ((1200 * wallN k * wallN k : ℕ) : ℝ) = wallK k := by
      rw [wallK]
      push_cast
      ring
    have hKe : wallK k = 1200 * (wallN k : ℝ) * wallN k := rfl
    have hL : 210000 * (wallN k : ℝ) ^ 2 * wallN k ≤ ((M + 1 : ℕ) : ℝ) := by
      have : 210000 * wallN k ^ 2 * wallN k ≤ M + 1 := by omega
      exact_mod_cast this
    have hL0 : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
    set x : ℝ := ringLen (1200 * wallN k * wallN k) / ((M + 1 : ℕ) : ℝ) with hx
    have hx0 : 0 ≤ x := by
      rw [hx, ringLen]
      positivity
    have hxL : x * ((M + 1 : ℕ) : ℝ) = 2 * Real.pi * wallK k := by
      rw [hx, ringLen, hKc]
      field_simp
    have hxN : x * wallN k ≤ 1 / 25 := by
      have h1 : x * (210000 * (wallN k : ℝ) ^ 2 * wallN k) ≤ 2 * Real.pi * wallK k := by
        rw [← hxL]
        exact mul_le_mul_of_nonneg_left hL hx0
      have h2 : 2 * Real.pi * wallK k ≤ 8400 * ((wallN k : ℝ) * wallN k) := by
        rw [hKe]
        nlinarith only [Real.pi_lt_d2, mul_pos (lt_of_lt_of_le one_pos hN1)
          (lt_of_lt_of_le one_pos hN1)]
      have h3 : x * wallN k * (210000 * ((wallN k : ℝ) * wallN k))
          ≤ 1 / 25 * (210000 * ((wallN k : ℝ) * wallN k)) := by
        nlinarith only [h1, h2]
      exact le_of_mul_le_mul_right h3 (by nlinarith only [hN1])
    have hxN0 : 0 ≤ x * wallN k := mul_nonneg hx0 (by linarith only [hN1])
    have hsq2 : (x * wallN k) ^ 2 ≤ (1 / 25) ^ 2 := pow_le_pow_left₀ hxN0 hxN 2
    have e : (wallGap k + x ^ 2 * (1 / 2) ^ 3 / 6) * (8 * wallK k)
        = 8 * (wallGap k * wallK k) + 200 * (x * wallN k) ^ 2 := by
      rw [hKe]
      ring
    rw [e, hΔK]
    nlinarith only [hsq2]
  have hEr := radar_error_le (RA := ringRate (1200 * wallN k * wallN k) M 0 (wallGap k))
    (RB := ringRate (1200 * wallN k * wallN k) M (1 / 2) (wallGap k))
    (TR := radarTR (Real.pi * wallK k))
    (TRet := radarTRet (Real.pi * wallK k) (vRel 1 1 (1 / 2)))
    (TM := radarTM (Real.pi * wallK k) (vRel 1 1 (1 / 2)))
    hK0 hX hKX hΔK hRA hR2 a1.le (by linarith only [a2, hRA]) a3.le
    (by linarith only [a4, hR2]) hκ0 hκ hv.2 hs o1 o2 o4 q2 p2
    (by linarith only [o4, o5, s5]) (by linarith only [q2, q3, sM]) g1 g2 g3 g4 g5 g6 g7 g8
  have hB := radar_rest_time_le (v := vRel 1 1 (1 / 2)) hK0 hX hΔK a1.le
    (by linarith only [a2, hRA]) p2 q2 g3 g4 g7 g8
  rw [← hRA] at hB
  have hq0 : 0 < wallK k / k := div_pos hK0 hX0
  have hρ0 : (0 : ℝ) < 1 / (12000 * (k : ℝ) ^ 2) := by positivity
  have hρ1 : (0 : ℝ) < 1 / (24000 * (k : ℝ) ^ 2) := by positivity
  have hrad := radar_radius_B hK0 hX hΔK hRA hs (by linarith only [hv.2]) o1 o2 q2 p2
    g1 g2 g3 g4
  have Hn := Wray (wallK k / k) (wallK k / k) (1 / 40) (wallGap k / 5)
    (1 / (24000 * (k : ℝ) ^ 2)) (1 / (12000 * (k : ℝ) ^ 2))
    (by rw [hRA]) (by linarith only [hR2]) (by norm_num)
    ((radar_band_le hX hΔK hRB0.le hR2 o1 o2 g1 g5
      (sclB _ (by linarith only [o2, o3, o4, o5, s5]))
      (sclB _ (by linarith only [o4, o5, s5, t30]))).trans (by norm_num))
    (by
      have := sclB _ ((q2.trans q3).trans sM)
      linarith only [this, h24])
    (by
      have := sclA _ ((p2.trans p3).trans sR)
      linarith only [this, h24])
    (by
      have := sclA _ ((q2.trans q3).trans sM)
      linarith only [this, h24])
    ((sclB _ (by linarith only [o4, o5, s5, t30])).trans (by norm_num))
    ((sclB _ (by linarith only [s5, t40])).trans (by norm_num))
    ((sclB _ (by linarith only [sM, tM0, q2])).trans (by norm_num))
    ((sclA _ (by linarith only [sR, p1, p2])).trans (by norm_num))
    ((sclA _ (by linarith only [sM, tM0, q2])).trans (by norm_num))
    hρ1 (by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith only [hX])
    (by
      have h := radar_radius_A hX hΔK
      rw [show (1 : ℝ) / (24000 * (k : ℝ) ^ 2) = 1 / (12000 * (k : ℝ) ^ 2) / 2 by ring]
      linarith only [h])
    (by
      rw [show (1 : ℝ) / (24000 * (k : ℝ) ^ 2) = 1 / (12000 * (k : ℝ) ^ 2) / 2 by ring]
      linarith only [hrad, hq0])
    (by
      rw [show 4 * (wallGap k / 5) * 1 * (1 / (12000 * (k : ℝ) ^ 2)) * (8 * wallK k)
          = 32 / 60000 * (wallGap k * wallK k) / (k : ℝ) ^ 2 by ring, hΔK,
        div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith only [hX])
    (ray_error_of_radius hρ0.le (by linarith only [hΔ0]) (by linarith only [hK0]) hq0.le hrad)
  exact fun W hW θ ψ χ ξ ζ h1 h2 h3 h4 h5 =>
    (Hn W hW θ ψ χ ξ ζ h1 h2 h3 h4 h5).mono (by linarith only [hEr.1])
      (by linarith only [hEr.2]) (by linarith only [hB])

end Run

end CSD.RecordLayer

end
