/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracMasslessTails

/-!
# The relay at rest: a massless messenger from the moving observer, returned by `A`

**Category:** 7-SigmaLayer (the record layer). BACKLOG #278, second landing, second part.

The mirror of ~~#274~~'s relay arena (`DiracRelay.lean`) with the roles swapped: the messenger is
`B`'s massless `bMess` (`DiracMasslessTails.lean`), sent from `B`'s position at `t = 0`, and the
relay is at `A` — `A`'s register integrates its encounter weight with the messenger, clipped at
`1/2`, and drives the gate pulsing `σ_y` on the messenger. The whole is **one gated flow**; the
generic machinery (saturation, the pulse shape, the relay field, blocks, the pulse bound,
blindness to gate rotations) is `DiracRelay.lean`'s, unchanged.

## The arena

* `aRelayMass` (`A`'s levels, `B`'s levels, the massless messenger), `aRelayHam`, `aRelayBlock`,
  `aRelayState`, `hasDerivAt_aRelayState_block`, `hasDerivAt_aRelayState`; `aRelayRaw` (the clipped
  encounter weight of `A` with the messenger), `aRelayWeight` (saturated),
  ★ `exists_lipschitzWith_aRelayWeight`; `aRelayLipschitz`, ★★ `aRelayFlow`, `aRelayPrep`;
  ★★ `aRelayFlow_block_free`, `devA_aRelayFlow`, `devB_aRelayFlow` — the devices run free.

## Where `A` and the messenger are, sharply

* ★ `rest_tail_fine` (`A` off the chord-`1/100` arc about `1`: `≤ 2.2·10⁻²`),
  ★ `bMess_tail_fine` (the messenger off its chord-`1/100` arc: `≤ 1.1·10⁻²`);
* ★★ `aEncounter_near` — **within `8·10¹¹` of `3·10¹³` the encounter weight is at least
  `0.978 · 0.989`**; ★★ `aEncounter_far` — **beyond `1.3·10¹²` it is at most `3.3·10⁻²`**.

## The register

* `aRelayTk` (`3·10¹³`), `aRelayRate`, `aRelayReg`; `aRelayRate_eq_zero` (far), `aRelayRate_ge`
  (near); `aRelayReg_start_le` (`≤ 2.5·10¹¹` at `3·10¹³ − 8·10¹¹`), `aRelayReg_end_ge`
  (`≥ 3.7·10¹¹` at `3·10¹³`), ★★ `exists_aRelayCross` — **the register crosses `3·10¹¹` inside
  `[3·10¹³ − 8·10¹¹, 3·10¹³]`**; ★★ `aRelayFlow_eq_free` (the free trajectory up to the crossing).

## The pulse and the echo

* `sqNorm_bMess`, `sqNorm_aRelayState`, `norm_aRelayState_le`, ★ `sqNorm_aRelayFlow` (weight `3`),
  `norm_aRelayFlow_le`, ★ `aRelayWeight_aRelayFlow`, `sqNorm_mess_aRelayFlow`;
  ★ `sqNorm_diracHam_bMess_le` (**the massless messenger's energy `‖Hψ‖² ≤ 17`**),
  `sqNorm_bMess_sub_le`;
* `sqNorm_mess_aRelayFlow_sub_le`, ★★ `aRelayRaw_aRelayFlow_ge` (**the rate stays above `2/5`
  through the pulse**), ★★ `aRelayReg_after_pulse` (the pulse completes in `3·10⁻³`),
  ★★★ `sqNorm_mess_aFlip_le`, ★★★ `sqNorm_mess_aReturn_le` (**after the pulse the messenger is the
  band-flipped free messenger run backward, `‖·‖² ≤ 1.53·10⁻⁴`: a massless echo back toward `B`**);
* ★★★ `dirac_relay_at_rest` — the bundle.

## Honest scope

⚠️ **The relay fires early**: `A`'s encounter window has chord `1/10`, so the register crosses while
the messenger is still up to `8·10¹¹` short of `A` (the crossing lies in
`[3·10¹³ − 8·10¹¹, 3·10¹³]`), and the flip happens there — a `5%` uncertainty in the event's
place against `B`'s radar coordinates `≈ 1.5·10¹³`.

References: `specs/BACKLOG.md` #278, #274; `RecordLayer/DiracRelay.lean` (`gatedFlow`,
`exists_lipschitzWith_relayField`, `gatedFlow_block_eq`, `sqNorm_gateBlock_sub_gateRot_le`,
`relWeight_levelLift_gateRot_spinY`, `abs_relWeight_levelLift_sub_le`, `relayFlow`);
`RecordLayer/DiracMasslessTails.lean` (`bMess`, `bMess_tail`); `RecordLayer/DiracTwin.lean`
(`rest_tail`, `twin_budget`); `RecordLayer/DiracDoppler.lean` (`offset_mem_of_near_at`,
`offset_not_mem_of_far_at`, `devRegionWeight_levelLift`); `RecordLayer/DiracObservers.lean`
(`le_relWeight`, `relWeight_le`, `two_sin_le_norm_exp_sub_one`).
-/

@[expose] public section

open Set MeasureTheory Complex CSD.CV CSD.SigmaLayer
open scoped Matrix NNReal

namespace CSD.RecordLayer

variable {L : ℕ} [NeZero L]

/-! ### The arena -/

/-- **The rest energies**: `A`'s two levels, `B`'s two levels, the massless messenger. -/
noncomputable def aRelayMass : Fin 5 → ℝ := ![3, 3 + 1 / 10 ^ 11, 3, 3 + 1 / 10 ^ 11, 0]

theorem aRelayMass_zero : aRelayMass 0 = 3 := by simp [aRelayMass]
theorem aRelayMass_one : aRelayMass 1 = 3 + 1 / 10 ^ 11 := by simp [aRelayMass]
theorem aRelayMass_two : aRelayMass 2 = 3 := by simp [aRelayMass]
theorem aRelayMass_three : aRelayMass 3 = 3 + 1 / 10 ^ 11 := by simp [aRelayMass]
theorem aRelayMass_four : aRelayMass 4 = 0 := by simp [aRelayMass]

/-- **The free Hamiltonian**: five Dirac chains, the messenger's massless. -/
noncomputable abbrev aRelayHam (L : ℕ) : Matrix (RelayIdx L) (RelayIdx L) ℂ :=
  Matrix.blockDiagonal fun k => diracHam (relayHop L) (aRelayMass k)

/-- **The free blocks**: `A` at rest, `B` approaching, `B`'s massless messenger. -/
noncomputable def aRelayBlock (t : ℝ) : Fin 5 → ZMod L × Fin 2 → ℂ :=
  ![fun q => restObserver t (q, 0), fun q => restObserver t (q, 1),
    fun q => approachObserver (t - 5 * 10 ^ 13) (q, 0),
    fun q => approachObserver (t - 5 * 10 ^ 13) (q, 1), bMess t]

/-- **The free trajectory** as one state. -/
noncomputable def aRelayState (t : ℝ) : RelayIdx L → ℂ := fun x => aRelayBlock t x.2 x.1

theorem blockOf_aRelayState (t : ℝ) (k : Fin 5) :
    blockOf (aRelayState (L := L) t) k = aRelayBlock t k := rfl

theorem aRelayBlock_zero (t : ℝ) :
    aRelayBlock (L := L) t 0 = fun q => restObserver t (q, 0) := by simp [aRelayBlock]
theorem aRelayBlock_one (t : ℝ) :
    aRelayBlock (L := L) t 1 = fun q => restObserver t (q, 1) := by simp [aRelayBlock]
theorem aRelayBlock_two (t : ℝ) :
    aRelayBlock (L := L) t 2 = fun q => approachObserver (t - 5 * 10 ^ 13) (q, 0) := by
  simp [aRelayBlock]
theorem aRelayBlock_three (t : ℝ) :
    aRelayBlock (L := L) t 3 = fun q => approachObserver (t - 5 * 10 ^ 13) (q, 1) := by
  simp [aRelayBlock]
theorem aRelayBlock_four (t : ℝ) : aRelayBlock (L := L) t 4 = bMess t := by simp [aRelayBlock]

theorem devA_aRelayState (t : ℝ) : devA (aRelayState (L := L) t) = restObserver t := by
  funext ⟨q, i⟩
  fin_cases i
  · exact congrFun (aRelayBlock_zero (L := L) t) q
  · exact congrFun (aRelayBlock_one (L := L) t) q

theorem devB_aRelayState (t : ℝ) :
    devB (aRelayState (L := L) t) = approachObserver (t - 5 * 10 ^ 13) := by
  funext ⟨q, i⟩
  fin_cases i
  · exact congrFun (aRelayBlock_two (L := L) t) q
  · exact congrFun (aRelayBlock_three (L := L) t) q

theorem mess_aRelayState (t : ℝ) : mess (aRelayState (L := L) t) = bMess t := by
  rw [mess, blockOf_aRelayState, aRelayBlock_four]

/-- **Each block of the free trajectory solves its Dirac equation.** -/
theorem hasDerivAt_aRelayState_block (k : Fin 5) (t : ℝ) :
    HasDerivAt (fun t => aRelayBlock (L := L) t k)
      ((-I) • (diracHam (relayHop L) (aRelayMass k) *ᵥ aRelayBlock t k)) t := by
  fin_cases k
  · show HasDerivAt (fun t => aRelayBlock (L := L) t 0)
      ((-I) • (diracHam (relayHop L) (aRelayMass 0) *ᵥ aRelayBlock t 0)) t
    simp only [aRelayBlock_zero, aRelayMass_zero, restObserver, relayHop]
    exact hasDerivAt_devicePacket_level (L := L) _ 3 (3 + 1 / 10 ^ 11) _ twinAmp t 0
  · show HasDerivAt (fun t => aRelayBlock (L := L) t 1)
      ((-I) • (diracHam (relayHop L) (aRelayMass 1) *ᵥ aRelayBlock t 1)) t
    simp only [aRelayBlock_one, aRelayMass_one, restObserver, relayHop]
    exact hasDerivAt_devicePacket_level (L := L) _ 3 (3 + 1 / 10 ^ 11) _ twinAmp t 1
  · show HasDerivAt (fun t => aRelayBlock (L := L) t 2)
      ((-I) • (diracHam (relayHop L) (aRelayMass 2) *ᵥ aRelayBlock t 2)) t
    simp only [aRelayBlock_two, aRelayMass_two, approachObserver, relayHop]
    exact (hasDerivAt_devicePacket_level (L := L) _ 3 (3 + 1 / 10 ^ 11) _ twinAmp
      (t - 5 * 10 ^ 13) 0).comp_sub_const t (5 * 10 ^ 13)
  · show HasDerivAt (fun t => aRelayBlock (L := L) t 3)
      ((-I) • (diracHam (relayHop L) (aRelayMass 3) *ᵥ aRelayBlock t 3)) t
    simp only [aRelayBlock_three, aRelayMass_three, approachObserver, relayHop]
    exact (hasDerivAt_devicePacket_level (L := L) _ 3 (3 + 1 / 10 ^ 11) _ twinAmp
      (t - 5 * 10 ^ 13) 1).comp_sub_const t (5 * 10 ^ 13)
  · show HasDerivAt (fun t => aRelayBlock (L := L) t 4)
      ((-I) • (diracHam (relayHop L) (aRelayMass 4) *ᵥ aRelayBlock t 4)) t
    simp only [aRelayBlock_four, aRelayMass_four, bMess, ringPacket, relayHop]
    exact (hasDerivAt_packet (L := L) _ 0 bMessWin _ (t - 3 * 10 ^ 13)).comp_sub_const t
      (3 * 10 ^ 13)

/-- **The free trajectory solves the free equation.** -/
theorem hasDerivAt_aRelayState (t : ℝ) :
    HasDerivAt (aRelayState (L := L)) ((-I) • (aRelayHam L *ᵥ aRelayState t)) t := by
  rw [hasDerivAt_pi]
  rintro ⟨q, k⟩
  refine (hasDerivAt_pi.1 (hasDerivAt_aRelayState_block k t) q).congr_deriv ?_
  simp only [Pi.smul_apply, smul_eq_mul, aRelayHam, blockDiagonal_mulVec_block,
    blockOf_aRelayState]

theorem continuous_aRelayState : Continuous (aRelayState (L := L)) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_aRelayState t).continuousAt

omit [NeZero L] in
theorem isHermitian_aRelayHam : (aRelayHam L).IsHermitian :=
  isHermitian_blockDiagonal fun _ => diracHam_isHermitian _ _

/-! #### The weight and the gate -/

/-- **The clipped encounter weight of `A` with the messenger**: zero while the messenger is far. -/
noncomputable def aRelayRaw (Ψ : RelayIdx L → ℂ) : ℝ :=
  max (relWeight 1 (1 / 10) (devA Ψ) (levelLift 0 (mess Ψ)) - 1 / 2) 0

/-- **The register's weight**, saturated beyond sup-norm `2` and closed from `3`. -/
noncomputable def aRelayWeight (Ψ : RelayIdx L → ℂ) : ℝ := satCut 3 aRelayRaw Ψ

theorem continuous_aRelayRaw : Continuous (aRelayRaw (L := L)) :=
  ((continuous_relWeight_comp continuous_devA (continuous_levelLift_zero.comp continuous_mess) 1
    (1 / 10)).sub continuous_const).max continuous_const

theorem aRelayRaw_nonneg (Ψ : RelayIdx L → ℂ) : 0 ≤ aRelayRaw Ψ := le_max_right _ _

/-- The encounter weight is smooth: a polynomial in the components. -/
theorem contDiff_relWeight_devA_mess :
    ContDiff ℝ 1 fun Ψ : RelayIdx L → ℂ =>
      relWeight 1 (1 / 10) (devA Ψ) (levelLift 0 (mess Ψ)) := by
  simp only [relWeight, devSiteWeight_levelLift]
  refine ContDiff.sum fun j _ => ContDiff.sum fun k _ => ?_
  by_cases h : ‖(ZMod.toCircle k : ℂ) * star (ZMod.toCircle j : ℂ) - (1 : ℂ)‖ ≤ 1 / 10
  · simp only [h, ↓reduceIte]
    refine ContDiff.mul ?_ ?_
    · simp only [devSiteWeight, siteWeight, devA]
      exact ContDiff.sum fun i _ => ContDiff.sum fun c _ =>
        ContDiff.norm_sq ℂ (contDiff_apply ℝ ℂ _)
    · simp only [siteWeight, mess, blockOf]
      exact ContDiff.sum fun c _ => ContDiff.norm_sq ℂ (contDiff_apply ℝ ℂ _)
  · simp only [h, ↓reduceIte]
    exact contDiff_const

theorem exists_lipschitzOnWith_aRelayRaw :
    ∃ K : ℝ≥0, LipschitzOnWith K (aRelayRaw (L := L)) (Metric.closedBall 0 3) := by
  obtain ⟨K, hK⟩ := (contDiff_relWeight_devA_mess (L := L)).contDiffOn.exists_lipschitzOnWith
    one_ne_zero (convex_closedBall _ _) (isCompact_closedBall _ _)
  have h1 : LipschitzWith 1 fun x : ℝ => max (x - 1 / 2) 0 :=
    ((LipschitzWith.id.sub (LipschitzWith.const _)).weaken (le_of_eq (add_zero _))).max_const 0
  exact ⟨1 * K, h1.comp_lipschitzOnWith hK⟩

theorem exists_bound_aRelayRaw :
    ∃ M : ℝ≥0, ∀ Ψ : RelayIdx L → ℂ, ‖Ψ‖ ≤ 3 → |aRelayRaw Ψ| ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : RelayIdx L → ℂ) 3).exists_bound_of_continuousOn
    (continuous_aRelayRaw (L := L)).continuousOn
  refine ⟨Real.toNNReal C, fun Ψ hΨ => ?_⟩
  have := hC Ψ (mem_closedBall_zero_iff.2 hΨ)
  rw [Real.norm_eq_abs] at this
  exact this.trans (Real.le_coe_toNNReal C)

/-- ★ **The saturated weight is globally Lipschitz.** -/
theorem exists_lipschitzWith_aRelayWeight :
    ∃ K : ℝ≥0, LipschitzWith K (aRelayWeight (L := L)) := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_aRelayRaw (L := L)
  obtain ⟨M, hM⟩ := exists_bound_aRelayRaw (L := L)
  exact ⟨K + M, lipschitzWith_satCut hK hM⟩

theorem exists_bound_aRelayWeight :
    ∃ M : ℝ≥0, ∀ Ψ : RelayIdx L → ℂ, |aRelayWeight Ψ| ≤ M := by
  obtain ⟨M, hM⟩ := exists_bound_aRelayRaw (L := L)
  exact ⟨M, fun Ψ => abs_satCut_le hM Ψ⟩

theorem aRelayWeight_eq_zero {Ψ : RelayIdx L → ℂ} (h : (3 : ℝ) ≤ ‖Ψ‖) : aRelayWeight Ψ = 0 :=
  satCut_eq_zero _ h

theorem aRelayWeight_eq_of_le {Ψ : RelayIdx L → ℂ} (h : ‖Ψ‖ ≤ 2) :
    aRelayWeight Ψ = aRelayRaw Ψ :=
  satCut_eq_of_le _ (by linarith)

theorem aRelayWeight_nonneg (Ψ : RelayIdx L → ℂ) : 0 ≤ aRelayWeight Ψ :=
  satCut_nonneg aRelayRaw_nonneg Ψ

theorem continuous_aRelayWeight : Continuous (aRelayWeight (L := L)) :=
  (exists_lipschitzWith_aRelayWeight (L := L)).choose_spec.continuous

/-- ★★ **The relay field at `A` is globally Lipschitz.** -/
theorem aRelayLipschitz : ∃ K : ℝ≥0, LipschitzWith K
    (gatedField (aRelayHam L) (relayGateMat L) (relayGate relayLo relayHi aRelayWeight)
      aRelayWeight) := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_aRelayWeight (L := L)
  obtain ⟨M, hM⟩ := exists_bound_aRelayWeight (L := L)
  exact exists_lipschitzWith_relayField _ _ relayLo_lt_relayHi hK hM (by norm_num)
    fun Ψ h => aRelayWeight_eq_zero h

/-- ★★ **The relay flow at `A`**: `A`, `B`, `B`'s massless messenger and `A`'s relay register, one
gated flow. -/
noncomputable def aRelayFlow (t : ℝ) (x : GateArena (RelayIdx L)) : GateArena (RelayIdx L) :=
  gatedFlow aRelayLipschitz t x

/-- **The preparation**: the free state at time `0`, the register at `0`. -/
noncomputable def aRelayPrep (L : ℕ) [NeZero L] : GateArena (RelayIdx L) := (aRelayState 0, 0)

theorem continuous_aRelayGate : Continuous fun x : GateArena (RelayIdx L) =>
    relayGate relayLo relayHi aRelayWeight x.1 x.2 :=
  ((continuous_pulseRate _ _).comp continuous_snd).mul (continuous_aRelayWeight.comp continuous_fst)

/-- ★★ **The devices evolve freely for all time.** -/
theorem aRelayFlow_block_free {k : Fin 5} (hk : k ≠ 4) (t : ℝ) :
    blockOf (aRelayFlow t (aRelayPrep L)).1 k = aRelayBlock t k :=
  gatedFlow_block_eq aRelayLipschitz (aRelayPrep L) hk (hasDerivAt_aRelayState_block k) rfl t

theorem devA_aRelayFlow (t : ℝ) : devA (aRelayFlow t (aRelayPrep L)).1 = restObserver t := by
  funext ⟨q, i⟩
  fin_cases i
  · show blockOf (aRelayFlow t (aRelayPrep L)).1 0 q = restObserver t (q, 0)
    rw [aRelayFlow_block_free (by decide), aRelayBlock_zero]
  · show blockOf (aRelayFlow t (aRelayPrep L)).1 1 q = restObserver t (q, 1)
    rw [aRelayFlow_block_free (by decide), aRelayBlock_one]

theorem devB_aRelayFlow (t : ℝ) :
    devB (aRelayFlow t (aRelayPrep L)).1 = approachObserver (t - 5 * 10 ^ 13) := by
  funext ⟨q, i⟩
  fin_cases i
  · show blockOf (aRelayFlow t (aRelayPrep L)).1 2 q = approachObserver (t - 5 * 10 ^ 13) (q, 0)
    rw [aRelayFlow_block_free (by decide), aRelayBlock_two]
  · show blockOf (aRelayFlow t (aRelayPrep L)).1 3 q = approachObserver (t - 5 * 10 ^ 13) (q, 1)
    rw [aRelayFlow_block_free (by decide), aRelayBlock_three]

theorem aRelayFlow_register_mono {s t : ℝ} (hst : s ≤ t) :
    (aRelayFlow s (aRelayPrep L)).2 ≤ (aRelayFlow t (aRelayPrep L)).2 := by
  have e : aRelayFlow t (aRelayPrep L) = aRelayFlow (t - s) (aRelayFlow s (aRelayPrep L)) := by
    rw [aRelayFlow, aRelayFlow, aRelayFlow, ← gatedFlow_add, add_sub_cancel]
  rw [e]
  exact register_mono_gatedFlow _ continuous_aRelayWeight aRelayWeight_nonneg _ (by linarith)

/-! ### The free register -/

/-- The messenger's arrival at `A`, `3·10¹³`. -/
noncomputable def aRelayTk : ℝ := 3 * 10 ^ 13

/-- **The free register's rate**. -/
noncomputable def aRelayRate (L : ℕ) [NeZero L] (s : ℝ) : ℝ := aRelayRaw (aRelayState (L := L) s)

/-- **The free register**. -/
noncomputable def aRelayReg (L : ℕ) [NeZero L] (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, aRelayRate L s

theorem aRelayRate_eq (s : ℝ) :
    aRelayRate L s = max (relWeight 1 (1 / 10) (restObserver (L := L) s)
      (levelLift 0 (bMess (L := L) s)) - 1 / 2) 0 := by
  rw [aRelayRate, aRelayRaw, devA_aRelayState, mess_aRelayState]

theorem continuous_aRelayRate : Continuous (aRelayRate L) :=
  continuous_aRelayRaw.comp continuous_aRelayState

theorem aRelayRate_nonneg (s : ℝ) : 0 ≤ aRelayRate L s := aRelayRaw_nonneg _

theorem hasDerivAt_aRelayReg (t : ℝ) : HasDerivAt (aRelayReg L) (aRelayRate L t) t :=
  ((continuous_aRelayRate (L := L)).integral_hasStrictDerivAt 0 t).hasDerivAt

theorem continuous_aRelayReg : Continuous (aRelayReg L) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_aRelayReg t).continuousAt

theorem aRelayReg_zero : aRelayReg L 0 = 0 := intervalIntegral.integral_same

theorem aRelayReg_mono {s t : ℝ} (hst : s ≤ t) : aRelayReg L s ≤ aRelayReg L t := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((continuous_aRelayRate (L := L)).intervalIntegrable 0 s)
    ((continuous_aRelayRate (L := L)).intervalIntegrable s t)
  have h2 := intervalIntegral.integral_nonneg (μ := volume) hst
    fun u _ => aRelayRate_nonneg (L := L) u
  unfold aRelayReg
  linarith

section WithL

variable (hL : 10 ^ 19 ≤ L)
include hL

/-! ### Where `A` and the messenger are, sharply -/

/-- ★ **`A` off the chord-`1/100` arc about `1`**: at most `2.2·10⁻²` of its weight. -/
theorem rest_tail_fine {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 8 * 10 ^ 13) :
    devRegionWeight (restObserver (L := L) t) (chordArc 1 (1 / 100))ᶜ ≤ 22 / 1000 := by
  have hz : ∀ μ : ℝ,
      ‖exp (I * ((2 * Real.pi / (2 * Real.pi * 10 ^ 13) * vRel 1 μ (1 * 0) * t : ℝ) : ℂ)) - 1‖
        ≤ 0 := fun μ => by
    simp [vRel]
  have h := devRegionWeight_compl_chordArc_le (L := L) (c := 1) (μ₀ := 3) (μ₁ := 3 + 1 / 10 ^ 11)
    (ℓ := 2 * Real.pi * 10 ^ 13) (P := 0) (D := 1 / 10 ^ 7) (p₀ := 0) one_pos (by norm_num)
    (by norm_num) (by positivity) (by simp) (by positivity) (rest_win hL) rest_spread twinAmp
    (twin_norm hL _) (z := 1) (ρ := 1 / 100) (η := 0) (by norm_num) t (hz 3) (hz _)
  have b0 := twin_budget (L := L) hL (μ := 3) le_rfl (-1000000) (D := 1 / 10 ^ 7) (P := 0)
    (by positivity) (by norm_num) le_rfl (by norm_num) ht0 ht
  have b1 := twin_budget (L := L) hL (μ := 3 + 1 / 10 ^ 11) (by norm_num) (-1000000)
    (D := 1 / 10 ^ 7) (P := 0) (by positivity) (by norm_num) le_rfl (by norm_num) ht0 ht
  have hnn := devRegionWeight_nonneg (restObserver (L := L) t) (chordArc 1 (1 / 100))ᶜ
  unfold restObserver at hnn ⊢
  rw [sub_zero] at h
  nlinarith

/-- ★ **The messenger off its chord-`1/100` arc**: at most `1.1·10⁻²`. -/
theorem bMess_tail_fine {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 8 * 10 ^ 13) :
    regionWeight (bMess (L := L) t)
        (chordArc (exp (I * ((1 / 10 ^ 13 * (t - 3 * 10 ^ 13) : ℝ) : ℂ))) (1 / 100))ᶜ
      ≤ 11 / 1000 := by
  have hLr : (10 ^ 19 : ℝ) ≤ L := by exact_mod_cast hL
  have hπ2 : Real.pi < 63 / 20 := by
    have := Real.pi_lt_d2
    norm_num at this ⊢
    linarith
  set s := t - 3 * 10 ^ 13 with hs
  have hs_abs : |s| ≤ 5 * 10 ^ 13 := by rw [abs_le]; constructor <;> linarith
  have hrate := abs_bMessRate_sub_le hL
  have hz : ‖exp (I * ((bMessRate L * s : ℝ) : ℂ))
      - exp (I * ((1 / 10 ^ 13 * s : ℝ) : ℂ))‖ ≤ 1 / 10 ^ 8 := by
    have h := norm_exp_I_mul_sub_le (bMessRate L) (1 / 10 ^ 13) s
    rw [show I * ((bMessRate L * s : ℝ) : ℂ) = I * (((bMessRate L : ℝ) : ℂ) * (s : ℂ)) by
        push_cast; ring,
      show I * ((1 / 10 ^ 13 * s : ℝ) : ℂ) = I * (((1 / 10 ^ 13 : ℝ) : ℂ) * (s : ℂ)) by
        push_cast; ring]
    refine h.trans ?_
    calc |s| * |bMessRate L - 1 / 10 ^ 13| ≤ 5 * 10 ^ 13 * (4 / 10 ^ 23) :=
          mul_le_mul hs_abs hrate (abs_nonneg _) (by norm_num)
      _ ≤ 1 / 10 ^ 8 := by norm_num
  have h := regionWeight_compl_chordArc_massless_le (L := L) (c := 1) (ℓ := 2 * Real.pi * 10 ^ 13)
    (D := 2 / 10 ^ 7) (p₀ := 4) one_pos (by positivity) (by positivity) (bMess_win hL)
    (rightWindow_bMessWin hL) moving_spread twinAmp (twin_norm hL _)
    (z := exp (I * ((1 / 10 ^ 13 * s : ℝ) : ℂ))) (ρ := 1 / 100) (η := 1 / 10 ^ 8) (by norm_num) s
    hz
  rw [bMess_re_transPhase_zero hL] at h
  set a := 2 * Real.pi * 10 ^ 13 / L
  have ha0 : 0 < a := by positivity
  have ha : a ≤ 63 / 10 ^ 7 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hE : |s| * masslessErr 1 (2 * Real.pi * 10 ^ 13) (2 / 10 ^ 7) a ≤ 1 / 10 ^ 10 := by
    have e : masslessErr 1 (2 * Real.pi * 10 ^ 13) (2 / 10 ^ 7) a
        = 1 / 10 ^ 13 * a * (2 / 10 ^ 7 + 1 / 10 ^ 13) := by
      rw [masslessErr]
      field_simp
    rw [e]
    have h1 : 0 ≤ 1 / 10 ^ 13 * a * (2 / 10 ^ 7 + 1 / 10 ^ 13) := by positivity
    calc |s| * (1 / 10 ^ 13 * a * (2 / 10 ^ 7 + 1 / 10 ^ 13))
        ≤ 5 * 10 ^ 13 * (1 / 10 ^ 13 * (63 / 10 ^ 7) * (2 / 10 ^ 7 + 1 / 10 ^ 13)) := by
          gcongr
      _ ≤ 1 / 10 ^ 10 := by norm_num
  have hnn := regionWeight_nonneg (bMess (L := L) t)
    (chordArc (exp (I * ((1 / 10 ^ 13 * s : ℝ) : ℂ))) (1 / 100))ᶜ
  unfold bMess at hnn ⊢
  rw [← hs] at hnn ⊢
  have hN : ((2000000 : ℕ) : ℝ) = 2000000 := by norm_num
  rw [hN] at h
  set w := regionWeight (ringPacket (L := L) 1 0 (2 * Real.pi * 10 ^ 13) bMessWin twinAmp s)
    (chordArc (exp (I * ((1 / 10 ^ 13 * s : ℝ) : ℂ))) (1 / 100))ᶜ
  have hK : (1 / 20000 : ℝ) * (99 / 100) ≤ (1 / 100 - 1 / 10 ^ 8) ^ 2 / 2 := by norm_num
  have h3 := mul_le_mul_of_nonneg_left hK hnn
  nlinarith

/-- ★★ **The messenger at `A`**: within `8·10¹¹` of `3·10¹³` the encounter weight is at least
`(1 − 0.022)(1 − 0.011)`. -/
theorem aEncounter_near {s : ℝ} (hs0 : 0 ≤ s) (hs8 : s ≤ 8 * 10 ^ 13)
    (hs : |s - 3 * 10 ^ 13| ≤ 8 * 10 ^ 11) :
    (1 - 22 / 1000) * (1 - 11 / 1000) ≤ relWeight 1 (1 / 10) (restObserver (L := L) s)
      (levelLift 0 (bMess (L := L) s)) := by
  have tA := rest_tail_fine hL hs0 hs8
  have tm := bMess_tail_fine hL hs0 hs8
  have hX := devRegionWeight_add_compl (restObserver (L := L) s) (chordArc 1 (1 / 100))
  rw [rest_total hL] at hX
  have hY := regionWeight_add_compl (bMess (L := L) s)
    (chordArc (exp (I * ((1 / 10 ^ 13 * (s - 3 * 10 ^ 13) : ℝ) : ℂ))) (1 / 100))
  rw [bMess_norm hL, Complex.one_re] at hY
  have hoff : ‖exp (I * ((1 / 10 ^ 13 * (s - 3 * 10 ^ 13) : ℝ) : ℂ)) * star (1 : ℂ) - 1‖
      ≤ 8 / 100 := by
    rw [star_one, mul_one]
    have := norm_exp_sub_exp_le (1 / 10 ^ 13 * (s - 3 * 10 ^ 13)) 0
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_zero, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 10 ^ 13)] at this
    refine this.trans ?_
    calc 1 / 10 ^ 13 * |s - 3 * 10 ^ 13| ≤ 1 / 10 ^ 13 * (8 * 10 ^ 11) :=
          mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = 8 / 100 := by norm_num
  have hle := le_relWeight (w := 1) (ρ := 1 / 10) (ΨA := restObserver (L := L) s)
    (ΨB := levelLift 0 (bMess (L := L) s)) (X := chordArc 1 (1 / 100))
    (Y := chordArc (exp (I * ((1 / 10 ^ 13 * (s - 3 * 10 ^ 13) : ℝ) : ℂ))) (1 / 100))
    fun j hj k hk =>
      offset_mem_of_near_at (norm_exp_I_mul_ofReal_eq_one _) (mem_chordArc.1 hj)
        (mem_chordArc.1 hk) (by linarith)
  rw [devRegionWeight_levelLift] at hle
  have hA : 1 - 22 / 1000 ≤ devRegionWeight (restObserver (L := L) s) (chordArc 1 (1 / 100)) := by
    linarith
  have hB : 1 - 11 / 1000 ≤ regionWeight (bMess (L := L) s)
      (chordArc (exp (I * ((1 / 10 ^ 13 * (s - 3 * 10 ^ 13) : ℝ) : ℂ))) (1 / 100)) := by linarith
  calc (1 - 22 / 1000) * (1 - 11 / 1000)
      ≤ _ := mul_le_mul hA hB (by norm_num) (devRegionWeight_nonneg _ _)
    _ ≤ _ := hle

/-- ★★ **The messenger away from `A`**: while their angle is at least `0.13` from every multiple of
`2π`, the encounter weight is at most `3.3·10⁻²`. -/
theorem aEncounter_far {s : ℝ} (hs0 : 0 ≤ s) (hs8 : s ≤ 8 * 10 ^ 13)
    (h1 : 13 / 100 ≤ |1 / 10 ^ 13 * (s - 3 * 10 ^ 13)|)
    (h2 : |1 / 10 ^ 13 * (s - 3 * 10 ^ 13)| ≤ 2 * Real.pi - 13 / 100) :
    relWeight 1 (1 / 10) (restObserver (L := L) s) (levelLift 0 (bMess (L := L) s))
      ≤ 33 / 1000 := by
  have tA := rest_tail_fine hL hs0 hs8
  have tm := bMess_tail_fine hL hs0 hs8
  have hsin := Real.sin_gt_sub_cube (x := 13 / 100 / 2) (by norm_num)
  have hfar := two_sin_le_norm_exp_sub_one (y := 13 / 100)
    (z := 1 / 10 ^ 13 * (s - 3 * 10 ^ 13)) (by norm_num) h1 h2
  have : (12 / 100 : ℝ) < 2 * (13 / 100 / 2 - (13 / 100 / 2) ^ 3 / 6) := by norm_num
  have hoff : 12 / 100
      < ‖exp (I * ((1 / 10 ^ 13 * (s - 3 * 10 ^ 13) : ℝ) : ℂ)) * star (1 : ℂ) - 1‖ := by
    rw [star_one, mul_one]
    linarith
  have hle := relWeight_le (w := 1) (ρ := 1 / 10) (ΨA := restObserver (L := L) s)
    (ΨB := levelLift 0 (bMess (L := L) s)) (X := chordArc 1 (1 / 100))
    (Y := chordArc (exp (I * ((1 / 10 ^ 13 * (s - 3 * 10 ^ 13) : ℝ) : ℂ))) (1 / 100))
    fun j hj k hk =>
      offset_not_mem_of_far_at (norm_exp_I_mul_ofReal_eq_one _) (mem_chordArc.1 hj)
        (mem_chordArc.1 hk) (by linarith)
  rw [devRegionWeight_levelLift, devRegionWeight_levelLift, rest_total hL] at hle
  have hn : regionWeight (bMess (L := L) s) Finset.univ = 1 := by
    have := regionWeight_add_compl (bMess (L := L) s) Finset.univ
    rw [bMess_norm hL, Complex.one_re, Finset.compl_univ] at this
    simpa [regionWeight] using this
  rw [hn, mul_one, one_mul] at hle
  linarith

/-! ### Norms and the messenger's energy -/

theorem sqNorm_bMess (t : ℝ) : sqNorm (bMess (L := L) t) = 1 := by
  rw [sqNorm_eq_re_chainInner, bMess_norm hL, Complex.one_re]

/-- **The free state carries weight `3`.** -/
theorem sqNorm_aRelayState (t : ℝ) : sqNorm (aRelayState (L := L) t) = 3 := by
  rw [sqNorm_eq_sum_blocks]
  simp only [Fin.sum_univ_five, blockOf_aRelayState, aRelayBlock_zero, aRelayBlock_one,
    aRelayBlock_two, aRelayBlock_three, aRelayBlock_four]
  have hA := rest_total (L := L) hL t
  have hB := approach_total (L := L) hL (t - 5 * 10 ^ 13)
  rw [devRegionWeight_univ_eq, Fin.sum_univ_two] at hA hB
  have hM := sqNorm_bMess hL t
  linarith

theorem norm_aRelayState_le (t : ℝ) : ‖aRelayState (L := L) t‖ ≤ 2 :=
  norm_le_two_of_sqNorm_le (le_of_eq (sqNorm_aRelayState hL t))

/-- ★ **The relay flow at `A` conserves the weight `3`.** -/
theorem sqNorm_aRelayFlow (t : ℝ) : sqNorm (aRelayFlow t (aRelayPrep L)).1 = 3 := by
  have h := sum_norm_sq_gatedFlow aRelayLipschitz isHermitian_aRelayHam isHermitian_relayGateMat
    (aRelayPrep L) t
  show ∑ i, ‖(gatedFlow aRelayLipschitz t (aRelayPrep L)).1 i‖ ^ 2 = 3
  rw [h]
  exact sqNorm_aRelayState hL 0

theorem norm_aRelayFlow_le (t : ℝ) : ‖(aRelayFlow t (aRelayPrep L)).1‖ ≤ 2 :=
  norm_le_two_of_sqNorm_le (le_of_eq (sqNorm_aRelayFlow hL t))

/-- ★ **Along the orbit the saturation is invisible.** -/
theorem aRelayWeight_aRelayFlow (t : ℝ) :
    aRelayWeight (aRelayFlow t (aRelayPrep L)).1 = aRelayRaw (aRelayFlow t (aRelayPrep L)).1 :=
  aRelayWeight_eq_of_le (norm_aRelayFlow_le hL t)

/-- **The messenger keeps its weight `1`** through the pulse. -/
theorem sqNorm_mess_aRelayFlow (t : ℝ) :
    sqNorm (mess (aRelayFlow t (aRelayPrep L)).1) = 1 := by
  have h := sqNorm_aRelayFlow hL t
  rw [sqNorm_eq_sum_blocks] at h
  simp only [Fin.sum_univ_five, aRelayFlow_block_free (k := 0) (by decide),
    aRelayFlow_block_free (k := 1) (by decide), aRelayFlow_block_free (k := 2) (by decide),
    aRelayFlow_block_free (k := 3) (by decide), aRelayBlock_zero, aRelayBlock_one,
    aRelayBlock_two, aRelayBlock_three] at h
  have hA := rest_total (L := L) hL t
  have hB := approach_total (L := L) hL (t - 5 * 10 ^ 13)
  rw [devRegionWeight_univ_eq, Fin.sum_univ_two] at hA hB
  show sqNorm (blockOf (aRelayFlow t (aRelayPrep L)).1 4) = 1
  linarith

/-- ★ **The massless messenger's energy**: `‖Hψ‖² ≤ 17` (`E² ≤ (4 + 2·10⁻⁷)²`). -/
theorem sqNorm_diracHam_bMess_le (s : ℝ) :
    sqNorm (diracHam (relayHop L) 0 *ᵥ bMess (L := L) s) ≤ 17 := by
  have hD := (noWrap_distinct_of_window (L := L) (bMess_win hL)).2
  have h := sqNorm_diracHam_mulVec_packet_le (L := L) (relayHop L) 0 hD
    (unitAmp L (relayHop L) 0 twinAmp) (s - 3 * 10 ^ 13) (E2 := 17) fun m hm => by
      have := bandE_sq_le_scaled (L := L) (ℓ := 2 * Real.pi * 10 ^ 13) (by positivity) 0
        (moving_spread m hm)
      refine this.trans ?_
      norm_num
  have hn := sqNorm_bMess hL s
  simp only [bMess, ringPacket] at hn ⊢
  simp only [relayHop] at h
  rw [hn, mul_one] at h
  exact h

/-- **The free messenger drifts by at most `u√17` in time `u`.** -/
theorem sqNorm_bMess_sub_le (s : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    sqNorm (bMess (L := L) (s + u) - bMess s) ≤ u ^ 2 * 17 := by
  have h := sqNorm_sub_gateRot_le (H := diracHam (relayHop L) 0) (V := spinY)
    (diracHam_isHermitian _ _) spinY_isHermitian (spinY_mulVec_diracHam_mulVec _ _)
    spinY_mulVec_spinY (c := fun _ => 0) continuous_const
    (Ψ := fun u => bMess (L := L) (s + u)) (fun u => ?_) hu
  · rw [intervalIntegral.integral_zero, gateRot_zero_mulVec, add_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (sqNorm_diracHam_bMess_le hL _) (sq_nonneg _))
  · have h1 := ((hasDerivAt_packet (L := L) (relayHop L) 0 bMessWin
      (unitAmp L (relayHop L) 0 twinAmp) (s + u - 3 * 10 ^ 13)).comp_sub_const (s + u)
      (3 * 10 ^ 13)).comp_const_add s u
    simp only [bMess, ringPacket, Complex.ofReal_zero, zero_smul, add_zero]
    simpa only [relayHop] using h1

/-! ### The register before, through and after the encounter -/

/-- **Before the encounter the rate is zero.** -/
theorem aRelayRate_eq_zero {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ aRelayTk - 13 * 10 ^ 11) :
    aRelayRate L s = 0 := by
  have hπ := pi_gt_314
  have htk : aRelayTk = 3 * 10 ^ 13 := rfl
  rw [aRelayRate_eq]
  have hs' : s ≤ 3 * 10 ^ 13 - 13 * 10 ^ 11 := by rw [htk] at hs; exact hs
  have habs : |1 / 10 ^ 13 * (s - 3 * 10 ^ 13)| = 1 / 10 ^ 13 * (3 * 10 ^ 13 - s) := by
    rw [abs_of_nonpos (by nlinarith)]
    ring
  have hfar := aEncounter_far hL hs0 (by linarith) (by rw [habs]; linarith)
    (by rw [habs]; linarith)
  exact max_eq_right (by linarith)

theorem aRelayRate_le_half (s : ℝ) : aRelayRate L s ≤ 1 / 2 := by
  rw [aRelayRate_eq]
  have h := relWeight_le_mul 1 (1 / 10) (restObserver (L := L) s) (levelLift 0 (bMess (L := L) s))
  rw [rest_total hL, devRegionWeight_levelLift, one_mul] at h
  have hn : regionWeight (bMess (L := L) s) Finset.univ = 1 := by
    have := regionWeight_add_compl (bMess (L := L) s) Finset.univ
    rw [bMess_norm hL, Complex.one_re, Finset.compl_univ] at this
    simpa [regionWeight] using this
  rw [hn] at h
  exact max_le (by linarith) (by norm_num)

/-- **Through the encounter the rate is at least `0.978 · 0.989 − 1/2`.** -/
theorem aRelayRate_ge {s : ℝ} (hs0 : 0 ≤ s) (hs8 : s ≤ 8 * 10 ^ 13)
    (hs : |s - aRelayTk| ≤ 8 * 10 ^ 11) :
    (1 - 22 / 1000) * (1 - 11 / 1000) - 1 / 2 ≤ aRelayRate L s := by
  rw [aRelayRate_eq]
  have hnear := aEncounter_near hL hs0 hs8 hs
  exact le_max_of_le_left (by linarith)

/-- **At the start of the sure window the register is at most `2.5·10¹¹`.** -/
theorem aRelayReg_start_le : aRelayReg L (aRelayTk - 8 * 10 ^ 11) ≤ 25 * 10 ^ 10 := by
  have htk : aRelayTk = 3 * 10 ^ 13 := rfl
  have h := integral_le_of_le_on_then (continuous_aRelayRate (L := L)) (ε := 0) (M := 1 / 2)
    (tf := aRelayTk - 13 * 10 ^ 11) (t := aRelayTk - 8 * 10 ^ 11) (by rw [htk]; norm_num)
    (by rw [htk]; norm_num) (fun s hs0 hs => (aRelayRate_eq_zero hL hs0 hs).le)
    (aRelayRate_le_half hL)
  rw [aRelayReg]
  refine h.trans ?_
  rw [htk]
  norm_num

/-- **At the messenger's arrival the register is at least `3.7·10¹¹`.** -/
theorem aRelayReg_end_ge : 37 * 10 ^ 10 ≤ aRelayReg L aRelayTk := by
  have htk : aRelayTk = 3 * 10 ^ 13 := rfl
  have h := le_integral_of_ge_on (continuous_aRelayRate (L := L))
    (κ := (1 - 22 / 1000) * (1 - 11 / 1000) - 1 / 2)
    (tn := aRelayTk - 8 * 10 ^ 11) (te := aRelayTk) (t := aRelayTk)
    (by rw [htk]; norm_num) (by linarith) le_rfl (fun s _ => aRelayRate_nonneg s)
    fun s hs1 hs2 => aRelayRate_ge hL (by rw [htk] at hs1; linarith)
      (by rw [htk] at hs2; linarith) (by rw [abs_le]; constructor <;> linarith)
  rw [aRelayReg]
  refine le_trans ?_ h
  rw [htk]
  norm_num

/-- ★★ **The register crosses the threshold inside `[3·10¹³ − 8·10¹¹, 3·10¹³]`.** -/
theorem exists_aRelayCross :
    ∃ s₀ ∈ Icc (aRelayTk - 8 * 10 ^ 11) aRelayTk, aRelayReg L s₀ = relayLo := by
  have h := intermediate_value_Icc (f := aRelayReg L)
    (a := aRelayTk - 8 * 10 ^ 11) (b := aRelayTk) (by linarith)
    (continuous_aRelayReg (L := L)).continuousOn
  have hmem : relayLo ∈ Icc (aRelayReg L (aRelayTk - 8 * 10 ^ 11)) (aRelayReg L aRelayTk) := by
    constructor
    · exact (aRelayReg_start_le hL).trans (by unfold relayLo; norm_num)
    · exact (by unfold relayLo; norm_num : relayLo ≤ 37 * 10 ^ 10).trans (aRelayReg_end_ge hL)
  obtain ⟨s₀, hs₀, h₀⟩ := h hmem
  exact ⟨s₀, hs₀, h₀⟩

/-- ★★ **Up to the crossing the orbit is the free trajectory with the free register.** -/
theorem aRelayFlow_eq_free {s₀ : ℝ} (hr : aRelayReg L s₀ ≤ relayLo) :
    ∀ t ∈ Icc (0 : ℝ) s₀, aRelayFlow t (aRelayPrep L) = (aRelayState t, aRelayReg L t) := by
  refine gatedFlow_eq_of_hasDerivAt_Icc aRelayLipschitz (aRelayPrep L)
    (y := fun t => (aRelayState t, aRelayReg L t)) (fun t ht => ?_) ?_
  · have hreg : aRelayReg L t ≤ relayLo := (aRelayReg_mono ht.2).trans hr
    have hgate : relayGate relayLo relayHi aRelayWeight (aRelayState (L := L) t)
        (aRelayReg L t) = 0 :=
      relayGate_eq_zero_of_le relayLo_lt_relayHi _ _ hreg
    have hw : aRelayWeight (aRelayState (L := L) t) = aRelayRate L t :=
      aRelayWeight_eq_of_le (norm_aRelayState_le hL t)
    refine ((hasDerivAt_aRelayState t).prodMk (hasDerivAt_aRelayReg t)).congr_deriv ?_
    simp only [gatedField, hgate, Complex.ofReal_zero, zero_smul, add_zero, hw]
  · show (aRelayState (L := L) 0, aRelayReg L 0) = (aRelayState 0, 0)
    rw [aRelayReg_zero]

/-! ### The pulse -/

/-- **The pulse bound on the messenger** from a free crossing state. -/
theorem sqNorm_mess_aRelayFlow_sub_le {s₀ : ℝ}
    (hfree : aRelayFlow s₀ (aRelayPrep L) = (aRelayState s₀, relayLo)) {u : ℝ} (hu : 0 ≤ u) :
    sqNorm (mess (aRelayFlow (s₀ + u) (aRelayPrep L)).1
        - gateRot spinY (∫ s in (0 : ℝ)..u, relayGate relayLo relayHi aRelayWeight
            (aRelayFlow (s₀ + s) (aRelayPrep L)).1 (aRelayFlow (s₀ + s) (aRelayPrep L)).2)
          *ᵥ bMess s₀)
      ≤ u ^ 2 * 17 := by
  have h := sqNorm_gateBlock_sub_gateRot_le aRelayLipschitz (k₀ := 4) (diracHam_isHermitian _ _)
    spinY_isHermitian (spinY_mulVec_diracHam_mulVec _ _) spinY_mulVec_spinY continuous_aRelayGate
    (aRelayPrep L) s₀ hu
  change sqNorm (mess (aRelayFlow (s₀ + u) (aRelayPrep L)).1 - gateRot spinY
    (∫ s in (0 : ℝ)..u, relayGate relayLo relayHi aRelayWeight
      (aRelayFlow (s₀ + s) (aRelayPrep L)).1 (aRelayFlow (s₀ + s) (aRelayPrep L)).2)
    *ᵥ mess (aRelayFlow s₀ (aRelayPrep L)).1) ≤ u ^ 2 * sqNorm (diracHam (relayHop L)
    (aRelayMass 4) *ᵥ mess (aRelayFlow s₀ (aRelayPrep L)).1) at h
  rw [aRelayMass_four, hfree] at h
  have e : mess (aRelayState (L := L) s₀, relayLo).1 = bMess s₀ := mess_aRelayState s₀
  rw [e] at h
  exact h.trans (mul_le_mul_of_nonneg_left (sqNorm_diracHam_bMess_le hL _) (sq_nonneg _))

/-- ★★ **Through the pulse the rate stays above `2/5`**: blindness to the rotation, and two drifts
of at most `u√17 ≤ 0.0126`. -/
theorem aRelayRaw_aRelayFlow_ge {s₀ : ℝ} (hs₀ : s₀ ∈ Icc (aRelayTk - 8 * 10 ^ 11) aRelayTk)
    (hfree : aRelayFlow s₀ (aRelayPrep L) = (aRelayState s₀, relayLo)) {u : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ 3 / 1000) : 2 / 5 ≤ aRelayRaw (aRelayFlow (s₀ + u) (aRelayPrep L)).1 := by
  have htk : aRelayTk = 3 * 10 ^ 13 := rfl
  obtain ⟨hs1, hs2⟩ := hs₀
  rw [htk] at hs1 hs2
  set ψ₀ := bMess (L := L) s₀ with hψ₀def
  set ψu := bMess (L := L) (s₀ + u) with hψudef
  set Mu := mess (aRelayFlow (s₀ + u) (aRelayPrep L)).1 with hMudef
  set θ := ∫ s in (0 : ℝ)..u, relayGate relayLo relayHi aRelayWeight
    (aRelayFlow (s₀ + s) (aRelayPrep L)).1 (aRelayFlow (s₀ + s) (aRelayPrep L)).2 with hθdef
  set A := restObserver (L := L) (s₀ + u) with hAdef
  have hA : devA (aRelayFlow (s₀ + u) (aRelayPrep L)).1 = A := devA_aRelayFlow _
  have h1 : sqNorm (Mu - gateRot spinY θ *ᵥ ψ₀) ≤ u ^ 2 * 17 :=
    sqNorm_mess_aRelayFlow_sub_le hL hfree hu0
  have h2 : sqNorm (ψ₀ - ψu) ≤ u ^ 2 * 17 := by
    rw [sqNorm_sub_comm, hψudef]
    exact sqNorm_bMess_sub_le hL _ hu0
  have hMu : sqNorm Mu = 1 := sqNorm_mess_aRelayFlow hL _
  have hψ₀ : sqNorm ψ₀ = 1 := sqNorm_bMess hL _
  have hψu : sqNorm ψu = 1 := sqNorm_bMess hL _
  have hrot : sqNorm (gateRot spinY θ *ᵥ ψ₀) = 1 := by
    rw [sqNorm_gateRot_mulVec spinY_isHermitian spinY_mulVec_spinY, hψ₀]
  have hAtot : devRegionWeight A Finset.univ = 1 := rest_total hL _
  have hsqrt4 : Real.sqrt (2 * 1 + 2 * 1) = 2 := by
    rw [show (2 : ℝ) * 1 + 2 * 1 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hbound : ∀ d : ℝ, d ≤ u ^ 2 * 17 → Real.sqrt d ≤ 3 / 1000 * (42 / 10) := fun d hd => by
    rw [Real.sqrt_le_left (by norm_num)]
    calc d ≤ u ^ 2 * 17 := hd
      _ ≤ (3 / 1000) ^ 2 * 17 := by gcongr
      _ ≤ (3 / 1000 * (42 / 10)) ^ 2 := by norm_num
  have e1 := abs_relWeight_levelLift_sub_le 1 (1 / 10) A Mu (gateRot spinY θ *ᵥ ψ₀)
  have e1' := sum_abs_norm_sq_sub_le Mu (gateRot spinY θ *ᵥ ψ₀)
  rw [hMu, hrot, hsqrt4] at e1'
  have s1 := hbound _ h1
  have e2 := relWeight_levelLift_gateRot_spinY 1 (1 / 10) θ A ψ₀
  have e3 := abs_relWeight_levelLift_sub_le 1 (1 / 10) A ψ₀ ψu
  have e3' := sum_abs_norm_sq_sub_le ψ₀ ψu
  rw [hψ₀, hψu, hsqrt4] at e3'
  have s2 := hbound _ h2
  have hnear : (1 - 22 / 1000) * (1 - 11 / 1000) ≤ relWeight 1 (1 / 10) A (levelLift 0 ψu) :=
    aEncounter_near hL (s := s₀ + u) (by linarith) (by linarith)
      (by rw [abs_le]; constructor <;> linarith)
  rw [hAtot, one_mul] at e1 e3
  have a1 := (abs_le.1 e1).1
  have a3 := (abs_le.1 e3).1
  have hsum1 := e1'.trans (mul_le_mul_of_nonneg_left s1 (by norm_num))
  have hsum3 := e3'.trans (mul_le_mul_of_nonneg_left s2 (by norm_num))
  rw [aRelayRaw, hA]
  exact le_max_of_le_left (by linarith)

/-- ★★ **The pulse completes**: `3·10⁻³` after the crossing the register has passed `relayHi`. -/
theorem aRelayReg_after_pulse {s₀ : ℝ} (hs₀ : s₀ ∈ Icc (aRelayTk - 8 * 10 ^ 11) aRelayTk)
    (hfree : aRelayFlow s₀ (aRelayPrep L) = (aRelayState s₀, relayLo)) :
    relayHi ≤ (aRelayFlow (s₀ + 3 / 1000) (aRelayPrep L)).2 := by
  have hgrp : aRelayFlow (s₀ + 3 / 1000) (aRelayPrep L)
      = aRelayFlow (3 / 1000) (aRelayFlow s₀ (aRelayPrep L)) := gatedFlow_add _ _ _ _
  have hreg : (aRelayFlow (3 / 1000) (aRelayFlow s₀ (aRelayPrep L))).2
      = (aRelayFlow s₀ (aRelayPrep L)).2 + ∫ s in (0 : ℝ)..3 / 1000,
          aRelayWeight (aRelayFlow s (aRelayFlow s₀ (aRelayPrep L))).1 :=
    register_gatedFlow aRelayLipschitz continuous_aRelayWeight _ _
  have hy2 : (aRelayFlow s₀ (aRelayPrep L)).2 = relayLo := by rw [hfree]
  have hint := le_integral_of_ge_on
    (F := fun s => aRelayWeight (aRelayFlow s (aRelayFlow s₀ (aRelayPrep L))).1)
    (continuous_aRelayWeight.comp (continuous_fst.comp (continuous_gatedFlow_time _ _)))
    (κ := 2 / 5) (tn := 0) (te := 3 / 1000) (t := 3 / 1000) le_rfl (by norm_num) le_rfl
    (fun s _ => aRelayWeight_nonneg _) fun s hs1 hs2 => by
      have e : aRelayFlow s (aRelayFlow s₀ (aRelayPrep L)) = aRelayFlow (s₀ + s) (aRelayPrep L) :=
        (gatedFlow_add _ _ _ _).symm
      rw [e, aRelayWeight_aRelayFlow hL]
      exact aRelayRaw_aRelayFlow_ge hL hs₀ hfree hs1 hs2
  rw [hgrp, hreg, hy2]
  unfold relayLo relayHi at *
  linarith

/-- ★★★ **The messenger is flipped**: `3·10⁻³` after the crossing it is within `√(1.53·10⁻⁴)` of
`−i σ_y ψ(s₀)`. -/
theorem sqNorm_mess_aFlip_le {s₀ : ℝ} (hs₀ : s₀ ∈ Icc (aRelayTk - 8 * 10 ^ 11) aRelayTk)
    (hfree : aRelayFlow s₀ (aRelayPrep L) = (aRelayState s₀, relayLo)) :
    sqNorm (mess (aRelayFlow (s₀ + 3 / 1000) (aRelayPrep L)).1
        - (-I) • (spinY *ᵥ bMess s₀))
      ≤ (3 / 1000) ^ 2 * 17 := by
  have h := sqNorm_mess_aRelayFlow_sub_le hL hfree (u := 3 / 1000) (by norm_num)
  have hint : (∫ s in (0 : ℝ)..3 / 1000, relayGate relayLo relayHi aRelayWeight
      (aRelayFlow (s₀ + s) (aRelayPrep L)).1 (aRelayFlow (s₀ + s) (aRelayPrep L)).2)
      = Real.pi / 2 := by
    simp only [aRelayFlow]
    rw [integral_relayGate_eq aRelayLipschitz continuous_aRelayWeight (aRelayPrep L) s₀
      (3 / 1000)]
    change pulseStep relayLo relayHi (aRelayFlow (s₀ + 3 / 1000) (aRelayPrep L)).2
      - pulseStep relayLo relayHi (aRelayFlow s₀ (aRelayPrep L)).2 = Real.pi / 2
    rw [pulseStep_eq_of_ge relayLo_lt_relayHi (aRelayReg_after_pulse hL hs₀ hfree), hfree,
      pulseStep_eq_zero_of_le relayLo_lt_relayHi le_rfl, sub_zero]
  rw [hint, gateRot_pi_div_two_mulVec] at h
  exact h

/-- ★★★ **After the pulse the messenger runs back from `A` toward `B`**: for every
`t ≥ s₀ + 3·10⁻³` it is within `√(1.53·10⁻⁴)` of `−i σ_y ψ_free(2 s₀ + 3·10⁻³ − 3·10¹³ − t)`, the
band-flipped free messenger run backward. -/
theorem sqNorm_mess_aReturn_le {s₀ : ℝ} (hs₀ : s₀ ∈ Icc (aRelayTk - 8 * 10 ^ 11) aRelayTk)
    (hfree : aRelayFlow s₀ (aRelayPrep L) = (aRelayState s₀, relayLo)) {t : ℝ}
    (ht : s₀ + 3 / 1000 ≤ t) :
    sqNorm (mess (aRelayFlow t (aRelayPrep L)).1
        - (-I) • (spinY *ᵥ ringPacket (L := L) 1 0 (2 * Real.pi * 10 ^ 13) bMessWin twinAmp
          (2 * s₀ + 3 / 1000 - 3 * 10 ^ 13 - t)))
      ≤ (3 / 1000) ^ 2 * 17 := by
  set D : ℝ → ZMod L × Fin 2 → ℂ := fun u => mess (aRelayFlow u (aRelayPrep L)).1
    - (-I) • (spinY *ᵥ ringPacket (L := L) 1 0 (2 * Real.pi * 10 ^ 13) bMessWin twinAmp
      (2 * s₀ + 3 / 1000 - 3 * 10 ^ 13 - u)) with hDdef
  have hD : ∀ u ∈ Icc (s₀ + 3 / 1000) t,
      HasDerivAt D ((-I) • (diracHam (relayHop L) 0 *ᵥ D u)) u := by
    intro u hu
    have hreg : relayHi ≤ (aRelayFlow u (aRelayPrep L)).2 :=
      (aRelayReg_after_pulse hL hs₀ hfree).trans (aRelayFlow_register_mono hu.1)
    have hc : relayGate relayLo relayHi aRelayWeight (aRelayFlow u (aRelayPrep L)).1
        (aRelayFlow u (aRelayPrep L)).2 = 0 := relayGate_eq_zero_of_ge relayLo_lt_relayHi _ _ hreg
    have h1 := hasDerivAt_gatedFlow_gateBlock aRelayLipschitz (k₀ := 4) (aRelayPrep L) u
    change HasDerivAt (fun u => mess (aRelayFlow u (aRelayPrep L)).1)
      ((-I) • ((diracHam (relayHop L) (aRelayMass 4) + ((relayGate relayLo relayHi aRelayWeight
        (aRelayFlow u (aRelayPrep L)).1 (aRelayFlow u (aRelayPrep L)).2 : ℝ) : ℂ) • spinY)
          *ᵥ mess (aRelayFlow u (aRelayPrep L)).1)) u at h1
    rw [aRelayMass_four, hc, Complex.ofReal_zero, zero_smul, add_zero] at h1
    have hp := (hasDerivAt_packet (L := L) (relayHop L) 0 bMessWin
      (unitAmp L (relayHop L) 0 twinAmp) (2 * s₀ + 3 / 1000 - 3 * 10 ^ 13 - u)).comp_const_sub
      (2 * s₀ + 3 / 1000 - 3 * 10 ^ 13) u
    have h2 := (hasDerivAt_mulVec spinY hp).const_smul (-I)
    have h2' : HasDerivAt
        (fun u => (-I) • (spinY *ᵥ ringPacket (L := L) 1 0 (2 * Real.pi * 10 ^ 13) bMessWin twinAmp
          (2 * s₀ + 3 / 1000 - 3 * 10 ^ 13 - u)))
        ((-I) • (diracHam (relayHop L) 0
          *ᵥ ((-I) • (spinY *ᵥ ringPacket (L := L) 1 0 (2 * Real.pi * 10 ^ 13) bMessWin twinAmp
            (2 * s₀ + 3 / 1000 - 3 * 10 ^ 13 - u))))) u := by
      simp only [ringPacket]
      simp only [relayHop] at h2 ⊢
      refine h2.congr_deriv ?_
      rw [Matrix.mulVec_neg, Matrix.mulVec_smul, spinY_mulVec_diracHam_mulVec, Matrix.mulVec_smul]
      funext i
      simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      ring
    refine (h1.sub h2').congr_deriv ?_
    rw [Matrix.mulVec_sub, smul_sub]
  have h := sqNorm_eq_of_hasDerivAt_Icc (diracHam_isHermitian (relayHop L) 0) ht hD
  have e : D (s₀ + 3 / 1000) = mess (aRelayFlow (s₀ + 3 / 1000) (aRelayPrep L)).1
      - (-I) • (spinY *ᵥ bMess s₀) := by
    simp only [hDdef, bMess]
    congr 4
    ring
  rw [e] at h
  change sqNorm (D t) ≤ _
  rw [h]
  exact sqNorm_mess_aFlip_le hL hs₀ hfree

/-! ### The bundle -/

/-- ★★★ **The relay at rest** (BACKLOG #278, second landing). `A` at rest, `B` approaching at `3/5`,
`B`'s massless messenger sent from `B`'s position at `t = 0` toward `A`, and `A` carrying a relay
register fed by the clipped encounter weight with a gate `c = Φ'(r) · w` pulsing `σ_y` on the
messenger — **one gated flow**, with:

* both devices free for all time, total weight `3`, the saturation invisible along the orbit;
* a crossing time `s₀ ∈ [3·10¹³ − 8·10¹¹, 3·10¹³]` at which `A`'s register reaches `3·10¹¹`, the
  orbit free up to it;
* `3·10⁻³` later the pulse has delivered `π/2`;
* from then on the messenger is within `‖·‖² ≤ 1.53·10⁻⁴` of the band-flipped free messenger run
  backward, `−i σ_y ψ_free(2 s₀ + 3·10⁻³ − 3·10¹³ − t)` — **a massless echo back toward `B`**. -/
theorem dirac_relay_at_rest :
    (∀ s t u : OnticTime, gatedEvolve (aRelayLipschitz (L := L)) t u
      ∘ gatedEvolve aRelayLipschitz s t = gatedEvolve aRelayLipschitz s u)
    ∧ (∀ t, devA (aRelayFlow t (aRelayPrep L)).1 = restObserver t)
    ∧ (∀ t, devB (aRelayFlow t (aRelayPrep L)).1 = approachObserver (t - 5 * 10 ^ 13))
    ∧ (∀ t, sqNorm (aRelayFlow t (aRelayPrep L)).1 = 3)
    ∧ (∀ t, relayGate relayLo relayHi aRelayWeight (aRelayFlow t (aRelayPrep L)).1
        (aRelayFlow t (aRelayPrep L)).2
        = pulseRate relayLo relayHi (aRelayFlow t (aRelayPrep L)).2
          * aRelayRaw (aRelayFlow t (aRelayPrep L)).1)
    ∧ ∃ s₀ ∈ Icc (aRelayTk - 8 * 10 ^ 11) aRelayTk,
        (∀ t ∈ Icc (0 : ℝ) s₀, aRelayFlow t (aRelayPrep L) = (aRelayState t, aRelayReg L t))
        ∧ (aRelayFlow s₀ (aRelayPrep L)).2 = relayLo
        ∧ relayHi ≤ (aRelayFlow (s₀ + 3 / 1000) (aRelayPrep L)).2
        ∧ ∀ t, s₀ + 3 / 1000 ≤ t →
            sqNorm (mess (aRelayFlow t (aRelayPrep L)).1
                - (-I) • (spinY *ᵥ ringPacket (L := L) 1 0 (2 * Real.pi * 10 ^ 13) bMessWin
                  twinAmp (2 * s₀ + 3 / 1000 - 3 * 10 ^ 13 - t)))
              ≤ (3 / 1000) ^ 2 * 17 := by
  refine ⟨gatedEvolve_comp _, devA_aRelayFlow, devB_aRelayFlow, sqNorm_aRelayFlow hL,
    fun t => ?_, ?_⟩
  · rw [relayGate, aRelayWeight_aRelayFlow hL]
  · obtain ⟨s₀, hs₀, h₀⟩ := exists_aRelayCross hL
    have htk : aRelayTk = 3 * 10 ^ 13 := rfl
    have hs₀0 : 0 ≤ s₀ := by linarith [hs₀.1]
    have hfreeOn := aRelayFlow_eq_free hL h₀.le
    have hfree : aRelayFlow s₀ (aRelayPrep L) = (aRelayState s₀, relayLo) := by
      rw [hfreeOn s₀ ⟨hs₀0, le_rfl⟩, h₀]
    refine ⟨s₀, hs₀, hfreeOn, by rw [hfree], aRelayReg_after_pulse hL hs₀ hfree,
      fun t ht => sqNorm_mess_aReturn_le hL hs₀ hfree ht⟩

end WithL

end CSD.RecordLayer

end
