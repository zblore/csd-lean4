/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.GatePulse
public import CsdLean4.RecordLayer.DiracDoppler

/-!
# The relay arena: a messenger returned by a moving observer

**Category:** 7-SigmaLayer (the record layer). BACKLOG #274, third landing (the relay arena; the
records and the two-way factor are the fourth).

#256's arena — `A` at rest, `B` approaching at `3/5`, a messenger launched from `A` at `4/5` — with
one addition: `B` carries a **relay register** fed by its encounter weight with the messenger, and
the register drives a gate that pulses `σ_y` on the messenger (`GatePulse`). The whole is **one
gated flow** (`GatedFlow`): an autonomous Lipschitz field, hence the two-time law an
`ActualOccurrence` needs. When the messenger reaches `B` the register climbs, the gate delivers
exactly `π/2`, and the messenger is flipped into the lower band at the same momentum: it runs
**backward along its own path**, from `B`'s position back to `A` at `4/5` — a radar echo returned by
a moving observer.

## Lipschitz plumbing (generic)

* `lipschitzWith_mul_of_bounded` (bounded Lipschitz functions multiply), `gateCut` (the radial
  cutoff, `1` up to `R − 1`, `0` from `R`), `satCut` (saturation: `f · χ_R(‖x‖)`),
  ★ `lipschitzWith_satCut` — **a function Lipschitz and bounded on a ball becomes globally Lipschitz
  when saturated**, `satCut_eq_of_le` (and is untouched on the ball of radius `R − 1`).

## The pulse shape (generic)

* `hat` (the hat on `[a, b]`), `hatMass`, `pulseStep` (`Φ(r) = (π/2) ∫_a^r hat / ∫_a^b hat`: `0` up
  to `a`, `π/2` from `b`), `pulseRate` (`Φ'`), `hasDerivAt_pulseStep`, `lipschitzWith_pulseRate`,
  `pulseStep_eq_zero_of_le`, `pulseStep_eq_of_ge`.

## The relay gate (generic)

* `relayGate` (`c(Ψ, r) = Φ'(r) · w(Ψ)`), ★★ `exists_lipschitzWith_relayField` — **the relay field
  is globally Lipschitz** for a Lipschitz, bounded, saturated weight; `integral_relayGate_eq` (the
  gate integrates to `Φ(r(s₀ + T)) − Φ(r(s₀))` along any orbit); `gatedFlow_eq_of_hasDerivAt_Icc`
  (uniqueness on an interval); `sqNorm_eq_of_hasDerivAt_Icc` (a free curve keeps its norm).

## Blocks (generic)

* `blockOf`, `blockDiagonal_mulVec_block`, `isHermitian_blockDiagonal`, `gateBlock` (`V₀` on block
  `k₀`, `0` elsewhere), `sqNorm_eq_sum_blocks`; `hasDerivAt_gatedFlow_block`,
  `hasDerivAt_gatedFlow_gateBlock`; ★★ `gatedFlow_block_eq` — **a block the gate does not touch
  evolves freely for all time**; ★★ `sqNorm_gateBlock_sub_gateRot_le` — **the pulse bound on the
  gated block from any start time**.

## The Dirac chain

* `diracHam_mulVec_packet`, ★ `sqNorm_diracHam_mulVec_packet_le` (**the energy bound**
  `‖Hψ‖² ≤ E²‖ψ‖²` over the window), `bandE_sq_le_scaled`;
* ★ `siteWeight_gateRot_spinY`, ★ `relWeight_levelLift_gateRot_spinY` — **the encounter register
  is blind to every gate rotation** `e^{−iθσ_y}`, not only to the completed flip;
* `abs_relWeight_levelLift_sub_le`, `sum_abs_norm_sq_sub_le` — **the encounter weight moves by at
  most `√(2‖ψ‖² + 2‖χ‖²) · ‖ψ − χ‖`** in the messenger; `devRegionWeight_univ_eq`,
  `hasDerivAt_devicePacket_level`.

## The arena

* `relayHop`, `relayMass` (five blocks: `A`'s levels, `B`'s levels, the messenger), `RelayIdx`,
  `relayHam`, `relayGateMat` (`σ_y` on block `4`), `devA`, `devB`, `mess`, `relayBlock`,
  `relayState` (the free trajectory), `hasDerivAt_relayState_block`, `hasDerivAt_relayState`;
* `relayRaw` (the clipped encounter weight `max (relWeight − 1/2) 0`), `relayWeight` (saturated),
  `contDiff_relWeight_devB_mess`, ★ `exists_lipschitzWith_relayWeight`; `relayLo = 3·10¹¹`,
  `relayHi = relayLo + 1.2·10⁻³`; ★★ `relayLipschitz`, ★★ `relayFlow`, `relayPrep`;
* ★★ `relayFlow_block_free`, `devA_relayFlow`, `devB_relayFlow` — **the devices run free for all
  time**; ★ `sqNorm_relayFlow` (weight `3` conserved), ★ `relayWeight_relayFlow` (**the saturation is
  invisible along the orbit**), `sqNorm_mess_relayFlow`;
* the free register `relayRate`, `relayReg`: `relayRate_eq_zero` (far), `relayRate_le_half`,
  `relayRate_ge` (near, `≥ 0.988² − 1/2`), `relayReg_start_le` (`≤ 2.9·10¹¹` at `t_k − 4.28·10¹¹`),
  `relayReg_end_ge` (`≥ 4·10¹¹` at `t_k + 4.28·10¹¹`), ★★ `exists_relayCross`;
* ★★ `relayFlow_eq_free` — **up to the crossing the orbit is the free trajectory**;
  `sqNorm_mess_relayFlow_sub_le`, ★★ `relayRaw_relayFlow_ge` (**the rate stays above `2/5` through
  the pulse**: blindness plus two drifts of at most `0.0153`), ★★ `relayReg_after_pulse` (**the pulse
  completes in `3·10⁻³`**), ★★★ `sqNorm_mess_flip_le`, ★★★ `sqNorm_mess_return_le` (**after the
  pulse the messenger is `−i σ_y ψ_free(2 s₀ + 3·10⁻³ − t)` up to `‖·‖² ≤ 2.34·10⁻⁴`**);
* ★★★ `dirac_relay` — the bundle.

## Findings

* **A relay need not know the register's value.** `#256`'s register carries a slack of order
  `10¹¹` from the packets' tails; the gate's own register is fed by the encounter weight clipped at
  `1/2`, so it is exactly zero until the encounter and crosses its threshold inside the sure window.
* **Blindness is what makes the pulse self-consistent**: the register's rate during the pulse is
  the free rate up to `4 u √26`, because site densities do not see `e^{−iθσ_y}` for any `θ`.
* **The pulse error is set by the energy, not by `‖H‖`**: `T‖HΨ₀‖ ≤ 0.003 · √26`.

## Honest scope

⚠️ **The messenger is flipped, not a packet carried by `B`.** A packet co-moving with `B` would, once
flipped, move away from `A` in #256's approach geometry; the relay returns the incoming messenger
itself, at its own speed `4/5`. The return is a radar echo from a moving observer.

⚠️ **The flip is approximate**: the returned messenger is within `‖·‖² ≤ 2.34·10⁻⁴` of the band flip
of its free past. The crossing time `s₀` is known only within `±4.28·10¹¹` of `t_k` — the window of
#256's reception record.

⚠️ **Nothing is a record here.** Emission, the relay's firing (reception), the return at `A`, and
the two-way factor read off `A`'s clock are the fourth landing.

References: `specs/BACKLOG.md` #274, #256, #270, #39; `RecordLayer/GatedFlow.lean`
(`gatedFlow`, `exists_lipschitzWith_gatedField`, `register_gatedFlow`);
`RecordLayer/GatePulse.lean` (`sqNorm_sub_gateRot_le`, `integral_gate_eq`, `spinY`,
`chainProp_spinY_packet`); `RecordLayer/DiracDoppler.lean` (`approachObserver`,
`reception_near`, `reception_far`, `approach_total`); `RecordLayer/DiracReturn.lean`
(`imagePacket`, `imageWin`, `image_spread`); `RecordLayer/DiracObservers.lean` (`relWeight`,
`le_integral_of_ge_on`); `CV/DiracPacketLimit.lean` (`chainInner_packet_self`).
-/

@[expose] public section

open Set MeasureTheory Complex CSD.CV
open scoped Matrix NNReal

namespace CSD.RecordLayer

open CSD.SigmaLayer

/-! ### Lipschitz plumbing -/

section Lipschitz

variable {α : Type*} [PseudoMetricSpace α]

/-- **The product of two bounded Lipschitz real functions is Lipschitz.** -/
theorem lipschitzWith_mul_of_bounded {f g : α → ℝ} {Kf Kg Mf Mg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) (hMf : ∀ x, |f x| ≤ Mf)
    (hMg : ∀ x, |g x| ≤ Mg) : LipschitzWith (Mf * Kg + Mg * Kf) fun x => f x * g x := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h1 := hf.dist_le_mul x y
  have h2 := hg.dist_le_mul x y
  rw [Real.dist_eq] at h1 h2 ⊢
  have e : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
  rw [e, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mul]
  calc |f x * (g x - g y) + g y * (f x - f y)|
      ≤ |f x * (g x - g y)| + |g y * (f x - f y)| := abs_add_le _ _
    _ = |f x| * |g x - g y| + |g y| * |f x - f y| := by rw [abs_mul, abs_mul]
    _ ≤ Mf * (Kg * dist x y) + Mg * (Kf * dist x y) :=
        add_le_add (mul_le_mul (hMf x) h2 (abs_nonneg _) (NNReal.coe_nonneg _))
          (mul_le_mul (hMg y) h1 (abs_nonneg _) (NNReal.coe_nonneg _))
    _ = (Mf * Kg + Mg * Kf) * dist x y := by ring

/-- **The radial cutoff** `χ_R(s) = min 1 (max (R − s) 0)`: `1` up to `R − 1`, `0` from `R`. -/
noncomputable def gateCut (R s : ℝ) : ℝ := min 1 (max (R - s) 0)

theorem gateCut_nonneg (R s : ℝ) : 0 ≤ gateCut R s := le_min zero_le_one (le_max_right _ _)

theorem gateCut_le_one (R s : ℝ) : gateCut R s ≤ 1 := min_le_left _ _

theorem gateCut_eq_one {R s : ℝ} (h : s ≤ R - 1) : gateCut R s = 1 :=
  min_eq_left (le_max_of_le_left (by linarith))

theorem gateCut_eq_zero {R s : ℝ} (h : R ≤ s) : gateCut R s = 0 := by
  rw [gateCut, max_eq_right (by linarith), min_eq_right zero_le_one]

theorem lipschitzWith_gateCut (R : ℝ) : LipschitzWith 1 (gateCut R) := by
  have h1 : LipschitzWith 1 fun s : ℝ => R - s :=
    ((LipschitzWith.const R).sub LipschitzWith.id).weaken (le_of_eq (zero_add _))
  exact ((LipschitzWith.const (1 : ℝ)).min (h1.max_const 0)).weaken (max_le zero_le_one le_rfl)

variable {E : Type*} [NormedAddCommGroup E]

/-- **The saturated function** `f · χ_R(‖x‖)`: `f` up to radius `R − 1`, `0` from radius `R`. -/
noncomputable def satCut (R : ℝ) (f : E → ℝ) (x : E) : ℝ := f x * gateCut R ‖x‖

theorem satCut_eq_of_le {R : ℝ} (f : E → ℝ) {x : E} (h : ‖x‖ ≤ R - 1) : satCut R f x = f x := by
  rw [satCut, gateCut_eq_one h, mul_one]

theorem satCut_eq_zero {R : ℝ} (f : E → ℝ) {x : E} (h : R ≤ ‖x‖) : satCut R f x = 0 := by
  rw [satCut, gateCut_eq_zero h, mul_zero]

theorem satCut_nonneg {R : ℝ} {f : E → ℝ} (hf : ∀ x, 0 ≤ f x) (x : E) : 0 ≤ satCut R f x :=
  mul_nonneg (hf x) (gateCut_nonneg _ _)

theorem abs_satCut_le {R : ℝ} {f : E → ℝ} {M : ℝ≥0} (hM : ∀ x : E, ‖x‖ ≤ R → |f x| ≤ M) (x : E) :
    |satCut R f x| ≤ M := by
  by_cases hx : ‖x‖ ≤ R
  · rw [satCut, abs_mul, abs_of_nonneg (gateCut_nonneg _ _)]
    calc |f x| * gateCut R ‖x‖ ≤ M * 1 :=
          mul_le_mul (hM x hx) (gateCut_le_one _ _) (gateCut_nonneg _ _) (NNReal.coe_nonneg _)
      _ = M := mul_one _
  · rw [satCut_eq_zero f (not_le.1 hx).le, abs_zero]
    exact NNReal.coe_nonneg _

theorem abs_gateCut_sub_gateCut_le (R : ℝ) (u v : E) :
    |gateCut R ‖u‖ - gateCut R ‖v‖| ≤ ‖u - v‖ := by
  have h := (lipschitzWith_gateCut R).dist_le_mul ‖u‖ ‖v‖
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at h
  exact h.trans (abs_norm_sub_norm_le u v)

/-- ★ **Saturation makes a locally Lipschitz function globally Lipschitz**: if `f` is Lipschitz and
bounded on the closed ball of radius `R`, then `f · χ_R(‖x‖)` is Lipschitz on all of `E`. -/
theorem lipschitzWith_satCut {R : ℝ} {f : E → ℝ} {K M : ℝ≥0}
    (hf : LipschitzOnWith K f (Metric.closedBall 0 R)) (hM : ∀ x : E, ‖x‖ ≤ R → |f x| ≤ M) :
    LipschitzWith (K + M) (satCut R f) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_add]
  have hin : ∀ u v : E, ‖u‖ ≤ R → R < ‖v‖ → |satCut R f u - satCut R f v| ≤ M * ‖u - v‖ := by
    intro u v hu hv
    rw [satCut_eq_zero f hv.le, sub_zero, satCut, abs_mul, abs_of_nonneg (gateCut_nonneg _ _)]
    have e : gateCut R ‖u‖ = |gateCut R ‖u‖ - gateCut R ‖v‖| := by
      rw [gateCut_eq_zero hv.le, sub_zero, abs_of_nonneg (gateCut_nonneg _ _)]
    rw [e]
    exact mul_le_mul (hM u hu) (abs_gateCut_sub_gateCut_le R u v) (abs_nonneg _)
      (NNReal.coe_nonneg _)
  have hKM : (M : ℝ) * ‖x - y‖ ≤ (K + M) * ‖x - y‖ := by
    have := NNReal.coe_nonneg K
    nlinarith [norm_nonneg (x - y)]
  by_cases hx : ‖x‖ ≤ R
  · by_cases hy : ‖y‖ ≤ R
    · have hK := hf.dist_le_mul x (mem_closedBall_zero_iff.2 hx) y (mem_closedBall_zero_iff.2 hy)
      rw [Real.dist_eq, dist_eq_norm] at hK
      have e : satCut R f x - satCut R f y
          = (f x - f y) * gateCut R ‖y‖ + f x * (gateCut R ‖x‖ - gateCut R ‖y‖) := by
        simp only [satCut]
        ring
      rw [e]
      calc |(f x - f y) * gateCut R ‖y‖ + f x * (gateCut R ‖x‖ - gateCut R ‖y‖)|
          ≤ |(f x - f y) * gateCut R ‖y‖| + |f x * (gateCut R ‖x‖ - gateCut R ‖y‖)| :=
            abs_add_le _ _
        _ = |f x - f y| * gateCut R ‖y‖ + |f x| * |gateCut R ‖x‖ - gateCut R ‖y‖| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (gateCut_nonneg _ _)]
        _ ≤ (K * ‖x - y‖) * 1 + M * ‖x - y‖ :=
            add_le_add (mul_le_mul hK (gateCut_le_one _ _) (gateCut_nonneg _ _) (by positivity))
              (mul_le_mul (hM x hx) (abs_gateCut_sub_gateCut_le R x y) (abs_nonneg _)
                (NNReal.coe_nonneg _))
        _ = (K + M) * ‖x - y‖ := by ring
    · exact (hin x y hx (not_le.1 hy)).trans hKM
  · by_cases hy : ‖y‖ ≤ R
    · have h := hin y x hy (not_le.1 hx)
      rw [abs_sub_comm, norm_sub_rev] at h
      exact h.trans hKM
    · rw [satCut_eq_zero f (not_le.1 hx).le, satCut_eq_zero f (not_le.1 hy).le, sub_zero, abs_zero]
      positivity

end Lipschitz

/-! ### The pulse shape -/

section Pulse

/-- **The hat** on `[a, b]`: `1` at the middle, `0` outside, linear between. -/
noncomputable def hat (a b r : ℝ) : ℝ := max (1 - |r - (a + b) / 2| / ((b - a) / 2)) 0

theorem hat_nonneg (a b r : ℝ) : 0 ≤ hat a b r := le_max_right _ _

theorem hat_le_one {a b : ℝ} (hab : a < b) (r : ℝ) : hat a b r ≤ 1 := by
  have : 0 ≤ |r - (a + b) / 2| / ((b - a) / 2) := div_nonneg (abs_nonneg _) (by linarith)
  exact max_le (by linarith) zero_le_one

theorem hat_eq_zero_of_le {a b r : ℝ} (hab : a < b) (h : r ≤ a) : hat a b r = 0 := by
  rw [hat, max_eq_right]
  rw [sub_nonpos, le_div_iff₀ (by linarith), one_mul, abs_of_nonpos (by linarith)]
  linarith

theorem hat_eq_zero_of_ge {a b r : ℝ} (hab : a < b) (h : b ≤ r) : hat a b r = 0 := by
  rw [hat, max_eq_right]
  rw [sub_nonpos, le_div_iff₀ (by linarith), one_mul, abs_of_nonneg (by linarith)]
  linarith

theorem continuous_hat (a b : ℝ) : Continuous (hat a b) := by
  unfold hat
  fun_prop

/-- The hat is `2/(b − a)`-Lipschitz. -/
theorem lipschitzWith_hat {a b : ℝ} (hab : a < b) :
    LipschitzWith ⟨2 / (b - a), (div_pos two_pos (by linarith)).le⟩ (hat a b) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  show |hat a b x - hat a b y| ≤ 2 / (b - a) * |x - y|
  have hw : 0 < (b - a) / 2 := by linarith
  calc |hat a b x - hat a b y|
      ≤ |(1 - |x - (a + b) / 2| / ((b - a) / 2)) - (1 - |y - (a + b) / 2| / ((b - a) / 2))| :=
        abs_max_sub_max_le_abs _ _ _
    _ = |(|y - (a + b) / 2| - |x - (a + b) / 2|) / ((b - a) / 2)| := by
        congr 1
        ring
    _ = |(|y - (a + b) / 2| - |x - (a + b) / 2|)| / ((b - a) / 2) := by
        rw [abs_div, abs_of_pos hw]
    _ ≤ |y - x| / ((b - a) / 2) := by
        refine div_le_div_of_nonneg_right ?_ hw.le
        have := abs_abs_sub_abs_le_abs_sub (y - (a + b) / 2) (x - (a + b) / 2)
        rwa [sub_sub_sub_cancel_right] at this
    _ = 2 / (b - a) * |x - y| := by
        rw [abs_sub_comm y x]
        field_simp

/-- The hat's integral over `[a, b]`. -/
noncomputable def hatMass (a b : ℝ) : ℝ := ∫ s in a..b, hat a b s

theorem hatMass_pos {a b : ℝ} (hab : a < b) : 0 < hatMass a b := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_hat a b).intervalIntegrable _ _) (fun x hx => ?_) hab
  refine lt_max_of_lt_left ?_
  rw [sub_pos, div_lt_one (by linarith), abs_lt]
  constructor <;> linarith [hx.1, hx.2]

/-- **The pulse step** `Φ(r) = (π/2) ∫_a^r hat / ∫_a^b hat`: `0` up to `a`, `π/2` from `b`. -/
noncomputable def pulseStep (a b r : ℝ) : ℝ := Real.pi / 2 * (∫ s in a..r, hat a b s) / hatMass a b

/-- **Its rate** `Φ'(r) = (π/2) hat(r) / ∫_a^b hat`. -/
noncomputable def pulseRate (a b r : ℝ) : ℝ := Real.pi / 2 * hat a b r / hatMass a b

theorem hasDerivAt_pulseStep (a b r : ℝ) : HasDerivAt (pulseStep a b) (pulseRate a b r) r := by
  unfold pulseStep pulseRate
  exact (((continuous_hat a b).integral_hasStrictDerivAt a r).hasDerivAt.const_mul
    (Real.pi / 2)).div_const (hatMass a b)

theorem continuous_pulseRate (a b : ℝ) : Continuous (pulseRate a b) := by
  unfold pulseRate
  exact (continuous_const.mul (continuous_hat a b)).div_const _

theorem pulseRate_nonneg {a b : ℝ} (hab : a < b) (r : ℝ) : 0 ≤ pulseRate a b r :=
  div_nonneg (mul_nonneg (by positivity) (hat_nonneg _ _ _)) (hatMass_pos hab).le

theorem pulseRate_eq_zero_of_le {a b r : ℝ} (hab : a < b) (h : r ≤ a) : pulseRate a b r = 0 := by
  rw [pulseRate, hat_eq_zero_of_le hab h, mul_zero, zero_div]

theorem pulseRate_eq_zero_of_ge {a b r : ℝ} (hab : a < b) (h : b ≤ r) : pulseRate a b r = 0 := by
  rw [pulseRate, hat_eq_zero_of_ge hab h, mul_zero, zero_div]

theorem pulseRate_le {a b : ℝ} (hab : a < b) (r : ℝ) :
    pulseRate a b r ≤ Real.pi / 2 / hatMass a b := by
  rw [pulseRate]
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_right (by positivity) (hat_le_one hab r)) (hatMass_pos hab).le

theorem lipschitzWith_pulseRate {a b : ℝ} (hab : a < b) :
    ∃ K : ℝ≥0, LipschitzWith K (pulseRate a b) := by
  have hM := hatMass_pos hab
  have hc0 : 0 ≤ Real.pi / 2 / hatMass a b := (div_pos (by positivity) hM).le
  have hc : 0 ≤ Real.pi / 2 / hatMass a b * (2 / (b - a)) :=
    mul_nonneg hc0 (div_pos two_pos (by linarith)).le
  refine ⟨⟨_, hc⟩, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have h : |hat a b x - hat a b y| ≤ 2 / (b - a) * |x - y| := (lipschitzWith_hat hab).dist_le_mul x y
  show |pulseRate a b x - pulseRate a b y| ≤ Real.pi / 2 / hatMass a b * (2 / (b - a)) * |x - y|
  have e : pulseRate a b x - pulseRate a b y
      = Real.pi / 2 / hatMass a b * (hat a b x - hat a b y) := by
    simp only [pulseRate]
    field_simp
  rw [e, abs_mul, abs_of_nonneg hc0, mul_assoc]
  exact mul_le_mul_of_nonneg_left h hc0

theorem pulseStep_eq_zero_of_le {a b r : ℝ} (hab : a < b) (h : r ≤ a) : pulseStep a b r = 0 := by
  have : ∫ s in a..r, hat a b s = ∫ s in a..r, (0 : ℝ) :=
    intervalIntegral.integral_congr fun s hs => by
      rw [mem_uIcc] at hs
      exact hat_eq_zero_of_le hab (by rcases hs with hs | hs <;> linarith)
  rw [pulseStep, this, intervalIntegral.integral_zero, mul_zero, zero_div]

theorem pulseStep_eq_of_ge {a b r : ℝ} (hab : a < b) (h : b ≤ r) : pulseStep a b r = Real.pi / 2 := by
  have h0 : ∫ s in b..r, hat a b s = ∫ s in b..r, (0 : ℝ) :=
    intervalIntegral.integral_congr fun s hs => by
      rw [mem_uIcc] at hs
      exact hat_eq_zero_of_ge hab (by rcases hs with hs | hs <;> linarith)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((continuous_hat a b).intervalIntegrable a b) ((continuous_hat a b).intervalIntegrable b r)
  rw [h0, intervalIntegral.integral_zero, add_zero] at hsplit
  rw [pulseStep, ← hsplit]
  exact mul_div_cancel_right₀ _ (hatMass_pos hab).ne'

end Pulse

/-! ### The relay gate -/

section Gate

variable {ι : Type*} [Fintype ι]

/-- **The relay gate** `c(Ψ, r) = Φ'(r) · w(Ψ)`: the pulse rate at the register, times the weight. -/
noncomputable def relayGate (a b : ℝ) (w : (ι → ℂ) → ℝ) (Ψ : ι → ℂ) (r : ℝ) : ℝ :=
  pulseRate a b r * w Ψ

omit [Fintype ι] in
theorem relayGate_eq_zero_of_le {a b : ℝ} (hab : a < b) (w : (ι → ℂ) → ℝ) (Ψ : ι → ℂ) {r : ℝ}
    (h : r ≤ a) : relayGate a b w Ψ r = 0 := by
  rw [relayGate, pulseRate_eq_zero_of_le hab h, zero_mul]

omit [Fintype ι] in
theorem relayGate_eq_zero_of_ge {a b : ℝ} (hab : a < b) (w : (ι → ℂ) → ℝ) (Ψ : ι → ℂ) {r : ℝ}
    (h : b ≤ r) : relayGate a b w Ψ r = 0 := by
  rw [relayGate, pulseRate_eq_zero_of_ge hab h, zero_mul]

omit [Fintype ι] in
theorem relayGate_eq_zero_of_weight (a b : ℝ) {w : (ι → ℂ) → ℝ} {Ψ : ι → ℂ} (h : w Ψ = 0) (r : ℝ) :
    relayGate a b w Ψ r = 0 := by
  rw [relayGate, h, mul_zero]

omit [Fintype ι] in
theorem abs_relayGate_le {a b : ℝ} (hab : a < b) {w : (ι → ℂ) → ℝ} {Mw : ℝ≥0}
    (hMw : ∀ Ψ, |w Ψ| ≤ Mw) (x : GateArena ι) :
    |relayGate a b w x.1 x.2| ≤ Real.pi / 2 / hatMass a b * Mw := by
  rw [relayGate, abs_mul, abs_of_nonneg (pulseRate_nonneg hab _)]
  exact mul_le_mul (pulseRate_le hab _) (hMw _) (abs_nonneg _)
    (div_pos (by positivity) (hatMass_pos hab)).le

theorem exists_lipschitzWith_relayGate {a b : ℝ} (hab : a < b) {w : (ι → ℂ) → ℝ} {Kw Mw : ℝ≥0}
    (hw : LipschitzWith Kw w) (hMw : ∀ Ψ, |w Ψ| ≤ Mw) :
    ∃ K : ℝ≥0, LipschitzWith K fun x : GateArena ι => relayGate a b w x.1 x.2 := by
  obtain ⟨Kp, hKp⟩ := lipschitzWith_pulseRate hab
  have hp0 : 0 ≤ Real.pi / 2 / hatMass a b := (div_pos (by positivity) (hatMass_pos hab)).le
  have hMp : ∀ x : GateArena ι,
      |pulseRate a b x.2| ≤ (Real.toNNReal (Real.pi / 2 / hatMass a b) : ℝ) := fun x => by
    rw [abs_of_nonneg (pulseRate_nonneg hab _), Real.coe_toNNReal _ hp0]
    exact pulseRate_le hab _
  exact ⟨_, lipschitzWith_mul_of_bounded (hKp.comp LipschitzWith.prod_snd)
    (hw.comp LipschitzWith.prod_fst) hMp fun x => hMw x.1⟩

/-- ★★ **The relay field is globally Lipschitz** for a Lipschitz, bounded weight closed beyond
`R`: the gated flow exists. -/
theorem exists_lipschitzWith_relayField (H₀ V : Matrix ι ι ℂ) {a b : ℝ} (hab : a < b)
    {w : (ι → ℂ) → ℝ} {Kw Mw : ℝ≥0} {R : ℝ} (hw : LipschitzWith Kw w) (hMw : ∀ Ψ, |w Ψ| ≤ Mw)
    (hR : 0 ≤ R) (hw0 : ∀ Ψ : ι → ℂ, R ≤ ‖Ψ‖ → w Ψ = 0) :
    ∃ K : ℝ≥0, LipschitzWith K (gatedField H₀ V (relayGate a b w) w) := by
  obtain ⟨Kc, hKc⟩ := exists_lipschitzWith_relayGate hab hw hMw
  exact exists_lipschitzWith_gatedField H₀ V hKc
    (mul_nonneg (div_pos (by positivity) (hatMass_pos hab)).le (NNReal.coe_nonneg _))
    (abs_relayGate_le hab hMw) hR (fun Ψ r h => relayGate_eq_zero_of_weight a b (hw0 Ψ h) r) hw

/-- **The accumulated gate along an orbit is the step of the register**: from `s₀` to `s₀ + T`,
`∫ c = Φ(r(s₀ + T)) − Φ(r(s₀))`. -/
theorem integral_relayGate_eq {H₀ V : Matrix ι ι ℂ} {a b : ℝ} {w : (ι → ℂ) → ℝ}
    (hL : ∃ K : ℝ≥0, LipschitzWith K (gatedField H₀ V (relayGate a b w) w)) (hw : Continuous w)
    (x : GateArena ι) (s₀ T : ℝ) :
    ∫ s in (0 : ℝ)..T,
        relayGate a b w (gatedFlow hL (s₀ + s) x).1 (gatedFlow hL (s₀ + s) x).2
      = pulseStep a b (gatedFlow hL (s₀ + T) x).2 - pulseStep a b (gatedFlow hL s₀ x).2 := by
  have hcont : Continuous fun s : ℝ =>
      pulseRate a b (gatedFlow hL (s₀ + s) x).2 * w (gatedFlow hL (s₀ + s) x).1 := by
    have hφ : Continuous fun s : ℝ => gatedFlow hL (s₀ + s) x :=
      (continuous_gatedFlow_time hL x).comp (continuous_const.add continuous_id)
    exact ((continuous_pulseRate a b).comp (continuous_snd.comp hφ)).mul
      (hw.comp (continuous_fst.comp hφ))
  have h := integral_gate_eq (Φ := pulseStep a b) (φ := pulseRate a b) (hasDerivAt_pulseStep a b)
    (r := fun s => (gatedFlow hL (s₀ + s) x).2) (w := fun s => w (gatedFlow hL (s₀ + s) x).1)
    (fun s => (hasDerivAt_gatedFlow_snd hL x (s₀ + s)).comp_const_add s₀ s) hcont T
  simpa only [add_zero, relayGate] using h

/-- **Uniqueness on an interval**: a curve solving the gated equation on `[0, T]` from `x` is the
orbit there. -/
theorem gatedFlow_eq_of_hasDerivAt_Icc {H₀ V : Matrix ι ι ℂ} {c : (ι → ℂ) → ℝ → ℝ}
    {w : (ι → ℂ) → ℝ} (hL : ∃ K : ℝ≥0, LipschitzWith K (gatedField H₀ V c w)) (x : GateArena ι)
    {y : ℝ → GateArena ι} {T : ℝ}
    (hy : ∀ s ∈ Icc (0 : ℝ) T, HasDerivAt y (gatedField H₀ V c w (y s)) s) (hy0 : y 0 = x) :
    ∀ s ∈ Icc (0 : ℝ) T, gatedFlow hL s x = y s := by
  obtain ⟨K, hK⟩ := id hL
  exact ODE_solution_unique (v := fun _ => gatedField H₀ V c w) (K := K) (a := 0) (b := T)
    (f := fun s => gatedFlow hL s x) (g := y) (fun _ => hK)
    (HasDerivAt.continuousOn fun s _ => hasDerivAt_gatedFlow hL x s)
    (fun s _ => (hasDerivAt_gatedFlow hL x s).hasDerivWithinAt)
    (HasDerivAt.continuousOn hy)
    (fun s hs => (hy s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (by rw [gatedFlow_zero, hy0])

/-- **A free curve keeps its norm on an interval**: `Ψ' = −i H Ψ` on `[a, b]` with `H` Hermitian
gives `‖Ψ(b)‖² = ‖Ψ(a)‖²`. -/
theorem sqNorm_eq_of_hasDerivAt_Icc {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {Ψ : ℝ → ι → ℂ}
    {a b : ℝ} (hab : a ≤ b) (hΨ : ∀ t ∈ Icc a b, HasDerivAt Ψ ((-I) • (H *ᵥ Ψ t)) t) :
    sqNorm (Ψ b) = sqNorm (Ψ a) := by
  set F : ℝ → ℂ := fun t => star (Ψ t) ⬝ᵥ Ψ t with hF
  have hd : ∀ t ∈ Icc a b, HasDerivAt F 0 t := by
    intro t ht
    have h := hasDerivAt_star_dotProduct (hΨ t ht) (hΨ t ht)
    convert h using 1
    rw [star_smul, smul_dotProduct, dotProduct_smul, star_neg, show star I = -I from Complex.conj_I,
      neg_neg, smul_eq_mul, smul_eq_mul, star_mulVec_dotProduct hH]
    ring
  have hc : ContinuousOn F (Icc a b) := HasDerivAt.continuousOn (f' := fun _ => 0) hd
  have h := constant_of_has_deriv_right_zero hc
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt) b ⟨hab, le_rfl⟩
  simp only [hF] at h
  rw [sqNorm_eq_re, sqNorm_eq_re, h]

end Gate

/-! ### Blocks -/

section Blocks

variable {m κ : Type*} [Fintype m] [Fintype κ] [DecidableEq κ]

/-- **Block `k` of a state** on `m × κ`. -/
def blockOf (Ψ : m × κ → ℂ) (k : κ) : m → ℂ := fun q => Ψ (q, k)

theorem blockDiagonal_mulVec_block (M : κ → Matrix m m ℂ) (Ψ : m × κ → ℂ) (q : m) (k : κ) :
    (Matrix.blockDiagonal M *ᵥ Ψ) (q, k) = (M k *ᵥ blockOf Ψ k) q := by
  simp only [Matrix.mulVec, dotProduct, Matrix.blockDiagonal_apply, Fintype.sum_prod_type, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, blockOf]

omit [Fintype m] [Fintype κ] in
theorem isHermitian_blockDiagonal {M : κ → Matrix m m ℂ} (hM : ∀ k, (M k).IsHermitian) :
    (Matrix.blockDiagonal M).IsHermitian := by
  show (Matrix.blockDiagonal M)ᴴ = Matrix.blockDiagonal M
  rw [Matrix.blockDiagonal_conjTranspose]
  congr 1
  funext k
  exact hM k

/-- **The gate matrix on block `k₀`**: `V₀` there, `0` on every other block. -/
def gateBlock (k₀ : κ) (V₀ : Matrix m m ℂ) : Matrix (m × κ) (m × κ) ℂ :=
  Matrix.blockDiagonal fun k => if k = k₀ then V₀ else 0

theorem gateBlock_mulVec_apply_ne (k₀ : κ) (V₀ : Matrix m m ℂ) (Ψ : m × κ → ℂ) (q : m) {k : κ}
    (hk : k ≠ k₀) : (gateBlock k₀ V₀ *ᵥ Ψ) (q, k) = 0 := by
  rw [gateBlock, blockDiagonal_mulVec_block]
  simp [hk]

theorem gateBlock_mulVec_apply_eq (k₀ : κ) (V₀ : Matrix m m ℂ) (Ψ : m × κ → ℂ) (q : m) :
    (gateBlock k₀ V₀ *ᵥ Ψ) (q, k₀) = (V₀ *ᵥ blockOf Ψ k₀) q := by
  rw [gateBlock, blockDiagonal_mulVec_block]
  simp

omit [Fintype m] [Fintype κ] in
theorem isHermitian_gateBlock (k₀ : κ) {V₀ : Matrix m m ℂ} (hV : V₀.IsHermitian) :
    (gateBlock k₀ V₀).IsHermitian :=
  isHermitian_blockDiagonal fun k => by
    by_cases h : k = k₀ <;> simp [h, hV, Matrix.isHermitian_zero]

omit [DecidableEq κ] in
/-- The squared norm is the sum over the blocks. -/
theorem sqNorm_eq_sum_blocks (Ψ : m × κ → ℂ) : sqNorm Ψ = ∑ k, sqNorm (blockOf Ψ k) := by
  simp only [sqNorm, blockOf, Fintype.sum_prod_type]
  exact Finset.sum_comm

variable {M : κ → Matrix m m ℂ} {k₀ : κ} {V₀ : Matrix m m ℂ} {c : (m × κ → ℂ) → ℝ → ℝ}
  {w : (m × κ → ℂ) → ℝ}
  (hL : ∃ K : ℝ≥0, LipschitzWith K (gatedField (Matrix.blockDiagonal M) (gateBlock k₀ V₀) c w))

/-- **A block the gate does not touch solves its own free equation.** -/
theorem hasDerivAt_gatedFlow_block (x : GateArena (m × κ)) (t : ℝ) {k : κ} (hk : k ≠ k₀) :
    HasDerivAt (fun t => blockOf (gatedFlow hL t x).1 k)
      ((-I) • (M k *ᵥ blockOf (gatedFlow hL t x).1 k)) t := by
  have h := hasDerivAt_gatedFlow_fst hL x t
  rw [hasDerivAt_pi] at h ⊢
  intro q
  refine (h (q, k)).congr_deriv ?_
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply,
    blockDiagonal_mulVec_block, gateBlock_mulVec_apply_ne k₀ V₀ _ q hk, mul_zero, add_zero]

/-- **The gated block solves the pulse equation** with the scalar `c` read off the orbit. -/
theorem hasDerivAt_gatedFlow_gateBlock (x : GateArena (m × κ)) (t : ℝ) :
    HasDerivAt (fun t => blockOf (gatedFlow hL t x).1 k₀)
      ((-I) • ((M k₀ + ((c (gatedFlow hL t x).1 (gatedFlow hL t x).2 : ℝ) : ℂ) • V₀)
        *ᵥ blockOf (gatedFlow hL t x).1 k₀)) t := by
  have h := hasDerivAt_gatedFlow_fst hL x t
  rw [hasDerivAt_pi] at h ⊢
  intro q
  refine (h (q, k₀)).congr_deriv ?_
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply,
    blockDiagonal_mulVec_block, gateBlock_mulVec_apply_eq]

/-- ★★ **An untouched block evolves freely for all time**: it is the free solution from its start,
whatever the gate does elsewhere. -/
theorem gatedFlow_block_eq (x : GateArena (m × κ)) {k : κ} (hk : k ≠ k₀) {γ : ℝ → m → ℂ}
    (hγ : ∀ t, HasDerivAt γ ((-I) • (M k *ᵥ γ t)) t) (hγ0 : γ 0 = blockOf x.1 k) (t : ℝ) :
    blockOf (gatedFlow hL t x).1 k = γ t := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_mulVec ((-I) • M k)
  have hK' : ∀ _ : ℝ, LipschitzOnWith K (fun v : m → ℂ => (-I) • (M k *ᵥ v)) univ := fun _ => by
    simpa only [Matrix.smul_mulVec] using hK.lipschitzOnWith
  have h := ODE_solution_unique_univ (v := fun _ v => (-I) • (M k *ᵥ v)) (s := fun _ => univ)
    (K := K) (t₀ := 0) (f := fun t => blockOf (gatedFlow hL t x).1 k) (g := γ) hK'
    (fun t => ⟨hasDerivAt_gatedFlow_block hL x t hk, trivial⟩) (fun t => ⟨hγ t, trivial⟩)
    (by simp only [gatedFlow_zero, hγ0])
  exact congrFun h t

section PulseBlock

variable [DecidableEq m]

/-- ★★ **The pulse on the gated block**: from any `s₀`, the block stays within
`T ‖M_{k₀} Ψ_{k₀}(s₀)‖` of its rotation by the accumulated gate. -/
theorem sqNorm_gateBlock_sub_gateRot_le (hM : (M k₀).IsHermitian) (hV : V₀.IsHermitian)
    (hVH : ∀ v, V₀ *ᵥ (M k₀ *ᵥ v) = -(M k₀ *ᵥ (V₀ *ᵥ v))) (hV2 : ∀ v, V₀ *ᵥ (V₀ *ᵥ v) = v)
    (hc : Continuous fun x : GateArena (m × κ) => c x.1 x.2) (x : GateArena (m × κ)) (s₀ : ℝ)
    {T : ℝ} (hT : 0 ≤ T) :
    sqNorm (blockOf (gatedFlow hL (s₀ + T) x).1 k₀
        - gateRot V₀ (∫ s in (0 : ℝ)..T,
            c (gatedFlow hL (s₀ + s) x).1 (gatedFlow hL (s₀ + s) x).2)
          *ᵥ blockOf (gatedFlow hL s₀ x).1 k₀)
      ≤ T ^ 2 * sqNorm (M k₀ *ᵥ blockOf (gatedFlow hL s₀ x).1 k₀) := by
  have hcont : Continuous fun s : ℝ =>
      c (gatedFlow hL (s₀ + s) x).1 (gatedFlow hL (s₀ + s) x).2 :=
    hc.comp ((continuous_gatedFlow_time hL x).comp (continuous_const.add continuous_id))
  have h := sqNorm_sub_gateRot_le hM hV hVH hV2 hcont
    (Ψ := fun s => blockOf (gatedFlow hL (s₀ + s) x).1 k₀)
    (fun s => (hasDerivAt_gatedFlow_gateBlock hL x (s₀ + s)).comp_const_add s₀ s) hT
  simpa only [add_zero] using h

end PulseBlock

end Blocks

/-! ### The Dirac chain: energies, the blind register, the drift of the weight -/

section Chain

variable {L : ℕ} [NeZero L]

/-- **`H` on a packet multiplies each amplitude by its energy.** -/
theorem diracHam_mulVec_packet (J μ : ℝ) (W : Finset ℤ) (a : ℤ → ℂ) (t : ℝ) :
    diracHam J μ *ᵥ packet (L := L) J μ W a t
      = packet (L := L) J μ W (fun m => ((bandE J μ (angleZ L m) : ℝ) : ℂ) * a m) t := by
  unfold packet
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.mulVec_smul, diracHam_mulVec_diracMode, dispE_modeS_intCast, smul_smul]
  congr 1
  ring

theorem sqNorm_eq_re_chainInner (ψ : ZMod L × Fin 2 → ℂ) : sqNorm ψ = (chainInner ψ ψ).re :=
  (re_chainInner_self ψ).symm

/-- ★ **The energy bound**: `‖Hψ‖² ≤ E² ‖ψ‖²` for a packet whose window's energies have squares at
most `E²`. -/
theorem sqNorm_diracHam_mulVec_packet_le (J μ : ℝ) {W : Finset ℤ} (hD : Distinct L W) (a : ℤ → ℂ)
    (t : ℝ) {E2 : ℝ} (hE : ∀ m ∈ W, bandE J μ (angleZ L m) ^ 2 ≤ E2) :
    sqNorm (diracHam J μ *ᵥ packet (L := L) J μ W a t)
      ≤ E2 * sqNorm (packet (L := L) J μ W a t) := by
  rw [diracHam_mulVec_packet, sqNorm_eq_re_chainInner, sqNorm_eq_re_chainInner,
    chainInner_packet_self J μ hD, chainInner_packet_self J μ hD, Complex.ofReal_re,
    Complex.ofReal_re, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc, mul_pow, sq_abs]
  exact mul_le_mul_of_nonneg_right (hE m hm) (sq_nonneg _)

/-- The band energy on a scaled ring: `E² ≤ μ² + (|p₀| + D)²` for a mode within `D` of `p₀`. -/
theorem bandE_sq_le_scaled {ℓ : ℝ} (hℓ : 0 < ℓ) (μ : ℝ) {m : ℤ} {p₀ D : ℝ}
    (hm : |2 * Real.pi * m / ℓ - p₀| ≤ D) :
    bandE (scaledHop 1 (ℓ / L)) μ (angleZ L m) ^ 2 ≤ μ ^ 2 + (|p₀| + D) ^ 2 := by
  rw [bandE, dispE_sq]
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have e : 2 * scaledHop 1 (ℓ / L) * angleZ L m = 2 * Real.pi * m / ℓ := by
    rw [scaledHop, angleZ]
    field_simp
  have hs : |2 * scaledHop 1 (ℓ / L) * Real.sin (angleZ L m)| ≤ |p₀| + D := by
    calc |2 * scaledHop 1 (ℓ / L) * Real.sin (angleZ L m)|
        = |2 * scaledHop 1 (ℓ / L)| * |Real.sin (angleZ L m)| := abs_mul _ _
      _ ≤ |2 * scaledHop 1 (ℓ / L)| * |angleZ L m| :=
          mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (abs_nonneg _)
      _ = |2 * Real.pi * m / ℓ| := by rw [← abs_mul, e]
      _ ≤ |p₀| + D := by
          have := abs_sub_abs_le_abs_sub (2 * Real.pi * m / ℓ) p₀
          linarith
  have h2 := sq_le_sq' (by linarith [(abs_le.1 hs).1, abs_nonneg p₀]) (abs_le.1 hs).2
  linarith

/-- ★ **Site densities do not see any gate rotation** `e^{−iθσ_y}`. -/
theorem siteWeight_gateRot_spinY (θ : ℝ) (v : ZMod L × Fin 2 → ℂ) (k : ZMod L) :
    siteWeight (gateRot spinY θ *ᵥ v) k = siteWeight v k := by
  rw [gateRot_mulVec]
  simp only [siteWeight, Fin.sum_univ_two, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [(spinY_mulVec_apply v k).1, (spinY_mulVec_apply v k).2]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im]
  linear_combination ((v (k, 0)).re ^ 2 + (v (k, 0)).im ^ 2 + (v (k, 1)).re ^ 2 + (v (k, 1)).im ^ 2)
    * Real.cos_sq_add_sin_sq θ

/-- ★ **The encounter register is blind to the gate rotation of the messenger.** -/
theorem relWeight_levelLift_gateRot_spinY (w : ℂ) (ρ θ : ℝ) (ΨA : (ZMod L × Fin 2) × Fin 2 → ℂ)
    (v : ZMod L × Fin 2 → ℂ) :
    relWeight w ρ ΨA (levelLift 0 (gateRot spinY θ *ᵥ v)) = relWeight w ρ ΨA (levelLift 0 v) := by
  simp only [relWeight, devSiteWeight_levelLift, siteWeight_gateRot_spinY]

/-- **The encounter weight moves by at most the total weight of `A` times the change of the site
densities.** -/
theorem abs_relWeight_levelLift_sub_le (w : ℂ) (ρ : ℝ) (ΨA : (ZMod L × Fin 2) × Fin 2 → ℂ)
    (ψ χ : ZMod L × Fin 2 → ℂ) :
    |relWeight w ρ ΨA (levelLift 0 ψ) - relWeight w ρ ΨA (levelLift 0 χ)|
      ≤ devRegionWeight ΨA Finset.univ * ∑ p, |‖ψ p‖ ^ 2 - ‖χ p‖ ^ 2| := by
  simp only [relWeight, devSiteWeight_levelLift]
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [devRegionWeight, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hsite : ∑ k, |siteWeight ψ k - siteWeight χ k| ≤ ∑ p, |‖ψ p‖ ^ 2 - ‖χ p‖ ^ 2| := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun k _ => ?_
    simp only [siteWeight, ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  calc ∑ k, |(if ‖(ZMod.toCircle k : ℂ) * star (ZMod.toCircle j : ℂ) - w‖ ≤ ρ
            then devSiteWeight ΨA j * siteWeight ψ k else 0)
          - (if ‖(ZMod.toCircle k : ℂ) * star (ZMod.toCircle j : ℂ) - w‖ ≤ ρ
            then devSiteWeight ΨA j * siteWeight χ k else 0)|
      ≤ ∑ k, devSiteWeight ΨA j * |siteWeight ψ k - siteWeight χ k| :=
        Finset.sum_le_sum fun k _ => by
          split_ifs
          · rw [← mul_sub, abs_mul, abs_of_nonneg (devSiteWeight_nonneg _ _)]
          · rw [sub_zero, abs_zero]
            exact mul_nonneg (devSiteWeight_nonneg _ _) (abs_nonneg _)
    _ = devSiteWeight ΨA j * ∑ k, |siteWeight ψ k - siteWeight χ k| := by rw [Finset.mul_sum]
    _ ≤ devSiteWeight ΨA j * ∑ p, |‖ψ p‖ ^ 2 - ‖χ p‖ ^ 2| :=
        mul_le_mul_of_nonneg_left hsite (devSiteWeight_nonneg _ _)

end Chain

/-- **The change of the site densities is controlled by the `ℓ²` distance**:
`Σ_p |‖ψ_p‖² − ‖χ_p‖²| ≤ √(2‖ψ‖² + 2‖χ‖²) · ‖ψ − χ‖`. -/
theorem sum_abs_norm_sq_sub_le {ι : Type*} [Fintype ι] (ψ χ : ι → ℂ) :
    ∑ p, |‖ψ p‖ ^ 2 - ‖χ p‖ ^ 2|
      ≤ Real.sqrt (2 * sqNorm ψ + 2 * sqNorm χ) * Real.sqrt (sqNorm (ψ - χ)) := by
  have h1 : ∀ p, |‖ψ p‖ ^ 2 - ‖χ p‖ ^ 2| ≤ (‖ψ p‖ + ‖χ p‖) * ‖ψ p - χ p‖ := fun p => by
    rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le _ _) (by positivity)
  have h2 : ∑ p, (‖ψ p‖ + ‖χ p‖) * ‖ψ p - χ p‖
      ≤ Real.sqrt (∑ p, (‖ψ p‖ + ‖χ p‖) ^ 2) * Real.sqrt (∑ p, ‖ψ p - χ p‖ ^ 2) := by
    rw [← Real.sqrt_mul (Finset.sum_nonneg fun p _ => sq_nonneg _)]
    exact (Real.le_sqrt (Finset.sum_nonneg fun p _ => by positivity)
      (by positivity)).2 (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  have h3 : ∑ p, (‖ψ p‖ + ‖χ p‖) ^ 2 ≤ 2 * sqNorm ψ + 2 * sqNorm χ := by
    simp only [sqNorm, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun p _ => by nlinarith [sq_nonneg (‖ψ p‖ - ‖χ p‖)]
  have h4 : ∑ p, ‖ψ p - χ p‖ ^ 2 = sqNorm (ψ - χ) := by
    simp only [sqNorm, Pi.sub_apply]
  calc ∑ p, |‖ψ p‖ ^ 2 - ‖χ p‖ ^ 2|
      ≤ ∑ p, (‖ψ p‖ + ‖χ p‖) * ‖ψ p - χ p‖ := Finset.sum_le_sum fun p _ => h1 p
    _ ≤ Real.sqrt (∑ p, (‖ψ p‖ + ‖χ p‖) ^ 2) * Real.sqrt (∑ p, ‖ψ p - χ p‖ ^ 2) := h2
    _ ≤ Real.sqrt (2 * sqNorm ψ + 2 * sqNorm χ) * Real.sqrt (sqNorm (ψ - χ)) := by
        rw [h4]
        exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h3) (Real.sqrt_nonneg _)

/-- **A device's total weight is the sum of its levels' squared norms.** -/
theorem devRegionWeight_univ_eq {L : ℕ} [NeZero L] (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) :
    devRegionWeight Ψ Finset.univ = ∑ i : Fin 2, sqNorm fun q => Ψ (q, i) := by
  simp only [devRegionWeight, devSiteWeight, siteWeight, sqNorm, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- **Each level of a device solves its own Dirac equation.** -/
theorem hasDerivAt_devicePacket_level {L : ℕ} [NeZero L] (J μ₀ μ₁ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ)
    (t : ℝ) (i : Fin 2) :
    HasDerivAt (fun t => fun q => devicePacket (L := L) J μ₀ μ₁ W β t (q, i))
      ((-I) • (diracHam J (levelMass μ₀ μ₁ i)
        *ᵥ fun q => devicePacket (L := L) J μ₀ μ₁ W β t (q, i))) t := by
  rw [hasDerivAt_pi]
  intro q
  refine (hasDerivAt_pi.1 (hasDerivAt_devicePacket (L := L) J μ₀ μ₁ W β t) (q, i)).congr_deriv ?_
  simp only [Pi.smul_apply, smul_eq_mul, deviceHam_mulVec_apply]

/-! ### Small generic facts for the arena -/

theorem gateRot_pi_div_two_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (V : Matrix ι ι ℂ)
    (v : ι → ℂ) : gateRot V (Real.pi / 2) *ᵥ v = (-I) • (V *ᵥ v) := by
  rw [gateRot_mulVec, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp [neg_smul]

theorem sqNorm_sub_comm {ι : Type*} [Fintype ι] (ψ χ : ι → ℂ) :
    sqNorm (ψ - χ) = sqNorm (χ - ψ) := by
  simp only [sqNorm, Pi.sub_apply, norm_sub_rev]

theorem norm_le_two_of_sqNorm_le {ι : Type*} [Fintype ι] {Ψ : ι → ℂ} (h : sqNorm Ψ ≤ 3) :
    ‖Ψ‖ ≤ 2 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  have hi : ‖Ψ i‖ ^ 2 ≤ sqNorm Ψ :=
    Finset.single_le_sum (f := fun i => ‖Ψ i‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
  nlinarith [norm_nonneg (Ψ i)]

/-- An integrand at most `ε` up to `t_f` and at most `M` after integrates to at most
`ε t_f + M (t − t_f)`. -/
theorem integral_le_of_le_on_then {F : ℝ → ℝ} (hF : Continuous F) {ε M tf t : ℝ}
    (htf0 : 0 ≤ tf) (htf : tf ≤ t) (hε : ∀ s, 0 ≤ s → s ≤ tf → F s ≤ ε) (hM : ∀ s, F s ≤ M) :
    ∫ s in (0 : ℝ)..t, F s ≤ ε * tf + M * (t - tf) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable 0 tf)
    (hF.intervalIntegrable tf t)]
  have h1 := intervalIntegral.integral_mono_on htf (hF.intervalIntegrable tf t)
    (intervalIntegrable_const (μ := volume) (c := M)) fun s _ => hM s
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at h1
  have h0 := integral_le_of_le_on hF htf0 le_rfl hε
  linarith

theorem pi_gt_314 : (314 / 100 : ℝ) < Real.pi := by
  have := Real.pi_gt_d2
  norm_num at this ⊢
  linarith

/-! ### The relay arena on the Dirac chain -/

section Arena

variable {L : ℕ} [NeZero L]

/-- The hop of the Doppler arena's chains: lattice spacing `2π·10¹³/L`, `c = 1`. -/
noncomputable def relayHop (L : ℕ) : ℝ := scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)

/-- **The rest energies of the five blocks**: `A`'s two levels, `B`'s two levels, the messenger. -/
noncomputable def relayMass : Fin 5 → ℝ := ![3, 3 + 1 / 10 ^ 11, 3, 3 + 1 / 10 ^ 11, 3]

theorem relayMass_zero : relayMass 0 = 3 := by simp [relayMass]
theorem relayMass_one : relayMass 1 = 3 + 1 / 10 ^ 11 := by simp [relayMass]
theorem relayMass_two : relayMass 2 = 3 := by simp [relayMass]
theorem relayMass_three : relayMass 3 = 3 + 1 / 10 ^ 11 := by simp [relayMass]
theorem relayMass_four : relayMass 4 = 3 := by simp [relayMass]

/-- **The index of the relay arena**: a site and a spinor component, in one of five blocks. -/
abbrev RelayIdx (L : ℕ) : Type := (ZMod L × Fin 2) × Fin 5

/-- **The free Hamiltonian**: five Dirac chains, one per block. -/
noncomputable abbrev relayHam (L : ℕ) : Matrix (RelayIdx L) (RelayIdx L) ℂ :=
  Matrix.blockDiagonal fun k => diracHam (relayHop L) (relayMass k)

/-- **The gate matrix**: `σ_y` on the messenger's block, nothing elsewhere. -/
noncomputable abbrev relayGateMat (L : ℕ) : Matrix (RelayIdx L) (RelayIdx L) ℂ :=
  gateBlock (4 : Fin 5) (spinY (L := L))

/-- Device `A`, read off blocks `0` and `1`. -/
def devA (Ψ : RelayIdx L → ℂ) : (ZMod L × Fin 2) × Fin 2 → ℂ := fun x => Ψ (x.1, ![0, 1] x.2)

/-- Device `B`, read off blocks `2` and `3`. -/
def devB (Ψ : RelayIdx L → ℂ) : (ZMod L × Fin 2) × Fin 2 → ℂ := fun x => Ψ (x.1, ![2, 3] x.2)

/-- The messenger, block `4`. -/
def mess (Ψ : RelayIdx L → ℂ) : ZMod L × Fin 2 → ℂ := blockOf Ψ 4

/-- **The free blocks**: `A` at rest, `B` approaching from `3` radians away (at `A` at `5·10¹³`),
the messenger leaving `A` at `4·10¹²` — #256's arena, block by block. -/
noncomputable def relayBlock (t : ℝ) : Fin 5 → ZMod L × Fin 2 → ℂ :=
  ![fun q => restObserver t (q, 0), fun q => restObserver t (q, 1),
    fun q => approachObserver (t - 5 * 10 ^ 13) (q, 0),
    fun q => approachObserver (t - 5 * 10 ^ 13) (q, 1), imagePacket (t - 4 * 10 ^ 12)]

/-- **The free trajectory** as one state. -/
noncomputable def relayState (t : ℝ) : RelayIdx L → ℂ := fun x => relayBlock t x.2 x.1

theorem blockOf_relayState (t : ℝ) (k : Fin 5) :
    blockOf (relayState (L := L) t) k = relayBlock t k := rfl

theorem relayBlock_zero (t : ℝ) : relayBlock (L := L) t 0 = fun q => restObserver t (q, 0) := by
  simp [relayBlock]
theorem relayBlock_one (t : ℝ) : relayBlock (L := L) t 1 = fun q => restObserver t (q, 1) := by
  simp [relayBlock]
theorem relayBlock_two (t : ℝ) :
    relayBlock (L := L) t 2 = fun q => approachObserver (t - 5 * 10 ^ 13) (q, 0) := by
  simp [relayBlock]
theorem relayBlock_three (t : ℝ) :
    relayBlock (L := L) t 3 = fun q => approachObserver (t - 5 * 10 ^ 13) (q, 1) := by
  simp [relayBlock]
theorem relayBlock_four (t : ℝ) : relayBlock (L := L) t 4 = imagePacket (t - 4 * 10 ^ 12) := by
  simp [relayBlock]

theorem devA_relayState (t : ℝ) : devA (relayState (L := L) t) = restObserver t := by
  funext ⟨q, i⟩
  fin_cases i
  · exact congrFun (relayBlock_zero (L := L) t) q
  · exact congrFun (relayBlock_one (L := L) t) q

theorem devB_relayState (t : ℝ) :
    devB (relayState (L := L) t) = approachObserver (t - 5 * 10 ^ 13) := by
  funext ⟨q, i⟩
  fin_cases i
  · exact congrFun (relayBlock_two (L := L) t) q
  · exact congrFun (relayBlock_three (L := L) t) q

theorem mess_relayState (t : ℝ) :
    mess (relayState (L := L) t) = imagePacket (t - 4 * 10 ^ 12) := by
  rw [mess, blockOf_relayState, relayBlock_four]

/-- **Each block of the free trajectory solves its Dirac equation.** -/
theorem hasDerivAt_relayState_block (k : Fin 5) (t : ℝ) :
    HasDerivAt (fun t => relayBlock (L := L) t k)
      ((-I) • (diracHam (relayHop L) (relayMass k) *ᵥ relayBlock t k)) t := by
  fin_cases k
  · show HasDerivAt (fun t => relayBlock (L := L) t 0)
      ((-I) • (diracHam (relayHop L) (relayMass 0) *ᵥ relayBlock t 0)) t
    simp only [relayBlock_zero, relayMass_zero, restObserver, relayHop]
    exact hasDerivAt_devicePacket_level (L := L) _ 3 (3 + 1 / 10 ^ 11) _ twinAmp t 0
  · show HasDerivAt (fun t => relayBlock (L := L) t 1)
      ((-I) • (diracHam (relayHop L) (relayMass 1) *ᵥ relayBlock t 1)) t
    simp only [relayBlock_one, relayMass_one, restObserver, relayHop]
    exact hasDerivAt_devicePacket_level (L := L) _ 3 (3 + 1 / 10 ^ 11) _ twinAmp t 1
  · show HasDerivAt (fun t => relayBlock (L := L) t 2)
      ((-I) • (diracHam (relayHop L) (relayMass 2) *ᵥ relayBlock t 2)) t
    simp only [relayBlock_two, relayMass_two, approachObserver, relayHop]
    exact (hasDerivAt_devicePacket_level (L := L) _ 3 (3 + 1 / 10 ^ 11) _ twinAmp
      (t - 5 * 10 ^ 13) 0).comp_sub_const t (5 * 10 ^ 13)
  · show HasDerivAt (fun t => relayBlock (L := L) t 3)
      ((-I) • (diracHam (relayHop L) (relayMass 3) *ᵥ relayBlock t 3)) t
    simp only [relayBlock_three, relayMass_three, approachObserver, relayHop]
    exact (hasDerivAt_devicePacket_level (L := L) _ 3 (3 + 1 / 10 ^ 11) _ twinAmp
      (t - 5 * 10 ^ 13) 1).comp_sub_const t (5 * 10 ^ 13)
  · show HasDerivAt (fun t => relayBlock (L := L) t 4)
      ((-I) • (diracHam (relayHop L) (relayMass 4) *ᵥ relayBlock t 4)) t
    simp only [relayBlock_four, relayMass_four, imagePacket, ringPacket, relayHop]
    exact (hasDerivAt_packet (L := L) _ 3 imageWin _ (t - 4 * 10 ^ 12)).comp_sub_const t
      (4 * 10 ^ 12)

/-- **The free trajectory solves the free equation.** -/
theorem hasDerivAt_relayState (t : ℝ) :
    HasDerivAt (relayState (L := L)) ((-I) • (relayHam L *ᵥ relayState t)) t := by
  rw [hasDerivAt_pi]
  rintro ⟨q, k⟩
  refine (hasDerivAt_pi.1 (hasDerivAt_relayState_block k t) q).congr_deriv ?_
  simp only [Pi.smul_apply, smul_eq_mul, relayHam, blockDiagonal_mulVec_block, blockOf_relayState]

theorem continuous_relayState : Continuous (relayState (L := L)) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_relayState t).continuousAt

omit [NeZero L] in
theorem isHermitian_relayHam : (relayHam L).IsHermitian :=
  isHermitian_blockDiagonal fun _ => diracHam_isHermitian _ _

omit [NeZero L] in
theorem isHermitian_relayGateMat : (relayGateMat L).IsHermitian :=
  isHermitian_gateBlock 4 spinY_isHermitian

/-! #### The weight and the gate -/

/-- **The clipped encounter weight**: `max (relWeight(B, messenger) − 1/2) 0` — zero while the
messenger is far from `B`, so the register does not drift before the encounter. -/
noncomputable def relayRaw (Ψ : RelayIdx L → ℂ) : ℝ :=
  max (relWeight 1 (1 / 10) (devB Ψ) (levelLift 0 (mess Ψ)) - 1 / 2) 0

/-- **The register's weight**: the clipped encounter weight, saturated beyond sup-norm `2` and
closed from `3` — the identity on every physical state. -/
noncomputable def relayWeight (Ψ : RelayIdx L → ℂ) : ℝ := satCut 3 relayRaw Ψ

omit [NeZero L] in
theorem continuous_devB : Continuous (devB (L := L)) := continuous_pi fun _ => continuous_apply _

omit [NeZero L] in
theorem continuous_mess : Continuous (mess (L := L)) := continuous_pi fun _ => continuous_apply _

theorem continuous_relayRaw : Continuous (relayRaw (L := L)) :=
  ((continuous_relWeight_comp continuous_devB (continuous_levelLift_zero.comp continuous_mess) 1
    (1 / 10)).sub continuous_const).max continuous_const

theorem relayRaw_nonneg (Ψ : RelayIdx L → ℂ) : 0 ≤ relayRaw Ψ := le_max_right _ _

/-- The encounter weight is smooth: a polynomial in the components. -/
theorem contDiff_relWeight_devB_mess :
    ContDiff ℝ 1 fun Ψ : RelayIdx L → ℂ =>
      relWeight 1 (1 / 10) (devB Ψ) (levelLift 0 (mess Ψ)) := by
  simp only [relWeight, devSiteWeight_levelLift]
  refine ContDiff.sum fun j _ => ContDiff.sum fun k _ => ?_
  by_cases h : ‖(ZMod.toCircle k : ℂ) * star (ZMod.toCircle j : ℂ) - (1 : ℂ)‖ ≤ 1 / 10
  · simp only [h, ↓reduceIte]
    refine ContDiff.mul ?_ ?_
    · simp only [devSiteWeight, siteWeight, devB]
      exact ContDiff.sum fun i _ => ContDiff.sum fun c _ =>
        ContDiff.norm_sq ℂ (contDiff_apply _ _ _)
    · simp only [siteWeight, mess, blockOf]
      exact ContDiff.sum fun c _ => ContDiff.norm_sq ℂ (contDiff_apply _ _ _)
  · simp only [h, ↓reduceIte]
    exact contDiff_const

theorem exists_lipschitzOnWith_relayRaw :
    ∃ K : ℝ≥0, LipschitzOnWith K (relayRaw (L := L)) (Metric.closedBall 0 3) := by
  obtain ⟨K, hK⟩ := (contDiff_relWeight_devB_mess (L := L)).contDiffOn.exists_lipschitzOnWith
    one_ne_zero (convex_closedBall _ _) (isCompact_closedBall _ _)
  have h1 : LipschitzWith 1 fun x : ℝ => max (x - 1 / 2) 0 :=
    ((LipschitzWith.id.sub (LipschitzWith.const _)).weaken (le_of_eq (add_zero _))).max_const 0
  exact ⟨1 * K, h1.comp_lipschitzOnWith hK⟩

theorem exists_bound_relayRaw :
    ∃ M : ℝ≥0, ∀ Ψ : RelayIdx L → ℂ, ‖Ψ‖ ≤ 3 → |relayRaw Ψ| ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : RelayIdx L → ℂ) 3).exists_bound_of_continuousOn
    (continuous_relayRaw (L := L)).continuousOn
  refine ⟨Real.toNNReal C, fun Ψ hΨ => ?_⟩
  have := hC Ψ (mem_closedBall_zero_iff.2 hΨ)
  rw [Real.norm_eq_abs] at this
  exact this.trans (Real.le_coe_toNNReal C)

/-- ★ **The saturated weight is globally Lipschitz.** -/
theorem exists_lipschitzWith_relayWeight : ∃ K : ℝ≥0, LipschitzWith K (relayWeight (L := L)) := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_relayRaw (L := L)
  obtain ⟨M, hM⟩ := exists_bound_relayRaw (L := L)
  exact ⟨K + M, lipschitzWith_satCut hK hM⟩

theorem exists_bound_relayWeight : ∃ M : ℝ≥0, ∀ Ψ : RelayIdx L → ℂ, |relayWeight Ψ| ≤ M := by
  obtain ⟨M, hM⟩ := exists_bound_relayRaw (L := L)
  exact ⟨M, fun Ψ => abs_satCut_le hM Ψ⟩

theorem relayWeight_eq_zero {Ψ : RelayIdx L → ℂ} (h : (3 : ℝ) ≤ ‖Ψ‖) : relayWeight Ψ = 0 :=
  satCut_eq_zero _ h

/-- **On the physical region the saturation is invisible.** -/
theorem relayWeight_eq_of_le {Ψ : RelayIdx L → ℂ} (h : ‖Ψ‖ ≤ 2) : relayWeight Ψ = relayRaw Ψ :=
  satCut_eq_of_le _ (by linarith)

theorem relayWeight_nonneg (Ψ : RelayIdx L → ℂ) : 0 ≤ relayWeight Ψ :=
  satCut_nonneg relayRaw_nonneg Ψ

theorem continuous_relayWeight : Continuous (relayWeight (L := L)) :=
  (exists_lipschitzWith_relayWeight (L := L)).choose_spec.continuous

/-- **The gate opens when the register reaches `3·10¹¹`** ... -/
noncomputable def relayLo : ℝ := 3 * 10 ^ 11

/-- ... **and has delivered `π/2` once it reaches `3·10¹¹ + 1.2·10⁻³`.** -/
noncomputable def relayHi : ℝ := 3 * 10 ^ 11 + 12 / 10 ^ 4

theorem relayLo_lt_relayHi : relayLo < relayHi := by
  unfold relayLo relayHi
  norm_num

/-- ★★ **The relay field is globally Lipschitz**: the relay is a flow. -/
theorem relayLipschitz : ∃ K : ℝ≥0, LipschitzWith K
    (gatedField (relayHam L) (relayGateMat L) (relayGate relayLo relayHi relayWeight)
      relayWeight) := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_relayWeight (L := L)
  obtain ⟨M, hM⟩ := exists_bound_relayWeight (L := L)
  exact exists_lipschitzWith_relayField _ _ relayLo_lt_relayHi hK hM (by norm_num)
    fun Ψ h => relayWeight_eq_zero h

/-- ★★ **The relay flow**: `A`, `B`, the messenger and `B`'s relay register, one gated flow. -/
noncomputable def relayFlow (t : ℝ) (x : GateArena (RelayIdx L)) : GateArena (RelayIdx L) :=
  gatedFlow relayLipschitz t x

/-- **The preparation**: the free state at time `0`, the register at `0`. -/
noncomputable def relayPrep (L : ℕ) [NeZero L] : GateArena (RelayIdx L) := (relayState 0, 0)

theorem continuous_relayGate : Continuous fun x : GateArena (RelayIdx L) =>
    relayGate relayLo relayHi relayWeight x.1 x.2 :=
  ((continuous_pulseRate _ _).comp continuous_snd).mul (continuous_relayWeight.comp continuous_fst)

/-- ★★ **The devices evolve freely for all time**, whatever the gate does to the messenger. -/
theorem relayFlow_block_free {k : Fin 5} (hk : k ≠ 4) (t : ℝ) :
    blockOf (relayFlow t (relayPrep L)).1 k = relayBlock t k :=
  gatedFlow_block_eq relayLipschitz (relayPrep L) hk (hasDerivAt_relayState_block k) rfl t

theorem devA_relayFlow (t : ℝ) : devA (relayFlow t (relayPrep L)).1 = restObserver t := by
  funext ⟨q, i⟩
  fin_cases i
  · show blockOf (relayFlow t (relayPrep L)).1 0 q = restObserver t (q, 0)
    rw [relayFlow_block_free (by decide), relayBlock_zero]
  · show blockOf (relayFlow t (relayPrep L)).1 1 q = restObserver t (q, 1)
    rw [relayFlow_block_free (by decide), relayBlock_one]

theorem devB_relayFlow (t : ℝ) :
    devB (relayFlow t (relayPrep L)).1 = approachObserver (t - 5 * 10 ^ 13) := by
  funext ⟨q, i⟩
  fin_cases i
  · show blockOf (relayFlow t (relayPrep L)).1 2 q = approachObserver (t - 5 * 10 ^ 13) (q, 0)
    rw [relayFlow_block_free (by decide), relayBlock_two]
  · show blockOf (relayFlow t (relayPrep L)).1 3 q = approachObserver (t - 5 * 10 ^ 13) (q, 1)
    rw [relayFlow_block_free (by decide), relayBlock_three]

theorem relayFlow_register_mono {s t : ℝ} (hst : s ≤ t) :
    (relayFlow s (relayPrep L)).2 ≤ (relayFlow t (relayPrep L)).2 := by
  have e : relayFlow t (relayPrep L) = relayFlow (t - s) (relayFlow s (relayPrep L)) := by
    rw [relayFlow, relayFlow, relayFlow, ← gatedFlow_add, add_sub_cancel]
  rw [e]
  exact register_mono_gatedFlow _ continuous_relayWeight relayWeight_nonneg _ (by linarith)

/-! #### The free register -/

/-- The encounter time of #256's first reception, `t_k = 1.66·10¹⁴/7`. -/
noncomputable def relayTk : ℝ := 166 * 10 ^ 12 / 7

/-- **The free register's rate**: the clipped encounter weight along the free trajectory. -/
noncomputable def relayRate (L : ℕ) [NeZero L] (s : ℝ) : ℝ := relayRaw (relayState (L := L) s)

/-- **The free register**: its integral from `0`. -/
noncomputable def relayReg (L : ℕ) [NeZero L] (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, relayRate L s

theorem relayRate_eq (s : ℝ) :
    relayRate L s = max (relWeight 1 (1 / 10) (approachObserver (L := L) (s - 5 * 10 ^ 13))
      (levelLift 0 (imagePacket (s - 4 * 10 ^ 12))) - 1 / 2) 0 := by
  rw [relayRate, relayRaw, devB_relayState, mess_relayState]

theorem continuous_relayRate : Continuous (relayRate L) :=
  continuous_relayRaw.comp continuous_relayState

theorem relayRate_nonneg (s : ℝ) : 0 ≤ relayRate L s := relayRaw_nonneg _

theorem hasDerivAt_relayReg (t : ℝ) : HasDerivAt (relayReg L) (relayRate L t) t :=
  ((continuous_relayRate (L := L)).integral_hasStrictDerivAt 0 t).hasDerivAt

theorem continuous_relayReg : Continuous (relayReg L) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_relayReg t).continuousAt

theorem relayReg_zero : relayReg L 0 = 0 := intervalIntegral.integral_same

theorem relayReg_mono {s t : ℝ} (hst : s ≤ t) : relayReg L s ≤ relayReg L t := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((continuous_relayRate (L := L)).intervalIntegrable 0 s)
    ((continuous_relayRate (L := L)).intervalIntegrable s t)
  have h2 := intervalIntegral.integral_nonneg (μ := volume) hst fun u _ => relayRate_nonneg (L := L) u
  unfold relayReg
  linarith

section WithL

variable (hL : 10 ^ 19 ≤ L)
include hL

theorem sqNorm_imagePacket (t : ℝ) : sqNorm (imagePacket (L := L) t) = 1 := by
  rw [sqNorm_eq_re_chainInner, imagePacket_norm hL, Complex.one_re]

/-- **The free state carries weight `3`**: one for each device, one for the messenger. -/
theorem sqNorm_relayState (t : ℝ) : sqNorm (relayState (L := L) t) = 3 := by
  rw [sqNorm_eq_sum_blocks]
  simp only [Fin.sum_univ_five, blockOf_relayState, relayBlock_zero, relayBlock_one,
    relayBlock_two, relayBlock_three, relayBlock_four]
  have hA := rest_total (L := L) hL t
  have hB := approach_total (L := L) hL (t - 5 * 10 ^ 13)
  rw [devRegionWeight_univ_eq, Fin.sum_univ_two] at hA hB
  have hM := sqNorm_imagePacket hL (t - 4 * 10 ^ 12)
  linarith

theorem norm_relayState_le (t : ℝ) : ‖relayState (L := L) t‖ ≤ 2 :=
  norm_le_two_of_sqNorm_le (le_of_eq (sqNorm_relayState hL t))

/-- ★ **The relay flow conserves the weight `3`.** -/
theorem sqNorm_relayFlow (t : ℝ) : sqNorm (relayFlow t (relayPrep L)).1 = 3 := by
  have h := sum_norm_sq_gatedFlow relayLipschitz isHermitian_relayHam isHermitian_relayGateMat
    (relayPrep L) t
  show ∑ i, ‖(gatedFlow relayLipschitz t (relayPrep L)).1 i‖ ^ 2 = 3
  rw [h]
  exact sqNorm_relayState hL 0

theorem norm_relayFlow_le (t : ℝ) : ‖(relayFlow t (relayPrep L)).1‖ ≤ 2 :=
  norm_le_two_of_sqNorm_le (le_of_eq (sqNorm_relayFlow hL t))

/-- ★ **Along the orbit the saturation is invisible**: the weight is the clipped encounter
weight. -/
theorem relayWeight_relayFlow (t : ℝ) :
    relayWeight (relayFlow t (relayPrep L)).1 = relayRaw (relayFlow t (relayPrep L)).1 :=
  relayWeight_eq_of_le (norm_relayFlow_le hL t)

/-- **The messenger keeps its weight `1`** through the pulse. -/
theorem sqNorm_mess_relayFlow (t : ℝ) :
    sqNorm (mess (relayFlow t (relayPrep L)).1) = 1 := by
  have h := sqNorm_relayFlow hL t
  rw [sqNorm_eq_sum_blocks] at h
  simp only [Fin.sum_univ_five, relayFlow_block_free (k := 0) (by decide),
    relayFlow_block_free (k := 1) (by decide), relayFlow_block_free (k := 2) (by decide),
    relayFlow_block_free (k := 3) (by decide), relayBlock_zero, relayBlock_one, relayBlock_two,
    relayBlock_three] at h
  have hA := rest_total (L := L) hL t
  have hB := approach_total (L := L) hL (t - 5 * 10 ^ 13)
  rw [devRegionWeight_univ_eq, Fin.sum_univ_two] at hA hB
  show sqNorm (blockOf (relayFlow t (relayPrep L)).1 4) = 1
  linarith

/-- ★ **The messenger's energy**: `‖Hψ‖² ≤ 26` (`E² = 9 + 16` up to the window's spread). -/
theorem sqNorm_diracHam_imagePacket_le (s : ℝ) :
    sqNorm (diracHam (relayHop L) 3 *ᵥ imagePacket (L := L) s) ≤ 26 := by
  have hD := (noWrap_distinct_of_window (L := L) (image_win hL)).2
  have h := sqNorm_diracHam_mulVec_packet_le (L := L) (relayHop L) 3 hD
    (unitAmp L (relayHop L) 3 twinAmp) s (E2 := 26) fun m hm => by
      have := bandE_sq_le_scaled (L := L) (ℓ := 2 * Real.pi * 10 ^ 13) (by positivity) 3
        (image_spread m hm)
      refine this.trans ?_
      norm_num
  have hn := sqNorm_imagePacket hL s
  simp only [imagePacket, ringPacket] at hn ⊢
  simp only [relayHop] at h
  rw [hn, mul_one] at h
  exact h

/-- **The free messenger drifts by at most `u√26` in time `u`.** -/
theorem sqNorm_imagePacket_sub_le (s : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    sqNorm (imagePacket (L := L) (s + u) - imagePacket s) ≤ u ^ 2 * 26 := by
  have h := sqNorm_sub_gateRot_le (H := diracHam (relayHop L) 3) (V := spinY)
    (diracHam_isHermitian _ _) spinY_isHermitian (spinY_mulVec_diracHam_mulVec _ _)
    spinY_mulVec_spinY (c := fun _ => 0) continuous_const
    (Ψ := fun u => imagePacket (L := L) (s + u)) (fun u => ?_) hu
  · rw [intervalIntegral.integral_zero, gateRot_zero_mulVec, add_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (sqNorm_diracHam_imagePacket_le hL _) (sq_nonneg _))
  · have := (hasDerivAt_packet (L := L) (relayHop L) 3 imageWin
      (unitAmp L (relayHop L) 3 twinAmp) (s + u)).comp_const_add s u
    simp only [imagePacket, ringPacket, Complex.ofReal_zero, zero_smul, add_zero]
    simpa only [relayHop] using this

/-! #### The register before, through and after the encounter -/

/-- **Before the encounter the rate is zero**: the messenger is far from `B`. -/
theorem relayRate_eq_zero {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ relayTk - 1008 * 10 ^ 9) :
    relayRate L s = 0 := by
  have hπ := pi_gt_314
  have htk : relayTk = 166 * 10 ^ 12 / 7 := rfl
  rw [relayRate_eq]
  have hfar := reception_far hL (e := 4 * 10 ^ 12) (t := s)
    (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith)
    (by rw [abs_of_nonneg (by linarith)]; linarith) (by rw [abs_of_nonneg (by linarith)]; linarith)
  exact max_eq_right (by linarith)

theorem relayRate_le_half (s : ℝ) : relayRate L s ≤ 1 / 2 := by
  rw [relayRate_eq]
  exact max_le (by linarith [rel_approach_le_one hL (4 * 10 ^ 12) s]) (by norm_num)

/-- **Through the encounter the rate is at least `0.988² − 1/2`.** -/
theorem relayRate_ge {s : ℝ} (hs : |s - relayTk| ≤ 4285 * 10 ^ 8) :
    (1 - 6 / 1000) ^ 2 - 1 / 2 ≤ relayRate L s := by
  have htk : relayTk = 166 * 10 ^ 12 / 7 := rfl
  rw [abs_le] at hs
  rw [relayRate_eq]
  have hnear := reception_near hL (e := 4 * 10 ^ 12) (t := s)
    (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith)
    (by rw [abs_le]; constructor <;> linarith)
  exact le_max_of_le_left (by linarith)

/-- **At the start of the sure window the register is at most `2.9·10¹¹`.** -/
theorem relayReg_start_le : relayReg L (relayTk - 428 * 10 ^ 9) ≤ 29 * 10 ^ 10 := by
  have htk : relayTk = 166 * 10 ^ 12 / 7 := rfl
  have h := integral_le_of_le_on_then (continuous_relayRate (L := L)) (ε := 0) (M := 1 / 2)
    (tf := relayTk - 1008 * 10 ^ 9) (t := relayTk - 428 * 10 ^ 9) (by rw [htk]; norm_num)
    (by rw [htk]; norm_num) (fun s hs0 hs => (relayRate_eq_zero hL hs0 hs).le)
    (relayRate_le_half hL)
  rw [relayReg]
  refine h.trans ?_
  rw [htk]
  norm_num

/-- **At the end of the sure window the register is at least `4·10¹¹`.** -/
theorem relayReg_end_ge : 4 * 10 ^ 11 ≤ relayReg L (relayTk + 428 * 10 ^ 9) := by
  have htk : relayTk = 166 * 10 ^ 12 / 7 := rfl
  have h := le_integral_of_ge_on (continuous_relayRate (L := L)) (κ := (1 - 6 / 1000) ^ 2 - 1 / 2)
    (tn := relayTk - 428 * 10 ^ 9) (te := relayTk + 428 * 10 ^ 9) (t := relayTk + 428 * 10 ^ 9)
    (by rw [htk]; norm_num) (by linarith) le_rfl (fun s _ => relayRate_nonneg s)
    fun s hs1 hs2 => relayRate_ge hL (by rw [abs_le]; constructor <;> linarith)
  rw [relayReg]
  refine le_trans ?_ h
  rw [htk]
  norm_num

/-- ★★ **The register crosses the threshold inside the sure window.** -/
theorem exists_relayCross :
    ∃ s₀ ∈ Icc (relayTk - 428 * 10 ^ 9) (relayTk + 428 * 10 ^ 9), relayReg L s₀ = relayLo := by
  have h := intermediate_value_Icc (f := relayReg L)
    (a := relayTk - 428 * 10 ^ 9) (b := relayTk + 428 * 10 ^ 9) (by linarith)
    (continuous_relayReg (L := L)).continuousOn
  have hmem : relayLo ∈ Icc (relayReg L (relayTk - 428 * 10 ^ 9))
      (relayReg L (relayTk + 428 * 10 ^ 9)) := by
    constructor
    · exact (relayReg_start_le hL).trans (by unfold relayLo; norm_num)
    · exact (by unfold relayLo; norm_num : relayLo ≤ 4 * 10 ^ 11).trans (relayReg_end_ge hL)
  obtain ⟨s₀, hs₀, h₀⟩ := h hmem
  exact ⟨s₀, hs₀, h₀⟩

/-! #### Free until the crossing -/

/-- ★★ **Up to the crossing the relay orbit is the free trajectory with the free register.** -/
theorem relayFlow_eq_free {s₀ : ℝ} (hr : relayReg L s₀ ≤ relayLo) :
    ∀ t ∈ Icc (0 : ℝ) s₀, relayFlow t (relayPrep L) = (relayState t, relayReg L t) := by
  refine gatedFlow_eq_of_hasDerivAt_Icc relayLipschitz (relayPrep L)
    (y := fun t => (relayState t, relayReg L t)) (fun t ht => ?_) ?_
  · have hreg : relayReg L t ≤ relayLo := (relayReg_mono ht.2).trans hr
    have hgate : relayGate relayLo relayHi relayWeight (relayState (L := L) t) (relayReg L t) = 0 :=
      relayGate_eq_zero_of_le relayLo_lt_relayHi _ _ hreg
    have hw : relayWeight (relayState (L := L) t) = relayRate L t :=
      relayWeight_eq_of_le (norm_relayState_le hL t)
    refine ((hasDerivAt_relayState t).prodMk (hasDerivAt_relayReg t)).congr_deriv ?_
    simp only [gatedField, hgate, Complex.ofReal_zero, zero_smul, add_zero, hw]
  · show (relayState (L := L) 0, relayReg L 0) = (relayState 0, 0)
    rw [relayReg_zero]

/-! #### The pulse -/

/-- **The pulse bound on the messenger** from a free crossing state. -/
theorem sqNorm_mess_relayFlow_sub_le {s₀ : ℝ}
    (hfree : relayFlow s₀ (relayPrep L) = (relayState s₀, relayLo)) {u : ℝ} (hu : 0 ≤ u) :
    sqNorm (mess (relayFlow (s₀ + u) (relayPrep L)).1
        - gateRot spinY (∫ s in (0 : ℝ)..u, relayGate relayLo relayHi relayWeight
            (relayFlow (s₀ + s) (relayPrep L)).1 (relayFlow (s₀ + s) (relayPrep L)).2)
          *ᵥ imagePacket (s₀ - 4 * 10 ^ 12))
      ≤ u ^ 2 * 26 := by
  have h := sqNorm_gateBlock_sub_gateRot_le relayLipschitz (k₀ := 4) (diracHam_isHermitian _ _)
    spinY_isHermitian (spinY_mulVec_diracHam_mulVec _ _) spinY_mulVec_spinY continuous_relayGate
    (relayPrep L) s₀ hu
  change sqNorm (mess (relayFlow (s₀ + u) (relayPrep L)).1 - gateRot spinY
    (∫ s in (0 : ℝ)..u, relayGate relayLo relayHi relayWeight
      (relayFlow (s₀ + s) (relayPrep L)).1 (relayFlow (s₀ + s) (relayPrep L)).2)
    *ᵥ mess (relayFlow s₀ (relayPrep L)).1) ≤ u ^ 2 * sqNorm (diracHam (relayHop L) (relayMass 4)
    *ᵥ mess (relayFlow s₀ (relayPrep L)).1) at h
  rw [relayMass_four, hfree] at h
  have e : mess (relayState (L := L) s₀, relayLo).1 = imagePacket (s₀ - 4 * 10 ^ 12) :=
    mess_relayState s₀
  rw [e] at h
  exact h.trans (mul_le_mul_of_nonneg_left (sqNorm_diracHam_imagePacket_le hL _) (sq_nonneg _))

/-- ★★ **Through the pulse the rate stays above `2/5`**: the register is blind to the rotation,
and the pulse error and the free drift are both at most `u√26 ≤ 0.0153`. -/
theorem relayRaw_relayFlow_ge {s₀ : ℝ} (hs₀ : |s₀ - relayTk| ≤ 428 * 10 ^ 9)
    (hfree : relayFlow s₀ (relayPrep L) = (relayState s₀, relayLo)) {u : ℝ} (hu0 : 0 ≤ u)
    (hu : u ≤ 3 / 1000) : 2 / 5 ≤ relayRaw (relayFlow (s₀ + u) (relayPrep L)).1 := by
  have htk : relayTk = 166 * 10 ^ 12 / 7 := rfl
  rw [abs_le] at hs₀
  set ψ₀ := imagePacket (L := L) (s₀ - 4 * 10 ^ 12) with hψ₀def
  set ψu := imagePacket (L := L) (s₀ + u - 4 * 10 ^ 12) with hψudef
  set Mu := mess (relayFlow (s₀ + u) (relayPrep L)).1 with hMudef
  set θ := ∫ s in (0 : ℝ)..u, relayGate relayLo relayHi relayWeight
    (relayFlow (s₀ + s) (relayPrep L)).1 (relayFlow (s₀ + s) (relayPrep L)).2 with hθdef
  set B := approachObserver (L := L) (s₀ + u - 5 * 10 ^ 13) with hBdef
  have hB : devB (relayFlow (s₀ + u) (relayPrep L)).1 = B := devB_relayFlow _
  have h1 : sqNorm (Mu - gateRot spinY θ *ᵥ ψ₀) ≤ u ^ 2 * 26 :=
    sqNorm_mess_relayFlow_sub_le hL hfree hu0
  have h2 : sqNorm (ψ₀ - ψu) ≤ u ^ 2 * 26 := by
    rw [sqNorm_sub_comm, hψudef, show s₀ + u - 4 * 10 ^ 12 = (s₀ - 4 * 10 ^ 12) + u by ring]
    exact sqNorm_imagePacket_sub_le hL _ hu0
  have hMu : sqNorm Mu = 1 := sqNorm_mess_relayFlow hL _
  have hψ₀ : sqNorm ψ₀ = 1 := sqNorm_imagePacket hL _
  have hψu : sqNorm ψu = 1 := sqNorm_imagePacket hL _
  have hrot : sqNorm (gateRot spinY θ *ᵥ ψ₀) = 1 := by
    rw [sqNorm_gateRot_mulVec spinY_isHermitian spinY_mulVec_spinY, hψ₀]
  have hBtot : devRegionWeight B Finset.univ = 1 := approach_total hL _
  have hsqrt4 : Real.sqrt (2 * 1 + 2 * 1) = 2 := by
    rw [show (2 : ℝ) * 1 + 2 * 1 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hbound : ∀ d : ℝ, d ≤ u ^ 2 * 26 → Real.sqrt d ≤ 3 / 1000 * (51 / 10) := fun d hd => by
    rw [Real.sqrt_le_left (by norm_num)]
    calc d ≤ u ^ 2 * 26 := hd
      _ ≤ (3 / 1000) ^ 2 * 26 := by gcongr
      _ ≤ (3 / 1000 * (51 / 10)) ^ 2 := by norm_num
  have e1 := abs_relWeight_levelLift_sub_le 1 (1 / 10) B Mu (gateRot spinY θ *ᵥ ψ₀)
  have e1' := sum_abs_norm_sq_sub_le Mu (gateRot spinY θ *ᵥ ψ₀)
  rw [hMu, hrot, hsqrt4] at e1'
  have s1 := hbound _ h1
  have e2 := relWeight_levelLift_gateRot_spinY 1 (1 / 10) θ B ψ₀
  have e3 := abs_relWeight_levelLift_sub_le 1 (1 / 10) B ψ₀ ψu
  have e3' := sum_abs_norm_sq_sub_le ψ₀ ψu
  rw [hψ₀, hψu, hsqrt4] at e3'
  have s2 := hbound _ h2
  have hnear : (1 - 6 / 1000) ^ 2 ≤ relWeight 1 (1 / 10) B (levelLift 0 ψu) :=
    reception_near hL (e := 4 * 10 ^ 12) (t := s₀ + u)
      (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith)
      (by rw [abs_le]; constructor <;> linarith)
  rw [hBtot, one_mul] at e1 e3
  have a1 := (abs_le.1 e1).1
  have a3 := (abs_le.1 e3).1
  have hsum1 := e1'.trans (mul_le_mul_of_nonneg_left s1 (by norm_num))
  have hsum3 := e3'.trans (mul_le_mul_of_nonneg_left s2 (by norm_num))
  rw [relayRaw, hB]
  exact le_max_of_le_left (by linarith)

/-- ★★ **The pulse completes**: `3·10⁻³` after the crossing the register has passed `relayHi`. -/
theorem relayReg_after_pulse {s₀ : ℝ} (hs₀ : |s₀ - relayTk| ≤ 428 * 10 ^ 9)
    (hfree : relayFlow s₀ (relayPrep L) = (relayState s₀, relayLo)) :
    relayHi ≤ (relayFlow (s₀ + 3 / 1000) (relayPrep L)).2 := by
  have hgrp : relayFlow (s₀ + 3 / 1000) (relayPrep L)
      = relayFlow (3 / 1000) (relayFlow s₀ (relayPrep L)) := gatedFlow_add _ _ _ _
  have hreg : (relayFlow (3 / 1000) (relayFlow s₀ (relayPrep L))).2
      = (relayFlow s₀ (relayPrep L)).2 + ∫ s in (0 : ℝ)..3 / 1000,
          relayWeight (relayFlow s (relayFlow s₀ (relayPrep L))).1 :=
    register_gatedFlow relayLipschitz continuous_relayWeight _ _
  have hy2 : (relayFlow s₀ (relayPrep L)).2 = relayLo := by rw [hfree]
  have hint := le_integral_of_ge_on
    (F := fun s => relayWeight (relayFlow s (relayFlow s₀ (relayPrep L))).1)
    (continuous_relayWeight.comp (continuous_fst.comp (continuous_gatedFlow_time _ _)))
    (κ := 2 / 5) (tn := 0) (te := 3 / 1000) (t := 3 / 1000) le_rfl (by norm_num) le_rfl
    (fun s _ => relayWeight_nonneg _) fun s hs1 hs2 => by
      have e : relayFlow s (relayFlow s₀ (relayPrep L)) = relayFlow (s₀ + s) (relayPrep L) :=
        (gatedFlow_add _ _ _ _).symm
      rw [e, relayWeight_relayFlow hL]
      exact relayRaw_relayFlow_ge hL hs₀ hfree hs1 hs2
  rw [hgrp, hreg, hy2]
  unfold relayLo relayHi at *
  linarith

/-- ★★★ **The messenger is flipped**: `3·10⁻³` after the crossing it is within `√(2.34·10⁻⁴)` of
`−i σ_y ψ(s₀)`, the band flip of the free messenger at the crossing. -/
theorem sqNorm_mess_flip_le {s₀ : ℝ} (hs₀ : |s₀ - relayTk| ≤ 428 * 10 ^ 9)
    (hfree : relayFlow s₀ (relayPrep L) = (relayState s₀, relayLo)) :
    sqNorm (mess (relayFlow (s₀ + 3 / 1000) (relayPrep L)).1
        - (-I) • (spinY *ᵥ imagePacket (s₀ - 4 * 10 ^ 12)))
      ≤ (3 / 1000) ^ 2 * 26 := by
  have h := sqNorm_mess_relayFlow_sub_le hL hfree (u := 3 / 1000) (by norm_num)
  have hint : (∫ s in (0 : ℝ)..3 / 1000, relayGate relayLo relayHi relayWeight
      (relayFlow (s₀ + s) (relayPrep L)).1 (relayFlow (s₀ + s) (relayPrep L)).2)
      = Real.pi / 2 := by
    simp only [relayFlow]
    rw [integral_relayGate_eq relayLipschitz continuous_relayWeight (relayPrep L) s₀ (3 / 1000)]
    change pulseStep relayLo relayHi (relayFlow (s₀ + 3 / 1000) (relayPrep L)).2
      - pulseStep relayLo relayHi (relayFlow s₀ (relayPrep L)).2 = Real.pi / 2
    rw [pulseStep_eq_of_ge relayLo_lt_relayHi (relayReg_after_pulse hL hs₀ hfree), hfree,
      pulseStep_eq_zero_of_le relayLo_lt_relayHi le_rfl, sub_zero]
  rw [hint, gateRot_pi_div_two_mulVec] at h
  exact h

/-! #### After the pulse: the messenger runs back -/

/-- ★★★ **After the pulse the messenger runs backward from `B`**: for every `t ≥ s₀ + 3·10⁻³`
it is within `√(2.34·10⁻⁴)` of `−i σ_y ψ_free(2 s₀ + 3·10⁻³ − t)` — the free messenger's past, so
it retraces its path to `A` at `4/5`. -/
theorem sqNorm_mess_return_le {s₀ : ℝ} (hs₀ : |s₀ - relayTk| ≤ 428 * 10 ^ 9)
    (hfree : relayFlow s₀ (relayPrep L) = (relayState s₀, relayLo)) {t : ℝ}
    (ht : s₀ + 3 / 1000 ≤ t) :
    sqNorm (mess (relayFlow t (relayPrep L)).1
        - (-I) • (spinY *ᵥ imagePacket (2 * s₀ + 3 / 1000 - 4 * 10 ^ 12 - t)))
      ≤ (3 / 1000) ^ 2 * 26 := by
  set D : ℝ → ZMod L × Fin 2 → ℂ := fun u => mess (relayFlow u (relayPrep L)).1
    - (-I) • (spinY *ᵥ imagePacket (2 * s₀ + 3 / 1000 - 4 * 10 ^ 12 - u)) with hDdef
  have hD : ∀ u ∈ Icc (s₀ + 3 / 1000) t,
      HasDerivAt D ((-I) • (diracHam (relayHop L) 3 *ᵥ D u)) u := by
    intro u hu
    have hreg : relayHi ≤ (relayFlow u (relayPrep L)).2 :=
      (relayReg_after_pulse hL hs₀ hfree).trans (relayFlow_register_mono hu.1)
    have hc : relayGate relayLo relayHi relayWeight (relayFlow u (relayPrep L)).1
        (relayFlow u (relayPrep L)).2 = 0 := relayGate_eq_zero_of_ge relayLo_lt_relayHi _ _ hreg
    have h1 := hasDerivAt_gatedFlow_gateBlock relayLipschitz (k₀ := 4) (relayPrep L) u
    change HasDerivAt (fun u => mess (relayFlow u (relayPrep L)).1)
      ((-I) • ((diracHam (relayHop L) (relayMass 4) + ((relayGate relayLo relayHi relayWeight
        (relayFlow u (relayPrep L)).1 (relayFlow u (relayPrep L)).2 : ℝ) : ℂ) • spinY)
          *ᵥ mess (relayFlow u (relayPrep L)).1)) u at h1
    rw [relayMass_four, hc, Complex.ofReal_zero, zero_smul, add_zero] at h1
    have hp := (hasDerivAt_packet (L := L) (relayHop L) 3 imageWin
      (unitAmp L (relayHop L) 3 twinAmp) (2 * s₀ + 3 / 1000 - 4 * 10 ^ 12 - u)).comp_const_sub
      (2 * s₀ + 3 / 1000 - 4 * 10 ^ 12) u
    have h2 := (hasDerivAt_mulVec spinY hp).const_smul (-I)
    have h2' : HasDerivAt
        (fun u => (-I) • (spinY *ᵥ imagePacket (L := L) (2 * s₀ + 3 / 1000 - 4 * 10 ^ 12 - u)))
        ((-I) • (diracHam (relayHop L) 3
          *ᵥ ((-I) • (spinY *ᵥ imagePacket (2 * s₀ + 3 / 1000 - 4 * 10 ^ 12 - u))))) u := by
      simp only [imagePacket, ringPacket]
      simp only [relayHop] at h2 ⊢
      refine h2.congr_deriv ?_
      rw [Matrix.mulVec_neg, Matrix.mulVec_smul, spinY_mulVec_diracHam_mulVec, Matrix.mulVec_smul]
      funext i
      simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      ring
    refine (h1.sub h2').congr_deriv ?_
    rw [Matrix.mulVec_sub, smul_sub]
  have h := sqNorm_eq_of_hasDerivAt_Icc (diracHam_isHermitian (relayHop L) 3) ht hD
  have e : D (s₀ + 3 / 1000) = mess (relayFlow (s₀ + 3 / 1000) (relayPrep L)).1
      - (-I) • (spinY *ᵥ imagePacket (s₀ - 4 * 10 ^ 12)) := by
    simp only [hDdef]
    congr 4
    ring
  rw [e] at h
  change sqNorm (D t) ≤ _
  rw [h]
  exact sqNorm_mess_flip_le hL hs₀ hfree

/-! #### The bundle -/

/-- ★★★ **The relay arena** (BACKLOG #274, third landing). On the Dirac chain of #256 — `A` at rest,
`B` approaching at `3/5`, the messenger launched from `A` at `4/5` — with `B` carrying a relay
register fed by the clipped encounter weight and a gate `c = Φ'(r) · w` that pulses `σ_y` on the
messenger, the whole is **one gated flow** (`relayFlow`, with the two-time law of
`gatedEvolve`), and:

* `A`'s and `B`'s devices evolve freely for all time, and the total weight is `3`;
* along the orbit the gate is `Φ'(r)` times the clipped encounter weight — the saturation is
  invisible;
* there is a crossing time `s₀` within `4.28·10¹¹` of #256's reception time `t_k` at which the
  register reaches `3·10¹¹`, and up to `s₀` the orbit is the free trajectory with the free register;
* `3·10⁻³` later the register has passed `3·10¹¹ + 1.2·10⁻³`: the pulse has delivered `π/2`;
* from then on the messenger is within `‖·‖² ≤ 2.34·10⁻⁴` of `−i σ_y ψ_free(2 s₀ + 3·10⁻³ − t)`:
  **the band-flipped free messenger run backward**, which returns to `A` at `4/5`. -/
theorem dirac_relay :
    (∀ s t u : OnticTime, gatedEvolve (relayLipschitz (L := L)) t u ∘ gatedEvolve relayLipschitz s t
      = gatedEvolve relayLipschitz s u)
    ∧ (∀ t, devA (relayFlow t (relayPrep L)).1 = restObserver t)
    ∧ (∀ t, devB (relayFlow t (relayPrep L)).1 = approachObserver (t - 5 * 10 ^ 13))
    ∧ (∀ t, sqNorm (relayFlow t (relayPrep L)).1 = 3)
    ∧ (∀ t, relayGate relayLo relayHi relayWeight (relayFlow t (relayPrep L)).1
        (relayFlow t (relayPrep L)).2
        = pulseRate relayLo relayHi (relayFlow t (relayPrep L)).2 * relayRaw (relayFlow t (relayPrep L)).1)
    ∧ ∃ s₀ ∈ Icc (relayTk - 428 * 10 ^ 9) (relayTk + 428 * 10 ^ 9),
        (∀ t ∈ Icc (0 : ℝ) s₀, relayFlow t (relayPrep L) = (relayState t, relayReg L t))
        ∧ (relayFlow s₀ (relayPrep L)).2 = relayLo
        ∧ relayHi ≤ (relayFlow (s₀ + 3 / 1000) (relayPrep L)).2
        ∧ ∀ t, s₀ + 3 / 1000 ≤ t →
            sqNorm (mess (relayFlow t (relayPrep L)).1
                - (-I) • (spinY *ᵥ imagePacket (2 * s₀ + 3 / 1000 - 4 * 10 ^ 12 - t)))
              ≤ (3 / 1000) ^ 2 * 26 := by
  refine ⟨gatedEvolve_comp _, devA_relayFlow, devB_relayFlow, sqNorm_relayFlow hL, fun t => ?_, ?_⟩
  · rw [relayGate, relayWeight_relayFlow hL]
  · obtain ⟨s₀, hs₀, h₀⟩ := exists_relayCross hL
    have htk : relayTk = 166 * 10 ^ 12 / 7 := rfl
    have hs₀0 : 0 ≤ s₀ := by linarith [hs₀.1]
    have hfreeOn := relayFlow_eq_free hL h₀.le
    have hfree : relayFlow s₀ (relayPrep L) = (relayState s₀, relayLo) := by
      rw [hfreeOn s₀ ⟨hs₀0, le_rfl⟩, h₀]
    have habs : |s₀ - relayTk| ≤ 428 * 10 ^ 9 := by
      rw [abs_le]; constructor <;> linarith [hs₀.1, hs₀.2]
    refine ⟨s₀, hs₀, hfreeOn, by rw [hfree], relayReg_after_pulse hL habs hfree,
      fun t ht => sqNorm_mess_return_le hL habs hfree ht⟩

end WithL

end Arena

end CSD.RecordLayer
