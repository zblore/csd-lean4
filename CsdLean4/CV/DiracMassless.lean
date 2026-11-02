/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.DiracPacketLimit

/-!
# Massless messengers on the Dirac chain

**Category:** 3-Local (CV). BACKLOG #278, first landing (massless route chosen 2026-11-02).

#278 asks for the moving observer's own radar. Massive messengers move at different speeds out and
back in the moving frame, so a radar with them needs calibration; **massless** messengers move at
`c` in the chain's frame to `O((ap)²)`, and a Lorentz-covariant chain would carry that to every
frame. This file builds them. At rest energy `0` the upper-band spinor of every right-moving mode
(lattice angle in `(0, π)`) is `(1, 1)` up to its norm, so neighbouring modes are **exactly**
parallel and the band is `E(θ) = 2J sin θ`, whose group velocity `2J cos θ` is `2J`-Lipschitz with
no `1/μ`: a massless packet moves rigidly at `c cos(ap₀)` with an error rate `c k a (D + k)` that
**vanishes as the spacing shrinks** — there is no spreading term.

## The massless band

* `bandE_zero` (`E(θ) = 2J sin θ` on `[0, π]`), ★ `abs_bandE_zero_step_sub_le` — **the energy step
  between neighbouring momenta is `h · 2J cos θ₀` within `2J h (|θ − θ₀| + h)`**;
  `spinNorm_zero` (`√2 · 2J sin θ`), `spinNorm_zero_pos`, `modeNorm_zero_pos`,
  ★ `spinOverlap_zero` (**neighbouring spinors exactly parallel**: the overlap is the product of
  the norms), `spinCos_zero`.

## The packet

* `RightWindow` (every momentum's angle in `(0, π)`); `norm_transWeight_zero_le`,
  ★ `sum_norm_transWeight_zero_le` (`Σ ‖w_m‖ ≤ ⟨ψ, ψ⟩`), `norm_transPhase_zero_le`;
  `driftErrorZero`, ★★★ `transPhase_drift_zero` — **the massless packet's translation phase rotates
  at `(2π/L) · 2J cos θ₀` within `|t|` times its drift error**; `driftErrorZero_le`;
* `norm_unitAmp_mul_zero`, ★ `chainInner_packet_unitAmp_zero` (normalised),
  `transWeight_unitAmp_zero`, ★★ `re_transPhase_unitAmp_zero` — **the initial localisation
  exactly**: `Re T(0) = Σ β_{m+1} β_m` for real coefficients (no spinor factor).

## Fixed physical length

* `masslessErr` (`c k a (D + k)`), `tendsto_masslessErr` (**→ 0 as `a → 0`**),
  ★ `c_mul_cos_mem` (`c − c(ap₀)²/2 ≤ c cos(ap₀) ≤ c`);
* ★★★ `dirac_massless_limit` — **the capstone**: on a ring of physical length `ℓ`, a normalised
  massless packet of right-moving modes within `D` of `p₀` is normalised at every time and moves at
  `c cos(ap₀)`, within `c(ap₀)²/2` of `c`: its translation phase rotates at `k c cos(ap₀)` within
  `|t| · c k a (D + k)`, its modulus drops by at most that, its phase is within twice that over
  `|T(0)|`; ★★ `flat_massless_localised` — the flat packet of `N` modes has `|T(0)| ≥ 1 − 1/N`.

## The findings

1. **Massless packets do not spread in the scaled limit**: the error rate is `c k a (D + k)`,
   entirely lattice; a massive packet's rate has the spacing-independent spread `k (c²/μ)(D + k)`
   (`dirac_packet_limit`).
2. **They move at `c` to `O((ap₀)²)`** in the chain's frame — the speed the moving observer's radar
   (#278) will assume in its own frame.

## Honest scope

⚠️ **Right-movers only**: angles in `(0, π)` (positive momenta below `π/a`); the left-moving family
is the mirror image (`chainParity_ringPacket`, `DiracReturn.lean`) and is not restated here.

⚠️ **Bounds in the chain's frame.** That massless packets move at `c` in the moving observer's frame
is what #278's later landings test, not an input.

References: `specs/BACKLOG.md` #278, #259, #261, #246, #39; `CV/DiracPacket.lean` (`packet`,
`transPhase_packet`, `transPhase_drift`, `norm_sum_phase_sub_le`, `bandE`, `angleZ_succ`);
`CV/DiracPacketLimit.lean` (`spinOverlap_eq`, `spinNorm`, `modeNorm`, `chainInner_packet_self`,
`sum_filter_succ_mul_le`, `unitAmp`, `spinCos`, `ringPacket`, `dirac_packet_limit`, `flat_sums`,
`norm_mul_norm_div_sub_le`); `CV/DiracContinuum.lean` (`scaledHop`).
-/

@[expose] public section

open Complex

namespace CSD.CV

variable {L : ℕ} [NeZero L]

/-! ### The massless band -/

/-- **The massless band** on `[0, π]`: `E(θ) = 2J sin θ`. -/
theorem bandE_zero {J θ : ℝ} (hJ : 0 ≤ J) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    bandE J 0 θ = 2 * J * Real.sin θ := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi h0 hπ
  rw [bandE, dispE, show (0 : ℝ) ^ 2 + (2 * J * Real.sin θ) ^ 2 = (2 * J * Real.sin θ) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

/-- ★ **The massless energy step**: `E(θ + h) − E(θ)` is `h · 2J cos θ₀` within
`2J h (|θ − θ₀| + h)` — the group velocity `2J cos` is `2J`-Lipschitz, with no `1/μ`. -/
theorem abs_bandE_zero_step_sub_le {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 < h) {θ θ₀ : ℝ}
    (h0 : 0 ≤ θ) (hπ : θ + h ≤ Real.pi) :
    |(bandE J 0 (θ + h) - bandE J 0 θ) - h * (2 * J * Real.cos θ₀)|
      ≤ 2 * J * h * (|θ - θ₀| + h) := by
  rw [bandE_zero hJ (by linarith) hπ, bandE_zero hJ h0 (by linarith)]
  obtain ⟨ξ, hξ, hc⟩ := exists_hasDerivAt_eq_slope Real.sin Real.cos (show θ < θ + h by linarith)
    Real.continuous_sin.continuousOn (fun x _ => Real.hasDerivAt_sin x)
  rw [show θ + h - θ = h by ring, eq_div_iff hh.ne'] at hc
  have e : 2 * J * Real.sin (θ + h) - 2 * J * Real.sin θ - h * (2 * J * Real.cos θ₀)
      = 2 * J * h * (Real.cos ξ - Real.cos θ₀) := by
    rw [← mul_sub, ← hc]
    ring
  rw [e, abs_mul, abs_of_nonneg (by positivity)]
  have hd : |ξ - θ₀| ≤ |θ - θ₀| + h := by
    have := abs_sub_le ξ θ θ₀
    rw [abs_of_pos (by linarith [hξ.1] : 0 < ξ - θ)] at this
    linarith [hξ.2]
  exact mul_le_mul_of_nonneg_left ((Real.abs_cos_sub_cos_le ξ θ₀).trans hd) (by positivity)

/-- The massless spinor's norm: `√2 · 2J sin θ` on `[0, π]`. -/
theorem spinNorm_zero {J θ : ℝ} (hJ : 0 ≤ J) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    spinNorm J 0 θ = Real.sqrt 2 * (2 * J * Real.sin θ) := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi h0 hπ
  rw [spinNorm, bandE_zero hJ h0 hπ, zero_add,
    show (2 * J * Real.sin θ) ^ 2 + (2 * J * Real.sin θ) ^ 2 = 2 * (2 * J * Real.sin θ) ^ 2 by ring,
    Real.sqrt_mul zero_le_two, Real.sqrt_sq (by positivity)]

theorem spinNorm_zero_pos {J θ : ℝ} (hJ : 0 < J) (h0 : 0 < θ) (hπ : θ < Real.pi) :
    0 < spinNorm J 0 θ := by
  rw [spinNorm_zero hJ.le h0.le hπ.le]
  have := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  positivity

/-- **Every momentum's angle in `(0, π)`**: the window of right-movers. -/
def RightWindow (L : ℕ) (W : Finset ℤ) : Prop :=
  ∀ m ∈ W, 0 < angleZ L m ∧ angleZ L m < Real.pi

theorem modeNorm_zero_pos {J : ℝ} (hJ : 0 < J) {m : ℤ} (h0 : 0 < angleZ L m)
    (hπ : angleZ L m < Real.pi) : 0 < modeNorm L J 0 m :=
  mul_pos (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)))
    (spinNorm_zero_pos hJ h0 hπ)

/-- ★ **Massless spinors are exactly parallel**: the overlap of two right-moving modes is the
product of their spinors' norms. -/
theorem spinOverlap_zero {J : ℝ} (hJ : 0 ≤ J) {m' m : ℤ} (h0' : 0 ≤ angleZ L m')
    (hπ' : angleZ L m' ≤ Real.pi) (h0 : 0 ≤ angleZ L m) (hπ : angleZ L m ≤ Real.pi) :
    spinOverlap (L := L) J 0 0 m' m
      = ((spinNorm J 0 (angleZ L m') * spinNorm J 0 (angleZ L m) : ℝ) : ℂ) := by
  rw [spinOverlap_eq, bandE_zero hJ h0' hπ', bandE_zero hJ h0 hπ, spinNorm_zero hJ h0' hπ',
    spinNorm_zero hJ h0 hπ]
  congr 1
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt zero_le_two
  linear_combination (-(2 * J * Real.sin (angleZ L m')) * (2 * J * Real.sin (angleZ L m))) * h2

/-- The cosine between massless spinors is `1`. -/
theorem spinCos_zero {J θ' θ : ℝ} (hJ : 0 < J) (h0' : 0 < θ') (hπ' : θ' < Real.pi) (h0 : 0 < θ)
    (hπ : θ < Real.pi) : spinCos J 0 θ' θ = 1 := by
  have hN := mul_pos (spinNorm_zero_pos hJ h0' hπ') (spinNorm_zero_pos hJ h0 hπ)
  rw [spinCos, div_eq_one_iff_eq hN.ne', bandE_zero hJ.le h0'.le hπ'.le,
    bandE_zero hJ.le h0.le hπ.le, spinNorm_zero hJ.le h0'.le hπ'.le,
    spinNorm_zero hJ.le h0.le hπ.le]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt zero_le_two
  linear_combination (-(2 * J * Real.sin θ') * (2 * J * Real.sin θ)) * h2

/-! ### The packet -/

/-- Cauchy–Schwarz for a neighbouring massless pair (an equality here). -/
theorem norm_transWeight_zero_le {J : ℝ} (hJ : 0 ≤ J) (a : ℤ → ℂ) {m : ℤ}
    (h0' : 0 ≤ angleZ L (m + 1)) (hπ' : angleZ L (m + 1) ≤ Real.pi) (h0 : 0 ≤ angleZ L m)
    (hπ : angleZ L m ≤ Real.pi) :
    ‖transWeight (L := L) J 0 a m‖
      ≤ (‖a (m + 1)‖ * modeNorm L J 0 (m + 1)) * (‖a m‖ * modeNorm L J 0 m) := by
  have hL : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (Nat.cast_nonneg L)
  have hn' : 0 ≤ spinNorm J 0 (angleZ L (m + 1)) := Real.sqrt_nonneg _
  have hn : 0 ≤ spinNorm J 0 (angleZ L m) := Real.sqrt_nonneg _
  rw [transWeight, spinOverlap_zero hJ h0' hπ' h0 hπ, norm_mul, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hn' hn), norm_star,
    Complex.norm_natCast, modeNorm, modeNorm]
  apply le_of_eq
  linear_combination (-(‖a (m + 1)‖ * ‖a m‖ * spinNorm J 0 (angleZ L (m + 1))
    * spinNorm J 0 (angleZ L m))) * hL

/-- ★ **The massless translation weights are bounded by the squared norm.** -/
theorem sum_norm_transWeight_zero_le {J : ℝ} (hJ : 0 ≤ J) {W : Finset ℤ} (hR : RightWindow L W)
    (hD : Distinct L W) (a : ℤ → ℂ) (t : ℝ) :
    ∑ m ∈ W.filter (fun m => m + 1 ∈ W), ‖transWeight (L := L) J 0 a m‖
      ≤ ‖chainInner (packet (L := L) J 0 W a t) (packet (L := L) J 0 W a t)‖ := by
  rw [chainInner_packet_self J 0 hD a t, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  refine (Finset.sum_le_sum fun m hm => ?_).trans
    (sum_filter_succ_mul_le W fun m => ‖a m‖ * modeNorm L J 0 m)
  obtain ⟨hmW, hm1W⟩ := Finset.mem_filter.1 hm
  exact norm_transWeight_zero_le hJ a (hR _ hm1W).1.le (hR _ hm1W).2.le (hR _ hmW).1.le
    (hR _ hmW).2.le

theorem norm_transPhase_zero_le {J : ℝ} (hJ : 0 ≤ J) {W : Finset ℤ} (hR : RightWindow L W)
    (hW : NoWrap L W) (hD : Distinct L W) (a : ℤ → ℂ) (t : ℝ) :
    ‖transPhase (packet (L := L) J 0 W a t)‖
      ≤ ‖chainInner (packet (L := L) J 0 W a t) (packet (L := L) J 0 W a t)‖ := by
  rw [transPhase_packet J 0 hW a t]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun m _ => ?_).trans
    (sum_norm_transWeight_zero_le hJ hR hD a t))
  rw [norm_mul, norm_exp_I_mul_ofReal_mul, mul_one]

/-- **The massless drift error**: `|t|` times the weighted spread of the window's energy steps. -/
noncomputable def driftErrorZero (J : ℝ) (W : Finset ℤ) (a : ℤ → ℂ) (θ₀ : ℝ) : ℝ :=
  ∑ m ∈ W.filter (fun m => m + 1 ∈ W), ‖transWeight (L := L) J 0 a m‖
    * (2 * J * (2 * Real.pi / L) * (|angleZ L m - θ₀| + 2 * Real.pi / L))

/-- ★★★ **The massless packet moves at `2J cos θ₀`**: its translation phase rotates at
`(2π/L) · 2J cos θ₀` within `|t|` times the drift error. -/
theorem transPhase_drift_zero {J : ℝ} (hJ : 0 ≤ J) {W : Finset ℤ} (hR : RightWindow L W)
    (hW : NoWrap L W) (a : ℤ → ℂ) (θ₀ t : ℝ) :
    ‖transPhase (packet (L := L) J 0 W a t)
        - exp (I * (((2 * Real.pi / L * (2 * J * Real.cos θ₀) : ℝ) : ℂ) * t))
          * transPhase (packet (L := L) J 0 W a 0)‖
      ≤ |t| * driftErrorZero (L := L) J W a θ₀ := by
  have hL : (0 : ℝ) < 2 * Real.pi / L := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  rw [transPhase_packet J 0 hW a t, transPhase_packet J 0 hW a 0]
  simp only [mul_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  refine (norm_sum_phase_sub_le _ _ _ _ t).trans ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m hm => ?_) (abs_nonneg t)
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  obtain ⟨hmW, hm1W⟩ := Finset.mem_filter.1 hm
  have h1 := (hR _ hm1W).2
  rw [angleZ_succ] at h1 ⊢
  exact abs_bandE_zero_step_sub_le hJ hL (hR _ hmW).1.le h1.le

/-- The massless drift error of a window within `δ` of `θ₀` is at most `2J h (δ + h) ⟨ψ, ψ⟩`. -/
theorem driftErrorZero_le {J : ℝ} (hJ : 0 ≤ J) {W : Finset ℤ} (hR : RightWindow L W)
    (hD : Distinct L W) (a : ℤ → ℂ) {θ₀ δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ m ∈ W, |angleZ L m - θ₀| ≤ δ) :
    driftErrorZero (L := L) J W a θ₀ ≤ 2 * J * (2 * Real.pi / L) * (δ + 2 * Real.pi / L)
      * ‖chainInner (packet (L := L) J 0 W a 0) (packet (L := L) J 0 W a 0)‖ := by
  have hC : 0 ≤ 2 * J * (2 * Real.pi / L) := by positivity
  rw [driftErrorZero]
  calc ∑ m ∈ W.filter (fun m => m + 1 ∈ W), ‖transWeight (L := L) J 0 a m‖
        * (2 * J * (2 * Real.pi / L) * (|angleZ L m - θ₀| + 2 * Real.pi / L))
      ≤ ∑ m ∈ W.filter (fun m => m + 1 ∈ W), ‖transWeight (L := L) J 0 a m‖
        * (2 * J * (2 * Real.pi / L) * (δ + 2 * Real.pi / L)) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have := hδ m (Finset.mem_filter.1 hm).1
        gcongr
    _ = (∑ m ∈ W.filter (fun m => m + 1 ∈ W), ‖transWeight (L := L) J 0 a m‖)
        * (2 * J * (2 * Real.pi / L) * (δ + 2 * Real.pi / L)) := by rw [Finset.sum_mul]
    _ ≤ ‖chainInner (packet (L := L) J 0 W a 0) (packet (L := L) J 0 W a 0)‖
        * (2 * J * (2 * Real.pi / L) * (δ + 2 * Real.pi / L)) :=
        mul_le_mul_of_nonneg_right (sum_norm_transWeight_zero_le hJ hR hD a 0) (by positivity)
    _ = _ := mul_comm _ _

theorem norm_unitAmp_mul_zero {J : ℝ} (hJ : 0 < J) (β : ℤ → ℂ) {m : ℤ} (h0 : 0 < angleZ L m)
    (hπ : angleZ L m < Real.pi) : ‖unitAmp L J 0 β m‖ * modeNorm L J 0 m = ‖β m‖ := by
  have h := modeNorm_zero_pos (L := L) hJ h0 hπ
  rw [unitAmp, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h,
    div_mul_cancel₀ _ h.ne']

/-- ★ **A normalised massless packet**: `⟨ψ(t), ψ(t)⟩ = Σ |β_m|²`. -/
theorem chainInner_packet_unitAmp_zero {J : ℝ} (hJ : 0 < J) {W : Finset ℤ} (hR : RightWindow L W)
    (hD : Distinct L W) (β : ℤ → ℂ) (t : ℝ) :
    chainInner (packet (L := L) J 0 W (unitAmp L J 0 β) t)
        (packet (L := L) J 0 W (unitAmp L J 0 β) t)
      = ((∑ m ∈ W, ‖β m‖ ^ 2 : ℝ) : ℂ) := by
  rw [chainInner_packet_self J 0 hD]
  congr 1
  exact Finset.sum_congr rfl fun m hm => by
    rw [norm_unitAmp_mul_zero hJ β (hR m hm).1 (hR m hm).2]

theorem transWeight_unitAmp_zero {J : ℝ} (hJ : 0 < J) (β : ℤ → ℂ) {m : ℤ}
    (h0' : 0 < angleZ L (m + 1)) (hπ' : angleZ L (m + 1) < Real.pi) (h0 : 0 < angleZ L m)
    (hπ : angleZ L m < Real.pi) :
    transWeight (L := L) J 0 (unitAmp L J 0 β) m = star (β (m + 1)) * β m := by
  have h1 := spinNorm_zero_pos hJ h0' hπ'
  have h0n := spinNorm_zero_pos hJ h0 hπ
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hs : ((Real.sqrt L : ℝ) : ℂ) ^ 2 = (L : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hL.le]
    push_cast
    rfl
  have hs0 : ((Real.sqrt L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hL).ne'
  have h1' : ((spinNorm J 0 (angleZ L (m + 1)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1.ne'
  have hz0 : ((spinNorm J 0 (angleZ L m) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0n.ne'
  rw [transWeight, spinOverlap_zero hJ.le h0'.le hπ'.le h0.le hπ.le, unitAmp, unitAmp, modeNorm,
    modeNorm]
  simp only [Complex.star_def, map_div₀, Complex.conj_ofReal]
  push_cast
  rw [← hs]
  field_simp

/-- ★★ **The massless initial localisation, exactly**: for real coefficients,
`Re T(0) = Σ_m β_{m+1} β_m`. -/
theorem re_transPhase_unitAmp_zero {J : ℝ} (hJ : 0 < J) {W : Finset ℤ} (hR : RightWindow L W)
    (hW : NoWrap L W) (β : ℤ → ℝ) :
    (transPhase (packet (L := L) J 0 W (unitAmp L J 0 fun m => (β m : ℂ)) 0)).re
      = ∑ m ∈ W.filter (fun m => m + 1 ∈ W), β (m + 1) * β m := by
  rw [transPhase_packet J 0 hW _ 0, Complex.re_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨hmW, hm1W⟩ := Finset.mem_filter.1 hm
  rw [Complex.ofReal_zero, mul_zero, mul_zero, Complex.exp_zero, mul_one,
    transWeight_unitAmp_zero hJ _ (hR _ hm1W).1 (hR _ hm1W).2 (hR _ hmW).1 (hR _ hmW).2,
    Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]

/-! ### Fixed physical length -/

/-- **The massless error rate** `c k a (D + k)`, `k = 2π/ℓ`: entirely lattice. -/
noncomputable def masslessErr (c ℓ D a : ℝ) : ℝ := c * (2 * Real.pi / ℓ) * a * (D + 2 * Real.pi / ℓ)

/-- **It vanishes with the spacing.** -/
theorem tendsto_masslessErr (c ℓ D : ℝ) :
    Filter.Tendsto (masslessErr c ℓ D) (nhds 0) (nhds 0) := by
  have h : Continuous (masslessErr c ℓ D) := by
    unfold masslessErr
    fun_prop
  simpa [masslessErr] using h.tendsto 0

/-- ★ **The massless speed is `c` to `O((ap₀)²)`**: `c − c(ap₀)²/2 ≤ c cos(ap₀) ≤ c`. -/
theorem c_mul_cos_mem {c x : ℝ} (hc : 0 ≤ c) :
    c - c * x ^ 2 / 2 ≤ c * Real.cos x ∧ c * Real.cos x ≤ c := by
  have h1 := Real.one_sub_sq_div_two_le_cos (x := x)
  have h2 := Real.cos_le_one x
  constructor <;> nlinarith

/-- ★★★ **A massless packet of fixed physical width (#278, first landing).** On a ring of physical
length `ℓ` with `L` sites, spacing `a = ℓ/L`, hop `J = c/(2a)`, take right-moving modes (angles in
`(0, π)`) on a window shorter than the ring, with physical momenta within `D` of `p₀`, and
coefficients with `Σ |β_m|² = 1`. Then the massless packet is normalised at every time,
`|T(0)| ≤ 1`, it moves at `c cos(ap₀)` — within `c(ap₀)²/2` of `c` — its translation phase
rotating at `k c cos(ap₀)` within `|t| · c k a (D + k)`, its modulus dropping by at most that
and its phase within twice that over `|T(0)|`. -/
theorem dirac_massless_limit {c ℓ D p₀ : ℝ} (hc : 0 < c) (hℓ : 0 < ℓ) (hD0 : 0 ≤ D)
    {W : Finset ℤ} {lo : ℤ} (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L) (hR : RightWindow L W)
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D)
    (β : ℤ → ℂ) (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) :
    (∀ t, chainInner (ringPacket (L := L) c 0 ℓ W β t) (ringPacket (L := L) c 0 ℓ W β t) = 1)
    ∧ ‖transPhase (ringPacket (L := L) c 0 ℓ W β 0)‖ ≤ 1
    ∧ (c - c * (ℓ / L * p₀) ^ 2 / 2 ≤ c * Real.cos (ℓ / L * p₀) ∧ c * Real.cos (ℓ / L * p₀) ≤ c)
    ∧ (∀ t, ‖transPhase (ringPacket (L := L) c 0 ℓ W β t)
        - exp (I * (((2 * Real.pi / ℓ * (c * Real.cos (ℓ / L * p₀)) : ℝ) : ℂ) * t))
          * transPhase (ringPacket (L := L) c 0 ℓ W β 0)‖
        ≤ |t| * masslessErr c ℓ D (ℓ / L))
    ∧ (∀ t, ‖transPhase (ringPacket (L := L) c 0 ℓ W β 0)‖ - |t| * masslessErr c ℓ D (ℓ / L)
        ≤ ‖transPhase (ringPacket (L := L) c 0 ℓ W β t)‖)
    ∧ (∀ t, ‖transPhase (ringPacket (L := L) c 0 ℓ W β 0)‖
        * ‖transPhase (ringPacket (L := L) c 0 ℓ W β t)
            / (‖transPhase (ringPacket (L := L) c 0 ℓ W β t)‖ : ℂ)
          - exp (I * (((2 * Real.pi / ℓ * (c * Real.cos (ℓ / L * p₀)) : ℝ) : ℂ) * t))
            * (transPhase (ringPacket (L := L) c 0 ℓ W β 0)
              / (‖transPhase (ringPacket (L := L) c 0 ℓ W β 0)‖ : ℂ))‖
        ≤ 2 * (|t| * masslessErr c ℓ D (ℓ / L))) := by
  obtain ⟨hW, hDst⟩ := noWrap_distinct_of_window (L := L) hWin
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set a := ℓ / L with ha_def
  have ha : 0 < a := div_pos hℓ hL
  set k := 2 * Real.pi / ℓ with hk_def
  set J := scaledHop c a
  have hJ : 0 < J := by
    show 0 < scaledHop c a
    unfold scaledHop
    positivity
  set T : ℝ → ℂ := fun t => transPhase (ringPacket (L := L) c 0 ℓ W β t) with hT
  have hnorm : ∀ t, chainInner (ringPacket (L := L) c 0 ℓ W β t)
      (ringPacket (L := L) c 0 ℓ W β t) = 1 := fun t => by
    rw [ringPacket, chainInner_packet_unitAmp_zero hJ hR hDst, hβ, Complex.ofReal_one]
  have hT0 : ‖T 0‖ ≤ 1 := by
    have h := norm_transPhase_zero_le (L := L) (J := J) hJ.le hR hW hDst (unitAmp L J 0 β) 0
    have h1 := hnorm 0
    rw [ringPacket] at h1
    rw [h1, norm_one] at h
    exact h
  have hstep : 2 * Real.pi / L = a * k := by
    rw [ha_def, hk_def]
    field_simp
  have hδ : ∀ m ∈ W, |angleZ L m - a * p₀| ≤ a * D := fun m hm => by
    rw [angleZ_div_spacing hℓ.ne' hL.ne', ← mul_sub, abs_mul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left (hWD m hm) ha.le
  have hJa : 2 * J * a = c := by
    show 2 * scaledHop c a * a = c
    unfold scaledHop
    field_simp
  have hmain : ∀ t : ℝ, ‖T t - exp (I * (((k * (c * Real.cos (a * p₀)) : ℝ) : ℂ) * t)) * T 0‖
      ≤ |t| * masslessErr c ℓ D a := fun t => by
    have h := transPhase_drift_zero (L := L) (J := J) hJ.le hR hW (unitAmp L J 0 β) (a * p₀) t
    have hrate : 2 * Real.pi / L * (2 * J * Real.cos (a * p₀)) = k * (c * Real.cos (a * p₀)) := by
      rw [hstep, ← hJa]
      ring
    rw [hrate] at h
    have he := driftErrorZero_le (L := L) (J := J) hJ.le hR hDst (unitAmp L J 0 β)
      (mul_nonneg ha.le hD0) hδ
    have h1 := hnorm 0
    rw [ringPacket] at h1
    rw [h1, norm_one, mul_one, hstep] at he
    refine h.trans (mul_le_mul_of_nonneg_left (he.trans (le_of_eq ?_)) (abs_nonneg t))
    rw [masslessErr, ← hJa]
    ring
  refine ⟨hnorm, hT0, c_mul_cos_mem hc.le, hmain, fun t => ?_, fun t => ?_⟩
  · have h2 := norm_sub_norm_le (exp (I * (((k * (c * Real.cos (a * p₀)) : ℝ) : ℂ) * t)) * T 0)
      (T t)
    rw [norm_mul, norm_exp_I_mul_ofReal_mul, one_mul, norm_sub_rev] at h2
    linarith [hmain t]
  · have h := norm_mul_norm_div_sub_le (T t)
      (exp (I * (((k * (c * Real.cos (a * p₀)) : ℝ) : ℂ) * t)) * T 0)
    have hn : ‖exp (I * (((k * (c * Real.cos (a * p₀)) : ℝ) : ℂ) * t)) * T 0‖ = ‖T 0‖ := by
      rw [norm_mul, norm_exp_I_mul_ofReal_mul, one_mul]
    rw [hn, mul_div_assoc] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hmain t) two_pos.le)

/-- ★★ **A flat massless packet of `N` neighbouring right-moving modes starts localised**:
`|T(0)| ≥ 1 − 1/N`, whatever the number of sites. -/
theorem flat_massless_localised {c ℓ : ℝ} (hc : 0 < c) (hℓ : 0 < ℓ) (lo : ℤ) {N : ℕ}
    (hN : 0 < N) (hNL : N < L) (hR : RightWindow L (Finset.Ico lo (lo + N))) :
    ∑ _m ∈ Finset.Ico lo (lo + N), ‖((1 / Real.sqrt N : ℝ) : ℂ)‖ ^ 2 = 1
    ∧ 1 - 1 / (N : ℝ)
      ≤ ‖transPhase (ringPacket (L := L) c 0 ℓ (Finset.Ico lo (lo + N))
          (fun _ => ((1 / Real.sqrt N : ℝ) : ℂ)) 0)‖ := by
  obtain ⟨h1, h2⟩ := flat_sums lo hN
  have hpos : 0 ≤ 1 / Real.sqrt N := by positivity
  refine ⟨by simpa [Complex.norm_real, abs_of_nonneg hpos] using h1, ?_⟩
  obtain ⟨hW, -⟩ := noWrap_distinct_of_window (L := L) (W := Finset.Ico lo (lo + N)) (lo := lo)
    (fun m hm => by
      rw [Finset.mem_Ico] at hm
      constructor <;> omega)
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hJ : 0 < scaledHop c (ℓ / L) := by
    unfold scaledHop
    positivity
  have h := re_transPhase_unitAmp_zero (L := L) (J := scaledHop c (ℓ / L)) hJ hR hW
    (fun _ => 1 / Real.sqrt N)
  rw [h2] at h
  rw [ringPacket]
  exact h.symm.le.trans (Complex.re_le_norm _)

end CSD.CV

end
