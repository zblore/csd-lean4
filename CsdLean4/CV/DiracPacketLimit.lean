/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.DiracContinuum

/-!
# A Dirac packet of fixed physical width in the scaled limit

**Category:** 3-Local (CV). BACKLOG #261 (residue of ~~#260~~; first brick in `DiracPacket.lean` and
`DiracContinuum.lean`).

~~#250~~'s packet moves at the group velocity within `|t|` times a drift error weighted by
`Σ_m ‖w_m‖`, and stays localised within the same error from its initial `|T(0)|`. #261's first brick
made the curvature constant spacing-independent (`c²/μ`). This file closes the rest: it bounds the
weights by the packet's norm, normalises the packet, bounds its initial localisation below, and
states the drift on a ring of **fixed physical length `ℓ`** as the number of sites `L` grows, so the
spacing `a = ℓ/L` shrinks while every mode keeps its physical momentum `2πm/ℓ`.

## Neighbouring spinors

* `spinSlope`, `hasDerivAt_spinSlope`, ★ `abs_spinSlope_sub_le` — the slope `s/(μ + E(s))` of the
  upper-band spinor `u(s) = (μ + E(s), s)` is `1/(2μ)`-Lipschitz;
* ★★★ `spin_align` — **two upper-band spinors are nearly parallel**: `u(s) · u(t) > 0` and
  `(1 − (s − t)²/(4μ²)) ‖u(s)‖ ‖u(t)‖ ≤ u(s) · u(t) ≤ ‖u(s)‖ ‖u(t)‖` (the upper bound is
  Cauchy–Schwarz; the lower one is Lagrange's identity with the slope bound).

## The packet's norm bounds its translation phase

* `spinOverlap_eq`, `spinNorm`, `sq_spinNorm`, `spinNorm_pos`, `modeNorm` (the mode's norm
  `√L ‖u‖`), `modeNorm_pos`, `clockWeight_self`; ★★ `chainInner_packet_self` — **the packet's squared norm is
  `Σ_m (|a_m| ‖mode_m‖)²` at every time**;
* ★★ `norm_transWeight_le` — each weight is at most the product of its two modes' amplitudes times
  norms; `sum_filter_succ_mul_le`; ★★★ `sum_norm_transWeight_le` — **`Σ_m ‖w_m‖ ≤ ⟨ψ, ψ⟩`**;
  `norm_exp_I_mul_ofReal_mul`, ★★ `norm_transPhase_le` (`|T| ≤ ⟨ψ, ψ⟩`), ★★ `driftError_le` — the
  drift error of a window within `δ` of `θ₀` is at most `vgLip · h (δ + h) ⟨ψ, ψ⟩`, `h = 2π/L`.

## Normalised packets and their initial localisation

* `unitAmp` (amplitudes `β_m/‖mode_m‖`, coefficients in the orthonormal basis of modes),
  `norm_unitAmp_mul`, ★★ `chainInner_packet_unitAmp` — `⟨ψ(t), ψ(t)⟩ = Σ |β_m|²`;
* `spinCos`, ★★ `one_sub_le_spinCos` (`cos ∠(u(θ'), u(θ)) ≥ 1 − (J(θ' − θ)/μ)²`),
  `transWeight_unitAmp`; ★★★ `re_transPhase_unitAmp_ge` — **for real nonnegative coefficients,
  `Re T(0) ≥ (1 − (2πJ/(Lμ))²) Σ_m β_{m+1} β_m`**;
* `filter_succ_Ico`, ★★ `flat_sums` — the flat packet on `N` neighbouring modes has `Σ β² = 1` and
  `Σ β_{m+1} β_m = 1 − 1/N`.

## Fixed physical length

* ★★ `norm_mul_norm_div_sub_le` — close complex numbers have close phases:
  `‖w‖ ‖z/‖z‖ − w/‖w‖‖ ≤ 2‖z − w‖` (the phase of `T` is the circular position times `k`);
* `ringPacket` (the packet on `L` sites at spacing `ℓ/L`, hop `J = c/(2a)`, normalised
  coefficients), `limitErr`, ★★ `tendsto_limitErr` — the lattice part of the error rate vanishes as
  `a → 0`; `angleZ_div_spacing`;
* ★★★ `dirac_packet_limit` — **the capstone**: for coefficients with `Σ |β_m|² = 1` on a window
  shorter than the ring, physical momenta within `D` of `p₀`, `|p₀| ≤ P`, the packet is normalised
  at every time, `|T(0)| ≤ 1`, and with `k = 2π/ℓ` and `v = c²p₀/√(μ² + c²p₀²)`,
  `‖T(t) − e^{ikvt} T(0)‖ ≤ |t| · limitErr`, `|T(t)| ≥ |T(0)| − |t| · limitErr`, and
  `|T(0)| · ‖T(t)/|T(t)| − e^{ikvt} T(0)/|T(0)|‖ ≤ 2|t| · limitErr`, where
  `limitErr = k ((c²/μ)(D + k) + a² (cP²/2 + c²P³/(6μ)))`;
* ★★★ `ringPacket_localised` — **its initial localisation does not depend on `L`**: for real
  nonnegative coefficients, `|T(0)| ≥ (1 − (πc/(ℓμ))²) Σ_m β_{m+1} β_m`; ★★★
  `flat_packet_localised` — the flat packet on `N < L` modes is normalised and has
  `|T(0)| ≥ (1 − (πc/(ℓμ))²)(1 − 1/N)`.

## The findings

1. **The packet, not only its modes, has the relativistic drift in the scaled limit.** On a ring of
   fixed physical length, a normalised packet's translation phase rotates at `k v(p₀)`, the
   relativistic velocity, within an error rate uniform in the spacing; the lattice's share of it is
   `O(a²)` (`tendsto_limitErr`).
2. **What does not vanish is the packet's own spread**, `k (c²/μ)(D + k)`: the window's momentum
   spread `D` times the curvature `c²/μ`, the dispersion of any relativistic packet of that width.
   A narrower window means a smaller spread but, by the flat example, a weaker localisation; the
   horizon over which both hold is finite and explicit.
3. **The initial localisation is spacing-independent.** Neighbouring spinors stay parallel to within
   `(πc/(ℓμ))²`, a property of the ring's length against the Compton length, not of the lattice.

## Honest scope

⚠️ **Position is circular.** `T`'s phase is the circular position times `k = 2π/ℓ`; the bound is on
the chord `‖e^{ikX(t)} − e^{ik(X(0) + vt)}‖`, which is `k` times the position error when that error
is small. A linear position and the infinite line (`ℓ → ∞`, where `k → 0`) are not treated.

⚠️ **The error is linear in `t`** and is not a spreading law; it is an upper bound. The flat packet
is the only instance whose localisation is computed; a Gaussian packet and an optimised width–horizon
trade-off are not.

⚠️ **The lower bound on `|T(0)|` is useful only when `πc < ℓμ`**: the ring must be longer than `π`
Compton lengths `c/μ`.

⚠️ **One mass, no clock, no records.** The packet carries one rest energy `μ`; the two-level clock
transported as the same device and read as a phase is #262; the detector readout is #252. The
finite-level residue `2Δ/μ` of ~~#260~~ is untouched.

References: `specs/BACKLOG.md` #261, #260, #250, #262, #252, #39; `CV/DiracPacket.lean` (`packet`,
`transPhase`, `transPhase_packet`, `transWeight`, `clockOverlap_eq`, `transPhase_drift`,
`driftError`, `vgLip`, `noWrap_distinct_of_window`); `CV/DiracContinuum.lean` (`scaledHop`,
`scaledV`, `abs_scaledV_sub_le`, `vgLip_scaledHop_step`); R. Resta, PRL 80 (1998) 1800 (the position
on a ring as a phase).
-/

@[expose] public section

open Complex

noncomputable section

namespace CSD.CV

/-! ### Neighbouring spinors are nearly parallel -/

/-- The slope of the upper-band spinor `(μ + E(s), s)`: `s/(μ + E(s))`. -/
def spinSlope (μ s : ℝ) : ℝ := s / (μ + dispE μ s)

theorem hasDerivAt_spinSlope {μ : ℝ} (hμ : 0 < μ) (s : ℝ) :
    HasDerivAt (spinSlope μ) (μ / (dispE μ s * (μ + dispE μ s))) s := by
  have hE := dispE_pos hμ s
  have hx : 0 < μ + dispE μ s := by linarith
  have h := (hasDerivAt_id s).div ((hasDerivAt_dispE hμ s).const_add μ) hx.ne'
  convert h using 1
  · funext x
    rfl
  · rw [id]
    field_simp
    linear_combination (-1 : ℝ) * dispE_sq μ s

/-- ★ **The spinor's slope is `1/(2μ)`-Lipschitz.** -/
theorem abs_spinSlope_sub_le {μ : ℝ} (hμ : 0 < μ) (s t : ℝ) :
    |spinSlope μ s - spinSlope μ t| ≤ |s - t| / (2 * μ) := by
  have hder : ∀ x, |μ / (dispE μ x * (μ + dispE μ x))| ≤ 1 / (2 * μ) := fun x => by
    have hE := dispE_pos hμ x
    have hμE := le_dispE μ x
    rw [abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul hμE (add_le_add_left hμE μ) (by linarith) hE.le]
  have key : ∀ a b : ℝ, a < b → |spinSlope μ b - spinSlope μ a| ≤ |b - a| / (2 * μ) := by
    intro a b hab
    obtain ⟨x, _, hx⟩ := exists_hasDerivAt_eq_slope (spinSlope μ)
      (fun x => μ / (dispE μ x * (μ + dispE μ x))) hab
      (fun x _ => (hasDerivAt_spinSlope hμ x).continuousAt.continuousWithinAt)
      (fun x _ => hasDerivAt_spinSlope hμ x)
    have hne : b - a ≠ 0 := by linarith
    rw [eq_div_iff hne] at hx
    rw [← hx, abs_mul, mul_comm]
    calc |b - a| * |μ / (dispE μ x * (μ + dispE μ x))| ≤ |b - a| * (1 / (2 * μ)) :=
          mul_le_mul_of_nonneg_left (hder x) (abs_nonneg _)
      _ = |b - a| / (2 * μ) := by ring
  rcases lt_trichotomy s t with h | rfl | h
  · rw [abs_sub_comm, abs_sub_comm s t]
    exact key s t h
  · simp
  · exact key t s h

/-- ★★★ **Two upper-band spinors are nearly parallel**: for `u(s) = (μ + E(s), s)`,
`0 < u(s) · u(t)` and `(1 − (s − t)²/(4μ²)) ‖u(s)‖ ‖u(t)‖ ≤ u(s) · u(t) ≤ ‖u(s)‖ ‖u(t)‖`. -/
theorem spin_align {μ : ℝ} (hμ : 0 < μ) (s t : ℝ) :
    0 < (μ + dispE μ s) * (μ + dispE μ t) + s * t
    ∧ (1 - (s - t) ^ 2 / (4 * μ ^ 2))
        * (Real.sqrt ((μ + dispE μ s) ^ 2 + s ^ 2) * Real.sqrt ((μ + dispE μ t) ^ 2 + t ^ 2))
      ≤ (μ + dispE μ s) * (μ + dispE μ t) + s * t
    ∧ (μ + dispE μ s) * (μ + dispE μ t) + s * t
      ≤ Real.sqrt ((μ + dispE μ s) ^ 2 + s ^ 2) * Real.sqrt ((μ + dispE μ t) ^ 2 + t ^ 2) := by
  have hdet : s * (μ + dispE μ t) - (μ + dispE μ s) * t
      = (μ + dispE μ s) * (μ + dispE μ t) * (spinSlope μ s - spinSlope μ t) := by
    have hs : 0 < μ + dispE μ s := by linarith [dispE_pos hμ s]
    have ht : 0 < μ + dispE μ t := by linarith [dispE_pos hμ t]
    rw [spinSlope, spinSlope]
    field_simp
  have hsl := abs_spinSlope_sub_le hμ s t
  set x := μ + dispE μ s
  set y := μ + dispE μ t
  have hxs : |s| < x := by have := abs_le_dispE μ s; linarith
  have hyt : |t| < y := by have := abs_le_dispE μ t; linarith
  have hD : 0 < x * y + s * t := by
    have h1 : |s * t| < x * y := by
      rw [abs_mul]
      exact mul_lt_mul'' hxs hyt (abs_nonneg _) (abs_nonneg _)
    linarith [neg_abs_le (s * t)]
  have hA : 0 ≤ x ^ 2 + s ^ 2 := by positivity
  rw [← Real.sqrt_mul hA]
  have hlag : (x ^ 2 + s ^ 2) * (y ^ 2 + t ^ 2)
      = (x * y + s * t) ^ 2 + (s * y - x * t) ^ 2 := by ring
  have hup : x * y + s * t ≤ Real.sqrt ((x ^ 2 + s ^ 2) * (y ^ 2 + t ^ 2)) :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (s * y - x * t)])
  refine ⟨hD, ?_, hup⟩
  set ε := (s - t) ^ 2 / (4 * μ ^ 2)
  have hsl2 : (spinSlope μ s - spinSlope μ t) ^ 2 ≤ ε := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hsl 2
    rw [sq_abs, div_pow, sq_abs, mul_pow] at h
    simpa [ε, show (2 : ℝ) ^ 2 = 4 by norm_num] using h
  have hε : 0 ≤ ε := by positivity
  have hxy : (x * y) ^ 2 ≤ (x ^ 2 + s ^ 2) * (y ^ 2 + t ^ 2) := by
    rw [mul_pow]
    exact mul_le_mul (by nlinarith) (by nlinarith) (sq_nonneg _) hA
  have hdet2 : (s * y - x * t) ^ 2 ≤ ε * ((x ^ 2 + s ^ 2) * (y ^ 2 + t ^ 2)) := by
    rw [hdet, mul_pow]
    calc (x * y) ^ 2 * (spinSlope μ s - spinSlope μ t) ^ 2 ≤ (x * y) ^ 2 * ε :=
          mul_le_mul_of_nonneg_left hsl2 (sq_nonneg _)
      _ ≤ ((x ^ 2 + s ^ 2) * (y ^ 2 + t ^ 2)) * ε := mul_le_mul_of_nonneg_right hxy hε
      _ = _ := mul_comm _ _
  have hAB : 0 ≤ (x ^ 2 + s ^ 2) * (y ^ 2 + t ^ 2) := by positivity
  rcases le_or_gt (1 - ε) 0 with h1 | h1
  · exact (mul_nonpos_of_nonpos_of_nonneg h1 (Real.sqrt_nonneg _)).trans hD.le
  · refine (le_abs_self _).trans (abs_le_of_sq_le_sq ?_ hD.le)
    rw [mul_pow, Real.sq_sqrt hAB]
    have h2 : (1 - ε) ^ 2 ≤ 1 - ε := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h2 hAB]

/-! ### Mode norms and the packet's norm -/

variable {L : ℕ} [NeZero L]

/-- The spinor overlap of two modes on the ring, as a real number. -/
theorem spinOverlap_eq (J μ₀ μ₁ : ℝ) (m' m : ℤ) :
    spinOverlap (L := L) J μ₀ μ₁ m' m
      = (((μ₀ + bandE J μ₀ (angleZ L m')) * (μ₁ + bandE J μ₁ (angleZ L m))
          + 2 * J * Real.sin (angleZ L m') * (2 * J * Real.sin (angleZ L m)) : ℝ) : ℂ) := by
  simp only [spinOverlap, modeSpin, Fin.sum_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero,
    Complex.star_def, Complex.conj_ofReal, dispE_modeS_intCast]
  simp only [modeS, latticeAngle_intCast_sin]
  push_cast
  ring

/-- **The norm of the spinor** `(μ + E(θ), 2J sin θ)` of the upper-band mode at angle `θ`. -/
def spinNorm (J μ θ : ℝ) : ℝ := Real.sqrt ((μ + bandE J μ θ) ^ 2 + (2 * J * Real.sin θ) ^ 2)

theorem sq_spinNorm (J μ θ : ℝ) :
    spinNorm J μ θ ^ 2 = (μ + bandE J μ θ) ^ 2 + (2 * J * Real.sin θ) ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem spinNorm_pos {J μ : ℝ} (hμ : 0 < μ) (θ : ℝ) : 0 < spinNorm J μ θ := by
  have := le_bandE J μ θ
  exact Real.sqrt_pos.2 (by nlinarith [sq_nonneg (2 * J * Real.sin θ)])

/-- **The norm of the mode of integer momentum `m`** on a ring of `L` sites: `√L` times its spinor's
norm. -/
def modeNorm (L : ℕ) (J μ : ℝ) (m : ℤ) : ℝ := Real.sqrt L * spinNorm J μ (angleZ L m)

theorem modeNorm_pos {J μ : ℝ} (hμ : 0 < μ) (m : ℤ) : 0 < modeNorm L J μ m :=
  mul_pos (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L))) (spinNorm_pos hμ _)

/-- **Each momentum's weight in the norm**: `L |a_m|² ‖u_m‖² = (|a_m| ‖mode_m‖)²`. -/
theorem clockWeight_self (J μ : ℝ) (a : ℤ → ℂ) (m : ℤ) :
    clockWeight (L := L) J μ μ a m = (((‖a m‖ * modeNorm L J μ m) ^ 2 : ℝ) : ℂ) := by
  rw [clockWeight, spinOverlap_eq, modeNorm, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg L),
    sq_spinNorm, mul_assoc (L : ℂ), Complex.star_def, Complex.conj_mul']
  push_cast
  ring

/-- ★★ **The packet's squared norm**, conserved: `⟨ψ(t), ψ(t)⟩ = Σ_m (|a_m| ‖mode_m‖)²`. -/
theorem chainInner_packet_self (J μ : ℝ) {W : Finset ℤ} (hD : Distinct L W) (a : ℤ → ℂ) (t : ℝ) :
    chainInner (packet (L := L) J μ W a t) (packet (L := L) J μ W a t)
      = ((∑ m ∈ W, (‖a m‖ * modeNorm L J μ m) ^ 2 : ℝ) : ℂ) := by
  have h := clockOverlap_eq (L := L) J μ μ hD a t
  rw [clockOverlap] at h
  rw [h]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [sub_self, zero_mul, mul_zero, Complex.exp_zero, mul_one,
    clockWeight_self]
  push_cast
  rfl

/-- ★★ **Cauchy–Schwarz for a neighbouring pair**:
`‖w_m‖ ≤ (|a_{m+1}| ‖mode_{m+1}‖)(|a_m| ‖mode_m‖)`. -/
theorem norm_transWeight_le {J μ : ℝ} (hμ : 0 < μ) (a : ℤ → ℂ) (m : ℤ) :
    ‖transWeight (L := L) J μ a m‖
      ≤ (‖a (m + 1)‖ * modeNorm L J μ (m + 1)) * (‖a m‖ * modeNorm L J μ m) := by
  obtain ⟨hD, -, hup⟩ := spin_align hμ (2 * J * Real.sin (angleZ L (m + 1)))
    (2 * J * Real.sin (angleZ L m))
  change 0 < (μ + bandE J μ (angleZ L (m + 1))) * (μ + bandE J μ (angleZ L m)) + _ at hD
  change _ ≤ spinNorm J μ (angleZ L (m + 1)) * spinNorm J μ (angleZ L m) at hup
  have hL : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (Nat.cast_nonneg L)
  rw [transWeight, spinOverlap_eq, norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hD, norm_star, Complex.norm_natCast, modeNorm, modeNorm,
    show ‖a (m + 1)‖ * (Real.sqrt L * spinNorm J μ (angleZ L (m + 1)))
        * (‖a m‖ * (Real.sqrt L * spinNorm J μ (angleZ L m)))
      = Real.sqrt L * Real.sqrt L * ‖a (m + 1)‖ * ‖a m‖
        * (spinNorm J μ (angleZ L (m + 1)) * spinNorm J μ (angleZ L m)) by ring, hL]
  gcongr
  exact hup

/-- **A sum over neighbouring pairs is at most the sum of squares.** -/
theorem sum_filter_succ_mul_le (W : Finset ℤ) (g : ℤ → ℝ) :
    ∑ m ∈ W.filter (fun m => m + 1 ∈ W), g (m + 1) * g m ≤ ∑ m ∈ W, g m ^ 2 := by
  have h1 : ∑ m ∈ W.filter (fun m => m + 1 ∈ W), g m ^ 2 ≤ ∑ m ∈ W, g m ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
  have h2 : ∑ m ∈ W.filter (fun m => m + 1 ∈ W), g (m + 1) ^ 2 ≤ ∑ m ∈ W, g m ^ 2 := by
    calc ∑ m ∈ W.filter (fun m => m + 1 ∈ W), g (m + 1) ^ 2
        = ∑ m ∈ (W.filter (fun m => m + 1 ∈ W)).image (fun m : ℤ => m + 1), g m ^ 2 :=
          (Finset.sum_image (f := fun m => g m ^ 2) (g := fun m : ℤ => m + 1)
            (fun _ _ _ _ h => add_right_cancel h)).symm
      _ ≤ ∑ m ∈ W, g m ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _)
          intro x hx
          obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hx
          exact (Finset.mem_filter.1 hm).2
  have h3 : ∀ m, g (m + 1) * g m ≤ (g (m + 1) ^ 2 + g m ^ 2) / 2 := fun m => by
    nlinarith [sq_nonneg (g (m + 1) - g m)]
  calc ∑ m ∈ W.filter (fun m => m + 1 ∈ W), g (m + 1) * g m
      ≤ ∑ m ∈ W.filter (fun m => m + 1 ∈ W), (g (m + 1) ^ 2 + g m ^ 2) / 2 :=
        Finset.sum_le_sum fun m _ => h3 m
    _ = (∑ m ∈ W.filter (fun m => m + 1 ∈ W), g (m + 1) ^ 2
          + ∑ m ∈ W.filter (fun m => m + 1 ∈ W), g m ^ 2) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ ∑ m ∈ W, g m ^ 2 := by linarith

/-- ★★★ **The translation weights are bounded by the packet's squared norm**:
`Σ_m ‖w_m‖ ≤ ⟨ψ, ψ⟩`. -/
theorem sum_norm_transWeight_le {J μ : ℝ} (hμ : 0 < μ) {W : Finset ℤ} (hD : Distinct L W)
    (a : ℤ → ℂ) (t : ℝ) :
    ∑ m ∈ W.filter (fun m => m + 1 ∈ W), ‖transWeight (L := L) J μ a m‖
      ≤ ‖chainInner (packet (L := L) J μ W a t) (packet (L := L) J μ W a t)‖ := by
  rw [chainInner_packet_self J μ hD a t, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact (Finset.sum_le_sum fun m _ => norm_transWeight_le hμ a m).trans
    (sum_filter_succ_mul_le W fun m => ‖a m‖ * modeNorm L J μ m)

theorem norm_exp_I_mul_ofReal_mul (r t : ℝ) : ‖exp (I * ((r : ℂ) * (t : ℂ)))‖ = 1 := by
  rw [show I * ((r : ℂ) * (t : ℂ)) = ((r * t : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- ★★ **The translation phase is at most the squared norm**: `|T| ≤ ⟨ψ, ψ⟩`. -/
theorem norm_transPhase_le {J μ : ℝ} (hμ : 0 < μ) {W : Finset ℤ} (hW : NoWrap L W)
    (hD : Distinct L W) (a : ℤ → ℂ) (t : ℝ) :
    ‖transPhase (packet (L := L) J μ W a t)‖
      ≤ ‖chainInner (packet (L := L) J μ W a t) (packet (L := L) J μ W a t)‖ := by
  rw [transPhase_packet J μ hW a t]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun m _ => ?_).trans
    (sum_norm_transWeight_le hμ hD a t))
  rw [norm_mul, norm_exp_I_mul_ofReal_mul, mul_one]

/-- ★★ **The drift error of a packet within `δ` of `θ₀`** is at most `vgLip · h (δ + h) ⟨ψ, ψ⟩`,
`h = 2π/L`. -/
theorem driftError_le {J μ : ℝ} (hμ : 0 < μ) {W : Finset ℤ} (hD : Distinct L W) (a : ℤ → ℂ)
    {θ₀ δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : ∀ m ∈ W, |angleZ L m - θ₀| ≤ δ) :
    driftError (L := L) J μ W a θ₀ ≤ vgLip J μ * (2 * Real.pi / L) * (δ + 2 * Real.pi / L)
      * ‖chainInner (packet (L := L) J μ W a 0) (packet (L := L) J μ W a 0)‖ := by
  have hC' : 0 ≤ vgLip J μ * (2 * Real.pi / L) * (δ + 2 * Real.pi / L) := by
    rw [vgLip]
    positivity
  rw [driftError]
  calc ∑ m ∈ W.filter (fun m => m + 1 ∈ W), ‖transWeight (L := L) J μ a m‖
        * (vgLip J μ * (2 * Real.pi / L) * (|angleZ L m - θ₀| + 2 * Real.pi / L))
      ≤ ∑ m ∈ W.filter (fun m => m + 1 ∈ W), ‖transWeight (L := L) J μ a m‖
        * (vgLip J μ * (2 * Real.pi / L) * (δ + 2 * Real.pi / L)) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have := hδ m (Finset.mem_filter.1 hm).1
        have hC : 0 ≤ vgLip J μ * (2 * Real.pi / L) := by
          rw [vgLip]
          positivity
        gcongr
    _ = (∑ m ∈ W.filter (fun m => m + 1 ∈ W), ‖transWeight (L := L) J μ a m‖)
        * (vgLip J μ * (2 * Real.pi / L) * (δ + 2 * Real.pi / L)) := by rw [Finset.sum_mul]
    _ ≤ ‖chainInner (packet (L := L) J μ W a 0) (packet (L := L) J μ W a 0)‖
        * (vgLip J μ * (2 * Real.pi / L) * (δ + 2 * Real.pi / L)) :=
        mul_le_mul_of_nonneg_right (sum_norm_transWeight_le hμ hD a 0) hC'
    _ = _ := mul_comm _ _

/-! ### Normalised packets -/

/-- **Amplitudes in the orthonormal basis of modes**: `a_m = β_m / ‖mode_m‖`. -/
def unitAmp (L : ℕ) (J μ : ℝ) (β : ℤ → ℂ) (m : ℤ) : ℂ := β m / (modeNorm L J μ m : ℂ)

theorem norm_unitAmp_mul {J μ : ℝ} (hμ : 0 < μ) (β : ℤ → ℂ) (m : ℤ) :
    ‖unitAmp L J μ β m‖ * modeNorm L J μ m = ‖β m‖ := by
  have h := modeNorm_pos (L := L) (J := J) hμ m
  rw [unitAmp, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h,
    div_mul_cancel₀ _ h.ne']

/-- ★★ **A normalised packet**: with amplitudes `β_m/‖mode_m‖`, `⟨ψ(t), ψ(t)⟩ = Σ_m |β_m|²` at
every time. -/
theorem chainInner_packet_unitAmp {J μ : ℝ} (hμ : 0 < μ) {W : Finset ℤ} (hD : Distinct L W)
    (β : ℤ → ℂ) (t : ℝ) :
    chainInner (packet (L := L) J μ W (unitAmp L J μ β) t)
        (packet (L := L) J μ W (unitAmp L J μ β) t)
      = ((∑ m ∈ W, ‖β m‖ ^ 2 : ℝ) : ℂ) := by
  rw [chainInner_packet_self J μ hD]
  simp only [norm_unitAmp_mul hμ]

/-- **The cosine of the angle between the spinors at `θ'` and `θ`.** -/
def spinCos (J μ θ' θ : ℝ) : ℝ :=
  ((μ + bandE J μ θ') * (μ + bandE J μ θ) + 2 * J * Real.sin θ' * (2 * J * Real.sin θ))
    / (spinNorm J μ θ' * spinNorm J μ θ)

/-- ★★ **Neighbouring spinors are nearly parallel**: `1 − (J(θ' − θ)/μ)² ≤ cos ∠(u(θ'), u(θ))`. -/
theorem one_sub_le_spinCos {J μ : ℝ} (hμ : 0 < μ) (θ' θ : ℝ) :
    1 - (J * (θ' - θ) / μ) ^ 2 ≤ spinCos J μ θ' θ := by
  obtain ⟨-, hlo, -⟩ := spin_align hμ (2 * J * Real.sin θ') (2 * J * Real.sin θ)
  change _ * (spinNorm J μ θ' * spinNorm J μ θ) ≤ _ at hlo
  have hN := mul_pos (spinNorm_pos (J := J) hμ θ') (spinNorm_pos (J := J) hμ θ)
  rw [spinCos, le_div_iff₀ hN]
  refine le_trans ?_ hlo
  refine mul_le_mul_of_nonneg_right ?_ hN.le
  have hs := Real.abs_sin_sub_sin_le θ' θ
  have h2 := pow_le_pow_left₀ (abs_nonneg _) hs 2
  rw [sq_abs, sq_abs] at h2
  have : (2 * J * Real.sin θ' - 2 * J * Real.sin θ) ^ 2 / (4 * μ ^ 2)
      ≤ (J * (θ' - θ) / μ) ^ 2 := by
    rw [div_pow, mul_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 * J * Real.sin θ' - 2 * J * Real.sin θ) ^ 2
        = 4 * J ^ 2 * (Real.sin θ' - Real.sin θ) ^ 2 := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * J ^ 2 * μ ^ 2)]
  linarith

theorem transWeight_unitAmp {J μ : ℝ} (hμ : 0 < μ) (β : ℤ → ℂ) (m : ℤ) :
    transWeight (L := L) J μ (unitAmp L J μ β) m
      = star (β (m + 1)) * β m * (spinCos J μ (angleZ L (m + 1)) (angleZ L m) : ℂ) := by
  have h1 := spinNorm_pos (J := J) hμ (angleZ L (m + 1))
  have h0 := spinNorm_pos (J := J) hμ (angleZ L m)
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hs : ((Real.sqrt L : ℝ) : ℂ) ^ 2 = (L : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hL.le]
    push_cast
    rfl
  have hs0 : ((Real.sqrt L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hL).ne'
  have h1' : ((spinNorm J μ (angleZ L (m + 1)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1.ne'
  have h0' : ((spinNorm J μ (angleZ L m) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  rw [transWeight, spinOverlap_eq, unitAmp, unitAmp, spinCos, modeNorm, modeNorm]
  simp only [Complex.star_def, map_div₀, Complex.conj_ofReal]
  push_cast
  rw [← hs]
  field_simp

/-- ★★★ **The initial localisation, bounded below**: for real nonnegative coefficients `β`,
`Re T(0) ≥ (1 − (2πJ/(Lμ))²) Σ_m β_{m+1} β_m`. -/
theorem re_transPhase_unitAmp_ge {J μ : ℝ} (hμ : 0 < μ) {W : Finset ℤ} (hW : NoWrap L W)
    (β : ℤ → ℝ) (hβ : ∀ m, 0 ≤ β m) :
    (1 - (2 * Real.pi * J / (L * μ)) ^ 2)
        * ∑ m ∈ W.filter (fun m => m + 1 ∈ W), β (m + 1) * β m
      ≤ (transPhase (packet (L := L) J μ W (unitAmp L J μ fun m => (β m : ℂ)) 0)).re := by
  rw [transPhase_packet J μ hW _ 0, Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [Complex.ofReal_zero, mul_zero, mul_zero, Complex.exp_zero, mul_one, transWeight_unitAmp hμ,
    Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  have hc := one_sub_le_spinCos (J := J) hμ (angleZ L (m + 1)) (angleZ L m)
  have hd : angleZ L (m + 1) - angleZ L m = 2 * Real.pi / L := by
    rw [angleZ_succ]
    ring
  rw [hd, show J * (2 * Real.pi / L) / μ = 2 * Real.pi * J / (L * μ) by ring] at hc
  have hb : 0 ≤ β (m + 1) * β m := mul_nonneg (hβ _) (hβ _)
  nlinarith

/-- The window of `N` neighbouring momenta from `lo`: its neighbouring pairs start at
`lo, …, lo + N − 2`. -/
theorem filter_succ_Ico (lo : ℤ) (N : ℕ) :
    (Finset.Ico lo (lo + N)).filter (fun m => m + 1 ∈ Finset.Ico lo (lo + N))
      = Finset.Ico lo (lo + N - 1) := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_Ico]
  omega

/-- ★★ **The flat packet** on `N ≥ 1` neighbouring momenta, coefficients `1/√N`: `Σ β² = 1` and
`Σ β_{m+1} β_m = 1 − 1/N`. -/
theorem flat_sums (lo : ℤ) {N : ℕ} (hN : 0 < N) :
    ∑ _m ∈ Finset.Ico lo (lo + N), (1 / Real.sqrt N) ^ 2 = 1
    ∧ ∑ _m ∈ (Finset.Ico lo (lo + N)).filter (fun m => m + 1 ∈ Finset.Ico lo (lo + N)),
        1 / Real.sqrt N * (1 / Real.sqrt N) = 1 - 1 / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : (1 / Real.sqrt N) ^ 2 = 1 / N := by rw [div_pow, one_pow, Real.sq_sqrt hN'.le]
  rw [filter_succ_Ico, Finset.sum_const, Finset.sum_const, Int.card_Ico, Int.card_Ico, ← sq, hs,
    show lo + N - lo = (N : ℤ) by ring, show lo + N - 1 - lo = ((N - 1 : ℕ) : ℤ) by omega,
    Int.toNat_natCast, Int.toNat_natCast, nsmul_eq_mul, nsmul_eq_mul,
    Nat.cast_sub (show 1 ≤ N from hN), Nat.cast_one]
  constructor <;> field_simp

/-- ★★ **Close complex numbers have close phases**: `‖w‖ ‖z/‖z‖ − w/‖w‖‖ ≤ 2‖z − w‖`. -/
theorem norm_mul_norm_div_sub_le (z w : ℂ) :
    ‖w‖ * ‖z / (‖z‖ : ℂ) - w / (‖w‖ : ℂ)‖ ≤ 2 * ‖z - w‖ := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  rcases eq_or_ne z 0 with rfl | hz
  · have hw' : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hw).ne'
    rw [zero_div, zero_sub, norm_neg, norm_div, Complex.norm_real, norm_norm,
      div_self (norm_pos_iff.2 hw).ne', mul_one, zero_sub, norm_neg]
    linarith [norm_nonneg w]
  have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  have key : ((‖w‖ : ℝ) : ℂ) * (z / (‖z‖ : ℂ) - w / (‖w‖ : ℂ))
      = ((‖w‖ / ‖z‖ - 1 : ℝ) : ℂ) * z + (z - w) := by
    have : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hz'.ne'
    have : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hw'.ne'
    push_cast
    field_simp
    ring
  have e1 : ‖w‖ * ‖z / (‖z‖ : ℂ) - w / (‖w‖ : ℂ)‖
      = ‖((‖w‖ : ℝ) : ℂ) * (z / (‖z‖ : ℂ) - w / (‖w‖ : ℂ))‖ := by
    rw [norm_mul, Complex.norm_real, norm_norm]
  rw [e1, key]
  refine (norm_add_le _ _).trans ?_
  have e2 : ‖((‖w‖ / ‖z‖ - 1 : ℝ) : ℂ) * z‖ = |‖w‖ - ‖z‖| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← abs_of_pos hz', ← abs_mul,
      abs_of_pos hz']
    congr 1
    field_simp
  rw [e2]
  linarith [abs_norm_sub_norm_le w z, norm_sub_rev w z]

/-! ### A packet of fixed physical width on a ring of fixed physical length -/

/-- **The packet on a ring of physical length `ℓ`** with `L` sites (spacing `a = ℓ/L`), hop
`J(a) = c/(2a)`, rest energy `μ`, coefficients `β` on the window `W` in the orthonormal basis of
modes. Mode `m` has physical momentum `2πm/ℓ`, whatever `L`. -/
def ringPacket (c μ ℓ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (t : ℝ) : ZMod L × Fin 2 → ℂ :=
  packet (L := L) (scaledHop c (ℓ / L)) μ W (unitAmp L (scaledHop c (ℓ / L)) μ β) t

/-- **The error rate** of `dirac_packet_limit`: with `k = 2π/ℓ`,
`k ((c²/μ)(D + k) + a² (cP²/2 + c²P³/(6μ)))`, the first term the window's spread, the second the
lattice's correction to the drift velocity. -/
def limitErr (c μ ℓ D P a : ℝ) : ℝ :=
  2 * Real.pi / ℓ * (c ^ 2 / μ * (D + 2 * Real.pi / ℓ)
    + a ^ 2 * (c * P ^ 2 / 2 + c ^ 2 * P ^ 3 / (6 * μ)))

/-- ★★ **The lattice part of the error rate vanishes**: as `a → 0`, `limitErr` tends to
`k (c²/μ)(D + k)`, `k = 2π/ℓ`, the window's own spread. -/
theorem tendsto_limitErr (c μ ℓ D P : ℝ) :
    Filter.Tendsto (limitErr c μ ℓ D P) (nhds 0)
      (nhds (2 * Real.pi / ℓ * (c ^ 2 / μ * (D + 2 * Real.pi / ℓ)))) := by
  have h : Continuous (limitErr c μ ℓ D P) := by
    unfold limitErr
    fun_prop
  convert h.tendsto 0 using 2
  simp [limitErr]

omit [NeZero L] in
theorem angleZ_div_spacing {ℓ : ℝ} (hℓ : ℓ ≠ 0) (hL : (L : ℝ) ≠ 0) (m : ℤ) :
    angleZ L m = ℓ / L * (2 * Real.pi * m / ℓ) := by
  rw [angleZ]
  field_simp

/-- ★★★ **A packet of fixed physical width converges as the spacing shrinks (#261).** On a ring of
physical length `ℓ` with `L` sites, spacing `a = ℓ/L`, `J(a) = c/(2a)`, take a window `W` of
modes shorter than the ring, with physical momenta `2πm/ℓ` within `D` of `p₀`, `|p₀| ≤ P`, and
coefficients `β` with `Σ |β_m|² = 1`. Then, with `k = 2π/ℓ` and `v = c²p₀/√(μ² + c²p₀²)`:
the state is normalised at every time; `|T(0)| ≤ 1`; the translation phase rotates at `k v`
within `|t| · limitErr`; its modulus drops by at most that; and its phase — the circular position
times `k` — is within `2|t| · limitErr / |T(0)|` of `e^{ikvt}` times its initial phase. The error
rate is `k (c²/μ)(D + k)` plus `k a² (cP²/2 + c²P³/(6μ))`: uniform in `a`, its lattice part
`O(a²)`. The window `W`, the ring length `ℓ` and the time `t` are explicit. -/
theorem dirac_packet_limit {c μ ℓ P D p₀ : ℝ} (hc : 0 < c) (hμ : 0 < μ) (hℓ : 0 < ℓ)
    (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D) {W : Finset ℤ} {lo : ℤ}
    (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L)
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D)
    (β : ℤ → ℂ) (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) :
    (∀ t, chainInner (ringPacket (L := L) c μ ℓ W β t) (ringPacket (L := L) c μ ℓ W β t) = 1)
    ∧ ‖transPhase (ringPacket (L := L) c μ ℓ W β 0)‖ ≤ 1
    ∧ (∀ t, ‖transPhase (ringPacket (L := L) c μ ℓ W β t)
        - exp (I * (((2 * Real.pi / ℓ * vRel c μ (c * p₀) : ℝ) : ℂ) * t))
          * transPhase (ringPacket (L := L) c μ ℓ W β 0)‖
        ≤ |t| * limitErr c μ ℓ D P (ℓ / L))
    ∧ (∀ t, ‖transPhase (ringPacket (L := L) c μ ℓ W β 0)‖ - |t| * limitErr c μ ℓ D P (ℓ / L)
        ≤ ‖transPhase (ringPacket (L := L) c μ ℓ W β t)‖)
    ∧ (∀ t, ‖transPhase (ringPacket (L := L) c μ ℓ W β 0)‖
        * ‖transPhase (ringPacket (L := L) c μ ℓ W β t)
            / (‖transPhase (ringPacket (L := L) c μ ℓ W β t)‖ : ℂ)
          - exp (I * (((2 * Real.pi / ℓ * vRel c μ (c * p₀) : ℝ) : ℂ) * t))
            * (transPhase (ringPacket (L := L) c μ ℓ W β 0)
              / (‖transPhase (ringPacket (L := L) c μ ℓ W β 0)‖ : ℂ))‖
        ≤ 2 * (|t| * limitErr c μ ℓ D P (ℓ / L))) := by
  obtain ⟨hW, hDst⟩ := noWrap_distinct_of_window (L := L) hWin
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set a := ℓ / L with ha_def
  have ha : 0 < a := div_pos hℓ hL
  set k := 2 * Real.pi / ℓ with hk_def
  have hk : 0 < k := by positivity
  set J := scaledHop c a
  set T : ℝ → ℂ := fun t => transPhase (ringPacket (L := L) c μ ℓ W β t) with hT
  have hnorm : ∀ t, chainInner (ringPacket (L := L) c μ ℓ W β t)
      (ringPacket (L := L) c μ ℓ W β t) = 1 := fun t => by
    rw [ringPacket, chainInner_packet_unitAmp hμ hDst, hβ, Complex.ofReal_one]
  have hT0 : ‖T 0‖ ≤ 1 := by
    have h := norm_transPhase_le (L := L) (J := J) hμ hW hDst (unitAmp L J μ β) 0
    have h1 := hnorm 0
    rw [ringPacket] at h1
    rw [h1, norm_one] at h
    exact h
  -- the drift at the lattice velocity
  have hstep : 2 * Real.pi / L = a * k := by
    rw [ha_def, hk_def]
    field_simp
  have hδ : ∀ m ∈ W, |angleZ L m - a * p₀| ≤ a * D := fun m hm => by
    rw [angleZ_div_spacing hℓ.ne' hL.ne', ← mul_sub, abs_mul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left (hWD m hm) ha.le
  have hdrift : ∀ t : ℝ, ‖T t - exp (I * (((k * scaledV c μ a p₀ : ℝ) : ℂ) * t)) * T 0‖
      ≤ |t| * (k * (c ^ 2 / μ * (D + k))) := fun t => by
    have h := transPhase_drift (L := L) (J := J) hμ hW (unitAmp L J μ β) (a * p₀) t
    have hrate : 2 * Real.pi / L * groupVel J μ (a * p₀) = k * scaledV c μ a p₀ := by
      rw [hstep, scaledV]
      ring
    rw [hrate] at h
    have he := driftError_le (L := L) (J := J) hμ hDst (unitAmp L J μ β)
      (mul_nonneg ha.le hD0) hδ
    have h1 := hnorm 0
    rw [ringPacket] at h1
    rw [h1, norm_one, mul_one, hstep, vgLip_scaledHop_step ha.ne'] at he
    refine h.trans (mul_le_mul_of_nonneg_left (he.trans (le_of_eq ?_)) (abs_nonneg t))
    ring
  -- from the lattice velocity to the relativistic one
  have hrel : ∀ t : ℝ, ‖exp (I * (((k * scaledV c μ a p₀ : ℝ) : ℂ) * t)) * T 0
      - exp (I * (((k * vRel c μ (c * p₀) : ℝ) : ℂ) * t)) * T 0‖
      ≤ |t| * (k * (a ^ 2 * (c * P ^ 2 / 2 + c ^ 2 * P ^ 3 / (6 * μ)))) := fun t => by
    have h := norm_sum_phase_sub_le ({()} : Finset Unit) (fun _ => T 0)
      (fun _ => k * scaledV c μ a p₀) (k * vRel c μ (c * p₀)) t
    simp only [Finset.sum_singleton] at h
    rw [mul_comm (T 0)] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg t))
    rw [← mul_sub, abs_mul, abs_of_pos hk]
    have hv := abs_scaledV_sub_le hc hμ ha hp₀
    calc ‖T 0‖ * (k * |scaledV c μ a p₀ - vRel c μ (c * p₀)|)
        ≤ 1 * (k * (a ^ 2 * (c * P ^ 2 / 2 + c ^ 2 * P ^ 3 / (6 * μ)))) := by
          gcongr
      _ = _ := one_mul _
  have hmain : ∀ t : ℝ,
      ‖T t - exp (I * (((2 * Real.pi / ℓ * vRel c μ (c * p₀) : ℝ) : ℂ) * t)) * T 0‖
      ≤ |t| * limitErr c μ ℓ D P a := fun t => by
    calc ‖T t - exp (I * (((k * vRel c μ (c * p₀) : ℝ) : ℂ) * t)) * T 0‖
        ≤ ‖T t - exp (I * (((k * scaledV c μ a p₀ : ℝ) : ℂ) * t)) * T 0‖
          + ‖exp (I * (((k * scaledV c μ a p₀ : ℝ) : ℂ) * t)) * T 0
            - exp (I * (((k * vRel c μ (c * p₀) : ℝ) : ℂ) * t)) * T 0‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ |t| * (k * (c ^ 2 / μ * (D + k)))
          + |t| * (k * (a ^ 2 * (c * P ^ 2 / 2 + c ^ 2 * P ^ 3 / (6 * μ)))) :=
          add_le_add (hdrift t) (hrel t)
      _ = |t| * limitErr c μ ℓ D P a := by
          rw [limitErr]
          ring
  refine ⟨hnorm, hT0, hmain, fun t => ?_, fun t => ?_⟩
  · have h2 := norm_sub_norm_le (exp (I * (((2 * Real.pi / ℓ * vRel c μ (c * p₀) : ℝ) : ℂ) * t))
      * T 0) (T t)
    rw [norm_mul, norm_exp_I_mul_ofReal_mul, one_mul, norm_sub_rev] at h2
    linarith [hmain t]
  · have h := norm_mul_norm_div_sub_le (T t)
      (exp (I * (((2 * Real.pi / ℓ * vRel c μ (c * p₀) : ℝ) : ℂ) * t)) * T 0)
    have hn : ‖exp (I * (((2 * Real.pi / ℓ * vRel c μ (c * p₀) : ℝ) : ℂ) * t)) * T 0‖ = ‖T 0‖ := by
      rw [norm_mul, norm_exp_I_mul_ofReal_mul, one_mul]
    rw [hn, mul_div_assoc] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hmain t) two_pos.le)

/-- ★★★ **…and it starts localised**: for real nonnegative coefficients,
`|T(0)| ≥ (1 − (πc/(ℓμ))²) Σ_m β_{m+1} β_m`, whatever the number of sites. -/
theorem ringPacket_localised {c μ ℓ : ℝ} (hμ : 0 < μ) (hℓ : 0 < ℓ) {W : Finset ℤ}
    (hW : NoWrap L W) (β : ℤ → ℝ) (hβ : ∀ m, 0 ≤ β m) :
    (1 - (Real.pi * c / (ℓ * μ)) ^ 2) * ∑ m ∈ W.filter (fun m => m + 1 ∈ W), β (m + 1) * β m
      ≤ ‖transPhase (ringPacket (L := L) c μ ℓ W (fun m => (β m : ℂ)) 0)‖ := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have h := re_transPhase_unitAmp_ge (L := L) (J := scaledHop c (ℓ / L)) hμ hW β hβ
  have he : 2 * Real.pi * scaledHop c (ℓ / L) / (L * μ) = Real.pi * c / (ℓ * μ) := by
    rw [scaledHop]
    field_simp
  rw [he] at h
  exact h.trans (Complex.re_le_norm _)

/-- ★★★ **A flat packet of `N` neighbouring modes is normalised and starts localised**:
`|T(0)| ≥ (1 − (πc/(ℓμ))²)(1 − 1/N)`, whatever the number of sites `L > N`. -/
theorem flat_packet_localised {c μ ℓ : ℝ} (hμ : 0 < μ) (hℓ : 0 < ℓ) (lo : ℤ) {N : ℕ}
    (hN : 0 < N) (hNL : N < L) :
    ∑ _m ∈ Finset.Ico lo (lo + N), ‖((1 / Real.sqrt N : ℝ) : ℂ)‖ ^ 2 = 1
    ∧ (1 - (Real.pi * c / (ℓ * μ)) ^ 2) * (1 - 1 / N)
      ≤ ‖transPhase (ringPacket (L := L) c μ ℓ (Finset.Ico lo (lo + N))
          (fun _ => ((1 / Real.sqrt N : ℝ) : ℂ)) 0)‖ := by
  obtain ⟨h1, h2⟩ := flat_sums lo hN
  have hpos : 0 ≤ 1 / Real.sqrt N := by positivity
  refine ⟨by simpa [Complex.norm_real, abs_of_nonneg hpos] using h1, ?_⟩
  obtain ⟨hW, -⟩ := noWrap_distinct_of_window (L := L) (W := Finset.Ico lo (lo + N)) (lo := lo)
    (fun m hm => by
      rw [Finset.mem_Ico] at hm
      constructor <;> omega)
  have h := ringPacket_localised (L := L) (c := c) hμ hℓ hW (fun _ => 1 / Real.sqrt N)
    (fun _ => hpos)
  rwa [h2] at h

end CSD.CV

end
