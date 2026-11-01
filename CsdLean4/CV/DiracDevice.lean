/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.DiracPacketLimit
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# One clock device on the Dirac chain, read as a phase

**Category:** 3-Local (CV). BACKLOG #262 (residue of ~~#260~~).

~~#250~~'s `dirac_packet` transported a packet at one rest energy `μ` and estimated the coherence
between packets at `μ₀` and `μ₁` without tying them to one device, and bounded the complex coherence,
not its phase. Here **one device** carries both internal levels, under **one Hamiltonian**, in the
scaled limit of ~~#260~~ and ~~#261~~, and the clock is **read** as a phase.

## Two rest energies

* ★★ `level_align` — **the upper-band spinors of rest energies `μ₀ ≤ μ₁` at the same momentum are
  nearly parallel**: `(1 − ((μ₁ − μ₀)/μ₀)²) ‖u₀‖ ‖u₁‖ ≤ u₀ · u₁ ≤ ‖u₀‖ ‖u₁‖` (Lagrange's identity, the
  gap `0 ≤ x₁ − x₀ ≤ 2(μ₁ − μ₀)`);
* `levelCoherence`, `levelWeight`, ★★ `levelCoherence_eq` (each momentum's phase turns at
  `−(E¹_m − E⁰_m)`), `levelError`, ★★★ `levelCoherence_rate` — `dirac_packet`'s coherence with each
  level's own amplitudes;
* `levelWeight_unitAmp` (each level normalised in its own basis: the weight is `|β_m|²` times the
  spinors' cosine), ★ `levelWeight_unitAmp_bounds`; ★ `abs_vRel_sub_le` — **the levels' velocities
  differ by at most `c (μ₁ − μ₀)/μ₀`**; ★ `levelError_scaled_le` — **the clock's error rate in
  physical units is at most `2cD`**, spacing-independent.

## The device

* `levelMass`, ★ `deviceHam` (the block-diagonal Hamiltonian: Dirac at `μ₀` on level `0`, at `μ₁` on
  level `1`), `deviceHam_mulVec_apply`, ★★ `devicePacket` (one packet carrying both levels, weight
  `1/2` each), ★★ `hasDerivAt_devicePacket` — **the device solves `i Ψ' = H_dev Ψ`**;
* `deviceNorm`, `deviceTrans` (**its position**: the translation phase over both levels),
  `deviceCoherence` (**its clock**: the coherence between its levels), `star_sqrt_two_inv`,
  `device_observables` — each is the average over the levels;
* ★★★ `dirac_device` — **the capstone**: the device is one quantum system and stays normalised; its
  position turns at `k v₀` within `|t|` times the levels' errors and their velocity gap; its clock's
  coherence turns at the level splitting `R` within `|t| c D` and starts at
  `|C(0)| ≥ (1 − ((μ₁ − μ₀)/μ₀)²)/2`; **its reading** `C(t)/|C(t)|` is within `2|t| c D/|C(0)|` of
  `e^{−iRt} C(0)/|C(0)|`; and `R/(μ₁ − μ₀)` is within `(μ₁ − μ₀)/E₀` of `√(1 − (v/c)²)`.

## The findings

1. **The device's position and clock reading are bounded together**, from one state under one
   Hamiltonian: the reading is a phase whose drift from the dilated rate is controlled by the
   window's momentum spread, `2cD`, independently of the lattice spacing.
2. **Carrying both levels costs a velocity gap** `c (μ₁ − μ₀)/μ₀` between them — the clock's two
   levels move at slightly different speeds, which the position error carries — and a coherence
   loss `((μ₁ − μ₀)/μ₀)²/2` at the start, both small for a small level splitting.

## Honest scope

⚠️ **The errors grow linearly in `t`**: the reading is controlled over a horizon `≪ |C(0)|/(cD)`,
the position over one `≪ 1/(limitErr + k|v₁ − v₀|)`. Both are upper bounds.

⚠️ **The dilation is against the lattice momentum** `2J sin(a p₀)`, which tends to `c p₀` as
`a → 0` (~~#260~~); the residue `(μ₁ − μ₀)/E₀` of ~~#249~~ is the finite level splitting.

⚠️ **No records.** The reading is a phase of the state; a detector writing it as a record is the
analogue of #252's detectors for the clock, and an observer timing #269's signal with this clock is
#253's.

References: `specs/BACKLOG.md` #262, #260, #261, #250, #249, #252, #253, #269, #39;
`CV/DiracPacket.lean` (`packet`, `clockOverlap_eq`, `clockOverlap_rate`, `norm_sum_phase_sub_le`);
`CV/DiracPacketLimit.lean` (`dirac_packet_limit`, `unitAmp`, `spinNorm`, `spin_align`,
`norm_mul_norm_div_sub_le`, `angleZ_div_spacing`); `CV/DiracClockChain.lean` (`diracHam`,
`clockRate_mem`, `abs_clockRate_div_sub_le`); `CV/DiracContinuum.lean` (`scaledHop`).
-/

@[expose] public section

open Complex
open scoped Matrix

namespace CSD.CV

/-! ### Spinors of two rest energies -/

/-- ★★ **The upper-band spinors of two rest energies are nearly parallel**: for `0 < μ₀ ≤ μ₁` and
the same momentum term `s`, with `x_i = μ_i + E_i`,
`(1 − ((μ₁ − μ₀)/μ₀)²) ‖u₀‖ ‖u₁‖ ≤ u₀ · u₁ ≤ ‖u₀‖ ‖u₁‖`. -/
theorem level_align {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ ≤ μ₁) (s : ℝ) :
    (1 - ((μ₁ - μ₀) / μ₀) ^ 2)
        * (Real.sqrt ((μ₀ + dispE μ₀ s) ^ 2 + s ^ 2) * Real.sqrt ((μ₁ + dispE μ₁ s) ^ 2 + s ^ 2))
      ≤ (μ₀ + dispE μ₀ s) * (μ₁ + dispE μ₁ s) + s ^ 2
    ∧ (μ₀ + dispE μ₀ s) * (μ₁ + dispE μ₁ s) + s ^ 2
      ≤ Real.sqrt ((μ₀ + dispE μ₀ s) ^ 2 + s ^ 2) * Real.sqrt ((μ₁ + dispE μ₁ s) ^ 2 + s ^ 2) := by
  have h1 : 0 < μ₁ := h0.trans_le h01
  have hE0 := le_dispE μ₀ s
  have hE1 := le_dispE μ₁ s
  obtain ⟨hr0, hr1⟩ := clockRate_mem h0 h01 s
  have hE1pos := dispE_pos h1 s
  have hrate : levelClockRate μ₀ μ₁ s ≤ μ₁ - μ₀ := by
    refine hr1.trans ?_
    have : μ₁ / dispE μ₁ s ≤ 1 := (div_le_one hE1pos).2 hE1
    nlinarith
  have hrate0 : 0 ≤ levelClockRate μ₀ μ₁ s := by
    refine le_trans ?_ hr0
    have : 0 ≤ μ₀ / dispE μ₀ s := div_nonneg h0.le (dispE_pos h0 s).le
    nlinarith
  rw [levelClockRate] at hrate hrate0
  set x0 := μ₀ + dispE μ₀ s
  set x1 := μ₁ + dispE μ₁ s
  set N0 := x0 ^ 2 + s ^ 2
  set N1 := x1 ^ 2 + s ^ 2
  have hx0 : 2 * μ₀ ≤ x0 := by simp only [x0]; linarith
  have hx1 : 0 < x1 := by simp only [x1]; linarith
  have hdot : 0 ≤ x0 * x1 + s ^ 2 :=
    add_nonneg (mul_nonneg (by linarith) hx1.le) (sq_nonneg s)
  have hP : 0 ≤ Real.sqrt N0 * Real.sqrt N1 := by positivity
  have hP2 : (Real.sqrt N0 * Real.sqrt N1) ^ 2 = N0 * N1 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  have hlag : N0 * N1 = (x0 * x1 + s ^ 2) ^ 2 + s ^ 2 * (x0 - x1) ^ 2 := by
    simp only [N0, N1]
    ring
  have hgap : 0 ≤ x1 - x0 ∧ x1 - x0 ≤ 2 * (μ₁ - μ₀) := by
    simp only [x0, x1]
    constructor <;> linarith
  constructor
  · set ε := ((μ₁ - μ₀) / μ₀) ^ 2
    have hcross : s ^ 2 * (x0 - x1) ^ 2 ≤ ε * (N0 * N1) := by
      have hq : (x0 - x1) ^ 2 ≤ 4 * (μ₁ - μ₀) ^ 2 := by nlinarith [hgap.1, hgap.2]
      have hq2 : 4 * (μ₁ - μ₀) ^ 2 ≤ ε * x0 ^ 2 := by
        have e : 4 * (μ₁ - μ₀) ^ 2 = ε * (2 * μ₀) ^ 2 := by
          simp only [ε]
          field_simp
          ring
        rw [e]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hx0 2) (sq_nonneg _)
      have hN0 : x0 ^ 2 ≤ N0 := by simp only [N0]; nlinarith [sq_nonneg s]
      have hN1 : s ^ 2 ≤ N1 := by simp only [N1]; nlinarith [sq_nonneg x1]
      have hε0 : 0 ≤ ε := sq_nonneg _
      calc s ^ 2 * (x0 - x1) ^ 2 ≤ s ^ 2 * (ε * x0 ^ 2) :=
            mul_le_mul_of_nonneg_left (hq.trans hq2) (sq_nonneg s)
        _ = ε * x0 ^ 2 * s ^ 2 := by ring
        _ ≤ ε * N0 * N1 := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hN0 hε0) hN1 (sq_nonneg s)
            positivity
        _ = ε * (N0 * N1) := by ring
    by_cases hε1 : 1 - ε ≤ 0
    · exact (mul_nonpos_of_nonpos_of_nonneg hε1 hP).trans hdot
    · push Not at hε1
      by_contra hlt
      push Not at hlt
      have hsq : (x0 * x1 + s ^ 2) ^ 2 < ((1 - ε) * (Real.sqrt N0 * Real.sqrt N1)) ^ 2 :=
        pow_lt_pow_left₀ hlt hdot (by norm_num)
      rw [mul_pow, hP2] at hsq
      have : (1 - ε) ^ 2 * (N0 * N1) ≤ (1 - ε) * (N0 * N1) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [sq_nonneg ((μ₁ - μ₀) / μ₀)]
      nlinarith
  · by_contra hlt
    push Not at hlt
    have hsq : (Real.sqrt N0 * Real.sqrt N1) ^ 2 < (x0 * x1 + s ^ 2) ^ 2 :=
      pow_lt_pow_left₀ hlt hP (by norm_num)
    rw [hP2, hlag] at hsq
    have := mul_nonneg (sq_nonneg s) (sq_nonneg (x0 - x1))
    linarith

variable {L : ℕ} [NeZero L]

/-! ### The coherence between two levels -/

/-- **The coherence between a device's two levels**: level `0` at rest energy `μ₀` with amplitudes
`a₀`, level `1` at `μ₁` with `a₁`. -/
noncomputable def levelCoherence (J μ₀ μ₁ : ℝ) (W : Finset ℤ) (a₀ a₁ : ℤ → ℂ) (t : ℝ) : ℂ :=
  chainInner (packet (L := L) J μ₀ W a₀ t) (packet (L := L) J μ₁ W a₁ t)

/-- The weight of momentum `m` in the coherence. -/
noncomputable def levelWeight (J μ₀ μ₁ : ℝ) (a₀ a₁ : ℤ → ℂ) (m : ℤ) : ℂ :=
  (L : ℂ) * star (a₀ m) * a₁ m * spinOverlap (L := L) J μ₀ μ₁ m m

/-- ★★ **The coherence, exactly**: each momentum's phase turns at `−(E¹_m − E⁰_m)`. -/
theorem levelCoherence_eq (J μ₀ μ₁ : ℝ) {W : Finset ℤ} (hD : Distinct L W) (a₀ a₁ : ℤ → ℂ)
    (t : ℝ) :
    levelCoherence (L := L) J μ₀ μ₁ W a₀ a₁ t
      = ∑ m ∈ W, levelWeight (L := L) J μ₀ μ₁ a₀ a₁ m
          * exp (I * (((bandE J μ₀ (angleZ L m) - bandE J μ₁ (angleZ L m) : ℝ) : ℂ) * t)) := by
  unfold levelCoherence packet
  rw [chainInner_sum_left]
  simp only [chainInner_sum_right, diracMode_eq, chainInner_planeWave]
  calc ∑ m' ∈ W, star (a₀ m' * exp (-(I * bandE J μ₀ (angleZ L m')) * t))
        * ∑ m ∈ W, a₁ m * exp (-(I * bandE J μ₁ (angleZ L m)) * t)
          * ((if (m' : ZMod L) = (m : ZMod L) then (L : ℂ) else 0)
            * ∑ b, star (modeSpin J μ₀ (m' : ZMod L) b) * modeSpin J μ₁ (m : ZMod L) b)
      = ∑ m' ∈ W, star (a₀ m' * exp (-(I * bandE J μ₀ (angleZ L m')) * t))
          * (a₁ m' * exp (-(I * bandE J μ₁ (angleZ L m')) * t)
            * ((L : ℂ) * spinOverlap (L := L) J μ₀ μ₁ m' m')) := by
        refine Finset.sum_congr rfl fun m' hm' => ?_
        congr 1
        rw [Finset.sum_eq_single m' (fun m hm hne => by
          rw [ite_eq_right (fun h => hne ((hD m hm m' hm').1 h).symm), zero_mul, mul_zero])
          (fun h => absurd hm' h), ite_eq_left rfl, spinOverlap]
    _ = _ := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [star_mul', star_exp_neg_I_mul, levelWeight]
        have hexp : exp (I * (bandE J μ₀ (angleZ L m) * t))
            * exp (-(I * bandE J μ₁ (angleZ L m)) * t)
            = exp (I * (((bandE J μ₀ (angleZ L m) - bandE J μ₁ (angleZ L m) : ℝ) : ℂ) * t)) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        rw [← hexp]
        ring

/-- The coherence error: the window's spread of clock rates about `θ₀`. -/
noncomputable def levelError (J μ₀ μ₁ : ℝ) (W : Finset ℤ) (a₀ a₁ : ℤ → ℂ) (θ₀ : ℝ) : ℝ :=
  ∑ m ∈ W, ‖levelWeight (L := L) J μ₀ μ₁ a₀ a₁ m‖ * (4 * |J| * |angleZ L m - θ₀|)

/-- ★★★ **The coherence rotates at the centre's level splitting** within `|t|` times the window's
spread. -/
theorem levelCoherence_rate {J μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h1 : 0 < μ₁) {W : Finset ℤ}
    (hD : Distinct L W) (a₀ a₁ : ℤ → ℂ) (θ₀ t : ℝ) :
    ‖levelCoherence (L := L) J μ₀ μ₁ W a₀ a₁ t
        - exp (I * (((-levelClockRate μ₀ μ₁ (2 * J * Real.sin θ₀) : ℝ) : ℂ) * t))
          * levelCoherence (L := L) J μ₀ μ₁ W a₀ a₁ 0‖
      ≤ |t| * levelError (L := L) J μ₀ μ₁ W a₀ a₁ θ₀ := by
  rw [levelCoherence_eq J μ₀ μ₁ hD a₀ a₁ t, levelCoherence_eq J μ₀ μ₁ hD a₀ a₁ 0]
  simp only [mul_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  refine (norm_sum_phase_sub_le _ _ _ _ t).trans ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => ?_) (abs_nonneg t)
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have e0 := abs_bandE_sub_le (J := J) h0 (angleZ L m) θ₀
  have e1 := abs_bandE_sub_le (J := J) h1 (angleZ L m) θ₀
  rw [abs_mul, abs_two] at e0 e1
  have hR : -levelClockRate μ₀ μ₁ (2 * J * Real.sin θ₀) = bandE J μ₀ θ₀ - bandE J μ₁ θ₀ := by
    rw [levelClockRate, bandE, bandE]
    ring
  rw [hR]
  calc |bandE J μ₀ (angleZ L m) - bandE J μ₁ (angleZ L m) - (bandE J μ₀ θ₀ - bandE J μ₁ θ₀)|
      = |(bandE J μ₀ (angleZ L m) - bandE J μ₀ θ₀)
          - (bandE J μ₁ (angleZ L m) - bandE J μ₁ θ₀)| := by ring_nf
    _ ≤ |bandE J μ₀ (angleZ L m) - bandE J μ₀ θ₀| + |bandE J μ₁ (angleZ L m) - bandE J μ₁ θ₀| :=
        abs_sub _ _
    _ ≤ 4 * |J| * |angleZ L m - θ₀| := by linarith

/-- **Each momentum's weight in a normalised device**: with each level's amplitudes `β` in its own
orthonormal basis of modes, the weight is `|β_m|²` times the cosine between the two spinors. -/
theorem levelWeight_unitAmp {J μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h1 : 0 < μ₁) (β : ℤ → ℂ) (m : ℤ) :
    levelWeight (L := L) J μ₀ μ₁ (unitAmp L J μ₀ β) (unitAmp L J μ₁ β) m
      = ((‖β m‖ ^ 2 * (((μ₀ + bandE J μ₀ (angleZ L m)) * (μ₁ + bandE J μ₁ (angleZ L m))
          + (2 * J * Real.sin (angleZ L m)) ^ 2)
          / (spinNorm J μ₀ (angleZ L m) * spinNorm J μ₁ (angleZ L m))) : ℝ) : ℂ) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hn0 := spinNorm_pos (J := J) h0 (angleZ L m)
  have hn1 := spinNorm_pos (J := J) h1 (angleZ L m)
  have hsL : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hL.le
  have hsLpos : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hβ : star (β m) * β m = ((‖β m‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  set n0 := spinNorm J μ₀ (angleZ L m)
  set n1 := spinNorm J μ₁ (angleZ L m)
  set d := (μ₀ + bandE J μ₀ (angleZ L m)) * (μ₁ + bandE J μ₁ (angleZ L m))
    + (2 * J * Real.sin (angleZ L m)) ^ 2
  have hd : (μ₀ + bandE J μ₀ (angleZ L m)) * (μ₁ + bandE J μ₁ (angleZ L m))
      + 2 * J * Real.sin (angleZ L m) * (2 * J * Real.sin (angleZ L m)) = d := by
    simp only [d]
    ring
  rw [levelWeight, unitAmp, unitAmp, spinOverlap_eq, modeNorm, modeNorm, hd, star_div₀,
    Complex.star_def, Complex.conj_ofReal, ← Complex.star_def]
  have hden : Real.sqrt L * n0 * (Real.sqrt L * n1) = L * (n0 * n1) := by
    rw [show Real.sqrt L * n0 * (Real.sqrt L * n1) = (Real.sqrt L * Real.sqrt L) * (n0 * n1) by ring,
      Real.mul_self_sqrt hL.le]
  calc (L : ℂ) * (star (β m) / ((Real.sqrt L * n0 : ℝ) : ℂ)) * (β m / ((Real.sqrt L * n1 : ℝ) : ℂ))
        * (d : ℂ)
      = (L : ℂ) * (star (β m) * β m) * d / (((Real.sqrt L * n0 : ℝ) : ℂ)
          * ((Real.sqrt L * n1 : ℝ) : ℂ)) := by ring
    _ = ((L * ‖β m‖ ^ 2 * d / (Real.sqrt L * n0 * (Real.sqrt L * n1)) : ℝ) : ℂ) := by
        rw [hβ]
        push_cast
        ring
    _ = ((‖β m‖ ^ 2 * d / (n0 * n1) : ℝ) : ℂ) := by
        congr 1
        rw [hden]
        field_simp
    _ = _ := by
        congr 1
        ring

/-! ### The device -/

/-- The rest energy of level `i`: `μ₀` for level `0`, `μ₁` for level `1`. -/
noncomputable def levelMass (μ₀ μ₁ : ℝ) (i : Fin 2) : ℝ := if i = 0 then μ₀ else μ₁

/-- ★ **The device's Hamiltonian**: the lattice Dirac Hamiltonian at rest energy `μ₀` on internal
level `0` and at `μ₁` on level `1`, one block per level. -/
noncomputable def deviceHam (J μ₀ μ₁ : ℝ) :
    Matrix ((ZMod L × Fin 2) × Fin 2) ((ZMod L × Fin 2) × Fin 2) ℂ :=
  Matrix.blockDiagonal fun i => diracHam J (levelMass μ₀ μ₁ i)

/-- ★★ **The device**: one packet carrying both internal levels, each with the amplitudes `β` in its
own orthonormal basis of modes, weight `1/2` each. -/
noncomputable def devicePacket (J μ₀ μ₁ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (t : ℝ) :
    (ZMod L × Fin 2) × Fin 2 → ℂ := fun x =>
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
    * packet (L := L) J (levelMass μ₀ μ₁ x.2) W (unitAmp L J (levelMass μ₀ μ₁ x.2) β) t x.1

theorem deviceHam_mulVec_apply (J μ₀ μ₁ : ℝ) (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ)
    (p : ZMod L × Fin 2) (i : Fin 2) :
    (deviceHam J μ₀ μ₁ *ᵥ Ψ) (p, i) = (diracHam J (levelMass μ₀ μ₁ i) *ᵥ fun q => Ψ (q, i)) p := by
  simp only [Matrix.mulVec, dotProduct, deviceHam, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- ★★ **The device is one quantum system**: it solves `i Ψ' = H_dev Ψ`. -/
theorem hasDerivAt_devicePacket (J μ₀ μ₁ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (t : ℝ) :
    HasDerivAt (devicePacket (L := L) J μ₀ μ₁ W β)
      ((-I) • (deviceHam J μ₀ μ₁ *ᵥ devicePacket (L := L) J μ₀ μ₁ W β t)) t := by
  rw [hasDerivAt_pi]
  rintro ⟨p, i⟩
  have h := (hasDerivAt_pi.1 (hasDerivAt_packet (L := L) J (levelMass μ₀ μ₁ i) W
    (unitAmp L J (levelMass μ₀ μ₁ i) β) t) p).const_mul (((Real.sqrt 2 : ℝ) : ℂ)⁻¹)
  have hf : (fun q => devicePacket (L := L) J μ₀ μ₁ W β t (q, i))
      = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • packet (L := L) J (levelMass μ₀ μ₁ i) W
          (unitAmp L J (levelMass μ₀ μ₁ i) β) t := by
    funext q
    rfl
  refine HasDerivAt.congr_deriv (f := fun x => devicePacket (L := L) J μ₀ μ₁ W β x (p, i)) h ?_
  show _ = -I • (deviceHam J μ₀ μ₁ *ᵥ devicePacket (L := L) J μ₀ μ₁ W β t) (p, i)
  rw [deviceHam_mulVec_apply, hf, Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The device's squared norm. -/
noncomputable def deviceNorm (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) : ℂ := ∑ x, star (Ψ x) * Ψ x

/-- **The device's position**: its translation phase, both levels together. -/
noncomputable def deviceTrans (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) : ℂ :=
  ∑ x, star (Ψ x) * ((ZMod.toCircle x.1.1 : ℂ) * Ψ x)

/-- **The device's clock**: the coherence between its two levels; its phase is the reading. -/
noncomputable def deviceCoherence (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) : ℂ :=
  ∑ p, star (Ψ (p, 0)) * Ψ (p, 1)

theorem star_sqrt_two_inv : star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num)]
  push_cast
  ring

/-- Each observable of the device is the average over its levels. -/
theorem device_observables (J μ₀ μ₁ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (t : ℝ) :
    deviceNorm (devicePacket (L := L) J μ₀ μ₁ W β t)
      = (1 / 2) * (chainInner (packet (L := L) J μ₀ W (unitAmp L J μ₀ β) t)
          (packet (L := L) J μ₀ W (unitAmp L J μ₀ β) t)
        + chainInner (packet (L := L) J μ₁ W (unitAmp L J μ₁ β) t)
          (packet (L := L) J μ₁ W (unitAmp L J μ₁ β) t))
    ∧ deviceTrans (devicePacket (L := L) J μ₀ μ₁ W β t)
      = (1 / 2) * (transPhase (packet (L := L) J μ₀ W (unitAmp L J μ₀ β) t)
        + transPhase (packet (L := L) J μ₁ W (unitAmp L J μ₁ β) t))
    ∧ deviceCoherence (devicePacket (L := L) J μ₀ μ₁ W β t)
      = (1 / 2) * levelCoherence (L := L) J μ₀ μ₁ W (unitAmp L J μ₀ β) (unitAmp L J μ₁ β) t := by
  have hm0 : levelMass μ₀ μ₁ 0 = μ₀ := by simp [levelMass]
  have hm1 : levelMass μ₀ μ₁ 1 = μ₁ := by simp [levelMass]
  have hs := star_sqrt_two_inv
  refine ⟨?_, ?_, ?_⟩
  · rw [deviceNorm, Fintype.sum_prod_type, Finset.sum_comm, Fin.sum_univ_two, chainInner,
      chainInner, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun p _ => ?_ <;>
      simp only [devicePacket, hm0, hm1, star_mul'] <;> rw [← hs] <;> ring
  · rw [deviceTrans, Fintype.sum_prod_type, Finset.sum_comm, Fin.sum_univ_two, transPhase,
      transPhase, chainInner, chainInner, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun p _ => ?_ <;>
      simp only [devicePacket, transMul, hm0, hm1, star_mul'] <;> rw [← hs] <;> ring
  · rw [deviceCoherence, levelCoherence, chainInner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [devicePacket, hm0, hm1, star_mul']
    rw [← hs]
    ring

/-- **Each level weight of a normalised device is a fraction of `|β_m|²` close to all of it**:
`(1 − ((μ₁ − μ₀)/μ₀)²) |β_m|² ≤ w_m`, `w_m` real, `|w_m| ≤ |β_m|²`. -/
theorem levelWeight_unitAmp_bounds {J μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ ≤ μ₁) (β : ℤ → ℂ)
    (m : ℤ) :
    (1 - ((μ₁ - μ₀) / μ₀) ^ 2) * ‖β m‖ ^ 2
        ≤ (levelWeight (L := L) J μ₀ μ₁ (unitAmp L J μ₀ β) (unitAmp L J μ₁ β) m).re
    ∧ ‖levelWeight (L := L) J μ₀ μ₁ (unitAmp L J μ₀ β) (unitAmp L J μ₁ β) m‖ ≤ ‖β m‖ ^ 2 := by
  have h1 : 0 < μ₁ := h0.trans_le h01
  rw [levelWeight_unitAmp h0 h1, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs]
  set θ := angleZ L m
  have hn0 := spinNorm_pos (J := J) h0 θ
  have hn1 := spinNorm_pos (J := J) h1 θ
  obtain ⟨hlo, hhi⟩ := level_align h0 h01 (2 * J * Real.sin θ)
  have e0 : spinNorm J μ₀ θ = Real.sqrt ((μ₀ + dispE μ₀ (2 * J * Real.sin θ)) ^ 2
      + (2 * J * Real.sin θ) ^ 2) := rfl
  have e1 : spinNorm J μ₁ θ = Real.sqrt ((μ₁ + dispE μ₁ (2 * J * Real.sin θ)) ^ 2
      + (2 * J * Real.sin θ) ^ 2) := rfl
  rw [← e0, ← e1] at hlo hhi
  have hb0 : 0 ≤ ‖β m‖ ^ 2 := sq_nonneg _
  have hP : 0 < spinNorm J μ₀ θ * spinNorm J μ₁ θ := mul_pos hn0 hn1
  have hq1 : (μ₀ + bandE J μ₀ θ) * (μ₁ + bandE J μ₁ θ) + (2 * J * Real.sin θ) ^ 2
      ≤ spinNorm J μ₀ θ * spinNorm J μ₁ θ := hhi
  have hq0 : (1 - ((μ₁ - μ₀) / μ₀) ^ 2) * (spinNorm J μ₀ θ * spinNorm J μ₁ θ)
      ≤ (μ₀ + bandE J μ₀ θ) * (μ₁ + bandE J μ₁ θ) + (2 * J * Real.sin θ) ^ 2 := hlo
  have hdpos : 0 ≤ (μ₀ + bandE J μ₀ θ) * (μ₁ + bandE J μ₁ θ) + (2 * J * Real.sin θ) ^ 2 := by
    have h0' := le_bandE J μ₀ θ
    have h1' := le_bandE J μ₁ θ
    exact add_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
  set q := ((μ₀ + bandE J μ₀ θ) * (μ₁ + bandE J μ₁ θ) + (2 * J * Real.sin θ) ^ 2)
    / (spinNorm J μ₀ θ * spinNorm J μ₁ θ)
  have hq_le : q ≤ 1 := (div_le_one hP).2 hq1
  have hq_ge : 1 - ((μ₁ - μ₀) / μ₀) ^ 2 ≤ q := (le_div_iff₀ hP).2 hq0
  have hq_nn : 0 ≤ q := div_nonneg hdpos hP.le
  constructor
  · nlinarith
  · rw [abs_of_nonneg (mul_nonneg hb0 hq_nn)]
    nlinarith

/-- **The rest energies' velocity gap**: `|v(μ₁) − v(μ₀)| ≤ c (μ₁ − μ₀)/μ₀` at any momentum. -/
theorem abs_vRel_sub_le {c μ₀ μ₁ : ℝ} (hc : 0 ≤ c) (h0 : 0 < μ₀) (h01 : μ₀ ≤ μ₁) (s : ℝ) :
    |vRel c μ₁ s - vRel c μ₀ s| ≤ c * (μ₁ - μ₀) / μ₀ := by
  have h1 : 0 < μ₁ := h0.trans_le h01
  have hE0 := dispE_pos h0 s
  have hE1 := dispE_pos h1 s
  have hle0 := le_dispE μ₀ s
  have hle1 := le_dispE μ₁ s
  have hs := abs_le_dispE μ₀ s
  obtain ⟨hr0, hr1⟩ := clockRate_mem h0 h01 s
  have hrate : dispE μ₁ s - dispE μ₀ s ≤ μ₁ - μ₀ := by
    have : μ₁ / dispE μ₁ s ≤ 1 := (div_le_one hE1).2 hle1
    rw [levelClockRate] at hr1
    nlinarith
  have hrate0 : 0 ≤ dispE μ₁ s - dispE μ₀ s := by
    have : 0 ≤ μ₀ / dispE μ₀ s := div_nonneg h0.le hE0.le
    rw [levelClockRate] at hr0
    nlinarith
  rw [vRel, vRel, show c * s / dispE μ₁ s - c * s / dispE μ₀ s
      = -(c * s * (dispE μ₁ s - dispE μ₀ s) / (dispE μ₀ s * dispE μ₁ s)) by field_simp; ring,
    abs_neg, abs_div, abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg hrate0,
    abs_of_pos (mul_pos hE0 hE1), div_le_div_iff₀ (mul_pos hE0 hE1) h0]
  have hΔ : 0 ≤ μ₁ - μ₀ := by linarith
  calc c * |s| * (dispE μ₁ s - dispE μ₀ s) * μ₀ ≤ c * dispE μ₀ s * (μ₁ - μ₀) * μ₀ := by
        gcongr
    _ ≤ c * (μ₁ - μ₀) * (dispE μ₀ s * dispE μ₁ s) := by
        have h' : μ₀ ≤ dispE μ₁ s := h01.trans hle1
        nlinarith [mul_le_mul_of_nonneg_left h' (mul_nonneg (mul_nonneg hc hΔ) hE0.le)]

/-- **The coherence error in physical units**: with `J = c/(2a)` and the window's momenta within `D`
of `p₀`, the spread of clock rates is at most `2cD`. -/
theorem levelError_scaled_le {c μ₀ μ₁ ℓ D p₀ : ℝ} (hc : 0 < c) (h0 : 0 < μ₀) (h01 : μ₀ ≤ μ₁)
    (hℓ : 0 < ℓ) {W : Finset ℤ} (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D) (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) :
    levelError (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ W
        (unitAmp L (scaledHop c (ℓ / L)) μ₀ β) (unitAmp L (scaledHop c (ℓ / L)) μ₁ β) (ℓ / L * p₀)
      ≤ 2 * c * D := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have ha : 0 < ℓ / L := div_pos hℓ hL
  have hJ : 4 * |scaledHop c (ℓ / L)| = 2 * c / (ℓ / L) := by
    rw [scaledHop, abs_of_pos (by positivity)]
    field_simp
    ring
  calc levelError (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ W _ _ (ℓ / L * p₀)
      ≤ ∑ m ∈ W, ‖β m‖ ^ 2 * (2 * c * D) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hw := (levelWeight_unitAmp_bounds (L := L) (J := scaledHop c (ℓ / L)) h0 h01 β m).2
        have hang : 4 * |scaledHop c (ℓ / L)| * |angleZ L m - ℓ / L * p₀| ≤ 2 * c * D := by
          rw [hJ, angleZ_div_spacing hℓ.ne' hL.ne', ← mul_sub, abs_mul, abs_of_pos ha]
          rw [show 2 * c / (ℓ / L) * (ℓ / L * |2 * Real.pi * m / ℓ - p₀|)
              = 2 * c * |2 * Real.pi * m / ℓ - p₀| by field_simp]
          exact mul_le_mul_of_nonneg_left (hWD m hm) (by positivity)
        have h4 : 0 ≤ 4 * |scaledHop c (ℓ / L)| * |angleZ L m - ℓ / L * p₀| := by positivity
        calc ‖levelWeight (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ _ _ m‖
              * (4 * |scaledHop c (ℓ / L)| * |angleZ L m - ℓ / L * p₀|)
            ≤ ‖β m‖ ^ 2 * (4 * |scaledHop c (ℓ / L)| * |angleZ L m - ℓ / L * p₀|) :=
              mul_le_mul_of_nonneg_right hw h4
          _ ≤ ‖β m‖ ^ 2 * (2 * c * D) := mul_le_mul_of_nonneg_left hang (sq_nonneg _)
    _ = 2 * c * D := by rw [← Finset.sum_mul, hβ, one_mul]

/-- ★★★ **One clock device on the Dirac chain, read as a phase** (BACKLOG #262). On a ring of
physical length `ℓ` with `L` sites (`J = c/(2a)`, `a = ℓ/L`, `k = 2π/ℓ`), a device with internal
levels of rest energies `0 < μ₀ ≤ μ₁`, carried by one normalised packet of momenta within `D` of `p₀`
on a window shorter than the ring:

* **it is one quantum system**: it solves `i Ψ' = H_dev Ψ` with `H_dev` the Dirac Hamiltonian at
  `μ₀` on level `0` and at `μ₁` on level `1`, and stays normalised;
* **its position**: its translation phase turns at `k v₀`, `v_i = c²p₀/√(μ_i² + c²p₀²)`, within
  `|t|` times the two levels' `limitErr` and `k |v₁ − v₀|`, both halved; and `|v₁ − v₀| ≤ c (μ₁ − μ₀)/μ₀`;
* **its clock**: the coherence `C` between its levels turns at `−R`, `R` the level splitting at the
  window's centre, within `|t| c D`; it starts at `|C(0)| ≥ (1 − ((μ₁ − μ₀)/μ₀)²)/2`;
* **its reading**: the phase `C(t)/|C(t)|` is within `2|t| c D / |C(0)|` of `e^{−iRt} C(0)/|C(0)|`;
* **the reading's rate is dilated**: `R/(μ₁ − μ₀)` is within `(μ₁ − μ₀)/E₀` of
  `√(1 − (v/c)²)` at the lattice momentum (~~#249~~). -/
theorem dirac_device {c μ₀ μ₁ ℓ P D p₀ : ℝ} (hc : 0 < c) (h0 : 0 < μ₀) (h01 : μ₀ ≤ μ₁)
    (hℓ : 0 < ℓ) (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D) {W : Finset ℤ} {lo : ℤ}
    (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L) (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D)
    (β : ℤ → ℂ) (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) :
    let J := scaledHop c (ℓ / L)
    let Ψ := devicePacket (L := L) J μ₀ μ₁ W β
    let R := levelClockRate μ₀ μ₁ (2 * J * Real.sin (ℓ / L * p₀))
    (∀ t, HasDerivAt Ψ ((-I) • (deviceHam J μ₀ μ₁ *ᵥ Ψ t)) t)
    ∧ (∀ t, deviceNorm (Ψ t) = 1)
    ∧ (∀ t, ‖deviceTrans (Ψ t)
        - exp (I * (((2 * Real.pi / ℓ * vRel c μ₀ (c * p₀) : ℝ) : ℂ) * t)) * deviceTrans (Ψ 0)‖
        ≤ |t| * ((limitErr c μ₀ ℓ D P (ℓ / L) + limitErr c μ₁ ℓ D P (ℓ / L)) / 2
          + 2 * Real.pi / ℓ * |vRel c μ₁ (c * p₀) - vRel c μ₀ (c * p₀)| / 2))
    ∧ |vRel c μ₁ (c * p₀) - vRel c μ₀ (c * p₀)| ≤ c * (μ₁ - μ₀) / μ₀
    ∧ (∀ t, ‖deviceCoherence (Ψ t) - exp (I * (((-R : ℝ) : ℂ) * t)) * deviceCoherence (Ψ 0)‖
        ≤ |t| * (c * D))
    ∧ (1 - ((μ₁ - μ₀) / μ₀) ^ 2) / 2 ≤ ‖deviceCoherence (Ψ 0)‖
    ∧ (∀ t, ‖deviceCoherence (Ψ 0)‖
        * ‖deviceCoherence (Ψ t) / (‖deviceCoherence (Ψ t)‖ : ℂ)
          - exp (I * (((-R : ℝ) : ℂ) * t))
            * (deviceCoherence (Ψ 0) / (‖deviceCoherence (Ψ 0)‖ : ℂ))‖
        ≤ 2 * (|t| * (c * D)))
    ∧ (μ₀ < μ₁ → |R / (μ₁ - μ₀)
        - Real.sqrt (1 - (vRel c μ₀ (2 * J * Real.sin (ℓ / L * p₀)) / c) ^ 2)|
        ≤ (μ₁ - μ₀) / dispE μ₀ (2 * J * Real.sin (ℓ / L * p₀))) := by
  intro J Ψ R
  have h1 : 0 < μ₁ := h0.trans_le h01
  obtain ⟨hW, hDst⟩ := noWrap_distinct_of_window (L := L) hWin
  obtain ⟨hn0, -, hdr0, -, -⟩ := dirac_packet_limit hc h0 hℓ hp₀ hD0 hWin hWD β hβ
  obtain ⟨hn1, hT1, hdr1, -, -⟩ := dirac_packet_limit hc h1 hℓ hp₀ hD0 hWin hWD β hβ
  have hobs := fun t => device_observables (L := L) J μ₀ μ₁ W β t
  -- the coherence's rate
  have hrate : ∀ t, ‖deviceCoherence (Ψ t) - exp (I * (((-R : ℝ) : ℂ) * t))
      * deviceCoherence (Ψ 0)‖ ≤ |t| * (c * D) := fun t => by
    rw [(hobs t).2.2, (hobs 0).2.2]
    have h := levelCoherence_rate (L := L) (J := J) h0 h1 hDst (unitAmp L J μ₀ β)
      (unitAmp L J μ₁ β) (ℓ / L * p₀) t
    have he := levelError_scaled_le (L := L) hc h0 h01 hℓ hWD β hβ
    rw [show (1 / 2 : ℂ) * levelCoherence (L := L) J μ₀ μ₁ W (unitAmp L J μ₀ β) (unitAmp L J μ₁ β) t
        - exp (I * (((-R : ℝ) : ℂ) * t)) * ((1 / 2 : ℂ)
          * levelCoherence (L := L) J μ₀ μ₁ W (unitAmp L J μ₀ β) (unitAmp L J μ₁ β) 0)
        = (1 / 2 : ℂ) * (levelCoherence (L := L) J μ₀ μ₁ W (unitAmp L J μ₀ β) (unitAmp L J μ₁ β) t
          - exp (I * (((-R : ℝ) : ℂ) * t))
            * levelCoherence (L := L) J μ₀ μ₁ W (unitAmp L J μ₀ β) (unitAmp L J μ₁ β) 0) by ring,
      norm_mul]
    have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [hhalf]
    calc 1 / 2 * ‖levelCoherence (L := L) J μ₀ μ₁ W _ _ t - _‖
        ≤ 1 / 2 * (|t| * (2 * c * D)) := by
          gcongr
          exact h.trans (mul_le_mul_of_nonneg_left he (abs_nonneg t))
      _ = |t| * (c * D) := by ring
  -- the coherence at the start
  have hC0 : (1 - ((μ₁ - μ₀) / μ₀) ^ 2) / 2 ≤ ‖deviceCoherence (Ψ 0)‖ := by
    rw [(hobs 0).2.2, levelCoherence_eq J μ₀ μ₁ hDst _ _ 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul,
      Complex.re_sum]
    have hsum : (1 - ((μ₁ - μ₀) / μ₀) ^ 2) * ∑ m ∈ W, ‖β m‖ ^ 2
        ≤ ∑ m ∈ W, (levelWeight (L := L) J μ₀ μ₁ (unitAmp L J μ₀ β) (unitAmp L J μ₁ β) m).re := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun m _ => (levelWeight_unitAmp_bounds (L := L) h0 h01 β m).1
    rw [hβ, mul_one] at hsum
    linarith
  refine ⟨fun t => hasDerivAt_devicePacket J μ₀ μ₁ W β t, fun t => ?_, fun t => ?_,
    abs_vRel_sub_le hc.le h0 h01 _, hrate, hC0, fun t => ?_, fun hlt => ?_⟩
  · -- normalisation
    rw [(hobs t).1]
    have e0 : chainInner (packet (L := L) J μ₀ W (unitAmp L J μ₀ β) t)
        (packet (L := L) J μ₀ W (unitAmp L J μ₀ β) t) = 1 := hn0 t
    have e1 : chainInner (packet (L := L) J μ₁ W (unitAmp L J μ₁ β) t)
        (packet (L := L) J μ₁ W (unitAmp L J μ₁ β) t) = 1 := hn1 t
    rw [e0, e1]
    norm_num
  · -- position
    rw [(hobs t).2.1, (hobs 0).2.1]
    set T0t := transPhase (packet (L := L) J μ₀ W (unitAmp L J μ₀ β) t)
    set T1t := transPhase (packet (L := L) J μ₁ W (unitAmp L J μ₁ β) t)
    set T00 := transPhase (packet (L := L) J μ₀ W (unitAmp L J μ₀ β) 0)
    set T10 := transPhase (packet (L := L) J μ₁ W (unitAmp L J μ₁ β) 0)
    set e0 := exp (I * (((2 * Real.pi / ℓ * vRel c μ₀ (c * p₀) : ℝ) : ℂ) * t))
    set e1 := exp (I * (((2 * Real.pi / ℓ * vRel c μ₁ (c * p₀) : ℝ) : ℂ) * t))
    have hd0 : ‖T0t - e0 * T00‖ ≤ |t| * limitErr c μ₀ ℓ D P (ℓ / L) := hdr0 t
    have hd1 : ‖T1t - e1 * T10‖ ≤ |t| * limitErr c μ₁ ℓ D P (ℓ / L) := hdr1 t
    have hT10 : ‖T10‖ ≤ 1 := hT1
    have he : ‖e1 - e0‖ ≤ 2 * Real.pi / ℓ * |vRel c μ₁ (c * p₀) - vRel c μ₀ (c * p₀)| * |t| := by
      have hsplit : e1 - e0 = e0 * (exp (I * ((((2 * Real.pi / ℓ * vRel c μ₁ (c * p₀))
          - 2 * Real.pi / ℓ * vRel c μ₀ (c * p₀)) * t : ℝ) : ℂ)) - 1) := by
        simp only [e0, e1]
        rw [mul_sub, mul_one, ← Complex.exp_add]
        congr 2
        push_cast
        ring
      rw [hsplit, norm_mul, norm_exp_I_mul_ofReal_mul, one_mul]
      refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
      rw [Real.norm_eq_abs, abs_mul, ← mul_sub, abs_mul, abs_of_pos (by positivity)]
    have hsplit : (1 / 2 : ℂ) * (T0t + T1t) - e0 * ((1 / 2 : ℂ) * (T00 + T10))
        = (1 / 2 : ℂ) * ((T0t - e0 * T00) + (T1t - e1 * T10) + (e1 - e0) * T10) := by ring
    rw [hsplit, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    have h3 : ‖(e1 - e0) * T10‖ ≤ 2 * Real.pi / ℓ * |vRel c μ₁ (c * p₀) - vRel c μ₀ (c * p₀)| * |t| := by
      rw [norm_mul]
      calc ‖e1 - e0‖ * ‖T10‖ ≤ ‖e1 - e0‖ * 1 := mul_le_mul_of_nonneg_left hT10 (norm_nonneg _)
        _ ≤ _ := by rw [mul_one]; exact he
    have htri : ‖(T0t - e0 * T00) + (T1t - e1 * T10) + (e1 - e0) * T10‖
        ≤ ‖T0t - e0 * T00‖ + ‖T1t - e1 * T10‖ + ‖(e1 - e0) * T10‖ := norm_add₃_le
    calc 1 / 2 * ‖(T0t - e0 * T00) + (T1t - e1 * T10) + (e1 - e0) * T10‖
        ≤ 1 / 2 * (|t| * limitErr c μ₀ ℓ D P (ℓ / L) + |t| * limitErr c μ₁ ℓ D P (ℓ / L)
          + 2 * Real.pi / ℓ * |vRel c μ₁ (c * p₀) - vRel c μ₀ (c * p₀)| * |t|) := by
          gcongr
          linarith
      _ = _ := by ring
  · -- the reading
    set C0 := deviceCoherence (Ψ 0)
    set Ct := deviceCoherence (Ψ t)
    set e := exp (I * (((-R : ℝ) : ℂ) * t))
    have h := norm_mul_norm_div_sub_le Ct (e * C0)
    have hn : ‖e * C0‖ = ‖C0‖ := by
      rw [norm_mul, norm_exp_I_mul_ofReal_mul, one_mul]
    rw [hn, mul_div_assoc] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hrate t) two_pos.le)
  · -- the dilation
    exact abs_clockRate_div_sub_le hc.ne' h0 hlt _

end CSD.CV

end
