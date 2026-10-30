/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.DiracClockChain
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# A localised device on the Dirac chain

**Category:** 3-Local (CV). BACKLOG #250 (residue of ~~#249~~).

~~#249~~ proved the internal clock's dilation on exact plane-wave modes, which spread over the ring.
Here the device is localised: a **packet** of upper-band modes on a finite window of momenta, carrying
the two-level clock. Its evolution is exact (a finite sum of modes, each advancing by its phase), and
its position is read on the ring through the **translation phase** `T = ⟨ψ, e^{2πi x̂/L} ψ⟩`, whose
argument is the circular position and whose modulus is the localisation.

## Estimates in the angle

* ★ `norm_sum_phase_sub_le` — a sum of phases at nearby rates rotates at a common rate, within `|t|`
  times the weighted spread;
* `bandE`, `groupVel`, `hasDerivAt_bandE`, `abs_groupVel_le'`, `groupVel_eq`
  (`v_g = 2J² sin 2θ / E`), `le_bandE`; ★ `abs_bandE_sub_le` — the band energy is `2|J|`-Lipschitz;
  ★★ `abs_groupVel_sub_le` — **the group velocity is Lipschitz** with `C = 4J²/μ + 4|J|³/μ²`;
  ★★ `abs_bandE_step_sub_le` — the energy step between neighbouring momenta is `h v_g(θ₀)` within
  `C h (|θ − θ₀| + h)`.

## Modes on the ring

* `angleZ`, `latticeAngle_intCast_sin`, `dispE_modeS_intCast` — integer momenta, the mode's energy
  the band energy at `2πm/L`; `modeSpin`, `diracMode_eq`; `chainInner`; ★ `sum_toCircle_mul` (the
  ring's characters sum to zero unless trivial), ★★ `chainInner_planeWave` — **plane waves are
  orthogonal**; `transMul`, ★ `transPhase`, `transMul_mode` (the phase raises the momentum by one).

## The packet

* `packet`, ★ `hasDerivAt_packet` — **it solves Schrödinger's equation**; `NoWrap`, `Distinct`,
  ★ `noWrap_distinct_of_window` (a window shorter than the ring has neither); `chainInner_sum_left`,
  `chainInner_sum_right`, `transMul_sum`, `spinOverlap`, `transWeight`, `star_exp_neg_I_mul`;
* ★★ `transPhase_packet` — **the translation phase exactly**: a sum over neighbouring pairs of phases
  turning at `E_{m+1} − E_m`;
* `vgLip`, `angleZ_succ`, `driftError`; ★★★ `transPhase_drift` — **the packet moves at the group
  velocity**: `T(t)` rotates at `(2π/L) v_g(θ₀)` within `|t|` times the drift error;
  ★★ `norm_transPhase_ge` — **it stays localised**, `|T(t)| ≥ |T(0)| − |t| · error`;
* `clockOverlap` (the coherence between the two internal levels; its phase is the clock's reading),
  `clockWeight`, ★★ `clockOverlap_eq`, `clockError`; ★★★ `clockOverlap_rate` — **the moving clock ticks
  at the window centre's dilated rate** within `|t|` times the window's spread;
* ★★★ `dirac_packet` — the package.

## Honest scope

⚠️ **Position on a ring is an angle.** The translation phase is the standard circular position
(its argument times `L/2π`) and circular localisation (its modulus); a linear position on a ring is
not defined. For a packet narrow in space on a long ring the two agree.

⚠️ **The errors grow linearly in `t`** and are controlled by the window's spread about `θ₀`; a narrow
window in momentum is a wide packet in space, so the horizon over which a packet is both localised and
on course is finite, as the brief allows. No explicit Gaussian instance is computed.

⚠️ **No records yet.** The position and the clock are read as expectation values; reading them by
detectors on the sites, as `ActualOccurrence`s, is #242's remaining work for this candidate.

References: `specs/BACKLOG.md` #250, #249, #241, #242, #39; `CV/DiracClockChain.lean`
(`diracHam`, `diracMode`, `diracHam_mulVec_diracMode`, `hasDerivAt_dispE_lattice`,
`abs_clockRate_div_sub_le`); R. Resta, PRL 80 (1998) 1800 (the position on a ring as a phase).
-/

@[expose] public section

open Complex Matrix

noncomputable section

namespace CSD.CV

/-! ### Sums of phases -/

/-- ★ **A sum of phases rotating at nearby rates rotates at a common rate**, within `|t|` times the
weighted spread of the rates. -/
theorem norm_sum_phase_sub_le {ι : Type*} (s : Finset ι) (c : ι → ℂ) (Δ : ι → ℝ) (Ω t : ℝ) :
    ‖∑ i ∈ s, c i * exp (I * (Δ i * t)) - exp (I * (Ω * t)) * ∑ i ∈ s, c i‖
      ≤ |t| * ∑ i ∈ s, ‖c i‖ * |Δ i - Ω| := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have h : c i * exp (I * (Δ i * t)) - exp (I * (Ω * t)) * c i
      = c i * exp (I * (Ω * t)) * (exp (I * ((Δ i - Ω) * t : ℝ)) - 1) := by
    push_cast
    rw [mul_sub, mul_one, mul_assoc, ← Complex.exp_add]
    ring_nf
  rw [h, norm_mul, norm_mul, show (I * (Ω * t)) = (I * ((Ω * t : ℝ) : ℂ)) by push_cast; ring,
    Complex.norm_exp_I_mul_ofReal, mul_one]
  calc ‖c i‖ * ‖exp (I * ((Δ i - Ω) * t : ℝ)) - 1‖ ≤ ‖c i‖ * ‖(Δ i - Ω) * t‖ :=
        mul_le_mul_of_nonneg_left Real.norm_exp_I_mul_ofReal_sub_one_le (norm_nonneg _)
    _ = |t| * (‖c i‖ * |Δ i - Ω|) := by
        rw [Real.norm_eq_abs, abs_mul]
        ring

/-! ### The band energy and the group velocity as functions of the angle -/

/-- The upper band's energy at angle `θ`: `E(θ) = √(μ² + (2J sin θ)²)`. -/
def bandE (J μ θ : ℝ) : ℝ := dispE μ (2 * J * Real.sin θ)

/-- The group velocity at angle `θ`: `E'(θ) = v_rel · cos θ`. -/
def groupVel (J μ θ : ℝ) : ℝ := vRel (2 * J) μ (2 * J * Real.sin θ) * Real.cos θ

theorem hasDerivAt_bandE {J μ : ℝ} (hμ : 0 < μ) (θ : ℝ) :
    HasDerivAt (bandE J μ) (groupVel J μ θ) θ :=
  hasDerivAt_dispE_lattice hμ θ

theorem abs_groupVel_le' {J μ : ℝ} (hμ : 0 < μ) (θ : ℝ) : |groupVel J μ θ| ≤ |2 * J| :=
  abs_groupVel_le hμ θ

/-- **The band energy is `2|J|`-Lipschitz** in the angle. -/
theorem abs_bandE_sub_le {J μ : ℝ} (hμ : 0 < μ) (a b : ℝ) :
    |bandE J μ a - bandE J μ b| ≤ |2 * J| * |a - b| := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope (bandE J μ) (groupVel J μ) hab
      (fun x _ => (hasDerivAt_bandE hμ x).continuousAt.continuousWithinAt)
      (fun x _ => hasDerivAt_bandE hμ x)
    have hne : b - a ≠ 0 := by linarith
    rw [eq_div_iff hne] at hc
    rw [abs_sub_comm, ← hc, abs_mul, abs_sub_comm b a]
    exact mul_le_mul_of_nonneg_right (abs_groupVel_le' hμ c) (abs_nonneg _)
  · simp
  · obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope (bandE J μ) (groupVel J μ) hab
      (fun x _ => (hasDerivAt_bandE hμ x).continuousAt.continuousWithinAt)
      (fun x _ => hasDerivAt_bandE hμ x)
    have hne : a - b ≠ 0 := by linarith
    rw [eq_div_iff hne] at hc
    rw [← hc, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_groupVel_le' hμ c) (abs_nonneg _)

theorem groupVel_eq {J μ : ℝ} (hμ : 0 < μ) (θ : ℝ) :
    groupVel J μ θ = 2 * J ^ 2 * Real.sin (2 * θ) / bandE J μ θ := by
  have hE := dispE_pos hμ (2 * J * Real.sin θ)
  rw [groupVel, vRel, bandE, Real.sin_two_mul]
  field_simp

theorem le_bandE (J μ θ : ℝ) : μ ≤ bandE J μ θ := le_dispE μ _

/-- ★★ **The group velocity is Lipschitz** in the angle, with constant
`C = 4J²/μ + 4|J|³/μ²`: the curvature of the band is bounded by the rest energy. -/
theorem abs_groupVel_sub_le {J μ : ℝ} (hμ : 0 < μ) (a b : ℝ) :
    |groupVel J μ a - groupVel J μ b|
      ≤ (4 * J ^ 2 / μ + 4 * |J| ^ 3 / μ ^ 2) * |a - b| := by
  have hEa := (dispE_pos hμ (2 * J * Real.sin a))
  have hEb := (dispE_pos hμ (2 * J * Real.sin b))
  set Ea := bandE J μ a
  set Eb := bandE J μ b
  have hμa : μ ≤ Ea := le_bandE J μ a
  have hμb : μ ≤ Eb := le_bandE J μ b
  set A := 2 * J ^ 2 * Real.sin (2 * a)
  set B := 2 * J ^ 2 * Real.sin (2 * b)
  have hAB : |A - B| ≤ 4 * J ^ 2 * |a - b| := by
    have h := Real.abs_sin_sub_sin_le (2 * a) (2 * b)
    have : A - B = 2 * J ^ 2 * (Real.sin (2 * a) - Real.sin (2 * b)) := by ring
    rw [this, abs_mul, abs_of_nonneg (by positivity)]
    calc 2 * J ^ 2 * |Real.sin (2 * a) - Real.sin (2 * b)| ≤ 2 * J ^ 2 * |2 * a - 2 * b| :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 4 * J ^ 2 * |a - b| := by
          rw [show 2 * a - 2 * b = 2 * (a - b) by ring, abs_mul, abs_two]; ring
  have hB : |B| ≤ 2 * J ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)
  have hE := abs_bandE_sub_le (J := J) hμ b a
  rw [abs_mul, abs_two] at hE
  rw [groupVel_eq hμ, groupVel_eq hμ]
  have hEa0 : 0 < Ea := hEa
  have hEb0 : 0 < Eb := hEb
  have key : A / Ea - B / Eb = (A - B) / Ea + B * (Eb - Ea) / (Ea * Eb) := by
    field_simp
    ring
  rw [key]
  have h1 : |(A - B) / Ea| ≤ 4 * J ^ 2 / μ * |a - b| := by
    rw [abs_div, abs_of_pos hEa0, div_le_iff₀ hEa0]
    calc |A - B| ≤ 4 * J ^ 2 * |a - b| := hAB
      _ ≤ 4 * J ^ 2 / μ * |a - b| * Ea := by
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hμ]
          have : 4 * J ^ 2 * |a - b| * μ ≤ 4 * J ^ 2 * |a - b| * Ea :=
            mul_le_mul_of_nonneg_left hμa (by positivity)
          linarith
  have h2 : |B * (Eb - Ea) / (Ea * Eb)| ≤ 4 * |J| ^ 3 / μ ^ 2 * |a - b| := by
    rw [abs_div, abs_mul, abs_of_pos (mul_pos hEa0 hEb0), div_le_iff₀ (mul_pos hEa0 hEb0)]
    have hJ2 : J ^ 2 = |J| ^ 2 := (sq_abs J).symm
    calc |B| * |Eb - Ea| ≤ 2 * J ^ 2 * (2 * |J| * |b - a|) :=
          mul_le_mul hB hE (abs_nonneg _) (by positivity)
      _ = 4 * |J| ^ 3 * |a - b| := by rw [hJ2, abs_sub_comm b a]; ring
      _ ≤ 4 * |J| ^ 3 / μ ^ 2 * |a - b| * (Ea * Eb) := by
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          have hEE : μ ^ 2 ≤ Ea * Eb := by nlinarith
          nlinarith [abs_nonneg (a - b), pow_nonneg (abs_nonneg J) 3,
            mul_le_mul_of_nonneg_left hEE (mul_nonneg (pow_nonneg (abs_nonneg J) 3)
              (abs_nonneg (a - b)))]
  calc |(A - B) / Ea + B * (Eb - Ea) / (Ea * Eb)| ≤ |(A - B) / Ea| + |B * (Eb - Ea) / (Ea * Eb)| :=
        abs_add_le _ _
    _ ≤ _ := by linarith

/-- ★★ **The energy step between neighbouring momenta is the group velocity times the step**, within
`C · h · (|θ − θ₀| + h)`. -/
theorem abs_bandE_step_sub_le {J μ : ℝ} (hμ : 0 < μ) {h : ℝ} (hh : 0 < h) (θ θ₀ : ℝ) :
    |(bandE J μ (θ + h) - bandE J μ θ) - h * groupVel J μ θ₀|
      ≤ (4 * J ^ 2 / μ + 4 * |J| ^ 3 / μ ^ 2) * h * (|θ - θ₀| + h) := by
  obtain ⟨ξ, hξ, hc⟩ := exists_hasDerivAt_eq_slope (bandE J μ) (groupVel J μ)
    (show θ < θ + h by linarith)
    (fun x _ => (hasDerivAt_bandE hμ x).continuousAt.continuousWithinAt)
    (fun x _ => hasDerivAt_bandE hμ x)
  rw [show θ + h - θ = h by ring, eq_div_iff hh.ne'] at hc
  rw [← hc, mul_comm (groupVel J μ ξ) h, ← mul_sub, abs_mul, abs_of_pos hh]
  have hl := abs_groupVel_sub_le (J := J) hμ ξ θ₀
  have hd : |ξ - θ₀| ≤ |θ - θ₀| + h := by
    calc |ξ - θ₀| = |(ξ - θ) + (θ - θ₀)| := by ring_nf
      _ ≤ |ξ - θ| + |θ - θ₀| := abs_add_le _ _
      _ ≤ h + |θ - θ₀| := by
          gcongr
          rw [abs_of_pos (by linarith [hξ.1])]
          linarith [hξ.2]
      _ = |θ - θ₀| + h := by ring
  have hC : 0 ≤ 4 * J ^ 2 / μ + 4 * |J| ^ 3 / μ ^ 2 := by positivity
  calc h * |groupVel J μ ξ - groupVel J μ θ₀|
      ≤ h * ((4 * J ^ 2 / μ + 4 * |J| ^ 3 / μ ^ 2) * |ξ - θ₀|) :=
        mul_le_mul_of_nonneg_left hl hh.le
    _ ≤ h * ((4 * J ^ 2 / μ + 4 * |J| ^ 3 / μ ^ 2) * (|θ - θ₀| + h)) := by gcongr
    _ = _ := by ring

/-! ### Modes on the ring, and their overlaps -/

variable {L : ℕ} [NeZero L]

/-- The integer momentum `m` read as an angle, `θ_m = 2πm/L`. -/
def angleZ (L : ℕ) (m : ℤ) : ℝ := 2 * Real.pi * m / L

theorem latticeAngle_intCast_sin (m : ℤ) :
    Real.sin (latticeAngle (m : ZMod L)) = Real.sin (angleZ L m) := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hv : (((m : ZMod L).val : ℤ) : ℝ) = (m : ℝ) - ((m / L : ℤ) : ℝ) * L := by
    rw [ZMod.val_intCast]
    have := Int.emod_def m L
    rw [this]
    push_cast
    ring
  rw [latticeAngle, angleZ, show (2 * Real.pi * ((m : ZMod L).val : ℝ) / L)
      = 2 * Real.pi * m / L - ((m / L : ℤ) : ℝ) * (2 * Real.pi) by
    rw [show (((m : ZMod L).val : ℕ) : ℝ) = (((m : ZMod L).val : ℤ) : ℝ) by push_cast; rfl, hv]
    field_simp, Real.sin_sub_int_mul_two_pi]

/-- **The mode of integer momentum `m` has the band energy at `θ_m`.** -/
theorem dispE_modeS_intCast (J μ : ℝ) (m : ℤ) :
    dispE μ (modeS J (m : ZMod L)) = bandE J μ (angleZ L m) := by
  rw [modeS, bandE, latticeAngle_intCast_sin]

/-- The two-component spinor of mode `n`, `(μ + E, s)`. -/
def modeSpin (J μ : ℝ) (n : ZMod L) : Fin 2 → ℂ := fun a =>
  if a = 0 then ((μ + dispE μ (modeS J n) : ℝ) : ℂ) else (modeS J n : ℂ)

theorem diracMode_eq (J μ : ℝ) (n : ZMod L) :
    diracMode J μ n = fun p => planeWave n p.1 * modeSpin J μ n p.2 := rfl

/-- The inner product on the chain. -/
def chainInner (u v : ZMod L × Fin 2 → ℂ) : ℂ := ∑ p, star (u p) * v p

/-- **The sum of a character over the ring**: `L` for the trivial one, `0` otherwise. -/
theorem sum_toCircle_mul (k : ZMod L) :
    ∑ j : ZMod L, (ZMod.toCircle (k * j) : ℂ) = if k = 0 then (L : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp [ZMod.card]
  · rw [ite_eq_right hk]
    have hshift : ∑ j : ZMod L, (ZMod.toCircle (k * j) : ℂ)
        = (ZMod.toCircle k : ℂ) * ∑ j : ZMod L, (ZMod.toCircle (k * j) : ℂ) := by
      have h := Equiv.sum_comp (Equiv.addRight (1 : ZMod L)) (fun j => (ZMod.toCircle (k * j) : ℂ))
      conv_lhs => rw [← h]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Equiv.coe_addRight, mul_add, mul_one, AddChar.map_add_eq_mul, Circle.coe_mul]
      ring
    have hne : (ZMod.toCircle k : ℂ) ≠ 1 := by
      intro h
      apply hk
      apply ZMod.injective_toCircle
      rw [AddChar.map_zero_eq_one]
      exact Circle.ext (by simpa using h)
    have : (1 - (ZMod.toCircle k : ℂ)) * ∑ j : ZMod L, (ZMod.toCircle (k * j) : ℂ) = 0 := by
      rw [sub_mul, one_mul, ← hshift, sub_self]
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h).symm hne
    · exact h

/-- **Plane waves are orthogonal**: two products of a plane wave and a spinor overlap only at the same
momentum, with weight `L`. -/
theorem chainInner_planeWave (n' n : ZMod L) (v' v : Fin 2 → ℂ) :
    chainInner (fun p => planeWave n' p.1 * v' p.2) (fun p => planeWave n p.1 * v p.2)
      = (if n' = n then (L : ℂ) else 0) * ∑ a, star (v' a) * v a := by
  have hpw : ∀ j : ZMod L, star (planeWave n' j) * planeWave n j
      = (ZMod.toCircle ((n - n') * j) : ℂ) := by
    intro j
    rw [planeWave, planeWave, Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul,
      ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  rw [chainInner, Fintype.sum_prod_type]
  simp only [star_mul']
  calc ∑ j, ∑ a, star (planeWave n' j) * star (v' a) * (planeWave n j * v a)
      = ∑ j, (star (planeWave n' j) * planeWave n j) * ∑ a, star (v' a) * v a := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
    _ = _ := by
        simp only [hpw]
        rw [← Finset.sum_mul, sum_toCircle_mul]
        congr 1
        by_cases h : n' = n
        · rw [ite_eq_left (sub_eq_zero.2 h.symm), ite_eq_left h]
        · rw [ite_eq_right (fun h' => h (sub_eq_zero.1 h').symm), ite_eq_right h]

/-! ### The translation phase -/

/-- **Multiplication by `e^{2πi j/L}`**: the position read as a phase on the ring. -/
def transMul (v : ZMod L × Fin 2 → ℂ) : ZMod L × Fin 2 → ℂ := fun p => (ZMod.toCircle p.1 : ℂ) * v p

/-- ★ **The translation phase** `T = ⟨ψ, e^{2πi x̂/L} ψ⟩`: its argument times `L/2π` is the circular
position, its modulus the localisation (`1` for a state at one site). -/
def transPhase (ψ : ZMod L × Fin 2 → ℂ) : ℂ := chainInner ψ (transMul ψ)

theorem transMul_mode (J μ : ℝ) (n : ZMod L) :
    transMul (diracMode J μ n) = fun p => planeWave (n + 1) p.1 * modeSpin J μ n p.2 := by
  funext ⟨j, a⟩
  simp only [transMul, diracMode_eq, planeWave]
  rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  congr 3
  ring

/-! ### Packets -/

/-- **A packet of upper-band modes**: amplitudes `a m` on a finite window `W` of integer momenta, each
mode advancing by its phase. -/
def packet (J μ : ℝ) (W : Finset ℤ) (a : ℤ → ℂ) (t : ℝ) : ZMod L × Fin 2 → ℂ :=
  ∑ m ∈ W, (a m * exp (-(I * bandE J μ (angleZ L m)) * t)) • diracMode J μ (m : ZMod L)

/-- ★ **The packet solves Schrödinger's equation** `i ψ' = H ψ`. -/
theorem hasDerivAt_packet (J μ : ℝ) (W : Finset ℤ) (a : ℤ → ℂ) (t : ℝ) :
    HasDerivAt (packet (L := L) J μ W a) ((-I) • (diracHam J μ *ᵥ packet (L := L) J μ W a t)) t := by
  unfold packet
  rw [Matrix.mulVec_sum, Finset.smul_sum]
  refine HasDerivAt.fun_sum fun m _ => ?_
  have h := (hasDerivAt_diracMode (L := L) J μ (m : ZMod L) t).const_smul (a m)
  rw [dispE_modeS_intCast] at h
  convert h using 1
  · funext s
    rw [Pi.smul_apply, smul_smul]
  · rw [Matrix.mulVec_smul, Matrix.mulVec_smul, smul_comm (a m) (-I), smul_smul, smul_smul,
      smul_smul]
    ring_nf

/-- **No wrap-around**: in the window, `m + 1` is congruent to a window element only as itself. -/
def NoWrap (L : ℕ) (W : Finset ℤ) : Prop :=
  ∀ m ∈ W, ∀ m' ∈ W, ((m' : ZMod L) = ((m + 1 : ℤ) : ZMod L) ↔ m' = m + 1)

/-- **Distinct momenta**: the window's elements are distinct modulo `L`. -/
def Distinct (L : ℕ) (W : Finset ℤ) : Prop :=
  ∀ m ∈ W, ∀ m' ∈ W, ((m' : ZMod L) = (m : ZMod L) ↔ m' = m)

omit [NeZero L] in
/-- ★ **A window shorter than the ring has neither wrap-around nor repeated momenta.** -/
theorem noWrap_distinct_of_window {W : Finset ℤ} {lo : ℤ} (hW : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L) :
    NoWrap L W ∧ Distinct L W := by
  have key : ∀ x y : ℤ, lo ≤ x → x < lo + L → lo ≤ y → y < lo + L →
      ((x : ZMod L) = (y : ZMod L) ↔ x = y) := by
    intro x y hx1 hx2 hy1 hy2
    refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
    have hd : (L : ℤ) ∣ x - y := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [h, sub_self]
    have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> linarith)
    linarith
  refine ⟨fun m hm m' hm' => ?_, fun m hm m' hm' => ?_⟩
  · obtain ⟨h1, h2⟩ := hW m hm
    obtain ⟨h1', h2'⟩ := hW m' hm'
    exact key m' (m + 1) h1' (by linarith) (by linarith) h2
  · obtain ⟨h1, h2⟩ := hW m hm
    obtain ⟨h1', h2'⟩ := hW m' hm'
    exact key m' m h1' (by linarith) h1 (by linarith)

theorem chainInner_sum_left {ι : Type*} (s : Finset ι) (c : ι → ℂ) (u : ι → ZMod L × Fin 2 → ℂ)
    (v : ZMod L × Fin 2 → ℂ) :
    chainInner (∑ i ∈ s, c i • u i) v = ∑ i ∈ s, star (c i) * chainInner (u i) v := by
  simp only [chainInner, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, star_mul',
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by ring

theorem chainInner_sum_right {ι : Type*} (s : Finset ι) (c : ι → ℂ) (u : ZMod L × Fin 2 → ℂ)
    (v : ι → ZMod L × Fin 2 → ℂ) :
    chainInner u (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i * chainInner u (v i) := by
  simp only [chainInner, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by ring

theorem transMul_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (v : ι → ZMod L × Fin 2 → ℂ) :
    transMul (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • transMul (v i) := by
  funext p
  simp only [transMul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The spinor overlap of neighbouring momenta. -/
def spinOverlap (J μ₀ μ₁ : ℝ) (m' m : ℤ) : ℂ :=
  ∑ b, star (modeSpin J μ₀ (m' : ZMod L) b) * modeSpin J μ₁ (m : ZMod L) b

/-- The weight of the pair `(m, m + 1)` in the translation phase. -/
def transWeight (J μ : ℝ) (a : ℤ → ℂ) (m : ℤ) : ℂ :=
  (L : ℂ) * star (a (m + 1)) * a m * spinOverlap (L := L) J μ μ (m + 1) m

theorem star_exp_neg_I_mul (E t : ℝ) : star (exp (-(I * E) * t)) = exp (I * (E * t)) := by
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]
  ring

/-- ★★ **The translation phase of a packet, exactly**: a sum over neighbouring pairs in the window of
phases rotating at the energy steps `E_{m+1} − E_m`. -/
theorem transPhase_packet (J μ : ℝ) {W : Finset ℤ} (hW : NoWrap L W) (a : ℤ → ℂ) (t : ℝ) :
    transPhase (packet (L := L) J μ W a t)
      = ∑ m ∈ W.filter (fun m => m + 1 ∈ W), transWeight (L := L) J μ a m
          * exp (I * (((bandE J μ (angleZ L (m + 1)) - bandE J μ (angleZ L m) : ℝ) : ℂ) * t)) := by
  unfold transPhase packet
  rw [transMul_sum, chainInner_sum_left]
  simp only [chainInner_sum_right, transMul_mode]
  simp only [diracMode_eq, chainInner_planeWave]
  have hcond : ∀ m ∈ W, ∀ m' ∈ W, ((m' : ZMod L) = (m : ZMod L) + 1 ↔ m' = m + 1) := by
    intro m hm m' hm'
    rw [← hW m hm m' hm']
    push_cast
    rfl
  set c : ℤ → ℂ := fun m => a m * exp (-(I * bandE J μ (angleZ L m)) * t) with hc
  calc ∑ m' ∈ W, star (c m') * ∑ m ∈ W, c m
          * ((if (m' : ZMod L) = ((m : ZMod L)) + 1 then (L : ℂ) else 0)
            * ∑ b, star (modeSpin J μ (m' : ZMod L) b) * modeSpin J μ (m : ZMod L) b)
      = ∑ m' ∈ W, ∑ m ∈ W, if m' = m + 1 then star (c m') * (c m
            * ((L : ℂ) * spinOverlap (L := L) J μ μ m' m)) else 0 := by
        refine Finset.sum_congr rfl fun m' hm' => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        by_cases h : m' = m + 1
        · rw [ite_eq_left ((hcond m hm m' hm').2 h), ite_eq_left h, spinOverlap]
        · rw [ite_eq_right (fun h' => h ((hcond m hm m' hm').1 h')), ite_eq_right h, zero_mul,
            mul_zero, mul_zero]
    _ = ∑ m ∈ W, if m + 1 ∈ W then star (c (m + 1)) * (c m
            * ((L : ℂ) * spinOverlap (L := L) J μ μ (m + 1) m)) else 0 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_ite_eq']
    _ = _ := by
        rw [← Finset.sum_filter]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [hc]
        rw [star_mul', star_exp_neg_I_mul, transWeight]
        have hexp : exp (I * (bandE J μ (angleZ L (m + 1)) * t))
            * exp (-(I * bandE J μ (angleZ L m)) * t)
            = exp (I * (((bandE J μ (angleZ L (m + 1)) - bandE J μ (angleZ L m) : ℝ) : ℂ) * t)) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        rw [← hexp]
        ring

/-! ### The packet moves at the group velocity -/

/-- The Lipschitz constant of the group velocity, `C = 4J²/μ + 4|J|³/μ²`. -/
def vgLip (J μ : ℝ) : ℝ := 4 * J ^ 2 / μ + 4 * |J| ^ 3 / μ ^ 2

omit [NeZero L] in
theorem angleZ_succ (m : ℤ) : angleZ L (m + 1) = angleZ L m + 2 * Real.pi / L := by
  rw [angleZ, angleZ]
  push_cast
  ring

/-- **The drift error**: `|t|` times the weighted spread of the window's energy steps about
`(2π/L) v_g(θ₀)`. -/
def driftError (J μ : ℝ) (W : Finset ℤ) (a : ℤ → ℂ) (θ₀ : ℝ) : ℝ :=
  ∑ m ∈ W.filter (fun m => m + 1 ∈ W), ‖transWeight (L := L) J μ a m‖
    * (vgLip J μ * (2 * Real.pi / L) * (|angleZ L m - θ₀| + 2 * Real.pi / L))

/-- ★★★ **The packet moves at the group velocity**: its translation phase rotates at
`(2π/L) v_g(θ₀)` — the circular position advancing `v_g(θ₀)` sites per unit time — within
`|t|` times the drift error, which is small when the window is narrow about `θ₀`. -/
theorem transPhase_drift {J μ : ℝ} (hμ : 0 < μ) {W : Finset ℤ} (hW : NoWrap L W) (a : ℤ → ℂ)
    (θ₀ t : ℝ) :
    ‖transPhase (packet (L := L) J μ W a t)
        - exp (I * (((2 * Real.pi / L * groupVel J μ θ₀ : ℝ) : ℂ) * t)) * transPhase (packet (L := L) J μ W a 0)‖
      ≤ |t| * driftError (L := L) J μ W a θ₀ := by
  have hL : (0 : ℝ) < 2 * Real.pi / L := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  rw [transPhase_packet J μ hW a t, transPhase_packet J μ hW a 0]
  simp only [mul_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  refine (norm_sum_phase_sub_le _ _ _ _ t).trans ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => ?_) (abs_nonneg t)
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [angleZ_succ]
  exact abs_bandE_step_sub_le hμ hL (angleZ L m) θ₀

/-- ★★ **The packet stays localised**: the modulus of its translation phase drops by at most the
drift error over time `t`. -/
theorem norm_transPhase_ge {J μ : ℝ} (hμ : 0 < μ) {W : Finset ℤ} (hW : NoWrap L W) (a : ℤ → ℂ)
    (θ₀ t : ℝ) :
    ‖transPhase (packet (L := L) J μ W a 0)‖ - |t| * driftError (L := L) J μ W a θ₀
      ≤ ‖transPhase (packet (L := L) J μ W a t)‖ := by
  have h := transPhase_drift (L := L) (J := J) hμ hW a θ₀ t
  have hn : ‖exp (I * (((2 * Real.pi / L * groupVel J μ θ₀ : ℝ) : ℂ) * t))‖ = 1 := by
    rw [show I * (((2 * Real.pi / L * groupVel J μ θ₀ : ℝ) : ℂ) * t)
        = I * ((2 * Real.pi / L * groupVel J μ θ₀ * t : ℝ) : ℂ) by push_cast; ring]
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have h2 := norm_sub_norm_le (exp (I * (((2 * Real.pi / L * groupVel J μ θ₀ : ℝ) : ℂ) * t))
    * transPhase (packet (L := L) J μ W a 0)) (transPhase (packet (L := L) J μ W a t))
  rw [norm_mul, hn, one_mul, norm_sub_rev] at h2
  linarith

/-! ### The clock carried by the packet -/

/-- **The clock's coherence**: the overlap of the packet's two internal levels. Its phase is the
clock's reading. -/
def clockOverlap (J μ₀ μ₁ : ℝ) (W : Finset ℤ) (a : ℤ → ℂ) (t : ℝ) : ℂ :=
  chainInner (packet (L := L) J μ₀ W a t) (packet (L := L) J μ₁ W a t)

/-- The weight of momentum `m` in the clock's coherence. -/
def clockWeight (J μ₀ μ₁ : ℝ) (a : ℤ → ℂ) (m : ℤ) : ℂ :=
  (L : ℂ) * star (a m) * a m * spinOverlap (L := L) J μ₀ μ₁ m m

/-- ★★ **The clock's coherence, exactly**: each momentum's phase turns at `−(E¹_m − E⁰_m)`. -/
theorem clockOverlap_eq (J μ₀ μ₁ : ℝ) {W : Finset ℤ} (hD : Distinct L W) (a : ℤ → ℂ) (t : ℝ) :
    clockOverlap (L := L) J μ₀ μ₁ W a t
      = ∑ m ∈ W, clockWeight (L := L) J μ₀ μ₁ a m
          * exp (I * (((bandE J μ₀ (angleZ L m) - bandE J μ₁ (angleZ L m) : ℝ) : ℂ) * t)) := by
  unfold clockOverlap packet
  rw [chainInner_sum_left]
  simp only [chainInner_sum_right, diracMode_eq, chainInner_planeWave]
  calc ∑ m' ∈ W, star (a m' * exp (-(I * bandE J μ₀ (angleZ L m')) * t))
        * ∑ m ∈ W, a m * exp (-(I * bandE J μ₁ (angleZ L m)) * t)
          * ((if (m' : ZMod L) = (m : ZMod L) then (L : ℂ) else 0)
            * ∑ b, star (modeSpin J μ₀ (m' : ZMod L) b) * modeSpin J μ₁ (m : ZMod L) b)
      = ∑ m' ∈ W, star (a m' * exp (-(I * bandE J μ₀ (angleZ L m')) * t))
          * (a m' * exp (-(I * bandE J μ₁ (angleZ L m')) * t)
            * ((L : ℂ) * spinOverlap (L := L) J μ₀ μ₁ m' m')) := by
        refine Finset.sum_congr rfl fun m' hm' => ?_
        congr 1
        rw [Finset.sum_eq_single m' (fun m hm hne => by
          rw [ite_eq_right (fun h => hne ((hD m hm m' hm').1 h).symm), zero_mul, mul_zero])
          (fun h => absurd hm' h), ite_eq_left rfl, spinOverlap]
    _ = _ := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [star_mul', star_exp_neg_I_mul, clockWeight]
        have hexp : exp (I * (bandE J μ₀ (angleZ L m) * t))
            * exp (-(I * bandE J μ₁ (angleZ L m)) * t)
            = exp (I * (((bandE J μ₀ (angleZ L m) - bandE J μ₁ (angleZ L m) : ℝ) : ℂ) * t)) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        rw [← hexp]
        ring

/-- The clock error: the window's spread of clock rates about `θ₀`. -/
def clockError (J μ₀ μ₁ : ℝ) (W : Finset ℤ) (a : ℤ → ℂ) (θ₀ : ℝ) : ℝ :=
  ∑ m ∈ W, ‖clockWeight (L := L) J μ₀ μ₁ a m‖ * (4 * |J| * |angleZ L m - θ₀|)

/-- ★★★ **The moving clock ticks at its dilated rate**: the packet's clock coherence rotates at the
clock rate of the window's centre, `E¹(θ₀) − E⁰(θ₀)` — which ~~#249~~ shows is the rest rate times
`√(1 − (v/c)²)` — within `|t|` times the window's spread. -/
theorem clockOverlap_rate {J μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h1 : 0 < μ₁) {W : Finset ℤ}
    (hD : Distinct L W) (a : ℤ → ℂ) (θ₀ t : ℝ) :
    ‖clockOverlap (L := L) J μ₀ μ₁ W a t
        - exp (I * (((-levelClockRate μ₀ μ₁ (2 * J * Real.sin θ₀) : ℝ) : ℂ) * t))
          * clockOverlap (L := L) J μ₀ μ₁ W a 0‖
      ≤ |t| * clockError (L := L) J μ₀ μ₁ W a θ₀ := by
  rw [clockOverlap_eq J μ₀ μ₁ hD a t, clockOverlap_eq J μ₀ μ₁ hD a 0]
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
      = |(bandE J μ₀ (angleZ L m) - bandE J μ₀ θ₀) - (bandE J μ₁ (angleZ L m) - bandE J μ₁ θ₀)| := by
        ring_nf
    _ ≤ |bandE J μ₀ (angleZ L m) - bandE J μ₀ θ₀| + |bandE J μ₁ (angleZ L m) - bandE J μ₁ θ₀| :=
        abs_sub _ _
    _ ≤ 4 * |J| * |angleZ L m - θ₀| := by linarith

/-- ★★★ **A localised device on the Dirac chain (#250).** A packet of upper-band modes on a window of
momenta shorter than the ring: it solves Schrödinger's equation; its translation phase is an exact
finite sum of phases; it moves at the group velocity of the window's centre within `|t|` times the
drift error; it stays localised within the same error; and the clock it carries in two internal
levels ticks at the centre's clock rate — `√(1 − (v/c)²)` times its rest rate, by ~~#249~~ —
within `|t|` times the window's spread. -/
theorem dirac_packet {J μ μ₀ μ₁ : ℝ} (hμ : 0 < μ) (h0 : 0 < μ₀) (h1 : 0 < μ₁) {W : Finset ℤ}
    {lo : ℤ} (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L) (a : ℤ → ℂ) (θ₀ : ℝ) :
    (∀ t, HasDerivAt (packet (L := L) J μ W a)
        ((-I) • (diracHam J μ *ᵥ packet (L := L) J μ W a t)) t)
    ∧ (∀ t, ‖transPhase (packet (L := L) J μ W a t)
        - exp (I * (((2 * Real.pi / L * groupVel J μ θ₀ : ℝ) : ℂ) * t)) * transPhase (packet (L := L) J μ W a 0)‖
          ≤ |t| * driftError (L := L) J μ W a θ₀)
    ∧ (∀ t, ‖transPhase (packet (L := L) J μ W a 0)‖ - |t| * driftError (L := L) J μ W a θ₀
        ≤ ‖transPhase (packet (L := L) J μ W a t)‖)
    ∧ (∀ t, ‖clockOverlap (L := L) J μ₀ μ₁ W a t
        - exp (I * (((-levelClockRate μ₀ μ₁ (2 * J * Real.sin θ₀) : ℝ) : ℂ) * t))
          * clockOverlap (L := L) J μ₀ μ₁ W a 0‖
          ≤ |t| * clockError (L := L) J μ₀ μ₁ W a θ₀) := by
  obtain ⟨hW, hD⟩ := noWrap_distinct_of_window (L := L) hWin
  exact ⟨fun t => hasDerivAt_packet J μ W a t, fun t => transPhase_drift hμ hW a θ₀ t,
    fun t => norm_transPhase_ge hμ hW a θ₀ t, fun t => clockOverlap_rate h0 h1 hD a θ₀ t⟩

end CSD.CV

end
