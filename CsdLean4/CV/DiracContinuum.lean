/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.DiracPacket

/-!
# The Dirac chain's continuum limit for modes and the clock

**Category:** 3-Local (CV). BACKLOG #260 (out of an external review of ~~#249~~/~~#250~~).

~~#249~~ and ~~#250~~ prove exact lattice statements and error bounds at fixed hop amplitude `J`
and rest energy `μ`. Their preferred-frame defect `sin² θ` vanishes as `θ → 0`, but at fixed `J`
and `μ` that limit also drives the velocity to zero, so it is not a relativistic limit at
nonzero momentum. This file takes the controlled limit: a physical spacing `a > 0`, `ħ = 1`, the
limiting speed `c > 0` and the rest energy `μ > 0` **held fixed**, and

`J(a) = c/(2a)`, `θ = ap`, `E_a(p) = bandE (J(a), μ, ap)`, `V_a(p) = a · groupVel (J(a), μ, ap)`.

## What is proved, uniformly on `|p| ≤ P`

* `scaledHop`, `scaledMom`, `scaledE`, `scaledV`, `scaledClock`; ★ `two_mul_scaledHop`
  (`a · 2J(a) = c`), `scaledV_eq` (`V_a = v_rel · cos(ap)`);
* ★ `abs_dispE_sub_le` (`E` is `1`-Lipschitz in the momentum term), `hasDerivAt_dispE`,
  `hasDerivAt_div_dispE`, ★ `abs_div_dispE_sub_le` (`s/E` is `1/μ`-Lipschitz), `abs_cos_sub_one_le`;
  ★★ `abs_scaledMom_sub_le` — `|(c/a) sin(ap) − cp| ≤ c a² |p|³/6` (Mathlib's `abs_sub_sin_le`);
* ★★★ `abs_scaledE_sub_le` — **the band energy converges to the massive dispersion**:
  `|E_a(p) − √(μ² + c²p²)| ≤ c a² P³/6`;
* ★★★ `abs_scaledV_sub_le` — **the packet's drift velocity converges to the relativistic one**:
  `|V_a(p) − c²p/√(μ² + c²p²)| ≤ a² (cP²/2 + c²P³/(6μ))`;
* `scaledClock_mem` (the normalised rate is in `[0, 1]`); ★★★ `scaled_clock_dilation_sq_error_le` —
  **the clock against the measured drift velocity**: for levels `μ`, `μ + Δ`,
  `|R_a² − (1 − (V_a/c)²)| ≤ 2Δ/μ + a²P²`, from `abs_clockRate_div_sub_le` (the finite-level error,
  the factor `2` from `R_a, D_a ∈ [0, 1]`) and `lattice_dilation_defect` (the lattice defect,
  `sin²(ap) ≤ a²P²`);
* ★★★ `scaled_limit` — **uniform convergence as `a → 0⁺`**, with the residue `2Δ/μ` kept; ★★
  `scaled_clock_limit` — the clock error tends to zero only when `Δ → 0` as well.

## The findings

1. **The Dirac chain has a controlled relativistic limit for its modes and its clock, at nonzero
   physical momentum.** The errors are `O(a²)`, uniform on bounded momenta, with explicit constants.
2. **The clock is compared with the measured velocity.** ~~#249~~'s exact identity
   `μ/E = √(1 − (v_rel/c)²)` uses the defined velocity `v_rel = cs/E`. Here the comparison is with the
   packet's drift velocity `V_a`, and the lattice defect between the two is part of the bound.
3. **The finite two-level clock keeps an error of its own**, `2Δ/μ`, which does not shrink with the
   spacing. The clock's normalised rate is not claimed to equal one exact dilation factor.

## Honest scope

⚠️ **Modes and the window centre only.** `V_a` is the drift velocity ~~#250~~ proves for a packet's
centre. ~~#250~~'s packet errors are bounded by `vgLip = 4J²/μ + 4|J|³/μ²`, whose second term grows
like `a⁻³` under `J = c/(2a)`. So packet convergence does not follow from the present bounds; it
needs a sharper curvature bound, priced as #261.

⚠️ **Not one device.** `dirac_packet` lets the transport mass `μ` differ from the clock levels `μ₀`,
`μ₁`, and its clock estimate bounds the complex coherence, which gives the clock's phase only while
the coherence stays away from zero. Both levels transported together as one device, with the
reading as a phase, is #262.

⚠️ **No record writes and no observers.** The detector readout of the packet is #252; the observers'
transformation for this chain is #259. The Galilean control's records (~~#242~~–~~#247~~) are a
separate model.

⚠️ **`c` is a scale held fixed, not a value derived.** The residue `2Δ/μ` is an upper bound; its
sharpness is not proved.

References: `specs/BACKLOG.md` #260, #249, #250, #261, #262, #252, #259, #39;
`CV/DiracClockChain.lean` (`dispE`, `vRel`, `levelClockRate`, `div_dispE_eq_sqrt`,
`abs_clockRate_div_sub_le`, `lattice_dilation_defect`); `CV/DiracPacket.lean` (`bandE`, `groupVel`,
`vgLip`, `dirac_packet`).
-/

@[expose] public section

open Filter Topology

namespace CSD.CV

/-! ### The scaling -/

/-- **The hop amplitude at spacing `a`** that holds the limiting speed at `c`: `J(a) = c/(2a)`. -/
noncomputable def scaledHop (c a : ℝ) : ℝ := c / (2 * a)

/-- The lattice momentum term at physical momentum `p`: `2J(a) sin(ap) = (c/a) sin(ap)`. -/
noncomputable def scaledMom (c a p : ℝ) : ℝ := 2 * scaledHop c a * Real.sin (a * p)

/-- **The lattice band energy at physical momentum `p`.** -/
noncomputable def scaledE (c μ a p : ℝ) : ℝ := bandE (scaledHop c a) μ (a * p)

/-- **The packet's drift velocity in physical units**: `a · v_g`, the group velocity in sites per
unit time times the spacing. -/
noncomputable def scaledV (c μ a p : ℝ) : ℝ := a * groupVel (scaledHop c a) μ (a * p)

/-- **The clock's rate at spacing `a`**, normalised by its rest rate `Δ`, for levels `μ` and
`μ + Δ`. -/
noncomputable def scaledClock (c μ Δ a p : ℝ) : ℝ :=
  levelClockRate μ (μ + Δ) (scaledMom c a p) / Δ

theorem scaledE_eq (c μ a p : ℝ) : scaledE c μ a p = dispE μ (scaledMom c a p) := rfl

theorem two_mul_scaledHop {c a : ℝ} (ha : a ≠ 0) : a * (2 * scaledHop c a) = c := by
  rw [scaledHop]
  field_simp

/-! ### Elementary estimates -/

/-- **`dispE` is `1`-Lipschitz in the momentum term.** -/
theorem abs_dispE_sub_le {μ : ℝ} (hμ : 0 < μ) (s t : ℝ) : |dispE μ s - dispE μ t| ≤ |s - t| := by
  have hs := dispE_pos hμ s
  have ht := dispE_pos hμ t
  have hsum : 0 < dispE μ s + dispE μ t := by linarith
  have heq : dispE μ s - dispE μ t = (s - t) * ((s + t) / (dispE μ s + dispE μ t)) := by
    field_simp
    linear_combination dispE_sq μ s - dispE_sq μ t
  rw [heq, abs_mul]
  have h1 : |(s + t) / (dispE μ s + dispE μ t)| ≤ 1 := by
    rw [abs_div, abs_of_pos hsum, div_le_one hsum]
    linarith [abs_add_le s t, abs_le_dispE μ s, abs_le_dispE μ t]
  calc |s - t| * |(s + t) / (dispE μ s + dispE μ t)| ≤ |s - t| * 1 :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |s - t| := mul_one _

theorem hasDerivAt_dispE {μ : ℝ} (hμ : 0 < μ) (s : ℝ) :
    HasDerivAt (dispE μ) (s / dispE μ s) s := by
  have hin : HasDerivAt (fun s => μ ^ 2 + s ^ 2) (2 * s) s := by
    simpa using ((hasDerivAt_id s).pow 2).const_add (μ ^ 2)
  have h := hin.sqrt (by nlinarith [pow_pos hμ 2, sq_nonneg s])
  unfold dispE
  convert h using 1
  field_simp

/-- The derivative of `s ↦ s/E(s)` is `μ²/E³`. -/
theorem hasDerivAt_div_dispE {μ : ℝ} (hμ : 0 < μ) (s : ℝ) :
    HasDerivAt (fun s => s / dispE μ s) (μ ^ 2 / dispE μ s ^ 3) s := by
  have hE := dispE_pos hμ s
  have h := (hasDerivAt_id s).div (hasDerivAt_dispE hμ s) hE.ne'
  convert h using 1
  · funext x
    rfl
  · have h2 := dispE_sq μ s
    have key : 1 * dispE μ s - id s * (s / dispE μ s) = μ ^ 2 / dispE μ s := by
      rw [eq_div_iff hE.ne', sub_mul, id, mul_assoc s, div_mul_cancel₀ _ hE.ne']
      linear_combination h2
    rw [key]
    ring

/-- **`s ↦ s/E(s)` is `1/μ`-Lipschitz.** -/
theorem abs_div_dispE_sub_le {μ : ℝ} (hμ : 0 < μ) (s t : ℝ) :
    |s / dispE μ s - t / dispE μ t| ≤ |s - t| / μ := by
  have hder : ∀ x, |μ ^ 2 / dispE μ x ^ 3| ≤ 1 / μ := fun x => by
    have hE := dispE_pos hμ x
    have hμE := le_dispE μ x
    rw [abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) hμ]
    nlinarith [pow_le_pow_left₀ hμ.le hμE 3, pow_pos hμ 3]
  have key : ∀ a b : ℝ, a < b → |b / dispE μ b - a / dispE μ a| ≤ |b - a| / μ := by
    intro a b hab
    obtain ⟨x, _, hx⟩ := exists_hasDerivAt_eq_slope (fun s => s / dispE μ s)
      (fun x => μ ^ 2 / dispE μ x ^ 3) hab
      (fun x _ => (hasDerivAt_div_dispE hμ x).continuousAt.continuousWithinAt)
      (fun x _ => hasDerivAt_div_dispE hμ x)
    have hne : b - a ≠ 0 := by linarith
    rw [eq_div_iff hne] at hx
    rw [← hx, abs_mul, mul_comm]
    calc |b - a| * |μ ^ 2 / dispE μ x ^ 3| ≤ |b - a| * (1 / μ) :=
          mul_le_mul_of_nonneg_left (hder x) (abs_nonneg _)
      _ = |b - a| / μ := by ring
  rcases lt_trichotomy s t with h | rfl | h
  · rw [abs_sub_comm, abs_sub_comm s t]
    exact key s t h
  · simp
  · exact key t s h

/-- `|cos x − 1| ≤ x²/2`. -/
theorem abs_cos_sub_one_le (x : ℝ) : |Real.cos x - 1| ≤ x ^ 2 / 2 := by
  rw [abs_sub_comm, abs_of_nonneg (by linarith [Real.cos_le_one x])]
  linarith [Real.one_sub_sq_div_two_le_cos (x := x)]

/-- ★★ **The lattice momentum term converges to `cp`**: `|(c/a) sin(ap) − cp| ≤ c a² |p|³ / 6`. -/
theorem abs_scaledMom_sub_le {c a : ℝ} (hc : 0 ≤ c) (ha : 0 < a) (p : ℝ) :
    |scaledMom c a p - c * p| ≤ c * a ^ 2 * |p| ^ 3 / 6 := by
  have hm : scaledMom c a p - c * p = c / a * (Real.sin (a * p) - a * p) := by
    rw [scaledMom, scaledHop]
    field_simp
  rw [hm, abs_mul, abs_div, abs_of_nonneg hc, abs_of_pos ha, abs_sub_comm]
  have h := Real.abs_sub_sin_le (a * p)
  rw [abs_mul, abs_of_pos ha, mul_pow] at h
  calc c / a * |a * p - Real.sin (a * p)| ≤ c / a * (a ^ 3 * |p| ^ 3 / 6) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = c * a ^ 2 * |p| ^ 3 / 6 := by field_simp

/-! ### The modes -/

/-- ★★★ **The band energy converges to the massive dispersion**, uniformly on `|p| ≤ P`:
`|E_a(p) − √(μ² + c²p²)| ≤ c a² P³ / 6`. -/
theorem abs_scaledE_sub_le {c μ a p P : ℝ} (hc : 0 ≤ c) (hμ : 0 < μ) (ha : 0 < a) (hp : |p| ≤ P) :
    |scaledE c μ a p - dispE μ (c * p)| ≤ c * a ^ 2 * P ^ 3 / 6 := by
  rw [scaledE_eq]
  refine (abs_dispE_sub_le hμ _ _).trans ((abs_scaledMom_sub_le hc ha p).trans ?_)
  have := pow_le_pow_left₀ (abs_nonneg p) hp 3
  have : 0 ≤ c * a ^ 2 := by positivity
  rw [mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (by linarith) this

/-- **The drift velocity in physical units**: `V_a = vRel c μ s · cos(ap)`. -/
theorem scaledV_eq {c μ a : ℝ} (ha : a ≠ 0) (p : ℝ) :
    scaledV c μ a p = vRel c μ (scaledMom c a p) * Real.cos (a * p) := by
  rw [scaledV, groupVel, vRel, vRel, ← scaledMom, ← mul_assoc, ← mul_div_assoc, ← mul_assoc,
    two_mul_scaledHop ha]

/-- ★★★ **The drift velocity converges to the relativistic one**, uniformly on `|p| ≤ P`:
`|V_a(p) − c²p/√(μ² + c²p²)| ≤ a² (cP²/2 + c²P³/(6μ))`. -/
theorem abs_scaledV_sub_le {c μ a p P : ℝ} (hc : 0 < c) (hμ : 0 < μ) (ha : 0 < a) (hp : |p| ≤ P) :
    |scaledV c μ a p - vRel c μ (c * p)| ≤ a ^ 2 * (c * P ^ 2 / 2 + c ^ 2 * P ^ 3 / (6 * μ)) := by
  rw [scaledV_eq ha.ne']
  set s := scaledMom c a p
  have hv := abs_vRel_lt hc hμ s
  have hcos := abs_cos_sub_one_le (a * p)
  have hlip : |vRel c μ s - vRel c μ (c * p)| ≤ c * (|s - c * p| / μ) := by
    have h := abs_div_dispE_sub_le hμ s (c * p)
    rw [vRel, vRel, mul_div_assoc, mul_div_assoc, ← mul_sub, abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left h hc.le
  have hs := abs_scaledMom_sub_le hc.le ha p
  have hP3 := pow_le_pow_left₀ (abs_nonneg p) hp 3
  have hP2 := pow_le_pow_left₀ (abs_nonneg p) hp 2
  have hsplit : vRel c μ s * Real.cos (a * p) - vRel c μ (c * p)
      = vRel c μ s * (Real.cos (a * p) - 1) + (vRel c μ s - vRel c μ (c * p)) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]
  have h1 : |vRel c μ s| * |Real.cos (a * p) - 1| ≤ c * (a ^ 2 * P ^ 2 / 2) := by
    have hap : (a * p) ^ 2 / 2 ≤ a ^ 2 * P ^ 2 / 2 := by
      rw [mul_pow, ← sq_abs p]
      have : 0 ≤ a ^ 2 := by positivity
      nlinarith
    exact mul_le_mul hv.le (hcos.trans hap) (abs_nonneg _) hc.le
  have h2 : c * (|s - c * p| / μ) ≤ c * ((c * a ^ 2 * P ^ 3 / 6) / μ) := by
    refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hμ.le) hc.le
    refine hs.trans ?_
    have : 0 ≤ c * a ^ 2 := by positivity
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (by linarith) this
  have h3 : c * (a ^ 2 * P ^ 2 / 2) + c * ((c * a ^ 2 * P ^ 3 / 6) / μ)
      = a ^ 2 * (c * P ^ 2 / 2 + c ^ 2 * P ^ 3 / (6 * μ)) := by
    field_simp
  linarith

/-! ### The clock -/

/-- The normalised clock rate lies in `[0, 1]`. -/
theorem scaledClock_mem {c μ Δ a p : ℝ} (hμ : 0 < μ) (hΔ : 0 < Δ) :
    0 ≤ scaledClock c μ Δ a p ∧ scaledClock c μ Δ a p ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := clockRate_mem hμ (by linarith : μ ≤ μ + Δ) (scaledMom c a p)
  have hE0 := dispE_pos hμ (scaledMom c a p)
  have hE1 := dispE_pos (by linarith : 0 < μ + Δ) (scaledMom c a p)
  have h1 : (μ + Δ) / dispE (μ + Δ) (scaledMom c a p) ≤ 1 :=
    (div_le_one hE1).2 (le_dispE _ _)
  rw [scaledClock]
  refine ⟨div_nonneg ((mul_nonneg (by linarith) (div_nonneg hμ.le hE0.le)).trans hlo)
    hΔ.le, (div_le_one hΔ).2 ?_⟩
  calc levelClockRate μ (μ + Δ) (scaledMom c a p)
      ≤ (μ + Δ - μ) * ((μ + Δ) / dispE (μ + Δ) (scaledMom c a p)) := hhi
    _ ≤ (μ + Δ - μ) * 1 := mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = Δ := by ring

/-- ★★★ **The scaled clock dilation, with both errors**: the square of the clock's normalised rate
is `1 − (V_a/c)²` — the dilation factor of the packet's **measured** drift velocity — within the
finite-level residue `2Δ/μ` and the lattice defect `a²P²`. -/
theorem scaled_clock_dilation_sq_error_le {c μ Δ a p P : ℝ} (hc : 0 < c) (hμ : 0 < μ) (hΔ : 0 < Δ)
    (ha : 0 < a) (hp : |p| ≤ P) :
    |scaledClock c μ Δ a p ^ 2 - (1 - (scaledV c μ a p / c) ^ 2)| ≤ 2 * Δ / μ + a ^ 2 * P ^ 2 := by
  set s := scaledMom c a p
  set J := scaledHop c a
  have hJ : J ≠ 0 := by
    simp only [J, scaledHop]
    positivity
  have h2J : 2 * J ≠ 0 := mul_ne_zero two_ne_zero hJ
  have hE0 := dispE_pos hμ s
  -- the finite-level error, through `abs_clockRate_div_sub_le`
  have hR := abs_clockRate_div_sub_le (c := 2 * J) h2J hμ (by linarith : μ < μ + Δ) s
  rw [add_sub_cancel_left, ← div_dispE_eq_sqrt h2J hμ s] at hR
  have hD0 : 0 ≤ μ / dispE μ s ∧ μ / dispE μ s ≤ 1 :=
    ⟨by positivity, (div_le_one hE0).2 (le_dispE μ s)⟩
  obtain ⟨hR0, hR1⟩ := scaledClock_mem (c := c) (a := a) (p := p) hμ hΔ
  have hfin : |scaledClock c μ Δ a p ^ 2 - (μ / dispE μ s) ^ 2| ≤ 2 * Δ / μ := by
    have h := hR.trans (div_le_div_of_nonneg_left hΔ.le hμ (le_dispE μ s))
    rw [sq_sub_sq, abs_mul]
    have hsum : |scaledClock c μ Δ a p + μ / dispE μ s| ≤ 2 := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    calc |scaledClock c μ Δ a p + μ / dispE μ s| * |scaledClock c μ Δ a p - μ / dispE μ s|
        ≤ 2 * (Δ / μ) := mul_le_mul hsum h (abs_nonneg _) zero_le_two
      _ = 2 * Δ / μ := by ring
  -- the lattice defect, through `lattice_dilation_defect`
  obtain ⟨hdef, hdefle⟩ := lattice_dilation_defect hJ hμ (a * p)
  have hsdef : 2 * J * Real.sin (a * p) = s := rfl
  rw [hsdef] at hdef hdefle
  have hVc : scaledV c μ a p / c = vRel (2 * J) μ s * Real.cos (a * p) / (2 * J) := by
    have hc' : c = a * (2 * J) := (two_mul_scaledHop ha.ne').symm
    calc scaledV c μ a p / c = a * (vRel (2 * J) μ s * Real.cos (a * p)) / c := rfl
      _ = a * (vRel (2 * J) μ s * Real.cos (a * p)) / (a * (2 * J)) := by rw [hc']
      _ = vRel (2 * J) μ s * Real.cos (a * p) / (2 * J) := mul_div_mul_left _ _ ha.ne'
  have hD0sq : (μ / dispE μ s) ^ 2 = 1 - (vRel (2 * J) μ s / (2 * J)) ^ 2 := by
    rw [div_dispE_eq_sqrt h2J hμ s, Real.sq_sqrt (by linarith [sq_vRel_div_le_one h2J hμ s])]
  have hsin : Real.sin (a * p) ^ 2 ≤ a ^ 2 * P ^ 2 := by
    have h1 := Real.abs_sin_le_abs (x := a * p)
    have h2 : |a * p| ≤ a * P := by rw [abs_mul, abs_of_pos ha]; exact mul_le_mul_of_nonneg_left hp ha.le
    rw [← sq_abs, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) 2
  have hlat : |(μ / dispE μ s) ^ 2 - (1 - (scaledV c μ a p / c) ^ 2)| ≤ a ^ 2 * P ^ 2 := by
    rw [hVc, hD0sq, abs_sub_comm, hdef, abs_of_nonneg (by positivity)]
    exact hdefle.trans hsin
  calc |scaledClock c μ Δ a p ^ 2 - (1 - (scaledV c μ a p / c) ^ 2)|
      ≤ |scaledClock c μ Δ a p ^ 2 - (μ / dispE μ s) ^ 2|
        + |(μ / dispE μ s) ^ 2 - (1 - (scaledV c μ a p / c) ^ 2)| := abs_sub_le _ _ _
    _ ≤ 2 * Δ / μ + a ^ 2 * P ^ 2 := add_le_add hfin hlat

/-! ### The limit -/

/-- ★★★ **Uniform convergence as `a → 0⁺`**: for every `ε > 0` there is `a₀ > 0` such that for all
spacings `0 < a < a₀` and momenta `|p| ≤ P` the band energy and the drift velocity are within `ε` of
the massive relativistic ones, and the clock's squared rate is within `2Δ/μ + ε` of the dilation
factor of the drift velocity, for every level splitting `Δ > 0`. The finite-level residue `2Δ/μ` is
kept. -/
theorem scaled_limit {c μ P ε : ℝ} (hc : 0 < c) (hμ : 0 < μ) (hP : 0 ≤ P) (hε : 0 < ε) :
    ∃ a₀, 0 < a₀ ∧ ∀ a, 0 < a → a < a₀ → ∀ p, |p| ≤ P →
      |scaledE c μ a p - dispE μ (c * p)| ≤ ε
      ∧ |scaledV c μ a p - vRel c μ (c * p)| ≤ ε
      ∧ ∀ Δ, 0 < Δ →
        |scaledClock c μ Δ a p ^ 2 - (1 - (scaledV c μ a p / c) ^ 2)| ≤ 2 * Δ / μ + ε := by
  set K := c * P ^ 3 / 6 + (c * P ^ 2 / 2 + c ^ 2 * P ^ 3 / (6 * μ)) + P ^ 2 + 1
  have hK : 0 < K := by positivity
  refine ⟨Real.sqrt (ε / K), Real.sqrt_pos.2 (by positivity), fun a ha haa p hp => ?_⟩
  have ha2 : a ^ 2 * K < ε := by
    have := (Real.lt_sqrt ha.le).1 haa
    rwa [lt_div_iff₀ hK] at this
  have t1 : 0 ≤ c * P ^ 3 / 6 := by positivity
  have t2 : 0 ≤ c * P ^ 2 / 2 := by positivity
  have t3 : 0 ≤ c ^ 2 * P ^ 3 / (6 * μ) := by positivity
  have t4 : 0 ≤ P ^ 2 := by positivity
  have ha0 : 0 ≤ a ^ 2 := by positivity
  have hA : a ^ 2 * (c * P ^ 3 / 6) ≤ a ^ 2 * K :=
    mul_le_mul_of_nonneg_left (by simp only [K]; linarith) ha0
  have hB : a ^ 2 * (c * P ^ 2 / 2 + c ^ 2 * P ^ 3 / (6 * μ)) ≤ a ^ 2 * K :=
    mul_le_mul_of_nonneg_left (by simp only [K]; linarith) ha0
  have hC : a ^ 2 * P ^ 2 ≤ a ^ 2 * K :=
    mul_le_mul_of_nonneg_left (by simp only [K]; linarith) ha0
  refine ⟨?_, ?_, fun Δ hΔ => ?_⟩
  · have h := abs_scaledE_sub_le hc.le hμ ha hp
    linarith [show c * a ^ 2 * P ^ 3 / 6 = a ^ 2 * (c * P ^ 3 / 6) by ring]
  · linarith [abs_scaledV_sub_le hc hμ ha hp]
  · linarith [scaled_clock_dilation_sq_error_le hc hμ hΔ ha hp]

/-- ★★ **…and to zero when the level splitting also vanishes**: for every `ε > 0` there are
`a₀, Δ₀ > 0` with the clock's squared rate within `ε` of the drift velocity's dilation factor for all
`0 < a < a₀`, `0 < Δ < Δ₀`, `|p| ≤ P`. -/
theorem scaled_clock_limit {c μ P ε : ℝ} (hc : 0 < c) (hμ : 0 < μ) (hP : 0 ≤ P) (hε : 0 < ε) :
    ∃ a₀ Δ₀, 0 < a₀ ∧ 0 < Δ₀ ∧ ∀ a, 0 < a → a < a₀ → ∀ Δ, 0 < Δ → Δ < Δ₀ → ∀ p, |p| ≤ P →
      |scaledClock c μ Δ a p ^ 2 - (1 - (scaledV c μ a p / c) ^ 2)| ≤ ε := by
  obtain ⟨a₀, ha₀, h⟩ := scaled_limit hc hμ hP (half_pos hε)
  refine ⟨a₀, ε * μ / 4, ha₀, by positivity, fun a ha haa Δ hΔ hΔ₀ p hp => ?_⟩
  have h1 := (h a ha haa p hp).2.2 Δ hΔ
  have h2 : 2 * Δ / μ < ε / 2 := by
    rw [div_lt_iff₀ hμ]
    nlinarith
  linarith

end CSD.CV

end
