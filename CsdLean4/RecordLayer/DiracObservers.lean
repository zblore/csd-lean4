/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracDeviceTicks

/-!
# Observers on the Dirac chain: where they are, and what they record of each other

**Category:** 7-SigmaLayer (the record layer). BACKLOG #253 (the machinery; the instance is
`DiracTwin.lean`).

The tools for two of #262's devices on one chain: chords on the unit circle in place of angles, the
device's weight site by site and **where it is** (from each level's translation phase), the
**relational weight** — the joint Born weight of one device at a given offset from the other — and
an arena whose registers integrate any continuous weight along a flow.

## Chords

* `re_star_mul_eq_chord` (`Re(w̄ z) = 1 − |z − w|²/2` on the circle), `norm_star_sub_one`,
  `norm_star_of_norm`, ★ `norm_mul_star_sub_le` and `norm_sub_le_mul_star` (**the chord of a relative
  position, both ways**), `norm_exp_I_mul_ofReal_eq_one`, `norm_exp_sub_exp_le` (a chord is at most its arc),
  ★ `two_sin_le_norm_exp_sub_one` (and at least the chord of its shortest arc); `chordArc`,
  `mem_chordArc`.

## Where a device is

* `devSiteWeight`, `devRegionWeight`, `devSiteWeight_nonneg`, `devRegionWeight_nonneg`,
  `continuous_devSiteWeight`, `siteWeight_smul_sqrt_two`, ★ `devSiteWeight_devicePacket` and
  `devRegionWeight_devicePacket` (**the device's weight is the average of its levels'**),
  `devRegionWeight_univ`;
* `regionWeight_compl_chordArc_le`; ★★ `devRegionWeight_compl_chordArc_le` — **off a chord arc around
  a point near both levels' predictions, the device's weight is bounded by their budgets**.

## What one device records of the other

* ★ `relWeight` — **the relational weight** `Σ_{j,k : |e^{2πi(k−j)/L} − w| ≤ ρ} w_A(j) w_B(k)`;
  `relWeight_nonneg`, `continuous_relWeight`, `continuous_relWeight_comp`, `relWeight_le_mul`;
  ★ `relWeight_swap` — **mutual**: `B` at offset `w` from `A` is `A` at offset `w̄` from `B`;
* ★ `le_relWeight`, ★ `relWeight_le` — **from below when every offset is in the window, from above
  when none is**; `offset_mem_of_near`, `offset_not_mem_of_far`.

## An arena whose registers integrate along a flow

* `regFlow` (a state moved by a flow `Φ`, register `i` integrating `f i` along it), `regFlow_zero`,
  `regFlow_add`, `measurable_regFlow`, `regEvolve`, `regEvolve_self`, `regEvolve_comp`, `regRead`,
  `measurable_regRead`; ★★ `regDetector` — **a register's write as an actual occurrence**, for any
  flow and any nonnegative continuous weight;
* `integral_le_of_le_on`, `integral_le_of_le_on_then_one`, `le_integral_of_ge_on` — integrals over
  phases.

References: `specs/BACKLOG.md` #253, #262, #271, #272, #265, #39; `CV/DiracDevice.lean`
(`devicePacket`, `levelMass`); `RecordLayer/DiracArrival.lean` (`regionWeight_ringPacket_le`,
`re_star_exp_mul_toCircle`, `regionWeight`); `RecordLayer/DiracDetector.lean` (`siteWeight`);
`RecordLayer/DiracDeviceTicks.lean`; `RecordLayer/RecordOccurrence.lean` (`ActualOccurrence`).
-/

@[expose] public section

open MeasureTheory Set CSD.CV Complex
open scoped Matrix

namespace CSD.RecordLayer

open CSD.SigmaLayer

/-! ### Chords on the unit circle -/

/-- On the unit circle, `Re(w̄ z) = 1 − |z − w|²/2`. -/
theorem re_star_mul_eq_chord {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    (star w * z).re = 1 - ‖z - w‖ ^ 2 / 2 := by
  have hz2 : Complex.normSq z = 1 := by rw [← Complex.sq_norm, hz, one_pow]
  have hw2 : Complex.normSq w = 1 := by rw [← Complex.sq_norm, hw, one_pow]
  rw [Complex.sq_norm, Complex.normSq_sub, hz2, hw2, Complex.star_def, mul_comm]
  ring

theorem norm_star_sub_one {b : ℂ} : ‖star b - 1‖ = ‖b - 1‖ := by
  calc ‖star b - 1‖ = ‖(starRingEnd ℂ) (b - 1)‖ := by rw [map_sub, map_one]; rfl
    _ = ‖b - 1‖ := Complex.norm_conj _

theorem norm_star_of_norm {b : ℂ} (hb : ‖b‖ = 1) : ‖star b‖ = 1 := by
  rw [Complex.star_def, Complex.norm_conj, hb]

/-- **The chord of a relative position**: for unit `b, u`, `|a b̄ − w| ≤ |a − u| + |b − 1| + |u − w|`. -/
theorem norm_mul_star_sub_le {a b u w : ℂ} (hb : ‖b‖ = 1) (hu : ‖u‖ = 1) :
    ‖a * star b - w‖ ≤ ‖a - u‖ + ‖b - 1‖ + ‖u - w‖ := by
  have e : a * star b - w = (a - u) * star b + u * (star b - 1) + (u - w) := by ring
  rw [e]
  refine norm_add₃_le.trans ?_
  rw [norm_mul, norm_mul, norm_star_of_norm hb, mul_one, hu, one_mul, norm_star_sub_one]

/-- The reverse: `|u − w| ≤ |a b̄ − w| + |a − u| + |b − 1|`. -/
theorem norm_sub_le_mul_star {a b u w : ℂ} (hb : ‖b‖ = 1) (hu : ‖u‖ = 1) :
    ‖u - w‖ ≤ ‖a * star b - w‖ + ‖a - u‖ + ‖b - 1‖ := by
  have e : u - w = (a * star b - w) - (a - u) * star b - u * (star b - 1) := by ring
  rw [e]
  have h1 := norm_sub_le (a * star b - w - (a - u) * star b) (u * (star b - 1))
  have h2 := norm_sub_le (a * star b - w) ((a - u) * star b)
  have h3 : ‖(a - u) * star b‖ = ‖a - u‖ := by rw [norm_mul, norm_star_of_norm hb, mul_one]
  have h4 : ‖u * (star b - 1)‖ = ‖b - 1‖ := by rw [norm_mul, hu, one_mul, norm_star_sub_one]
  linarith

theorem norm_exp_I_mul_ofReal_eq_one (x : ℝ) : ‖exp (I * (x : ℂ))‖ = 1 := by
  rw [show I * (x : ℂ) = (x : ℂ) * I by ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **A chord is at most its arc**: `|e^{ix} − e^{iy}| ≤ |x − y|`. -/
theorem norm_exp_sub_exp_le (x y : ℝ) : ‖exp (I * (x : ℂ)) - exp (I * (y : ℂ))‖ ≤ |x - y| := by
  have e : exp (I * (x : ℂ)) - exp (I * (y : ℂ))
      = exp (I * (y : ℂ)) * (exp (I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e, norm_mul, norm_exp_I_mul_ofReal_eq_one, one_mul, ← Real.norm_eq_abs]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- **A chord is at least the chord of its shortest arc**: if `y ≤ |z| ≤ 2π − y`, then
`|e^{iz} − 1| ≥ 2 sin(y/2)`. -/
theorem two_sin_le_norm_exp_sub_one {y z : ℝ} (hy : 0 ≤ y) (h1 : y ≤ |z|)
    (h2 : |z| ≤ 2 * Real.pi - y) : 2 * Real.sin (y / 2) ≤ ‖exp (I * (z : ℂ)) - 1‖ := by
  have hπ := Real.pi_pos
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_two]
  have key : ∀ x, y / 2 ≤ x → x ≤ Real.pi - y / 2 → Real.sin (y / 2) ≤ Real.sin x := by
    intro x hx1 hx2
    rcases le_total x (Real.pi / 2) with h | h
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h hx1
    · rw [← Real.sin_pi_sub x]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  refine mul_le_mul_of_nonneg_left ?_ two_pos.le
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz] at h1 h2
    exact (key (z / 2) (by linarith) (by linarith)).trans (le_abs_self _)
  · rw [abs_of_nonpos hz] at h1 h2
    have := key (-z / 2) (by linarith) (by linarith)
    rw [show -z / 2 = -(z / 2) by ring, Real.sin_neg] at this
    exact this.trans (neg_le_abs _)

variable {L : ℕ} [NeZero L]

/-- **The sites within chord `ρ` of the point `z`** of the unit circle. -/
noncomputable def chordArc (z : ℂ) (ρ : ℝ) : Finset (ZMod L) :=
  Finset.univ.filter fun k => ‖(ZMod.toCircle k : ℂ) - z‖ ≤ ρ

theorem mem_chordArc {z : ℂ} {ρ : ℝ} {k : ZMod L} :
    k ∈ chordArc z ρ ↔ ‖(ZMod.toCircle k : ℂ) - z‖ ≤ ρ := by
  simp [chordArc]

/-! ### Where a device is -/

/-- **The device's weight on site `k`**: both levels, both components. -/
noncomputable def devSiteWeight (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) (k : ZMod L) : ℝ :=
  ∑ i : Fin 2, siteWeight (fun q => Ψ (q, i)) k

/-- The device's weight on a region. -/
noncomputable def devRegionWeight (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) (A : Finset (ZMod L)) : ℝ :=
  ∑ k ∈ A, devSiteWeight Ψ k

omit [NeZero L] in
theorem devSiteWeight_nonneg (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) (k : ZMod L) :
    0 ≤ devSiteWeight Ψ k :=
  Finset.sum_nonneg fun _ _ => siteWeight_nonneg _ _

omit [NeZero L] in
theorem devRegionWeight_nonneg (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) (A : Finset (ZMod L)) :
    0 ≤ devRegionWeight Ψ A :=
  Finset.sum_nonneg fun k _ => devSiteWeight_nonneg Ψ k

omit [NeZero L] in
theorem continuous_devSiteWeight (k : ZMod L) :
    Continuous fun Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ => devSiteWeight Ψ k :=
  continuous_finsetSum _ fun i _ =>
    (continuous_siteWeight k).comp
      (continuous_pi fun q => continuous_apply (q, i) :
        Continuous fun Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ => fun q : ZMod L × Fin 2 => Ψ (q, i))

omit [NeZero L] in
theorem siteWeight_smul_sqrt_two (ψ : ZMod L × Fin 2 → ℂ) (k : ZMod L) :
    siteWeight (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • ψ) k = siteWeight ψ k / 2 := by
  simp only [siteWeight, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 two_pos), inv_pow,
    Real.sq_sqrt two_pos.le]
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **The device's weight is the average of its levels'.** -/
theorem devSiteWeight_devicePacket (c μ₀ μ₁ ℓ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (t : ℝ)
    (k : ZMod L) :
    devSiteWeight (devicePacket (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ W β t) k
      = (siteWeight (ringPacket (L := L) c μ₀ ℓ W β t) k
        + siteWeight (ringPacket (L := L) c μ₁ ℓ W β t) k) / 2 := by
  have h : ∀ i : Fin 2,
      (fun q => devicePacket (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ W β t (q, i))
        = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • ringPacket (L := L) c (levelMass μ₀ μ₁ i) ℓ W β t :=
    fun i => by
      funext q
      rfl
  have hm0 : levelMass μ₀ μ₁ 0 = μ₀ := by simp [levelMass]
  have hm1 : levelMass μ₀ μ₁ 1 = μ₁ := by simp [levelMass]
  rw [devSiteWeight, Fin.sum_univ_two, h 0, h 1, hm0, hm1, siteWeight_smul_sqrt_two,
    siteWeight_smul_sqrt_two]
  ring

theorem devRegionWeight_devicePacket (c μ₀ μ₁ ℓ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (t : ℝ)
    (A : Finset (ZMod L)) :
    devRegionWeight (devicePacket (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ W β t) A
      = (regionWeight (ringPacket (L := L) c μ₀ ℓ W β t) A
        + regionWeight (ringPacket (L := L) c μ₁ ℓ W β t) A) / 2 := by
  simp only [devRegionWeight, devSiteWeight_devicePacket, regionWeight]
  rw [← Finset.sum_div, Finset.sum_add_distrib]

section Packet

variable {c μ₀ μ₁ ℓ P D p₀ : ℝ} {W : Finset ℤ} {lo : ℤ}

/-- **A normalised device has total weight `1`.** -/
theorem devRegionWeight_univ (hc : 0 < c) (h0 : 0 < μ₀) (h01 : μ₀ ≤ μ₁) (hℓ : 0 < ℓ)
    (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D) (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L)
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D) (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) (t : ℝ) :
    devRegionWeight (devicePacket (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ W β t) Finset.univ = 1 := by
  have h1 : 0 < μ₁ := h0.trans_le h01
  rw [devRegionWeight_devicePacket, regionWeight, regionWeight, sum_siteWeight, sum_siteWeight,
    (dirac_packet_limit hc h0 hℓ hp₀ hD0 hWin hWD β hβ).1 t,
    (dirac_packet_limit hc h1 hℓ hp₀ hD0 hWin hWD β hβ).1 t, Complex.one_re]
  norm_num

/-- **One level's tail away from a point near its prediction**: if the level's predicted point
`e^{iΩt}` is within `η ≤ ρ` of `z`, its weight off the chord-`ρ` arc around `z`, times
`(ρ − η)²/2`, is at most its budget. -/
theorem regionWeight_compl_chordArc_le (hc : 0 < c) {μ : ℝ} (hμ : 0 < μ) (hℓ : 0 < ℓ)
    (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D) (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L)
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D) (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) {z : ℂ} {ρ η : ℝ} (hηρ : η ≤ ρ) (t : ℝ)
    (hz : ‖exp (I * ((2 * Real.pi / ℓ * vRel c μ (c * p₀) * t : ℝ) : ℂ)) - z‖ ≤ η) :
    regionWeight (ringPacket (L := L) c μ ℓ W β t) (chordArc z ρ)ᶜ * ((ρ - η) ^ 2 / 2)
      ≤ 1 - (transPhase (ringPacket (L := L) c μ ℓ W β 0)).re
        + |t| * limitErr c μ ℓ D P (ℓ / L) := by
  have h := regionWeight_ringPacket_le hc hμ hℓ hp₀ hD0 hWin hWD β hβ
    (B := (chordArc z ρ)ᶜ) (γ := 1 - (ρ - η) ^ 2 / 2) t fun k hk => by
      rw [Finset.mem_compl, mem_chordArc, not_le] at hk
      rw [← re_star_exp_mul_toCircle, re_star_mul_eq_chord (Circle.norm_coe _)
        (norm_exp_I_mul_ofReal_eq_one _)]
      have hd : ρ - η ≤ ‖(ZMod.toCircle k : ℂ)
          - exp (I * ((2 * Real.pi / ℓ * vRel c μ (c * p₀) * t : ℝ) : ℂ))‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub (ZMod.toCircle k : ℂ)
          (exp (I * ((2 * Real.pi / ℓ * vRel c μ (c * p₀) * t : ℝ) : ℂ))) z
        linarith
      have hsq := pow_le_pow_left₀ (by linarith) hd 2
      linarith
  rwa [show 1 - (1 - (ρ - η) ^ 2 / 2) = (ρ - η) ^ 2 / 2 by ring] at h

/-- ★★ **Where the device is**: if both levels' predicted points are within `η ≤ ρ` of `z`, the
device's weight off the chord-`ρ` arc around `z`, times `(ρ − η)²/2`, is at most the average of
the levels' budgets. -/
theorem devRegionWeight_compl_chordArc_le (hc : 0 < c) (h0 : 0 < μ₀) (h01 : μ₀ ≤ μ₁)
    (hℓ : 0 < ℓ) (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D) (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L)
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D) (β : ℤ → ℂ)
    (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) {z : ℂ} {ρ η : ℝ} (hηρ : η ≤ ρ) (t : ℝ)
    (hz₀ : ‖exp (I * ((2 * Real.pi / ℓ * vRel c μ₀ (c * p₀) * t : ℝ) : ℂ)) - z‖ ≤ η)
    (hz₁ : ‖exp (I * ((2 * Real.pi / ℓ * vRel c μ₁ (c * p₀) * t : ℝ) : ℂ)) - z‖ ≤ η) :
    devRegionWeight (devicePacket (L := L) (scaledHop c (ℓ / L)) μ₀ μ₁ W β t) (chordArc z ρ)ᶜ
        * ((ρ - η) ^ 2 / 2)
      ≤ ((1 - (transPhase (ringPacket (L := L) c μ₀ ℓ W β 0)).re
          + |t| * limitErr c μ₀ ℓ D P (ℓ / L))
        + (1 - (transPhase (ringPacket (L := L) c μ₁ ℓ W β 0)).re
          + |t| * limitErr c μ₁ ℓ D P (ℓ / L))) / 2 := by
  have h1 : 0 < μ₁ := h0.trans_le h01
  have e0 := regionWeight_compl_chordArc_le (L := L) hc h0 hℓ hp₀ hD0 hWin hWD β hβ hηρ t hz₀
  have e1 := regionWeight_compl_chordArc_le (L := L) hc h1 hℓ hp₀ hD0 hWin hWD β hβ hηρ t hz₁
  rw [devRegionWeight_devicePacket]
  linarith

end Packet

/-! ### The relational weight -/

/-- ★ **The relational weight**: the joint Born weight that device `B` sits at offset within chord
`ρ` of `w` from device `A` — `Σ_{j,k : |e^{2πi(k−j)/L} − w| ≤ ρ} w_A(j) w_B(k)`. It is the weight
**of `B` seen from `A`** and, by the same token, **of `A` seen from `B`** at offset `w̄`. -/
noncomputable def relWeight (w : ℂ) (ρ : ℝ) (ΨA ΨB : (ZMod L × Fin 2) × Fin 2 → ℂ) : ℝ :=
  ∑ j, ∑ k, if ‖(ZMod.toCircle k : ℂ) * star (ZMod.toCircle j : ℂ) - w‖ ≤ ρ
    then devSiteWeight ΨA j * devSiteWeight ΨB k else 0

theorem relWeight_nonneg (w : ℂ) (ρ : ℝ) (ΨA ΨB : (ZMod L × Fin 2) × Fin 2 → ℂ) :
    0 ≤ relWeight w ρ ΨA ΨB :=
  Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by
    split_ifs
    · exact mul_nonneg (devSiteWeight_nonneg _ _) (devSiteWeight_nonneg _ _)
    · exact le_rfl

theorem continuous_relWeight (w : ℂ) (ρ : ℝ) :
    Continuous fun p : ((ZMod L × Fin 2) × Fin 2 → ℂ) × ((ZMod L × Fin 2) × Fin 2 → ℂ) =>
      relWeight w ρ p.1 p.2 :=
  continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
    continuous_if_const _
      (fun _ => ((continuous_devSiteWeight j).comp continuous_fst).mul
        ((continuous_devSiteWeight k).comp continuous_snd))
      fun _ => continuous_const

/-- ★ **Mutual**: the weight of `B` at offset `w` seen from `A` is the weight of `A` at offset `w̄`
seen from `B`. -/
theorem relWeight_swap (w : ℂ) (ρ : ℝ) (ΨA ΨB : (ZMod L × Fin 2) × Fin 2 → ℂ) :
    relWeight w ρ ΨA ΨB = relWeight (star w) ρ ΨB ΨA := by
  rw [relWeight, relWeight, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  have e : (ZMod.toCircle j : ℂ) * star (ZMod.toCircle k : ℂ) - star w
      = star ((ZMod.toCircle k : ℂ) * star (ZMod.toCircle j : ℂ) - w) := by
    rw [star_sub, star_mul', star_star, mul_comm]
  rw [e, Complex.star_def, Complex.norm_conj]
  split_ifs <;> ring

theorem continuous_relWeight_comp {α : Type*} [TopologicalSpace α]
    {f g : α → (ZMod L × Fin 2) × Fin 2 → ℂ} (hf : Continuous f) (hg : Continuous g) (w : ℂ)
    (ρ : ℝ) : Continuous fun x => relWeight w ρ (f x) (g x) := by
  have h := (continuous_relWeight (L := L) w ρ).comp (hf.prodMk hg)
  exact h

theorem relWeight_le_mul (w : ℂ) (ρ : ℝ) (ΨA ΨB : (ZMod L × Fin 2) × Fin 2 → ℂ) :
    relWeight w ρ ΨA ΨB ≤ devRegionWeight ΨA Finset.univ * devRegionWeight ΨB Finset.univ := by
  rw [devRegionWeight, devRegionWeight, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (devSiteWeight_nonneg _ _) (devSiteWeight_nonneg _ _)

/-- ★ **The relational weight from below**: if every offset from a site of `X` to a site of `Y` is
in the window, the relational weight is at least `w_A(X) w_B(Y)`. -/
theorem le_relWeight {w : ℂ} {ρ : ℝ} {ΨA ΨB : (ZMod L × Fin 2) × Fin 2 → ℂ}
    {X Y : Finset (ZMod L)}
    (h : ∀ j ∈ X, ∀ k ∈ Y, ‖(ZMod.toCircle k : ℂ) * star (ZMod.toCircle j : ℂ) - w‖ ≤ ρ) :
    devRegionWeight ΨA X * devRegionWeight ΨB Y ≤ relWeight w ρ ΨA ΨB := by
  have hnn : ∀ j k, 0 ≤ (if ‖(ZMod.toCircle k : ℂ) * star (ZMod.toCircle j : ℂ) - w‖ ≤ ρ
      then devSiteWeight ΨA j * devSiteWeight ΨB k else 0) := fun j k => by
    split_ifs
    · exact mul_nonneg (devSiteWeight_nonneg _ _) (devSiteWeight_nonneg _ _)
    · exact le_rfl
  rw [devRegionWeight, devRegionWeight, Finset.sum_mul_sum]
  calc ∑ j ∈ X, ∑ k ∈ Y, devSiteWeight ΨA j * devSiteWeight ΨB k
      = ∑ j ∈ X, ∑ k ∈ Y, (if ‖(ZMod.toCircle k : ℂ) * star (ZMod.toCircle j : ℂ) - w‖ ≤ ρ
          then devSiteWeight ΨA j * devSiteWeight ΨB k else 0) :=
        Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => by
          simp only [h j hj k hk, ↓reduceIte]
    _ ≤ ∑ j ∈ X, ∑ k, (if ‖(ZMod.toCircle k : ℂ) * star (ZMod.toCircle j : ℂ) - w‖ ≤ ρ
          then devSiteWeight ΨA j * devSiteWeight ΨB k else 0) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _) fun k _ _ => hnn j k
    _ ≤ relWeight w ρ ΨA ΨB :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ =>
          Finset.sum_nonneg fun k _ => hnn j k

/-- ★ **The relational weight from above**: if no offset from a site of `X` to a site of `Y` is in
the window, the relational weight is at most `w_A(Xᶜ) N_B + N_A w_B(Yᶜ)`. -/
theorem relWeight_le {w : ℂ} {ρ : ℝ} {ΨA ΨB : (ZMod L × Fin 2) × Fin 2 → ℂ}
    {X Y : Finset (ZMod L)}
    (h : ∀ j ∈ X, ∀ k ∈ Y, ρ < ‖(ZMod.toCircle k : ℂ) * star (ZMod.toCircle j : ℂ) - w‖) :
    relWeight w ρ ΨA ΨB
      ≤ devRegionWeight ΨA Xᶜ * devRegionWeight ΨB Finset.univ
        + devRegionWeight ΨA Finset.univ * devRegionWeight ΨB Yᶜ := by
  set a := devSiteWeight ΨA
  set b := devSiteWeight ΨB
  have hterm : ∀ j k, (if ‖(ZMod.toCircle k : ℂ) * star (ZMod.toCircle j : ℂ) - w‖ ≤ ρ
      then a j * b k else 0)
      ≤ (if j ∈ Xᶜ then a j else 0) * b k + a j * (if k ∈ Yᶜ then b k else 0) := fun j k => by
    have ha := devSiteWeight_nonneg ΨA j
    have hb := devSiteWeight_nonneg ΨB k
    by_cases hj : j ∈ X
    · by_cases hk : k ∈ Y
      · have hn := not_le.2 (h j hj k hk)
        simp only [hn, ↓reduceIte, Finset.mem_compl, hj, hk, not_true_eq_false, zero_mul,
          mul_zero, add_zero, le_refl]
      · simp only [Finset.mem_compl, hj, hk, not_true_eq_false, not_false_eq_true, ↓reduceIte,
          zero_mul, zero_add]
        split_ifs <;> nlinarith
    · simp only [Finset.mem_compl, hj, not_false_eq_true, ↓reduceIte]
      split_ifs <;> nlinarith
  calc relWeight w ρ ΨA ΨB
      ≤ ∑ j, ∑ k, ((if j ∈ Xᶜ then a j else 0) * b k + a j * (if k ∈ Yᶜ then b k else 0)) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hterm j k
    _ = (∑ j, if j ∈ Xᶜ then a j else 0) * ∑ k, b k
        + (∑ j, a j) * ∑ k, if k ∈ Yᶜ then b k else 0 := by
        rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by rw [← Finset.sum_add_distrib]
    _ = _ := by
        rw [Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.univ_inter, Finset.univ_inter]
        rfl

/-- **Offsets near the window**: if `A`'s site is within `ρA` of `1`, `B`'s within `ρB` of `u`, and
`|u − w| + ρA + ρB ≤ ρ`, the offset is in the window. -/
theorem offset_mem_of_near {j k : ZMod L} {u w : ℂ} {ρA ρB ρ : ℝ} (hu : ‖u‖ = 1)
    (hj : ‖(ZMod.toCircle j : ℂ) - 1‖ ≤ ρA) (hk : ‖(ZMod.toCircle k : ℂ) - u‖ ≤ ρB)
    (h : ‖u - w‖ + ρA + ρB ≤ ρ) :
    ‖(ZMod.toCircle k : ℂ) * star (ZMod.toCircle j : ℂ) - w‖ ≤ ρ := by
  have := norm_mul_star_sub_le (a := (ZMod.toCircle k : ℂ)) (w := w) (Circle.norm_coe _) hu
    (b := (ZMod.toCircle j : ℂ))
  linarith

/-- **Offsets far from the window**: if `ρ + ρA + ρB < |u − w|`, the offset is out of it. -/
theorem offset_not_mem_of_far {j k : ZMod L} {u w : ℂ} {ρA ρB ρ : ℝ} (hu : ‖u‖ = 1)
    (hj : ‖(ZMod.toCircle j : ℂ) - 1‖ ≤ ρA) (hk : ‖(ZMod.toCircle k : ℂ) - u‖ ≤ ρB)
    (h : ρ + ρA + ρB < ‖u - w‖) :
    ρ < ‖(ZMod.toCircle k : ℂ) * star (ZMod.toCircle j : ℂ) - w‖ := by
  have := norm_sub_le_mul_star (a := (ZMod.toCircle k : ℂ)) (w := w) (Circle.norm_coe _) hu
    (b := (ZMod.toCircle j : ℂ))
  linarith

/-! ### An arena whose registers integrate along a flow -/

section Registers

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {ι : Type*} (Φ : ℝ → X → X) (f : ι → X → ℝ)

/-- **A state with registers**: the state moves by the flow `Φ`, and register `i` integrates
`f i` along it. -/
noncomputable def regFlow (t : ℝ) (y : X × (ι → ℝ)) : X × (ι → ℝ) :=
  (Φ t y.1, fun i => y.2 i + ∫ s in (0 : ℝ)..t, f i (Φ s y.1))

omit [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem regFlow_zero (hΦ0 : ∀ x, Φ 0 x = x) (y : X × (ι → ℝ)) : regFlow Φ f 0 y = y := by
  ext
  · simp [regFlow, hΦ0]
  · simp [regFlow]

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem regFlow_add (hΦadd : ∀ s t x, Φ (s + t) x = Φ t (Φ s x))
    (hcont : ∀ i, Continuous fun p : X × ℝ => f i (Φ p.2 p.1)) (s t : ℝ) (y : X × (ι → ℝ)) :
    regFlow Φ f (s + t) y = regFlow Φ f t (regFlow Φ f s y) := by
  ext i
  · simp only [regFlow, hΦadd]
  · simp only [regFlow]
    have hi : ∀ a b : ℝ, IntervalIntegrable (fun u => f i (Φ u y.1)) volume a b := fun a b =>
      ((hcont i).comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
    have hs : (∫ v in (0 : ℝ)..t, f i (Φ v (Φ s y.1)))
        = ∫ v in s..s + t, f i (Φ v y.1) := by
      calc (∫ v in (0 : ℝ)..t, f i (Φ v (Φ s y.1)))
          = ∫ v in (0 : ℝ)..t, f i (Φ (s + v) y.1) := by simp only [hΦadd]
        _ = ∫ v in s + 0..s + t, f i (Φ v y.1) :=
            intervalIntegral.integral_comp_add_left (fun v => f i (Φ v y.1)) s
        _ = _ := by rw [add_zero]
    rw [hs, ← intervalIntegral.integral_add_adjacent_intervals (hi 0 s) (hi s (s + t))]
    ring

theorem measurable_regFlow (hΦm : ∀ t, Measurable (Φ t))
    (hcont : ∀ i, Continuous fun p : X × ℝ => f i (Φ p.2 p.1)) (t : ℝ) :
    Measurable (regFlow Φ f t) := by
  refine ((hΦm t).comp measurable_fst).prodMk (measurable_pi_iff.2 fun i => ?_)
  refine ((measurable_pi_apply i).comp measurable_snd).add ?_
  have hc : Continuous fun x : X => ∫ s in (0 : ℝ)..t, f i (Φ s x) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x s => f i (Φ s x)) ((hcont i).comp (continuous_fst.prodMk continuous_snd)) 0 t
  exact hc.measurable.comp measurable_fst

/-- The two-time evolution of the arena with registers. -/
noncomputable def regEvolve (s t : OnticTime) : X × (ι → ℝ) → X × (ι → ℝ) :=
  regFlow Φ f (t - s)

omit [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem regEvolve_self (hΦ0 : ∀ x, Φ 0 x = x) (t : OnticTime) :
    regEvolve Φ f t t = (id : X × (ι → ℝ) → X × (ι → ℝ)) := by
  funext y
  simp only [regEvolve, sub_self, regFlow_zero Φ f hΦ0, id]

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem regEvolve_comp (hΦadd : ∀ s t x, Φ (s + t) x = Φ t (Φ s x))
    (hcont : ∀ i, Continuous fun p : X × ℝ => f i (Φ p.2 p.1)) (s t u : OnticTime) :
    regEvolve Φ f t u ∘ regEvolve Φ f s t = (regEvolve Φ f s u : X × (ι → ℝ) → X × (ι → ℝ)) := by
  funext y
  simp only [regEvolve, Function.comp]
  rw [show u - s = (t - s) + (u - t) by ring, regFlow_add Φ f hΦadd hcont]

/-- **Register `i`'s readout**: `1` once it has reached `θ`. -/
noncomputable def regRead (i : ι) (θ : ℝ) (y : X × (ι → ℝ)) : ℕ := if θ ≤ y.2 i then 1 else 0

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
theorem measurable_regRead (i : ι) (θ : ℝ) : Measurable (regRead (X := X) i θ) :=
  Measurable.ite (measurableSet_le measurable_const ((measurable_pi_apply i).comp measurable_snd))
    measurable_const measurable_const

/-- ★★ **A register's write as an actual occurrence**: prepared at `(x₀, 0)`, register `i` below
`θ` before `τ₀`, at `θ` by `τ₁`, and held (its integrand is nonnegative). -/
noncomputable def regDetector {K : ℕ} (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦadd : ∀ s t x, Φ (s + t) x = Φ t (Φ s x))
    (hcont : ∀ i, Continuous fun p : X × ℝ => f i (Φ p.2 p.1)) (hΦm : ∀ t, Measurable (Φ t))
    (i : ι) (θ : ℝ) (x₀ : X) (site : Finset (Fin K)) {τ₀ τ₁ w : ℝ} (hτ₀ : 0 ≤ τ₀)
    (hτ : τ₀ ≤ τ₁) (hw : 0 ≤ w) (hpos : ∀ s, 0 ≤ s → 0 ≤ f i (Φ s x₀))
    (hbefore : ∀ t, 0 ≤ t → t < τ₀ → ∫ s in (0 : ℝ)..t, f i (Φ s x₀) < θ)
    (hafter : θ ≤ ∫ s in (0 : ℝ)..τ₁, f i (Φ s x₀)) :
    ActualOccurrence (X × (ι → ℝ)) ℕ K where
  evolve := regEvolve Φ f
  evolve_self := regEvolve_self Φ f hΦ0
  evolve_comp := regEvolve_comp Φ f hΦadd hcont
  measurable_evolve := fun s t => measurable_regFlow Φ f hΦm hcont (t - s)
  readout := regRead i θ
  measurable_readout := measurable_regRead i θ
  ready := {y | y.2 i = 0}
  measurableSet_ready :=
    measurableSet_eq_fun ((measurable_pi_apply i).comp measurable_snd) measurable_const
  prep := (x₀, 0)
  prep_mem := rfl
  site := site
  start := 0
  value := 1
  writeStart := τ₀
  writeEnd := τ₁
  window := w
  isWrite :=
    { start_le := hτ₀
      interval := hτ
      window_nonneg := hw
      before := fun t ht0 ht => by
        show regRead i θ (regFlow Φ f (t - 0) (x₀, 0)) ≠ 1
        simp only [regRead, regFlow, sub_zero, Pi.zero_apply, zero_add]
        split_ifs with h
        · exact absurd h (not_le.2 (hbefore t ht0 ht))
        · decide
      holds := fun t ht₁ _ => by
        show regRead i θ (regFlow Φ f (t - 0) (x₀, 0)) = 1
        simp only [regRead, regFlow, sub_zero, Pi.zero_apply, zero_add]
        have hi : ∀ a b : ℝ, IntervalIntegrable (fun u => f i (Φ u x₀)) volume a b := fun a b =>
          ((hcont i).comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
        have hmono : (∫ s in (0 : ℝ)..τ₁, f i (Φ s x₀)) ≤ ∫ s in (0 : ℝ)..t, f i (Φ s x₀) := by
          rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 τ₁) (hi τ₁ t)]
          have := intervalIntegral.integral_nonneg (μ := volume) ht₁ fun s hs =>
            hpos s (by linarith [hs.1])
          linarith
        split_ifs with h
        · rfl
        · exact absurd (hafter.trans hmono) h }

end Registers

/-! ### Integrals over phases -/

/-- An integrand at most `ε` up to `t_f` integrates to at most `ε t` there. -/
theorem integral_le_of_le_on {F : ℝ → ℝ} (hF : Continuous F) {ε tf t : ℝ} (ht0 : 0 ≤ t)
    (htf : t ≤ tf) (hε : ∀ s, 0 ≤ s → s ≤ tf → F s ≤ ε) :
    ∫ s in (0 : ℝ)..t, F s ≤ ε * t := by
  have h := intervalIntegral.integral_mono_on ht0 (hF.intervalIntegrable 0 t)
    (intervalIntegrable_const (μ := volume) (c := ε)) fun s hs => hε s hs.1 (hs.2.trans htf)
  rwa [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm] at h

/-- An integrand at most `ε` up to `t_f` and at most `1` after integrates to at most
`ε t_f + (t − t_f)`. -/
theorem integral_le_of_le_on_then_one {F : ℝ → ℝ} (hF : Continuous F) {ε tf t : ℝ}
    (htf0 : 0 ≤ tf) (htf : tf ≤ t) (hε : ∀ s, 0 ≤ s → s ≤ tf → F s ≤ ε) (h1 : ∀ s, F s ≤ 1) :
    ∫ s in (0 : ℝ)..t, F s ≤ ε * tf + (t - tf) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable 0 tf)
    (hF.intervalIntegrable tf t)]
  have h1' := intervalIntegral.integral_mono_on htf (hF.intervalIntegrable tf t)
    (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))) fun s _ => h1 s
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h1'
  have h0 := integral_le_of_le_on hF htf0 le_rfl hε
  linarith

/-- A nonnegative integrand at least `κ` on `[t_n, t_e]` integrates to at least `κ(t − t_n)` by
`t ∈ [t_n, t_e]`. -/
theorem le_integral_of_ge_on {F : ℝ → ℝ} (hF : Continuous F) {κ tn te t : ℝ} (htn0 : 0 ≤ tn)
    (htn : tn ≤ t) (hte : t ≤ te) (hpos : ∀ s, 0 ≤ s → 0 ≤ F s)
    (hκ : ∀ s, tn ≤ s → s ≤ te → κ ≤ F s) :
    κ * (t - tn) ≤ ∫ s in (0 : ℝ)..t, F s := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable 0 tn)
    (hF.intervalIntegrable tn t)]
  have h0 := intervalIntegral.integral_nonneg (μ := volume) htn0 fun s hs => hpos s hs.1
  have h1 := intervalIntegral.integral_mono_on htn
    (intervalIntegrable_const (μ := volume) (c := κ)) (hF.intervalIntegrable tn t)
    fun s hs => hκ s hs.1 (hs.2.trans hte)
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at h1
  linarith

end CSD.RecordLayer

end
