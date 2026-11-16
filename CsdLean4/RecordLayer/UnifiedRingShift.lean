/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedWallValues

/-!
# Translating a carrier round the ring: the observer at the far wall

**Category:** 7-SigmaLayer (the record layer). BACKLOG #417 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Task 5 of the research delivery
plan of 2026-11-16, first part. No new assumption beyond UA-18 (b).

The feasibility note (`specs/unified-m6-feasibility.md`, §1) found that the theorems force
the layout: the moving observer and the messenger start beside one wall, so the observer at
rest must sit at the other, half the ring away. Every packet built so far sits at the angle
`0` at packet time `0`. This module translates carriers round the ring. The lattice Dirac
energy does not depend on the site, so translation commutes with the evolution; the clock's
reading does not change, and its place moves with it.

* ★ `exp_smul_mulVec_intertwine` — a linear map that intertwines two matrices intertwines
  their exponentials;
* `chainShift`, `chainShiftₗ`, ★ `diracHam_mulVec_chainShift`, `chainProp_mulVec_chainShift`,
  `chainInner_chainShift`, `regionWeight_chainShift`, `chainParity_chainShift` — one Dirac
  carrier; the translation by a half turn commutes with the mirror;
* `deviceShift`, `deviceShiftₗ`, `deviceShift_ne_zero`, ★ `deviceHam_mulVec_deviceShift`,
  `deviceProp_mulVec_deviceShift`, `deviceCoherence_deviceShift`, `deviceNorm_deviceShift`,
  `deviceRegionWeight_deviceShift` — the two-level clock;
* ★★ `clockFreeRead_deviceShift`, ★★ `clockPointerShift_deviceShift` — **a translated clock
  reads the same**: its uncoupled reading, and its pointer's displacement on a fibre where
  the profile vanishes, are those of the clock it was translated from;
* ★★ `sum_arenaObs_siteSel_deviceShift` — its occupancy of a region along the orbit is the
  original's occupancy of the region translated back;
* `cos_site_sub`, `mem_ringArc_sub`, `image_sub_ringArc` — arcs under translation;
* ★★★ `far_wall_clock_swing_fine` — **the clock at rest, translated by any `h`, swings with
  the margin of #411**;
* ★★★ `far_wall_clock_outside_le` — **and stays in the arc about the angle `2π h/L`**: the
  occupancy outside it, times `1 − cos δ`, is at most `4 · lightBudget n N 1 (t₁ + s)`.

## Exact scope

* **Any translation `h`.** The observer of UA-18 (b) at the far wall is `h` with `h = −h`
  and `h ≠ 0`, the half turn, on a ring with an even number of sites; then the translated
  state is still mirror-odd (`chainParity_chainShift`, stated for one Dirac carrier). That
  the translated *clock* is mirror-odd is the same statement level by level and is not
  restated for the device.
* **Uncoupled orbits and the fibre where the profile vanishes.** The pointer's displacement
  is the one of #357 on that fibre; nothing is said off it (R7).
* **One clock and its own pointer.** No gate with the messenger or the other clock: the
  occupancy bound is what #410's gate lemmas take, and they are not applied here.
* **The ticks are not restated.** `wall_clock_ticks` is about the count of the untranslated
  clock; the count is a function of the pointer's history, which
  `clockPointerShift_deviceShift` identifies on the zero fibre, but the count theorem for
  the translated clock is not written out.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-12, UA-18, UO-16, UD-175, UD-180, UD-184, UD-187); `specs/unified-m6-feasibility.md`
(§1, §6 item 2); `RecordLayer/UnifiedWallValues.lean` (#415:
`one_sub_sum_arenaObs_wallArcs_icoDevice_time_le`, `lightBudget`);
`RecordLayer/UnifiedWallOrbits.lean` (#411: `wall_clock_swing_fine`);
`RecordLayer/UnifiedGateRegions.lean` (#395: `ringArc`, `mem_ringArc`,
`sum_arenaObs_siteSel_free_deviceRay`); `RecordLayer/UnifiedDiracClock.lean` (#357:
`clockFreeRead`, `clockFreeRead_deviceRay`, `clockPointerShift`,
`clockRead_of_lift_eq_zero`, `deviceRay`); `RecordLayer/DiracTiming.lean`
(`diracHam_mulVec_apply`); `CV/DiracDevice.lean` (`deviceHam_mulVec_apply`,
`deviceCoherence`, `deviceNorm`); `RecordLayer/DiracSegment.lean` (#275: the series argument
of `segOf_chainProp_mulVec`, made generic here).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### Intertwining exponentials -/

/-- ★ **A linear map that intertwines two matrices intertwines their exponentials.** -/
theorem exp_smul_mulVec_intertwine {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] {A : Matrix n n ℂ} {B : Matrix m m ℂ} (S : (n → ℂ) →ₗ[ℂ] (m → ℂ))
    (h : ∀ v, S (A *ᵥ v) = B *ᵥ S v) (c : ℂ) (v : n → ℂ) :
    S (NormedSpace.exp (c • A) *ᵥ v) = NormedSpace.exp (c • B) *ᵥ S v := by
  have hpow : ∀ k : ℕ, S (A ^ k *ᵥ v) = B ^ k *ᵥ S v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, h, ih, pow_succ', Matrix.mulVec_mulVec]
  have hA := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c • A)
  have hB := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c • B)
  let LA : Matrix n n ℂ →ₗ[ℂ] (m → ℂ) :=
    { toFun := fun A' => S (A' *ᵥ v)
      map_add' := fun A' B' => by rw [Matrix.add_mulVec, map_add]
      map_smul' := fun a A' => by rw [Matrix.smul_mulVec, map_smul]; rfl }
  let LB : Matrix m m ℂ →ₗ[ℂ] (m → ℂ) :=
    { toFun := fun B' => B' *ᵥ S v
      map_add' := fun A' B' => Matrix.add_mulVec A' B' _
      map_smul' := fun a A' => Matrix.smul_mulVec a A' _ }
  have h1 := hA.mapL (LinearMap.toContinuousLinearMap LA)
  have h2 := hB.mapL (LinearMap.toContinuousLinearMap LB)
  have heq : (fun k => LinearMap.toContinuousLinearMap LA
        (((k.factorial : ℂ)⁻¹) • (c • A) ^ k))
      = fun k => LinearMap.toContinuousLinearMap LB
        (((k.factorial : ℂ)⁻¹) • (c • B) ^ k) := by
    funext k
    simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk, LA, LB,
      smul_pow, Matrix.smul_mulVec]
    rw [map_smul, map_smul, hpow]
  rw [heq] at h1
  exact h1.unique h2

/-! ### One Dirac carrier -/

section Chain

variable {L : ℕ}

/-- **The translation of a chain state by `h` sites.** -/
def chainShift (h : ZMod L) (φ : ZMod L × Fin 2 → ℂ) : ZMod L × Fin 2 → ℂ :=
  fun p => φ (p.1 - h, p.2)

/-- The translation, as a linear map. -/
def chainShiftₗ (h : ZMod L) : (ZMod L × Fin 2 → ℂ) →ₗ[ℂ] (ZMod L × Fin 2 → ℂ) where
  toFun := chainShift h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem chainShiftₗ_apply (h : ZMod L) (φ : ZMod L × Fin 2 → ℂ) :
    chainShiftₗ h φ = chainShift h φ := rfl

theorem regionWeight_chainShift (h : ZMod L) (φ : ZMod L × Fin 2 → ℂ) (A : Finset (ZMod L)) :
    regionWeight (chainShift h φ) A = regionWeight φ (A.image fun k => k - h) := by
  rw [regionWeight, regionWeight, Finset.sum_image (fun x _ y _ hxy => sub_left_injective hxy)]
  rfl

variable [NeZero L]

/-- ★ **Translation commutes with the lattice Dirac energy.** -/
theorem diracHam_mulVec_chainShift (J μ : ℝ) (h : ZMod L) (φ : ZMod L × Fin 2 → ℂ) :
    diracHam J μ *ᵥ chainShift h φ = chainShift h (diracHam J μ *ᵥ φ) := by
  funext ⟨j, a⟩
  rw [diracHam_mulVec_apply]
  simp only [chainShift]
  rw [diracHam_mulVec_apply, add_sub_right_comm, sub_right_comm]

/-- Translation commutes with the evolution. -/
theorem chainProp_mulVec_chainShift (J μ t : ℝ) (h : ZMod L) (φ : ZMod L × Fin 2 → ℂ) :
    chainProp (L := L) J μ t *ᵥ chainShift h φ = chainShift h (chainProp J μ t *ᵥ φ) := by
  rw [chainProp]
  exact (exp_smul_mulVec_intertwine (chainShiftₗ h)
    (fun v => (diracHam_mulVec_chainShift J μ h v).symm) _ φ).symm

theorem chainInner_chainShift (h : ZMod L) (φ ψ : ZMod L × Fin 2 → ℂ) :
    chainInner (chainShift h φ) (chainShift h ψ) = chainInner φ ψ := by
  rw [chainInner, chainInner]
  exact Fintype.sum_equiv ((Equiv.subRight h).prodCongr (Equiv.refl (Fin 2))) _ _ fun _ => rfl

omit [NeZero L] in
/-- The translation by a half turn commutes with the mirror. -/
theorem chainParity_chainShift {h : ZMod L} (hh : -h = h) (φ : ZMod L × Fin 2 → ℂ) :
    chainParity (chainShift h φ) = chainShift h (chainParity φ) := by
  funext ⟨j, a⟩
  simp only [chainParity, chainShift]
  rw [show -j - h = -(j - h) by linear_combination hh]

end Chain

/-! ### The two-level clock -/

section Device

variable {L : ℕ}

/-- **The translation of a clock state by `h` sites.** -/
def deviceShift (h : ZMod L) (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) :
    (ZMod L × Fin 2) × Fin 2 → ℂ := fun x => Ψ ((x.1.1 - h, x.1.2), x.2)

/-- The translation of a clock state, as a linear map. -/
def deviceShiftₗ (h : ZMod L) :
    ((ZMod L × Fin 2) × Fin 2 → ℂ) →ₗ[ℂ] ((ZMod L × Fin 2) × Fin 2 → ℂ) where
  toFun := deviceShift h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem deviceShift_ne_zero (h : ZMod L) {Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ} (hΨ : Ψ ≠ 0) :
    deviceShift h Ψ ≠ 0 := fun h0 => hΨ (funext fun x => by
  have h1 := congrFun h0 ((x.1.1 + h, x.1.2), x.2)
  simpa [deviceShift] using h1)

theorem deviceRegionWeight_deviceShift (h : ZMod L) (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ)
    (A : Finset (ZMod L)) :
    deviceRegionWeight (deviceShift h Ψ) A = deviceRegionWeight Ψ (A.image fun k => k - h) := by
  rw [deviceRegionWeight, deviceRegionWeight,
    show (fun p => deviceShift h Ψ (p, 0)) = chainShift h (fun p => Ψ (p, 0)) from rfl,
    show (fun p => deviceShift h Ψ (p, 1)) = chainShift h (fun p => Ψ (p, 1)) from rfl,
    regionWeight_chainShift, regionWeight_chainShift]

variable [NeZero L]

theorem deviceCoherence_deviceShift (h : ZMod L) (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) :
    deviceCoherence (deviceShift h Ψ) = deviceCoherence Ψ := by
  rw [deviceCoherence, deviceCoherence]
  exact Fintype.sum_equiv ((Equiv.subRight h).prodCongr (Equiv.refl (Fin 2))) _ _ fun _ => rfl

theorem deviceNorm_deviceShift (h : ZMod L) (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) :
    deviceNorm (deviceShift h Ψ) = deviceNorm Ψ := by
  rw [deviceNorm, deviceNorm]
  exact Fintype.sum_equiv
    (((Equiv.subRight h).prodCongr (Equiv.refl (Fin 2))).prodCongr (Equiv.refl (Fin 2))) _ _
    fun _ => rfl

/-- ★ **Translation commutes with the clock's energy.** -/
theorem deviceHam_mulVec_deviceShift (J μ₀ μ₁ : ℝ) (h : ZMod L)
    (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) :
    deviceHam J μ₀ μ₁ *ᵥ deviceShift h Ψ = deviceShift h (deviceHam J μ₀ μ₁ *ᵥ Ψ) := by
  funext ⟨p, i⟩
  rw [deviceHam_mulVec_apply]
  show _ = (deviceHam J μ₀ μ₁ *ᵥ Ψ) ((p.1 - h, p.2), i)
  rw [deviceHam_mulVec_apply,
    show (fun q => deviceShift h Ψ (q, i)) = chainShift h (fun q => Ψ (q, i)) from rfl,
    diracHam_mulVec_chainShift]
  rfl

/-- Translation commutes with the clock's evolution. -/
theorem deviceProp_mulVec_deviceShift (J μ₀ μ₁ t : ℝ) (h : ZMod L)
    (Ψ : (ZMod L × Fin 2) × Fin 2 → ℂ) :
    deviceProp (L := L) J μ₀ μ₁ t *ᵥ deviceShift h Ψ
      = deviceShift h (deviceProp J μ₀ μ₁ t *ᵥ Ψ) := by
  rw [deviceProp]
  exact (exp_smul_mulVec_intertwine (deviceShiftₗ h)
    (fun v => (deviceHam_mulVec_deviceShift J μ₀ μ₁ h v).symm) _ Ψ).symm

end Device

/-! ### A translated clock reads the same, somewhere else -/

section Clock

variable {M : ℕ}

/-- ★★ **A translated clock has the same uncoupled reading.** -/
theorem clockFreeRead_deviceShift (J μ₀ μ₁ : ℝ) (h : ZMod (M + 1))
    {Ψ : (ZMod (M + 1) × Fin 2) × Fin 2 → ℂ} (hΨ : Ψ ≠ 0) (s : ℝ) :
    clockFreeRead J μ₀ μ₁ (deviceRay (deviceShift h Ψ) (deviceShift_ne_zero h hΨ)) s
      = clockFreeRead J μ₀ μ₁ (deviceRay Ψ hΨ) s := by
  rw [clockFreeRead_deviceRay, clockFreeRead_deviceRay, deviceProp_mulVec_deviceShift,
    deviceCoherence_deviceShift, deviceNorm_deviceShift]

/-- ★★ **A translated clock moves its pointer the same**, on a fibre where the profile
vanishes. -/
theorem clockPointerShift_deviceShift {f : ℝ → ℝ} (J μ₀ μ₁ g : ℝ)
    (hf : Function.Periodic f 1) {φ : AddCircle (1 : ℝ)} (h0 : hf.lift φ = 0)
    (h : ZMod (M + 1)) {Ψ : (ZMod (M + 1) × Fin 2) × Fin 2 → ℂ} (hΨ : Ψ ≠ 0) (t : ℝ) :
    clockPointerShift J μ₀ μ₁ g hf φ
        (deviceRay (deviceShift h Ψ) (deviceShift_ne_zero h hΨ)) t
      = clockPointerShift J μ₀ μ₁ g hf φ (deviceRay Ψ hΨ) t := by
  rw [clockPointerShift, clockPointerShift]
  simp only [clockRead_of_lift_eq_zero J μ₀ μ₁ g hf h0,
    clockFreeRead_deviceShift J μ₀ μ₁ h hΨ]

/-- ★★ **A translated clock's occupancy of a region along its orbit** is the original's
occupancy of the region translated back. -/
theorem sum_arenaObs_siteSel_deviceShift (J μ₀ μ₁ : ℝ) (h : ZMod (M + 1))
    {Ψ : (ZMod (M + 1) × Fin 2) × Fin 2 → ℂ} (hΨ : Ψ ≠ 0) (A : Finset (ZMod (M + 1)))
    (s : ℝ) :
    ∑ k ∈ A, arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k)
        (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1) J μ₀ μ₁) s)
          (deviceRay (deviceShift h Ψ) (deviceShift_ne_zero h hΨ)))
      = ∑ k ∈ A.image fun k => k - h,
          arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k)
            (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1) J μ₀ μ₁) s)
              (deviceRay Ψ hΨ)) := by
  rw [sum_arenaObs_siteSel_free_deviceRay, sum_arenaObs_siteSel_free_deviceRay,
    deviceProp_mulVec_deviceShift, deviceRegionWeight_deviceShift, deviceNorm_deviceShift]

end Clock

/-! ### Arcs under translation -/

section Arcs

variable {L : ℕ} [NeZero L]

/-- The angle of a translated site. -/
theorem cos_site_sub (k h : ZMod L) (x : ℝ) :
    Real.cos (2 * Real.pi * (k - h).val / L - x)
      = Real.cos (2 * Real.pi * k.val / L - 2 * Real.pi * h.val / L - x) := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hc : (((k - h).val : ℤ) : ZMod L) = (((k.val : ℤ) - (h.val : ℤ) : ℤ) : ZMod L) := by
    push_cast
    simp
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hc
  obtain ⟨m, hm⟩ := hc
  have e : ((k - h).val : ℝ) = k.val - h.val - L * m := by
    have h1 := congrArg (fun z : ℤ => (z : ℝ)) hm
    push_cast at h1
    linarith
  have e2 : 2 * Real.pi * ((k.val : ℝ) - h.val - L * m) / L - x
      = (2 * Real.pi * k.val / L - 2 * Real.pi * h.val / L - x) - m * (2 * Real.pi) := by
    field_simp
    ring
  rw [e, e2, Real.cos_sub_int_mul_two_pi]

theorem mem_ringArc_sub {x δ : ℝ} {k h : ZMod L} :
    k - h ∈ ringArc L x δ ↔ k ∈ ringArc L (x + 2 * Real.pi * h.val / L) δ := by
  rw [mem_ringArc, mem_ringArc, cos_site_sub,
    show 2 * Real.pi * k.val / L - 2 * Real.pi * h.val / L - x
      = 2 * Real.pi * k.val / L - (x + 2 * Real.pi * h.val / L) by ring]

/-- The arc about a translated angle, translated back, is the arc about the angle. -/
theorem image_sub_ringArc (x δ : ℝ) (h : ZMod L) :
    (ringArc L (x + 2 * Real.pi * h.val / L) δ).image (fun k => k - h) = ringArc L x δ := by
  ext k
  rw [Finset.mem_image]
  constructor
  · rintro ⟨k', hk', rfl⟩
    exact mem_ringArc_sub.2 hk'
  · intro hk
    exact ⟨k + h, mem_ringArc_sub.1 (by rwa [add_sub_cancel_right]), add_sub_cancel_right k h⟩

end Arcs

/-! ### The clock at rest, at any place on the ring -/

section FarWall

variable {n N M : ℕ}

/-- ★★★ **The clock at rest, translated, swings with a margin.** The clock of
`wall_clock_ticks`, translated by any `h`: for `1 ≤ j ≤ n` and some strength `0 < g ≤ R/5`
its pointer's displacement on the fibre `0` is within `1/(24 j)` of `(1/4)(1 − cos R t)` up
to `2π n/(j R)`, `R` the rate at momentum `0`. -/
theorem far_wall_clock_swing_fine {j : ℕ} (hj : 0 < j) (hjn : j ≤ n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ 1 / 2)
    (h : ZMod (M + 1)) :
    ∃ (g : ℝ) (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
          (wallWindow N ∪ negWin (wallWindow N)) (oddExt (wallWindow N) (flatAmpN N))
          (-(Real.pi / (2 * ringRate (1200 * n * N) M 0 Δ))) ≠ 0),
      0 < g ∧ g ≤ ringRate (1200 * n * N) M 0 Δ / 5
      ∧ ∀ t, 0 ≤ t → t ≤ 2 * Real.pi * n / (j * ringRate (1200 * n * N) M 0 Δ) →
        |clockPointerShift (ringHop (1200 * n * N) M) 1 (1 + Δ) g trainF_periodic
              (0 : AddCircle (1 : ℝ))
              (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨ)) t
            - 1 / 4 * (1 - Real.cos (ringRate (1200 * n * N) M 0 Δ * t))|
          ≤ 1 / (24 * j) := by
  obtain ⟨g, hΨ, hg0, hg, hsw⟩ := wall_clock_swing_fine (M := M) hj hjn hN hM hΔ0 hΔ
  refine ⟨g, hΨ, hg0, hg, fun t ht0 ht => ?_⟩
  rw [clockPointerShift_deviceShift _ _ _ _ trainF_periodic trainF_lift_zero h hΨ]
  exact hsw t ht0 ht

/-- ★★★ **The clock at rest, translated, stays where it was put.** The clock of
`wall_clock_ticks`, translated by `h`, along its uncoupled orbit from the packet time `t₁`:
at every flow time `s` the occupancy outside the arc of half-angle `δ` about the angle
`2π h/L`, times `1 − cos δ`, is at most `4 · lightBudget n N 1 (t₁ + s)`. -/
theorem far_wall_clock_outside_le (hn : 0 < n) (hN : 0 < N)
    (hM : 210000 * n ^ 2 * N ≤ M) {Δ : ℝ} (hΔ0 : 0 < Δ) (h : ZMod (M + 1)) (t₁ : ℝ)
    (hΨ : devicePacket (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ)
      (wallWindow N ∪ negWin (wallWindow N)) (oddExt (wallWindow N) (flatAmpN N)) t₁ ≠ 0)
    {δ : ℝ} (hδ : Real.cos δ < 1) (s : ℝ) :
    (1 - ∑ k ∈ ringArc (M + 1) (0 + 2 * Real.pi * h.val / (M + 1 : ℕ)) δ,
        arenaObs (siteSel (fun x : (ZMod (M + 1) × Fin 2) × Fin 2 => x.1.1) k)
          (arenaKick (idxFreeU (deviceHam_isHermitian (L := M + 1)
            (ringHop (1200 * n * N) M) 1 (1 + Δ)) s)
            (deviceRay (deviceShift h _) (deviceShift_ne_zero h hΨ)))) * (1 - Real.cos δ)
      ≤ 4 * lightBudget n N 1 (t₁ + s) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h4 : 4 * N ≤ M := by
    have h1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
    have h2 : 4 * N ≤ 210000 * n ^ 2 * N := Nat.mul_le_mul_right N (by nlinarith)
    exact h2.trans hM
  have hN1 : 1 ≤ N := hN
  have hhi : 2 * ((1 : ℤ) + N) ≤ M := by
    have : (4 * N : ℤ) ≤ M := by exact_mod_cast h4
    have : (1 : ℤ) ≤ N := by exact_mod_cast hN1
    linarith
  have hWD : ∀ m ∈ Finset.Ico (1 : ℤ) (1 + N),
      |2 * Real.pi * m / ringLen (1200 * n * N) - 0| ≤ 1 / (600 * n) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have h1 : (0 : ℝ) ≤ m := by exact_mod_cast (by omega : (0 : ℤ) ≤ m)
    have h2 : (m : ℝ) ≤ N := by exact_mod_cast (by omega : m ≤ (N : ℤ))
    have hπ := Real.pi_pos
    have hden : (0 : ℝ) < 1200 * n * N := by positivity
    have e : 2 * Real.pi * (m : ℝ) / ringLen (1200 * n * N) = (m : ℝ) / (1200 * n * N) := by
      rw [ringLen]
      push_cast
      field_simp
    rw [e, sub_zero, abs_of_nonneg (by positivity), div_le_div_iff₀ hden (by positivity)]
    nlinarith
  have b := one_sub_sum_arenaObs_wallArcs_icoDevice_time_le (lo := 1) (p₀ := 0) hn hN hM hΔ0
    one_pos hhi (by rw [abs_zero]; norm_num) hWD t₁ hΨ hδ s
  simp only [mul_zero, vRel, zero_div, zero_mul] at b
  have e : wallArc (M + 1) 0 δ ∪ wallArc (M + 1) 0 δ = ringArc (M + 1) 0 δ := by
    rw [Finset.union_self, wallArc, neg_zero, Finset.union_self]
  rw [e] at b
  rw [sum_arenaObs_siteSel_deviceShift, image_sub_ringArc]
  exact b

end FarWall

end CSD.RecordLayer

end
