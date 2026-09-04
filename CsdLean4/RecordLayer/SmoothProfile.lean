/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.CircleFibre
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# SigmaLayer/SmoothProfile: the `C^∞` transition profile and arc weight

**Category:** dynamical measurement — the low-level `C^∞` primitives of the ε-corridor
witness.

Extracted 2026-08-04 from `PointerSmoothProfile.lean` so that `PointerWeights.lean` can
**use** them rather than merely cite them. That module sits *above* the pointer stack in
the import graph (`PointerWeights → … → PointerBorn → PointerGeneration →
PointerSmoothProfile`), so while the smooth profiles lived there the witness could not be
built on them — and it was not: before this extraction `grep` found **zero consumers** of
these definitions outside their own file. Two external reviews listed that as outstanding
and it was twice recorded as "mechanical"; the extraction is what makes doing it possible.

Why it is load-bearing rather than cosmetic: the Poisson bracket `{wᵢ, wⱼ}` that the
joint-arena Hamiltonian route turns on is **undefined** on the old trapezoid weights,
because `clampDiv = max 0 (min 1 (u/ε))` is Lipschitz but not `C¹`. Smooth weights are a
*prerequisite* for that argument, not a presentational upgrade (`specs/BACKLOG.md` A2/B1).

Contents: `smoothClampDiv` (the `Real.smoothTransition` profile, same plateaus as
`clampDiv` with the same hypotheses), `smoothArcWeight` (its circle-distance form), and
★ `contDiff_smoothArcWeight_lift` — the periodic lift is `C^∞` on the universal cover,
the circle-distance kinks at the cell centre and the cut locus both falling inside
plateaus.

⚠️ **Honest scope.** Smoothness is of the **periodic lift on `ℝ`**, under `2ε < r` and
`r < 1`; manifold-level smoothness on `KSigma` remains the §2a-scoped A1/A3 boundary
(`MATHLIB-GAPS.md`). The time ramp is deliberately **not** moved here: it is not a
phase-space function, so it plays no part in the Poisson prerequisite, and substituting it
would change the capstone's `generation` field to carry a rate factor — a separate
decision, recorded in `BACKLOG.md`.

## References

`specs/BACKLOG.md` (B1, and A2 which depends on it); `RecordLayer/PointerWeights.lean` (the
consumer); `RecordLayer/PointerSmoothProfile.lean` (the time ramp and the global-time
Schrödinger ODE, which stay there).
-/

@[expose] public section

namespace CSD.RecordLayer

open Filter
open scoped Topology

/-! ### The smooth clamp -/

/-- The smooth `[0,1]` transition profile `u ↦ smoothTransition (u/ε)`: `0` for `u ≤ 0`,
`1` for `u ≥ ε`, `C^∞` everywhere — `clampDiv` with the corner-free profile. -/
noncomputable def smoothClampDiv (ε u : ℝ) : ℝ := Real.smoothTransition (u / ε)

lemma smoothClampDiv_nonneg (ε u : ℝ) : 0 ≤ smoothClampDiv ε u :=
  Real.smoothTransition.nonneg _

lemma smoothClampDiv_le_one (ε u : ℝ) : smoothClampDiv ε u ≤ 1 :=
  Real.smoothTransition.le_one _

/-- Same plateau as `clampDiv_eq_one`, same hypotheses. -/
lemma smoothClampDiv_eq_one {ε u : ℝ} (hε : 0 < ε) (hu : ε ≤ u) : smoothClampDiv ε u = 1 :=
  Real.smoothTransition.one_of_one_le ((le_div_iff₀ hε).mpr (by linarith))

/-- Same plateau as `clampDiv_eq_zero`, same hypotheses. -/
lemma smoothClampDiv_eq_zero {ε u : ℝ} (hε : 0 < ε) (hu : u ≤ 0) : smoothClampDiv ε u = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hu hε.le)

/-- **The smooth clamp is `C^∞`** — what the trapezoid could not be at its joins. -/
lemma contDiff_smoothClampDiv (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (smoothClampDiv ε) :=
  Real.smoothTransition.contDiff.comp (contDiff_id.div_const ε)

/-! ### The smooth arc weight and its lift -/

/-- The smooth arc weight at cell radius `r` and midpoint `mid`: the smooth clamp of the
signed depth into the cell. The smooth counterpart of `pointerWeights`' per-cell profile. -/
noncomputable def smoothArcWeight (ε r : ℝ) (mid θ : CircleFibre) : ℝ :=
  smoothClampDiv ε (r / 2 - dist θ mid)

lemma smoothArcWeight_nonneg (ε r : ℝ) (mid θ : CircleFibre) :
    0 ≤ smoothArcWeight ε r mid θ := smoothClampDiv_nonneg _ _

lemma smoothArcWeight_le_one (ε r : ℝ) (mid θ : CircleFibre) :
    smoothArcWeight ε r mid θ ≤ 1 := smoothClampDiv_le_one _ _

/-- In the `ε`-shrunk cell arc, the smooth weight is exactly `1` — the same plateau fact,
with the same hypotheses, as `pointerWeights_eq_one`. -/
lemma smoothArcWeight_eq_one {ε r : ℝ} (hε : 0 < ε) {mid θ : CircleFibre}
    (hθ : dist θ mid ≤ r / 2 - ε) : smoothArcWeight ε r mid θ = 1 :=
  smoothClampDiv_eq_one hε (by linarith)

/-- Off the open cell arc, the smooth weight is exactly `0` — the same plateau fact, with
the same hypotheses, as `pointerWeights_eq_zero`. -/
lemma smoothArcWeight_eq_zero {ε r : ℝ} (hε : 0 < ε) {mid θ : CircleFibre}
    (hθ : r / 2 ≤ dist θ mid) : smoothArcWeight ε r mid θ = 0 :=
  smoothClampDiv_eq_zero hε (by linarith)

/-- The lift of the smooth arc weight to the universal cover is `1`-periodic — the
smoothness statement below is genuinely a statement about the circle function. -/
lemma smoothArcWeight_lift_periodic (ε r mid : ℝ) :
    Function.Periodic (fun s : ℝ => smoothArcWeight ε r (mid : CircleFibre) (s : CircleFibre))
      1 := by
  intro s
  have hcoe : ((s + 1 : ℝ) : CircleFibre) = (s : CircleFibre) := by
    rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]
  simp only [hcoe]

/-- ★ **The smooth arc weight is `C^∞` on the universal cover.** The circle distance has
kinks at the cell centre and at the cut locus, but both fall inside plateaus of the
transition profile — near the centre the weight is identically `1` (`ε < r/2`), near the
cut locus identically `0` (`r < 1`) — and a locally constant function is smooth no matter
what it is composed with. In the transition zone `d ∈ [r/2−ε, r/2]` the distance lift is
locally affine, so the composition is a smooth profile of an affine function. -/
theorem contDiff_smoothArcWeight_lift {ε r : ℝ} (hε : 0 < ε) (h2ε : 2 * ε < r)
    (hr : r < 1) (mid : ℝ) {n : ℕ∞} :
    ContDiff ℝ n
      (fun s : ℝ => smoothArcWeight ε r (mid : CircleFibre) (s : CircleFibre)) := by
  have hdc : Continuous fun s : ℝ => dist ((s : ℝ) : CircleFibre) ((mid : ℝ) : CircleFibre) :=
    Continuous.dist ((AddCircle.continuous_mk' (p := (1 : ℝ))).comp continuous_id)
      continuous_const
  rw [contDiff_iff_contDiffAt]
  intro s₀
  set d₀ : ℝ := dist ((s₀ : ℝ) : CircleFibre) ((mid : ℝ) : CircleFibre) with hd₀
  by_cases hA : d₀ < r / 2 - ε
  · -- centre plateau: locally ≡ 1
    refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hdc.continuousAt.preimage_mem_nhds (Iio_mem_nhds hA)] with s hs
    exact smoothArcWeight_eq_one hε (le_of_lt hs)
  by_cases hB : r / 2 < d₀
  · -- cut-locus plateau: locally ≡ 0
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hdc.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hB)] with s hs
    exact smoothArcWeight_eq_zero hε (le_of_lt hs)
  -- transition zone: the distance lift is locally affine
  have hd₀lo : r / 2 - ε ≤ d₀ := not_lt.mp hA
  have hd₀hi : d₀ ≤ r / 2 := not_lt.mp hB
  have hd₀pos : 0 < d₀ := lt_of_lt_of_le (by linarith) hd₀lo
  have hd₀half : d₀ < 1 / 2 := lt_of_le_of_lt hd₀hi (by linarith)
  -- the distance at the base point, in round form
  have hdist₀ : d₀ = |s₀ - mid - round (s₀ - mid)| := by
    rw [hd₀, dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]
  set R : ℤ := round (s₀ - mid) with hR
  have htIoo : s₀ - mid - R ∈ Set.Ioo (-(1 / 2) : ℝ) (1 / 2) := by
    have := abs_lt.mp (hdist₀ ▸ hd₀half)
    exact ⟨by linarith [this.1], this.2⟩
  -- round is locally constant strictly inside the half-integer window
  have hround : ∀ y : ℝ, y ∈ Set.Ioo ((R : ℝ) - 1 / 2) ((R : ℝ) + 1 / 2) → round y = R := by
    intro y hy
    rw [round_eq]
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    · linarith [hy.1]
    · linarith [hy.2]
  have hIoo1 : (R : ℝ) - 1 / 2 < s₀ - mid := by
    have h1 := htIoo.1
    linarith
  have hIoo2 : s₀ - mid < (R : ℝ) + 1 / 2 := by
    have h2 := htIoo.2
    linarith
  have hev1 : ∀ᶠ s in 𝓝 s₀, s - mid ∈ Set.Ioo ((R : ℝ) - 1 / 2) ((R : ℝ) + 1 / 2) :=
    (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
      (Ioo_mem_nhds hIoo1 hIoo2)
  have ht₀ne : s₀ - mid - (R : ℝ) ≠ 0 := fun h =>
    hd₀pos.ne' (by rw [hdist₀, h, abs_zero])
  -- eventual agreement of the circle distance with a signed affine function
  rcases lt_or_gt_of_ne ht₀ne with hneg | hpos
  · -- distance = −(s − mid − R) locally
    have hev2 : ∀ᶠ s in 𝓝 s₀, s - mid - R < 0 :=
      ((continuous_id.sub continuous_const).sub continuous_const).continuousAt.preimage_mem_nhds
        (Iio_mem_nhds hneg)
    have hsm : ContDiff ℝ n fun s : ℝ => smoothClampDiv ε (r / 2 - -(s - mid - (R : ℝ))) :=
      (contDiff_smoothClampDiv ε).comp
        (contDiff_const.sub (((contDiff_id.sub contDiff_const).sub contDiff_const).neg))
    refine hsm.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [hev1, hev2] with s hs1 hs2
    show smoothArcWeight ε r (mid : CircleFibre) (s : CircleFibre)
      = smoothClampDiv ε (r / 2 - -(s - mid - (R : ℝ)))
    rw [smoothArcWeight, dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq,
      hround _ hs1, abs_of_neg hs2]
  · -- distance = s − mid − R locally
    have hev2 : ∀ᶠ s in 𝓝 s₀, 0 < s - mid - R :=
      ((continuous_id.sub continuous_const).sub continuous_const).continuousAt.preimage_mem_nhds
        (Ioi_mem_nhds hpos)
    have hsm : ContDiff ℝ n fun s : ℝ => smoothClampDiv ε (r / 2 - (s - mid - (R : ℝ))) :=
      (contDiff_smoothClampDiv ε).comp
        (contDiff_const.sub ((contDiff_id.sub contDiff_const).sub contDiff_const))
    refine hsm.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [hev1, hev2] with s hs1 hs2
    show smoothArcWeight ε r (mid : CircleFibre) (s : CircleFibre)
      = smoothClampDiv ε (r / 2 - (s - mid - (R : ℝ)))
    rw [smoothArcWeight, dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq,
      hround _ hs1, abs_of_pos hs2]


/-! ### The smooth time ramp -/

/-- The smooth time ramp: `0` before the stroke, `π/2` after, `C^∞` throughout. Moved here
2026-08-04 (B1b) so that `PointerProtocol.lean` can be built on it. -/
noncomputable def smoothPointerRamp (t : ℝ) : ℝ := Real.pi / 2 * Real.smoothTransition t

/-- Before the stroke the smooth ramp is `0`. -/
lemma smoothPointerRamp_of_nonpos {t : ℝ} (ht : t ≤ 0) : smoothPointerRamp t = 0 := by
  rw [smoothPointerRamp, Real.smoothTransition.zero_of_nonpos ht, mul_zero]

/-- After the stroke the smooth ramp is `π/2`, so freezing/persistence consume it
unchanged. -/
lemma smoothPointerRamp_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    smoothPointerRamp t = Real.pi / 2 := by
  rw [smoothPointerRamp, Real.smoothTransition.one_of_one_le ht, mul_one]

/-- **The smooth ramp is `C^∞`.** -/
lemma contDiff_smoothPointerRamp {n : ℕ∞} : ContDiff ℝ n smoothPointerRamp :=
  contDiff_const.mul Real.smoothTransition.contDiff

end CSD.RecordLayer
