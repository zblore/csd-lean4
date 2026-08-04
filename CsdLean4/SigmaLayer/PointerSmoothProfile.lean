/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.PointerGeneration
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# SigmaLayer/PointerSmoothProfile: `C^∞` ingredients for the ε-corridor witness

**Category:** dynamical measurement — the `C^∞` ingredient upgrade recorded against the
fourth external review's "continuous, not smooth" finding (2026-08-03).

The ε-corridor witness's transition profiles were trapezoids: `clampDiv` (`max`/`min` of a
linear ramp) in the weights, `pointerRamp` (piecewise-linear) in time — Lipschitz, proved
`Continuous`, not `C¹` at their joins. This module replaces the *profile* with
`Real.smoothTransition` and proves genuine smoothness, while keeping the **plateau
interface verbatim identical** — every fact the landing/Born/protocol analysis consumes
(`= 1` on the shrunk arc, `= 0` off the open arc, values in `[0,1]`, `0` before the
stroke, `π/2` after) holds for the smooth profiles with the *same statements and the same
hypotheses*. Only the shape of the transition corridor changed.

- `smoothClampDiv ε u = smoothTransition (u/ε)` — the smooth clamp: same plateaus as
  `clampDiv`, and `C^∞` (`contDiff_smoothClampDiv`).
- ★ `contDiff_smoothArcWeight_lift` — **the smooth arc weight is `C^∞` on the universal
  cover**: the periodic lift of `s ↦ smoothClampDiv ε (r/2 − dist(s, mid))` is
  `ContDiff ℝ n` for every `n`, despite the circle distance's kinks at the cell centre
  and the cut locus — both kinks fall inside **plateaus** of the transition profile
  (centre: weight ≡ 1 since `ε < r/2`; cut locus: weight ≡ 0 since `r < 1`), where a
  locally constant function is smooth regardless of what it is composed with. The
  transition zone `d ∈ [r/2−ε, r/2]` avoids both kinks, and there the distance lift is
  locally affine. `smoothArcWeight_lift_periodic` descends the statement to the circle
  as a periodic function.
- ★ `smoothRampedU_schrodinger` — with the smooth time ramp
  `smoothPointerRamp t = (π/2)·smoothTransition t`, the ramped propagator satisfies the
  **Schrödinger equation at every time**, with the *time-dependent* generator
  `smoothTransition′(t) · H_eff` rather than the constant `H_eff` of `rampedU_schrodinger`
  (*Corrected 2026-08-04 (codebase audit).* — this header said simply "the Schrödinger equation"; the rate factor was always in
  the theorem and its docstring). This removes the open-window restriction of
  `rampedU_schrodinger`, which the trapezoid ramp's corners forced — exactly as
  `PointerGeneration.lean`'s honest scope predicted ("a `C^∞` ramp variant would move the
  corners' smoothing into the ramp with no structural change").

⚠️ **Honest scope.** (i) Smoothness is stated for the **periodic lifts on `ℝ`** (the
universal cover) — the strongest formulation expressible without a smooth-manifold
structure on the arena; manifold-level smoothness on `KSigma × ℂℙ^K` remains the
§2a-scoped A1/A3 boundary (`MATHLIB-GAPS.md`), and the *fibrewise* (not joint-arena
Hamiltonian) character of the flow is unchanged by this upgrade — see
`PointerGeneration.lean`'s dated boundary note. (ii) The hypotheses `2ε < r` (the shrunk
cell is nonempty — already the ε-Born sandwich's nonvacuity condition) and `r < 1` (an
antipodal transition exists to smooth; at `r = 1` there is one cell and no measurement)
are geometric, not technical debt. (iii) Re-instantiating the full protocol stack
(`PointerProtocol` → `PointerBorn`) with the smooth profiles is mechanical — the plateau
interface proved here is statement-for-statement the one the trapezoid analysis consumes,
and the two-time law (`couplingUAt_mul`) is ramp-agnostic — and is recorded, not
duplicated. (iv) The weight field's modulation across the *base* (selector-dependent
rates) is untouched: smoothness here is per cell at fixed rates.

## References

`specs/BACKLOG.md` (the `C^∞`-ingredients row — this discharges it; fourth external
review 2026-08-03); `SigmaLayer/PointerWeights.lean` (`clampDiv`, `pointerWeights`, the
trapezoid interface this mirrors), `SigmaLayer/PointerProtocol.lean` (`couplingUAt`,
`pointerRamp`), `SigmaLayer/PointerGeneration.lean` (`pointerHeff`,
`rampedU_schrodinger`, the honest-scope boundary), `Mathlib.Analysis.SpecialFunctions.
SmoothTransition` (`Real.smoothTransition`).
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory Matrix NormedSpace Filter
open scoped Matrix.Norms.L2Operator Topology

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
    · push_cast
      linarith [hy.1]
    · push_cast
      linarith [hy.2]
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

/-! ### The smooth time ramp, and Schrödinger at every time -/

/-- The smooth time ramp: `0` before the stroke, `π/2` after, `C^∞` throughout — the
trapezoid `pointerRamp` with the corner-free profile. -/
noncomputable def smoothPointerRamp (t : ℝ) : ℝ := Real.pi / 2 * Real.smoothTransition t

/-- Before the stroke the smooth ramp is `0` — the same plateau as `pointerRamp`'s. -/
lemma smoothPointerRamp_of_nonpos {t : ℝ} (ht : t ≤ 0) : smoothPointerRamp t = 0 := by
  rw [smoothPointerRamp, Real.smoothTransition.zero_of_nonpos ht, mul_zero]

/-- After the stroke the smooth ramp is `π/2` — the same plateau as `pointerRamp`'s, so
freezing/persistence consume it unchanged. -/
lemma smoothPointerRamp_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    smoothPointerRamp t = Real.pi / 2 := by
  rw [smoothPointerRamp, Real.smoothTransition.one_of_one_le ht, mul_one]

/-- **The smooth ramp is `C^∞`.** -/
lemma contDiff_smoothPointerRamp {n : ℕ∞} : ContDiff ℝ n smoothPointerRamp :=
  contDiff_const.mul Real.smoothTransition.contDiff

/-- ★ **Schrödinger at every time.** With the smooth ramp, the ramped propagator
satisfies the Schrödinger equation

  `U̇(t) = smoothTransition′(t) • (U(t) · (−i • H_eff(w)))`

for **every** `t : ℝ` — no open interaction window: the corners that forced
`rampedU_schrodinger` onto `(0,1)` are gone, exactly as `PointerGeneration.lean`'s honest
scope predicted. Outside `[0,1]` the ramp derivative vanishes and the equation reads
`U̇ = 0` — the propagator is frozen, which is the persistence structure said as an ODE. -/
theorem smoothRampedU_schrodinger {K : ℕ} (w : Fin K → ℝ) (s t : ℝ) :
    HasDerivAt (fun u => couplingUAt (smoothPointerRamp u - smoothPointerRamp s) w)
      (deriv Real.smoothTransition t •
        (couplingUAt (smoothPointerRamp t - smoothPointerRamp s) w
          * ((-Complex.I) • pointerHeff w))) t := by
  set A := (-Complex.I) • couplingH w with hA
  have hT : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition t) t :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero t).hasDerivAt
  have haff : HasDerivAt (fun u : ℝ => smoothPointerRamp u - smoothPointerRamp s)
      (Real.pi / 2 * deriv Real.smoothTransition t) t :=
    (hT.const_mul (Real.pi / 2)).sub_const (smoothPointerRamp s)
  have hexp := hasDerivAt_exp_smul_const A (smoothPointerRamp t - smoothPointerRamp s)
  have hcomp := HasDerivAt.scomp t hexp haff
  have hder : deriv Real.smoothTransition t •
        (couplingUAt (smoothPointerRamp t - smoothPointerRamp s) w
          * ((-Complex.I) • pointerHeff w))
      = (Real.pi / 2 * deriv Real.smoothTransition t) •
        (NormedSpace.exp ((smoothPointerRamp t - smoothPointerRamp s) • A) * A) := by
    have h1 : (-Complex.I) • pointerHeff w = (Real.pi / 2 : ℝ) • A := by
      rw [pointerHeff, hA, smul_comm]
    rw [h1, mul_smul_comm, couplingUAt, smul_smul, mul_comm]
  rw [hder]
  exact hcomp

end CSD.RecordLayer
