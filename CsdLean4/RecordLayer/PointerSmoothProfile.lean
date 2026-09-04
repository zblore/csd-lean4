/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.PointerGeneration
public import CsdLean4.RecordLayer.SmoothProfile
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
review 2026-08-03); `RecordLayer/PointerWeights.lean` (`clampDiv`, `pointerWeights`, the
trapezoid interface this mirrors), `RecordLayer/PointerProtocol.lean` (`couplingUAt`,
`pointerRamp`), `RecordLayer/PointerGeneration.lean` (`pointerHeff`,
`rampedU_schrodinger`, the honest-scope boundary), `Mathlib.Analysis.SpecialFunctions.
SmoothTransition` (`Real.smoothTransition`).
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory Matrix NormedSpace Filter
open scoped Matrix.Norms.L2Operator Topology

/-! ### Schrödinger at every time -/

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
