/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.PointerBorn

/-!
# SigmaLayer/PointerGeneration: the Schrödinger generation of the smooth witness (brick 5)

**Category:** dynamical measurement — the smooth-Hamiltonian witness route
(`specs/pointer-witness-plan.md` brick 5; completes the ladder).

★ **The generation theorem** (`rampedU_schrodinger`): on the interaction window `t ∈ (0, 1)`,
the ramped propagator of the smooth witness satisfies the **Schrödinger equation**

  `U̇(t) = U(t) · (−i · H_eff(w))`,  `H_eff(w) = (π/2) • couplingH w`  **Hermitian**
  (`pointerHeff_isHermitian`),

as a machine-checked `HasDerivAt`, for **every** weight vector — in particular for the
selector-modulated weights `w = pointerWeights c ε x` at every ontic point. Together with
brick 2a's `pointerRot_eq_exp` (the single-plane closed form **is** its exponential, by ODE
uniqueness), this is the Hamiltonian-generation statement at the formalisable level: the
record-creating dynamics is the flow of an explicit Hermitian generator family — not a
piecewise map wearing a Hamiltonian label. The torus-flux obstruction that killed the
register-translation reading (`PiecewiseHamiltonian.lean`, 2026-08-02 correction) does not
exist here: the pointer is projective (`H¹(ℂℙ^K) = 0`), and the generator is exhibited, not
asserted.

**The no-collapse theorem** (`pointerEvolve_base_marginal_unchanged`): the measurement
stroke leaves the sector marginal of **every** initial measure untouched — the smooth
witness, like the shear (`shear_base_marginal_unchanged`), creates records **without
back-reaction**. Records yes, collapse no: this is the honest boundary of the smooth horn,
stated as a theorem rather than left implicit.

⚠️ **Honest scope.**

* The ODE holds on the **open** interaction window; at the ramp corners `t ∈ {0, 1}` the
  `C⁰` ramp is not differentiable (one-sided derivatives differ). A `C^∞` ramp variant
  would move the corners' smoothing into the ramp with no structural change; recorded as a
  presentational upgrade, not a gap — the propagator itself is continuous in time and state
  everywhere (`continuous_pointerRampedEvolve`).
* The **symplectic/moment-map reading** of "the flow of `H_eff` is the Hamiltonian flow of
  the FS moment map" remains prose: Mathlib has no symplectic-manifold API
  (`MATHLIB-GAPS.md`) — the *same* §2a-scoped boundary as A1/A3, but with no flux
  obstruction hiding behind it.
* **The Lüders composition is a recorded extension, not delivered here**: the smooth
  witness does not collapse (that is the no-collapse theorem above, a feature of its
  design); the ψ-dependent state update lives on the swap/join witnesses
  (`swap_luders_born`, `joinWitness_blockLuders`). Composing the smooth record stroke with
  the relocation machinery on one arena is the recorded `M–L` item in
  [`BACKLOG.md`](../../specs/BACKLOG.md), alongside the LLN layer over the ε-Born sandwich.

## References

`specs/pointer-witness-plan.md` (brick 5, closing the ladder); `specs/BACKLOG.md`;
`specs/reconstruction-status.md` §2a (A2); `specs/future-work.md`. Reused corpus API:
`couplingUAt`/`pointerRamp` (`SigmaLayer/PointerProtocol.lean`), `couplingH_isHermitian`
(`PointerCoupling.lean`), `pointerEvolve_fst` (`PointerWeights.lean`),
`hasDerivAt_exp_smul_const` (Mathlib), `shear_base_marginal_unchanged` (the piecewise
counterpart).
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory Matrix Matrix.UnitaryGroup NormedSpace Filter
open scoped Matrix.Norms.L2Operator Topology

variable {K : ℕ}

/-! ### The effective Hamiltonian -/

/-- The effective Hamiltonian of the measurement stroke: `H_eff(w) = (π/2) • couplingH w`
— the coupling, at the stroke rate the ramp actually runs. -/
noncomputable def pointerHeff (w : Fin K → ℝ) : Matrix (Fin (K + 1)) (Fin (K + 1)) ℂ :=
  (Real.pi / 2 : ℝ) • couplingH w

/-- **The effective Hamiltonian is Hermitian** — a real multiple of the Hermitian
coupling. -/
theorem pointerHeff_isHermitian (w : Fin K → ℝ) : (pointerHeff w).IsHermitian := by
  show (pointerHeff w)ᴴ = pointerHeff w
  rw [pointerHeff, Matrix.conjTranspose_smul, star_trivial, (couplingH_isHermitian w).eq]

/-! ### The generation theorem -/

/-- ★ **The Schrödinger equation of the smooth witness**: on the interaction window
`t ∈ (0, 1)`, the ramped propagator satisfies

  `U̇(t) = U(t) · (−i • H_eff(w))`

with the explicit Hermitian generator `pointerHeff w` — for every start time `s` and every
weight vector, hence for the selector-modulated weights at every ontic point. The
Hamiltonian-generation statement at the formalisable level. -/
theorem rampedU_schrodinger (w : Fin K → ℝ) (s : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun u => couplingUAt (pointerRamp u - pointerRamp s) w)
      (couplingUAt (pointerRamp t - pointerRamp s) w * ((-Complex.I) • pointerHeff w))
      t := by
  set A := (-Complex.I) • couplingH w with hA
  -- the affine angle on the window
  have haff : HasDerivAt (fun u : ℝ => Real.pi / 2 * u - pointerRamp s) (Real.pi / 2) t := by
    simpa using ((hasDerivAt_id t).const_mul (Real.pi / 2)).sub_const (pointerRamp s)
  -- derivative of the exponential at the affine angle
  have hexp := hasDerivAt_exp_smul_const A (Real.pi / 2 * t - pointerRamp s)
  have hcomp := HasDerivAt.scomp t hexp haff
  -- the curve agrees with the affine-angle exponential near `t`
  have hEE : (fun u => couplingUAt (pointerRamp u - pointerRamp s) w)
      =ᶠ[nhds t] fun u => NormedSpace.exp ((Real.pi / 2 * u - pointerRamp s) • A) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    rw [couplingUAt, pointerRamp, max_eq_right hu.1.le, min_eq_right hu.2.le]
  have hgoal := (hcomp.congr_of_eventuallyEq hEE)
  -- massage the derivative and the point
  have hpt : pointerRamp t = Real.pi / 2 * t := by
    rw [pointerRamp, max_eq_right ht.1.le, min_eq_right ht.2.le]
  have hder : couplingUAt (pointerRamp t - pointerRamp s) w * ((-Complex.I) • pointerHeff w)
      = (Real.pi / 2 : ℝ) • (NormedSpace.exp ((Real.pi / 2 * t - pointerRamp s) • A) * A) := by
    have h1 : (-Complex.I) • pointerHeff w = (Real.pi / 2 : ℝ) • A := by
      rw [pointerHeff, hA, smul_comm]
    rw [h1, mul_smul_comm, couplingUAt, hpt]
  rw [hder]
  exact hgoal

/-! ### The no-collapse theorem -/

variable {N : ℕ} [NeZero N]

/-- **The smooth witness creates records without back-reaction**: the measurement stroke
leaves the sector marginal of every initial measure untouched — the smooth counterpart of
`shear_base_marginal_unchanged`. Records yes, collapse no; the ψ-dependent state update
lives on the swap/join witnesses, and composing the two is the recorded extension. -/
theorem pointerEvolve_base_marginal_unchanged (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) (ε : ℝ)
    (μ : Measure (PointerArena N N)) :
    (μ.map (pointerEvolve c ε)).map Prod.fst = μ.map Prod.fst := by
  rw [Measure.map_map measurable_fst (continuous_pointerEvolve c hc ε).measurable]
  rfl

end CSD.RecordLayer
