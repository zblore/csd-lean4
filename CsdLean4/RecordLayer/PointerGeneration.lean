/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.PointerBorn

/-!
# SigmaLayer/PointerGeneration: the Schrödinger generation of the smooth witness (brick 5)

**Category:** dynamical measurement — the smooth-Hamiltonian witness route
(`specs/pointer-witness-plan.md` brick 5; completes the ladder).

★ **The generation theorem** (`rampedU_schrodinger`): at **every** time `t : ℝ` the ramped
propagator of the smooth witness satisfies the **Schrödinger equation**

  `U̇(t) = smoothTransition′(t) • (U(t) · (−i · H_eff(w)))`,
  `H_eff(w) = (π/2) • couplingH w`  **Hermitian** (`pointerHeff_isHermitian`),

*(B1b, 2026-08-04: the ramp is now `C^∞`, so the open-window restriction `t ∈ (0,1)` is
gone. The price is the rate factor `smoothTransition′(t)` — a window-free ODE with a
time-dependent generator, in place of a constant-generator ODE on a punctured interval.
Outside `[0,1]` the factor vanishes and the equation reads `U̇ = 0`: persistence, as an
ODE.)*

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
stroke leaves the sector marginal of **every** initial measure untouched (for every context
with continuous rates — the theorem carries `hc`, *Corrected 2026-08-04 (codebase audit).*) — the smooth
witness, like the shear (`shear_base_marginal_unchanged`), creates records **without
back-reaction**. Records yes, collapse no: this is the honest boundary of the smooth horn,
stated as a theorem rather than left implicit.

⚠️ **Honest scope.**

* ~~The ODE holds on the **open** interaction window; at the ramp corners the `C⁰` ramp is
  not differentiable~~ — **superseded *B1b, 2026-08-04.***: `pointerRamp` *is* the `C^∞` profile now, so the
  ODE holds at **every** time. The trade taken: a rate factor `smoothTransition′(t)`
  multiplies the generator, i.e. a window-free ODE with a time-dependent generator replaces
  a constant-generator ODE on a punctured interval. Outside `[0,1]` the factor vanishes and
  the ODE reads `U̇ = 0` — persistence, as an ODE.
* The **symplectic/moment-map reading** of "the flow of `H_eff` is the Hamiltonian flow of
  the FS moment map" remains prose: Mathlib has no symplectic-manifold API
  (`MATHLIB-GAPS.md`) — the *same* §2a-scoped boundary as A1/A3, but with no flux
  obstruction hiding behind it.
* ⚠️ *Boundary sharpened 2026-08-03 (fourth external review, verified both ways):* the
  generation is **fibrewise**, not joint-arena. The arena propagator's generator is
  vertical, `(0, V_Q)`, while the natural joint scalar `𝓗(x,q) = μ_{H_eff(w(x))}(q)` has
  `d𝓗` with a nonzero horizontal component wherever the weights vary — so `ι_V ω ≠ d𝓗`
  on the ε-collars, and the flow there is *not* the Hamiltonian flow of any interaction
  scalar on the product structure. The suppressed horizontal component is register
  back-reaction, and `pointerEvolve_base_marginal_unchanged` below is its fingerprint,
  stated as a theorem. Mitigation, also exact: off the collars the weights are locally
  constant, `d𝓗` is vertical, and the flow is genuinely (locally) Hamiltonian — the
  non-Hamiltonicity defect shares the Born error's `O(ε)` budget. The accurate label is
  **continuous fibrewise-Schrödinger witness**; the full back-reacting joint flow (where
  the register moves mid-stroke and the exact moment-transport argument no longer applies)
  is the recorded research row in [`BACKLOG.md`](../../specs/BACKLOG.md).
* *Same review, same date:* the weight and ramp ingredients (`clampDiv`, `min`/`max`, the
  trapezoid) *were* Lipschitz and proved `Continuous`, not `C¹` at their joins — and the
  **weights are now `C^∞`** (substituted 2026-08-04, `RecordLayer/SmoothProfile.lean`;
  `contDiff_pointerWeights_lift`), which the joint-arena Poisson route required, since
  `{wᵢ,wⱼ}` is undefined on non-differentiable weights. The *time ramp* is deliberately
  still the trapezoid `pointerRamp`: it is not a phase-space function, so it plays no part
  in that argument, and swapping it would change this module's generation statement to
  carry a rate factor (see `smoothRampedU_schrodinger`). Historically, "smooth
  horn" names the ε-corridor architecture, not a `C^∞` claim. The `Real.smoothTransition`
  ingredient upgrade (plateaus cover the circle-distance kinks, so compositions stay
  smooth) *landed same day*: `PointerSmoothProfile.lean` — identical plateau interface,
  `C^∞` weight lift, Schrödinger at every time.
* ~~**The Lüders composition is a recorded extension, not delivered here**~~ **Delivered
  2026-08-05** (`RecordLayer/PointerLuders.lean` + `PointerLudersMarginal.lean`, BACKLOG
  B3b): the smooth record stroke composed with record-triggered relocation on one arena,
  with `pointer_luders_marginal` the conditioned post-measurement marginal. The
  no-collapse theorem below is untouched — the update is a *second* stroke. The ε-Born
  LLN layer landed 2026-08-04 (`PointerFrequency.lean`, B3a).

## References

`specs/pointer-witness-plan.md` (brick 5, closing the ladder); `specs/BACKLOG.md`;
`specs/reconstruction-status.md` §2a (A2); `specs/future-work.md`. Reused corpus API:
`couplingUAt`/`pointerRamp` (`RecordLayer/PointerProtocol.lean`), `couplingH_isHermitian`
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

/-- ★ **The Schrödinger equation of the smooth witness**, at **every** time `t : ℝ`:

  `U̇(t) = smoothTransition′(t) • (U(t) · (−i • H_eff(w)))`

with the explicit Hermitian generator `pointerHeff w` — for every start time `s` and every
weight vector, hence for the selector-modulated weights at every ontic point. The
Hamiltonian-generation statement at the formalisable level. (*B1b, 2026-08-04.*: the window `(0,1)` is
gone with the trapezoid ramp; the rate factor is what it cost.) -/
theorem rampedU_schrodinger (w : Fin K → ℝ) (s t : ℝ) :
    HasDerivAt (fun u => couplingUAt (pointerRamp u - pointerRamp s) w)
      (deriv Real.smoothTransition t •
        (couplingUAt (pointerRamp t - pointerRamp s) w * ((-Complex.I) • pointerHeff w)))
      t := by
  set A := (-Complex.I) • couplingH w with hA
  have hT : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition t) t :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero t).hasDerivAt
  have haff : HasDerivAt (fun u : ℝ => pointerRamp u - pointerRamp s)
      (Real.pi / 2 * deriv Real.smoothTransition t) t :=
    (hT.const_mul (Real.pi / 2)).sub_const (pointerRamp s)
  have hexp := hasDerivAt_exp_smul_const A (pointerRamp t - pointerRamp s)
  have hcomp := HasDerivAt.scomp t hexp haff
  have hder : deriv Real.smoothTransition t •
        (couplingUAt (pointerRamp t - pointerRamp s) w * ((-Complex.I) • pointerHeff w))
      = (Real.pi / 2 * deriv Real.smoothTransition t) •
        (NormedSpace.exp ((pointerRamp t - pointerRamp s) • A) * A) := by
    have h1 : (-Complex.I) • pointerHeff w = (Real.pi / 2 : ℝ) • A := by
      rw [pointerHeff, hA, smul_comm]
    rw [h1, mul_smul_comm, couplingUAt, smul_smul, mul_comm]
  rw [hder]
  exact hcomp

/-! ### The no-collapse theorem -/

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- **The smooth witness creates records without back-reaction**: the measurement stroke
leaves the sector marginal of every initial measure untouched — the smooth counterpart of
`shear_base_marginal_unchanged`. Records yes, collapse no; the ψ-dependent state update
is a *second*, record-triggered stroke (~~recorded extension~~ delivered 2026-08-05,
`PointerLudersMarginal.lean` — which leans on precisely this theorem's division of
labour). -/
theorem pointerEvolve_base_marginal_unchanged (c : ContextField N)
    (hc : ∀ j, Continuous fun p => c.rate p j) (ε : ℝ)
    (μ : Measure (PointerArena N N)) :
    (μ.map (pointerEvolve c ε)).map Prod.fst = μ.map Prod.fst := by
  rw [Measure.map_map measurable_fst (continuous_pointerEvolve c hc ε).measurable]
  rfl

end CSD.RecordLayer
