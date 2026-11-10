/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracPointerBorn

/-!
# The click law of the pointer of `Σ_*`: determined by the flow, and not an operator's expectation

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 7-SigmaLayer (the record layer). BACKLOG #355 — milestone **M3, part B** of the
author's programme "From `Σ` to physical spacetime". M3 asks whether the Hamiltonian and the
apparatus fix the measures of the outcome regions without a stipulated rate field (gate A of the
programme). Part A (`RecordLayer/DiracPointerBorn.lean`, #354) proved that a statistic read at one
time does not see the pointer. This module treats the event that does: *ready at `0` and displayed
at `T`*.

The click event `diracClick` is built from the two arcs, the readout time and the joint flow
`diracPointerFlow`, and from nothing else. Its probability under the preparation law
`epistemicMeasure` is `diracClickProb`, a function of the carrier's ray. Three things are proved.

**It is determined.** The probability is the average over the conserved angle `θ₂` of a fixed
function `clickWindow` of the pointer's displacement (`diracClickProb_eq_lintegral`). No rate field
enters and no region depends on the carrier.

**It has a cut-off.** Over a time `T` the pointer turns by at most
`|κ| (T w + (‖H_D‖ + |g f(θ₂)|) T²)`, where `w` is the occupancy of the detector's site the carrier
started with. Where that bound is below a sixth of a turn on every fibre, the click probability is
`0` (`diracClickProb_eq_zero_of_weight_le`): a carrier with a small, positive occupancy never
clicks. And no carrier clicks with the probability `1/6` of a ready pointer (`diracClickProb_lt`).

**It is not the expectation of an operator.** In quantum mechanics the probability of an outcome is
`⟨ψ, E ψ⟩ / ⟨ψ, ψ⟩` for an effect `E`, which on the arena is `arenaObs E p`. A function on rays
that vanishes at the rays of `e_a`, `e_a + s e_b` and `e_a − s e_b` differs from `arenaObs E`
somewhere by at least its value at the ray of `e_b` times `s² / (2 (1 + s²))`, for every matrix `E`
(`exists_mul_le_abs_sub_arenaObs`). The cut-off supplies the three zeros, the lower bound of part A
supplies the positive value, and so the click probability is at a positive distance from every
operator (`exists_mul_le_abs_diracClickProb_sub_arenaObs`).

`diracPointer_clickLaw` collects the three for the profile `trainF`. It is the statement the
programme's gate A asks for: the selected dynamics does determine a click probability, and that
probability is not the quantum one.

## The expectation of an operator along a real superposition

* `arenaObs_mk_eq_inner`; `pairVec`, `pairVec_ne_zero`, `norm_pairVec_sq`, `pairRay`,
  `arenaObs_pairRay` — the expectation at the ray of `e_a + s e_b` is a quadratic in `s` over
  `1 + s²`;
* ★★ `exists_mul_le_abs_sub_arenaObs` — **three zeros keep a function away from every operator.**

## The click event and its probability

* `diracClick`, `measurableSet_diracClick`, `diracClickProb`, `diracClickProb_eq_volume`;
* `clickWindow`, `clickWindow_le`, `clickWindow_eq_zero`, `clickWindow_eq_of_mem` — the window is
  `0` for a displacement below `1/6`, is `1/6` on `[1/3, 2/3]`, and is at most `1/6`;
* ★★★ `diracClickProb_eq_lintegral` — **the click law**: the click probability is the `θ₂`-average
  of the window of the displacement.

## Bounds on the click probability

* `abs_diracPointerShift_le_weight` — the displacement in terms of the initial occupancy;
* ★★★ `diracClickProb_eq_zero_of_weight_le` — **the weight cut-off**;
* `diracClickProb_le`, ★★ `diracClickProb_lt` — **no carrier clicks with the probability of a ready
  pointer**; `ofReal_mul_volume_writeFibres_le_diracClickProb` — the lower bound of part A.

## No operator gives the click probability

* `arenaObs_siteProj_pairRay`;
* ★★★ `exists_mul_le_abs_diracClickProb_sub_arenaObs` — **for every matrix `E` some carrier has a
  click probability differing from `⟨E⟩` by at least `P(siteRay j) · s² / (2 (1 + s²))`**;
  ★★ `not_exists_diracClickProb_eq_arenaObs`.

## The check: the profile `trainF`

* `abs_trainF_deriv_lift_le`, `abs_trainF_lift_le`, `trainF_weight_cutoff`;
* ★★★ `diracPointer_clickLaw` — **the package**: for every ring, `J`, `μ` and site there are a
  coupling and a readout time with the click law, a positive click probability on the detector's
  site, a click probability below `1/6` everywhere, a cut-off at occupancy `1/8`, and a distance of
  at least `P(siteRay j) / 20` from every matrix.

## Honest scope

* **Exact, and bound.** The click law is an equality. The window is evaluated where it is `0` and
  where it is `1/6`; its values for a displacement between `1/6` and `1/3`, or between `2/3` and
  `5/6`, are bounded by `1/6` and not computed. The cut-off is a sufficient condition from a bound
  on the displacement, not the exact threshold. The distance from an operator is a lower bound.
* **What the result is about.** The coupling of `Σ_*` (UA-5) drives the pointer by the expectation
  `⟨P_j⟩` of the carrier. On one trajectory the pointer turns by an amount fixed by the carrier's
  ray, `θ₂` and the time, and the readout is a threshold on that amount. A threshold on a quantity
  proportional to an expectation gives a cut-off, and a cut-off is not linear in the state. The
  theorem is about this coupling, this readout and one pointer. It says nothing about a dynamics
  in which the pointer is not driven by an expectation, and it does not show that no dynamics on
  `Σ` gives the quantum weights.
* **What it means for the rate field.** The corpus obtains the quantum weights from the rate field
  of UA-6 (Posit 1), and `epistemicMeasure_diracPointerFlow_globalBasin` of part A carries that
  field along the coupled flow. Nothing here derives the field. The reconstruction of the quantum
  statistics stays conditional on UA-6. The size of the detector's effect on that conditional
  statistic is bounded in `RecordLayer/DiracPointerBasin.lean` (#356).
* **Every matrix.** `E` is not asked to be Hermitian or positive. So the comparison covers an
  effect, an effect times an efficiency, and an effect carried back along a linear evolution of
  the carrier, averaged over `θ₂` or not.
* **The probability is that of the joint event**, ready at `0` and displayed at `T`. The
  probability conditional on a ready pointer is six times it. `arenaObs E p` is linear in `E`, so
  the comparison with operators is the same for both.
* **The instance is one coupling and one time.** `diracPointer_clickLaw` takes
  `T = 1 / (8 (‖H_D‖ + 1))` and `g = 1 / (4 T)`, a short readout: `‖H_D‖ T ≤ 1/8`. The cut-off
  theorem has the displacement bound as a hypothesis, and for a long readout time that hypothesis
  can fail. For such times only the click law and the bound `1/6` are proved.
* **The fibre law is uniform** (UA-2). The pointer being ready is an event at time `0` under that
  law (UA-4), not a different law. A non-uniform law for `θ₂` is not treated.
* **One trial, one detector.** Several detectors, one outcome per trial, repeated trials,
  no-signalling and sequential update are not treated.
* **What is assumed** (`specs/unified-record-spacetime-plan.md`, Register 1): the arena (UA-1), the
  preparation law (UA-2) and its reading as the probability of a region (UA-3), the coupling (UA-5)
  and the propagation law (UA-8) are the definitions the statements are about. The arcs, the site,
  the profile, the coupling strength and the readout time are apparatus input (UA-4). UA-6 is not
  used.

References: `specs/BACKLOG.md` #355, #354, #352, #349, #350; `specs/future-work.md`;
`specs/unified-record-spacetime-plan.md` (UO-7, UO-8, UO-9; calculation 2 of the M3 section; UD-50
to UD-54); `specs/POSITS.md` (Posit 1); `RecordLayer/DiracPointerBorn.lean`
(`ofReal_mul_volume_writeFibres_le`, `epistemicMeasure_diracPointerFlow_globalBasin`,
`epistemicMeasure_eq_map`); `RecordLayer/DiracPointerThreshold.lean`
(`pshift_notMem_displayArc`, `abs_diracPointerShift_sub_init_le`, `norm_diracPointerH_le`,
`slowFibres`, `volume_slowFibres_pos`, `writeFibres`, `volume_writeFibres_trainF_pos`, `diracReady`,
`diracDisplayed`, `diracPointerFlow_not_displayed_of_mem_slowFibres`);
`RecordLayer/DiracPointerHamiltonian.lean` (`diracPointerFlow`, `diracPointerShift`, `siteProj`,
`siteRay`, `arenaObs_siteProj_mk`); `RecordLayer/GlobalBasin.lean` (`epistemicMeasure`);
`RecordLayer/ActivatedWrite.lean` (`displayArc`);
`CV/ArenaBridge.lean` (`arenaObs`, `arenaDM_mk`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology ENNReal

namespace CSD.RecordLayer

/-! ### The expectation of an operator along a real superposition of two basis rays -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The expectation of an operator at the ray of `v` is `re ⟨v, A v⟩ / ‖v‖²`. -/
theorem arenaObs_mk_eq_inner (A : Matrix ι ι ℂ) {v : EuclideanSpace ℂ ι} (hv : v ≠ 0) :
    arenaObs A (Projectivization.mk ℂ v hv)
      = (inner ℂ v (Matrix.toEuclideanLin A v)).re / ‖v‖ ^ 2 := by
  rw [arenaObs, arenaDM_mk hv]
  have key : (dmVec v * A).trace
      = (((‖v‖ ^ 2 : ℝ) : ℂ))⁻¹ * inner ℂ v (Matrix.toEuclideanLin A v) := by
    rw [Matrix.trace, PiLp.inner_apply, Finset.mul_sum]
    simp only [Matrix.diag_apply, Matrix.mul_apply, dmVec_apply', toEuclideanLin_coord,
      Matrix.mulVec, dotProduct, RCLike.inner_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def]
    ring
  rw [key, ← Complex.ofReal_inv, RCLike.re_to_complex, Complex.re_ofReal_mul, div_eq_inv_mul]

/-- The vector `e_a + s e_b`, `s` real. -/
noncomputable def pairVec (a b : ι) (s : ℝ) : EuclideanSpace ℂ ι :=
  EuclideanSpace.single a (1 : ℂ) + (s : ℂ) • EuclideanSpace.single b (1 : ℂ)

omit [Fintype ι] in
/-- `e_a + s e_b` is not zero when `a ≠ b`. -/
theorem pairVec_ne_zero {a b : ι} (hab : a ≠ b) (s : ℝ) : pairVec a b s ≠ 0 := fun h => by
  have h' := congrArg (fun v : EuclideanSpace ℂ ι => v a) h
  simp [pairVec, hab] at h'

/-- The squared norm of `e_a + s e_b` is `1 + s²` when `a ≠ b`. -/
theorem norm_pairVec_sq {a b : ι} (hab : a ≠ b) (s : ℝ) : ‖pairVec a b s‖ ^ 2 = 1 + s ^ 2 := by
  rw [pairVec, @norm_add_sq ℂ, norm_smul, PiLp.norm_single, inner_smul_right,
    EuclideanSpace.inner_single_left]
  simp [hab]

/-- The ray of `e_a + s e_b`. -/
noncomputable def pairRay {a b : ι} (hab : a ≠ b) (s : ℝ) : GenArena ι :=
  Projectivization.mk ℂ (pairVec a b s) (pairVec_ne_zero hab s)

/-- Along the rays of `e_a + s e_b` the expectation of an operator is a quadratic in `s` over
`1 + s²`. -/
theorem arenaObs_pairRay (A : Matrix ι ι ℂ) {a b : ι} (hab : a ≠ b) (s : ℝ) :
    arenaObs A (pairRay hab s)
      = ((inner ℂ (EuclideanSpace.single a (1 : ℂ))
            (Matrix.toEuclideanLin A (EuclideanSpace.single a (1 : ℂ)))).re
          + s * ((inner ℂ (EuclideanSpace.single a (1 : ℂ))
              (Matrix.toEuclideanLin A (EuclideanSpace.single b (1 : ℂ)))).re
            + (inner ℂ (EuclideanSpace.single b (1 : ℂ))
              (Matrix.toEuclideanLin A (EuclideanSpace.single a (1 : ℂ)))).re)
          + s ^ 2 * (inner ℂ (EuclideanSpace.single b (1 : ℂ))
              (Matrix.toEuclideanLin A (EuclideanSpace.single b (1 : ℂ)))).re) / (1 + s ^ 2) := by
  rw [pairRay, arenaObs_mk_eq_inner, norm_pairVec_sq hab]
  congr 1
  simp only [pairVec, map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal, Complex.add_re, Complex.re_ofReal_mul]
  ring

/-- ★★ **Three zeros of a function on the rays forbid every operator.** If `P` vanishes at the
rays of `e_a`, `e_a + s e_b` and `e_a − s e_b`, then for every matrix `E` there is a ray at which
`P` and the expectation of `E` differ by at least `P(e_b) · s² / (2 (1 + s²))`. -/
theorem exists_mul_le_abs_sub_arenaObs (E : Matrix ι ι ℂ) {a b : ι} (hab : a ≠ b)
    (hb : EuclideanSpace.single b (1 : ℂ) ≠ 0) (P : GenArena ι → ℝ) {s : ℝ}
    (h0 : P (pairRay hab 0) = 0) (hs : P (pairRay hab s) = 0)
    (hs' : P (pairRay hab (-s)) = 0) :
    ∃ p, P (Projectivization.mk ℂ (EuclideanSpace.single b (1 : ℂ)) hb)
        * (s ^ 2 / (2 * (1 + s ^ 2))) ≤ |P p - arenaObs E p| := by
  by_contra hcon
  push Not at hcon
  set c := P (Projectivization.mk ℂ (EuclideanSpace.single b (1 : ℂ)) hb) with hc
  set ε := c * (s ^ 2 / (2 * (1 + s ^ 2))) with hε
  have hpos : (0 : ℝ) < 1 + s ^ 2 := by positivity
  have hεeq : ε * (2 * (1 + s ^ 2)) = c * s ^ 2 := by
    rw [hε]
    field_simp
  set B := (inner ℂ (EuclideanSpace.single a (1 : ℂ))
    (Matrix.toEuclideanLin E (EuclideanSpace.single a (1 : ℂ)))).re with hB
  set C := (inner ℂ (EuclideanSpace.single a (1 : ℂ))
      (Matrix.toEuclideanLin E (EuclideanSpace.single b (1 : ℂ)))).re
    + (inner ℂ (EuclideanSpace.single b (1 : ℂ))
      (Matrix.toEuclideanLin E (EuclideanSpace.single a (1 : ℂ)))).re with hC
  set A := (inner ℂ (EuclideanSpace.single b (1 : ℂ))
    (Matrix.toEuclideanLin E (EuclideanSpace.single b (1 : ℂ)))).re with hA
  have key : ∀ t : ℝ, P (pairRay hab t) = 0 →
      |B + t * C + t ^ 2 * A| < ε * (1 + t ^ 2) := by
    intro t ht
    have h := hcon (pairRay hab t)
    have htpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
    rw [ht, zero_sub, abs_neg, arenaObs_pairRay E hab t, abs_div, abs_of_pos htpos,
      div_lt_iff₀ htpos] at h
    exact h
  have k0 := abs_lt.mp (key 0 h0)
  have k1 := abs_lt.mp (key s hs)
  have k2 := abs_lt.mp (key (-s) hs')
  have kb := hcon (Projectivization.mk ℂ (EuclideanSpace.single b (1 : ℂ)) hb)
  rw [arenaObs_mk_eq_inner, PiLp.norm_single, norm_one, one_pow, div_one] at kb
  have kb' := abs_lt.mp kb
  have hmul : s ^ 2 * (c - A) ≤ s ^ 2 * ε :=
    mul_le_mul_of_nonneg_left kb'.2.le (sq_nonneg s)
  have e2 : (-s) ^ 2 = s ^ 2 := neg_sq s
  rw [e2] at k2
  simp only [zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_one] at k0
  nlinarith [k0.1, k0.2, k1.1, k1.2, k2.1, k2.2, hmul, hεeq]

end Generic

/-! ### The click event and its probability -/

section Arena

variable {M : ℕ} {f : ℝ → ℝ} (J μ g : ℝ) (j : ZMod (M + 1)) (hf : Function.Periodic f 1)

/-- **The click event** for the readout time `T`: the pointer is ready at time `0` and the readout
shows `true` at time `T`. It is fixed by the two arcs, the site, the profile, the coupling and the
readout time, and by nothing about the carrier. -/
def diracClick (hc : ContDiff ℝ ∞ f) (T : ℝ) : Set (KSigma (2 * M + 1 + 1)) :=
  {x | x ∈ diracReady M ∧ diracDisplayed M (diracPointerFlow J μ g j hf hc T x) = true}

/-- The click event is measurable. -/
theorem measurableSet_diracClick (hc : ContDiff ℝ ∞ f) (T : ℝ) :
    MeasurableSet (diracClick J μ g j hf hc T) :=
  (measurableSet_diracReady M).inter (measurable_diracPointerFlow J μ g j hf hc T
    (measurable_diracDisplayed M (measurableSet_singleton true)))

/-- **The click probability** of a carrier ray `p`: the measure of the click event under the
preparation `δ_p ⊗ Haar` of `GlobalBasin.lean`. -/
noncomputable def diracClickProb (hc : ContDiff ℝ ∞ f) (T : ℝ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) : ℝ≥0∞ :=
  epistemicMeasure (diracArenaEquiv M p) (diracClick J μ g j hf hc T)

/-- The click probability is the Haar measure of the pointer pairs that are ready and that the
displacement carries into the displayed arc. -/
theorem diracClickProb_eq_volume (hc : ContDiff ℝ ∞ f) (T : ℝ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) :
    diracClickProb J μ g j hf hc T p
      = volume {q : KTorus | q ∈ readyArc 2
          ∧ pshift (diracPointerShift J μ g j hf q.2 p T) q ∈ displayArc} := by
  rw [diracClickProb, epistemicMeasure_eq_map,
    Measure.map_apply measurable_prodMk_left (measurableSet_diracClick J μ g j hf hc T)]
  congr 1
  ext q
  show (q ∈ readyArc 2 ∧ diracDisplayed M
    (diracPointerFlow J μ g j hf hc T (diracArenaEquiv M p, q)) = true) ↔ _
  rw [diracDisplayed_eq_true_iff, diracPointerFlow_snd]
  exact Iff.rfl

/-- **The click window** of a displacement `s`: the Haar measure of the ready angles `(0, 1/6]`
that a turn by `s` carries into the displayed arc `(1/3, 5/6]`. It is a function of the two arcs
alone. -/
noncomputable def clickWindow (s : ℝ) : ℝ≥0∞ :=
  volume {θ : AddCircle (1 : ℝ) | rep θ ∈ Ioc (0 : ℝ) (shearWidth 2)
    ∧ rep (θ + (s : AddCircle (1 : ℝ))) ∈ Ioc (2 * shearWidth 2) (1 - shearWidth 2)}

/-- The window is at most the measure `1/6` of the ready arc. -/
theorem clickWindow_le (s : ℝ) : clickWindow s ≤ ENNReal.ofReal (1 / 6) := by
  refine (measure_mono (t := rep ⁻¹' Ioc (0 : ℝ) (shearWidth 2)) fun θ hθ => hθ.1).trans ?_
  rw [shearWidth_two, volume_repPreimage le_rfl (by norm_num) (by norm_num), sub_zero]

/-- Below a sixth of a turn, either way, the window is closed. -/
theorem clickWindow_eq_zero {s : ℝ} (h : |s| < 1 / 6) : clickWindow s = 0 := by
  refine measure_mono_null (t := ∅) (fun θ hθ => ?_) measure_empty
  exact pshift_notMem_displayArc (q := ((θ, 0) : KTorus)) hθ.1 h hθ.2

/-- Between a third and two thirds of a turn the window is fully open. -/
theorem clickWindow_eq_of_mem {s : ℝ} (h₁ : 1 / 3 ≤ s) (h₂ : s ≤ 2 / 3) :
    clickWindow s = ENNReal.ofReal (1 / 6) := by
  refine le_antisymm (clickWindow_le s) ?_
  have hsub : rep ⁻¹' Ioc (0 : ℝ) (shearWidth 2)
      ⊆ {θ : AddCircle (1 : ℝ) | rep θ ∈ Ioc (0 : ℝ) (shearWidth 2)
        ∧ rep (θ + (s : AddCircle (1 : ℝ))) ∈ Ioc (2 * shearWidth 2) (1 - shearWidth 2)} :=
    fun θ hθ => ⟨hθ, pshift_mem_displayArc (q := ((θ, 0) : KTorus)) hθ h₁ h₂⟩
  refine le_trans (le_of_eq ?_) (measure_mono hsub)
  rw [shearWidth_two, volume_repPreimage le_rfl (by norm_num) (by norm_num), sub_zero]

/-- ★★★ **The click law.** The click probability of a carrier is the average over the conserved
angle `θ₂` of the click window of the pointer's displacement. The Hamiltonian flow and the two
arcs fix it; no rate field enters. -/
theorem diracClickProb_eq_lintegral (hc : ContDiff ℝ ∞ f) (T : ℝ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) :
    diracClickProb J μ g j hf hc T p
      = ∫⁻ φ : AddCircle (1 : ℝ), clickWindow (diracPointerShift J μ g j hf φ p T) := by
  have hE := measurableSet_diracClick J μ g j hf hc T
  have hmk : Measurable (Prod.mk (diracArenaEquiv M p) : KTorus → KSigma (2 * M + 1 + 1)) :=
    measurable_prodMk_left
  rw [diracClickProb, epistemicMeasure_eq_map, Measure.map_apply hmk hE, Measure.volume_eq_prod,
    Measure.prod_apply_symm (hmk hE)]
  refine lintegral_congr fun φ => ?_
  rw [clickWindow]
  congr 1
  ext θ
  show (((θ, φ) : KTorus) ∈ readyArc 2 ∧ diracDisplayed M
    (diracPointerFlow J μ g j hf hc T (diracArenaEquiv M p, (θ, φ))) = true) ↔ _
  rw [diracDisplayed_eq_true_iff, diracPointerFlow_snd]
  exact Iff.rfl

/-! ### Bounds on the click probability -/

/-- The displacement in terms of the occupancy the carrier started with: over a time `t` the
pointer turns by at most `|κ| (t w + (‖H_D‖ + |g f(θ₂)|) t²)`, `w` the initial occupancy of the
detector's site. -/
theorem abs_diracPointerShift_le_weight (φ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    |diracPointerShift J μ g j hf φ p t|
      ≤ |rateAt g 1 hf φ| * (t * arenaObs (siteProj j) p
          + (‖diracHam (L := M + 1) J μ‖ + |g * hf.lift φ|) * t ^ 2) := by
  have h1 := abs_diracPointerShift_sub_init_le J μ g j hf φ p ht
  have h2 := norm_diracPointerH_le J μ g j hf φ
  have hw := arenaObs_siteProj_nonneg j p
  have h3 : |rateAt g 1 hf φ * (t * arenaObs (siteProj j) p)|
      = |rateAt g 1 hf φ| * (t * arenaObs (siteProj j) p) := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg ht hw)]
  have h4 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (sq_nonneg t))
    (abs_nonneg (rateAt g 1 hf φ))
  have h5 := abs_add_le
    (diracPointerShift J μ g j hf φ p t - rateAt g 1 hf φ * (t * arenaObs (siteProj j) p))
    (rateAt g 1 hf φ * (t * arenaObs (siteProj j) p))
  rw [sub_add_cancel] at h5
  rw [mul_add]
  linarith

/-- ★★★ **The weight cut-off.** If the bound on the displacement at occupancy `w₀` is below a
sixth of a turn on every fibre, then every carrier whose occupancy of the detector's site is at
most `w₀` has click probability `0`. The hypothesis does not ask `w₀` to be `0`. -/
theorem diracClickProb_eq_zero_of_weight_le (hc : ContDiff ℝ ∞ f) {T w₀ : ℝ} (hT : 0 ≤ T)
    (hdead : ∀ φ : AddCircle (1 : ℝ), |rateAt g 1 hf φ| * (T * w₀
      + (‖diracHam (L := M + 1) J μ‖ + |g * hf.lift φ|) * T ^ 2) < 1 / 6)
    {p : GenArena (ZMod (M + 1) × Fin 2)} (hp : arenaObs (siteProj j) p ≤ w₀) :
    diracClickProb J μ g j hf hc T p = 0 := by
  rw [diracClickProb_eq_volume]
  refine measure_mono_null (t := ∅) (fun q hq => ?_) measure_empty
  refine pshift_notMem_displayArc hq.1 (lt_of_le_of_lt ?_ (hdead q.2)) hq.2
  refine (abs_diracPointerShift_le_weight J μ g j hf q.2 p hT).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  linarith [mul_le_mul_of_nonneg_left hp hT]

/-- The click probability is at most a sixth of the measure of the fibres that are not slow. -/
theorem diracClickProb_le (hc : ContDiff ℝ ∞ f) {T : ℝ} (hT : 0 ≤ T)
    (p : GenArena (ZMod (M + 1) × Fin 2)) :
    diracClickProb J μ g j hf hc T p
      ≤ ENNReal.ofReal (1 / 6) * volume (slowFibres g hf T)ᶜ := by
  rw [diracClickProb_eq_volume]
  have hsub : {q : KTorus | q ∈ readyArc 2
        ∧ pshift (diracPointerShift J μ g j hf q.2 p T) q ∈ displayArc}
      ⊆ (rep ⁻¹' Ioc (0 : ℝ) (shearWidth 2)) ×ˢ (slowFibres g hf T)ᶜ := by
    rintro q ⟨hq, hd⟩
    refine ⟨hq, fun hslow => ?_⟩
    have h := diracPointerFlow_not_displayed_of_mem_slowFibres J μ g j hf hc hq hslow p hT le_rfl
    rw [diracDisplayed_eq_false_iff, diracPointerFlow_snd] at h
    exact h hd
  refine (measure_mono hsub).trans (le_of_eq ?_)
  rw [Measure.volume_eq_prod, Measure.prod_prod, shearWidth_two,
    volume_repPreimage le_rfl (by norm_num) (by norm_num), sub_zero]

/-- ★★ **No carrier clicks with the probability of a ready pointer.** The pointer is ready with
probability `1/6`; for every carrier, profile, coupling and readout time the click probability is
strictly below that, because the slow fibres are not null. -/
theorem diracClickProb_lt (hc : ContDiff ℝ ∞ f) {T : ℝ} (hT : 0 ≤ T)
    (p : GenArena (ZMod (M + 1) × Fin 2)) :
    diracClickProb J μ g j hf hc T p < ENNReal.ofReal (1 / 6) := by
  have hf1 : ContDiff ℝ 1 f := hc.of_le (by simp)
  have hslow := volume_slowFibres_pos g hf hf1 T
  have hcompl : volume (slowFibres g hf T)ᶜ < 1 := by
    rw [measure_compl (isOpen_slowFibres g hf hf1 T).measurableSet (measure_ne_top _ _),
      circleFibre_volume_univ]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hslow.ne'
  refine (diracClickProb_le J μ g j hf hc hT p).trans_lt ?_
  calc ENNReal.ofReal (1 / 6) * volume (slowFibres g hf T)ᶜ
      < ENNReal.ofReal (1 / 6) * 1 :=
        ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
          ENNReal.ofReal_ne_top hcompl
    _ = ENNReal.ofReal (1 / 6) := mul_one _

/-- The lower bound of `DiracPointerBorn.lean`, read as a statement about the click probability of
the carrier on the detector's site. -/
theorem ofReal_mul_volume_writeFibres_le_diracClickProb (hc : ContDiff ℝ ∞ f) {T : ℝ}
    (hT : 0 ≤ T) :
    ENNReal.ofReal (1 / 6) * volume (writeFibres M J μ g hf T)
      ≤ diracClickProb J μ g j hf hc T (siteRay j) :=
  ofReal_mul_volume_writeFibres_le J μ g j hf hc hT

/-! ### No operator gives the click probability -/

/-- The occupancy of site `j` at the ray of `e_(k,0) + s e_(j,0)`, `k ≠ j`, is `s² / (1 + s²)`. -/
theorem arenaObs_siteProj_pairRay {k : ZMod (M + 1)}
    (hkj : ((k, 0) : ZMod (M + 1) × Fin 2) ≠ (j, 0)) (s : ℝ) :
    arenaObs (siteProj j) (pairRay hkj s) = s ^ 2 / (1 + s ^ 2) := by
  have hk : k ≠ j := fun h => hkj (by rw [h])
  rw [pairRay, arenaObs_siteProj_mk, norm_pairVec_sq hkj]
  congr 1
  simp [siteWeight, pairVec, hk.symm]

/-- ★★★ **The click probability is not the expectation of any operator.** On a ring with a second
site, suppose every carrier whose occupancy of the detector's site is at most `s² / (1 + s²)` has
click probability `0`. Then for every matrix `E` there is a carrier at which the click probability
and the expectation of `E` differ by at least `P(siteRay j) · s² / (2 (1 + s²))`: half the click
probability of the carrier on the site, times that occupancy. -/
theorem exists_mul_le_abs_diracClickProb_sub_arenaObs (hc : ContDiff ℝ ∞ f) {T : ℝ}
    {k : ZMod (M + 1)} (hk : k ≠ j) {s : ℝ}
    (hzero : ∀ p : GenArena (ZMod (M + 1) × Fin 2),
      arenaObs (siteProj j) p ≤ s ^ 2 / (1 + s ^ 2) → diracClickProb J μ g j hf hc T p = 0)
    (E : Matrix (ZMod (M + 1) × Fin 2) (ZMod (M + 1) × Fin 2) ℂ) :
    ∃ p, (diracClickProb J μ g j hf hc T (siteRay j)).toReal * (s ^ 2 / (2 * (1 + s ^ 2)))
      ≤ |(diracClickProb J μ g j hf hc T p).toReal - arenaObs E p| := by
  have hkj : ((k, 0) : ZMod (M + 1) × Fin 2) ≠ (j, 0) := fun h => hk (congrArg Prod.fst h)
  have z : ∀ t : ℝ, t ^ 2 = s ^ 2
      → (diracClickProb J μ g j hf hc T (pairRay hkj t)).toReal = 0 := by
    intro t ht
    rw [hzero _ (by rw [arenaObs_siteProj_pairRay, ht]), ENNReal.toReal_zero]
  have z0 : (diracClickProb J μ g j hf hc T (pairRay hkj 0)).toReal = 0 := by
    rw [hzero _ (by rw [arenaObs_siteProj_pairRay, zero_pow two_ne_zero, zero_div]; positivity),
      ENNReal.toReal_zero]
  exact exists_mul_le_abs_sub_arenaObs E hkj _
    (fun p => (diracClickProb J μ g j hf hc T p).toReal) z0 (z s rfl) (z (-s) (neg_sq s))

/-- ★★ **No operator at all**: with a cut-off at a positive occupancy and a carrier that clicks
with positive probability, the click probability is not `p ↦ ⟨E⟩_p` for any matrix `E`. -/
theorem not_exists_diracClickProb_eq_arenaObs (hc : ContDiff ℝ ∞ f) {T : ℝ} (hT : 0 ≤ T)
    {k : ZMod (M + 1)} (hk : k ≠ j) {s : ℝ} (hs : s ≠ 0)
    (hzero : ∀ p : GenArena (ZMod (M + 1) × Fin 2),
      arenaObs (siteProj j) p ≤ s ^ 2 / (1 + s ^ 2) → diracClickProb J μ g j hf hc T p = 0)
    (hpos : 0 < diracClickProb J μ g j hf hc T (siteRay j)) :
    ¬ ∃ E : Matrix (ZMod (M + 1) × Fin 2) (ZMod (M + 1) × Fin 2) ℂ,
      ∀ p, (diracClickProb J μ g j hf hc T p).toReal = arenaObs E p := by
  rintro ⟨E, hE⟩
  obtain ⟨p, hp⟩ := exists_mul_le_abs_diracClickProb_sub_arenaObs J μ g j hf hc hk hzero E
  rw [hE p, sub_self, abs_zero] at hp
  have hc' : 0 < (diracClickProb J μ g j hf hc T (siteRay j)).toReal :=
    ENNReal.toReal_pos hpos.ne'
      ((diracClickProb_lt J μ g j hf hc hT (siteRay j)).trans ENNReal.ofReal_lt_top).ne
  have hs2 : 0 < s ^ 2 / (2 * (1 + s ^ 2)) := by positivity
  nlinarith [mul_pos hc' hs2]

end Arena

/-! ### The check: the profile `trainF` -/

section Check

variable (M : ℕ) (J μ : ℝ)

/-- The derivative of `trainF` is at most `1` in absolute value. -/
theorem abs_trainF_deriv_lift_le (φ : AddCircle (1 : ℝ)) :
    |trainF_periodic.deriv_periodic.lift φ| ≤ 1 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective φ
  show |trainF_periodic.deriv_periodic.lift ((x : ℝ) : AddCircle (1 : ℝ))| ≤ 1
  rw [Function.Periodic.lift_coe, (hasDerivAt_trainF x).deriv, abs_neg]
  exact Real.abs_cos_le_one _

/-- `trainF` is at most `1/6` in absolute value (it is at most `1 / (2π)`). -/
theorem abs_trainF_lift_le (φ : AddCircle (1 : ℝ)) : |trainF_periodic.lift φ| ≤ 1 / 6 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective φ
  show |trainF_periodic.lift ((x : ℝ) : AddCircle (1 : ℝ))| ≤ 1 / 6
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [Function.Periodic.lift_coe, trainF, abs_div, abs_neg, abs_of_pos hπ, div_le_iff₀ hπ]
  linarith [Real.abs_sin_le_one (2 * Real.pi * x), Real.pi_gt_three]

/-- **The cut-off for the profile `trainF`** at coupling `g = 1/(4T)`: for a readout time with
`‖H_D‖ T ≤ 1/8`, the bound on the displacement at occupancy `1/8` is below a sixth of a turn on
every fibre. -/
theorem trainF_weight_cutoff {T : ℝ} (hT : 0 < T)
    (hJT : ‖diracHam (L := M + 1) J μ‖ * T ≤ 1 / 8) (φ : AddCircle (1 : ℝ)) :
    |rateAt (1 / (4 * T)) 1 trainF_periodic φ| * (T * (1 / 8)
      + (‖diracHam (L := M + 1) J μ‖ + |1 / (4 * T) * trainF_periodic.lift φ|) * T ^ 2)
      < 1 / 6 := by
  have hn : 0 ≤ ‖diracHam (L := M + 1) J μ‖ := norm_nonneg _
  set h := ‖diracHam (L := M + 1) J μ‖ with hh
  have hg : (0 : ℝ) < 1 / (4 * T) := by positivity
  have hκ : |rateAt (1 / (4 * T)) 1 trainF_periodic φ| ≤ 1 / (2 * T) := by
    rw [rateAt_one, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * (1 / (4 * T)))]
    calc 2 * (1 / (4 * T)) * |trainF_periodic.deriv_periodic.lift φ|
        ≤ 2 * (1 / (4 * T)) * 1 :=
          mul_le_mul_of_nonneg_left (abs_trainF_deriv_lift_le φ) (by positivity)
      _ = 1 / (2 * T) := by
          field_simp
          norm_num
  have hgf : |1 / (4 * T) * trainF_periodic.lift φ| ≤ 1 / (24 * T) := by
    rw [abs_mul, abs_of_pos hg]
    calc 1 / (4 * T) * |trainF_periodic.lift φ|
        ≤ 1 / (4 * T) * (1 / 6) := mul_le_mul_of_nonneg_left (abs_trainF_lift_le φ) hg.le
      _ = 1 / (24 * T) := by
          field_simp
          norm_num
  have e1 : (h + |1 / (4 * T) * trainF_periodic.lift φ|) * T ^ 2
      ≤ (h + 1 / (24 * T)) * T ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg T)
  have e2 : (h + 1 / (24 * T)) * T ^ 2 = h * T * T + T / 24 := by
    field_simp
  have e3 : h * T * T ≤ 1 / 8 * T := mul_le_mul_of_nonneg_right hJT hT.le
  have hin : 0 ≤ T * (1 / 8) + (h + |1 / (4 * T) * trainF_periodic.lift φ|) * T ^ 2 :=
    add_nonneg (by positivity) (mul_nonneg (add_nonneg hn (abs_nonneg _)) (sq_nonneg T))
  calc |rateAt (1 / (4 * T)) 1 trainF_periodic φ| * (T * (1 / 8)
        + (h + |1 / (4 * T) * trainF_periodic.lift φ|) * T ^ 2)
      ≤ 1 / (2 * T) * (T * (1 / 8)
        + (h + |1 / (4 * T) * trainF_periodic.lift φ|) * T ^ 2) :=
        mul_le_mul_of_nonneg_right hκ hin
    _ ≤ 1 / (2 * T) * (T * (7 / 24)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 7 / 48 := by
        field_simp
        norm_num
    _ < 1 / 6 := by norm_num

/-- ★★★ **The click law of the pointer of `Σ_*`, the package.** For every ring, every `J`, `μ`
and every site there
are a coupling and a readout time at which, for the profile `trainF`:

* the click probability of every carrier is the `θ₂`-average of the click window of the
  displacement — the Hamiltonian flow and the two arcs determine it, with no rate field;
* the carrier on the detector's site clicks with positive probability;
* every carrier clicks with probability strictly below that of a ready pointer;
* every carrier whose occupancy of the detector's site is at most `1/8` has click probability `0`;
* on a ring with a second site, for every matrix `E` there is a carrier at which the click
  probability and the expectation of `E` differ by at least a twentieth of the click probability of
  the carrier on the site.

The dynamics determines a click probability, and it is not the expectation of an operator.
This is the statement gate A of the programme asks for. It uses UA-1, UA-2, UA-3, UA-4, UA-5
and UA-8, and not UA-6. -/
theorem diracPointer_clickLaw (j : ZMod (M + 1)) :
    ∃ g T : ℝ, 0 < T
      ∧ (∀ p, diracClickProb J μ g j trainF_periodic contDiff_trainF T p
          = ∫⁻ φ : AddCircle (1 : ℝ),
              clickWindow (diracPointerShift J μ g j trainF_periodic φ p T))
      ∧ 0 < diracClickProb J μ g j trainF_periodic contDiff_trainF T (siteRay j)
      ∧ (∀ p, diracClickProb J μ g j trainF_periodic contDiff_trainF T p
          < ENNReal.ofReal (1 / 6))
      ∧ (∀ p, arenaObs (siteProj j) p ≤ 1 / 8
          → diracClickProb J μ g j trainF_periodic contDiff_trainF T p = 0)
      ∧ ∀ k, k ≠ j → ∀ E : Matrix (ZMod (M + 1) × Fin 2) (ZMod (M + 1) × Fin 2) ℂ,
          ∃ p, (diracClickProb J μ g j trainF_periodic contDiff_trainF T (siteRay j)).toReal / 20
            ≤ |(diracClickProb J μ g j trainF_periodic contDiff_trainF T p).toReal
                - arenaObs E p| := by
  have hn : 0 ≤ ‖diracHam (L := M + 1) J μ‖ := norm_nonneg _
  set h := ‖diracHam (L := M + 1) J μ‖ with hh
  have hT : (0 : ℝ) < 1 / (8 * (h + 1)) := by positivity
  have hJT : h * (1 / (8 * (h + 1))) ≤ 1 / 8 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  have hzero : ∀ p : GenArena (ZMod (M + 1) × Fin 2), arenaObs (siteProj j) p ≤ 1 / 8
      → diracClickProb J μ (1 / (4 * (1 / (8 * (h + 1))))) j trainF_periodic contDiff_trainF
          (1 / (8 * (h + 1))) p = 0 := fun p hp =>
    diracClickProb_eq_zero_of_weight_le J μ _ j trainF_periodic contDiff_trainF hT.le
      (trainF_weight_cutoff M J μ hT hJT) hp
  refine ⟨1 / (4 * (1 / (8 * (h + 1)))), 1 / (8 * (h + 1)), hT,
    fun p => diracClickProb_eq_lintegral J μ _ j trainF_periodic contDiff_trainF _ p,
    lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
        (volume_writeFibres_trainF_pos M J μ hT (hJT.trans (by norm_num))).ne')
      (ofReal_mul_volume_writeFibres_le_diracClickProb J μ _ j trainF_periodic contDiff_trainF
        hT.le),
    fun p => diracClickProb_lt J μ _ j trainF_periodic contDiff_trainF hT.le p,
    hzero, fun k hk E => ?_⟩
  obtain ⟨p, hp⟩ := exists_mul_le_abs_diracClickProb_sub_arenaObs J μ _ j trainF_periodic
    contDiff_trainF (T := 1 / (8 * (h + 1))) hk (s := 1 / 3)
    (fun p hp => hzero p (hp.trans (by norm_num))) E
  rw [show ((1 : ℝ) / 3) ^ 2 / (2 * (1 + (1 / 3) ^ 2)) = 1 / 20 by norm_num,
    mul_one_div] at hp
  exact ⟨p, hp⟩

end Check

end CSD.RecordLayer

end
