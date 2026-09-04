/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QuantumEraser
public import CsdLean4.RecordLayer.Measurement
public import CsdLean4.RecordLayer.DegenerateLuders

/-!
# Empirical/CSD: the quantum eraser — the conditioned fringe as an ontic typicality volume

**Category:** CSD bridge (the ontic reading of `Empirical/QM/QuantumEraser.lean`), built on the
**record layer**, like `HongOuMandelVolume.lean` and unlike every DH-route `…Volume` twin.

## Why the record layer

The eraser's defining empirical signature is the **dark fringe**: conditioned on the erasing
marker outcome, the screen probability at phase `π` is **exactly `0`** (`eraser_fringe_dark`).
The Duistermaat–Heckman volume route (`fs_born_volume_ratio_N`) carries `hpos` — *strictly
positive* Born weights — and it is load-bearing (`replaceMap_det`: a zero weight makes the
vertex-replacement map singular). So the *original* DH lemmas cannot state the eraser's central
zero; the record layer can: `volume_cdfCell` has no positivity hypothesis — a zero rate is a
zero-width cell. ⚠️ *Correction 2026-08-02 (external review):* the hpos-free `_uncond` engine
(`fs_born_volume_ratio_N_uncond`, landed 2026-06-11) does state zero weights — the record
route here is a **choice** (with its own foundational motivation), not a necessity. See
`HongOuMandelVolume.lean` for the corrected architectural discussion.

## What is derived and what is transported

The **conditioned screen state** `eraserOut φ c ∝ (1 + c·e^{−iφ}, 1 − c·e^{−iφ})/2` is tied to
the QM module two ways, so its rates are *derived*, not asserted:

* `eraserOut_eq_jointAmplitude` — its components are the QM module's joint amplitudes
  `⟨φ_a ⊗ c|Φ⟩/2`, cancellation included.
* `eraserOut_rate_conditional` — its Born rates equal `P(a,c)/(P(+,c) + P(−,c))`: the textbook
  conditional probability, joint over marker marginal, both sides QM-module quantities.

The conditioning bookkeeping itself (Bayes on the marker record) is classical probability applied
to the QM joint — transported, not re-derived. What CSD adds is the **ontic realisation of the
conditioned statistics, zeros included**.

## What this file proves

* ★ `eraser_fringe_typicality` — the full-visibility conditioned fringe `(1 + c·cos φ)/2` is a
  fibre-typicality volume for **every** phase — including the boundary values the DH route
  excludes.
* ★ `eraser_dark_typicality_zero` — at `φ = π` the dark-fringe cell is **exactly null**: no
  microstate of `Σ` produces a dark-port detection. The dark fringe is an ontic impossibility,
  not a statistical cancellation.
* ★ `eraser_dark_record_null` / `eraser_dark_measurement_zero` — the same at the level of the
  P5 record event and of the `Measurement` interface.
* `eraser_dark_bright_one` — the complementary cell carries typicality `1`: genuine
  redistribution, not a normalisation artefact.
* ★ `eraser_dark_basin_null` / `eraser_bright_basin_one` — the same zero **at the v1.0
  context-fixed basin layer**: at `φ = π` the conditioned state *is* the vertex `[e₁]`
  (`mk_eraserOut_pi`), and the dark outcome's global basin has epistemic measure `0` for that
  preparation — by `globalBasin_prob` + `momentMap_vertex`, the same lemmas that drive
  repeatability in `SequentialMeasurement.lean`.

The contrast with the **flat unconditioned marginal** (`eraser_no_interference`, QM side: `1/2`
independent of `φ`) is the eraser: interference lives *only* in the marker-conditioned
subensembles. `eraser_marker_marginal` (each marker outcome has probability `1/2`) is what makes
the conditioning well-posed at every phase — the eraser never conditions on a null outcome, so
the `hpos`-style caveat of `SequentialMeasurement.lean` is discharged here, not dodged.

## ⚠️ Honest scope

The marker measurement is not constructed as a dynamical process here: the calibrated-swap
witness measures in the computational basis of a single `KSigma N`, while the eraser's first
measurement is in a *rotated* basis on a *composite*. A fully dynamical eraser — marker
measurement as swap-witness dynamics on the two-qubit arena, screen read via a rotated context
field — needs the unitary-covariance extension and is recorded in `specs/BACKLOG.md`. This twin
realises the conditioned *statistics* ontically, and *Corrected 2026-08-04 (codebase audit).* the conditioning
**process** is now realised too: `Empirical/CSD/EraserDynamics.lean` (2026-08-03) proves the
dynamical post-states' screen amplitudes are exactly `√2 ·` **this module's** `eraserOut`
(`erased_amp`), so every statistic certified here is a statement about the measurement
dynamics' own output; `sequential_no_revival` (`EraserSequential.lean`) adds irreversibility.

**Experimental verification:** Kim et al. 2000 (delayed-choice); Scully–Drühl 1982 — via the QM
module, whose delayed-choice remark applies verbatim: the statistics are the same whether the
erasure choice precedes or follows the screen detection.

## References

`Empirical/QM/QuantumEraser.lean` (`jointAmp_eq`, `eraser_joint`, `eraser_no_interference`,
`eraser_fringe_dark`); `Empirical/CSD/HongOuMandelVolume.lean` (the record-route template and
the `hpos` discussion); `SigmaLayer/BornFibrePartition.lean` (`cdfCell`, `bornRate`);
`SigmaLayer/DeIsolationFlow.lean` (`fibreTypicality_bornCell`); `SigmaLayer/FibreRecord.lean`
(`fibreTypicality_bornRecord`); `SigmaLayer/Measurement.lean` (`bornMeasurement_prob`);
`SigmaLayer/GlobalBasin.lean` (`globalBasin_prob`, `momentContext`);
`SigmaLayer/DegenerateLuders.lean` (`vertexPoint`, `momentMap_vertex`);
`specs/BACKLOG.md`; `specs/record-layer-plan.md`.
-/

@[expose] public section

open MeasureTheory Set
open CSD.RecordLayer

namespace CSD.Empirical.CSDBridge.QuantumEraserVolume

open CSD.Empirical.QM.QuantumEraser

/-! ### The conditioned screen state -/

/-- The phase factor `e^{−iφ} = cos φ − i·sin φ`, as it appears in the QM module's joint
amplitude. -/
noncomputable def phaseC (φ : ℝ) : ℂ :=
  (Real.cos φ : ℂ) - (Real.sin φ : ℂ) * Complex.I

/-- **The marker-conditioned screen state**: given erasing-basis marker outcome `c = ±1`, the
system's screen-basis amplitudes are `(1 ± c·e^{−iφ})/2` — the QM module's joint amplitudes,
renormalised by the marker marginal `1/2`. Index `0` is the screen outcome `a = +1`, index `1`
is `a = −1`. -/
noncomputable def eraserOut (φ c : ℝ) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![(1 + (c : ℂ) * phaseC φ) / 2, (1 - (c : ℂ) * phaseC φ) / 2]

@[simp] lemma eraserOut_zero (φ c : ℝ) :
    eraserOut φ c 0 = (1 + (c : ℂ) * phaseC φ) / 2 := by
  simp [eraserOut, WithLp.ofLp_toLp]

@[simp] lemma eraserOut_one (φ c : ℝ) :
    eraserOut φ c 1 = (1 - (c : ℂ) * phaseC φ) / 2 := by
  simp [eraserOut, WithLp.ofLp_toLp]

/-- **The conditioned amplitudes are the QM module's joint amplitudes** `⟨φ_a ⊗ c|Φ⟩/2` — the
cancellation at the dark fringe happens in `jointAmplitude`, not in this file. -/
theorem eraserOut_eq_jointAmplitude (φ c : ℝ) :
    eraserOut φ c 0 = jointAmplitude (sysBra φ 1) (markBra c) bellVec / 2 ∧
    eraserOut φ c 1 = jointAmplitude (sysBra φ (-1)) (markBra c) bellVec / 2 := by
  rw [eraserOut_zero, eraserOut_one, jointAmp_eq, jointAmp_eq]
  constructor <;> · simp only [phaseC]; push_cast; ring

/-! ### Rates: the conditional Born probabilities, with their normalisation derived -/

/-- The marker marginal: each erasing-basis marker outcome has probability `1/2`, at **every**
phase — so the eraser's conditioning is well-posed everywhere (it never conditions on a null
outcome). -/
theorem eraser_marker_marginal (φ : ℝ) {c : ℝ} (hc : c = 1 ∨ c = -1) :
    bornP φ 1 c + bornP φ (-1) c = 1 / 2 := by
  rw [eraser_joint φ (Or.inl rfl) hc, eraser_joint φ (Or.inr rfl) hc]
  ring

lemma normSq_eraserOut_zero (φ : ℝ) {c : ℝ} (hc : c = 1 ∨ c = -1) :
    ‖eraserOut φ c 0‖ ^ 2 = (1 + c * Real.cos φ) / 2 := by
  have hw : eraserOut φ c 0
      = (↑((1 + c * Real.cos φ) / 2) : ℂ) + (↑(-(c * Real.sin φ) / 2) : ℂ) * Complex.I := by
    rw [eraserOut_zero]
    simp only [phaseC]
    push_cast
    ring
  rw [hw, Complex.sq_norm, Complex.normSq_add_mul_I]
  rcases hc with hc | hc <;> subst hc <;>
    linear_combination (1 / 4 : ℝ) * Real.sin_sq_add_cos_sq φ

lemma normSq_eraserOut_one (φ : ℝ) {c : ℝ} (hc : c = 1 ∨ c = -1) :
    ‖eraserOut φ c 1‖ ^ 2 = (1 - c * Real.cos φ) / 2 := by
  have hw : eraserOut φ c 1
      = (↑((1 - c * Real.cos φ) / 2) : ℂ) + (↑(c * Real.sin φ / 2) : ℂ) * Complex.I := by
    rw [eraserOut_one]
    simp only [phaseC]
    push_cast
    ring
  rw [hw, Complex.sq_norm, Complex.normSq_add_mul_I]
  rcases hc with hc | hc <;> subst hc <;>
    linear_combination (1 / 4 : ℝ) * Real.sin_sq_add_cos_sq φ

/-- **The conditioned rates are joint over marginal** — textbook Bayes on the marker record,
with both sides QM-module quantities. This pins the `/2` normalisation of `eraserOut` to
`eraser_marker_marginal` rather than asserting it. -/
theorem eraserOut_rate_conditional (φ : ℝ) {c : ℝ} (hc : c = 1 ∨ c = -1) :
    ‖eraserOut φ c 0‖ ^ 2 = bornP φ 1 c / (bornP φ 1 c + bornP φ (-1) c) ∧
    ‖eraserOut φ c 1‖ ^ 2 = bornP φ (-1) c / (bornP φ 1 c + bornP φ (-1) c) := by
  rw [normSq_eraserOut_zero φ hc, normSq_eraserOut_one φ hc, eraser_marker_marginal φ hc,
    eraser_joint φ (Or.inl rfl) hc, eraser_joint φ (Or.inr rfl) hc]
  constructor <;> ring

lemma eraserOut_normsq (φ : ℝ) {c : ℝ} (hc : c = 1 ∨ c = -1) :
    ∑ i, ‖eraserOut φ c i‖ ^ 2 = 1 := by
  rw [Fin.sum_univ_two, normSq_eraserOut_zero φ hc, normSq_eraserOut_one φ hc]
  ring

theorem eraserOut_norm (φ : ℝ) {c : ℝ} (hc : c = 1 ∨ c = -1) : ‖eraserOut φ c‖ = 1 := by
  rw [EuclideanSpace.norm_eq, eraserOut_normsq φ hc, Real.sqrt_one]

/-! ### The conditioned fringe as a typicality volume — every phase, boundary included -/

/-- **★ The full-visibility conditioned fringe is an ontic typicality volume.** For every phase
`φ` and marker outcome `c`, the screen-outcome-`+` cell has fibre typicality `(1 + c·cos φ)/2` —
ranging over the **full** interval `[0, 1]`, including the boundary values the DH route's `hpos`
excludes. -/
theorem eraser_fringe_typicality (φ : ℝ) {c : ℝ} (hc : c = 1 ∨ c = -1) :
    fibreTypicality (cdfCell (bornRate (eraserOut φ c)) 0)
      = ENNReal.ofReal ((1 + c * Real.cos φ) / 2) := by
  rw [fibreTypicality_bornCell (eraserOut φ c) (eraserOut_norm φ hc) 0,
    normSq_eraserOut_zero φ hc]

/-! ### The dark fringe: `φ = π`, marker `+` — an exact ontic zero -/

-- Not `@[simp]`: `eraserOut_zero` rewrites the head first, so the specialisation at `φ = π` could
-- never fire (`simpNF`). Both are used by name below.
lemma eraserOut_pi_zero : eraserOut Real.pi 1 0 = 0 := by
  rw [eraserOut_zero]
  simp [phaseC, Real.cos_pi, Real.sin_pi]

lemma eraserOut_pi_one : eraserOut Real.pi 1 1 = 1 := by
  rw [eraserOut_one]
  simp [phaseC, Real.cos_pi, Real.sin_pi]

/-- **★ The dark fringe is an ontic impossibility.** At phase `π`, conditioned on the erasing
marker outcome `+`, the dark screen outcome's Born cell has fibre typicality **exactly zero**:
the set of microstates that would produce a dark-port detection is null. Nothing is cancelled
across runs — there is nothing in `Σ` to cancel. -/
theorem eraser_dark_typicality_zero :
    fibreTypicality (cdfCell (bornRate (eraserOut Real.pi 1)) 0) = 0 := by
  rw [fibreTypicality_bornCell (eraserOut Real.pi 1) (eraserOut_norm Real.pi (Or.inl rfl)) 0,
    eraserOut_pi_zero]
  simp

/-- **★ The same at the level of the record**: the P5 record event "this context recorded the
dark outcome" is a null subset of `Σ` — no record of a dark-fringe detection is ever laid
down. -/
theorem eraser_dark_record_null (t : CSD.SigmaLayer.OnticTime) :
    fibreTypicality
        ((fibreRecordSemantics 2).event ⟨bornContext (eraserOut Real.pi 1), (0 : Fin 2), t⟩)
      = 0 := by
  rw [fibreTypicality_bornRecord (eraserOut Real.pi 1) (eraserOut_norm Real.pi (Or.inl rfl)) 0 t,
    eraserOut_pi_zero]
  simp

/-- **★ And as a measurement**: the dark outcome of the conditioned screen measurement has
probability `0` — for a.e. microstate the deterministic context-plus-microstate map lands in the
bright basin. -/
theorem eraser_dark_measurement_zero (t : CSD.SigmaLayer.OnticTime) :
    (Measurement.bornMeasurement (eraserOut Real.pi 1) t).prob 0 = 0 := by
  rw [Measurement.bornMeasurement_prob (eraserOut Real.pi 1)
    (eraserOut_norm Real.pi (Or.inl rfl)) 0 t, eraserOut_pi_zero]
  simp

/-- The bright cell carries typicality `1` — the dark weight is genuinely redistributed, not
renormalised away. -/
theorem eraser_dark_bright_one :
    fibreTypicality (cdfCell (bornRate (eraserOut Real.pi 1)) 1) = 1 := by
  rw [fibreTypicality_bornCell (eraserOut Real.pi 1) (eraserOut_norm Real.pi (Or.inl rfl)) 1,
    eraserOut_pi_one]
  simp

/-! ### The dark fringe at the v1.0 basin layer -/

lemma eraserOut_pi_eq_single :
    eraserOut Real.pi 1 = EuclideanSpace.single (1 : Fin 2) (1 : ℂ) := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [phaseC, Real.cos_pi, Real.sin_pi]

lemma eraserOut_pi_ne_zero : eraserOut Real.pi 1 ≠ 0 := by
  intro h
  have h1 : eraserOut Real.pi 1 1 = 0 := by rw [h]; rfl
  rw [eraserOut_pi_one] at h1
  exact one_ne_zero h1

/-- At the dark point the conditioned state **is** the computational vertex `[e₁]` — the same
collapsed preparation that drives repeatability in `SequentialMeasurement.lean`. -/
lemma mk_eraserOut_pi :
    Projectivization.mk ℂ (eraserOut Real.pi 1) eraserOut_pi_ne_zero = vertexPoint 1 := by
  unfold vertexPoint
  rw [Projectivization.mk_eq_mk_iff]
  exact ⟨1, by rw [one_smul]; exact eraserOut_pi_eq_single.symm⟩

/-- **★ The dark fringe at the context-fixed basin layer.** For the post-erasure preparation at
phase `π`, the dark outcome's global basin — a set fixed by the apparatus context alone — has
epistemic measure **zero**. The ontic trajectory cannot enter the dark basin's fibre arc, because
the arc has width `0` at that base point. -/
theorem eraser_dark_basin_null :
    epistemicMeasure (Projectivization.mk ℂ (eraserOut Real.pi 1) eraserOut_pi_ne_zero)
      (globalBasin (momentContext 2) 0) = 0 := by
  rw [mk_eraserOut_pi, globalBasin_prob, momentContext_rate, momentMap_vertex]
  simp

/-- The companion certainty: the bright basin has epistemic measure `1` for the same
preparation. -/
theorem eraser_bright_basin_one :
    epistemicMeasure (Projectivization.mk ℂ (eraserOut Real.pi 1) eraserOut_pi_ne_zero)
      (globalBasin (momentContext 2) 1) = 1 := by
  rw [mk_eraserOut_pi, globalBasin_prob, momentContext_rate, momentMap_vertex]
  simp

end CSD.Empirical.CSDBridge.QuantumEraserVolume
