/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.MeasureTheory.InvariantTwist
public import CsdLean4.RecordLayer.DiracPointerRecord
public import CsdLean4.RecordLayer.GlobalBasin

/-!
# Statistics of the pointer at one time: what the preparation law cannot see

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 7-SigmaLayer (the record layer). BACKLOG #354 — milestone **M3, part A** of the
author's programme "From `Σ` to physical spacetime" (2026-11-09). M3 asks whether the Hamiltonian
and the apparatus fix the measures of the outcome regions without a stipulated rate field. This
module settles the first half of the question, and the answer is an obstruction.

The preparation law of the record layer is `epistemicMeasure x₀ = δ_{x₀} ⊗ Haar`: the carrier's ray
`x₀` is known and the fibre point is uniform on `T²` (`RecordLayer/GlobalBasin.lean`). The joint
flow `diracPointerFlow` of `Σ_* = ℂℙ^{2M+1} × T²` (#349) turns the pointer angle `θ₁` by a
displacement that depends on the carrier, on `θ₂` and on the time. Over a fixed carrier ray that is
a turn of `θ₁` by an amount depending on `θ₂` alone, and such a map preserves Haar measure. The
consequence is exact: the law of the arena point at time `t` is the law it would have *if the
pointer had not moved at all*. Every statistic read at one time under the preparation law is blind
to the pointer's displacement.

Two things follow. A region of the fibre fixed by the apparatus has, at every time, a probability
equal to its Haar measure, the same for every carrier; so it cannot track the occupancy
`⟨ψ, P_j ψ⟩` of the detector's site, and the error is at least `1/2` for some carrier. And a region
that does depend on the base point, such as the `globalBasin` of a rate field, has at time `t` the
probability of the rate field at the coupled carrier, averaged over `θ₂`: the dependence on the
state is the dependence the rate field was given, and the pointer's motion adds nothing to it.

The statement is about one time. An event that refers to two times, *ready at `0` and displayed at
`T`*, does see the displacement, and the last section proves it. That event is the subject of the
second half of M3, `RecordLayer/DiracPointerClick.lean` (#355).

## The fibre over a carrier ray

* `diracPointerFlow_fst`, `diracPointerFlow_fst_congr` — the carrier's ray at time `t` depends on
  the fibre point through `θ₂` alone;
* ★★ `measurePreserving_diracPointerFlow_fibre` — **over a fixed carrier ray the pointer pair moves
  by a map that preserves `Haar ⊗ ν`**, for any law `ν` of `θ₂`.

## The pointer held

* `diracPointerHeld` — the carrier moved as in the flow, the fibre point left where it was;
  `diracPointerHeld_fst`, `diracPointerHeld_snd`, `measurable_diracPointerHeld`,
  `diracPointerFlow_eq_held`.

## The law at one time

* `epistemicMeasure_eq_map`;
* ★★★ `map_diracPointerFlow_dirac_prod` — **the law at time `t` is the law with the pointer
  held**, for the preparation `δ_{x₀} ⊗ (Haar ⊗ ν)`; `map_diracPointerFlow_epistemicMeasure`,
  `epistemicMeasure_preimage_diracPointerFlow` — the same for `epistemicMeasure`;
* ★★ `map_snd_diracPointerFlow_dirac_prod`, `map_snd_diracPointerFlow_epistemicMeasure` — the
  fibre point at time `t` has the law it started with.

## Regions of the fibre

* ★★★ `dirac_prod_diracPointerFlow_fibreRegion`, `epistemicMeasure_diracPointerFlow_fibreRegion` —
  **the probability that the fibre point is in a region `F` at time `t` is the measure of `F`**,
  for every carrier, time, coupling and profile;
* `volume_displayArc`; ★★ `epistemicMeasure_diracDisplayed` — **the readout shows `true` with
  probability `1/2`**; `epistemicMeasure_diracReady` — the pointer is in the ready arc with
  probability `1/6`;
* ★★★ `exists_half_le_abs_fibreRegion_sub_siteWeight` — **no region of the fibre has a probability
  within `1/2` of the occupancy of the detector's site for every carrier.**

## Regions that depend on the base point

* ★★ `epistemicMeasure_diracPointerFlow_globalBasin` — **the basin of a rate field `c` has at time
  `t` the probability `∫ c.rate (the coupled carrier at time t) i dθ₂`.** Conditional on the rate
  field (UA-6): the statement does not derive one.

## The check: two times

* `ready_diracPointerHeld_displayed_eq_empty` — with the pointer held, *ready at `0` and displayed
  at `T`* never happens;
* ★★ `ofReal_mul_volume_writeFibres_le`, `epistemicMeasure_ready_displayed_pos`,
  `exists_epistemicMeasure_ready_displayed_pos` — **under the flow it has probability at least
  `(1/6) · vol(writeFibres)` for the carrier on the detector's site**, positive for the profile
  `trainF`.

## Honest scope

* **Exact.** Every statement is an equality of measures or of probabilities. No error term enters.
* **What the obstruction says, and under which law.** The preparation law is the one of UA-2: the
  carrier's ray fixed, the fibre uniform. The pointer angle `θ₁` is uniform under it, at time `0`
  and (by the theorem) at every time. The general form allows any law `ν` for `θ₂`; the law of `θ₁`
  must be Haar. Under that law the outcome statistic of an apparatus-fixed region of the fibre is a
  constant, so the bound asked by M3, `|P(i | ψ, M) − ⟨ψ, P_i ψ⟩| ≤ ε_meas`, holds for all carriers
  only with `ε_meas ≥ 1/2`.
* **What it does not say.** A pointer prepared in the ready arc is the same law conditioned on
  `diracReady`, an event at time `0`. *Ready at `0` and displayed at `T`* is an event about two
  times; the theorem does not apply to it and the last section shows it is false there. Whether
  that event's probability follows the occupancy of the detector's site is not decided here;
  `RecordLayer/DiracPointerClick.lean` (#355) decides it, and it does not.
* **Two features of the flow are used:** `θ₂` is conserved, and the carrier's evolution does not
  depend on `θ₁`. A dynamics in which the pointer angle acts back on the carrier is not covered.
* **The basin statement is conditional.** `epistemicMeasure_diracPointerFlow_globalBasin` holds for
  every rate field. With the moment-map field it returns the occupancies of the coupled carrier
  averaged over `θ₂`, and that is the rate field's own content (UA-6, Posit 1) carried along the
  carrier's evolution. It is recorded as conditional on UA-6 and is not a derivation of outcome
  statistics from the dynamics. The carrier in it is the coupled one, with the detector's term
  `g f(θ₂) P_j` in its generator.
* **`diracPointerHeld` is a comparison map**, not a dynamics the model has. It is not a flow of
  `Σ_*` and nothing is claimed about it beyond its definition.
* **One trial, one detector.** One pointer, one site, a readout with two values. Several
  detectors, repeated trials, no-signalling and sequential update are not treated.
* **What is assumed** (`specs/unified-record-spacetime-plan.md`, Register 1): the arena (UA-1), the
  preparation law (UA-2) and its reading as the probability of a region (UA-3), the coupling (UA-5)
  and the propagation law (UA-8) are the definitions the statements are about. The arcs, the site,
  the profile and the readout time are apparatus input (UA-4). The rate field of the basin
  statement is UA-6.

References: `specs/BACKLOG.md` #354, #353, #352, #349, #350; `specs/future-work.md`;
`specs/unified-record-spacetime-plan.md` (UO-7, UO-9; calculation 1 of the M3 section; UD-45 to
UD-49); `RecordLayer/GlobalBasin.lean` (`epistemicMeasure`, `ContextField`, `globalBasin`,
`globalBasin_prob`); `RecordLayer/DiracPointerHamiltonian.lean` (`diracPointerFlow`,
`diracPointerFlow_apply`, `diracPointerFlow_snd_snd`, `siteRay`, `arenaObs_siteProj_siteRay`);
`RecordLayer/DiracPointerWrite.lean` (`diracPointerFlow_snd_fst`);
`RecordLayer/DiracPointerThreshold.lean` (`diracReady`, `diracDisplayed`, `writeFibres`,
`diracPointerFlow_displayed_of_mem_writeFibres`, `exists_volume_writeFibres_pos`);
`RecordLayer/DiracPointerRecord.lean` (`measurable_diracPointerFlow`);
`RecordLayer/ShearWitness.lean` (`pshift`, `measurePreserving_pshift`, `volume_readyArc`);
`RecordLayer/ActivatedWrite.lean` (`displayArc`, `readyArc_disjoint_displayArc`);
`Mathlib/MeasureTheory/InvariantTwist.lean` (`MeasurePreserving.vadd_twist_of_invariant`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### The preparation law as a push-forward -/

/-- The preparation law `δ_p ⊗ Haar` is the push-forward of Haar measure on the fibre under
`θ ↦ (p, θ)`. -/
theorem epistemicMeasure_eq_map {N : ℕ} (p : CPN N) :
    epistemicMeasure p = Measure.map (Prod.mk p) (volume : Measure KTorus) :=
  Measure.dirac_prod p

/-- The displayed arc `(1/3, 5/6]` has Haar measure `1/2`. -/
theorem volume_displayArc : (volume : Measure KTorus) displayArc = ENNReal.ofReal (1 / 2) := by
  have h : displayArc = (rep ⁻¹' Ioc (2 * shearWidth 2) (1 - shearWidth 2))
      ×ˢ (univ : Set (AddCircle (1 : ℝ))) := by
    ext x
    simp [displayArc]
  rw [h, Measure.volume_eq_prod, Measure.prod_prod, circleFibre_volume_univ, mul_one,
    shearWidth_two, volume_repPreimage (by norm_num) (by norm_num) (by norm_num)]
  norm_num

section Arena

variable {M : ℕ} {f : ℝ → ℝ} (J μ g : ℝ) (j : ZMod (M + 1)) (hf : Function.Periodic f 1)

/-! ### The fibre over a carrier ray -/

/-- The carrier's ray at time `t`: the ray moved by the coupled propagator of the fibre `θ₂`. -/
theorem diracPointerFlow_fst (hc : ContDiff ℝ ∞ f) (t : ℝ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (q : KTorus) :
    (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M p, q)).1
      = diracArenaEquiv M (arenaKick (diracCarrierU J μ g j hf q.2 t) p) := by
  rw [diracPointerFlow_apply]

/-- The carrier's ray at time `t` depends on the fibre point through `θ₂` alone. -/
theorem diracPointerFlow_fst_congr (hc : ContDiff ℝ ∞ f) (t : ℝ) (x₀ : CPN (2 * M + 1 + 1))
    {θ θ' : KTorus} (h : θ.2 = θ'.2) :
    (diracPointerFlow J μ g j hf hc t (x₀, θ)).1
      = (diracPointerFlow J μ g j hf hc t (x₀, θ')).1 := by
  obtain ⟨p, rfl⟩ := (diracArenaEquiv M).surjective x₀
  rw [diracPointerFlow_fst, diracPointerFlow_fst, h]

/-- ★★ **Over a fixed carrier ray the pointer pair moves by a measure-preserving map.** The map
`θ ↦ (pointer pair at time t)` turns `θ₁` by an amount that depends on `θ₂` alone, so it preserves
`Haar ⊗ ν` for every law `ν` of `θ₂`. -/
theorem measurePreserving_diracPointerFlow_fibre (hc : ContDiff ℝ ∞ f) (t : ℝ)
    (x₀ : CPN (2 * M + 1 + 1)) (ν : Measure (AddCircle (1 : ℝ))) [SFinite ν] :
    MeasurePreserving (fun θ : KTorus => (diracPointerFlow J μ g j hf hc t (x₀, θ)).2)
      ((volume : Measure (AddCircle (1 : ℝ))).prod ν)
      ((volume : Measure (AddCircle (1 : ℝ))).prod ν) := by
  obtain ⟨p, rfl⟩ := (diracArenaEquiv M).surjective x₀
  have hact : Measurable (Function.uncurry
      fun (a : AddCircle (1 : ℝ)) (θ : KTorus) => ((θ.1 + a, θ.2) : KTorus)) :=
    ((measurable_fst.comp measurable_snd).add measurable_fst).prodMk
      (measurable_snd.comp measurable_snd)
  have hφ : Measurable fun θ : KTorus =>
      (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M p, θ)).2.1 - θ.1 :=
    ((measurable_fst.comp measurable_snd).comp
      ((measurable_diracPointerFlow J μ g j hf hc t).comp measurable_prodMk_left)).sub
      measurable_fst
  have h := MeasurePreserving.vadd_twist_of_invariant (volume : Measure (AddCircle (1 : ℝ)))
    (μ := (volume : Measure (AddCircle (1 : ℝ))).prod ν) hact
    (fun a b θ => Prod.ext (by show θ.1 + b + a = θ.1 + (a + b); abel) rfl)
    (fun a => (measurePreserving_add_right (volume : Measure (AddCircle (1 : ℝ))) a).prod
      (MeasurePreserving.id ν)) hφ
    (fun a θ => by
      simp only [diracPointerFlow_snd_fst, add_sub_cancel_left])
  have he : (fun θ : KTorus => (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M p, θ)).2)
      = fun θ : KTorus => ((θ.1 + ((diracPointerFlow J μ g j hf hc t
          (diracArenaEquiv M p, θ)).2.1 - θ.1), θ.2) : KTorus) := by
    funext θ
    exact Prod.ext (add_sub_cancel _ _).symm
      (diracPointerFlow_snd_snd J μ g j hf hc t (diracArenaEquiv M p, θ))
  rw [he]
  exact h

/-! ### The pointer held -/

/-- **The pointer held**: the carrier's ray moved as in the joint flow, the fibre point left where
it was. A comparison map for the statistics; it is not a dynamics of `Σ_*`. -/
noncomputable def diracPointerHeld (hc : ContDiff ℝ ∞ f) (t : ℝ) (x : KSigma (2 * M + 1 + 1)) :
    KSigma (2 * M + 1 + 1) :=
  ((diracPointerFlow J μ g j hf hc t x).1, x.2)

theorem diracPointerHeld_fst (hc : ContDiff ℝ ∞ f) (t : ℝ) (x : KSigma (2 * M + 1 + 1)) :
    (diracPointerHeld J μ g j hf hc t x).1 = (diracPointerFlow J μ g j hf hc t x).1 :=
  rfl

theorem diracPointerHeld_snd (hc : ContDiff ℝ ∞ f) (t : ℝ) (x : KSigma (2 * M + 1 + 1)) :
    (diracPointerHeld J μ g j hf hc t x).2 = x.2 :=
  rfl

theorem measurable_diracPointerHeld (hc : ContDiff ℝ ∞ f) (t : ℝ) :
    Measurable (diracPointerHeld J μ g j hf hc t) :=
  (measurable_fst.comp (measurable_diracPointerFlow J μ g j hf hc t)).prodMk measurable_snd

/-- The flow is the held map applied after the fibre has been moved: the carrier's ray does not
depend on where the pointer angle is. -/
theorem diracPointerFlow_eq_held (hc : ContDiff ℝ ∞ f) (t : ℝ) (x : KSigma (2 * M + 1 + 1)) :
    diracPointerFlow J μ g j hf hc t x
      = diracPointerHeld J μ g j hf hc t (x.1, (diracPointerFlow J μ g j hf hc t x).2) :=
  Prod.ext (diracPointerFlow_fst_congr J μ g j hf hc t x.1
    (diracPointerFlow_snd_snd J μ g j hf hc t x).symm) rfl

/-! ### The law at one time -/

/-- ★★★ **The law at time `t` is the law with the pointer held.** For the preparation
`δ_{x₀} ⊗ (Haar ⊗ ν)`, with the pointer angle uniform and any law `ν` of `θ₂`, the push-forward
under the joint flow equals the push-forward under `diracPointerHeld`: no statistic read at one
time sees the pointer's displacement. -/
theorem map_diracPointerFlow_dirac_prod (hc : ContDiff ℝ ∞ f) (t : ℝ)
    (x₀ : CPN (2 * M + 1 + 1)) (ν : Measure (AddCircle (1 : ℝ))) [SFinite ν] :
    Measure.map (diracPointerFlow J μ g j hf hc t)
        ((Measure.dirac x₀).prod ((volume : Measure (AddCircle (1 : ℝ))).prod ν))
      = Measure.map (diracPointerHeld J μ g j hf hc t)
        ((Measure.dirac x₀).prod ((volume : Measure (AddCircle (1 : ℝ))).prod ν)) := by
  have hF := measurable_diracPointerFlow J μ g j hf hc t
  have hH := measurable_diracPointerHeld J μ g j hf hc t
  have hS := measurePreserving_diracPointerFlow_fibre J μ g j hf hc t x₀ ν
  have hmk : Measurable (Prod.mk x₀ : KTorus → KSigma (2 * M + 1 + 1)) := measurable_prodMk_left
  have he : diracPointerFlow J μ g j hf hc t ∘ Prod.mk x₀
      = (diracPointerHeld J μ g j hf hc t ∘ Prod.mk x₀)
        ∘ fun θ : KTorus => (diracPointerFlow J μ g j hf hc t (x₀, θ)).2 := by
    funext θ
    exact diracPointerFlow_eq_held J μ g j hf hc t (x₀, θ)
  rw [Measure.dirac_prod, Measure.map_map hF hmk, Measure.map_map hH hmk, he,
    ← Measure.map_map (hH.comp hmk) hS.measurable, hS.map_eq]

/-- ★★★ The same for the preparation law of the record layer, `epistemicMeasure x₀ = δ_{x₀} ⊗
Haar`. -/
theorem map_diracPointerFlow_epistemicMeasure (hc : ContDiff ℝ ∞ f) (t : ℝ)
    (x₀ : CPN (2 * M + 1 + 1)) :
    Measure.map (diracPointerFlow J μ g j hf hc t) (epistemicMeasure x₀)
      = Measure.map (diracPointerHeld J μ g j hf hc t) (epistemicMeasure x₀) :=
  map_diracPointerFlow_dirac_prod J μ g j hf hc t x₀ volume

/-- A region of `Σ_*` has at time `t` the probability it has with the pointer held. -/
theorem epistemicMeasure_preimage_diracPointerFlow (hc : ContDiff ℝ ∞ f) (t : ℝ)
    (x₀ : CPN (2 * M + 1 + 1)) {R : Set (KSigma (2 * M + 1 + 1))} (hR : MeasurableSet R) :
    epistemicMeasure x₀ (diracPointerFlow J μ g j hf hc t ⁻¹' R)
      = epistemicMeasure x₀ (diracPointerHeld J μ g j hf hc t ⁻¹' R) := by
  rw [← Measure.map_apply (measurable_diracPointerFlow J μ g j hf hc t) hR,
    ← Measure.map_apply (measurable_diracPointerHeld J μ g j hf hc t) hR,
    map_diracPointerFlow_epistemicMeasure]

/-- ★★ **The fibre point at time `t` has the law it started with**, `Haar ⊗ ν`, whatever the
carrier. -/
theorem map_snd_diracPointerFlow_dirac_prod (hc : ContDiff ℝ ∞ f) (t : ℝ)
    (x₀ : CPN (2 * M + 1 + 1)) (ν : Measure (AddCircle (1 : ℝ))) [SFinite ν] :
    Measure.map (fun x => (diracPointerFlow J μ g j hf hc t x).2)
        ((Measure.dirac x₀).prod ((volume : Measure (AddCircle (1 : ℝ))).prod ν))
      = (volume : Measure (AddCircle (1 : ℝ))).prod ν := by
  have hm : Measurable fun x : KSigma (2 * M + 1 + 1) =>
      (diracPointerFlow J μ g j hf hc t x).2 :=
    measurable_snd.comp (measurable_diracPointerFlow J μ g j hf hc t)
  rw [Measure.dirac_prod, Measure.map_map hm measurable_prodMk_left]
  exact (measurePreserving_diracPointerFlow_fibre J μ g j hf hc t x₀ ν).map_eq

/-- ★★ Under `epistemicMeasure` the fibre point is Haar distributed at every time. -/
theorem map_snd_diracPointerFlow_epistemicMeasure (hc : ContDiff ℝ ∞ f) (t : ℝ)
    (x₀ : CPN (2 * M + 1 + 1)) :
    Measure.map (fun x => (diracPointerFlow J μ g j hf hc t x).2) (epistemicMeasure x₀)
      = (volume : Measure KTorus) :=
  map_snd_diracPointerFlow_dirac_prod J μ g j hf hc t x₀ volume

/-! ### Regions of the fibre -/

/-- ★★★ **A region of the fibre cannot see the carrier.** Under the preparation
`δ_{x₀} ⊗ (Haar ⊗ ν)` the probability that the fibre point lies in `F` at time `t` is the measure
of `F`: the same for every carrier ray, time, coupling, site and profile. -/
theorem dirac_prod_diracPointerFlow_fibreRegion (hc : ContDiff ℝ ∞ f) (t : ℝ)
    (x₀ : CPN (2 * M + 1 + 1)) (ν : Measure (AddCircle (1 : ℝ))) [SFinite ν]
    {F : Set KTorus} (hF : MeasurableSet F) :
    (Measure.dirac x₀).prod ((volume : Measure (AddCircle (1 : ℝ))).prod ν)
        (diracPointerFlow J μ g j hf hc t ⁻¹' (Prod.snd ⁻¹' F))
      = (volume : Measure (AddCircle (1 : ℝ))).prod ν F :=
  calc (Measure.dirac x₀).prod ((volume : Measure (AddCircle (1 : ℝ))).prod ν)
        (diracPointerFlow J μ g j hf hc t ⁻¹' (Prod.snd ⁻¹' F))
      = Measure.map (fun x => (diracPointerFlow J μ g j hf hc t x).2)
          ((Measure.dirac x₀).prod ((volume : Measure (AddCircle (1 : ℝ))).prod ν)) F :=
        (Measure.map_apply
          (measurable_snd.comp (measurable_diracPointerFlow J μ g j hf hc t)) hF).symm
    _ = (volume : Measure (AddCircle (1 : ℝ))).prod ν F := by
        rw [map_snd_diracPointerFlow_dirac_prod]

/-- ★★★ The same under `epistemicMeasure`: the probability is the Haar measure of the region. -/
theorem epistemicMeasure_diracPointerFlow_fibreRegion (hc : ContDiff ℝ ∞ f) (t : ℝ)
    (x₀ : CPN (2 * M + 1 + 1)) {F : Set KTorus} (hF : MeasurableSet F) :
    epistemicMeasure x₀ (diracPointerFlow J μ g j hf hc t ⁻¹' (Prod.snd ⁻¹' F))
      = (volume : Measure KTorus) F :=
  dirac_prod_diracPointerFlow_fibreRegion J μ g j hf hc t x₀ volume hF

/-- ★★ **The readout shows `true` with probability `1/2`** at every time, for every carrier. -/
theorem epistemicMeasure_diracDisplayed (hc : ContDiff ℝ ∞ f) (t : ℝ)
    (x₀ : CPN (2 * M + 1 + 1)) :
    epistemicMeasure x₀ {x | diracDisplayed M (diracPointerFlow J μ g j hf hc t x) = true}
      = ENNReal.ofReal (1 / 2) := by
  have h : {x | diracDisplayed M (diracPointerFlow J μ g j hf hc t x) = true}
      = diracPointerFlow J μ g j hf hc t ⁻¹' (Prod.snd ⁻¹' displayArc) := by
    ext x
    exact diracDisplayed_eq_true_iff
  rw [h, epistemicMeasure_diracPointerFlow_fibreRegion J μ g j hf hc t x₀
    measurableSet_displayArc, volume_displayArc]

/-- The pointer is in the ready arc with probability `1/6` at every time, for every carrier. -/
theorem epistemicMeasure_diracReady (hc : ContDiff ℝ ∞ f) (t : ℝ) (x₀ : CPN (2 * M + 1 + 1)) :
    epistemicMeasure x₀ (diracPointerFlow J μ g j hf hc t ⁻¹' diracReady M)
      = ENNReal.ofReal (1 / 6) := by
  have h := epistemicMeasure_diracPointerFlow_fibreRegion J μ g j hf hc t x₀
    (measurableSet_readyArc (K := 2))
  rw [volume_readyArc, shearWidth_two] at h
  exact h

/-- ★★★ **No region of the fibre tracks the occupancy of the detector's site.** On a ring with a
second site `k ≠ j`, for every measurable region `F` of the fibre and every time there is a
carrier whose probability of being found in `F` differs from the occupancy `⟨P_j⟩` of the
detector's site by at least `1/2`. The carrier on the detector's site or the carrier on `k` will
do. -/
theorem exists_half_le_abs_fibreRegion_sub_siteWeight (hc : ContDiff ℝ ∞ f)
    {k : ZMod (M + 1)} (hk : j ≠ k) (t : ℝ) {F : Set KTorus} (hF : MeasurableSet F) :
    ∃ p : GenArena (ZMod (M + 1) × Fin 2),
      1 / 2 ≤ |(epistemicMeasure (diracArenaEquiv M p)
          (diracPointerFlow J μ g j hf hc t ⁻¹' (Prod.snd ⁻¹' F))).toReal
        - arenaObs (siteProj j) p| := by
  simp only [epistemicMeasure_diracPointerFlow_fibreRegion J μ g j hf hc t _ hF]
  rcases le_total ((volume : Measure KTorus) F).toReal (1 / 2) with h | h
  · refine ⟨siteRay j, ?_⟩
    rw [arenaObs_siteProj_siteRay, abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · refine ⟨siteRay k, ?_⟩
    rw [arenaObs_siteProj_siteRay_of_ne hk, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
    exact h

/-! ### Regions that depend on the base point -/

/-- ★★ **The basin of a rate field at time `t`.** For any rate field `c` on the carrier's rays, the
probability that the arena point is in `globalBasin c i` at time `t` is the rate `c.rate · i` at
the *coupled* carrier, averaged over the conserved angle `θ₂`. The pointer's displacement does not
enter.

Conditional on the rate field (UA-6 of `specs/unified-record-spacetime-plan.md`): the dependence
on the carrier is the one `c` was given. This is not a derivation of outcome statistics from the
flow. -/
theorem epistemicMeasure_diracPointerFlow_globalBasin (hc : ContDiff ℝ ∞ f) (t : ℝ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (c : ContextField (2 * M + 1 + 1))
    (i : Fin (2 * M + 1 + 1)) :
    epistemicMeasure (diracArenaEquiv M p)
        (diracPointerFlow J μ g j hf hc t ⁻¹' globalBasin c i)
      = ∫⁻ φ : AddCircle (1 : ℝ), ENNReal.ofReal
          (c.rate (diracArenaEquiv M (arenaKick (diracCarrierU J μ g j hf φ t) p)) i) := by
  have hH := measurable_diracPointerHeld J μ g j hf hc t
  have hmk : Measurable (Prod.mk (diracArenaEquiv M p) : KTorus → KSigma (2 * M + 1 + 1)) :=
    measurable_prodMk_left
  have hB := measurableSet_globalBasin c i
  rw [epistemicMeasure_preimage_diracPointerFlow J μ g j hf hc t _ hB, epistemicMeasure_eq_map,
    Measure.map_apply hmk (hH hB), Measure.volume_eq_prod,
    Measure.prod_apply_symm (hmk (hH hB))]
  refine lintegral_congr fun φ => ?_
  have hs : (fun θ₁ : AddCircle (1 : ℝ) => ((θ₁, φ) : KTorus)) ⁻¹'
        (Prod.mk (diracArenaEquiv M p) ⁻¹'
          (diracPointerHeld J μ g j hf hc t ⁻¹' globalBasin c i))
      = circleCell
          (c.rate (diracArenaEquiv M (arenaKick (diracCarrierU J μ g j hf φ t) p))) i := by
    ext θ₁
    show θ₁ ∈ circleCell
        (c.rate (diracPointerFlow J μ g j hf hc t (diracArenaEquiv M p, (θ₁, φ))).1) i ↔ _
    rw [diracPointerFlow_fst]
  rw [hs]
  exact volume_circleCell _ (c.nonneg _) (c.loSum_le_one _) i

/-! ### The check: an event about two times -/

/-- With the pointer held, *ready at `0` and displayed at `T`* never happens: the ready arc and the
displayed arc are disjoint. -/
theorem ready_diracPointerHeld_displayed_eq_empty (hc : ContDiff ℝ ∞ f) (T : ℝ) :
    {x | x ∈ diracReady M ∧ diracDisplayed M (diracPointerHeld J μ g j hf hc T x) = true}
      = (∅ : Set (KSigma (2 * M + 1 + 1))) := by
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  exact Set.disjoint_left.mp readyArc_disjoint_displayArc hx.1
    (diracDisplayed_eq_true_iff.mp hx.2)

/-- ★★ **Under the flow, *ready at `0` and displayed at `T`* has probability at least
`(1/6) · vol(writeFibres)`** for the carrier on the detector's site. The one-time theorem
`map_diracPointerFlow_epistemicMeasure` does not extend to events about two times. -/
theorem ofReal_mul_volume_writeFibres_le (hc : ContDiff ℝ ∞ f) {T : ℝ} (hT : 0 ≤ T) :
    ENNReal.ofReal (1 / 6) * volume (writeFibres M J μ g hf T)
      ≤ epistemicMeasure (diracArenaEquiv M (siteRay j))
          {x | x ∈ diracReady M
            ∧ diracDisplayed M (diracPointerFlow J μ g j hf hc T x) = true} := by
  have hD : MeasurableSet {x : KSigma (2 * M + 1 + 1) | diracDisplayed M x = true} :=
    measurable_diracDisplayed M (measurableSet_singleton true)
  have hE : MeasurableSet {x | x ∈ diracReady M
      ∧ diracDisplayed M (diracPointerFlow J μ g j hf hc T x) = true} :=
    (measurableSet_diracReady M).inter (measurable_diracPointerFlow J μ g j hf hc T hD)
  have hsub : (rep ⁻¹' Ioc (0 : ℝ) (shearWidth 2)) ×ˢ writeFibres M J μ g hf T
      ⊆ Prod.mk (diracArenaEquiv M (siteRay j)) ⁻¹' {x | x ∈ diracReady M
        ∧ diracDisplayed M (diracPointerFlow J μ g j hf hc T x) = true} := by
    rintro q ⟨hq₁, hq₂⟩
    exact ⟨hq₁, diracPointerFlow_displayed_of_mem_writeFibres J μ g j hf hc hT hq₁ hq₂⟩
  rw [epistemicMeasure_eq_map, Measure.map_apply measurable_prodMk_left hE]
  refine le_trans (le_of_eq ?_) (measure_mono hsub)
  rw [Measure.volume_eq_prod, Measure.prod_prod, shearWidth_two,
    volume_repPreimage le_rfl (by norm_num) (by norm_num), sub_zero]

/-- ★★ Where the write fibres are not null, the carrier on the detector's site is *ready at `0`
and displayed at `T`* with positive probability. -/
theorem epistemicMeasure_ready_displayed_pos (hc : ContDiff ℝ ∞ f) {T : ℝ} (hT : 0 ≤ T)
    (hW : 0 < volume (writeFibres M J μ g hf T)) :
    0 < epistemicMeasure (diracArenaEquiv M (siteRay j))
      {x | x ∈ diracReady M ∧ diracDisplayed M (diracPointerFlow J μ g j hf hc T x) = true} :=
  lt_of_lt_of_le
    (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by norm_num)).ne' hW.ne')
    (ofReal_mul_volume_writeFibres_le J μ g j hf hc hT)

end Arena

/-- ★★ **The two-time event is not empty of probability**: for every ring, every `J`, `μ` and
every site there are a coupling and a readout time at which, for the profile `trainF`, the carrier
on the detector's site is *ready at `0` and displayed at `T`* with positive probability, while
with the pointer held that event is empty (`ready_diracPointerHeld_displayed_eq_empty`). -/
theorem exists_epistemicMeasure_ready_displayed_pos (M : ℕ) (J μ : ℝ) (j : ZMod (M + 1)) :
    ∃ g T : ℝ, 0 < T ∧ 0 < epistemicMeasure (diracArenaEquiv M (siteRay j))
      {x | x ∈ diracReady M ∧ diracDisplayed M
        (diracPointerFlow J μ g j trainF_periodic contDiff_trainF T x) = true} := by
  obtain ⟨g, T, hT, hW⟩ := exists_volume_writeFibres_pos M J μ
  exact ⟨g, T, hT,
    epistemicMeasure_ready_displayed_pos J μ g j trainF_periodic contDiff_trainF hT.le hW⟩

end CSD.RecordLayer

end
