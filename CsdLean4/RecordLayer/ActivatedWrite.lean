/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.DetunedExchange
public import CsdLean4.RecordLayer.RecordOccurrence
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.AddCirclePeriodicLift
public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The activated write: one pointer set in motion by the arriving carrier

**Category:** 7-SigmaLayer (the record layer). BACKLOG #194 (out of #39; the research gate of the
author's second operational-geometry brief, #191–#197).

Every write in the corpus so far was triggered by a schedule: a readout time indexed by `t_Σ`
(`RecordedExchange.lean`, `ChainClocks.lean`). This file replaces one of them by an internal
activation. The arena is the two-site exchange of #183 with one pointer torus,

  `ActiveArena = FieldArena 2 2 × T²`,   `θ = (θ₁, θ₂)`,

and the dynamics is the one the **time-independent joint Hamiltonian**

  `𝓗(p, θ) = ⟨p, J X p⟩ + g · n_B(p) · f(θ₂)`,   `f` periodic and `C¹`,

prescribes on the product: at fixed `θ₂` the ray evolves by the detuned exchange `H(Δ) = J X + Δ n_B`
with `Δ = g f(θ₂)` (`CV/DetunedExchange.lean`), the pointer `θ₁` moves at the rate
`−(2g/ħ) f'(θ₂) · n_B(p)` (the factor is the arena form's normalisation, fixed by #195),
and `θ₂` is conserved. The pointer therefore moves **only while the carrier occupies the receiver**:
the activation is the arriving carrier, and no test of `t_Σ` appears anywhere — the evolution is
autonomous (`activeEvolve_shift`).

* `detuningAt`, `rateAt` — `g f(θ₂)` and `−(2g/ħ) f'(θ₂)` on the circle (`Function.Periodic.lift`);
  `Function.Periodic.deriv_periodic` (`AddCirclePeriodicLift.lean`); ★ `pointerAmount`, ★ `activeFlow` — **the dynamics as data**;
* `activeFlow_zero`, ★★ `activeFlow_add` — **a one-parameter group**, by the group law of the
  accumulated occupancy; `activeEvolve`, `activeEvolve_self`, `activeEvolve_comp` — **the two-time
  law**; ★ `activeEvolve_shift` — **autonomy**: only `t − s` enters;
* `continuous_activeFlow`; ★★ `activeFlow_measurePreserving` — **Liouville**: the skew product
  of the Fubini–Study-preserving unitary at fixed `θ₂` with a translation of `θ₁` by a function of
  `(p, θ₂)`, over the conserved `θ₂`;
* ★★ `activeEnergy_activeFlow` — **the joint energy `J⟨X⟩ + g f(θ₂) n_B` is conserved**;
  `activeFlow_angle` — `θ₂` is conserved;
* ★★ `hasDerivAt_pointerAmount` — **the pointer's equation of motion**: the lifted angle moves at
  the rate `−(2g/ħ) f'(θ₂) · n_B(p(t))`; `occHist_msgPoint_one_zero`, `occHist_msgPoint_one_pos` (in
  `DetunedExchange.lean`) — the pointer starts at rest and is set in motion by the carrier;
* ★★★ `pointerAmount_msgPoint_one`, `activeFlow_msgPoint_zero` — **the message-dependent pointer
  displacement**: for message `1` the pointer has turned by `κ (ωt − sin ωt cos ωt)/(2ω)` with
  `κ = −(2g/ħ) f'(θ₂) (J/Ω)²`, `ω = Ω/ħ`; for message `0` the whole arena point is fixed;
* `displayArc`, `displayed`, `writeStart`, `writeEnd`, `retention`; ★★ `message_one_not_displayed`,
  ★★ `message_one_displayed` — **the write interval and the retention window**, under the explicit
  hypotheses `0 < κ` and `3κ ≤ 2ω` (the pointer gains at most two thirds of a turn per Rabi radian);
  ★★★ `activatedRegister` — **the write as an `ActualOccurrence`** (#191), site `{B}`, from the
  start `0`, value `true`, with its write interval `[1/(6κ), 2/(3κ) + 1/(2ω)]` and window
  `2/(3κ) − 1/ω`;
* ★★ `records_distinguish` — **the two messages leave the pointer in disjoint arcs** throughout the
  window; the detuning loss `(J/Ω)² < 1` is paid in the rate, not in the record;
* ★★ `message_one_returns` — **the retention is finite**: the carrier oscillates on, the pointer
  keeps turning, and at an explicit later time it is back where message `0` left it;
* ★★ `transition_region` — **the obstruction half**: for every horizon `T` the set of `θ₂` at which
  the message-`1` write has not been displayed by `T` is open and of positive Haar measure. It
  contains the zero of `f'` that Rolle's theorem forces on every periodic `C¹` coupling
  (`exists_rateAt_eq_zero`). The write is continuous in the preparation, so it is exact only off a
  transition region — the trilemma's price, which the brief allows;
* ★★★ `activated_write` — the package.

## What is and is not claimed

* ⚠️ **Hamiltonian generation is #195.** This file builds the dynamics the Hamiltonian prescribes
  and proves it is a two-time, measure-preserving, energy-conserving flow whose pointer obeys the
  stated equation of motion (`hasDerivAt_pointerAmount`) and whose ray obeys Schrödinger's equation
  with the state-dependent generator (`hasDerivAt_detunedFlowVal`). That `activeFlow` is the
  Hamiltonian flow of `𝓗` for the arena form of `LF4/ArenaSymplectic.lean` is not proved here.
* The pointer coordinate that moves is `θ₁`; the record is read off it. Its symplectic partner `θ₂`
  is a conserved parameter that sets both the detuning and the rate; nothing is claimed about a
  global translation on the torus (`θ̇₂ = 0`).
* The write is exact for the preparations stated: ready pointer, `0 < κ`, `3κ ≤ 2ω`. Angles with
  `f'(θ₂) < 0` turn the pointer the other way and are not treated; angles with small `|f'|` are the
  transition region of `transition_region`, and that region has positive measure for every finite
  horizon. This is the honest form of "exact only off a transition region".
* No clock is in this arena; the forgetful map to `CV.RecordEvent` needs one and is not taken.

References: `specs/BACKLOG.md` #194, #191, #195, #39; `CV/DetunedExchange.lean`,
`RecordLayer/RecordOccurrence.lean` (`ActualOccurrence`, `IsRecordWrite`),
`RecordLayer/ShearWitness.lean` (`pshift`, `readyArc`, `rep_pshift_of_mem`),
`RecordLayer/RecordedExchange.lean` (the scheduled writes this replaces one of),
`SigmaLayer/UntriggeredFlow.lean` (the chart-level one-stroke witness), `SigmaLayer/FrozenBase.lean`.
-/

@[expose] public section

open MeasureTheory Set CSD.CV Projectivization Matrix.UnitaryGroup

namespace CSD.RecordLayer

open CSD.SigmaLayer

/-! ### The arena -/

/-- **The arena of the activated write**: the two-site exchange and one pointer torus. -/
abbrev ActiveArena := FieldArena 2 2 × LF4.KTorus

/-! ### The coupling function on the conserved angle -/

section Coupling

variable {f : ℝ → ℝ}

/-- The detuning `g f(θ₂)`. -/
noncomputable def detuningAt (g : ℝ) (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ)) : ℝ :=
  g * hf.lift φ

/-- The pointer rate `−(2g/ħ) f'(θ₂)`: the rate Hamilton's equations prescribe for the arena form,
whose Fubini–Study normalisation makes the Schrödinger unitary of `H` the flow of `−2⟨H⟩`
(`LF4/ArenaCoupledFlow.lean`, #195). -/
noncomputable def rateAt (g ħ : ℝ) (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ)) : ℝ :=
  -(2 * g / ħ) * hf.deriv_periodic.lift φ

theorem detuningAt_coe (g : ℝ) (hf : Function.Periodic f 1) (x : ℝ) :
    detuningAt g hf (x : AddCircle (1 : ℝ)) = g * f x := by
  rw [detuningAt, Function.Periodic.lift_coe]

theorem rateAt_coe (g ħ : ℝ) (hf : Function.Periodic f 1) (x : ℝ) :
    rateAt g ħ hf (x : AddCircle (1 : ℝ)) = -(2 * g / ħ) * deriv f x := by
  rw [rateAt, Function.Periodic.lift_coe]

theorem continuous_periodicLift (hf : Function.Periodic f 1) (hc : Continuous f) :
    Continuous (hf.lift : AddCircle (1 : ℝ) → ℝ) := by
  refine (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr ?_
  exact hc.congr fun x => (hf.lift_coe x).symm

theorem continuous_detuningAt (g : ℝ) (hf : Function.Periodic f 1) (hc : Continuous f) :
    Continuous (detuningAt g hf) :=
  continuous_const.mul (continuous_periodicLift hf hc)

theorem continuous_rateAt (g ħ : ℝ) (hf : Function.Periodic f 1) (hf1 : ContDiff ℝ 1 f) :
    Continuous (rateAt g ħ hf) :=
  continuous_const.mul (continuous_periodicLift _ hf1.continuous_deriv_one)

/-- **Rolle**: a periodic `C¹` coupling has a stationary angle, at which the pointer rate vanishes. -/
theorem exists_rateAt_eq_zero (g ħ : ℝ) (hf : Function.Periodic f 1) (hf1 : ContDiff ℝ 1 f) :
    ∃ φ : AddCircle (1 : ℝ), rateAt g ħ hf φ = 0 := by
  obtain ⟨c, -, hc⟩ := exists_deriv_eq_zero (f := f) zero_lt_one hf1.continuous.continuousOn
    (by simpa using (hf 0).symm)
  exact ⟨(c : AddCircle (1 : ℝ)), by rw [rateAt_coe, hc, mul_zero]⟩

end Coupling

/-! ### The dynamics -/

section Dynamics

variable {f : ℝ → ℝ} (J ħ g : ℝ) (hf : Function.Periodic f 1)

/-- **The lifted pointer displacement** after time `t`: `−(2g/ħ) f'(θ₂) ∫₀ᵗ n_B(p(s)) ds`. -/
noncomputable def pointerAmount (t : ℝ) (x : ActiveArena) : ℝ :=
  rateAt g ħ hf x.2.2 * occAccum J ħ (detuningAt g hf x.2.2) x.1 t

/-- ★ **The activated flow**: at fixed `θ₂` the ray evolves by the detuned exchange with
`Δ = g f(θ₂)`, and the pointer `θ₁` is translated by the lifted displacement. -/
noncomputable def activeFlow (t : ℝ) : ActiveArena → ActiveArena := fun x =>
  ((detunedFlow J ħ (detuningAt g hf x.2.2)).arenaFlow t x.1,
    pshift (pointerAmount J ħ g hf t x) x.2)

theorem activeFlow_fst (t : ℝ) (x : ActiveArena) :
    (activeFlow J ħ g hf t x).1 = (detunedFlow J ħ (detuningAt g hf x.2.2)).arenaFlow t x.1 := rfl

theorem activeFlow_snd (t : ℝ) (x : ActiveArena) :
    (activeFlow J ħ g hf t x).2 = pshift (pointerAmount J ħ g hf t x) x.2 := rfl

/-- **`θ₂` is conserved.** -/
theorem activeFlow_angle (t : ℝ) (x : ActiveArena) : (activeFlow J ħ g hf t x).2.2 = x.2.2 := rfl

/-- The receiver's occupancy along the flow is the occupancy history of the detuned exchange. -/
theorem occupancy_activeFlow (t : ℝ) (x : ActiveArena) :
    arenaObs occB (activeFlow J ħ g hf t x).1 = occHist J ħ (detuningAt g hf x.2.2) x.1 t := rfl

theorem activeFlow_zero : activeFlow J ħ g hf 0 = id := by
  funext x
  simp [activeFlow, pointerAmount, FieldStructuredFlow.arenaFlow_zero', occAccum_zero]

theorem pointerAmount_add (s t : ℝ) (x : ActiveArena) :
    pointerAmount J ħ g hf (s + t) x
      = pointerAmount J ħ g hf s x + pointerAmount J ħ g hf t (activeFlow J ħ g hf s x) := by
  unfold pointerAmount
  rw [activeFlow_angle, activeFlow_fst, occAccum_add, mul_add]

/-- ★★ **The group law**: the flow is a one-parameter group, because the accumulated occupancy
obeys the group law of the detuned exchange (`occAccum_add`). -/
theorem activeFlow_add (s t : ℝ) :
    activeFlow J ħ g hf (s + t) = activeFlow J ħ g hf t ∘ activeFlow J ħ g hf s := by
  funext x
  refine Prod.ext ?_ ?_
  · show (detunedFlow J ħ (detuningAt g hf x.2.2)).arenaFlow (s + t) x.1
      = (detunedFlow J ħ (detuningAt g hf x.2.2)).arenaFlow t
          ((detunedFlow J ħ (detuningAt g hf x.2.2)).arenaFlow s x.1)
    rw [add_comm, FieldStructuredFlow.arenaFlow_add]
  · show pshift (pointerAmount J ħ g hf (s + t) x) x.2
      = pshift (pointerAmount J ħ g hf t (activeFlow J ħ g hf s x))
          (pshift (pointerAmount J ħ g hf s x) x.2)
    rw [pshift_add, pointerAmount_add, add_comm]

/-- **The two-time propagator**: autonomous, so only the elapsed time enters. -/
noncomputable def activeEvolve (s t : OnticTime) : ActiveArena → ActiveArena :=
  activeFlow J ħ g hf (t - s)

theorem activeEvolve_self (t : OnticTime) : activeEvolve J ħ g hf t t = id := by
  rw [activeEvolve, sub_self, activeFlow_zero]

/-- **The two-time law.** -/
theorem activeEvolve_comp (s t u : OnticTime) :
    activeEvolve J ħ g hf t u ∘ activeEvolve J ħ g hf s t = activeEvolve J ħ g hf s u := by
  unfold activeEvolve
  rw [← activeFlow_add]
  congr 1
  ring

/-- ★ **Autonomy**: shifting both times leaves the propagator unchanged — no test of `t_Σ`
appears. Compare the scheduled `hopOn`/`arrived` of `RecordedExchange.lean`. -/
theorem activeEvolve_shift (s t a : OnticTime) :
    activeEvolve J ħ g hf (s + a) (t + a) = activeEvolve J ħ g hf s t := by
  unfold activeEvolve
  congr 1
  ring

/-! ### Continuity and Liouville -/

theorem continuous_pointerAmount (hf1 : ContDiff ℝ 1 f) (t : ℝ) :
    Continuous (pointerAmount J ħ g hf t) := by
  unfold pointerAmount
  have hΔ : Continuous fun x : ActiveArena => detuningAt g hf x.2.2 :=
    ((continuous_detuningAt g hf hf1.continuous).snd').snd'
  exact (((continuous_rateAt g ħ hf hf1).snd').snd').mul
    ((continuous_occAccum_prod J ħ t).comp₂ continuous_fst hΔ)

theorem continuous_activeFlow (hf1 : ContDiff ℝ 1 f) (t : ℝ) :
    Continuous (activeFlow J ħ g hf t) := by
  unfold activeFlow FieldStructuredFlow.arenaFlow
  have hΔ : Continuous fun x : ActiveArena => detuningAt g hf x.2.2 :=
    ((continuous_detuningAt g hf hf1.continuous).snd').snd'
  have hU : Continuous fun x : ActiveArena => (detunedFlow J ħ (detuningAt g hf x.2.2)).flow t :=
    (continuous_detunedFlow_prod J ħ).comp₂ hΔ continuous_const
  exact (hU.arenaKick continuous_fst).prodMk
    (continuous_pshift_uncurry.comp₂ (continuous_pointerAmount J ħ g hf hf1 t) continuous_snd)

theorem measurable_activeEvolve (hf1 : ContDiff ℝ 1 f) (s t : OnticTime) :
    Measurable (activeEvolve J ħ g hf s t) :=
  (continuous_activeFlow J ħ g hf hf1 (t - s)).measurable

/-- Translation of one circle coordinate, written as `pshift` writes it. -/
noncomputable def cshift (a : ℝ) (θ : AddCircle (1 : ℝ)) : AddCircle (1 : ℝ) :=
  θ + (a : AddCircle (1 : ℝ))

theorem continuous_cshift_uncurry :
    Continuous fun aθ : ℝ × AddCircle (1 : ℝ) => cshift aθ.1 aθ.2 := by
  unfold cshift
  fun_prop

theorem measurePreserving_cshift (a : ℝ) :
    MeasurePreserving (cshift a) (volume : Measure (AddCircle (1 : ℝ))) volume := by
  have h : cshift a = fun θ => (a : AddCircle (1 : ℝ)) + θ := funext fun θ => add_comm _ _
  rw [h]
  exact measurePreserving_add_left volume _

/-- ★★ **Liouville**: the activated flow preserves Fubini–Study × Haar × Haar. The proof is the
skew product over the conserved `θ₂`: at fixed `θ₂` the ray moves by a unitary (Fubini–Study
preserving) and `θ₁` by a translation depending on `(p, θ₂)` (Haar preserving). -/
theorem activeFlow_measurePreserving (hf1 : ContDiff ℝ 1 f) (t : ℝ) (p₀ : FieldArena 2 2) :
    MeasurePreserving (activeFlow J ħ g hf t) ((fsMeasure p₀).prod volume)
      ((fsMeasure p₀).prod volume) := by
  let eF : ActiveArena → AddCircle (1 : ℝ) × (FieldArena 2 2 × AddCircle (1 : ℝ)) :=
    fun x => (x.2.2, (x.1, x.2.1))
  let eB : AddCircle (1 : ℝ) × (FieldArena 2 2 × AddCircle (1 : ℝ)) → ActiveArena :=
    fun y => (y.2.1, (y.2.2, y.1))
  let G : AddCircle (1 : ℝ) × (FieldArena 2 2 × AddCircle (1 : ℝ))
      → AddCircle (1 : ℝ) × (FieldArena 2 2 × AddCircle (1 : ℝ)) := fun y =>
    (y.1, ((detunedFlow J ħ (detuningAt g hf y.1)).arenaFlow t y.2.1,
      cshift (rateAt g ħ hf y.1 * occAccum J ħ (detuningAt g hf y.1) y.2.1 t) y.2.2))
  have hEq : activeFlow J ħ g hf t = eB ∘ G ∘ eF := by
    funext x
    rfl
  have hassoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (FieldArena 2 2 × AddCircle (1 : ℝ)) × AddCircle (1 : ℝ) ≃ᵐ
        FieldArena 2 2 × (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))
      (((fsMeasure p₀).prod volume).prod volume) ((fsMeasure p₀).prod (volume.prod volume)) :=
    ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩
  have heF : MeasurePreserving eF ((fsMeasure p₀).prod volume)
      (volume.prod ((fsMeasure p₀).prod volume)) := by
    rw [Measure.volume_eq_prod]
    exact Measure.measurePreserving_swap.comp (hassoc.symm _)
  have heB : MeasurePreserving eB (volume.prod ((fsMeasure p₀).prod volume))
      ((fsMeasure p₀).prod volume) := by
    rw [Measure.volume_eq_prod]
    exact hassoc.comp Measure.measurePreserving_swap
  have hfib : ∀ φ : AddCircle (1 : ℝ), MeasurePreserving
      (fun y : FieldArena 2 2 × AddCircle (1 : ℝ) =>
        ((detunedFlow J ħ (detuningAt g hf φ)).arenaFlow t y.1,
          cshift (rateAt g ħ hf φ * occAccum J ħ (detuningAt g hf φ) y.1 t) y.2))
      ((fsMeasure p₀).prod volume) ((fsMeasure p₀).prod volume) := by
    intro φ
    have hgm : Measurable (Function.uncurry fun (p : FieldArena 2 2) (θ : AddCircle (1 : ℝ)) =>
        cshift (rateAt g ħ hf φ * occAccum J ħ (detuningAt g hf φ) p t) θ) := by
      unfold Function.uncurry
      exact (continuous_cshift_uncurry.comp₂ (continuous_const.mul
        ((continuous_occAccum_prod J ħ t).comp₂ continuous_fst continuous_const))
        continuous_snd).measurable
    exact ((detunedFlow J ħ (detuningAt g hf φ)).arenaFlow_measurePreserving t p₀).skew_product hgm
      (ae_of_all _ fun p => (measurePreserving_cshift _).map_eq)
  have hG : MeasurePreserving G (volume.prod ((fsMeasure p₀).prod volume))
      (volume.prod ((fsMeasure p₀).prod volume)) := by
    have hgm : Measurable (Function.uncurry fun (φ : AddCircle (1 : ℝ))
        (y : FieldArena 2 2 × AddCircle (1 : ℝ)) =>
        ((detunedFlow J ħ (detuningAt g hf φ)).arenaFlow t y.1,
          cshift (rateAt g ħ hf φ * occAccum J ħ (detuningAt g hf φ) y.1 t) y.2)) := by
      unfold Function.uncurry FieldStructuredFlow.arenaFlow
      have hΔ : Continuous fun z : AddCircle (1 : ℝ) × (FieldArena 2 2 × AddCircle (1 : ℝ)) =>
          detuningAt g hf z.1 := (continuous_detuningAt g hf hf1.continuous).fst'
      have hU : Continuous fun z : AddCircle (1 : ℝ) × (FieldArena 2 2 × AddCircle (1 : ℝ)) =>
          (detunedFlow J ħ (detuningAt g hf z.1)).flow t :=
        (continuous_detunedFlow_prod J ħ).comp₂ hΔ continuous_const
      refine ((hU.arenaKick (continuous_fst.comp continuous_snd)).prodMk ?_).measurable
      exact continuous_cshift_uncurry.comp₂
        (((continuous_rateAt g ħ hf hf1).fst').mul
          ((continuous_occAccum_prod J ħ t).comp₂ (continuous_fst.comp continuous_snd) hΔ))
        (continuous_snd.comp continuous_snd)
    exact (MeasurePreserving.id volume).skew_product hgm (ae_of_all _ fun φ => (hfib φ).map_eq)
  rw [hEq]
  exact heB.comp (hG.comp heF)

theorem activeEvolve_measurePreserving (hf1 : ContDiff ℝ 1 f) (s t : OnticTime)
    (p₀ : FieldArena 2 2) :
    MeasurePreserving (activeEvolve J ħ g hf s t) ((fsMeasure p₀).prod volume)
      ((fsMeasure p₀).prod volume) :=
  activeFlow_measurePreserving J ħ g hf hf1 (t - s) p₀

/-! ### Energy and the equations of motion -/

/-- **The joint energy** `J⟨X⟩ + g f(θ₂) n_B`: the Hamiltonian function of #194 read at an arena
point. -/
noncomputable def activeEnergy (x : ActiveArena) : ℝ :=
  J * arenaObs hopX x.1 + detuningAt g hf x.2.2 * momentMap x.1 excB

theorem activeEnergy_eq (x : ActiveArena) :
    activeEnergy J g hf x = arenaObs (detunedH J (detuningAt g hf x.2.2)) x.1 :=
  (arenaObs_detunedH _ _ _).symm

/-- ★★ **Energy conservation**: the joint energy is constant along the activated flow. -/
theorem activeEnergy_activeFlow (t : ℝ) (x : ActiveArena) :
    activeEnergy J g hf (activeFlow J ħ g hf t x) = activeEnergy J g hf x := by
  rw [activeEnergy_eq, activeEnergy_eq, activeFlow_angle, activeFlow_fst,
    arenaObs_detunedH_arenaFlow]

/-- ★★ **The pointer's equation of motion**: the lifted displacement moves at the rate
`−(2g/ħ) f'(θ₂) · n_B(p(t))` — only while the carrier occupies the receiver. -/
theorem hasDerivAt_pointerAmount (x : ActiveArena) (t : ℝ) :
    HasDerivAt (fun t => pointerAmount J ħ g hf t x)
      (rateAt g ħ hf x.2.2 * arenaObs occB (activeFlow J ħ g hf t x).1) t :=
  (hasDerivAt_occAccum J ħ _ x.1 t).const_mul _

/-! ### The two messages -/

/-- **Message `0` is fixed**: the vacuum never reaches the receiver, so the pointer never moves. -/
theorem activeFlow_msgPoint_zero (hJ : 0 < J) (q : LF4.KTorus) (t : ℝ) :
    activeFlow J ħ g hf t (msgPoint 0, q) = (msgPoint 0, q) := by
  unfold activeFlow pointerAmount
  simp only [detunedFlow_msgPoint_zero hJ, occAccum_msgPoint_zero hJ, mul_zero, pshift_zero]

/-- The pointer drift `κ (ωt − sin ωt cos ωt)/(2ω)` as a function of time. -/
noncomputable def pointerDrift (κ ω t : ℝ) : ℝ :=
  κ * (ω * t - Real.sin (ω * t) * Real.cos (ω * t)) / (2 * ω)

/-- The mean pointer rate over a Rabi cycle: `κ = −(2g/ħ) f'(θ₂) (J/Ω)²`. -/
noncomputable def driftRate (φ : AddCircle (1 : ℝ)) : ℝ :=
  rateAt g ħ hf φ * (J / rabiFreq J (detuningAt g hf φ)) ^ 2

/-- ★★★ **The message-dependent pointer displacement**: for message `1` the lifted pointer has turned
by `pointerDrift κ ω t` with `κ = −(2g/ħ) f'(θ₂) (J/Ω)²` and `ω = Ω/ħ`. -/
theorem pointerAmount_msgPoint_one (hJ : 0 < J) (hħ : 0 < ħ) (q : LF4.KTorus) (t : ℝ) :
    pointerAmount J ħ g hf t (msgPoint 1, q)
      = pointerDrift (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2)) t := by
  unfold pointerAmount pointerDrift driftRate
  dsimp only
  rw [occAccum_msgPoint_one hJ hħ, rabiAngle]
  ring

theorem activeFlow_msgPoint_one_snd (hJ : 0 < J) (hħ : 0 < ħ) (q : LF4.KTorus) (t : ℝ) :
    (activeFlow J ħ g hf t (msgPoint 1, q)).2
      = pshift (pointerDrift (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2)) t) q := by
  rw [activeFlow_snd, pointerAmount_msgPoint_one J ħ g hf hJ hħ]

end Dynamics

/-! ### Bounds on the drift -/

theorem abs_sin_mul_cos_le_half (x : ℝ) : |Real.sin x * Real.cos x| ≤ 1 / 2 := by
  have h : Real.sin x * Real.cos x = Real.sin (2 * x) / 2 := by
    rw [Real.sin_two_mul]
    ring
  rw [h, abs_div, abs_two]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by norm_num)

theorem sub_sin_mul_cos_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ x - Real.sin x * Real.cos x := by
  have h : Real.sin x * Real.cos x = Real.sin (2 * x) / 2 := by
    rw [Real.sin_two_mul]
    ring
  have h2 := Real.abs_sin_le_abs (x := 2 * x)
  rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 * x by linarith)] at h2
  have := (abs_le.mp h2).2
  rw [h]
  linarith

theorem sub_sin_mul_cos_le_two_mul {x : ℝ} (hx : 0 ≤ x) :
    x - Real.sin x * Real.cos x ≤ 2 * x := by
  have h : Real.sin x * Real.cos x = Real.sin (2 * x) / 2 := by
    rw [Real.sin_two_mul]
    ring
  have h2 := Real.abs_sin_le_abs (x := 2 * x)
  rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 * x by linarith)] at h2
  have := (abs_le.mp h2).1
  rw [h]
  linarith

theorem pointerDrift_nonneg {κ ω : ℝ} (hκ : 0 ≤ κ) (hω : 0 < ω) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ pointerDrift κ ω t :=
  div_nonneg (mul_nonneg hκ (sub_sin_mul_cos_nonneg (mul_nonneg hω.le ht))) (by positivity)

theorem pointerDrift_le {κ ω : ℝ} (hκ : 0 ≤ κ) (hω : 0 < ω) {t : ℝ} (ht : 0 ≤ t) :
    pointerDrift κ ω t ≤ κ * t := by
  unfold pointerDrift
  rw [div_le_iff₀ (by positivity)]
  have := sub_sin_mul_cos_le_two_mul (mul_nonneg hω.le ht)
  nlinarith [mul_le_mul_of_nonneg_left this hκ]

theorem pointerDrift_lower {κ ω : ℝ} (hκ : 0 ≤ κ) (hω : 0 < ω) (t : ℝ) :
    κ * (t / 2 - 1 / (4 * ω)) ≤ pointerDrift κ ω t := by
  unfold pointerDrift
  rw [le_div_iff₀ (by positivity)]
  have h := (abs_le.mp (abs_sin_mul_cos_le_half (ω * t))).2
  have heq : κ * (t / 2 - 1 / (4 * ω)) * (2 * ω) = κ * (ω * t - 1 / 2) := by
    field_simp
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (by linarith) hκ

theorem pointerDrift_upper {κ ω : ℝ} (hκ : 0 ≤ κ) (hω : 0 < ω) (t : ℝ) :
    pointerDrift κ ω t ≤ κ * (t / 2 + 1 / (4 * ω)) := by
  unfold pointerDrift
  rw [div_le_iff₀ (by positivity)]
  have h := (abs_le.mp (abs_sin_mul_cos_le_half (ω * t))).1
  have heq : κ * (t / 2 + 1 / (4 * ω)) * (2 * ω) = κ * (ω * t + 1 / 2) := by
    field_simp
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (by linarith) hκ

theorem continuous_pointerDrift (κ ω : ℝ) : Continuous (pointerDrift κ ω) := by
  unfold pointerDrift
  fun_prop

/-! ### The display arc, the readout and the write interval -/

/-- The displayed arc `(1/3, 5/6]`: two ready widths past the ready arc, one width short of the
turn. -/
noncomputable def displayArc : Set LF4.KTorus :=
  {q | rep q.1 ∈ Ioc (2 * shearWidth 2) (1 - shearWidth 2)}

theorem measurableSet_displayArc : MeasurableSet displayArc :=
  (measurable_rep.comp measurable_fst) measurableSet_Ioc

theorem shearWidth_two : shearWidth 2 = 1 / 6 := by
  norm_num [shearWidth]

theorem readyArc_disjoint_displayArc : Disjoint (readyArc 2) displayArc := by
  refine Set.disjoint_left.mpr fun q hr hd => ?_
  change rep q.1 ∈ Ioc (0 : ℝ) (shearWidth 2) at hr
  change rep q.1 ∈ Ioc (2 * shearWidth 2) (1 - shearWidth 2) at hd
  have := shearWidth_pos (K := 2)
  linarith [hr.2, hd.1]

open Classical in
/-- The Boolean readout: is the pointer in the displayed arc? -/
noncomputable def displayed (x : ActiveArena) : Bool := if x.2 ∈ displayArc then true else false

theorem measurable_displayed : Measurable displayed := by
  unfold displayed
  exact Measurable.ite (measurable_snd measurableSet_displayArc) measurable_const measurable_const

theorem displayed_eq_true {x : ActiveArena} (hx : x.2 ∈ displayArc) : displayed x = true := by
  unfold displayed
  exact ite_eq_left hx

theorem displayed_eq_false {x : ActiveArena} (hx : x.2 ∉ displayArc) : displayed x = false := by
  unfold displayed
  exact ite_eq_right hx

/-- The readout as an `Observation` (#191, kind 2). -/
noncomputable def displayObservation : Observation ActiveArena Bool :=
  ⟨displayed, measurable_displayed⟩

/-- The write interval begins: `1/(6κ)`. -/
noncomputable def writeStart (κ : ℝ) : ℝ := 1 / (6 * κ)

/-- The write interval ends: `2/(3κ) + 1/(2ω)`. -/
noncomputable def writeEnd (κ ω : ℝ) : ℝ := 2 / (3 * κ) + 1 / (2 * ω)

/-- The retention window: `2/(3κ) − 1/ω`. -/
noncomputable def retention (κ ω : ℝ) : ℝ := 2 / (3 * κ) - 1 / ω

theorem writeStart_nonneg {κ : ℝ} (hκ : 0 < κ) : 0 ≤ writeStart κ := by
  unfold writeStart
  positivity

theorem writeStart_le_writeEnd {κ ω : ℝ} (hκ : 0 < κ) (hω : 0 < ω) :
    writeStart κ ≤ writeEnd κ ω := by
  unfold writeStart writeEnd
  have h1 : 1 / (6 * κ) ≤ 2 / (3 * κ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h2 : 0 ≤ 1 / (2 * ω) := by positivity
  linarith

/-- The window is a window exactly when the pointer gains at most two thirds of a turn per Rabi
radian: `3κ ≤ 2ω`. -/
theorem retention_nonneg {κ ω : ℝ} (hκ : 0 < κ) (hω : 0 < ω) (hslow : 3 * κ ≤ 2 * ω) :
    0 ≤ retention κ ω := by
  unfold retention
  rw [sub_nonneg, div_le_div_iff₀ hω (by positivity)]
  linarith

theorem mul_writeStart {κ : ℝ} (hκ : 0 < κ) : κ * writeStart κ = 1 / 6 := by
  unfold writeStart
  field_simp

theorem drift_at_writeEnd {κ ω : ℝ} (hκ : 0 < κ) (hω : 0 < ω) :
    κ * (writeEnd κ ω / 2 - 1 / (4 * ω)) = 1 / 3 := by
  unfold writeEnd
  field_simp
  ring

theorem drift_at_window_end {κ ω : ℝ} (hκ : 0 < κ) (hω : 0 < ω) :
    κ * ((writeEnd κ ω + retention κ ω) / 2 + 1 / (4 * ω)) = 2 / 3 := by
  unfold writeEnd retention
  field_simp
  ring

section Write

variable {f : ℝ → ℝ} {J ħ : ℝ} (g : ℝ) (hf : Function.Periodic f 1)

/-- ★★ **Before the write interval the register is not displayed**: the pointer has turned by less
than `κ t < 1/6`. -/
theorem message_one_not_displayed (hJ : 0 < J) (hħ : 0 < ħ) {q : LF4.KTorus} (hq : q ∈ readyArc 2)
    (hκ : 0 < driftRate J ħ g hf q.2) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < writeStart (driftRate J ħ g hf q.2)) :
    (activeFlow J ħ g hf t (msgPoint 1, q)).2 ∉ displayArc := by
  set κ := driftRate J ħ g hf q.2 with hκdef
  set ω := rabiRate J ħ (detuningAt g hf q.2) with hωdef
  have hω : 0 < ω := rabiRate_pos hJ hħ _
  have hD0 := pointerDrift_nonneg hκ.le hω ht0
  have hD1 : pointerDrift κ ω t < 1 / 6 := by
    calc pointerDrift κ ω t ≤ κ * t := pointerDrift_le hκ.le hω ht0
      _ < κ * writeStart κ := mul_lt_mul_of_pos_left ht hκ
      _ = 1 / 6 := mul_writeStart hκ
  have hr : rep q.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hq
  rw [shearWidth_two] at hr
  rw [activeFlow_msgPoint_one_snd J ħ g hf hJ hħ]
  intro hd
  change rep (pshift (pointerDrift κ ω t) q).1 ∈ Ioc (2 * shearWidth 2) (1 - shearWidth 2) at hd
  rw [shearWidth_two, rep_pshift_of_mem _ _ ⟨by linarith [hr.1], by linarith [hr.2]⟩] at hd
  linarith [hd.1, hr.2]

/-- ★★ **Through the window the register is displayed**: the pointer has turned by between `1/3`
and `2/3` of a turn. -/
theorem message_one_displayed (hJ : 0 < J) (hħ : 0 < ħ) {q : LF4.KTorus} (hq : q ∈ readyArc 2)
    (hκ : 0 < driftRate J ħ g hf q.2) {t : ℝ}
    (ht₁ : writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2)) ≤ t)
    (ht₂ : t ≤ writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))
      + retention (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))) :
    (activeFlow J ħ g hf t (msgPoint 1, q)).2 ∈ displayArc := by
  set κ := driftRate J ħ g hf q.2 with hκdef
  set ω := rabiRate J ħ (detuningAt g hf q.2) with hωdef
  have hω : 0 < ω := rabiRate_pos hJ hħ _
  have hl := pointerDrift_lower hκ.le hω t
  have hu := pointerDrift_upper hκ.le hω t
  have h1 : 1 / 3 ≤ pointerDrift κ ω t := by
    rw [← drift_at_writeEnd hκ hω]
    exact (mul_le_mul_of_nonneg_left (by linarith) hκ.le).trans hl
  have h2 : pointerDrift κ ω t ≤ 2 / 3 := by
    rw [← drift_at_window_end hκ hω]
    exact hu.trans (mul_le_mul_of_nonneg_left (by linarith) hκ.le)
  have hr : rep q.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hq
  rw [shearWidth_two] at hr
  rw [activeFlow_msgPoint_one_snd J ħ g hf hJ hħ]
  change rep (pshift (pointerDrift κ ω t) q).1 ∈ Ioc (2 * shearWidth 2) (1 - shearWidth 2)
  rw [shearWidth_two, rep_pshift_of_mem _ _ ⟨by linarith [hr.1], by linarith [hr.2]⟩]
  constructor <;> linarith [hr.1, hr.2]

/-- ★★★ **The activated write as an actual occurrence** (#191): the carrier at `B` (site `{1}`),
history from `0`, value `true`, write interval `[1/(6κ), 2/(3κ) + 1/(2ω)]`, window `2/(3κ) − 1/ω`.
The hypotheses are the ready pointer, a positive mean rate `κ = −(2g/ħ) f'(θ₂) (J/Ω)²`, and the slowness
`3κ ≤ 2ω`. -/
noncomputable def activatedRegister (hJ : 0 < J) (hħ : 0 < ħ) (hf1 : ContDiff ℝ 1 f)
    {q : LF4.KTorus} (hq : q ∈ readyArc 2) (hκ : 0 < driftRate J ħ g hf q.2)
    (hslow : 3 * driftRate J ħ g hf q.2 ≤ 2 * rabiRate J ħ (detuningAt g hf q.2)) :
    ActualOccurrence ActiveArena Bool 2 where
  evolve := activeEvolve J ħ g hf
  evolve_self := activeEvolve_self J ħ g hf
  evolve_comp := activeEvolve_comp J ħ g hf
  measurable_evolve := measurable_activeEvolve J ħ g hf hf1
  readout := displayed
  measurable_readout := measurable_displayed
  ready := {x | x.2 ∈ readyArc 2}
  measurableSet_ready := measurable_snd measurableSet_readyArc
  prep := (msgPoint 1, q)
  prep_mem := hq
  site := {1}
  start := 0
  value := true
  writeStart := writeStart (driftRate J ħ g hf q.2)
  writeEnd := writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))
  window := retention (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))
  isWrite :=
    { start_le := writeStart_nonneg hκ
      interval := writeStart_le_writeEnd hκ (rabiRate_pos hJ hħ _)
      window_nonneg := retention_nonneg hκ (rabiRate_pos hJ hħ _) hslow
      before := fun t ht0 ht => by
        show displayed (activeFlow J ħ g hf (t - 0) (msgPoint 1, q)) ≠ true
        rw [sub_zero, displayed_eq_false (message_one_not_displayed g hf hJ hħ hq hκ ht0 ht)]
        exact Bool.false_ne_true
      holds := fun t ht₁ ht₂ => by
        show displayed (activeFlow J ħ g hf (t - 0) (msgPoint 1, q)) = true
        rw [sub_zero]
        exact displayed_eq_true (message_one_displayed g hf hJ hħ hq hκ ht₁ ht₂) }

theorem activatedRegister_prep (hJ : 0 < J) (hħ : 0 < ħ) (hf1 : ContDiff ℝ 1 f) {q : LF4.KTorus}
    (hq : q ∈ readyArc 2) (hκ : 0 < driftRate J ħ g hf q.2)
    (hslow : 3 * driftRate J ħ g hf q.2 ≤ 2 * rabiRate J ħ (detuningAt g hf q.2)) :
    (activatedRegister g hf hJ hħ hf1 hq hκ hslow).prep = (msgPoint 1, q) := rfl

theorem activatedRegister_site (hJ : 0 < J) (hħ : 0 < ħ) (hf1 : ContDiff ℝ 1 f) {q : LF4.KTorus}
    (hq : q ∈ readyArc 2) (hκ : 0 < driftRate J ħ g hf q.2)
    (hslow : 3 * driftRate J ħ g hf q.2 ≤ 2 * rabiRate J ħ (detuningAt g hf q.2)) :
    (activatedRegister g hf hJ hħ hf1 hq hκ hslow).site = {1} := rfl

/-- ★★ **The two messages are distinguishable throughout the window**: message `1` displays, message
`0` leaves the pointer ready, and the two pointer positions differ. -/
theorem records_distinguish (hJ : 0 < J) (hħ : 0 < ħ) {q : LF4.KTorus} (hq : q ∈ readyArc 2)
    (hκ : 0 < driftRate J ħ g hf q.2) {t : ℝ}
    (ht₁ : writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2)) ≤ t)
    (ht₂ : t ≤ writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))
      + retention (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))) :
    (activeFlow J ħ g hf t (msgPoint 1, q)).2 ∈ displayArc
      ∧ (activeFlow J ħ g hf t (msgPoint 0, q)).2 ∈ readyArc 2
      ∧ (activeFlow J ħ g hf t (msgPoint 1, q)).2 ≠ (activeFlow J ħ g hf t (msgPoint 0, q)).2 := by
  have h1 := message_one_displayed g hf hJ hħ hq hκ ht₁ ht₂
  rw [activeFlow_msgPoint_zero J ħ g hf hJ]
  refine ⟨h1, hq, fun h => ?_⟩
  rw [h] at h1
  exact Set.disjoint_left.mp readyArc_disjoint_displayArc hq h1

/-- ★★ **The retention is finite**: after the window there is a time at which the message-`1`
pointer is back exactly where message `0` left it — the carrier oscillates on and the pointer
completes a turn. -/
theorem message_one_returns (hJ : 0 < J) (hħ : 0 < ħ) (q : LF4.KTorus)
    (hκ : 0 < driftRate J ħ g hf q.2) :
    ∃ t, writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))
        + retention (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2)) < t
      ∧ (activeFlow J ħ g hf t (msgPoint 1, q)).2 = q := by
  set κ := driftRate J ħ g hf q.2 with hκdef
  set ω := rabiRate J ħ (detuningAt g hf q.2) with hωdef
  have hω : 0 < ω := rabiRate_pos hJ hħ _
  set a := writeEnd κ ω + retention κ ω with ha
  set b := 2 / κ + 1 / (2 * ω) with hb
  have hab : a ≤ b := by
    rw [ha, hb]
    unfold writeEnd retention
    have h1 : 2 / (3 * κ) + 2 / (3 * κ) ≤ 2 / κ := by
      rw [← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h2 : 0 ≤ 1 / (2 * ω) := by positivity
    have h3 : 0 ≤ 1 / ω := by positivity
    linarith
  have hDa : pointerDrift κ ω a ≤ 2 / 3 := by
    rw [← drift_at_window_end hκ hω]
    exact pointerDrift_upper hκ.le hω a
  have hDb : 1 ≤ pointerDrift κ ω b := by
    have h : κ * (b / 2 - 1 / (4 * ω)) = 1 := by
      rw [hb]
      field_simp
      ring
    rw [← h]
    exact pointerDrift_lower hκ.le hω b
  obtain ⟨t, ⟨hta, -⟩, hDt⟩ := intermediate_value_Icc hab
    (continuous_pointerDrift κ ω).continuousOn ⟨by linarith, hDb⟩
  refine ⟨t, lt_of_le_of_ne hta fun h => ?_, ?_⟩
  · rw [← h] at hDt
    linarith
  · rw [activeFlow_msgPoint_one_snd J ħ g hf hJ hħ, hDt]
    show (q.1 + ((1 : ℝ) : AddCircle (1 : ℝ)), q.2) = q
    rw [AddCircle.coe_period, add_zero]

/-! ### The transition region -/

/-- A translation that wraps once drops the representative by a turn. -/
theorem rep_pshift_of_mem_neg (q : LF4.KTorus) {a : ℝ} (h : rep q.1 + a ∈ Ioc (-1 : ℝ) 0) :
    rep (pshift a q).1 = rep q.1 + a + 1 := by
  have h1 : (pshift a q).1 = ((rep q.1 + a + 1 : ℝ) : AddCircle (1 : ℝ)) := by
    show q.1 + (a : AddCircle (1 : ℝ)) = _
    rw [AddCircle.coe_add, AddCircle.coe_period, add_zero, AddCircle.coe_add, coe_rep]
  rw [h1, rep_coe_of_mem_Ioc ⟨by linarith [h.1], by linarith [h.2]⟩]

/-- ★★ **The transition region has positive measure for every horizon.** For every `T > 0` the set
of angles `θ₂` with `|2g f'(θ₂)/ħ| T < 1/6` is open and nonempty (it contains Rolle's zero of `f'`),
hence of positive Haar measure, and from every ready pointer at such an angle the message-`1` write
is not displayed at time `T`. The write is exact only off this region. -/
theorem transition_region (hf1 : ContDiff ℝ 1 f) {T : ℝ} (hT : 0 < T) :
    IsOpen {φ : AddCircle (1 : ℝ) | |rateAt g ħ hf φ| * T < shearWidth 2}
      ∧ 0 < volume {φ : AddCircle (1 : ℝ) | |rateAt g ħ hf φ| * T < shearWidth 2}
      ∧ ∀ φ ∈ {φ : AddCircle (1 : ℝ) | |rateAt g ħ hf φ| * T < shearWidth 2},
          ∀ q ∈ readyArc 2, q.2 = φ → (activeFlow J ħ g hf T (msgPoint 1, q)).2 ∉ displayArc := by
  have hopen : IsOpen {φ : AddCircle (1 : ℝ) | |rateAt g ħ hf φ| * T < shearWidth 2} :=
    isOpen_lt ((continuous_rateAt g ħ hf hf1).abs.mul continuous_const) continuous_const
  obtain ⟨φ₀, hφ₀⟩ := exists_rateAt_eq_zero g ħ hf hf1
  have hne : ({φ : AddCircle (1 : ℝ) | |rateAt g ħ hf φ| * T < shearWidth 2}).Nonempty :=
    ⟨φ₀, by simp [hφ₀, shearWidth_pos]⟩
  refine ⟨hopen, hopen.measure_pos volume hne, ?_⟩
  intro φ hφ q hq hqφ
  have hamt : |pointerAmount J ħ g hf T (msgPoint 1, q)| < shearWidth 2 := by
    unfold pointerAmount
    dsimp only
    rw [hqφ, abs_mul]
    have h0 := occAccum_nonneg J ħ (detuningAt g hf φ) (msgPoint 1) hT.le
    have h1 := occAccum_le J ħ (detuningAt g hf φ) (msgPoint 1) hT.le
    calc |rateAt g ħ hf φ| * |occAccum J ħ (detuningAt g hf φ) (msgPoint 1) T|
        = |rateAt g ħ hf φ| * occAccum J ħ (detuningAt g hf φ) (msgPoint 1) T := by
          rw [abs_of_nonneg h0]
      _ ≤ |rateAt g ħ hf φ| * T := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ < shearWidth 2 := hφ
  rw [activeFlow_snd]
  intro hd
  change rep (pshift (pointerAmount J ħ g hf T (msgPoint 1, q)) q).1
    ∈ Ioc (2 * shearWidth 2) (1 - shearWidth 2) at hd
  set a := pointerAmount J ħ g hf T (msgPoint 1, q) with hadef
  have hr : rep q.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hq
  rw [shearWidth_two] at hamt hd hr
  obtain ⟨ha1, ha2⟩ := abs_lt.mp hamt
  by_cases hpos : 0 < rep q.1 + a
  · rw [rep_pshift_of_mem _ _ ⟨hpos, by linarith [hr.2]⟩] at hd
    linarith [hd.1, hr.2]
  · rw [rep_pshift_of_mem_neg _ ⟨by linarith [hr.1], not_lt.mp hpos⟩] at hd
    linarith [hd.2, hr.1]

/-! ### The package -/

/-- ★★★ **The activated write.** On `FieldArena 2 2 × T²` with the dynamics of the time-independent
joint Hamiltonian `⟨p, J X p⟩ + g n_B(p) f(θ₂)`: the two-time law holds and the propagator is
autonomous; Liouville measure is preserved; the joint energy and `θ₂` are conserved; the pointer's
lifted angle moves at the rate `−(2g/ħ) f'(θ₂) n_B(p(t))`; message `0` leaves the whole arena point
fixed; through the window message `1` displays and the two pointer positions differ; the retention
is finite; and the write is registered as an `ActualOccurrence` at site `{B}`. -/
theorem activated_write (hJ : 0 < J) (hħ : 0 < ħ) (hf1 : ContDiff ℝ 1 f) {q : LF4.KTorus}
    (hq : q ∈ readyArc 2) (hκ : 0 < driftRate J ħ g hf q.2)
    (hslow : 3 * driftRate J ħ g hf q.2 ≤ 2 * rabiRate J ħ (detuningAt g hf q.2)) :
    (∀ s t u : OnticTime, activeEvolve J ħ g hf t u ∘ activeEvolve J ħ g hf s t
        = activeEvolve J ħ g hf s u)
      ∧ (∀ s t a : OnticTime, activeEvolve J ħ g hf (s + a) (t + a) = activeEvolve J ħ g hf s t)
      ∧ (∀ (s t : OnticTime) (p₀ : FieldArena 2 2), MeasurePreserving (activeEvolve J ħ g hf s t)
          ((fsMeasure p₀).prod volume) ((fsMeasure p₀).prod volume))
      ∧ (∀ (t : ℝ) (x : ActiveArena),
          activeEnergy J g hf (activeFlow J ħ g hf t x) = activeEnergy J g hf x)
      ∧ (∀ (t : ℝ) (x : ActiveArena), (activeFlow J ħ g hf t x).2.2 = x.2.2)
      ∧ (∀ (x : ActiveArena) (t : ℝ), HasDerivAt (fun t => pointerAmount J ħ g hf t x)
          (rateAt g ħ hf x.2.2 * arenaObs occB (activeFlow J ħ g hf t x).1) t)
      ∧ (∀ t : ℝ, activeFlow J ħ g hf t (msgPoint 0, q) = (msgPoint 0, q))
      ∧ (∀ t : ℝ, writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2)) ≤ t →
          t ≤ writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))
            + retention (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2)) →
          (activeFlow J ħ g hf t (msgPoint 1, q)).2 ∈ displayArc
            ∧ (activeFlow J ħ g hf t (msgPoint 1, q)).2 ≠ (activeFlow J ħ g hf t (msgPoint 0, q)).2)
      ∧ (∃ t, writeEnd (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2))
            + retention (driftRate J ħ g hf q.2) (rabiRate J ħ (detuningAt g hf q.2)) < t
          ∧ (activeFlow J ħ g hf t (msgPoint 1, q)).2 = q)
      ∧ (activatedRegister g hf hJ hħ hf1 hq hκ hslow).prep = (msgPoint 1, q)
      ∧ (activatedRegister g hf hJ hħ hf1 hq hκ hslow).site = {1} :=
  ⟨activeEvolve_comp J ħ g hf, activeEvolve_shift J ħ g hf,
    fun s t p₀ => activeEvolve_measurePreserving J ħ g hf hf1 s t p₀,
    activeEnergy_activeFlow J ħ g hf, activeFlow_angle J ħ g hf,
    hasDerivAt_pointerAmount J ħ g hf, fun t => activeFlow_msgPoint_zero J ħ g hf hJ q t,
    fun _ ht₁ ht₂ => ⟨(records_distinguish g hf hJ hħ hq hκ ht₁ ht₂).1,
      (records_distinguish g hf hJ hħ hq hκ ht₁ ht₂).2.2⟩,
    message_one_returns g hf hJ hħ q hκ, rfl, rfl⟩

end Write

end CSD.RecordLayer

end
