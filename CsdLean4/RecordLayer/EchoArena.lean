/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.TwoSiteDetuned
public import CsdLean4.RecordLayer.ActivatedWrite

/-!
# The autonomous echo arena: emission, reception and return as activated writes

**Category:** 7-SigmaLayer (the record layer). BACKLOG #199 (out of #39; the author's third
operational-geometry brief, #198–#205).

The activated write of #194 has one pointer, at the receiver. The echo puts a pointer at each
station:

  `EchoArena = FieldArena 2 2 × (T² × T²)`,   `x = (p, (q_A, q_B))`,

pointer `A` coupled to the occupancy of `A`, pointer `B` to the occupancy of `B`, each detuning
the carrier by its own back-reaction (#198: `H = J X + Δ_A n_A + Δ_B n_B`). The dynamics is the one
the time-independent joint Hamiltonian

  `𝓗 = ⟨p, J X p⟩ + g_A n_A(p) f_A(θ₂ᴬ) + g_B n_B(p) f_B(θ₂ᴮ)`

prescribes: at fixed conserved angles the ray evolves by the two-site detuned exchange, pointer `A`
turns at the rate `−(2g_A/ħ) f_A'(θ₂ᴬ) · n_A(p)` and pointer `B` at `−(2g_B/ħ) f_B'(θ₂ᴮ) · n_B(p)`.
**Each pointer moves only while the carrier is at its station.** For message `1` the carrier
leaves `A`, arrives at `B`, and comes back to `A` on its own at the detuned round trip
(`twoDetuned_return`), so pointer `A` is driven twice — once as the carrier leaves (the emission),
once as it returns — and pointer `B` once (the reception). Read in thirds of a turn, pointer `A`'s
first arc is the **emission record** and its second arc the **return record**: two displacement
arcs of one register at `A`, written by the carrier itself.

* `PointerCoupling`; `echoAmountA`, `echoAmountB`, ★ `echoFlow` — **the dynamics as data**;
  `echoFlow_zero`, ★★ `echoFlow_add` — **a one-parameter group** (the group laws of both
  accumulated occupancies along the two-site flow); `echoEvolve`, `echoEvolve_self`,
  `echoEvolve_comp`, ★ `echoEvolve_shift` — **the two-time law and autonomy**;
* ★★ `echoFlow_measurePreserving` — **Liouville**: a skew product over the two conserved angles,
  assembled from three measure-preserving steps (`measurePreserving_cshift_mid`, the translation
  of one circle coordinate by a function of the others, used once per pointer; the unitary kick);
* ★★ `echoEnergy_echoFlow` — **the joint energy is conserved**; `echoFlow_angles` — both `θ₂`
  conserved; ★★ `hasDerivAt_echoAmountA`, `hasDerivAt_echoAmountB` — **the equations of motion**;
* `echoFlow_msgPoint_zero` — **message `0` fixes both pointers**; ★★★ `echoAmountA_msgPoint_one`,
  `echoAmountB_msgPoint_one` — **the two pointer displacements in closed form**: `A` turns by
  `r_A (t − λ (ωt − sin ωt cos ωt)/(2ω))`, `B` by `r_B λ (ωt − sin ωt cos ωt)/(2ω)`, with
  `λ = (J/Ω')²` the transfer factor and `ω = Ω'/ħ`; ★ `echo_return_ray` — **the carrier is back at
  `A` at the detuned round trip**; `senderDrift_hopTime`, `sender_rate_hopTime`,
  `receiver_rate_roundTrip` — **the plateaus**: at the detuned hop time pointer `A` has turned by
  `r_A τ (1 − λ/2)` and moves at the rate `r_A (1 − λ)`, the loss alone; at the round trip pointer
  `B` is stationary;
* `thirds`, `senderRead` (pointer `A` read in thirds), `receiverRead` (pointer `B` read on #194's
  display arc); ★★★ `emissionRecord`, `receptionRecord`, `returnRecord` — **the three writes as
  `ActualOccurrence`s on the one arena** (#191), sites `{A}`, `{B}`, `{A}`, from the start `0`,
  with write intervals and windows derived from the occupancy integrals (`emitStart`, `emitEnd`,
  `returnStart`, `returnEnd`, `senderWindow`, and #194's `writeStart`/`writeEnd`/`retention` for
  `B`), under the explicit hypotheses: both pointers ready, both rates positive, the slowness
  conditions `3 r_A λ ≤ ω` and `3 r_B λ ≤ 2ω`;
* ★★ `emission_return_disjoint` — **the return arc is disjoint from the emission arc, and the
  return record is written after the emission record**; ★★ `sender_returns`, `receiver_returns` —
  **the retention is finite for all three**; ★★★ `autonomous_echo` — the package.

## What is and is not claimed

* ⚠️ **Hamiltonian generation on `ℂℙ³ × T² × T²` is #202's second half.** This file builds the
  dynamics the Hamiltonian prescribes and proves it is a two-time, measure-preserving,
  energy-conserving flow whose pointers obey the stated equations of motion and whose ray obeys
  Schrödinger's equation with the state-dependent generator (`hasDerivAt_twoDetunedFlowVal`).
* The arc arithmetic uses the band `|D_A(t) − r_A t (1 − λ/2)| ≤ r_A λ/(4ω)` of the sender's
  displacement about its mean growth, and the record windows are where the band sits inside an arc.
  The plateaus are stated exactly but are not what the windows rest on, so the windows are valid
  for every `λ ∈ (0, 1]`, the loss entering only through the band and the mean rate.
* With `λ < 1` pointer `A` never fully stops: its rate at the hop time is `r_A (1 − λ)`. This is
  the detuning loss, read at `A`.
* No clock is in this arena. The round-trip radar read entirely from `A`'s records is #200.

References: `specs/BACKLOG.md` #199, #198, #200, #194, #191, #39; `CV/TwoSiteDetuned.lean`,
`RecordLayer/ActivatedWrite.lean` (`detuningAt`, `rateAt`, `pointerDrift`, `displayArc`,
`writeStart`, `writeEnd`, `retention`), `RecordLayer/RecordOccurrence.lean`.
-/

@[expose] public section

open MeasureTheory Set CSD.CV Projectivization Matrix.UnitaryGroup

namespace CSD.RecordLayer

open CSD.SigmaLayer

/-! ### The arena and the couplings -/

/-- **The arena of the echo**: the two-site exchange and one pointer torus per station. -/
abbrev EchoArena := FieldArena 2 2 × (LF4.KTorus × LF4.KTorus)

/-- The product instance, which instance search does not find at this depth. -/
instance : OpensMeasurableSpace EchoArena := Prod.opensMeasurableSpace

/-- The product instance, which instance search does not find at this depth. -/
instance : BorelSpace EchoArena := Prod.borelSpace

/-- A pointer coupling: a periodic `C¹` potential `f` and a strength `g`. -/
structure PointerCoupling where
  /-- The potential on the conserved angle. -/
  f : ℝ → ℝ
  /-- The coupling strength. -/
  g : ℝ
  /-- The potential is `1`-periodic. -/
  periodic : Function.Periodic f 1
  /-- The potential is `C¹`. -/
  smooth : ContDiff ℝ 1 f

/-! ### A generic Liouville step: translating one circle coordinate -/

/-- **Translating one circle coordinate by a measurable function of the other coordinates preserves
the product measure.** The fibre map over `x` is `swap ∘ (skew product of `id` with a translation)
∘ swap`, and the whole map is the skew product of `id` with those fibres. -/
theorem measurePreserving_cshift_mid {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] {c : α → β → ℝ}
    (hc : Measurable (Function.uncurry c)) :
    MeasurePreserving
      (fun z : α × (AddCircle (1 : ℝ) × β) => (z.1, (cshift (c z.1 z.2.2) z.2.1, z.2.2)))
      (μ.prod (volume.prod ν)) (μ.prod (volume.prod ν)) := by
  have hfib : ∀ x : α, MeasurePreserving
      (fun w : AddCircle (1 : ℝ) × β => (cshift (c x w.2) w.1, w.2))
      (volume.prod ν) (volume.prod ν) := by
    intro x
    have h1 : MeasurePreserving (fun w : β × AddCircle (1 : ℝ) => (w.1, cshift (c x w.1) w.2))
        (ν.prod volume) (ν.prod volume) := by
      refine (MeasurePreserving.id ν).skew_product ?_
        (ae_of_all _ fun y => (measurePreserving_cshift _).map_eq)
      show Measurable fun w : β × AddCircle (1 : ℝ) => cshift (c x w.1) w.2
      exact continuous_cshift_uncurry.measurable.comp
        ((hc.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
    have heq : (fun w : AddCircle (1 : ℝ) × β => (cshift (c x w.2) w.1, w.2))
        = Prod.swap ∘ (fun w : β × AddCircle (1 : ℝ) => (w.1, cshift (c x w.1) w.2)) ∘ Prod.swap := by
      funext w
      rfl
    rw [heq]
    exact Measure.measurePreserving_swap.comp (h1.comp Measure.measurePreserving_swap)
  refine (MeasurePreserving.id μ).skew_product ?_ (ae_of_all _ fun x => (hfib x).map_eq)
  show Measurable fun z : α × (AddCircle (1 : ℝ) × β) => (cshift (c z.1 z.2.2) z.2.1, z.2.2)
  exact (continuous_cshift_uncurry.measurable.comp
    ((hc.comp (measurable_fst.prodMk measurable_snd.snd)).prodMk measurable_snd.fst)).prodMk
    measurable_snd.snd

/-! ### The dynamics -/

section Dynamics

variable (J ħ : ℝ) (A B : PointerCoupling)

/-- The detuning at `A`: `g_A f_A(θ₂ᴬ)`. -/
noncomputable def echoDetA (x : EchoArena) : ℝ := detuningAt A.g A.periodic x.2.1.2

/-- The detuning at `B`: `g_B f_B(θ₂ᴮ)`. -/
noncomputable def echoDetB (x : EchoArena) : ℝ := detuningAt B.g B.periodic x.2.2.2

/-- **The lifted displacement of pointer `A`** after time `t`: `r_A ∫₀ᵗ n_A(p(s)) ds`. -/
noncomputable def echoAmountA (t : ℝ) (x : EchoArena) : ℝ :=
  rateAt A.g ħ A.periodic x.2.1.2 * occAccumA J ħ (echoDetA A x) (echoDetB B x) x.1 t

/-- **The lifted displacement of pointer `B`** after time `t`: `r_B ∫₀ᵗ n_B(p(s)) ds`. -/
noncomputable def echoAmountB (t : ℝ) (x : EchoArena) : ℝ :=
  rateAt B.g ħ B.periodic x.2.2.2 * occAccum J ħ (echoDetB B x - echoDetA A x) x.1 t

/-- ★ **The echo flow**: at fixed conserved angles the ray evolves by the two-site detuned exchange,
and each pointer is translated by its lifted displacement. -/
noncomputable def echoFlow (t : ℝ) : EchoArena → EchoArena := fun x =>
  ((twoDetunedFlow J ħ (echoDetA A x) (echoDetB B x)).arenaFlow t x.1,
    (pshift (echoAmountA J ħ A B t x) x.2.1, pshift (echoAmountB J ħ A B t x) x.2.2))

theorem echoFlow_fst (t : ℝ) (x : EchoArena) :
    (echoFlow J ħ A B t x).1
      = (twoDetunedFlow J ħ (echoDetA A x) (echoDetB B x)).arenaFlow t x.1 := rfl

theorem echoFlow_pointerA (t : ℝ) (x : EchoArena) :
    (echoFlow J ħ A B t x).2.1 = pshift (echoAmountA J ħ A B t x) x.2.1 := rfl

theorem echoFlow_pointerB (t : ℝ) (x : EchoArena) :
    (echoFlow J ħ A B t x).2.2 = pshift (echoAmountB J ħ A B t x) x.2.2 := rfl

/-- **Both conserved angles are conserved.** -/
theorem echoFlow_angles (t : ℝ) (x : EchoArena) :
    (echoFlow J ħ A B t x).2.1.2 = x.2.1.2 ∧ (echoFlow J ħ A B t x).2.2.2 = x.2.2.2 :=
  ⟨rfl, rfl⟩

theorem echoDetA_echoFlow (t : ℝ) (x : EchoArena) :
    echoDetA A (echoFlow J ħ A B t x) = echoDetA A x := rfl

theorem echoDetB_echoFlow (t : ℝ) (x : EchoArena) :
    echoDetB B (echoFlow J ħ A B t x) = echoDetB B x := rfl

theorem echoFlow_zero : echoFlow J ħ A B 0 = id := by
  funext x
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact FieldStructuredFlow.arenaFlow_zero' _ _
  · show pshift (echoAmountA J ħ A B 0 x) x.2.1 = x.2.1
    rw [echoAmountA, occAccumA_zero, mul_zero, pshift_zero]
  · show pshift (echoAmountB J ħ A B 0 x) x.2.2 = x.2.2
    rw [echoAmountB, occAccum_zero, mul_zero, pshift_zero]

theorem echoAmountA_add (s t : ℝ) (x : EchoArena) :
    echoAmountA J ħ A B (s + t) x
      = echoAmountA J ħ A B s x + echoAmountA J ħ A B t (echoFlow J ħ A B s x) := by
  unfold echoAmountA
  rw [echoDetA_echoFlow, echoDetB_echoFlow, echoFlow_fst, occAccumA_add, mul_add]
  rfl

theorem echoAmountB_add (s t : ℝ) (x : EchoArena) :
    echoAmountB J ħ A B (s + t) x
      = echoAmountB J ħ A B s x + echoAmountB J ħ A B t (echoFlow J ħ A B s x) := by
  unfold echoAmountB
  rw [echoDetA_echoFlow, echoDetB_echoFlow, echoFlow_fst, occAccum_twoDetuned_add, mul_add]
  rfl

/-- ★★ **The group law**: the echo flow is a one-parameter group, by the group laws of both
accumulated occupancies along the two-site flow. -/
theorem echoFlow_add (s t : ℝ) : echoFlow J ħ A B (s + t) = echoFlow J ħ A B t ∘ echoFlow J ħ A B s := by
  funext x
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show (twoDetunedFlow J ħ (echoDetA A x) (echoDetB B x)).arenaFlow (s + t) x.1
      = (twoDetunedFlow J ħ (echoDetA A x) (echoDetB B x)).arenaFlow t
          ((twoDetunedFlow J ħ (echoDetA A x) (echoDetB B x)).arenaFlow s x.1)
    rw [add_comm, FieldStructuredFlow.arenaFlow_add]
  · show pshift (echoAmountA J ħ A B (s + t) x) x.2.1
      = pshift (echoAmountA J ħ A B t (echoFlow J ħ A B s x))
          (pshift (echoAmountA J ħ A B s x) x.2.1)
    rw [pshift_add, echoAmountA_add, add_comm]
  · show pshift (echoAmountB J ħ A B (s + t) x) x.2.2
      = pshift (echoAmountB J ħ A B t (echoFlow J ħ A B s x))
          (pshift (echoAmountB J ħ A B s x) x.2.2)
    rw [pshift_add, echoAmountB_add, add_comm]

/-- **The two-time propagator**: autonomous, so only the elapsed time enters. -/
noncomputable def echoEvolve (s t : OnticTime) : EchoArena → EchoArena :=
  echoFlow J ħ A B (t - s)

theorem echoEvolve_self (t : OnticTime) : echoEvolve J ħ A B t t = id := by
  rw [echoEvolve, sub_self, echoFlow_zero]

/-- **The two-time law.** -/
theorem echoEvolve_comp (s t u : OnticTime) :
    echoEvolve J ħ A B t u ∘ echoEvolve J ħ A B s t = echoEvolve J ħ A B s u := by
  unfold echoEvolve
  rw [← echoFlow_add]
  congr 1
  ring

/-- ★ **Autonomy**: no test of `t_Σ` appears. -/
theorem echoEvolve_shift (s t a : OnticTime) :
    echoEvolve J ħ A B (s + a) (t + a) = echoEvolve J ħ A B s t := by
  unfold echoEvolve
  congr 1
  ring

/-! ### Continuity and Liouville -/

theorem continuous_echoDetA : Continuous (echoDetA A) :=
  ((continuous_detuningAt A.g A.periodic A.smooth.continuous).snd').fst'.snd'

theorem continuous_echoDetB : Continuous (echoDetB B) :=
  ((continuous_detuningAt B.g B.periodic B.smooth.continuous).snd').snd'.snd'

theorem continuous_echoAmountA (t : ℝ) : Continuous (echoAmountA J ħ A B t) := by
  unfold echoAmountA
  exact ((((continuous_rateAt A.g ħ A.periodic A.smooth).snd').fst').snd').mul
    ((continuous_echoDetA A).occAccumA (continuous_echoDetB B) continuous_fst J ħ t)

theorem continuous_echoAmountB (t : ℝ) : Continuous (echoAmountB J ħ A B t) := by
  unfold echoAmountB
  exact ((((continuous_rateAt B.g ħ B.periodic B.smooth).snd').snd').snd').mul
    (((continuous_echoDetB B).sub (continuous_echoDetA A)).occAccum continuous_fst J ħ t)

theorem continuous_echoFlow (t : ℝ) : Continuous (echoFlow J ħ A B t) := by
  unfold echoFlow FieldStructuredFlow.arenaFlow
  have hU : Continuous fun x : EchoArena =>
      (twoDetunedFlow J ħ (echoDetA A x) (echoDetB B x)).flow t :=
    (continuous_twoDetunedFlow_prod J ħ).comp₂
      ((continuous_echoDetA A).prodMk (continuous_echoDetB B)) continuous_const
  exact (hU.arenaKick continuous_fst).prodMk
    ((continuous_pshift_uncurry.comp₂ (continuous_echoAmountA J ħ A B t)
        (continuous_fst.comp continuous_snd)).prodMk
      (continuous_pshift_uncurry.comp₂ (continuous_echoAmountB J ħ A B t)
        (continuous_snd.comp continuous_snd)))

theorem measurable_echoEvolve (s t : OnticTime) : Measurable (echoEvolve J ħ A B s t) :=
  (continuous_echoFlow J ħ A B (t - s)).measurable

/-! ### The three steps of the echo flow -/

/-- The ray step: the unitary kick at fixed angles, the pointers untouched. -/
noncomputable def echoRayStep (t : ℝ) (x : EchoArena) : EchoArena :=
  ((twoDetunedFlow J ħ (echoDetA A x) (echoDetB B x)).arenaFlow t x.1, x.2)

/-- The translation of pointer `A`. -/
noncomputable def echoShiftA (t : ℝ) (x : EchoArena) : EchoArena :=
  (x.1, (pshift (echoAmountA J ħ A B t x) x.2.1, x.2.2))

/-- The translation of pointer `B`. -/
noncomputable def echoShiftB (t : ℝ) (x : EchoArena) : EchoArena :=
  (x.1, (x.2.1, pshift (echoAmountB J ħ A B t x) x.2.2))

theorem echoShiftA_fst (t : ℝ) (x : EchoArena) : (echoShiftA J ħ A B t x).1 = x.1 := rfl

theorem echoShiftB_fst (t : ℝ) (x : EchoArena) : (echoShiftB J ħ A B t x).1 = x.1 := rfl

theorem echoShiftA_pointerB (t : ℝ) (x : EchoArena) :
    (echoShiftA J ħ A B t x).2.2 = x.2.2 := rfl

theorem echoShiftB_pointerA (t : ℝ) (x : EchoArena) :
    (echoShiftB J ħ A B t x).2.1 = x.2.1 := rfl

theorem echoDetA_echoShiftA (t : ℝ) (x : EchoArena) :
    echoDetA A (echoShiftA J ħ A B t x) = echoDetA A x := rfl

theorem echoDetB_echoShiftA (t : ℝ) (x : EchoArena) :
    echoDetB B (echoShiftA J ħ A B t x) = echoDetB B x := rfl

theorem echoDetA_echoShiftB (t : ℝ) (x : EchoArena) :
    echoDetA A (echoShiftB J ħ A B t x) = echoDetA A x := rfl

theorem echoDetB_echoShiftB (t : ℝ) (x : EchoArena) :
    echoDetB B (echoShiftB J ħ A B t x) = echoDetB B x := rfl

/-- Pointer `B`'s amount is read from coordinates the translation of `A` does not touch. -/
theorem echoAmountB_echoShiftA (t : ℝ) (x : EchoArena) :
    echoAmountB J ħ A B t (echoShiftA J ħ A B t x) = echoAmountB J ħ A B t x := rfl

/-- **The echo flow is the ray step after the two translations.** -/
theorem echoFlow_eq_comp (t : ℝ) :
    echoFlow J ħ A B t = echoRayStep J ħ A B t ∘ echoShiftB J ħ A B t ∘ echoShiftA J ħ A B t := by
  funext x
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show (twoDetunedFlow J ħ (echoDetA A x) (echoDetB B x)).arenaFlow t x.1
      = (twoDetunedFlow J ħ (echoDetA A (echoShiftB J ħ A B t (echoShiftA J ħ A B t x)))
          (echoDetB B (echoShiftB J ħ A B t (echoShiftA J ħ A B t x)))).arenaFlow t
            (echoShiftB J ħ A B t (echoShiftA J ħ A B t x)).1
    rw [echoDetA_echoShiftB, echoDetA_echoShiftA, echoDetB_echoShiftB, echoDetB_echoShiftA,
      echoShiftB_fst, echoShiftA_fst]
  · show pshift (echoAmountA J ħ A B t x) x.2.1
      = (echoShiftB J ħ A B t (echoShiftA J ħ A B t x)).2.1
    rw [echoShiftB_pointerA]
    rfl
  · show pshift (echoAmountB J ħ A B t x) x.2.2
      = (echoShiftB J ħ A B t (echoShiftA J ħ A B t x)).2.2
    show pshift (echoAmountB J ħ A B t x) x.2.2
      = pshift (echoAmountB J ħ A B t (echoShiftA J ħ A B t x)) (echoShiftA J ħ A B t x).2.2
    rw [echoAmountB_echoShiftA, echoShiftA_pointerB]

set_option synthInstance.maxSize 512 in
/-- The ray step preserves the measure: a skew product over the angles of the unitary kick. -/
theorem echoRayStep_measurePreserving (t : ℝ) (p₀ : FieldArena 2 2) :
    MeasurePreserving (echoRayStep J ħ A B t) ((fsMeasure p₀).prod volume)
      ((fsMeasure p₀).prod volume) := by
  have hΔA : Continuous fun q : LF4.KTorus => detuningAt A.g A.periodic q.2 :=
    (continuous_detuningAt A.g A.periodic A.smooth.continuous).snd'
  have hΔB : Continuous fun q : LF4.KTorus => detuningAt B.g B.periodic q.2 :=
    (continuous_detuningAt B.g B.periodic B.smooth.continuous).snd'
  have hfib : ∀ q : LF4.KTorus × LF4.KTorus, MeasurePreserving
      ((twoDetunedFlow J ħ (detuningAt A.g A.periodic q.1.2)
        (detuningAt B.g B.periodic q.2.2)).arenaFlow t) (fsMeasure p₀) (fsMeasure p₀) :=
    fun q => (twoDetunedFlow J ħ _ _).arenaFlow_measurePreserving t p₀
  have hm : Measurable fun w : (LF4.KTorus × LF4.KTorus) × FieldArena 2 2 =>
      (twoDetunedFlow J ħ (detuningAt A.g A.periodic w.1.1.2)
        (detuningAt B.g B.periodic w.1.2.2)).arenaFlow t w.2 := by
    unfold FieldStructuredFlow.arenaFlow
    have hU : Continuous fun w : (LF4.KTorus × LF4.KTorus) × FieldArena 2 2 =>
        (twoDetunedFlow J ħ (detuningAt A.g A.periodic w.1.1.2)
          (detuningAt B.g B.periodic w.1.2.2)).flow t :=
      (continuous_twoDetunedFlow_prod J ħ).comp₂
        ((hΔA.comp (continuous_fst.comp continuous_fst)).prodMk
          (hΔB.comp (continuous_snd.comp continuous_fst))) continuous_const
    exact (hU.arenaKick continuous_snd).measurable
  have h : MeasurePreserving (fun w : (LF4.KTorus × LF4.KTorus) × FieldArena 2 2 =>
      (w.1, (twoDetunedFlow J ħ (detuningAt A.g A.periodic w.1.1.2)
        (detuningAt B.g B.periodic w.1.2.2)).arenaFlow t w.2))
      (volume.prod (fsMeasure p₀)) (volume.prod (fsMeasure p₀)) :=
    (MeasurePreserving.id volume).skew_product hm (ae_of_all _ fun q => (hfib q).map_eq)
  exact Measure.measurePreserving_swap.comp (h.comp Measure.measurePreserving_swap)

/-- Reassociating the two pointer tori preserves Haar. -/
theorem measurePreserving_torusAssoc :
    MeasurePreserving (MeasurableEquiv.prodAssoc :
      (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) × LF4.KTorus
        ≃ᵐ AddCircle (1 : ℝ) × (AddCircle (1 : ℝ) × LF4.KTorus)) volume volume :=
  ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩

set_option synthInstance.maxSize 512 in
/-- The translation of pointer `A` preserves the measure. -/
theorem echoShiftA_measurePreserving (t : ℝ) (p₀ : FieldArena 2 2) :
    MeasurePreserving (echoShiftA J ħ A B t) ((fsMeasure p₀).prod volume)
      ((fsMeasure p₀).prod volume) := by
  have hΔB : Continuous fun q : LF4.KTorus => detuningAt B.g B.periodic q.2 :=
    (continuous_detuningAt B.g B.periodic B.smooth.continuous).snd'
  have hm : Measurable fun z : FieldArena 2 2 × (AddCircle (1 : ℝ) × LF4.KTorus) =>
      rateAt A.g ħ A.periodic z.2.1
        * occAccumA J ħ (detuningAt A.g A.periodic z.2.1) (detuningAt B.g B.periodic z.2.2.2)
          z.1 t :=
    (((continuous_rateAt A.g ħ A.periodic A.smooth).comp
      (continuous_fst.comp continuous_snd)).mul
      (((continuous_detuningAt A.g A.periodic A.smooth.continuous).comp
        (continuous_fst.comp continuous_snd)).occAccumA
        (hΔB.comp (continuous_snd.comp continuous_snd)) continuous_fst J ħ t)).measurable
  have hmid := measurePreserving_cshift_mid (fsMeasure p₀)
    (volume : Measure (AddCircle (1 : ℝ) × LF4.KTorus))
    (c := fun (p : FieldArena 2 2) (y : AddCircle (1 : ℝ) × LF4.KTorus) =>
      rateAt A.g ħ A.periodic y.1
        * occAccumA J ħ (detuningAt A.g A.periodic y.1) (detuningAt B.g B.periodic y.2.2) p t) hm
  have heq : echoShiftA J ħ A B t = (Prod.map id MeasurableEquiv.prodAssoc.symm)
      ∘ (fun z : FieldArena 2 2 × (AddCircle (1 : ℝ) × (AddCircle (1 : ℝ) × LF4.KTorus)) =>
          (z.1, (cshift (rateAt A.g ħ A.periodic z.2.2.1
            * occAccumA J ħ (detuningAt A.g A.periodic z.2.2.1)
              (detuningAt B.g B.periodic z.2.2.2.2) z.1 t) z.2.1, z.2.2)))
      ∘ (Prod.map id MeasurableEquiv.prodAssoc) := by
    funext x
    rfl
  rw [heq]
  exact ((MeasurePreserving.id _).prod (measurePreserving_torusAssoc.symm _)).comp
    (hmid.comp ((MeasurePreserving.id _).prod measurePreserving_torusAssoc))

set_option synthInstance.maxSize 512 in
/-- The translation of pointer `B` preserves the measure. -/
theorem echoShiftB_measurePreserving (t : ℝ) (p₀ : FieldArena 2 2) :
    MeasurePreserving (echoShiftB J ħ A B t) ((fsMeasure p₀).prod volume)
      ((fsMeasure p₀).prod volume) := by
  have hΔA : Continuous fun q : LF4.KTorus => detuningAt A.g A.periodic q.2 :=
    (continuous_detuningAt A.g A.periodic A.smooth.continuous).snd'
  have heB : MeasurePreserving (fun w : LF4.KTorus × LF4.KTorus => (w.2.1, (w.2.2, w.1)))
      (volume : Measure (LF4.KTorus × LF4.KTorus)) volume :=
    measurePreserving_torusAssoc.comp Measure.measurePreserving_swap
  have heB' : MeasurePreserving
      (fun z : AddCircle (1 : ℝ) × (AddCircle (1 : ℝ) × LF4.KTorus) => (z.2.2, (z.1, z.2.1)))
      volume (volume : Measure (LF4.KTorus × LF4.KTorus)) :=
    Measure.measurePreserving_swap.comp (measurePreserving_torusAssoc.symm _)
  have hm : Measurable fun z : FieldArena 2 2 × (AddCircle (1 : ℝ) × LF4.KTorus) =>
      rateAt B.g ħ B.periodic z.2.1
        * occAccum J ħ (detuningAt B.g B.periodic z.2.1 - detuningAt A.g A.periodic z.2.2.2)
          z.1 t :=
    (((continuous_rateAt B.g ħ B.periodic B.smooth).comp
      (continuous_fst.comp continuous_snd)).mul
      ((((continuous_detuningAt B.g B.periodic B.smooth.continuous).comp
        (continuous_fst.comp continuous_snd)).sub
        (hΔA.comp (continuous_snd.comp continuous_snd))).occAccum continuous_fst J ħ t)).measurable
  have hmid := measurePreserving_cshift_mid (fsMeasure p₀)
    (volume : Measure (AddCircle (1 : ℝ) × LF4.KTorus))
    (c := fun (p : FieldArena 2 2) (y : AddCircle (1 : ℝ) × LF4.KTorus) =>
      rateAt B.g ħ B.periodic y.1
        * occAccum J ħ (detuningAt B.g B.periodic y.1 - detuningAt A.g A.periodic y.2.2) p t) hm
  have heq : echoShiftB J ħ A B t
      = (Prod.map id fun z : AddCircle (1 : ℝ) × (AddCircle (1 : ℝ) × LF4.KTorus) =>
          (z.2.2, (z.1, z.2.1)))
      ∘ (fun z : FieldArena 2 2 × (AddCircle (1 : ℝ) × (AddCircle (1 : ℝ) × LF4.KTorus)) =>
          (z.1, (cshift (rateAt B.g ħ B.periodic z.2.2.1
            * occAccum J ħ (detuningAt B.g B.periodic z.2.2.1
              - detuningAt A.g A.periodic z.2.2.2.2) z.1 t) z.2.1, z.2.2)))
      ∘ (Prod.map id fun w : LF4.KTorus × LF4.KTorus => (w.2.1, (w.2.2, w.1))) := by
    funext x
    rfl
  rw [heq]
  exact ((MeasurePreserving.id _).prod heB').comp (hmid.comp ((MeasurePreserving.id _).prod heB))

/-- ★★ **Liouville**: the echo flow preserves Fubini–Study × Haar⁴ — the ray step after the two
pointer translations, each measure-preserving. -/
theorem echoFlow_measurePreserving (t : ℝ) (p₀ : FieldArena 2 2) :
    MeasurePreserving (echoFlow J ħ A B t) ((fsMeasure p₀).prod volume)
      ((fsMeasure p₀).prod volume) := by
  rw [echoFlow_eq_comp]
  exact (echoRayStep_measurePreserving J ħ A B t p₀).comp
    ((echoShiftB_measurePreserving J ħ A B t p₀).comp (echoShiftA_measurePreserving J ħ A B t p₀))

theorem echoEvolve_measurePreserving (s t : OnticTime) (p₀ : FieldArena 2 2) :
    MeasurePreserving (echoEvolve J ħ A B s t) ((fsMeasure p₀).prod volume)
      ((fsMeasure p₀).prod volume) :=
  echoFlow_measurePreserving J ħ A B (t - s) p₀

/-! ### Energy and the equations of motion -/

/-- **The joint energy** `J⟨X⟩ + g_A f_A(θ₂ᴬ) n_A + g_B f_B(θ₂ᴮ) n_B`. -/
noncomputable def echoEnergy (x : EchoArena) : ℝ :=
  J * arenaObs hopX x.1 + echoDetA A x * momentMap x.1 excA + echoDetB B x * momentMap x.1 excB

theorem echoEnergy_eq (x : EchoArena) :
    echoEnergy J A B x = arenaObs (twoDetunedH J (echoDetA A x) (echoDetB B x)) x.1 :=
  (arenaObs_twoDetunedH _ _ _ _).symm

/-- ★★ **Energy conservation**: the joint energy is constant along the echo flow. -/
theorem echoEnergy_echoFlow (t : ℝ) (x : EchoArena) :
    echoEnergy J A B (echoFlow J ħ A B t x) = echoEnergy J A B x := by
  rw [echoEnergy_eq, echoEnergy_eq, echoDetA_echoFlow, echoDetB_echoFlow, echoFlow_fst,
    arenaObs_twoDetunedH_arenaFlow]

/-- ★★ **Pointer `A`'s equation of motion**: it turns at the rate `−(2g_A/ħ) f_A'(θ₂ᴬ) · n_A(p(t))`
— only while the carrier is at `A`. -/
theorem hasDerivAt_echoAmountA (x : EchoArena) (t : ℝ) :
    HasDerivAt (fun t => echoAmountA J ħ A B t x)
      (rateAt A.g ħ A.periodic x.2.1.2 * arenaObs occA (echoFlow J ħ A B t x).1) t :=
  (hasDerivAt_occAccumA J ħ _ _ x.1 t).const_mul _

/-- ★★ **Pointer `B`'s equation of motion**: it turns at the rate `−(2g_B/ħ) f_B'(θ₂ᴮ) · n_B(p(t))`
— only while the carrier is at `B`. -/
theorem hasDerivAt_echoAmountB (x : EchoArena) (t : ℝ) :
    HasDerivAt (fun t => echoAmountB J ħ A B t x)
      (rateAt B.g ħ B.periodic x.2.2.2 * arenaObs occB (echoFlow J ħ A B t x).1) t := by
  rw [echoFlow_fst, occB_twoDetunedFlow]
  exact (hasDerivAt_occAccum J ħ _ x.1 t).const_mul _

end Dynamics

/-! ### The two messages -/

section Messages

variable {J ħ : ℝ} (A B : PointerCoupling)

/-- The detuning difference `Δ_B − Δ_A` seen by the carrier for pointers prepared at `q_A`, `q_B`. -/
noncomputable def echoDetuning (qA qB : LF4.KTorus) : ℝ :=
  detuningAt B.g B.periodic qB.2 - detuningAt A.g A.periodic qA.2

/-- The transfer factor `λ = (J/Ω')²`. -/
noncomputable def echoLoss (J : ℝ) (qA qB : LF4.KTorus) : ℝ :=
  (J / rabiFreq J (echoDetuning A B qA qB)) ^ 2

/-- The Rabi rate `ω = Ω'/ħ` of the echo. -/
noncomputable def echoRate (J ħ : ℝ) (qA qB : LF4.KTorus) : ℝ :=
  rabiRate J ħ (echoDetuning A B qA qB)

/-- Pointer `A`'s rate `r_A = −(2g_A/ħ) f_A'(θ₂ᴬ)`. -/
noncomputable def senderRate (ħ : ℝ) (qA : LF4.KTorus) : ℝ := rateAt A.g ħ A.periodic qA.2

/-- Pointer `B`'s mean rate over a Rabi cycle, `κ_B = r_B λ`. -/
noncomputable def receiverDrift (J ħ : ℝ) (qA qB : LF4.KTorus) : ℝ :=
  rateAt B.g ħ B.periodic qB.2 * echoLoss A B J qA qB

theorem echoLoss_pos (hJ : 0 < J) (qA qB : LF4.KTorus) : 0 < echoLoss A B J qA qB :=
  div_rabiFreq_sq_pos hJ _

theorem echoLoss_le_one (hJ : 0 < J) (qA qB : LF4.KTorus) : echoLoss A B J qA qB ≤ 1 :=
  div_rabiFreq_sq_le_one hJ _

theorem echoRate_pos (hJ : 0 < J) (hħ : 0 < ħ) (qA qB : LF4.KTorus) :
    0 < echoRate A B J ħ qA qB :=
  rabiRate_pos hJ hħ _

/-- **Message `0` fixes the whole arena point**: the vacuum never moves and neither pointer turns. -/
theorem echoFlow_msgPoint_zero (hJ : 0 < J) (qA qB : LF4.KTorus) (t : ℝ) :
    echoFlow J ħ A B t (msgPoint 0, (qA, qB)) = (msgPoint 0, (qA, qB)) := by
  unfold echoFlow echoAmountA echoAmountB
  simp only [twoDetunedFlow_msgPoint_zero hJ, occAccumA_msgPoint_zero hJ, occAccum_msgPoint_zero hJ,
    mul_zero, pshift_zero]

/-- The sender's displacement for message `1`: `r (t − λ (ωt − sin ωt cos ωt)/(2ω))`. -/
noncomputable def senderDrift (r l ω t : ℝ) : ℝ :=
  r * (t - l * (ω * t - Real.sin (ω * t) * Real.cos (ω * t)) / (2 * ω))

theorem senderDrift_eq (r l ω t : ℝ) : senderDrift r l ω t = r * t - pointerDrift (r * l) ω t := by
  unfold senderDrift pointerDrift
  ring

/-- ★★★ **Pointer `A`'s displacement for message `1`**, in closed form. -/
theorem echoAmountA_msgPoint_one (hJ : 0 < J) (hħ : 0 < ħ) (qA qB : LF4.KTorus) (t : ℝ) :
    echoAmountA J ħ A B t (msgPoint 1, (qA, qB))
      = senderDrift (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) t := by
  unfold echoAmountA senderDrift senderRate echoLoss echoRate echoDetuning echoDetA echoDetB
  dsimp only
  rw [occAccumA_msgPoint_one, occAccum_msgPoint_one hJ hħ, rabiAngle]

/-- ★★★ **Pointer `B`'s displacement for message `1`**, in closed form: #194's drift with
`κ_B = r_B λ`. -/
theorem echoAmountB_msgPoint_one (hJ : 0 < J) (hħ : 0 < ħ) (qA qB : LF4.KTorus) (t : ℝ) :
    echoAmountB J ħ A B t (msgPoint 1, (qA, qB))
      = pointerDrift (receiverDrift A B J ħ qA qB) (echoRate A B J ħ qA qB) t := by
  unfold echoAmountB pointerDrift receiverDrift echoLoss echoRate echoDetuning echoDetA echoDetB
  dsimp only
  rw [occAccum_msgPoint_one hJ hħ, rabiAngle]
  ring

theorem echoFlow_msgPoint_one_pointerA (hJ : 0 < J) (hħ : 0 < ħ) (qA qB : LF4.KTorus) (t : ℝ) :
    (echoFlow J ħ A B t (msgPoint 1, (qA, qB))).2.1
      = pshift (senderDrift (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) t)
          qA := by
  rw [echoFlow_pointerA, echoAmountA_msgPoint_one A B hJ hħ]

theorem echoFlow_msgPoint_one_pointerB (hJ : 0 < J) (hħ : 0 < ħ) (qA qB : LF4.KTorus) (t : ℝ) :
    (echoFlow J ħ A B t (msgPoint 1, (qA, qB))).2.2
      = pshift (pointerDrift (receiverDrift A B J ħ qA qB) (echoRate A B J ħ qA qB) t) qB := by
  rw [echoFlow_pointerB, echoAmountB_msgPoint_one A B hJ hħ]

/-- ★ **The carrier is back at `A`** at the detuned round trip, as a ray. -/
theorem echo_return_ray (hJ : 0 < J) (hħ : 0 < ħ) (qA qB : LF4.KTorus) :
    (echoFlow J ħ A B (detunedRoundTrip J ħ (echoDetuning A B qA qB)) (msgPoint 1, (qA, qB))).1
      = msgPoint 1 :=
  twoDetuned_return hJ hħ _ _

/-! ### The plateaus -/

/-- At the detuned hop time pointer `A` has turned by `r_A τ (1 − λ/2)`. -/
theorem senderDrift_hopTime (hJ : 0 < J) (hħ : 0 < ħ) (r : ℝ) (qA qB : LF4.KTorus) :
    senderDrift r (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
        (detunedHopTime J ħ (echoDetuning A B qA qB))
      = r * detunedHopTime J ħ (echoDetuning A B qA qB) * (1 - echoLoss A B J qA qB / 2) := by
  have hθ : echoRate A B J ħ qA qB * detunedHopTime J ħ (echoDetuning A B qA qB) = Real.pi / 2 :=
    rabiAngle_detunedHopTime hJ hħ _
  have hω := (echoRate_pos A B hJ hħ qA qB).ne'
  unfold senderDrift
  rw [hθ, Real.sin_pi_div_two, Real.cos_pi_div_two, mul_zero, sub_zero]
  have h2 : Real.pi / 2 = echoRate A B J ħ qA qB * detunedHopTime J ħ (echoDetuning A B qA qB) :=
    hθ.symm
  rw [h2]
  field_simp

/-- **The sender's plateau**: at the detuned hop time pointer `A` moves at the rate `r_A (1 − λ)` —
the loss alone; at zero detuning it is stationary while the carrier is at `B`. -/
theorem sender_rate_hopTime (hJ : 0 < J) (hħ : 0 < ħ) (qA qB : LF4.KTorus) :
    HasDerivAt (fun t => echoAmountA J ħ A B t (msgPoint 1, (qA, qB)))
      (senderRate A ħ qA * (1 - echoLoss A B J qA qB))
      (detunedHopTime J ħ (echoDetuning A B qA qB)) := by
  have h := hasDerivAt_echoAmountA J ħ A B (msgPoint 1, (qA, qB))
    (detunedHopTime J ħ (echoDetuning A B qA qB))
  rw [echoFlow_fst] at h
  have hocc : arenaObs occA ((twoDetunedFlow J ħ (echoDetA A (msgPoint 1, (qA, qB)))
      (echoDetB B (msgPoint 1, (qA, qB)))).arenaFlow (detunedHopTime J ħ (echoDetuning A B qA qB))
        (msgPoint 1)) = 1 - echoLoss A B J qA qB := by
    rw [twoDetuned_readout_A_one hJ]
    unfold echoLoss echoDetuning echoDetA echoDetB
    dsimp only
    rw [rabiAngle_detunedHopTime hJ hħ, Real.sin_pi_div_two, one_pow, mul_one]
  rw [hocc] at h
  exact h

/-- **The receiver's plateau**: at the detuned round trip pointer `B` is stationary — the carrier is
back at `A`. -/
theorem receiver_rate_roundTrip (hJ : 0 < J) (hħ : 0 < ħ) (qA qB : LF4.KTorus) :
    HasDerivAt (fun t => echoAmountB J ħ A B t (msgPoint 1, (qA, qB))) 0
      (detunedRoundTrip J ħ (echoDetuning A B qA qB)) := by
  have h := hasDerivAt_echoAmountB J ħ A B (msgPoint 1, (qA, qB))
    (detunedRoundTrip J ħ (echoDetuning A B qA qB))
  rw [echo_return_ray A B hJ hħ, arenaObs_occB_msgPoint_one, mul_zero] at h
  exact h

end Messages

/-! ### Bounds on the sender's drift -/

theorem senderDrift_nonneg {r l ω : ℝ} (hr : 0 ≤ r) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hω : 0 < ω)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ senderDrift r l ω t := by
  rw [senderDrift_eq]
  have h := pointerDrift_le (mul_nonneg hr hl0) hω ht
  nlinarith [mul_nonneg hr ht, mul_nonneg (mul_nonneg hr ht) (sub_nonneg.2 hl1)]

theorem senderDrift_le {r l ω : ℝ} (hr : 0 ≤ r) (hl0 : 0 ≤ l) (hω : 0 < ω) {t : ℝ} (ht : 0 ≤ t) :
    senderDrift r l ω t ≤ r * t := by
  rw [senderDrift_eq]
  linarith [pointerDrift_nonneg (mul_nonneg hr hl0) hω ht]

/-- The band about the mean growth: `r (t (1 − λ/2) − λ/(4ω)) ≤ D_A(t)`. -/
theorem senderDrift_lower {r l ω : ℝ} (hr : 0 ≤ r) (hl0 : 0 ≤ l) (hω : 0 < ω) (t : ℝ) :
    r * (t * (1 - l / 2) - l / (4 * ω)) ≤ senderDrift r l ω t := by
  unfold senderDrift
  refine mul_le_mul_of_nonneg_left ?_ hr
  have h := (abs_le.mp (abs_sin_mul_cos_le_half (ω * t))).1
  have key : t - l * (ω * t - Real.sin (ω * t) * Real.cos (ω * t)) / (2 * ω)
      - (t * (1 - l / 2) - l / (4 * ω))
      = l / (2 * ω) * (Real.sin (ω * t) * Real.cos (ω * t) + 1 / 2) := by
    field_simp
    ring
  have : 0 ≤ l / (2 * ω) * (Real.sin (ω * t) * Real.cos (ω * t) + 1 / 2) :=
    mul_nonneg (by positivity) (by linarith)
  linarith

/-- The band about the mean growth: `D_A(t) ≤ r (t (1 − λ/2) + λ/(4ω))`. -/
theorem senderDrift_upper {r l ω : ℝ} (hr : 0 ≤ r) (hl0 : 0 ≤ l) (hω : 0 < ω) (t : ℝ) :
    senderDrift r l ω t ≤ r * (t * (1 - l / 2) + l / (4 * ω)) := by
  unfold senderDrift
  refine mul_le_mul_of_nonneg_left ?_ hr
  have h := (abs_le.mp (abs_sin_mul_cos_le_half (ω * t))).2
  have key : (t * (1 - l / 2) + l / (4 * ω))
      - (t - l * (ω * t - Real.sin (ω * t) * Real.cos (ω * t)) / (2 * ω))
      = l / (2 * ω) * (1 / 2 - Real.sin (ω * t) * Real.cos (ω * t)) := by
    field_simp
    ring
  have : 0 ≤ l / (2 * ω) * (1 / 2 - Real.sin (ω * t) * Real.cos (ω * t)) :=
    mul_nonneg (by positivity) (by linarith)
  linarith

theorem continuous_senderDrift (r l ω : ℝ) : Continuous (senderDrift r l ω) := by
  unfold senderDrift
  fun_prop

/-! ### The sender's write intervals -/

/-- The sender's mean rate `r (1 − λ/2)`. -/
noncomputable def meanRate (r l : ℝ) : ℝ := r * (1 - l / 2)

/-- The half-width `r λ/(4ω)` of the band about the mean growth. -/
noncomputable def band (r l ω : ℝ) : ℝ := r * l / (4 * ω)

/-- The emission write begins: `1/(6 r)`. -/
noncomputable def emitStart (r : ℝ) : ℝ := 1 / (6 * r)

/-- The emission write ends: the mean growth reaches `1/3` plus the band. -/
noncomputable def emitEnd (r l ω : ℝ) : ℝ := (1 / 3 + band r l ω) / meanRate r l

/-- The return write begins: `1/(2 r)`. -/
noncomputable def returnStart (r : ℝ) : ℝ := 1 / (2 * r)

/-- The return write ends: the mean growth reaches `2/3` plus the band. -/
noncomputable def returnEnd (r l ω : ℝ) : ℝ := (2 / 3 + band r l ω) / meanRate r l

/-- The sender's retention window: `(1/6 − 2 band)/meanRate`. -/
noncomputable def senderWindow (r l ω : ℝ) : ℝ := (1 / 6 - 2 * band r l ω) / meanRate r l

theorem meanRate_pos {r l : ℝ} (hr : 0 < r) (hl : l ≤ 1) : 0 < meanRate r l := by
  unfold meanRate
  nlinarith

theorem meanRate_le {r l : ℝ} (hr : 0 ≤ r) (hl : 0 ≤ l) : meanRate r l ≤ r := by
  unfold meanRate
  nlinarith

theorem band_nonneg {r l ω : ℝ} (hr : 0 ≤ r) (hl : 0 ≤ l) (hω : 0 < ω) : 0 ≤ band r l ω := by
  unfold band
  positivity

/-- The slowness condition `3 r λ ≤ ω` is exactly `band ≤ 1/12`. -/
theorem band_le {r l ω : ℝ} (hω : 0 < ω) (hslow : 3 * (r * l) ≤ ω) : band r l ω ≤ 1 / 12 := by
  unfold band
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

theorem meanRate_mul_emitEnd {r l ω : ℝ} (hr : 0 < r) (hl : l ≤ 1) :
    meanRate r l * emitEnd r l ω = 1 / 3 + band r l ω := by
  unfold emitEnd
  have := (meanRate_pos hr hl).ne'
  field_simp

theorem meanRate_mul_returnEnd {r l ω : ℝ} (hr : 0 < r) (hl : l ≤ 1) :
    meanRate r l * returnEnd r l ω = 2 / 3 + band r l ω := by
  unfold returnEnd
  have := (meanRate_pos hr hl).ne'
  field_simp

theorem meanRate_mul_senderWindow {r l ω : ℝ} (hr : 0 < r) (hl : l ≤ 1) :
    meanRate r l * senderWindow r l ω = 1 / 6 - 2 * band r l ω := by
  unfold senderWindow
  have := (meanRate_pos hr hl).ne'
  field_simp

theorem senderWindow_nonneg {r l ω : ℝ} (hr : 0 < r) (hl : l ≤ 1) (hω : 0 < ω)
    (hslow : 3 * (r * l) ≤ ω) : 0 ≤ senderWindow r l ω := by
  unfold senderWindow
  have := band_le hω hslow
  exact div_nonneg (by linarith) (meanRate_pos hr hl).le

theorem emitStart_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ emitStart r := by
  unfold emitStart
  positivity

theorem returnStart_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ returnStart r := by
  unfold returnStart
  positivity

theorem emitStart_le_emitEnd {r l ω : ℝ} (hr : 0 < r) (hl0 : 0 ≤ l) (hl : l ≤ 1) (hω : 0 < ω) :
    emitStart r ≤ emitEnd r l ω := by
  unfold emitStart emitEnd
  rw [div_le_div_iff₀ (by positivity) (meanRate_pos hr hl)]
  have h1 := meanRate_le hr.le hl0
  have h2 := band_nonneg hr.le hl0 hω
  nlinarith

theorem returnStart_le_returnEnd {r l ω : ℝ} (hr : 0 < r) (hl0 : 0 ≤ l) (hl : l ≤ 1) (hω : 0 < ω) :
    returnStart r ≤ returnEnd r l ω := by
  unfold returnStart returnEnd
  rw [div_le_div_iff₀ (by positivity) (meanRate_pos hr hl)]
  have h1 := meanRate_le hr.le hl0
  have h2 := band_nonneg hr.le hl0 hω
  nlinarith

/-- **The emission record is written before the return record.** -/
theorem emitEnd_add_window_lt_returnEnd {r l ω : ℝ} (hr : 0 < r) (hl0 : 0 ≤ l) (hl : l ≤ 1)
    (hω : 0 < ω) (hslow : 3 * (r * l) ≤ ω) :
    emitEnd r l ω + senderWindow r l ω < returnEnd r l ω := by
  have hμ := meanRate_pos hr hl
  have hb := band_le hω hslow
  have hb0 := band_nonneg hr.le hl0 hω
  refine lt_of_mul_lt_mul_left ?_ hμ.le
  rw [mul_add, meanRate_mul_emitEnd hr hl, meanRate_mul_senderWindow hr hl,
    meanRate_mul_returnEnd hr hl]
  linarith

/-- **Through the emission window the sender's displacement lies in `[1/3, 1/2]`.** -/
theorem senderDrift_mem_emit {r l ω : ℝ} (hr : 0 < r) (hl0 : 0 ≤ l) (hl : l ≤ 1) (hω : 0 < ω)
    {t : ℝ} (ht₁ : emitEnd r l ω ≤ t) (ht₂ : t ≤ emitEnd r l ω + senderWindow r l ω) :
    1 / 3 ≤ senderDrift r l ω t ∧ senderDrift r l ω t ≤ 1 / 2 := by
  have hμ := meanRate_pos hr hl
  have hlow := senderDrift_lower hr.le hl0 hω t
  have hup := senderDrift_upper hr.le hl0 hω t
  have e1 : r * (t * (1 - l / 2) - l / (4 * ω)) = meanRate r l * t - band r l ω := by
    unfold meanRate band
    ring
  have e2 : r * (t * (1 - l / 2) + l / (4 * ω)) = meanRate r l * t + band r l ω := by
    unfold meanRate band
    ring
  rw [e1] at hlow
  rw [e2] at hup
  have h1 := mul_le_mul_of_nonneg_left ht₁ hμ.le
  have h2 := mul_le_mul_of_nonneg_left ht₂ hμ.le
  rw [meanRate_mul_emitEnd hr hl] at h1
  rw [mul_add, meanRate_mul_emitEnd hr hl, meanRate_mul_senderWindow hr hl] at h2
  constructor <;> linarith

/-- **Through the return window the sender's displacement lies in `[2/3, 5/6]`.** -/
theorem senderDrift_mem_return {r l ω : ℝ} (hr : 0 < r) (hl0 : 0 ≤ l) (hl : l ≤ 1) (hω : 0 < ω)
    {t : ℝ} (ht₁ : returnEnd r l ω ≤ t) (ht₂ : t ≤ returnEnd r l ω + senderWindow r l ω) :
    2 / 3 ≤ senderDrift r l ω t ∧ senderDrift r l ω t ≤ 5 / 6 := by
  have hμ := meanRate_pos hr hl
  have hlow := senderDrift_lower hr.le hl0 hω t
  have hup := senderDrift_upper hr.le hl0 hω t
  have e1 : r * (t * (1 - l / 2) - l / (4 * ω)) = meanRate r l * t - band r l ω := by
    unfold meanRate band
    ring
  have e2 : r * (t * (1 - l / 2) + l / (4 * ω)) = meanRate r l * t + band r l ω := by
    unfold meanRate band
    ring
  rw [e1] at hlow
  rw [e2] at hup
  have h1 := mul_le_mul_of_nonneg_left ht₁ hμ.le
  have h2 := mul_le_mul_of_nonneg_left ht₂ hμ.le
  rw [meanRate_mul_returnEnd hr hl] at h1
  rw [mul_add, meanRate_mul_returnEnd hr hl, meanRate_mul_senderWindow hr hl] at h2
  constructor <;> linarith

/-! ### The readouts -/

/-- A real number read in thirds: `0` on `(−∞, 1/3]`, `1` on `(1/3, 2/3]`, `2` above. -/
noncomputable def thirds (r : ℝ) : Fin 3 := if r ≤ 1 / 3 then 0 else if r ≤ 2 / 3 then 1 else 2

theorem measurable_thirds : Measurable thirds := by
  unfold thirds
  exact Measurable.ite measurableSet_Iic measurable_const
    (Measurable.ite measurableSet_Iic measurable_const measurable_const)

theorem thirds_eq_zero {r : ℝ} (h : r ≤ 1 / 3) : thirds r = 0 := by
  unfold thirds
  exact ite_eq_left h

theorem thirds_eq_one {r : ℝ} (h1 : 1 / 3 < r) (h2 : r ≤ 2 / 3) : thirds r = 1 := by
  unfold thirds
  rw [ite_eq_right (not_le.2 h1)]
  exact ite_eq_left h2

theorem thirds_eq_two {r : ℝ} (h : 2 / 3 < r) : thirds r = 2 := by
  have h' : ¬ r ≤ 1 / 3 := by linarith
  unfold thirds
  rw [ite_eq_right h', ite_eq_right (not_le.2 h)]

/-- **Pointer `A` read in thirds**: `0` ready, `1` emitted, `2` returned. -/
noncomputable def senderRead (x : EchoArena) : Fin 3 := thirds (rep x.2.1.1)

theorem measurable_senderRead : Measurable senderRead :=
  measurable_thirds.comp (measurable_rep.comp measurable_snd.fst.fst)

open Classical in
/-- **Pointer `B` read on #194's display arc.** -/
noncomputable def receiverRead (x : EchoArena) : Bool := if x.2.2 ∈ displayArc then true else false

theorem measurable_receiverRead : Measurable receiverRead := by
  unfold receiverRead
  exact Measurable.ite (measurable_snd.snd measurableSet_displayArc) measurable_const
    measurable_const

theorem receiverRead_eq_true {x : EchoArena} (hx : x.2.2 ∈ displayArc) : receiverRead x = true := by
  unfold receiverRead
  exact ite_eq_left hx

theorem receiverRead_eq_false {x : EchoArena} (hx : x.2.2 ∉ displayArc) :
    receiverRead x = false := by
  unfold receiverRead
  exact ite_eq_right hx

/-- Both pointers ready. -/
def echoReady : Set EchoArena := {x | x.2.1 ∈ readyArc 2 ∧ x.2.2 ∈ readyArc 2}

theorem measurableSet_echoReady : MeasurableSet echoReady :=
  (measurable_snd.fst measurableSet_readyArc).inter (measurable_snd.snd measurableSet_readyArc)

/-! ### Reading the pointers after a shift from the ready arc -/

/-- A shift by `D ∈ [0, 5/6]` of a ready pointer keeps its representative at `rep q + D`. -/
theorem rep_pshift_of_ready {q : LF4.KTorus} (hq : q ∈ readyArc 2) {D : ℝ} (h0 : 0 ≤ D)
    (h1 : D ≤ 5 / 6) : rep (pshift D q).1 = rep q.1 + D := by
  have hr : rep q.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hq
  rw [shearWidth_two] at hr
  exact rep_pshift_of_mem _ _ ⟨by linarith [hr.1], by linarith [hr.2]⟩

theorem thirds_pshift_ready_zero {q : LF4.KTorus} (hq : q ∈ readyArc 2) {D : ℝ} (h0 : 0 ≤ D)
    (h1 : D ≤ 1 / 6) : thirds (rep (pshift D q).1) = 0 := by
  have hr : rep q.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hq
  rw [shearWidth_two] at hr
  rw [rep_pshift_of_ready hq h0 (by linarith)]
  exact thirds_eq_zero (by linarith [hr.2])

theorem thirds_pshift_ready_one {q : LF4.KTorus} (hq : q ∈ readyArc 2) {D : ℝ} (h0 : 1 / 3 ≤ D)
    (h1 : D ≤ 1 / 2) : thirds (rep (pshift D q).1) = 1 := by
  have hr : rep q.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hq
  rw [shearWidth_two] at hr
  rw [rep_pshift_of_ready hq (by linarith) (by linarith)]
  exact thirds_eq_one (by linarith [hr.1]) (by linarith [hr.2])

theorem thirds_pshift_ready_two {q : LF4.KTorus} (hq : q ∈ readyArc 2) {D : ℝ} (h0 : 2 / 3 ≤ D)
    (h1 : D ≤ 5 / 6) : thirds (rep (pshift D q).1) = 2 := by
  have hr : rep q.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hq
  rw [shearWidth_two] at hr
  rw [rep_pshift_of_ready hq (by linarith) h1]
  exact thirds_eq_two (by linarith [hr.1])

theorem thirds_pshift_ready_ne_two {q : LF4.KTorus} (hq : q ∈ readyArc 2) {D : ℝ} (h0 : 0 ≤ D)
    (h1 : D ≤ 1 / 2) : thirds (rep (pshift D q).1) ≠ 2 := by
  have hr : rep q.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hq
  rw [shearWidth_two] at hr
  rw [rep_pshift_of_ready hq h0 (by linarith)]
  by_cases h : rep q.1 + D ≤ 1 / 3
  · rw [thirds_eq_zero h]
    decide
  · rw [thirds_eq_one (not_le.1 h) (by linarith [hr.2])]
    decide

/-- #194's display-arc test, for a bare pointer: before the write interval the drifted pointer is
not displayed. -/
theorem pshift_pointerDrift_notMem_displayArc {q : LF4.KTorus} (hq : q ∈ readyArc 2) {κ ω : ℝ}
    (hκ : 0 < κ) (hω : 0 < ω) {t : ℝ} (ht0 : 0 ≤ t) (ht : t < writeStart κ) :
    pshift (pointerDrift κ ω t) q ∉ displayArc := by
  have hD0 := pointerDrift_nonneg hκ.le hω ht0
  have hD1 : pointerDrift κ ω t < 1 / 6 := by
    calc pointerDrift κ ω t ≤ κ * t := pointerDrift_le hκ.le hω ht0
      _ < κ * writeStart κ := mul_lt_mul_of_pos_left ht hκ
      _ = 1 / 6 := mul_writeStart hκ
  have hr : rep q.1 ∈ Ioc (0 : ℝ) (shearWidth 2) := hq
  rw [shearWidth_two] at hr
  intro hd
  change rep (pshift (pointerDrift κ ω t) q).1 ∈ Ioc (2 * shearWidth 2) (1 - shearWidth 2) at hd
  rw [shearWidth_two, rep_pshift_of_mem _ _ ⟨by linarith [hr.1], by linarith [hr.2]⟩] at hd
  linarith [hd.1, hr.2]

/-- #194's display-arc test, for a bare pointer: through the window the drifted pointer is
displayed. -/
theorem pshift_pointerDrift_mem_displayArc {q : LF4.KTorus} (hq : q ∈ readyArc 2) {κ ω : ℝ}
    (hκ : 0 < κ) (hω : 0 < ω) {t : ℝ} (ht₁ : writeEnd κ ω ≤ t)
    (ht₂ : t ≤ writeEnd κ ω + retention κ ω) : pshift (pointerDrift κ ω t) q ∈ displayArc := by
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
  change rep (pshift (pointerDrift κ ω t) q).1 ∈ Ioc (2 * shearWidth 2) (1 - shearWidth 2)
  rw [shearWidth_two, rep_pshift_of_mem _ _ ⟨by linarith [hr.1], by linarith [hr.2]⟩]
  constructor <;> linarith [hr.1, hr.2]

/-! ### The three writes -/

section Writes

variable {J ħ : ℝ} (A B : PointerCoupling) {qA qB : LF4.KTorus}

/-- ★★ **Before the emission write pointer `A` reads `0`.** -/
theorem sender_before_emit (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hr : 0 < senderRate A ħ qA) (qB : LF4.KTorus) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < emitStart (senderRate A ħ qA)) :
    senderRead (echoFlow J ħ A B t (msgPoint 1, (qA, qB))) = 0 := by
  unfold senderRead
  rw [echoFlow_msgPoint_one_pointerA A B hJ hħ]
  have hl0 := (echoLoss_pos A B hJ qA qB).le
  have hl1 := echoLoss_le_one A B hJ qA qB
  have hω := echoRate_pos A B hJ hħ qA qB
  have hD0 := senderDrift_nonneg hr.le hl0 hl1 hω ht0
  have hD1 : senderDrift (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) t
      ≤ 1 / 6 := by
    refine (senderDrift_le hr.le hl0 hω ht0).trans ?_
    have hE : senderRate A ħ qA * emitStart (senderRate A ħ qA) = 1 / 6 := by
      unfold emitStart
      field_simp
    have := mul_lt_mul_of_pos_left ht hr
    rw [hE] at this
    linarith
  exact thirds_pshift_ready_zero hqA hD0 hD1

/-- ★★ **Through the emission window pointer `A` reads `1`.** -/
theorem sender_emitted (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hr : 0 < senderRate A ħ qA) (qB : LF4.KTorus) {t : ℝ}
    (ht₁ : emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) ≤ t)
    (ht₂ : t ≤ emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
      + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)) :
    senderRead (echoFlow J ħ A B t (msgPoint 1, (qA, qB))) = 1 := by
  unfold senderRead
  rw [echoFlow_msgPoint_one_pointerA A B hJ hħ]
  obtain ⟨h0, h1⟩ := senderDrift_mem_emit hr (echoLoss_pos A B hJ qA qB).le
    (echoLoss_le_one A B hJ qA qB) (echoRate_pos A B hJ hħ qA qB) ht₁ ht₂
  exact thirds_pshift_ready_one hqA h0 h1

/-- ★★ **Before the return write pointer `A` does not read `2`.** -/
theorem sender_before_return (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hr : 0 < senderRate A ħ qA) (qB : LF4.KTorus) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < returnStart (senderRate A ħ qA)) :
    senderRead (echoFlow J ħ A B t (msgPoint 1, (qA, qB))) ≠ 2 := by
  unfold senderRead
  rw [echoFlow_msgPoint_one_pointerA A B hJ hħ]
  have hl0 := (echoLoss_pos A B hJ qA qB).le
  have hl1 := echoLoss_le_one A B hJ qA qB
  have hω := echoRate_pos A B hJ hħ qA qB
  have hD0 := senderDrift_nonneg hr.le hl0 hl1 hω ht0
  have hD1 : senderDrift (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) t
      ≤ 1 / 2 := by
    refine (senderDrift_le hr.le hl0 hω ht0).trans ?_
    have hE : senderRate A ħ qA * returnStart (senderRate A ħ qA) = 1 / 2 := by
      unfold returnStart
      field_simp
    have := mul_lt_mul_of_pos_left ht hr
    rw [hE] at this
    linarith
  exact thirds_pshift_ready_ne_two hqA hD0 hD1

/-- ★★ **Through the return window pointer `A` reads `2`.** -/
theorem sender_returned (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hr : 0 < senderRate A ħ qA) (qB : LF4.KTorus) {t : ℝ}
    (ht₁ : returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) ≤ t)
    (ht₂ : t ≤ returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
      + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)) :
    senderRead (echoFlow J ħ A B t (msgPoint 1, (qA, qB))) = 2 := by
  unfold senderRead
  rw [echoFlow_msgPoint_one_pointerA A B hJ hħ]
  obtain ⟨h0, h1⟩ := senderDrift_mem_return hr (echoLoss_pos A B hJ qA qB).le
    (echoLoss_le_one A B hJ qA qB) (echoRate_pos A B hJ hħ qA qB) ht₁ ht₂
  exact thirds_pshift_ready_two hqA h0 h1

/-- ★★ **Before the reception write pointer `B` is not displayed.** -/
theorem receiver_before (hJ : 0 < J) (hħ : 0 < ħ) (qA : LF4.KTorus) (hqB : qB ∈ readyArc 2)
    (hκ : 0 < receiverDrift A B J ħ qA qB) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < writeStart (receiverDrift A B J ħ qA qB)) :
    receiverRead (echoFlow J ħ A B t (msgPoint 1, (qA, qB))) = false := by
  apply receiverRead_eq_false
  rw [echoFlow_msgPoint_one_pointerB A B hJ hħ]
  exact pshift_pointerDrift_notMem_displayArc hqB hκ (echoRate_pos A B hJ hħ qA qB) ht0 ht

/-- ★★ **Through the reception window pointer `B` is displayed.** -/
theorem receiver_received (hJ : 0 < J) (hħ : 0 < ħ) (qA : LF4.KTorus) (hqB : qB ∈ readyArc 2)
    (hκ : 0 < receiverDrift A B J ħ qA qB) {t : ℝ}
    (ht₁ : writeEnd (receiverDrift A B J ħ qA qB) (echoRate A B J ħ qA qB) ≤ t)
    (ht₂ : t ≤ writeEnd (receiverDrift A B J ħ qA qB) (echoRate A B J ħ qA qB)
      + retention (receiverDrift A B J ħ qA qB) (echoRate A B J ħ qA qB)) :
    receiverRead (echoFlow J ħ A B t (msgPoint 1, (qA, qB))) = true := by
  apply receiverRead_eq_true
  rw [echoFlow_msgPoint_one_pointerB A B hJ hħ]
  exact pshift_pointerDrift_mem_displayArc hqB hκ (echoRate_pos A B hJ hħ qA qB) ht₁ ht₂

/-- ★★★ **The emission record**: pointer `A`'s first arc, written by the carrier as it leaves —
an `ActualOccurrence` at site `{A}` from the start `0`, value `1`, write interval
`[1/(6 r_A), emitEnd]`, window `senderWindow`. -/
noncomputable def emissionRecord (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hr : 0 < senderRate A ħ qA)
    (hslow : 3 * (senderRate A ħ qA * echoLoss A B J qA qB) ≤ echoRate A B J ħ qA qB) :
    ActualOccurrence EchoArena (Fin 3) 2 where
  evolve := echoEvolve J ħ A B
  evolve_self := echoEvolve_self J ħ A B
  evolve_comp := echoEvolve_comp J ħ A B
  measurable_evolve := measurable_echoEvolve J ħ A B
  readout := senderRead
  measurable_readout := measurable_senderRead
  ready := echoReady
  measurableSet_ready := measurableSet_echoReady
  prep := (msgPoint 1, (qA, qB))
  prep_mem := ⟨hqA, hqB⟩
  site := {0}
  start := 0
  value := 1
  writeStart := emitStart (senderRate A ħ qA)
  writeEnd := emitEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
  window := senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
  isWrite :=
    { start_le := emitStart_nonneg hr
      interval := emitStart_le_emitEnd hr (echoLoss_pos A B hJ qA qB).le
        (echoLoss_le_one A B hJ qA qB) (echoRate_pos A B hJ hħ qA qB)
      window_nonneg := senderWindow_nonneg hr (echoLoss_le_one A B hJ qA qB)
        (echoRate_pos A B hJ hħ qA qB) hslow
      before := fun t ht0 ht => by
        show senderRead (echoFlow J ħ A B (t - 0) (msgPoint 1, (qA, qB))) ≠ 1
        rw [sub_zero, sender_before_emit A B hJ hħ hqA hr qB ht0 ht]
        decide
      holds := fun t ht₁ ht₂ => by
        show senderRead (echoFlow J ħ A B (t - 0) (msgPoint 1, (qA, qB))) = 1
        rw [sub_zero]
        exact sender_emitted A B hJ hħ hqA hr qB ht₁ ht₂ }

/-- ★★★ **The reception record**: pointer `B`'s arc, #194's write on the echo arena — an
`ActualOccurrence` at site `{B}`, value `true`, write interval `[1/(6κ_B), 2/(3κ_B) + 1/(2ω)]`,
window `2/(3κ_B) − 1/ω`. -/
noncomputable def receptionRecord (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hκ : 0 < receiverDrift A B J ħ qA qB)
    (hslow : 3 * receiverDrift A B J ħ qA qB ≤ 2 * echoRate A B J ħ qA qB) :
    ActualOccurrence EchoArena Bool 2 where
  evolve := echoEvolve J ħ A B
  evolve_self := echoEvolve_self J ħ A B
  evolve_comp := echoEvolve_comp J ħ A B
  measurable_evolve := measurable_echoEvolve J ħ A B
  readout := receiverRead
  measurable_readout := measurable_receiverRead
  ready := echoReady
  measurableSet_ready := measurableSet_echoReady
  prep := (msgPoint 1, (qA, qB))
  prep_mem := ⟨hqA, hqB⟩
  site := {1}
  start := 0
  value := true
  writeStart := writeStart (receiverDrift A B J ħ qA qB)
  writeEnd := writeEnd (receiverDrift A B J ħ qA qB) (echoRate A B J ħ qA qB)
  window := retention (receiverDrift A B J ħ qA qB) (echoRate A B J ħ qA qB)
  isWrite :=
    { start_le := writeStart_nonneg hκ
      interval := writeStart_le_writeEnd hκ (echoRate_pos A B hJ hħ qA qB)
      window_nonneg := retention_nonneg hκ (echoRate_pos A B hJ hħ qA qB) hslow
      before := fun t ht0 ht => by
        show receiverRead (echoFlow J ħ A B (t - 0) (msgPoint 1, (qA, qB))) ≠ true
        rw [sub_zero, receiver_before A B hJ hħ qA hqB hκ ht0 ht]
        exact Bool.false_ne_true
      holds := fun t ht₁ ht₂ => by
        show receiverRead (echoFlow J ħ A B (t - 0) (msgPoint 1, (qA, qB))) = true
        rw [sub_zero]
        exact receiver_received A B hJ hħ qA hqB hκ ht₁ ht₂ }

/-- ★★★ **The return record**: pointer `A`'s second arc, written by the carrier as it comes back —
an `ActualOccurrence` at site `{A}`, value `2`, write interval `[1/(2 r_A), returnEnd]`, window
`senderWindow`. **The final reading comes from a register locally accessible at `A`.** -/
noncomputable def returnRecord (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hr : 0 < senderRate A ħ qA)
    (hslow : 3 * (senderRate A ħ qA * echoLoss A B J qA qB) ≤ echoRate A B J ħ qA qB) :
    ActualOccurrence EchoArena (Fin 3) 2 where
  evolve := echoEvolve J ħ A B
  evolve_self := echoEvolve_self J ħ A B
  evolve_comp := echoEvolve_comp J ħ A B
  measurable_evolve := measurable_echoEvolve J ħ A B
  readout := senderRead
  measurable_readout := measurable_senderRead
  ready := echoReady
  measurableSet_ready := measurableSet_echoReady
  prep := (msgPoint 1, (qA, qB))
  prep_mem := ⟨hqA, hqB⟩
  site := {0}
  start := 0
  value := 2
  writeStart := returnStart (senderRate A ħ qA)
  writeEnd := returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
  window := senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
  isWrite :=
    { start_le := returnStart_nonneg hr
      interval := returnStart_le_returnEnd hr (echoLoss_pos A B hJ qA qB).le
        (echoLoss_le_one A B hJ qA qB) (echoRate_pos A B hJ hħ qA qB)
      window_nonneg := senderWindow_nonneg hr (echoLoss_le_one A B hJ qA qB)
        (echoRate_pos A B hJ hħ qA qB) hslow
      before := fun t ht0 ht => by
        show senderRead (echoFlow J ħ A B (t - 0) (msgPoint 1, (qA, qB))) ≠ 2
        rw [sub_zero]
        exact sender_before_return A B hJ hħ hqA hr qB ht0 ht
      holds := fun t ht₁ ht₂ => by
        show senderRead (echoFlow J ħ A B (t - 0) (msgPoint 1, (qA, qB))) = 2
        rw [sub_zero]
        exact sender_returned A B hJ hħ hqA hr qB ht₁ ht₂ }

/-- ★★ **The return arc is disjoint from the emission arc, and the return record is written after
the emission record**: the two values differ, the emission window ends before the return write
ends, and through the emission window the register does not read `2`. -/
theorem emission_return_disjoint (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2)
    (hqB : qB ∈ readyArc 2) (hr : 0 < senderRate A ħ qA)
    (hslow : 3 * (senderRate A ħ qA * echoLoss A B J qA qB) ≤ echoRate A B J ħ qA qB) :
    (emissionRecord A B hJ hħ hqA hqB hr hslow).value
        ≠ (returnRecord A B hJ hħ hqA hqB hr hslow).value
      ∧ (emissionRecord A B hJ hħ hqA hqB hr hslow).writeEnd
          + (emissionRecord A B hJ hħ hqA hqB hr hslow).window
        < (returnRecord A B hJ hħ hqA hqB hr hslow).writeEnd
      ∧ ∀ t, (emissionRecord A B hJ hħ hqA hqB hr hslow).writeEnd ≤ t →
          t ≤ (emissionRecord A B hJ hħ hqA hqB hr hslow).writeEnd
            + (emissionRecord A B hJ hħ hqA hqB hr hslow).window →
          (returnRecord A B hJ hħ hqA hqB hr hslow).history t
            ≠ (returnRecord A B hJ hħ hqA hqB hr hslow).value := by
  refine ⟨show (1 : Fin 3) ≠ 2 by decide, emitEnd_add_window_lt_returnEnd hr
    (echoLoss_pos A B hJ qA qB).le (echoLoss_le_one A B hJ qA qB) (echoRate_pos A B hJ hħ qA qB)
    hslow, fun t ht₁ ht₂ => ?_⟩
  show senderRead (echoFlow J ħ A B (t - 0) (msgPoint 1, (qA, qB))) ≠ 2
  rw [sub_zero, sender_emitted A B hJ hħ hqA hr qB ht₁ ht₂]
  decide

/-- ★★ **The sender's retention is finite**: after the return window there is a time at which pointer
`A` is back exactly where message `0` left it — the carrier keeps shuttling and the pointer completes
a turn. -/
theorem sender_returns (hJ : 0 < J) (hħ : 0 < ħ) (qA qB : LF4.KTorus) (hr : 0 < senderRate A ħ qA)
    (hslow : 3 * (senderRate A ħ qA * echoLoss A B J qA qB) ≤ echoRate A B J ħ qA qB) :
    ∃ t, returnEnd (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB)
        + senderWindow (senderRate A ħ qA) (echoLoss A B J qA qB) (echoRate A B J ħ qA qB) < t
      ∧ (echoFlow J ħ A B t (msgPoint 1, (qA, qB))).2.1 = qA := by
  set r := senderRate A ħ qA with hrdef
  set l := echoLoss A B J qA qB with hldef
  set ω := echoRate A B J ħ qA qB with hωdef
  have hl0 := (echoLoss_pos A B hJ qA qB).le
  have hl1 := echoLoss_le_one A B hJ qA qB
  have hω := echoRate_pos A B hJ hħ qA qB
  have hμ := meanRate_pos hr hl1
  have hb := band_le hω hslow
  set a := returnEnd r l ω + senderWindow r l ω with ha
  set b := (1 + band r l ω) / meanRate r l with hb'
  have hab : a ≤ b := by
    refine le_of_mul_le_mul_left ?_ hμ
    rw [ha, hb', mul_add, meanRate_mul_returnEnd hr hl1, meanRate_mul_senderWindow hr hl1,
      mul_div_cancel₀ _ hμ.ne']
    linarith [band_nonneg hr.le hl0 hω]
  have hDa : senderDrift r l ω a ≤ 5 / 6 := by
    have := senderDrift_upper hr.le hl0 hω a
    have e : r * (a * (1 - l / 2) + l / (4 * ω)) = meanRate r l * a + band r l ω := by
      unfold meanRate band
      ring
    rw [e, ha, mul_add, meanRate_mul_returnEnd hr hl1, meanRate_mul_senderWindow hr hl1] at this
    linarith
  have hDb : 1 ≤ senderDrift r l ω b := by
    have := senderDrift_lower hr.le hl0 hω b
    have e : r * (b * (1 - l / 2) - l / (4 * ω)) = meanRate r l * b - band r l ω := by
      unfold meanRate band
      ring
    rw [e, hb', mul_div_cancel₀ _ hμ.ne'] at this
    linarith
  obtain ⟨t, ⟨hta, -⟩, hDt⟩ := intermediate_value_Icc hab
    (continuous_senderDrift r l ω).continuousOn ⟨by linarith, hDb⟩
  refine ⟨t, lt_of_le_of_ne hta fun h => ?_, ?_⟩
  · rw [← h] at hDt
    linarith
  · rw [echoFlow_msgPoint_one_pointerA A B hJ hħ, hDt]
    show (qA.1 + ((1 : ℝ) : AddCircle (1 : ℝ)), qA.2) = qA
    rw [AddCircle.coe_period, add_zero]

/-- ★★ **The receiver's retention is finite** (#194's `message_one_returns` on the echo arena). -/
theorem receiver_returns (hJ : 0 < J) (hħ : 0 < ħ) (qA qB : LF4.KTorus)
    (hκ : 0 < receiverDrift A B J ħ qA qB) :
    ∃ t, writeEnd (receiverDrift A B J ħ qA qB) (echoRate A B J ħ qA qB)
        + retention (receiverDrift A B J ħ qA qB) (echoRate A B J ħ qA qB) < t
      ∧ (echoFlow J ħ A B t (msgPoint 1, (qA, qB))).2.2 = qB := by
  set κ := receiverDrift A B J ħ qA qB with hκdef
  set ω := echoRate A B J ħ qA qB with hωdef
  have hω : 0 < ω := echoRate_pos A B hJ hħ qA qB
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
  · rw [echoFlow_msgPoint_one_pointerB A B hJ hħ, hDt]
    show (qB.1 + ((1 : ℝ) : AddCircle (1 : ℝ)), qB.2) = qB
    rw [AddCircle.coe_period, add_zero]

/-! ### The package -/

/-- ★★★ **The autonomous echo.** On `FieldArena 2 2 × (T² × T²)` with the dynamics of the joint
Hamiltonian `⟨p, J X p⟩ + g_A n_A f_A(θ₂ᴬ) + g_B n_B f_B(θ₂ᴮ)`: the two-time law holds and the
propagator is autonomous; Liouville measure is preserved; the joint energy and both `θ₂` are
conserved; each pointer turns at its own rate times the occupancy of its own station; message `0`
fixes the whole arena point; for message `1` the carrier is back at `A` at the detuned round trip;
the emission, the reception and the return are three `ActualOccurrence`s on the one arena at sites
`{A}`, `{B}`, `{A}` from the one preparation; the return arc is disjoint from the emission arc and
written after it; and all three retentions are finite. -/
theorem autonomous_echo (hJ : 0 < J) (hħ : 0 < ħ) (hqA : qA ∈ readyArc 2) (hqB : qB ∈ readyArc 2)
    (hr : 0 < senderRate A ħ qA) (hκ : 0 < receiverDrift A B J ħ qA qB)
    (hslowA : 3 * (senderRate A ħ qA * echoLoss A B J qA qB) ≤ echoRate A B J ħ qA qB)
    (hslowB : 3 * receiverDrift A B J ħ qA qB ≤ 2 * echoRate A B J ħ qA qB) :
    (∀ s t u : OnticTime, echoEvolve J ħ A B t u ∘ echoEvolve J ħ A B s t = echoEvolve J ħ A B s u)
      ∧ (∀ s t a : OnticTime, echoEvolve J ħ A B (s + a) (t + a) = echoEvolve J ħ A B s t)
      ∧ (∀ (s t : OnticTime) (p₀ : FieldArena 2 2), MeasurePreserving (echoEvolve J ħ A B s t)
          ((fsMeasure p₀).prod volume) ((fsMeasure p₀).prod volume))
      ∧ (∀ (t : ℝ) (x : EchoArena), echoEnergy J A B (echoFlow J ħ A B t x) = echoEnergy J A B x)
      ∧ (∀ (t : ℝ) (x : EchoArena),
          (echoFlow J ħ A B t x).2.1.2 = x.2.1.2 ∧ (echoFlow J ħ A B t x).2.2.2 = x.2.2.2)
      ∧ (∀ (x : EchoArena) (t : ℝ), HasDerivAt (fun t => echoAmountA J ħ A B t x)
          (rateAt A.g ħ A.periodic x.2.1.2 * arenaObs occA (echoFlow J ħ A B t x).1) t)
      ∧ (∀ (x : EchoArena) (t : ℝ), HasDerivAt (fun t => echoAmountB J ħ A B t x)
          (rateAt B.g ħ B.periodic x.2.2.2 * arenaObs occB (echoFlow J ħ A B t x).1) t)
      ∧ (∀ t : ℝ, echoFlow J ħ A B t (msgPoint 0, (qA, qB)) = (msgPoint 0, (qA, qB)))
      ∧ (echoFlow J ħ A B (detunedRoundTrip J ħ (echoDetuning A B qA qB))
          (msgPoint 1, (qA, qB))).1 = msgPoint 1
      ∧ (emissionRecord A B hJ hħ hqA hqB hr hslowA).site = {0}
      ∧ (receptionRecord A B hJ hħ hqA hqB hκ hslowB).site = {1}
      ∧ (returnRecord A B hJ hħ hqA hqB hr hslowA).site = {0}
      ∧ (emissionRecord A B hJ hħ hqA hqB hr hslowA).prep = (msgPoint 1, (qA, qB))
      ∧ (receptionRecord A B hJ hħ hqA hqB hκ hslowB).prep = (msgPoint 1, (qA, qB))
      ∧ (returnRecord A B hJ hħ hqA hqB hr hslowA).prep = (msgPoint 1, (qA, qB))
      ∧ (emissionRecord A B hJ hħ hqA hqB hr hslowA).value
          ≠ (returnRecord A B hJ hħ hqA hqB hr hslowA).value
      ∧ (emissionRecord A B hJ hħ hqA hqB hr hslowA).writeEnd
          + (emissionRecord A B hJ hħ hqA hqB hr hslowA).window
        < (returnRecord A B hJ hħ hqA hqB hr hslowA).writeEnd
      ∧ (∃ t, (returnRecord A B hJ hħ hqA hqB hr hslowA).writeEnd
            + (returnRecord A B hJ hħ hqA hqB hr hslowA).window < t
          ∧ (echoFlow J ħ A B t (msgPoint 1, (qA, qB))).2.1 = qA)
      ∧ (∃ t, (receptionRecord A B hJ hħ hqA hqB hκ hslowB).writeEnd
            + (receptionRecord A B hJ hħ hqA hqB hκ hslowB).window < t
          ∧ (echoFlow J ħ A B t (msgPoint 1, (qA, qB))).2.2 = qB) :=
  ⟨echoEvolve_comp J ħ A B, echoEvolve_shift J ħ A B,
    fun s t p₀ => echoEvolve_measurePreserving J ħ A B s t p₀, echoEnergy_echoFlow J ħ A B,
    echoFlow_angles J ħ A B, hasDerivAt_echoAmountA J ħ A B, hasDerivAt_echoAmountB J ħ A B,
    fun t => echoFlow_msgPoint_zero A B hJ qA qB t, echo_return_ray A B hJ hħ qA qB, rfl, rfl, rfl,
    rfl, rfl, rfl, (emission_return_disjoint A B hJ hħ hqA hqB hr hslowA).1,
    (emission_return_disjoint A B hJ hħ hqA hqB hr hslowA).2.1,
    sender_returns A B hJ hħ qA qB hr hslowA, receiver_returns A B hJ hħ qA qB hκ⟩

end Writes

end CSD.RecordLayer

end
