/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.BlockCollapse
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# SigmaLayer/PhaseSlot: the phase-carrying slot — degenerate Lüders, route (ii), brick 2

**Category:** 7-SigmaLayer (dynamical measurement — the degenerate-Lüders construction,
route (ii) of the sharpened wall).

## What this proves

`BlockCollapse.lean` sharpened the wall: the vector-level collapse-with-storage
(`componentSwap`) fails to descend to ray pairs because the product `ℙ×ℙ` quotient forgets the
relative scale. Route (ii) keeps the phase: the slot carries **nonzero vectors**, and the
preparation carries its ontic phase as an epistemically uniform circle orbit. Three pieces:

1. ★ `pairSwap` — the **total, involutive, measurable** pair dynamics on nonzero-vector pairs:
   fire `componentSwap` exactly when both outputs are nonzero, else the identity. The
   condition evaluated *at a fired image* is automatically true (`componentSwap` is involutive
   and the inputs were nonzero), which is what makes the conditional map a genuine involution
   (`pairSwap_involutive`) — reversibility, hence storage, hence `no_exact_collapse` respected.
2. `phasePrep` — the **phase-orbit preparation**: the uniform measure on `{χ(θ)·ψ}`, the image
   of the circle's Haar measure. The ray-level readout of the orbit is the Dirac at `[ψ]`
   (`readout_phasePrep`): the enrichment adds ontic phase, not epistemic content.
3. ★★ `phase_slot_block_luders` — **the degenerate Lüders update, realised**: with a **fixed**
   block-calibrated slot `α` (`Πᵢα = α`, `α ≠ 0`), the ray-level readout of the post-swap
   system is **exactly** `δ_{[Πᵢψ]}` — the `blockLudersObligation_iff_relocation` target — for
   every preparation with nonvanishing block component.

## Why this evades `swap_not_blockLuders`, honestly

The no-go's mechanism was: the full swap makes the post-system *the slot's prior content*,
hence preparation-independent, hence wrong at two in-block vertices. The pair swap here is
**partial**: the block component of the system *stays* — the dynamics moves system-information
into the slot (the complement is stored), not slot-content into the system. The slot
calibration is still **fixed** (`Measure.dirac`); preparation-dependence of the post-state
comes from the preparation itself. No contradiction with the no-go: its premise fails for a
partial swap. And the partial swap is only well-defined because the arena is phase-enriched —
on rays it was ill-defined, which is exactly what the sharpened wall said.

## ⚠️ Honest scope — what brick 3 still owes

This is the **state-update core**, not yet the full protocol: (a) the register/sector plumbing
(a `MeasurementProtocol` on the phase-enriched arena with the record trigger, mirroring
`SwapWitness`); (b) **Liouville preservation on the enriched arena** — `pairSwap` preserves
summed norms (`componentSwap_norm_sum`), so the natural invariant reference measure is a
unitarily-invariant one (e.g. Gaussian) on the doubled space; formalising that invariance is
the recorded remaining work (`specs/BACKLOG.md`, effort M). Nothing here claims either.

*Corrected 2026-08-04 (codebase audit).* **Both debts were paid the same day (2026-08-02), and (b) did not need the Gaussian
route**: the phase-enriched pair arena *is* the projective join, so Liouville preservation is
FS unitary invariance (`joinSwap_measurePreserving`, `SigmaLayer/JoinArena.lean`), and the
protocol plumbing (a) is `SigmaLayer/JoinProtocol.lean`. The paragraph above is kept as the
construction record. The
obligation is discharged at the level `BlockLudersObligation` actually demands — the
post-state as a measure — for the canonical phase-orbit preparations and fixed calibration.

## References

`SigmaLayer/BlockCollapse.lean` (`componentSwap`, the sharpened wall, brick 1);
`SigmaLayer/DegenerateLuders.lean` (`swap_not_blockLuders` — the boundary this evades,
`BlockLudersObligation`); `SigmaLayer/MeasurementConstraints.lean` (`no_exact_collapse`);
`Mathlib/LinearAlgebra/Projectivization/MeasureSpace.lean` (`measurable_mk'`);
`Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean` (`AddCircle.toCircle`);
`specs/BACKLOG.md`.
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

open scoped Classical

variable {N K : ℕ}

/-! ### The total conditional pair swap -/

/-- The firing condition: both `componentSwap` outputs are nonzero. -/
def pairSwapCond (b : Fin N → Fin K) (i : Fin K)
    (p : EuclideanSpace ℂ (Fin N) × EuclideanSpace ℂ (Fin N)) : Prop :=
  (componentSwap b i p).1 ≠ 0 ∧ (componentSwap b i p).2 ≠ 0

/-- **The total pair swap** on nonzero-vector pairs: fire the component swap exactly when both
outputs are nonzero, else the identity. -/
noncomputable def pairSwap (b : Fin N → Fin K) (i : Fin K)
    (p : { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 } × { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 }) :
    { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 } × { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 } :=
  (⟨if pairSwapCond b i ((p.1 : EuclideanSpace ℂ (Fin N)), (p.2 : EuclideanSpace ℂ (Fin N)))
      then (componentSwap b i ((p.1 : EuclideanSpace ℂ (Fin N)),
        (p.2 : EuclideanSpace ℂ (Fin N)))).1
      else (p.1 : EuclideanSpace ℂ (Fin N)), by
      by_cases h : pairSwapCond b i ((p.1 : EuclideanSpace ℂ (Fin N)),
          (p.2 : EuclideanSpace ℂ (Fin N)))
      · rw [if_pos h]; exact h.1
      · rw [if_neg h]; exact p.1.2⟩,
   ⟨if pairSwapCond b i ((p.1 : EuclideanSpace ℂ (Fin N)), (p.2 : EuclideanSpace ℂ (Fin N)))
      then (componentSwap b i ((p.1 : EuclideanSpace ℂ (Fin N)),
        (p.2 : EuclideanSpace ℂ (Fin N)))).2
      else (p.2 : EuclideanSpace ℂ (Fin N)), by
      by_cases h : pairSwapCond b i ((p.1 : EuclideanSpace ℂ (Fin N)),
          (p.2 : EuclideanSpace ℂ (Fin N)))
      · rw [if_pos h]; exact h.2
      · rw [if_neg h]; exact p.2.2⟩)

/-- The fired-branch values. -/
lemma pairSwap_of_cond (b : Fin N → Fin K) (i : Fin K)
    {p : { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 } × { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 }}
    (h : pairSwapCond b i ((p.1 : EuclideanSpace ℂ (Fin N)), (p.2 : EuclideanSpace ℂ (Fin N)))) :
    ((pairSwap b i p).1 : EuclideanSpace ℂ (Fin N))
        = (componentSwap b i ((p.1 : EuclideanSpace ℂ (Fin N)),
            (p.2 : EuclideanSpace ℂ (Fin N)))).1
      ∧ ((pairSwap b i p).2 : EuclideanSpace ℂ (Fin N))
        = (componentSwap b i ((p.1 : EuclideanSpace ℂ (Fin N)),
            (p.2 : EuclideanSpace ℂ (Fin N)))).2 := by
  constructor <;>
    · show ite _ _ _ = _
      rw [if_pos h]

/-- The unfired-branch value. -/
lemma pairSwap_of_not_cond (b : Fin N → Fin K) (i : Fin K)
    {p : { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 } × { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 }}
    (h : ¬ pairSwapCond b i ((p.1 : EuclideanSpace ℂ (Fin N)),
      (p.2 : EuclideanSpace ℂ (Fin N)))) :
    pairSwap b i p = p := by
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;>
    · show ite _ _ _ = _
      rw [if_neg h]

/-- **★ The pair swap is a genuine involution** — the reversibility that makes the collapse a
relocation-with-storage rather than a contraction. The key: at a fired image the firing
condition is automatically satisfied, because `componentSwap` is involutive and the original
inputs were nonzero. -/
theorem pairSwap_involutive (b : Fin N → Fin K) (i : Fin K) :
    Function.Involutive (pairSwap b i) := by
  intro p
  by_cases h : pairSwapCond b i ((p.1 : EuclideanSpace ℂ (Fin N)),
      (p.2 : EuclideanSpace ℂ (Fin N)))
  · obtain ⟨h1, h2⟩ := pairSwap_of_cond b i h
    have himg : (((pairSwap b i p).1 : EuclideanSpace ℂ (Fin N)),
        ((pairSwap b i p).2 : EuclideanSpace ℂ (Fin N)))
        = componentSwap b i ((p.1 : EuclideanSpace ℂ (Fin N)),
            (p.2 : EuclideanSpace ℂ (Fin N))) := by
      rw [h1, h2]
    have hcond2 : pairSwapCond b i (((pairSwap b i p).1 : EuclideanSpace ℂ (Fin N)),
        ((pairSwap b i p).2 : EuclideanSpace ℂ (Fin N))) := by
      unfold pairSwapCond
      rw [himg, componentSwap_involutive b i]
      exact ⟨p.1.2, p.2.2⟩
    obtain ⟨h1', h2'⟩ := pairSwap_of_cond b i hcond2
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [h1', himg, componentSwap_involutive b i]
    · rw [h2', himg, componentSwap_involutive b i]
  · rw [pairSwap_of_not_cond b i h, pairSwap_of_not_cond b i h]

/-- The firing condition holds in the calibrated-measurement situation: nonzero block
component, block-supported nonzero slot. -/
lemma pairSwapCond_of_calibrated (b : Fin N → Fin K) (i : Fin K)
    {ψ α : EuclideanSpace ℂ (Fin N)} (hPi : blockProj b i ψ ≠ 0)
    (hα : blockProj b i α = α) (hα0 : α ≠ 0) :
    pairSwapCond b i (ψ, α) := by
  constructor
  · show blockProj b i ψ + (α - blockProj b i α) ≠ 0
    rw [hα, sub_self, add_zero]
    exact hPi
  · show blockProj b i α + (ψ - blockProj b i ψ) ≠ 0
    intro h0
    apply hα0
    have happ := congrArg (blockProj b i) h0
    rw [map_add, blockProj_idem, blockProj_compl, add_zero, map_zero, hα] at happ
    exact happ

/-- **The calibrated fired value**: the post-swap system vector is exactly the Lüders-collapsed
`Πᵢψ`. -/
lemma pairSwap_fst_calibrated (b : Fin N → Fin K) (i : Fin K)
    {ψ α : EuclideanSpace ℂ (Fin N)} (hψ0 : ψ ≠ 0) (hPi : blockProj b i ψ ≠ 0)
    (hα : blockProj b i α = α) (hα0 : α ≠ 0) :
    ((pairSwap b i (⟨ψ, hψ0⟩, ⟨α, hα0⟩)).1 : EuclideanSpace ℂ (Fin N))
      = blockProj b i ψ := by
  rw [(pairSwap_of_cond b i (pairSwapCond_of_calibrated b i hPi hα hα0)).1]
  exact componentSwap_collapse b i hα

/-- The component swap is continuous (a linear coordinate exchange). -/
lemma continuous_componentSwap (b : Fin N → Fin K) (i : Fin K) :
    Continuous (componentSwap b i) := by
  have hPi : Continuous (blockProj b i) := LinearMap.continuous_of_finiteDimensional _
  unfold componentSwap
  exact ((hPi.comp continuous_fst).add
      (continuous_snd.sub (hPi.comp continuous_snd))).prodMk
    ((hPi.comp continuous_snd).add (continuous_fst.sub (hPi.comp continuous_fst)))

/-- The pair swap is measurable. -/
theorem measurable_pairSwap (b : Fin N → Fin K) (i : Fin K) :
    Measurable (pairSwap b i) := by
  classical
  have hcoe : Measurable fun p : { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 }
      × { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 } =>
      ((p.1 : EuclideanSpace ℂ (Fin N)), (p.2 : EuclideanSpace ℂ (Fin N))) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_subtype_coe.comp measurable_snd)
  have hopen : IsOpen {q : EuclideanSpace ℂ (Fin N) × EuclideanSpace ℂ (Fin N) |
      pairSwapCond b i q} := by
    unfold pairSwapCond
    exact ((isOpen_compl_singleton.preimage
        (continuous_fst.comp (continuous_componentSwap b i))).inter
      (isOpen_compl_singleton.preimage
        (continuous_snd.comp (continuous_componentSwap b i))))
  have hC : MeasurableSet {p : { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 }
      × { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 } |
      pairSwapCond b i ((p.1 : EuclideanSpace ℂ (Fin N)),
        (p.2 : EuclideanSpace ℂ (Fin N)))} :=
    hcoe hopen.measurableSet
  have hf1 : Measurable fun p : { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 }
      × { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 } =>
      (if pairSwapCond b i ((p.1 : EuclideanSpace ℂ (Fin N)), (p.2 : EuclideanSpace ℂ (Fin N)))
        then (componentSwap b i ((p.1 : EuclideanSpace ℂ (Fin N)),
          (p.2 : EuclideanSpace ℂ (Fin N)))).1
        else (p.1 : EuclideanSpace ℂ (Fin N))) :=
    Measurable.ite hC
      ((continuous_fst.comp (continuous_componentSwap b i)).measurable.comp hcoe)
      (measurable_subtype_coe.comp measurable_fst)
  have hf2 : Measurable fun p : { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 }
      × { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 } =>
      (if pairSwapCond b i ((p.1 : EuclideanSpace ℂ (Fin N)), (p.2 : EuclideanSpace ℂ (Fin N)))
        then (componentSwap b i ((p.1 : EuclideanSpace ℂ (Fin N)),
          (p.2 : EuclideanSpace ℂ (Fin N)))).2
        else (p.2 : EuclideanSpace ℂ (Fin N))) :=
    Measurable.ite hC
      ((continuous_snd.comp (continuous_componentSwap b i)).measurable.comp hcoe)
      (measurable_subtype_coe.comp measurable_snd)
  exact (hf1.subtype_mk).prodMk (hf2.subtype_mk)

/-! ### The phase-orbit preparation -/

/-- The phase orbit of a preparation: `θ ↦ χ(θ)·ψ`, a nonzero vector for every phase. -/
noncomputable def phaseVec (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0)
    (θ : AddCircle (1 : ℝ)) : { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 } :=
  ⟨((AddCircle.toCircle θ : Circle) : ℂ) • ψ,
    smul_ne_zero (Circle.coe_ne_zero _) hψ0⟩

lemma measurable_phaseVec (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0) :
    Measurable (phaseVec ψ hψ0) := by
  have hχ : Continuous fun θ : AddCircle (1 : ℝ) =>
      ((AddCircle.toCircle θ : Circle) : ℂ) :=
    continuous_subtype_val.comp AddCircle.continuous_toCircle
  exact ((hχ.smul continuous_const).measurable).subtype_mk

/-- **The phase-orbit preparation**: uniform over the ontic phase, Dirac in every other
respect. -/
noncomputable def phasePrep (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0) :
    Measure { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 } :=
  Measure.map (phaseVec ψ hψ0) volume

instance (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0) :
    IsProbabilityMeasure (phasePrep ψ hψ0) :=
  Measure.isProbabilityMeasure_map (measurable_phaseVec ψ hψ0).aemeasurable

/-- Every point of the phase orbit reads out to the same ray. -/
lemma mk'_phaseVec (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0) (θ : AddCircle (1 : ℝ)) :
    Projectivization.mk' ℂ (phaseVec ψ hψ0 θ) = Projectivization.mk ℂ ψ hψ0 := by
  rw [Projectivization.mk'_eq_mk, Projectivization.mk_eq_mk_iff']
  exact ⟨((AddCircle.toCircle θ : Circle) : ℂ), rfl⟩

/-- **The enrichment adds ontic phase, not epistemic content**: the ray-level readout of the
phase orbit is the Dirac at the ray. -/
theorem readout_phasePrep (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0) :
    Measure.map (Projectivization.mk' ℂ) (phasePrep ψ hψ0)
      = Measure.dirac (Projectivization.mk ℂ ψ hψ0) := by
  rw [phasePrep, Measure.map_map Projectivization.measurable_mk' (measurable_phaseVec ψ hψ0),
    show (Projectivization.mk' ℂ) ∘ (phaseVec ψ hψ0)
      = fun _ => Projectivization.mk ℂ ψ hψ0 from funext (mk'_phaseVec ψ hψ0),
    Measure.map_const, measure_univ, one_smul]

/-! ### The degenerate Lüders update, realised -/

/-- **★★ The degenerate Lüders update, realised by the phase-carrying slot.** Prepare the
phase orbit of `ψ`; calibrate the slot with a **fixed** block-supported `α`; fire the pair
swap; read out the system ray. The result is **exactly** `δ_{[Πᵢψ]}` — the target
`blockLudersObligation_iff_relocation` demands — for every preparation with nonvanishing
block-`i` component. A fixed calibration achieves a preparation-dependent post-state because
the partial swap moves system-information into the slot, not slot-content into the system;
`swap_not_blockLuders`'s premise fails, and its conclusion is evaded. -/
theorem phase_slot_block_luders (b : Fin N → Fin K) (i : Fin K)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ0 : ψ ≠ 0) (h : blockProj b i ψ ≠ 0)
    {α : EuclideanSpace ℂ (Fin N)} (hα : blockProj b i α = α) (hα0 : α ≠ 0) :
    Measure.map
        (fun p : { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 }
            × { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 } =>
          Projectivization.mk' ℂ (pairSwap b i p).1)
        ((phasePrep ψ hψ0).prod (Measure.dirac (⟨α, hα0⟩ :
          { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 })))
      = Measure.dirac (Projectivization.mk ℂ (blockProj b i ψ) h) := by
  have hreadout : Measurable fun p : { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 }
      × { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 } =>
      Projectivization.mk' ℂ (pairSwap b i p).1 :=
    Projectivization.measurable_mk'.comp (measurable_fst.comp (measurable_pairSwap b i))
  have hpairwith : Measurable fun x : { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 } =>
      (x, (⟨α, hα0⟩ : { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 })) :=
    measurable_id.prodMk measurable_const
  rw [Measure.prod_dirac, phasePrep,
    Measure.map_map hpairwith (measurable_phaseVec ψ hψ0),
    Measure.map_map hreadout (hpairwith.comp (measurable_phaseVec ψ hψ0))]
  have hconst : (fun p : { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 }
        × { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 } =>
        Projectivization.mk' ℂ (pairSwap b i p).1)
      ∘ ((fun x : { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 } =>
          (x, (⟨α, hα0⟩ : { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 })))
        ∘ (phaseVec ψ hψ0))
      = fun _ => Projectivization.mk ℂ (blockProj b i ψ) h := by
    funext θ
    simp only [Function.comp_apply]
    have hPiTheta : blockProj b i (((AddCircle.toCircle θ : Circle) : ℂ) • ψ) ≠ 0 := by
      rw [map_smul]
      exact smul_ne_zero (Circle.coe_ne_zero _) h
    have hval : ((pairSwap b i (phaseVec ψ hψ0 θ,
        (⟨α, hα0⟩ : { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 }))).1
          : EuclideanSpace ℂ (Fin N))
        = blockProj b i (((AddCircle.toCircle θ : Circle) : ℂ) • ψ) :=
      pairSwap_fst_calibrated b i (phaseVec ψ hψ0 θ).2 hPiTheta hα hα0
    rw [Projectivization.mk'_eq_mk, Projectivization.mk_eq_mk_iff']
    exact ⟨((AddCircle.toCircle θ : Circle) : ℂ), by rw [hval, map_smul]⟩
  rw [hconst, Measure.map_const, measure_univ, one_smul]

end CSD.RecordLayer
