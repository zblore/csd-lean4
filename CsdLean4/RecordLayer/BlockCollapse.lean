/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DegenerateLuders
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.MeasureSpace
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# SigmaLayer/BlockCollapse: the degenerate-Lüders target as a relocation — the join route, brick 1

**Category:** 7-SigmaLayer (dynamical measurement — the degenerate-Lüders construction,
first brick of the projective-join route).

## Where this sits

`swap_not_blockLuders` (`DegenerateLuders.lean`) proved the boundary: no *fixed* calibration
implements the degenerate Lüders update, because the demanded post-state `[Πᵢψ]` depends on the
preparation. The recorded route forward is the projective join. This module builds the route's
first brick — the **object** every witness must implement, and the **vector-level mechanism**
that implements it one level above the rays:

1. ★ `blockCollapse` — the measurable ray-level collapse map `[ψ] ↦ [Πᵢψ]` (junk = identity
   where the block component vanishes), constructed by quotient descent
   (`Projectivization.lift`) with measurability through
   `measurable_iff_measurable_comp_mk'`.
2. ★ `luders_target_eq_relocation` — **collapse as relocation, at the epistemic level**: the
   degenerate-Lüders target `epistemicMeasure [Πᵢψ]` *is* the pushforward of the preparation
   under the deterministic system-side relocation `ludersRelocation` (collapse the base ray,
   keep the fibre). `blockLudersObligation_iff_relocation` restates the §8.3 obligation
   accordingly: what a witness must realise is exactly this pushforward, as the conditioned
   trace of its dynamics.
3. ★ `componentSwap` — the **vector-level witness core**: on the doubled space
   `ℂᴺ ⊕ ℂᴺ` (system ⊕ slot), exchange the block-`i` complements and keep the block parts. It
   is involutive (`componentSwap_involutive`) and preserves summed norms
   (`componentSwap_norm_sum`) — the content of unitarity — and with a slot calibrated *inside*
   the block it performs exactly the collapse **with the residual stored**
   (`componentSwap_collapse`, `componentSwap_stores`): `(ψ, α) ↦ (Πᵢψ, Πᵢα + (ψ − Πᵢψ))`.
   No information is destroyed; `no_exact_collapse` is respected by storage, exactly as in the
   rank-one swap.

## ⚠️ The wall, sharpened

The witness therefore **exists one level above the rays**. What blocks the descent to the
`SwapArena` is now precisely diagnosed: `componentSwap` acts on *vectors*, and its ray-pair
version is ill-defined — `[Πᵢα + (ψ − Πᵢψ)]` depends on the **relative scale** of the two
inputs, which the product `ℙ(ℂᴺ) × ℙ(ℂᴺ)` forgets (the product quotient kills a `U(1) × U(1)`,
the join needs a surviving relative `U(1)`). Two recorded repair routes (`specs/BACKLOG.md`):
**(i)** the Fubini–Study disintegration under join coordinates (the originally recorded wall);
**(ii)** a *phase-carrying slot* — run the bank at sphere level (or `ℙ × S¹`) so the relative
scale survives, and quotient at readout. Route (ii) is new with this diagnosis and is likely
the cheaper one. Until one lands, `swap_not_blockLuders` remains the honest boundary; nothing
here claims a ray-level witness.

## References

`RecordLayer/DegenerateLuders.lean` (`blockProj`, `BlockLudersObligation`,
`swap_not_blockLuders` — the boundary); `RecordLayer/MeasurementConstraints.lean`
(`no_exact_collapse` — why storage is forced); `RecordLayer/SwapWitness.lean` (the rank-one
precedent); `Mathlib/LinearAlgebra/Projectivization/MeasureSpace.lean`
(`measurable_iff_measurable_comp_mk'`); `specs/BACKLOG.md`.
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

variable {N K : ℕ}

/-! ### `blockProj` algebra -/

lemma blockProj_idem (b : Fin N → Fin K) (i : Fin K) (ψ : EuclideanSpace ℂ (Fin N)) :
    blockProj b i (blockProj b i ψ) = blockProj b i ψ := by
  apply PiLp.ext
  intro j
  show (if b j = i then (blockProj b i ψ) j else 0) = (if b j = i then ψ j else 0)
  by_cases h : b j = i
  · simp only [if_pos h]
    show (if b j = i then ψ j else 0) = ψ j
    rw [if_pos h]
  · simp [h]

lemma blockProj_compl (b : Fin N → Fin K) (i : Fin K) (ψ : EuclideanSpace ℂ (Fin N)) :
    blockProj b i (ψ - blockProj b i ψ) = 0 := by
  rw [map_sub, blockProj_idem, sub_self]

/-! ### The vector-level witness core: the component swap -/

/-- **The component swap** on the doubled space (system ⊕ slot): keep the block-`i` parts,
exchange the complements. Linear in each coordinate slot by construction; the unitary content
is `componentSwap_involutive` + `componentSwap_norm_sum`. -/
def componentSwap (b : Fin N → Fin K) (i : Fin K) :
    EuclideanSpace ℂ (Fin N) × EuclideanSpace ℂ (Fin N)
      → EuclideanSpace ℂ (Fin N) × EuclideanSpace ℂ (Fin N) :=
  fun p => (blockProj b i p.1 + (p.2 - blockProj b i p.2),
            blockProj b i p.2 + (p.1 - blockProj b i p.1))

theorem componentSwap_involutive (b : Fin N → Fin K) (i : Fin K) :
    Function.Involutive (componentSwap b i) := by
  intro p
  unfold componentSwap
  refine Prod.ext ?_ ?_ <;>
    simp only [map_add, map_sub, blockProj_idem, sub_self, add_zero,
      add_sub_cancel_left] <;>
    abel

/-- The summed-norm identity: the swap redistributes entries, so the total square-norm over
the two slots is conserved — the isometry half of unitarity. -/
theorem componentSwap_norm_sum (b : Fin N → Fin K) (i : Fin K)
    (p : EuclideanSpace ℂ (Fin N) × EuclideanSpace ℂ (Fin N)) :
    ‖(componentSwap b i p).1‖ ^ 2 + ‖(componentSwap b i p).2‖ ^ 2
      = ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 := by
  have hsq : ∀ v : EuclideanSpace ℂ (Fin N), ‖v‖ ^ 2 = ∑ j, ‖v j‖ ^ 2 := fun v => by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  simp only [hsq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ((componentSwap b i p).1) j = if b j = i then p.1 j else p.2 j := by
    show (blockProj b i p.1) j + (p.2 j - (blockProj b i p.2) j) = _
    show (if b j = i then p.1 j else 0) + (p.2 j - (if b j = i then p.2 j else 0)) = _
    by_cases h : b j = i <;> simp [h]
  have h2 : ((componentSwap b i p).2) j = if b j = i then p.2 j else p.1 j := by
    show (blockProj b i p.2) j + (p.1 j - (blockProj b i p.1) j) = _
    show (if b j = i then p.2 j else 0) + (p.1 j - (if b j = i then p.1 j else 0)) = _
    by_cases h : b j = i <;> simp [h]
  rw [h1, h2]
  by_cases h : b j = i
  · simp [h]
  · simp [h, add_comm]

/-- **★ The collapse, with a block-calibrated slot.** If the slot state lies inside the
block (`Πᵢα = α`), the swap delivers exactly the Lüders-collapsed system vector. -/
theorem componentSwap_collapse (b : Fin N → Fin K) (i : Fin K)
    {ψ α : EuclideanSpace ℂ (Fin N)} (hα : blockProj b i α = α) :
    (componentSwap b i (ψ, α)).1 = blockProj b i ψ := by
  show blockProj b i ψ + (α - blockProj b i α) = blockProj b i ψ
  rw [hα, sub_self, add_zero]

/-- **…and the residual is stored, not destroyed**: the slot receives the complement of the
system state (on top of its own block part). `no_exact_collapse` is respected by storage. -/
theorem componentSwap_stores (b : Fin N → Fin K) (i : Fin K)
    (ψ α : EuclideanSpace ℂ (Fin N)) :
    (componentSwap b i (ψ, α)).2 = blockProj b i α + (ψ - blockProj b i ψ) := rfl

/-! ### The ray-level collapse map -/

/-- The vector-level representative map: collapse to the block component where it is nonzero,
identity otherwise (junk branch, documented). -/
noncomputable def blockCollapseAux (b : Fin N → Fin K) (i : Fin K)
    (v : { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 }) :
    { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 } :=
  ⟨if blockProj b i (v : EuclideanSpace ℂ (Fin N)) ≠ 0
      then blockProj b i (v : EuclideanSpace ℂ (Fin N))
      else (v : EuclideanSpace ℂ (Fin N)), by
    by_cases h : blockProj b i (v : EuclideanSpace ℂ (Fin N)) ≠ 0
    · rwa [if_pos h]
    · rw [if_neg h]
      exact v.2⟩

/-- On the physical branch (nonzero block component), the representative IS the block
projection (interface lemma, §9.1 — the case split its unfold sites re-derive). -/
lemma blockCollapseAux_coe_of_ne {b : Fin N → Fin K} {i : Fin K}
    {v : { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 }}
    (h : blockProj b i (v : EuclideanSpace ℂ (Fin N)) ≠ 0) :
    (blockCollapseAux b i v : EuclideanSpace ℂ (Fin N))
      = blockProj b i (v : EuclideanSpace ℂ (Fin N)) := by
  simp only [blockCollapseAux, if_pos h]

/-- On the junk branch (vanishing block component), the representative is the identity
(interface lemma, §9.1). -/
lemma blockCollapseAux_coe_of_eq {b : Fin N → Fin K} {i : Fin K}
    {v : { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 }}
    (h : blockProj b i (v : EuclideanSpace ℂ (Fin N)) = 0) :
    (blockCollapseAux b i v : EuclideanSpace ℂ (Fin N))
      = (v : EuclideanSpace ℂ (Fin N)) := by
  simp only [blockCollapseAux, if_neg (not_not_intro h)]

/-- **★ The ray-level collapse map** `[ψ] ↦ [Πᵢψ]` (identity where the block component
vanishes), by quotient descent. This is the object any degenerate-Lüders witness must realise
as the conditioned trace of its dynamics. -/
noncomputable def blockCollapse (b : Fin N → Fin K) (i : Fin K) : LF4.CPN N → LF4.CPN N :=
  Projectivization.lift
    (fun v => Projectivization.mk' ℂ (blockCollapseAux b i v))
    (by
      rintro ⟨a, ha⟩ ⟨w, hw⟩ t rfl
      have ht : t ≠ 0 := fun h => ha (by simp [h])
      by_cases h : blockProj b i w ≠ 0
      · have h' : blockProj b i (t • w) ≠ 0 := by
          rw [map_smul]
          simpa [smul_eq_zero, ht] using h
        simp only [blockCollapseAux, Projectivization.mk'_eq_mk, if_pos h', if_pos h]
        rw [Projectivization.mk_eq_mk_iff']
        exact ⟨t, by rw [map_smul]⟩
      · have h' : ¬ blockProj b i (t • w) ≠ 0 := by
          rw [map_smul]
          simpa [smul_eq_zero, ht] using h
        simp only [blockCollapseAux, Projectivization.mk'_eq_mk, if_neg h', if_neg h]
        rw [Projectivization.mk_eq_mk_iff']
        exact ⟨t, rfl⟩)

/-- The value lemma: where the block component is nonzero, `blockCollapse` is `[ψ] ↦ [Πᵢψ]`. -/
theorem blockCollapse_mk (b : Fin N → Fin K) (i : Fin K)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ0 : ψ ≠ 0) (h : blockProj b i ψ ≠ 0) :
    blockCollapse b i (Projectivization.mk ℂ ψ hψ0)
      = Projectivization.mk ℂ (blockProj b i ψ) h := by
  rw [blockCollapse, Projectivization.lift_mk]
  simp only [blockCollapseAux, if_pos h, Projectivization.mk'_eq_mk]

/-- Collapsed states are fixed points: idempotence on the good set. -/
theorem blockCollapse_idem (b : Fin N → Fin K) (i : Fin K)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ0 : ψ ≠ 0) (h : blockProj b i ψ ≠ 0) :
    blockCollapse b i (blockCollapse b i (Projectivization.mk ℂ ψ hψ0))
      = blockCollapse b i (Projectivization.mk ℂ ψ hψ0) := by
  rw [blockCollapse_mk b i hψ0 h, blockCollapse_mk b i h
    (by rw [blockProj_idem]; exact h)]
  congr 1
  exact blockProj_idem b i ψ

/-- Block-supported vertices are fixed: consistency with the rank-one story. -/
theorem blockCollapse_vertex [NeZero N] (b : Fin N → Fin K) {i : Fin K} {j : Fin N}
    (hb : b j = i) :
    blockCollapse b i (vertexPoint j) = vertexPoint j := by
  unfold vertexPoint
  rw [blockCollapse_mk b i (single_ne_zero' j)
    (by rw [blockProj_single hb]; exact single_ne_zero' j)]
  congr 1
  exact blockProj_single hb

/-- `blockCollapse` is measurable — through the coinduced-Borel coincidence
(`measurable_iff_measurable_comp_mk'`). -/
theorem measurable_blockCollapse (b : Fin N → Fin K) (i : Fin K) :
    Measurable (blockCollapse b i) := by
  rw [Projectivization.measurable_iff_measurable_comp_mk']
  have hcont : Continuous (blockProj b i) :=
    LinearMap.continuous_of_finiteDimensional _
  have hS : MeasurableSet {v : { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 } |
      blockProj b i (v : EuclideanSpace ℂ (Fin N)) ≠ 0} := by
    have : Continuous fun v : { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 } =>
        blockProj b i (v : EuclideanSpace ℂ (Fin N)) :=
      hcont.comp continuous_subtype_val
    exact (isOpen_compl_singleton.preimage this).measurableSet
  have hg : Measurable fun v : { w : EuclideanSpace ℂ (Fin N) // w ≠ 0 } =>
      (if blockProj b i (v : EuclideanSpace ℂ (Fin N)) ≠ 0
        then blockProj b i (v : EuclideanSpace ℂ (Fin N))
        else (v : EuclideanSpace ℂ (Fin N))) := by
    exact Measurable.ite hS (hcont.comp continuous_subtype_val).measurable
      measurable_subtype_coe
  exact Projectivization.continuous_mk'.measurable.comp (hg.subtype_mk)

/-! ### Collapse as relocation: the obligation, reformulated -/

/-- **The system-side relocation on `KSigma`**: collapse the base ray, keep the fibre. -/
noncomputable def ludersRelocation (b : Fin N → Fin K) (i : Fin K) :
    LF4.KSigma N → LF4.KSigma N :=
  fun x => (blockCollapse b i x.1, x.2)

theorem measurable_ludersRelocation (b : Fin N → Fin K) (i : Fin K) :
    Measurable (ludersRelocation b i) :=
  ((measurable_blockCollapse b i).comp measurable_fst).prodMk measurable_snd

/-- **★ Collapse as relocation, at the epistemic level.** The degenerate-Lüders target — the
post-measurement state `epistemicMeasure [Πᵢψ]` demanded by the §8.3 obligation — is exactly
the pushforward of the preparation under the deterministic relocation map. Nothing stochastic:
the update is a measurable relocation of the epistemic Dirac slice, fibre untouched. -/
theorem luders_target_eq_relocation (b : Fin N → Fin K) (i : Fin K)
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ0 : ψ ≠ 0) (h : blockProj b i ψ ≠ 0) :
    epistemicMeasure (Projectivization.mk ℂ (blockProj b i ψ) h)
      = Measure.map (ludersRelocation b i)
          (epistemicMeasure (Projectivization.mk ℂ ψ hψ0)) := by
  rw [epistemicMeasure, epistemicMeasure, ← blockCollapse_mk b i hψ0 h,
    show ludersRelocation b i = Prod.map (blockCollapse b i) id from rfl,
    ← Measure.map_prod_map _ _ (measurable_blockCollapse b i) measurable_id,
    Measure.map_id]
  congr 1
  exact (Measure.map_dirac' (measurable_blockCollapse b i) _).symm

/-- **The obligation is a relocation demand.** `BlockLudersObligation` holds for a
post-measurement assignment iff, at every preparation with nonvanishing block weight, the
assignment is the pushforward of the preparation under `ludersRelocation`. What a witness must
realise is exactly this pushforward, as the conditioned trace of measure-preserving
dynamics. -/
theorem blockLudersObligation_iff_relocation (b : Fin N → Fin K)
    (post : (ψ : EuclideanSpace ℂ (Fin N)) → ψ ≠ 0 → Fin K → Measure (LF4.KSigma N)) :
    BlockLudersObligation b post
      ↔ ∀ (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0) (i : Fin K)
          (_ : blockProj b i ψ ≠ 0),
          post ψ hψ0 i
            = Measure.map (ludersRelocation b i)
                (epistemicMeasure (Projectivization.mk ℂ ψ hψ0)) := by
  constructor
  · intro hp ψ hψ0 i h
    rw [hp ψ hψ0 i h]
    exact luders_target_eq_relocation b i hψ0 h
  · intro hp ψ hψ0 i h
    rw [hp ψ hψ0 i h]
    exact (luders_target_eq_relocation b i hψ0 h).symm

end CSD.RecordLayer
