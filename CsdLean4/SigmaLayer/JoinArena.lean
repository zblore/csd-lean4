/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.PhaseSlot
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudy
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.TransitionProbability

/-!
# SigmaLayer/JoinArena: the projective join — Liouville-preserving degenerate Lüders

**Category:** 7-SigmaLayer (dynamical measurement — the degenerate-Lüders construction,
brick 3: the Liouville half).

## The identification that makes brick 3 cheap

`PhaseSlot.lean` realised the degenerate Lüders update on phase-enriched *vector pairs*. This
module observes that **the phase-enriched pair arena is the projective join**: a point of
`ℙ(ℂᴺ ⊕ ℂᴺ) = ℙ(ℂ^{N+N})` is a system-and-slot pair quotiented only by the *global* phase — so
the **relative** phase, the coordinate the sharpened wall demanded, survives in the point
itself. On this arena:

* the component swap is a **coordinate permutation** (`joinPerm`), hence a **permutation
  unitary** (`joinMat`, `joinMat_mem_unitaryGroup`), acting on rays through the standard
  unitary action;
* ★★ **Liouville preservation is Fubini–Study unitary invariance**
  (`joinSwap_measurePreserving`): the measure-preservation obligation recorded as brick 3's
  hard half is discharged by `fubiniStudyMeasure_smul_invariant`, because the dynamics *is* a
  unitary;
* ★★ the Lüders update is **pointwise deterministic** (`join_block_luders`): for every join
  microstate `[ψ ⊕ α]` with nonvanishing block component and block-calibrated slot, the
  post-swap system readout is **exactly** `[Πᵢψ]`. Every microstate updates correctly; the
  `PhaseSlot` measure form is the orbit-averaged shadow of this.

## The three-brick arc, closed at the state level

1. `BlockCollapse.lean`: the target is a relocation; the mechanism exists on vectors; the wall
   is the relative phase.
2. `PhaseSlot.lean`: keep the phase → the update works with fixed calibration (measure form).
3. Here: the phase-kept arena is `ℙ(ℂ^{N+N})`, the dynamics is unitary — **Liouville-preserving
   by FS invariance, Lüders pointwise**.

## ⚠️ What remains for full protocol integration (recorded, mechanical)

The register/sector plumbing: a `MeasurementProtocol` on `ℙ(ℂ^{N+N}) × T²_R` whose record
trigger fires `joinSwap`, mirroring `SwapWitness`, and the conditioned-marginal bookkeeping
tying `join_block_luders` to a `BlockLudersObligation` instance. Both consume only theorems
proved here and machinery that already exists (`specs/BACKLOG.md`, effort M); neither requires
new mathematics. Until that lands, `swap_not_blockLuders` remains the recorded boundary *for
the ray-pair `SwapArena`* — the join arena is where degenerate measurements live.

## References

`SigmaLayer/BlockCollapse.lean` (`componentSwap`, brick 1);
`SigmaLayer/PhaseSlot.lean` (brick 2 — the measure form);
`SigmaLayer/DegenerateLuders.lean` (`swap_not_blockLuders`, `blockProj`);
`Mathlib/LinearAlgebra/Projectivization/FubiniStudy.lean`
(`fubiniStudyMeasure_smul_invariant` — the Liouville driver); `specs/BACKLOG.md`.
-/

@[expose] public section

open MeasureTheory Set Matrix Matrix.UnitaryGroup

namespace CSD.RecordLayer

variable {N K : ℕ}

/-! ### `componentSwap`, entrywise -/

lemma componentSwap_fst_apply (b : Fin N → Fin K) (i : Fin K)
    (p : EuclideanSpace ℂ (Fin N) × EuclideanSpace ℂ (Fin N)) (j : Fin N) :
    (componentSwap b i p).1 j = if b j = i then p.1 j else p.2 j := by
  show (blockProj b i p.1) j + (p.2 j - (blockProj b i p.2) j) = _
  show (if b j = i then p.1 j else 0) + (p.2 j - (if b j = i then p.2 j else 0)) = _
  by_cases h : b j = i <;> simp [h]

lemma componentSwap_snd_apply (b : Fin N → Fin K) (i : Fin K)
    (p : EuclideanSpace ℂ (Fin N) × EuclideanSpace ℂ (Fin N)) (j : Fin N) :
    (componentSwap b i p).2 j = if b j = i then p.2 j else p.1 j := by
  show (blockProj b i p.2) j + (p.1 j - (blockProj b i p.1) j) = _
  show (if b j = i then p.2 j else 0) + (p.1 j - (if b j = i then p.1 j else 0)) = _
  by_cases h : b j = i <;> simp [h]

/-! ### The join permutation and its unitary -/

/-- The block-complement swap on the doubled index set: fix the block-`i` coordinates of both
copies, exchange the complements. -/
def swpSum (b : Fin N → Fin K) (i : Fin K) : Fin N ⊕ Fin N → Fin N ⊕ Fin N
  | Sum.inl j => if b j = i then Sum.inl j else Sum.inr j
  | Sum.inr j => if b j = i then Sum.inr j else Sum.inl j

lemma swpSum_involutive (b : Fin N → Fin K) (i : Fin K) :
    Function.Involutive (swpSum b i) := by
  intro s
  rcases s with j | j <;> by_cases h : b j = i <;> simp [swpSum, h]

/-- The join permutation on `Fin (N + N)`. -/
def joinPerm (b : Fin N → Fin K) (i : Fin K) : Fin (N + N) → Fin (N + N) :=
  fun j => finSumFinEquiv (swpSum b i (finSumFinEquiv.symm j))

lemma joinPerm_involutive (b : Fin N → Fin K) (i : Fin K) :
    Function.Involutive (joinPerm b i) := by
  intro j
  unfold joinPerm
  rw [Equiv.symm_apply_apply, swpSum_involutive b i, Equiv.apply_symm_apply]

lemma joinPerm_injective (b : Fin N → Fin K) (i : Fin K) :
    Function.Injective (joinPerm b i) :=
  (joinPerm_involutive b i).injective

/-- The permutation matrix of the join swap. -/
def joinMat (b : Fin N → Fin K) (i : Fin K) : Matrix (Fin (N + N)) (Fin (N + N)) ℂ :=
  Matrix.of fun j k => if k = joinPerm b i j then 1 else 0

lemma joinMat_mulVec (b : Fin N → Fin K) (i : Fin K) (w : Fin (N + N) → ℂ) :
    joinMat b i *ᵥ w = fun j => w (joinPerm b i j) := by
  funext j
  simp [joinMat, Matrix.mulVec, dotProduct, ite_mul, one_mul, zero_mul]

/-- **The join swap is a unitary** — a permutation matrix. -/
theorem joinMat_mem_unitaryGroup (b : Fin N → Fin K) (i : Fin K) :
    joinMat b i ∈ Matrix.unitaryGroup (Fin (N + N)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext j k
  simp only [Matrix.mul_apply, Matrix.star_apply, joinMat, Matrix.of_apply,
    apply_ite (star : ℂ → ℂ), star_one, star_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.one_apply]
  exact if_congr ⟨fun h => joinPerm_injective b i h, fun h => h ▸ rfl⟩ rfl rfl

/-- The join unitary. -/
noncomputable def joinU (b : Fin N → Fin K) (i : Fin K) :
    Matrix.unitaryGroup (Fin (N + N)) ℂ :=
  ⟨joinMat b i, joinMat_mem_unitaryGroup b i⟩

/-! ### The doubled vectors -/

/-- The doubled vector: system in the first copy, slot in the second. -/
noncomputable def dblVec (v α : EuclideanSpace ℂ (Fin N)) :
    EuclideanSpace ℂ (Fin (N + N)) :=
  WithLp.toLp 2 (fun j => Sum.elim (fun k => v k) (fun k => α k) (finSumFinEquiv.symm j))

@[simp] lemma dblVec_inl (v α : EuclideanSpace ℂ (Fin N)) (k : Fin N) :
    dblVec v α (finSumFinEquiv (Sum.inl k)) = v k := by
  show Sum.elim (fun k => v k) (fun k => α k)
    (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl k))) = v k
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] lemma dblVec_inr (v α : EuclideanSpace ℂ (Fin N)) (k : Fin N) :
    dblVec v α (finSumFinEquiv (Sum.inr k)) = α k := by
  show Sum.elim (fun k => v k) (fun k => α k)
    (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr k))) = α k
  rw [Equiv.symm_apply_apply]
  rfl

lemma dblVec_ne_zero {v : EuclideanSpace ℂ (Fin N)} (hv : v ≠ 0)
    (α : EuclideanSpace ℂ (Fin N)) : dblVec v α ≠ 0 := by
  intro h0
  apply hv
  apply PiLp.ext
  intro k
  have h1 : dblVec v α (finSumFinEquiv (Sum.inl k)) = 0 := by rw [h0]; rfl
  rw [dblVec_inl] at h1
  exact h1

/-- The action of the join unitary on a doubled vector is exactly the component swap. -/
lemma toEuclideanLin_joinMat_dblVec (b : Fin N → Fin K) (i : Fin K)
    (ψ α : EuclideanSpace ℂ (Fin N)) :
    Matrix.toEuclideanLin (joinMat b i) (dblVec ψ α)
      = dblVec ((componentSwap b i (ψ, α)).1) ((componentSwap b i (ψ, α)).2) := by
  apply PiLp.ext
  intro j
  have happ : (Matrix.toEuclideanLin (joinMat b i) (dblVec ψ α)) j
      = dblVec ψ α (joinPerm b i j) := by
    show ((joinMat b i) *ᵥ _) j = _
    rw [joinMat_mulVec]
    rfl
  rw [happ]
  obtain ⟨s, rfl⟩ : ∃ s, j = finSumFinEquiv s :=
    ⟨finSumFinEquiv.symm j, (Equiv.apply_symm_apply _ _).symm⟩
  rcases s with k | k
  · rw [dblVec_inl, componentSwap_fst_apply]
    unfold joinPerm
    rw [Equiv.symm_apply_apply]
    by_cases h : b k = i
    · rw [show swpSum b i (Sum.inl k) = Sum.inl k from by simp [swpSum, h], dblVec_inl,
        if_pos h]
    · rw [show swpSum b i (Sum.inl k) = Sum.inr k from by simp [swpSum, h], dblVec_inr,
        if_neg h]
  · rw [dblVec_inr, componentSwap_snd_apply]
    unfold joinPerm
    rw [Equiv.symm_apply_apply]
    by_cases h : b k = i
    · rw [show swpSum b i (Sum.inr k) = Sum.inr k from by simp [swpSum, h], dblVec_inr,
        if_pos h]
    · rw [show swpSum b i (Sum.inr k) = Sum.inl k from by simp [swpSum, h], dblVec_inl,
        if_neg h]

/-! ### The join dynamics -/

/-- **The join swap on rays**: the unitary action of the permutation on `ℙ(ℂ^{N+N})`. -/
noncomputable def joinSwap (b : Fin N → Fin K) (i : Fin K) :
    LF4.CPN (N + N) → LF4.CPN (N + N) :=
  fun p => joinU b i • p

/-- **★★ Liouville preservation, discharged.** The join swap is a unitary, so it preserves the
Fubini–Study measure — the obligation recorded as brick 3's hard half, closed by
`fubiniStudyMeasure_smul_invariant`. -/
theorem joinSwap_measurePreserving (b : Fin N → Fin K) (i : Fin K)
    (p₀ : LF4.CPN (N + N)) :
    MeasurePreserving (joinSwap b i) (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀) :=
  ⟨(continuous_const_smul (joinU b i)).measurable,
    fubiniStudyMeasure_smul_invariant (joinU b i) p₀⟩

/-! ### The system readout -/

/-- The first-copy projection, as a linear map. -/
noncomputable def fstPart : EuclideanSpace ℂ (Fin (N + N)) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) where
  toFun w := WithLp.toLp 2 (fun k => w (finSumFinEquiv (Sum.inl k)))
  map_add' w₁ w₂ := by
    apply PiLp.ext
    intro k
    show (w₁ + w₂) (finSumFinEquiv (Sum.inl k)) = _
    simp [PiLp.add_apply]
  map_smul' c w := by
    apply PiLp.ext
    intro k
    show (c • w) (finSumFinEquiv (Sum.inl k)) = _
    simp [PiLp.smul_apply]

@[simp] lemma fstPart_dblVec (v α : EuclideanSpace ℂ (Fin N)) :
    fstPart (dblVec v α) = v := by
  apply PiLp.ext
  intro k
  show dblVec v α (finSumFinEquiv (Sum.inl k)) = v k
  rw [dblVec_inl]

variable [NeZero N]

/-- The vector-level readout representative: first copy where nonzero, junk vertex
otherwise. -/
noncomputable def joinFstAux (v : { w : EuclideanSpace ℂ (Fin (N + N)) // w ≠ 0 }) :
    { u : EuclideanSpace ℂ (Fin N) // u ≠ 0 } :=
  ⟨if fstPart (v : EuclideanSpace ℂ (Fin (N + N))) ≠ 0
      then fstPart (v : EuclideanSpace ℂ (Fin (N + N)))
      else EuclideanSpace.single 0 (1 : ℂ), by
    by_cases h : fstPart (v : EuclideanSpace ℂ (Fin (N + N))) ≠ 0
    · rwa [if_pos h]
    · rw [if_neg h]
      exact single_ne_zero' 0⟩

/-- **The system readout from the join**: project a join microstate to its system ray (junk
vertex where the system component vanishes — documented, off the physical set). -/
noncomputable def joinFst : LF4.CPN (N + N) → LF4.CPN N :=
  Projectivization.lift
    (fun v => Projectivization.mk' ℂ (joinFstAux v))
    (by
      rintro ⟨a, ha⟩ ⟨w, hw⟩ t rfl
      have ht : t ≠ 0 := fun h => ha (by simp [h])
      by_cases h : fstPart w ≠ 0
      · have h' : fstPart (t • w) ≠ 0 := by
          rw [map_smul]
          simpa [smul_eq_zero, ht] using h
        simp only [joinFstAux, Projectivization.mk'_eq_mk, if_pos h', if_pos h]
        rw [Projectivization.mk_eq_mk_iff']
        exact ⟨t, by rw [map_smul]⟩
      · have h' : ¬ fstPart (t • w) ≠ 0 := by
          rw [map_smul]
          simpa [smul_eq_zero, ht] using h
        simp only [joinFstAux, Projectivization.mk'_eq_mk, if_neg h', if_neg h])

lemma joinFst_mk {w : EuclideanSpace ℂ (Fin (N + N))} (hw : w ≠ 0)
    (h : fstPart w ≠ 0) :
    joinFst (Projectivization.mk ℂ w hw) = Projectivization.mk ℂ (fstPart w) h := by
  rw [joinFst, Projectivization.lift_mk]
  simp only [joinFstAux, if_pos h, Projectivization.mk'_eq_mk]

/-- The readout is measurable — same coinduced-Borel route as `blockCollapse`. -/
theorem measurable_joinFst : Measurable (joinFst (N := N)) := by
  rw [Projectivization.measurable_iff_measurable_comp_mk']
  have hcont : Continuous (fstPart (N := N)) :=
    LinearMap.continuous_of_finiteDimensional _
  have hS : MeasurableSet {v : { w : EuclideanSpace ℂ (Fin (N + N)) // w ≠ 0 } |
      fstPart (v : EuclideanSpace ℂ (Fin (N + N))) ≠ 0} := by
    have : Continuous fun v : { w : EuclideanSpace ℂ (Fin (N + N)) // w ≠ 0 } =>
        fstPart (v : EuclideanSpace ℂ (Fin (N + N))) :=
      hcont.comp continuous_subtype_val
    exact (isOpen_compl_singleton.preimage this).measurableSet
  have hg : Measurable fun v : { w : EuclideanSpace ℂ (Fin (N + N)) // w ≠ 0 } =>
      (if fstPart (v : EuclideanSpace ℂ (Fin (N + N))) ≠ 0
        then fstPart (v : EuclideanSpace ℂ (Fin (N + N)))
        else EuclideanSpace.single 0 (1 : ℂ)) :=
    Measurable.ite hS ((LinearMap.continuous_of_finiteDimensional _).comp
      continuous_subtype_val).measurable measurable_const
  exact Projectivization.continuous_mk'.measurable.comp (hg.subtype_mk)

/-! ### The pointwise Lüders update -/

/-- **★★ Degenerate Lüders on the join arena, pointwise.** For every join microstate
`[ψ ⊕ α]` with nonvanishing block-`i` component and block-calibrated slot, the post-swap
system readout is exactly the Lüders-collapsed ray `[Πᵢψ]`. Deterministic at every microstate;
combined with `joinSwap_measurePreserving`, the update is a **Liouville-preserving unitary
dynamics** whose readout is the Lüders update — the construction `swap_not_blockLuders`
proved impossible on the ray-pair arena, delivered on the join. -/
theorem join_block_luders (b : Fin N → Fin K) (i : Fin K)
    {ψ α : EuclideanSpace ℂ (Fin N)} (hψ0 : ψ ≠ 0) (hPi : blockProj b i ψ ≠ 0)
    (hα : blockProj b i α = α) :
    joinFst (joinSwap b i (Projectivization.mk ℂ (dblVec ψ α) (dblVec_ne_zero hψ0 α)))
      = Projectivization.mk ℂ (blockProj b i ψ) hPi := by
  unfold joinSwap
  rw [Projectivization.smul_mk_eq_mk_toEuclideanLin _ (dblVec_ne_zero hψ0 α)]
  have hvec : Matrix.toEuclideanLin ((joinU b i) : Matrix (Fin (N + N)) (Fin (N + N)) ℂ)
      (dblVec ψ α)
      = dblVec (blockProj b i ψ) ((componentSwap b i (ψ, α)).2) := by
    rw [show ((joinU b i) : Matrix (Fin (N + N)) (Fin (N + N)) ℂ) = joinMat b i from rfl,
      toEuclideanLin_joinMat_dblVec]
    rw [componentSwap_collapse b i hα]
  have hmk : Projectivization.mk ℂ
      (Matrix.toEuclideanLin ((joinU b i) : Matrix (Fin (N + N)) (Fin (N + N)) ℂ)
        (dblVec ψ α)) (by rw [hvec]; exact dblVec_ne_zero hPi _)
      = Projectivization.mk ℂ (dblVec (blockProj b i ψ) ((componentSwap b i (ψ, α)).2))
          (dblVec_ne_zero hPi _) := by
    rw [Projectivization.mk_eq_mk_iff']
    exact ⟨1, by rw [one_smul, hvec]⟩
  rw [hmk, joinFst_mk _ (by rw [fstPart_dblVec]; exact hPi)]
  rw [Projectivization.mk_eq_mk_iff']
  exact ⟨1, by rw [one_smul, fstPart_dblVec]⟩

end CSD.RecordLayer
