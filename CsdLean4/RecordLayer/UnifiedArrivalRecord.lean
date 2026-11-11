/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedTwoSiteRecords

/-!
# A record written on arrival

**Category:** 7-SigmaLayer (the record layer). BACKLOG #365 — the author's programme "From `Σ` to
physical spacetime", towards milestone M6: a reception record. Remainder (c) of #363 and of #364.
The records of #363 and #364 are written by fast detectors, in a time short against the carrier's
motion: the carrier is where the detector is from the start. A reception record needs the
opposite. The carrier starts away from the detector, travels, and the record is written when it
arrives and not before. `RecordLayer/DiracArrival.lean` (#265) has that for a packet crossing a
ring, with a detector whose law is stated. Here the detector is a pointer of the joint
Hamiltonian flow.

**A crossing of the threshold** (no arena). A pointer starts ready and sits at `pshift (κ I t)`,
`I t = ∫₀ᵗ F` for a continuous `F` with values in `[0, 1]`, `κ > 0`. If `κ I(T₁) ≤ 1/6` and
`1/3 ≤ κ I(T₃)` there is a time `τ` in `[T₁, T₃]` such that the readout history is an
`IsRecordWrite` of `true` from time `0` with write interval `[T₁, τ]` and window `1/(3κ)`
(`isRecordWrite_of_integral_crossing`). The time `τ` is where the displacement reaches `1/3`,
found by the intermediate value theorem.

**A detector on a region.** `regionProj A` is the projector on the sites of `A`. It is Hermitian
and of norm at most one, its expectation is the sum of the occupancies of the sites of `A`, in
`[0, 1]`, and at the ray of `ψ` it is the weight of `ψ` on `A` over the norm
(`arenaObs_regionProj`, `arenaObs_regionProj_mk`). The uncoupled carrier `idxFreeU` of the generic
layer is the whole chain's evolution `chainProp` (`idxFreeU_diracHam_val`), so along it the
expectation at the ray of `ψ` is the weight of `e^{−isH_D} ψ` on `A`
(`arenaObs_regionProj_free_chainRay`).

**The arena.** `regionPointerFlow` is the Hamiltonian flow, for the form of the arena
`ℂℙ^{2M+1} × T²`, of the joint energy `−2⟨H_D⟩ − 2 g f(θ₂)⟨P_A⟩`: the arena `Σ_*` of #349 with the
site projector replaced by the region projector. It moves the carrier by
`exp (−i t (H_D + g f(θ₂) P_A))` and turns the pointer by `κ ∫₀ᵗ⟨P_A⟩`, `κ = −2 g f'(θ₂)`
(`regionPointerFlow_apply`, `diracDisplayed_regionPointerFlow_iff`).

**The arrival.** The ring has at least `640000` sites and physical length `2000π`, with `c = 1`
and rest energy `3`. The carrier is the packet `crossPacket` of #265: `16` momenta about `p₀ = 4`,
velocity `4/5`. The detector is on the far half of the ring, which begins a quarter ring, `500π`,
from the packet's start; the predicted arrival there is at `625π`. Along the free chain the far
half holds at most `1/4` of the weight up to `625π/3` and at least `3/4` between `3125π/3` and
`4375π/3` (#265). The detector's term moves the accumulated weight by at most `|g f(θ₂)| t²`
(#357's comparison). On the arrival fibres (`arrivalFibres`), where

  `6 κ (625π/12 + |g f(θ₂)| (625π/3)²) < 1` and `1 < 3 κ (625π/2 − |g f(θ₂)| (4375π/3)²)`,

from a ready pointer, there is a flow time `τ` in `[625π/3, 4375π/3]` such that the readout
history along `regionPointerFlow` is an `IsRecordWrite` of `true` from time `0` with write
interval `[625π/3, τ]` and window `1/(3κ)` (`regionPointerFlow_arrival_write`). The readout is
not `true` at any time before `625π/3`. The arrival fibres are open
(`isOpen_arrivalFibres`), and for the profile `trainF` and strength `g = 1/(1250π)` they contain
`θ₂ = 0` and have positive measure (`volume_arrivalFibres_trainF_pos`).

## Exact scope

* **A half ring, not a site.** The detector is coupled to the projector on half the ring. The
  record says the carrier has reached that half. It does not locate it within the half.
* **A coarse time.** The write is complete at some `τ` in `[625π/3, 4375π/3]`, an interval that
  contains the predicted arrival `625π` and is seven times longer at its end than at its start.
  `τ` is not computed. No speed is read off the record.
* **Not before, and by.** What is proved is that the record is not written before `625π/3`, when
  the far half holds at most a quarter of the weight, and is written by `4375π/3`. The quarter
  is the packet's tail on the far half: the readout is silent because the accumulated weight is
  small, not because the far half is empty.
* **One packet, one ring.** The numbers are those of #265: `ℓ = 2000π`, at least `640000` sites,
  `16` modes. No family is given, and no scaling.
* **A weak detector.** The strength is of order `1/(1250π)`: the pointer takes the whole transit
  to turn by a third. The back-reaction on the carrier is bounded through `|g f(θ₂)| t²`, and the
  arrival fibres are those where that bound is small. For the profile `trainF` they are a
  neighbourhood of `θ₂ = 0` of positive Haar measure; its size is not computed.
* **One pointer.** There is no emission record, no second detector and no clock on this arena.
  A radar exchange needs all three (M6).
* **A definite fact, not a statistic.** The record is that the accumulated weight on the far
  half crossed the threshold along the one trajectory. No weight of quantum mechanics is derived.
* **The record is held for a window** `1/(3κ)` and then the pointer turns on. All times are flow
  times (UA-7). The readout and the ready arc are apparatus input (UA-4), and the coupling to a
  region projector is a choice (UA-5).

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-4,
UA-5, UA-7, UA-8, UO-12, UO-16, UD-89 to UD-91); `RecordLayer/DiracArrival.lean` (`crossPacket`,
`farHalf`, `crossHop`, `regionWeight`, `chainProp`, `chainProp_crossPacket`,
`regionWeight_cross_far`, `regionWeight_cross_near`, `dirac_arrival`);
`RecordLayer/UnifiedDiracClock.lean` (`idxCarrierU`, `idxFreeU`, `idxPointerShift`,
`hamiltonianFlow_coupledEnergy_reindex`, `abs_integral_arenaObs_idxCarrierU_sub_le`);
`RecordLayer/UnifiedTwoPointer.lean` (`idxPointerShift_ofReal_smul`);
`RecordLayer/DiracPointerWrite.lean` (`chainRay`, `norm_sq_toLp_chain`);
`RecordLayer/DiracPointerThreshold.lean` (`diracDisplayed`, `pshift_mem_displayArc`);
`RecordLayer/DiracPointerRecord.lean` (`pshift_notMem_displayArc_of_le`);
`RecordLayer/RecordOccurrence.lean` (`IsRecordWrite`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### A crossing of the threshold -/

/-- ★★★ **A pointer driven across the threshold writes.** A pointer starts ready and sits at
`pshift (κ ∫₀ᵗ F)`, `F` continuous with values in `[0, 1]`, `κ > 0`. If the displacement is at
most `1/6` at `T₁` and at least `1/3` at `T₃`, there is a time `τ` in `[T₁, T₃]` such that the
readout history is an `IsRecordWrite` of `true` from time `0`, with write interval `[T₁, τ]` and
window `1/(3κ)`. -/
theorem isRecordWrite_of_integral_crossing {F : ℝ → ℝ} (hF : Continuous F)
    (h0 : ∀ s, 0 ≤ F s) (h1 : ∀ s, F s ≤ 1) {κ : ℝ} (hκ : 0 < κ) {T₁ T₃ : ℝ} (hT₁ : 0 ≤ T₁)
    (hT : T₁ ≤ T₃) (hlo : κ * (∫ s in (0 : ℝ)..T₁, F s) ≤ 1 / 6)
    (hhi : 1 / 3 ≤ κ * ∫ s in (0 : ℝ)..T₃, F s) {a : KTorus} (ha : a ∈ readyArc 2)
    {hist : ℝ → Bool}
    (hhist : ∀ t, hist t = true ↔ pshift (κ * ∫ s in (0 : ℝ)..t, F s) a ∈ displayArc) :
    ∃ τ, T₁ ≤ τ ∧ τ ≤ T₃ ∧ IsRecordWrite hist 0 T₁ τ (1 / (3 * κ)) true := by
  have hi : ∀ a b : ℝ, IntervalIntegrable F volume a b := fun a b => hF.intervalIntegrable a b
  obtain ⟨I, hI⟩ : ∃ I : ℝ → ℝ, ∀ t, I t = κ * ∫ s in (0 : ℝ)..t, F s := ⟨_, fun _ => rfl⟩
  have hIc : Continuous I := by
    have hfun : I = fun t => κ * ∫ s in (0 : ℝ)..t, F s := funext hI
    rw [hfun]
    exact continuous_const.mul (intervalIntegral.continuous_primitive hi 0)
  have hsplit : ∀ s t : ℝ, I t = I s + κ * ∫ u in s..t, F u := fun s t => by
    have hsub := intervalIntegral.integral_interval_sub_left (hi 0 t) (hi 0 s)
    rw [hI, hI, ← hsub]
    ring
  have hmono : ∀ {s t : ℝ}, s ≤ t → I s ≤ I t := fun {s t} hst => by
    have hn : 0 ≤ ∫ u in s..t, F u := intervalIntegral.integral_nonneg hst fun u _ => h0 u
    rw [hsplit s t]
    nlinarith
  have hstep : ∀ {s t : ℝ}, s ≤ t → I t ≤ I s + κ * (t - s) := fun {s t} hst => by
    have hle : (∫ u in s..t, F u) ≤ t - s := by
      have h := intervalIntegral.integral_mono_on hst (hi s t)
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume s t)
        (fun u _ => h1 u)
      rwa [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h
    rw [hsplit s t]
    nlinarith
  have hI0 : I 0 = 0 := by rw [hI, intervalIntegral.integral_same, mul_zero]
  rw [← hI] at hlo hhi
  have hhist' : ∀ t, hist t = true ↔ pshift (I t) a ∈ displayArc := fun t => by
    rw [hI]
    exact hhist t
  obtain ⟨τ, hτmem, hτ⟩ : ∃ τ ∈ Set.Icc T₁ T₃, I τ = 1 / 3 :=
    intermediate_value_Icc hT hIc.continuousOn ⟨by linarith, hhi⟩
  refine ⟨τ, hτmem.1, hτmem.2, ⟨hT₁, hτmem.1, by positivity, fun t ht0 ht => ?_,
    fun t ht₁ ht₂ => ?_⟩⟩
  · intro hshown
    refine pshift_notMem_displayArc_of_le ha ?_ ?_ ((hhist' t).1 hshown)
    · have := hmono ht0
      rwa [hI0] at this
    · exact (hmono ht.le).trans hlo
  · refine (hhist' t).2 (pshift_mem_displayArc ha ?_ ?_)
    · rw [← hτ]
      exact hmono ht₁
    · have h := hstep ht₁
      have h2 : t - τ ≤ 1 / (3 * κ) := by linarith
      have h3 : κ * (t - τ) ≤ 1 / 3 := by
        have := mul_le_mul_of_nonneg_left h2 hκ.le
        have e : κ * (1 / (3 * κ)) = 1 / 3 := by
          have hκne : κ ≠ 0 := hκ.ne'
          field_simp
        rwa [e] at this
      linarith

/-! ### A detector on a region of sites -/

section Region

variable {M : ℕ}

/-- **The projector on a region of sites** `A`: `Σ_{k ∈ A} P_k`. -/
def regionProj (A : Finset (ZMod (M + 1))) :
    Matrix (ZMod (M + 1) × Fin 2) (ZMod (M + 1) × Fin 2) ℂ :=
  Matrix.diagonal fun p => if p.1 ∈ A then 1 else 0

theorem regionProj_isHermitian (A : Finset (ZMod (M + 1))) : (regionProj A).IsHermitian := by
  refine Matrix.IsHermitian.ext fun p q => ?_
  simp only [regionProj, Matrix.diagonal_apply]
  by_cases h : p = q
  · subst h
    split_ifs <;> simp
  · simp [h, Ne.symm h]

theorem norm_regionProj_le (A : Finset (ZMod (M + 1))) : ‖regionProj A‖ ≤ 1 := by
  unfold regionProj
  exact Matrix.l2_opNorm_diagonal_le _ zero_le_one fun x => by split_ifs <;> simp

/-- The occupancies of the sites of the ring sum to one. -/
theorem sum_arenaObs_siteProj (p : GenArena (ZMod (M + 1) × Fin 2)) :
    ∑ y : ZMod (M + 1), arenaObs (siteProj y) p = 1 := by
  have h := momentMap_sum_eq_one p
  rw [Fintype.sum_prod_type] at h
  rw [← h]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [arenaObs_siteProj, Fin.sum_univ_two]

/-- ★ **The expectation of the region projector** is the sum of the occupancies of its sites. -/
theorem arenaObs_regionProj (A : Finset (ZMod (M + 1)))
    (p : GenArena (ZMod (M + 1) × Fin 2)) :
    arenaObs (regionProj A) p = ∑ k ∈ A, arenaObs (siteProj k) p := by
  have hc : (fun x : ZMod (M + 1) × Fin 2 => if x.1 ∈ A then (1 : ℂ) else 0)
      = fun x => (((if x.1 ∈ A then (1 : ℝ) else 0 : ℝ)) : ℂ) := by
    funext x
    split_ifs <;> simp
  rw [regionProj, hc, arenaObs_diagonal_ofReal, Fintype.sum_prod_type]
  calc ∑ k : ZMod (M + 1), ∑ c : Fin 2, (if k ∈ A then (1 : ℝ) else 0) * momentMap p (k, c)
      = ∑ k : ZMod (M + 1), if k ∈ A then arenaObs (siteProj k) p else 0 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [arenaObs_siteProj, Fin.sum_univ_two]
        split_ifs <;> simp
    _ = ∑ k ∈ A, arenaObs (siteProj k) p := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem arenaObs_regionProj_nonneg (A : Finset (ZMod (M + 1)))
    (p : GenArena (ZMod (M + 1) × Fin 2)) : 0 ≤ arenaObs (regionProj A) p := by
  rw [arenaObs_regionProj]
  exact Finset.sum_nonneg fun k _ => arenaObs_siteProj_nonneg k p

theorem arenaObs_regionProj_le_one (A : Finset (ZMod (M + 1)))
    (p : GenArena (ZMod (M + 1) × Fin 2)) : arenaObs (regionProj A) p ≤ 1 := by
  rw [arenaObs_regionProj, ← sum_arenaObs_siteProj p]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
    fun k _ _ => arenaObs_siteProj_nonneg k p

/-- At the ray of `v` the expectation of the region projector is the weight of `v` on the region
over its squared norm. -/
theorem arenaObs_regionProj_mk (A : Finset (ZMod (M + 1)))
    {v : EuclideanSpace ℂ (ZMod (M + 1) × Fin 2)} (hv : v ≠ 0) :
    arenaObs (regionProj A) (Projectivization.mk ℂ v hv) = regionWeight v A / ‖v‖ ^ 2 := by
  rw [arenaObs_regionProj, regionWeight, Finset.sum_div]
  exact Finset.sum_congr rfl fun k _ => arenaObs_siteProj_mk k hv

/-- **The uncoupled carrier is the whole chain's evolution**: `exp (−i s H_D) = chainProp`. -/
theorem idxFreeU_diracHam_val (J μ s : ℝ) :
    (idxFreeU (diracHam_isHermitian (L := M + 1) J μ) s).val = chainProp J μ s := by
  rw [idxFreeU_val, chainProp]
  congr 1
  ext a b
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  ring

/-- ★ **Along the uncoupled carrier the expectation of a region projector is the weight on the
region** of the chain state evolved by `e^{−isH_D}`, over the norm. -/
theorem arenaObs_regionProj_free_chainRay (J μ : ℝ) (A : Finset (ZMod (M + 1)))
    {ψ : ZMod (M + 1) × Fin 2 → ℂ} (hψ : ψ ≠ 0) (s : ℝ) :
    arenaObs (regionProj A)
        (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1) J μ) s) (chainRay ψ hψ))
      = regionWeight (chainProp J μ s *ᵥ ψ) A / (chainInner ψ ψ).re := by
  have hU : ((idxFreeU (diracHam_isHermitian (L := M + 1) J μ) s).val)ᴴ
      * (idxFreeU (diracHam_isHermitian (L := M + 1) J μ) s).val = 1 := by
    have hmem := (idxFreeU (diracHam_isHermitian (L := M + 1) J μ) s).property
    rwa [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hmem
  rw [chainRay, arenaKick_mk, arenaObs_regionProj_mk, Matrix.norm_toEuclideanLin_of_isom hU,
    norm_sq_toLp_chain]
  congr 2
  rw [← idxFreeU_diracHam_val]
  rfl

end Region

/-! ### The arena: a pointer coupled to a region -/

section Arena

variable {M : ℕ} {f : ℝ → ℝ} (J μ g : ℝ) (A : Finset (ZMod (M + 1)))
  (hf : Function.Periodic f 1)

/-- A real multiple of the region projector is Hermitian. -/
theorem regionProj_smul_isHermitian : ((g : ℂ) • regionProj A).IsHermitian :=
  isHermitian_ofReal_smul g (regionProj_isHermitian A)

/-- **The joint flow of the Dirac carrier and a pointer coupled to a region**: the Hamiltonian
flow, for the form of `ℂℙ^{2M+1} × T²`, of `−2⟨H_D⟩ − 2 g f(θ₂)⟨P_A⟩`. -/
noncomputable def regionPointerFlow (hc : ContDiff ℝ ∞ f) (t : ℝ) :
    KSigma (2 * M + 1 + 1) → KSigma (2 * M + 1 + 1) :=
  (arenaForm_isSymplectic (2 * M + 1)).hamiltonianFlow
    (contMDiff_coupledEnergy (Matrix.reindex (diracIdx M) (diracIdx M) (diracHam J μ))
      (Matrix.reindex (diracIdx M) (diracIdx M) ((g : ℂ) • regionProj A)) hf hc) t

/-- ★★ **The flow in the carrier's coordinates.** The carrier moves by
`exp (−i t (H_D + g f(θ₂) P_A))`, the pointer's moving angle advances by the displacement of the
generic layer, and `θ₂` is fixed. -/
theorem regionPointerFlow_apply (hc : ContDiff ℝ ∞ f) (t : ℝ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (θ : KTorus) :
    regionPointerFlow J μ g A hf hc t (idxArenaEquiv (diracIdx M) p, θ)
      = (idxArenaEquiv (diracIdx M)
          (arenaKick (idxCarrierU (diracHam_isHermitian J μ)
            (regionProj_smul_isHermitian g A) hf θ.2 t) p),
          (θ.1 + ((idxPointerShift (diracHam_isHermitian J μ)
            (regionProj_smul_isHermitian g A) hf θ.2 p t : ℝ) : AddCircle (1 : ℝ)), θ.2)) :=
  hamiltonianFlow_coupledEnergy_reindex (diracIdx M) (diracHam_isHermitian J μ)
    (regionProj_smul_isHermitian g A) hf hc t p θ

/-- The readout along the flow, in terms of the accumulated weight on the region. -/
theorem diracDisplayed_regionPointerFlow_iff (hc : ContDiff ℝ ∞ f)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (θ : KTorus) (t : ℝ) :
    diracDisplayed M (regionPointerFlow J μ g A hf hc t (idxArenaEquiv (diracIdx M) p, θ)) = true
      ↔ pshift (rateAt g 1 hf θ.2 * ∫ s in (0 : ℝ)..t, arenaObs (regionProj A)
          (arenaKick (idxCarrierU (diracHam_isHermitian J μ)
            (regionProj_smul_isHermitian g A) hf θ.2 s) p)) θ ∈ displayArc := by
  have e : idxPointerShift (diracHam_isHermitian J μ) (regionProj_smul_isHermitian g A) hf θ.2
        p t
      = rateAt g 1 hf θ.2 * ∫ s in (0 : ℝ)..t, arenaObs (regionProj A)
          (arenaKick (idxCarrierU (diracHam_isHermitian J μ)
            (regionProj_smul_isHermitian g A) hf θ.2 s) p) :=
    (idxPointerShift_ofReal_smul g (diracHam_isHermitian J μ) (regionProj_isHermitian A) hf θ.2
      p t).trans (by rw [rateAt, div_one])
  rw [diracDisplayed_eq_true_iff, regionPointerFlow_apply, ← e]
  rfl

/-- ★ **The detector's term moves the accumulated weight on the region by at most
`|g f(θ₂)| t²`.** -/
theorem abs_integral_regionProj_sub_free_le (φ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    |(∫ s in (0 : ℝ)..t, arenaObs (regionProj A)
          (arenaKick (idxCarrierU (diracHam_isHermitian J μ)
            (regionProj_smul_isHermitian g A) hf φ s) p))
        - ∫ s in (0 : ℝ)..t, arenaObs (regionProj A)
          (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1) J μ) s) p)|
      ≤ |g * hf.lift φ| * t ^ 2 := by
  refine (abs_integral_arenaObs_idxCarrierU_sub_le (diracHam_isHermitian J μ)
    (regionProj_smul_isHermitian g A) hf φ (regionProj A) p ht).trans ?_
  have h1 := norm_regionProj_le A
  have h2 : ‖(g : ℂ) • regionProj A‖ ≤ |g| := norm_ofReal_smul_le g h1
  have h3 : ‖regionProj A‖ * (|hf.lift φ| * ‖(g : ℂ) • regionProj A‖) ≤ 1 * (|hf.lift φ| * |g|) :=
    mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)) (by positivity) zero_le_one
  rw [abs_mul, mul_comm |g|]
  nlinarith [sq_nonneg t]

end Arena

/-! ### The arrival -/

section Arrival

variable {M : ℕ} {f : ℝ → ℝ} (g : ℝ) (hf : Function.Periodic f 1)

/-- **The arrival fibres**: the conserved angles `θ₂` at which the pointer's rate `κ` is
positive, the displacement at `625π/3` is below `1/6` and the displacement at `4375π/3` is above
`1/3`, with the detector's back-reaction `|g f(θ₂)| t²` allowed for. -/
def arrivalFibres : Set (AddCircle (1 : ℝ)) :=
  {φ | 0 < rateAt g 1 hf φ
    ∧ 6 * rateAt g 1 hf φ
        * (625 * Real.pi / 12 + |g * hf.lift φ| * (625 * Real.pi / 3) ^ 2) < 1
    ∧ 1 < 3 * rateAt g 1 hf φ
        * (625 * Real.pi / 2 - |g * hf.lift φ| * (4375 * Real.pi / 3) ^ 2)}

/-- The arrival fibres are open. -/
theorem isOpen_arrivalFibres (hf1 : ContDiff ℝ 1 f) : IsOpen (arrivalFibres g hf) := by
  have hκ := continuous_rateAt g 1 hf hf1
  have hb : Continuous fun φ : AddCircle (1 : ℝ) => |g * hf.lift φ| :=
    (continuous_const.mul (continuous_periodicLift hf hf1.continuous)).abs
  exact (isOpen_lt continuous_const hκ).inter
    ((isOpen_lt ((continuous_const.mul hκ).mul
        (continuous_const.add (hb.mul continuous_const))) continuous_const).inter
      (isOpen_lt continuous_const ((continuous_const.mul hκ).mul
        (continuous_const.sub (hb.mul continuous_const)))))

/-- **For the profile `trainF` and the strength `1/(1250π)` the angle `θ₂ = 0` is an arrival
fibre.** -/
theorem zero_mem_arrivalFibres_trainF :
    (0 : AddCircle (1 : ℝ)) ∈ arrivalFibres (1 / (1250 * Real.pi)) trainF_periodic := by
  have hπ := Real.pi_pos
  have hπne : Real.pi ≠ 0 := hπ.ne'
  show _ ∧ _ ∧ _
  rw [rateAt_trainF_zero, trainF_lift_zero]
  simp only [mul_zero, abs_zero, zero_mul, add_zero, sub_zero]
  refine ⟨by positivity, ?_, ?_⟩
  · have e : 6 * (2 * (1 / (1250 * Real.pi))) * (625 * Real.pi / 12) = 1 / 2 := by
      field_simp
      ring
    rw [e]
    norm_num
  · have e : 3 * (2 * (1 / (1250 * Real.pi))) * (625 * Real.pi / 2) = 3 / 2 := by
      field_simp
      ring
    rw [e]
    norm_num

/-- ★★ **The arrival fibres have positive measure** for the profile `trainF` and the strength
`1/(1250π)`. -/
theorem volume_arrivalFibres_trainF_pos :
    0 < volume (arrivalFibres (1 / (1250 * Real.pi)) trainF_periodic) :=
  (isOpen_arrivalFibres _ trainF_periodic (contDiff_trainF.of_le (by simp))).measure_pos volume
    ⟨0, zero_mem_arrivalFibres_trainF⟩

variable (hL : 640000 ≤ M + 1)
include hL

/-- The crossing packet is not zero. -/
theorem crossPacket_ne_zero : crossPacket (L := M + 1) 0 ≠ 0 := fun h => by
  have h1 := (dirac_arrival (L := M + 1) hL (le_refl (0 : ℝ))).2.2.2.2.2.1 0
  rw [h] at h1
  simp [chainInner] at h1

/-- ★★ **Along the uncoupled carrier the expectation of the far half's projector is the crossing
packet's weight on the far half.** -/
theorem arenaObs_farHalf_free_crossPacket (s : ℝ) :
    arenaObs (regionProj (farHalf (M + 1)))
        (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3) s)
          (chainRay (crossPacket (L := M + 1) 0) (crossPacket_ne_zero hL)))
      = regionWeight (crossPacket (L := M + 1) s) (farHalf (M + 1)) := by
  have h1 := (dirac_arrival (L := M + 1) hL (le_refl (0 : ℝ))).2.2.2.2.2.1 0
  rw [arenaObs_regionProj_free_chainRay, chainProp_crossPacket, h1, Complex.one_re, div_one]

/-- ★★★ **A record written on arrival.** On a ring of at least `640000` sites, the carrier is
the crossing packet of #265 and the pointer is coupled to the projector on the far half of the
ring. On an arrival fibre, from a ready pointer, there is a flow time `τ` in
`[625π/3, 4375π/3]` such that the readout history along the joint Hamiltonian flow is an
`IsRecordWrite` of `true` from time `0`, with write interval `[625π/3, τ]` and window `1/(3κ)`,
`κ` the pointer's rate. In particular the readout is not `true` before `625π/3`, while the far
half holds at most a quarter of the packet's weight. The times are flow times (UA-7); the
predicted arrival at the far half is `625π`. -/
theorem regionPointerFlow_arrival_write (hc : ContDiff ℝ ∞ f) {θ : KTorus}
    (hθ : θ ∈ readyArc 2) (hφ : θ.2 ∈ arrivalFibres g hf) :
    ∃ τ, 625 * Real.pi / 3 ≤ τ ∧ τ ≤ 4375 * Real.pi / 3
      ∧ IsRecordWrite
          (fun t => diracDisplayed M
            (regionPointerFlow (crossHop (M + 1)) 3 g (farHalf (M + 1)) hf hc t
              (idxArenaEquiv (diracIdx M)
                (chainRay (crossPacket (L := M + 1) 0) (crossPacket_ne_zero hL)), θ)))
          0 (625 * Real.pi / 3) τ (1 / (3 * rateAt g 1 hf θ.2)) true := by
  obtain ⟨hκ, hlo, hhi⟩ := hφ
  have hπ := Real.pi_pos
  set p := chainRay (crossPacket (L := M + 1) 0) (crossPacket_ne_zero hL) with hp
  set κ := rateAt g 1 hf θ.2 with hκdef
  set b := |g * hf.lift θ.2| with hb
  have hb0 : 0 ≤ b := abs_nonneg _
  have hT₁ : (0 : ℝ) ≤ 625 * Real.pi / 3 := by positivity
  have hT₃ : (0 : ℝ) ≤ 4375 * Real.pi / 3 := by positivity
  have hT : 625 * Real.pi / 3 ≤ 4375 * Real.pi / 3 := by linarith
  have hUc := continuous_idxCarrierU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)
    (regionProj_smul_isHermitian g (farHalf (M + 1))) hf θ.2
  have hFc : Continuous fun s : ℝ => arenaObs (regionProj (farHalf (M + 1)))
      (arenaKick (idxCarrierU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)
        (regionProj_smul_isHermitian g (farHalf (M + 1))) hf θ.2 s) p) :=
    (continuous_arenaObs _).comp (hUc.arenaKick continuous_const)
  have hfree : ∀ s, arenaObs (regionProj (farHalf (M + 1)))
      (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3) s) p)
      = regionWeight (crossPacket (L := M + 1) s) (farHalf (M + 1)) :=
    arenaObs_farHalf_free_crossPacket hL
  have hW : Continuous fun s : ℝ => regionWeight (crossPacket (L := M + 1) s)
      (farHalf (M + 1)) := by
    have h := (continuous_arenaObs (regionProj (farHalf (M + 1)))).comp
      ((continuous_idxFreeU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)).arenaKick
        (continuous_const (y := p)))
    exact h.congr hfree
  have hWi : ∀ a c : ℝ, IntervalIntegrable (fun s : ℝ => regionWeight (crossPacket (L := M + 1) s)
      (farHalf (M + 1))) volume a c := fun a c => hW.intervalIntegrable a c
  -- the free accumulated weight at the two times
  have hfar : (∫ s in (0 : ℝ)..(625 * Real.pi / 3),
      regionWeight (crossPacket (L := M + 1) s) (farHalf (M + 1))) ≤ 625 * Real.pi / 12 := by
    have h := intervalIntegral.integral_mono_on hT₁ (hWi 0 _)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 / 4 : ℝ)) volume 0
        (625 * Real.pi / 3))
      (fun s hs => regionWeight_cross_far hL hs.1 hs.2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    linarith
  have hnear : 625 * Real.pi / 2 ≤ ∫ s in (0 : ℝ)..(4375 * Real.pi / 3),
      regionWeight (crossPacket (L := M + 1) s) (farHalf (M + 1)) := by
    have hmid : (0 : ℝ) ≤ 3125 * Real.pi / 3 := by positivity
    have hle : 3125 * Real.pi / 3 ≤ 4375 * Real.pi / 3 := by linarith
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hWi 0 (3125 * Real.pi / 3))
      (hWi (3125 * Real.pi / 3) (4375 * Real.pi / 3))
    have h0 : 0 ≤ ∫ s in (0 : ℝ)..(3125 * Real.pi / 3),
        regionWeight (crossPacket (L := M + 1) s) (farHalf (M + 1)) :=
      intervalIntegral.integral_nonneg hmid fun s _ => regionWeight_nonneg _ _
    have h := intervalIntegral.integral_mono_on hle
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (3 / 4 : ℝ)) volume
        (3125 * Real.pi / 3) (4375 * Real.pi / 3)) (hWi _ _)
      (fun s hs => regionWeight_cross_near hL hs.1 hs.2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    linarith
  -- the coupled accumulated weight is within the back-reaction of the free one
  have hcmp : ∀ {t : ℝ}, 0 ≤ t →
      |(∫ s in (0 : ℝ)..t, arenaObs (regionProj (farHalf (M + 1)))
          (arenaKick (idxCarrierU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)
            (regionProj_smul_isHermitian g (farHalf (M + 1))) hf θ.2 s) p))
        - ∫ s in (0 : ℝ)..t, regionWeight (crossPacket (L := M + 1) s) (farHalf (M + 1))|
      ≤ b * t ^ 2 := fun {t} ht => by
    have h := abs_integral_regionProj_sub_free_le (crossHop (M + 1)) 3 g (farHalf (M + 1)) hf
      θ.2 p ht
    simp only [hfree] at h
    exact h
  have c₁ := (abs_le.1 (hcmp hT₁)).2
  have c₃ := (abs_le.1 (hcmp hT₃)).1
  have hlo' : κ * (∫ s in (0 : ℝ)..(625 * Real.pi / 3), arenaObs (regionProj (farHalf (M + 1)))
      (arenaKick (idxCarrierU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)
        (regionProj_smul_isHermitian g (farHalf (M + 1))) hf θ.2 s) p)) ≤ 1 / 6 := by
    have h1 : (∫ s in (0 : ℝ)..(625 * Real.pi / 3), arenaObs (regionProj (farHalf (M + 1)))
        (arenaKick (idxCarrierU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)
          (regionProj_smul_isHermitian g (farHalf (M + 1))) hf θ.2 s) p))
        ≤ 625 * Real.pi / 12 + b * (625 * Real.pi / 3) ^ 2 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hκ.le
    linarith
  have hhi' : 1 / 3 ≤ κ * ∫ s in (0 : ℝ)..(4375 * Real.pi / 3),
      arenaObs (regionProj (farHalf (M + 1)))
        (arenaKick (idxCarrierU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)
          (regionProj_smul_isHermitian g (farHalf (M + 1))) hf θ.2 s) p) := by
    have h1 : 625 * Real.pi / 2 - b * (4375 * Real.pi / 3) ^ 2
        ≤ ∫ s in (0 : ℝ)..(4375 * Real.pi / 3), arenaObs (regionProj (farHalf (M + 1)))
          (arenaKick (idxCarrierU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)
            (regionProj_smul_isHermitian g (farHalf (M + 1))) hf θ.2 s) p) := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hκ.le
    linarith
  exact isRecordWrite_of_integral_crossing hFc (fun s => arenaObs_regionProj_nonneg _ _)
    (fun s => arenaObs_regionProj_le_one _ _) hκ hT₁ hT hlo' hhi' hθ
    (diracDisplayed_regionPointerFlow_iff (crossHop (M + 1)) 3 g (farHalf (M + 1)) hf hc p θ)

end Arrival

end CSD.RecordLayer

end
