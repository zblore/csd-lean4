/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedArrivalRecord

/-!
# A departure record and an arrival record in one run

**Category:** 7-SigmaLayer (the record layer). BACKLOG #367 — the author's programme "From `Σ` to
physical spacetime", towards milestone M6; Remainder (a) of #365.
`RecordLayer/UnifiedArrivalRecord.lean` has one pointer, coupled to the far half of a ring, that
writes when a travelling packet arrives. A radar exchange needs a record where the packet leaves
as well, in the same run. This module puts two pointers on the arena of two pointers of #359, one
coupled to the near half of the ring and one to the far half, and reads both records along one
orbit: the near pointer writes by `625π/3`, and the far pointer does not show before `625π/3`
and writes by `4375π/3`.

**Two families of unitaries** (any finite index). If two continuous families satisfy
`‖U s − V s‖ ≤ |s| N` and `‖D‖ ≤ 1`, the accumulated expectations of `D` along them differ by at
most `N t²` (`abs_integral_arenaObs_sub_integral_le`). The carrier with two pointers is within
`|s| (|f(θ₂)| ‖B₀‖ + |h(ψ₂)| ‖C₀‖)` of the uncoupled carrier
(`norm_idxTwoCarrierU_sub_idxFreeU_le`).

**The arena.** `regionTwoFlow` is the flow, on `ℂℙ^{2M+1} × T² × T²`, of the joint energy
`−2⟨H_D⟩ − 2 g₁ f(θ₂)⟨P_A⟩ − 2 g₂ h(ψ₂)⟨P_B⟩` for two regions `A`, `B` of sites: the arena of two
site pointers of #359 with region projectors. Each pointer is turned by its rate times the
accumulated weight on its region along the one carrier orbit
(`echoFstShown_regionTwoFlow_iff`, `echoSiteShown_regionTwoFlow_iff`), and the two detectors
together move an accumulated weight by at most `(|g₁ f(θ₂)| + |g₂ h(ψ₂)|) t²`
(`abs_integral_regionProj_two_sub_free_le`).

**The run.** The ring, the packet and the far half are those of #365. The first pointer is
coupled to the near half, the complement of the far half, and the second to the far half. Along
the free chain the near half holds at least `3/4` of the weight up to `625π/3`
(`arenaObs_nearHalf_free_crossPacket`). On the fibres `departureArrivalFibres`, with
`b = |g₁ f(θ₂)| + |g₂ h(ψ₂)|`,

  `1 < 3 κ₁ (625π/4 − b (625π/3)²)`,
  `6 κ₂ (625π/12 + b (625π/3)²) < 1`, `1 < 3 κ₂ (625π/2 − b (4375π/3)²)`,

from two ready pointers there are flow times `τ_d ≤ 625π/3 ≤ τ_a ≤ 4375π/3` such that, along the
one orbit of `regionTwoFlow`:

* the near pointer's readout history is an `IsRecordWrite` of `true` from time `0` with write
  interval `[0, τ_d]` and window `1/(3κ₁)`;
* the far pointer's readout history is an `IsRecordWrite` of `true` from time `0` with write
  interval `[625π/3, τ_a]` and window `1/(3κ₂)`

(`regionTwoFlow_departure_arrival`). The departure write is complete by `625π/3` and the arrival
readout is not `true` before `625π/3`. The fibres are open, and for both profiles `trainF` and
strengths `g₁ = 1/(625π)`, `g₂ = 1/(1250π)` they contain `(0, 0)` and have positive measure
(`volume_departureArrivalFibres_trainF_pos`).

## Exact scope

* **Departure, not emission.** The packet is prepared on the near half. The near pointer
  records that accumulated weight on that half crossed the threshold. Nothing emits it, and no
  event of emission is singled out: the write is complete at some `τ_d` in `[0, 625π/3]`. With
  write interval `[0, τ_d]` the not-displayed-before clause of `IsRecordWrite` is empty: the
  statement is that the near readout is `true` through `[τ_d, τ_d + 1/(3κ₁)]`. That it is not
  `true` at the start follows from the ready arc and is not part of the theorem.
* **The order is through one time.** The departure write is complete by `625π/3`, and the
  arrival readout does not show before `625π/3`. The two could meet at that time. Both
  thresholds read accumulated weight: with a constant far-half weight between `1/7` and `1/4`
  both conclusions would still hold (a calculation, not in Lean), so the order does not certify
  a transit. `τ_d` and
  `τ_a` are found by the intermediate value theorem and are not computed, so no transit time
  and no speed are read off the two records.
* **Half rings.** Each detector is on half the ring. Each record says that the accumulated
  weight on its half crossed the threshold. It locates nothing within the half.
* **One packet, one ring, weak detectors**, as in #365. The back-reaction of both detectors is
  inside the statement through `b t²`, and the fibres are where it is small: a neighbourhood of
  `(0, 0)` for `trainF`, of positive Haar measure, whose size is not computed. The carrier is
  one ray, so no measure of the set of start points is stated.
* **No clock.** The arena has two pointers and both are detectors. A time read by a clock at
  either record needs a third pointer (M6). The arena with three pointer tori is
  `LF4/TriCoupledFlow.lean` (#368).
* **Definite facts, not statistics.** No weight of quantum mechanics is derived. Each record is
  held for its window and then its pointer turns on.
* **All times are flow times** (UA-7). The readouts and ready arcs are apparatus input (UA-4),
  and the couplings to region projectors are choices (UA-5, UA-13).

A statement on this flow and start that no carrier with a constant far-half occupancy
satisfies, at the level of accumulated occupancies, is
`RecordLayer/UnifiedTransitCertificate.lean` (#373).

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-4,
UA-5, UA-7, UA-8, UA-13, UO-16, UD-93, UD-94); `RecordLayer/UnifiedArrivalRecord.lean`
(`regionProj`, `isRecordWrite_of_integral_crossing`, `arenaObs_farHalf_free_crossPacket`,
`crossPacket_ne_zero`); `RecordLayer/UnifiedTwoPointer.lean` (`twoCoupledFlow_reindex`,
`idxTwoCarrierU`, `idxTwoShiftFst_ofReal_smul`, `idxTwoShiftSnd_ofReal_smul`);
`RecordLayer/UnifiedTwoSiteRecords.lean` (`echoFstShown`); `RecordLayer/DiracArrival.lean`
(`crossPacket`, `farHalf`, `regionWeight_cross_far`, `regionWeight_cross_near`,
`regionWeight_add_compl`); `LF4/EchoVolume.lean` (`twoCoupledFlow`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### Two families of unitaries -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- ★ **Accumulated expectations along two families of unitaries** that stay within `|s| N` of
each other differ by at most `N t²`, for an observable of norm at most one. -/
theorem abs_integral_arenaObs_sub_integral_le {U V : ℝ → Matrix.unitaryGroup ι ℂ}
    (hUc : Continuous U) (hVc : Continuous V) {N : ℝ}
    (hUV : ∀ s, ‖(U s).val - (V s).val‖ ≤ |s| * N) {D : Matrix ι ι ℂ} (hD : ‖D‖ ≤ 1)
    (p : GenArena ι) {t : ℝ} (ht : 0 ≤ t) :
    |(∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (U s) p))
        - ∫ s in (0 : ℝ)..t, arenaObs D (arenaKick (V s) p)| ≤ N * t ^ 2 := by
  have hU : Continuous fun s : ℝ => arenaObs D (arenaKick (U s) p) :=
    (continuous_arenaObs D).comp (hUc.arenaKick continuous_const)
  have hV : Continuous fun s : ℝ => arenaObs D (arenaKick (V s) p) :=
    (continuous_arenaObs D).comp (hVc.arenaKick continuous_const)
  rw [← intervalIntegral.integral_sub (hU.intervalIntegrable 0 t) (hV.intervalIntegrable 0 t)]
  have hlin : Continuous fun s : ℝ => 2 * s * N := by fun_prop
  refine (intervalIntegral.abs_integral_le_integral_abs ht).trans ?_
  refine (intervalIntegral.integral_mono_on ht ((hU.sub hV).abs.intervalIntegrable 0 t)
    (hlin.intervalIntegrable 0 t) fun s hs => ?_).trans_eq ?_
  · have h := abs_arenaObs_arenaKick_sub_le (U s) (V s) D p
    have hs' := hUV s
    rw [abs_of_nonneg hs.1] at hs'
    have h0 : 0 ≤ ‖(U s).val - (V s).val‖ := norm_nonneg _
    have h1 := mul_le_mul_of_nonneg_right hD h0
    show |arenaObs D (arenaKick (U s) p) - arenaObs D (arenaKick (V s) p)| ≤ 2 * s * N
    linarith
  · rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_id]
    ring

variable {f h : ℝ → ℝ} {A₀ B₀ C₀ : Matrix ι ι ℂ}

/-- The carrier with two pointers is within `|s| (|f(φ)| ‖B₀‖ + |h(χ)| ‖C₀‖)` of the uncoupled
carrier. -/
theorem norm_idxTwoCarrierU_sub_idxFreeU_le (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hC : C₀.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (φ χ : AddCircle (1 : ℝ)) (s : ℝ) :
    ‖(idxTwoCarrierU hA hB hC hf hh φ χ s).val - (idxFreeU hA s).val‖
      ≤ |s| * (|hf.lift φ| * ‖B₀‖ + |hh.lift χ| * ‖C₀‖) := by
  rw [idxTwoCarrierU_val, idxFreeU_val]
  refine (Matrix.norm_exp_smul_neg_I_sub_le _ _ (idxTwoH_isHermitian hA hB hC hf hh φ χ) hA
    s).trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg s))
  have hd : idxTwoH A₀ B₀ C₀ hf hh φ χ - A₀
      = ((hf.lift φ : ℝ) : ℂ) • B₀ + ((hh.lift χ : ℝ) : ℂ) • C₀ := by
    rw [idxTwoH, add_assoc, add_sub_cancel_left]
  rw [hd]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]

end Generic

/-! ### The arena: two pointers coupled to two regions -/

section Arena

variable {M : ℕ} {f h : ℝ → ℝ} (J μ g₁ g₂ : ℝ) (A B : Finset (ZMod (M + 1)))
  (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)

/-- **The joint flow of the Dirac carrier and two pointers coupled to two regions**: the flow,
for the form of `ℂℙ^{2M+1} × T² × T²`, of
`−2⟨H_D⟩ − 2 g₁ f(θ₂)⟨P_A⟩ − 2 g₂ h(ψ₂)⟨P_B⟩`. -/
noncomputable def regionTwoFlow (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (t : ℝ) :
    EchoSigma (2 * M + 1) → EchoSigma (2 * M + 1) :=
  twoCoupledFlow (Matrix.reindex (diracIdx M) (diracIdx M) (diracHam J μ))
    (Matrix.reindex (diracIdx M) (diracIdx M) ((g₁ : ℂ) • regionProj A))
    (Matrix.reindex (diracIdx M) (diracIdx M) ((g₂ : ℂ) • regionProj B)) hf hh hc hch t

/-- ★★ **The flow in the carrier's coordinates.** The carrier moves by the one propagator with
both region terms in its generator, each pointer advances by its displacement along that orbit,
and both conserved angles are fixed. -/
theorem regionTwoFlow_apply (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (t : ℝ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (θ ψ : KTorus) :
    regionTwoFlow J μ g₁ g₂ A B hf hh hc hch t ((idxArenaEquiv (diracIdx M) p, θ), ψ)
      = ((idxArenaEquiv (diracIdx M)
            (arenaKick (idxTwoCarrierU (diracHam_isHermitian J μ)
              (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B) hf hh
              θ.2 ψ.2 t) p),
          (θ.1 + ((idxTwoShiftFst (diracHam_isHermitian J μ)
              (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B) hf hh
              θ.2 ψ.2 p t : ℝ) : AddCircle (1 : ℝ)), θ.2)),
         (ψ.1 + ((idxTwoShiftSnd (diracHam_isHermitian J μ)
              (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B) hf hh
              θ.2 ψ.2 p t : ℝ) : AddCircle (1 : ℝ)), ψ.2)) :=
  twoCoupledFlow_reindex (diracIdx M) (diracHam_isHermitian J μ)
    (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B) hf hh hc hch t p θ ψ

/-- The first readout along the flow, in terms of the accumulated weight on the first region. -/
theorem echoFstShown_regionTwoFlow_iff (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (θ ψ : KTorus) (t : ℝ) :
    echoFstShown (2 * M + 1)
        (regionTwoFlow J μ g₁ g₂ A B hf hh hc hch t
          ((idxArenaEquiv (diracIdx M) p, θ), ψ)) = true
      ↔ pshift (rateAt g₁ 1 hf θ.2 * ∫ s in (0 : ℝ)..t, arenaObs (regionProj A)
          (arenaKick (idxTwoCarrierU (diracHam_isHermitian J μ)
            (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B) hf hh
            θ.2 ψ.2 s) p)) θ ∈ displayArc := by
  have e : idxTwoShiftFst (diracHam_isHermitian J μ) (regionProj_smul_isHermitian g₁ A)
        (regionProj_smul_isHermitian g₂ B) hf hh θ.2 ψ.2 p t
      = rateAt g₁ 1 hf θ.2 * ∫ s in (0 : ℝ)..t, arenaObs (regionProj A)
          (arenaKick (idxTwoCarrierU (diracHam_isHermitian J μ)
            (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B) hf hh
            θ.2 ψ.2 s) p) :=
    (idxTwoShiftFst_ofReal_smul g₁ (diracHam_isHermitian J μ) (regionProj_isHermitian A)
      (regionProj_smul_isHermitian g₂ B) hf hh θ.2 ψ.2 p t).trans (by rw [rateAt, div_one])
  rw [echoFstShown_eq_true_iff, regionTwoFlow_apply, ← e]
  rfl

/-- The second readout along the flow, in terms of the accumulated weight on the second
region. -/
theorem echoSiteShown_regionTwoFlow_iff (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (θ ψ : KTorus) (t : ℝ) :
    echoSiteShown (2 * M + 1)
        (regionTwoFlow J μ g₁ g₂ A B hf hh hc hch t
          ((idxArenaEquiv (diracIdx M) p, θ), ψ)) = true
      ↔ pshift (rateAt g₂ 1 hh ψ.2 * ∫ s in (0 : ℝ)..t, arenaObs (regionProj B)
          (arenaKick (idxTwoCarrierU (diracHam_isHermitian J μ)
            (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B) hf hh
            θ.2 ψ.2 s) p)) ψ ∈ displayArc := by
  have e : idxTwoShiftSnd (diracHam_isHermitian J μ) (regionProj_smul_isHermitian g₁ A)
        (regionProj_smul_isHermitian g₂ B) hf hh θ.2 ψ.2 p t
      = rateAt g₂ 1 hh ψ.2 * ∫ s in (0 : ℝ)..t, arenaObs (regionProj B)
          (arenaKick (idxTwoCarrierU (diracHam_isHermitian J μ)
            (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B) hf hh
            θ.2 ψ.2 s) p) :=
    (idxTwoShiftSnd_ofReal_smul g₂ (diracHam_isHermitian J μ)
      (regionProj_smul_isHermitian g₁ A) (regionProj_isHermitian B) hf hh θ.2 ψ.2 p
      t).trans (by rw [rateAt, div_one])
  rw [echoSiteShown_eq_true_iff, regionTwoFlow_apply, ← e]
  rfl

/-- ★ **The two detectors together move an accumulated weight by at most
`(|g₁ f(θ₂)| + |g₂ h(ψ₂)|) t²`**, for any region. -/
theorem abs_integral_regionProj_two_sub_free_le (C : Finset (ZMod (M + 1)))
    (φ χ : AddCircle (1 : ℝ)) (p : GenArena (ZMod (M + 1) × Fin 2)) {t : ℝ} (ht : 0 ≤ t) :
    |(∫ s in (0 : ℝ)..t, arenaObs (regionProj C)
          (arenaKick (idxTwoCarrierU (diracHam_isHermitian J μ)
            (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B) hf hh
            φ χ s) p))
        - ∫ s in (0 : ℝ)..t, arenaObs (regionProj C)
          (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1) J μ) s) p)|
      ≤ (|g₁ * hf.lift φ| + |g₂ * hh.lift χ|) * t ^ 2 := by
  refine abs_integral_arenaObs_sub_integral_le
    (continuous_idxTwoCarrierU _ _ _ hf hh φ χ) (continuous_idxFreeU _) (fun s => ?_)
    (norm_regionProj_le C) p ht
  refine (norm_idxTwoCarrierU_sub_idxFreeU_le (diracHam_isHermitian J μ)
    (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B) hf hh φ χ s).trans
    (mul_le_mul_of_nonneg_left ?_ (abs_nonneg s))
  have h1 : ‖(g₁ : ℂ) • regionProj A‖ ≤ |g₁| := norm_ofReal_smul_le g₁ (norm_regionProj_le A)
  have h2 : ‖(g₂ : ℂ) • regionProj B‖ ≤ |g₂| := norm_ofReal_smul_le g₂ (norm_regionProj_le B)
  rw [abs_mul, abs_mul, mul_comm |g₁|, mul_comm |g₂|]
  exact add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
    (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))

end Arena

/-! ### The run -/

section Run

variable {M : ℕ} {f h : ℝ → ℝ} (g₁ g₂ : ℝ) (hf : Function.Periodic f 1)
  (hh : Function.Periodic h 1)

/-- **The departure-and-arrival fibres**: the pairs of conserved angles `(θ₂, ψ₂)` at which both
rates are positive, the near pointer's displacement at `625π/3` is above `1/3`, and the far
pointer's is below `1/6` at `625π/3` and above `1/3` at `4375π/3`, with the back-reaction
`(|g₁ f(θ₂)| + |g₂ h(ψ₂)|) t²` of both detectors allowed for. -/
def departureArrivalFibres : Set (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) :=
  {x | 0 < rateAt g₁ 1 hf x.1 ∧ 0 < rateAt g₂ 1 hh x.2
    ∧ 1 < 3 * rateAt g₁ 1 hf x.1
        * (625 * Real.pi / 4
          - (|g₁ * hf.lift x.1| + |g₂ * hh.lift x.2|) * (625 * Real.pi / 3) ^ 2)
    ∧ 6 * rateAt g₂ 1 hh x.2
        * (625 * Real.pi / 12
          + (|g₁ * hf.lift x.1| + |g₂ * hh.lift x.2|) * (625 * Real.pi / 3) ^ 2) < 1
    ∧ 1 < 3 * rateAt g₂ 1 hh x.2
        * (625 * Real.pi / 2
          - (|g₁ * hf.lift x.1| + |g₂ * hh.lift x.2|) * (4375 * Real.pi / 3) ^ 2)}

/-- The departure-and-arrival fibres are open. -/
theorem isOpen_departureArrivalFibres (hf1 : ContDiff ℝ 1 f) (hh1 : ContDiff ℝ 1 h) :
    IsOpen (departureArrivalFibres g₁ g₂ hf hh) := by
  have hκ₁ : Continuous fun x : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) => rateAt g₁ 1 hf x.1 :=
    (continuous_rateAt g₁ 1 hf hf1).comp continuous_fst
  have hκ₂ : Continuous fun x : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) => rateAt g₂ 1 hh x.2 :=
    (continuous_rateAt g₂ 1 hh hh1).comp continuous_snd
  have hb : Continuous fun x : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
      |g₁ * hf.lift x.1| + |g₂ * hh.lift x.2| :=
    (continuous_const.mul
        ((continuous_periodicLift hf hf1.continuous).comp continuous_fst)).abs.add
      (continuous_const.mul
        ((continuous_periodicLift hh hh1.continuous).comp continuous_snd)).abs
  exact (isOpen_lt continuous_const hκ₁).inter
    ((isOpen_lt continuous_const hκ₂).inter
      ((isOpen_lt continuous_const ((continuous_const.mul hκ₁).mul
          (continuous_const.sub (hb.mul continuous_const)))).inter
        ((isOpen_lt ((continuous_const.mul hκ₂).mul
            (continuous_const.add (hb.mul continuous_const))) continuous_const).inter
          (isOpen_lt continuous_const ((continuous_const.mul hκ₂).mul
            (continuous_const.sub (hb.mul continuous_const)))))))

/-- **For both profiles `trainF` and the strengths `1/(625π)`, `1/(1250π)` the pair `(0, 0)` is
a departure-and-arrival fibre.** -/
theorem zero_mem_departureArrivalFibres_trainF :
    ((0 : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ)))
      ∈ departureArrivalFibres (1 / (625 * Real.pi)) (1 / (1250 * Real.pi)) trainF_periodic
          trainF_periodic := by
  have hπ := Real.pi_pos
  have hπne : Real.pi ≠ 0 := hπ.ne'
  show _ ∧ _ ∧ _ ∧ _ ∧ _
  rw [rateAt_trainF_zero, rateAt_trainF_zero, trainF_lift_zero]
  simp only [mul_zero, abs_zero, zero_mul, add_zero, sub_zero]
  have e₁ : 3 * (2 * (1 / (625 * Real.pi))) * (625 * Real.pi / 4) = 3 / 2 := by
    field_simp
    ring
  have e₂ : 6 * (2 * (1 / (1250 * Real.pi))) * (625 * Real.pi / 12) = 1 / 2 := by
    field_simp
    ring
  have e₃ : 3 * (2 * (1 / (1250 * Real.pi))) * (625 * Real.pi / 2) = 3 / 2 := by
    field_simp
    ring
  rw [e₁, e₂, e₃]
  exact ⟨by positivity, by positivity, by norm_num, by norm_num, by norm_num⟩

/-- ★★ **The departure-and-arrival fibres have positive measure** for both profiles `trainF`
and the strengths `1/(625π)`, `1/(1250π)`. -/
theorem volume_departureArrivalFibres_trainF_pos :
    0 < volume (departureArrivalFibres (1 / (625 * Real.pi)) (1 / (1250 * Real.pi))
      trainF_periodic trainF_periodic) :=
  (isOpen_departureArrivalFibres _ _ trainF_periodic trainF_periodic
    (contDiff_trainF.of_le (by simp)) (contDiff_trainF.of_le (by simp))).measure_pos volume
    ⟨(0, 0), zero_mem_departureArrivalFibres_trainF⟩

variable (hL : 640000 ≤ M + 1)
include hL

/-- The crossing packet's weight on the far half is continuous in time. -/
theorem continuous_regionWeight_crossPacket :
    Continuous fun s : ℝ => regionWeight (crossPacket (L := M + 1) s) (farHalf (M + 1)) := by
  have h := (continuous_arenaObs (regionProj (farHalf (M + 1)))).comp
    ((continuous_idxFreeU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)).arenaKick
      (continuous_const
        (y := chainRay (crossPacket (L := M + 1) 0) (crossPacket_ne_zero hL))))
  exact h.congr (arenaObs_farHalf_free_crossPacket hL)

/-- Up to `625π/3` the far half has accumulated at most `625π/12` of the packet's weight. -/
theorem integral_regionWeight_crossPacket_le :
    (∫ s in (0 : ℝ)..(625 * Real.pi / 3),
      regionWeight (crossPacket (L := M + 1) s) (farHalf (M + 1))) ≤ 625 * Real.pi / 12 := by
  have hπ := Real.pi_pos
  have hT₁ : (0 : ℝ) ≤ 625 * Real.pi / 3 := by positivity
  have h := intervalIntegral.integral_mono_on hT₁
    ((continuous_regionWeight_crossPacket hL).intervalIntegrable 0 _)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 / 4 : ℝ)) volume 0
      (625 * Real.pi / 3))
    (fun s hs => regionWeight_cross_far hL hs.1 hs.2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith

/-- By `4375π/3` the far half has accumulated at least `625π/2` of the packet's weight. -/
theorem le_integral_regionWeight_crossPacket :
    625 * Real.pi / 2 ≤ ∫ s in (0 : ℝ)..(4375 * Real.pi / 3),
      regionWeight (crossPacket (L := M + 1) s) (farHalf (M + 1)) := by
  have hπ := Real.pi_pos
  have hWi : ∀ a c : ℝ, IntervalIntegrable (fun s : ℝ => regionWeight (crossPacket (L := M + 1) s)
      (farHalf (M + 1))) volume a c := fun a c =>
    (continuous_regionWeight_crossPacket hL).intervalIntegrable a c
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

/-- ★★ **Along the uncoupled carrier the expectation of the near half's projector is one minus
the crossing packet's weight on the far half.** -/
theorem arenaObs_nearHalf_free_crossPacket (s : ℝ) :
    arenaObs (regionProj (farHalf (M + 1))ᶜ)
        (arenaKick (idxFreeU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3) s)
          (chainRay (crossPacket (L := M + 1) 0) (crossPacket_ne_zero hL)))
      = 1 - regionWeight (crossPacket (L := M + 1) s) (farHalf (M + 1)) := by
  have h0 := (dirac_arrival (L := M + 1) hL (le_refl (0 : ℝ))).2.2.2.2.2.1 0
  have hs := (dirac_arrival (L := M + 1) hL (le_refl (0 : ℝ))).2.2.2.2.2.1 s
  have hadd := regionWeight_add_compl (crossPacket (L := M + 1) s) (farHalf (M + 1))
  rw [hs, Complex.one_re] at hadd
  rw [arenaObs_regionProj_free_chainRay, chainProp_crossPacket, h0, Complex.one_re, div_one]
  linarith

/-- ★★★ **A departure record and an arrival record in one run.** On a ring of at least `640000`
sites, the carrier is the crossing packet of #265, the first pointer is coupled to the near half
of the ring and the second to the far half. On a departure-and-arrival fibre, from two ready
pointers, there are flow times `τ_d ≤ 625π/3 ≤ τ_a ≤ 4375π/3` such that along the one orbit of
`regionTwoFlow` the near readout's history is an `IsRecordWrite` of `true` with write interval
`[0, τ_d]` and window `1/(3κ₁)`, and the far readout's history is an `IsRecordWrite` of `true`
with write interval `[625π/3, τ_a]` and window `1/(3κ₂)`. The times are flow times (UA-7). -/
theorem regionTwoFlow_departure_arrival (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    {θ ψ : KTorus} (hθ : θ ∈ readyArc 2) (hψ : ψ ∈ readyArc 2)
    (hx : (θ.2, ψ.2) ∈ departureArrivalFibres g₁ g₂ hf hh) :
    ∃ τd τa : ℝ, 0 ≤ τd ∧ τd ≤ 625 * Real.pi / 3 ∧ 625 * Real.pi / 3 ≤ τa
      ∧ τa ≤ 4375 * Real.pi / 3
      ∧ IsRecordWrite
          (fun t => echoFstShown (2 * M + 1)
            (regionTwoFlow (crossHop (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) hf hh
              hc hch t ((idxArenaEquiv (diracIdx M)
                (chainRay (crossPacket (L := M + 1) 0) (crossPacket_ne_zero hL)), θ), ψ)))
          0 0 τd (1 / (3 * rateAt g₁ 1 hf θ.2)) true
      ∧ IsRecordWrite
          (fun t => echoSiteShown (2 * M + 1)
            (regionTwoFlow (crossHop (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) hf hh
              hc hch t ((idxArenaEquiv (diracIdx M)
                (chainRay (crossPacket (L := M + 1) 0) (crossPacket_ne_zero hL)), θ), ψ)))
          0 (625 * Real.pi / 3) τa (1 / (3 * rateAt g₂ 1 hh ψ.2)) true := by
  obtain ⟨hκ₁, hκ₂, hdep, hlo, hhi⟩ := hx
  have hπ := Real.pi_pos
  set p := chainRay (crossPacket (L := M + 1) 0) (crossPacket_ne_zero hL) with hp
  set κ₁ := rateAt g₁ 1 hf θ.2 with hκ₁def
  set κ₂ := rateAt g₂ 1 hh ψ.2 with hκ₂def
  set b := |g₁ * hf.lift θ.2| + |g₂ * hh.lift ψ.2| with hb
  have hT₁ : (0 : ℝ) ≤ 625 * Real.pi / 3 := by positivity
  have hT₃ : (0 : ℝ) ≤ 4375 * Real.pi / 3 := by positivity
  have hT : 625 * Real.pi / 3 ≤ 4375 * Real.pi / 3 := by linarith
  have hUc := continuous_idxTwoCarrierU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)
    (regionProj_smul_isHermitian g₁ (farHalf (M + 1))ᶜ)
    (regionProj_smul_isHermitian g₂ (farHalf (M + 1))) hf hh θ.2 ψ.2
  have hW := continuous_regionWeight_crossPacket hL
  have hWi : ∀ a c : ℝ, IntervalIntegrable (fun s : ℝ => regionWeight (crossPacket (L := M + 1) s)
      (farHalf (M + 1))) volume a c := fun a c => hW.intervalIntegrable a c
  have hfar := integral_regionWeight_crossPacket_le hL
  have hnear := le_integral_regionWeight_crossPacket hL
  -- the far half: coupled against free
  have cF : ∀ {t : ℝ}, 0 ≤ t →
      |(∫ s in (0 : ℝ)..t, arenaObs (regionProj (farHalf (M + 1)))
          (arenaKick (idxTwoCarrierU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)
            (regionProj_smul_isHermitian g₁ (farHalf (M + 1))ᶜ)
            (regionProj_smul_isHermitian g₂ (farHalf (M + 1))) hf hh θ.2 ψ.2 s) p))
        - ∫ s in (0 : ℝ)..t, regionWeight (crossPacket (L := M + 1) s) (farHalf (M + 1))|
      ≤ b * t ^ 2 := fun {t} ht => by
    have h := abs_integral_regionProj_two_sub_free_le (crossHop (M + 1)) 3 g₁ g₂
      (farHalf (M + 1))ᶜ (farHalf (M + 1)) hf hh (farHalf (M + 1)) θ.2 ψ.2 p ht
    simp only [hp, arenaObs_farHalf_free_crossPacket hL] at h
    exact h
  -- the near half: coupled against free
  have cN : |(∫ s in (0 : ℝ)..(625 * Real.pi / 3), arenaObs (regionProj (farHalf (M + 1))ᶜ)
          (arenaKick (idxTwoCarrierU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)
            (regionProj_smul_isHermitian g₁ (farHalf (M + 1))ᶜ)
            (regionProj_smul_isHermitian g₂ (farHalf (M + 1))) hf hh θ.2 ψ.2 s) p))
        - ∫ s in (0 : ℝ)..(625 * Real.pi / 3),
            (1 - regionWeight (crossPacket (L := M + 1) s) (farHalf (M + 1)))|
      ≤ b * (625 * Real.pi / 3) ^ 2 := by
    have h := abs_integral_regionProj_two_sub_free_le (crossHop (M + 1)) 3 g₁ g₂
      (farHalf (M + 1))ᶜ (farHalf (M + 1)) hf hh (farHalf (M + 1))ᶜ θ.2 ψ.2 p hT₁
    simp only [hp, arenaObs_nearHalf_free_crossPacket hL] at h
    exact h
  have hNfree : (∫ s in (0 : ℝ)..(625 * Real.pi / 3),
      (1 - regionWeight (crossPacket (L := M + 1) s) (farHalf (M + 1))))
      = 625 * Real.pi / 3 - ∫ s in (0 : ℝ)..(625 * Real.pi / 3),
          regionWeight (crossPacket (L := M + 1) s) (farHalf (M + 1)) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hWi 0 _),
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  rw [hNfree] at cN
  have cN' := (abs_le.1 cN).1
  have c₁ := (abs_le.1 (cF hT₁)).2
  have c₃ := (abs_le.1 (cF hT₃)).1
  -- the departure write
  have hdep' : 1 / 3 ≤ κ₁ * ∫ s in (0 : ℝ)..(625 * Real.pi / 3),
      arenaObs (regionProj (farHalf (M + 1))ᶜ)
        (arenaKick (idxTwoCarrierU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)
          (regionProj_smul_isHermitian g₁ (farHalf (M + 1))ᶜ)
          (regionProj_smul_isHermitian g₂ (farHalf (M + 1))) hf hh θ.2 ψ.2 s) p) := by
    have h1 : 625 * Real.pi / 4 - b * (625 * Real.pi / 3) ^ 2
        ≤ ∫ s in (0 : ℝ)..(625 * Real.pi / 3), arenaObs (regionProj (farHalf (M + 1))ᶜ)
          (arenaKick (idxTwoCarrierU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)
            (regionProj_smul_isHermitian g₁ (farHalf (M + 1))ᶜ)
            (regionProj_smul_isHermitian g₂ (farHalf (M + 1))) hf hh θ.2 ψ.2 s) p) := by
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hκ₁.le
    linarith
  have hzero : κ₁ * (∫ s in (0 : ℝ)..(0 : ℝ), arenaObs (regionProj (farHalf (M + 1))ᶜ)
      (arenaKick (idxTwoCarrierU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)
        (regionProj_smul_isHermitian g₁ (farHalf (M + 1))ᶜ)
        (regionProj_smul_isHermitian g₂ (farHalf (M + 1))) hf hh θ.2 ψ.2 s) p)) ≤ 1 / 6 := by
    rw [intervalIntegral.integral_same, mul_zero]
    norm_num
  obtain ⟨τd, hτd0, hτd, hwd⟩ := isRecordWrite_of_integral_crossing
    ((continuous_arenaObs (regionProj (farHalf (M + 1))ᶜ)).comp
      (hUc.arenaKick (continuous_const (y := p))))
    (fun s => arenaObs_regionProj_nonneg _ _) (fun s => arenaObs_regionProj_le_one _ _) hκ₁
    (le_refl (0 : ℝ)) hT₁ hzero hdep' hθ
    (echoFstShown_regionTwoFlow_iff (crossHop (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
      (farHalf (M + 1)) hf hh hc hch p θ ψ)
  -- the arrival write
  have hlo' : κ₂ * (∫ s in (0 : ℝ)..(625 * Real.pi / 3), arenaObs (regionProj (farHalf (M + 1)))
      (arenaKick (idxTwoCarrierU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)
        (regionProj_smul_isHermitian g₁ (farHalf (M + 1))ᶜ)
        (regionProj_smul_isHermitian g₂ (farHalf (M + 1))) hf hh θ.2 ψ.2 s) p)) ≤ 1 / 6 := by
    have h1 : (∫ s in (0 : ℝ)..(625 * Real.pi / 3), arenaObs (regionProj (farHalf (M + 1)))
        (arenaKick (idxTwoCarrierU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)
          (regionProj_smul_isHermitian g₁ (farHalf (M + 1))ᶜ)
          (regionProj_smul_isHermitian g₂ (farHalf (M + 1))) hf hh θ.2 ψ.2 s) p))
        ≤ 625 * Real.pi / 12 + b * (625 * Real.pi / 3) ^ 2 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hκ₂.le
    linarith
  have hhi' : 1 / 3 ≤ κ₂ * ∫ s in (0 : ℝ)..(4375 * Real.pi / 3),
      arenaObs (regionProj (farHalf (M + 1)))
        (arenaKick (idxTwoCarrierU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)
          (regionProj_smul_isHermitian g₁ (farHalf (M + 1))ᶜ)
          (regionProj_smul_isHermitian g₂ (farHalf (M + 1))) hf hh θ.2 ψ.2 s) p) := by
    have h1 : 625 * Real.pi / 2 - b * (4375 * Real.pi / 3) ^ 2
        ≤ ∫ s in (0 : ℝ)..(4375 * Real.pi / 3), arenaObs (regionProj (farHalf (M + 1)))
          (arenaKick (idxTwoCarrierU (diracHam_isHermitian (L := M + 1) (crossHop (M + 1)) 3)
            (regionProj_smul_isHermitian g₁ (farHalf (M + 1))ᶜ)
            (regionProj_smul_isHermitian g₂ (farHalf (M + 1))) hf hh θ.2 ψ.2 s) p) := by
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hκ₂.le
    linarith
  obtain ⟨τa, hτa0, hτa, hwa⟩ := isRecordWrite_of_integral_crossing
    ((continuous_arenaObs (regionProj (farHalf (M + 1)))).comp
      (hUc.arenaKick (continuous_const (y := p))))
    (fun s => arenaObs_regionProj_nonneg _ _) (fun s => arenaObs_regionProj_le_one _ _) hκ₂
    hT₁ hT hlo' hhi' hψ
    (echoSiteShown_regionTwoFlow_iff (crossHop (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
      (farHalf (M + 1)) hf hh hc hch p θ ψ)
  exact ⟨τd, τa, hτd0, hτd, hτa0, hτa, hwd, hwa⟩

end Run

end CSD.RecordLayer

end
