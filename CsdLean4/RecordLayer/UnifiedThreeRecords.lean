/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedArrivalReturn

/-!
# Three records and three counts in one run: before, during and after the absence

**Category:** 7-SigmaLayer (the record layer). BACKLOG #384 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Remainder (a) of #383. It amends
UA-17 with clause (f); the author has not yet read that amendment.

#383 has two records in one run, one written during the absence and one on the return leg, from a
prepared start. Here a third pointer is coupled to the near half with a larger rate, so its
readout is written during the first presence. One run then has three records in order (`τ_d ≤ τ_a
≤ τ_r`), before, during and after the absence, and the clock's own pointer of #381 has a count at
a flow time by which each is complete. All three writes are thresholds of accumulated occupancy.
The first is not an emission record and nothing is certified.

The third pointer takes the place of the gated pointer of #376: on the four-pointer arena the
third pointer's operator is `P ⊗ X`, and here `X` is `g₃ · 1`. No new arena is built. **In
this variant no term of the energy couples the messenger and the clock**: every pointer is
coupled to an observable of one factor. From a product ray the run is that of the uncoupled
arena of #372 with a third region pointer, written on the composite base (a calculation;
Lean has it only on the fibre where the third and fourth profiles vanish).

* `clockOne`, `clockOne_isHermitian`, `arenaObs_clockOne` — the clock factor `g₃ · 1`;
* `threeRecordFlow`, `quadMuL_map_threeRecordFlow` — the flow and its preserved measure;
* `gateShift_clockOne`, `threeRecordFlow_fst_prodRay` — from a product ray, on a fibre where
  the third and fourth profiles vanish, the carrier stays a product ray and all three region
  pointers move as region pointers of the messenger's own arena;
* `integral_nearOcc_le_self` (on any fibre the near half has accumulated at most the elapsed
  flow time), `le_integral_nearOcc_out` — on a round fibre the near half has accumulated at
  least `(1 − fineEta n δ) · roundOut n δ` by the end of the first presence;
* `roundAway_le_midpoint`, `midpoint_le_roundAwayEnd` — arithmetic on the intervals of #379;
* `threeRecordStart`, `threeRecordRun`, `threeRecordRun_fst_pointer`,
  `threeRecordRun_snd_pointer`, `threeRecordRun_thd_pointer`, `threeRecordRun_clock_pointer`;
* `echoFstShown_threeRecord_iff`, `echoSiteShown_threeRecord_iff`,
  `triThdShown_threeRecord_iff`, `isSwing_threeRecord`;
* ★ `three_records_with_counts` — **three records and three counts**: flow times `τ_d` in the
  first presence, `τ_a` in the absence and `τ_r` on the return leg, each the end of the write
  interval of an `IsRecordWrite`; the clock's counts `N_d`, `N_a`, `N_r` at them; the two
  count differences from `N_d`, times the period, within two periods of the differences of
  the flow times; and the midpoint `(τ_d + τ_r)/2` in the absence, within one period of
  `(N_d + N_r)/2` periods.

## Exact scope

* **The first write is not an emission record.** The messenger is prepared in the near half.
  The third pointer accumulates its presence there and its readout turns once enough has
  accumulated. Nothing is emitted and nothing records a departure. With `T₁ = 0` the theorem
  allows the write at any flow time of the first presence; a positive `T₁` needs
  `κ₃ T₁ ≤ 1/6`, which with the other condition holds only for
  `T₁ ≤ (1 − fineEta n δ)/2 · roundOut n δ`, about half the first presence (a calculation,
  not in Lean).
* **No write certifies a departure, an arrival or a return.** All three are thresholds of
  accumulated occupancy, as in #367. Carriers with suitable constant occupancies would give
  readouts with the same clauses (a calculation, not in Lean; not exhibited on this arena).
  What shows the round trip is the occupancy statement of #379, which is not a record.
* **The times are ends of write intervals**, not the instants the readouts turn, and each is
  located only within its interval. Each readout is shown to display only through its window
  after its `τ`. The three are not shown to display at one flow time: the third pointer keeps
  turning whenever the messenger is in the near half, and may leave its displayed arc before
  the later writes.
* **The midpoint statement is arithmetic on three intervals.** The first presence ends before the
  absence and the return leg begins after it, and for `δ ≤ π/2` the midpoint of any non-negative
  time up to `roundOut` and any time of the return leg lies in the absence. The two intervals are
  not symmetric about it: the return leg is twice as long as the first presence. Interval
  arithmetic puts the midpoint in `[1250 n² (3π/4 + δ/2), 1250 n² (3π/2 − δ)]`; the theorem
  states only the absence's whole interval. It locates the midpoint only to within the absence's
  whole length `1250 n² (π − 2δ)`, the same interval that holds `τ_a`. It is formed from flow
  times; no degree of freedom holds it and no record reads it.
* **Not a radar time.** There is no reflector and no distance. The messenger returns because
  the ring closes, and all three records are read on the one messenger's ring. There is no
  second observer.
* **The time content is the clock's alone.** The count bounds are those of #366 and hold at
  any non-negative flow times. No hypothesis relates the period `2π/R` to any of the
  intervals, and all three counts may be zero.
* **The counts are read at flow times** (UA-7). No record reads a count and no degree of
  freedom holds a pair (UO-14 (b)).
* **The gated pointer is absent, and nothing couples the two carriers.** Neither half of the
  author's decision of 2026-11-12 is exercised in this run: the product coupling `P ⊗ X` with
  `X` the clock's level swap is not there, and the composite base carries no joint term. The
  clock is read by its own pointer, as since #381. With `X = g₃ · 1` the third coupling is a
  messenger observable, so it is expected not to entangle the carrier on any fibre (a
  calculation, not in Lean); the lemma used asks that its profile vanish on the fibre, where
  the third pointer does not act back on the messenger.
* **Six rate windows and three signs are hypotheses.** The first two pairs are those of #383.
  The third is satisfiable with `T₁ = 0` by any large enough rate once `δ < π/2` and
  `fineEta n δ < 1`, which the first two windows force (a calculation, not in Lean); at
  `δ = π/2` the theorem is vacuous. That one start meets all of them together with the
  round-fibre bound is not stated in Lean. The margin must be positive (`cos δ < 1`).
* **Null sets.** The third and fourth profiles vanish on their fibres and the start is a
  product ray (null sets by calculations not in Lean); the round fibres of #379; one clock
  start. The writes and counts are `IsRecordWrite` and `IsTickCount` statements about readout
  histories, not `ActualOccurrence`s.
* **Earlier.** #367 has a departure write and an arrival write in one run (thresholds of
  accumulated weight); #369 three records and two counts in one run, for one momentum mode;
  #372 a separate clock's counts at two writes, on the uncoupled product arena. #200 and #202
  (echo arena), #270 (reflection, stated detector law) and #274 and #278 (relay, stated hybrid
  law) have emission and return records with a clock reading, under their own laws.
  What is new here is the third write, during the first presence, in a round-trip run like
  that of #383, and the midpoint clause. In this variant no term couples the messenger and the
  clock, so from a product ray the run is that of #372's uncoupled arena with a third region
  pointer (a calculation; Lean has it only on the fibre where the third and fourth profiles
  vanish). Nothing here is evidence about Lorentz kinematics.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-2,
UA-4, UA-5, UA-7, UA-8, UA-12, UA-13, UA-15, UA-17, UO-14, UO-16, UD-92, UD-94, UD-111,
UD-118, UD-123, UD-126, UD-128, UD-129, UD-130); `RecordLayer/UnifiedArrivalReturn.lean`
(#383: `farOcc`, `integral_farOcc_le`, `le_integral_farOcc`, `roundAway`, `roundAwayEnd`);
`RecordLayer/UnifiedRoundTrip.lean` (#382: `nearOcc`, `integral_nearOcc_le`,
`le_integral_nearOcc`); `RecordLayer/UnifiedTwoCounts.lean` (#381: `gateFreeFlow`,
`gateFreeFlow_fst`, `gateFreeFlow_snd_prodRay`, `isSwing_snd_of_abs_shift_sub_le`);
`RecordLayer/UnifiedCompositeCarrier.lean` (#376: `gateFlow_prodRay`, `gateShift`);
`RecordLayer/UnifiedFineReturn.lean` (#379: `fineCarrier_far_le_before`);
`RecordLayer/UnifiedDepartureArrival.lean` (#367: `echoFstShown_regionTwoFlow_iff`,
`echoSiteShown_regionTwoFlow_iff`); `RecordLayer/UnifiedArrivalRecord.lean` (#365:
`isRecordWrite_of_integral_crossing`); `RecordLayer/UnifiedCountAtWrite.lean` (#366:
`IsSwing.abs_tickTime_sub_le`, `IsSwing.abs_tickTime_sub_sub_le`);
`RecordLayer/UnifiedClockTwoSites.lean` (#369: `triThdShown`).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### A second pointer on the near half, in place of the gated pointer -/

section Flow

variable {M Mc : ℕ} {f h k l : ℝ → ℝ} (J μ g₁ g₂ : ℝ) (A B : Finset (ZMod (M + 1)))
  (Jc μ₀ μ₁ g₃ g₀ : ℝ) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
  (hk : Function.Periodic k 1) (hl : Function.Periodic l 1)

variable (Mc) in
/-- **A strength times the identity on the clock's state space**: the clock factor of the
third pointer's operator in this module. -/
noncomputable def clockOne (g : ℝ) :
    Matrix ((ZMod (Mc + 1) × Fin 2) × Fin 2) ((ZMod (Mc + 1) × Fin 2) × Fin 2) ℂ :=
  (g : ℂ) • 1

theorem clockOne_isHermitian (g : ℝ) : (clockOne Mc g).IsHermitian :=
  isHermitian_ofReal_smul g Matrix.isHermitian_one

/-- The expectation of `g · 1` is `g` at every ray. -/
theorem arenaObs_clockOne (g : ℝ) (q : GenArena ((ZMod (Mc + 1) × Fin 2) × Fin 2)) :
    arenaObs (clockOne Mc g) q = g := by
  rw [clockOne, arenaObs_real_smul, arenaObs_one, mul_one]

variable (Mc) in
/-- **The joint flow of the messenger-and-clock composite with three region pointers and the
clock's own pointer**: `gateFreeFlow` with the third pointer coupled to `P_A ⊗ g₃ 1`, the
region of the first pointer with its own strength, and the fourth to the clock's level swap.
The energy is
`−2⟨H_D ⊗ 1 + 1 ⊗ H_dev⟩ − 2 g₁ f(θ₂)⟨P_A ⊗ 1⟩ − 2 g₂ h(ψ₂)⟨P_B ⊗ 1⟩ − 2 g₃ k(χ₂)⟨P_A ⊗ 1⟩
  − 2 g₀ l(ξ₂)⟨1 ⊗ X⟩` (UA-17 (f)). The gated pointer of #376 is absent. -/
noncomputable def threeRecordFlow (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l) (t : ℝ) :
    QuadSigma ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
      → QuadSigma ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)) :=
  gateFreeFlow (diracIdx M) (clockIdx Mc) (diracHam J μ) ((g₁ : ℂ) • regionProj A)
    ((g₂ : ℂ) • regionProj B) (regionProj A) (deviceHam Jc μ₀ μ₁) (clockOne Mc g₃)
    (clockB Mc g₀) hf hh hk hl hc hch hck hcl t

/-- **The flow preserves `μ_FS ⊗ vol ⊗ vol ⊗ vol ⊗ vol`.** -/
theorem quadMuL_map_threeRecordFlow (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l)
    (p₀ : CPN ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3) + 1)) (t : ℝ) :
    Measure.map
        (threeRecordFlow Mc J μ g₁ g₂ A B Jc μ₀ μ₁ g₃ g₀ hf hh hk hl hc hch hck hcl t)
        (quadMuL p₀) = quadMuL p₀ :=
  quadMuL_map_gateFreeFlow (diracIdx M) (clockIdx Mc) (diracHam_isHermitian J μ)
    (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B)
    (regionProj_isHermitian A) (deviceHam_isHermitian Jc μ₀ μ₁) (clockOne_isHermitian g₃)
    (clockB_isHermitian g₀) hf hh hk hl hc hch hck hcl p₀ t

/-- **With the clock factor `g₃ · 1` the third pointer's displacement is a region pointer's**:
its rate at the fibre times the messenger's accumulated occupancy of the region. -/
theorem gateShift_clockOne (φ ζ' ζ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) (q : GenArena ((ZMod (Mc + 1) × Fin 2) × Fin 2))
    (t : ℝ) :
    gateShift (diracHam_isHermitian J μ) (regionProj_smul_isHermitian g₁ A)
        (regionProj_smul_isHermitian g₂ B) (deviceHam_isHermitian Jc μ₀ μ₁) (regionProj A)
        (clockOne Mc g₃) hf hh hk φ ζ' ζ p q t
      = rateAt g₃ 1 hk ζ * ∫ s in (0 : ℝ)..t, arenaObs (regionProj A)
          (arenaKick (idxTwoCarrierU (diracHam_isHermitian J μ)
            (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B) hf hh
            φ ζ' s) p) := by
  rw [gateShift, rateAt]
  simp only [arenaObs_clockOne, div_one]
  rw [intervalIntegral.integral_mul_const]
  ring

/-- ★ **From a product ray, on a fibre where the third and fourth profiles vanish, the carrier
stays a product ray and all three region pointers move as region pointers of the messenger's
own arena.** The first two are those of `regionTwoFlow`; the third advances by its rate times
the accumulated occupancy of the first pointer's region along the same messenger orbit. -/
theorem threeRecordFlow_fst_prodRay (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l) (t : ℝ)
    (p : GenArena (ZMod (M + 1) × Fin 2)) (q : GenArena ((ZMod (Mc + 1) × Fin 2) × Fin 2))
    (θ ψ : KTorus) {χ ξ : KTorus} (hzk : hk.lift χ.2 = 0) (hz : hl.lift ξ.2 = 0) :
    (threeRecordFlow Mc J μ g₁ g₂ A B Jc μ₀ μ₁ g₃ g₀ hf hh hk hl hc hch hck hcl t
        ((((idxArenaEquiv (prodIdx (diracIdx M) (clockIdx Mc)) (prodRay p q), θ), ψ), χ),
          ξ)).1
      = (((idxArenaEquiv (prodIdx (diracIdx M) (clockIdx Mc))
              (prodRay (arenaKick (idxTwoCarrierU (diracHam_isHermitian J μ)
                  (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B) hf hh
                  θ.2 ψ.2 t) p)
                (arenaKick (idxFreeU (deviceHam_isHermitian Jc μ₀ μ₁) t) q)),
            (θ.1 + ((idxTwoShiftFst (diracHam_isHermitian J μ)
                (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B) hf hh
                θ.2 ψ.2 p t : ℝ) : AddCircle (1 : ℝ)), θ.2)),
           (ψ.1 + ((idxTwoShiftSnd (diracHam_isHermitian J μ)
                (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B) hf hh
                θ.2 ψ.2 p t : ℝ) : AddCircle (1 : ℝ)), ψ.2)),
          pshift (rateAt g₃ 1 hk χ.2 * ∫ s in (0 : ℝ)..t, arenaObs (regionProj A)
            (arenaKick (idxTwoCarrierU (diracHam_isHermitian J μ)
              (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B) hf hh
              θ.2 ψ.2 s) p)) χ) := by
  rw [threeRecordFlow,
    gateFreeFlow_fst (diracIdx M) (clockIdx Mc) hf hh hk hl hc hch hck hcl t _ hz,
    gateFlow_prodRay (diracIdx M) (clockIdx Mc) (diracHam_isHermitian J μ)
      (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B)
      (regionProj_isHermitian A) (deviceHam_isHermitian Jc μ₀ μ₁) hf hh hk hc hch hck t p q θ
      ψ hzk,
    gateShift_clockOne]

end Flow

/-! ### The near half's accumulated occupancy during the first presence -/

section Near

variable {M : ℕ} {f h : ℝ → ℝ} (g₁ g₂ : ℝ) (hf : Function.Periodic f 1)
  (hh : Function.Periodic h 1) {n : ℕ} (hn : 0 < n) (hL : 640000 * n ^ 3 ≤ M + 1)

/-- The accumulated near-half occupancy is at most the elapsed flow time. -/
theorem integral_nearOcc_le_self (φ χ : AddCircle (1 : ℝ)) {T : ℝ} (hT : 0 ≤ T) :
    (∫ s in (0 : ℝ)..T, nearOcc g₁ g₂ hf hh hn hL φ χ s) ≤ T := by
  have h := integral_le_of_forall_le (continuous_nearOcc g₁ g₂ hf hh hn hL φ χ) hT (c := 1)
    fun s _ => nearOcc_le_one g₁ g₂ hf hh hn hL φ χ s
  simpa using h

/-- **By the end of the first presence the near half has accumulated at least the fraction
`1 − fineEta n δ` of it**, on a round fibre. -/
theorem le_integral_nearOcc_out {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ roundFibres g₁ g₂ hf hh n) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 2)
    (hcos : Real.cos δ < 1) :
    (1 - fineEta n δ) * roundOut n δ
      ≤ ∫ s in (0 : ℝ)..roundOut n δ, nearOcc g₁ g₂ hf hh hn hL φ χ s := by
  have h0a : (0 : ℝ) ≤ roundOut n δ := by
    unfold roundOut
    exact mul_nonneg (by positivity) (by linarith)
  have h := le_integral_of_forall_le (continuous_nearOcc g₁ g₂ hf hh hn hL φ χ) h0a
    (c := 1 - fineEta n δ) fun s hs => by
      rw [nearOcc_eq]
      have := fineCarrier_far_le_before g₁ g₂ hf hh hn hL hx hδ0 hcos hs.1 hs.2
      linarith
  simpa using h

end Near

/-! ### The midpoint of a time in the first presence and a time on the return leg -/

/-- The midpoint of a non-negative flow time and a flow time on the return leg is not before
the absence begins. -/
theorem roundAway_le_midpoint {n : ℕ} {δ τd τr : ℝ} (hδ : δ ≤ Real.pi / 2) (hd : 0 ≤ τd)
    (hr : roundBack n δ ≤ τr) : roundAway n δ ≤ (τd + τr) / 2 := by
  unfold roundBack at hr
  unfold roundAway
  have h1 : 1250 * (n : ℝ) ^ 2 * (Real.pi / 2 + δ)
      ≤ 1250 * (n : ℝ) ^ 2 * ((3 * Real.pi / 2 + δ) / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e : 1250 * (n : ℝ) ^ 2 * ((3 * Real.pi / 2 + δ) / 2)
      = 1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 + δ) / 2 := by ring
  linarith

/-- The midpoint of a flow time in the first presence and a flow time on the return leg is not
after the absence ends. -/
theorem midpoint_le_roundAwayEnd {n : ℕ} {δ τd τr : ℝ} (hd : τd ≤ roundOut n δ)
    (hr : τr ≤ roundEnd n δ) : (τd + τr) / 2 ≤ roundAwayEnd n δ := by
  unfold roundOut at hd
  unfold roundEnd at hr
  unfold roundAwayEnd
  have e : 1250 * (n : ℝ) ^ 2 * (3 * Real.pi / 2 - δ)
      = (1250 * (n : ℝ) ^ 2 * (Real.pi / 2 - δ)
        + 1250 * (n : ℝ) ^ 2 * (5 * Real.pi / 2 - δ)) / 2 := by ring
  linarith

/-! ### The run -/

section Run

variable {M Mc : ℕ} {f h k : ℝ → ℝ} (g₁ g₂ g₃ : ℝ) (hf : Function.Periodic f 1)
  (hh : Function.Periodic h 1) (hk : Function.Periodic k 1) {n : ℕ} (hn : 0 < n)
  (hL : 640000 * n ^ 3 ≤ M + 1) (Jc : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ < μ₁)
  (h10 : μ₁ < 2 * μ₀) (m : ℤ) {β : ℤ → ℂ} (hβ : β m ≠ 0) {R : ℝ}

/-- **The start of the three-record run**: the messenger on the fine packet of index `n` and
the clock on the one-mode start of #358 at the rate `R`, as one product ray; the three region
pointers at `θ`, `ψ`, `χ`; the clock's own pointer at the angle `1/12` on the fibre
`ξ₂ = 0`. -/
noncomputable def threeRecordStart (R : ℝ) (θ ψ χ : KTorus) :
    QuadSigma ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)) :=
  ((((idxArenaEquiv (prodIdx (diracIdx M) (clockIdx Mc))
      (prodRay (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL))
        (deviceRay (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
          (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _))), θ), ψ), χ),
    ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))))

variable (Mc) in
/-- **The three-record run**: the orbit of `threeRecordStart` under `threeRecordFlow`, with the
first and third pointers on the near half of the messenger's ring, the second on the far half
and the clock's own pointer's profile `trainF`. -/
noncomputable def threeRecordRun (g₀ : ℝ) (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (R : ℝ) (θ ψ χ : KTorus) (t : ℝ) :
    QuadSigma ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)) :=
  threeRecordFlow Mc (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) Jc μ₀
    μ₁ g₃ g₀ hf hh hk trainF_periodic hc hch hck contDiff_trainF t
    (threeRecordStart hn hL Jc h0 h01 m hβ R θ ψ χ)

/-- Along the run the first pointer moves exactly as in `regionTwoFlow` (#367). -/
theorem threeRecordRun_fst_pointer (g₀ : ℝ) (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (θ ψ : KTorus) {χ : KTorus} (hzk : hk.lift χ.2 = 0) (t : ℝ) :
    (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ
        t).1.1.1.2
      = (regionTwoFlow (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) hf hh
          hc hch t ((idxArenaEquiv (diracIdx M)
            (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)), θ), ψ)).1.2
      := by
  unfold threeRecordRun threeRecordStart
  rw [threeRecordFlow_fst_prodRay (Mc := Mc) (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
    (farHalf (M + 1)) Jc μ₀ μ₁ g₃ g₀ hf hh hk trainF_periodic hc hch hck contDiff_trainF t _
    _ θ ψ hzk trainF_lift_zero, regionTwoFlow_apply]

/-- Along the run the second pointer moves exactly as in `regionTwoFlow` (#367). -/
theorem threeRecordRun_snd_pointer (g₀ : ℝ) (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (θ ψ : KTorus) {χ : KTorus} (hzk : hk.lift χ.2 = 0) (t : ℝ) :
    (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ
        t).1.1.2
      = (regionTwoFlow (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) hf hh
          hc hch t ((idxArenaEquiv (diracIdx M)
            (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)), θ), ψ)).2
      := by
  unfold threeRecordRun threeRecordStart
  rw [threeRecordFlow_fst_prodRay (Mc := Mc) (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
    (farHalf (M + 1)) Jc μ₀ μ₁ g₃ g₀ hf hh hk trainF_periodic hc hch hck contDiff_trainF t _
    _ θ ψ hzk trainF_lift_zero, regionTwoFlow_apply]

/-- ★ **Along the run the third pointer is its start turned by its rate times the accumulated
near-half occupancy** of the same coupled messenger. -/
theorem threeRecordRun_thd_pointer (g₀ : ℝ) (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (θ ψ : KTorus) {χ : KTorus} (hzk : hk.lift χ.2 = 0) (t : ℝ) :
    (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ t).1.2
      = pshift (rateAt g₃ 1 hk χ.2
          * ∫ s in (0 : ℝ)..t, nearOcc g₁ g₂ hf hh hn hL θ.2 ψ.2 s) χ := by
  unfold threeRecordRun threeRecordStart
  rw [threeRecordFlow_fst_prodRay (Mc := Mc) (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
    (farHalf (M + 1)) Jc μ₀ μ₁ g₃ g₀ hf hh hk trainF_periodic hc hch hck contDiff_trainF t _
    _ θ ψ hzk trainF_lift_zero]
  rfl

/-- Along the run the clock's own pointer is its start turned by the displacement of the
pointer of #357 on the clock's own arena. -/
theorem threeRecordRun_clock_pointer (g₀ : ℝ) (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (θ ψ : KTorus) {χ : KTorus} (hzk : hk.lift χ.2 = 0) (t : ℝ) :
    (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ t).2
      = pshift (clockPointerShift Jc μ₀ μ₁ g₀ trainF_periodic (0 : AddCircle (1 : ℝ))
          (deviceRay (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β (-(Real.pi / (2 * R))))
            (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _)) t)
        ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))) := by
  rw [← idxPointerShift_clock]
  unfold threeRecordRun threeRecordStart threeRecordFlow
  exact gateFreeFlow_snd_prodRay (diracIdx M) (clockIdx Mc) (diracHam_isHermitian _ _)
    (regionProj_smul_isHermitian g₁ _) (regionProj_smul_isHermitian g₂ _)
    (regionProj_isHermitian _) (deviceHam_isHermitian Jc μ₀ μ₁) (clockB_isHermitian g₀) hf hh
    hk trainF_periodic hc hch hck contDiff_trainF t _ _ θ ψ (χ := χ)
    (ξ := ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))) hzk trainF_lift_zero

/-- **The first pointer's readout along the run**, in terms of the accumulated near-half
occupancy. -/
theorem echoFstShown_threeRecord_iff (g₀ : ℝ) (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (θ ψ : KTorus) {χ : KTorus} (hzk : hk.lift χ.2 = 0) (t : ℝ) :
    echoFstShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
        (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ
          t).1.1 = true
      ↔ pshift (rateAt g₁ 1 hf θ.2
          * ∫ s in (0 : ℝ)..t, nearOcc g₁ g₂ hf hh hn hL θ.2 ψ.2 s) θ ∈ displayArc := by
  have hp := threeRecordRun_fst_pointer (Mc := Mc) (R := R) g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01
    m hβ g₀ hc hch hck θ ψ hzk t
  have hiff := echoFstShown_regionTwoFlow_iff (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
    (farHalf (M + 1)) hf hh hc hch
    (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)) θ ψ t
  rw [echoFstShown_eq_true_iff] at hiff ⊢
  have hmem : (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ
        t).1.1 ∈ echoFstDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
      ↔ regionTwoFlow (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) hf hh
          hc hch t ((idxArenaEquiv (diracIdx M)
            (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)), θ), ψ)
        ∈ echoFstDisplay (2 * M + 1) := by
    show (_ : KTorus) ∈ displayArc ↔ (_ : KTorus) ∈ displayArc
    rw [hp]
  rw [hmem]
  exact hiff

/-- **The second pointer's readout along the run**, in terms of the accumulated far-half
occupancy. -/
theorem echoSiteShown_threeRecord_iff (g₀ : ℝ) (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (θ ψ : KTorus) {χ : KTorus} (hzk : hk.lift χ.2 = 0) (t : ℝ) :
    echoSiteShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
        (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ
          t).1.1 = true
      ↔ pshift (rateAt g₂ 1 hh ψ.2
          * ∫ s in (0 : ℝ)..t, farOcc g₁ g₂ hf hh hn hL θ.2 ψ.2 s) ψ ∈ displayArc := by
  have hp := threeRecordRun_snd_pointer (Mc := Mc) (R := R) g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01
    m hβ g₀ hc hch hck θ ψ hzk t
  have hiff := echoSiteShown_regionTwoFlow_iff (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
    (farHalf (M + 1)) hf hh hc hch
    (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)) θ ψ t
  rw [echoSiteShown_eq_true_iff] at hiff ⊢
  have hmem : (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ
        t).1.1 ∈ echoSiteDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
      ↔ regionTwoFlow (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) hf hh
          hc hch t ((idxArenaEquiv (diracIdx M)
            (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)), θ), ψ)
        ∈ echoSiteDisplay (2 * M + 1) := by
    show (_ : KTorus) ∈ displayArc ↔ (_ : KTorus) ∈ displayArc
    rw [hp]
  rw [hmem]
  exact hiff

/-- **The third pointer's readout along the run**, in terms of the accumulated near-half
occupancy. -/
theorem triThdShown_threeRecord_iff (g₀ : ℝ) (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (θ ψ : KTorus) {χ : KTorus} (hzk : hk.lift χ.2 = 0) (t : ℝ) :
    triThdShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
        (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ
          t).1 = true
      ↔ pshift (rateAt g₃ 1 hk χ.2
          * ∫ s in (0 : ℝ)..t, nearOcc g₁ g₂ hf hh hn hL θ.2 ψ.2 s) χ ∈ displayArc := by
  rw [triThdShown_eq_true_iff]
  show (_ : KTorus) ∈ displayArc ↔ _
  rw [threeRecordRun_thd_pointer (Mc := Mc) (R := R) g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ
    g₀ hc hch hck θ ψ hzk t]

variable (hRe : R = levelClockRate μ₀ μ₁ (2 * Jc * Real.sin (angleZ (Mc + 1) m))) {g₀ : ℝ}
  (hg : g₀ = R * ‖β m‖ ^ 2
    / (16 * (deviceCoherence (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β 0)).re))
include h10 hRe hg

/-- **The clock's own pointer is a swing at the rate `R`, for every horizon, in the
three-record run.** -/
theorem isSwing_threeRecord (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (θ ψ : KTorus) {χ : KTorus} (hzk : hk.lift χ.2 = 0) (T : ℝ) :
    IsSwing (quadFreeReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (quadFreeDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
      (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ)
      R 0 0 T := by
  have hR : 0 < R := by
    rw [hRe]
    exact levelClockRate_pos h0 h01 _
  have hrep : rep (((1 / 12 : ℝ) : CircleFibre)) = 1 / 12 :=
    rep_coe_of_mem_Ioc ⟨by norm_num, by norm_num⟩
  have hsw := isSwing_snd_of_abs_shift_sub_le (A := 1 / 4) (δ := 0) (T := T) hR (by norm_num)
    le_rfl
    (fun t _ _ => threeRecordRun_clock_pointer (Mc := Mc) (R := R) g₁ g₂ g₃ hf hh hk hn hL Jc
      h0 h01 m hβ g₀ hc hch hck θ ψ hzk t)
    (fun t ht0 _ => by
      rw [clockPointerShift_train Jc h0 h01 h10 m hβ hRe hg ht0, sub_self, abs_zero])
    (by show _ < rep (((1 / 12 : ℝ) : CircleFibre)); rw [hrep]; norm_num)
    (by show rep (((1 / 12 : ℝ) : CircleFibre)) + _ ≤ _; rw [hrep]; norm_num)
    (by show _ < rep (((1 / 12 : ℝ) : CircleFibre)) + _ - _; rw [hrep]; norm_num)
    (by show rep (((1 / 12 : ℝ) : CircleFibre)) + _ + _ ≤ _; rw [hrep]; norm_num)
  have e₁ : (1 : ℝ) - (1 / 3 - rep (((1 / 12 : ℝ) : CircleFibre)) - 0) / (1 / 4) = 0 := by
    rw [hrep]
    norm_num
  have e₂ : (1 : ℝ) - (1 / 3 - rep (((1 / 12 : ℝ) : CircleFibre)) + 0) / (1 / 4) = 0 := by
    rw [hrep]
    norm_num
  rw [e₁, e₂] at hsw
  exact hsw

/-- ★ **Three records and three counts in one run.** On the composite carrier with
three region pointers and the clock's own pointer, from `threeRecordStart` with the three
region pointers ready, on a round fibre, with `0 < δ ≤ π/2` (in Lean `0 ≤ δ`, `δ ≤ π/2`,
`cos δ < 1`), the third profile vanishing on its fibre and all three rates positive: if the
near rate `κ₁` and the far rate `κ₂` are in the windows of #383, and the third rate `κ₃` has
`κ₃ T₁ ≤ 1/6` for a chosen `0 ≤ T₁ ≤ roundOut n δ` and
`1/3 ≤ κ₃ (1 − fineEta n δ) roundOut n δ`, there are flow times `τ_d`, `τ_a`, `τ_r` and
numbers `N_d`, `N_a`, `N_r` such that

* `T₁ ≤ τ_d ≤ roundOut n δ`, `roundAway n δ ≤ τ_a ≤ roundAwayEnd n δ` and
  `roundBack n δ ≤ τ_r ≤ roundEnd n δ`, so `τ_d ≤ τ_a ≤ τ_r`;
* the third, the far and the near readout histories are `IsRecordWrite`s of `true` from the
  start, with write intervals `[T₁, τ_d]`, `[roundAway n δ, τ_a]`, `[roundBack n δ, τ_r]`;
* the clock's own pointer has exactly `N_d`, `N_a`, `N_r` ticks by `τ_d`, `τ_a`, `τ_r`;
* `|(N_a − N_d) · 2π/R − (τ_a − τ_d)| ≤ 4π/R` and `|(N_r − N_d) · 2π/R − (τ_r − τ_d)| ≤ 4π/R`;
* `roundAway n δ ≤ (τ_d + τ_r)/2 ≤ roundAwayEnd n δ` and
  `|(N_d + N_r)/2 · 2π/R − (τ_d + τ_r)/2| ≤ 2π/R`.

The times are flow times (UA-7). The writes are thresholds of accumulated occupancy: the first
is not an emission record and none certifies a departure, an arrival or a return. The midpoint
clause is arithmetic on the three intervals. The counts may be zero. -/
theorem three_records_with_counts (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) {θ ψ χ : KTorus} (hθ : θ ∈ readyArc 2) (hψ : ψ ∈ readyArc 2)
    (hχ : χ ∈ readyArc 2) (hzk : hk.lift χ.2 = 0)
    (hx : (θ.2, ψ.2) ∈ roundFibres g₁ g₂ hf hh n) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ Real.pi / 2) (hcos : Real.cos δ < 1)
    (hκ₁ : 0 < rateAt g₁ 1 hf θ.2) (hlo₁ : rateAt g₁ 1 hf θ.2 * roundUpper n δ ≤ 1 / 6)
    (hhi₁ : 1 / 3 ≤ rateAt g₁ 1 hf θ.2 * roundLower n δ)
    (hκ₂ : 0 < rateAt g₂ 1 hh ψ.2) (hlo₂ : rateAt g₂ 1 hh ψ.2 * farUpper n δ ≤ 1 / 6)
    (hhi₂ : 1 / 3 ≤ rateAt g₂ 1 hh ψ.2 * farLower n δ)
    (hκ₃ : 0 < rateAt g₃ 1 hk χ.2) {T₁ : ℝ} (hT₁0 : 0 ≤ T₁) (hT₁ : T₁ ≤ roundOut n δ)
    (hlo₃ : rateAt g₃ 1 hk χ.2 * T₁ ≤ 1 / 6)
    (hhi₃ : 1 / 3 ≤ rateAt g₃ 1 hk χ.2 * ((1 - fineEta n δ) * roundOut n δ)) :
    ∃ (τd τa τr : ℝ) (Nd Na Nr : ℕ), T₁ ≤ τd ∧ τd ≤ roundOut n δ
      ∧ roundAway n δ ≤ τa ∧ τa ≤ roundAwayEnd n δ
      ∧ roundBack n δ ≤ τr ∧ τr ≤ roundEnd n δ ∧ τd ≤ τa ∧ τa ≤ τr
      ∧ IsRecordWrite
          (fun t => triThdShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
            (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ
              t).1)
          0 T₁ τd (1 / (3 * rateAt g₃ 1 hk χ.2)) true
      ∧ IsRecordWrite
          (fun t => echoSiteShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
            (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ
              t).1.1)
          0 (roundAway n δ) τa (1 / (3 * rateAt g₂ 1 hh ψ.2)) true
      ∧ IsRecordWrite
          (fun t => echoFstShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
            (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ
              t).1.1)
          0 (roundBack n δ) τr (1 / (3 * rateAt g₁ 1 hf θ.2)) true
      ∧ IsTickCount (quadFreeReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
          (quadFreeDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
          (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ)
          τd Nd
      ∧ IsTickCount (quadFreeReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
          (quadFreeDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
          (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ)
          τa Na
      ∧ IsTickCount (quadFreeReady ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
          (quadFreeDisplay ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)))
          (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ)
          τr Nr
      ∧ |((Na : ℝ) - Nd) * (2 * Real.pi / R) - (τa - τd)| ≤ 4 * Real.pi / R
      ∧ |((Nr : ℝ) - Nd) * (2 * Real.pi / R) - (τr - τd)| ≤ 4 * Real.pi / R
      ∧ roundAway n δ ≤ (τd + τr) / 2 ∧ (τd + τr) / 2 ≤ roundAwayEnd n δ
      ∧ |((Nd : ℝ) + Nr) / 2 * (2 * Real.pi / R) - (τd + τr) / 2| ≤ 2 * Real.pi / R := by
  have hπ := Real.pi_pos
  have hr2 : (0 : ℝ) < 1250 * (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hTo0 : 0 ≤ roundOut n δ := hT₁0.trans hT₁
  have hToa : roundOut n δ ≤ roundAway n δ := by
    unfold roundOut roundAway
    exact mul_le_mul_of_nonneg_left (by linarith) hr2.le
  have hTa0 : 0 ≤ roundAway n δ := hTo0.trans hToa
  have hTae : roundAway n δ ≤ roundAwayEnd n δ := by
    unfold roundAway roundAwayEnd
    exact mul_le_mul_of_nonneg_left (by linarith) hr2.le
  have hTeb : roundAwayEnd n δ ≤ roundBack n δ := by
    unfold roundAwayEnd roundBack
    exact mul_le_mul_of_nonneg_left (by linarith) hr2.le
  have hTb0 : 0 ≤ roundBack n δ := (hTa0.trans hTae).trans hTeb
  have hTbc : roundBack n δ ≤ roundEnd n δ := by
    unfold roundBack roundEnd
    exact mul_le_mul_of_nonneg_left (by linarith) hr2.le
  -- the write during the first presence
  have hUd := mul_le_mul_of_nonneg_left
    (integral_nearOcc_le_self g₁ g₂ hf hh hn hL θ.2 ψ.2 hT₁0) hκ₃.le
  have hLd := mul_le_mul_of_nonneg_left
    (le_integral_nearOcc_out g₁ g₂ hf hh hn hL hx hδ0 hδ hcos) hκ₃.le
  obtain ⟨τd, hd1, hd2, hwd⟩ := isRecordWrite_of_integral_crossing
    (continuous_nearOcc g₁ g₂ hf hh hn hL θ.2 ψ.2)
    (fun s => nearOcc_nonneg g₁ g₂ hf hh hn hL θ.2 ψ.2 s)
    (fun s => nearOcc_le_one g₁ g₂ hf hh hn hL θ.2 ψ.2 s) hκ₃ hT₁0 hT₁ (hUd.trans hlo₃)
    (hhi₃.trans hLd) hχ
    (hist := fun t => triThdShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
      (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ t).1)
    (fun t => triThdShown_threeRecord_iff g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch
      hck θ ψ hzk t)
  -- the write during the absence
  have hUa := mul_le_mul_of_nonneg_left
    (integral_farOcc_le g₁ g₂ hf hh hn hL hx hδ0 hδ hcos) hκ₂.le
  have hLa := mul_le_mul_of_nonneg_left
    (le_integral_farOcc g₁ g₂ hf hh hn hL hx hδ0 hδ hcos) hκ₂.le
  obtain ⟨τa, ha1, ha2, hwa⟩ := isRecordWrite_of_integral_crossing
    (continuous_farOcc g₁ g₂ hf hh hn hL θ.2 ψ.2)
    (fun s => farOcc_nonneg g₁ g₂ hf hh hn hL θ.2 ψ.2 s)
    (fun s => farOcc_le_one g₁ g₂ hf hh hn hL θ.2 ψ.2 s) hκ₂ hTa0 hTae (hUa.trans hlo₂)
    (hhi₂.trans hLa) hψ
    (hist := fun t => echoSiteShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
      (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ t).1.1)
    (fun t => echoSiteShown_threeRecord_iff g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch
      hck θ ψ hzk t)
  -- the write on the return leg
  have hUr := mul_le_mul_of_nonneg_left
    (integral_nearOcc_le g₁ g₂ hf hh hn hL hx hδ0 hδ hcos) hκ₁.le
  have hLr := mul_le_mul_of_nonneg_left
    (le_integral_nearOcc g₁ g₂ hf hh hn hL hx hδ0 hδ hcos) hκ₁.le
  obtain ⟨τr, hr1, hr2', hwr⟩ := isRecordWrite_of_integral_crossing
    (continuous_nearOcc g₁ g₂ hf hh hn hL θ.2 ψ.2)
    (fun s => nearOcc_nonneg g₁ g₂ hf hh hn hL θ.2 ψ.2 s)
    (fun s => nearOcc_le_one g₁ g₂ hf hh hn hL θ.2 ψ.2 s) hκ₁ hTb0 hTbc (hUr.trans hlo₁)
    (hhi₁.trans hLr) hθ
    (hist := fun t => echoFstShown ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
      (threeRecordRun Mc g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch hck R θ ψ χ t).1.1)
    (fun t => echoFstShown_threeRecord_iff g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 m hβ g₀ hc hch
      hck θ ψ hzk t)
  have hτd0 : 0 ≤ τd := hT₁0.trans hd1
  have hτa0 : 0 ≤ τa := hTa0.trans ha1
  have hτr0 : 0 ≤ τr := hTb0.trans hr1
  have hsw := fun T => isSwing_threeRecord g₁ g₂ g₃ hf hh hk hn hL Jc h0 h01 h10 m hβ hRe hg
    hc hch hck θ ψ hzk T
  obtain ⟨Nd, hNd⟩ := (hsw τd).exists_tickCount hτd0
  obtain ⟨Na, hNa⟩ := (hsw τa).exists_tickCount hτa0
  obtain ⟨Nr, hNr⟩ := (hsw τr).exists_tickCount hτr0
  have kd := abs_le.1 ((hsw τd).abs_tickTime_sub_le hτd0 hNd)
  have kr := abs_le.1 ((hsw τr).abs_tickTime_sub_le hτr0 hNr)
  refine ⟨τd, τa, τr, Nd, Na, Nr, hd1, hd2, ha1, ha2, hr1, hr2', (hd2.trans hToa).trans ha1,
    (ha2.trans hTeb).trans hr1, hwd, hwa, hwr, hNd, hNa, hNr,
    (hsw τd).abs_tickTime_sub_sub_le (hsw τa) hτd0 hτa0 hNd hNa,
    (hsw τd).abs_tickTime_sub_sub_le (hsw τr) hτd0 hτr0 hNd hNr,
    roundAway_le_midpoint hδ hτd0 hr1, midpoint_le_roundAwayEnd hd2 hr2', ?_⟩
  rw [abs_le]
  constructor <;> linarith [kd.1, kd.2, kr.1, kr.2]

end Run

end CSD.RecordLayer

end
