/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.ProductRay
public import CsdLean4.LF4.TriCoupledFlow
public import CsdLean4.RecordLayer.UnifiedCausalArrival
public import CsdLean4.RecordLayer.UnifiedClockTwoSites
public import CsdLean4.RecordLayer.UnifiedFineTransit

/-!
# A composite carrier: the clock's pointer turns only while the messenger is in a region

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 7-SigmaLayer (the record layer). BACKLOG #376 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16, after the author's decision of
2026-11-12: the messenger and the clock are one ray of a composite carrier, and the clock's
pointer is coupled to a product observable. The arena is assumption UA-17 of
`specs/unified-record-spacetime-plan.md`.

On the arena of #372 the messenger and the clock are two factors with no term between them, and
by #374 nothing there depends on where a pointer started. Here the carrier is one ray of
`ℙ(ℂ^ι ⊗ ℂ^κ)`, with `ι` the messenger's index and `κ` the clock's. It has three pointers. Two
are coupled to messenger observables `B₁ ⊗ 1` and `B₂ ⊗ 1`. The third is coupled to the product
`P ⊗ X` of a messenger observable and a clock observable. The joint energy is

  `−2⟨A₀ ⊗ 1 + 1 ⊗ C₀⟩ − 2 f(θ₂)⟨B₁ ⊗ 1⟩ − 2 h(ψ₂)⟨B₂ ⊗ 1⟩ − 2 k(χ₂)⟨P ⊗ X⟩`

on `ℂℙ^N × T² × T² × T²`, an instance of the three-pointer energy of #368.

## The generic arena

* `prodIdx`, `compositeH`, `compositeH_isHermitian`, `idxTwoH_composite`;
* ★★ `idxTwoCarrierU_composite` — **with the third pointer's term absent the composite
  propagator is the product of the messenger's propagator, with its two pointers' terms, and
  the clock's free propagator**; `arenaKick_idxTwoCarrierU_composite`,
  `idxTwoShiftFst_composite`, `idxTwoShiftSnd_composite`;
* `gateShift`, `gateFlow`, `triMuL_map_gateFlow`;
* ★★★ `gateFlow_prodRay` — **the flow from a product ray, on a fibre where the third profile
  vanishes**: the carrier stays a product ray, the messenger and its two pointers move as on
  their own arena, the clock moves freely, and the third pointer advances by
  `−2 k'(χ₂) ∫₀ᵗ ⟨P⟩_messenger(s) ⟨X⟩_clock(s) ds`;
* ★★ `abs_gateShift_sub_le` — **between two flow times the third pointer moves by at most
  `2|k'(χ₂)| c` times the accumulated `⟨P⟩`** (for `0 ≤ ⟨P⟩`, `‖X‖ ≤ c`);
  `abs_gateShift_sub_le_of_le`;
* ★★ `abs_gateShift_sub_free_le` — **the third pointer is within `2|k'(χ₂)| c` times the
  accumulated `1 − ⟨P⟩` of the pointer coupled to `X` alone** (for `⟨P⟩ ≤ 1`);
  `abs_gateShift_sub_free_le_of_le`, `idxPointerShift_eq_free`.

## The messenger on the ring, the two-level clock

* `arenaObs_regionProj_compl`;
* `gateClockFlow` — the Dirac messenger with pointers on two regions `A` and `B`, the
  two-level device of #357, and the device's pointer coupled to `P_A ⊗ g_c X`;
  `triMuL_map_gateClockFlow`, ★★ `gateClockFlow_apply`, `gateClockShift`;
* ★★ `gateClockFlow_fst_pointer`, `gateClockFlow_snd_pointer` — **the two region pointers
  move exactly as in `regionTwoFlow`** (#367);
* ★★ `fine_gateClock_before`, `fine_gateClock_after` — **on the packet family of #375, with
  the gate on the near half: up to `(625π/3) n²` the clock's pointer is within
  `|k'(χ₂)||g_c| t/n` of the pointer of #357 on the same clock, and between any two flow times
  of `[(3125π/3) n², (4375π/3) n²]` it moves by at most `|k'(χ₂)||g_c| (t₂ − t₁)/n`**.

## Exact scope

* **A new arena assumption (UA-17).** The composite base, the absence of symmetrisation, the
  product observable and its strength are chosen. Nothing here derives them.
* **Only the fibres where the third profile vanishes, and only product starts.** There the
  third pointer does not act on the carrier, so a product ray stays a product ray. For the
  profile `trainF` that is a null set of fibres. Off it the term `k(χ₂) P ⊗ X` entangles the
  messenger with the clock, and nothing is proved. Product rays are a null set for the measure
  of the arena, so no statement here is about a set of starts of positive measure in the base.
* **The pointer is gated by an occupancy, not by a record.** Its rate is the product of the
  messenger's occupancy of the region and the clock's reading, both expectations. No readout of
  the departure pointer enters. By #374 the pointer is again a cyclic coordinate: the flow
  commutes with turning it, and nothing else depends on where it started.
* **No tick, no count, no record.** No ready arc, no threshold, no `IsSwing`, no `IsTickCount`
  and no `IsRecordWrite` is stated on this arena. That the gated pointer's swings are tick
  records whose count stops at departure is not proved. The swing, its tick records and a count
  before departure are in `RecordLayer/UnifiedGateTicks.lean` (#377); the count is not shown
  to stop there either.
* **The errors grow with the system.** On the family of #375 the two bounds are
  `|k'||g_c| t/n` with `t` up to `(625π/3) n²`, so the first is at most `(625π/3)|k'||g_c| n`
  at the end of its interval. Against the swing of the free pointer, of order `|k'||g_c|/R` for
  a clock of rate `R`, that is small only when `n R` is small, and then the number of swings
  before departure is of order `n² R`. A regime with many swings and a small error needs
  `1/n² ≪ R ≪ 1/n`. That is a calculation and not a theorem of this module.
* **Two intervals.** Nothing is stated between `(625π/3) n²` and `(3125π/3) n²` or after
  `(4375π/3) n²`.
* **The clock's ring is not placed.** The gate is the messenger's occupancy of a region of the
  messenger's ring. The clock's own position on its ring does not enter: `X` acts at every site
  of the clock's ring. "The clock is in the departure region" is not a statement of this arena.
* **Flow times throughout (UA-7).**
* **Definite facts, not statistics.** The measure statement is invariance only. UA-6 is not
  used.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-5,
UA-7, UA-8, UA-9, UA-12, UA-13, UA-15, UA-17, UO-16, UO-24, UD-110 to UD-112);
`CV/ProductRay.lean` (`prodRay`, `arenaObs_kronecker`, `arenaKick_kronU`,
`exp_smul_kronecker_add`); `LF4/TriCoupledFlow.lean` (`threeCoupledFlow`,
`triMuL_map_threeCoupledFlow`); `RecordLayer/UnifiedClockTwoSites.lean`
(`threeCoupledFlow_fst_of_lift_eq_zero`, `threeCoupledFlow_snd_of_lift_eq_zero`);
`RecordLayer/UnifiedTwoPointer.lean` (`twoCoupledFlow_reindex`, `idxTwoCarrierU`);
`RecordLayer/UnifiedDiracClock.lean` (`clockB`, `clockIdx`, `idxPointerShift`,
`idxPointerShift_clock`: the pointer of #357); `RecordLayer/UnifiedDepartureArrival.lean`
(`regionTwoFlow`, #367); `RecordLayer/UnifiedFineTransit.lean` (`fineCarrier`,
`fineCarrier_far_before`, `fineCarrier_far_after`, #375); `RecordLayer/UnifiedRecordInert.lean`
(#374); `RecordLayer/UnifiedClockMessenger.lean` (#372: the two carriers side by side);
`CV/CompositeArena.lean` (`bell_not_join`: product rays are not all rays).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### The composite carrier over two index types -/

section Composite

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {a b : ℕ}
  (e₁ : ι ≃ Fin (a + 1)) (e₂ : κ ≃ Fin (b + 1)) {f h k : ℝ → ℝ}
  {A₀ B₁ B₂ P : Matrix ι ι ℂ} {C₀ X : Matrix κ κ ℂ}

/-- **The index bridge of a composite**: the pair of indices of two carriers as the index of
one projective sector of `Σ`. -/
def prodIdx : ι × κ ≃ Fin (a * (b + 1) + b + 1) :=
  (e₁.prodCongr e₂).trans (finProdFinEquiv.trans (finCongr (by ring)))

/-- **The uncoupled energy matrix of the composite**: `A₀ ⊗ 1 + 1 ⊗ C₀`. -/
def compositeH (A₀ : Matrix ι ι ℂ) (C₀ : Matrix κ κ ℂ) : Matrix (ι × κ) (ι × κ) ℂ :=
  A₀ ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ C₀

omit [Fintype ι] [Fintype κ] in
theorem compositeH_isHermitian (hA : A₀.IsHermitian) (hC : C₀.IsHermitian) :
    (compositeH A₀ C₀).IsHermitian :=
  (kronecker_isHermitian hA Matrix.isHermitian_one).add
    (kronecker_isHermitian Matrix.isHermitian_one hC)

omit [Fintype ι] [Fintype κ] in
/-- With two pointers coupled to messenger observables, the composite's matrix on a fibre is
the composite of the messenger's matrix on that fibre and the clock's. -/
theorem idxTwoH_composite (A₀ B₁ B₂ : Matrix ι ι ℂ) (C₀ : Matrix κ κ ℂ)
    (hf : Function.Periodic f 1) (hh : Function.Periodic h 1) (φ χ : AddCircle (1 : ℝ)) :
    idxTwoH (compositeH A₀ C₀) (B₁ ⊗ₖ (1 : Matrix κ κ ℂ)) (B₂ ⊗ₖ (1 : Matrix κ κ ℂ)) hf hh φ χ
      = compositeH (idxTwoH A₀ B₁ B₂ hf hh φ χ) C₀ := by
  unfold idxTwoH compositeH
  rw [Matrix.add_kronecker, Matrix.add_kronecker, Matrix.smul_kronecker, Matrix.smul_kronecker]
  abel

/-- ★★ **With the third pointer's term absent the composite propagator is a product**: the
messenger's propagator with its two pointers' terms, and the clock's free propagator. -/
theorem idxTwoCarrierU_composite (hA : A₀.IsHermitian) (hB₁ : B₁.IsHermitian)
    (hB₂ : B₂.IsHermitian) (hC : C₀.IsHermitian) (hf : Function.Periodic f 1)
    (hh : Function.Periodic h 1) (φ χ : AddCircle (1 : ℝ)) (t : ℝ) :
    idxTwoCarrierU (compositeH_isHermitian hA hC)
        (kronecker_isHermitian hB₁ (Matrix.isHermitian_one (n := κ) (α := ℂ)))
        (kronecker_isHermitian hB₂ (Matrix.isHermitian_one (n := κ) (α := ℂ))) hf hh φ χ t
      = kronU (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ t) (idxFreeU hC t) := by
  apply Subtype.ext
  have e : (-Complex.I) • compositeH (idxTwoH A₀ B₁ B₂ hf hh φ χ) C₀
      = ((-Complex.I) • idxTwoH A₀ B₁ B₂ hf hh φ χ) ⊗ₖ (1 : Matrix κ κ ℂ)
        + (1 : Matrix ι ι ℂ) ⊗ₖ ((-Complex.I) • C₀) := by
    rw [compositeH, smul_add, Matrix.smul_kronecker, Matrix.kronecker_smul]
  rw [kronU_val, idxTwoCarrierU_val, idxTwoCarrierU_val, idxFreeU_val, idxTwoH_composite, e,
    exp_smul_kronecker_add]

/-- A product ray stays a product ray under that propagator. -/
theorem arenaKick_idxTwoCarrierU_composite (hA : A₀.IsHermitian) (hB₁ : B₁.IsHermitian)
    (hB₂ : B₂.IsHermitian) (hC : C₀.IsHermitian) (hf : Function.Periodic f 1)
    (hh : Function.Periodic h 1) (φ χ : AddCircle (1 : ℝ)) (t : ℝ) (p : GenArena ι)
    (q : GenArena κ) :
    arenaKick (idxTwoCarrierU (compositeH_isHermitian hA hC)
        (kronecker_isHermitian hB₁ (Matrix.isHermitian_one (n := κ) (α := ℂ)))
        (kronecker_isHermitian hB₂ (Matrix.isHermitian_one (n := κ) (α := ℂ))) hf hh φ χ t)
        (prodRay p q)
      = prodRay (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ t) p)
          (arenaKick (idxFreeU hC t) q) := by
  rw [idxTwoCarrierU_composite, arenaKick_kronU]

/-- The first pointer's displacement on the composite is its displacement on the messenger. -/
theorem idxTwoShiftFst_composite (hA : A₀.IsHermitian) (hB₁ : B₁.IsHermitian)
    (hB₂ : B₂.IsHermitian) (hC : C₀.IsHermitian) (hf : Function.Periodic f 1)
    (hh : Function.Periodic h 1) (φ χ : AddCircle (1 : ℝ)) (p : GenArena ι) (q : GenArena κ)
    (t : ℝ) :
    idxTwoShiftFst (compositeH_isHermitian hA hC)
        (kronecker_isHermitian hB₁ (Matrix.isHermitian_one (n := κ) (α := ℂ)))
        (kronecker_isHermitian hB₂ (Matrix.isHermitian_one (n := κ) (α := ℂ))) hf hh φ χ
        (prodRay p q) t
      = idxTwoShiftFst hA hB₁ hB₂ hf hh φ χ p t := by
  rw [idxTwoShiftFst_eq, idxTwoShiftFst_eq]
  simp only [arenaKick_idxTwoCarrierU_composite hA hB₁ hB₂ hC, arenaObs_kronecker_one]

/-- The second pointer's displacement on the composite is its displacement on the messenger. -/
theorem idxTwoShiftSnd_composite (hA : A₀.IsHermitian) (hB₁ : B₁.IsHermitian)
    (hB₂ : B₂.IsHermitian) (hC : C₀.IsHermitian) (hf : Function.Periodic f 1)
    (hh : Function.Periodic h 1) (φ χ : AddCircle (1 : ℝ)) (p : GenArena ι) (q : GenArena κ)
    (t : ℝ) :
    idxTwoShiftSnd (compositeH_isHermitian hA hC)
        (kronecker_isHermitian hB₁ (Matrix.isHermitian_one (n := κ) (α := ℂ)))
        (kronecker_isHermitian hB₂ (Matrix.isHermitian_one (n := κ) (α := ℂ))) hf hh φ χ
        (prodRay p q) t
      = idxTwoShiftSnd hA hB₁ hB₂ hf hh φ χ p t := by
  rw [idxTwoShiftSnd_eq, idxTwoShiftSnd_eq]
  simp only [arenaKick_idxTwoCarrierU_composite hA hB₁ hB₂ hC, arenaObs_kronecker_one]

/-- **The gated pointer's lifted displacement**: `−2 k'(ζ)` times the accumulated product of
the messenger's expectation of `P` and the clock's expectation of `X`, the messenger moving
with its two pointers' terms on the fibre `(φ, χ)` and the clock moving freely. -/
noncomputable def gateShift (hA : A₀.IsHermitian) (hB₁ : B₁.IsHermitian)
    (hB₂ : B₂.IsHermitian) (hC : C₀.IsHermitian) (P : Matrix ι ι ℂ) (X : Matrix κ κ ℂ)
    (hf : Function.Periodic f 1) (hh : Function.Periodic h 1) (hk : Function.Periodic k 1)
    (φ χ ζ : AddCircle (1 : ℝ)) (p : GenArena ι) (q : GenArena κ) (t : ℝ) : ℝ :=
  -2 * hk.deriv_periodic.lift ζ
    * ∫ s in (0 : ℝ)..t, arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p)
        * arenaObs X (arenaKick (idxFreeU hC s) q)

/-- **The joint flow of a composite carrier with three pointers**: two coupled to the messenger
observables `B₁ ⊗ 1`, `B₂ ⊗ 1` and the third to the product `P ⊗ X`. The flow, for the form of
`ℂℙ^N × T² × T² × T²`, of
`−2⟨A₀ ⊗ 1 + 1 ⊗ C₀⟩ − 2 f(θ₂)⟨B₁ ⊗ 1⟩ − 2 h(ψ₂)⟨B₂ ⊗ 1⟩ − 2 k(χ₂)⟨P ⊗ X⟩` (UA-17). -/
noncomputable def gateFlow (A₀ B₁ B₂ P : Matrix ι ι ℂ) (C₀ X : Matrix κ κ ℂ)
    (hf : Function.Periodic f 1) (hh : Function.Periodic h 1) (hk : Function.Periodic k 1)
    (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (hck : ContDiff ℝ ∞ k) (t : ℝ) :
    TriSigma (a * (b + 1) + b) → TriSigma (a * (b + 1) + b) :=
  threeCoupledFlow
    (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) (compositeH A₀ C₀))
    (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) (B₁ ⊗ₖ (1 : Matrix κ κ ℂ)))
    (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) (B₂ ⊗ₖ (1 : Matrix κ κ ℂ)))
    (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) (P ⊗ₖ X)) hf hh hk hc hch hck t

omit [Fintype ι] [Fintype κ] in
/-- ★ **The flow of the composite carrier preserves `μ_FS ⊗ vol ⊗ vol ⊗ vol`.** -/
theorem triMuL_map_gateFlow (hA : A₀.IsHermitian) (hB₁ : B₁.IsHermitian)
    (hB₂ : B₂.IsHermitian) (hP : P.IsHermitian) (hC : C₀.IsHermitian) (hX : X.IsHermitian)
    (hf : Function.Periodic f 1) (hh : Function.Periodic h 1) (hk : Function.Periodic k 1)
    (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (hck : ContDiff ℝ ∞ k)
    (p₀ : CPN (a * (b + 1) + b + 1)) (t : ℝ) :
    Measure.map (gateFlow e₁ e₂ A₀ B₁ B₂ P C₀ X hf hh hk hc hch hck t) (triMuL p₀)
      = triMuL p₀ :=
  triMuL_map_threeCoupledFlow ((compositeH_isHermitian hA hC).reindex (prodIdx e₁ e₂))
    ((kronecker_isHermitian hB₁ Matrix.isHermitian_one).reindex (prodIdx e₁ e₂))
    ((kronecker_isHermitian hB₂ Matrix.isHermitian_one).reindex (prodIdx e₁ e₂))
    ((kronecker_isHermitian hP hX).reindex (prodIdx e₁ e₂)) hf hh hk hc hch hck p₀ t

/-- ★★★ **The flow of the composite carrier from a product ray, on a fibre where the third
profile vanishes.** The carrier stays a product ray: the messenger moves by its own propagator
with its two pointers' terms and the clock moves freely. The two messenger pointers advance as
on the messenger's arena. The third pointer advances by `gateShift`: `−2 k'(χ₂)` times the
accumulated product of the messenger's `⟨P⟩` and the clock's `⟨X⟩`. -/
theorem gateFlow_prodRay (hA : A₀.IsHermitian) (hB₁ : B₁.IsHermitian)
    (hB₂ : B₂.IsHermitian) (hP : P.IsHermitian) (hC : C₀.IsHermitian)
    (hf : Function.Periodic f 1) (hh : Function.Periodic h 1) (hk : Function.Periodic k 1)
    (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (hck : ContDiff ℝ ∞ k) (t : ℝ)
    (p : GenArena ι) (q : GenArena κ) (θ ψ : KTorus) {χ : KTorus} (hz : hk.lift χ.2 = 0) :
    gateFlow e₁ e₂ A₀ B₁ B₂ P C₀ X hf hh hk hc hch hck t
        (((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q), θ), ψ), χ)
      = (((idxArenaEquiv (prodIdx e₁ e₂)
              (prodRay (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh θ.2 ψ.2 t) p)
                (arenaKick (idxFreeU hC t) q)),
            (θ.1 + ((idxTwoShiftFst hA hB₁ hB₂ hf hh θ.2 ψ.2 p t : ℝ) : AddCircle (1 : ℝ)),
              θ.2)),
           (ψ.1 + ((idxTwoShiftSnd hA hB₁ hB₂ hf hh θ.2 ψ.2 p t : ℝ) : AddCircle (1 : ℝ)),
              ψ.2)),
          pshift (gateShift hA hB₁ hB₂ hC P X hf hh hk θ.2 ψ.2 χ.2 p q t) χ) := by
  have h2 : ∀ u : ℝ, twoCoupledFlow
        (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) (compositeH A₀ C₀))
        (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) (B₁ ⊗ₖ (1 : Matrix κ κ ℂ)))
        (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) (B₂ ⊗ₖ (1 : Matrix κ κ ℂ))) hf hh hc
        hch u ((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q), θ), ψ)
      = ((idxArenaEquiv (prodIdx e₁ e₂)
            (prodRay (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh θ.2 ψ.2 u) p)
              (arenaKick (idxFreeU hC u) q)),
          (θ.1 + ((idxTwoShiftFst hA hB₁ hB₂ hf hh θ.2 ψ.2 p u : ℝ) : AddCircle (1 : ℝ)),
            θ.2)),
         (ψ.1 + ((idxTwoShiftSnd hA hB₁ hB₂ hf hh θ.2 ψ.2 p u : ℝ) : AddCircle (1 : ℝ)),
            ψ.2)) := by
    intro u
    rw [twoCoupledFlow_reindex (prodIdx e₁ e₂) (compositeH_isHermitian hA hC)
      (kronecker_isHermitian hB₁ Matrix.isHermitian_one)
      (kronecker_isHermitian hB₂ Matrix.isHermitian_one) hf hh hc hch u (prodRay p q) θ ψ,
      arenaKick_idxTwoCarrierU_composite hA hB₁ hB₂ hC, idxTwoShiftFst_composite hA hB₁ hB₂ hC,
      idxTwoShiftSnd_composite hA hB₁ hB₂ hC]
  refine Prod.ext ?_ ?_
  · rw [gateFlow, threeCoupledFlow_fst_of_lift_eq_zero _ _ _ _ hf hh hk hc hch hck t _ hz]
    exact h2 t
  · rw [gateFlow, threeCoupledFlow_snd_of_lift_eq_zero _ _ _ _ hf hh hk hc hch hck t _ hz]
    simp only [h2, schrodingerHamiltonian_reindex, arenaObs_kronecker hP]
    rw [gateShift, intervalIntegral.integral_const_mul]
    congr 1
    ring

/-! ### The gate: the third pointer moves only while the messenger is in the region -/

section Gate

variable [Nonempty κ]

omit [DecidableEq κ] [Nonempty κ] in
/-- The messenger's reading of `P` along its orbit is continuous in the flow parameter. -/
theorem continuous_arenaObs_idxTwoCarrierU (hA : A₀.IsHermitian) (hB₁ : B₁.IsHermitian)
    (hB₂ : B₂.IsHermitian) (P : Matrix ι ι ℂ) (hf : Function.Periodic f 1)
    (hh : Function.Periodic h 1) (φ χ : AddCircle (1 : ℝ)) (p : GenArena ι) :
    Continuous fun s : ℝ => arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p) :=
  (continuous_arenaObs P).comp
    ((continuous_idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ).arenaKick continuous_const)

omit [Fintype ι] [DecidableEq ι] [Nonempty κ] in
/-- The clock's free reading of `X` is continuous in the flow parameter. -/
theorem continuous_arenaObs_idxFreeU (hC : C₀.IsHermitian) (X : Matrix κ κ ℂ)
    (q : GenArena κ) :
    Continuous fun s : ℝ => arenaObs X (arenaKick (idxFreeU hC s) q) :=
  (continuous_arenaObs X).comp ((continuous_idxFreeU hC).arenaKick continuous_const)

/-- ★★ **Between two flow times the gated pointer moves by at most `2|k'(ζ)| c` times the
messenger's accumulated `⟨P⟩`**, when `⟨P⟩ ≥ 0` at every ray and `‖X‖ ≤ c`. While the messenger
is out of the region the pointer does not turn. -/
theorem abs_gateShift_sub_le (hA : A₀.IsHermitian) (hB₁ : B₁.IsHermitian)
    (hB₂ : B₂.IsHermitian) (hC : C₀.IsHermitian) (hf : Function.Periodic f 1)
    (hh : Function.Periodic h 1) (hk : Function.Periodic k 1) (φ χ ζ : AddCircle (1 : ℝ))
    (p : GenArena ι) (q : GenArena κ) (hP0 : ∀ r : GenArena ι, 0 ≤ arenaObs P r) {c : ℝ}
    (hX : ‖X‖ ≤ c) {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    |gateShift hA hB₁ hB₂ hC P X hf hh hk φ χ ζ p q t₂
        - gateShift hA hB₁ hB₂ hC P X hf hh hk φ χ ζ p q t₁|
      ≤ 2 * |hk.deriv_periodic.lift ζ| * c
        * ∫ s in t₁..t₂, arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p) := by
  have ho := continuous_arenaObs_idxTwoCarrierU hA hB₁ hB₂ P hf hh φ χ p
  have hx := continuous_arenaObs_idxFreeU hC X q
  have hox : Continuous fun s : ℝ =>
      arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p)
        * arenaObs X (arenaKick (idxFreeU hC s) q) := ho.mul hx
  have hkey : |∫ s in t₁..t₂, arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p)
        * arenaObs X (arenaKick (idxFreeU hC s) q)|
      ≤ c * ∫ s in t₁..t₂,
          arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p) := by
    rw [← intervalIntegral.integral_const_mul]
    refine (intervalIntegral.abs_integral_le_integral_abs ht).trans ?_
    refine intervalIntegral.integral_mono_on ht (hox.abs.intervalIntegrable t₁ t₂)
      ((continuous_const.mul ho).intervalIntegrable t₁ t₂) fun s _ => ?_
    rw [abs_mul, abs_of_nonneg (hP0 _)]
    exact (mul_comm _ _).trans_le
      (mul_le_mul_of_nonneg_right ((abs_arenaObs_le X _).trans hX) (hP0 _))
  rw [gateShift, gateShift, ← mul_sub,
    intervalIntegral.integral_interval_sub_left (hox.intervalIntegrable 0 t₂)
      (hox.intervalIntegrable 0 t₁), abs_mul, abs_mul, abs_neg, abs_two]
  exact (mul_le_mul_of_nonneg_left hkey
    (show (0 : ℝ) ≤ 2 * |hk.deriv_periodic.lift ζ| by positivity)).trans_eq (by ring)

/-- The same with a pointwise bound `⟨P⟩ ≤ η` on the interval: the pointer moves by at most
`2|k'(ζ)| c η (t₂ − t₁)`. -/
theorem abs_gateShift_sub_le_of_le (hA : A₀.IsHermitian) (hB₁ : B₁.IsHermitian)
    (hB₂ : B₂.IsHermitian) (hC : C₀.IsHermitian) (hf : Function.Periodic f 1)
    (hh : Function.Periodic h 1) (hk : Function.Periodic k 1) (φ χ ζ : AddCircle (1 : ℝ))
    (p : GenArena ι) (q : GenArena κ) (hP0 : ∀ r : GenArena ι, 0 ≤ arenaObs P r) {c : ℝ}
    (hc0 : 0 ≤ c) (hX : ‖X‖ ≤ c) {t₁ t₂ η : ℝ} (ht : t₁ ≤ t₂)
    (hη : ∀ s ∈ Icc t₁ t₂,
      arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p) ≤ η) :
    |gateShift hA hB₁ hB₂ hC P X hf hh hk φ χ ζ p q t₂
        - gateShift hA hB₁ hB₂ hC P X hf hh hk φ χ ζ p q t₁|
      ≤ 2 * |hk.deriv_periodic.lift ζ| * c * (η * (t₂ - t₁)) := by
  refine (abs_gateShift_sub_le hA hB₁ hB₂ hC hf hh hk φ χ ζ p q hP0 hX ht).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have ho := continuous_arenaObs_idxTwoCarrierU hA hB₁ hB₂ P hf hh φ χ p
  refine (intervalIntegral.integral_mono_on ht (ho.intervalIntegrable t₁ t₂)
    (continuous_const.intervalIntegrable t₁ t₂) hη).trans_eq ?_
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]

/-- ★★ **The gated pointer is within `2|k'(ζ)| c` times the accumulated `1 − ⟨P⟩` of the
pointer coupled to `X` alone**, when `⟨P⟩ ≤ 1` at every ray and `‖X‖ ≤ c`. While the messenger
is in the region the gated pointer is the clock's pointer. -/
theorem abs_gateShift_sub_free_le (hA : A₀.IsHermitian) (hB₁ : B₁.IsHermitian)
    (hB₂ : B₂.IsHermitian) (hC : C₀.IsHermitian) (hf : Function.Periodic f 1)
    (hh : Function.Periodic h 1) (hk : Function.Periodic k 1) (φ χ ζ : AddCircle (1 : ℝ))
    (p : GenArena ι) (q : GenArena κ) (hP1 : ∀ r : GenArena ι, arenaObs P r ≤ 1) {c : ℝ}
    (hX : ‖X‖ ≤ c) {t : ℝ} (ht : 0 ≤ t) :
    |gateShift hA hB₁ hB₂ hC P X hf hh hk φ χ ζ p q t
        - -2 * hk.deriv_periodic.lift ζ
          * ∫ s in (0 : ℝ)..t, arenaObs X (arenaKick (idxFreeU hC s) q)|
      ≤ 2 * |hk.deriv_periodic.lift ζ| * c
        * ∫ s in (0 : ℝ)..t,
            (1 - arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p)) := by
  have ho := continuous_arenaObs_idxTwoCarrierU hA hB₁ hB₂ P hf hh φ χ p
  have hx := continuous_arenaObs_idxFreeU hC X q
  have hox : Continuous fun s : ℝ =>
      arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p)
        * arenaObs X (arenaKick (idxFreeU hC s) q) := ho.mul hx
  have hkey : |∫ s in (0 : ℝ)..t,
        (arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p)
          * arenaObs X (arenaKick (idxFreeU hC s) q)
        - arenaObs X (arenaKick (idxFreeU hC s) q))|
      ≤ c * ∫ s in (0 : ℝ)..t,
          (1 - arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine (intervalIntegral.abs_integral_le_integral_abs ht).trans ?_
    refine intervalIntegral.integral_mono_on ht ((hox.sub hx).abs.intervalIntegrable 0 t)
      ((continuous_const.mul (continuous_const.sub ho)).intervalIntegrable 0 t) fun s _ => ?_
    have h1 : 0 ≤ 1 - arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p) :=
      sub_nonneg.2 (hP1 _)
    have e : arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p)
          * arenaObs X (arenaKick (idxFreeU hC s) q) - arenaObs X (arenaKick (idxFreeU hC s) q)
        = -((1 - arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p))
            * arenaObs X (arenaKick (idxFreeU hC s) q)) := by ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg h1]
    exact (mul_comm _ _).trans_le
      (mul_le_mul_of_nonneg_right ((abs_arenaObs_le X _).trans hX) h1)
  rw [gateShift, ← mul_sub,
    ← intervalIntegral.integral_sub (hox.intervalIntegrable 0 t) (hx.intervalIntegrable 0 t),
    abs_mul, abs_mul, abs_neg, abs_two]
  exact (mul_le_mul_of_nonneg_left hkey
    (show (0 : ℝ) ≤ 2 * |hk.deriv_periodic.lift ζ| by positivity)).trans_eq (by ring)

/-- The same with a pointwise bound `1 − ⟨P⟩ ≤ η` on `[0, t]`: the two pointers differ by at
most `2|k'(ζ)| c η t`. -/
theorem abs_gateShift_sub_free_le_of_le (hA : A₀.IsHermitian) (hB₁ : B₁.IsHermitian)
    (hB₂ : B₂.IsHermitian) (hC : C₀.IsHermitian) (hf : Function.Periodic f 1)
    (hh : Function.Periodic h 1) (hk : Function.Periodic k 1) (φ χ ζ : AddCircle (1 : ℝ))
    (p : GenArena ι) (q : GenArena κ) (hP1 : ∀ r : GenArena ι, arenaObs P r ≤ 1) {c : ℝ}
    (hc0 : 0 ≤ c) (hX : ‖X‖ ≤ c) {t η : ℝ} (ht : 0 ≤ t)
    (hη : ∀ s ∈ Icc (0 : ℝ) t,
      1 - arenaObs P (arenaKick (idxTwoCarrierU hA hB₁ hB₂ hf hh φ χ s) p) ≤ η) :
    |gateShift hA hB₁ hB₂ hC P X hf hh hk φ χ ζ p q t
        - -2 * hk.deriv_periodic.lift ζ
          * ∫ s in (0 : ℝ)..t, arenaObs X (arenaKick (idxFreeU hC s) q)|
      ≤ 2 * |hk.deriv_periodic.lift ζ| * c * (η * t) := by
  refine (abs_gateShift_sub_free_le hA hB₁ hB₂ hC hf hh hk φ χ ζ p q hP1 hX ht).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have ho := continuous_arenaObs_idxTwoCarrierU hA hB₁ hB₂ P hf hh φ χ p
  refine (intervalIntegral.integral_mono_on ht
    ((continuous_const.sub ho).intervalIntegrable 0 t)
    (continuous_const.intervalIntegrable 0 t) hη).trans_eq ?_
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]

end Gate

end Composite

/-! ### The messenger on the ring and the two-level clock -/

section Region

variable {M : ℕ}

/-- The occupancy of the complement of a region is one minus the occupancy of the region. -/
theorem arenaObs_regionProj_compl (A : Finset (ZMod (M + 1)))
    (p : GenArena (ZMod (M + 1) × Fin 2)) :
    arenaObs (regionProj Aᶜ) p = 1 - arenaObs (regionProj A) p := by
  rw [arenaObs_regionProj, arenaObs_regionProj, ← sum_arenaObs_siteProj p,
    ← Finset.sum_compl_add_sum A]
  ring

end Region

section Clock

variable {M Mc : ℕ} {f h k : ℝ → ℝ} (J μ g₁ g₂ : ℝ) (A B : Finset (ZMod (M + 1)))
  (Jc μ₀ μ₁ gc : ℝ) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
  (hk : Function.Periodic k 1)

variable (Mc) in
/-- **The joint flow of a messenger and a clock as one composite carrier, with three
pointers**: the Dirac messenger on its ring with pointers coupled to the regions `A` and `B`,
the two-level device on its own ring, and the device's pointer coupled to the product of the
messenger's projector on `A` and the device's level swap. The energy is
`−2⟨H_D ⊗ 1 + 1 ⊗ H_dev⟩ − 2 g₁ f(θ₂)⟨P_A ⊗ 1⟩ − 2 g₂ h(ψ₂)⟨P_B ⊗ 1⟩
  − 2 g_c k(χ₂)⟨P_A ⊗ X⟩` (UA-17). -/
noncomputable def gateClockFlow (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (t : ℝ) :
    TriSigma ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3))
      → TriSigma ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3)) :=
  gateFlow (diracIdx M) (clockIdx Mc) (diracHam J μ) ((g₁ : ℂ) • regionProj A)
    ((g₂ : ℂ) • regionProj B) (regionProj A) (deviceHam Jc μ₀ μ₁) (clockB Mc gc) hf hh hk hc
    hch hck t

/-- ★ **The flow of the messenger-and-clock composite preserves
`μ_FS ⊗ vol ⊗ vol ⊗ vol`.** -/
theorem triMuL_map_gateClockFlow (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (p₀ : CPN ((2 * M + 1) * (4 * Mc + 3 + 1) + (4 * Mc + 3) + 1))
    (t : ℝ) :
    Measure.map (gateClockFlow Mc J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hk hc hch hck t)
        (triMuL p₀) = triMuL p₀ :=
  triMuL_map_gateFlow (diracIdx M) (clockIdx Mc) (diracHam_isHermitian J μ)
    (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B)
    (regionProj_isHermitian A) (deviceHam_isHermitian Jc μ₀ μ₁) (clockB_isHermitian gc) hf hh
    hk hc hch hck p₀ t

/-- **The gated clock pointer's lifted displacement**: `−2 k'(χ₂)` times the accumulated
product of the messenger's occupancy of `A` and the device's reading of `g_c X`. -/
noncomputable def gateClockShift (φ χ ζ : AddCircle (1 : ℝ))
    (p : GenArena (ZMod (M + 1) × Fin 2)) (q : GenArena ((ZMod (Mc + 1) × Fin 2) × Fin 2))
    (t : ℝ) : ℝ :=
  gateShift (diracHam_isHermitian J μ) (regionProj_smul_isHermitian g₁ A)
    (regionProj_smul_isHermitian g₂ B) (deviceHam_isHermitian Jc μ₀ μ₁) (regionProj A)
    (clockB Mc gc) hf hh hk φ χ ζ p q t

/-- ★★ **The messenger-and-clock composite from a product ray, on a fibre where the clock
pointer's profile vanishes.** -/
theorem gateClockFlow_apply (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (t : ℝ) (p : GenArena (ZMod (M + 1) × Fin 2))
    (q : GenArena ((ZMod (Mc + 1) × Fin 2) × Fin 2)) (θ ψ : KTorus) {χ : KTorus}
    (hz : hk.lift χ.2 = 0) :
    gateClockFlow Mc J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hk hc hch hck t
        (((idxArenaEquiv (prodIdx (diracIdx M) (clockIdx Mc)) (prodRay p q), θ), ψ), χ)
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
          pshift (gateClockShift J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hk θ.2 ψ.2 χ.2 p q t) χ) :=
  gateFlow_prodRay (diracIdx M) (clockIdx Mc) (diracHam_isHermitian J μ)
    (regionProj_smul_isHermitian g₁ A) (regionProj_smul_isHermitian g₂ B)
    (regionProj_isHermitian A) (deviceHam_isHermitian Jc μ₀ μ₁) hf hh hk hc hch hck t p q θ ψ
    hz

/-- ★★ **The departure pointer moves exactly as in `regionTwoFlow`** (#367), from a product
ray on a fibre where the clock pointer's profile vanishes. -/
theorem gateClockFlow_fst_pointer (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (t : ℝ) (p : GenArena (ZMod (M + 1) × Fin 2))
    (q : GenArena ((ZMod (Mc + 1) × Fin 2) × Fin 2)) (θ ψ : KTorus) {χ : KTorus}
    (hz : hk.lift χ.2 = 0) :
    (gateClockFlow Mc J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hk hc hch hck t
        (((idxArenaEquiv (prodIdx (diracIdx M) (clockIdx Mc)) (prodRay p q), θ), ψ), χ)).1.1.2
      = (regionTwoFlow J μ g₁ g₂ A B hf hh hc hch t
          ((idxArenaEquiv (diracIdx M) p, θ), ψ)).1.2 := by
  rw [gateClockFlow_apply J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hk hc hch hck t p q θ ψ hz,
    regionTwoFlow_apply]

/-- ★★ **The arrival pointer moves exactly as in `regionTwoFlow`** (#367), from a product ray
on a fibre where the clock pointer's profile vanishes. -/
theorem gateClockFlow_snd_pointer (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hck : ContDiff ℝ ∞ k) (t : ℝ) (p : GenArena (ZMod (M + 1) × Fin 2))
    (q : GenArena ((ZMod (Mc + 1) × Fin 2) × Fin 2)) (θ ψ : KTorus) {χ : KTorus}
    (hz : hk.lift χ.2 = 0) :
    (gateClockFlow Mc J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hk hc hch hck t
        (((idxArenaEquiv (prodIdx (diracIdx M) (clockIdx Mc)) (prodRay p q), θ), ψ), χ)).1.2
      = (regionTwoFlow J μ g₁ g₂ A B hf hh hc hch t
          ((idxArenaEquiv (diracIdx M) p, θ), ψ)).2 := by
  rw [gateClockFlow_apply J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hk hc hch hck t p q θ ψ hz,
    regionTwoFlow_apply]

/-- On a fibre where its profile vanishes, the pointer of #357 on the same clock advances by
`−2 k'(ζ)` times the accumulated free reading of `g_c X`. -/
theorem idxPointerShift_eq_free {ζ : AddCircle (1 : ℝ)} (hz : hk.lift ζ = 0)
    (q : GenArena ((ZMod (Mc + 1) × Fin 2) × Fin 2)) (t : ℝ) :
    idxPointerShift (deviceHam_isHermitian Jc μ₀ μ₁) (clockB_isHermitian gc) hk ζ q t
      = -2 * hk.deriv_periodic.lift ζ
        * ∫ s in (0 : ℝ)..t, arenaObs (clockB Mc gc)
            (arenaKick (idxFreeU (deviceHam_isHermitian Jc μ₀ μ₁) s) q) :=
  idxPointerShift_of_lift_eq_zero _ _ hk hz q t

end Clock

/-! ### On the packet family of #375 -/

section Fine

variable {M Mc : ℕ} {f h k : ℝ → ℝ} (g₁ g₂ : ℝ) (Jc μ₀ μ₁ gc : ℝ)
  (hf : Function.Periodic f 1) (hh : Function.Periodic h 1) (hk : Function.Periodic k 1)
  {n : ℕ} (hn : 0 < n) (hL : 640000 * n ^ 3 ≤ M + 1)
include hn hL

/-- ★★ **Before the transit the gated pointer is the clock's pointer, within
`|k'(χ₂)||g_c| t/n`.** The messenger starts on the fine packet of index `n`, the gate is the
near half of its ring, and the fibre of the two region pointers is fine. At every flow time
`t ≤ (625π/3) n²` the gated pointer's displacement is within `|k'(ζ)||g_c| t/n` of the
displacement of the pointer of #357 on the same clock, on a fibre `ζ` where the clock
pointer's profile vanishes. -/
theorem fine_gateClock_before {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ fineFibres g₁ g₂ hf hh n) {ζ : AddCircle (1 : ℝ)} (hz : hk.lift ζ = 0)
    (q : GenArena ((ZMod (Mc + 1) × Fin 2) × Fin 2)) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ 625 * Real.pi / 3 * (n : ℝ) ^ 2) :
    |gateClockShift (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) Jc μ₀
          μ₁ gc hf hh hk φ χ ζ
          (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)) q t
        - idxPointerShift (deviceHam_isHermitian Jc μ₀ μ₁) (clockB_isHermitian gc) hk ζ q t|
      ≤ |hk.deriv_periodic.lift ζ| * |gc| * t / n := by
  have hr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [idxPointerShift_eq_free Jc μ₀ μ₁ gc hk hz q t]
  refine (abs_gateShift_sub_free_le_of_le (diracHam_isHermitian _ _)
    (regionProj_smul_isHermitian g₁ _) (regionProj_smul_isHermitian g₂ _)
    (deviceHam_isHermitian Jc μ₀ μ₁) hf hh hk φ χ ζ _ q
    (fun r => arenaObs_regionProj_le_one _ r) (abs_nonneg gc) (norm_clockB_le gc) ht0
    (η := 1 / (2 * (n : ℝ))) fun s hs => ?_).trans_eq ?_
  · rw [arenaObs_regionProj_compl, sub_sub_cancel]
    exact fineCarrier_far_before g₁ g₂ hf hh hn hL hx hs.1 (hs.2.trans ht)
  · field_simp

/-- ★★ **After the transit the gated pointer has stopped, within
`|k'(χ₂)||g_c| (t₂ − t₁)/n`.** With the same start and fibres, between any two flow times
`t₁ ≤ t₂` of `[(3125π/3) n², (4375π/3) n²]` the gated pointer's displacement changes by at
most `|k'(ζ)||g_c| (t₂ − t₁)/n`. -/
theorem fine_gateClock_after {φ χ : AddCircle (1 : ℝ)}
    (hx : (φ, χ) ∈ fineFibres g₁ g₂ hf hh n) (ζ : AddCircle (1 : ℝ))
    (q : GenArena ((ZMod (Mc + 1) × Fin 2) × Fin 2)) {t₁ t₂ : ℝ}
    (ht0 : 3125 * Real.pi / 3 * (n : ℝ) ^ 2 ≤ t₁) (ht : t₁ ≤ t₂)
    (ht2 : t₂ ≤ 4375 * Real.pi / 3 * (n : ℝ) ^ 2) :
    |gateClockShift (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) Jc μ₀
          μ₁ gc hf hh hk φ χ ζ
          (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)) q t₂
        - gateClockShift (fineHop n (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) Jc
          μ₀ μ₁ gc hf hh hk φ χ ζ
          (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)) q t₁|
      ≤ |hk.deriv_periodic.lift ζ| * |gc| * (t₂ - t₁) / n := by
  have hr : (0 : ℝ) < n := by exact_mod_cast hn
  refine (abs_gateShift_sub_le_of_le (diracHam_isHermitian _ _)
    (regionProj_smul_isHermitian g₁ _) (regionProj_smul_isHermitian g₂ _)
    (deviceHam_isHermitian Jc μ₀ μ₁) hf hh hk φ χ ζ _ q
    (fun r => arenaObs_regionProj_nonneg _ r) (abs_nonneg gc) (norm_clockB_le gc) ht
    (η := 1 / (2 * (n : ℝ))) fun s hs => ?_).trans_eq ?_
  · rw [arenaObs_regionProj_compl]
    have h := fineCarrier_far_after g₁ g₂ hf hh hn hL hx (ht0.trans hs.1) (hs.2.trans ht2)
    have e : arenaObs (regionProj (farHalf (M + 1)))
        (arenaKick (idxTwoCarrierU (diracHam_isHermitian (L := M + 1) (fineHop n (M + 1)) 3)
          (regionProj_smul_isHermitian g₁ (farHalf (M + 1))ᶜ)
          (regionProj_smul_isHermitian g₂ (farHalf (M + 1))) hf hh φ χ s)
          (chainRay (finePacket (L := M + 1) n 0) (finePacket_ne_zero hn hL)))
        = arenaObs (regionProj (farHalf (M + 1))) (fineCarrier g₁ g₂ hf hh hn hL φ χ s) := rfl
    rw [e]
    linarith
  · field_simp

end Fine

end CSD.RecordLayer

end
