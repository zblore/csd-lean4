/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedPentaRun
public import CsdLean4.RecordLayer.UnifiedCoincidenceFlow

/-!
# Three carriers and five gates: each pointer's displacement is a two-carrier one

**Category:** 7-SigmaLayer (the record layer). BACKLOG #405 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; item R1 of the list under
UD-164, second half. No new assumption beyond UA-18.

#404 has the five-pointer flow for any carrier and any five observables. This module takes the
carrier of UA-18: a messenger times a composite of two clocks, started in a product ray, with
the five observables the five gates of UA-18 (c). Each gate joins two of the three carriers,
and its pointer's displacement is the two-carrier `coincShift` of #393 for those two; the
third carrier drops out.

* `freeShift_prodRay` — along the uncoupled orbit of a product ray `freeShift` is `coincShift`;
* `arenaObs_kronecker_right`, `siteSel_snd`, `siteSel_fst`;
* ★ `arenaObs_gateOp_snd`, `arenaObs_gateOp_fst` — a gate between the first carrier and one
  member of a composite second carrier reads that member only;
* `gateOpL`, ★ `arenaObs_gateOpL_prodRay` — a gate whose operator acts on the first carrier is
  the gate of #390 with the two carriers exchanged;
* `gateOp_snd_isHermitian`;
* ★★ `coincShift_gate_snd`, `coincShift_gate_fst`, `coincShift_one_kronecker_pair`,
  `coincShift_gateOpL` — the same for the displacements along the uncoupled orbits;
* `triRun` — the five-pointer flow of the three carriers with the five gates;
* ★★★ `tri_radar_lorentz` — the top-down statement of #402 for `triRun`: the five histories
  are now histories of five two-carrier gate displacements (messenger with `B` twice, `A`
  with `B` twice, messenger with `A` once).

## Exact scope

* **R1 is reduced, not discharged.** What is done: the run is the five-pointer flow of three
  carriers with five gates, and each hypothesis of #402 about a pointer is a statement about
  the `coincShift` of a `gateOp` for two carriers, the object of #394, #399 and #400. What is
  not done: the five histories themselves. Those theorems give them on the ring, for a flat
  messenger and a flat clock packet; on the chain with walls they need R2.
* **Any three carriers, sites and relations.** The uncoupled energies, the site maps, the five
  relations and the two operators `Ya`, `Yb` are arbitrary, except that `Yb` is Hermitian and
  does not move `B` between sites. No chain, wall, packet or clock is instantiated.
* **A product start, on the fibres where all five profiles vanish.** Both are null sets (R7 of
  the list is untouched).
* **Conditional as #402** on the four times, their relations and tolerances, and the moving
  clock's rate. R2 to R7 are untouched.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-18,
UO-16, UD-140, UD-145, UD-164, UD-167, UD-168, UD-169, UD-170);
`RecordLayer/UnifiedPentaRun.lean` (#404: `freeShift`, `penta_radar_lorentz`);
`RecordLayer/UnifiedCoincidenceFlow.lean` (#393: `coincShift`, `arenaKick_idxFreeU_composite`,
`coincShift_one_kronecker`); `RecordLayer/UnifiedCoincidence.lean` (#390: `gateOp`, `siteSel`,
`coincProj_eq_sum`, `arenaObs_gateOp_prodRay`, `gateOp_isHermitian`); `CV/ProductRay.lean`
(`arenaObs_kronecker`, `arenaObs_one_kronecker`, `arenaObs_kronecker_one`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### A product start: `freeShift` is `coincShift` -/

section Reduce

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {A₀ : Matrix ι ι ℂ} {C₀ : Matrix κ κ ℂ}

/-- Along the uncoupled orbit of a product ray of a composite, a pointer's displacement is the
two-carrier displacement of #393. -/
theorem freeShift_prodRay (hA : A₀.IsHermitian) (hC : C₀.IsHermitian)
    (G : Matrix (ι × κ) (ι × κ) ℂ) (z : ℝ) (p : GenArena ι) (q : GenArena κ) (t : ℝ) :
    freeShift (compositeH_isHermitian hA hC) G z (prodRay p q) t
      = coincShift hA hC G z p q t := by
  simp only [freeShift, coincShift, arenaKick_idxFreeU_composite hA hC]

omit [DecidableEq ι] [DecidableEq κ] in
/-- The expectation of `A ⊗ B` in a product ray is the product of the expectations, for
Hermitian `B`. -/
theorem arenaObs_kronecker_right (A : Matrix ι ι ℂ) {B : Matrix κ κ ℂ} (hB : B.IsHermitian)
    (p : GenArena ι) (q : GenArena κ) :
    arenaObs (A ⊗ₖ B) (prodRay p q) = arenaObs A p * arenaObs B q := by
  rw [arenaObs, arenaObs, arenaObs, arenaDM_prodRay, ← Matrix.mul_kronecker_mul,
    Matrix.trace_kronecker]
  simp only [RCLike.re_to_complex]
  rw [Complex.mul_re, im_trace_arenaDM_mul q hB, mul_zero, sub_zero]

end Reduce

/-! ### Gates between two of three carriers -/

section Gates

variable {ι κa κb S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κa] [DecidableEq κa]
  [Fintype κb] [DecidableEq κb] [Fintype S] [DecidableEq S]

omit [Fintype κa] [Fintype κb] [Fintype S] in
/-- The site projector of a composite whose site is that of its second member. -/
theorem siteSel_snd (β : κb → S) (s : S) :
    siteSel (fun k : κa × κb => β k.2) s = (1 : Matrix κa κa ℂ) ⊗ₖ siteSel β s := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [siteSel, Matrix.kroneckerMap_apply, Matrix.diagonal_apply, Matrix.one_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all

omit [Fintype κa] [Fintype κb] [Fintype S] in
/-- The site projector of a composite whose site is that of its first member. -/
theorem siteSel_fst (α : κa → S) (s : S) :
    siteSel (fun k : κa × κb => α k.1) s = siteSel α s ⊗ₖ (1 : Matrix κb κb ℂ) := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [siteSel, Matrix.kroneckerMap_apply, Matrix.diagonal_apply, Matrix.one_apply,
    Prod.mk.injEq]
  split_ifs <;> simp_all

variable (σ : ι → S) (α : κa → S) (β : κb → S) (r : S → S → Prop) [DecidableRel r]

/-- ★ **A gate between the first carrier and the second member of a composite reads that
member only**, on a product ray. -/
theorem arenaObs_gateOp_snd (Y : Matrix κb κb ℂ) (p : GenArena ι) (qa : GenArena κa)
    (qb : GenArena κb) :
    arenaObs (gateOp σ (fun k : κa × κb => β k.2) r ((1 : Matrix κa κa ℂ) ⊗ₖ Y))
        (prodRay p (prodRay qa qb))
      = arenaObs (gateOp σ β r Y) (prodRay p qb) := by
  rw [arenaObs_gateOp_prodRay, arenaObs_gateOp_prodRay]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
  rw [siteSel_snd, ← Matrix.mul_kronecker_mul, Matrix.one_mul, arenaObs_one_kronecker]

/-- A gate between the first carrier and the first member of a composite reads that member
only, on a product ray. -/
theorem arenaObs_gateOp_fst (Y : Matrix κa κa ℂ) (p : GenArena ι) (qa : GenArena κa)
    (qb : GenArena κb) :
    arenaObs (gateOp σ (fun k : κa × κb => α k.1) r (Y ⊗ₖ (1 : Matrix κb κb ℂ)))
        (prodRay p (prodRay qa qb))
      = arenaObs (gateOp σ α r Y) (prodRay p qa) := by
  rw [arenaObs_gateOp_prodRay, arenaObs_gateOp_prodRay]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
  rw [siteSel_fst, ← Matrix.mul_kronecker_mul, Matrix.one_mul, arenaObs_kronecker_one]

/-- **A gated operator acting on the first carrier**: the coincidence projector times
`Y ⊗ 1`. -/
def gateOpL (Y : Matrix κa κa ℂ) : Matrix (κa × κb) (κa × κb) ℂ :=
  coincProj α β r * (Y ⊗ₖ (1 : Matrix κb κb ℂ))

/-- ★ **A gate whose operator acts on the first carrier is the gate of #390 with the two
carriers exchanged**, on a product ray. -/
theorem arenaObs_gateOpL_prodRay (Y : Matrix κa κa ℂ) (qa : GenArena κa) (qb : GenArena κb) :
    arenaObs (gateOpL α β r Y) (prodRay qa qb)
      = arenaObs (gateOp β α (fun s s' => r s' s) Y) (prodRay qb qa) := by
  have h : gateOpL α β r Y
      = ∑ s, ∑ s', if r s s' then (siteSel α s * Y) ⊗ₖ siteSel β s' else 0 := by
    rw [gateOpL, coincProj_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s' _ => ?_
    split_ifs
    · rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
    · rw [zero_mul]
  rw [h, arenaObs_gateOp_prodRay]
  simp only [arenaObs_finset_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun s _ => ?_
  split_ifs
  · rw [arenaObs_kronecker_right _ (siteSel_isHermitian β s') qa qb, mul_comm]
  · exact arenaObs_zero' _

omit [Fintype S] [DecidableEq S] in
/-- The gate between the first carrier and the second member of a composite is Hermitian when
`Y` is Hermitian and does not move that member between sites. -/
theorem gateOp_snd_isHermitian {Y : Matrix κb κb ℂ} (hYh : Y.IsHermitian)
    (hY : ∀ i j, β i ≠ β j → Y i j = 0) :
    (gateOp σ (fun k : κa × κb => β k.2) r ((1 : Matrix κa κa ℂ) ⊗ₖ Y)).IsHermitian := by
  refine gateOp_isHermitian σ _ r (kronecker_isHermitian Matrix.isHermitian_one hYh) ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  rw [Matrix.kroneckerMap_apply, hY b b' h, mul_zero]

variable {M₀ : Matrix ι ι ℂ} {A₀ : Matrix κa κa ℂ} {B₀ : Matrix κb κb ℂ}

/-- ★★ **The messenger's gate with the second clock**: the first clock drops out of the
displacement. -/
theorem coincShift_gate_snd (hM : M₀.IsHermitian) (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (Y : Matrix κb κb ℂ) (z : ℝ) (p : GenArena ι) (qa : GenArena κa) (qb : GenArena κb)
    (t : ℝ) :
    coincShift hM (compositeH_isHermitian hA hB)
        (gateOp σ (fun k : κa × κb => β k.2) r ((1 : Matrix κa κa ℂ) ⊗ₖ Y)) z p
        (prodRay qa qb) t
      = coincShift hM hB (gateOp σ β r Y) z p qb t := by
  simp only [coincShift, arenaKick_idxFreeU_composite hA hB, arenaObs_gateOp_snd]

/-- **The messenger's gate with the first clock**: the second clock drops out of the
displacement. -/
theorem coincShift_gate_fst (hM : M₀.IsHermitian) (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (Y : Matrix κa κa ℂ) (z : ℝ) (p : GenArena ι) (qa : GenArena κa) (qb : GenArena κb)
    (t : ℝ) :
    coincShift hM (compositeH_isHermitian hA hB)
        (gateOp σ (fun k : κa × κb => α k.1) r (Y ⊗ₖ (1 : Matrix κb κb ℂ))) z p
        (prodRay qa qb) t
      = coincShift hM hA (gateOp σ α r Y) z p qa t := by
  simp only [coincShift, arenaKick_idxFreeU_composite hA hB, arenaObs_gateOp_fst]

omit [Fintype S] [DecidableEq S] in
/-- **An observable of the two clocks alone**: the messenger drops out of the displacement. -/
theorem coincShift_one_kronecker_pair (hM : M₀.IsHermitian) (hA : A₀.IsHermitian)
    (hB : B₀.IsHermitian) (G : Matrix (κa × κb) (κa × κb) ℂ) (z : ℝ) (p : GenArena ι)
    (qa : GenArena κa) (qb : GenArena κb) (t : ℝ) :
    coincShift hM (compositeH_isHermitian hA hB) ((1 : Matrix ι ι ℂ) ⊗ₖ G) z p
        (prodRay qa qb) t
      = coincShift hA hB G z qa qb t := by
  rw [coincShift_one_kronecker]
  simp only [coincShift, arenaKick_idxFreeU_composite hA hB]

/-- **A gate of the two clocks with the operator on the first** is, in displacement, the gate
of #390 with the two clocks exchanged. -/
theorem coincShift_gateOpL (hA : A₀.IsHermitian) (hB : B₀.IsHermitian) (Y : Matrix κa κa ℂ)
    (z : ℝ) (qa : GenArena κa) (qb : GenArena κb) (t : ℝ) :
    coincShift hA hB (gateOpL α β r Y) z qa qb t
      = coincShift hB hA (gateOp β α (fun s s' => r s' s) Y) z qb qa t := by
  simp only [coincShift, arenaObs_gateOpL_prodRay]

end Gates

/-! ### M6 from the top, for three carriers and five gates -/

section Tri

variable {ι κa κb S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κa] [DecidableEq κa]
  [Fintype κb] [DecidableEq κb] [Fintype S] [DecidableEq S] {N : ℕ}
  (e : ι × (κa × κb) ≃ Fin (N + 1)) (M₀ : Matrix ι ι ℂ) (A₀ : Matrix κa κa ℂ)
  (B₀ : Matrix κb κb ℂ) (σ : ι → S) (α : κa → S) (β : κb → S)
  (r₁ r₂ r₃ r₄ r₅ : S → S → Prop) [DecidableRel r₁] [DecidableRel r₂] [DecidableRel r₃]
  [DecidableRel r₄] [DecidableRel r₅] (Ya : Matrix κa κa ℂ) (Yb : Matrix κb κb ℂ)
  {f g k l r : ℝ → ℝ}

/-- **The run of three carriers with five gates**: the five-pointer flow of UA-18's arena for
the carrier messenger × (clock `A` × clock `B`), from a product ray. Pointer 1 is gated by
the relation `r₁` between the messenger and `B` and coupled to `B`'s operator `Yb`; pointer 2
the same with `r₂`; pointer 3 is gated by `r₃` between `A` and `B` and coupled to `Yb`;
pointer 4 by `r₄` between the messenger and `A`, coupled to `A`'s operator `Ya`; pointer 5 by
`r₅` between `A` and `B`, coupled to `Ya`. -/
def triRun (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hr : Function.Periodic r 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k)
    (hcl : ContDiff ℝ ∞ l) (hcr : ContDiff ℝ ∞ r) (p : GenArena ι) (qa : GenArena κa)
    (qb : GenArena κb) (θ ψ χ ξ ζ : KTorus) : ℝ → PentaSigma N := fun t =>
  fiveCoupledFlow (Matrix.reindex e e (compositeH M₀ (compositeH A₀ B₀)))
    (Matrix.reindex e e
      (gateOp σ (fun k : κa × κb => β k.2) r₁ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)))
    (Matrix.reindex e e
      (gateOp σ (fun k : κa × κb => β k.2) r₂ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)))
    (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ gateOp α β r₃ Yb))
    (Matrix.reindex e e
      (gateOp σ (fun k : κa × κb => α k.1) r₄ (Ya ⊗ₖ (1 : Matrix κb κb ℂ))))
    (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ gateOpL α β r₅ Ya))
    hf hg hk hl hr hc hcg hck hcl hcr t
    (((((idxArenaEquiv e (prodRay p (prodRay qa qb)), θ), ψ), χ), ξ), ζ)

variable {e M₀ A₀ B₀ σ α β r₁ r₂ r₃ r₄ r₅ Ya Yb}

/-- ★★★ **M6 from the top, for three carriers and five gates.** The run `triRun` from a
product ray on the fibre where all five profiles vanish, the five pointers started at `1/12`.
If the five two-carrier gate displacements have the histories of
`radar_lorentz_of_histories` (#402): the messenger's two gates with `B` (emission gated,
return away), `B`'s gate with `A` (meeting), the messenger's gate with `A` (relay) and `A`'s
gate with `B` (meeting); with the rate and the times as there: then at every choice of flow
times in the five reading windows the five pointers have counts, and those counts satisfy the
Lorentz statement with the errors of #402. -/
theorem tri_radar_lorentz (hM : M₀.IsHermitian) (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hYb : Yb.IsHermitian) (hYbs : ∀ i j, β i ≠ β j → Yb i j = 0)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hr : Function.Periodic r 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k)
    (hcl : ContDiff ℝ ∞ l) (hcr : ContDiff ℝ ∞ r) (p : GenArena ι) (qa : GenArena κa)
    (qb : GenArena κb) {θ ψ χ ξ ζ : KTorus}
    (hθ : hf.lift θ.2 = 0) (hψ : hg.lift ψ.2 = 0) (hχ : hk.lift χ.2 = 0)
    (hξ : hl.lift ξ.2 = 0) (hζ : hr.lift ζ.2 = 0)
    (hθ1 : rep θ.1 = 1 / 12) (hψ1 : rep ψ.1 = 1 / 12) (hχ1 : rep χ.1 = 1 / 12)
    (hξ1 : rep ξ.1 = 1 / 12) (hζ1 : rep ζ.1 = 1 / 12)
    {v R₀ RB κ TE TR TRet TM tE tR tRet tMB tMA τE τR τRet τMB τMA : ℝ}
    {δe ve tbe tce c vr η₀ η t4 t5 δμ vμ tbμ tcμ δρ vρ tbρ tcρ δm vm tbm tcm : ℝ}
    (hv0 : 0 ≤ v) (hv : v < 1) (hR₀ : 0 < R₀)
    (hκ : |RB - Real.sqrt (1 - v ^ 2) * R₀| ≤ κ * R₀)
    (hE : TR - TE = v * (TM - TE)) (hRet : TRet - TR = v * (TM - TRet))
    (hτE : |tE - TE| ≤ τE) (hτRet : |tRet - TRet| ≤ τRet) (hτMB : |tMB - TM| ≤ τMB)
    (hτR : |tR - TR| ≤ τR) (hτMA : |tMA - TM| ≤ τMA)
    (He : IsGatedHistory
      (coincShift hM hB (gateOp σ β r₁ Yb) (hf.deriv_periodic.lift θ.2) p qb) RB δe ve tE tbe
      tce)
    (Hr : IsAwayHistory
      (coincShift hM hB (gateOp σ β r₂ Yb) (hg.deriv_periodic.lift ψ.2) p qb) RB c vr η₀ η tE
      tbe tRet t4 t5)
    (Hμ : IsGatedHistory
      (coincShift hA hB (gateOp α β r₃ Yb) (hk.deriv_periodic.lift χ.2) qa qb) RB δμ vμ tMB
      tbμ tcμ)
    (Hρ : IsGatedHistory
      (coincShift hM hA (gateOp σ α r₄ Ya) (hl.deriv_periodic.lift ξ.2) p qa) R₀ δρ vρ tR tbρ
      tcρ)
    (Hm : IsGatedHistory
      (coincShift hB hA (gateOp β α (fun s s' => r₅ s' s) Ya) (hr.deriv_periodic.lift ζ.2)
        qb qa) R₀ δm vm tMA tbm tcm) :
    ∀ se, tbe ≤ se → se ≤ tce → ∀ sr, t4 ≤ sr → sr ≤ t5 → ∀ sμ, tbμ ≤ sμ → sμ ≤ tcμ →
      ∀ sρ, tbρ ≤ sρ → sρ ≤ tcρ → ∀ sm, tbm ≤ sm → sm ≤ tcm →
      ∃ Ne Nr Nμ Nρ Nm : ℕ,
        IsTickCount {x : PentaSigma N | x.1.1.1.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.1.1.1.2 ∈ displayArc}
            (triRun e M₀ A₀ B₀ σ α β r₁ r₂ r₃ r₄ r₅ Ya Yb hf hg hk hl hr hc hcg hck hcl hcr
              p qa qb θ ψ χ ξ ζ) se Ne
        ∧ IsTickCount {x : PentaSigma N | x.1.1.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.1.1.2 ∈ displayArc}
            (triRun e M₀ A₀ B₀ σ α β r₁ r₂ r₃ r₄ r₅ Ya Yb hf hg hk hl hr hc hcg hck hcl hcr
              p qa qb θ ψ χ ξ ζ) sr Nr
        ∧ IsTickCount {x : PentaSigma N | x.1.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.1.2 ∈ displayArc}
            (triRun e M₀ A₀ B₀ σ α β r₁ r₂ r₃ r₄ r₅ Ya Yb hf hg hk hl hr hc hcg hck hcl hcr
              p qa qb θ ψ χ ξ ζ) sμ Nμ
        ∧ IsTickCount {x : PentaSigma N | x.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.2 ∈ displayArc}
            (triRun e M₀ A₀ B₀ σ α β r₁ r₂ r₃ r₄ r₅ Ya Yb hf hg hk hl hr hc hcg hck hcl hcr
              p qa qb θ ψ χ ξ ζ) sρ Nρ
        ∧ IsTickCount {x : PentaSigma N | x.2 ∈ readyArc 2}
            {x : PentaSigma N | x.2 ∈ displayArc}
            (triRun e M₀ A₀ B₀ σ α β r₁ r₂ r₃ r₄ r₅ Ya Yb hf hg hk hl hr hc hcg hck hcl hcr
              p qa qb θ ψ χ ξ ζ) sm Nm
        ∧ |(lorentzBoost 1 (-v)
                ((Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀, 0)).1
              - (((Ne : ℝ) * (2 * Real.pi) / R₀
                    + ((Ne : ℝ) * (2 * Real.pi) + (Nr : ℝ) * (2 * Real.pi)) / R₀) / 2
                  - (Nμ : ℝ) * (2 * Real.pi) / R₀)|
            ≤ ((gatedErr ve tE tbe / R₀ + κ * tE + τE)
                + ((gatedErr ve tE tbe + awayErr vr tE tbe tRet t4 + RB * (tbe - tE)) / R₀
                    + κ * tRet + τRet)) / 2
              + (gatedErr vμ tMB tbμ / R₀ + κ * tMB + τMB)
              + ((gatedErr vρ tR tbρ / R₀ + τR) + (gatedErr vm tMA tbm / R₀ + τMA))
                / Real.sqrt (1 - v ^ 2)
        ∧ |(lorentzBoost 1 (-v)
                ((Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀, 0)).2
              - (-((((Ne : ℝ) * (2 * Real.pi) + (Nr : ℝ) * (2 * Real.pi)) / R₀
                    - (Ne : ℝ) * (2 * Real.pi) / R₀) / 2))|
            ≤ ((gatedErr ve tE tbe / R₀ + κ * tE + τE)
                + ((gatedErr ve tE tbe + awayErr vr tE tbe tRet t4 + RB * (tbe - tE)) / R₀
                    + κ * tRet + τRet)) / 2
              + v * ((gatedErr vρ tR tbρ / R₀ + τR) + (gatedErr vm tMA tbm / R₀ + τMA))
                / Real.sqrt (1 - v ^ 2)
        ∧ |(Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀ - (tR - tMA)|
            ≤ (gatedErr vρ tR tbρ + gatedErr vm tMA tbm) / R₀ := by
  have hAB := compositeH_isHermitian hA hB
  have hH := compositeH_isHermitian hM hAB
  have e1 : ∀ (rr : S → S → Prop) [DecidableRel rr] (z : ℝ),
      freeShift hH (gateOp σ (fun k : κa × κb => β k.2) rr ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)) z
          (prodRay p (prodRay qa qb))
        = coincShift hM hB (gateOp σ β rr Yb) z p qb := fun rr _ z =>
    funext fun t => by rw [freeShift_prodRay hM hAB, coincShift_gate_snd σ β rr hM hA hB]
  have e3 : ∀ z : ℝ,
      freeShift hH ((1 : Matrix ι ι ℂ) ⊗ₖ gateOp α β r₃ Yb) z (prodRay p (prodRay qa qb))
        = coincShift hA hB (gateOp α β r₃ Yb) z qa qb := fun z =>
    funext fun t => by rw [freeShift_prodRay hM hAB, coincShift_one_kronecker_pair hM hA hB]
  have e4 : ∀ z : ℝ,
      freeShift hH (gateOp σ (fun k : κa × κb => α k.1) r₄ (Ya ⊗ₖ (1 : Matrix κb κb ℂ))) z
          (prodRay p (prodRay qa qb))
        = coincShift hM hA (gateOp σ α r₄ Ya) z p qa := fun z =>
    funext fun t => by rw [freeShift_prodRay hM hAB, coincShift_gate_fst σ α r₄ hM hA hB]
  have e5 : ∀ z : ℝ,
      freeShift hH ((1 : Matrix ι ι ℂ) ⊗ₖ gateOpL α β r₅ Ya) z (prodRay p (prodRay qa qb))
        = coincShift hB hA (gateOp β α (fun s s' => r₅ s' s) Ya) z qb qa := fun z =>
    funext fun t => by
      rw [freeShift_prodRay hM hAB, coincShift_one_kronecker_pair hM hA hB,
        coincShift_gateOpL]
  rw [← e1 r₁] at He
  rw [← e1 r₂] at Hr
  rw [← e3] at Hμ
  rw [← e4] at Hρ
  rw [← e5] at Hm
  unfold triRun
  exact penta_radar_lorentz e hH (gateOp_snd_isHermitian σ β r₁ hYb hYbs)
    (gateOp_snd_isHermitian σ β r₂ hYb hYbs) hf hg hk hl hr hc hcg hck hcl hcr
    (prodRay p (prodRay qa qb)) hθ hψ hχ hξ hζ hθ1 hψ1 hχ1 hξ1 hζ1 hv0 hv hR₀ hκ hE hRet hτE
    hτRet hτMB hτR hτMA He Hr Hμ Hρ Hm

end Tri

end CSD.RecordLayer

end
