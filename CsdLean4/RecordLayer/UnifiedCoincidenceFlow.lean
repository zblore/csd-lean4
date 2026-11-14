/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedCoincidence

/-!
# Two gated pointers on a composite carrier, from a product ray

**Category:** 7-SigmaLayer (the record layer). BACKLOG #393 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; step (4) of the plan of
2026-11-14, third brick: the flow with the couplings of UA-18 (c). No new assumption beyond
UA-18.

#390 has the coincidence projector and the gated operator as operators. This module puts two
pointers, each coupled to an observable of a composite of two carriers, into one joint flow
on `ℂℙ^N × T² × T²` (the two-pointer arena of #359), and solves it from a product ray on a
fibre where both profiles vanish.

* `idxFreeU_composite`, `arenaKick_idxFreeU_composite` — the composite's uncoupled propagator
  is the product of the two carriers' propagators;
* ★ `idxTwoCarrierU_of_lift_eq_zero` — on a fibre where both profiles vanish the carrier
  moves by its uncoupled propagator, whatever the two coupled observables are;
* `coincShift`, `coincFlow`, ★★ `coincFlow_prodRay` — from a product ray on such a fibre: the
  carrier stays a product ray, each carrier moving freely, and each pointer advances by
  `−2 z ∫₀ᵗ ⟨G⟩`, `z` the derivative of its profile at its conserved angle;
* `continuous_arenaObs_prodRay_free`, ★ `coincShift_add`, `coincShift_one_kronecker`;
* ★ `gateOp_add_gateOp_not` — `gateOp r Y + gateOp (¬r) Y = 1 ⊗ Y`;
* ★★ `coincShift_gateOp` — the gated displacement site by site: the accumulated sum over
  related pairs of the first carrier's occupancy of its site times the second carrier's
  `arenaObs (siteSel τ s' * Y)`;
* ★★★ `coincShift_gateOp_add_not` — for two pointers with the same profile derivative, one
  coupled to a gate and one to its complement: the two displacements add up, at every flow
  time, to the displacement of a pointer coupled to `Y` on the second carrier alone.

## Exact scope

* **Displacements, not records.** Nothing here is a swing, a tick, a count or a reading. The
  identity is between lifted displacements of two pointers. Tick counts are whole numbers of
  passages and are not shown to add.
* **Only the fibres where both profiles vanish, and only product starts.** There neither
  pointer acts on the carrier. For the profile `trainF` that is a null set of fibres, and
  product rays are a null set of the base (two calculations, not in Lean). Off those fibres
  a gated term joins the two carriers; nothing is proved there.
* **The same profile derivative for both pointers** in the last theorem: for instance the
  same profile and the same conserved angle.
* **Any two Hermitian observables of the composite** in `coincFlow_prodRay`. For a gate,
  `gateOp_isHermitian` (#390) supplies that when `Y` does not move the second carrier
  between sites; no carrier, clock or relation is instantiated here.
* **Two carriers and two pointers.** UA-18 has three carriers, five pointers and walls. The
  carriers' uncoupled energies are arbitrary Hermitian matrices here.
* **That the flow preserves the product measure** follows from #359 for the two-pointer
  arena and is not restated.
* **Earlier.** #376 (`gateFlow_prodRay`) is the same statement for one product observable
  `P ⊗ X` as a third pointer beside two messenger pointers.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-13,
UA-17, UA-18, UO-16, UD-140, UD-145, UD-146); `RecordLayer/UnifiedCoincidence.lean` (#390:
`gateOp`, `coincProj`, `one_sub_coincProj`, `arenaObs_gateOp_prodRay`);
`RecordLayer/UnifiedCompositeCarrier.lean` (#376: `compositeH`, `prodIdx`,
`gateFlow_prodRay`); `RecordLayer/UnifiedTwoPointer.lean` (#359: `twoCoupledFlow_reindex`,
`idxTwoCarrierU`, `idxTwoShiftFst_eq`); `CV/ProductRay.lean` (`kronU`, `arenaKick_kronU`,
`exp_smul_kronecker_add`, `arenaObs_one_kronecker`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

section PairFlow

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {a b : ℕ}
  (e₁ : ι ≃ Fin (a + 1)) (e₂ : κ ≃ Fin (b + 1)) {f h : ℝ → ℝ}
  {A₀ : Matrix ι ι ℂ} {C₀ : Matrix κ κ ℂ} {G₁ G₂ : Matrix (ι × κ) (ι × κ) ℂ}

/-- The uncoupled propagator of a composite is the product of the two carriers' uncoupled
propagators. -/
theorem idxFreeU_composite (hA : A₀.IsHermitian) (hC : C₀.IsHermitian) (t : ℝ) :
    idxFreeU (compositeH_isHermitian hA hC) t = kronU (idxFreeU hA t) (idxFreeU hC t) := by
  apply Subtype.ext
  have e : (-Complex.I) • compositeH A₀ C₀
      = ((-Complex.I) • A₀) ⊗ₖ (1 : Matrix κ κ ℂ)
        + (1 : Matrix ι ι ℂ) ⊗ₖ ((-Complex.I) • C₀) := by
    rw [compositeH, smul_add, Matrix.smul_kronecker, Matrix.kronecker_smul]
  rw [kronU_val, idxFreeU_val, idxFreeU_val, idxFreeU_val, e, exp_smul_kronecker_add]

/-- ★ **On a fibre where both profiles vanish the composite moves by its uncoupled
propagator**, whatever the two coupled observables are. -/
theorem idxTwoCarrierU_of_lift_eq_zero {ν : Type*} [Fintype ν] [DecidableEq ν]
    {H B₁ B₂ : Matrix ν ν ℂ} (hH : H.IsHermitian) (hB₁ : B₁.IsHermitian)
    (hB₂ : B₂.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    {φ χ : AddCircle (1 : ℝ)} (hφ : hf.lift φ = 0) (hχ : hh.lift χ = 0) (t : ℝ) :
    idxTwoCarrierU hH hB₁ hB₂ hf hh φ χ t = idxFreeU hH t := by
  apply Subtype.ext
  rw [idxTwoCarrierU_val, idxFreeU_val, idxTwoH, hφ, hχ]
  simp

/-- **A gated pointer's lifted displacement from a product ray**, on a fibre where both
profiles vanish: `−2 z` times the accumulated expectation of `G` along the two carriers'
uncoupled orbits, `z` the derivative of the pointer's profile at its conserved angle. -/
noncomputable def coincShift (hA : A₀.IsHermitian) (hC : C₀.IsHermitian)
    (G : Matrix (ι × κ) (ι × κ) ℂ) (z : ℝ) (p : GenArena ι) (q : GenArena κ) (t : ℝ) : ℝ :=
  -2 * z * ∫ s in (0 : ℝ)..t,
    arenaObs G (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q))

/-- **The joint flow of a composite carrier with two pointers**, coupled to the observables
`G₁` and `G₂` of the composite: the flow, for the form of `ℂℙ^N × T² × T²`, of
`−2⟨A₀ ⊗ 1 + 1 ⊗ C₀⟩ − 2 f(θ₂)⟨G₁⟩ − 2 h(ψ₂)⟨G₂⟩`. -/
noncomputable def coincFlow (A₀ : Matrix ι ι ℂ) (C₀ : Matrix κ κ ℂ)
    (G₁ G₂ : Matrix (ι × κ) (ι × κ) ℂ) (hf : Function.Periodic f 1)
    (hh : Function.Periodic h 1) (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (t : ℝ) :
    EchoSigma (a * (b + 1) + b) → EchoSigma (a * (b + 1) + b) :=
  twoCoupledFlow
    (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) (compositeH A₀ C₀))
    (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) G₁)
    (Matrix.reindex (prodIdx e₁ e₂) (prodIdx e₁ e₂) G₂) hf hh hc hch t

/-- The orbit of a product ray under the composite's uncoupled propagator is the product of
the two carriers' orbits. -/
theorem arenaKick_idxFreeU_composite (hA : A₀.IsHermitian) (hC : C₀.IsHermitian) (t : ℝ)
    (p : GenArena ι) (q : GenArena κ) :
    arenaKick (idxFreeU (compositeH_isHermitian hA hC) t) (prodRay p q)
      = prodRay (arenaKick (idxFreeU hA t) p) (arenaKick (idxFreeU hC t) q) := by
  rw [idxFreeU_composite, arenaKick_kronU]

/-- ★★ **The flow from a product ray, on a fibre where both profiles vanish.** The carrier
stays a product ray, each carrier moving by its own uncoupled propagator, and each pointer
advances by `coincShift` of its observable. -/
theorem coincFlow_prodRay (hA : A₀.IsHermitian) (hC : C₀.IsHermitian) (hG₁ : G₁.IsHermitian)
    (hG₂ : G₂.IsHermitian) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
    (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h) (t : ℝ) (p : GenArena ι) (q : GenArena κ)
    {θ ψ : KTorus} (hθ : hf.lift θ.2 = 0) (hψ : hh.lift ψ.2 = 0) :
    coincFlow e₁ e₂ A₀ C₀ G₁ G₂ hf hh hc hch t
        ((idxArenaEquiv (prodIdx e₁ e₂) (prodRay p q), θ), ψ)
      = ((idxArenaEquiv (prodIdx e₁ e₂)
            (prodRay (arenaKick (idxFreeU hA t) p) (arenaKick (idxFreeU hC t) q)),
          (θ.1 + ((coincShift hA hC G₁ (hf.deriv_periodic.lift θ.2) p q t : ℝ)
            : AddCircle (1 : ℝ)), θ.2)),
         (ψ.1 + ((coincShift hA hC G₂ (hh.deriv_periodic.lift ψ.2) p q t : ℝ)
            : AddCircle (1 : ℝ)), ψ.2)) := by
  have key : ∀ s, arenaKick (idxFreeU (compositeH_isHermitian hA hC) s) (prodRay p q)
      = prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q) :=
    fun s => arenaKick_idxFreeU_composite hA hC s p q
  rw [coincFlow, twoCoupledFlow_reindex (prodIdx e₁ e₂) (compositeH_isHermitian hA hC) hG₁ hG₂
    hf hh hc hch t (prodRay p q) θ ψ, idxTwoShiftFst_eq, idxTwoShiftSnd_eq]
  simp only [idxTwoCarrierU_of_lift_eq_zero (compositeH_isHermitian hA hC) hG₁ hG₂ hf hh hθ hψ,
    key, coincShift]

/-- The expectation of an observable of the composite along the uncoupled orbit of a product
ray is continuous in the flow parameter. -/
theorem continuous_arenaObs_prodRay_free (hA : A₀.IsHermitian) (hC : C₀.IsHermitian)
    (G : Matrix (ι × κ) (ι × κ) ℂ) (p : GenArena ι) (q : GenArena κ) :
    Continuous fun s : ℝ =>
      arenaObs G (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)) := by
  have h := continuous_arenaObs_idxFreeU (compositeH_isHermitian hA hC) G (prodRay p q)
  have key : (fun s : ℝ =>
        arenaObs G (prodRay (arenaKick (idxFreeU hA s) p) (arenaKick (idxFreeU hC s) q)))
      = fun s : ℝ =>
        arenaObs G (arenaKick (idxFreeU (compositeH_isHermitian hA hC) s) (prodRay p q)) :=
    funext fun s => by rw [arenaKick_idxFreeU_composite hA hC s p q]
  rw [key]
  exact h

/-- ★ **Displacements add over the observables**, at one profile derivative. -/
theorem coincShift_add (hA : A₀.IsHermitian) (hC : C₀.IsHermitian)
    (G G' : Matrix (ι × κ) (ι × κ) ℂ) (z : ℝ) (p : GenArena ι) (q : GenArena κ) (t : ℝ) :
    coincShift hA hC (G + G') z p q t
      = coincShift hA hC G z p q t + coincShift hA hC G' z p q t := by
  simp only [coincShift, arenaObs_add]
  rw [intervalIntegral.integral_add
    ((continuous_arenaObs_prodRay_free hA hC G p q).intervalIntegrable _ _)
    ((continuous_arenaObs_prodRay_free hA hC G' p q).intervalIntegrable _ _)]
  ring

/-- An observable of the second carrier alone: its displacement is the second carrier's
uncoupled accumulated reading. -/
theorem coincShift_one_kronecker (hA : A₀.IsHermitian) (hC : C₀.IsHermitian)
    (Y : Matrix κ κ ℂ) (z : ℝ) (p : GenArena ι) (q : GenArena κ) (t : ℝ) :
    coincShift hA hC ((1 : Matrix ι ι ℂ) ⊗ₖ Y) z p q t
      = -2 * z * ∫ s in (0 : ℝ)..t, arenaObs Y (arenaKick (idxFreeU hC s) q) := by
  simp only [coincShift, arenaObs_one_kronecker]

end PairFlow

/-! ### The two gates of one observer: together, and apart -/

section Gates

variable {ι κ S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype S]
  [DecidableEq S] (σ : ι → S) (τ : κ → S) (r : S → S → Prop) [DecidableRel r]
  {A₀ : Matrix ι ι ℂ} {C₀ : Matrix κ κ ℂ}

omit [Fintype S] [DecidableEq S] in
/-- ★ **A gate and its complement make the ungated operator**:
`gateOp r Y + gateOp (¬r) Y = 1 ⊗ Y`. -/
theorem gateOp_add_gateOp_not (Y : Matrix κ κ ℂ) :
    gateOp σ τ r Y + gateOp σ τ (fun s s' => ¬ r s s') Y = (1 : Matrix ι ι ℂ) ⊗ₖ Y := by
  rw [gateOp, gateOp, ← one_sub_coincProj, ← add_mul, add_sub_cancel, one_mul]

/-- ★★ **The gated displacement, site by site.** On a fibre where both profiles vanish, from
a product ray, the pointer coupled to `gateOp r Y` advances by `−2 z` times the accumulated
sum over related pairs of sites of the first carrier's occupancy of its site times the
second carrier's `arenaObs (siteSel τ s' * Y)`. -/
theorem coincShift_gateOp (hA : A₀.IsHermitian) (hC : C₀.IsHermitian) (Y : Matrix κ κ ℂ)
    (z : ℝ) (p : GenArena ι) (q : GenArena κ) (t : ℝ) :
    coincShift hA hC (gateOp σ τ r Y) z p q t
      = -2 * z * ∫ u in (0 : ℝ)..t, ∑ s, ∑ s', if r s s'
          then arenaObs (siteSel σ s) (arenaKick (idxFreeU hA u) p)
            * arenaObs (siteSel τ s' * Y) (arenaKick (idxFreeU hC u) q) else 0 := by
  simp only [coincShift, arenaObs_gateOp_prodRay]

omit [Fintype S] [DecidableEq S] in
/-- ★★★ **The displacement while together plus the displacement while apart is the ungated
clock pointer's displacement.** For two pointers with the same profile derivative `z`, one
coupled to `gateOp r Y` and one to its complement, from a product ray on a fibre where both
profiles vanish: the two displacements add up to `−2 z` times the second carrier's uncoupled
accumulated reading of `Y`, at every flow time. -/
theorem coincShift_gateOp_add_not (hA : A₀.IsHermitian) (hC : C₀.IsHermitian)
    (Y : Matrix κ κ ℂ) (z : ℝ) (p : GenArena ι) (q : GenArena κ) (t : ℝ) :
    coincShift hA hC (gateOp σ τ r Y) z p q t
        + coincShift hA hC (gateOp σ τ (fun s s' => ¬ r s s') Y) z p q t
      = -2 * z * ∫ s in (0 : ℝ)..t, arenaObs Y (arenaKick (idxFreeU hC s) q) := by
  rw [← coincShift_add, gateOp_add_gateOp_not, coincShift_one_kronecker]

end Gates

end CSD.RecordLayer

end
