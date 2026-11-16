/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedPentaRun

/-!
# The five-pointer run on any fibre

**Category:** 7-SigmaLayer (the record layer). BACKLOG #428 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Task 9 of the research delivery
plan of 2026-11-16 (an open set of pointer angles), second part. No new assumption beyond
UA-18.

`pentaRun_eq` (#404) solves the five-pointer flow on the fibres where the five profiles
vanish: there the carrier moves freely. This module solves it on **every** fibre. The second
angle of each pointer is conserved, so the five profile values are constants of the motion,
and the carrier moves by the free flow of one constant matrix,

`H_θ = H + r(ζ₂) G₅ + l(ξ₂) G₄ + k(χ₂) G₃ + f(θ₂) G₁ + g(ψ₂) G₂`,

while pointer `i` is turned by its profile's derivative at its own conserved angle times the
accumulated `−2⟨G_i⟩` along that orbit.

* `freeTurn_congr` — the turning depends on the matrix only;
* `twoCoupledFlow_fibre`, `threeCoupledFlow_fibre`, `fourCoupledFlow_fibre`,
  ★★ `fiveCoupledFlow_fibre` — the flows on any fibre;
* `fibreH`, `fibreH_reindex` — the constant matrix, and its reindexing;
* ★★★ `pentaRun_fibre` — the five-pointer run of a carrier with any index type, on any
  fibre: the carrier at `arenaKick (idxFreeU H_θ t) p` and pointer `i` at
  `pshift (freeShift H_θ G_i z_i p t)` of its start.

## Exact scope

* **An exact solution of the flow**, not an estimate. All five observables Hermitian.
* **Nothing is said about how close `H_θ` is to `H`**, nor about histories or counts.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-168, UD-196, UD-197, UD-198); `RecordLayer/UnifiedPentaRun.lean` (#404:
`pentaRun_eq`, `freeTurn`, `freeShift`, `freeTurn_reindex`, `idxArenaEquiv_kick_free`);
`LF4/PentaCoupledFlow.lean` (`fiveCoupledFlow_apply`); `LF4/QuadCoupledFlow.lean`
(`fourCoupledFlow_apply`); `LF4/TriCoupledFlow.lean` (`threeCoupledFlow_apply`);
`LF4/EchoVolume.lean` (`twoCoupledFlow_apply`, `schrodingerUnitary_congr`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

section Fibre

variable {N : ℕ} {f g k l r : ℝ → ℝ} {A BA BB BC BD BE : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}

/-- The turning along the uncoupled orbit depends on the matrix only. -/
theorem freeTurn_congr {A A' : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} (h : A = A')
    (hA : A.IsHermitian) (hA' : A'.IsHermitian) (B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (z : ℝ) (x : CPN (N + 1)) (t : ℝ) : freeTurn hA B z x t = freeTurn hA' B z x t := by
  subst h
  rfl

/-- **The two-pointer flow on any fibre.** -/
theorem twoCoupledFlow_fibre (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (x : CPN (N + 1)) (θ ψ : KTorus) (t : ℝ) :
    twoCoupledFlow A BA BB hf hg hc hcg t ((x, θ), ψ)
      = ((Matrix.schrodingerUnitary
            (twoCoupledMatrix_isHermitian hA hBA hBB hf hg θ.2 ψ.2) t • x,
          pshift (freeTurn (twoCoupledMatrix_isHermitian hA hBA hBB hf hg θ.2 ψ.2) BA
            (hf.deriv_periodic.lift θ.2) x t) θ),
         pshift (freeTurn (twoCoupledMatrix_isHermitian hA hBA hBB hf hg θ.2 ψ.2) BB
            (hg.deriv_periodic.lift ψ.2) x t) ψ) := by
  rw [twoCoupledFlow_apply hA hBA hBB hf hg hc hcg]
  rfl

/-- **The three-pointer flow on any fibre.** -/
theorem threeCoupledFlow_fibre (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hBC : BC.IsHermitian) (hf : Function.Periodic f 1)
    (hg : Function.Periodic g 1) (hk : Function.Periodic k 1) (hc : ContDiff ℝ ∞ f)
    (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k) (x : CPN (N + 1)) (θ ψ χ : KTorus)
    (t : ℝ) :
    threeCoupledFlow A BA BB BC hf hg hk hc hcg hck t (((x, θ), ψ), χ)
      = (((Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian
              (isHermitian_add_real_smul hA hBC (hk.lift χ.2)) hBA hBB hf hg θ.2 ψ.2) t • x,
            pshift (freeTurn (twoCoupledMatrix_isHermitian
              (isHermitian_add_real_smul hA hBC (hk.lift χ.2)) hBA hBB hf hg θ.2 ψ.2) BA
              (hf.deriv_periodic.lift θ.2) x t) θ),
          pshift (freeTurn (twoCoupledMatrix_isHermitian
            (isHermitian_add_real_smul hA hBC (hk.lift χ.2)) hBA hBB hf hg θ.2 ψ.2) BB
            (hg.deriv_periodic.lift ψ.2) x t) ψ),
         pshift (freeTurn (twoCoupledMatrix_isHermitian
            (isHermitian_add_real_smul hA hBC (hk.lift χ.2)) hBA hBB hf hg θ.2 ψ.2) BC
            (hk.deriv_periodic.lift χ.2) x t) χ) := by
  rw [threeCoupledFlow_apply]
  simp only [twoCoupledFlow_fibre (isHermitian_add_real_smul hA hBC (hk.lift χ.2)) hBA hBB hf
    hg hc hcg x θ ψ]
  rfl

/-- **The four-pointer flow on any fibre.** -/
theorem fourCoupledFlow_fibre (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hBC : BC.IsHermitian) (hBD : BD.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (hk : Function.Periodic k 1)
    (hl : Function.Periodic l 1) (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g)
    (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l) (x : CPN (N + 1)) (θ ψ χ ξ : KTorus)
    (t : ℝ) :
    fourCoupledFlow A BA BB BC BD hf hg hk hl hc hcg hck hcl t ((((x, θ), ψ), χ), ξ)
      = ((((Matrix.schrodingerUnitary (twoCoupledMatrix_isHermitian
                (isHermitian_add_real_smul (isHermitian_add_real_smul hA hBD (hl.lift ξ.2))
                  hBC (hk.lift χ.2)) hBA hBB hf hg θ.2 ψ.2) t • x,
              pshift (freeTurn (twoCoupledMatrix_isHermitian
                (isHermitian_add_real_smul (isHermitian_add_real_smul hA hBD (hl.lift ξ.2))
                  hBC (hk.lift χ.2)) hBA hBB hf hg θ.2 ψ.2) BA
                (hf.deriv_periodic.lift θ.2) x t) θ),
            pshift (freeTurn (twoCoupledMatrix_isHermitian
              (isHermitian_add_real_smul (isHermitian_add_real_smul hA hBD (hl.lift ξ.2))
                hBC (hk.lift χ.2)) hBA hBB hf hg θ.2 ψ.2) BB
              (hg.deriv_periodic.lift ψ.2) x t) ψ),
           pshift (freeTurn (twoCoupledMatrix_isHermitian
            (isHermitian_add_real_smul (isHermitian_add_real_smul hA hBD (hl.lift ξ.2))
              hBC (hk.lift χ.2)) hBA hBB hf hg θ.2 ψ.2) BC
            (hk.deriv_periodic.lift χ.2) x t) χ),
         pshift (freeTurn (twoCoupledMatrix_isHermitian
            (isHermitian_add_real_smul (isHermitian_add_real_smul hA hBD (hl.lift ξ.2))
              hBC (hk.lift χ.2)) hBA hBB hf hg θ.2 ψ.2) BD
            (hl.deriv_periodic.lift ξ.2) x t) ξ) := by
  rw [fourCoupledFlow_apply]
  simp only [triRayEnergy, echoRayEnergy,
    threeCoupledFlow_fibre (isHermitian_add_real_smul hA hBD (hl.lift ξ.2)) hBA hBB hBC hf hg
      hk hc hcg hck x θ ψ χ]
  rfl

/-- ★★ **The five-pointer flow on any fibre.** The ray moves by the Schrödinger unitary of
the constant matrix `A + r(ζ₂) B_E + l(ξ₂) B_D + k(χ₂) B_C + f(θ₂) B_A + g(ψ₂) B_B`, and each
pointer is turned by its profile's derivative times the accumulated `−2⟨B⟩` of its own
observable along that orbit. -/
theorem fiveCoupledFlow_fibre (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hBC : BC.IsHermitian) (hBD : BD.IsHermitian)
    (hBE : BE.IsHermitian) (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hr : Function.Periodic r 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k)
    (hcl : ContDiff ℝ ∞ l) (hcr : ContDiff ℝ ∞ r) (x : CPN (N + 1)) (θ ψ χ ξ ζ : KTorus)
    {M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} (hM : M.IsHermitian)
    (hMe : twoCoupledMatrix (A + ((hr.lift ζ.2 : ℝ) : ℂ) • BE + ((hl.lift ξ.2 : ℝ) : ℂ) • BD
      + ((hk.lift χ.2 : ℝ) : ℂ) • BC) BA BB hf hg θ.2 ψ.2 = M) (t : ℝ) :
    fiveCoupledFlow A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr t
        (((((x, θ), ψ), χ), ξ), ζ)
      = (((((Matrix.schrodingerUnitary hM t • x,
                pshift (freeTurn hM BA (hf.deriv_periodic.lift θ.2) x t) θ),
              pshift (freeTurn hM BB (hg.deriv_periodic.lift ψ.2) x t) ψ),
             pshift (freeTurn hM BC (hk.deriv_periodic.lift χ.2) x t) χ),
            pshift (freeTurn hM BD (hl.deriv_periodic.lift ξ.2) x t) ξ),
         pshift (freeTurn hM BE (hr.deriv_periodic.lift ζ.2) x t) ζ) := by
  subst hMe
  rw [fiveCoupledFlow_apply]
  simp only [quadRayEnergy, triRayEnergy, echoRayEnergy,
    fourCoupledFlow_fibre (isHermitian_add_real_smul hA hBE (hr.lift ζ.2)) hBA hBB hBC hBD hf
      hg hk hl hc hcg hck hcl x θ ψ χ ξ]
  rfl

end Fibre

/-! ### A carrier with any index type -/

section Indexed

variable {ν : Type*} [Fintype ν] [DecidableEq ν] {N : ℕ} (e : ν ≃ Fin (N + 1))
  {H G₁ G₂ G₃ G₄ G₅ : Matrix ν ν ℂ} {f g k l r : ℝ → ℝ}

/-- **The carrier's matrix on a fibre**: the uncoupled matrix plus the five observables with
the five conserved profile values. -/
def fibreH (H G₁ G₂ G₃ G₄ G₅ : Matrix ν ν ℂ) (a b c d w : ℝ) : Matrix ν ν ℂ :=
  H + (w : ℂ) • G₅ + (d : ℂ) • G₄ + (c : ℂ) • G₃ + (a : ℂ) • G₁ + (b : ℂ) • G₂

omit [Fintype ν] [DecidableEq ν] in
/-- The reindexed matrix on a fibre is the two-pointer matrix of the reindexed data. -/
theorem fibreH_reindex (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hr : Function.Periodic r 1)
    (θ ψ χ ξ ζ : AddCircle (1 : ℝ)) :
    twoCoupledMatrix (Matrix.reindex e e H + ((hr.lift ζ : ℝ) : ℂ) • Matrix.reindex e e G₅
        + ((hl.lift ξ : ℝ) : ℂ) • Matrix.reindex e e G₄
        + ((hk.lift χ : ℝ) : ℂ) • Matrix.reindex e e G₃) (Matrix.reindex e e G₁)
        (Matrix.reindex e e G₂) hf hg θ ψ
      = Matrix.reindex e e (fibreH H G₁ G₂ G₃ G₄ G₅ (hf.lift θ) (hg.lift ψ) (hk.lift χ)
          (hl.lift ξ) (hr.lift ζ)) := by
  simp [twoCoupledMatrix, coupledMatrix, fibreH, Matrix.submatrix_add, Matrix.submatrix_smul]

/-- ★★★ **The five-pointer run of a carrier, on any fibre.** The flow of the five-pointer
arena of UA-18 for a carrier with any index type and five Hermitian observables, from any
ray and any pointer angles: the carrier moves by the free propagator of the constant matrix
`fibreH` of the five conserved profile values, and pointer `i` is at
`pshift (freeShift G_i z_i p t)` of its start along that orbit. -/
theorem pentaRun_fibre (hH : H.IsHermitian) (hG₁ : G₁.IsHermitian) (hG₂ : G₂.IsHermitian)
    (hG₃ : G₃.IsHermitian) (hG₄ : G₄.IsHermitian) (hG₅ : G₅.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (hk : Function.Periodic k 1)
    (hl : Function.Periodic l 1) (hr : Function.Periodic r 1) (hc : ContDiff ℝ ∞ f)
    (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l)
    (hcr : ContDiff ℝ ∞ r) (p : GenArena ν) (θ ψ χ ξ ζ : KTorus)
    (hF : (fibreH H G₁ G₂ G₃ G₄ G₅ (hf.lift θ.2) (hg.lift ψ.2) (hk.lift χ.2) (hl.lift ξ.2)
      (hr.lift ζ.2)).IsHermitian) (t : ℝ) :
    fiveCoupledFlow (Matrix.reindex e e H) (Matrix.reindex e e G₁) (Matrix.reindex e e G₂)
        (Matrix.reindex e e G₃) (Matrix.reindex e e G₄) (Matrix.reindex e e G₅)
        hf hg hk hl hr hc hcg hck hcl hcr t (((((idxArenaEquiv e p, θ), ψ), χ), ξ), ζ)
      = (((((idxArenaEquiv e (arenaKick (idxFreeU hF t) p),
                pshift (freeShift hF G₁ (hf.deriv_periodic.lift θ.2) p t) θ),
              pshift (freeShift hF G₂ (hg.deriv_periodic.lift ψ.2) p t) ψ),
             pshift (freeShift hF G₃ (hk.deriv_periodic.lift χ.2) p t) χ),
            pshift (freeShift hF G₄ (hl.deriv_periodic.lift ξ.2) p t) ξ),
         pshift (freeShift hF G₅ (hr.deriv_periodic.lift ζ.2) p t) ζ) := by
  rw [fiveCoupledFlow_fibre (hH.reindex e) (hG₁.reindex e) (hG₂.reindex e) (hG₃.reindex e)
    (hG₄.reindex e) (hG₅.reindex e) hf hg hk hl hr hc hcg hck hcl hcr _ θ ψ χ ξ ζ
    (hF.reindex e) (fibreH_reindex e hf hg hk hl hr θ.2 ψ.2 χ.2 ξ.2 ζ.2)]
  rw [freeTurn_reindex e hF G₁, freeTurn_reindex e hF G₂, freeTurn_reindex e hF G₃,
    freeTurn_reindex e hF G₄, freeTurn_reindex e hF G₅, idxArenaEquiv_kick_free e hF]

end Indexed

end CSD.RecordLayer

end
