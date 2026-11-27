/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.ReleasedFlow
public import CsdLean4.RecordLayer.UnifiedPentaRun

/-!
# A return carrier released by a pointer: the composite's flow

**Category:** 7-SigmaLayer (the record layer). BACKLOG #437 (obligation UO-26, the mechanism
of UA-22; link L2 of the skeleton, `specs/unified-record-spacetime-plan.md` §9.4; route (β1)
of the task plans).

`LF4/ReleasedFlow.lean` solves the flow of `−2⟨A⟩ − 2 f(θ₂)⟨B⟩ + c b(θ₁)(−2⟨C⟩)` where
`⟨C⟩ = 0`, for three matrices on `Fin (N + 1)` with `C` commuting with the other two. Here
it is read on a carrier with any index, and then on a composite of two carriers:

* the **earlier carriers**, index `ι`, with the Hamiltonian `H_a` and the observable `P`
  that the pointer reads;
* a **return carrier**, index `κ`, that no other term acts on: `A = H_a ⊗ 1`,
  `B = P ⊗ 1`, `C = 1 ⊗ K`.

From a product ray whose return carrier has `⟨K⟩ = 0` the flow keeps the ray a product. The
earlier carriers and the pointer run exactly as they do with no return carrier at all. The
return carrier is moved by `exp(−iκ(t)K)` with the clock `κ(t) = c ∫₀ᵗ b(θ₁(u)) du`: it is
at rest while the pointer's window is shut and free, with its whole weight, while it is
open.

* `reindex_mul_comm`, ★★ `hamiltonianFlow_released_reindex` — the flow in the carrier's own
  coordinates;
* `idxFreeU_one_kronecker`, `idxCarrierU_kronecker_one`, `arenaKick_one`,
  `arenaKick_idxFreeU_one_kronecker_prodRay`, `arenaKick_idxCarrierU_kronecker_one_prodRay`,
  `idxPointerShift_kronecker_one`;
* ★★★ `hamiltonianFlow_released_composite` — **the composite's flow from a product ray**.

## Honest scope

⚠️ **Only where the return carrier has `⟨K⟩ = 0`**, and only from a product ray. For a
return carrier with Hamiltonian `H_R` take `K = H_R − Ē` with `Ē` its mean energy; that
choice is the preparation's (UA-22, risk (v)). Nothing is given for other rays.

⚠️ **The constant `c`** stands for the next pointer's profile at its conserved angle
(UA-20). The step that adds that pointer is not composed here, so this is the base's flow
of `hamiltonianFlow_controlledEnergy` and not a flow of the full arena.

⚠️ **No record is read.** That the pointer turns into the window, and when, is not shown;
no detector reads the return carrier; no packet is put in.

⚠️ **Flow times.**

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-20, UA-22,
UO-24, UO-26, UD-271, UD-272; §9.4); `specs/unified-records-spacetime-task-plans.md` (§9,
route (β1)); `LF4/ReleasedFlow.lean` (`hamiltonianFlow_released`, `releasedCurve`);
`RecordLayer/UnifiedDiracClock.lean` (`idxCarrierU`, `idxFreeU`, `idxPointerShift`,
`hamiltonianFlow_coupledEnergy_reindex`, `idxArenaEquiv_kick`);
`RecordLayer/UnifiedPentaRun.lean` (`idxArenaEquiv_kick_free`); `CV/ProductRay.lean`
(`prodRay`, `kronU`, `arenaKick_kronU`, `arenaObs_one_kronecker`, `exp_smul_one_kronecker`);
`specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### The flow in the carrier's own coordinates -/

section Indexed

variable {ν : Type*} [Fintype ν] [DecidableEq ν] {N : ℕ} (e : ν ≃ Fin (N + 1))
  {A₀ B₀ C₀ : Matrix ν ν ℂ} {f b : ℝ → ℝ}

omit [DecidableEq ν] in
/-- Reindexing keeps a commutation. -/
theorem reindex_mul_comm (h : C₀ * A₀ = A₀ * C₀) :
    Matrix.reindex e e C₀ * Matrix.reindex e e A₀
      = Matrix.reindex e e A₀ * Matrix.reindex e e C₀ := by
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, h]

/-- ★★ **The flow with a released term, in the carrier's coordinates.** `C₀` commutes with
`A₀` and `B₀`, and `⟨C₀⟩ = 0` at the ray `p`. The flow of
`−2⟨A₀⟩ − 2 f(θ₂)⟨B₀⟩ + c b(θ₁)(−2⟨C₀⟩)` moves the carrier by `exp(−iκ(t)C₀)` and then by
`exp(−it(A₀ + f(θ₂) B₀))`, with `κ(t) = c ∫₀ᵗ b(θ₁(u)) du`; `θ₁` advances by the pointer's
displacement without the term; `θ₂` is fixed. -/
theorem hamiltonianFlow_released_reindex (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hC : C₀.IsHermitian) (hCA : C₀ * A₀ = A₀ * C₀) (hCB : C₀ * B₀ = B₀ * C₀)
    (hf : Function.Periodic f 1) (hb : Function.Periodic b 1) (hc : ContDiff ℝ ∞ f)
    (hcb : ContDiff ℝ ∞ b) (c : ℝ) {p : GenArena ν} (hp : arenaObs C₀ p = 0) (a₀ : ℝ)
    (φ : AddCircle (1 : ℝ)) (t : ℝ) :
    (arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_add_const_smul
          (contMDiff_coupledEnergy (Matrix.reindex e e A₀) (Matrix.reindex e e B₀) hf hc)
          (contMDiff_controlObs (Matrix.reindex e e C₀) hb hcb) c) t
        (idxArenaEquiv e p, ((a₀ : AddCircle (1 : ℝ)), φ))
      = (idxArenaEquiv e (arenaKick (idxCarrierU hA hB hf φ t)
            (arenaKick (idxFreeU hC
              (c * ∫ u in (0 : ℝ)..t, b (a₀ + idxPointerShift hA hB hf φ p u))) p)),
          (((a₀ + idxPointerShift hA hB hf φ p t : ℝ) : AddCircle (1 : ℝ)), φ)) := by
  have hx : schrodingerHamiltonian (Matrix.reindex e e C₀) (idxArenaEquiv e p) = 0 := by
    rw [schrodingerHamiltonian_reindex, hp, mul_zero]
  have hang : ∀ u : ℝ,
      releasedAngle (hA.reindex e) (hB.reindex e) hf (idxArenaEquiv e p) a₀ φ u
        = a₀ + idxPointerShift hA hB hf φ p u := fun u => by
    unfold releasedAngle
    rw [idxPointerShift_eq]
  rw [hamiltonianFlow_released (hA.reindex e) (hB.reindex e) (hC.reindex e)
    (reindex_mul_comm e hCA) (reindex_mul_comm e hCB) hf hb hc hcb c hx a₀ φ t]
  unfold releasedCurve releasedClock
  simp only [hang]
  rw [mul_smul, ← idxArenaEquiv_kick_free e hC, ← idxArenaEquiv_kick e hA hB hf]

end Indexed

/-! ### The earlier carriers and a return carrier -/

section Composite

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {Ha P : Matrix ι ι ℂ} {K : Matrix κ κ ℂ} {f b : ℝ → ℝ}

/-- The propagator of a second-carrier Hamiltonian acts on the second carrier only. -/
theorem idxFreeU_one_kronecker (hK : K.IsHermitian) (t : ℝ) :
    idxFreeU (kronecker_isHermitian (Matrix.isHermitian_one : (1 : Matrix ι ι ℂ).IsHermitian)
        hK) t
      = kronU (1 : Matrix.unitaryGroup ι ℂ) (idxFreeU hK t) := by
  apply Subtype.ext
  rw [idxFreeU_val, ← Matrix.kronecker_smul, exp_smul_one_kronecker, kronU_val, idxFreeU_val]
  rfl

/-- The propagator of first-carrier matrices acts on the first carrier only. -/
theorem idxCarrierU_kronecker_one (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ)) (t : ℝ) :
    idxCarrierU
        (kronecker_isHermitian hHa (Matrix.isHermitian_one : (1 : Matrix κ κ ℂ).IsHermitian))
        (kronecker_isHermitian hP (Matrix.isHermitian_one : (1 : Matrix κ κ ℂ).IsHermitian))
        hf φ t
      = kronU (idxCarrierU hHa hP hf φ t) (1 : Matrix.unitaryGroup κ ℂ) := by
  have eH : idxCoupledH (Ha ⊗ₖ (1 : Matrix κ κ ℂ)) (P ⊗ₖ (1 : Matrix κ κ ℂ)) hf φ
      = idxCoupledH Ha P hf φ ⊗ₖ (1 : Matrix κ κ ℂ) := by
    unfold idxCoupledH
    rw [Matrix.add_kronecker, Matrix.smul_kronecker]
  apply Subtype.ext
  rw [idxCarrierU_val, eH, ← Matrix.smul_kronecker, exp_smul_kronecker_one, kronU_val,
    idxCarrierU_val]
  rfl

/-- The identity leaves a ray where it is. -/
theorem arenaKick_one (p : GenArena ι) : arenaKick (1 : Matrix.unitaryGroup ι ℂ) p = p := by
  rw [arenaKick_eq_smul', one_smul]

/-- A second-carrier propagator on a product ray moves the second ray only. -/
theorem arenaKick_idxFreeU_one_kronecker_prodRay (hK : K.IsHermitian) (t : ℝ)
    (pa : GenArena ι) (r : GenArena κ) :
    arenaKick (idxFreeU (kronecker_isHermitian
        (Matrix.isHermitian_one : (1 : Matrix ι ι ℂ).IsHermitian) hK) t) (prodRay pa r)
      = prodRay pa (arenaKick (idxFreeU hK t) r) := by
  rw [idxFreeU_one_kronecker, arenaKick_kronU, arenaKick_one]

/-- A first-carrier propagator on a product ray moves the first ray only. -/
theorem arenaKick_idxCarrierU_kronecker_one_prodRay (hHa : Ha.IsHermitian)
    (hP : P.IsHermitian) (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ)) (t : ℝ)
    (pa : GenArena ι) (r : GenArena κ) :
    arenaKick (idxCarrierU
        (kronecker_isHermitian hHa (Matrix.isHermitian_one : (1 : Matrix κ κ ℂ).IsHermitian))
        (kronecker_isHermitian hP (Matrix.isHermitian_one : (1 : Matrix κ κ ℂ).IsHermitian))
        hf φ t) (prodRay pa r)
      = prodRay (arenaKick (idxCarrierU hHa hP hf φ t) pa) r := by
  rw [idxCarrierU_kronecker_one, arenaKick_kronU, arenaKick_one]

/-- The pointer's displacement does not see the second carrier. -/
theorem idxPointerShift_kronecker_one (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hf : Function.Periodic f 1) (φ : AddCircle (1 : ℝ)) (pa : GenArena ι) (r : GenArena κ)
    (t : ℝ) :
    idxPointerShift
        (kronecker_isHermitian hHa (Matrix.isHermitian_one : (1 : Matrix κ κ ℂ).IsHermitian))
        (kronecker_isHermitian hP (Matrix.isHermitian_one : (1 : Matrix κ κ ℂ).IsHermitian))
        hf φ (prodRay pa r) t
      = idxPointerShift hHa hP hf φ pa t := by
  unfold idxPointerShift
  refine congrArg (fun z : ℝ => -2 * hf.deriv_periodic.lift φ * z)
    (intervalIntegral.integral_congr fun s _ => ?_)
  show arenaObs (P ⊗ₖ (1 : Matrix κ κ ℂ)) (arenaKick (idxCarrierU _ _ hf φ s) (prodRay pa r))
    = arenaObs P (arenaKick (idxCarrierU hHa hP hf φ s) pa)
  rw [arenaKick_idxCarrierU_kronecker_one_prodRay, arenaObs_kronecker_one]

variable {N : ℕ} (e : ι × κ ≃ Fin (N + 1))

/-- ★★★ **The composite's flow with a return carrier released by the pointer.** The earlier
carriers have the Hamiltonian `H_a` and the observable `P` that the pointer reads; the
return carrier has the Hermitian `K`, on which no other term acts, with `⟨K⟩ = 0` at its ray
`r`. For every constant `c`, the flow of

  `−2⟨H_a ⊗ 1⟩ − 2 f(θ₂)⟨P ⊗ 1⟩ + c b(θ₁)(−2⟨1 ⊗ K⟩)`

from the product ray of `pa` and `r` keeps the ray a product: the earlier carriers move by
`exp(−it(H_a + f(θ₂) P))` and the pointer by its displacement, as with no return carrier;
the return carrier moves by `exp(−iκ(t)K)`, `κ(t) = c ∫₀ᵗ b(θ₁(u)) du`. -/
theorem hamiltonianFlow_released_composite (hHa : Ha.IsHermitian) (hP : P.IsHermitian)
    (hK : K.IsHermitian) (hf : Function.Periodic f 1) (hb : Function.Periodic b 1)
    (hc : ContDiff ℝ ∞ f) (hcb : ContDiff ℝ ∞ b) (c : ℝ) (pa : GenArena ι)
    {r : GenArena κ} (hr : arenaObs K r = 0) (a₀ : ℝ) (φ : AddCircle (1 : ℝ)) (t : ℝ) :
    (arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_add_const_smul
          (contMDiff_coupledEnergy (Matrix.reindex e e (Ha ⊗ₖ (1 : Matrix κ κ ℂ)))
            (Matrix.reindex e e (P ⊗ₖ (1 : Matrix κ κ ℂ))) hf hc)
          (contMDiff_controlObs (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ K)) hb hcb) c) t
        (idxArenaEquiv e (prodRay pa r), ((a₀ : AddCircle (1 : ℝ)), φ))
      = (idxArenaEquiv e (prodRay (arenaKick (idxCarrierU hHa hP hf φ t) pa)
            (arenaKick (idxFreeU hK
              (c * ∫ u in (0 : ℝ)..t, b (a₀ + idxPointerShift hHa hP hf φ pa u))) r)),
          (((a₀ + idxPointerShift hHa hP hf φ pa t : ℝ) : AddCircle (1 : ℝ)), φ)) := by
  have hCA : ((1 : Matrix ι ι ℂ) ⊗ₖ K) * (Ha ⊗ₖ (1 : Matrix κ κ ℂ))
      = (Ha ⊗ₖ (1 : Matrix κ κ ℂ)) * ((1 : Matrix ι ι ℂ) ⊗ₖ K) := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, one_mul, mul_one, mul_one,
      one_mul]
  have hCB : ((1 : Matrix ι ι ℂ) ⊗ₖ K) * (P ⊗ₖ (1 : Matrix κ κ ℂ))
      = (P ⊗ₖ (1 : Matrix κ κ ℂ)) * ((1 : Matrix ι ι ℂ) ⊗ₖ K) := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, one_mul, mul_one, mul_one,
      one_mul]
  rw [hamiltonianFlow_released_reindex e
    (kronecker_isHermitian hHa (Matrix.isHermitian_one : (1 : Matrix κ κ ℂ).IsHermitian))
    (kronecker_isHermitian hP (Matrix.isHermitian_one : (1 : Matrix κ κ ℂ).IsHermitian))
    (kronecker_isHermitian (Matrix.isHermitian_one : (1 : Matrix ι ι ℂ).IsHermitian) hK)
    hCA hCB hf hb hc hcb c (by rw [arenaObs_one_kronecker]; exact hr) a₀ φ t]
  have hsh : ∀ u : ℝ, idxPointerShift
      (kronecker_isHermitian hHa (Matrix.isHermitian_one : (1 : Matrix κ κ ℂ).IsHermitian))
      (kronecker_isHermitian hP (Matrix.isHermitian_one : (1 : Matrix κ κ ℂ).IsHermitian))
      hf φ (prodRay pa r) u = idxPointerShift hHa hP hf φ pa u := fun u =>
    idxPointerShift_kronecker_one hHa hP hf φ pa r u
  simp only [hsh]
  rw [arenaKick_idxFreeU_one_kronecker_prodRay hK,
    arenaKick_idxCarrierU_kronecker_one_prodRay hHa hP]

end Composite

end CSD.RecordLayer

end
