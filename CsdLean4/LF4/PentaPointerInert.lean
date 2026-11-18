/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.PentaCoupledFlow

/-!
# The five-pointer flow does not see where its pointers are

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 3-Local (the Kähler arena). BACKLOG #440, first brick (Task 5 of the author's plan
"Unified records, quantum measurement and emergent spacetime" of 2026-11-18, workstream R;
obligation UO-25, item (5); the obstruction of UO-24 on the arena of UA-18).

`LF4/PointerInert.lean` (#374) shows that a step's flow commutes with turning the pointer the
step adds. On the five-pointer arena of UA-18 that covers the fifth pointer only. Here it is
shown for all five at once, by the skew-product formulas of the four levels.

* `isHermitian_add_ofReal_smul`; `shiftEcho`, `shiftTri`, `shiftQuad`, `shiftPenta` (turn the
  pointers' moving angles, leaving the ray and the conserved angles);
* `twoCoupledFlow_shiftEcho`, `threeCoupledFlow_shiftTri`, `fourCoupledFlow_shiftQuad`;
* ★★★ `fiveCoupledFlow_shiftPenta` — **the five-pointer flow commutes with turning the
  pointers**;
* ★★ `fiveCoupledFlow_shiftPenta_snd` (the fifth pointer's angles at every time do not depend
  on where the other four started), ★★ `fiveCoupledFlow_shiftPenta_ray` (nor does the ray).

## What it means for a record that is to control an apparatus

A record on this arena is a pointer's moving angle having crossed its arcs. By
`fiveCoupledFlow_shiftPenta` the carriers, the conserved angles and every other pointer evolve
the same whatever that angle is. So no second apparatus on the arena of UA-18 can depend on
a record held by a pointer: the first record cannot control a later interaction. This is an
obstruction, for the couplings admitted by UA-18 (c). It is not a statement about
apparatus in general.

## Honest scope

⚠️ **For this arena and these couplings.** The energy contains no moving angle (UA-13 (c));
that is the hypothesis in all but name. A pointer whose moving angle acts back (UO-24) is
not covered and is not built.

⚠️ **Correlation is not excluded.** Two pointers gated by the same carrier are correlated
through the carrier. The theorem says neither depends on the other's angle, not that their
counts are independent.

⚠️ **Hermitian matrices** are assumed (the two-pointer formula is stated for them).

References: `specs/BACKLOG.md` #440, ~~#374~~;
`specs/unified-record-spacetime-plan.md` (UA-13, UA-18, UO-24, UO-25, UD-106, UD-107,
UD-139, UD-227); `specs/unified-records-spacetime-task-plans.md` (§3);
`LF4/PointerInert.lean` (`hamiltonianFlow_stepEnergy_shiftMoving`);
`LF4/PentaCoupledFlow.lean` (`fiveCoupledFlow_apply`); `LF4/EchoVolume.lean`
(`twoCoupledFlow_apply`); `RecordLayer/UnifiedRecordInert.lean`
(`clockMessengerFlow_shiftPointers`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open Projectivization DifferentialForm MeasureTheory
open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix.Norms.L2Operator

namespace CSD
namespace LF4

variable {N : ℕ} {f g k l r : ℝ → ℝ}
  {A BA BB BC BD BE : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}

/-- A Hermitian matrix plus a real multiple of a Hermitian matrix is Hermitian. -/
theorem isHermitian_add_ofReal_smul (hA : A.IsHermitian) (hB : BA.IsHermitian) (w : ℝ) :
    (A + ((w : ℝ) : ℂ) • BA).IsHermitian :=
  hA.add (by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hB.eq, Complex.star_def,
      Complex.conj_ofReal])

/-- Turn the two pointers' moving angles by `a`, `b`. -/
def shiftEcho (a b : AddCircle (1 : ℝ)) (z : EchoSigma N) : EchoSigma N :=
  ((z.1.1, (z.1.2.1 + a, z.1.2.2)), (z.2.1 + b, z.2.2))

/-- Turn the three pointers' moving angles. -/
def shiftTri (a b c : AddCircle (1 : ℝ)) (z : TriSigma N) : TriSigma N :=
  (shiftEcho a b z.1, (z.2.1 + c, z.2.2))

/-- Turn the four pointers' moving angles. -/
def shiftQuad (a b c d : AddCircle (1 : ℝ)) (z : QuadSigma N) : QuadSigma N :=
  (shiftTri a b c z.1, (z.2.1 + d, z.2.2))

/-- **Turn the five pointers' moving angles** by `a`, `b`, `c`, `d`, `e`, leaving the ray and
the conserved angles. -/
def shiftPenta (a b c d e : AddCircle (1 : ℝ)) (z : PentaSigma N) : PentaSigma N :=
  (shiftQuad a b c d z.1, (z.2.1 + e, z.2.2))

theorem twoCoupledFlow_shiftEcho (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (t : ℝ) (a b : AddCircle (1 : ℝ))
    (z : EchoSigma N) :
    twoCoupledFlow A BA BB hf hg hc hcg t (shiftEcho a b z)
      = shiftEcho a b (twoCoupledFlow A BA BB hf hg hc hcg t z) := by
  obtain ⟨⟨x, θ⟩, ψ⟩ := z
  have e : shiftEcho a b ((x, θ), ψ) = ((x, (θ.1 + a, θ.2)), (ψ.1 + b, ψ.2)) := rfl
  rw [e, twoCoupledFlow_apply hA hBA hBB hf hg hc hcg t x (θ.1 + a, θ.2) (ψ.1 + b, ψ.2),
    twoCoupledFlow_apply hA hBA hBB hf hg hc hcg t x θ ψ]
  simp only [shiftEcho, add_right_comm]

theorem threeCoupledFlow_shiftTri (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hBC : BC.IsHermitian) (hf : Function.Periodic f 1)
    (hg : Function.Periodic g 1) (hk : Function.Periodic k 1) (hc : ContDiff ℝ ∞ f)
    (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k) (t : ℝ) (a b c : AddCircle (1 : ℝ))
    (z : TriSigma N) :
    threeCoupledFlow A BA BB BC hf hg hk hc hcg hck t (shiftTri a b c z)
      = shiftTri a b c (threeCoupledFlow A BA BB BC hf hg hk hc hcg hck t z) := by
  obtain ⟨q, χ⟩ := z
  have e : shiftTri a b c (q, χ) = (shiftEcho a b q, (χ.1 + c, χ.2)) := rfl
  have hA' := isHermitian_add_ofReal_smul hA hBC (hk.lift χ.2)
  rw [e, threeCoupledFlow_apply, threeCoupledFlow_apply]
  dsimp only
  simp only [twoCoupledFlow_shiftEcho hA' hBA hBB]
  simp only [shiftTri, shiftEcho, add_right_comm]

theorem fourCoupledFlow_shiftQuad (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hBC : BC.IsHermitian) (hBD : BD.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (hk : Function.Periodic k 1)
    (hl : Function.Periodic l 1) (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g)
    (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l) (t : ℝ) (a b c d : AddCircle (1 : ℝ))
    (z : QuadSigma N) :
    fourCoupledFlow A BA BB BC BD hf hg hk hl hc hcg hck hcl t (shiftQuad a b c d z)
      = shiftQuad a b c d (fourCoupledFlow A BA BB BC BD hf hg hk hl hc hcg hck hcl t z) := by
  obtain ⟨q, ξ⟩ := z
  have e : shiftQuad a b c d (q, ξ) = (shiftTri a b c q, (ξ.1 + d, ξ.2)) := rfl
  have hA' := isHermitian_add_ofReal_smul hA hBD (hl.lift ξ.2)
  rw [e, fourCoupledFlow_apply, fourCoupledFlow_apply]
  dsimp only
  simp only [threeCoupledFlow_shiftTri hA' hBA hBB hBC]
  simp only [shiftQuad, shiftTri, shiftEcho, triRayEnergy, echoRayEnergy, add_right_comm]

/-- ★★★ **The five-pointer flow commutes with turning the pointers.** For Hermitian matrices,
starting the five pointers `a`, …, `e` further round leaves them `a`, …, `e` further round at
every time, and leaves the ray and the five conserved angles as they were. -/
theorem fiveCoupledFlow_shiftPenta (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hBC : BC.IsHermitian) (hBD : BD.IsHermitian)
    (hBE : BE.IsHermitian) (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hr : Function.Periodic r 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k)
    (hcl : ContDiff ℝ ∞ l) (hcr : ContDiff ℝ ∞ r) (t : ℝ) (a b c d e : AddCircle (1 : ℝ))
    (z : PentaSigma N) :
    fiveCoupledFlow A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr t
        (shiftPenta a b c d e z)
      = shiftPenta a b c d e
        (fiveCoupledFlow A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr t z) := by
  obtain ⟨q, ζ⟩ := z
  have e' : shiftPenta a b c d e (q, ζ) = (shiftQuad a b c d q, (ζ.1 + e, ζ.2)) := rfl
  have hA' := isHermitian_add_ofReal_smul hA hBE (hr.lift ζ.2)
  rw [e', fiveCoupledFlow_apply, fiveCoupledFlow_apply]
  dsimp only
  simp only [fourCoupledFlow_shiftQuad hA' hBA hBB hBC hBD]
  simp only [shiftPenta, shiftQuad, shiftTri, shiftEcho, quadRayEnergy, triRayEnergy,
    echoRayEnergy, add_right_comm]

/-- ★★ **No pointer's state depends on where the other pointers started.** Turning the first
four pointers leaves the fifth pointer's angles at every time as they were. -/
theorem fiveCoupledFlow_shiftPenta_snd (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hBC : BC.IsHermitian) (hBD : BD.IsHermitian)
    (hBE : BE.IsHermitian) (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hr : Function.Periodic r 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k)
    (hcl : ContDiff ℝ ∞ l) (hcr : ContDiff ℝ ∞ r) (t : ℝ) (a b c d : AddCircle (1 : ℝ))
    (z : PentaSigma N) :
    (fiveCoupledFlow A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr t
        (shiftPenta a b c d 0 z)).2
      = (fiveCoupledFlow A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr t z).2 := by
  rw [fiveCoupledFlow_shiftPenta hA hBA hBB hBC hBD hBE]
  simp only [shiftPenta, add_zero]

/-- ★★ **The ray does not see where the pointers are.** -/
theorem fiveCoupledFlow_shiftPenta_ray (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hBC : BC.IsHermitian) (hBD : BD.IsHermitian)
    (hBE : BE.IsHermitian) (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hr : Function.Periodic r 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k)
    (hcl : ContDiff ℝ ∞ l) (hcr : ContDiff ℝ ∞ r) (t : ℝ) (a b c d e : AddCircle (1 : ℝ))
    (z : PentaSigma N) :
    (fiveCoupledFlow A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr t
        (shiftPenta a b c d e z)).1.1.1.1.1
      = (fiveCoupledFlow A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr t z).1.1.1.1.1 := by
  rw [fiveCoupledFlow_shiftPenta hA hBA hBB hBC hBD hBE]
  rfl

end LF4
end CSD

end
