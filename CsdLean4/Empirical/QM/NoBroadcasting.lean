/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.LinearAlgebra.Matrix.PartialTrace
public import CsdLean4.LF2.BornWrapper
public import CsdLean4.LF2.ReducedDensity

/-!
# Empirical/QM: No-broadcasting — pure-marginal confinement core (E2)

**Category:** 3-Local.

No-broadcasting (Barnum-Caves-Fuchs-Jozsa-Schumacher 1996) generalises no-cloning
to mixed states: a set of states can be *broadcast* (each marginal of a joint
output equals the corresponding input) iff the states mutually commute. The full
iff is fidelity / channel-monotonicity content and is **out of scope** here —
Mathlib has no fidelity, relative entropy, or CPTP/Kraus machinery (it joins the
deferred quantum-information-infrastructure tranche alongside E7/E91, see
`specs/qm-empirical-tests.md`).

What the partial-trace infrastructure
(`CsdLean4/Mathlib/LinearAlgebra/Matrix/PartialTrace.lean`) *does* deliver is the
**structural squeeze that makes broadcasting of a pure state impossible**:

> **Pure-marginal confinement.** If a bipartite (PSD, Hermitian) operator `ρ` on
> `ℂ^N ⊗ ℂ^n` has a *pure* first-factor marginal `traceRight ρ = |ψ⟩⟨ψ|`, then
> `ρ` is confined to that pure sector: `(P ⊗ I) · ρ · (P ⊗ I) = ρ`, where
> `P = |ψ⟩⟨ψ|`.

A pure marginal leaves the joint state no freedom outside the `P`-sector — the
operative fact behind "broadcasting pure states = cloning them." The proof is the
positive-semidefinite block-vanishing technique (mirroring
`LF2.rankOneDensity_unique_of_certainty`): the complementary block
`(Q ⊗ I) · ρ · (Q ⊗ I)` (with `Q = I − P`) is PSD with trace zero — its trace is
`Tr(traceRight ρ · Q) = Tr(P · Q) = 0` via the partial-trace module laws — hence
zero, which pins `ρ` to the `P`-sector.

## Source

Barnum, Caves, Fuchs, Jozsa, Schumacher 1996, *Phys. Rev. Lett.* **76**, 2818
(the full no-broadcasting theorem; only the pure-marginal core is formalised here).
-/

@[expose] public section

open Matrix
open scoped ComplexOrder Kronecker

namespace CSD
namespace Empirical
namespace QM
namespace NoBroadcasting

variable {N n : ℕ}

/-- The pure-state density `P = |ψ⟩⟨ψ|` for a unit vector `ψ`. -/
local notation3 "P[" ψ "]" => CSD.LF2.outerProduct ψ

/-- **Trace of the complementary-block conjugation vanishes.** With `P = |ψ⟩⟨ψ|`,
`Q = I − P`, and a bipartite operator `ρ` whose first-factor marginal is `P`,
the trace of `(Q ⊗ I) · ρ · (Q ⊗ I)` is zero:
`Tr = Tr(ρ · (Q ⊗ I)) = Tr(traceRight ρ · Q) = Tr(P · Q) = 0` (since `P·Q = 0`). -/
theorem traceForm_complement_block_zero
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1)
    (ρ : Matrix (Fin N × Fin n) (Fin N × Fin n) ℂ)
    (hmarg : traceRight ρ = CSD.LF2.outerProduct ψ) :
    (((1 - CSD.LF2.outerProduct ψ) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * ρ
        * ((1 - CSD.LF2.outerProduct ψ) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))).trace = 0 := by
  set P := CSD.LF2.outerProduct ψ with hP
  set Q : Matrix (Fin N) (Fin N) ℂ := 1 - P with hQ
  set K : Matrix (Fin N × Fin n) (Fin N × Fin n) ℂ := Q ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) with hK
  have hPidem : P * P = P := CSD.LF2.outerProduct_mul_self_of_unit_norm ψ hψ
  have hPtr : P.trace = 1 := CSD.LF2.outerProduct_trace_of_unit_norm ψ hψ
  -- K is idempotent: (Q⊗I)(Q⊗I) = Q²⊗I = Q⊗I, since Q² = Q.
  have hQidem : Q * Q = Q := by
    rw [hQ, sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hPidem]
    abel
  have hKidem : K * K = K := by
    rw [hK, ← Matrix.mul_kronecker_mul, hQidem, Matrix.one_mul]
  -- Tr(K ρ K) = Tr(ρ K K) = Tr(ρ K).
  have h1 : (K * ρ * K).trace = (ρ * K).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm K (ρ * K), Matrix.mul_assoc, hKidem]
  -- Tr(ρ (Q⊗I)) = Tr(traceRight ρ · Q) by the right-module law.
  have h2 : (ρ * K).trace = (traceRight ρ * Q).trace := by
    rw [hK, ← Matrix.traceRight_mul_kronecker_one ρ Q, Matrix.trace_traceRight]
  -- traceRight ρ = P, and Tr(P Q) = Tr(P) − Tr(P P) = 1 − 1 = 0.
  rw [h1, h2, hmarg, hQ, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, hPidem, hPtr,
    sub_self]

/-- **Pure-marginal confinement (E2 core).** A bipartite positive-semidefinite
operator `ρ` whose first-factor marginal is the pure state `P = |ψ⟩⟨ψ|` is confined
to the `P`-sector: `(P ⊗ I) · ρ · (P ⊗ I) = ρ`.

This is the structural obstruction to broadcasting a pure state: the joint output
of any prospective broadcaster, having `|ψ⟩⟨ψ|` as a marginal, has no support
outside the one-dimensional `ψ`-sector — leaving no room for an independent second
copy (which would require support on `|φ⟩` for a distinct `φ`). The proof: the
complementary block `(Q ⊗ I)·ρ·(Q ⊗ I)` is PSD (sandwich of PSD by Hermitian) with
trace zero (`traceForm_complement_block_zero`), hence zero; standard PSD reasoning
then collapses `ρ` to its `P`-sector. -/
theorem pure_marginal_confinement
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1)
    (ρ : Matrix (Fin N × Fin n) (Fin N × Fin n) ℂ) (hρ : ρ.PosSemidef)
    (hmarg : traceRight ρ = CSD.LF2.outerProduct ψ) :
    (CSD.LF2.outerProduct ψ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * ρ
        * (CSD.LF2.outerProduct ψ ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) = ρ := by
  set P := CSD.LF2.outerProduct ψ with hP
  set Q : Matrix (Fin N) (Fin N) ℂ := 1 - P with hQ
  set Kp : Matrix (Fin N × Fin n) (Fin N × Fin n) ℂ := P ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) with hKp
  set Kq : Matrix (Fin N × Fin n) (Fin N × Fin n) ℂ := Q ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) with hKq
  have hP_herm : P.IsHermitian := CSD.LF2.outerProduct_isHermitian ψ
  have hKq_herm : Kq.IsHermitian := by
    rw [hKq, Matrix.IsHermitian, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
    rw [show Qᴴ = Q from (Matrix.isHermitian_one.sub hP_herm).eq]
  -- Kq ρ Kq is PSD with trace zero, hence zero.
  have hKqρKq_psd : (Kq * ρ * Kq).PosSemidef := by
    have hsub : Kqᴴ * ρ * Kq = Kq * ρ * Kq := by rw [hKq_herm.eq]
    rw [← hsub]; exact hρ.conjTranspose_mul_mul_same Kq
  have hKqρKq_zero : Kq * ρ * Kq = 0 :=
    (Matrix.PosSemidef.trace_eq_zero_iff hKqρKq_psd).mp
      (traceForm_complement_block_zero ψ hψ ρ hmarg)
  -- ρ Kq = 0, by PSD dotProduct-mulVec zero (same route as rankOneDensity_unique).
  have hρKq_zero : ρ * Kq = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
    apply (hρ.dotProduct_mulVec_zero_iff _).mp
    rw [Matrix.star_mulVec, hKq_herm.eq, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hKqρKq_zero, Matrix.zero_mulVec,
      dotProduct_zero]
  -- Kp = I − Kq (since P + Q = I). So ρ = ρ Kp and (taking adjoints) ρ = Kp ρ Kp.
  -- Kp + Kq = (P + Q) ⊗ I = I ⊗ I = I, so Kp = I − Kq.
  have hKpKq : Kp = 1 - Kq := by
    have hsum : Kp + Kq = 1 := by
      rw [hKp, hKq, ← Matrix.add_kronecker, hQ, add_sub_cancel, Matrix.one_kronecker_one]
    rw [eq_sub_iff_add_eq, hsum]
  have hρKp : ρ * Kp = ρ := by
    rw [hKpKq, Matrix.mul_sub, Matrix.mul_one, hρKq_zero, sub_zero]
  -- Kp is Hermitian; ρ Hermitian ⟹ ρ = Kp ρ = ρ Kp, and ρ = Kp ρ Kp.
  have hKp_herm : Kp.IsHermitian := by
    rw [hKp, Matrix.IsHermitian, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      hP_herm.eq]
  have hKpρ : Kp * ρ = ρ := by
    have h := congrArg Matrix.conjTranspose hρKp
    rwa [Matrix.conjTranspose_mul, hKp_herm.eq, hρ.isHermitian.eq] at h
  calc Kp * ρ * Kp = ρ * Kp := by rw [hKpρ]
    _ = ρ := hρKp

end NoBroadcasting
end QM
end Empirical
end CSD
