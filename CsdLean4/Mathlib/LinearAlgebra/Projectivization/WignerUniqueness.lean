/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.WignerRigidity
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.PhaseRigidity
public import Mathlib.LinearAlgebra.Center

/-!
# Wigner uniqueness: the inducing (anti)unitary is unique up to phase

**Category:** 1-Mathlib (CSD-free Mathlib upstream candidate).

The **uniqueness clause** of the classical Wigner/Bargmann theorem, in the
vocabulary of `wigner_rigidity`'s own conclusion (`projMap` of a `≃ₗᵢ[ℂ]`,
antiunitary branch through `conjProj`):

- `Projectivization.exists_unit_smul_of_projMap_eq` — two linear isometry
  equivalences with the same projective action differ by a global unit-modulus
  phase: `e₂ = c • e₁` pointwise with `‖c‖ = 1` (any complex inner-product
  space, subsingleton case included).
- `Projectivization.conjProj_conjProj` — `conjProj` is an involution on
  `ℂℙ^{N-1}` (hence surjective).
- `Projectivization.exists_unit_smul_of_projMap_conjProj_eq` — the antiunitary
  twin: two inducers of the same antiunitary ray map (`projMap e ∘ conjProj`)
  differ by a global unit-modulus phase.

Together with `wigner_rigidity` (existence) and the branch-exclusivity facts
(`conjProj_ne_projMap` / `smul_action_not_antiunitary`,
`Empirical/CSD/Gates/WignerDischarge.lean`; Bargmann discriminator,
`Projectivization/Bargmann.lean`), this completes the classical statement:
every transition-probability-preserving map is induced by a unitary or
antiunitary operator, **unique up to a global phase within its branch**.

The matrix-vocabulary sibling (two `Matrix.unitaryGroup` elements with the
same ray action differ by a phase — the kernel of `U(N) → PU(N)` is the
circle) predates this module: `Projectivization.exists_unit_smul_of_smul_eq_smul`
(`PhaseRigidity.lean`, built for the W5-S1 phase lift). This module proves the
`≃ₗᵢ`-vocabulary form directly (same homothety engine,
`LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent`) rather than
transporting through matrices, because `projMap` is what `wigner_rigidity`
outputs and the isometry route needs no unitary star-algebra.

Provenance: CL-024 audit follow-up (2026-08-06) — the audit named up-to-phase
uniqueness as the formalization gap against the reference; the matrix form
turned out to already exist in `PhaseRigidity.lean`, and this module closes
the remaining vocabulary gap. See `specs/audit-sweep-plan.md` (intake) and
`specs/BACKLOG.md` G11.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace Projectivization

/-! ### Uniqueness up to phase, `projMap` vocabulary -/

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Wigner uniqueness (unitary branch).** Two linear isometry equivalences
inducing the same projective self-map are equal up to a global unit-modulus
phase: `e₂ = c • e₁` pointwise with `‖c‖ = 1`. Route: `e₂ ∘ e₁⁻¹` fixes every
ray, so every vector is an eigenvector of the composite; by the homothety
lemma it is `c • id`, and the isometry property pins `‖c‖ = 1`. -/
theorem exists_unit_smul_of_projMap_eq (e₁ e₂ : E ≃ₗᵢ[ℂ] E)
    (h : ∀ p : ℙ ℂ E, projMap e₁ p = projMap e₂ p) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v : E, e₂ v = c • e₁ v := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact ⟨1, norm_one, fun v => Subsingleton.elim _ _⟩
  -- The composite `f := e₂ ∘ e₁⁻¹` sends every vector to a scalar multiple of
  -- itself: every ray is fixed.
  set f : E →ₗ[ℂ] E :=
    (e₂.toLinearEquiv.toLinearMap).comp e₁.symm.toLinearEquiv.toLinearMap with hf
  have hdep : ∀ w : E, ¬ LinearIndependent ℂ ![w, f w] := by
    intro w
    by_cases hw : w = 0
    · intro hli
      exact hli.ne_zero 0 (by rw [Matrix.cons_val_zero, hw])
    · have hv1 : e₁.symm w ≠ 0 := by
        simpa using e₁.symm.toLinearEquiv.map_ne_zero_iff.mpr hw
      have hmk := h (Projectivization.mk ℂ (e₁.symm w) hv1)
      rw [projMap_mk, projMap_mk, Projectivization.mk_eq_mk_iff'] at hmk
      -- hmk : ∃ a, a • e₂ (e₁.symm w) = e₁ (e₁.symm w)
      obtain ⟨a, ha⟩ := hmk
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [zero_smul] at ha
        exact hw (by simpa using congrArg e₁.symm ha.symm)
      have hw' : e₁ (e₁.symm w) = w := e₁.apply_symm_apply w
      rw [hw'] at ha
      have hfw : f w = a⁻¹ • w := by
        show e₂ (e₁.symm w) = a⁻¹ • w
        conv_rhs => rw [← ha]
        rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
      intro hli
      exact (LinearIndependent.pair_iff' hw).mp hli (a⁻¹ : ℂ) hfw.symm
  obtain ⟨c, hc⟩ :=
    LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hdep
  -- The isometry property pins the modulus.
  obtain ⟨w, hw⟩ := exists_ne (0 : E)
  have hfw : f w = c • w := by rw [hc]; rfl
  have hnormw : ‖f w‖ = ‖w‖ := by
    show ‖e₂ (e₁.symm w)‖ = ‖w‖
    rw [e₂.norm_map, e₁.symm.norm_map]
  have hcn : ‖c‖ = 1 := by
    rw [hfw, norm_smul] at hnormw
    exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hw)
      (by rw [hnormw, one_mul])
  refine ⟨c, hcn, fun v => ?_⟩
  have hv : f (e₁ v) = c • e₁ v := by rw [hc]; rfl
  have hv' : f (e₁ v) = e₂ v := by
    show e₂ (e₁.symm (e₁ v)) = e₂ v
    rw [e₁.symm_apply_apply]
  rw [← hv', hv]

end General

/-! ### The antiunitary branch -/

section Antiunitary

variable {N : ℕ}

/-- `conjVec` is an involution: coordinatewise double conjugation is the
identity. -/
lemma conjVec_conjVec (ψ : EuclideanSpace ℂ (Fin N)) :
    conjVec (conjVec ψ) = ψ := by
  ext i
  rw [conjVec_ofLp, conjVec_ofLp, Complex.conj_conj]

/-- **`conjProj` is an involution** on `ℂℙ^{N-1}`: conjugating the ray twice
returns the ray (hence `conjProj` is surjective — the fact the antiunitary
uniqueness reduction needs). -/
theorem conjProj_conjProj (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    conjProj (conjProj p) = p := by
  -- The rep of `conjProj p` is a scalar multiple of `conjVec p.rep`.
  have h1 : Projectivization.mk ℂ ((conjProj p).rep) (conjProj p).rep_nonzero
      = Projectivization.mk ℂ (conjVec p.rep) (conjVec_ne_zero p.rep_nonzero) := by
    rw [Projectivization.mk_rep]
    rfl
  rw [Projectivization.mk_eq_mk_iff'] at h1
  obtain ⟨a, ha⟩ := h1
  -- ha : a • conjVec p.rep = (conjProj p).rep
  show Projectivization.mk ℂ (conjVec ((conjProj p).rep))
      (conjVec_ne_zero (conjProj p).rep_nonzero) = p
  conv_rhs => rw [← p.mk_rep]
  rw [Projectivization.mk_eq_mk_iff']
  refine ⟨starRingEnd ℂ a, ?_⟩
  rw [← ha, conjVec_smul, conjVec_conjVec]

/-- **Wigner uniqueness (antiunitary branch).** Two linear isometry
equivalences inducing the same antiunitary ray map (`projMap e ∘ conjProj`,
the shape of `wigner_rigidity`'s second disjunct) are equal up to a global
unit-modulus phase. Reduces to the unitary branch through the involutivity of
`conjProj`. -/
theorem exists_unit_smul_of_projMap_conjProj_eq
    (e₁ e₂ : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N))
    (h : ∀ p : ℙ ℂ (EuclideanSpace ℂ (Fin N)),
      projMap e₁ (conjProj p) = projMap e₂ (conjProj p)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, e₂ v = c • e₁ v := by
  refine exists_unit_smul_of_projMap_eq e₁ e₂ fun q => ?_
  have hq := h (conjProj q)
  rwa [conjProj_conjProj] at hq

end Antiunitary

end Projectivization
