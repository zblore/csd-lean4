/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.CompositeInterface
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# SigmaLayer/Luders: the projective (Lüders) state update

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)).

Ledger target **T8**, the projective post-measurement (Lüders) update, closing the gap left by
`SigmaLayer/MeasurementRecord.lean` (which supplies only the epistemic-support conditioning
`compatibleSet_appendEstablishedFact` and explicitly declines to call it a Lüders update until an
equality with the Lüders rule is proved).

For a projection `p` (self-adjoint idempotent) and a state `x` with `p x ≠ 0`, the Lüders update is the
normalised projected state `ludersUpdate p x = (‖p x‖)⁻¹ • p x`. Its Born weight for a projection is
`projWeight p x = ‖p x‖²` (equal to `Re⟨x, p x⟩`, the effect/POVM weight, `projWeight_eq_re_inner`). We
prove the three defining properties:

* **normalisation** (`ludersUpdate_norm`): the updated state is a unit vector;
* **repeatability** (`ludersUpdate_repeatable`): `p` fixes the updated state, so an immediate
  re-measurement yields the same outcome with certainty (Born weight `1`);
* **Lüders = conditional probability** (`ludersUpdate_conditional`): for a finer projection `q` inside
  the range of `p` (`q ∘ p = q`), the Born weight of `q` in the updated state is
  `projWeight q x / projWeight p x` — the update reproduces the CONDITIONAL Born probabilities.

The third property is the content of "Lüders update", the state-space counterpart of the ontic
conditioning `compatibleSet_appendEstablishedFact` (both condition on the realised outcome); it is
Bayesian conditionalisation at the level of Born weights. Matrix projections instantiate the abstract
`IsProjection` via `isProjection_toEuclideanLin`, connecting to the repository's matrix-based Born
weights and `LF2.POVM` effects.

Everything is proved for a general finite-dimensional complex inner product space; no new postulate.
-/

@[expose] public section

open scoped ComplexConjugate Matrix

-- Several lemmas below (norms, the conditional-probability identity) do not use the ambient
-- `FiniteDimensional ℂ E` instance; it is only needed where `LinearMap.adjoint` appears.
set_option linter.unusedSectionVars false

namespace CSD.SigmaLayer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- **A projection: a self-adjoint idempotent operator.** The observable's spectral projector for a
measurement outcome. -/
structure IsProjection (p : E →ₗ[ℂ] E) : Prop where
  /-- The projector is self-adjoint. -/
  selfAdjoint : LinearMap.adjoint p = p
  /-- The projector is idempotent. -/
  idempotent : ∀ x, p (p x) = p x

/-- **The projective Born weight of a state.** `‖p x‖²`, the probability of the outcome whose projector
is `p`. -/
noncomputable def projWeight (p : E →ₗ[ℂ] E) (x : E) : ℝ := ‖p x‖ ^ 2

/-- **The Lüders update.** The normalised projected state `(‖p x‖)⁻¹ • p x` (and `0` on the null set
`p x = 0`). -/
noncomputable def ludersUpdate (p : E →ₗ[ℂ] E) (x : E) : E := ((‖p x‖ : ℂ))⁻¹ • p x

/-- **The projective Born weight is the effect expectation `Re⟨x, p x⟩`.** For a projection,
`‖p x‖² = Re⟨x, p x⟩`, so `projWeight` agrees with the `LF2.POVM`/effect weight convention on projective
effects. -/
theorem projWeight_eq_re_inner (p : E →ₗ[ℂ] E) (hp : IsProjection p) (x : E) :
    projWeight p x = (inner ℂ x (p x)).re := by
  have h1 : inner ℂ x (p x) = inner ℂ (p x) (p x) := by
    nth_rewrite 1 [← hp.idempotent x]
    rw [show p (p x) = (LinearMap.adjoint p) (p x) from by rw [hp.selfAdjoint]]
    rw [LinearMap.adjoint_inner_right]
  rw [projWeight, h1, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- Norm of the scalar `(‖p x‖ : ℂ)⁻¹`. -/
theorem norm_inv_ofReal_norm (p : E →ₗ[ℂ] E) (x : E) :
    ‖((‖p x‖ : ℂ))⁻¹‖ = (‖p x‖)⁻¹ := by
  rw [norm_inv, Complex.norm_real, norm_norm]

/-- **Normalisation.** The Lüders update is a unit vector whenever the outcome is possible
(`p x ≠ 0`). -/
theorem ludersUpdate_norm (p : E →ₗ[ℂ] E) (x : E) (hx : p x ≠ 0) :
    ‖ludersUpdate p x‖ = 1 := by
  rw [ludersUpdate, norm_smul, norm_inv_ofReal_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

/-- **Repeatability.** The projector `p` fixes its own Lüders update, so an immediate re-measurement of
the same observable returns the same outcome with certainty (`projWeight p` of the updated state is
`1`). -/
theorem ludersUpdate_repeatable (p : E →ₗ[ℂ] E) (hp : IsProjection p) (x : E) :
    p (ludersUpdate p x) = ludersUpdate p x := by
  rw [ludersUpdate, map_smul, hp.idempotent x]

/-- **Lüders = conditional probability.** For a finer projection `q` supported inside the range of `p`
(`q ∘ p = q`), the Born weight of `q` in the Lüders-updated state equals the conditional probability
`projWeight q x / projWeight p x`: the projective update reproduces Bayesian conditionalisation of the
Born weights. -/
theorem ludersUpdate_conditional (p q : E →ₗ[ℂ] E) (hqp : ∀ x, q (p x) = q x) (x : E)
    (hx : p x ≠ 0) :
    projWeight q (ludersUpdate p x) = projWeight q x / projWeight p x := by
  have hpx : ‖p x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rw [projWeight, ludersUpdate, map_smul, hqp x, norm_smul, norm_inv_ofReal_norm, mul_pow,
    projWeight, projWeight]
  rw [inv_pow, div_eq_mul_inv, mul_comm]

/-- **T8: the projective (Lüders) update, its three defining properties.** For any projection `p`, the
Lüders update `ludersUpdate p` is normalised, repeatable, and reproduces the conditional Born
probabilities. This is the projective post-measurement state update, the state-space counterpart of the
ontic conditioning `compatibleSet_appendEstablishedFact`. -/
theorem luders_capstone (p : E →ₗ[ℂ] E) (hp : IsProjection p) :
    (∀ x, p x ≠ 0 → ‖ludersUpdate p x‖ = 1)
    ∧ (∀ x, p (ludersUpdate p x) = ludersUpdate p x)
    ∧ (∀ q : E →ₗ[ℂ] E, (∀ x, q (p x) = q x) → ∀ x, p x ≠ 0 →
        projWeight q (ludersUpdate p x) = projWeight q x / projWeight p x) :=
  ⟨fun x hx => ludersUpdate_norm p x hx,
    fun x => ludersUpdate_repeatable p hp x,
    fun q hqp x hx => ludersUpdate_conditional p q hqp x hx⟩

/-- **Matrix projections are projections.** A Hermitian idempotent matrix `P` (`Pᴴ = P`, `P * P = P`)
gives a projection `Matrix.toEuclideanLin P`, connecting the abstract Lüders update to the repository's
matrix-based Born weights and `LF2.POVM` effects. -/
theorem isProjection_toEuclideanLin {N : ℕ} (P : Matrix (Fin N) (Fin N) ℂ)
    (hh : Pᴴ = P) (hi : P * P = P) :
    IsProjection (Matrix.toEuclideanLin P) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hh]
  · have hcomp : Matrix.toEuclideanLin (P * P) x
        = Matrix.toEuclideanLin P (Matrix.toEuclideanLin P x) := by
      rw [Matrix.toLpLin_mul_same]; rfl
    rw [hi] at hcomp
    exact hcomp.symm

end CSD.SigmaLayer
