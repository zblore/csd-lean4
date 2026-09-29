import CsdLean4.Mathlib.Analysis.InnerProductSpace.Gleason.RealFrame
import CsdLean4.LF2.EffectGleason

open Matrix Gleason

namespace SubmissionAudit

-- Closed types: the actual declarations fit these signatures without extra premises.
example : ∀ {N : ℕ} (OP : RealProjectionPackage N), 3 ≤ N →
    ∃! ρ : Matrix (Fin N) (Fin N) ℝ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ P, IsStarProjection P → OP.p P = (ρ * P).trace :=
  @RealProjectionPackage.real_gleason_representation

example : ∀ {N : ℕ} {f : EuclideanSpace ℝ (Fin N) → ℝ} {W : ℝ},
    IsFrameFunction ℝ f W → 3 ≤ N → (∀ v, ‖v‖ = 1 → 0 ≤ f v) →
    ∃! A : Matrix (Fin N) (Fin N) ℝ, A.PosSemidef ∧ A.trace = W ∧
      ∀ v, ‖v‖ = 1 → f v = ⇑v ⬝ᵥ (A *ᵥ ⇑v) :=
  @existsUnique_density_of_frameFunction

-- A submission-facing statement using only Mathlib notions in the signature.
theorem real_matrices {N : ℕ} (hN : 3 ≤ N) (p : Matrix (Fin N) (Fin N) ℝ → ℝ)
    (h0 : ∀ P, IsStarProjection P → 0 ≤ p P) (h1 : p 1 = 1)
    (ha : ∀ P Q, IsStarProjection P → IsStarProjection Q → P * Q = 0 →
      p (P + Q) = p P + p Q) :
    ∃! ρ : Matrix (Fin N) (Fin N) ℝ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ P, IsStarProjection P → p P = (ρ * P).trace :=
  (RealProjectionPackage.mk p h0 h1 ha).real_gleason_representation hN

theorem real_frames {N : ℕ} (hN : 3 ≤ N) (f : EuclideanSpace ℝ (Fin N) → ℝ) (W : ℝ)
    (h0 : ∀ v, ‖v‖ = 1 → 0 ≤ f v)
    (hb : ∀ b : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)),
      ∑ i, f (b i) = W) :
    ∃! A : Matrix (Fin N) (Fin N) ℝ, A.PosSemidef ∧ A.trace = W ∧
      ∀ v, ‖v‖ = 1 → f v = ⇑v ⬝ᵥ (A *ᵥ ⇑v) :=
  existsUnique_density_of_frameFunction hb hN h0

-- Construct a nonconstant input without any representation theorem.
def coordinateReal {N : ℕ} (i : Fin N) : RealProjectionPackage N where
  p P := P i i
  nonneg P hp := by
    have heq : Pᴴ * P = P := by
      simpa only [← Matrix.star_eq_conjTranspose, hp.isSelfAdjoint.star_eq] using
        hp.isIdempotentElem.eq
    have hpsd := Matrix.posSemidef_conjTranspose_mul_self P
    rw [heq] at hpsd
    exact hpsd.diag_nonneg
  total_one := by simp
  additive P Q _ _ _ := by simp [Matrix.add_apply]

theorem real_dimension_three :
    ∃! ρ : Matrix (Fin 3) (Fin 3) ℝ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ P, IsStarProjection P → P 0 0 = (ρ * P).trace :=
  (coordinateReal (0 : Fin 3)).real_gleason_representation (by norm_num)

example : (coordinateReal (0 : Fin 3)).frame (EuclideanSpace.single 0 (1 : ℝ)) = 1 ∧
    (coordinateReal (0 : Fin 3)).frame (EuclideanSpace.single 1 (1 : ℝ)) = 0 := by
  simp [RealProjectionPackage.frame, coordinateReal, rankOneR, Matrix.vecMulVec,
    Pi.single_apply]

-- Exercise arbitrary nonnegative weights, including 0 and weights above 1.
theorem weighted_coordinate (W : ℝ) (hW : 0 ≤ W) :
    ∃! A : Matrix (Fin 3) (Fin 3) ℝ, A.PosSemidef ∧ A.trace = W ∧
      ∀ v : EuclideanSpace ℝ (Fin 3), ‖v‖ = 1 →
        W * (coordinateReal (0 : Fin 3)).frame v = ⇑v ⬝ᵥ (A *ᵥ ⇑v) := by
  apply real_frames (by norm_num) _ W
  · intro v hv
    exact mul_nonneg hW ((coordinateReal (0 : Fin 3)).frame_nonneg hv)
  · intro b
    rw [← Finset.mul_sum, (coordinateReal (0 : Fin 3)).sum_frame_orthonormalBasis, mul_one]

example : ∃! A : Matrix (Fin 3) (Fin 3) ℝ, A.PosSemidef ∧ A.trace = 0 ∧
    ∀ v : EuclideanSpace ℝ (Fin 3), ‖v‖ = 1 → 0 = ⇑v ⬝ᵥ (A *ᵥ ⇑v) := by
  simpa using weighted_coordinate 0 (le_refl 0)

example : ∃! A : Matrix (Fin 3) (Fin 3) ℝ, A.PosSemidef ∧ A.trace = 2 ∧
    ∀ v : EuclideanSpace ℝ (Fin 3), ‖v‖ = 1 →
      2 * (coordinateReal (0 : Fin 3)).frame v = ⇑v ⬝ᵥ (A *ᵥ ⇑v) :=
  weighted_coordinate 2 (by norm_num)

theorem negative_weight_impossible {N : ℕ} {f : EuclideanSpace ℝ (Fin N) → ℝ} {W : ℝ}
    (hf : IsFrameFunction ℝ f W) (h0 : ∀ v, ‖v‖ = 1 → 0 ≤ f v) (hW : W < 0) : False :=
  (not_lt_of_ge (hf.zero_le_weight h0)) hW

theorem no_zero_dimensional_real (OP : RealProjectionPackage 0) : False := by
  have h : (1 : Matrix (Fin 0) (Fin 0) ℝ) = 0 := Subsingleton.elim _ _
  have ht := OP.total_one
  rw [h, OP.p_zero] at ht
  norm_num at ht

end SubmissionAudit

open Lean Elab Command in
run_cmd do
  let standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``Gleason.coreLemma, ``Gleason.ProjectionPackage.gleason_representation,
      ``CSD.LF2.OperationalPackage.effect_gleason_representation,
      ``Gleason.RealProjectionPackage.real_gleason_representation,
      ``Gleason.existsUnique_density_of_frameFunction,
      ``SubmissionAudit.real_matrices, ``SubmissionAudit.real_frames,
      ``SubmissionAudit.weighted_coordinate] do
    unless (← getEnv).contains n do throwError m!"missing declaration: {n}"
    let axs ← collectAxioms n
    let extra := axs.filter fun a => !standard.contains a
    unless extra.isEmpty do throwError m!"unexpected axioms for {n}: {extra}"
    logInfo m!"PASS {n}: {axs}"
