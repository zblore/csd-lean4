import CsdLean4.Mathlib.Analysis.InnerProductSpace.Gleason.Core
import CsdLean4.LF2.EffectGleason

open Matrix CSD.LF2
open scoped ComplexOrder

namespace EndpointAudit

-- Closed-type checks: no additional ambient assumptions can be hidden here.
example : ∀ {N : ℕ} (OP : Gleason.ProjectionPackage N), 3 ≤ N →
    ∃! ρ : Matrix (Fin N) (Fin N) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ P, IsStarProjection P → OP.p P = ((ρ * P).trace).re :=
  @Gleason.ProjectionPackage.gleason_representation

example : ∀ {N : ℕ} (OP : OperationalPackage N),
    ∃! ρ : DensityOperator N, ∀ E : Effect N, OP.p E = traceForm ρ E :=
  @OperationalPackage.effect_gleason_representation

-- A projection theorem whose signature contains no local package definitions.
theorem gleason_matrices {N : ℕ} (hN : 3 ≤ N)
    (p : Matrix (Fin N) (Fin N) ℂ → ℝ)
    (h0 : ∀ P, IsStarProjection P → 0 ≤ p P)
    (h1 : p 1 = 1)
    (ha : ∀ P Q, IsStarProjection P → IsStarProjection Q → P * Q = 0 →
      p (P + Q) = p P + p Q) :
    ∃! ρ : Matrix (Fin N) (Fin N) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ P, IsStarProjection P → p P = ((ρ * P).trace).re :=
  (Gleason.ProjectionPackage.mk p h0 h1 ha).gleason_representation hN

-- No upper-bound or continuity assumption; additivity includes noncommuting effects.
-- The returned object is a matrix, so uniqueness does not depend on proof fields.
theorem busch_matrices {N : ℕ} (p : Matrix (Fin N) (Fin N) ℂ → ℝ)
    (h0 : ∀ E, E.PosSemidef → (1 - E).PosSemidef → 0 ≤ p E)
    (h1 : p 1 = 1)
    (ha : ∀ E F, E.PosSemidef → (1 - E).PosSemidef →
      F.PosSemidef → (1 - F).PosSemidef → (1 - (E + F)).PosSemidef →
      p (E + F) = p E + p F) :
    ∃! ρ : Matrix (Fin N) (Fin N) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ E, E.PosSemidef → (1 - E).PosSemidef → p E = ((ρ * E).trace).re := by
  let OP : OperationalPackage N := {
    p := fun E => p E.M
    nonneg := fun E => h0 E.M E.nonneg E.le_one
    le_one := by
      intro E
      have hc : (1 - (1 - E.M)).PosSemidef := by simpa using E.nonneg
      have hs : (1 - (E.M + (1 - E.M))).PosSemidef := by
        simpa using (Matrix.PosSemidef.zero (n := Fin N) (R := ℂ))
      have hadd := ha E.M (1 - E.M) E.nonneg E.le_one E.le_one hc hs
      rw [add_sub_cancel, h1] at hadd
      have hn := h0 (1 - E.M) E.le_one hc
      linarith
    total_one := by simpa [Effect.one] using h1
    additivity := fun E F h => ha E.M F.M E.nonneg E.le_one F.nonneg F.le_one h }
  obtain ⟨ρ, hρ, hu⟩ := OP.effect_gleason_representation
  refine ⟨ρ.M, ⟨ρ.nonneg, ρ.trace_one, ?_⟩, ?_⟩
  · intro E he hc
    exact hρ ⟨E, he.isHermitian, he, hc⟩
  · rintro A ⟨ha0, ha1, hap⟩
    let σ : DensityOperator N := ⟨A, ha0.isHermitian, ha0, ha1⟩
    have heq : σ = ρ := hu σ (fun E => hap E.M E.nonneg E.le_one)
    exact congrArg DensityOperator.M heq

-- Construct inputs directly, without using either representation theorem.
def coordinateProjection {N : ℕ} (i : Fin N) : Gleason.ProjectionPackage N where
  p P := (P i i).re
  nonneg P hp := by
    have heq : Pᴴ * P = P := by
      simpa only [← Matrix.star_eq_conjTranspose, hp.isSelfAdjoint.star_eq] using
        hp.isIdempotentElem.eq
    have hpsd := Matrix.posSemidef_conjTranspose_mul_self P
    rw [heq] at hpsd
    exact (Complex.nonneg_iff.mp (hpsd.diag_nonneg (i := i))).1
  total_one := by simp
  additive P Q _ _ _ := by simp [Matrix.add_apply]

def coordinateOperational {N : ℕ} (i : Fin N) : OperationalPackage N where
  p E := (E.M i i).re
  nonneg E := (Complex.nonneg_iff.mp (E.nonneg.diag_nonneg (i := i))).1
  le_one E := by
    have h := (Complex.nonneg_iff.mp (E.le_one.diag_nonneg (i := i))).1
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Complex.sub_re, Complex.one_re] at h
    linarith
  total_one := by simp [Effect.one]
  additivity E F _ := by simp [Effect.add, Matrix.add_apply]

theorem busch_dimension_one :
    ∃! ρ : DensityOperator 1, ∀ E : Effect 1, (E.M 0 0).re = traceForm ρ E :=
  (coordinateOperational (0 : Fin 1)).effect_gleason_representation

theorem busch_dimension_two :
    ∃! ρ : DensityOperator 2, ∀ E : Effect 2, (E.M 0 0).re = traceForm ρ E :=
  (coordinateOperational (0 : Fin 2)).effect_gleason_representation

theorem gleason_dimension_three :
    ∃! ρ : Matrix (Fin 3) (Fin 3) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ P, IsStarProjection P → (P 0 0).re = ((ρ * P).trace).re :=
  (coordinateProjection (0 : Fin 3)).gleason_representation (by norm_num)

-- These inputs distinguish orthogonal outcomes, rather than forcing a scalar state.
example : (coordinateProjection (0 : Fin 3)).p
    (Gleason.rankOne (EuclideanSpace.single 0 (1 : ℂ))) = 1 ∧
    (coordinateProjection (0 : Fin 3)).p
    (Gleason.rankOne (EuclideanSpace.single 1 (1 : ℂ))) = 0 := by
  simp [coordinateProjection, Gleason.rankOne, Matrix.vecMulVec, Pi.single_apply]

theorem no_zero_dimensional_operational (OP : OperationalPackage 0) : False := by
  have h : (Effect.one : Effect 0) = Effect.zero :=
    Effect.ext_M (by ext i; exact Fin.elim0 i)
  have ht := OP.total_one
  rw [h, OP.p_zero] at ht
  norm_num at ht

theorem no_zero_dimensional_projection (OP : Gleason.ProjectionPackage 0) : False := by
  have h : (1 : Matrix (Fin 0) (Fin 0) ℂ) = 0 := Subsingleton.elim _ _
  have ht := OP.total_one
  rw [h, OP.p_zero] at ht
  norm_num at ht

-- Re-run the terminal axiom pins against freshly compiled source, including the
-- new namespace that a CSD-only sweep would miss.
/-- info: 'Gleason.coreLemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Gleason.coreLemma
/-- info: 'Gleason.ProjectionPackage.gleason_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Gleason.ProjectionPackage.gleason_representation
/-- info: 'CSD.LF2.OperationalPackage.effect_gleason_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OperationalPackage.effect_gleason_representation
/-- info: 'EndpointAudit.gleason_matrices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gleason_matrices
/-- info: 'EndpointAudit.busch_matrices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms busch_matrices

end EndpointAudit
