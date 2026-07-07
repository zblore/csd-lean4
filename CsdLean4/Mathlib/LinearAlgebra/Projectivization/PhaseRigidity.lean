import CsdLean4.Mathlib.LinearAlgebra.Projectivization.TransitionProbability
import Mathlib.LinearAlgebra.Center

/-!
# Phase rigidity: unitaries with the same projective action differ by a phase

**Category:** 1-Mathlib (CSD-free Mathlib upstream candidate).

Two matrix unitaries acting identically on every point of complex projective
space are equal up to a global unit-modulus scalar (a "phase"). This is the
uniqueness half of the projective-representation dictionary: the kernel of
`U(N) → PU(N)` is the circle `U(1) · 1`.

## Main results

- `Matrix.UnitaryGroup.unit_smul_mem` : a unit-modulus scalar multiple of a
  unitary matrix is unitary (the circle acts on `unitaryGroup (Fin N) ℂ`).
- `Projectivization.smul_eq_smul_of_eq_smul` : unitaries whose matrices
  differ by a scalar act identically on `ℙ ℂ (EuclideanSpace ℂ (Fin N))`
  (scalars act trivially on rays).
- `Projectivization.exists_unit_smul_of_smul_eq_smul` (**phase rigidity**):
  conversely, if `A • p = B • p` for every projective point `p`, then
  `A = c • B` as matrices for some `c : ℂ` with `‖c‖ = 1`.

## Proof sketch (rigidity)

`C := B⁻¹ * A` fixes every ray, so every nonzero vector is an eigenvector of
the induced endomorphism `toEuclideanLin C`. An endomorphism of a free module
over a commutative domain all of whose vectors are eigenvectors is a homothety
(`LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent`, Mathlib), so
`C = a • 1`; unitarity of `C` forces `star a * a = 1`, i.e. `‖a‖ = 1`.
The degenerate `N = 0` case is handled separately (`Matrix (Fin 0) (Fin 0) ℂ`
is a subsingleton, so `c = 1` works).

**Provenance.** Needed by the CSD dynamics spine W5-S1
(`CsdLean4/LF4/PhaseLift.lean`): extracting the `U(1)` phase cocycle of the
one-parameter unitary family realising a projected Kähler-sector flow, the
first step of the projective-to-vector phase lift.

## Tags

projectivization, unitary group, projective representation, phase, rigidity
-/

open scoped LinearAlgebra.Projectivization
open Matrix

namespace Matrix.UnitaryGroup

variable {N : ℕ}

/-- A unit-modulus scalar multiple of a unitary matrix is unitary: the circle
`U(1)` acts on `unitaryGroup (Fin N) ℂ` by scalar multiplication. -/
theorem unit_smul_mem {c : ℂ} (hc : ‖c‖ = 1) {M : Matrix (Fin N) (Fin N) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    c • M ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hM ⊢
  rw [star_smul, smul_mul_smul_comm, hM]
  have hcc : star c * c = 1 := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      hc, one_pow, Complex.ofReal_one]
  rw [hcc, one_smul]

end Matrix.UnitaryGroup

namespace Projectivization

variable {N : ℕ}

/-- Unitaries whose matrices differ by a scalar act identically on
projective space: scalars act trivially on rays. This is the easy (descent)
direction of phase rigidity. (No nonzero hypothesis on `c` is needed: for
`N ≥ 1` a unitary is nonzero, so `c = 0` is vacuous, and for `N = 0` the
statement is trivial.) -/
theorem smul_eq_smul_of_eq_smul {c : ℂ}
    {A B : Matrix.unitaryGroup (Fin N) ℂ}
    (hAB : (A : Matrix (Fin N) (Fin N) ℂ) = c • (B : Matrix (Fin N) (Fin N) ℂ))
    (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    A • p = B • p := by
  conv_lhs => rw [← p.mk_rep]
  conv_rhs => rw [← p.mk_rep]
  rw [smul_mk_eq_mk_toEuclideanLin A p.rep_nonzero,
    smul_mk_eq_mk_toEuclideanLin B p.rep_nonzero,
    mk_eq_mk_iff']
  refine ⟨c, ?_⟩
  rw [hAB, map_smul, LinearMap.smul_apply]

/-- **Phase rigidity.** Two unitaries acting identically on every point of
`ℙ ℂ (EuclideanSpace ℂ (Fin N))` are equal up to a global unit-modulus phase:
`A = c • B` as matrices with `‖c‖ = 1`. Equivalently, the kernel of
`U(N) → PU(N)` is the circle of phases.

Route: `C := B⁻¹ * A` fixes every ray, so every nonzero vector is an
eigenvector of `toEuclideanLin C`; by
`LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent` such an
endomorphism is a homothety `a • 1`, and unitarity pins `‖a‖ = 1`. -/
theorem exists_unit_smul_of_smul_eq_smul
    (A B : Matrix.unitaryGroup (Fin N) ℂ)
    (h : ∀ p : ℙ ℂ (EuclideanSpace ℂ (Fin N)), A • p = B • p) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      (A : Matrix (Fin N) (Fin N) ℂ) = c • (B : Matrix (Fin N) (Fin N) ℂ) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · -- Degenerate case: `Matrix (Fin 0) (Fin 0) ℂ` is a subsingleton.
    subst hN
    exact ⟨1, norm_one, by rw [one_smul]; exact Matrix.ext fun i _ => i.elim0⟩
  -- `C := B⁻¹ * A` fixes every ray.
  have hCfix : ∀ p : ℙ ℂ (EuclideanSpace ℂ (Fin N)), (B⁻¹ * A) • p = p := by
    intro p
    rw [SemigroupAction.mul_smul, h p, ← SemigroupAction.mul_smul,
      inv_mul_cancel, one_smul]
  -- Hence every nonzero vector is an eigenvector of the induced endomorphism.
  set f : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
    Matrix.toEuclideanLin
      ((B⁻¹ * A : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
    with hf
  have hdep : ∀ v : EuclideanSpace ℂ (Fin N), ¬ LinearIndependent ℂ ![v, f v] := by
    intro v
    by_cases hv : v = 0
    · intro hli
      exact hli.ne_zero 0 (by rw [Matrix.cons_val_zero, hv])
    · have hmk := hCfix (Projectivization.mk ℂ v hv)
      rw [smul_mk_eq_mk_toEuclideanLin (B⁻¹ * A) hv, mk_eq_mk_iff] at hmk
      obtain ⟨a, ha⟩ := hmk
      rw [Units.smul_def] at ha
      intro hli
      exact (LinearIndependent.pair_iff' hv).mp hli (a : ℂ) ha
  -- Homothety: `f = a • 1`, transported back to the matrix level.
  obtain ⟨a, hfa⟩ :=
    LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hdep
  have hCmat : ((B⁻¹ * A : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
      = a • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    apply Matrix.toEuclideanLin.injective
    rw [map_smul, ← hf, hfa]
    congr 1
    exact (Matrix.toLpLin_one 2).symm
  -- Unitarity of `C` pins the modulus: `star a * a = 1`.
  have i₀ : Fin N := ⟨0, hN⟩
  have hCunit : star ((B⁻¹ * A : Matrix.unitaryGroup (Fin N) ℂ)
        : Matrix (Fin N) (Fin N) ℂ)
      * ((B⁻¹ * A : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
      = 1 := Unitary.coe_star_mul_self _
  rw [hCmat, star_smul, star_one, smul_mul_smul_comm, one_mul] at hCunit
  have haa : star a * a = 1 := by
    have := congrFun (congrFun hCunit i₀) i₀
    simpa [Matrix.smul_apply, Matrix.one_apply_eq] using this
  have hnorm : ‖a‖ = 1 := by
    have hsq : ‖a‖ ^ 2 = 1 := by
      have : (Complex.normSq a : ℂ) = 1 := by
        rw [← Complex.mul_conj, mul_comm, ← Complex.star_def, haa]
      rw [← Complex.normSq_eq_norm_sq]
      exact_mod_cast this
    calc ‖a‖ = Real.sqrt (‖a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg a)).symm
      _ = 1 := by rw [hsq, Real.sqrt_one]
  -- Assemble: `A = B * C = a • B`.
  refine ⟨a, hnorm, ?_⟩
  have hBC : (B * (B⁻¹ * A) : Matrix.unitaryGroup (Fin N) ℂ) = A := by
    rw [mul_inv_cancel_left]
  calc (A : Matrix (Fin N) (Fin N) ℂ)
      = ((B * (B⁻¹ * A) : Matrix.unitaryGroup (Fin N) ℂ)
          : Matrix (Fin N) (Fin N) ℂ) := by rw [hBC]
    _ = (B : Matrix (Fin N) (Fin N) ℂ)
          * ((B⁻¹ * A : Matrix.unitaryGroup (Fin N) ℂ)
              : Matrix (Fin N) (Fin N) ℂ) := by
        exact_mod_cast rfl
    _ = a • (B : Matrix (Fin N) (Fin N) ℂ) := by
        rw [hCmat, mul_smul_comm, mul_one]

end Projectivization
