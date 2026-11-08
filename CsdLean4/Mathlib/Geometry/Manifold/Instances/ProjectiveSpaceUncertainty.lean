/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceGeometricTensor
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceCriticalPoints

/-!
# Uncertainty is the length of the Hamiltonian vector field

**TERM-SCOPE(Hamiltonian)** **TERM-SCOPE(Kahler)** — this module uses the vector-field sense of
"Hamiltonian" and the restricted sense of "Kähler"; `specs/TERMS.md` records what is backed.

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold.Instances`).
BACKLOG #329 (geometric QM, item 4 of the 2026-11-08 plan, first half).

The variance of an observable is the squared length, in the Fubini–Study metric, of the vector
field the observable generates: `g(X_A, X_A) = 4 (ΔA)²`, with `(ΔA)² = ⟨A²⟩ − ⟨A⟩²`. So a state
is an eigenstate exactly when `ΔA = 0`, and a Schrödinger curve `t ↦ exp(-itH) • p` moves at the
constant squared speed `4 (ΔH)²` — speed `ΔH` in the normalisation `g / 4` of the textbook
Fubini–Study metric (`ħ = 1`).

* `variance A p = ⟨A²⟩_p − ⟨A⟩_p²`; `expectation_eq_insertOne` (`⟨A⟩` in the chart of the point);
* ★★★ `fsMetric_schrodingerField_self` — **`g(X_A, X_A) = 4 (ΔA)²`** for Hermitian `A`, from the
  Provost–Vallée formula (#327): the lifted field is `-i (Aψ − (Aψ)ᵢ ψ)` and the `(Aψ)ᵢ` terms
  cancel;
* ★ `variance_nonneg`; ★★ `variance_eq_zero_iff` — **`ΔA = 0` exactly on the eigenlines of `A`**
  (#326's `schrodingerField_eq_zero_iff`);
* `variance_schrodingerUnitary_smul` — `ΔH` is conserved by the flow of `H`;
* ★★★ `fsMetric_velocity_schrodingerUnitary_smul` — **the Schrödinger curve through `p` has
  velocity `X_H` (G4) of squared length `4 (ΔH)²_p` at every time**.

## Honest scope

⚠️ **The factor is the corpus's normalisation.** `fsForm` carries the `-4` of its potential, so the
metric is `4 Re h` (#327) and the identity reads `g(X_A, X_A) = 4 (ΔA)²`; for the textbook metric
`g / 4` it is `(ΔA)²`. Nothing is rescaled.

⚠️ **The speed limit is not here.** `t ≥ arccos |⟨ψ₀|ψₜ⟩| / ΔH` needs the Fubini–Study distance
(#330); it is #331.

## References

J. Anandan, Y. Aharonov, Phys. Rev. Lett. 65 (1990) 1697; A. Ashtekar, T. A. Schilling, in *On
Einstein's Path* (1999) 23, § 3.3 (uncertainty as the length of the Hamiltonian field);
`Instances/ProjectiveSpaceGeometricTensor.lean` (#327),
`Instances/ProjectiveSpaceCriticalPoints.lean` (#326); `specs/BACKLOG.md` #329, #330, #331;
`specs/future-work.md`.
-/

@[expose] public section

open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix
open Kahler DifferentialForm

noncomputable section

namespace Projectivization

variable {n : ℕ}

/-- **The variance** `(ΔA)² = ⟨A²⟩ − ⟨A⟩²` at a ray. -/
def variance (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (p : ℙ ℂ (Ambient n)) : ℝ :=
  expectation (A * A) p - expectation A p ^ 2

/-- `⟨A⟩` read through the representative of the chart at the point. -/
theorem expectation_eq_insertOne (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (p : ℙ ℂ (Ambient n)) :
    expectation A p
      = (inner ℂ (insertOne (idx p) (chartFun (idx p) p))
          (Matrix.toEuclideanLin A (insertOne (idx p) (chartFun (idx p) p)))).re
        / ‖insertOne (idx p) (chartFun (idx p) p)‖ ^ 2 := by
  conv_lhs => rw [← chartInv_idx_chartFun p, chartInv_def]
  exact expectation_mk A _ _

/-- ★★★ **Uncertainty is the length of the Hamiltonian field**: `g(X_A, X_A) = 4 (ΔA)²`. -/
theorem fsMetric_schrodingerField_self {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) (p : ℙ ℂ (Ambient n)) :
    fsMetric p (schrodingerField A p) (schrodingerField A p) = 4 * variance A p := by
  have hT := Matrix.isSymmetric_toEuclideanLin_iff.2 hA
  set i := idx p with hidef
  set ψ := insertOne i (chartFun i p) with hψdef
  set Aψ := Matrix.toEuclideanLin A ψ with hAψdef
  set a : ℂ := (A *ᵥ ψ.ofLp) i
  have hU : insertZeroCLM i (schrodingerField A p) = (-Complex.I) • (Aψ - a • ψ) :=
    insertZeroCLM_schrodingerChartField A i (chartFun i p)
  have he := qgt_eq p (schrodingerField A p) (schrodingerField A p)
  rw [qgt_self, hU, ← hidef, ← hψdef] at he
  set N : ℝ := ‖ψ‖ ^ 2 with hNdef
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (norm_sq_insertOne_pos _ _).ne'
  have hψψ : inner ℂ ψ ψ = (N : ℂ) := by
    simp [hNdef, inner_self_eq_norm_sq_to_K]
  have hAψψ : inner ℂ Aψ ψ = inner ℂ ψ Aψ := hT ψ ψ
  have hss : inner ℂ Aψ Aψ = ((‖Aψ‖ ^ 2 : ℝ) : ℂ) := by
    simp [inner_self_eq_norm_sq_to_K]
  obtain ⟨er, her⟩ : ∃ r : ℝ, inner ℂ ψ Aψ = (r : ℂ) := by
    refine ⟨(inner ℂ ψ Aψ).re, ?_⟩
    have h := hT.coe_re_inner_apply_self ψ
    rw [hAψψ] at h
    exact h.symm
  have hvar : variance A p = ‖Aψ‖ ^ 2 / N - (er / N) ^ 2 := by
    unfold variance
    rw [expectation_eq_insertOne (A * A) p, expectation_eq_insertOne A p, ← hidef, ← hψdef,
      Matrix.toEuclideanLin_mul_apply, ← hAψdef, ← hT ψ Aψ, ← hAψdef, hss, her, ← hNdef]
    simp only [Complex.ofReal_re]
  apply Complex.ofReal_injective
  rw [he, hvar]
  simp only [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, hψψ, hAψψ, hss,
    her, map_neg, Complex.conj_I, neg_neg]
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- `g(0, 0) = 0`. -/
theorem fsMetric_zero (p : ℙ ℂ (Ambient n)) :
    fsMetric p (0 : TangentSpace (𝓘(ℝ, Fin n → ℂ)) p) 0 = 0 := by
  show fsForm p ![Complex.I • (0 : Fin n → ℂ), 0] = 0
  rw [smul_zero]
  exact (fsForm p).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)

/-- ★ **The variance is nonnegative.** -/
theorem variance_nonneg {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : A.IsHermitian)
    (p : ℙ ℂ (Ambient n)) : 0 ≤ variance A p := by
  have h := fsMetric_schrodingerField_self hA p
  by_cases hX : schrodingerField A p = 0
  · rw [hX, fsMetric_zero] at h
    linarith
  · have hpos := (fsForm_isAlmostKahler n).metric_self_pos p hX
    rw [← fsMetric_eq_metric, h] at hpos
    linarith

/-- ★★ **`ΔA = 0` exactly on the eigenlines of `A`.** -/
theorem variance_eq_zero_iff {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : A.IsHermitian)
    (p : ℙ ℂ (Ambient n)) :
    variance A p = 0 ↔ ∃ c : ℂ, Matrix.toEuclideanLin A p.rep = c • p.rep := by
  rw [← schrodingerField_eq_zero_iff]
  have h := fsMetric_schrodingerField_self hA p
  constructor
  · intro hv
    by_contra hX
    have hpos := (fsForm_isAlmostKahler n).metric_self_pos p hX
    rw [← fsMetric_eq_metric, h, hv] at hpos
    norm_num at hpos
  · intro hX
    rw [hX, fsMetric_zero] at h
    linarith

/-- `ΔH` is conserved by the flow of `H`. -/
theorem variance_schrodingerUnitary_smul {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (p : ℙ ℂ (Ambient n)) (t : ℝ) :
    variance H (Matrix.schrodingerUnitary hH t • p) = variance H p := by
  have hHH : (H * H).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, hH.eq]
  have h2 := (expectation_conserved_iff_commute hHH hH).2 (mul_assoc H H H) p t
  unfold variance
  rw [h2, expectation_schrodingerUnitary_smul hH]

/-- ★★★ **A Schrödinger curve moves at constant squared speed `4 (ΔH)²`**: the curve
`t ↦ exp(-itH) • p` has velocity `X_H` (G4), of squared length `4 (ΔH)²_p` at every time. -/
theorem fsMetric_velocity_schrodingerUnitary_smul {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (p : ℙ ℂ (Ambient n)) :
    IsMIntegralCurve (fun t : ℝ => Matrix.schrodingerUnitary hH t • p) (schrodingerField H) ∧
      ∀ t : ℝ, fsMetric (Matrix.schrodingerUnitary hH t • p)
          (schrodingerField H (Matrix.schrodingerUnitary hH t • p))
          (schrodingerField H (Matrix.schrodingerUnitary hH t • p)) = 4 * variance H p :=
  ⟨isMIntegralCurve_schrodingerUnitary_smul hH p, fun t => by
    rw [fsMetric_schrodingerField_self hH, variance_schrodingerUnitary_smul hH]⟩

end Projectivization
