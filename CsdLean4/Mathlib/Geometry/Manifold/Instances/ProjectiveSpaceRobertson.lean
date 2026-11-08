/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceUncertainty
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpacePoissonBracket

/-!
# The Robertson–Schrödinger uncertainty relation is Cauchy–Schwarz on `ℂℙⁿ`

**TERM-SCOPE(Hamiltonian)** **TERM-SCOPE(Kahler)** — this module uses the vector-field sense of
"Hamiltonian" and the restricted sense of "Kähler"; `specs/TERMS.md` records what is backed.

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold.Instances`).
BACKLOG #333 (geometric QM, completion item 2 of 2026-11-08).

The quantum geometric tensor `Q = g − i ω` is a positive Hermitian form, so it obeys
Cauchy–Schwarz: `g(u, v)² + ω(u, v)² ≤ g(u, u) g(v, v)`. On the Hamiltonian fields of two
observables, `g(X_A, X_A) = 4 (ΔA)²` (#329), `g(X_A, X_B) = 4 Cov(A, B)` (polarisation) and
`ω(X_A, X_B) = -2 ⟨-i[A, B]⟩` (#325), and the inequality is the Robertson–Schrödinger relation

  `Cov(A, B)² + (½ ⟨-i[A, B]⟩)² ≤ (ΔA)² (ΔB)²`,

whose second term alone is Robertson's `ΔA ΔB ≥ ½ |⟨[A, B]⟩|`.

## Cauchy–Schwarz for an almost Kähler metric

* `IsAlmostKahler.metric_add_right` / `_smul_right` / `_add_left` / `_smul_left` /
  `_zero_right` — the compatible metric is bilinear (right slot from the form, left slot by
  symmetry, so no linearity of `J` is used); `IsAlmostKahler.metric_self_nonneg`;
* ★ `IsAlmostKahler.metric_sq_le` — `g(u, v)² ≤ g(u, u) g(v, v)` (the discriminant);
* ★★ `IsAlmostKahler.metric_sq_add_apply_sq_le` — **`g(u, v)² + β(u, v)² ≤ g(u, u) g(v, v)`**,
  Cauchy–Schwarz for the Hermitian form `g − i β`, from the real one applied to `u` and
  `g(u, v) v + β(u, v) J v`.

## The uncertainty relations

* `schrodingerField_add`, `expectation_add`; `covariance A B = ½ ⟨AB + BA⟩ − ⟨A⟩⟨B⟩`,
  `covariance_self`;
* ★★ `fsMetric_schrodingerField_schrodingerField` — **`g(X_A, X_B) = 4 Cov(A, B)`**;
* ★★ `fsForm_schrodingerField` — **`ω(X_A, X_B) = -2 ⟨-i[A, B]⟩`**;
* ★★★ `covariance_sq_add_sq_le_variance_mul` — **Robertson–Schrödinger**:
  `Cov(A, B)² + (⟨-i[A, B]⟩ / 2)² ≤ (ΔA)² (ΔB)²`;
* ★★★ `abs_expectation_commObs_div_two_le` — **Robertson**: `|⟨-i[A, B]⟩| / 2 ≤ ΔA ΔB`, with
  `ΔA = √(ΔA)²`.

## Honest scope

⚠️ **Inequalities only.** The equality cases (minimum-uncertainty states: `X_B` a real-and-`J`
multiple of `X_A`) are not characterised.

⚠️ **Pure states of a finite level system.** `A`, `B` are Hermitian `(n+1) × (n+1)` matrices and the
states are rays; mixed states and unbounded operators are not here. `|⟨-i[A, B]⟩| = |⟨[A, B]⟩|`
since `⟨[A, B]⟩` is imaginary; the corpus states the real form `commObs A B = -i (AB − BA)`.

## References

H. P. Robertson, Phys. Rev. 34 (1929) 163; E. Schrödinger, Sitzungsber. Preuss. Akad. Wiss.
(1930) 296; A. Ashtekar, T. A. Schilling, in *On Einstein's Path* (1999) 23, § 3.3 (the
uncertainty relation as Cauchy–Schwarz for the Kähler structure);
`Instances/ProjectiveSpaceUncertainty.lean` (#329), `Instances/ProjectiveSpacePoissonBracket.lean`
(#325), `Instances/ProjectiveSpaceGeometricTensor.lean` (#327); `specs/BACKLOG.md` #333;
`specs/future-work.md`.
-/

@[expose] public section

open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix
open Kahler DifferentialForm

noncomputable section

namespace DifferentialForm.IsAlmostKahler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  {β : DifferentialForm (𝓘(ℝ, E)) M ∞ (Fin 2) ℝ}
  {J : ∀ x : M, TangentSpace (𝓘(ℝ, E)) x → TangentSpace (𝓘(ℝ, E)) x}

theorem metric_add_right (h : IsAlmostKahler β J) (x : M) (u a b : TangentSpace (𝓘(ℝ, E)) x) :
    h.metric x u (a + b) = h.metric x u a + h.metric x u b := by
  unfold metric
  exact apply_add_right (fun x => β x) x _ a b

theorem metric_smul_right (h : IsAlmostKahler β J) (x : M) (c : ℝ)
    (u a : TangentSpace (𝓘(ℝ, E)) x) : h.metric x u (c • a) = c * h.metric x u a := by
  unfold metric
  exact apply_smul_right (fun x => β x) x c _ a

theorem metric_add_left (h : IsAlmostKahler β J) (x : M) (a b v : TangentSpace (𝓘(ℝ, E)) x) :
    h.metric x (a + b) v = h.metric x a v + h.metric x b v := by
  rw [h.metric_comm, h.metric_add_right, h.metric_comm x v a, h.metric_comm x v b]

theorem metric_smul_left (h : IsAlmostKahler β J) (x : M) (c : ℝ)
    (a v : TangentSpace (𝓘(ℝ, E)) x) : h.metric x (c • a) v = c * h.metric x a v := by
  rw [h.metric_comm, h.metric_smul_right, h.metric_comm x v a]

theorem metric_zero_right (h : IsAlmostKahler β J) (x : M) (u : TangentSpace (𝓘(ℝ, E)) x) :
    h.metric x u 0 = 0 := by
  have h0 := h.metric_smul_right x 0 u 0
  rwa [zero_smul, zero_mul] at h0

theorem metric_self_nonneg (h : IsAlmostKahler β J) (x : M) (v : TangentSpace (𝓘(ℝ, E)) x) :
    0 ≤ h.metric x v v := by
  by_cases hv : v = 0
  · rw [hv, h.metric_zero_right]
  · exact (h.metric_self_pos x hv).le

/-- ★ **Cauchy–Schwarz for the compatible metric**: `g(u, v)² ≤ g(u, u) g(v, v)`. -/
theorem metric_sq_le (h : IsAlmostKahler β J) (x : M) (u v : TangentSpace (𝓘(ℝ, E)) x) :
    h.metric x u v ^ 2 ≤ h.metric x u u * h.metric x v v := by
  have hq : ∀ t : ℝ,
      0 ≤ h.metric x v v * (t * t) + 2 * h.metric x u v * t + h.metric x u u := by
    intro t
    have h0 := h.metric_self_nonneg x (u + t • v)
    simp only [h.metric_add_left, h.metric_add_right, h.metric_smul_left,
      h.metric_smul_right] at h0
    rw [h.metric_comm x v u] at h0
    nlinarith [h0]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith [hd]

/-- ★★ **Cauchy–Schwarz for the Hermitian form `g − i β`**:
`g(u, v)² + β(u, v)² ≤ g(u, u) g(v, v)`. -/
theorem metric_sq_add_apply_sq_le (h : IsAlmostKahler β J) (x : M)
    (u v : TangentSpace (𝓘(ℝ, E)) x) :
    h.metric x u v ^ 2 + (β x ![u, v] : ℝ) ^ 2 ≤ h.metric x u u * h.metric x v v := by
  have hw : (β x ![u, v] : ℝ) = h.metric x u (J x v) := h.apply_eq_metric x u v
  have hvJ : h.metric x v (J x v) = 0 := by
    rw [← h.apply_eq_metric]
    exact (β x).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
  have hJv : h.metric x (J x v) (J x v) = h.metric x v v := h.metric_J_J x v v
  have hub : h.metric x u (h.metric x u v • v + (β x ![u, v] : ℝ) • J x v)
      = h.metric x u v ^ 2 + (β x ![u, v] : ℝ) ^ 2 := by
    rw [h.metric_add_right, h.metric_smul_right, h.metric_smul_right, ← hw]
    ring
  have hbb : h.metric x (h.metric x u v • v + (β x ![u, v] : ℝ) • J x v)
        (h.metric x u v • v + (β x ![u, v] : ℝ) • J x v)
      = (h.metric x u v ^ 2 + (β x ![u, v] : ℝ) ^ 2) * h.metric x v v := by
    simp only [h.metric_add_left, h.metric_add_right, h.metric_smul_left, h.metric_smul_right]
    rw [h.metric_comm x (J x v) v, hvJ, hJv]
    ring
  have hcs := h.metric_sq_le x u (h.metric x u v • v + (β x ![u, v] : ℝ) • J x v)
  rw [hub, hbb] at hcs
  have huu := h.metric_self_nonneg x u
  have hvv := h.metric_self_nonneg x v
  rcases (add_nonneg (sq_nonneg (h.metric x u v)) (sq_nonneg (β x ![u, v] : ℝ))).eq_or_lt
    with h0 | hpos
  · rw [← h0]
    exact mul_nonneg huu hvv
  · refine le_of_mul_le_mul_left ?_ hpos
    nlinarith [hcs]

end DifferentialForm.IsAlmostKahler

namespace Projectivization

variable {n : ℕ}

theorem schrodingerChartField_add (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1))
    (w : Fin n → ℂ) :
    schrodingerChartField (A + B) i w
      = schrodingerChartField A i w + schrodingerChartField B i w := by
  funext j
  simp only [schrodingerChartField, Matrix.add_mulVec, Pi.add_apply]
  ring

/-- The Schrödinger field is additive in the observable. -/
theorem schrodingerField_add (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (p : ℙ ℂ (Ambient n)) :
    schrodingerField (A + B) p = schrodingerField A p + schrodingerField B p :=
  schrodingerChartField_add A B _ _

/-- The expectation value is additive in the observable. -/
theorem expectation_add (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (p : ℙ ℂ (Ambient n)) :
    expectation (A + B) p = expectation A p + expectation B p := by
  unfold expectation
  rw [map_add, LinearMap.add_apply, inner_add_right, Complex.add_re, add_div]

/-- **The symmetrised covariance** `Cov(A, B) = ½ ⟨AB + BA⟩ − ⟨A⟩⟨B⟩` at a ray. -/
def covariance (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (p : ℙ ℂ (Ambient n)) : ℝ :=
  (expectation (A * B) p + expectation (B * A) p) / 2 - expectation A p * expectation B p

theorem covariance_self (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (p : ℙ ℂ (Ambient n)) :
    covariance A A p = variance A p := by
  unfold covariance variance
  ring

/-- ★★ **The metric on two Hamiltonian fields is the covariance**: `g(X_A, X_B) = 4 Cov(A, B)`. -/
theorem fsMetric_schrodingerField_schrodingerField {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (p : ℙ ℂ (Ambient n)) :
    fsMetric p (schrodingerField A p) (schrodingerField B p) = 4 * covariance A B p := by
  have h := fsMetric_schrodingerField_self (hA.add hB) p
  have hA' := fsMetric_schrodingerField_self hA p
  have hB' := fsMetric_schrodingerField_self hB p
  rw [schrodingerField_add] at h
  rw [fsMetric_eq_metric] at h hA' hB' ⊢
  rw [(fsForm_isAlmostKahler n).metric_add_left, (fsForm_isAlmostKahler n).metric_add_right,
    (fsForm_isAlmostKahler n).metric_add_right,
    (fsForm_isAlmostKahler n).metric_comm p (schrodingerField B p) (schrodingerField A p)] at h
  have hv : variance (A + B) p = variance A p + variance B p + 2 * covariance A B p := by
    unfold variance covariance
    rw [add_mul, mul_add, mul_add]
    simp only [expectation_add]
    ring
  rw [hv] at h
  linarith

/-- ★★ **The form on two Hamiltonian fields is the commutator**: `ω(X_A, X_B) = -2 ⟨-i[A, B]⟩`. -/
theorem fsForm_schrodingerField {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (p : ℙ ℂ (Ambient n)) :
    (fsForm p ![schrodingerField A p, schrodingerField B p] : ℝ)
      = -2 * expectation (commObs A B) p := by
  refine (schrodingerField_isHamiltonianVectorField hA p (schrodingerField B p)).trans ?_
  have h := mfderiv_apply_eq_of_hasDerivAt (isMIntegralCurve_schrodingerUnitary_smul hB p)
    (t := 0) (((contMDiff_schrodingerHamiltonian (m := 1) A) _).mdifferentiableAt (by simp))
    ((hasDerivAt_expectation_schrodingerUnitary_smul hB A p).const_mul (-2))
  rw [schrodingerUnitary_zero_smul hB] at h
  exact h

/-- ★★★ **The Robertson–Schrödinger uncertainty relation**:
`Cov(A, B)² + (⟨-i[A, B]⟩ / 2)² ≤ (ΔA)² (ΔB)²`, Cauchy–Schwarz for the geometric tensor on the
Hamiltonian fields of `A` and `B`. -/
theorem covariance_sq_add_sq_le_variance_mul {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (p : ℙ ℂ (Ambient n)) :
    covariance A B p ^ 2 + (expectation (commObs A B) p / 2) ^ 2
      ≤ variance A p * variance B p := by
  have h := (fsForm_isAlmostKahler n).metric_sq_add_apply_sq_le p (schrodingerField A p)
    (schrodingerField B p)
  rw [← fsMetric_eq_metric, fsMetric_schrodingerField_schrodingerField hA hB,
    fsMetric_schrodingerField_self hA, fsMetric_schrodingerField_self hB,
    fsForm_schrodingerField hA hB] at h
  nlinarith [h]

/-- Robertson's relation squared: `(⟨-i[A, B]⟩ / 2)² ≤ (ΔA)² (ΔB)²`. -/
theorem expectation_commObs_div_two_sq_le {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (p : ℙ ℂ (Ambient n)) :
    (expectation (commObs A B) p / 2) ^ 2 ≤ variance A p * variance B p := by
  nlinarith [covariance_sq_add_sq_le_variance_mul hA hB p, sq_nonneg (covariance A B p)]

/-- ★★★ **Robertson's uncertainty relation**: `|⟨-i[A, B]⟩| / 2 ≤ ΔA ΔB`. -/
theorem abs_expectation_commObs_div_two_le {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (p : ℙ ℂ (Ambient n)) :
    |expectation (commObs A B) p| / 2 ≤ √(variance A p) * √(variance B p) := by
  have h := Real.abs_le_sqrt (expectation_commObs_div_two_sq_le hA hB p)
  rwa [abs_div, abs_two, Real.sqrt_mul (variance_nonneg hA p)] at h

end Projectivization
