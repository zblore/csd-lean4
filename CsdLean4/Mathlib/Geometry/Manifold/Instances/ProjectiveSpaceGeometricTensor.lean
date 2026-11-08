/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudyRiemannian
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceSchrodingerFlow

/-!
# The quantum geometric tensor of `ℂℙⁿ`

**TERM-SCOPE(Kahler)** — this module uses the restricted sense of "Kähler"; `specs/TERMS.md`
records what is backed.

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold.Instances`).
BACKLOG #327 (geometric QM, item 6 of the 2026-11-08 plan).

The Fubini–Study metric `g` and the Fubini–Study form `ω` are the real and imaginary parts of one
Hermitian form on each tangent space, the **quantum geometric tensor** `Q = g − i ω`. Provost and
Vallée's formula reads it off the state: with `ψ` a representative of the point and `U`, `V` the
tangent vectors lifted to the ambient space,
`Q(u, v) = 4 ⟪U, (1 − |ψ⟩⟨ψ| / ‖ψ‖²) V⟫ / ‖ψ‖²` — the metric is its real part and the Berry
curvature its imaginary part.

* `qgt x u v = g(u, v) − i ω(u, v)`; `qgt_re` (the metric), `qgt_im` (minus the form);
* `fsModelForm_qgt` — the computation in the model;
* ★★★ `qgt_eq` — **Provost–Vallée**: `Q(u, v) = 4 (⟪U, V⟫ / ‖ψ‖² − ⟪U, ψ⟫ ⟪ψ, V⟫ / ‖ψ‖⁴)` in the
  chart at the point, `ψ = insertOne i w`, `U = insertZeroCLM i u`;
* ★★ `qgt_eq_inner_proj` — the same with the projector: `4 ⟪U, V − (⟪ψ, V⟫ / ‖ψ‖²) ψ⟫ / ‖ψ‖²`;
* ★ `qgt_conj` — **Hermitian**: `conj Q(u, v) = Q(v, u)`;
* `qgt_self` (`Q(u, u) = g(u, u)`), ★ `qgt_self_re_pos` — positive definite.

## Honest scope

⚠️ **The sign and the factor are conventions.** With the corpus's `fsForm` (the `-4` of its
potential) the metric is `4 Re h` and the form is `-4 Im h` for the sesquilinear
`h = ⟪U, (1 − P_ψ) V⟫ / ‖ψ‖²`, so the Hermitian combination is `g − i ω = 4 h`. The textbook
`Q = g + i ω` has the opposite sign of `ω`; nothing is rescaled here.

⚠️ **One chart.** The formula is read in the chart of the point itself (`idx x`), the chart in
which the manifold's tangent space is identified with the model; a change of chart moves `ψ` and
the lifts together and is not restated.

## References

J. P. Provost, G. Vallée, Commun. Math. Phys. 76 (1980) 289; A. Ashtekar, T. A. Schilling, in *On
Einstein's Path* (1999) 23, § 3; `Instances/ProjectiveSpaceFubiniStudyRiemannian.lean` (`fsMetric`),
`Instances/ProjectiveSpaceFubiniStudyMass.lean` (`fsModelForm_apply`),
`Instances/ProjectiveSpaceSchrodingerFlow.lean` (the lifts); `specs/BACKLOG.md` #327;
`specs/future-work.md`.
-/

@[expose] public section

open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Kahler DifferentialForm

noncomputable section

namespace Projectivization

variable {n : ℕ}

/-- **The quantum geometric tensor** `Q(u, v) = g(u, v) − i ω(u, v)` on the tangent space of
`ℂℙⁿ` at `x`. -/
def qgt (x : ℙ ℂ (Ambient n)) (u v : TangentSpace (𝓘(ℝ, Fin n → ℂ)) x) : ℂ :=
  (fsMetric x u v : ℂ) - Complex.I * (fsForm x ![u, v] : ℝ)

theorem qgt_re (x : ℙ ℂ (Ambient n)) (u v : TangentSpace (𝓘(ℝ, Fin n → ℂ)) x) :
    (qgt x u v).re = fsMetric x u v := by
  simp [qgt]

theorem qgt_im (x : ℙ ℂ (Ambient n)) (u v : TangentSpace (𝓘(ℝ, Fin n → ℂ)) x) :
    (qgt x u v).im = -(fsForm x ![u, v] : ℝ) := by
  simp [qgt]

/-- The model computation: `ω_w(i u, v) − i ω_w(u, v)` against the lifts to the chart `i`. -/
theorem fsModelForm_qgt (i : Fin (n + 1)) (w u v : Fin n → ℂ) :
    ((fsModelForm w ![Complex.I • u, v] : ℝ) : ℂ) - Complex.I * (fsModelForm w ![u, v] : ℝ)
      = 4 * (inner ℂ (insertZeroCLM i u) (insertZeroCLM i v) / (‖insertOne i w‖ ^ 2 : ℝ)
          - inner ℂ (insertZeroCLM i u) (insertOne i w)
              * inner ℂ (insertOne i w) (insertZeroCLM i v)
            / ((‖insertOne i w‖ ^ 2) ^ 2 : ℝ)) := by
  rw [inner_insertZeroCLM_insertZeroCLM, inner_insertZeroCLM_insertOne,
    inner_insertOne_insertZeroCLM, norm_sq_insertOne_toLpCLM]
  have hI : toLpCLM (Complex.I • u) = Complex.I • toLpCLM u := rfl
  rw [fsModelForm_apply, fsModelForm_apply, hI]
  simp only [inner_smul_left, Complex.conj_I]
  have ht : (1 + ‖toLpCLM w‖ ^ 2 : ℝ) ≠ 0 := by positivity
  apply Complex.ext <;>
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.div_ofReal_re,
    Complex.div_ofReal_im, Complex.neg_re, Complex.neg_im, Complex.re_ofNat, Complex.im_ofNat] <;>
  field_simp <;>
  ring

/-- ★★★ **Provost–Vallée**: `Q(u, v) = 4 (⟪U, V⟫ / ‖ψ‖² − ⟪U, ψ⟫ ⟪ψ, V⟫ / ‖ψ‖⁴)`, read in the chart
of the point. -/
theorem qgt_eq (x : ℙ ℂ (Ambient n)) (u v : TangentSpace (𝓘(ℝ, Fin n → ℂ)) x) :
    qgt x u v
      = 4 * (inner ℂ (insertZeroCLM (idx x) u) (insertZeroCLM (idx x) v)
            / (‖insertOne (idx x) (chartFun (idx x) x)‖ ^ 2 : ℝ)
          - inner ℂ (insertZeroCLM (idx x) u) (insertOne (idx x) (chartFun (idx x) x))
            * inner ℂ (insertOne (idx x) (chartFun (idx x) x)) (insertZeroCLM (idx x) v)
            / ((‖insertOne (idx x) (chartFun (idx x) x)‖ ^ 2) ^ 2 : ℝ)) :=
  fsModelForm_qgt (idx x) (chartFun (idx x) x) u v

/-- ★★ **Provost–Vallée with the projector**: `Q(u, v) = 4 ⟪U, (1 − P_ψ) V⟫ / ‖ψ‖²`. -/
theorem qgt_eq_inner_proj (x : ℙ ℂ (Ambient n)) (u v : TangentSpace (𝓘(ℝ, Fin n → ℂ)) x) :
    qgt x u v
      = 4 * inner ℂ (insertZeroCLM (idx x) u)
            (insertZeroCLM (idx x) v
              - (inner ℂ (insertOne (idx x) (chartFun (idx x) x)) (insertZeroCLM (idx x) v)
                  / (‖insertOne (idx x) (chartFun (idx x) x)‖ ^ 2 : ℝ))
                • insertOne (idx x) (chartFun (idx x) x))
          / (‖insertOne (idx x) (chartFun (idx x) x)‖ ^ 2 : ℝ) := by
  rw [qgt_eq, inner_sub_right, inner_smul_right]
  have hψ : (‖insertOne (idx x) (chartFun (idx x) x)‖ ^ 2 : ℝ) ≠ 0 :=
    (norm_sq_insertOne_pos _ _).ne'
  push_cast
  ring

/-- ★ **The tensor is Hermitian**: `conj Q(u, v) = Q(v, u)`. -/
theorem qgt_conj (x : ℙ ℂ (Ambient n)) (u v : TangentSpace (𝓘(ℝ, Fin n → ℂ)) x) :
    (starRingEnd ℂ) (qgt x u v) = qgt x v u := by
  rw [qgt_eq, qgt_eq]
  simp only [map_mul, map_sub, map_div₀, Complex.conj_ofReal, inner_conj_symm, map_ofNat]
  ring

/-- On the diagonal the tensor is the metric. -/
theorem qgt_self (x : ℙ ℂ (Ambient n)) (u : TangentSpace (𝓘(ℝ, Fin n → ℂ)) x) :
    qgt x u u = (fsMetric x u u : ℂ) := by
  have h0 : (fsSection x ![u, u] : ℝ) = 0 :=
    (fsSection x).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
  simp [qgt, h0]

/-- ★ **The tensor is positive definite.** -/
theorem qgt_self_re_pos (x : ℙ ℂ (Ambient n)) {u : TangentSpace (𝓘(ℝ, Fin n → ℂ)) x}
    (hu : u ≠ 0) : 0 < (qgt x u u).re := by
  rw [qgt_re, fsMetric_eq_metric]
  exact (fsForm_isAlmostKahler n).metric_self_pos x hu

end Projectivization
