/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# LF4/QubitReflection: the reflection identity on ℂ² (context-fixed qubit, A7)

**Category:** 2-LF4 (Kähler / moment-map layer — qubit context-fixed measurement).

The **reflection identity** (piece 1 of the qubit context-fixed proof, `specs/record-layer-plan.md` §2):
for unit vectors `n, ψ, φ` in `ℂ²`, with the reflection `R_n φ = 2⟨n,φ⟩·n − φ` (`= 2|n⟩⟨n| − I`),

  `‖⟨ψ,φ⟩‖² + ‖⟨ψ, R_n φ⟩‖² = 2·c·u + 2·(1−c)·(1−u)`,   `c = ‖⟨n,ψ⟩‖²`, `u = ‖⟨n,φ⟩‖²`.

In Bloch terms this is `s + s′ = 2cu + 2(1−c)(1−u)`, the `C`-term crux of §2. The proof uses the
`{n, n^⊥}` orthonormal decomposition of `ℂ²` (completeness), so that `⟨ψ,φ⟩ = P + Q`,
`⟨ψ, R_n φ⟩ = P − Q`, then the parallelogram law `‖P+Q‖² + ‖P−Q‖² = 2‖P‖² + 2‖Q‖²`, with
`‖P‖² = cu` and `‖Q‖² = (1−c)(1−u)` (the latter using that the complement of `n` is 1-dimensional —
Parseval, obtained from completeness at `φ = ψ`). Pure ℂ² linear algebra, no measure theory.
Foundational-triple, no `sorry`.

## References
`specs/record-layer-plan.md` §2 (the qubit context-fixed crux, `C`-term); `LF4/HatBox.lean` (the
hat-box + density normalisation, the single-axis ingredients).
-/

@[expose] public section

open ComplexConjugate

namespace CSD.LF4

/-- The inner product on `ℂ²` in coordinates: `⟨x,y⟩ = conj(x₀)y₀ + conj(x₁)y₁`. -/
theorem inner_two (x y : EuclideanSpace ℂ (Fin 2)) :
    (inner ℂ x y : ℂ) = conj (x 0) * y 0 + conj (x 1) * y 1 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]
  ring

/-- The orthogonal complement unit vector `n^⊥ = (−conj n₁, conj n₀)` in `ℂ²`. -/
noncomputable def perp (n : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![-conj (n 1), conj (n 0)]

@[simp] theorem perp_zero (n : EuclideanSpace ℂ (Fin 2)) : (perp n) 0 = -conj (n 1) := by
  simp [perp, WithLp.ofLp_toLp]

@[simp] theorem perp_one (n : EuclideanSpace ℂ (Fin 2)) : (perp n) 1 = conj (n 0) := by
  simp [perp, WithLp.ofLp_toLp]

/-- The unit-norm hypothesis as the complex identity `conj(n₀)n₀ + conj(n₁)n₁ = 1`. -/
theorem normSq_eq_one_of_norm (n : EuclideanSpace ℂ (Fin 2)) (hn : ‖n‖ = 1) :
    conj (n 0) * n 0 + conj (n 1) * n 1 = 1 := by
  have h := inner_two n n
  rw [inner_self_eq_norm_sq_to_K] at h
  rw [hn] at h
  simpa using h.symm

/-- **Completeness of `{n, n^⊥}` in `ℂ²`:** `⟨ψ,φ⟩ = ⟨ψ,n⟩⟨n,φ⟩ + ⟨ψ,n^⊥⟩⟨n^⊥,φ⟩` for unit `n`. -/
theorem completeness (n ψ φ : EuclideanSpace ℂ (Fin 2)) (hn : ‖n‖ = 1) :
    (inner ℂ ψ φ : ℂ)
      = inner ℂ ψ n * inner ℂ n φ + inner ℂ ψ (perp n) * inner ℂ (perp n) φ := by
  have hnorm := normSq_eq_one_of_norm n hn
  simp only [inner_two, perp_zero, perp_one, map_neg, map_mul, RingHomCompTriple.comp_apply,
    RCLike.star_def, Complex.conj_conj]
  linear_combination (-(conj (ψ 0) * φ 0 + conj (ψ 1) * φ 1)) * hnorm

/-- The inner-product norm is symmetric: `‖⟨x,y⟩‖ = ‖⟨y,x⟩‖`. -/
theorem norm_inner_comm (x y : EuclideanSpace ℂ (Fin 2)) :
    ‖inner ℂ x y‖ = ‖inner ℂ y x‖ := by
  rw [← inner_conj_symm x y, RCLike.norm_conj]

/-- **Parseval for `{n, n^⊥}`:** `‖⟨n,x⟩‖² + ‖⟨n^⊥,x⟩‖² = 1` for unit `n, x` (completeness at `x=x`). -/
theorem parseval_vec (n x : EuclideanSpace ℂ (Fin 2)) (hn : ‖n‖ = 1) (hx : ‖x‖ = 1) :
    ‖inner ℂ n x‖ ^ 2 + ‖inner ℂ (perp n) x‖ ^ 2 = 1 := by
  have hc := completeness n x x hn
  rw [← inner_conj_symm x n, ← inner_conj_symm x (perp n), RCLike.conj_mul, RCLike.conj_mul,
    inner_self_eq_norm_sq_to_K, hx] at hc
  have h2 : ‖inner ℂ n x‖ ^ 2 + ‖inner ℂ (perp n) x‖ ^ 2 = (1 : ℝ) ^ 2 := by exact_mod_cast hc.symm
  simpa using h2

/-- **The reflection identity (piece 1 of the qubit context-fixed proof).** For unit `n, ψ, φ` in
`ℂ²`, with the reflection `R_n φ = 2⟨n,φ⟩·n − φ`,
`‖⟨ψ,φ⟩‖² + ‖⟨ψ,R_nφ⟩‖² = 2·c·u + 2·(1−c)·(1−u)`, `c = ‖⟨n,ψ⟩‖²`, `u = ‖⟨n,φ⟩‖²`. The `C`-term
crux of `record-layer-plan.md` §2. Proof: completeness gives `⟨ψ,φ⟩ = P+Q`, `⟨ψ,R_nφ⟩ = P−Q`;
parallelogram; `‖P‖²=cu`, `‖Q‖²=(1−c)(1−u)` (Parseval). -/
theorem reflect_sq_add (n ψ φ : EuclideanSpace ℂ (Fin 2)) (hn : ‖n‖ = 1) (hψ : ‖ψ‖ = 1)
    (hφ : ‖φ‖ = 1) :
    ‖inner ℂ ψ φ‖ ^ 2 + ‖inner ℂ ψ ((2 * inner ℂ n φ) • n - φ)‖ ^ 2
      = 2 * (‖inner ℂ n ψ‖ ^ 2 * ‖inner ℂ n φ‖ ^ 2)
        + 2 * ((1 - ‖inner ℂ n ψ‖ ^ 2) * (1 - ‖inner ℂ n φ‖ ^ 2)) := by
  set P : ℂ := inner ℂ ψ n * inner ℂ n φ with hP
  set Q : ℂ := inner ℂ ψ (perp n) * inner ℂ (perp n) φ with hQ
  have hA : (inner ℂ ψ φ : ℂ) = P + Q := completeness n ψ φ hn
  have hR : (inner ℂ ψ ((2 * inner ℂ n φ) • n - φ) : ℂ) = P - Q := by
    rw [inner_sub_right, inner_smul_right, hA, hP]; ring
  -- ‖⟨ψ,n⟩‖ = ‖⟨n,ψ⟩‖  and Parseval-derived norms
  have hcn : ‖inner ℂ ψ n‖ = ‖inner ℂ n ψ‖ := norm_inner_comm ψ n
  have hPn : ‖P‖ ^ 2 = ‖inner ℂ n ψ‖ ^ 2 * ‖inner ℂ n φ‖ ^ 2 := by
    rw [hP, norm_mul, mul_pow, hcn]
  have hpsi : ‖inner ℂ ψ (perp n)‖ ^ 2 = 1 - ‖inner ℂ n ψ‖ ^ 2 := by
    have hp := parseval_vec n ψ hn hψ
    rw [norm_inner_comm ψ (perp n)]; linarith
  have hphi : ‖inner ℂ (perp n) φ‖ ^ 2 = 1 - ‖inner ℂ n φ‖ ^ 2 := by
    have hp := parseval_vec n φ hn hφ; linarith
  have hQn : ‖Q‖ ^ 2 = (1 - ‖inner ℂ n ψ‖ ^ 2) * (1 - ‖inner ℂ n φ‖ ^ 2) := by
    rw [hQ, norm_mul, mul_pow, hpsi, hphi]
  have hpar : ‖P + Q‖ ^ 2 + ‖P - Q‖ ^ 2 = 2 * ‖P‖ ^ 2 + 2 * ‖Q‖ ^ 2 := by
    have h := parallelogram_law_with_norm ℝ P Q
    linarith [h]
  rw [hA, hR, hpar, hPn, hQn]

end CSD.LF4
