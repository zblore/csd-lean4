/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Empirical/QM/KCBS: the Klyachko–Can–Binicioğlu–Shumovsky pentagon (state-dependent contextuality)

The **KCBS inequality** is the simplest *state-dependent* contextuality test — the qutrit analogue of
Bell/CHSH, on the pentagon graph `C₅`. Five rank-1 projectors `Π₀,…,Π₄` on `ℂ³` are arranged so that
*consecutive* ones (cyclically) are orthogonal (mutually exclusive outcomes). Any **noncontextual**
hidden-variable model assigns each `Πᵢ` a definite value in `{0,1}` respecting the exclusivity, and
then

  `K₅ := ∑ᵢ ⟨Πᵢ⟩ ≤ 2`

— because the independence number of the 5-cycle `C₅` is `2` (no three of five cyclically-arranged
vertices are pairwise non-adjacent). Quantum mechanics reaches `√5 ≈ 2.236 > 2` on the pentagon
"apex" state, violating noncontextuality.

This module proves the **noncontextual bound** over a *genuine measure-theoretic* model (five `{0,1}`
observables with cyclic exclusivity on a probability space), mirroring the CHSH-LHV / Leggett–Garg
pattern:

* `kcbs_pointwise` — the `C₅` combinatorial core: `∑ xᵢ ≤ 2` for `xᵢ ∈ {0,1}` with `xᵢ·xᵢ₊₁ = 0`.
* `kcbs_noncontextual_bound` — `∑ᵢ ∫ Xᵢ ≤ 2` for any such model.

The quantum `√5` violation (the pentagon `ℂ³` vectors + golden-ratio orthogonality) is a separate,
heavier construction and is *not* in this module.

**Experimental verification:** Lapkiewicz et al. 2011 (single photons, three-level).
**CSD note:** KCBS is *state-dependent* contextuality — Gleason/KS-style noncontextuality is exactly
the assumption CSD's contextual (apparatus-fixed) outcome regions deny, so CSD is unconstrained by it.

## References
`Empirical/QM/Crypto/E91.lean` (the LHV-bound measure-theoretic pattern);
`Empirical/QM/LeggettGarg.lean` (the pointwise-inequality + `integral_mono` pattern);
`Empirical/CSD/Contextuality/KS18.lean` (state-*independent* contextuality, for contrast).
-/

@[expose] public section

open MeasureTheory

namespace CSD.Empirical.QM.KCBS

/-- **The pentagon (`C₅`) combinatorial core.** For five `{0,1}` values with cyclic
consecutive-exclusivity `xᵢ·xᵢ₊₁ = 0`, at most two can be `1`: `∑ xᵢ ≤ 2` (the independence number of
`C₅`). -/
lemma kcbs_pointwise {x₀ x₁ x₂ x₃ x₄ : ℝ}
    (h₀ : x₀ = 0 ∨ x₀ = 1) (h₁ : x₁ = 0 ∨ x₁ = 1) (h₂ : x₂ = 0 ∨ x₂ = 1)
    (h₃ : x₃ = 0 ∨ x₃ = 1) (h₄ : x₄ = 0 ∨ x₄ = 1)
    (e₀ : x₀ * x₁ = 0) (e₁ : x₁ * x₂ = 0) (e₂ : x₂ * x₃ = 0) (e₃ : x₃ * x₄ = 0)
    (e₄ : x₄ * x₀ = 0) :
    x₀ + x₁ + x₂ + x₃ + x₄ ≤ 2 := by
  rcases h₀ with h₀ | h₀ <;> rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;>
    rcases h₃ with h₃ | h₃ <;> rcases h₄ with h₄ | h₄ <;>
    subst_vars <;> simp_all <;> norm_num

/-- **The KCBS noncontextual bound `K₅ ≤ 2`.** For any noncontextual model — a probability space with
five `{0,1}`-valued observables `X₀,…,X₄` obeying cyclic exclusivity `Xᵢ·Xᵢ₊₁ = 0` — the pentagon sum
`∑ᵢ ⟨Xᵢ⟩ ≤ 2`. Proved from the `C₅` pointwise bound by integral monotonicity. -/
theorem kcbs_noncontextual_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X₀ X₁ X₂ X₃ X₄ : Ω → ℝ)
    (h₀ : ∀ ω, X₀ ω = 0 ∨ X₀ ω = 1) (h₁ : ∀ ω, X₁ ω = 0 ∨ X₁ ω = 1)
    (h₂ : ∀ ω, X₂ ω = 0 ∨ X₂ ω = 1) (h₃ : ∀ ω, X₃ ω = 0 ∨ X₃ ω = 1)
    (h₄ : ∀ ω, X₄ ω = 0 ∨ X₄ ω = 1)
    (e₀ : ∀ ω, X₀ ω * X₁ ω = 0) (e₁ : ∀ ω, X₁ ω * X₂ ω = 0) (e₂ : ∀ ω, X₂ ω * X₃ ω = 0)
    (e₃ : ∀ ω, X₃ ω * X₄ ω = 0) (e₄ : ∀ ω, X₄ ω * X₀ ω = 0)
    (i₀ : Integrable X₀ μ) (i₁ : Integrable X₁ μ) (i₂ : Integrable X₂ μ)
    (i₃ : Integrable X₃ μ) (i₄ : Integrable X₄ μ) :
    (∫ ω, X₀ ω ∂μ) + (∫ ω, X₁ ω ∂μ) + (∫ ω, X₂ ω ∂μ) + (∫ ω, X₃ ω ∂μ) + (∫ ω, X₄ ω ∂μ) ≤ 2 := by
  have hcomb : (∫ ω, X₀ ω ∂μ) + (∫ ω, X₁ ω ∂μ) + (∫ ω, X₂ ω ∂μ) + (∫ ω, X₃ ω ∂μ)
        + (∫ ω, X₄ ω ∂μ)
      = ∫ ω, (X₀ ω + X₁ ω + X₂ ω + X₃ ω + X₄ ω) ∂μ := by
    rw [integral_add (f := fun ω => X₀ ω + X₁ ω + X₂ ω + X₃ ω) (g := X₄)
          (((i₀.add i₁).add i₂).add i₃) i₄,
      integral_add (f := fun ω => X₀ ω + X₁ ω + X₂ ω) (g := X₃) ((i₀.add i₁).add i₂) i₃,
      integral_add (f := fun ω => X₀ ω + X₁ ω) (g := X₂) (i₀.add i₁) i₂,
      integral_add (f := X₀) (g := X₁) i₀ i₁]
  rw [hcomb]
  calc ∫ ω, (X₀ ω + X₁ ω + X₂ ω + X₃ ω + X₄ ω) ∂μ
      ≤ ∫ _ω, (2 : ℝ) ∂μ :=
        integral_mono ((((i₀.add i₁).add i₂).add i₃).add i₄) (integrable_const 2)
          (fun ω => kcbs_pointwise (h₀ ω) (h₁ ω) (h₂ ω) (h₃ ω) (h₄ ω)
            (e₀ ω) (e₁ ω) (e₂ ω) (e₃ ω) (e₄ ω))
    _ = 2 := by rw [integral_const]; simp

/-! ### The quantum `√5` violation — the pentagon on `ℝ³` -/

open Real in
/-- `cos θ` for the pentagon apex angle, with `cos²θ = 1/√5`. -/
noncomputable def cc : ℝ := Real.sqrt (1 / Real.sqrt 5)

/-- `sin θ`, with `sin²θ = 1 − 1/√5`. -/
noncomputable def ss : ℝ := Real.sqrt (1 - 1 / Real.sqrt 5)

lemma sqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)

lemma sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

lemma one_le_sqrt5 : (1 : ℝ) ≤ Real.sqrt 5 := by
  rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

lemma cc_sq : cc ^ 2 = 1 / Real.sqrt 5 := Real.sq_sqrt (by positivity)

lemma ss_sq : ss ^ 2 = 1 - 1 / Real.sqrt 5 := by
  refine Real.sq_sqrt ?_
  rw [sub_nonneg, div_le_one sqrt5_pos]; exact one_le_sqrt5

/-- A pentagon unit vector at azimuthal angle `a`: `(sinθ·cos a, sinθ·sin a, cosθ)`. -/
noncomputable def kvA (a : ℝ) : Fin 3 → ℝ := ![ss * Real.cos a, ss * Real.sin a, cc]

/-- The apex state `|ψ⟩ = (0,0,1)`. -/
def apex : Fin 3 → ℝ := ![0, 0, 1]

/-- Real 3-vector dot product. -/
def dot3 (u v : Fin 3 → ℝ) : ℝ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- The five pentagon azimuths `4πk/5`. -/
noncomputable def ang : Fin 5 → ℝ := ![0, 4 * Real.pi / 5, 8 * Real.pi / 5,
  12 * Real.pi / 5, 16 * Real.pi / 5]

/-- The five KCBS pentagon vectors. -/
noncomputable def kv (k : Fin 5) : Fin 3 → ℝ := kvA (ang k)

/-- The dot product of two pentagon vectors folds to `sin²θ·cos(a−b) + cos²θ`. -/
lemma dot_kvA (a b : ℝ) : dot3 (kvA a) (kvA b) = ss ^ 2 * Real.cos (a - b) + cc ^ 2 := by
  simp only [dot3, kvA, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [Real.cos_sub]; ring

/-- `cos(4π/5) = −(1+√5)/4`. -/
lemma cos_4pi5 : Real.cos (4 * Real.pi / 5) = -(1 + Real.sqrt 5) / 4 := by
  rw [show (4 * Real.pi / 5 : ℝ) = Real.pi - Real.pi / 5 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_five]
  ring

/-- Orthogonality from the folded dot product: if `cos(a−b) = cos(4π/5)` then the vectors are
orthogonal (the pentagon overlap identity, using `√5² = 5`). -/
lemma orth_of_cos {a b : ℝ} (h : Real.cos (a - b) = -(1 + Real.sqrt 5) / 4) :
    dot3 (kvA a) (kvA b) = 0 := by
  rw [dot_kvA, h, ss_sq, cc_sq]
  have key : (1 - 1 / Real.sqrt 5) * (-(1 + Real.sqrt 5) / 4) + 1 / Real.sqrt 5
      = (5 - Real.sqrt 5 ^ 2) / (4 * Real.sqrt 5) := by
    field_simp
    ring
  rw [key, sqrt5_sq]; norm_num

/-- **Consecutive pentagon vectors are orthogonal** (the exclusivity structure). Each cyclic
azimuth gap reduces to `cos(4π/5)`. -/
lemma kv_orth (k : Fin 5) : dot3 (kv k) (kv (k + 1)) = 0 := by
  have hneg : Real.cos (-(4 * Real.pi / 5)) = -(1 + Real.sqrt 5) / 4 := by
    rw [Real.cos_neg]; exact cos_4pi5
  have hwrap : Real.cos (16 * Real.pi / 5) = -(1 + Real.sqrt 5) / 4 := by
    rw [show (16 * Real.pi / 5 : ℝ) = -(4 * Real.pi / 5) + 2 * Real.pi + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_add_two_pi]
    exact hneg
  fin_cases k
  · refine orth_of_cos ?_
    show Real.cos (0 - 4 * Real.pi / 5) = -(1 + Real.sqrt 5) / 4
    rw [show (0 - 4 * Real.pi / 5 : ℝ) = -(4 * Real.pi / 5) by ring]; exact hneg
  · refine orth_of_cos ?_
    show Real.cos (4 * Real.pi / 5 - 8 * Real.pi / 5) = -(1 + Real.sqrt 5) / 4
    rw [show (4 * Real.pi / 5 - 8 * Real.pi / 5 : ℝ) = -(4 * Real.pi / 5) by ring]; exact hneg
  · refine orth_of_cos ?_
    show Real.cos (8 * Real.pi / 5 - 12 * Real.pi / 5) = -(1 + Real.sqrt 5) / 4
    rw [show (8 * Real.pi / 5 - 12 * Real.pi / 5 : ℝ) = -(4 * Real.pi / 5) by ring]; exact hneg
  · refine orth_of_cos ?_
    show Real.cos (12 * Real.pi / 5 - 16 * Real.pi / 5) = -(1 + Real.sqrt 5) / 4
    rw [show (12 * Real.pi / 5 - 16 * Real.pi / 5 : ℝ) = -(4 * Real.pi / 5) by ring]; exact hneg
  · refine orth_of_cos ?_
    show Real.cos (16 * Real.pi / 5 - 0) = -(1 + Real.sqrt 5) / 4
    rw [sub_zero]; exact hwrap

/-- Each pentagon vector is a unit vector. -/
lemma kv_unit (k : Fin 5) : dot3 (kv k) (kv k) = 1 := by
  rw [kv, dot_kvA, sub_self, Real.cos_zero, mul_one, ss_sq, cc_sq]; ring

/-- The apex overlap Born weight `⟨ψ|Πₖ|ψ⟩ = cos²θ = 1/√5`. -/
lemma kv_apex_born (k : Fin 5) : (dot3 apex (kv k)) ^ 2 = 1 / Real.sqrt 5 := by
  have : dot3 apex (kv k) = cc := by
    simp [dot3, apex, kv, kvA, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [this, cc_sq]

/-- **The quantum KCBS value is `√5`.** `∑ₖ ⟨ψ|Πₖ|ψ⟩ = 5·(1/√5) = √5`. -/
theorem kcbs_qm_value : ∑ k : Fin 5, (dot3 apex (kv k)) ^ 2 = Real.sqrt 5 := by
  simp only [kv_apex_born]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div,
    div_eq_iff sqrt5_pos.ne', Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  norm_num

/-- **The quantum violation `K₅ = √5 > 2`.** The pentagon apex state exceeds the noncontextual
bound `2`, so quantum mechanics violates KCBS noncontextuality. -/
theorem kcbs_quantum_violation : (2 : ℝ) < ∑ k : Fin 5, (dot3 apex (kv k)) ^ 2 := by
  rw [kcbs_qm_value]
  rw [show (2 : ℝ) = Real.sqrt 4 from by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

end CSD.Empirical.QM.KCBS
