/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Dynamics.ToralReturns

/-!
# Non-hyperbolic toral automorphisms have no return growth: the criterion is the trace

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #179 (out of #19 and #177).

For `B ∈ SL₂(ℤ)` with `|tr B| ≤ 2`, `toral B` has no return growth at any rate
(★★★ `not_hasReturnGrowth_toral_of_abs_trace_le_two`): some power `Bᵗ − 1` is singular, and the
kernel of a singular toral endomorphism is infinite (★★ `infinite_ker_toral_of_det_eq_zero`) — a
nonzero integer kernel vector `k` gives the line `s ↦ s·k/kᵢ mod ℤ²`, injective on `[0, 1)`. The five
cases are Cayley–Hamilton `B² = (tr B)·B − 1`: `tr = 0` gives `B⁴ = 1`, `tr = 1` gives `B⁶ = 1`,
`tr = −1` gives `B³ = 1`, `tr = 2` gives `(B − 1)² = 0`, `tr = −2` gives `(B + 1)² = 0` and
`B² − 1 = −2(B + 1)`.

With #178 this is the characterisation ★★★ `hasReturnGrowth_toral_iff`:
**an element of `SL₂(ℤ)` has return growth at some rate iff `|tr B| > 2`** — the return criterion
(#177) on integer matrices is decided by one integer.

## Honest scope

* `det B = 1` throughout, as in #178.
* The rate in the hyperbolic case is `log ρ` (#178); the characterisation here only asserts
  existence of a rate, which is what decides the criterion.

References: Katok–Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, §1.8
(classification of elements of `SL₂(ℤ)` by the trace); `Mathlib/Dynamics/ToralReturns.lean` (#178),
`Mathlib/Dynamics/ReturnCriterion.lean` (#177); `specs/BACKLOG.md` #179, #178, #19.
-/

@[expose] public section

open Filter Topology Function Module

namespace MeasureTheory

/-! ### A singular integer matrix has a nonzero integer kernel vector -/

/-- A `2 × 2` integer matrix of determinant `0` kills a nonzero integer vector. -/
theorem exists_kernel_vector (C : Matrix (Fin 2) (Fin 2) ℤ) (hC : C.det = 0) :
    ∃ k : Fin 2 → ℤ, k ≠ 0 ∧ Matrix.toLin' C k = 0 := by
  rw [Matrix.det_fin_two] at hC
  by_cases h0 : C 0 0 = 0 ∧ C 0 1 = 0
  · by_cases h1 : C 1 0 = 0 ∧ C 1 1 = 0
    · refine ⟨![1, 0], ?_, ?_⟩
      · intro h
        have := congrFun h 0
        simp at this
      · rw [Matrix.toLin'_apply]
        ext j
        fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0.1, h0.2, h1.1, h1.2]
    · refine ⟨![-C 1 1, C 1 0], ?_, ?_⟩
      · intro h
        apply h1
        have e0 := congrFun h 0
        have e1 := congrFun h 1
        simp at e0 e1
        exact ⟨e1, e0⟩
      · rw [Matrix.toLin'_apply]
        ext j
        fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0.1, h0.2]
        ring
  · refine ⟨![-C 0 1, C 0 0], ?_, ?_⟩
    · intro h
      apply h0
      have e0 := congrFun h 0
      have e1 := congrFun h 1
      simp at e0 e1
      exact ⟨e1, e0⟩
    · rw [Matrix.toLin'_apply]
      ext j
      fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      · ring
      · linear_combination hC

/-! ### A singular toral endomorphism has an infinite kernel -/

theorem realMat_eq_zero_of_toLin'_eq_zero (C : Matrix (Fin 2) (Fin 2) ℤ) {k : Fin 2 → ℤ}
    (hk : Matrix.toLin' C k = 0) : realMat C ((k 0 : ℝ), (k 1 : ℝ)) = 0 := by
  rw [realMat_intCast, hk]
  simp

/-- ★★ **The kernel of a singular toral endomorphism is infinite**: the line through a nonzero
integer kernel vector, parametrised by `[0, 1)`, lies in it injectively. -/
theorem infinite_ker_toral_of_det_eq_zero (C : Matrix (Fin 2) (Fin 2) ℤ) (hC : C.det = 0) :
    Infinite {p : Torus2 // toral C p = 0} := by
  obtain ⟨k, hk0, hk⟩ := exists_kernel_vector C hC
  have hreal : realMat C ((k 0 : ℝ), (k 1 : ℝ)) = 0 := realMat_eq_zero_of_toLin'_eq_zero C hk
  -- a nonzero coordinate
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, k i ≠ 0 := by
    by_contra! h
    exact hk0 (funext h)
  have hki : (k i : ℝ) ≠ 0 := by exact_mod_cast hi
  -- the line, in the kernel
  have hmem : ∀ s : ℝ,
      toral C ((((s / k i) * k 0 : ℝ) : AddCircle (1 : ℝ)), (((s / k i) * k 1 : ℝ) : AddCircle (1 : ℝ))) = 0 := by
    intro s
    rw [toral_coe]
    have : realMat C ((s / k i) * k 0, (s / k i) * k 1) = 0 := by
      have h := realMat_smul C (s / k i) ((k 0 : ℝ), (k 1 : ℝ))
      rw [hreal, smul_zero] at h
      simpa [Prod.smul_mk, smul_eq_mul] using h
    rw [this]
    simp
  let f : Set.Ico (0 : ℝ) 1 → {p : Torus2 // toral C p = 0} := fun s =>
    ⟨((((s : ℝ) / k i) * k 0 : ℝ), (((s : ℝ) / k i) * k 1 : ℝ)), hmem s⟩
  have hf : Injective f := by
    intro s s' hss'
    have h := congrArg (fun q : {p : Torus2 // toral C p = 0} => (q : Torus2)) hss'
    simp only [f] at h
    have hs : (s : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 1) := by simp
    have hs' : (s' : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 1) := by simp
    have key : (((s : ℝ) / k i) * k i : ℝ) = s := by field_simp
    have key' : (((s' : ℝ) / k i) * k i : ℝ) = s' := by field_simp
    have hcomp : (((s : ℝ) / k i * k i : ℝ) : AddCircle (1 : ℝ)) = (((s' : ℝ) / k i * k i : ℝ) : AddCircle (1 : ℝ)) := by
      fin_cases i
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h
    rw [key, key'] at hcomp
    exact Subtype.ext ((AddCircle.coe_eq_coe_iff_of_mem_Ico hs hs').1 hcomp)
  have : Infinite (Set.Ico (0 : ℝ) 1) := Set.Ico.infinite (by norm_num)
  exact Infinite.of_injective f hf

/-! ### The five non-hyperbolic cases -/

/-- In each non-hyperbolic case some `Bᵗ − 1` (`t ≥ 1`) is singular. -/
theorem exists_det_pow_sub_one_eq_zero (B : Matrix (Fin 2) (Fin 2) ℤ) (hdet : B.det = 1)
    (hτ : |B.trace| ≤ 2) : ∃ t : ℕ, (B ^ (t + 1) - 1).det = 0 := by
  have hCH := cayley_hamilton_fin_two B
  rw [hdet, one_smul] at hCH
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℤ, B.trace = τ := ⟨_, rfl⟩
  rw [hτdef] at hCH hτ
  have hτ' : -2 ≤ τ ∧ τ ≤ 2 := abs_le.1 hτ
  obtain ⟨hlo, hhi⟩ := hτ'
  interval_cases τ
  · -- `tr = −2`: `(B + 1)² = 0`, `B² − 1 = −2(B + 1)`
    refine ⟨1, ?_⟩
    have hsq : (B + 1) * (B + 1) = 0 := by
      have : (B + 1) * (B + 1) = B ^ 2 + 2 • B + 1 := by
        rw [sq, two_smul]; noncomm_ring
      rw [this, hCH]
      simp only [neg_smul, two_smul]
      abel
    have hdet1 : (B + 1).det = 0 := by
      have := congrArg Matrix.det hsq
      rw [Matrix.det_mul, Matrix.det_zero] at this
      exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (by rw [sq]; exact this)
    have hB2 : B ^ (1 + 1) - 1 = (-2 : ℤ) • (B + 1) := by
      rw [hCH]
      simp only [neg_smul, two_smul, smul_add]
      abel
    rw [hB2, Matrix.det_smul, hdet1, mul_zero]
  · -- `tr = −1`: `B³ = 1`
    refine ⟨2, ?_⟩
    have h3 : B ^ (2 + 1) = 1 := by
      rw [pow_succ, hCH, sub_mul, neg_smul, one_smul, neg_mul, one_mul, ← sq, hCH]
      abel
    rw [h3, sub_self, Matrix.det_zero]
  · -- `tr = 0`: `B⁴ = 1`
    refine ⟨3, ?_⟩
    have h4 : B ^ (3 + 1) = 1 := by
      rw [show (3 + 1 : ℕ) = 2 * 2 from rfl, pow_mul, hCH]
      simp
    rw [h4, sub_self, Matrix.det_zero]
  · -- `tr = 1`: `B³ = −1`, `B⁶ = 1`
    refine ⟨5, ?_⟩
    have h3 : B ^ 3 = -1 := by
      rw [pow_succ, hCH, one_smul, sub_mul, one_mul, ← sq, hCH, one_smul]
      abel
    have h6 : B ^ (5 + 1) = 1 := by
      rw [show (5 + 1 : ℕ) = 3 * 2 from rfl, pow_mul, h3]
      simp
    rw [h6, sub_self, Matrix.det_zero]
  · -- `tr = 2`: `(B − 1)² = 0`
    refine ⟨0, ?_⟩
    have hsq : (B - 1) * (B - 1) = 0 := by
      have : (B - 1) * (B - 1) = B ^ 2 - 2 • B + 1 := by
        rw [sq, two_smul]; noncomm_ring
      rw [this, hCH]
      simp only [two_smul]
      abel
    have := congrArg Matrix.det hsq
    rw [Matrix.det_mul, Matrix.det_zero] at this
    rw [pow_one]
    exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (by rw [sq]; exact this)

/-! ### The converse, and the characterisation -/

/-- ★★★ **No non-hyperbolic element of `SL₂(ℤ)` has return growth**: at some stroke every return
set is infinite. -/
theorem not_hasReturnGrowth_toral_of_abs_trace_le_two (B : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : B.det = 1) (hτ : |(B.trace : ℝ)| ≤ 2) (h : ℝ) : ¬ HasReturnGrowth (toral B) h := by
  intro H
  have hτℤ : |B.trace| ≤ 2 := by exact_mod_cast (by rwa [← Int.cast_abs] at hτ : ((|B.trace| : ℤ) : ℝ) ≤ 2)
  obtain ⟨t, ht⟩ := exists_det_pow_sub_one_eq_zero B hdet hτℤ
  have hfin := H.finite t
  rw [toral_pow] at hfin
  have : Finite {p : Torus2 // toral (B ^ (t + 1) - 1) p = 0} :=
    Finite.of_equiv _ (Equiv.subtypeEquivRight fun p => toral_fixed_iff (B ^ (t + 1)) p)
  have := infinite_ker_toral_of_det_eq_zero _ ht
  exact not_finite {p : Torus2 // toral (B ^ (t + 1) - 1) p = 0}

/-- ★★★ **The return criterion on `SL₂(ℤ)` is decided by the trace**: `toral B` has return growth at
some rate iff `|tr B| > 2`. -/
theorem hasReturnGrowth_toral_iff (B : Matrix (Fin 2) (Fin 2) ℤ) (hdet : B.det = 1) :
    (∃ h : ℝ, HasReturnGrowth (toral B) h) ↔ 2 < |(B.trace : ℝ)| := by
  constructor
  · rintro ⟨h, H⟩
    by_contra! hle
    exact not_hasReturnGrowth_toral_of_abs_trace_le_two B hdet hle h H
  · intro hτ
    exact ⟨_, hasReturnGrowth_toral B hτ hdet⟩

end MeasureTheory

end
