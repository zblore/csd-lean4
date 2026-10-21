/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Dynamics.ToralReturnsConverse

/-!
# The return criterion for orientation-reversing toral automorphisms, and on all of `GL₂(ℤ)`

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #180 (out of #19, #178, #179).

For `B` with `det B = −1` the eigenvalues have product `−1`, so `tr B = λ − λ⁻¹`, the trace
recurrence is `tr Bᵗ⁺² = tr B · tr Bᵗ⁺¹ + tr Bᵗ`, the closed form is
`tr Bᵗ = εᵗ (μᵗ + (−1)ᵗ μ⁻ᵗ)` with `μ = (|tr B| + √(tr B² + 4))/2` the spectral radius and `ε` the
sign of the trace, and `det(Bᵗ − 1) = (−1)ᵗ − tr Bᵗ + 1`. Hyperbolicity is `tr B ≠ 0`:

* ★★★ `hasReturnGrowth_toral_neg` — `det B = −1`, `tr B ≠ 0` give return growth `log μ`;
* ★★ `not_hasReturnGrowth_toral_of_trace_eq_zero_neg` — `tr B = 0` gives `B² = 1`, every point
  returns at the second stroke;
* ★★★ `hasReturnGrowth_toral_iff_neg` — for `det B = −1`: return growth iff `tr B ≠ 0`;
* ★★★ `hasReturnGrowth_toral_iff_of_det` — **on all of `GL₂(ℤ)`**: `toral B` has return growth at
  some rate iff `(det B = 1 ∧ |tr B| > 2) ∨ (det B = −1 ∧ tr B ≠ 0)`.

Also `tendsto_log_div_of_bounds`, the squeeze `c μᵗ ≤ uₜ ≤ C μᵗ ⇒ (1/t) log uₜ → log μ` used by both
this file and (inline) #178, now a lemma.

## Honest scope

* The parity of `t` enters the bounds: at odd strokes the count is `μᵗ − μ⁻ᵗ`, at even strokes
  `μᵗ + μ⁻ᵗ − 2`; both are at least `(1 − μ⁻²)² μᵗ` and at most `4 μᵗ`.
* Matrices with `|det| ≠ 1` are not automorphisms of the torus and are out of scope.

References: Katok–Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*, §1.8;
`Mathlib/Dynamics/ToralReturns.lean` (#178), `ToralReturnsConverse.lean` (#179);
`specs/BACKLOG.md` #180, #19.
-/

@[expose] public section

open Filter Topology Function Module

namespace MeasureTheory

/-! ### The squeeze, as a lemma -/

/-- **The squeeze**: `c μᵗ ≤ uₜ ≤ C μᵗ` for `t ≥ 1` gives `(1/t) log uₜ → log μ`. -/
theorem tendsto_log_div_of_bounds {u : ℕ → ℝ} {μ c C : ℝ} (hμ : 1 < μ) (hc : 0 < c) (hC : 0 < C)
    (h : ∀ s : ℕ, c * μ ^ (s + 1) ≤ u s ∧ u s ≤ C * μ ^ (s + 1)) :
    Tendsto (fun s : ℕ => Real.log (u s) / ((s : ℝ) + 1)) atTop (𝓝 (Real.log μ)) := by
  have hμ0 : 0 < μ := zero_lt_one.trans hμ
  have hlog : ∀ s : ℕ, Real.log μ + Real.log c / ((s : ℝ) + 1) ≤ Real.log (u s) / ((s : ℝ) + 1)
      ∧ Real.log (u s) / ((s : ℝ) + 1) ≤ Real.log μ + Real.log C / ((s : ℝ) + 1) := by
    intro s
    obtain ⟨hlo, hhi⟩ := h s
    have hpos : 0 < c * μ ^ (s + 1) := by positivity
    have hs : (0 : ℝ) < (s : ℝ) + 1 := by positivity
    have hlog_hi := Real.log_le_log (hpos.trans_le hlo) hhi
    have hlog_lo := Real.log_le_log hpos hlo
    rw [Real.log_mul hc.ne' (by positivity), Real.log_pow μ (s + 1)] at hlog_lo
    rw [Real.log_mul hC.ne' (by positivity), Real.log_pow μ (s + 1)] at hlog_hi
    push_cast at hlog_lo hlog_hi
    constructor
    · rw [le_div_iff₀ hs]
      have : (Real.log μ + Real.log c / ((s : ℝ) + 1)) * ((s : ℝ) + 1)
          = ((s : ℝ) + 1) * Real.log μ + Real.log c := by field_simp
      linarith [this]
    · rw [div_le_iff₀ hs]
      have : (Real.log μ + Real.log C / ((s : ℝ) + 1)) * ((s : ℝ) + 1)
          = ((s : ℝ) + 1) * Real.log μ + Real.log C := by field_simp
      linarith [this]
  have hlim : ∀ k : ℝ, Tendsto (fun s : ℕ => Real.log μ + k / ((s : ℝ) + 1)) atTop (𝓝 (Real.log μ)) := by
    intro k
    have h0 : Tendsto (fun s : ℕ => k / ((s : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat k).comp (tendsto_add_atTop_nat 1)
      refine this.congr fun s => ?_
      simp [Function.comp]
    simpa using tendsto_const_nhds.add h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (hlim (Real.log c)) (hlim (Real.log C))
    (fun s => (hlog s).1) (fun s => (hlog s).2)

/-! ### The signed recurrence and the closed form -/

variable (B : Matrix (Fin 2) (Fin 2) ℤ)

theorem det_pow_sub_one_neg (hdet : B.det = -1) (t : ℕ) :
    (B ^ t - 1).det = (-1) ^ t - (B ^ t).trace + 1 := by
  rw [det_sub_one_fin_two, Matrix.det_pow, hdet]

theorem trace_pow_add_two_neg (hdet : B.det = -1) (t : ℕ) :
    (B ^ (t + 2)).trace = B.trace * (B ^ (t + 1)).trace + (B ^ t).trace := by
  rw [pow_add, cayley_hamilton_fin_two, hdet, neg_smul, one_smul, sub_neg_eq_add, Matrix.mul_add,
    Matrix.mul_smul, mul_one, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, ← pow_succ]

/-- The spectral radius of an orientation-reversing element: `(|tr B| + √(tr B² + 4)) / 2`. -/
noncomputable def spectralRadiusNeg : ℝ :=
  (|(B.trace : ℝ)| + Real.sqrt ((B.trace : ℝ) ^ 2 + 4)) / 2

theorem spectralRadiusNeg_pos : 0 < spectralRadiusNeg B := by
  unfold spectralRadiusNeg
  have := Real.sqrt_pos.2 (by positivity : (0 : ℝ) < (B.trace : ℝ) ^ 2 + 4)
  positivity

theorem one_lt_spectralRadiusNeg (hτ : (B.trace : ℝ) ≠ 0) : 1 < spectralRadiusNeg B := by
  unfold spectralRadiusNeg
  have h4 : (2 : ℝ) < Real.sqrt ((B.trace : ℝ) ^ 2 + 4) := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by have := sq_pos_of_ne_zero hτ; linarith)
  have := abs_nonneg (B.trace : ℝ)
  linarith

/-- `μ − μ⁻¹ = |tr B|`. -/
theorem spectralRadiusNeg_sub_inv : spectralRadiusNeg B - (spectralRadiusNeg B)⁻¹ = |(B.trace : ℝ)| := by
  have hprod : spectralRadiusNeg B
      * ((Real.sqrt ((B.trace : ℝ) ^ 2 + 4) - |(B.trace : ℝ)|) / 2) = 1 := by
    unfold spectralRadiusNeg
    have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (B.trace : ℝ) ^ 2 + 4)
    have ha := sq_abs (B.trace : ℝ)
    nlinarith [hs, ha]
  have hinv : (spectralRadiusNeg B)⁻¹ = (Real.sqrt ((B.trace : ℝ) ^ 2 + 4) - |(B.trace : ℝ)|) / 2 :=
    inv_eq_of_mul_eq_one_right hprod
  rw [hinv]
  unfold spectralRadiusNeg
  ring

/-- ★★ **The closed form of the trace**, `det B = −1`: `tr Bᵗ = εᵗ (μᵗ + (−1)ᵗ μ⁻ᵗ)`. -/
theorem trace_pow_eq_neg (hdet : B.det = -1) (t : ℕ) :
    ((B ^ t).trace : ℝ)
      = traceSign B ^ t * (spectralRadiusNeg B ^ t + (-1) ^ t * (spectralRadiusNeg B)⁻¹ ^ t) := by
  set μ := spectralRadiusNeg B with hμ
  set σ := μ⁻¹ with hσ
  set ε := traceSign B with hε
  have hμσ : μ * σ = 1 := mul_inv_cancel₀ (spectralRadiusNeg_pos B).ne'
  have hsub : μ - σ = |(B.trace : ℝ)| := spectralRadiusNeg_sub_inv B
  have hε2 : ε ^ 2 = 1 := traceSign_sq B
  have hεabs : ε * |(B.trace : ℝ)| = (B.trace : ℝ) := traceSign_mul_abs B
  have key : ∀ t : ℕ, ((B ^ t).trace : ℝ) = ε ^ t * (μ ^ t + (-1) ^ t * σ ^ t)
      ∧ ((B ^ (t + 1)).trace : ℝ) = ε ^ (t + 1) * (μ ^ (t + 1) + (-1) ^ (t + 1) * σ ^ (t + 1)) := by
    intro t
    induction t with
    | zero =>
        constructor
        · simp [Matrix.trace_one]
          norm_num
        · simp only [pow_one, zero_add, neg_one_mul]
          rw [← hεabs, ← hsub]
          ring
    | succ k ih =>
        refine ⟨ih.2, ?_⟩
        have hrec := trace_pow_add_two_neg B hdet k
        rw [show k + 1 + 1 = k + 2 by ring]
        have hrecR : ((B ^ (k + 2)).trace : ℝ) = (B.trace : ℝ) * ((B ^ (k + 1)).trace : ℝ)
            + ((B ^ k).trace : ℝ) := by exact_mod_cast hrec
        rw [hrecR, ih.1, ih.2, ← hεabs, ← hsub]
        linear_combination (-(ε ^ k * (μ ^ k + (-1) ^ k * σ ^ k) * ε ^ 2)) * hμσ
          - (ε ^ k * (μ ^ k + (-1) ^ k * σ ^ k)) * hε2
  exact (key t).1

/-! ### Nonvanishing and bounds, by parity -/

theorem traceSign_pow_even {t : ℕ} (ht : Even t) : traceSign B ^ t = 1 := by
  obtain ⟨k, rfl⟩ := ht
  rw [← two_mul, pow_mul, traceSign_sq, one_pow]

section Hyperbolic

variable (hτ : (B.trace : ℝ) ≠ 0)

/-- The fixed-point count at stroke `t ≥ 1`, with its two-sided bound. -/
theorem count_bounds_neg (hdet : B.det = -1) (hτ : (B.trace : ℝ) ≠ 0) (s : ℕ) :
    (1 - (spectralRadiusNeg B)⁻¹ ^ 2) ^ 2 * spectralRadiusNeg B ^ (s + 1)
        ≤ |((-1 : ℝ) ^ (s + 1) - ((B ^ (s + 1)).trace : ℝ) + 1)|
      ∧ |((-1 : ℝ) ^ (s + 1) - ((B ^ (s + 1)).trace : ℝ) + 1)| ≤ 4 * spectralRadiusNeg B ^ (s + 1)
      ∧ ((-1 : ℝ) ^ (s + 1) - ((B ^ (s + 1)).trace : ℝ) + 1) ≠ 0 := by
  set μ := spectralRadiusNeg B with hμ
  have hμ1 : 1 < μ := one_lt_spectralRadiusNeg B hτ
  have hμ0 : 0 < μ := zero_lt_one.trans hμ1
  set σ := μ⁻¹ with hσ
  have hσ1 : σ < 1 := inv_lt_one_of_one_lt₀ hμ1
  have hσ0 : 0 < σ := inv_pos.2 hμ0
  have hμσ : μ * σ = 1 := mul_inv_cancel₀ hμ0.ne'
  rw [trace_pow_eq_neg B hdet]
  set x : ℝ := μ ^ (s + 1) with hx
  set y : ℝ := σ ^ (s + 1) with hy
  have hx1 : μ ≤ x := le_self_pow₀ hμ1.le (by omega)
  have hx0 : 0 < x := hμ0.trans_le hx1
  have hy0 : 0 < y := by positivity
  have hxy : x * y = 1 := by rw [hx, hy, ← mul_pow, hμσ, one_pow]
  have hy1 : y ≤ σ := by
    rw [hy]
    exact pow_le_of_le_one hσ0.le hσ1.le (by omega)
  have hyσ : y ≤ σ ^ 2 ∨ s + 1 = 1 := by
    rcases Nat.lt_or_ge (s + 1) 2 with h | h
    · right; omega
    · left; rw [hy]; exact pow_le_pow_of_le_one hσ0.le hσ1.le h
  have hc0 : 0 < 1 - σ ^ 2 := by nlinarith
  have hc1 : 1 - σ ^ 2 < 1 := by nlinarith
  have hεabs : |traceSign B ^ (s + 1)| = 1 := abs_traceSign_pow B (s + 1)
  rcases Nat.even_or_odd (s + 1) with heven | hodd
  · -- even stroke: the count is `x + y − 2 = x (1 − y)²`
    have hε : traceSign B ^ (s + 1) = 1 := traceSign_pow_even B heven
    have hm : (-1 : ℝ) ^ (s + 1) = 1 := heven.neg_one_pow
    rw [hε, hm, one_mul, one_mul]
    have hform : (1 : ℝ) - (x + y) + 1 = -(x * (1 - y) ^ 2) := by
      have : x * (1 - y) ^ 2 = x - 2 * (x * y) + (x * y) * y := by ring
      rw [this, hxy]; ring
    have hy2 : y ≤ σ ^ 2 := by
      rcases hyσ with h | h
      · exact h
      · exfalso
        obtain ⟨k, hk⟩ := heven
        omega
    have hge : (1 - σ ^ 2) ^ 2 ≤ (1 - y) ^ 2 := by
      have : 1 - σ ^ 2 ≤ 1 - y := by linarith
      exact pow_le_pow_left₀ hc0.le this 2
    refine ⟨?_, ?_, ?_⟩
    · rw [hform, abs_neg, abs_of_nonneg (by positivity)]
      nlinarith [hge, hx0]
    · rw [hform, abs_neg, abs_of_nonneg (by positivity)]
      have : (1 - y) ^ 2 ≤ 1 := by
        have h0 : 0 ≤ 1 - y := by linarith
        have h1 : 1 - y ≤ 1 := by linarith
        nlinarith
      nlinarith
    · rw [hform]
      have : 0 < x * (1 - y) ^ 2 := by
        have : 0 < 1 - y := by linarith
        positivity
      linarith
  · -- odd stroke: the count is `x − y = x (1 − y²)`
    have hm : (-1 : ℝ) ^ (s + 1) = -1 := hodd.neg_one_pow
    rw [hm]
    have hform : (-1 : ℝ) - traceSign B ^ (s + 1) * (x + -1 * y) + 1 = -(traceSign B ^ (s + 1) * (x - y)) := by
      ring
    rw [hform, abs_neg, abs_mul, hεabs, one_mul]
    have hxy' : x - y = x * (1 - y ^ 2) := by
      have : x * (1 - y ^ 2) = x - (x * y) * y := by ring
      rw [this, hxy]; ring
    have hy2 : y ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ hy0.le hy1 2
    have hpos : 0 < x - y := by
      have : y < 1 := hy1.trans_lt hσ1
      have : 1 ≤ x := hμ1.le.trans hx1
      linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_of_pos hpos, hxy']
      have : (1 - σ ^ 2) ^ 2 ≤ 1 - y ^ 2 := by nlinarith
      nlinarith [hx0]
    · rw [abs_of_pos hpos]
      have : 1 ≤ x := hμ1.le.trans hx1
      linarith
    · intro h
      rw [neg_eq_zero, mul_eq_zero] at h
      rcases h with h | h
      · rw [h, abs_zero] at hεabs
        exact zero_ne_one hεabs
      · linarith

/-- `det(Bᵗ − 1) ≠ 0` for `t ≥ 1`. -/
theorem det_pow_sub_one_ne_zero_neg (hdet : B.det = -1) (hτ : (B.trace : ℝ) ≠ 0) (s : ℕ) :
    (B ^ (s + 1) - 1).det ≠ 0 := by
  rw [det_pow_sub_one_neg B hdet]
  have := (count_bounds_neg B hdet hτ s).2.2
  intro h
  apply this
  have : (((-1 : ℤ) ^ (s + 1) - (B ^ (s + 1)).trace + 1 : ℤ) : ℝ) = 0 := by rw [h]; simp
  push_cast at this
  exact this

/-- ★★ The fixed points of `toral Bᵗ` for `det B = −1`: `|(−1)ᵗ − tr Bᵗ + 1|` in number. -/
theorem card_fixedPoints_toral_pow_neg (hdet : B.det = -1) (hτ : (B.trace : ℝ) ≠ 0) (s : ℕ) :
    Nat.card {p : Torus2 // toral (B ^ (s + 1)) p = p}
      = ((-1) ^ (s + 1) - (B ^ (s + 1)).trace + 1).natAbs := by
  rw [card_fixedPoints_toral _ (det_pow_sub_one_ne_zero_neg B hdet hτ s), det_pow_sub_one_neg B hdet]

/-- ★★★ **An orientation-reversing hyperbolic toral automorphism has return growth `log μ`.** -/
theorem hasReturnGrowth_toral_neg (hdet : B.det = -1) (hτ : (B.trace : ℝ) ≠ 0) :
    HasReturnGrowth (toral B) (Real.log (spectralRadiusNeg B)) where
  finite t := by
    rw [toral_pow]
    have h : Nat.card {p : Torus2 // toral (B ^ (t + 1)) p = p} ≠ 0 := by
      rw [card_fixedPoints_toral_pow_neg B hdet hτ]
      exact Int.natAbs_ne_zero.2 (by
        have := det_pow_sub_one_ne_zero_neg B hdet hτ t
        rwa [det_pow_sub_one_neg B hdet] at this)
    exact Nat.finite_of_card_ne_zero h
  nonempty t := by
    rw [toral_pow]
    have h : Nat.card {p : Torus2 // toral (B ^ (t + 1)) p = p} ≠ 0 := by
      rw [card_fixedPoints_toral_pow_neg B hdet hτ]
      exact Int.natAbs_ne_zero.2 (by
        have := det_pow_sub_one_ne_zero_neg B hdet hτ t
        rwa [det_pow_sub_one_neg B hdet] at this)
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact h Nat.card_of_isEmpty
  tendsto := by
    have hμ1 : 1 < spectralRadiusNeg B := one_lt_spectralRadiusNeg B hτ
    have hσ1 : (spectralRadiusNeg B)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hμ1
    have hσ0 : 0 < (spectralRadiusNeg B)⁻¹ := inv_pos.2 (zero_lt_one.trans hμ1)
    have hc : 0 < (1 - (spectralRadiusNeg B)⁻¹ ^ 2) ^ 2 := by
      have : (spectralRadiusNeg B)⁻¹ ^ 2 < 1 := by nlinarith
      positivity
    refine tendsto_log_div_of_bounds hμ1 hc (by norm_num : (0 : ℝ) < 4) fun s => ?_
    have hcount : (returnCount (toral B) (s + 1) : ℝ)
        = |((-1 : ℝ) ^ (s + 1) - ((B ^ (s + 1)).trace : ℝ) + 1)| := by
      rw [returnCount, toral_pow, card_fixedPoints_toral_pow_neg B hdet hτ, Nat.cast_natAbs]
      push_cast
      rfl
    rw [hcount]
    exact ⟨(count_bounds_neg B hdet hτ s).1, (count_bounds_neg B hdet hτ s).2.1⟩

end Hyperbolic

/-! ### The converse and the characterisation on `GL₂(ℤ)` -/

/-- ★★ `tr B = 0`, `det B = −1` give `B² = 1`: every point returns at the second stroke. -/
theorem not_hasReturnGrowth_toral_of_trace_eq_zero_neg (hdet : B.det = -1) (hτ : B.trace = 0)
    (h : ℝ) : ¬ HasReturnGrowth (toral B) h := by
  intro H
  have hCH := cayley_hamilton_fin_two B
  rw [hdet, hτ, zero_smul, zero_sub, neg_smul, one_smul, neg_neg] at hCH
  have hfin := H.finite 1
  rw [toral_pow] at hfin
  have : Finite {p : Torus2 // toral (B ^ (1 + 1) - 1) p = 0} :=
    Finite.of_equiv _ (Equiv.subtypeEquivRight fun p => toral_fixed_iff (B ^ (1 + 1)) p)
  have hz : (B ^ (1 + 1) - 1).det = 0 := by
    rw [show (1 + 1 : ℕ) = 2 from rfl, hCH, sub_self, Matrix.det_zero]
  have := infinite_ker_toral_of_det_eq_zero _ hz
  exact not_finite {p : Torus2 // toral (B ^ (1 + 1) - 1) p = 0}

/-- ★★★ For `det B = −1`: return growth at some rate iff `tr B ≠ 0`. -/
theorem hasReturnGrowth_toral_iff_neg (hdet : B.det = -1) :
    (∃ h : ℝ, HasReturnGrowth (toral B) h) ↔ B.trace ≠ 0 := by
  constructor
  · rintro ⟨h, H⟩ hτ
    exact not_hasReturnGrowth_toral_of_trace_eq_zero_neg B hdet hτ h H
  · intro hτ
    exact ⟨_, hasReturnGrowth_toral_neg B hdet (by exact_mod_cast hτ)⟩

/-- ★★★ **The return criterion on `GL₂(ℤ)`**: for `det B = ±1`, `toral B` has return growth at some
rate iff `(det B = 1 ∧ |tr B| > 2) ∨ (det B = −1 ∧ tr B ≠ 0)`. -/
theorem hasReturnGrowth_toral_iff_of_det (hdet : B.det = 1 ∨ B.det = -1) :
    (∃ h : ℝ, HasReturnGrowth (toral B) h)
      ↔ (B.det = 1 ∧ 2 < |(B.trace : ℝ)|) ∨ (B.det = -1 ∧ B.trace ≠ 0) := by
  rcases hdet with h1 | h1
  · rw [hasReturnGrowth_toral_iff B h1]
    constructor
    · intro h; exact Or.inl ⟨h1, h⟩
    · rintro (⟨-, h⟩ | ⟨h2, -⟩)
      · exact h
      · rw [h1] at h2; norm_num at h2
  · rw [hasReturnGrowth_toral_iff_neg B h1]
    constructor
    · intro h; exact Or.inr ⟨h1, h⟩
    · rintro (⟨h2, -⟩ | ⟨-, h⟩)
      · rw [h1] at h2; norm_num at h2
      · exact h

end MeasureTheory

end
