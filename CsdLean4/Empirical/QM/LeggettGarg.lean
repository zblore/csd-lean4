/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.QuantumZeno
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Empirical/QM/LeggettGarg: the Leggett–Garg inequality and its quantum violation

The **Leggett–Garg inequality** (LGI) is the temporal analogue of CHSH: a test of
*macrorealism* using a single dichotomic observable `Q(t) ∈ {±1}` measured at three times.
Any macrorealist model (definite values + non-invasive measurability) obeys the `K₃` bound

  `K₃ := ⟨Q₁Q₂⟩ + ⟨Q₂Q₃⟩ − ⟨Q₁Q₃⟩ ≤ 1`.

Quantum mechanics violates it. For a two-level system with `Q = σ_z` precessing under
`e^{-iΔσ_x}` (the `QuantumZeno.zenoU` rotation), the Born two-time correlation is
`⟨QᵢQⱼ⟩ = cos(2Δ_{ij})`, giving `K₃(Δ) = 2cos(2Δ) − cos(4Δ)`, which peaks at the **Lüders bound
`3/2`** at `Δ = π/6` — well above the macrorealist `1`.

Results (all foundational-triple, no `sorry`):
* `lg_macrorealist_bound` — the `K₃ ≤ 1` bound over a **genuine measure-theoretic** macrorealist
  model (probability space with three `±1` observables), mirroring the CHSH LHV bound in
  `Empirical/QM/Crypto/E91.lean`;
* `lgCorr_eq` — the Born two-time correlation `= cos(2Δ)`, derived from `zenoU` (not asserted);
* `lg_qm_value` — `K₃(Δ) = 2cos(2Δ) − cos(4Δ)`;
* `lg_violation` — `K₃(π/6) = 3/2`; `lg_macrorealist_bound_violated` — `1 < 3/2`.

**Experimental verification:** Palacios-Laloy et al. 2010 (superconducting qubit); Knee et al.
2012; many since. **CSD note:** the macrorealist "non-invasive measurability" assumption is exactly
what the record layer / de-isolation reading denies — an intermediate measurement forms a record
(de-isolates), so CSD is realist yet LG-violating, consistent with QM.

## References
`Empirical/CSD/QuantumZeno.lean` (`zenoU`, the qubit rotation + Born machinery);
`Empirical/QM/Bell.lean` / `Empirical/QM/Crypto/E91.lean` (the CHSH analogue + LHV bound pattern).
-/

@[expose] public section

open MeasureTheory
open CSD.Empirical.CSDBridge.QuantumZeno

namespace CSD.Empirical.QM.LeggettGarg

/-! ### Part 1 — the macrorealist (classical) bound `K₃ ≤ 1` -/

/-- Pointwise Leggett–Garg: for `q₁, q₂, q₃ ∈ {±1}`, `q₁q₂ + q₂q₃ − q₁q₃ ≤ 1`. -/
lemma lg_pointwise {q₁ q₂ q₃ : ℝ} (h₁ : q₁ = 1 ∨ q₁ = -1) (h₂ : q₂ = 1 ∨ q₂ = -1)
    (h₃ : q₃ = 1 ∨ q₃ = -1) : q₁ * q₂ + q₂ * q₃ - q₁ * q₃ ≤ 1 := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rcases h₃ with h₃ | h₃ <;>
    subst h₁ <;> subst h₂ <;> subst h₃ <;> norm_num

/-- **The macrorealist Leggett–Garg bound `K₃ ≤ 1`.** For any macrorealist model — a probability
space carrying three dichotomic `±1` observables `Q₁, Q₂, Q₃` — the temporal combination
`⟨Q₁Q₂⟩ + ⟨Q₂Q₃⟩ − ⟨Q₁Q₃⟩ ≤ 1`. A genuine measure-theoretic hidden-variable bound (the temporal
analogue of the CHSH LHV bound), proved from the pointwise inequality by integral monotonicity. -/
theorem lg_macrorealist_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Q₁ Q₂ Q₃ : Ω → ℝ)
    (h₁ : ∀ ω, Q₁ ω = 1 ∨ Q₁ ω = -1) (h₂ : ∀ ω, Q₂ ω = 1 ∨ Q₂ ω = -1)
    (h₃ : ∀ ω, Q₃ ω = 1 ∨ Q₃ ω = -1)
    (i₁₂ : Integrable (fun ω => Q₁ ω * Q₂ ω) μ) (i₂₃ : Integrable (fun ω => Q₂ ω * Q₃ ω) μ)
    (i₁₃ : Integrable (fun ω => Q₁ ω * Q₃ ω) μ) :
    (∫ ω, Q₁ ω * Q₂ ω ∂μ) + (∫ ω, Q₂ ω * Q₃ ω ∂μ) - (∫ ω, Q₁ ω * Q₃ ω ∂μ) ≤ 1 := by
  have hcomb : (∫ ω, Q₁ ω * Q₂ ω ∂μ) + (∫ ω, Q₂ ω * Q₃ ω ∂μ) - (∫ ω, Q₁ ω * Q₃ ω ∂μ)
      = ∫ ω, (Q₁ ω * Q₂ ω + Q₂ ω * Q₃ ω - Q₁ ω * Q₃ ω) ∂μ := by
    rw [integral_sub (f := fun ω => Q₁ ω * Q₂ ω + Q₂ ω * Q₃ ω) (g := fun ω => Q₁ ω * Q₃ ω)
        (i₁₂.add i₂₃) i₁₃,
      integral_add (f := fun ω => Q₁ ω * Q₂ ω) (g := fun ω => Q₂ ω * Q₃ ω) i₁₂ i₂₃]
  rw [hcomb]
  calc ∫ ω, (Q₁ ω * Q₂ ω + Q₂ ω * Q₃ ω - Q₁ ω * Q₃ ω) ∂μ
      ≤ ∫ _ω, (1 : ℝ) ∂μ :=
        integral_mono ((i₁₂.add i₂₃).sub i₁₃) (integrable_const 1)
          (fun ω => lg_pointwise (h₁ ω) (h₂ ω) (h₃ ω))
    _ = 1 := by rw [integral_const]; simp

/-! ### Part 2 — the quantum two-time correlation (Born + qubit precession) -/

/-- `σ_z` eigenvalue of the computational basis state `i`: `+1` for `|0⟩`, `−1` for `|1⟩`. -/
def sgn : Fin 2 → ℝ := ![1, -1]

/-- **Born transition probability** `|⟨e_t, e^{-iΔσ_x} e_s⟩|²` between `σ_z`-eigenstates under
precession by `Δ` (`zenoU Δ`). -/
noncomputable def bornTP (Δ : ℝ) (s t : Fin 2) : ℝ :=
  ‖inner ℂ (EuclideanSpace.single t (1 : ℂ))
    (Matrix.toEuclideanLin (zenoU Δ) (EuclideanSpace.single s (1 : ℂ)))‖ ^ 2

/-- The Born transition amplitude is the matrix entry: `⟨e_t, zenoU Δ · e_s⟩ = (zenoU Δ) t s`. -/
lemma inner_single_zenoU (Δ : ℝ) (s t : Fin 2) :
    inner ℂ (EuclideanSpace.single t (1 : ℂ))
      (Matrix.toEuclideanLin (zenoU Δ) (EuclideanSpace.single s (1 : ℂ))) = (zenoU Δ) t s := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  simp only [toEuclideanLin_ofLp]
  fin_cases s <;> fin_cases t <;>
    simp [Matrix.mulVec, dotProduct, PiLp.single_apply]

/-- The Born transition probability is `|matrix entry|²`. -/
lemma bornTP_eq (Δ : ℝ) (s t : Fin 2) : bornTP Δ s t = ‖(zenoU Δ) t s‖ ^ 2 := by
  rw [bornTP, inner_single_zenoU]

/-- **The Born two-time correlation** `⟨Q(0)Q(Δ)⟩` of `σ_z` under precession by `Δ`, with
intermediate collapse: `∑_{s,t} sgn(s)·sgn(t)·½·|⟨e_t, zenoU Δ · e_s⟩|²`. -/
noncomputable def lgCorr (Δ : ℝ) : ℝ :=
  ∑ s : Fin 2, ∑ t : Fin 2, sgn s * sgn t * (1 / 2) * bornTP Δ s t

/-- **The quantum two-time correlation equals `cos(2Δ)`** — derived from `zenoU`, not asserted. -/
theorem lgCorr_eq (Δ : ℝ) : lgCorr Δ = Real.cos (2 * Δ) := by
  have h00 : bornTP Δ 0 0 = Real.cos Δ ^ 2 := by
    rw [bornTP_eq, show (zenoU Δ) 0 0 = (Real.cos Δ : ℂ) from by simp [zenoU],
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h11 : bornTP Δ 1 1 = Real.cos Δ ^ 2 := by
    rw [bornTP_eq, show (zenoU Δ) 1 1 = (Real.cos Δ : ℂ) from by simp [zenoU],
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h01 : bornTP Δ 0 1 = Real.sin Δ ^ 2 := by
    rw [bornTP_eq, show (zenoU Δ) 1 0 = -(Complex.I * (Real.sin Δ : ℂ)) from by simp [zenoU],
      norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h10 : bornTP Δ 1 0 = Real.sin Δ ^ 2 := by
    rw [bornTP_eq, show (zenoU Δ) 0 1 = -(Complex.I * (Real.sin Δ : ℂ)) from by simp [zenoU],
      norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have key : lgCorr Δ = Real.cos Δ ^ 2 - Real.sin Δ ^ 2 := by
    unfold lgCorr
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, h00, h01, h10, h11]
    simp only [sgn, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [key, Real.cos_two_mul]
  linarith [Real.sin_sq_add_cos_sq Δ]

/-! ### Part 3 — the `K₃` combination and its quantum violation -/

/-- The Leggett–Garg `K₃` combination for equal time-steps `Δ`:
`K₃(Δ) = ⟨Q₁Q₂⟩ + ⟨Q₂Q₃⟩ − ⟨Q₁Q₃⟩ = 2·lgCorr Δ − lgCorr (2Δ)` (adjacent pairs at separation
`Δ`, outer pair at separation `2Δ`). -/
noncomputable def lgK (Δ : ℝ) : ℝ := lgCorr Δ + lgCorr Δ - lgCorr (2 * Δ)

/-- **The quantum Leggett–Garg value** `K₃(Δ) = 2cos(2Δ) − cos(4Δ)`. -/
theorem lg_qm_value (Δ : ℝ) : lgK Δ = 2 * Real.cos (2 * Δ) - Real.cos (4 * Δ) := by
  rw [lgK, lgCorr_eq, lgCorr_eq]
  ring_nf

/-- **The quantum violation: `K₃(π/6) = 3/2`** — the Lüders bound, exceeding the macrorealist `1`. -/
theorem lg_violation : lgK (Real.pi / 6) = 3 / 2 := by
  rw [lg_qm_value]
  rw [show 2 * (Real.pi / 6) = Real.pi / 3 by ring,
    show 4 * (Real.pi / 6) = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

/-- The macrorealist Leggett–Garg bound value `1`. -/
def lgMacrorealistBoundValue : ℝ := 1

/-- **The macrorealist bound is violated:** `1 < K₃(π/6) = 3/2`. The numerical gap is the empirical
falsification of macrorealism (Palacios-Laloy 2010 and successors). -/
theorem lg_macrorealist_bound_violated : lgMacrorealistBoundValue < lgK (Real.pi / 6) := by
  rw [lgMacrorealistBoundValue, lg_violation]; norm_num

end CSD.Empirical.QM.LeggettGarg
