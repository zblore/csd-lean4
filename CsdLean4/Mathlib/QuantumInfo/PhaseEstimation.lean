/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Fourier
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Quantum phase estimation: exact readout and the `4/π²` lower bound

**Category:** 1-Mathlib (CSD-free).

**Glossary:** https://glossary.constraintsurfacedynamics.com/phase-estimation/
Plain-language, CSD-role and formal statements of phase estimation, with this
module as its Lean anchor. Kept symmetric by `scripts/check-glossary.sh`.

Phase estimation on a `T`-level counting register `EuclideanSpace ℂ (Fin T)`, entirely generic
in `T` — the standard textbook results (Nielsen–Chuang §5.2), machine-checked:

* **The exact case.** The inverse QFT inverts the QFT (`applyQFTinv_phaseColumn`), so the phase
  state carrying an exact phase `j₀/T` — the QFT column `phaseColumn T j₀` — is read out as
  `|j₀⟩` with certainty (`phase_estimation_exact`).

* **The `4/π²` bound (the headline).** For an **arbitrary real** phase `φ`, the phase state
  `phaseStateR T φ = (1/√T) ∑_x e^{2πiφx} |x⟩` read at the counting index `c` closest to `φ·T`
  (`|φ − c/T| ≤ 1/(2T)`) succeeds with probability at least `4/π²`
  (`phase_estimation_lower_bound`). The amplitude is the Dirichlet sum
  `(1/T) ∑_{x<T} e^{2πi(φ−c/T)x}` (`applyQFTinv_phaseStateR_apply`), closed by `geom_sum_eq`
  and reduced to a ratio of sines via `Complex.norm_exp_I_mul_ofReal_sub_one`
  (`prob_phaseStateR_eq`); the bound is the Jordan inequality (`Real.mul_abs_le_abs_sin`) on
  the numerator against `|sin t| ≤ |t|` (`Real.abs_sin_le_abs`) on the denominator.

Support: `applyQFT`/`applyQFTinv` (the QFT action on the register, with the coordinate lemmas
`applyQFT_apply`/`applyQFTinv_apply`), on the `Register.lean` primitives `basisState`/`prob`.

## Honest scope

This is the **single-phase** statement: one phase state, one readout, the per-index bound. A
consumer racing several eigenvalue branches (Shor's `r` eigenvectors, say) must control the
cross-terms of its own joint state — that composition is the consumer's affair and is not done
here (`Empirical/QM/Algorithms/ShorCore.lean` documents the deferred two-register marginal).

*Provenance: extracted verbatim from `ShorCore.lean` (S3 + S4, 2026-08-29) — the statements
never mentioned orders, orbits, or `ZMod`; no new mathematics. The Shor-specific bridge
(`qftω_div`, `eigenPhase_eq_phaseColumn`, `shor_order_readout`, `shor_phase_estimation_lower_bound`)
stays in `ShorCore.lean`.*
-/

@[expose] public section

open scoped ComplexConjugate
open scoped Matrix

namespace QuantumInfo

variable (T : ℕ) [NeZero T]

/-! ## The QFT action on the counting register -/

/-- The QFT action on the counting register. -/
noncomputable def applyQFT (ψ : EuclideanSpace ℂ (Fin T)) : EuclideanSpace ℂ (Fin T) :=
  Matrix.toEuclideanLin (qftMatrix T) ψ

/-- The inverse-QFT action on the counting register (`Fᴴ`). -/
noncomputable def applyQFTinv (ψ : EuclideanSpace ℂ (Fin T)) : EuclideanSpace ℂ (Fin T) :=
  Matrix.toEuclideanLin (qftMatrix T)ᴴ ψ

omit [NeZero T] in
lemma applyQFT_apply (ψ : EuclideanSpace ℂ (Fin T)) (y : Fin T) :
    applyQFT T ψ y = ∑ x, qftMatrix T y x * ψ x := by
  rw [applyQFT, Matrix.toLpLin_apply]
  rfl

omit [NeZero T] in
lemma applyQFTinv_apply (ψ : EuclideanSpace ℂ (Fin T)) (y : Fin T) :
    applyQFTinv T ψ y = ∑ x, (qftMatrix T)ᴴ y x * ψ x := by
  rw [applyQFTinv, Matrix.toLpLin_apply]
  rfl

/-! ## The exact case: a QFT column is read with certainty -/

/-- The QFT column `j₀`: the phase state `(1/√T) ∑_x ω_T^{x j₀} |x⟩`. -/
noncomputable def phaseColumn (j₀ : Fin T) : EuclideanSpace ℂ (Fin T) :=
  applyQFT T (basisState j₀)

omit [NeZero T] in
@[simp] lemma phaseColumn_apply (j₀ x : Fin T) :
    phaseColumn T j₀ x = (Real.sqrt T : ℂ)⁻¹ * qftω T ^ ((x : ℕ) * (j₀ : ℕ)) := by
  rw [phaseColumn, applyQFT_apply, Finset.sum_eq_single j₀]
  · rw [basisState_apply, if_pos rfl, mul_one, qftMatrix_apply]
  · intro b _ hb; rw [basisState_apply, if_neg hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Phase-estimation exactness:** the inverse QFT inverts the QFT, so the QFT column `j₀` is
sent back to the basis state `|j₀⟩`. -/
theorem applyQFTinv_phaseColumn (j₀ : Fin T) :
    applyQFTinv T (phaseColumn T j₀) = basisState j₀ := by
  rw [phaseColumn, applyQFT, applyQFTinv]
  rw [show Matrix.toEuclideanLin (qftMatrix T)ᴴ (Matrix.toEuclideanLin (qftMatrix T) (basisState j₀))
        = Matrix.toEuclideanLin ((qftMatrix T)ᴴ * qftMatrix T) (basisState j₀) from by
      rw [Matrix.toLpLin_mul_same]; rfl]
  rw [qft_unitary, Matrix.toLpLin_one]
  rfl

/-- **The exact case:** phase estimation reads the QFT column `j₀` with certainty. -/
theorem phase_estimation_exact (j₀ : Fin T) :
    prob (applyQFTinv T (phaseColumn T j₀)) j₀ = 1 := by
  rw [applyQFTinv_phaseColumn, prob_basisState, if_pos rfl]

/-! ## The general case: the `4/π²` lower bound (Dirichlet kernel)

For a phase state carrying a real phase `φ`, inverse-QFT concentrates the amplitude near
`c ≈ φ·T`. When `c` is the closest counting index to `φ·T` (`|φ − c/T| ≤ 1/(2T)`), the readout
probability is at least `4/π²`, the Dirichlet-kernel constant. -/

/-- The **counting-register phase state** carrying a real phase `φ`:
`phaseStateR φ = (1/√T) ∑_x e^{2πi φ x} |x⟩`. For `φ = j₀/T` this is `phaseColumn T j₀`, no
longer required to land on an exact QFT column. -/
noncomputable def phaseStateR (φ : ℝ) : EuclideanSpace ℂ (Fin T) :=
  (Real.sqrt T : ℂ)⁻¹ • ∑ x : Fin T,
    (Complex.exp (2 * ↑Real.pi * Complex.I * ↑φ * ↑(x : ℕ))) • basisState x

omit [NeZero T] in
/-- **The inverse-QFT amplitude of the phase state.** Reading out index `c`, the amplitude is
the Dirichlet sum `(1/T) ∑_{x<T} e^{2πi (φ − c/T) x}`. The two `(√T)⁻¹` factors (one from the
phase state, one from `Fᴴ`) collapse to `T⁻¹`; the per-term phases `e^{2πiφx}` and
`conj(ω_T)^{xc}` merge into `e^{2πi(φ − c/T)x}`. -/
lemma applyQFTinv_phaseStateR_apply (φ : ℝ) (c : Fin T) :
    applyQFTinv T (phaseStateR T φ) c
      = (T : ℂ)⁻¹ * ∑ x : Fin T,
          Complex.exp (2 * ↑Real.pi * Complex.I * (↑(φ - (c : ℕ) / (T : ℝ)) : ℂ) * ↑(x : ℕ)) := by
  rw [applyQFTinv_apply]
  have hcoord : ∀ x : Fin T, phaseStateR T φ x
      = (Real.sqrt T : ℂ)⁻¹ * Complex.exp (2 * ↑Real.pi * Complex.I * ↑φ * ↑(x : ℕ)) := by
    intro x
    rw [phaseStateR, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, sum_coord]
    congr 1
    rw [Finset.sum_eq_single x]
    · rw [WithLp.ofLp_smul, Pi.smul_apply, basisState_apply, if_pos rfl, smul_eq_mul, mul_one]
    · intro b _ hb
      rw [WithLp.ofLp_smul, Pi.smul_apply, basisState_apply, if_neg (fun h => hb h.symm),
        smul_eq_mul, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hcoord]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  -- `(qftMatrix T)ᴴ c x = (√T)⁻¹ · conj(ω_T)^{xc} = (√T)⁻¹ · (ω_T^{xc})⁻¹`
  rw [Matrix.conjTranspose_apply, ← starRingEnd_apply, qftMatrix_apply, map_mul, map_pow,
    map_inv₀, Complex.conj_ofReal, qftω_conj, inv_pow]
  -- `ω_T^{xc} = e^{(2πi/T)(xc)}`
  have hpow : qftω T ^ ((x : ℕ) * (c : ℕ))
      = Complex.exp (2 * ↑Real.pi * Complex.I / ↑T * ↑((x : ℕ) * (c : ℕ))) := by
    rw [qftω, ← Complex.exp_nat_mul]; congr 1; ring
  rw [hpow, ← Complex.exp_neg]
  -- collect the two `(√T)⁻¹` into `T⁻¹` and the two exps into one
  rw [show (Real.sqrt T : ℂ)⁻¹ * Complex.exp (-(2 * ↑Real.pi * Complex.I / ↑T * ↑((x:ℕ)*(c:ℕ))))
        * ((Real.sqrt T : ℂ)⁻¹ * Complex.exp (2 * ↑Real.pi * Complex.I * ↑φ * ↑(x : ℕ)))
      = ((Real.sqrt T : ℂ)⁻¹ * (Real.sqrt T : ℂ)⁻¹)
        * (Complex.exp (-(2 * ↑Real.pi * Complex.I / ↑T * ↑((x:ℕ)*(c:ℕ))))
           * Complex.exp (2 * ↑Real.pi * Complex.I * ↑φ * ↑(x : ℕ))) from by ring]
  rw [inv_sqrtN_sq, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring_nf

/-- **The closed-form readout probability.** With `δ = φ − c/T` and `z = e^{2πiδ}`: in the
on-resonance case `δ = 0` the amplitude is `1` (so `prob = 1`); off resonance with
`sin(πδ) ≠ 0` the geometric sum collapses (`geom_sum_eq`) and the norm reduces, via
`Complex.norm_exp_I_mul_ofReal_sub_one`, to `prob = T⁻² · sin²(πδT) / sin²(πδ)`. -/
lemma prob_phaseStateR_eq (φ : ℝ) (c : Fin T)
    (hsin : Real.sin (Real.pi * (φ - (c : ℕ) / (T : ℝ))) ≠ 0) :
    prob (applyQFTinv T (phaseStateR T φ)) c
      = (T : ℝ)⁻¹ ^ 2 *
          (Real.sin (Real.pi * (φ - (c : ℕ) / (T : ℝ)) * T) ^ 2
            / Real.sin (Real.pi * (φ - (c : ℕ) / (T : ℝ))) ^ 2) := by
  set δ : ℝ := φ - (c : ℕ) / (T : ℝ) with hδdef
  set z : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I * (↑δ : ℂ)) with hzdef
  -- `z ≠ 1`: else `‖z − 1‖ = 2|sin(πδ)| = 0`, contradicting `hsin`
  have hzne : z ≠ 1 := by
    intro hz1
    have hzeq : z = Complex.exp (Complex.I * ↑(2 * Real.pi * δ)) := by
      rw [hzdef]; congr 1; push_cast; ring
    have : ‖z - 1‖ = 2 * |Real.sin (Real.pi * δ)| := by
      rw [hzeq, Complex.norm_exp_I_mul_ofReal_sub_one,
        show (2 * Real.pi * δ) / 2 = Real.pi * δ by ring, Real.norm_eq_abs, abs_mul]
      norm_num
    rw [hz1, sub_self, norm_zero] at this
    exact hsin (by
      have h2 : (2 : ℝ) * |Real.sin (Real.pi * δ)| = 0 := this.symm
      rcases mul_eq_zero.mp h2 with h | h
      · norm_num at h
      · exact abs_eq_zero.mp h)
  -- amplitude in geometric closed form
  have hamp : applyQFTinv T (phaseStateR T φ) c = (T : ℂ)⁻¹ * ((z ^ T - 1) / (z - 1)) := by
    rw [applyQFTinv_phaseStateR_apply]
    simp only [← hδdef]
    congr 1
    -- `∑_{x<T} e^{2πiδx} = ∑_{x<T} z^x = (z^T − 1)/(z − 1)`
    have hterm : ∀ x : Fin T,
        Complex.exp (2 * ↑Real.pi * Complex.I * (↑δ : ℂ) * ↑(x : ℕ)) = z ^ (x : ℕ) := by
      intro x; rw [hzdef, ← Complex.exp_nat_mul]; congr 1; ring
    simp_rw [hterm]
    rw [Fin.sum_univ_eq_sum_range (fun i => z ^ i) T, geom_sum_eq hzne T]
  -- norms: ‖z^T − 1‖ = 2|sin(πδT)|, ‖z − 1‖ = 2|sin(πδ)|
  have hzT : z ^ T = Complex.exp (Complex.I * ↑(2 * Real.pi * δ * T)) := by
    rw [hzdef, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hz1form : z = Complex.exp (Complex.I * ↑(2 * Real.pi * δ)) := by
    rw [hzdef]; congr 1; push_cast; ring
  have hnumN : ‖z ^ T - 1‖ = 2 * |Real.sin (Real.pi * δ * T)| := by
    rw [hzT, Complex.norm_exp_I_mul_ofReal_sub_one,
      show (2 * Real.pi * δ * T) / 2 = Real.pi * δ * T by ring, Real.norm_eq_abs, abs_mul]
    norm_num
  have hdenN : ‖z - 1‖ = 2 * |Real.sin (Real.pi * δ)| := by
    rw [hz1form, Complex.norm_exp_I_mul_ofReal_sub_one,
      show (2 * Real.pi * δ) / 2 = Real.pi * δ by ring, Real.norm_eq_abs, abs_mul]
    norm_num
  have hdenpos : (0 : ℝ) < 2 * |Real.sin (Real.pi * δ)| := by
    have : (0 : ℝ) < |Real.sin (Real.pi * δ)| := abs_pos.mpr hsin
    linarith
  -- assemble `prob = ‖amp‖²`
  have hTne : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne T)
  have hs2 : Real.sin (Real.pi * δ) ^ 2 ≠ 0 := pow_ne_zero _ hsin
  rw [prob, hamp, norm_mul, norm_div, hnumN, hdenN, norm_inv, Complex.norm_natCast,
    mul_pow, div_pow, mul_pow, mul_pow, sq_abs, sq_abs]
  -- (T⁻¹)² · (2² sin²(πδT)) / (2² sin²(πδ)) = (T⁻¹)² · sin²(πδT)/sin²(πδ)
  field_simp

/-- **The `4/π²` phase-estimation lower bound (HEADLINE).** For any real phase `φ` and a
counting index `c` that is the closest index to `φ·T` (`|φ − c/T| ≤ 1/(2T)`), inverse-QFT reads
out `c` with probability at least `4/π²`. On resonance (`φ = c/T`) the probability is `1`;
otherwise the Jordan inequality bounds the Dirichlet numerator from below and `|sin t| ≤ |t|`
the denominator from above. Nielsen–Chuang §5.2. -/
theorem phase_estimation_lower_bound (φ : ℝ) (c : Fin T)
    (hδ : |φ - (c : ℝ) / T| ≤ 1 / (2 * T)) :
    4 / Real.pi ^ 2 ≤ prob (applyQFTinv T (phaseStateR T φ)) c := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hTpos : (0 : ℝ) < T := by
    have := (NeZero.ne T); positivity
  set δ : ℝ := φ - (c : ℕ) / (T : ℝ) with hδdef
  -- after `set`, `hδ : |δ| ≤ 1/(2T)`; recast in product form `|δ| · (2T) ≤ 1`
  have hδprod : |δ| * (2 * T) ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hδ; linarith [hδ]
  by_cases hδ0 : δ = 0
  · -- on resonance: amplitude is `T⁻¹ · T = 1`, prob = 1 ≥ 4/π²
    have hprob1 : prob (applyQFTinv T (phaseStateR T φ)) c = 1 := by
      rw [prob, applyQFTinv_phaseStateR_apply]
      have hsum : (∑ x : Fin T,
          Complex.exp (2 * ↑Real.pi * Complex.I * (↑δ : ℂ) * ↑(x : ℕ))) = (T : ℂ) := by
        simp_rw [hδ0, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      rw [hsum, inv_mul_cancel₀ (by exact_mod_cast (NeZero.ne T)), norm_one, one_pow]
    rw [hprob1]
    -- 4/π² ≤ 1 since π² ≥ 4 (π > 3)
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  · -- off resonance
    have hδabs : 0 < |δ| := abs_pos.mpr hδ0
    -- `|δT| ≤ 1/2`, `|πδ| ≤ π/2`, `|πδT| ≤ π/2`
    have hδT : |δ * T| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos hTpos]; nlinarith [hδprod]
    have hπδT : |Real.pi * δ * T| ≤ Real.pi / 2 := by
      rw [show Real.pi * δ * T = Real.pi * (δ * T) by ring, abs_mul, abs_of_pos hπ]
      calc Real.pi * |δ * T| ≤ Real.pi * (1 / 2) := by
              apply mul_le_mul_of_nonneg_left hδT (le_of_lt hπ)
        _ = Real.pi / 2 := by ring
    have hπδ : |Real.pi * δ| ≤ Real.pi / 2 := by
      rw [abs_mul, abs_of_pos hπ]
      have hδhalf : |δ| ≤ 1 / 2 := by
        have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (NeZero.ne T).bot_lt
        nlinarith [hδprod, hT1, hδabs]
      calc Real.pi * |δ| ≤ Real.pi * (1 / 2) := by
              apply mul_le_mul_of_nonneg_left hδhalf (le_of_lt hπ)
        _ = Real.pi / 2 := by ring
    -- `sin(πδ) ≠ 0`: `0 < |πδ| ≤ π/2 < π`
    have hsin : Real.sin (Real.pi * δ) ≠ 0 := by
      have hne0 : Real.pi * δ ≠ 0 := mul_ne_zero hπ.ne' hδ0
      have hlt : |Real.pi * δ| < Real.pi := lt_of_le_of_lt hπδ (by linarith)
      rcases lt_trichotomy (Real.pi * δ) 0 with h | h | h
      · have : Real.sin (-(Real.pi * δ)) ≠ 0 := by
          apply ne_of_gt
          apply Real.sin_pos_of_pos_of_lt_pi (by linarith)
          rw [abs_of_neg h] at hlt; linarith
        rw [Real.sin_neg] at this; simpa using this
      · exact absurd h hne0
      · apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi h
        rw [abs_of_pos h] at hlt; exact hlt
    rw [prob_phaseStateR_eq T φ c hsin]
    -- numerator Jordan bound: `2|δ|T ≤ |sin(πδT)|`
    have hnum : 2 * |δ| * T ≤ |Real.sin (Real.pi * δ * T)| := by
      have hJ := Real.mul_abs_le_abs_sin hπδT
      have hrw : 2 / Real.pi * |Real.pi * δ * T| = 2 * |δ| * T := by
        rw [abs_mul, abs_mul, abs_of_pos hπ, abs_of_pos hTpos]
        field_simp
      rwa [hrw] at hJ
    -- denominator bound: `|sin(πδ)| ≤ π|δ|`
    have hden : |Real.sin (Real.pi * δ)| ≤ Real.pi * |δ| := by
      have := Real.abs_sin_le_abs (x := Real.pi * δ)
      rwa [abs_mul, abs_of_pos hπ] at this
    -- assemble: `T⁻² · sin²(πδT)/sin²(πδ) ≥ 4/π²`
    set a : ℝ := |Real.sin (Real.pi * δ * T)| with hadef
    set b : ℝ := |Real.sin (Real.pi * δ)| with hbdef
    have hb0 : 0 < b := abs_pos.mpr hsin
    have ha0 : 0 < a := lt_of_lt_of_le (by positivity) hnum
    have hsinsqT : Real.sin (Real.pi * δ * T) ^ 2 = a ^ 2 := by rw [hadef, sq_abs]
    have hsinsq : Real.sin (Real.pi * δ) ^ 2 = b ^ 2 := by rw [hbdef, sq_abs]
    rw [hsinsqT, hsinsq]
    -- now: 4/π² ≤ (T⁻¹)² · (a²/b²)
    have hlb : 2 / Real.pi ≤ (T : ℝ)⁻¹ * a / b := by
      rw [le_div_iff₀ hb0]
      calc 2 / Real.pi * b ≤ 2 / Real.pi * (Real.pi * |δ|) := by
              apply mul_le_mul_of_nonneg_left hden (by positivity)
        _ = 2 * |δ| := by field_simp
        _ = (T : ℝ)⁻¹ * (2 * |δ| * T) := by field_simp
        _ ≤ (T : ℝ)⁻¹ * a := by apply mul_le_mul_of_nonneg_left hnum (by positivity)
    have h2π : 0 < 2 / Real.pi := by positivity
    have hfinal : 4 / Real.pi ^ 2 ≤ ((T : ℝ)⁻¹ * a / b) ^ 2 := by
      calc 4 / Real.pi ^ 2 = (2 / Real.pi) ^ 2 := by rw [div_pow]; norm_num
        _ ≤ ((T : ℝ)⁻¹ * a / b) ^ 2 := pow_le_pow_left₀ (le_of_lt h2π) hlb 2
    calc 4 / Real.pi ^ 2 ≤ ((T : ℝ)⁻¹ * a / b) ^ 2 := hfinal
      _ = (T : ℝ)⁻¹ ^ 2 * (a ^ 2 / b ^ 2) := by rw [div_pow, mul_pow]; ring

end QuantumInfo
