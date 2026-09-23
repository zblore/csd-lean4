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
# Quantum phase estimation: exact readout, the `4/π²` bound and the two-index `8/π²` bound

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

* **The two-index `8/π²` bound.** Both grid points straddling `φ·T` — `c` at phase distance
  `0 ≤ φ − c/T ≤ 1/T` and `c + 1` (read modulo `T`) — jointly carry at least `8/π²`
  (`phase_estimation_two_index`, BHMT Theorem 11 at `k = 1`), from the two-index Dirichlet
  bound `dirichlet_two_index` and the elementary inequality `sin²(πx)(1/x² + 1/(1−x)²) ≥ 8`
  (`eight_mul_sq_le_sin_sq_pi_mul`); a lower straddling index exists for every phase in
  `[0, 1)` (`exists_straddle_index`).

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

/-! ## Both grid points: the two-index `8/π²` bound (BHMT Theorem 11, `k = 1`)

`phase_estimation_lower_bound` is the single-index `4/π²`. Counting **both** counting indices
straddling `φ·T` — the lower one at phase distance `δ ∈ [0, 1/T]` and the upper one at
`1/T − δ` — the pair carries `8/π²`. This is a genuinely two-index inequality on the Dirichlet
kernel: a single index at distance up to `1/T` can carry probability `0`. The analytic core is
`eight_mul_sq_le_sin_sq_pi_mul`, the elementary inequality
`sin²(πx) (1/x² + 1/(1−x)²) ≥ 8` on `(0, 1)` (equality at `x = 1/2`). -/

/-- The cubic range `0 < x ≤ 1/4`: `sin t ≥ t − t³/6` at `t = πx`, then a polynomial estimate
with `3.1415 < π < 3.1416`. -/
lemma eight_mul_sq_le_sin_sq_pi_mul_of_le_quarter {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 4) :
    8 * (x * (1 - x)) ^ 2 ≤ Real.sin (Real.pi * x) ^ 2 * (x ^ 2 + (1 - x) ^ 2) := by
  have hπ1 := Real.pi_gt_d4
  have hπ2 := Real.pi_lt_d4
  have hπ0 : 0 < Real.pi := Real.pi_pos
  have hP1 : (9.869 : ℝ) < Real.pi ^ 2 := by nlinarith
  have hP2 : Real.pi ^ 2 < (9.8697 : ℝ) := by nlinarith
  have hw : x ^ 2 ≤ 1 / 16 := by nlinarith
  have hw0 : 0 ≤ x ^ 2 := sq_nonneg x
  -- the cubic lower bound `L = πx − (πx)³/6 = πx (1 − π²x²/6)`, nonnegative here
  have hL := Real.sin_ge_sub_cube (x := Real.pi * x) (by positivity)
  have hPw : Real.pi ^ 2 * x ^ 2 ≤ 1 := by nlinarith
  have hL0 : 0 ≤ Real.pi * x - (Real.pi * x) ^ 3 / 6 := by
    have h1 : 0 ≤ Real.pi * x * (1 - Real.pi ^ 2 * x ^ 2 / 6) :=
      mul_nonneg (by positivity) (by linarith)
    calc (0 : ℝ) ≤ Real.pi * x * (1 - Real.pi ^ 2 * x ^ 2 / 6) := h1
      _ = Real.pi * x - (Real.pi * x) ^ 3 / 6 := by ring
  have hs2 : (Real.pi * x - (Real.pi * x) ^ 3 / 6) ^ 2 ≤ Real.sin (Real.pi * x) ^ 2 :=
    pow_le_pow_left₀ hL0 hL 2
  have hL2 : (Real.pi * x - (Real.pi * x) ^ 3 / 6) ^ 2
      = Real.pi ^ 2 * x ^ 2 * (1 - Real.pi ^ 2 * x ^ 2 / 6) ^ 2 := by ring
  -- the polynomial core `8 ≤ π² (1 − π²x²/3)(1 + x²)` on `x² ≤ 1/16`
  have hcore : 8 ≤ Real.pi ^ 2 * (1 - Real.pi ^ 2 * x ^ 2 / 3) * (1 + x ^ 2) := by
    have h1 : 0 ≤ (1 / 16 - x ^ 2) * (Real.pi ^ 2 * Real.pi ^ 2 / 3 - Real.pi ^ 2) :=
      mul_nonneg (by linarith) (by nlinarith)
    have h2 : Real.pi ^ 2 * Real.pi ^ 2 * (x ^ 2 * x ^ 2)
        ≤ Real.pi ^ 2 * Real.pi ^ 2 * (1 / 256) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    have h3 : Real.pi ^ 2 * Real.pi ^ 2 < 97.42 := by nlinarith
    nlinarith
  -- `(1 − a)² ≥ 1 − 2a` and `x² + (1−x)² ≥ (1−x)²(1 + x²)`
  have hk2 : 1 - Real.pi ^ 2 * x ^ 2 / 3 ≤ (1 - Real.pi ^ 2 * x ^ 2 / 6) ^ 2 := by
    nlinarith [sq_nonneg (Real.pi ^ 2 * x ^ 2 / 6)]
  have hk3 : (1 - x) ^ 2 * (1 + x ^ 2) ≤ x ^ 2 + (1 - x) ^ 2 := by
    have h1 : 0 ≤ x ^ 2 * (1 - (1 - x) ^ 2) := mul_nonneg hw0 (by nlinarith)
    nlinarith
  have hA : 0 ≤ Real.pi ^ 2 * x ^ 2 := by positivity
  have hB : 0 ≤ (1 - x) ^ 2 * (1 + x ^ 2) := by positivity
  calc 8 * (x * (1 - x)) ^ 2 = 8 * (x ^ 2 * (1 - x) ^ 2) := by ring
    _ ≤ Real.pi ^ 2 * (1 - Real.pi ^ 2 * x ^ 2 / 3) * (1 + x ^ 2) * (x ^ 2 * (1 - x) ^ 2) :=
        mul_le_mul_of_nonneg_right hcore (by positivity)
    _ = Real.pi ^ 2 * x ^ 2 * (1 - Real.pi ^ 2 * x ^ 2 / 3) * ((1 - x) ^ 2 * (1 + x ^ 2)) := by
        ring
    _ ≤ Real.pi ^ 2 * x ^ 2 * (1 - Real.pi ^ 2 * x ^ 2 / 6) ^ 2
          * ((1 - x) ^ 2 * (1 + x ^ 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk2 hA) hB
    _ ≤ Real.pi ^ 2 * x ^ 2 * (1 - Real.pi ^ 2 * x ^ 2 / 6) ^ 2 * (x ^ 2 + (1 - x) ^ 2) :=
        mul_le_mul_of_nonneg_left hk3 (by positivity)
    _ = (Real.pi * x - (Real.pi * x) ^ 3 / 6) ^ 2 * (x ^ 2 + (1 - x) ^ 2) := by rw [hL2]
    _ ≤ Real.sin (Real.pi * x) ^ 2 * (x ^ 2 + (1 - x) ^ 2) :=
        mul_le_mul_of_nonneg_right hs2 (by positivity)

/-- The cosine range `1/4 ≤ x ≤ 1/2`: `sin(πx) = cos(πy)` with `y = 1/2 − x`, `cos t ≥ 1 − t²/2`,
then a polynomial estimate in `v = y² ≤ 1/16`. -/
lemma eight_mul_sq_le_sin_sq_pi_mul_of_quarter_le {x : ℝ} (hx : 1 / 4 ≤ x) (hx' : x ≤ 1 / 2) :
    8 * (x * (1 - x)) ^ 2 ≤ Real.sin (Real.pi * x) ^ 2 * (x ^ 2 + (1 - x) ^ 2) := by
  have hπ1 := Real.pi_gt_d4
  have hπ2 := Real.pi_lt_d4
  have hπ0 : 0 < Real.pi := Real.pi_pos
  have hP1 : (9.869 : ℝ) < Real.pi ^ 2 := by nlinarith
  have hP2 : Real.pi ^ 2 < (9.8697 : ℝ) := by nlinarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = 1 / 2 - x := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by linarith
  have hy4 : y ≤ 1 / 4 := by linarith
  have hv : y ^ 2 ≤ 1 / 16 := by nlinarith
  have hv0 : 0 ≤ y ^ 2 := sq_nonneg y
  -- `sin(πx) = cos(πy)` and the quadratic lower bound, nonnegative here
  have hsin : Real.sin (Real.pi * x) = Real.cos (Real.pi * y) := by
    rw [← Real.sin_pi_div_two_sub]
    congr 1
    rw [hy]; ring
  have hc := Real.one_sub_sq_div_two_le_cos (x := Real.pi * y)
  have hc0 : 0 ≤ 1 - (Real.pi * y) ^ 2 / 2 := by
    have : (Real.pi * y) ^ 2 ≤ 1 := by nlinarith
    linarith
  have hs2 : (1 - (Real.pi * y) ^ 2 / 2) ^ 2 ≤ Real.sin (Real.pi * x) ^ 2 := by
    rw [hsin]; exact pow_le_pow_left₀ hc0 hc 2
  have hxy1 : x * (1 - x) = 1 / 4 - y ^ 2 := by rw [hy]; ring
  have hxy2 : x ^ 2 + (1 - x) ^ 2 = 1 / 2 + 2 * y ^ 2 := by rw [hy]; ring
  -- the polynomial core: `(1 − Pv/2)²(1/2 + 2v) − 8(1/4 − v)² = v·Q(v)` with `Q ≥ 0`
  have hP4 : (97.39 : ℝ) < Real.pi ^ 2 * Real.pi ^ 2 := by nlinarith
  have hP4' : Real.pi ^ 2 * Real.pi ^ 2 < (97.42 : ℝ) := by nlinarith
  have hQ : 0 ≤ (6 - Real.pi ^ 2 / 2)
      + y ^ 2 * (Real.pi ^ 2 * Real.pi ^ 2 / 8 - 2 * Real.pi ^ 2 - 8)
      + Real.pi ^ 2 * Real.pi ^ 2 * (y ^ 2 * y ^ 2) / 2 := by
    have h1 : 0 ≤ (1 / 16 - y ^ 2) * (2 * Real.pi ^ 2 + 8 - Real.pi ^ 2 * Real.pi ^ 2 / 8) :=
      mul_nonneg (by linarith) (by nlinarith)
    have h2 : 0 ≤ Real.pi ^ 2 * Real.pi ^ 2 * (y ^ 2 * y ^ 2) / 2 := by positivity
    nlinarith
  have hcore : 8 * (1 / 4 - y ^ 2) ^ 2
      ≤ (1 - Real.pi ^ 2 * y ^ 2 / 2) ^ 2 * (1 / 2 + 2 * y ^ 2) := by
    have hid : (1 - Real.pi ^ 2 * y ^ 2 / 2) ^ 2 * (1 / 2 + 2 * y ^ 2) - 8 * (1 / 4 - y ^ 2) ^ 2
        = y ^ 2 * ((6 - Real.pi ^ 2 / 2)
            + y ^ 2 * (Real.pi ^ 2 * Real.pi ^ 2 / 8 - 2 * Real.pi ^ 2 - 8)
            + Real.pi ^ 2 * Real.pi ^ 2 * (y ^ 2 * y ^ 2) / 2) := by ring
    have := mul_nonneg hv0 hQ
    linarith
  calc 8 * (x * (1 - x)) ^ 2 = 8 * (1 / 4 - y ^ 2) ^ 2 := by rw [hxy1]
    _ ≤ (1 - Real.pi ^ 2 * y ^ 2 / 2) ^ 2 * (1 / 2 + 2 * y ^ 2) := hcore
    _ = (1 - (Real.pi * y) ^ 2 / 2) ^ 2 * (x ^ 2 + (1 - x) ^ 2) := by rw [hxy2]; ring
    _ ≤ Real.sin (Real.pi * x) ^ 2 * (x ^ 2 + (1 - x) ^ 2) :=
        mul_le_mul_of_nonneg_right hs2 (by positivity)

/-- The half range `0 < x ≤ 1/2`, the two ranges joined at `1/4`. -/
lemma eight_mul_sq_le_sin_sq_pi_mul_of_le_half {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 2) :
    8 * (x * (1 - x)) ^ 2 ≤ Real.sin (Real.pi * x) ^ 2 * (x ^ 2 + (1 - x) ^ 2) := by
  rcases le_or_gt x (1 / 4) with h | h
  · exact eight_mul_sq_le_sin_sq_pi_mul_of_le_quarter hx0 h
  · exact eight_mul_sq_le_sin_sq_pi_mul_of_quarter_le h.le hx

/-- ★ **The two-point kernel inequality.** For `0 < x < 1`,
`sin²(πx) · (x² + (1−x)²) ≥ 8 · (x(1−x))²`, i.e. `sin²(πx)(1/x² + 1/(1−x)²) ≥ 8`, with equality
at `x = 1/2`. The bound BHMT assert by calculus in the proof of their Theorem 11. -/
theorem eight_mul_sq_le_sin_sq_pi_mul {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    8 * (x * (1 - x)) ^ 2 ≤ Real.sin (Real.pi * x) ^ 2 * (x ^ 2 + (1 - x) ^ 2) := by
  rcases le_or_gt x (1 / 2) with h | h
  · exact eight_mul_sq_le_sin_sq_pi_mul_of_le_half hx0 h
  · -- reflect `x ↦ 1 − x`
    have h1 := eight_mul_sq_le_sin_sq_pi_mul_of_le_half (x := 1 - x) (by linarith) (by linarith)
    have hs : Real.sin (Real.pi * (1 - x)) = Real.sin (Real.pi * x) := by
      rw [show Real.pi * (1 - x) = Real.pi - Real.pi * x by ring, Real.sin_pi_sub]
    rw [hs, sub_sub_cancel] at h1
    calc 8 * (x * (1 - x)) ^ 2 = 8 * ((1 - x) * x) ^ 2 := by ring
      _ ≤ Real.sin (Real.pi * x) ^ 2 * ((1 - x) ^ 2 + x ^ 2) := h1
      _ = Real.sin (Real.pi * x) ^ 2 * (x ^ 2 + (1 - x) ^ 2) := by ring

omit [NeZero T] in
/-- The phase state is `1`-periodic in the phase: `e^{2πi(φ+1)x} = e^{2πiφx}`. -/
lemma phaseStateR_add_one (φ : ℝ) : phaseStateR T (φ + 1) = phaseStateR T φ := by
  unfold phaseStateR
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  rw [show 2 * ↑Real.pi * Complex.I * ↑(φ + 1) * ↑(x : ℕ)
      = 2 * ↑Real.pi * Complex.I * ↑φ * ↑(x : ℕ)
        + (((x : ℕ) : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) from by
      push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Reading index `c` at phase `φ` is reading index `0` at phase `φ − c/T`: the Dirichlet
amplitude depends only on the difference. -/
lemma prob_applyQFTinv_phaseStateR_sub (φ : ℝ) (c : Fin T) :
    prob (applyQFTinv T (phaseStateR T φ)) c
      = prob (applyQFTinv T (phaseStateR T (φ - (c : ℕ) / (T : ℝ)))) 0 := by
  rw [prob, prob, applyQFTinv_phaseStateR_apply, applyQFTinv_phaseStateR_apply]
  simp only [Fin.val_zero, Nat.cast_zero, zero_div, sub_zero]

/-- On resonance the readout is certain: `prob (phaseStateR T 0) 0 = 1`. -/
lemma prob_applyQFTinv_phaseStateR_zero : prob (applyQFTinv T (phaseStateR T 0)) 0 = 1 := by
  rw [prob, applyQFTinv_phaseStateR_apply]
  simp only [Fin.val_zero, Nat.cast_zero, zero_div, sub_zero, Complex.ofReal_zero, mul_zero,
    zero_mul, Complex.exp_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  rw [inv_mul_cancel₀ (by exact_mod_cast (NeZero.ne T)), norm_one, one_pow]

/-- ★ **The two-index Dirichlet bound.** For `0 ≤ δ ≤ 1/T` the two readouts at phase distance
`δ` and `δ − 1/T` — the two grid points straddling the phase — jointly carry at least `8/π²`.
On the boundary one of them is on resonance; inside, both closed forms
(`prob_phaseStateR_eq`) share the numerator `sin²(πδT)`, the denominators are bounded by
`|sin t| ≤ |t|`, and `eight_mul_sq_le_sin_sq_pi_mul` at `x = δT` finishes. -/
theorem dirichlet_two_index (δ : ℝ) (hlo : 0 ≤ δ) (hhi : δ ≤ 1 / T) :
    8 / Real.pi ^ 2 ≤ prob (applyQFTinv T (phaseStateR T δ)) 0
      + prob (applyQFTinv T (phaseStateR T (δ - 1 / T))) 0 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hTne : T ≠ 0 := NeZero.ne T
  have hTR : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hTne
  have hTpos : (0 : ℝ) < T := by positivity
  have h8 : 8 / Real.pi ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  rcases hlo.eq_or_lt with h0 | h0
  · rw [← h0, prob_applyQFTinv_phaseStateR_zero]
    linarith [prob_nonneg (applyQFTinv T (phaseStateR T (0 - 1 / T))) (0 : Fin T)]
  rcases hhi.eq_or_lt with h1 | h1
  · rw [h1, sub_self, prob_applyQFTinv_phaseStateR_zero]
    linarith [prob_nonneg (applyQFTinv T (phaseStateR T (1 / T))) (0 : Fin T)]
  -- `0 < δ < 1/T`: `x = δT ∈ (0, 1)`
  have hx0 : 0 < δ * T := mul_pos h0 hTpos
  have hx1 : δ * T < 1 := (lt_div_iff₀ hTpos).mp h1
  have h1x : 0 < 1 - δ * T := by linarith
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (NeZero.ne T).bot_lt
  have hδ1 : δ < 1 := by nlinarith
  have hs1 : Real.sin (Real.pi * δ) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (mul_lt_of_lt_one_right hπ hδ1)).ne'
  have hs2 : Real.sin (Real.pi * (δ - 1 / T)) ≠ 0 := by
    have e : Real.pi * (δ - 1 / T) = -(Real.pi * (1 / T - δ)) := by ring
    rw [e, Real.sin_neg, neg_ne_zero]
    apply ne_of_gt
    have hpos : 0 < 1 / (T : ℝ) - δ := by linarith
    have h1T : 1 / (T : ℝ) ≤ 1 := by rw [div_le_one hTpos]; exact hT1
    exact Real.sin_pos_of_pos_of_lt_pi (mul_pos hπ hpos) (mul_lt_of_lt_one_right hπ (by linarith))
  rw [prob_phaseStateR_eq T δ 0 (by simpa using hs1),
    prob_phaseStateR_eq T (δ - 1 / T) 0 (by simpa using hs2)]
  simp only [Fin.val_zero, Nat.cast_zero, zero_div, sub_zero]
  have e1 : Real.pi * δ * T = Real.pi * (δ * T) := by ring
  have e2 : Real.pi * (δ - 1 / T) * T = Real.pi * (δ * T) - Real.pi := by
    rw [show Real.pi * (δ - 1 / T) * T = Real.pi * (δ * T) - Real.pi * (1 / T * T) by ring,
      one_div_mul_cancel hTR, mul_one]
  rw [e1, e2, Real.sin_sub_pi, neg_sq]
  -- the denominators
  have ha : 0 < Real.sin (Real.pi * δ) ^ 2 := by positivity
  have hb : 0 < Real.sin (Real.pi * (δ - 1 / T)) ^ 2 := by positivity
  have hd1 : Real.sin (Real.pi * δ) ^ 2 ≤ (Real.pi * δ) ^ 2 := Real.sin_sq_le_sq
  have hd2 : Real.sin (Real.pi * (δ - 1 / T)) ^ 2 ≤ (Real.pi * (δ - 1 / T)) ^ 2 :=
    Real.sin_sq_le_sq
  have hA : Real.sin (Real.pi * (δ * T)) ^ 2 / (Real.pi ^ 2 * (δ * T) ^ 2)
      ≤ (T : ℝ)⁻¹ ^ 2 * (Real.sin (Real.pi * (δ * T)) ^ 2 / Real.sin (Real.pi * δ) ^ 2) := by
    have e3 : (T : ℝ)⁻¹ ^ 2 * (Real.sin (Real.pi * (δ * T)) ^ 2 / (Real.pi * δ) ^ 2)
        = Real.sin (Real.pi * (δ * T)) ^ 2 / (Real.pi ^ 2 * (δ * T) ^ 2) := by
      rw [inv_pow, ← div_eq_inv_mul, div_div]
      congr 1
      ring
    rw [← e3]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (sq_nonneg _) ha hd1)
      (by positivity)
  have hB : Real.sin (Real.pi * (δ * T)) ^ 2 / (Real.pi ^ 2 * (1 - δ * T) ^ 2)
      ≤ (T : ℝ)⁻¹ ^ 2
        * (Real.sin (Real.pi * (δ * T)) ^ 2 / Real.sin (Real.pi * (δ - 1 / T)) ^ 2) := by
    have e3 : (T : ℝ)⁻¹ ^ 2 * (Real.sin (Real.pi * (δ * T)) ^ 2 / (Real.pi * (δ - 1 / T)) ^ 2)
        = Real.sin (Real.pi * (δ * T)) ^ 2 / (Real.pi ^ 2 * (1 - δ * T) ^ 2) := by
      rw [inv_pow, ← div_eq_inv_mul, div_div]
      congr 1
      rw [show (Real.pi * (δ - 1 / T)) ^ 2 * (T : ℝ) ^ 2
          = Real.pi ^ 2 * ((δ - 1 / T) * T) ^ 2 by ring,
        show (δ - 1 / T) * T = δ * T - 1 / T * T by ring, one_div_mul_cancel hTR]
      ring
    rw [← e3]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (sq_nonneg _) hb hd2)
      (by positivity)
  -- the core inequality at `x = δT`
  have hcore := eight_mul_sq_le_sin_sq_pi_mul hx0 hx1
  have hD1 : 0 < Real.pi ^ 2 * (δ * T) ^ 2 := by positivity
  have hD2 : 0 < Real.pi ^ 2 * (1 - δ * T) ^ 2 := mul_pos (by positivity) (pow_pos h1x 2)
  have hfin : 8 / Real.pi ^ 2 ≤ Real.sin (Real.pi * (δ * T)) ^ 2 / (Real.pi ^ 2 * (δ * T) ^ 2)
      + Real.sin (Real.pi * (δ * T)) ^ 2 / (Real.pi ^ 2 * (1 - δ * T) ^ 2) := by
    rw [div_add_div _ _ hD1.ne' hD2.ne', le_div_iff₀ (mul_pos hD1 hD2)]
    have e : 8 / Real.pi ^ 2 * (Real.pi ^ 2 * (δ * T) ^ 2 * (Real.pi ^ 2 * (1 - δ * T) ^ 2))
        = Real.pi ^ 2 * (8 * (δ * T * (1 - δ * T)) ^ 2) := by
      rw [div_mul_eq_mul_div, div_eq_iff (by positivity)]
      ring
    rw [e]
    calc Real.pi ^ 2 * (8 * (δ * T * (1 - δ * T)) ^ 2)
        ≤ Real.pi ^ 2 * (Real.sin (Real.pi * (δ * T)) ^ 2 * ((δ * T) ^ 2 + (1 - δ * T) ^ 2)) :=
          mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = Real.sin (Real.pi * (δ * T)) ^ 2 * (Real.pi ^ 2 * (1 - δ * T) ^ 2)
          + Real.pi ^ 2 * (δ * T) ^ 2 * Real.sin (Real.pi * (δ * T)) ^ 2 := by ring
  linarith

/-- `(c + 1 : Fin T)` below the wrap: its value is `c + 1`. -/
lemma val_add_one_fin_of_lt {c : Fin T} (h : (c : ℕ) + 1 < T) :
    ((c + 1 : Fin T) : ℕ) = (c : ℕ) + 1 := by
  rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < T), Nat.mod_eq_of_lt h]

/-- `(c + 1 : Fin T)` at the wrap `c = T − 1`: its value is `0`. -/
lemma val_add_one_fin_of_eq {c : Fin T} (h : (c : ℕ) + 1 = T) : ((c + 1 : Fin T) : ℕ) = 0 := by
  rw [Fin.val_add, Fin.val_one', Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, h, Nat.mod_self]

/-- The lower straddling index exists: for `0 ≤ φ < 1` the index `c = ⌊φT⌋` has
`0 ≤ φ − c/T ≤ 1/T`. -/
lemma exists_straddle_index (φ : ℝ) (h0 : 0 ≤ φ) (h1 : φ < 1) :
    ∃ c : Fin T, 0 ≤ φ - (c : ℕ) / (T : ℝ) ∧ φ - (c : ℕ) / (T : ℝ) ≤ 1 / T := by
  have hTpos : (0 : ℝ) < T := by have := NeZero.ne T; positivity
  have hφT : 0 ≤ φ * T := by positivity
  have hlt : ⌊φ * T⌋₊ < T := by
    rw [Nat.floor_lt hφT]
    calc φ * T < 1 * T := mul_lt_mul_of_pos_right h1 hTpos
      _ = T := one_mul _
  refine ⟨⟨⌊φ * T⌋₊, hlt⟩, ?_, ?_⟩
  · show 0 ≤ φ - (⌊φ * T⌋₊ : ℝ) / T
    rw [sub_nonneg, div_le_iff₀ hTpos]
    exact Nat.floor_le hφT
  · show φ - (⌊φ * T⌋₊ : ℝ) / T ≤ 1 / T
    have := Nat.lt_floor_add_one (φ * T)
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hTpos]
    linarith

/-- ★★ **The two-index phase-estimation bound (BHMT Theorem 11, `k = 1`, one phase).** If the
counting index `c` sits at phase distance `0 ≤ φ − c/T ≤ 1/T` below the phase, then `c` and
`c + 1` — the two grid points straddling `φ·T`, the second read modulo `T` — jointly carry at
least `8/π²`. -/
theorem phase_estimation_two_index (φ : ℝ) (c : Fin T) (hlo : 0 ≤ φ - (c : ℝ) / T)
    (hhi : φ - (c : ℝ) / T ≤ 1 / T) :
    8 / Real.pi ^ 2 ≤ prob (applyQFTinv T (phaseStateR T φ)) c
      + prob (applyQFTinv T (phaseStateR T φ)) (c + 1) := by
  have hTpos : (0 : ℝ) < T := by have := NeZero.ne T; positivity
  have hTR : (T : ℝ) ≠ 0 := hTpos.ne'
  rw [prob_applyQFTinv_phaseStateR_sub T φ c, prob_applyQFTinv_phaseStateR_sub T φ (c + 1)]
  have key := dirichlet_two_index T (φ - (c : ℝ) / T) hlo hhi
  rcases Nat.lt_or_ge ((c : ℕ) + 1) T with hlt | hge
  · rw [val_add_one_fin_of_lt T hlt]
    push_cast
    rw [show φ - ((c : ℝ) + 1) / T = φ - (c : ℝ) / T - 1 / T by ring]
    exact key
  · have hc : (c : ℕ) + 1 = T := by have := c.isLt; omega
    have hcR : ((c : ℕ) : ℝ) + 1 = T := by exact_mod_cast hc
    have hφ : φ - (c : ℝ) / T - 1 / T + 1 = φ := by
      field_simp
      linarith
    have h2 : prob (applyQFTinv T (phaseStateR T φ)) 0
        = prob (applyQFTinv T (phaseStateR T (φ - (c : ℝ) / T - 1 / T))) 0 := by
      rw [← phaseStateR_add_one T (φ - (c : ℝ) / T - 1 / T), hφ]
    rw [val_add_one_fin_of_eq T hc, Nat.cast_zero, zero_div, sub_zero, h2]
    exact key

end QuantumInfo
