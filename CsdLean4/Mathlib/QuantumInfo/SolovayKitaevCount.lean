/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.CliffordTWords
public import CsdLean4.Mathlib.QuantumInfo.SolovayKitaevStep
public import CsdLean4.Mathlib.QuantumInfo.CommutatorDecomposition

/-!
# The Solovay–Kitaev theorem, with its gate count

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #116, the last brick of #74's split, and with it link 12.

#115 proved the error side (`C²ε_n ≤ (C²ε₀)^{(3/2)ⁿ}`) and #117 the length side (`ℓ_n ≤ 5ⁿℓ₀`). Two
things were left: eliminate `n` between them, and supply the **pairing** — which word approximates a
given `U`. This file does both, so the chain ends on a single statement about Clifford+T words.

## The count

`skLevel b ε = ⌈log R / log(3/2)⌉` where `R = log ε / log b` is how many times the base accuracy's
exponent must double-and-a-half to reach `ε`. ★★ `skLevel_rpow_le` says that many levels really do
reach `ε`; ★★ `five_pow_skLevel_le` says five to that power is at most `5·R^c`, with

`skExponent = log 5 / log (3/2)`,

and ★ `three_lt_skExponent`/★ `skExponent_lt_four` place `c` in `(3, 4)` — the literature's `≈ 3.97`
— each by one application of `Real.log_lt_log` to `(3/2)³ = 27/8 < 5 < 81/16 = (3/2)⁴`. No decimal
expansion is claimed.

## The pairing

★★★ `exists_mem_skWords_norm_sub_le` is the recursion: from a net at base accuracy `e`, the level-`n`
words of #117's shape reach `skErr e n` on every determinant-one unitary. One level approximates `U`,
takes the residual `Δ = U·(ctEval u)⋆`, writes it as a group commutator of two near-identity
determinant-one factors (#114), approximates *those* one level down, and reassembles. The
reassembled approximant is a word because ★★ `star_ctEval` identifies #117's `ctInvWord` with the
adjoint — so a group commutator of word values is the value of
`v ++ w ++ ctInvWord v ++ ctInvWord w`, exactly `skWords`' shape, and the length bound transfers
untouched.

Two things had to be built for that step, neither of them bookkeeping:

* ★ `ctEval_mem_unitary` — words are unitary (`hGateM_mem_unitary`, `tGateM_mem_unitary`, which the
  corpus did not have), so right multiplication by one is an isometry and the residual is as close to
  `1` as the approximation is good;
* **the determinant.** #114 needs its input to have determinant one, and a Clifford+T word does not.
  It is *forced*: ★ `det_ctEval_pow_eight` — the determinant of a word is an eighth root of unity,
  because `H² = 1` and `T⁸ = 1` and nothing else enters — together with
  ★★ `eq_one_of_pow_eight_eq_one`: an eighth root of unity within `1/8` of `1` **is** `1`. That last
  needs no root-of-unity theory, only `(z−1)·∑_{k<8} zᵏ = z⁸ − 1 = 0` and `‖1 − zᵏ‖ ≤ k‖1 − z‖` on
  the unit circle, which bounds the sum by `28/8 < 8`.

#114 was strengthened in place to record that its factors are determinant one (`axisRot_det`,
`det_conj_of_mem_unitary`), which its construction already gave.

## The theorem

★★★ `exists_word_approx_polylog`: for every determinant-one `U` and every small enough `ε`, a
Clifford+T **word** within `ε` of `U` of length at most `K·log(1/ε)^c`.

## Honest scope

⚠️ **`K` and `ε₀` are existential, by inheritance.** #113's net comes from compactness with no bound
on its size, and the radius forcing the residual's determinant comes from continuity of `det`.
Neither is quantitative, so no constant here is. The *exponent* is.

⚠️ **The exponent is #117's cost model, not a fact about `{H, T}`.** The letters are `H`, `T` and
`T⁻¹`, so inverting a word is free and a level costs five. Over two letters a shortest `T⁻¹` is `T⁷`,
a level costs `17`, and the exponent is `log 17 / log(3/2) ≈ 6.99`. #117's ★★
`mem_cliffordT_iff_exists_word` is what makes the choice free: the three letters generate exactly the
submonoid the two do. The literature's `3 + δ` needs a different net argument and stays unclaimed.

⚠️ **Nothing is computed.** The word is produced by a recursion over an existence statement, not by
an algorithm, and `skErr`'s constant `33` is a sufficient one rather than the best.

References: C. Dawson, M. Nielsen, *The Solovay-Kitaev algorithm*, Quantum Inf. Comput. 6 (2006) 81,
§§3–5; `SolovayKitaevStep.lean` (#115), `CliffordTWords.lean` (#117), `CliffordTNet.lean` (#113),
`CommutatorDecomposition.lean` (#114), `CliffordTDensity.lean` (#81);
`specs/BACKLOG.md` #116, #74, #113, #114, #115, #117.
-/

@[expose] public section

open Matrix

open scoped Matrix.Norms.L2Operator

namespace QuantumInfo.SU2

open CliffordT

/-! ### The exponent -/

/-- The Solovay–Kitaev exponent `log 5 / log (3/2)`, in the three-letter cost model of #117. -/
noncomputable def skExponent : ℝ := Real.log 5 / Real.log (3 / 2)

theorem log_three_halves_pos : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)

theorem skExponent_pos : 0 < skExponent :=
  div_pos (Real.log_pos (by norm_num)) log_three_halves_pos

/-- ★ **The exponent is below `4`**, because `5 < (3/2)⁴ = 81/16`. -/
theorem skExponent_lt_four : skExponent < 4 := by
  rw [skExponent, div_lt_iff₀ log_three_halves_pos]
  have h : Real.log 5 < Real.log ((3 / 2 : ℝ) ^ (4 : ℕ)) := by
    refine Real.log_lt_log (by norm_num) ?_
    norm_num
  rw [Real.log_pow, show ((4 : ℕ) : ℝ) = 4 from by norm_num] at h
  linarith

/-- ★ **And above `3`**, because `(3/2)³ = 27/8 < 5`. -/
theorem three_lt_skExponent : 3 < skExponent := by
  rw [skExponent, lt_div_iff₀ log_three_halves_pos]
  have h : Real.log ((3 / 2 : ℝ) ^ (3 : ℕ)) < Real.log 5 := by
    refine Real.log_lt_log (by norm_num) ?_
    norm_num
  rw [Real.log_pow, show ((3 : ℕ) : ℝ) = 3 from by norm_num] at h
  linarith

/-! ### The level count -/

/-- The number of recursion levels needed to turn base accuracy `b` into accuracy `ε`. -/
noncomputable def skLevel (b ε : ℝ) : ℕ := ⌈Real.log (Real.log ε / Real.log b) / Real.log (3 / 2)⌉₊

section Level

variable {b ε : ℝ} (hb : 0 < b) (hb1 : b < 1) (hε : 0 < ε) (hεb : ε ≤ b)

include hb hb1 hε hεb

theorem one_le_log_ratio : 1 ≤ Real.log ε / Real.log b := by
  have hlb : Real.log b < 0 := Real.log_neg hb hb1
  have hmono : Real.log ε ≤ Real.log b := Real.log_le_log hε hεb
  rw [le_div_iff_of_neg hlb]
  linarith

theorem log_ratio_pos : 0 < Real.log ε / Real.log b :=
  lt_of_lt_of_le zero_lt_one (one_le_log_ratio hb hb1 hε hεb)

/-- `(3/2)` to the level is at least the ratio: that many levels really do reach `ε`. -/
theorem log_ratio_le_three_halves_pow :
    Real.log ε / Real.log b ≤ (3 / 2 : ℝ) ^ skLevel b ε := by
  have hR : 0 < Real.log ε / Real.log b := log_ratio_pos hb hb1 hε hεb
  have hceil : Real.log (Real.log ε / Real.log b) / Real.log (3 / 2 : ℝ)
      ≤ (skLevel b ε : ℝ) := Nat.le_ceil _
  have hmul : Real.log (Real.log ε / Real.log b)
      ≤ (skLevel b ε : ℝ) * Real.log (3 / 2 : ℝ) := by
    rw [div_le_iff₀ log_three_halves_pos] at hceil
    exact hceil
  have hexp : Real.log ε / Real.log b
      ≤ Real.exp ((skLevel b ε : ℝ) * Real.log (3 / 2 : ℝ)) := by
    rw [← Real.exp_log hR]
    exact Real.exp_le_exp.2 hmul
  rwa [show Real.exp ((skLevel b ε : ℝ) * Real.log (3 / 2 : ℝ))
      = (3 / 2 : ℝ) ^ skLevel b ε from by
        rw [← Real.log_pow, Real.exp_log (by positivity)]] at hexp

/-- ★★ **The level count reaches the target accuracy.** -/
theorem skLevel_rpow_le : b ^ ((3 / 2 : ℝ) ^ skLevel b ε) ≤ ε := by
  have hR : 0 < Real.log ε / Real.log b := log_ratio_pos hb hb1 hε hεb
  have hbR : b ^ (Real.log ε / Real.log b) = ε := by
    rw [Real.rpow_def_of_pos hb, mul_div_cancel₀ _ (ne_of_lt (Real.log_neg hb hb1)),
      Real.exp_log hε]
  calc b ^ ((3 / 2 : ℝ) ^ skLevel b ε)
      ≤ b ^ (Real.log ε / Real.log b) :=
        Real.rpow_le_rpow_of_exponent_ge hb hb1.le (log_ratio_le_three_halves_pow hb hb1 hε hεb)
    _ = ε := hbR

/-- ★★ **And five to that power is only `5·R^c`** — the whole polylogarithmic gate count, with `c`
the exponent and `R = log ε / log b` the ratio of logarithms. -/
theorem five_pow_skLevel_le :
    (5 : ℝ) ^ skLevel b ε ≤ 5 * (Real.log ε / Real.log b) ^ skExponent := by
  have hR : 0 < Real.log ε / Real.log b := log_ratio_pos hb hb1 hε hεb
  have hR1 : 1 ≤ Real.log ε / Real.log b := one_le_log_ratio hb hb1 hε hεb
  set t : ℝ := Real.log (Real.log ε / Real.log b) / Real.log (3 / 2 : ℝ) with ht
  have ht0 : 0 ≤ t := by
    rw [ht]
    exact div_nonneg (Real.log_nonneg hR1) log_three_halves_pos.le
  have hlt : (skLevel b ε : ℝ) < t + 1 := by
    rw [skLevel, ← ht]
    exact Nat.ceil_lt_add_one ht0
  have hstep : (5 : ℝ) ^ skLevel b ε ≤ (5 : ℝ) ^ (t + 1) := by
    rw [← Real.rpow_natCast (5 : ℝ) (skLevel b ε)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hlt.le
  have hsplit : (5 : ℝ) ^ (t + 1) = 5 * (5 : ℝ) ^ t := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one, mul_comm]
  have hpow : (5 : ℝ) ^ t = (Real.log ε / Real.log b) ^ skExponent := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5),
      Real.rpow_def_of_pos hR, skExponent, ht]
    congr 1
    field_simp
  calc (5 : ℝ) ^ skLevel b ε ≤ (5 : ℝ) ^ (t + 1) := hstep
    _ = 5 * (5 : ℝ) ^ t := hsplit
    _ = 5 * (Real.log ε / Real.log b) ^ skExponent := by rw [hpow]

end Level

/-! ### Clifford+T words are unitary, with determinant an eighth root of unity -/

theorem star_hGateM : star hGateM = hGateM := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hGateM, Matrix.star_apply, Complex.conj_ofReal]

theorem hGateM_mem_unitary : hGateM ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  refine Unitary.mem_iff.2 ⟨?_, ?_⟩ <;> rw [star_hGateM] <;> exact hGateM_mul_self

theorem conj_tPhase : (starRingEnd ℂ) tPhase = tPhaseInv := by
  rw [tPhase, tPhaseInv, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.ofReal_neg]
  congr 1
  ring

theorem star_tGateM : star tGateM = !![1, 0; 0, tPhaseInv] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tGateM, Matrix.star_apply, conj_tPhase]

theorem tGateM_mem_unitary : tGateM ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  refine Unitary.mem_iff.2 ⟨?_, ?_⟩ <;> rw [star_tGateM] <;> ext i j <;> fin_cases i <;>
    fin_cases j <;>
    simp [tGateM, Matrix.mul_apply, Fin.sum_univ_two, tPhaseInv_mul, tPhase_mul_inv]

theorem ctGen_mem_unitary (i : Fin 3) : ctGen i ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  fin_cases i
  · simpa [ctGen] using hGateM_mem_unitary
  · simpa [ctGen] using tGateM_mem_unitary
  · simpa [ctGen] using pow_mem tGateM_mem_unitary 7

/-- ★ **Every Clifford+T word is a unitary.** -/
theorem ctEval_mem_unitary (w : List (Fin 3)) :
    ctEval w ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  induction w with
  | nil => simp
  | cons x xs ih =>
      rw [ctEval_cons]
      exact mul_mem (ctGen_mem_unitary x) ih

/-- ★★ **The inverse word is the adjoint.** #117 produced a left inverse; for a unitary that *is*
the star, so the group commutator of two word values is again a word value. -/
theorem star_ctEval (w : List (Fin 3)) : star (ctEval w) = ctEval (ctInvWord w) := by
  have hu := ctEval_mem_unitary w
  have h := ctEval_ctInvWord w
  symm
  calc ctEval (ctInvWord w) = ctEval (ctInvWord w) * (ctEval w * star (ctEval w)) := by
        rw [Unitary.mul_star_self_of_mem hu, mul_one]
    _ = ctEval (ctInvWord w) * ctEval w * star (ctEval w) := by noncomm_ring
    _ = star (ctEval w) := by rw [h, one_mul]

theorem det_ctGen_pow_eight (i : Fin 3) : (ctGen i).det ^ 8 = 1 := by
  have hT : tGateM.det ^ 8 = 1 := by
    rw [← Matrix.det_pow, tGateM_pow_eight, Matrix.det_one]
  have hH : hGateM.det ^ 8 = 1 := by
    have h : hGateM.det * hGateM.det = 1 := by
      rw [← Matrix.det_mul, hGateM_mul_self, Matrix.det_one]
    calc hGateM.det ^ 8 = (hGateM.det * hGateM.det) ^ 4 := by ring
      _ = 1 := by rw [h, one_pow]
  have hT7 : ((tGateM ^ 7).det) ^ 8 = 1 := by
    rw [Matrix.det_pow]
    calc (tGateM.det ^ 7) ^ 8 = (tGateM.det ^ 8) ^ 7 := by ring
      _ = 1 := by rw [hT, one_pow]
  fin_cases i
  · simpa [ctGen] using hH
  · simpa [ctGen] using hT
  · simpa [ctGen] using hT7

/-- ★ **The determinant of a word is an eighth root of unity** — `det H = -1` and `det T` has order
eight, and nothing else enters. -/
theorem det_ctEval_pow_eight (w : List (Fin 3)) : (ctEval w).det ^ 8 = 1 := by
  induction w with
  | nil => simp
  | cons x xs ih =>
      rw [ctEval_cons, Matrix.det_mul, mul_pow, det_ctGen_pow_eight, ih, one_mul]

/-! ### An eighth root of unity near one is one -/

/-- ★★ **An eighth root of unity within `1/8` of `1` is `1`.** The eight roots are `2π/8` apart, so
this is a gap statement; the proof needs no root-of-unity theory, only that
`(z - 1)·∑_{k<8} zᵏ = z⁸ - 1 = 0` and that each `‖1 - zᵏ‖ ≤ k·‖1 - z‖` on the unit circle, which
bounds the sum by `28/8 < 8`. -/
theorem eq_one_of_pow_eight_eq_one {z : ℂ} (h8 : z ^ 8 = 1) (hz : ‖z - 1‖ ≤ 1 / 8) : z = 1 := by
  have hn8 : ‖z‖ ^ 8 = 1 := by rw [← norm_pow, h8, norm_one]
  have hnz : ‖z‖ = 1 := by
    rcases lt_trichotomy ‖z‖ 1 with h | h | h
    · exact absurd hn8 (by
        have := pow_lt_one₀ (norm_nonneg z) h (by norm_num : (8 : ℕ) ≠ 0); linarith)
    · exact h
    · exact absurd hn8 (by have := one_lt_pow₀ h (by norm_num : (8 : ℕ) ≠ 0); linarith)
  have hstep : ∀ k : ℕ, ‖1 - z ^ k‖ ≤ (k : ℝ) * ‖1 - z‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hsplit : (1 : ℂ) - z ^ (k + 1) = (1 - z ^ k) + z ^ k * (1 - z) := by ring
        calc ‖(1 : ℂ) - z ^ (k + 1)‖ ≤ ‖(1 : ℂ) - z ^ k‖ + ‖z ^ k * (1 - z)‖ := by
              rw [hsplit]; exact norm_add_le _ _
          _ = ‖(1 : ℂ) - z ^ k‖ + ‖1 - z‖ := by rw [norm_mul, norm_pow, hnz, one_pow, one_mul]
          _ ≤ (k : ℝ) * ‖1 - z‖ + ‖1 - z‖ := by gcongr
          _ = ((k + 1 : ℕ) : ℝ) * ‖1 - z‖ := by push_cast; ring
  by_contra hne
  have hgeo : (∑ k ∈ Finset.range 8, z ^ k) = 0 := by
    have h := geom_sum_mul z 8
    rw [h8, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hne)
  have hsum : (∑ k ∈ Finset.range 8, ((1 : ℂ) - z ^ k)) = 8 := by
    rw [Finset.sum_sub_distrib, hgeo, sub_zero]
    simp
  have hle : ‖(8 : ℂ)‖ ≤ ∑ k ∈ Finset.range 8, ‖(1 : ℂ) - z ^ k‖ := by
    rw [← hsum]; exact norm_sum_le _ _
  have hbound : (∑ k ∈ Finset.range 8, ‖(1 : ℂ) - z ^ k‖) ≤ 28 * ‖1 - z‖ := by
    calc (∑ k ∈ Finset.range 8, ‖(1 : ℂ) - z ^ k‖)
        ≤ ∑ k ∈ Finset.range 8, (k : ℝ) * ‖1 - z‖ := Finset.sum_le_sum fun k _ => hstep k
      _ = 28 * ‖1 - z‖ := by
          rw [← Finset.sum_mul]
          norm_num [Finset.sum_range_succ]
  have h1z : ‖(1 : ℂ) - z‖ ≤ 1 / 8 := by
    rwa [show (1 : ℂ) - z = -(z - 1) from by ring, norm_neg]
  rw [show ‖(8 : ℂ)‖ = (8 : ℝ) from by norm_num] at hle
  linarith

/-- The radius within which a matrix's determinant is forced within `1/8` of `1`: `det` is
continuous, and no constant is claimed. -/
theorem exists_det_radius : ∃ r : ℝ, 0 < r ∧ ∀ A : Matrix (Fin 2) (Fin 2) ℂ,
    ‖A - 1‖ < r → ‖A.det - 1‖ ≤ 1 / 8 := by
  have hcont : ContinuousAt Matrix.det (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
    (continuous_id.matrix_det).continuousAt
  obtain ⟨r, hr, hmem⟩ := Metric.continuousAt_iff.1 hcont (1 / 8) (by norm_num)
  refine ⟨r, hr, fun A hA => ?_⟩
  have hdist : dist A (1 : Matrix (Fin 2) (Fin 2) ℂ) < r := by rwa [dist_eq_norm]
  have := hmem hdist
  rw [Matrix.det_one, dist_eq_norm] at this
  exact this.le


/-! ### The error of the recursion -/

/-- The error after `n` levels of the recursion, from base accuracy `e`. The constant `33` is what
the step below actually achieves at `√e ≤ 1/2`; #115's closed form then applies to it verbatim. -/
noncomputable def skErr (e : ℝ) : ℕ → ℝ
  | 0 => e
  | n + 1 => 33 * skErr e n ^ ((3 : ℝ) / 2)

@[simp] theorem skErr_zero (e : ℝ) : skErr e 0 = e := rfl

theorem skErr_succ (e : ℝ) (n : ℕ) : skErr e (n + 1) = 33 * skErr e n ^ ((3 : ℝ) / 2) := rfl

theorem rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ ((3 : ℝ) / 2) = Real.sqrt x ^ 3 := by
  obtain ⟨t, ht0, htsq, hteq⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ^ 2 = x ∧ Real.sqrt x = t :=
    ⟨Real.sqrt x, Real.sqrt_nonneg x, Real.sq_sqrt hx, rfl⟩
  rw [hteq, ← htsq, ← Real.rpow_natCast t 2, ← Real.rpow_mul ht0,
    show ((2 : ℕ) : ℝ) * ((3 : ℝ) / 2) = ((3 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]

theorem skErr_nonneg {e : ℝ} (he : 0 ≤ e) (n : ℕ) : 0 ≤ skErr e n := by
  induction n with
  | zero => simpa using he
  | succ n ih =>
      rw [skErr_succ]
      positivity

/-- The error never exceeds the base accuracy: the recursion only improves. -/
theorem skErr_le_base {e : ℝ} (he : 0 ≤ e) (hs : Real.sqrt e ≤ 1 / 33) (n : ℕ) :
    skErr e n ≤ e := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h0 : 0 ≤ skErr e n := skErr_nonneg he n
      have hsle : Real.sqrt (skErr e n) ≤ 1 / 33 := le_trans (Real.sqrt_le_sqrt ih) hs
      have hsq : Real.sqrt (skErr e n) ^ 2 = skErr e n := Real.sq_sqrt h0
      have hcube : Real.sqrt (skErr e n) ^ 3 = skErr e n * Real.sqrt (skErr e n) := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hsq]
      rw [skErr_succ, rpow_three_halves h0, hcube]
      calc 33 * (skErr e n * Real.sqrt (skErr e n)) ≤ 33 * (skErr e n * (1 / 33)) := by gcongr
        _ = skErr e n := by ring
        _ ≤ e := ih

/-- The step's arithmetic, stated in the square root alone so that nothing can rewrite inside it. -/
theorem step_arith {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    4 * (Real.sqrt 2 * t + t ^ 2) * t ^ 2 * (1 + (Real.sqrt 2 * t + t ^ 2)) ≤ 33 * t ^ 3 := by
  have h2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h2' : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hqt : Real.sqrt 2 * t ≤ 3 / 4 := by nlinarith
  have ht2 : t ^ 2 ≤ 1 / 4 := by nlinarith
  have hb : 4 * (Real.sqrt 2 + t) * (1 + (Real.sqrt 2 * t + t ^ 2)) ≤ 33 := by
    have hA : Real.sqrt 2 + t ≤ 2 := by linarith
    have hB : 1 + (Real.sqrt 2 * t + t ^ 2) ≤ 2 := by linarith
    have hA0 : (0 : ℝ) ≤ Real.sqrt 2 + t := by linarith
    have hB0 : (0 : ℝ) ≤ 1 + (Real.sqrt 2 * t + t ^ 2) := by positivity
    nlinarith [hA, hB, hA0, hB0]
  have ht3 : (0 : ℝ) ≤ t ^ 3 := by positivity
  calc 4 * (Real.sqrt 2 * t + t ^ 2) * t ^ 2 * (1 + (Real.sqrt 2 * t + t ^ 2))
      = t ^ 3 * (4 * (Real.sqrt 2 + t) * (1 + (Real.sqrt 2 * t + t ^ 2))) := by ring
    _ ≤ t ^ 3 * 33 := by gcongr
    _ = 33 * t ^ 3 := by ring

/-- The step's error bound: `4aδ(1+a)` at `a = √2·√ε + ε` and `δ = ε` is at most `33·ε^{3/2}`. -/
theorem step_bound {ε : ℝ} (hε : 0 ≤ ε) (hs : Real.sqrt ε ≤ 1 / 2) :
    4 * (Real.sqrt 2 * Real.sqrt ε + ε) * ε * (1 + (Real.sqrt 2 * Real.sqrt ε + ε))
      ≤ 33 * ε ^ ((3 : ℝ) / 2) := by
  obtain ⟨t, ht0, htsq, hteq⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ^ 2 = ε ∧ Real.sqrt ε = t :=
    ⟨Real.sqrt ε, Real.sqrt_nonneg ε, Real.sq_sqrt hε, rfl⟩
  rw [rpow_three_halves hε, hteq, ← htsq]
  rw [hteq] at hs
  exact step_arith ht0 hs

/-! ### The recursion -/

/-- ★★★ **The Solovay–Kitaev recursion, over words.** From a net at base accuracy `e`, the level-`n`
words of #117's shape reach accuracy `skErr e n` on **every** determinant-one unitary.

This is the pairing #117 declined to make: it says *which* words approximate a given `U`. One level:
approximate `U` by a level-`n` word `u`; take the residual `Δ = U·(ctEval u)⋆`, which is within `ε`
of `1` because right multiplication by a unitary is an isometry; write `Δ` as a group commutator of
two factors `√(2ε)`-close to the identity (#114, which now also records that they are determinant
one); approximate *those* at level `n`; reassemble.

The reassembled approximant is a word because #117's `ctInvWord` inverts a word and ★★ `star_ctEval`
identifies that inverse with the adjoint — so the group commutator of two word values is the value of
`v ++ w ++ ctInvWord v ++ ctInvWord w`, which is exactly the shape of `skWords`, and #117's length
bound applies unchanged.

The determinant is the one step that is not formal: the residual must be determinant one to feed
#114, and a Clifford+T word is not. It is *forced* — the determinant of a word is an eighth root of
unity (★ `det_ctEval_pow_eight`), the residual is near `1`, and ★★ `eq_one_of_pow_eight_eq_one` says
an eighth root of unity near `1` is `1`. -/
theorem exists_mem_skWords_norm_sub_le {F : Finset (List (Fin 3))} {e r : ℝ}
    (he : 0 ≤ e) (hsmall : Real.sqrt e ≤ 1 / 33) (hr : e < r)
    (hdet : ∀ A : Matrix (Fin 2) (Fin 2) ℂ, ‖A - 1‖ < r → ‖A.det - 1‖ ≤ 1 / 8)
    (hnet : ∀ U ∈ su2Set, ∃ w ∈ F, ‖U - ctEval w‖ ≤ e) (n : ℕ) :
    ∀ U ∈ su2Set, ∃ u ∈ skWords F n, ‖U - ctEval u‖ ≤ skErr e n := by
  induction n with
  | zero =>
      intro U hU
      obtain ⟨w, hw, hdist⟩ := hnet U hU
      exact ⟨w, by simpa [skWords] using hw, by simpa using hdist⟩
  | succ n ih =>
      intro U hU
      obtain ⟨u, hu, hdu⟩ := ih U hU
      have hε0 : 0 ≤ skErr e n := skErr_nonneg he n
      have hεe : skErr e n ≤ e := skErr_le_base he hsmall n
      have hAu : ctEval u ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := ctEval_mem_unitary u
      have hUu : U ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := hU.1
      -- the residual, and why it is determinant one
      have hΔu : U * star (ctEval u) ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) :=
        mul_mem hUu (Unitary.star_mem hAu)
      have hΔeq1 : U * star (ctEval u) - 1 = (U - ctEval u) * star (ctEval u) := by
        rw [sub_mul, Unitary.mul_star_self_of_mem hAu]
      have hΔnorm : ‖U * star (ctEval u) - 1‖ = ‖U - ctEval u‖ := by
        rw [hΔeq1, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hAu)]
      have hΔle : ‖U * star (ctEval u) - 1‖ ≤ skErr e n := by rw [hΔnorm]; exact hdu
      have hΔlt : ‖U * star (ctEval u) - 1‖ < r := lt_of_le_of_lt (le_trans hΔle hεe) hr
      have hΔdet8 : (U * star (ctEval u)).det ^ 8 = 1 := by
        rw [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, hU.2,
          one_mul, ← star_pow, det_ctEval_pow_eight, star_one]
      have hΔdet : (U * star (ctEval u)).det = 1 :=
        eq_one_of_pow_eight_eq_one hΔdet8 (hdet _ hΔlt)
      -- the commutator, and its two factors at level `n`
      obtain ⟨V, W, hVu, hWu, hVd, hWd, hΔfactor, hVb, hWb⟩ :=
        exists_commutator_of_det_one hΔu hΔdet
      obtain ⟨v, hv, hdv⟩ := ih V ⟨hVu, hVd⟩
      obtain ⟨w, hw, hdw⟩ := ih W ⟨hWu, hWd⟩
      have hcvu : ctEval v ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := ctEval_mem_unitary v
      have hcwu : ctEval w ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := ctEval_mem_unitary w
      have hsqle : Real.sqrt ‖U * star (ctEval u) - 1‖ ≤ Real.sqrt (skErr e n) :=
        Real.sqrt_le_sqrt hΔle
      have hmul : Real.sqrt 2 * Real.sqrt ‖U * star (ctEval u) - 1‖
          ≤ Real.sqrt 2 * Real.sqrt (skErr e n) :=
        mul_le_mul_of_nonneg_left hsqle (Real.sqrt_nonneg 2)
      -- the four distances to the identity, at the common radius `a`
      have haV : ‖V - 1‖ ≤ Real.sqrt 2 * Real.sqrt (skErr e n) + skErr e n := by
        refine le_trans hVb ?_
        linarith
      have haW : ‖W - 1‖ ≤ Real.sqrt 2 * Real.sqrt (skErr e n) + skErr e n := by
        refine le_trans hWb ?_
        linarith
      have haV' : ‖ctEval v - 1‖ ≤ Real.sqrt 2 * Real.sqrt (skErr e n) + skErr e n := by
        have hsplit : ctEval v - 1 = ctEval v - V + (V - 1) := by abel
        have hrev : ‖ctEval v - V‖ ≤ skErr e n := by rwa [norm_sub_rev]
        calc ‖ctEval v - 1‖ ≤ ‖ctEval v - V‖ + ‖V - 1‖ := by
              rw [hsplit]; exact norm_add_le _ _
          _ ≤ skErr e n + Real.sqrt 2 * Real.sqrt ‖U * star (ctEval u) - 1‖ := by
              gcongr
          _ ≤ Real.sqrt 2 * Real.sqrt (skErr e n) + skErr e n := by linarith
      have haW' : ‖ctEval w - 1‖ ≤ Real.sqrt 2 * Real.sqrt (skErr e n) + skErr e n := by
        have hsplit : ctEval w - 1 = ctEval w - W + (W - 1) := by abel
        have hrev : ‖ctEval w - W‖ ≤ skErr e n := by rwa [norm_sub_rev]
        calc ‖ctEval w - 1‖ ≤ ‖ctEval w - W‖ + ‖W - 1‖ := by
              rw [hsplit]; exact norm_add_le _ _
          _ ≤ skErr e n + Real.sqrt 2 * Real.sqrt ‖U * star (ctEval u) - 1‖ := by
              gcongr
          _ ≤ Real.sqrt 2 * Real.sqrt (skErr e n) + skErr e n := by linarith
      -- the commutator of the two approximants, as a word
      have hcomm := CSD.SolovayKitaev.norm_groupCommutator_sub_le hVu hWu hcvu hcwu haV haW
        haV' haW' hdv hdw
      have hword : ctEval (v ++ w ++ ctInvWord v ++ ctInvWord w)
          = ctEval v * ctEval w * star (ctEval v) * star (ctEval w) := by
        rw [ctEval_append, ctEval_append, ctEval_append, star_ctEval, star_ctEval]
      refine ⟨v ++ w ++ ctInvWord v ++ ctInvWord w ++ u, ⟨v, hv, w, hw, u, hu, rfl⟩, ?_⟩
      have hUfac : U = (V * W * star V * star W) * ctEval u := by
        rw [← hΔfactor, mul_assoc, Unitary.star_mul_self_of_mem hAu, mul_one]
      have hsplitU : U - ctEval (v ++ w ++ ctInvWord v ++ ctInvWord w ++ u)
          = (V * W * star V * star W
              - ctEval v * ctEval w * star (ctEval v) * star (ctEval w)) * ctEval u := by
        rw [ctEval_append, hword, hUfac, sub_mul]
      have hiso : ‖U - ctEval (v ++ w ++ ctInvWord v ++ ctInvWord w ++ u)‖
          = ‖V * W * star V * star W
              - ctEval v * ctEval w * star (ctEval v) * star (ctEval w)‖ := by
        rw [hsplitU, CStarRing.norm_mul_mem_unitary _ hAu]
      rw [hiso, skErr_succ]
      refine le_trans hcomm ?_
      have hs2 : Real.sqrt (skErr e n) ≤ 1 / 2 := by
        have h33 : Real.sqrt (skErr e n) ≤ 1 / 33 := le_trans (Real.sqrt_le_sqrt hεe) hsmall
        linarith
      exact step_bound hε0 hs2

/-! ### The theorem -/

/-- ★★★ **Solovay–Kitaev, with the gate count: link 12's last statement.** For every `U` of
determinant one and every small enough `ε`, there is a **Clifford+T word** within `ε` of `U` whose
length is at most `K·log(1/ε)^c`, with `c = skExponent ∈ (3, 4)`.

The three inputs meet here: #117's net gives the base case and the length recursion `5ⁿℓ₀`,
★★★ `exists_mem_skWords_norm_sub_le` says which level-`n` word to take, #115's
★★★ `skError_le_rpow` turns the per-level contraction into `33²ε_n ≤ (33²ε₀)^{(3/2)ⁿ}`, and
★★ `skLevel_rpow_le`/★★ `five_pow_skLevel_le` eliminate `n` between the two.

⚠️ **`K` and `ε₀` are existential, and that is inherited, not laziness.** #113's net comes from
compactness with no bound on its size, and the radius forcing the residual's determinant comes from
continuity of `det`; neither is quantitative, so no constant here can be. What is quantitative is the
*exponent*.

⚠️ **The cost model is #117's three letters** `H`, `T`, `T⁻¹` — see this file's header. The
literature's `3 + δ` needs a different net and stays unclaimed. -/
theorem exists_word_approx_polylog :
    ∃ K e : ℝ, 0 < K ∧ 0 < e ∧ ∀ ε : ℝ, 0 < ε → ε ≤ e →
      ∀ U ∈ su2Set, ∃ u : List (Fin 3),
        ‖U - ctEval u‖ ≤ ε ∧ (u.length : ℝ) ≤ K * (Real.log ε⁻¹) ^ skExponent := by
  obtain ⟨r, hr0, hrdet⟩ := exists_det_radius
  obtain ⟨e, he0, her, hesmall⟩ : ∃ e : ℝ, 0 < e ∧ e < r ∧ e ≤ 1 / 2178 :=
    ⟨min (r / 2) (1 / 2178), lt_min (by linarith) (by norm_num),
      lt_of_le_of_lt (min_le_left _ _) (by linarith), min_le_right _ _⟩
  have hsqrt : Real.sqrt e ≤ 1 / 33 := by
    calc Real.sqrt e ≤ Real.sqrt (1 / 1089) := Real.sqrt_le_sqrt (by linarith)
      _ = 1 / 33 := by
          rw [show (1 : ℝ) / 1089 = (1 / 33) ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
  obtain ⟨F, l₀, hFlen, hFnet⟩ := exists_word_net he0
  have hnet : ∀ U ∈ su2Set, ∃ w ∈ F, ‖U - ctEval w‖ ≤ e := by
    intro U hU
    obtain ⟨w, hw, hd⟩ := hFnet U hU
    exact ⟨w, hw, le_of_lt (by rwa [← dist_eq_norm])⟩
  obtain ⟨b, hb_eq⟩ : ∃ b : ℝ, b = 1089 * e := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hb_eq]; positivity
  have hb1 : b < 1 := by rw [hb_eq]; linarith
  have hlb : Real.log b < 0 := Real.log_neg hb0 hb1
  have hlogb : 0 < Real.log b⁻¹ := by rw [Real.log_inv]; linarith
  have hKpos : 0 < 5 * ((l₀ : ℝ) + 1) / (Real.log b⁻¹) ^ skExponent :=
    div_pos (by positivity) (Real.rpow_pos_of_pos hlogb _)
  refine ⟨5 * ((l₀ : ℝ) + 1) / (Real.log b⁻¹) ^ skExponent, e, hKpos, he0, ?_⟩
  intro ε hε hεe U hU
  have h1089ε : 0 < 1089 * ε := by positivity
  have hεb : 1089 * ε ≤ b := by rw [hb_eq]; linarith
  -- the level at which the error is below `ε`
  have hclosed := CSD.SolovayKitaev.skError_le_rpow (show (0 : ℝ) < 33 by norm_num)
    (skErr_nonneg he0.le) (fun k => le_of_eq (skErr_succ e k)) (skLevel b (1089 * ε))
  have hbase : (33 : ℝ) ^ 2 * skErr e 0 = b := by rw [skErr_zero, hb_eq]; norm_num
  rw [hbase] at hclosed
  have hreach : b ^ ((3 / 2 : ℝ) ^ skLevel b (1089 * ε)) ≤ 1089 * ε :=
    skLevel_rpow_le hb0 hb1 h1089ε hεb
  have herr : skErr e (skLevel b (1089 * ε)) ≤ ε := by
    have h1 : (1089 : ℝ) * skErr e (skLevel b (1089 * ε)) ≤ 1089 * ε := by
      calc (1089 : ℝ) * skErr e (skLevel b (1089 * ε))
          = (33 : ℝ) ^ 2 * skErr e (skLevel b (1089 * ε)) := by norm_num
        _ ≤ b ^ ((3 / 2 : ℝ) ^ skLevel b (1089 * ε)) := hclosed
        _ ≤ 1089 * ε := hreach
    linarith
  -- the word, and its length
  obtain ⟨u, hu, hdu⟩ :=
    exists_mem_skWords_norm_sub_le he0.le hsqrt her hrdet hnet (skLevel b (1089 * ε)) U hU
  refine ⟨u, le_trans hdu herr, ?_⟩
  have hlenR : (u.length : ℝ) ≤ 5 ^ skLevel b (1089 * ε) * (l₀ : ℝ) := by
    have h := length_le_of_mem_skWords hFlen (skLevel b (1089 * ε)) u hu
    exact_mod_cast h
  have hfive : (5 : ℝ) ^ skLevel b (1089 * ε)
      ≤ 5 * (Real.log (1089 * ε) / Real.log b) ^ skExponent :=
    five_pow_skLevel_le hb0 hb1 h1089ε hεb
  -- the ratio of logarithms only shrinks when the `1089` is dropped
  have hinv : Real.log ε⁻¹ / Real.log b⁻¹ = Real.log ε / Real.log b := by
    rw [Real.log_inv, Real.log_inv, neg_div_neg_eq]
  have hratio : Real.log (1089 * ε) / Real.log b ≤ Real.log ε⁻¹ / Real.log b⁻¹ := by
    rw [hinv, Real.log_mul (by norm_num) (ne_of_gt hε)]
    have hdiff : Real.log ε / Real.log b - (Real.log 1089 + Real.log ε) / Real.log b
        = -Real.log 1089 / Real.log b := by
      rw [div_sub_div_same]
      congr 1
      ring
    have hnn : 0 ≤ -Real.log 1089 / Real.log b := by
      refine div_nonneg_iff.2 (Or.inr ⟨?_, hlb.le⟩)
      simp [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 1089)]
    linarith [hdiff, hnn]
  have hr0' : 0 ≤ Real.log (1089 * ε) / Real.log b := (log_ratio_pos hb0 hb1 h1089ε hεb).le
  have hlogεinv : 0 ≤ Real.log ε⁻¹ := by
    rw [Real.log_inv]
    have : Real.log ε < 0 := Real.log_neg hε (by linarith)
    linarith
  have hpow : (Real.log (1089 * ε) / Real.log b) ^ skExponent
      ≤ (Real.log ε⁻¹) ^ skExponent / (Real.log b⁻¹) ^ skExponent := by
    rw [← Real.div_rpow hlogεinv hlogb.le]
    exact Real.rpow_le_rpow hr0' hratio skExponent_pos.le
  calc (u.length : ℝ) ≤ 5 ^ skLevel b (1089 * ε) * (l₀ : ℝ) := hlenR
    _ ≤ (5 * (Real.log (1089 * ε) / Real.log b) ^ skExponent) * ((l₀ : ℝ) + 1) :=
        mul_le_mul hfive (by linarith) (by positivity)
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hr0' _))
    _ ≤ (5 * ((Real.log ε⁻¹) ^ skExponent / (Real.log b⁻¹) ^ skExponent)) * ((l₀ : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (by linarith [hpow]) (by positivity)
    _ = 5 * ((l₀ : ℝ) + 1) / (Real.log b⁻¹) ^ skExponent * (Real.log ε⁻¹) ^ skExponent := by
        ring

end QuantumInfo.SU2

end
