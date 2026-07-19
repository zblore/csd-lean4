/-
Copyright (c) 2026 CSD contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CsdLean4.LF6.PartialSchmidtCorrelation

/-!
# LF6-6: Gisin's theorem — every entangled pure two-qubit state violates CHSH

**Category:** 6-Local (closes the LF6-6 non-factorisation witness beyond maximal entanglement).

`LF6/PartialSchmidtCorrelation.lean` computes, from the Hilbert space, the Pauli correlation of the
general real-Schmidt two-qubit state `Ψ(c,s) = c|00⟩ + s|11⟩`:

    ⟨Ψ(c,s) | σ·a ⊗ σ·b | Ψ(c,s)⟩ = a_z b_z + 2cs·(a_x b_x − a_y b_y)      (`psQubit_pauli_correlation`)

and there named the **remaining** cost of LF6-6: forcing non-factorisation for *unequal* Schmidt
coefficients needs a CHSH violation for a non-maximally-entangled state — **Gisin's theorem**. The
LF6-D `Φ⁺` reduction and the CGLMP Dirichlet kernel are both specific to equal weights and do not port.
This module supplies that witness.

## The result

`gisin_chsh_violation` : for every entangled state (`0 < c`, `0 < s`, `c² + s² = 1`) there are detector
settings `a, a', b, b'` with `2 < psCHSH c s a a' b b'` — the CHSH combination of the partial-Schmidt
correlation exceeds the Bell-1964 classical bound `2`. So *every* pure entangled two-qubit state is
Bell-nonlocal (Gisin 1991).

The witness is trig-free and `c,s`-dependent (as it must be — the optimal Bob angle depends on the
concurrence). With `t = 2cs` (the concurrence) and `r = 1/√(1+t²)`:

* Alice: `a = x̂ = (1,0,0)`, `a' = ẑ = (0,0,1)`;
* Bob: `b = (t·r, 0, r)`, `b' = (−t·r, 0, r)` — unit vectors in the `x`–`z` plane tilted toward `x̂` by
  exactly the concurrence.

`gisin_chsh_value` computes the CHSH combination in closed form, `psCHSH = 2√(1 + 4c²s²)` (the Horodecki
optimum for `T = diag(2cs, −2cs, 1)`), which exceeds `2` precisely because the concurrence `2cs > 0`;
the maximally-entangled `c = s = 1/√2` recovers the Tsirelson value `2√2`.

## Grounding

`psCorr` is not a free real function: `psExpectation_eq_psCorr` identifies it with the genuine
Hilbert-space expectation `⟨Ψ(c,s)|σ·a⊗σ·b|Ψ(c,s)⟩` (via `psQubit_pauli_correlation`), so `psCHSH` is the
CHSH combination of physical two-qubit Pauli correlations, matching the singlet `chshOperator`
convention `E(a,b) − E(a,b') + E(a',b) + E(a',b')` (`Empirical/QM/Bell.lean`).

References: `LF6/PartialSchmidtCorrelation.lean` (`psQubit`, `psQubit_pauli_correlation` — the correlation
this violates); `Empirical/QM/Bell.lean` (`chshOperator`, `chsh_singlet_tsirelson_bound` — the
maximally-entangled special case); `specs/future-work.md` (LF6-6); `specs/BACKLOG.md`.
-/

open scoped BigOperators
open Matrix

namespace CSD
namespace LF6

open CSD.LF3

/-- Build a `DetectorSetting` from three real components with the unit-norm side condition
(the local analogue of `Empirical/QM/Bell.detector3`, which is `private`). -/
noncomputable def detector3 (x y z : ℝ) (h_norm : x ^ 2 + y ^ 2 + z ^ 2 = 1) : DetectorSetting where
  vec := WithLp.toLp 2 (![x, y, z] : Fin 3 → ℝ)
  unit := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [h_norm]; exact Real.sqrt_one

@[simp] lemma detector3_vec (x y z : ℝ) (h_norm : x ^ 2 + y ^ 2 + z ^ 2 = 1) (i : Fin 3) :
    (detector3 x y z h_norm).vec i = ![x, y, z] i := rfl

/-- **The real partial-Schmidt correlation** in closed form,
`E(a,b) = a_z b_z + 2cs·(a_x b_x − a_y b_y)`. Identified with the Hilbert-space expectation of
`σ·a ⊗ σ·b` on `Ψ(c,s)` by `psExpectation_eq_psCorr`. -/
noncomputable def psCorr (c s : ℝ) (a b : DetectorSetting) : ℝ :=
  a.vec 2 * b.vec 2 + 2 * c * s * (a.vec 0 * b.vec 0 - a.vec 1 * b.vec 1)

/-- **`psCorr` is the physical correlation.** For a normalised Schmidt state the closed-form real
`psCorr` equals the Hilbert-space Pauli expectation `⟨Ψ(c,s)|σ·a⊗σ·b|Ψ(c,s)⟩`. -/
theorem psExpectation_eq_psCorr (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (a b : DetectorSetting) :
    psExpectation c s (sigmaDotJoint a b) = (psCorr c s a b : ℂ) :=
  psQubit_pauli_correlation c s hcs a b

/-- **The CHSH combination of the partial-Schmidt correlation**,
`S = E(a,b) − E(a,b') + E(a',b) + E(a',b')` — the same sign convention as the singlet `chshOperator`. -/
noncomputable def psCHSH (c s : ℝ) (a a' b b' : DetectorSetting) : ℝ :=
  psCorr c s a b - psCorr c s a b' + psCorr c s a' b + psCorr c s a' b'

/-! ### The Gisin witness settings -/

/-- Alice's first setting `a = x̂ = (1,0,0)`. -/
noncomputable def gisinA : DetectorSetting := detector3 1 0 0 (by ring)

/-- Alice's second setting `a' = ẑ = (0,0,1)`. -/
noncomputable def gisinA' : DetectorSetting := detector3 0 0 1 (by ring)

/-- `r = 1/√(1+t²)` with `t = 2cs`, squared: `r² = (1+(2cs)²)⁻¹`. -/
private lemma gisin_r_sq (c s : ℝ) :
    ((Real.sqrt (1 + (2 * c * s) ^ 2))⁻¹) ^ 2 = (1 + (2 * c * s) ^ 2)⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (by positivity)]

/-- The unit-norm condition for Bob's `b = (t·r, 0, r)`: `(t·r)² + 0² + r² = 1`. -/
private lemma gisin_B_norm (c s : ℝ) :
    (2 * c * s * (Real.sqrt (1 + (2 * c * s) ^ 2))⁻¹) ^ 2 + (0 : ℝ) ^ 2
      + ((Real.sqrt (1 + (2 * c * s) ^ 2))⁻¹) ^ 2 = 1 := by
  have hpos : (0 : ℝ) < 1 + (2 * c * s) ^ 2 := by positivity
  rw [mul_pow, gisin_r_sq]
  field_simp
  ring

/-- The unit-norm condition for Bob's `b' = (−t·r, 0, r)`. -/
private lemma gisin_B'_norm (c s : ℝ) :
    (-(2 * c * s * (Real.sqrt (1 + (2 * c * s) ^ 2))⁻¹)) ^ 2 + (0 : ℝ) ^ 2
      + ((Real.sqrt (1 + (2 * c * s) ^ 2))⁻¹) ^ 2 = 1 := by
  rw [neg_pow]; simpa using gisin_B_norm c s

/-- Bob's first setting `b = (t·r, 0, r)`, `t = 2cs`, `r = 1/√(1+t²)` — a unit vector in the `x`–`z`
plane tilted toward `x̂` by the concurrence. -/
noncomputable def gisinB (c s : ℝ) : DetectorSetting :=
  detector3 (2 * c * s * (Real.sqrt (1 + (2 * c * s) ^ 2))⁻¹) 0
    ((Real.sqrt (1 + (2 * c * s) ^ 2))⁻¹) (gisin_B_norm c s)

/-- Bob's second setting `b' = (−t·r, 0, r)` (the `x`-reflection of `b`). -/
noncomputable def gisinB' (c s : ℝ) : DetectorSetting :=
  detector3 (-(2 * c * s * (Real.sqrt (1 + (2 * c * s) ^ 2))⁻¹)) 0
    ((Real.sqrt (1 + (2 * c * s) ^ 2))⁻¹) (gisin_B'_norm c s)

/-- **The CHSH value on the Gisin witness** is `2√(1 + (2cs)²)` — the Horodecki optimum for the
correlation matrix `T = diag(2cs, −2cs, 1)`. At maximal entanglement `2cs = 1` this is `2√2`, the
Tsirelson bound. -/
theorem gisin_chsh_value (c s : ℝ) :
    psCHSH c s gisinA gisinA' (gisinB c s) (gisinB' c s)
      = 2 * Real.sqrt (1 + (2 * c * s) ^ 2) := by
  simp only [psCHSH, psCorr, gisinA, gisinA', gisinB, gisinB', detector3_vec,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  -- LHS collapses to `2·r·(1+(2cs)²)` with `r = (√(1+(2cs)²))⁻¹`; `Real.div_sqrt` turns it into `2√`.
  have hkey : (1 + (2 * c * s) ^ 2) * (Real.sqrt (1 + (2 * c * s) ^ 2))⁻¹
      = Real.sqrt (1 + (2 * c * s) ^ 2) := by
    rw [inv_eq_one_div, mul_one_div, Real.div_sqrt]
  linear_combination 2 * hkey

/-- **The Gisin witness beats the classical bound:** `2 < psCHSH` for the closed-form correlation, since
`psCHSH = 2√(1 + (2cs)²)` and the concurrence `2cs > 0`. (Pure statement about the settings; the physical
reading is `gisin_chsh_violation` below.) -/
theorem gisin_psCHSH_gt_two (c s : ℝ) (hc : 0 < c) (hs : 0 < s) :
    2 < psCHSH c s gisinA gisinA' (gisinB c s) (gisinB' c s) := by
  rw [gisin_chsh_value]
  have ht : (0 : ℝ) < (2 * c * s) ^ 2 := by positivity
  have h1 : (1 : ℝ) < 1 + (2 * c * s) ^ 2 := by linarith
  have hgt : (1 : ℝ) < Real.sqrt (1 + (2 * c * s) ^ 2) := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) h1
    rwa [Real.sqrt_one] at h
  linarith

/-- **Gisin's theorem (two-qubit, real-Schmidt form).** Every pure entangled two-qubit state
`Ψ(c,s) = c|00⟩ + s|11⟩` (with `0 < c`, `0 < s`, `c² + s² = 1`) violates the CHSH inequality: there are
detector settings `a, a', b, b'` for which the CHSH combination of the **genuine Hilbert-space Pauli
expectations** `⟨Ψ(c,s)|σ·a⊗σ·b|Ψ(c,s)⟩` exceeds the Bell-1964 classical bound `2`. The witness is
`gisinA/gisinA'/gisinB/gisinB'`, giving `2√(1 + (2cs)²) > 2` since the concurrence `2cs > 0`; every
pure entangled two-qubit state is thus Bell-nonlocal (Gisin 1991). The normalisation `c² + s² = 1` is
what identifies the closed-form `psCorr` with the physical expectation (`psExpectation_eq_psCorr`). -/
theorem gisin_chsh_violation (c s : ℝ) (hc : 0 < c) (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1) :
    ∃ a a' b b' : DetectorSetting,
      2 < (psExpectation c s (sigmaDotJoint a b)).re
            - (psExpectation c s (sigmaDotJoint a b')).re
            + (psExpectation c s (sigmaDotJoint a' b)).re
            + (psExpectation c s (sigmaDotJoint a' b')).re := by
  refine ⟨gisinA, gisinA', gisinB c s, gisinB' c s, ?_⟩
  simp only [psExpectation_eq_psCorr c s hcs, Complex.ofReal_re]
  exact gisin_psCHSH_gt_two c s hc hs

end LF6
end CSD
