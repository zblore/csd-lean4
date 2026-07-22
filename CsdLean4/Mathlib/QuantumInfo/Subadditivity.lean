/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Mathlib.QuantumInfo.Entropy
import CsdLean4.Mathlib.QuantumInfo.PartialTrace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef

/-!
# Relative entropy, Klein's inequality, subadditivity (K1-B.2)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

This file delivers the **quantum relative entropy** `D(ρ‖σ) = Tr(ρ log ρ) − Tr(ρ log σ)`,
**Klein's inequality** `D(ρ‖σ) ≥ 0` (for positive-definite `σ`), the **Kronecker-log operator
split** `log(ρ_A ⊗ ρ_B) = log ρ_A ⊗ I + I ⊗ log ρ_B` (`cfc_log_kronecker`), and the von Neumann
**subadditivity** headline `S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)` (`vonNeumannEntropy_subadditive`). This is
the K1-B.2 tranche of `specs/k1-plan.md`. It builds on the spectral von Neumann entropy of
`Entropy.lean` and the matrix partial trace of `PartialTrace.lean`.

## The Kronecker-log operator split (the former K1-B.2 wall, now closed)

The linchpin for subadditivity is `cfc_log_kronecker`:

  `log(ρ_A ⊗ ρ_B) = log ρ_A ⊗ I + I ⊗ log ρ_B`   (both factors positive-definite).

The proof routes through `cfc_eq_conj_diagonal`: if `M = U · diagonal d · Uᴴ` (`U` unitary, `d`
real) then `hM.cfc f = U · diagonal (↑∘f∘d) · Uᴴ`, proved via **Lagrange interpolation** of `f`
on the (finite) spectrum — `hM.cfc f = aeval M q` for an interpolating polynomial `q`, then `aeval`
conjugates through `U` and acts diagonally. This sidesteps the eigenvector-ambiguity / sorting
subtlety entirely (it holds for the `W = U_A ⊗ U_B` decomposition, not only the canonical
eigenvectorUnitary). Applied to `ρ_A ⊗ ρ_B = W · diagonal(λ_A·λ_B) · Wᴴ`
(`kronecker_eq_conj_diagonal_eigenvalues`), with the per-eigenvalue split
`log(λ_A,i · λ_B,j) = log λ_A,i + log λ_B,j` (positive-definite ⟹ all eigenvalues `> 0`) and
`mul_kronecker_mul` distribution, this gives the operator split. Subadditivity then follows
mechanically from `klein_inequality` at `σ = ρ_A ⊗ ρ_B` + the reduced-trace identities
`trace_mul_kronecker_one_right`/`_left` + `re_trace_self_log`.

## The doubly-stochastic overlap matrix

The technical core is the **overlap matrix** `V = U_ρᴴ U_σ` between the two eigenbases of `ρ` and
`σ`, with `Dᵢⱼ = ‖Vᵢⱼ‖²` doubly stochastic (`overlapV_row_sum`, `overlapV_col_sum`: rows and
columns of `D` sum to `1`, from the unitarity `Vᴴ V = V Vᴴ = 1`). The **cross-term spectral
expansion**

  `Tr(ρ · cfc g σ) = ∑ᵢ ∑ⱼ pᵢ · g(qⱼ) · ‖Vᵢⱼ‖²`   (`trace_mul_cfc_eq`),

`p`/`q` the eigenvalues of `ρ`/`σ`, is the linchpin: it expresses the trace of a product of two
operators in **different** eigenbases through the doubly-stochastic overlap.

## Klein's inequality (the positive-definite-`σ` form)

`Klein`/`relEntropy_nonneg` is proved for `σ` **positive-definite** (all `qⱼ > 0`). Writing
`∑ᵢ pᵢ log pᵢ = ∑ᵢⱼ ‖Vᵢⱼ‖² pᵢ log pᵢ` (row stochasticity) and pairing against the cross term,

  `D(ρ‖σ) = ∑ᵢⱼ ‖Vᵢⱼ‖² · pᵢ · (log pᵢ − log qⱼ) ≥ ∑ᵢⱼ ‖Vᵢⱼ‖² (pᵢ − qⱼ) = 1 − 1 = 0`,

where the entrywise bound `pᵢ(log pᵢ − log qⱼ) ≥ pᵢ − qⱼ` is the scalar Gibbs step
`log(qⱼ/pᵢ) ≤ qⱼ/pᵢ − 1` (`Real.log_le_sub_one_of_pos`), and the final collapse uses **both** row
and column stochasticity. This route uses only the scalar `log_le_sub_one`, **not** a
concave-Jensen step, so it is robust at zero `‖Vᵢⱼ‖²` weights and at `pᵢ = 0`.

**Honest scope.** The positive-definiteness of `σ` in Klein is load-bearing and not cosmetic:
with Mathlib's junk value `Real.log 0 = 0`, the *finite* expression `Tr(ρ log ρ) − Tr(ρ log σ)`
can be **negative** when `supp ρ ⊄ supp σ` (the genuine `D(ρ‖σ) = +∞` case), so Klein's `≥ 0` is
**false** as stated without a support hypothesis; `σ` positive-definite is the standard clean
sufficient condition. Correspondingly `vonNeumannEntropy_subadditive` hypothesises the **marginals**
`ρ_A = Tr_B ρ_AB`, `ρ_B = Tr_A ρ_AB` **positive-definite** (so `ρ_A ⊗ ρ_B` is PD for the Klein
step), and only `ρ_AB.PosSemidef` + `ρ_AB.trace = 1`. It does **NOT** assume `ρ_AB` itself
positive-definite — that would exclude the physically important pure entangled states (where
`S(ρ_AB) = 0` and the marginals are full-rank mixed), which the statement covers. The bound is
genuinely an inequality on correlated `ρ_AB` (equality only at product states), not a vacuous
product-state identity. The general singular-marginal case and **Araki–Lieb**
`|S(ρ_A) − S(ρ_B)| ≤ S(ρ_AB)` (which needs a purification construction) are deferred. See
`specs/k1-plan.md` for the ledger.
-/

open Matrix
open scoped ComplexOrder Kronecker

namespace QuantumInfo

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The overlap matrix and its double stochasticity -/

/-- The **overlap matrix** `V = U_ρᴴ U_σ` between the eigenvector unitaries of `ρ` and `σ`.
Its entries `Vᵢⱼ = ⟨aᵢ, bⱼ⟩` are the inner products of the two eigenbases; `‖Vᵢⱼ‖²` is the
doubly-stochastic overlap that mediates the cross term `Tr(ρ log σ)`. -/
noncomputable def overlapV {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    Matrix n n ℂ :=
  star (hρ.eigenvectorUnitary : Matrix n n ℂ) * (hσ.eigenvectorUnitary : Matrix n n ℂ)

/-- `Vᴴ V = 1`: the overlap matrix is unitary (left inverse). -/
theorem overlapV_star_mul_self {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    star (overlapV hρ hσ) * (overlapV hρ hσ) = 1 := by
  unfold overlapV
  have hρρ : (hρ.eigenvectorUnitary : Matrix n n ℂ) * star (hρ.eigenvectorUnitary : Matrix n n ℂ)
      = 1 := Unitary.coe_mul_star_self hρ.eigenvectorUnitary
  rw [StarMul.star_mul, star_star]
  rw [show star (hσ.eigenvectorUnitary : Matrix n n ℂ) * (hρ.eigenvectorUnitary : Matrix n n ℂ)
      * (star (hρ.eigenvectorUnitary : Matrix n n ℂ) * (hσ.eigenvectorUnitary : Matrix n n ℂ))
      = star (hσ.eigenvectorUnitary : Matrix n n ℂ)
        * ((hρ.eigenvectorUnitary : Matrix n n ℂ) * star (hρ.eigenvectorUnitary : Matrix n n ℂ))
        * (hσ.eigenvectorUnitary : Matrix n n ℂ) by
    simp only [Matrix.mul_assoc]]
  rw [hρρ, Matrix.mul_one, Unitary.coe_star_mul_self]

/-- `V Vᴴ = 1`: the overlap matrix is unitary (right inverse). -/
theorem overlapV_mul_star_self {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    (overlapV hρ hσ) * star (overlapV hρ hσ) = 1 := by
  unfold overlapV
  have hσσ : (hσ.eigenvectorUnitary : Matrix n n ℂ) * star (hσ.eigenvectorUnitary : Matrix n n ℂ)
      = 1 := Unitary.coe_mul_star_self hσ.eigenvectorUnitary
  rw [StarMul.star_mul, star_star]
  rw [show star (hρ.eigenvectorUnitary : Matrix n n ℂ) * (hσ.eigenvectorUnitary : Matrix n n ℂ)
      * (star (hσ.eigenvectorUnitary : Matrix n n ℂ) * (hρ.eigenvectorUnitary : Matrix n n ℂ))
      = star (hρ.eigenvectorUnitary : Matrix n n ℂ)
        * ((hσ.eigenvectorUnitary : Matrix n n ℂ) * star (hσ.eigenvectorUnitary : Matrix n n ℂ))
        * (hρ.eigenvectorUnitary : Matrix n n ℂ) by
    simp only [Matrix.mul_assoc]]
  rw [hσσ, Matrix.mul_one, Unitary.coe_star_mul_self]

/-- **Row stochasticity:** `∑ⱼ ‖Vᵢⱼ‖² = 1`, from `(V Vᴴ)ᵢᵢ = 1`. -/
theorem overlapV_row_sum {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (i : n) :
    ∑ j, ‖overlapV hρ hσ i j‖ ^ 2 = 1 := by
  have hii := congrFun (congrFun (overlapV_mul_star_self hρ hσ) i) i
  simp only [Matrix.mul_apply, Matrix.one_apply_eq, Matrix.star_apply] at hii
  have hre := congrArg Complex.re hii
  rw [Complex.re_sum, Complex.one_re] at hre
  rw [← hre]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- **Column stochasticity:** `∑ᵢ ‖Vᵢⱼ‖² = 1`, from `(Vᴴ V)ⱼⱼ = 1`. -/
theorem overlapV_col_sum {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (j : n) :
    ∑ i, ‖overlapV hρ hσ i j‖ ^ 2 = 1 := by
  have hjj := congrFun (congrFun (overlapV_star_mul_self hρ hσ) j) j
  simp only [Matrix.mul_apply, Matrix.one_apply_eq, Matrix.star_apply] at hjj
  have hre := congrArg Complex.re hjj
  rw [Complex.re_sum, Complex.one_re] at hre
  rw [← hre]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

/-! ## The cross-term spectral expansion -/

/-- **Cyclic reduction:** `Tr(ρ · cfc g σ) = Tr(diag(p) · V · diag(g∘q) · Vᴴ)`, where
`p`/`q` are the eigenvalues of `ρ`/`σ` and `V = overlapV`. From the two spectral forms
`ρ = U_ρ diag(p) U_ρᴴ`, `cfc g σ = U_σ diag(g∘q) U_σᴴ` and trace cyclicity. -/
theorem trace_mul_cfc_cyclic {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (g : ℝ → ℝ) :
    (ρ * hσ.cfc g).trace
      = (diagonal (fun i => (RCLike.ofReal (hρ.eigenvalues i) : ℂ))
          * overlapV hρ hσ
          * diagonal (fun j => (RCLike.ofReal (g (hσ.eigenvalues j)) : ℂ))
          * star (overlapV hρ hσ)).trace := by
  set Up := (hρ.eigenvectorUnitary : Matrix n n ℂ) with hUp
  set Uσ := (hσ.eigenvectorUnitary : Matrix n n ℂ) with hUσ
  set Dp := diagonal (fun i => (RCLike.ofReal (hρ.eigenvalues i) : ℂ)) with hDp
  set Dg := diagonal (fun j => (RCLike.ofReal (g (hσ.eigenvalues j)) : ℂ)) with hDg
  have hρ_eq : ρ = Up * Dp * star Up := by
    conv_lhs => rw [hρ.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  have hcfc_eq : hσ.cfc g = Uσ * Dg * star Uσ := by
    unfold Matrix.IsHermitian.cfc
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  show (ρ * hσ.cfc g).trace
      = (Dp * (star Up * Uσ) * Dg * star (star Up * Uσ)).trace
  rw [StarMul.star_mul, star_star]
  conv_lhs => rw [hρ_eq, hcfc_eq]
  rw [show Up * Dp * star Up * (Uσ * Dg * star Uσ)
      = Up * (Dp * (star Up * Uσ) * Dg * star Uσ) by
    simp only [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm]
  congr 1
  simp only [Matrix.mul_assoc]

/-- **Diagonal expansion:** `Tr(diag(p) · V · diag(c) · Vᴴ) = ∑ᵢ ∑ⱼ pᵢ · cⱼ · ‖Vᵢⱼ‖²`. -/
theorem trace_diag_overlap_expand {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (g : ℝ → ℝ) :
    (diagonal (fun i => (RCLike.ofReal (hρ.eigenvalues i) : ℂ))
        * overlapV hρ hσ
        * diagonal (fun j => (RCLike.ofReal (g (hσ.eigenvalues j)) : ℂ))
        * star (overlapV hρ hσ)).trace
      = ∑ i, ∑ j, (RCLike.ofReal (hρ.eigenvalues i) : ℂ)
          * (RCLike.ofReal (g (hσ.eigenvalues j)) : ℂ)
          * (RCLike.ofReal (‖overlapV hρ hσ i j‖ ^ 2) : ℂ) := by
  set V := overlapV hρ hσ with hVdef
  set p := fun i => (RCLike.ofReal (hρ.eigenvalues i) : ℂ) with hp
  set c := fun j => (RCLike.ofReal (g (hσ.eigenvalues j)) : ℂ) with hc
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply]
  have hentry : ∀ x, (diagonal p * V * diagonal c) i x = p i * V i x * c x := by
    intro x
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb; rw [if_neg (Ne.symm hb)]; ring
      · intro hi; exact absurd (Finset.mem_univ i) hi
    · intro b _ hb; rw [if_neg hb]; ring
    · intro hx; exact absurd (Finset.mem_univ x) hx
  simp_rw [hentry]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.star_apply, Complex.star_def]
  rw [show p i * V i j * c j * (starRingEnd ℂ) (V i j)
      = p i * c j * (V i j * (starRingEnd ℂ) (V i j)) by ring]
  rw [Complex.mul_conj]
  rw [show (Complex.normSq (V i j) : ℂ) = (RCLike.ofReal (‖V i j‖ ^ 2) : ℂ) by
    rw [Complex.normSq_eq_norm_sq]; rfl]

/-- **The cross-term spectral expansion (headline):**
`Tr(ρ · cfc g σ) = ∑ᵢ ∑ⱼ pᵢ · g(qⱼ) · ‖Vᵢⱼ‖²`, combining the cyclic reduction and the diagonal
expansion. -/
theorem trace_mul_cfc_eq {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (g : ℝ → ℝ) :
    (ρ * hσ.cfc g).trace
      = ∑ i, ∑ j, (RCLike.ofReal (hρ.eigenvalues i) : ℂ)
          * (RCLike.ofReal (g (hσ.eigenvalues j)) : ℂ)
          * (RCLike.ofReal (‖overlapV hρ hσ i j‖ ^ 2) : ℂ) := by
  rw [trace_mul_cfc_cyclic hρ hσ g, trace_diag_overlap_expand hρ hσ g]

/-- The **real part** of the cross term: `Re Tr(ρ · cfc g σ) = ∑ᵢ ∑ⱼ pᵢ · g(qⱼ) · ‖Vᵢⱼ‖²`. -/
theorem re_trace_mul_cfc_eq {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (g : ℝ → ℝ) :
    RCLike.re ((ρ * hσ.cfc g).trace)
      = ∑ i, ∑ j, hρ.eigenvalues i * g (hσ.eigenvalues j) * ‖overlapV hρ hσ i j‖ ^ 2 := by
  rw [trace_mul_cfc_eq hρ hσ g]
  rw [show (RCLike.re : ℂ → ℝ) = Complex.re from rfl, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  norm_cast

/-! ## Relative entropy and Klein's inequality -/

/-- The **quantum relative entropy** `D(ρ‖σ) = Re Tr(ρ log ρ) − Re Tr(ρ log σ)`, defined on the
operator-trace form. With `cfc Real.log σ = log σ`, this is the standard
`Tr(ρ log ρ − ρ log σ)`. -/
noncomputable def relEntropy {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    ℝ :=
  RCLike.re ((ρ * hρ.cfc Real.log).trace) - RCLike.re ((ρ * hσ.cfc Real.log).trace)

/-- The **`ρ log ρ` self-term** is the eigenvalue sum `∑ᵢ pᵢ log pᵢ` (single eigenbasis):
`Re Tr(ρ · cfc log ρ) = ∑ᵢ pᵢ log pᵢ`. From `re_trace_cfc` at `f = (x ↦ x log x)` and
`cfc_id_mul_log` (the cfc `ρ log ρ` is `cfc (x ↦ x log x) ρ`). -/
theorem re_trace_self_log {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    RCLike.re ((ρ * hρ.cfc Real.log).trace)
      = ∑ i, hρ.eigenvalues i * Real.log (hρ.eigenvalues i) := by
  rw [cfc_id_mul_log hρ, ← hρ.cfc_eq (fun x => x * Real.log x),
    re_trace_cfc hρ (fun x => x * Real.log x)]

/-- **Klein's inequality / relative-entropy non-negativity (positive-definite `σ`):**
`D(ρ‖σ) ≥ 0` for a density operator `ρ` and a **positive-definite** density `σ`.

`σ` positive-definite (`qⱼ > 0`) is load-bearing: see the file docstring — without a support
hypothesis the *finite* (junk-`log 0`) expression can be negative. The proof writes
`D(ρ‖σ) = ∑ᵢⱼ ‖Vᵢⱼ‖² pᵢ (log pᵢ − log qⱼ) ≥ ∑ᵢⱼ ‖Vᵢⱼ‖² (pᵢ − qⱼ) = 0` via the scalar
`Real.log_le_sub_one_of_pos` and double stochasticity (both `overlapV_row_sum` and
`overlapV_col_sum`). -/
theorem relEntropy_nonneg {ρ σ : Matrix n n ℂ} (hpsdρ : ρ.PosSemidef) (hpdσ : σ.PosDef)
    (htrρ : ρ.trace = 1) (htrσ : σ.trace = 1) :
    0 ≤ relEntropy hpsdρ.1 hpdσ.1 := by
  set p := hpsdρ.1.eigenvalues with hp
  set q := hpdσ.1.eigenvalues with hq
  set V := overlapV hpsdρ.1 hpdσ.1 with hV
  -- eigenvalue positivity / non-negativity
  have hpnn : ∀ i, 0 ≤ p i := fun i => hpsdρ.eigenvalues_nonneg i
  have hqpos : ∀ j, 0 < q j := fun j => hpdσ.eigenvalues_pos j
  -- eigenvalue sums (= 1)
  have hsump : ∑ i, p i = 1 := by
    have h := hpsdρ.1.trace_eq_sum_eigenvalues
    rw [htrρ] at h
    have hre := congrArg Complex.re h
    rw [Complex.one_re, Complex.re_sum] at hre
    simpa using hre.symm
  have hsumq : ∑ j, q j = 1 := by
    have h := hpdσ.1.trace_eq_sum_eigenvalues
    rw [htrσ] at h
    have hre := congrArg Complex.re h
    rw [Complex.one_re, Complex.re_sum] at hre
    simpa using hre.symm
  -- rewrite both trace terms spectrally.
  rw [relEntropy, re_trace_self_log hpsdρ.1, re_trace_mul_cfc_eq hpsdρ.1 hpdσ.1 Real.log]
  -- ∑ᵢ pᵢ log pᵢ = ∑ᵢ ∑ⱼ ‖Vᵢⱼ‖² pᵢ log pᵢ (row stochasticity).
  have hself : ∑ i, p i * Real.log (p i)
      = ∑ i, ∑ j, ‖V i j‖ ^ 2 * (p i * Real.log (p i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, overlapV_row_sum hpsdρ.1 hpdσ.1 i, one_mul]
  rw [hself]
  -- D = ∑ᵢⱼ [‖Vᵢⱼ‖² pᵢ log pᵢ − pᵢ log qⱼ ‖Vᵢⱼ‖²] = ∑ᵢⱼ ‖Vᵢⱼ‖² pᵢ (log pᵢ − log qⱼ).
  rw [← Finset.sum_sub_distrib]
  have hcombine : ∀ i, (∑ j, ‖V i j‖ ^ 2 * (p i * Real.log (p i)))
        - (∑ j, p i * Real.log (q j) * ‖V i j‖ ^ 2)
      = ∑ j, ‖V i j‖ ^ 2 * (p i * (Real.log (p i) - Real.log (q j))) := by
    intro i
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [Finset.sum_congr rfl (fun i _ => hcombine i)]
  -- entrywise bound: ‖Vᵢⱼ‖² pᵢ (log pᵢ − log qⱼ) ≥ ‖Vᵢⱼ‖² (pᵢ − qⱼ).
  have hbound : ∀ i j, ‖V i j‖ ^ 2 * (p i - q j)
      ≤ ‖V i j‖ ^ 2 * (p i * (Real.log (p i) - Real.log (q j))) := by
    intro i j
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    -- pᵢ (log pᵢ − log qⱼ) ≥ pᵢ − qⱼ.
    rcases eq_or_lt_of_le (hpnn i) with h0 | hpos
    · simp [← h0]; linarith [(hqpos j).le]
    · have hlog : Real.log (q j) - Real.log (p i) = Real.log (q j / p i) := by
        rw [Real.log_div (ne_of_gt (hqpos j)) (ne_of_gt hpos)]
      have hle : Real.log (q j / p i) ≤ q j / p i - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (hqpos j) hpos)
      have : p i * (Real.log (q j) - Real.log (p i)) ≤ q j - p i := by
        rw [hlog]
        calc p i * Real.log (q j / p i) ≤ p i * (q j / p i - 1) :=
              mul_le_mul_of_nonneg_left hle hpos.le
          _ = q j - p i := by field_simp
      nlinarith [this]
  -- sum up the entrywise bound, then collapse the lower bound to 0.
  have hge : (∑ i, ∑ j, ‖V i j‖ ^ 2 * (p i - q j))
      ≤ ∑ i, ∑ j, ‖V i j‖ ^ 2 * (p i * (Real.log (p i) - Real.log (q j))) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hbound i j
  refine le_trans ?_ hge
  -- ∑ᵢⱼ ‖Vᵢⱼ‖²(pᵢ − qⱼ) = ∑ᵢ pᵢ − ∑ⱼ qⱼ = 0.
  have hcollapse : (∑ i, ∑ j, ‖V i j‖ ^ 2 * (p i - q j)) = 0 := by
    have expand : ∀ i, (∑ j, ‖V i j‖ ^ 2 * (p i - q j))
        = p i - ∑ j, ‖V i j‖ ^ 2 * q j := by
      intro i
      rw [show (∑ j, ‖V i j‖ ^ 2 * (p i - q j))
          = (∑ j, ‖V i j‖ ^ 2 * p i) - ∑ j, ‖V i j‖ ^ 2 * q j from by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring]
      rw [← Finset.sum_mul, overlapV_row_sum hpsdρ.1 hpdσ.1 i, one_mul]
    rw [Finset.sum_congr rfl (fun i _ => expand i), Finset.sum_sub_distrib, hsump]
    -- ∑ᵢ ∑ⱼ ‖Vᵢⱼ‖² qⱼ = ∑ⱼ qⱼ ∑ᵢ ‖Vᵢⱼ‖² = ∑ⱼ qⱼ = 1.
    rw [Finset.sum_comm]
    rw [show (∑ j, ∑ i, ‖V i j‖ ^ 2 * q j) = ∑ j, (∑ i, ‖V i j‖ ^ 2) * q j from
      Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]]
    rw [Finset.sum_congr rfl (fun j _ => by rw [overlapV_col_sum hpsdρ.1 hpdσ.1 j, one_mul])]
    rw [hsumq]; ring
  rw [hcollapse]

/-- **Klein's inequality** (named form): `Tr(ρ log ρ) ≥ Tr(ρ log σ)` for a density `ρ` and a
positive-definite density `σ`. Equivalent to `relEntropy_nonneg`. -/
theorem klein_inequality {ρ σ : Matrix n n ℂ} (hpsdρ : ρ.PosSemidef) (hpdσ : σ.PosDef)
    (htrρ : ρ.trace = 1) (htrσ : σ.trace = 1) :
    RCLike.re ((ρ * hpdσ.1.cfc Real.log).trace)
      ≤ RCLike.re ((ρ * hpsdρ.1.cfc Real.log).trace) := by
  have := relEntropy_nonneg hpsdρ hpdσ htrρ htrσ
  rw [relEntropy] at this
  linarith

/-! ## Partial-trace / Kronecker-identity trace lemmas (subadditivity prerequisites)

These connect a bipartite trace against a `X ⊗ I` (resp. `I ⊗ Y`) observable to a trace of the
reduced state, the bridge needed to read `Tr(ρ_AB · log(ρ_A ⊗ ρ_B))` as `−S(ρ_A) − S(ρ_B)` once
the **Kronecker-log split** `log(ρ_A ⊗ ρ_B) = log ρ_A ⊗ I + I ⊗ log ρ_B` is available. See the
module docstring and `specs/k1-plan.md` for the status of that split (the remaining K1-B.2 wall). -/

section PartialTraceTrace

variable {m : Type*} [Fintype m] [DecidableEq m]

omit [DecidableEq n] in
/-- **Reduced-trace identity (right):** `Tr(M · (X ⊗ I)) = Tr(Tr_B(M) · X)`. Pairing a bipartite
operator against a `X ⊗ I_B` observable collapses to the right partial trace. Basis-free; from
expanding the trace, collapsing the `I_B` Kronecker factor (`l = k`), and `Finset.sum_comm`. -/
theorem trace_mul_kronecker_one_right (M : Matrix (n × m) (n × m) ℂ) (X : Matrix n n ℂ) :
    (M * (X ⊗ₖ (1 : Matrix m m ℂ))).trace = (partialTraceRight M * X).trace := by
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, partialTraceRight_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (∑ j, (∑ k, M (i, k) (j, k)) * X j i)
      = ∑ k, ∑ j, M (i, k) (j, k) * X j i from by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single k]
  · rw [Matrix.kronecker_apply, Matrix.one_apply_eq, mul_one]
  · intro l _ hl
    rw [Matrix.kronecker_apply, Matrix.one_apply, if_neg hl, mul_zero, mul_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

omit [DecidableEq m] in
/-- **Reduced-trace identity (left):** `Tr(M · (I ⊗ Y)) = Tr(Tr_A(M) · Y)`. -/
theorem trace_mul_one_kronecker_left (M : Matrix (n × m) (n × m) ℂ) (Y : Matrix m m ℂ) :
    (M * ((1 : Matrix n n ℂ) ⊗ₖ Y)).trace = (partialTraceLeft M * Y).trace := by
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, partialTraceLeft_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (∑ l, (∑ i, M (i, k) (i, l)) * Y l k)
      = ∑ i, ∑ l, M (i, k) (i, l) * Y l k from by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => by rw [Finset.sum_mul]]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.kronecker_apply, Matrix.one_apply_eq, one_mul]
  · intro i' _ hi'
    rw [Matrix.kronecker_apply, Matrix.one_apply, if_neg hi', zero_mul, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

end PartialTraceTrace

/-! ## The Kronecker-log operator split (the former K1-B.2 wall)

`cfc_log_kronecker : log(ρ_A ⊗ ρ_B) = log ρ_A ⊗ I + I ⊗ log ρ_B`, the operator identity that
turns subadditivity into a mechanical Klein-inequality application. The route is the
diagonalization-respecting `cfc_eq_conj_diagonal` helper (Lagrange-interpolation based) applied to
the Kronecker eigen-decomposition `kronecker_eq_conj_diagonal_eigenvalues`. -/

open Polynomial in
/-- **CFC of equal eigenvalue-actions agree.** If `f` and `g` agree on every eigenvalue of `ρ`,
then `hρ.cfc f = hρ.cfc g` (the converse of `cfc_eq_iff_on_eigenvalues`). Trivial: the diagonals
`↑∘f∘λ` and `↑∘g∘λ` coincide. -/
theorem cfc_eq_of_eq_on_eigenvalues {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) {f g : ℝ → ℝ}
    (h : ∀ i, f (hρ.eigenvalues i) = g (hρ.eigenvalues i)) : hρ.cfc f = hρ.cfc g := by
  unfold Matrix.IsHermitian.cfc
  congr 2
  funext i
  simp only [Function.comp_apply, h i]

open Polynomial in
/-- **Each diagonal value of a unitary diagonalization is an eigenvalue.** If
`M = U · diagonal d · Uᴴ` (`U` unitary, `d` real) then every `d c` equals some eigenvalue
`hM.eigenvalues i`. Via the charpoly root multiset: `M.charpoly = ∏ (X − ↑(d c))` and the roots
are the eigenvalues, so each `↑(d c)` is among them. The permutation-invariant route sidesteps
eigenvalue sorting. -/
theorem eigenvalue_of_conj_diagonal {M U : Matrix n n ℂ} (hM : M.IsHermitian)
    (hU : star U * U = 1) (d : n → ℝ)
    (hMeq : M = U * diagonal (fun i => (d i : ℂ)) * star U) (c : n) :
    ∃ i, hM.eigenvalues i = d c := by
  have hchar : M.charpoly = ∏ p : n, (X - C ((d p : ℂ))) := by
    rw [hMeq, charpoly_conj_unitary hU, charpoly_diagonal]
  have hroots1 := hM.roots_charpoly_eq_eigenvalues
  have hroots2 : M.charpoly.roots = Multiset.map (fun p => ((d p : ℝ) : ℂ)) Finset.univ.val := by
    rw [hchar, Polynomial.roots_prod _ _
      (by simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
    simp
  have hmem : ((d c : ℝ) : ℂ) ∈ M.charpoly.roots := by
    rw [hroots2]; exact Multiset.mem_map.mpr ⟨c, Finset.mem_univ_val c, rfl⟩
  rw [hroots1] at hmem
  obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
  simp only [Function.comp_apply] at hi
  exact ⟨i, Complex.ofReal_injective hi⟩

open Polynomial in
/-- `aeval (↑r) q = ↑(eval r q)` for a real polynomial `q` evaluated at `(r : ℂ)`. -/
private theorem aeval_ofReal_eq (r : ℝ) (q : ℝ[X]) :
    aeval ((r : ℝ) : ℂ) q = ((eval r q : ℝ) : ℂ) := by
  rw [show ((r:ℝ):ℂ) = algebraMap ℝ ℂ r from rfl, aeval_algebraMap_apply, aeval_def,
    Algebra.algebraMap_self, eval₂_id]
  rfl

open Polynomial in
/-- **CFC respects a unitary diagonalization.** If `M = U · diagonal d · Uᴴ` with `U` unitary
(`star U * U = 1`) and real `d`, then `hM.cfc f = U · diagonal (↑∘f∘d) · Uᴴ`. The proof routes
through Lagrange interpolation: a polynomial `q` matching `f` on the (finite) spectrum gives
`hM.cfc f = aeval M q` (`cfc_polynomial`), and `aeval` conjugates through `U` (`aeval_algHom_apply`
at the conjugation `*`-automorphism `Unitary.conjStarAlgAut`) and acts diagonally, so
`aeval M q = U · diagonal (eval·q ∘ d) · Uᴴ = U · diagonal (↑∘f∘d) · Uᴴ` since each `d c` is an
eigenvalue (`eigenvalue_of_conj_diagonal` ⟹ `eval (d c) q = f (d c)`). **This holds for the
`W = U_A ⊗ U_B` decomposition, not only the canonical `eigenvectorUnitary`**, which is what the
Kronecker split needs; it avoids the eigenvector-ambiguity / sorting subtlety entirely. -/
theorem cfc_eq_conj_diagonal {M U : Matrix n n ℂ} (hM : M.IsHermitian)
    (hU : star U * U = 1) (d : n → ℝ)
    (hMeq : M = U * diagonal (fun i => (d i : ℂ)) * star U) (f : ℝ → ℝ) :
    hM.cfc f = U * diagonal (fun i => ((f (d i) : ℝ) : ℂ)) * star U := by
  classical
  set S : Finset ℝ := Finset.image hM.eigenvalues Finset.univ with hS
  set q : ℝ[X] := Lagrange.interpolate S id f with hq
  have hInj : Set.InjOn (id : ℝ → ℝ) (S : Set ℝ) := Function.injective_id.injOn
  have hqeig : ∀ i, eval (hM.eigenvalues i) q = f (hM.eigenvalues i) := by
    intro i
    have hmem : hM.eigenvalues i ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ i)
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) f hInj hmem
    simpa [hq] using this
  have hqd : ∀ c, eval (d c) q = f (d c) := by
    intro c
    obtain ⟨i, hi⟩ := eigenvalue_of_conj_diagonal hM hU d hMeq c
    rw [← hi, hqeig i]
  have hcfc : hM.cfc f = aeval M q := by
    rw [cfc_eq_of_eq_on_eigenvalues hM (g := fun x => eval x q) (fun i => (hqeig i).symm)]
    rw [← hM.cfc_eq (fun x => eval x q), cfc_polynomial q M]
  rw [hcfc]
  have hUstar : U * star U = 1 := mul_eq_one_comm.mp hU
  have hUmem : U ∈ unitary (Matrix n n ℂ) := Unitary.mem_iff.mpr ⟨hU, hUstar⟩
  have hconj : aeval M q = U * aeval (diagonal (fun i => (d i : ℂ))) q * star U := by
    rw [hMeq]
    have key := Polynomial.aeval_algHom_apply
      ((Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) ⟨U, hUmem⟩).toAlgEquiv.toAlgHom.restrictScalars ℝ)
      (diagonal (fun i => (d i : ℂ))) q
    have hcoe : ∀ (a : Matrix n n ℂ),
        ((Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) ⟨U, hUmem⟩).toAlgEquiv.toAlgHom.restrictScalars ℝ) a
          = U * a * star U := by
      intro a
      rw [show (((Unitary.conjStarAlgAut ℂ (Matrix n n ℂ)
            ⟨U, hUmem⟩).toAlgEquiv.toAlgHom.restrictScalars ℝ) a)
          = (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) ⟨U, hUmem⟩) a from rfl,
        Unitary.conjStarAlgAut_apply]
    rw [hcoe, hcoe] at key
    exact key
  rw [hconj]
  congr 2
  ext i j
  by_cases hij : i = j
  · subst hij
    have hdiag : (aeval (diagonal (fun i => (d i : ℂ))) q) i i = aeval ((d i : ℝ) : ℂ) q := by
      rw [show (diagonal (fun i => (d i : ℂ)) : Matrix n n ℂ)
          = ((Matrix.diagonalAlgHom ℂ).restrictScalars ℝ) (fun i => (d i : ℂ)) from rfl,
        Polynomial.aeval_algHom_apply]
      show (diagonal (fun i => (aeval (fun i => (d i : ℂ)) q) i)) i i = _
      rw [diagonal_apply_eq, aeval_pi_apply₂]
    rw [hdiag, aeval_ofReal_eq, hqd, diagonal_apply_eq]
  · have hoff : (aeval (diagonal (fun i => (d i : ℂ))) q) i j = 0 := by
      rw [show (diagonal (fun i => (d i : ℂ)) : Matrix n n ℂ)
          = ((Matrix.diagonalAlgHom ℂ).restrictScalars ℝ) (fun i => (d i : ℂ)) from rfl,
        Polynomial.aeval_algHom_apply]
      show (diagonal (fun i => (aeval (fun i => (d i : ℂ)) q) i)) i j = _
      rw [diagonal_apply_ne _ hij]
    rw [hoff, diagonal_apply_ne _ hij]

section Kronecker

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **The Kronecker-log operator split:** `log(ρ_A ⊗ ρ_B) = log ρ_A ⊗ I + I ⊗ log ρ_B` for two
**positive-definite** matrices. (`log` is the Hermitian functional calculus `IsHermitian.cfc
Real.log`.) Genuinely the operator identity `logρ_A ⊗ I + I ⊗ logρ_B`, not a relabelling: it is
obtained from the eigen-decomposition `ρ_A ⊗ ρ_B = W · diagonal(λ_A·λ_B) · Wᴴ`
(`W = U_A ⊗ U_B`) via `cfc_eq_conj_diagonal`, the per-eigenvalue split
`log(λ_A,i · λ_B,j) = log λ_A,i + log λ_B,j` (positive-definite ⟹ `λ > 0`, `Real.log_mul`), and
`mul_kronecker_mul` distribution (with `U_B · I · U_Bᴴ = I`). The linchpin for subadditivity. -/
theorem cfc_log_kronecker {ρA : Matrix n n ℂ} {ρB : Matrix m m ℂ}
    (hpdA : ρA.PosDef) (hpdB : ρB.PosDef) :
    (isHermitian_kronecker hpdA.1 hpdB.1).cfc Real.log
      = (hpdA.1.cfc Real.log) ⊗ₖ (1 : Matrix m m ℂ)
        + (1 : Matrix n n ℂ) ⊗ₖ (hpdB.1.cfc Real.log) := by
  set hA := hpdA.1
  set hB := hpdB.1
  set UA := (hA.eigenvectorUnitary : Matrix n n ℂ) with hUA
  set UB := (hB.eigenvectorUnitary : Matrix m m ℂ) with hUB
  set W := UA ⊗ₖ UB with hW
  set d : (n × m) → ℝ := fun p => hA.eigenvalues p.1 * hB.eigenvalues p.2 with hd
  have hWU : star W * W = 1 := star_kronecker_eigenvectorUnitary_mul_self hA hB
  have hMeq : (ρA ⊗ₖ ρB) = W * diagonal (fun p => (d p : ℂ)) * star W := by
    rw [hW, hUA, hUB]
    rw [kronecker_eq_conj_diagonal_eigenvalues hA hB]
    congr 2
    ext p
    simp only [hd, diagonal, Matrix.of_apply]
    split <;> simp [Complex.ofReal_mul]
  have hcfc := cfc_eq_conj_diagonal (isHermitian_kronecker hA hB) hWU d hMeq Real.log
  rw [hcfc]
  set DA : Matrix n n ℂ := diagonal (fun i => ((Real.log (hA.eigenvalues i) : ℝ) : ℂ)) with hDA
  set DB : Matrix m m ℂ := diagonal (fun j => ((Real.log (hB.eigenvalues j) : ℝ) : ℂ)) with hDB
  have hposA : ∀ i, 0 < hA.eigenvalues i := fun i => hpdA.eigenvalues_pos i
  have hposB : ∀ j, 0 < hB.eigenvalues j := fun j => hpdB.eigenvalues_pos j
  have hsplit : (diagonal (fun p : n × m => ((Real.log (d p) : ℝ) : ℂ)) : Matrix (n × m) (n × m) ℂ)
      = DA ⊗ₖ (1 : Matrix m m ℂ) + (1 : Matrix n n ℂ) ⊗ₖ DB := by
    ext p q
    rcases p with ⟨i, j⟩
    rcases q with ⟨i', j'⟩
    by_cases hpq : (i, j) = (i', j')
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hpq
      simp only [Matrix.add_apply, Matrix.kronecker_apply, hDA, hDB,
        diagonal_apply_eq, Matrix.one_apply_eq, mul_one, one_mul]
      rw [show d (i, j) = hA.eigenvalues i * hB.eigenvalues j from rfl,
        Real.log_mul (ne_of_gt (hposA i)) (ne_of_gt (hposB j))]
      push_cast; ring
    · rw [diagonal_apply_ne _ hpq]
      simp only [Matrix.add_apply, Matrix.kronecker_apply, hDA, hDB]
      by_cases hi : i = i'
      · subst hi
        by_cases hj : j = j'
        · subst hj; exact absurd rfl hpq
        · rw [diagonal_apply_ne _ hj, Matrix.one_apply_ne hj]
          simp [Matrix.one_apply_eq, diagonal_apply_eq]
      · rw [Matrix.one_apply_ne hi, diagonal_apply_ne _ hi]
        simp
  have hcfcA : hA.cfc Real.log = UA * DA * star UA := by
    rw [hDA, hUA]; unfold Matrix.IsHermitian.cfc
    rw [Unitary.conjStarAlgAut_apply]; rfl
  have hcfcB : hB.cfc Real.log = UB * DB * star UB := by
    rw [hDB, hUB]; unfold Matrix.IsHermitian.cfc
    rw [Unitary.conjStarAlgAut_apply]; rfl
  have hUUA : UA * star UA = 1 := by rw [hUA]; exact Unitary.coe_mul_star_self _
  have hUUB : UB * star UB = 1 := by rw [hUB]; exact Unitary.coe_mul_star_self _
  rw [hsplit, Matrix.mul_add, Matrix.add_mul, hcfcA, hcfcB]
  congr 1
  · rw [hW, Matrix.star_eq_conjTranspose, conjTranspose_kronecker,
      ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose,
      ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, hUUB]
  · rw [hW, Matrix.star_eq_conjTranspose, conjTranspose_kronecker,
      ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose,
      ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, hUUA]

/-- **Von Neumann subadditivity:** `S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)` for a bipartite density operator
`ρ_AB` whose **marginals** `ρ_A = Tr_B ρ_AB`, `ρ_B = Tr_A ρ_AB` are **positive-definite**.

Hypotheses: `ρ_AB.PosSemidef`, `ρ_AB.trace = 1`, and `(partialTraceRight ρ_AB).PosDef`,
`(partialTraceLeft ρ_AB).PosDef`. **`ρ_AB` is NOT assumed positive-definite** — the statement
covers pure entangled states (where `S(ρ_AB) = 0`, marginals full-rank mixed) and every correlated
`ρ_AB`; the marginals-PD condition is the minimal one for the Klein step (`ρ_A ⊗ ρ_B` PD). The bound
is a genuine inequality (equality only at product `ρ_AB = ρ_A ⊗ ρ_B`), not a product-state identity.

Proof: `S(ρ_AB) = −Re Tr(ρ_AB log ρ_AB) ≤ −Re Tr(ρ_AB log(ρ_A⊗ρ_B))` by `klein_inequality` at
`σ = ρ_A ⊗ ρ_B` (PD via `PosDef.kronecker`); the Kronecker-log split `cfc_log_kronecker` rewrites
`log(ρ_A⊗ρ_B) = logρ_A ⊗ I + I ⊗ logρ_B`, and the reduced-trace identities
`trace_mul_kronecker_one_right`/`_left` collapse the two cross terms to `Tr(ρ_A logρ_A)`,
`Tr(ρ_B logρ_B)`, whose negatives are `S(ρ_A)`, `S(ρ_B)`. -/
theorem vonNeumannEntropy_subadditive
    {ρAB : Matrix (n × m) (n × m) ℂ} (hpsd : ρAB.PosSemidef) (htr : ρAB.trace = 1)
    (hpdA : (partialTraceRight ρAB).PosDef) (hpdB : (partialTraceLeft ρAB).PosDef) :
    vonNeumannEntropy hpsd.1
      ≤ vonNeumannEntropy hpdA.1 + vonNeumannEntropy hpdB.1 := by
  set ρA := partialTraceRight ρAB with hρA
  set ρB := partialTraceLeft ρAB with hρB
  have htrA : ρA.trace = 1 := by rw [hρA, partialTraceRight_trace, htr]
  have htrB : ρB.trace = 1 := by rw [hρB, partialTraceLeft_trace, htr]
  have hpdσ : (ρA ⊗ₖ ρB).PosDef := Matrix.PosDef.kronecker hpdA hpdB
  have htrσ : (ρA ⊗ₖ ρB).trace = 1 := by rw [Matrix.trace_kronecker, htrA, htrB, mul_one]
  have hklein := klein_inequality hpsd hpdσ htr htrσ
  have hSAB : vonNeumannEntropy hpsd.1 = - RCLike.re ((ρAB * hpsd.1.cfc Real.log).trace) := by
    rw [vonNeumannEntropy_eq_neg_re_trace_mul_log, cfc_id_mul_log]
  have hsplit : RCLike.re ((ρAB * hpdσ.1.cfc Real.log).trace)
      = RCLike.re ((ρA * hpdA.1.cfc Real.log).trace)
        + RCLike.re ((ρB * hpdB.1.cfc Real.log).trace) := by
    have hcfcσ : hpdσ.1.cfc Real.log
        = (hpdA.1.cfc Real.log) ⊗ₖ (1 : Matrix m m ℂ)
          + (1 : Matrix n n ℂ) ⊗ₖ (hpdB.1.cfc Real.log) := by
      rw [show hpdσ.1 = isHermitian_kronecker hpdA.1 hpdB.1 from rfl]
      exact cfc_log_kronecker hpdA hpdB
    rw [hcfcσ, Matrix.mul_add, Matrix.trace_add, map_add,
      trace_mul_kronecker_one_right, trace_mul_one_kronecker_left]
  have hSA : vonNeumannEntropy hpdA.1 = - RCLike.re ((ρA * hpdA.1.cfc Real.log).trace) := by
    rw [vonNeumannEntropy_eq_neg_re_trace_mul_log, cfc_id_mul_log]
  have hSB : vonNeumannEntropy hpdB.1 = - RCLike.re ((ρB * hpdB.1.cfc Real.log).trace) := by
    rw [vonNeumannEntropy_eq_neg_re_trace_mul_log, cfc_id_mul_log]
  rw [hSAB, hSA, hSB]
  linarith [hklein, hsplit]

end Kronecker

/-! ## Schmidt symmetry: equal marginal entropies of a pure bipartite state (Araki–Lieb 2a)

The two reduced density operators of a pure bipartite state have **equal** von Neumann entropy.
The algebraic core is the **cospectrum** of `M Mᴴ` and `Mᴴ M`: they share the same nonzero
eigenvalues with multiplicity, so any spectral sum `∑ g(λ)` with `g 0 = 0` agrees across the two.
This is the entropy-side input to Araki–Lieb. -/

section Cospectrum

open Polynomial

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Cospectral spectral sums of `M Mᴴ` and `Mᴴ M`.** For any rectangular `M : Matrix n m ℂ` and
any `g : ℝ → ℝ` with `g 0 = 0`, the spectral sums of `g` over the eigenvalues of `M Mᴴ` (size `n`)
and `Mᴴ M` (size `m`) coincide:

  `∑ᵢ g(λ(M Mᴴ)ᵢ) = ∑ⱼ g(λ(Mᴴ M)ⱼ)`.

Route (charpoly, multiset-of-roots, permutation-invariant): the rectangular charpoly identity
`charpoly_mul_comm'` gives `X^|m| · (M Mᴴ).charpoly = X^|n| · (Mᴴ M).charpoly` in `ℂ[X]`. Taking
`roots` of both (products of nonzero polynomials, `roots_mul`, `roots_pow`, `roots_X`) yields the
multiset identity `replicate |m| 0 + roots((M Mᴴ).charpoly) = replicate |n| 0 + roots((Mᴴ M).charpoly)`.
Each `roots(charpoly) = map (↑ ∘ eigenvalues) univ` (`roots_charpoly_eq_eigenvalues`), so mapping by
`g ∘ re` and summing, the `replicate _ 0` parts contribute `g 0 = 0` and the eigenvalue sums equate.
Avoids matching Mathlib's *sorted* `eigenvalues` pointwise. -/
theorem spectral_sum_mul_conjTranspose_comm (M : Matrix n m ℂ) {g : ℝ → ℝ} (hg0 : g 0 = 0) :
    ∑ i, g ((Matrix.isHermitian_mul_conjTranspose_self M).eigenvalues i)
      = ∑ j, g ((Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues j) := by
  set A := M * Mᴴ with hA
  set B := Mᴴ * M with hB
  have hAh : A.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self M
  have hBh : B.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  -- rectangular charpoly commutation: X^|m| · A.charpoly = X^|n| · B.charpoly.
  have hcomm : X ^ Fintype.card m * A.charpoly = X ^ Fintype.card n * B.charpoly :=
    Matrix.charpoly_mul_comm' M Mᴴ
  -- both charpolys are monic, hence nonzero.
  have hAne : A.charpoly ≠ 0 := (Matrix.charpoly_monic A).ne_zero
  have hBne : B.charpoly ≠ 0 := (Matrix.charpoly_monic B).ne_zero
  have hXn : (X : ℂ[X]) ^ Fintype.card n ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  have hXm : (X : ℂ[X]) ^ Fintype.card m ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  -- take roots of both sides.
  have hrootsX : ∀ k : ℕ, ((X : ℂ[X]) ^ k).roots = Multiset.replicate k 0 := by
    intro k
    rw [Polynomial.roots_pow, Polynomial.roots_X, Multiset.nsmul_singleton]
  have hroots : Multiset.replicate (Fintype.card m) (0 : ℂ) + A.charpoly.roots
      = Multiset.replicate (Fintype.card n) (0 : ℂ) + B.charpoly.roots := by
    have h := congrArg Polynomial.roots hcomm
    rw [Polynomial.roots_mul (by simp [hXm, hAne]),
      Polynomial.roots_mul (by simp [hXn, hBne]), hrootsX, hrootsX] at h
    exact h
  -- map by g ∘ re and sum; the replicate-0 parts vanish since g 0 = 0.
  have hsum := congrArg (fun s => (Multiset.map (fun z : ℂ => g (Complex.re z)) s).sum) hroots
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
    Complex.zero_re, hg0, Multiset.sum_replicate, smul_zero, zero_add] at hsum
  -- rewrite each eigenvalue sum via roots_charpoly_eq_eigenvalues.
  rw [hAh.roots_charpoly_eq_eigenvalues, hBh.roots_charpoly_eq_eigenvalues,
    Multiset.map_map, Multiset.map_map] at hsum
  simp only [Function.comp_apply] at hsum
  rw [Finset.sum, Finset.sum]
  -- A.eigenvalues / B.eigenvalues vs hAh / hBh eigenvalues are the same (definitional A = M*Mᴴ).
  exact hsum

/-- **Equal charpoly ⟹ equal spectral sums.** Two Hermitian matrices (of possibly different index
types) with the *same* characteristic polynomial have equal spectral sums `∑ g(λ)`. Via the root
multisets (`roots_charpoly_eq_eigenvalues`): equal charpoly ⟹ equal root multiset ⟹ equal mapped
sum. Used to transfer entropy across the transpose `(Mᴴ M)ᵀ` (`charpoly_transpose`). -/
theorem spectral_sum_eq_of_charpoly_eq {k : Type*} [Fintype k] [DecidableEq k]
    {X : Matrix n n ℂ} {Y : Matrix k k ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hcp : X.charpoly = Y.charpoly) (g : ℝ → ℝ) :
    ∑ i, g (hX.eigenvalues i) = ∑ j, g (hY.eigenvalues j) := by
  have hroots : X.charpoly.roots = Y.charpoly.roots := by rw [hcp]
  rw [hX.roots_charpoly_eq_eigenvalues, hY.roots_charpoly_eq_eigenvalues] at hroots
  have hsum := congrArg (fun s => (Multiset.map (fun z : ℂ => g (Complex.re z)) s).sum) hroots
  simp only [Multiset.map_map, Function.comp_apply] at hsum
  rw [Finset.sum, Finset.sum]
  exact hsum

/-- **PosDef transfers across equal charpoly.** Two Hermitian matrices with the same charpoly: if
one is positive-definite (all eigenvalues `> 0`) so is the other. The eigenvalue *multisets* agree
(`roots_charpoly_eq_eigenvalues`); positivity of every element is a multiset property, so it
transfers. Used to derive `ρ_R` positive-definite from `ρ_AB` positive-definite (cospectral). -/
theorem posDef_of_charpoly_eq {k : Type*} [Fintype k] [DecidableEq k]
    {X : Matrix n n ℂ} {Y : Matrix k k ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hcp : X.charpoly = Y.charpoly) (hXpd : X.PosDef) : Y.PosDef := by
  rw [hY.posDef_iff_eigenvalues_pos]
  intro j
  -- (↑(eigY j) : ℂ) is a root of Y.charpoly = X.charpoly, hence = (↑(eigX i)) for some i.
  have hmem : ((hY.eigenvalues j : ℝ) : ℂ) ∈ Y.charpoly.roots := by
    rw [hY.roots_charpoly_eq_eigenvalues]
    exact Multiset.mem_map.mpr ⟨j, Finset.mem_univ_val j, rfl⟩
  rw [← hcp, hX.roots_charpoly_eq_eigenvalues] at hmem
  obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
  simp only [Function.comp_apply] at hi
  have : hY.eigenvalues j = hX.eigenvalues i := (Complex.ofReal_injective hi).symm
  rw [this]
  exact (hX.posDef_iff_eigenvalues_pos.mp hXpd) i

/-- **Entropy is independent of the Hermitian witness.** Two `IsHermitian` proofs of the *same*
matrix give the same entropy (the eigenvalue *values* are matrix-determined; equal charpoly with
`rfl`). -/
theorem vonNeumannEntropy_congr {ρ : Matrix n n ℂ} (h1 h2 : ρ.IsHermitian) :
    vonNeumannEntropy h1 = vonNeumannEntropy h2 :=
  spectral_sum_eq_of_charpoly_eq h1 h2 rfl _

/-- **Entropy is invariant under reindexing.** `S(reindex e e ρ) = S(ρ)` for any `e : n ≃ k`:
reindexing is a permutation similarity, so `charpoly_reindex` + `spectral_sum_eq_of_charpoly_eq`.
The reassociation hinge for the Araki–Lieb tripartite cuts. -/
theorem vonNeumannEntropy_reindex {k : Type*} [Fintype k] [DecidableEq k]
    {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (e : n ≃ k) :
    vonNeumannEntropy (hρ.reindex e) = vonNeumannEntropy hρ := by
  rw [vonNeumannEntropy, vonNeumannEntropy]
  exact spectral_sum_eq_of_charpoly_eq (hρ.reindex e) hρ (Matrix.charpoly_reindex e ρ) _

end Cospectrum

/-! ## Schmidt symmetry of pure-state marginal entropies (Araki–Lieb 2a) -/

section Schmidt

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The pure bipartite density `ρψ = |ψ⟩⟨ψ|` of `ψ : (n × m) → ℂ`, as a matrix:
`ρψ p q = ψ p * conj (ψ q)`. -/
noncomputable def pureDensity (ψ : (n × m) → ℂ) : Matrix (n × m) (n × m) ℂ :=
  vecMulVec ψ (star ψ)

/-- The reshape of `ψ : (n × m) → ℂ` as a rectangular matrix `M : Matrix n m ℂ`, `M a b = ψ (a,b)`.
-/
def pureMatrix (ψ : (n × m) → ℂ) : Matrix n m ℂ := Matrix.of fun a b => ψ (a, b)

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
/-- **Right marginal of a pure state is `M Mᴴ`:** `Tr_B |ψ⟩⟨ψ| = M Mᴴ` with `M = pureMatrix ψ`.
`(Tr_B ρψ) i j = ∑ₖ ψ(i,k) conj(ψ(j,k)) = ∑ₖ M i k · conj(M j k) = (M Mᴴ) i j`. -/
theorem partialTraceRight_pureDensity (ψ : (n × m) → ℂ) :
    partialTraceRight (pureDensity ψ) = pureMatrix ψ * (pureMatrix ψ)ᴴ := by
  ext i j
  simp only [partialTraceRight_apply, pureDensity, vecMulVec_apply, Pi.star_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, pureMatrix, Matrix.of_apply, Complex.star_def]

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- **Left marginal of a pure state is `(Mᴴ M)ᵀ`:** `Tr_A |ψ⟩⟨ψ| = (Mᴴ M)ᵀ` with `M = pureMatrix ψ`.
`(Tr_A ρψ) k l = ∑ᵢ ψ(i,k) conj(ψ(i,l)) = ∑ᵢ M i k conj(M i l) = (Mᴴ M) l k = ((Mᴴ M)ᵀ) k l`. -/
theorem partialTraceLeft_pureDensity (ψ : (n × m) → ℂ) :
    partialTraceLeft (pureDensity ψ) = ((pureMatrix ψ)ᴴ * pureMatrix ψ)ᵀ := by
  ext k l
  simp only [partialTraceLeft_apply, pureDensity, vecMulVec_apply, Pi.star_apply,
    Matrix.transpose_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, pureMatrix,
    Matrix.of_apply, Complex.star_def]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]

omit [DecidableEq n] [DecidableEq m] in
/-- `trace |ψ⟩⟨ψ| = ∑ ‖ψ p‖²` (the squared norm of `ψ`). -/
theorem pureDensity_trace (ψ : (n × m) → ℂ) :
    (pureDensity ψ).trace = ((∑ p, ‖ψ p‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, pureDensity, vecMulVec_apply, Pi.star_apply, Complex.star_def]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- The pure density `|ψ⟩⟨ψ|` is Hermitian. -/
theorem pureDensity_isHermitian (ψ : (n × m) → ℂ) : (pureDensity ψ).IsHermitian := by
  ext p q
  simp only [pureDensity, Matrix.conjTranspose_apply, vecMulVec_apply, Pi.star_apply,
    Complex.star_def, map_mul, Complex.conj_conj, mul_comm]

/-- **Schmidt symmetry (Araki–Lieb 2a):** the two reduced density operators of a pure bipartite
state `|ψ⟩⟨ψ|` have **equal** von Neumann entropy:

  `S(Tr_B |ψ⟩⟨ψ|) = S(Tr_A |ψ⟩⟨ψ|)`.

Stated on the canonical Hermitian witnesses `partialTrace{Right,Left}_isHermitian` of the
Hermitian pure density (`pureDensity_isHermitian`). Genuine content: the right marginal is `M Mᴴ`,
the left marginal is `(Mᴴ M)ᵀ` (`partialTraceRight_pureDensity` / `partialTraceLeft_pureDensity`);
`M Mᴴ` and `Mᴴ M` are **cospectral** on their nonzero eigenvalues
(`spectral_sum_mul_conjTranspose_comm`, with `negMulLog 0 = 0`), and transpose preserves the
spectrum (`charpoly_transpose` via `spectral_sum_eq_of_charpoly_eq`). No unit-norm hypothesis is
needed for the entropy equality (it holds for every `ψ`); the unit condition only makes the
marginals genuine densities. -/
theorem pure_marginal_entropy_eq (ψ : (n × m) → ℂ) :
    vonNeumannEntropy (partialTraceRight_isHermitian (pureDensity_isHermitian ψ))
      = vonNeumannEntropy (partialTraceLeft_isHermitian (pureDensity_isHermitian ψ)) := by
  set M := pureMatrix ψ with hM
  -- Hermitian witnesses for the two marginals in their M Mᴴ / (Mᴴ M)ᵀ forms.
  have hR : (partialTraceRight (pureDensity ψ)).IsHermitian :=
    partialTraceRight_isHermitian (pureDensity_isHermitian ψ)
  have hL : (partialTraceLeft (pureDensity ψ)).IsHermitian :=
    partialTraceLeft_isHermitian (pureDensity_isHermitian ψ)
  -- the marginal-form Hermitian matrices.
  have hMMh : (M * Mᴴ).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self M
  have hMhM : (Mᴴ * M).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  have hMhMt : ((Mᴴ * M)ᵀ).IsHermitian := hMhM.transpose
  -- S(Tr_B) = ∑ negMulLog (eig (M Mᴴ)).
  have hSR : vonNeumannEntropy hR = ∑ i, Real.negMulLog (hMMh.eigenvalues i) := by
    rw [vonNeumannEntropy]
    apply spectral_sum_eq_of_charpoly_eq hR hMMh
    rw [partialTraceRight_pureDensity ψ, hM]
  -- S(Tr_A) = ∑ negMulLog (eig ((Mᴴ M)ᵀ)).
  have hSL : vonNeumannEntropy hL = ∑ i, Real.negMulLog (hMhMt.eigenvalues i) := by
    rw [vonNeumannEntropy]
    apply spectral_sum_eq_of_charpoly_eq hL hMhMt
    rw [partialTraceLeft_pureDensity ψ, hM]
  rw [hSR, hSL]
  -- ∑ negMulLog (eig ((Mᴴ M)ᵀ)) = ∑ negMulLog (eig (Mᴴ M)) (transpose preserves charpoly).
  have htrans : ∑ i, Real.negMulLog (hMhMt.eigenvalues i)
      = ∑ j, Real.negMulLog (hMhM.eigenvalues j) :=
    spectral_sum_eq_of_charpoly_eq hMhMt hMhM (Matrix.charpoly_transpose _) Real.negMulLog
  rw [htrans]
  -- cospectrum of M Mᴴ and Mᴴ M (negMulLog 0 = 0).
  exact spectral_sum_mul_conjTranspose_comm M Real.negMulLog_zero

end Schmidt

/-! ## Purification of a density operator (Araki–Lieb 2b) -/

section Purification

variable {m : Type*} [Fintype m]

/-- The **Hermitian square root** `√ρ := cfc Real.sqrt ρ` of a Hermitian matrix. For PSD `ρ`
(eigenvalues `≥ 0`) it satisfies `√ρ · √ρ = ρ` (`sqrtMat_mul_self`) and is itself Hermitian. -/
noncomputable def sqrtMat {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) : Matrix n n ℂ :=
  hρ.cfc Real.sqrt

/-- `√ρ` is Hermitian (the cfc of a real function is Hermitian). -/
theorem sqrtMat_isHermitian {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    (sqrtMat hρ).IsHermitian :=
  cfc_isHermitian hρ Real.sqrt

/-- `√ρ · √ρ = ρ` for PSD `ρ`: `√λ · √λ = λ` on the (nonneg) spectrum, via `cfc_mul` + `cfc_id`. -/
theorem sqrtMat_mul_self {ρ : Matrix n n ℂ} (hpsd : ρ.PosSemidef) :
    sqrtMat hpsd.1 * sqrtMat hpsd.1 = ρ := by
  rw [sqrtMat, cfc_mul hpsd.1 Real.sqrt Real.sqrt]
  rw [cfc_eq_of_eq_on_eigenvalues hpsd.1
    (f := fun x => Real.sqrt x * Real.sqrt x) (g := id)
    (fun i => Real.mul_self_sqrt (hpsd.eigenvalues_nonneg i))]
  exact cfc_id hpsd.1

/-- **Purification (Araki–Lieb 2b).** Every density operator `ρ : Matrix (n×m) (n×m) ℂ` is the right
marginal of a pure state on `(n×m) ⊗ (n×m)` (a copy of the system as ancilla): there is a unit
`ψ : ((n×m) × (n×m)) → ℂ` with `partialTraceRight (pureDensity ψ) = ρ`. The purifying vector is
`ψ = vec(√ρ)` (`pureMatrix ψ = √ρ`); then `partialTraceRight (pureDensity ψ) = √ρ · (√ρ)ᴴ =
√ρ · √ρ = ρ`, and `∑‖ψ‖² = Tr((√ρ)ᴴ √ρ) = Tr ρ = 1`. -/
theorem exists_purification {ρ : Matrix (n × m) (n × m) ℂ}
    [DecidableEq m] (hpsd : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ∃ ψ : ((n × m) × (n × m)) → ℂ,
      (∑ p, ‖ψ p‖ ^ 2 = 1) ∧ partialTraceRight (pureDensity ψ) = ρ := by
  classical
  set S := sqrtMat hpsd.1 with hS
  have hSh : S.IsHermitian := sqrtMat_isHermitian hpsd.1
  -- the purifying vector ψ (a,b) = S a b.
  refine ⟨fun p => S p.1 p.2, ?_, ?_⟩
  · -- ∑ ‖S a b‖² = Tr(S S) = Tr ρ = 1.
    have hSS : S * S = ρ := sqrtMat_mul_self hpsd
    have hkey : (∑ p : (n × m) × (n × m), ‖S p.1 p.2‖ ^ 2 : ℝ) = ((S * S).trace).re := by
      rw [Matrix.trace, Complex.re_sum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      -- (S S) a a summand at b: S a b * S b a; with S Hermitian, S b a = conj (S a b).
      have hherm : S b a = starRingEnd ℂ (S a b) := by
        have h := congrFun (congrFun hSh.eq a) b
        simp only [Matrix.conjTranspose_apply, Complex.star_def] at h
        have := congrArg (starRingEnd ℂ) h
        rwa [Complex.conj_conj] at this
      rw [hherm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    simp only []
    rw [hkey, hSS, htr, Complex.one_re]
  · -- partialTraceRight (pureDensity ψ) = pureMatrix ψ * (pureMatrix ψ)ᴴ = S Sᴴ = S S = ρ.
    rw [partialTraceRight_pureDensity]
    have hpm : pureMatrix (fun p : (n × m) × (n × m) => S p.1 p.2) = S := by
      ext a b; rfl
    rw [hpm, hSh.eq, sqrtMat_mul_self hpsd]

end Purification

/-! ## Araki–Lieb triangle inequality (2c)

`|S(ρ_A) − S(ρ_B)| ≤ S(ρ_AB)`. Route: purify `ρ_AB` to a pure `Ψ` on `(AB) ⊗ R` with `R ≅ AB`
(`exists_purification`); for the pure global state the `A | (BR)` cut gives `S(ρ_A) = S(ρ_BR)`
(Schmidt symmetry on the reshaped `Ψ' : n × (m × R)`); subadditivity on `ρ_BR` (split `B | R`)
gives `S(ρ_BR) ≤ S(ρ_B) + S(ρ_R)`, and the `AB | R` cut gives `S(ρ_R) = S(ρ_AB)`; hence
`S(ρ_A) ≤ S(ρ_B) + S(ρ_AB)`. The symmetric `A ↔ B` swap closes the absolute value.

The reshape marginal identities are direct index computations (no abstract reassociation of the
partial trace). The subadditivity step requires the `B`- and `R`-marginals **positive-definite**;
`ρ_R` is cospectral with `ρ_AB`, so this routes through `ρ_AB.PosDef`. -/

section ArakiLieb

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The `A | (BR)` reshape of a global pure-state vector on `(A B) × R = (n × m) × (n × m)`:
`Ψ' a (b, r) = Ψ ((a, b), r)`, regrouping as `A × (B × R)`. -/
def reshapeABR (Ψ : ((n × m) × (n × m)) → ℂ) : (n × (m × (n × m))) → ℂ :=
  fun p => Ψ ((p.1, p.2.1), p.2.2)

omit [DecidableEq n] [DecidableEq m] in
/-- **A-marginal via the `A | BR` reshape = double right partial trace.**
`Tr_{BR} |Ψ'⟩⟨Ψ'| = Tr_B (Tr_R |Ψ⟩⟨Ψ|) = ρ_A`. Direct index computation:
both equal `(a, a') ↦ ∑_{b,r} Ψ((a,b),r) conj Ψ((a',b),r)`. -/
theorem partialTraceRight_reshapeABR (Ψ : ((n × m) × (n × m)) → ℂ) :
    partialTraceRight (pureDensity (reshapeABR Ψ))
      = partialTraceRight (partialTraceRight (pureDensity Ψ)) := by
  ext a a'
  simp only [partialTraceRight_apply, pureDensity, vecMulVec_apply, Pi.star_apply,
    reshapeABR, Complex.star_def, Fintype.sum_prod_type]

omit [Fintype m] [DecidableEq n] [DecidableEq m] in
/-- **BR-marginal via the `A | BR` reshape = `ρ_BR`.** `Tr_A |Ψ'⟩⟨Ψ'| = ρ_BR`, the matrix
`((b,r),(b',r')) ↦ ∑_a Ψ((a,b),r) conj Ψ((a,b'),r')`. -/
theorem partialTraceLeft_reshapeABR (Ψ : ((n × m) × (n × m)) → ℂ) :
    partialTraceLeft (pureDensity (reshapeABR Ψ))
      = Matrix.of fun br br' : m × (n × m) =>
          ∑ a : n, Ψ ((a, br.1), br.2) * starRingEnd ℂ (Ψ ((a, br'.1), br'.2)) := by
  ext br br'
  simp only [partialTraceLeft_apply, pureDensity, vecMulVec_apply, Pi.star_apply,
    reshapeABR, Complex.star_def, Matrix.of_apply]

omit [DecidableEq n] [DecidableEq m] in
/-- **B-marginal of `ρ_BR` (trace out R) = `ρ_B = Tr_A (Tr_R |Ψ⟩⟨Ψ|)`.** Direct index computation. -/
theorem partialTraceRight_partialTraceLeft_reshapeABR (Ψ : ((n × m) × (n × m)) → ℂ) :
    partialTraceRight (partialTraceLeft (pureDensity (reshapeABR Ψ)))
      = partialTraceLeft (partialTraceRight (pureDensity Ψ)) := by
  ext b b'
  simp only [partialTraceRight_apply, partialTraceLeft_apply, pureDensity, vecMulVec_apply,
    Pi.star_apply, reshapeABR, Complex.star_def]
  rw [Finset.sum_comm]

omit [DecidableEq n] [DecidableEq m] in
/-- **R-marginal of `ρ_BR` (trace out B) = `ρ_R = Tr_A (Tr_B |Ψ⟩⟨Ψ|)` reassociated.** Here
`ρ_R = Tr_{AB} |Ψ⟩⟨Ψ|` is `partialTraceLeft (pureDensity Ψ)` (trace out the whole `AB` first
factor). Direct index computation: both equal `(r, r') ↦ ∑_{a,b} Ψ((a,b),r) conj Ψ((a,b),r')`. -/
theorem partialTraceLeft_partialTraceLeft_reshapeABR (Ψ : ((n × m) × (n × m)) → ℂ) :
    partialTraceLeft (partialTraceLeft (pureDensity (reshapeABR Ψ)))
      = partialTraceLeft (pureDensity Ψ) := by
  ext r r'
  simp only [partialTraceLeft_apply, pureDensity, vecMulVec_apply, Pi.star_apply, reshapeABR,
    Complex.star_def, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

omit [DecidableEq n] [DecidableEq m] in
/-- The pure density `|ψ⟩⟨ψ|` is positive-semidefinite. -/
theorem pureDensity_posSemidef (ψ : (n × m) → ℂ) : (pureDensity ψ).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star ψ

/-- **Cospectrum of the two pure marginals (charpoly form).** For a pure state on `(n×m) ⊗ (n×m)`
(both factors equal-dimensional), the right and left marginals have **equal characteristic
polynomial**: `partialTraceRight = M Mᴴ`, `partialTraceLeft = (Mᴴ M)ᵀ`, and for **square** `M`,
`(M Mᴴ).charpoly = (Mᴴ M).charpoly` (`charpoly_mul_comm`), with `charpoly_transpose`. The
equal-dimension square case is the one purification produces (`R ≅ AB`). -/
theorem charpoly_partialTrace_pure_eq (Ψ : ((n × m) × (n × m)) → ℂ) :
    (partialTraceRight (pureDensity Ψ)).charpoly
      = (partialTraceLeft (pureDensity Ψ)).charpoly := by
  rw [partialTraceRight_pureDensity, partialTraceLeft_pureDensity, Matrix.charpoly_transpose,
    Matrix.charpoly_mul_comm]

/-- **Araki–Lieb, one side:** `S(ρ_A) ≤ S(ρ_B) + S(ρ_AB)` for `ρ_AB` positive-definite with the
`B`-marginal positive-definite. Purify, use Schmidt symmetry on the `A | BR` cut
(`S(ρ_A) = S(ρ_BR)`), subadditivity on `ρ_BR` (`S(ρ_BR) ≤ S(ρ_B) + S(ρ_R)`, needs `ρ_B`, `ρ_R`
PD), and `S(ρ_R) = S(ρ_AB)` (the `AB | R` cut). `ρ_R` PD is derived from `ρ_AB` PD by cospectrum
(`posDef_of_charpoly_eq`). -/
theorem araki_lieb_one_side
    {ρAB : Matrix (n × m) (n × m) ℂ} (hpd : ρAB.PosDef) (htr : ρAB.trace = 1)
    (hpdB : (partialTraceLeft ρAB).PosDef) :
    vonNeumannEntropy (partialTraceRight_isHermitian hpd.1)
      ≤ vonNeumannEntropy (partialTraceLeft_isHermitian hpd.1)
        + vonNeumannEntropy hpd.1 := by
  classical
  -- purify ρAB to a pure Ψ on (AB) ⊗ R, R ≅ AB.
  obtain ⟨Ψ, _hΨnorm, hΨ⟩ := exists_purification hpd.posSemidef htr
  set ρBR := partialTraceLeft (pureDensity (reshapeABR Ψ)) with hρBR
  have hρBR_psd : ρBR.PosSemidef :=
    partialTraceLeft_posSemidef (pureDensity_posSemidef (reshapeABR Ψ))
  -- (1) S(ρ_A) = S(ρ_BR), Schmidt symmetry on the A|BR reshape.
  have hStep1 : vonNeumannEntropy (partialTraceRight_isHermitian hpd.1)
      = vonNeumannEntropy hρBR_psd.1 := by
    have hsym := pure_marginal_entropy_eq (n := n) (m := m × (n × m)) (reshapeABR Ψ)
    rw [show vonNeumannEntropy hρBR_psd.1
        = vonNeumannEntropy (partialTraceLeft_isHermitian (pureDensity_isHermitian (reshapeABR Ψ)))
        from rfl, ← hsym]
    exact spectral_sum_eq_of_charpoly_eq _ _
      (by rw [partialTraceRight_reshapeABR, hΨ]) _
  -- B- and R-marginals of ρ_BR.
  have hB_eq : partialTraceRight ρBR = partialTraceLeft ρAB := by
    rw [hρBR, partialTraceRight_partialTraceLeft_reshapeABR, hΨ]
  have hR_eq : partialTraceLeft ρBR = partialTraceLeft (pureDensity Ψ) := by
    rw [hρBR, partialTraceLeft_partialTraceLeft_reshapeABR]
  have hpdB' : (partialTraceRight ρBR).PosDef := by rw [hB_eq]; exact hpdB
  have hpdR' : (partialTraceLeft ρBR).PosDef := by
    rw [hR_eq]
    refine posDef_of_charpoly_eq hpd.1
      (partialTraceLeft_isHermitian (pureDensity_isHermitian Ψ)) ?_ hpd
    rw [← hΨ]; exact charpoly_partialTrace_pure_eq Ψ
  -- ρ_BR trace = 1: trace (pureDensity (reshapeABR Ψ)) = trace (pureDensity Ψ) = trace ρAB ... = 1.
  have htrBR : ρBR.trace = 1 := by
    rw [hρBR, partialTraceLeft_trace]
    -- trace |Ψ'⟩⟨Ψ'| = ∑ ‖Ψ' p‖² = ∑ ‖Ψ q‖² (reindex) = trace |Ψ⟩⟨Ψ| = trace ρAB = 1.
    have hreshape_norm : (∑ p, ‖reshapeABR Ψ p‖ ^ 2) = ∑ q, ‖Ψ q‖ ^ 2 := by
      refine Fintype.sum_bijective
        (fun p : n × (m × (n × m)) => ((p.1, p.2.1), p.2.2)) ?_ _ _ (fun p => rfl)
      exact ⟨fun a b h => by
        obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
        simp only [Prod.mk.injEq] at h ⊢; tauto,
        fun q => ⟨(q.1.1, q.1.2, q.2), rfl⟩⟩
    have htrΨ : (pureDensity Ψ).trace = 1 := by
      rw [← hΨ] at htr; rw [partialTraceRight_trace] at htr; exact htr
    rw [pureDensity_trace, hreshape_norm, ← pureDensity_trace, htrΨ]
  -- subadditivity on ρ_BR: S(ρ_BR) ≤ S(ρ_B) + S(ρ_R).
  have hsub := vonNeumannEntropy_subadditive hρBR_psd htrBR hpdB' hpdR'
  -- S(ρ_R) = S(ρ_AB) via the AB|R cut: S(Tr_B' ρBR) = S(Tr_A Ψ) = S(Tr_R Ψ) = S(ρ_AB).
  have hStep2 : vonNeumannEntropy hpdR'.1 = vonNeumannEntropy hpd.1 := by
    have hsym := pure_marginal_entropy_eq (n := n × m) (m := n × m) Ψ
    calc vonNeumannEntropy hpdR'.1
        = vonNeumannEntropy (partialTraceLeft_isHermitian (pureDensity_isHermitian Ψ)) :=
          spectral_sum_eq_of_charpoly_eq _ _ (by rw [hR_eq]) _
      _ = vonNeumannEntropy (partialTraceRight_isHermitian (pureDensity_isHermitian Ψ)) := hsym.symm
      _ = vonNeumannEntropy hpd.1 := spectral_sum_eq_of_charpoly_eq _ _ (by rw [hΨ]) _
  -- S(ρ_B) = S(partialTraceLeft ρAB).
  have hStepB : vonNeumannEntropy hpdB'.1
      = vonNeumannEntropy (partialTraceLeft_isHermitian hpd.1) :=
    spectral_sum_eq_of_charpoly_eq _ _ (by rw [hB_eq]) _
  rw [hStep1]
  rw [hStep2, hStepB] at hsub
  exact hsub

/-- **Araki–Lieb triangle inequality** `|S(ρ_A) − S(ρ_B)| ≤ S(ρ_AB)` for a **positive-definite**
bipartite density `ρ_AB` with both marginals `ρ_A = Tr_B ρ_AB`, `ρ_B = Tr_A ρ_AB`
**positive-definite**. Genuine, non-vacuous content for **correlated** full-rank `ρ_AB` (equality
only at product states; `S(ρ_A) − S(ρ_B)` is generically nonzero). Two applications of
`araki_lieb_one_side` (the second to the index-swapped state `ρ_BA`, whose marginals are `ρ_B`,
`ρ_A` and whose entropy equals `S(ρ_AB)` by reindexing).

**Honest scope.** The `ρ_AB` positive-definite hypothesis is load-bearing: the purification route
runs subadditivity on the `B | R` bipartition, which (via `vonNeumannEntropy_subadditive`) needs
the ancilla marginal `ρ_R` positive-definite, and `ρ_R` is cospectral with `ρ_AB`. The
**pure-entangled** case (`S(ρ_AB) = 0`, marginals full-rank) is therefore **not** covered by this
form (it is the boundary `S(ρ_A) = S(ρ_B)` there); extending to singular `ρ_AB` needs a
limiting / support-restriction argument. The bound is nonetheless a true inequality on correlated
full-rank states, not a product-state identity. -/
theorem vonNeumannEntropy_araki_lieb
    {ρAB : Matrix (n × m) (n × m) ℂ} (hpd : ρAB.PosDef) (htr : ρAB.trace = 1)
    (hpdA : (partialTraceRight ρAB).PosDef) (hpdB : (partialTraceLeft ρAB).PosDef) :
    |vonNeumannEntropy hpdA.1 - vonNeumannEntropy hpdB.1| ≤ vonNeumannEntropy hpd.1 := by
  classical
  -- forward direction: S(ρ_A) ≤ S(ρ_B) + S(ρ_AB).
  have hAB : vonNeumannEntropy hpdA.1 ≤ vonNeumannEntropy hpdB.1 + vonNeumannEntropy hpd.1 := by
    have h := araki_lieb_one_side hpd htr hpdB
    rwa [vonNeumannEntropy_congr (partialTraceRight_isHermitian hpd.1) hpdA.1,
      vonNeumannEntropy_congr (partialTraceLeft_isHermitian hpd.1) hpdB.1] at h
  -- backward direction via the swapped state ρ_BA = ρ_AB reindexed along Prod.swap.
  set e : (n × m) ≃ (m × n) := Equiv.prodComm n m with he
  set ρBA : Matrix (m × n) (m × n) ℂ := ρAB.reindex e e with hρBA
  have hBAh : ρBA.IsHermitian := by rw [hρBA]; exact hpd.1.reindex e
  -- charpoly of ρBA equals that of ρAB.
  have hcpBA : ρBA.charpoly = ρAB.charpoly := by rw [hρBA]; exact Matrix.charpoly_reindex e ρAB
  have hpdBA : ρBA.PosDef := posDef_of_charpoly_eq hpd.1 hBAh hcpBA.symm hpd
  have htrBA : ρBA.trace = 1 := by
    have hsubtr : (ρAB.submatrix e.symm e.symm).trace = ρAB.trace := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
      exact Equiv.sum_comp e.symm (fun i => ρAB i i)
    rw [hρBA, Matrix.reindex_apply, hsubtr, htr]
  -- marginals of ρBA: Tr_B' ρBA = ρ_B, Tr_A' ρBA = ρ_A (the A,B roles swap).
  have hBA_right : partialTraceRight ρBA = partialTraceLeft ρAB := by
    ext i j
    simp only [partialTraceRight_apply, partialTraceLeft_apply, hρBA, Matrix.reindex_apply,
      Matrix.submatrix_apply, he, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk]
  have hBA_left : partialTraceLeft ρBA = partialTraceRight ρAB := by
    ext i j
    simp only [partialTraceLeft_apply, partialTraceRight_apply, hρBA, Matrix.reindex_apply,
      Matrix.submatrix_apply, he, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk]
  have hpdB_BA : (partialTraceLeft ρBA).PosDef := by rw [hBA_left]; exact hpdA
  -- S(ρ_B) ≤ S(ρ_A) + S(ρ_BA), and S(ρ_BA) = S(ρ_AB).
  have hBA : vonNeumannEntropy hpdB.1 ≤ vonNeumannEntropy hpdA.1 + vonNeumannEntropy hpd.1 := by
    have h := araki_lieb_one_side hpdBA htrBA hpdB_BA
    rw [show vonNeumannEntropy (partialTraceRight_isHermitian hpdBA.1)
          = vonNeumannEntropy hpdB.1 from
        spectral_sum_eq_of_charpoly_eq _ _ (by rw [hBA_right]) _,
      show vonNeumannEntropy (partialTraceLeft_isHermitian hpdBA.1)
          = vonNeumannEntropy hpdA.1 from
        spectral_sum_eq_of_charpoly_eq _ _ (by rw [hBA_left]) _,
      show vonNeumannEntropy hpdBA.1 = vonNeumannEntropy hpd.1 from
        spectral_sum_eq_of_charpoly_eq _ _ hcpBA _] at h
    exact h
  rw [abs_le]
  constructor <;> linarith

end ArakiLieb

end QuantumInfo
