import CsdLean4.Mathlib.QuantumInfo.Entropy
import CsdLean4.Mathlib.QuantumInfo.PartialTrace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Matrix.Order

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
  rw [Matrix.star_mul, star_star]
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
  rw [Matrix.star_mul, star_star]
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
  rw [Matrix.star_mul, star_star]
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

end QuantumInfo
