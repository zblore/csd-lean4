import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.LinearAlgebra.Matrix.Block
import CsdLean4.LF4.MomentMarginalUniform
import CsdLean4.Mathlib.MeasureTheory.LintegralFintypeProd

/-!
# LF4 general-N DH, Slice D (the crux): the ratio map sends `expHalf^{⊗N}` to Dirichlet

The general-`N` analogue of `MomentRatioUniform.lean` (the qubit's
`ratioSqNorm_map_expHalf_prod`, `Beta(1,1)=Uniform[0,1]`): the `N`-fold ratio map
`R_N(s) = (s_0/∑s, …, s_{N-2}/∑s)` pushes `expHalf^{⊗N}` to the Dirichlet(1,…,1)
law, expressed (to dodge the missing Mathlib simplex surface measure) as the
constant `(N−1)!` density on the open simplex in free coordinates `ℝ^{N-1}`.

This file builds the slice incrementally; see `specs/general-n-dh-plan.md` Slice D
for the full DAG (D.1 radial constant → D.3 the determinant `det = S^{N-1}` → D.2
diffeo → D.4 inj/image → D.5 assembly).

**D.1 (this commit): the radial moment constant.** `∫⁻_{S>0} Sⁿ e^{−S/2} = 2^{n+1}·n!`
— the `n`-th moment base (`n = N−1`) that the substituted `S`-integral collapses
to. Generalises `lintegral_radial_const` (N=2: `n=1`, `∫ S e^{−S/2} = 4 = 2²·1!`).
-/

open MeasureTheory Real Set
open scoped ENNReal

namespace CSD
namespace LF4

/-- **D.1 (radial moment, general N).** `∫⁻_{S>0} Sⁿ·e^{−S/2} dS = 2^{n+1}·n!`.
The `n`-th moment of the `Exp(1/2)` shape; with `n = N−1` it is the normalisation
the post-substitution `S`-integral collapses to in the Gamma→Dirichlet change of
variables. Routes through `integral_rpow_mul_exp_neg_mul_Ioi` (`a = n+1`, `r = 1/2`,
giving `2^{n+1}·Γ(n+1)`) + `Real.Gamma_nat_eq_factorial` + the
`ofReal`↔`lintegral` bridge, mirroring `lintegral_radial_const`. -/
theorem lintegral_radial_moment (n : ℕ) :
    ∫⁻ S in Ioi (0 : ℝ), ENNReal.ofReal (S ^ n * Real.exp (-S / 2))
      = ENNReal.ofReal ((2 : ℝ) ^ (n + 1) * (n.factorial : ℝ)) := by
  have hnonneg : ∀ S ∈ Ioi (0 : ℝ), 0 ≤ S ^ n * Real.exp (-S / 2) := by
    intro S hS; simp only [mem_Ioi] at hS; positivity
  -- Bochner value: ∫ Sⁿ e^{−S/2} = 2^{n+1}·n!.
  have hbase : ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-t / 2)
      = (2 : ℝ) ^ (n + 1) * (n.factorial : ℝ) := by
    have h := integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (r := 1 / 2)
      (by positivity) (by norm_num)
    -- RHS: (1/(1/2))^(n+1) · Γ(n+1) = 2^{n+1}·n!.
    have hRHS : ((1 : ℝ) / (1 / 2)) ^ ((n : ℝ) + 1) * Real.Gamma ((n : ℝ) + 1)
        = (2 : ℝ) ^ (n + 1) * (n.factorial : ℝ) := by
      rw [Real.Gamma_nat_eq_factorial,
        show ((1 : ℝ) / (1 / 2)) = 2 by norm_num,
        show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    rw [hRHS] at h
    rw [← h]
    -- Match integrands: t^((n+1)-1) = tⁿ, exp(-(1/2·t)) = exp(-t/2) on Ioi 0.
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    show t ^ n * Real.exp (-t / 2) = t ^ ((n : ℝ) + 1 - 1) * Real.exp (-(1 / 2 * t))
    rw [show ((n : ℝ) + 1 - 1) = (n : ℝ) by ring, Real.rpow_natCast,
      show -(1 / 2 * t) = -t / 2 by ring]
  -- Integrability of `tⁿ·e^{−t/2}` on `Ioi 0`.
  have hint : IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-t / 2)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := 1 / 2)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (le_refl 1) (by norm_num)
    apply h.congr_fun ?_ measurableSet_Ioi
    intro t _
    show t ^ (n : ℝ) * Real.exp (-(1 / 2) * t ^ (1 : ℝ)) = t ^ n * Real.exp (-t / 2)
    rw [Real.rpow_natCast, Real.rpow_one, show -(1 / 2) * t = -t / 2 by ring]
  -- Bridge `ofReal ∘ Bochner = lintegral ∘ ofReal`.
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hnonneg)),
    hbase]

/-! ## D.3 — the Jacobian determinant `det = S^M`

The stick-breaking substitution `Ψ_N(t, S) = (t_0·S, …, t_{M-1}·S, (1−∑t)·S)` on
`ℝ^M × ℝ` (here `N = M+1`) has Jacobian the **bordered matrix** `psiMat S t`:
the top-left `M×M` block is `S·I`, the last column is `(t_0,…,t_{M-1}, 1−∑t)`, the
last row is `(−S,…,−S, 1−∑t)`. Its determinant is `S^M`, proved by the row
operation "add every `castSucc` row into the last row": the last row becomes
`(0,…,0,1)` because each `castSucc`-column sums to `S + (−S) = 0` and the
last column sums to `∑t + (1−∑t) = 1`. The result is then block-triangular.

This is the genuine general-N content (no direct Mathlib lemma); see
`specs/general-n-dh-plan.md` Slice D.3. -/

variable {M : ℕ}

/-- The Jacobian matrix of the stick-breaking substitution `Ψ_{M+1}` at `(t, S)`,
indexed by `Fin (M+1)` (first `M` directions are the `t`-coordinates, the last is
`S`). Bordered: `S·I` block, last column `t`/`1−∑t`, last row `−S`/`1−∑t`. -/
noncomputable def psiMat (S : ℝ) (t : Fin M → ℝ) : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ :=
  Matrix.of fun i j =>
    Fin.lastCases
      -- last row (i = last): −S on castSucc columns, 1−∑t on the last column
      (Fin.lastCases (1 - ∑ k, t k) (fun _ => -S) j)
      -- row i = castSucc a
      (fun a => Fin.lastCases (t a) (fun b => if a = b then S else 0) j)
      i

/-- Column-sum of `psiMat`: every column sums (over all rows) to `[j = last]`.
On a `castSucc` column the diagonal `S` and the last-row `−S` cancel; on the last
column `∑t + (1−∑t) = 1`. This is the content of the row operation. -/
theorem psiMat_col_sum (S : ℝ) (t : Fin M → ℝ) (j : Fin (M + 1)) :
    ∑ i, psiMat S t i j = if j = Fin.last M then (1 : ℝ) else 0 := by
  rw [Fin.sum_univ_castSucc]
  simp only [psiMat, Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]
  induction j using Fin.lastCases with
  | last =>
    simp only [Fin.lastCases_last, if_true]
    abel
  | cast a =>
    simp only [Fin.lastCases_castSucc, if_neg (Fin.castSucc_ne_last a)]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ a) h

/-- **D.3: the Jacobian determinant is `S^M`.** Via the row operation "add every
`castSucc` row into the last row" (`det_updateRow_sum`, coefficient 1), after which
the matrix is two-block-triangular (last row zero off the corner) with diagonal
blocks `S·I_M` and `[1]`. -/
theorem psiMat_det (S : ℝ) (t : Fin M → ℝ) : (psiMat S t).det = S ^ M := by
  -- Row operation: replace the last row by the sum of all rows (det unchanged,
  -- coefficient 1). The new last row is `e_last` by `psiMat_col_sum`.
  set A := psiMat S t with hA
  set B := A.updateRow (Fin.last M) (∑ k, A k) with hB
  have hdet_eq : A.det = B.det := by
    have h := Matrix.det_updateRow_sum A (Fin.last M) (fun _ => (1 : ℝ))
    simp only [one_smul] at h
    rw [hB, h]
  -- Last row of B is the indicator `[j = last]`.
  have hBlast : ∀ j, B (Fin.last M) j = if j = Fin.last M then (1 : ℝ) else 0 := by
    intro j
    have hBj : B (Fin.last M) j = ∑ k, A k j := by
      rw [hB, Matrix.updateRow_self]
      exact Finset.sum_apply j Finset.univ (fun k => A k)
    rw [hBj, hA, psiMat_col_sum]
  -- Off the last row, B agrees with A (= psiMat).
  have hBoff : ∀ i, i ≠ Fin.last M → ∀ j, B i j = A i j := by
    intro i hi j; rw [hB, Matrix.updateRow_ne hi]
  -- B is two-block-triangular for `p := (· ≠ last)`: rows that ARE last (¬p)
  -- vanish on columns that are NOT last (p).
  have htri : ∀ i, ¬ (i ≠ Fin.last M) → ∀ j, (j ≠ Fin.last M) → B i j = 0 := by
    intro i hi j hj
    rw [not_not] at hi; subst hi
    rw [hBlast, if_neg hj]
  rw [hdet_eq, B.twoBlockTriangular_det (· ≠ Fin.last M) htri]
  -- Corner block (i = last): 1×1 with entry B last last = 1.
  have hcorner : (B.toSquareBlockProp (fun i => ¬ (i ≠ Fin.last M))).det = 1 := by
    haveI hne : Nonempty {i : Fin (M + 1) // ¬ (i ≠ Fin.last M)} := ⟨⟨Fin.last M, by simp⟩⟩
    haveI hsub : Subsingleton {i : Fin (M + 1) // ¬ (i ≠ Fin.last M)} := by
      constructor; rintro ⟨a, ha⟩ ⟨b, hb⟩; rw [not_not] at ha hb; simp [ha, hb]
    rw [Matrix.det_eq_elem_of_subsingleton _ (Classical.arbitrary _)]
    obtain ⟨k, hk⟩ := (Classical.arbitrary {i : Fin (M + 1) // ¬ (i ≠ Fin.last M)})
    rw [not_not] at hk
    show B k k = 1
    rw [hk, hBlast, if_pos rfl]
  -- Big block (i ≠ last): `S·I` on the `M` `castSucc` indices, det `S^M`.
  have hbig : (B.toSquareBlockProp (· ≠ Fin.last M)).det = S ^ M := by
    have hblock : B.toSquareBlockProp (· ≠ Fin.last M)
        = Matrix.diagonal (fun _ : {i : Fin (M + 1) // i ≠ Fin.last M} => S) := by
      ext ⟨a, ha⟩ ⟨b, hb⟩
      show B a b = _
      rw [hBoff a ha b]
      obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.mpr ha
      obtain ⟨b', rfl⟩ := Fin.exists_castSucc_eq.mpr hb
      simp only [hA, psiMat, Matrix.of_apply, Fin.lastCases_castSucc, Matrix.diagonal_apply]
      by_cases h : a' = b'
      · subst h; simp
      · rw [if_neg h, if_neg]; exact fun hc => h (by simpa using Subtype.ext_iff.mp hc)
    rw [hblock, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq, Nat.add_sub_cancel]
  rw [hbig, hcorner, mul_one]

/-! ## D.2 — the stick-breaking diffeo `Ψ_N` and its derivative

`Ψ_N : (Fin (M+1) → ℝ) → (Fin (M+1) → ℝ)`,
`y ↦ (k ↦ y(castSucc k)·y(last))` on the first `M` coordinates and
`(1−∑_k y(castSucc k))·y(last)` on the last. On the domain `openSimplex ×ˢ Ioi 0`
(reading `y(last) = S`, `y(castSucc ·) = t`) this is the inverse substitution of the
Gamma→Dirichlet change of variables; its Jacobian is `psiMat S t` (D.3), det `S^M`. -/

/-- The stick-breaking substitution map on `Fin (M+1) → ℝ`. -/
noncomputable def PsiN (y : Fin (M + 1) → ℝ) : Fin (M + 1) → ℝ :=
  Fin.lastCases ((1 - ∑ k, y (Fin.castSucc k)) * y (Fin.last M))
    (fun k => y (Fin.castSucc k) * y (Fin.last M))

/-- The candidate Fréchet derivative of `Ψ_N` at `y`: the linear map of the
Jacobian matrix `psiMat (y last) (y ∘ castSucc)` (D.3). -/
noncomputable def psiFDerivN (y : Fin (M + 1) → ℝ) : (Fin (M + 1) → ℝ) →L[ℝ] (Fin (M + 1) → ℝ) :=
  (Matrix.toLin' (psiMat (y (Fin.last M)) (fun k => y (Fin.castSucc k)))).toContinuousLinearMap

/-- **Jacobian determinant of `Ψ_N`.** `det (psiFDerivN y) = (y last)^M`. Immediate
from `psiMat_det` (D.3) via `LinearMap.det_toLin'`. -/
theorem psiFDerivN_det (y : Fin (M + 1) → ℝ) :
    (psiFDerivN y).det = (y (Fin.last M)) ^ M := by
  rw [psiFDerivN, ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap,
    LinearMap.det_toLin', psiMat_det]

/-- `Ψ_N` is Fréchet differentiable everywhere with derivative `psiFDerivN`. Proved
componentwise (`hasFDerivAt_pi`): each output coordinate is a product/affine
polynomial in the `y`-coordinates; the assembled derivative's matrix is `psiMat`. -/
theorem hasFDerivAt_PsiN (y : Fin (M + 1) → ℝ) : HasFDerivAt PsiN (psiFDerivN y) y := by
  -- `psiFDerivN y = pi (fun i => (proj i).comp (psiFDerivN y))`, so it suffices to
  -- prove each component `(PsiN · i)` has derivative `(proj i).comp (psiFDerivN y)`.
  have hpi : psiFDerivN y
      = ContinuousLinearMap.pi (fun i =>
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (M + 1) => ℝ) i).comp
            (psiFDerivN y)) := by
    ext v i; rfl
  rw [hpi, hasFDerivAt_pi]
  intro i
  -- Component derivative equals `(proj i).comp (psiFDerivN y)`; prove by matching the
  -- explicit `.mul`/affine derivative to the matrix row (the `psiMat` row evaluation).
  induction i using Fin.lastCases with
  | last =>
    -- component: y ↦ (1 − ∑ y∘castSucc) · y last
    have hcomp : (fun x : Fin (M + 1) → ℝ => PsiN x (Fin.last M))
        = fun x => (1 - ∑ k, x (Fin.castSucc k)) * x (Fin.last M) := by
      funext x; simp [PsiN]
    rw [hcomp]
    have hbase :
        HasFDerivAt (fun x : Fin (M + 1) → ℝ => (1 - ∑ k, x (Fin.castSucc k)) * x (Fin.last M))
          ((((1 : ℝ) - ∑ k, y (Fin.castSucc k)) •
              ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (M + 1) => ℝ) (Fin.last M))
            + (y (Fin.last M)) •
              (((0 : (Fin (M + 1) → ℝ) →L[ℝ] ℝ)) -
                ∑ k, ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (M + 1) => ℝ)
                  (Fin.castSucc k))) y := by
      apply HasFDerivAt.mul
      · exact (hasFDerivAt_const (1 : ℝ) y).sub
          (HasFDerivAt.fun_sum (fun k _ => hasFDerivAt_apply (𝕜 := ℝ) (Fin.castSucc k) y))
      · exact hasFDerivAt_apply (𝕜 := ℝ) (Fin.last M) y
    refine hbase.congr_fderiv ?_
    ext v
    show _ = (psiFDerivN y v) (Fin.last M)
    rw [psiFDerivN]
    show _ = (Matrix.toLin' (psiMat (y (Fin.last M)) (fun k => y (Fin.castSucc k))) v) (Fin.last M)
    rw [Matrix.toLin'_apply]
    show _ = ∑ j, psiMat (y (Fin.last M)) (fun k => y (Fin.castSucc k)) (Fin.last M) j * v j
    rw [Fin.sum_univ_castSucc]
    simp only [psiMat, Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last,
      add_apply, FunLike.coe_smul, Pi.smul_apply,
      sub_apply, zero_apply,
      FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul]
    simp only [zero_sub, Finset.mul_sum, mul_neg, neg_mul, Finset.sum_neg_distrib]
    ring
  | cast k =>
    have hcomp : (fun x : Fin (M + 1) → ℝ => PsiN x (Fin.castSucc k))
        = fun x => x (Fin.castSucc k) * x (Fin.last M) := by
      funext x; simp [PsiN]
    rw [hcomp]
    have hbase :
        HasFDerivAt (fun x : Fin (M + 1) → ℝ => x (Fin.castSucc k) * x (Fin.last M))
          (y (Fin.castSucc k) •
              ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (M + 1) => ℝ) (Fin.last M)
            + y (Fin.last M) •
              ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (M + 1) => ℝ) (Fin.castSucc k)) y :=
      (hasFDerivAt_apply (𝕜 := ℝ) (Fin.castSucc k) y).mul (hasFDerivAt_apply (𝕜 := ℝ) (Fin.last M) y)
    refine hbase.congr_fderiv ?_
    ext v
    show _ = (psiFDerivN y v) (Fin.castSucc k)
    rw [psiFDerivN]
    show _ = (Matrix.toLin' (psiMat (y (Fin.last M)) (fun k => y (Fin.castSucc k))) v) (Fin.castSucc k)
    rw [Matrix.toLin'_apply]
    show _ = ∑ j, psiMat (y (Fin.last M)) (fun k => y (Fin.castSucc k)) (Fin.castSucc k) j * v j
    rw [Fin.sum_univ_castSucc]
    simp only [psiMat, Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last,
      add_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · simp; ring
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ k) h

/-! ## D.4 — injectivity and image of `Ψ_N`

`Ψ_N` is a bijection from the domain (open simplex in free coordinates × `Ioi 0`)
onto the open positive quadrant `{s | ∀ i, 0 < s i}`. The inverse sends `s` to
`S := ∑ s`, `t_k := s(castSucc k)/S`. -/

/-- The domain of the substitution, in `Fin (M+1) → ℝ` coordinates: the first `M`
coordinates form the open simplex (`t_k > 0`, `∑ t < 1`), the last is `S > 0`. -/
def domainN : Set (Fin (M + 1) → ℝ) :=
  {y | (∀ k, 0 < y (Fin.castSucc k)) ∧ (∑ k, y (Fin.castSucc k) < 1) ∧ 0 < y (Fin.last M)}

/-- The open positive quadrant in `Fin (M+1) → ℝ`. -/
def posQuadrant : Set (Fin (M + 1) → ℝ) := {s | ∀ i, 0 < s i}

theorem measurableSet_domainN : MeasurableSet (domainN (M := M)) := by
  have h1 : MeasurableSet {y : Fin (M + 1) → ℝ | ∀ k, 0 < y (Fin.castSucc k)} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => measurableSet_lt measurable_const (measurable_pi_apply _)
  have hsum : Measurable (fun y : Fin (M + 1) → ℝ => ∑ k, y (Fin.castSucc k)) :=
    Finset.measurable_sum Finset.univ fun k _ => measurable_pi_apply _
  refine h1.inter (.inter (measurableSet_lt hsum measurable_const)
    (measurableSet_lt measurable_const (measurable_pi_apply _)))

theorem measurableSet_posQuadrant : MeasurableSet (posQuadrant (M := M)) := by
  rw [posQuadrant, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)

/-- **Total-sum recovery.** `∑ i, Ψ_N(y) i = y last = S`. The inverse-map crux:
`(∑_k t_k)·S + (1−∑t)·S = S`. -/
theorem PsiN_sum (y : Fin (M + 1) → ℝ) : ∑ i, PsiN y i = y (Fin.last M) := by
  rw [Fin.sum_univ_castSucc]
  simp only [PsiN, Fin.lastCases_castSucc, Fin.lastCases_last]
  rw [← Finset.sum_mul]
  ring

/-- **D.4a: `Ψ_N` is injective on the domain.** From `Ψ_N y = Ψ_N y'`, summing
recovers `S = S'` (`PsiN_sum`); then each `castSucc` coordinate cancels `S > 0`,
and the last coordinate is `S`. -/
theorem injOn_PsiN : InjOn (PsiN (M := M)) domainN := by
  intro y hy y' hy' heq
  obtain ⟨_, _, hS⟩ := hy
  -- S = S' from the total sum.
  have hSeq : y (Fin.last M) = y' (Fin.last M) := by
    rw [← PsiN_sum y, ← PsiN_sum y', heq]
  -- Extensionality via Fin.lastCases: last coord is S, castSucc coords cancel.
  funext i
  induction i using Fin.lastCases with
  | last => exact hSeq
  | cast k =>
    have hk : PsiN y (Fin.castSucc k) = PsiN y' (Fin.castSucc k) := by rw [heq]
    simp only [PsiN, Fin.lastCases_castSucc] at hk
    rw [hSeq] at hk
    exact mul_right_cancel₀ (ne_of_gt (hSeq ▸ hS)) hk

/-- **D.4b: the image of `Ψ_N` over the domain is the positive quadrant.** -/
theorem image_PsiN : PsiN '' (domainN : Set (Fin (M + 1) → ℝ)) = posQuadrant := by
  ext s
  simp only [mem_image, domainN, posQuadrant, Set.mem_ofPred_eq]
  constructor
  · -- (⊆) every coordinate of Ψ_N y is positive on the domain.
    rintro ⟨y, ⟨ht, hsum, hS⟩, rfl⟩ i
    induction i using Fin.lastCases with
    | last =>
      simp only [PsiN, Fin.lastCases_last]
      exact mul_pos (by linarith) hS
    | cast k =>
      simp only [PsiN, Fin.lastCases_castSucc]
      exact mul_pos (ht k) hS
  · -- (⊇) given positive s, the inverse is S = ∑ s, t_k = s(castSucc k)/S.
    intro hs
    set S : ℝ := ∑ i, s i with hSdef
    have hSpos : 0 < S := Finset.sum_pos (fun i _ => hs i) ⟨Fin.last M, Finset.mem_univ _⟩
    refine ⟨Fin.lastCases S (fun k => s (Fin.castSucc k) / S), ⟨?_, ?_, ?_⟩, ?_⟩
    · -- t_k = s(castSucc k)/S > 0
      intro k; simp only [Fin.lastCases_castSucc]; exact div_pos (hs _) hSpos
    · -- ∑_k s(castSucc k)/S < 1: the omitted last term s(last)/S is positive.
      simp only [Fin.lastCases_castSucc, ← Finset.sum_div]
      rw [div_lt_one hSpos]
      have hsplit : S = (∑ k, s (Fin.castSucc k)) + s (Fin.last M) := by
        rw [hSdef, Fin.sum_univ_castSucc]
      rw [hsplit]; linarith [hs (Fin.last M)]
    · -- last coord = S > 0
      simp only [Fin.lastCases_last]; exact hSpos
    · -- Ψ_N (inverse) = s
      funext i
      induction i using Fin.lastCases with
      | last =>
        simp only [PsiN, Fin.lastCases_last, Fin.lastCases_castSucc, ← Finset.sum_div]
        rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hSpos), one_mul, hSdef,
          Fin.sum_univ_castSucc]
        ring
      | cast k =>
        simp only [PsiN, Fin.lastCases_castSucc, Fin.lastCases_last]
        rw [div_mul_cancel₀ _ (ne_of_gt hSpos)]

/-! ## D.5c — assembly: the ratio map sends `expHalf^{⊗N}` to Dirichlet(1,…,1)

The capstone of Slice D, generalising the qubit `ratioSqNorm_map_expHalf_prod`. -/

/-- The free-coordinate ratio map `s ↦ (k ↦ s(castSucc k)/∑s)`. -/
noncomputable def ratioN (s : Fin (M + 1) → ℝ) : Fin M → ℝ :=
  fun k => s (Fin.castSucc k) / (∑ i, s i)

/-- The open simplex in free coordinates `{t : Fin M → ℝ | (∀ k, 0 < t k) ∧ ∑ t < 1}`. -/
def openSimplexFree : Set (Fin M → ℝ) := {t | (∀ k, 0 < t k) ∧ ∑ k, t k < 1}

theorem measurableSet_openSimplexFree : MeasurableSet (openSimplexFree (M := M)) := by
  have h1 : MeasurableSet {t : Fin M → ℝ | ∀ k, 0 < t k} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => measurableSet_lt measurable_const (measurable_pi_apply k)
  have h2 : Measurable (fun t : Fin M → ℝ => ∑ k, t k) :=
    Finset.measurable_sum Finset.univ fun k _ => measurable_pi_apply _
  exact h1.inter (measurableSet_lt h2 measurable_const)

/-- The single-coordinate `Exp(1/2)` density. -/
private noncomputable def dExp (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (if 0 < s then (1 / 2) * Real.exp (-s / 2) else 0)

private theorem measurable_dExp : Measurable dExp := measurable_expHalf_density

private theorem expHalf_eq_withDensity_dExp : expHalf = volume.withDensity dExp := rfl

/-- **D.5c (the general-N Dirichlet law).** The free-coordinate ratio map pushes
the `N`-fold product `Exp(1/2)^{⊗N}` (`N = M+1`) to `M!` times the uniform measure
on the open simplex — the Dirichlet(1,…,1) law. The qubit
`ratioSqNorm_map_expHalf_prod` is the `M = 1` case (`1! = 1`, uniform on `(0,1)`). -/
theorem ratioSqNorm_map_expHalf_pi :
    Measure.map ratioN (Measure.pi (fun _ : Fin (M + 1) => expHalf))
      = (Nat.factorial M : ℝ≥0∞) • volume.restrict openSimplexFree := by
  have hsum_meas : Measurable (fun s : Fin (M + 1) → ℝ => ∑ i, s i) :=
    Finset.measurable_sum Finset.univ (fun i _ => measurable_pi_apply i)
  have hratio_meas : Measurable (ratioN (M := M)) :=
    measurable_pi_lambda _ (fun k => (measurable_pi_apply _).div hsum_meas)
  have hprod_meas : Measurable (fun x : Fin (M + 1) → ℝ => ∏ i, dExp (x i)) :=
    Finset.measurable_prod _ fun i _ => measurable_dExp.comp (measurable_pi_apply i)
  -- σ-finite of `expHalf` (probability measure) for the pi-withDensity bridge.
  haveI hsf : SigmaFinite ((volume : Measure ℝ).withDensity dExp) := by
    rw [← expHalf_eq_withDensity_dExp]; infer_instance
  -- `pi expHalf = volume.withDensity (∏ dExp)` (D.5b + volume_pi).
  have hpiexp : (Measure.pi (fun _ : Fin (M + 1) => expHalf))
      = (volume : Measure (Fin (M + 1) → ℝ)).withDensity (fun x => ∏ i, dExp (x i)) := by
    simp_rw [expHalf_eq_withDensity_dExp]
    rw [MeasureTheory.pi_withDensity (fun _ : Fin (M + 1) => volume) (fun _ => dExp)
      (fun _ => measurable_dExp), volume_pi]
  refine Measure.ext_of_lintegral _ (fun g hg => ?_)
  -- Step 1-3: push through `ratioN`, expose the joint density.
  rw [lintegral_map hg hratio_meas, hpiexp]
  rw [lintegral_withDensity_eq_lintegral_mul (f := fun x => ∏ i, dExp (x i)) _ hprod_meas
    (show Measurable (fun s : Fin (M + 1) → ℝ => g (ratioN s)) from hg.comp hratio_meas)]
  -- Fold the `Pi.mul` form into a single `fun s => _ * _` (so `set F` matches).
  show (∫⁻ s, (fun s => (∏ i, dExp (s i)) * g (ratioN s)) s ∂volume) = _
  -- The post-density integrand.
  set F : (Fin (M + 1) → ℝ) → ℝ≥0∞ :=
    fun s => (∏ i, dExp (s i)) * g (ratioN s) with hF
  -- Step 4: F is supported on the positive quadrant.
  have hFsupp : F = (posQuadrant (M := M)).indicator F := by
    classical
    funext s
    rw [Set.indicator_apply]
    by_cases hs : s ∈ posQuadrant
    · rw [if_pos hs]
    · rw [if_neg hs, hF]
      simp only [posQuadrant, Set.mem_ofPred_eq, not_forall, not_lt] at hs
      obtain ⟨i, hi⟩ := hs
      refine mul_eq_zero.mpr (Or.inl ?_)
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [dExp, if_neg (not_lt.mpr hi), ENNReal.ofReal_zero]
  -- Pointwise integrand after the substitution, on `domainN`.
  have hcongr : ∀ y ∈ domainN (M := M),
      ENNReal.ofReal |(psiFDerivN y).det| * F (PsiN y)
        = ENNReal.ofReal ((1 / 2) ^ (M + 1) * (y (Fin.last M)) ^ M
            * Real.exp (-(y (Fin.last M)) / 2)) * g (fun k => y (Fin.castSucc k)) := by
    intro y hy
    obtain ⟨ht, hsum, hS⟩ := hy
    -- |det| = S^M (S = y last > 0).
    rw [psiFDerivN_det, abs_of_nonneg (pow_nonneg hS.le M)]
    -- all coordinates of `PsiN y` are positive.
    have hposPsi : ∀ i, 0 < PsiN y i := by
      intro i
      induction i using Fin.lastCases with
      | last => simp only [PsiN, Fin.lastCases_last]; exact mul_pos (by linarith) hS
      | cast k => simp only [PsiN, Fin.lastCases_castSucc]; exact mul_pos (ht k) hS
    -- ratioN (PsiN y) = y ∘ castSucc.
    have hratioPsi : ratioN (PsiN y) = fun k => y (Fin.castSucc k) := by
      funext k; rw [ratioN, PsiN_sum]
      simp only [PsiN, Fin.lastCases_castSucc]
      rw [mul_div_assoc, div_self (ne_of_gt hS), mul_one]
    -- density product collapse: ∏ dExp(PsiN y) = ofReal ((1/2)^(M+1) exp(-S/2)).
    have hprodPsi : (∏ i, dExp (PsiN y i))
        = ENNReal.ofReal ((1 / 2) ^ (M + 1) * Real.exp (-(y (Fin.last M)) / 2)) := by
      have hpos : ∀ i, dExp (PsiN y i) = ENNReal.ofReal ((1 / 2) * Real.exp (-(PsiN y i) / 2)) :=
        fun i => by rw [dExp, if_pos (hposPsi i)]
      simp_rw [hpos]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity),
        Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Real.exp_sum]
      congr 2
      rw [← Finset.sum_div]
      congr 1
      rw [Finset.sum_neg_distrib, PsiN_sum]
    show ENNReal.ofReal (y (Fin.last M) ^ M) * ((∏ i, dExp (PsiN y i)) * g (ratioN (PsiN y))) = _
    rw [hprodPsi, hratioPsi, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    ring
  -- Step 5: change of variables; Step 4 restricts to posQuadrant = PsiN '' domainN.
  rw [hFsupp, lintegral_indicator measurableSet_posQuadrant, ← image_PsiN,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_domainN
      (fun y _ => (hasFDerivAt_PsiN y).hasFDerivWithinAt) injOn_PsiN F,
    setLIntegral_congr_fun measurableSet_domainN hcongr]
  -- Reindex `domainN` as a preimage of `Ioi 0 ×ˢ openSimplexFree` under the
  -- measure-preserving `piFinSuccAbove (last M)`, then Tonelli + radial collapse.
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => ℝ) (Fin.last M) with he_def
  have he : ∀ y, e y = (y (Fin.last M), fun k => y (Fin.castSucc k)) := by
    intro y; simp [he_def, MeasurableEquiv.piFinSuccAbove_apply, Fin.init_def]
  have hdom : domainN (M := M) = e ⁻¹' (Set.Ioi 0 ×ˢ openSimplexFree) := by
    ext y
    simp only [domainN, openSimplexFree, Set.mem_preimage, he, Set.mem_prod, Set.mem_Ioi,
      Set.mem_ofPred_eq]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h3, h1, h2⟩, fun ⟨h3, h1, h2⟩ => ⟨h1, h2, h3⟩⟩
  -- Volume MP for `e`.
  have hmp : MeasurePreserving e (volume : Measure (Fin (M + 1) → ℝ))
      (volume.prod (volume : Measure (Fin M → ℝ))) := by
    have h := measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => (volume : Measure ℝ))
      (Fin.last M)
    rwa [show (Measure.pi (fun _ : Fin (M + 1) => (volume : Measure ℝ)))
          = (volume : Measure (Fin (M + 1) → ℝ)) from volume_pi,
      show (Measure.pi (fun _ : Fin M => (volume : Measure ℝ)))
          = (volume : Measure (Fin M → ℝ)) from volume_pi] at h
  -- Express the integrand as `F' ∘ e` with `F' (S,t) = ofReal(...S^M...) · g t`.
  set F' : ℝ × (Fin M → ℝ) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal ((1 / 2) ^ (M + 1) * p.1 ^ M * Real.exp (-p.1 / 2)) * g p.2 with hF'
  rw [hdom,
    show (fun x : Fin (M + 1) → ℝ =>
        ENNReal.ofReal ((1 / 2) ^ (M + 1) * x (Fin.last M) ^ M * Real.exp (-x (Fin.last M) / 2))
          * g (fun k => x (Fin.castSucc k)))
      = fun x => F' (e x) from by funext x; rw [hF', he],
    hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding F']
  -- `setLIntegral_prod` (Tonelli): outer over `Ioi 0`, inner over `openSimplexFree`.
  rw [setLIntegral_prod _ (by refine Measurable.aemeasurable ?_; rw [hF']; fun_prop)]
  -- Inner integral pulls out the `S`-factor; outer is the radial moment (D.1).
  simp only [hF']
  -- RHS: M! • vol.restrict → (M! : ℝ≥0∞) * ∫⁻_{simplex} g.
  rw [lintegral_smul_measure]
  -- Inner integral: pull the (constant-in-`y`) radial factor out of `∫⁻_{simplex}`.
  have hinner : ∀ S : ℝ,
      (∫⁻ y in openSimplexFree, ENNReal.ofReal ((1 / 2) ^ (M + 1) * S ^ M * Real.exp (-S / 2))
          * g y)
        = ENNReal.ofReal ((1 / 2) ^ (M + 1) * S ^ M * Real.exp (-S / 2))
            * ∫⁻ y in openSimplexFree, g y := by
    intro S; rw [lintegral_const_mul _ hg]
  simp_rw [hinner]
  -- Outer: ∫⁻_{S>0} ofReal((1/2)^{M+1} S^M e^{-S/2}) dS · (∫⁻ g) = M! · (∫⁻ g).
  rw [lintegral_mul_const _ (by fun_prop)]
  -- The radial factor evaluates to `M!`.
  have hradial : (∫⁻ S in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((1 / 2) ^ (M + 1) * S ^ M * Real.exp (-S / 2)))
      = (Nat.factorial M : ℝ≥0∞) := by
    -- Factor out the constant `(1/2)^{M+1}`, apply D.1, then `(1/2)^{M+1}·2^{M+1} = 1`.
    have hfac : ∀ S : ℝ, ENNReal.ofReal ((1 / 2) ^ (M + 1) * S ^ M * Real.exp (-S / 2))
        = ENNReal.ofReal ((1 / 2) ^ (M + 1)) * ENNReal.ofReal (S ^ M * Real.exp (-S / 2)) := by
      intro S
      rw [mul_assoc, ENNReal.ofReal_mul (by positivity)]
    simp_rw [hfac]
    rw [lintegral_const_mul _ (by fun_prop), lintegral_radial_moment,
      ← ENNReal.ofReal_mul (by positivity)]
    rw [show (1 / 2 : ℝ) ^ (M + 1) * (2 ^ (M + 1) * (Nat.factorial M : ℝ))
          = (Nat.factorial M : ℝ) from by
        rw [show (1 / 2 : ℝ) ^ (M + 1) = (2 ^ (M + 1))⁻¹ by rw [one_div, inv_pow]]
        field_simp,
      ENNReal.ofReal_natCast]
  rw [hradial, smul_eq_mul]

end LF4
end CSD
