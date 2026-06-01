import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.LinearAlgebra.Matrix.Block
import CsdLean4.LF4.MomentMarginalUniform

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
    rw [hB, Matrix.updateRow_self, Finset.sum_apply, psiMat_col_sum]
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
      ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply,
      ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.proj_apply,
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
      ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
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
  simp only [mem_image, domainN, posQuadrant, Set.mem_setOf_eq]
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

end LF4
end CSD
