/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpacePoissonBracket
public import CsdLean4.Mathlib.Geometry.Manifold.HamiltonianLieDerivative
public import Mathlib.Analysis.Calculus.DifferentialForm.VectorField
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The Jacobi identity for the Poisson bracket of a symplectic form

**TERM-SCOPE(Hamiltonian)** — this module uses the vector-field sense of "Hamiltonian";
`specs/TERMS.md` records what is backed.

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold`).
BACKLOG #336 (geometric QM, completion item 5 of 2026-11-08). The general theorems need nothing
from `ℂℙⁿ`, but `IsSymplectic.poissonBracket` is defined in `ProjectiveSpacePoissonBracket.lean`,
which this module imports; upstreaming means moving the bracket and these theorems to a
`ℂℙⁿ`-free module first.

The Poisson bracket `{f, g} = ω(X_f, X_g)` of a symplectic form satisfies the Jacobi identity
for all smooth functions, because `ω` is closed: Cartan's formula writes `dω(X_f, X_g, X_h)` as
derivatives of the brackets along the fields minus `ω` on Lie brackets, and with Hamiltonian
fields and symmetric second derivatives every Lie-bracket term is again a derivative of a bracket.
The result is `dω(X_a, X_b, X_c) = −({a, {b, c}} + {b, {c, a}} + {c, {a, b}})`.

## The flat computation

* `extDeriv_apply_three` — Cartan's formula for a 2-form on three fields (Mathlib's
  `extDeriv_apply_vectorField`, sums evaluated);
* `flat_apply_lieBracket` — **`ω([X, Y], Z) = −Z{·}` terms**: for a Hamiltonian
  field `Z` of a `C²` function, `ω([X, Y], Z) = −d(ω(Z, Y))(X) + d(ω(Z, X))(Y)` (symmetry of the
  second derivative);
* ★★ `flat_jacobi` — **for a closed 2-form and three Hamiltonian fields of `C²` functions, the
  cyclic sum of `d(ω(B, C))(A)` vanishes at the point**.

## On the manifold

* `fderiv_transition_trivializationAt_snd`, `fderiv_comp_chartAt_symm_trivializationAt_snd` — the
  chart reads tangent vectors and derivatives (with `HamiltonianLieDerivative.lean`'s
  `localRep_apply_localHamiltonianVector` and `extDeriv_localRep_eq_zero`);
* ★★ `IsSymplectic.poissonBracket_poissonBracket_cyclic` — **`{{b, c}, a} + {{c, a}, b} +
  {{a, b}, c} = 0`**, i.e. `d{b, c}(X_a) + d{c, a}(X_b) + d{a, b}(X_c) = 0`, for smooth `a, b, c`;
* ★★★ `IsSymplectic.poissonBracket_jacobi` — **the Jacobi identity
  `{f, {g, h}} + {g, {h, f}} + {h, {f, g}} = 0`** for smooth functions on any symplectic manifold;
* ★★ `Projectivization.poissonBracket_jacobi` — on `ℂℙⁿ` with the Fubini–Study form.

## Honest scope

⚠️ **Smooth functions.** `f, g, h` are `C^∞` (the proof uses `C²` of each and smoothness of the
Hamiltonian fields, which the corpus proves for `C^∞` energies). Only closedness at the point is
used, through the chart at the point.

## References

V. I. Arnold, *Mathematical Methods of Classical Mechanics*, § 40; R. Abraham, J. E. Marsden,
*Foundations of Mechanics*, Prop. 3.3.8; Mathlib's `extDeriv_apply_vectorField`;
`Instances/ProjectiveSpacePoissonBracket.lean` (#325, the bracket and the Lie hom on `-2⟨A⟩`),
`Geometry/Manifold/HamiltonianVectorField.lean` (G1, G2, `localHamiltonianVector`);
`specs/BACKLOG.md` #336; `specs/future-work.md`.
-/

@[expose] public section

open scoped Manifold ContDiff Topology LinearAlgebra.Projectivization
open Filter Bundle VectorField

noncomputable section

namespace DifferentialForm

/-! ### The flat computation -/

section Flat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem sum_ge_one_fin_two (f : Fin 2 → ℝ) : (∑ x ≥ (1 : Fin 2), f x) = f 1 := by
  rw [Finset.sum_eq_single_of_mem 1 (by simp)]
  intro b hb hb1
  simp at hb
  omega

private theorem sum_ge_zero_fin_two (f : Fin 2 → ℝ) : (∑ x ≥ (0 : Fin 2), f x) = f 0 + f 1 := by
  rw [← Fin.sum_univ_two]
  exact Finset.sum_congr (by ext; simp) fun _ _ => rfl

/-- **Cartan's formula on three fields**: `dσ(A, B, C)` is the alternating sum of the
derivatives of `σ` on two of the fields along the third, minus `σ` on the Lie brackets. -/
theorem extDeriv_apply_three {σ : E → E [⋀^Fin 2]→L[ℝ] ℝ} {w₀ : E} {A B C : E → E}
    (hσd : DifferentiableAt ℝ σ w₀) (hA : DifferentiableAt ℝ A w₀)
    (hB : DifferentiableAt ℝ B w₀) (hC : DifferentiableAt ℝ C w₀) :
    extDeriv σ w₀ ![A w₀, B w₀, C w₀]
      = fderiv ℝ (fun x => σ x ![B x, C x]) w₀ (A w₀)
        - fderiv ℝ (fun x => σ x ![A x, C x]) w₀ (B w₀)
        + fderiv ℝ (fun x => σ x ![A x, B x]) w₀ (C w₀)
        - (σ w₀ ![lieBracket ℝ A B w₀, C w₀] - σ w₀ ![lieBracket ℝ A C w₀, B w₀]
          + σ w₀ ![lieBracket ℝ B C w₀, A w₀]) := by
  have hV : ∀ i, DifferentiableAt ℝ (![A, B, C] i) w₀ := by
    intro i; fin_cases i <;> simpa
  have h := extDeriv_apply_vectorField hσd hV
  have hv : (fun i => ![A, B, C] i w₀) = ![A w₀, B w₀, C w₀] := by
    funext i; fin_cases i <;> rfl
  rw [hv] at h
  rw [h, Fin.sum_univ_three, Fin.sum_univ_two, sum_ge_zero_fin_two, sum_ge_one_fin_two]
  have e0 : ∀ x, (Fin.removeNth 0 fun i => ![A, B, C] i x) = ![B x, C x] := fun x => by
    funext i; fin_cases i <;> rfl
  have e1 : ∀ x, (Fin.removeNth 1 fun i => ![A, B, C] i x) = ![A x, C x] := fun x => by
    funext i; fin_cases i <;> rfl
  have e2 : ∀ x, (Fin.removeNth 2 fun i => ![A, B, C] i x) = ![A x, B x] := fun x => by
    funext i; fin_cases i <;> rfl
  have c00 : Matrix.vecCons
      (lieBracket ℝ (![A, B, C] (Fin.castSucc 0)) (![A, B, C] (Fin.succ 0)) w₀)
      ((0 : Fin 2).removeNth ((Fin.castSucc (0 : Fin 2)).removeNth ![A w₀, B w₀, C w₀]))
      = ![lieBracket ℝ A B w₀, C w₀] := by
    funext i; fin_cases i <;> rfl
  have c01 : Matrix.vecCons
      (lieBracket ℝ (![A, B, C] (Fin.castSucc 0)) (![A, B, C] (Fin.succ 1)) w₀)
      ((1 : Fin 2).removeNth ((Fin.castSucc (0 : Fin 2)).removeNth ![A w₀, B w₀, C w₀]))
      = ![lieBracket ℝ A C w₀, B w₀] := by
    funext i; fin_cases i <;> rfl
  have c11 : Matrix.vecCons
      (lieBracket ℝ (![A, B, C] (Fin.castSucc 1)) (![A, B, C] (Fin.succ 1)) w₀)
      ((1 : Fin 2).removeNth ((Fin.castSucc (1 : Fin 2)).removeNth ![A w₀, B w₀, C w₀]))
      = ![lieBracket ℝ B C w₀, A w₀] := by
    funext i; fin_cases i <;> rfl
  simp only [e0, e1, e2, c00, c01, c11]
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, zero_add, pow_zero, pow_one,
    one_smul, neg_smul, Nat.reduceAdd, even_two, Even.neg_pow, one_pow, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **`σ` on a Lie bracket, against a Hamiltonian field**: if `Z` is a Hamiltonian field of a
`C²` function near `w₀`, then `σ([X, Y], Z) = −d(σ(Z, Y))(X) + d(σ(Z, X))(Y)` at `w₀`. -/
theorem flat_apply_lieBracket {σ : E → E [⋀^Fin 2]→L[ℝ] ℝ} {w₀ : E} {X Y Z : E → E}
    {z : E → ℝ} (hX : DifferentiableAt ℝ X w₀) (hY : DifferentiableAt ℝ Y w₀)
    (hz : ContDiffAt ℝ 2 z w₀)
    (hZ : ∀ᶠ w in 𝓝 w₀, ∀ u, σ w ![Z w, u] = fderiv ℝ z w u) :
    σ w₀ ![lieBracket ℝ X Y w₀, Z w₀]
      = -fderiv ℝ (fun w => σ w ![Z w, Y w]) w₀ (X w₀)
        + fderiv ℝ (fun w => σ w ![Z w, X w]) w₀ (Y w₀) := by
  have hdz : DifferentiableAt ℝ (fderiv ℝ z) w₀ :=
    (hz.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsym := hz.isSymmSndFDerivAt (by simp)
  have eY : (fun w => σ w ![Z w, Y w]) =ᶠ[𝓝 w₀] fun w => fderiv ℝ z w (Y w) :=
    hZ.mono fun w hw => hw (Y w)
  have eX : (fun w => σ w ![Z w, X w]) =ᶠ[𝓝 w₀] fun w => fderiv ℝ z w (X w) :=
    hZ.mono fun w hw => hw (X w)
  rw [eY.fderiv_eq, eX.fderiv_eq, fderiv_clm_apply hdz hY, fderiv_clm_apply hdz hX,
    ContinuousAlternatingMap.apply_swap_two, hZ.self_of_nhds, lieBracket_eq]
  simp only [FunLike.coe_add, Pi.add_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.flip_apply, map_sub]
  rw [hsym (X w₀) (Y w₀)]
  ring

/-- ★★ **The flat Jacobi identity**: for a 2-form closed at `w₀` and three Hamiltonian fields of
`C²` functions near `w₀`, the cyclic sum of `d(σ(B, C))(A)` vanishes at `w₀`. -/
theorem flat_jacobi {σ : E → E [⋀^Fin 2]→L[ℝ] ℝ} {w₀ : E} {A B C : E → E} {a b c : E → ℝ}
    (hσ0 : extDeriv σ w₀ = 0) (hσd : DifferentiableAt ℝ σ w₀)
    (hA : DifferentiableAt ℝ A w₀) (hB : DifferentiableAt ℝ B w₀)
    (hC : DifferentiableAt ℝ C w₀)
    (ha : ContDiffAt ℝ 2 a w₀) (hb : ContDiffAt ℝ 2 b w₀) (hc : ContDiffAt ℝ 2 c w₀)
    (hAa : ∀ᶠ w in 𝓝 w₀, ∀ u, σ w ![A w, u] = fderiv ℝ a w u)
    (hBb : ∀ᶠ w in 𝓝 w₀, ∀ u, σ w ![B w, u] = fderiv ℝ b w u)
    (hCc : ∀ᶠ w in 𝓝 w₀, ∀ u, σ w ![C w, u] = fderiv ℝ c w u) :
    fderiv ℝ (fun w => σ w ![B w, C w]) w₀ (A w₀)
      + fderiv ℝ (fun w => σ w ![C w, A w]) w₀ (B w₀)
      + fderiv ℝ (fun w => σ w ![A w, B w]) w₀ (C w₀) = 0 := by
  have hcart := extDeriv_apply_three hσd hA hB hC
  rw [hσ0] at hcart
  have sw : ∀ X Y : E → E, fderiv ℝ (fun w => σ w ![X w, Y w]) w₀
      = -fderiv ℝ (fun w => σ w ![Y w, X w]) w₀ := by
    intro X Y
    rw [← fderiv_neg]
    congr 1
    funext w
    exact ContinuousAlternatingMap.apply_swap_two _ _ _
  have b1 := flat_apply_lieBracket hA hB hc hCc
  have b2 := flat_apply_lieBracket hA hC hb hBb
  have b3 := flat_apply_lieBracket hB hC ha hAa
  rw [b1, b2, b3] at hcart
  simp only [sw (fun w => A w) (fun w => C w), sw (fun w => C w) (fun w => B w),
    sw (fun w => B w) (fun w => A w), FunLike.coe_neg, Pi.neg_apply] at hcart
  simp only [ContinuousAlternatingMap.coe_zero, Pi.zero_apply] at hcart
  linarith

end Flat

/-! ### On the manifold -/

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

omit [FiniteDimensional ℝ E] in
/-- The transition derivative undoes the tangent trivialisation at `x₀`. -/
theorem fderiv_transition_trivializationAt_snd (x₀ : M) {y : M}
    (hy : y ∈ (chartAt E x₀).source) (v : TangentSpace (𝓘(ℝ, E)) y) :
    fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ y)
        ((trivializationAt E (TangentSpace (𝓘(ℝ, E))) x₀ ⟨y, v⟩).2) = v := by
  have hyb : y ∈ (trivializationAt E (TangentSpace (𝓘(ℝ, E))) x₀).baseSet := hy
  rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
    (trivializationAt E (TangentSpace (𝓘(ℝ, E))) x₀) hyb v, ← tangent_symmL_eq_fderiv x₀ y hy]
  exact Trivialization.symmL_continuousLinearMapAt (R := ℝ)
    (trivializationAt E (TangentSpace (𝓘(ℝ, E))) x₀) hyb v

omit [FiniteDimensional ℝ E] in
/-- **A derivative read in the chart at `x₀`**: `d(k ∘ φ⁻¹)` on the trivialised vector is `dk`. -/
theorem fderiv_comp_chartAt_symm_trivializationAt_snd {k : M → ℝ} (x₀ : M) {y : M}
    (hy : y ∈ (chartAt E x₀).source) (hk : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) k y)
    (v : TangentSpace (𝓘(ℝ, E)) y) :
    fderiv ℝ (k ∘ (chartAt E x₀).symm) (chartAt E x₀ y)
        ((trivializationAt E (TangentSpace (𝓘(ℝ, E))) x₀ ⟨y, v⟩).2)
      = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) k y v := by
  set u := (trivializationAt E (TangentSpace (𝓘(ℝ, E))) x₀ ⟨y, v⟩).2
  have hwt : chartAt E x₀ y ∈ (chartAt E x₀).target := (chartAt E x₀).map_source hy
  have hyw : (chartAt E x₀).symm (chartAt E x₀ y) = y := (chartAt E x₀).left_inv hy
  have hsymm : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E))
      (chartAt E x₀).symm (chartAt E x₀ y) :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas E x₀) hwt
  have hky : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) k
      ((chartAt E x₀).symm (chartAt E x₀ y)) := by
    rw [hyw]; exact hk
  have hcomp := mfderiv_comp (chartAt E x₀ y) hky hsymm
  have hsd : mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (chartAt E x₀).symm (chartAt E x₀ y)
      = fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ y) := by
    rw [hsymm.mfderiv]
    simp only [writtenInExtChartAt, Function.comp_def, extChartAt_model_space_eq_id,
      PartialEquiv.refl_symm, PartialEquiv.refl_coe, id, extChartAt_coe, modelWithCornersSelf_coe,
      Set.range_id, fderivWithin_univ, hyw]
    rfl
  have hpt : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) k ((chartAt E x₀).symm (chartAt E x₀ y)) : E →L[ℝ] ℝ)
      = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) k y := by
    rw [hyw]
  have e2 : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (chartAt E x₀).symm (chartAt E x₀ y) u : E)
      = fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ y) u :=
    congrArg (fun L : E →L[ℝ] E => L u) hsd
  have hmf : mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) (k ∘ (chartAt E x₀).symm) (chartAt E x₀ y) u
      = fderiv ℝ (k ∘ (chartAt E x₀).symm) (chartAt E x₀ y) u := by
    have h := congrArg (fun L : E →L[ℝ] ℝ => L u)
      (mfderiv_eq_fderiv (f := k ∘ (chartAt E x₀).symm) (x := chartAt E x₀ y))
    exact h
  rw [← hmf, hcomp]
  refine ((congrArg (fun v : E => mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) k
    ((chartAt E x₀).symm (chartAt E x₀ y)) v) e2).trans
    (congrArg (fun L : E →L[ℝ] ℝ =>
      L (fderiv ℝ (chartAt E y ∘ (chartAt E x₀).symm) (chartAt E x₀ y) u)) hpt)).trans ?_
  exact congrArg (fun v' => mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) k y v')
    (fderiv_transition_trivializationAt_snd x₀ hy v)

variable {β : DifferentialForm (𝓘(ℝ, E)) M ∞ (Fin 2) ℝ}

/-- ★★ **The cyclic sum of derivatives of brackets vanishes**:
`{{b, c}, a} + {{c, a}, b} + {{a, b}, c} = 0`, i.e. `d{b, c}(X_a) + d{c, a}(X_b) + d{a, b}(X_c) = 0`
(`poissonBracket_eq_mfderiv`), for smooth `a, b, c`. -/
theorem IsSymplectic.poissonBracket_poissonBracket_cyclic (hβ : β.IsSymplectic) {a b c : M → ℝ}
    (ha : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) ∞ a) (hb : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) ∞ b)
    (hc : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) ∞ c) (x₀ : M) :
    hβ.poissonBracket (hβ.poissonBracket b c) a x₀
      + hβ.poissonBracket (hβ.poissonBracket c a) b x₀
      + hβ.poissonBracket (hβ.poissonBracket a b) c x₀ = 0 := by
  have hw₀ : chartAt E x₀ x₀ ∈ (chartAt E x₀).target := mem_chart_target E x₀
  have htn : (chartAt E x₀).target ∈ 𝓝 (chartAt E x₀ x₀) :=
    (chartAt E x₀).open_target.mem_nhds hw₀
  -- the flat data in the chart at `x₀`
  have hham : ∀ k : M → ℝ, ∀ᶠ w in 𝓝 (chartAt E x₀ x₀), ∀ u,
      localRep (fun x => β x) x₀ w ![localHamiltonianVector β k x₀ w, u]
        = fderiv ℝ (k ∘ (chartAt E x₀).symm) w u :=
    fun k => Filter.mem_of_superset htn fun w hw u =>
      localRep_apply_localHamiltonianVector β k hβ.nondegenerate x₀ hw u
  have hvd : ∀ k : M → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) ∞ k →
      DifferentiableAt ℝ (localHamiltonianVector β k x₀) (chartAt E x₀ x₀) := fun k hk =>
    (contDiffAt_localHamiltonianVector β k hβ.nondegenerate hk x₀ hw₀).differentiableAt
      (by simp)
  have hfl : ∀ k : M → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) ∞ k →
      ContDiffAt ℝ 2 (k ∘ (chartAt E x₀).symm) (chartAt E x₀ x₀) := by
    intro k hk
    have hs : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (chartAt E x₀).symm (chartAt E x₀ x₀) :=
      (contMDiffOn_chart_symm (n := ∞) (x := x₀)).contMDiffAt htn
    exact (contMDiffAt_iff_contDiffAt.1 ((hk _).comp _ hs)).of_le (by norm_cast)
  have hωd : DifferentiableAt ℝ (localRep (fun x => β x) x₀) (chartAt E x₀ x₀) :=
    (contDiffAt_localRep (fun x => β x) β.contMDiff_toFun x₀ hw₀).differentiableAt (by simp)
  have hω0 : extDeriv (localRep (fun x => β x) x₀) (chartAt E x₀ x₀) = 0 :=
    extDeriv_localRep_eq_zero β hβ x₀ hw₀
  have J := flat_jacobi hω0 hωd (hvd a ha) (hvd b hb) (hvd c hc) (hfl a ha) (hfl b hb)
    (hfl c hc) (hham a) (hham b) (hham c)
  -- each flat term is the manifold derivative of a bracket along a Hamiltonian field
  have key : ∀ p q r : M → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) ∞ p →
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) ∞ q → ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) ∞ r →
      fderiv ℝ (fun w => localRep (fun x => β x) x₀ w
          ![localHamiltonianVector β q x₀ w, localHamiltonianVector β r x₀ w])
          (chartAt E x₀ x₀) (localHamiltonianVector β p x₀ (chartAt E x₀ x₀))
        = hβ.poissonBracket (hβ.poissonBracket q r) p x₀ := by
    intro p q r hp hq hr
    rw [hβ.poissonBracket_eq_mfderiv]
    set R : E → ℝ := fun w => fderiv ℝ (q ∘ (chartAt E x₀).symm) w
      (localHamiltonianVector β r x₀ w) with hRdef
    have hPR : (fun w => localRep (fun x => β x) x₀ w
        ![localHamiltonianVector β q x₀ w, localHamiltonianVector β r x₀ w]) =ᶠ[𝓝 (chartAt E x₀ x₀)]
        R := (hham q).mono fun w hw => hw _
    have hRd : DifferentiableAt ℝ R (chartAt E x₀ x₀) := by
      have hq2 := hfl q hq
      have hdq : DifferentiableAt ℝ (fderiv ℝ (q ∘ (chartAt E x₀).symm)) (chartAt E x₀ x₀) :=
        (hq2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
      exact hdq.clm_apply (hvd r hr)
    -- the bracket is `R` read through the chart, near `x₀`
    have hbr : ∀ y ∈ (chartAt E x₀).source, hβ.poissonBracket q r y = R (chartAt E x₀ y) := by
      intro y hy
      rw [hβ.poissonBracket_eq_mfderiv, hRdef]
      dsimp only
      rw [← trivializationAt_hamiltonianVectorField_snd β r hβ.nondegenerate
        (hr.mdifferentiable (by simp)) x₀ hy]
      exact (fderiv_comp_chartAt_symm_trivializationAt_snd x₀ hy
        ((hq.mdifferentiable (by simp)) y) _).symm
    have hsrc : (chartAt E x₀).source ∈ 𝓝 x₀ :=
      (chartAt E x₀).open_source.mem_nhds (mem_chart_source E x₀)
    have hkd : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) (hβ.poissonBracket q r) x₀ := by
      have h1 : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) (R ∘ chartAt E x₀) x₀ :=
        hRd.mdifferentiableAt.comp x₀
          (mdifferentiableAt_atlas (chart_mem_atlas E x₀) (mem_chart_source E x₀))
      exact h1.congr_of_eventuallyEq (Filter.mem_of_superset hsrc fun y hy => hbr y hy)
    have hRk : (hβ.poissonBracket q r ∘ (chartAt E x₀).symm) =ᶠ[𝓝 (chartAt E x₀ x₀)] R :=
      Filter.mem_of_superset htn fun w hw => by
        show hβ.poissonBracket q r ((chartAt E x₀).symm w) = R w
        rw [hbr _ ((chartAt E x₀).map_target hw), (chartAt E x₀).right_inv hw]
    rw [hPR.fderiv_eq, ← hRk.fderiv_eq, ← trivializationAt_hamiltonianVectorField_snd β p
      hβ.nondegenerate (hp.mdifferentiable (by simp)) x₀ (mem_chart_source E x₀)]
    exact fderiv_comp_chartAt_symm_trivializationAt_snd x₀ (mem_chart_source E x₀) hkd _
  rw [← key a b c ha hb hc, ← key b c a hb hc ha, ← key c a b hc ha hb]
  exact J

/-- ★★★ **The Jacobi identity**: `{f, {g, h}} + {g, {h, f}} + {h, {f, g}} = 0` for smooth
functions on a symplectic manifold. -/
theorem IsSymplectic.poissonBracket_jacobi (hβ : β.IsSymplectic) {f g h : M → ℝ}
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) ∞ f) (hg : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) ∞ g)
    (hh : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) ∞ h) (x : M) :
    hβ.poissonBracket f (hβ.poissonBracket g h) x
      + hβ.poissonBracket g (hβ.poissonBracket h f) x
      + hβ.poissonBracket h (hβ.poissonBracket f g) x = 0 := by
  rw [hβ.poissonBracket_antisymm f, hβ.poissonBracket_antisymm g,
    hβ.poissonBracket_antisymm h]
  have := hβ.poissonBracket_poissonBracket_cyclic hf hg hh x
  linarith

end Manifold

end DifferentialForm

namespace Projectivization

variable {n : ℕ}

/-- ★★ **The Jacobi identity on `ℂℙⁿ`** for the Fubini–Study Poisson bracket of smooth
functions. -/
theorem poissonBracket_jacobi {f g h : ℙ ℂ (Ambient n) → ℝ}
    (hf : ContMDiff (𝓘(ℝ, Fin n → ℂ)) (𝓘(ℝ, ℝ)) ∞ f)
    (hg : ContMDiff (𝓘(ℝ, Fin n → ℂ)) (𝓘(ℝ, ℝ)) ∞ g)
    (hh : ContMDiff (𝓘(ℝ, Fin n → ℂ)) (𝓘(ℝ, ℝ)) ∞ h) (x : ℙ ℂ (Ambient n)) :
    (fsForm_isSymplectic n).poissonBracket f ((fsForm_isSymplectic n).poissonBracket g h) x
      + (fsForm_isSymplectic n).poissonBracket g ((fsForm_isSymplectic n).poissonBracket h f) x
      + (fsForm_isSymplectic n).poissonBracket h ((fsForm_isSymplectic n).poissonBracket f g) x
      = 0 :=
  (fsForm_isSymplectic n).poissonBracket_jacobi hf hg hh x

end Projectivization
