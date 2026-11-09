/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceSchrodingerFlow
public import CsdLean4.Mathlib.Analysis.InnerProductSpace.EuclideanLin

/-!
# The Poisson bracket of observables on `ℂℙⁿ` is the commutator

**TERM-SCOPE(Hamiltonian)** **TERM-SCOPE(Kahler)** — this module uses the vector-field sense of
"Hamiltonian" and the restricted sense of "Kähler";
`specs/TERMS.md` records what is backed.

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold.Instances`).
BACKLOG #325 (geometric QM, item 2 of the 2026-11-08 plan).

On a symplectic manifold the Poisson bracket of two functions is `{f, g} = ω(X_f, X_g)`, and a
function changes along the flow of `g` at the rate `{f, g}`. On `ℂℙⁿ` with the Fubini–Study form,
expectation values are functions, and their bracket is the expectation value of the commutator:
**Kibble's dictionary**, quantum commutators as classical Poisson brackets, with the constant fixed
by the corpus's `-2` convention (`schrodingerHamiltonian H = -2 ⟨H⟩`).

## The bracket on a symplectic manifold

* `IsSymplectic.poissonBracket` — `{f, g} x = ω x (X_f x, X_g x)`;
  `IsSymplectic.poissonBracket_eq_mfderiv` — `{f, g} = df (X_g)`;
  `IsSymplectic.poissonBracket_eq_of_isHamiltonianVectorField` — the same with any Hamiltonian field
  of `g`; `IsSymplectic.poissonBracket_antisymm`, `IsSymplectic.poissonBracket_self`;
* `hasDerivAt_comp_of_isMIntegralCurve'` — `f ∘ γ` has derivative `df (Y)` along an integral
  curve of `Y`; ★★ `IsSymplectic.hasDerivAt_comp_poissonBracket` — **`d/dt f(γ t) = {f, g}(γ t)`
  along the flow of `g`**.

## Ehrenfest's equation on the manifold

* `commObs A B = -i (AB - BA)`, `commObs_isHermitian`, `toEuclideanLinApplyCLM`, `inner_commObs`;
* ★★ `hasDerivAt_expectation_schrodingerUnitary_smul` — **`d/dt ⟨A⟩(exp(-itB) • p) = ⟨-i[A, B]⟩`
  at `t = 0`**, in the ambient inner product;
* `mfderiv_apply_eq_of_hasDerivAt`, `contMDiff_expectation`, `mdifferentiableAt_expectation`,
  `schrodingerUnitary_zero_smul`;
* ★★ `mfderiv_expectation_schrodingerField` — **`d⟨A⟩ (X_B) = ⟨-i[A, B]⟩`**, the manifold form;
  `expectation_isHamiltonianVectorField` — the field of `⟨B⟩` is `-½ X_B`.

## The bracket of observables

* ★★★ `poissonBracket_schrodingerHamiltonian` — **`{-2⟨A⟩, -2⟨B⟩} = -2⟨-i[A, B]⟩`**: the map
  `A ↦ -2⟨A⟩` carries the commutator bracket `-i[·, ·]` of Hermitian matrices to the Poisson
  bracket;
* ★★★ `poissonBracket_expectation` — **`{⟨A⟩, ⟨B⟩} = -½ ⟨-i[A, B]⟩`**;
* `expectation_eq_zero_iff` — a Hermitian `C` has `⟨C⟩ = 0` everywhere only if `C = 0` (a control:
  the bracket identity is not vacuous on the zero observable);
* ★★ `hasDerivAt_expectation_schrodingerUnitary_smul_at` — the rate at every time;
* ★★★ `expectation_conserved_iff_commute` — **`⟨A⟩` is conserved by the flow of `H` exactly when
  `A` commutes with `H`**.

## Honest scope

⚠️ **The constants are conventions, sign included.** `fsForm` at the chart origin is
`-4 Im⟪u, v⟫`, which is `-2` times the standard `i∂∂̄ log(1 + ‖w‖²)` (equal to
`2 Im⟪u, v⟫` there); with `g(u, v) = ω(Ju, v)` this gives
`ω(u, v) = -g(Ju, v)`, the opposite sign to the convention `ω = g(J·, ·)`.
That is why the generator of `exp(-itH)` is `-2⟨H⟩` and the bracket of expectations is `-½` times
the expectation of `-i[A, B]` (Kibble's `{⟨A⟩, ⟨B⟩} = ⟨-i[A, B]⟩` in the standard convention).
Nothing is rescaled.

⚠️ **Only the generator is assumed Hermitian.** The bracket identities and Ehrenfest's equation
need `B` Hermitian (it generates the flow) and hold for every matrix `A`, with `expectation` the
real part `⟪z, Az⟫.re / ‖z‖²`; the conservation theorem assumes both Hermitian, since it needs
`-i[A, H]` Hermitian to conclude from `⟨-i[A, H]⟩ = 0` that `[A, H] = 0`.

⚠️ **The Jacobi identity is elsewhere.** For general smooth functions on any symplectic manifold
it is `IsSymplectic.poissonBracket_jacobi` (#336, `Instances/ProjectiveSpacePoissonJacobi.lean`,
from `dω = 0` through Cartan's formula); this module proves only the Lie hom on `-2⟨A⟩`.

## References

T. W. B. Kibble, Commun. Math. Phys. 65 (1979) 189; A. Heslot, Phys. Rev. D 31 (1985) 1341;
A. Ashtekar, T. A. Schilling, in *On Einstein's Path* (1999) 23, § 3;
`Instances/ProjectiveSpaceSchrodingerFlow.lean` (G13, the Schrödinger field and its flow),
`Geometry/Manifold/HamiltonianVectorField.lean` (G1, G2, G4); `specs/BACKLOG.md` #325;
`specs/future-work.md`.
-/

@[expose] public section

open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix Matrix.Norms.L2Operator
open Kahler DifferentialForm

noncomputable section

/-! ### The bracket on a symplectic manifold -/

namespace DifferentialForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  {β : DifferentialForm (𝓘(ℝ, E)) M ∞ (Fin 2) ℝ}

/-- **The Poisson bracket** `{f, g} = ω(X_f, X_g)` of a symplectic form. -/
def IsSymplectic.poissonBracket (hβ : β.IsSymplectic) (f g : M → ℝ) (x : M) : ℝ :=
  β x ![hβ.hamiltonianVectorField f x, hβ.hamiltonianVectorField g x]

/-- `{f, g} = df (X_g)`. -/
theorem IsSymplectic.poissonBracket_eq_mfderiv (hβ : β.IsSymplectic) (f g : M → ℝ) (x : M) :
    hβ.poissonBracket f g x
      = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) f x (hβ.hamiltonianVectorField g x) :=
  hβ.hamiltonianVectorField_isHamiltonianVectorField f x _

/-- `{f, g} = df (Y)` for any Hamiltonian vector field `Y` of `g`. -/
theorem IsSymplectic.poissonBracket_eq_of_isHamiltonianVectorField (hβ : β.IsSymplectic)
    (f : M → ℝ) {g : M → ℝ} {Y : ∀ x : M, TangentSpace (𝓘(ℝ, E)) x}
    (hY : IsHamiltonianVectorField (fun x => β x) Y g) (x : M) :
    hβ.poissonBracket f g x = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) f x (Y x) := by
  rw [hβ.poissonBracket_eq_mfderiv, ← hY.eq_isSymplectic_hamiltonianVectorField hβ]

/-- The bracket is antisymmetric. -/
theorem IsSymplectic.poissonBracket_antisymm (hβ : β.IsSymplectic) (f g : M → ℝ) (x : M) :
    hβ.poissonBracket f g x = -hβ.poissonBracket g f x :=
  apply_swap (fun x => β x) x _ _

theorem IsSymplectic.poissonBracket_self (hβ : β.IsSymplectic) (f : M → ℝ) (x : M) :
    hβ.poissonBracket f f x = 0 :=
  (β x).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] in
/-- Along an integral curve of `Y`, `f ∘ γ` has derivative `df (Y)`. -/
theorem hasDerivAt_comp_of_isMIntegralCurve' {f : M → ℝ}
    {Y : ∀ x : M, TangentSpace (𝓘(ℝ, E)) x} {γ : ℝ → M} (hγ : IsMIntegralCurve γ Y) {t : ℝ}
    (hf : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) f (γ t)) :
    HasDerivAt (f ∘ γ) (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) f (γ t) (Y (γ t))) t := by
  have h1 : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (f ∘ γ) t
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) f (γ t)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y (γ t)))) :=
    hf.hasMFDerivAt.comp t (hγ t)
  have h2 : HasFDerivAt (f ∘ γ)
      (((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) f (γ t)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y (γ t))) : ℝ →L[ℝ] ℝ)) t :=
    hasMFDerivAt_iff_hasFDerivAt.mp h1
  show HasFDerivAt (f ∘ γ)
    ((1 : ℝ →L[ℝ] ℝ).smulRight (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) f (γ t) (Y (γ t)))) t
  refine h2.congr_fderiv (ContinuousLinearMap.ext_ring ?_)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self, one_smul]
  exact (one_smul ℝ _).symm

/-- ★★ **A function changes along the flow of `g` at the rate `{f, g}`.** -/
theorem IsSymplectic.hasDerivAt_comp_poissonBracket (hβ : β.IsSymplectic) {f g : M → ℝ}
    {Y : ∀ x : M, TangentSpace (𝓘(ℝ, E)) x} (hY : IsHamiltonianVectorField (fun x => β x) Y g)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ Y) {t : ℝ}
    (hf : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) f (γ t)) :
    HasDerivAt (f ∘ γ) (hβ.poissonBracket f g (γ t)) t := by
  rw [hβ.poissonBracket_eq_of_isHamiltonianVectorField f hY]
  exact hasDerivAt_comp_of_isMIntegralCurve' hγ hf

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] in
/-- The derivative of `f` along `Y` is read off the derivative of `f` along any integral curve. -/
theorem mfderiv_apply_eq_of_hasDerivAt {f : M → ℝ} {Y : ∀ x : M, TangentSpace (𝓘(ℝ, E)) x}
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ Y) {t : ℝ}
    (hf : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) f (γ t)) {c : ℝ} (hc : HasDerivAt (f ∘ γ) c t) :
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) f (γ t) (Y (γ t)) = c :=
  (hasDerivAt_comp_of_isMIntegralCurve' hγ hf).unique hc

end DifferentialForm

/-! ### Ehrenfest's equation on `ℂℙⁿ` -/

namespace Projectivization

variable {n : ℕ}

/-- The commutator observable `-i (AB - BA)`. -/
def commObs (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (-Complex.I) • (A * B - B * A)

theorem commObs_isHermitian {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) : (commObs A B).IsHermitian := by
  unfold commObs Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, hA.eq, hB.eq, star_neg, Complex.star_def, Complex.conj_I, neg_neg,
    ← neg_sub, smul_neg, neg_smul]

/-- The vector `M v`, as an `ℝ`-linear map of the matrix. -/
def toEuclideanLinApplyCLM (v : Ambient n) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ →L[ℝ] Ambient n :=
  (LinearMap.toContinuousLinearMap
    { toFun := fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => Matrix.toEuclideanLin M v
      map_add' := fun M M' => by simp
      map_smul' := fun c M => by simp } :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ →L[ℂ] Ambient n).restrictScalars ℝ

theorem toEuclideanLinApplyCLM_apply (v : Ambient n) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    toEuclideanLinApplyCLM v M = Matrix.toEuclideanLin M v := rfl

/-- The numerator of `⟨-i[A, B]⟩` at a vector. -/
theorem inner_commObs {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hB : B.IsHermitian)
    (ψ : Ambient n) :
    inner ℂ ψ (Matrix.toEuclideanLin (commObs A B) ψ)
      = inner ℂ ψ (Matrix.toEuclideanLin A (Matrix.toEuclideanLin ((-Complex.I) • B) ψ))
        + inner ℂ (Matrix.toEuclideanLin ((-Complex.I) • B) ψ) (Matrix.toEuclideanLin A ψ) := by
  have hBs := Matrix.isSymmetric_toEuclideanLin_iff.2 hB
  unfold commObs
  rw [map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply, Matrix.toEuclideanLin_mul_apply,
    Matrix.toEuclideanLin_mul_apply, map_smul, LinearMap.smul_apply, map_smul, inner_smul_right,
    inner_smul_right, inner_smul_left, inner_sub_right, hBs ψ, Complex.conj_neg_I]
  ring

/-- ★★ **Ehrenfest's equation, in the ambient space**: `d/dt ⟨A⟩(exp(-itB) • p) = ⟨-i[A, B]⟩_p`
at `t = 0`. -/
theorem hasDerivAt_expectation_schrodingerUnitary_smul {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hB : B.IsHermitian) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (p : ℙ ℂ (Ambient n)) :
    HasDerivAt (fun t : ℝ => expectation A (Matrix.schrodingerUnitary hB t • p))
      (expectation (commObs A B) p) 0 := by
  set ψ := p.rep with hψdef
  have hψ : ψ ≠ 0 := rep_nonzero p
  have hp : p = mk ℂ ψ hψ := (mk_rep p).symm
  set v : ℝ → Ambient n := fun t =>
    Matrix.toEuclideanLin (Matrix.schrodingerUnitary hB t : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) ψ
    with hvdef
  have hv0 : v 0 = ψ := by
    simp only [hvdef, schrodingerUnitary_zero_val hB]
    exact DFunLike.congr_fun (Matrix.toLpLin_one (p := 2)) ψ
  have hvne : ∀ t, v t ≠ 0 := fun t =>
    (Matrix.UnitaryGroup.toEuclideanLinearEquiv
      (Matrix.schrodingerUnitary hB t)).map_ne_zero_iff.2 hψ
  have hvnorm : ∀ t, ‖v t‖ = ‖ψ‖ := fun t => norm_toEuclideanLin_unitary _ ψ
  have hfun : (fun t : ℝ => expectation A (Matrix.schrodingerUnitary hB t • p))
      = fun t => (inner ℂ (v t) (Matrix.toEuclideanLin A (v t))).re / ‖ψ‖ ^ 2 := by
    funext t
    have hsmul : Matrix.schrodingerUnitary hB t • p = mk ℂ (v t) (hvne t) := by
      rw [hp]
      rfl
    rw [hsmul, expectation_mk, hvnorm]
  rw [hfun, hp, expectation_mk]
  -- the derivative of the vector
  have hvd : HasDerivAt v (Matrix.toEuclideanLin ((-Complex.I) • B) ψ) 0 := by
    have h := (toEuclideanLinApplyCLM ψ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (Matrix.schrodingerUnitary_hasDerivAt B hB 0)
    refine h.congr_deriv ?_
    rw [toEuclideanLinApplyCLM_apply, schrodingerUnitary_zero_val hB, one_mul]
  have hAvd : HasDerivAt (fun t => Matrix.toEuclideanLin A (v t))
      (Matrix.toEuclideanLin A (Matrix.toEuclideanLin ((-Complex.I) • B) ψ)) 0 :=
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) A).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hvd
  have hin := hvd.inner ℂ hAvd
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hin
  have hdiv := hre.div_const (‖ψ‖ ^ 2)
  refine hdiv.congr_deriv ?_
  simp only [Complex.reCLM_apply, hv0]
  rw [inner_commObs hB ψ, add_comm]

/-! ### The manifold form, and the bracket of observables -/

theorem contMDiff_expectation {m : WithTop ℕ∞} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ContMDiff (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ ℝ) m
      (expectation (n := n) A) := by
  have h : expectation (n := n) A
      = (fun x : ℝ => (-(1 / 2) : ℝ) * x) ∘ schrodingerHamiltonian A := by
    funext p
    simp only [Function.comp, schrodingerHamiltonian]
    ring
  rw [h]
  exact ((contDiff_const.mul contDiff_id :
    ContDiff ℝ m fun x : ℝ => (-(1 / 2) : ℝ) * x).contMDiff).comp
      (contMDiff_schrodingerHamiltonian A)

theorem mdifferentiableAt_expectation (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (p : ℙ ℂ (Ambient n)) :
    MDifferentiableAt (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ ℝ)
      (expectation A) p :=
  ((contMDiff_expectation (m := 1) A) p).mdifferentiableAt (by simp)

theorem schrodingerUnitary_zero_smul {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hB : B.IsHermitian) (p : ℙ ℂ (Ambient n)) : Matrix.schrodingerUnitary hB 0 • p = p := by
  rw [schrodingerUnitary_zero_val' hB, one_smul]

/-- ★★ **Ehrenfest's equation on the manifold**: `d⟨A⟩ (X_B) = ⟨-i[A, B]⟩`, with `X_B` the
Schrödinger field of `B`. -/
theorem mfderiv_expectation_schrodingerField {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hB : B.IsHermitian) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (p : ℙ ℂ (Ambient n)) :
    mfderiv (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ ℝ) (expectation A) p
      (schrodingerField B p) = expectation (commObs A B) p := by
  have h := mfderiv_apply_eq_of_hasDerivAt (isMIntegralCurve_schrodingerUnitary_smul hB p)
    (t := 0) (mdifferentiableAt_expectation A _)
    (hasDerivAt_expectation_schrodingerUnitary_smul hB A p)
  rwa [schrodingerUnitary_zero_smul hB] at h

/-- The Hamiltonian vector field of `⟨B⟩` is `-½` times the Schrödinger field of `B`. -/
theorem expectation_isHamiltonianVectorField {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hB : B.IsHermitian) :
    IsHamiltonianVectorField (fun x => fsForm x) (fun x => (-(1 / 2) : ℝ) • schrodingerField B x)
      (expectation B) := by
  have h := (schrodingerField_isHamiltonianVectorField hB).smul (-(1 / 2) : ℝ)
    fun x => ((contMDiff_schrodingerHamiltonian (m := 1) B) x).mdifferentiableAt (by simp)
  have he : (-(1 / 2) : ℝ) • schrodingerHamiltonian B = expectation (n := n) B := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, schrodingerHamiltonian]
    ring
  rwa [he] at h

/-- ★★★ **The Poisson bracket of two expectation values is the expectation value of the
commutator**: `{⟨A⟩, ⟨B⟩} = -½ ⟨-i[A, B]⟩` for the Fubini–Study form, `B` Hermitian. -/
theorem poissonBracket_expectation (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hB : B.IsHermitian) (p : ℙ ℂ (Ambient n)) :
    (fsForm_isSymplectic n).poissonBracket (expectation A) (expectation B) p
      = -(1 / 2) * expectation (commObs A B) p := by
  rw [(fsForm_isSymplectic n).poissonBracket_eq_of_isHamiltonianVectorField _
    (expectation_isHamiltonianVectorField hB), map_smul, mfderiv_expectation_schrodingerField hB]
  rfl

/-- ★★★ **`A ↦ -2⟨A⟩` carries the commutator bracket to the Poisson bracket**:
`{-2⟨A⟩, -2⟨B⟩} = -2⟨-i[A, B]⟩`, `B` Hermitian. -/
theorem poissonBracket_schrodingerHamiltonian (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hB : B.IsHermitian) (p : ℙ ℂ (Ambient n)) :
    (fsForm_isSymplectic n).poissonBracket (schrodingerHamiltonian A) (schrodingerHamiltonian B) p
      = schrodingerHamiltonian (commObs A B) p := by
  rw [(fsForm_isSymplectic n).poissonBracket_eq_of_isHamiltonianVectorField _
    (schrodingerField_isHamiltonianVectorField hB)]
  have h := mfderiv_apply_eq_of_hasDerivAt (isMIntegralCurve_schrodingerUnitary_smul hB p)
    (t := 0) (((contMDiff_schrodingerHamiltonian (m := 1) A) _).mdifferentiableAt (by simp))
    ((hasDerivAt_expectation_schrodingerUnitary_smul hB A p).const_mul (-2))
  rw [schrodingerUnitary_zero_smul hB] at h
  exact h

/-- **A Hermitian matrix with zero expectation everywhere is zero** (and conversely). -/
theorem expectation_eq_zero_iff {C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hC : C.IsHermitian) :
    (∀ p : ℙ ℂ (Ambient n), expectation C p = 0) ↔ C = 0 := by
  refine ⟨fun h => ?_, fun h p => by simp [h, expectation]⟩
  have hT := Matrix.isSymmetric_toEuclideanLin_iff.2 hC
  have hzero : ∀ x, inner ℂ (Matrix.toEuclideanLin C x) x = 0 := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    have h1 := h (mk ℂ x hx)
    rw [expectation_mk, div_eq_zero_iff] at h1
    have hre : (inner ℂ x (Matrix.toEuclideanLin C x)).re = 0 :=
      h1.resolve_right (pow_ne_zero 2 (norm_ne_zero_iff.2 hx))
    rw [← hT.coe_re_inner_apply_self x, hT x x]
    simp [hre]
  have h0 := (hT.inner_map_self_eq_zero).1 hzero
  exact Matrix.toEuclideanLin.map_eq_zero_iff.1 h0

/-- ★★ **The rate of `⟨A⟩` along the flow of `H` at every time**: `⟨-i[A, H]⟩` at the current
point. -/
theorem hasDerivAt_expectation_schrodingerUnitary_smul_at {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (p : ℙ ℂ (Ambient n)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => expectation A (Matrix.schrodingerUnitary hH s • p))
      (expectation (commObs A H) (Matrix.schrodingerUnitary hH t • p)) t := by
  have h := hasDerivAt_comp_of_isMIntegralCurve' (isMIntegralCurve_schrodingerUnitary_smul hH p)
    (t := t) (mdifferentiableAt_expectation A _)
  rwa [mfderiv_expectation_schrodingerField hH] at h

/-- ★★★ **`⟨A⟩` is conserved by the flow of `H` exactly when `A` commutes with `H`.** -/
theorem expectation_conserved_iff_commute {A H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : A.IsHermitian) (hH : H.IsHermitian) :
    (∀ (p : ℙ ℂ (Ambient n)) (t : ℝ),
        expectation A (Matrix.schrodingerUnitary hH t • p) = expectation A p)
      ↔ A * H = H * A := by
  have hcomm : A * H = H * A ↔ commObs A H = 0 := by
    rw [commObs, smul_eq_zero, sub_eq_zero]
    simp [Complex.I_ne_zero]
  rw [hcomm, ← expectation_eq_zero_iff (n := n) (commObs_isHermitian hA hH)]
  constructor
  · intro h p
    have hc : HasDerivAt (fun s : ℝ => expectation A (Matrix.schrodingerUnitary hH s • p)) 0 0 := by
      have : (fun s : ℝ => expectation A (Matrix.schrodingerUnitary hH s • p))
          = fun _ => expectation A p := funext fun s => h p s
      rw [this]
      exact hasDerivAt_const _ _
    exact (hasDerivAt_expectation_schrodingerUnitary_smul hH A p).unique hc
  · intro h p t
    have hd : ∀ s,
        HasDerivAt (fun s : ℝ => expectation A (Matrix.schrodingerUnitary hH s • p)) 0 s :=
      fun s => by
        have := hasDerivAt_expectation_schrodingerUnitary_smul_at hH A p s
        rwa [h] at this
    have := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
    rw [this, schrodingerUnitary_zero_smul hH]

end Projectivization
