/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.DiagonalOperator
public import CsdLean4.Mathlib.QuantumInfo.AharonovBohmCircle
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Differentiation in Fourier coordinates, and the twisted Laplacian on `L²(S¹)`

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #93(b)(c), closing #93.

[`AharonovBohmCircle.lean`](../QuantumInfo/AharonovBohmCircle.lean) states the Aharonov–Bohm
eigenvalue equation `−(∂ − iΦ)²ψₙ = (n − Φ)²ψₙ` pointwise on the Fourier modes, and says honestly
that "spectrum" there means the level set of those modes.
[`DiagonalOperator.lean`](../InnerProductSpace/DiagonalOperator.lean) supplies the missing operator
theory in general: the diagonal operator of a real weight family on a Hilbert basis is self-adjoint
with spectrum the closure of the weights. This file is the bridge between them, and it needs one
identity that the pin has only in boundary-term form.

## Differentiation in Fourier coordinates

* ★★ `fourierCoeffOn_deriv` — **for a `T`-periodic function, `cₙ(f') = (2πin/T) cₙ(f)`.** The
  boundary term of Mathlib's `fourierCoeffOn_of_hasDerivAt` vanishes by periodicity, and the `n = 0`
  case is the fundamental theorem of calculus; ★★ `fourierCoeffOn_deriv_two_pi` is the `T = 2π` form,
  where the factor is exactly `in`;
* `fourierCoeffOn_add`, `fourierCoeffOn_neg` — the linearity the pin leaves out;
* ★★★ `fourierCoeffOn_twistedLap` — **`−(∂ − iΦ)²` is multiplication by `(n − Φ)²` in Fourier
  coordinates.** This is the eigenvalue equation in the form spectral theory needs: not "the modes
  are eigenvectors" but "the operator is diagonal in the modes".

## The operator, its spectrum, and the flux

* `twistedOp Φ` — **the twisted Laplacian on `L²(ℝ/2πℤ)`** as `fourierBasis.diagOp (circleEigval Φ)`.
  Its domain is `H²` of the circle: the vectors whose weighted Fourier coefficients are still
  square-summable, which is what `diagDomain` *is*;
* ★★★ `isSelfAdjoint_twistedOp` and ★★★ `spectrum_twistedOp` — **self-adjoint, with spectrum the
  closure of the level set**, inherited from the generic brick;
* `toL2` and ★ `fourierCoeff_toL2` — a continuous periodic function on the line as an element of
  `L²(ℝ/2πℤ)`, with the coefficients it came with;
* ★★★ `twistedOp_apply_of_fourierCoeff` and ★★★ `twistedOp_toL2` — **the operator acts on every `C²`
  periodic function exactly as `−(∂ − iΦ)²` does**, which is what makes the two theorems above
  statements about the differential operator and not only about a multiplier;
* ★★★ `exists_eq_of_spectrum_twistedOp_eq` — **the flux is determined by the spectrum**, modulo a
  whole quantum and up to sign. `AharonovBohmCircle.exists_eq_of_range_circleEigval_eq` said this of
  a chosen level set; this says it of the spectrum of a self-adjoint operator on `L²(S¹)`. The
  extraction is `isLeast_norm_image_spectrum`: the ground level survives the closure because the
  bound that produced it is a closed condition.

## Honest scope

⚠️ **The identification is on `C²` periodic functions, not on the whole domain.** `twistedOp_toL2`
covers every twice-differentiable periodic function with continuous second derivative — a dense set
containing all the modes and all trigonometric polynomials — and `twistedOp_apply_of_fourierCoeff`
covers any pair of `L²` functions with the right coefficients. What is *not* proved is that every
element of the domain is twice differentiable in any classical sense: that is a Sobolev embedding
(`H²(S¹) ↪ C¹`), which the pin does not have and which nothing here needs.

⚠️ **No functional calculus and no eigenfunction expansion theorem.** The spectrum is computed as a
set; `hasSum_fourier_series_L2` is Mathlib's, and is not re-proved or used.

⚠️ The flux quantum here is `1` and the spatial period `2π`, as in `AharonovBohmCircle.lean`; the
lattice ring of `AharonovBohmRing.lean` is an analogue, not an instance, and nothing here changes
that.

References: the identity `cₙ(f') = in·cₙ(f)` is the classical one behind the `H^k` scale — e.g.
Katznelson, *An Introduction to Harmonic Analysis* I.§4 — and the multiplication-operator model of a
self-adjoint operator with prescribed spectrum is Reed–Simon I, Theorem VIII.4; Y. Aharonov,
D. Bohm, Phys. Rev. 115 (1959) 485; `specs/BACKLOG.md` #90, #93.
-/

@[expose] public section

open MeasureTheory Real Complex intervalIntegral
open scoped ComplexConjugate

noncomputable section

namespace CircleFourier

variable {a T : ℝ}

/-! ### Preliminaries -/

/-- The character, read on the line, is continuous. -/
theorem continuous_fourier_coe (T : ℝ) (n : ℤ) :
    Continuous fun x : ℝ => (fourier n (x : AddCircle T) : ℂ) :=
  (map_continuous (fourier n)).comp (AddCircle.continuous_mk' T)

theorem intervalIntegrable_fourier_smul {b : ℝ} (n : ℤ) {f : ℝ → ℂ} (hf : Continuous f) :
    IntervalIntegrable (fun x : ℝ => (fourier (-n) (x : AddCircle (b - a)) : ℂ) • f x)
      volume a b :=
  (((continuous_fourier_coe (b - a) (-n)).smul hf)).intervalIntegrable _ _

/-- `fourierCoeffOn` is additive. -/
theorem fourierCoeffOn_add {b : ℝ} (hab : a < b) {f g : ℝ → ℂ} (hf : Continuous f)
    (hg : Continuous g) (n : ℤ) :
    fourierCoeffOn hab (fun x => f x + g x) n
      = fourierCoeffOn hab f n + fourierCoeffOn hab g n := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral,
    ← smul_add, ← intervalIntegral.integral_add (intervalIntegrable_fourier_smul n hf)
      (intervalIntegrable_fourier_smul n hg)]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [smul_eq_mul, mul_add]

/-- `fourierCoeffOn` commutes with negation. -/
theorem fourierCoeffOn_neg {b : ℝ} (hab : a < b) (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn hab (fun x => -f x) n = -fourierCoeffOn hab f n := by
  have h : (fun x : ℝ => -f x) = fun x : ℝ => (-1 : ℂ) * f x := by
    funext x
    ring
  rw [h, fourierCoeffOn.const_mul]
  ring

/-! ### The Fourier coefficients of a derivative -/

/-- ★★ **Differentiation multiplies the `n`-th Fourier coefficient by `2πin/T`.** The boundary term
of the integration by parts vanishes because the function is periodic; this is the identity the
`H^k` scale of spaces is built on, and the pin has it only in the boundary-term form
`fourierCoeffOn_of_hasDerivAt`. -/
theorem fourierCoeffOn_deriv (hT : 0 < T) {f f' : ℝ → ℂ} (hper : Function.Periodic f T)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') (n : ℤ) :
    fourierCoeffOn (lt_add_of_pos_right a hT) f' n
      = 2 * π * Complex.I * n / T * fourierCoeffOn (lt_add_of_pos_right a hT) f n := by
  have hab : a < a + T := lt_add_of_pos_right a hT
  have hTne : ((T : ℝ) : ℂ) ≠ 0 := by
    simpa using hT.ne'
  rcases eq_or_ne n 0 with rfl | hn
  · have hzero : (∫ x in a..(a + T), f' x) = 0 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x)
        (hf'.intervalIntegrable _ _), hper a, sub_self]
    rw [fourierCoeffOn_eq_integral]
    simp only [Int.cast_zero, neg_zero, fourier_zero, one_smul, zero_mul, mul_zero, zero_div]
    rw [hzero, smul_zero]
  · have h := fourierCoeffOn_of_hasDerivAt hab hn (fun x _ => hf x)
      (hf'.intervalIntegrable _ _)
    rw [hper a, sub_self, mul_zero, zero_sub,
      show ((a + T : ℝ) : ℂ) - ((a : ℝ) : ℂ) = ((T : ℝ) : ℂ) from by push_cast; ring] at h
    have hne : (2 * (π : ℂ) * Complex.I * n) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero) ?_
      · exact_mod_cast Real.pi_ne_zero
      · exact_mod_cast hn
    rw [h]
    field_simp

/-- The interval of one period. -/
theorem two_pi_lt (a : ℝ) : a < a + 2 * π := lt_add_of_pos_right a Real.two_pi_pos

/-- ★★ The same at the period `2π`, where the factor is exactly `in`. -/
theorem fourierCoeffOn_deriv_two_pi {f f' : ℝ → ℂ} (hper : Function.Periodic f (2 * π))
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') (n : ℤ) :
    fourierCoeffOn (two_pi_lt a) f' n = Complex.I * n * fourierCoeffOn (two_pi_lt a) f n := by
  have hπ : ((π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  rw [fourierCoeffOn_deriv Real.two_pi_pos hper hf hf' n]
  push_cast
  field_simp

/-! ### The twisted Laplacian in Fourier coordinates -/

/-- `−(∂ − iΦ)²f = −f'' + 2iΦ f' + Φ² f`, written out. -/
def twistedLap (Φ : ℝ) (f f' f'' : ℝ → ℂ) : ℝ → ℂ :=
  fun x => -f'' x + 2 * Complex.I * Φ * f' x + (Φ : ℂ) ^ 2 * f x

theorem twistedLap_apply (Φ : ℝ) (f f' f'' : ℝ → ℂ) (x : ℝ) :
    twistedLap Φ f f' f'' x = -f'' x + 2 * Complex.I * Φ * f' x + (Φ : ℂ) ^ 2 * f x := rfl

/-- ★★★ **The twisted Laplacian is multiplication by `(n − Φ)²` in Fourier coordinates.** This is
the content of the eigenvalue equation of `AharonovBohmCircle.lean` in the form spectral theory
needs: not "the modes are eigenvectors" but "the operator is diagonal in the modes". -/
theorem fourierCoeffOn_twistedLap (Φ : ℝ) {f f' f'' : ℝ → ℂ}
    (hper : Function.Periodic f (2 * π)) (hper' : Function.Periodic f' (2 * π))
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'') (n : ℤ) :
    fourierCoeffOn (two_pi_lt a) (twistedLap Φ f f' f'') n
      = ((QuantumInfo.AharonovBohmCircle.circleEigval Φ n : ℝ) : ℂ)
        * fourierCoeffOn (two_pi_lt a) f n := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hf'c : Continuous f' := continuous_iff_continuousAt.2 fun x => (hf' x).continuousAt
  have h1 : fourierCoeffOn (two_pi_lt a) f' n
      = Complex.I * n * fourierCoeffOn (two_pi_lt a) f n :=
    fourierCoeffOn_deriv_two_pi hper hf hf'c n
  have h2 : fourierCoeffOn (two_pi_lt a) f'' n
      = Complex.I * n * fourierCoeffOn (two_pi_lt a) f' n :=
    fourierCoeffOn_deriv_two_pi hper' hf' hf'' n
  have hfun : twistedLap Φ f f' f''
      = fun x => (-f'' x + 2 * Complex.I * Φ * f' x) + (Φ : ℂ) ^ 2 * f x :=
    funext fun x => by rw [twistedLap_apply]
  have e1 : fourierCoeffOn (two_pi_lt a)
        (fun x => (-f'' x + 2 * Complex.I * Φ * f' x) + (Φ : ℂ) ^ 2 * f x) n
      = fourierCoeffOn (two_pi_lt a) (fun x => -f'' x + 2 * Complex.I * Φ * f' x) n
        + fourierCoeffOn (two_pi_lt a) (fun x => (Φ : ℂ) ^ 2 * f x) n :=
    fourierCoeffOn_add _ (hf''.neg.add (continuous_const.mul hf'c))
      (continuous_const.mul hfc) n
  have e2 : fourierCoeffOn (two_pi_lt a) (fun x => -f'' x + 2 * Complex.I * Φ * f' x) n
      = fourierCoeffOn (two_pi_lt a) (fun x => -f'' x) n
        + fourierCoeffOn (two_pi_lt a) (fun x => 2 * Complex.I * Φ * f' x) n :=
    fourierCoeffOn_add _ hf''.neg (continuous_const.mul hf'c) n
  have e3 : fourierCoeffOn (two_pi_lt a) (fun x => -f'' x) n
      = -fourierCoeffOn (two_pi_lt a) f'' n := fourierCoeffOn_neg _ _ n
  have e4 : fourierCoeffOn (two_pi_lt a) (fun x => 2 * Complex.I * Φ * f' x) n
      = 2 * Complex.I * Φ * fourierCoeffOn (two_pi_lt a) f' n :=
    fourierCoeffOn.const_mul _ _ _ _
  have e5 : fourierCoeffOn (two_pi_lt a) (fun x => (Φ : ℂ) ^ 2 * f x) n
      = (Φ : ℂ) ^ 2 * fourierCoeffOn (two_pi_lt a) f n := fourierCoeffOn.const_mul _ _ _ _
  rw [hfun, e1, e2, e3, e4, e5, h2, h1, QuantumInfo.AharonovBohmCircle.circleEigval]
  push_cast
  linear_combination (2 * (Φ : ℂ) * (n : ℂ) - (n : ℂ) ^ 2)
    * fourierCoeffOn (two_pi_lt a) f n * Complex.I_sq

/-! ### The twisted Laplacian as a self-adjoint operator on `L²(ℝ/2πℤ)` -/

local instance instTwoPiPos : Fact ((0 : ℝ) < 2 * π) := Fact.mk Real.two_pi_pos

open QuantumInfo.AharonovBohmCircle

/-- **The twisted Laplacian `−(∂ − iΦ)²` on `L²(ℝ/2πℤ)`**: the diagonal operator of the levels
`(n − Φ)²` in the Fourier basis, on the domain where those weighted coefficients are still
square-summable. That domain is `H²` of the circle, by definition rather than by construction. -/
def twistedOp (Φ : ℝ) :
    Lp ℂ 2 (@AddCircle.haarAddCircle (2 * π) _) →ₗ.[ℂ] Lp ℂ 2 (@AddCircle.haarAddCircle (2 * π) _) :=
  fourierBasis.diagOp (circleEigval Φ)

theorem twistedOp_eq (Φ : ℝ) : twistedOp Φ = fourierBasis.diagOp (circleEigval Φ) := rfl

/-- ★★★ **The twisted Laplacian is self-adjoint** on that domain. -/
theorem isSelfAdjoint_twistedOp (Φ : ℝ) : IsSelfAdjoint (twistedOp Φ) :=
  fourierBasis.isSelfAdjoint_diagOp _

/-- ★★★ **Its spectrum is the closure of the level set** — the honest spectrum of a self-adjoint
operator, not the set of eigenvalues of a chosen family. -/
theorem spectrum_twistedOp (Φ : ℝ) :
    LinearPMap.spectrum (twistedOp Φ)
      = closure (Set.range fun n : ℤ => ((circleEigval Φ n : ℝ) : ℂ)) :=
  fourierBasis.spectrum_diagOp _

/-- ★ Each Fourier mode is an eigenvector with eigenvalue `(n − Φ)²`. -/
theorem twistedOp_apply_fourierBasis (Φ : ℝ) (n : ℤ) :
    twistedOp Φ ⟨fourierBasis n, fourierBasis.basis_mem_diagDomain (circleEigval Φ) n⟩
      = ((circleEigval Φ n : ℝ) : ℂ) • fourierBasis n :=
  fourierBasis.diagOp_apply_basis _ n

/-- ★★★ **The operator *is* the twisted Laplacian.** Whenever two `L²` functions have the Fourier
coefficients that `−(∂ − iΦ)²` relates — which is what `fourierCoeffOn_twistedLap` says of a `C²`
periodic function and its twisted Laplacian — the first is in the domain and the second is its
image. This is the step that makes `spectrum_twistedOp` a statement about the differential
operator. -/
theorem twistedOp_apply_of_fourierCoeff (Φ : ℝ)
    (F G : Lp ℂ 2 (@AddCircle.haarAddCircle (2 * π) _))
    (h : ∀ n : ℤ, fourierCoeff (G : AddCircle (2 * π) → ℂ) n
      = ((circleEigval Φ n : ℝ) : ℂ) * fourierCoeff (F : AddCircle (2 * π) → ℂ) n) :
    ∃ hF : F ∈ (twistedOp Φ).domain, twistedOp Φ ⟨F, hF⟩ = G := by
  have hrepr : ∀ n : ℤ, fourierBasis.repr G n
      = ((circleEigval Φ n : ℝ) : ℂ) * fourierBasis.repr F n := by
    intro n
    rw [fourierBasis_repr, fourierBasis_repr]
    exact h n
  have hF : F ∈ (twistedOp Φ).domain := by
    refine (fourierBasis.mem_diagDomain_iff (circleEigval Φ)).2 ?_
    exact memℓp_two_of_eq (f := fun n => fourierBasis.repr G n) (fun n => hrepr n)
      (lp.memℓp _)
  refine ⟨hF, fourierBasis.eq_of_repr_eq fun n => ?_⟩
  exact (HilbertBasis.repr_diagOp fourierBasis (circleEigval Φ) ⟨F, hF⟩ n).trans (hrepr n).symm

/-! ### From a `C²` periodic function on the line to the operator -/

theorem continuous_of_hasDerivAt {f f' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x) :
    Continuous f :=
  continuous_iff_continuousAt.2 fun x => (hf x).continuousAt

/-- The derivative of a periodic function is periodic. -/
theorem periodic_deriv {f f' : ℝ → ℂ} (hp : Function.Periodic f T)
    (hf : ∀ x, HasDerivAt f (f' x) x) : Function.Periodic f' T := by
  intro x
  have hin : HasDerivAt (fun y : ℝ => y + T) 1 x := by
    simpa using (hasDerivAt_id x).add_const T
  have h1 : HasDerivAt (fun y : ℝ => f (y + T)) (f' (x + T)) x := by
    simpa [Function.comp_def] using (hf (x + T)).scomp x hin
  have h2 : (fun y : ℝ => f (y + T)) = f := funext fun y => hp y
  rw [h2] at h1
  exact h1.unique (hf x)

theorem continuous_twistedLap (Φ : ℝ) {f f' f'' : ℝ → ℂ} (hfc : Continuous f)
    (hf'c : Continuous f') (hf''c : Continuous f'') : Continuous (twistedLap Φ f f' f'') :=
  ((hf''c.neg).add ((continuous_const).mul hf'c)).add ((continuous_const).mul hfc)

theorem periodic_twistedLap (Φ : ℝ) {f f' f'' : ℝ → ℂ} (hp : Function.Periodic f T)
    (hp' : Function.Periodic f' T) (hp'' : Function.Periodic f'' T) :
    Function.Periodic (twistedLap Φ f f' f'') T := by
  intro x
  rw [twistedLap_apply, twistedLap_apply, hp x, hp' x, hp'' x]

/-- A continuous `2π`-periodic function on the line, as an element of `L²(ℝ/2πℤ)`. -/
def toL2 (f : ℝ → ℂ) (hc : Continuous f) (hp : Function.Periodic f (2 * π)) :
    Lp ℂ 2 (@AddCircle.haarAddCircle (2 * π) _) :=
  ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
    ⟨AddCircle.liftIoc (2 * π) 0 f,
      AddCircle.liftIoc_continuous (hp 0).symm hc.continuousOn⟩

/-- ★ Its Fourier coefficients are the interval coefficients of the function it came from. -/
theorem fourierCoeff_toL2 (f : ℝ → ℂ) (hc : Continuous f) (hp : Function.Periodic f (2 * π))
    (n : ℤ) :
    fourierCoeff ((toL2 f hc hp : AddCircle (2 * π) → ℂ)) n
      = fourierCoeffOn (two_pi_lt 0) f n := by
  have hae : ((toL2 f hc hp : Lp ℂ 2 (@AddCircle.haarAddCircle (2 * π) _)) :
      AddCircle (2 * π) → ℂ) =ᵐ[AddCircle.haarAddCircle] AddCircle.liftIoc (2 * π) 0 f :=
    ContinuousMap.coeFn_toLp AddCircle.haarAddCircle _
  have h1 : fourierCoeff ((toL2 f hc hp : AddCircle (2 * π) → ℂ)) n
      = fourierCoeff (AddCircle.liftIoc (2 * π) 0 f) n := by
    simp only [fourierCoeff]
    refine integral_congr_ae ?_
    filter_upwards [hae] with t ht
    rw [ht]
  rw [h1, fourierCoeff_liftIoc_eq]

/-- ★★★ **The operator applied to a `C²` periodic function is its twisted Laplacian.** This closes
the loop: `spectrum_twistedOp` and `isSelfAdjoint_twistedOp` are statements about an operator that
acts on every `C²` periodic function exactly as `−(∂ − iΦ)²` does. -/
theorem twistedOp_toL2 (Φ : ℝ) {f f' f'' : ℝ → ℂ} (hp : Function.Periodic f (2 * π))
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : Continuous f'') :
    ∃ h : toL2 f (continuous_of_hasDerivAt hf) hp ∈ (twistedOp Φ).domain,
      twistedOp Φ ⟨toL2 f (continuous_of_hasDerivAt hf) hp, h⟩
        = toL2 (twistedLap Φ f f' f'')
            (continuous_twistedLap Φ (continuous_of_hasDerivAt hf)
              (continuous_of_hasDerivAt hf') hf'')
            (periodic_twistedLap Φ hp (periodic_deriv hp hf)
              (periodic_deriv (periodic_deriv hp hf) hf')) := by
  refine twistedOp_apply_of_fourierCoeff Φ _ _ fun n => ?_
  rw [fourierCoeff_toL2, fourierCoeff_toL2]
  exact fourierCoeffOn_twistedLap Φ hp (periodic_deriv hp hf) hf hf' hf'' n

/-! ### The flux is determined by the spectrum -/

/-- The smallest modulus in the spectrum is the squared distance from the flux to the nearest whole
quantum: the ground level survives the closure, because the bound that produced it is closed. -/
theorem isLeast_norm_image_spectrum (Φ : ℝ) :
    IsLeast ((fun z : ℂ => ‖z‖) '' LinearPMap.spectrum (twistedOp Φ)) ((Φ - round Φ) ^ 2) := by
  constructor
  · refine ⟨((circleEigval Φ (round Φ) : ℝ) : ℂ), ?_, ?_⟩
    · rw [spectrum_twistedOp]
      exact subset_closure ⟨round Φ, rfl⟩
    · show ‖((circleEigval Φ (round Φ) : ℝ) : ℂ)‖ = (Φ - round Φ) ^ 2
      rw [Complex.norm_real, circleEigval_round]
      exact abs_of_nonneg (by positivity)
  · rintro y ⟨z, hz, rfl⟩
    rw [spectrum_twistedOp] at hz
    have hclosed : IsClosed {w : ℂ | (Φ - round Φ) ^ 2 ≤ ‖w‖} :=
      isClosed_le continuous_const continuous_norm
    have hsub : (Set.range fun n : ℤ => ((circleEigval Φ n : ℝ) : ℂ))
        ⊆ {w : ℂ | (Φ - round Φ) ^ 2 ≤ ‖w‖} := by
      rintro w ⟨n, rfl⟩
      have h1 : (Φ - round Φ) ^ 2 ≤ circleEigval Φ n := sq_sub_round_le_circleEigval Φ n
      have h2 : ‖((circleEigval Φ n : ℝ) : ℂ)‖ = circleEigval Φ n := by
        rw [Complex.norm_real]
        exact abs_of_nonneg (by rw [circleEigval]; positivity)
      rw [Set.mem_ofPred_eq, h2]
      exact h1
    exact closure_minimal hsub hclosed hz

/-- ★★★ **The flux is determined by the spectrum of the operator**, modulo a whole quantum and up to
sign. This is `AharonovBohmCircle.exists_eq_of_range_circleEigval_eq` upgraded from a statement about
a chosen level set to a statement about the spectrum of a self-adjoint operator on `L²(S¹)`. -/
theorem exists_eq_of_spectrum_twistedOp_eq {Φ Φ' : ℝ}
    (h : LinearPMap.spectrum (twistedOp Φ) = LinearPMap.spectrum (twistedOp Φ')) :
    ∃ k : ℤ, Φ' = Φ + k ∨ Φ' = -Φ + k := by
  have h1 := isLeast_norm_image_spectrum Φ
  have h2 := isLeast_norm_image_spectrum Φ'
  rw [h] at h1
  exact exists_eq_of_sq_sub_round_eq (le_antisymm (h1.2 h2.1) (h2.2 h1.1))

end CircleFourier

end

end
