/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InnerProductSpace.MultiplicationOperator
public import CsdLean4.Mathlib.Analysis.Semigroup.SchrodingerGroup

/-!
# The free Hamiltonian as a self-adjoint operator, and its spectrum

**Category:** 1-Mathlib (CSD-free; staged for upstream).

Everything the corpus proves about continuum dynamics is proved with **bounded** objects: the
unitary group `U₀(t) = 𝓕⁻¹ e^{−2π²itξ²} 𝓕` ([`SchrodingerGroup.lean`](SchrodingerGroup.lean)), the
Fourier multiplier, the kernel. The Hamiltonian itself is unbounded and was never written as an
operator. This module writes it, in the momentum representation, on top of
[`../InnerProductSpace/MultiplicationOperator.lean`](../InnerProductSpace/MultiplicationOperator.lean):

* `freeSymbolOp` — **the free Hamiltonian in the momentum representation**: multiplication by
  the corpus's own `freeSymbol`, `m(ξ) = 2π²ξ²`, on `L²(ℝ)` with its natural domain, dense
  (`dense_domain_freeSymbolOp`);
* ★★★ `isSelfAdjoint_freeSymbolOp` — **it is self-adjoint**: the first unbounded self-adjoint
  operator of the continuum in this corpus (the circle's twisted Laplacian,
  [`../Fourier/CircleSobolev.lean`](../Fourier/CircleSobolev.lean), is the discrete-spectrum case);
* ★★★ `spectrum_freeSymbolOp` — **its spectrum is the nonnegative real axis**, both
  inclusions: `⊆` because the symbol's values are the nonnegative reals and the resolvent exists off
  their closure (★ `range_freeSymbol`, `isClosed_nonnegAxis`), and `⊇` because every ball around a
  nonnegative real has preimage of positive measure (it is a nonempty open set) and finite measure
  (it is bounded, `preimage_ball_subset_Icc`), so ★★ `mem_spectrum_freeSymbolOp` applies. The
  spectrum is **purely continuous in the sense that matters here**: it is an uncountable set reached
  by approximate eigenvectors, not by eigenvectors — no eigenvalue is claimed anywhere;
* `coeFn_phaseGroup_freeSymbol` — the group and the generator are built from **one function**: in
  the momentum representation `U₀(t)` is multiplication by `e^{−itm}` for the same `m`.

## Honest scope

⚠️ **The momentum representation.** `freeSymbolOp` is `−½Δ` *conjugated by the Fourier
transform*. The position-space operator is its Fourier conjugate, and conjugating a `LinearPMap` by a
unitary is **not** built here, so "`−½Δ` is self-adjoint with spectrum `[0, ∞)`" is not stated in
position space. The Fourier transform is a unitary of `L²(ℝ)` (`SchrodingerGroup.fourierL2`), so the
two operators are unitarily equivalent in the ordinary mathematical sense; that equivalence is what
is missing in Lean (MATHLIB-ABSENT(LinearPMap.conjIsometry)).

⚠️ **No `H₀ + V`.** Adding a bounded real potential needs two things this module does not have:
the conjugation above (in momentum space a potential is a convolution, not a multiplier) and the
lemma that a bounded symmetric perturbation of a self-adjoint `LinearPMap` is self-adjoint on the
same domain. Both are recorded in `specs/BACKLOG.md` #64 as what the interacting Wigner equation
still waits on.

⚠️ **No Stone's theorem**, so `U₀(t) = e^{−itH₀}` is not an identity here: the two objects are
built from the same symbol, which is all `coeFn_phaseGroup_freeSymbol` says. One dimension.

References: M. Reed, B. Simon, *Methods of Modern Mathematical Physics* I §VIII.3, II §IX.7;
`MultiplicationOperator.lean`, `SchrodingerGroup.lean`, `CircleSobolev.lean`;
`specs/BACKLOG.md` #64, #93; `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ComplexConjugate ENNReal NNReal LinearPMap

noncomputable section

namespace SchrodingerGroup

/-! ### The range of the free symbol -/

theorem freeSymbol_real (ξ : ℝ) : freeSymbol ξ = 2 * Real.pi ^ 2 * ξ ^ 2 := by
  rw [freeSymbol, Real.norm_eq_abs, sq_abs]

theorem freeSymbol_nonneg (ξ : ℝ) : 0 ≤ freeSymbol ξ := by
  rw [freeSymbol_real]
  positivity

theorem continuous_freeSymbol : Continuous (freeSymbol (E := ℝ)) := by
  have h : (freeSymbol (E := ℝ)) = fun ξ : ℝ => 2 * Real.pi ^ 2 * ξ ^ 2 := funext freeSymbol_real
  rw [h]
  fun_prop

/-- Every nonnegative real is a value of the free symbol: `2π²ξ² = r` at `ξ = √(r/2π²)`. -/
theorem freeSymbol_sqrt {r : ℝ} (hr : 0 ≤ r) :
    freeSymbol (Real.sqrt (r / (2 * Real.pi ^ 2))) = r := by
  have hpos : (0 : ℝ) < 2 * Real.pi ^ 2 := by positivity
  rw [freeSymbol_real, Real.sq_sqrt (by positivity)]
  field_simp

/-- ★ **The free symbol's range is `[0, ∞)`.** -/
theorem range_freeSymbol : Set.range (freeSymbol (E := ℝ)) = Set.Ici (0 : ℝ) := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro r ⟨ξ, rfl⟩
    exact freeSymbol_nonneg ξ
  · intro r hr
    exact ⟨Real.sqrt (r / (2 * Real.pi ^ 2)), freeSymbol_sqrt hr⟩

/-! ### The nonnegative real axis in `ℂ` -/

/-- The nonnegative real axis, as the set the spectrum will turn out to be. -/
def nonnegAxis : Set ℂ := {z : ℂ | z.im = 0 ∧ 0 ≤ z.re}

theorem ofReal_image_Ici : (fun r : ℝ => ((r : ℂ))) '' Set.Ici (0 : ℝ) = nonnegAxis := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro z ⟨r, hr, rfl⟩
    exact ⟨by simp, by simpa using hr⟩
  · rintro z ⟨h1, h2⟩
    refine ⟨z.re, h2, ?_⟩
    rw [Complex.ext_iff]
    exact ⟨rfl, h1.symm⟩

theorem isClosed_nonnegAxis : IsClosed nonnegAxis := by
  have h : nonnegAxis = Complex.im ⁻¹' {0} ∩ Complex.re ⁻¹' Set.Ici (0 : ℝ) := by
    refine Set.eq_of_subset_of_subset ?_ ?_
    · rintro z ⟨h1, h2⟩
      exact ⟨by simpa using h1, h2⟩
    · rintro z ⟨h1, h2⟩
      exact ⟨by simpa using h1, h2⟩
  rw [h]
  exact (isClosed_singleton.preimage Complex.continuous_im).inter
    (isClosed_Ici.preimage Complex.continuous_re)

theorem range_ofReal_freeSymbol :
    Set.range (fun ξ : ℝ => ((freeSymbol ξ : ℝ) : ℂ)) = nonnegAxis := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro z ⟨ξ, rfl⟩
    exact ⟨by simp, by simpa using freeSymbol_nonneg ξ⟩
  · rintro z ⟨h1, h2⟩
    refine ⟨Real.sqrt (z.re / (2 * Real.pi ^ 2)), ?_⟩
    simp only [freeSymbol_sqrt h2]
    simp [Complex.ext_iff, h1]

/-! ### The free Hamiltonian in the momentum representation -/

/-- **The free Hamiltonian in the momentum representation**: multiplication by the free symbol
`2π²ξ²` on `L²(ℝ)`, on its natural domain `{f : (1 + ξ²) f ∈ L²}`. -/
def freeSymbolOp : Lp ℂ 2 (volume : Measure ℝ) →ₗ.[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  MeasureTheory.L2.mulOp (freeSymbol (E := ℝ))

theorem dense_domain_freeSymbolOp :
    Dense ((freeSymbolOp.domain : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) :
      Set (Lp ℂ 2 (volume : Measure ℝ))) :=
  MeasureTheory.L2.dense_mulDomain measurable_freeSymbol

/-- ★★★ **The free Hamiltonian is self-adjoint** on its natural domain: the first unbounded
self-adjoint operator of the continuum in this corpus. -/
theorem isSelfAdjoint_freeSymbolOp : IsSelfAdjoint freeSymbolOp :=
  MeasureTheory.L2.isSelfAdjoint_mulOp measurable_freeSymbol

/-! ### Its spectrum is the nonnegative real axis -/

theorem spectrum_freeSymbolOp_subset :
    LinearPMap.spectrum freeSymbolOp ⊆ nonnegAxis := by
  intro z hz
  by_contra hmem
  refine hz ?_
  refine MeasureTheory.L2.mem_resolventSet_mulOp measurable_freeSymbol ?_
  rw [range_ofReal_freeSymbol, isClosed_nonnegAxis.closure_eq]
  exact hmem

theorem isOpen_preimage_ball (lam ε : ℝ) :
    IsOpen (freeSymbol (E := ℝ) ⁻¹' Metric.ball lam ε) :=
  Metric.isOpen_ball.preimage continuous_freeSymbol

theorem preimage_ball_subset_Icc (lam ε : ℝ) :
    freeSymbol (E := ℝ) ⁻¹' Metric.ball lam ε
      ⊆ Set.Icc (-Real.sqrt ((|lam| + ε) / (2 * Real.pi ^ 2)))
        (Real.sqrt ((|lam| + ε) / (2 * Real.pi ^ 2))) := by
  intro ξ hξ
  rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hξ
  have hpos : (0 : ℝ) < 2 * Real.pi ^ 2 := by positivity
  have h1 : freeSymbol ξ ≤ |lam| + ε := by
    have h2 : freeSymbol ξ - lam ≤ |freeSymbol ξ - lam| := le_abs_self _
    have h3 : lam ≤ |lam| := le_abs_self _
    linarith
  have h4 : ξ ^ 2 ≤ (|lam| + ε) / (2 * Real.pi ^ 2) := by
    rw [le_div_iff₀ hpos, freeSymbol_real] at *
    linarith [h1]
  have h5 : |ξ| ≤ Real.sqrt ((|lam| + ε) / (2 * Real.pi ^ 2)) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h4
  exact abs_le.1 h5

/-- ★★ **Every nonnegative real is in the spectrum**: the preimage of each ball around it is a
nonempty open set, hence of positive measure, and bounded, hence of finite measure — so the
essential-value criterion applies. -/
theorem mem_spectrum_freeSymbolOp {r : ℝ} (hr : 0 ≤ r) :
    ((r : ℂ)) ∈ LinearPMap.spectrum freeSymbolOp := by
  refine MeasureTheory.L2.mem_spectrum_mulOp measurable_freeSymbol (fun ε hε => ?_)
    (fun ε hε => ?_)
  · refine ne_of_gt (IsOpen.measure_pos volume (isOpen_preimage_ball r ε) ?_)
    refine ⟨Real.sqrt (r / (2 * Real.pi ^ 2)), ?_⟩
    rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq, freeSymbol_sqrt hr, sub_self, abs_zero]
    exact hε
  · refine ne_top_of_le_ne_top ?_ (measure_mono (preimage_ball_subset_Icc r ε))
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

/-- ★★★ **The spectrum of the free Hamiltonian is the nonnegative real axis** `[0, ∞)`: the
continuum spectrum of `−½Δ`, with no eigenvalues anywhere in it. -/
theorem spectrum_freeSymbolOp : LinearPMap.spectrum freeSymbolOp = nonnegAxis := by
  refine Set.eq_of_subset_of_subset spectrum_freeSymbolOp_subset ?_
  intro z hz
  rw [← ofReal_image_Ici] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  exact mem_spectrum_freeSymbolOp hr

/-! ### The link with the propagator -/

/-- The free group, in the momentum representation, is multiplication by `e^{−it m}` for the same
symbol `m` whose multiplication operator is the free Hamiltonian: the group and the generator are
built from one function. Turning this into `U₀(t) = e^{−itH₀}` as operators is Stone's theorem,
which the pin does not have. -/
theorem coeFn_phaseGroup_freeSymbol (t : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    phaseGroup (measurable_freeSymbol (E := ℝ)) t f
      =ᵐ[volume] fun ξ => Complex.exp ((-(t * freeSymbol ξ) : ℝ) * Complex.I) * f ξ :=
  coeFn_phaseGroup _ t f

end SchrodingerGroup

end

end
