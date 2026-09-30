/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The Aharonov–Bohm effect on the circle

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #90, the continuum residue of #55.

`QuantumInfo/AharonovBohmRing.lean` is the lattice version: `N` sites, levels `2 cos((2πm + Φ)/N)`,
and the flux visible modulo a quantum and up to sign. This is the textbook continuum version on the
circle `ℝ/2πℤ`, where the twisted Hamiltonian `(−i∂ − Φ)² = −(∂ − iΦ)²` has the Fourier modes
`ψ_n(x) = e^{inx}` as its eigenfunctions with levels `(n − Φ)²`, the flux quantum is `1`, and the
same two operations are invisible.

* `circleMode n` — the Fourier mode, with ★ `circleMode_eq_fourier` identifying it with Mathlib's
  `fourier n` on `AddCircle (2π)` and `circleMode_periodic` its periodicity;
* ★★ `twisted_deriv_circleMode` — `(∂ − iΦ)ψ_n = i(n − Φ)ψ_n`, and ★★★ `twisted_eigen` —
  **`−(∂ − iΦ)²ψ_n = (n − Φ)²ψ_n`**, the eigenvalue equation written out;
* `circleEigval Φ n = (n − Φ)²`; ★★ `isLeast_range_circleEigval` — **the ground level is the squared
  distance from the flux to the nearest quantum**, attained at the mode `round Φ`;
* ★★ `range_circleEigval_add_one` and ★★ `range_circleEigval_neg` — one whole quantum, and reversing
  the flux, permute the levels;
* ★★★ `exists_eq_of_range_circleEigval_eq` — **and those are the only two**: two fluxes with the
  same level set differ by a whole quantum or are reflections of one another;
* ★★ `gauge_periodic_iff` — **the gauge that removes the flux lives on the circle only when the flux
  is a whole quantum**, which is the continuum form of "the vector potential is not observable but
  the flux is".

## Honest scope

⚠️ **No unbounded-operator theory.** `−(∂ − iΦ)²` is written out as iterated derivatives of a
specific smooth function, not as a self-adjoint operator on `L²(S¹)` with a domain. The pin has the
skeleton — `LinearPMap`, its adjoint, `IsSelfAdjoint` — and nothing built on it: Mathlib has no
diagonal multiplication operator on a Hilbert basis and no spectrum of one
(MATHLIB-ABSENT(LinearPMap.diagonal, LinearPMap.spectrum)), and no unbounded spectral theory to put
them in (MATHLIB-ABSENT(file:Mathlib/Analysis/InnerProductSpace/UnboundedSpectrum)). So "spectrum"
here means the set of eigenvalues *of the Fourier modes*, `Set.range (circleEigval Φ)`, and every
theorem below is about that set.

⚠️ The missing layer is **half built** as of 2026-09-30:
`Mathlib/Analysis/InnerProductSpace/DiagonalOperator.lean` (`BACKLOG.md` #93(a)) has the diagonal
operator of a real weight family on a Hilbert basis, proves it self-adjoint
(`HilbertBasis.isSelfAdjoint_diagOp`) and computes its spectrum as the closure of the weight set
(`HilbertBasis.spectrum_diagOp`). What still separates this module from that one is the Fourier side,
not the operator side: `H²(S¹)` as a domain and the identity `fourierCoeff (deriv f) n = i n ·
fourierCoeff f n`, which the pin has in no form (#93(b)). Until that lands, nothing here is a
statement about an operator.
`circleMode_eq_fourier` is the bridge that makes the family Mathlib's own: `fourierBasis` is a
Hilbert basis of `L²(AddCircle 2π)`, so the modes are complete and the twist does not change them —
only their levels — but the step from that to "these are all the spectral values of a self-adjoint
operator" is not taken here.

⚠️ The flux quantum is `1` in this parametrisation, where the ring module's is `2π`; the levels are
`(n − Φ)²` rather than `2 cos((2πm + Φ)/N)`, and the ground level rather than the top level is what
reads the flux. The two statements are analogues, not instances of one another.

⚠️ No solenoid and no double slit here either: the flux enters as the twist in the derivative, which
is the minimal-coupling substitution taken as the definition of the model.

References: Y. Aharonov, D. Bohm, Phys. Rev. 115 (1959) 485; the lattice twin in
`QuantumInfo/AharonovBohmRing.lean` and its empirical reading in `Empirical/QM/AharonovBohm.lean`;
`specs/berry-phase-scoping.md` BP-4; `specs/BACKLOG.md` #90.
-/

@[expose] public section

open Real Complex
open scoped Real

namespace QuantumInfo

namespace AharonovBohmCircle

/-! ### The Fourier modes of the circle -/

/-- The Fourier mode `ψ_n(x) = e^{inx}`, a function on `ℝ` of period `2π`. -/
noncomputable def circleMode (n : ℤ) (x : ℝ) : ℂ := Complex.exp ((n : ℂ) * (x : ℂ) * Complex.I)

/-- ★ The modes are Mathlib's Fourier family on `AddCircle (2π)`, so `fourierBasis` applies to
them: they are a Hilbert basis of `L²` and the twist below does not change them. -/
theorem circleMode_eq_fourier (n : ℤ) (x : ℝ) :
    (fourier n ((x : ℝ) : AddCircle (2 * π)) : ℂ) = circleMode n x := by
  rw [fourier_coe_apply, circleMode]
  congr 1
  have hπ : (π : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  field_simp
  push_cast
  ring

/-- The modes have period `2π`. -/
theorem circleMode_periodic (n : ℤ) (x : ℝ) : circleMode n (x + 2 * π) = circleMode n x := by
  rw [circleMode, circleMode]
  rw [show ((n : ℂ) * ((x + 2 * π : ℝ) : ℂ) * Complex.I)
      = (n : ℂ) * (x : ℂ) * Complex.I + (n : ℂ) * (2 * π * Complex.I) from by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem circleMode_ne_zero (n : ℤ) (x : ℝ) : circleMode n x ≠ 0 := Complex.exp_ne_zero _

/-- The derivative of a mode: `ψ_n' = i n ψ_n`. -/
theorem hasDerivAt_circleMode (n : ℤ) (x : ℝ) :
    HasDerivAt (circleMode n) (Complex.I * n * circleMode n x) x := by
  show HasDerivAt (fun y : ℝ => Complex.exp ((n : ℂ) * (y : ℂ) * Complex.I))
      (Complex.I * n * Complex.exp ((n : ℂ) * (x : ℂ) * Complex.I)) x
  have h : HasDerivAt (fun y : ℝ => (n : ℂ) * (y : ℂ) * Complex.I) ((n : ℂ) * Complex.I) x := by
    simpa using (((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (n : ℂ)).mul_const Complex.I)
  exact h.cexp.congr_deriv (by ring)

theorem deriv_circleMode (n : ℤ) (x : ℝ) :
    deriv (circleMode n) x = Complex.I * n * circleMode n x :=
  (hasDerivAt_circleMode n x).deriv

/-! ### The twisted derivative and the levels -/

/-- The level of the mode `n` at flux `Φ`. -/
noncomputable def circleEigval (Φ : ℝ) (n : ℤ) : ℝ := ((n : ℝ) - Φ) ^ 2

/-- ★★ **The twisted derivative of a mode**: `(∂ − iΦ)ψ_n = i(n − Φ)ψ_n`. The twist shifts the
label by the flux, which is the whole of the Aharonov–Bohm effect in one line. -/
theorem twisted_deriv_circleMode (Φ : ℝ) (n : ℤ) (x : ℝ) :
    deriv (circleMode n) x - Complex.I * (Φ : ℂ) * circleMode n x
      = Complex.I * (((n : ℝ) - Φ : ℝ) : ℂ) * circleMode n x := by
  rw [deriv_circleMode]
  push_cast
  ring

/-- The twisted derivative of a mode is a constant multiple of it, so it can be differentiated
again. -/
theorem hasDerivAt_twisted_circleMode (Φ : ℝ) (n : ℤ) (x : ℝ) :
    HasDerivAt (fun y => deriv (circleMode n) y - Complex.I * (Φ : ℂ) * circleMode n y)
      (Complex.I * (((n : ℝ) - Φ : ℝ) : ℂ) * (Complex.I * n * circleMode n x)) x := by
  have h : HasDerivAt (fun y => Complex.I * (((n : ℝ) - Φ : ℝ) : ℂ) * circleMode n y)
      (Complex.I * (((n : ℝ) - Φ : ℝ) : ℂ) * (Complex.I * n * circleMode n x)) x :=
    (hasDerivAt_circleMode n x).const_mul _
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with y
  exact twisted_deriv_circleMode Φ n y

/-- ★★★ **The eigenvalue equation**: `−(∂ − iΦ)²ψ_n = (n − Φ)²ψ_n`. The flux shifts every level by
shifting the label it is measured from, and no level is left where it was unless the shift is a
whole quantum. -/
theorem twisted_eigen (Φ : ℝ) (n : ℤ) (x : ℝ) :
    -(deriv (fun y => deriv (circleMode n) y - Complex.I * (Φ : ℂ) * circleMode n y) x
        - Complex.I * (Φ : ℂ)
          * (deriv (circleMode n) x - Complex.I * (Φ : ℂ) * circleMode n x))
      = ((circleEigval Φ n : ℝ) : ℂ) * circleMode n x := by
  rw [(hasDerivAt_twisted_circleMode Φ n x).deriv, twisted_deriv_circleMode, circleEigval]
  push_cast
  linear_combination (-(((n : ℂ) - (Φ : ℂ)) ^ 2 * circleMode n x)) * Complex.I_sq

/-! ### The flux is determined by the levels -/

/-- ★ No mode sits lower: the ground level is the squared distance from the flux to the nearest
whole quantum. -/
theorem sq_sub_round_le_circleEigval (Φ : ℝ) (n : ℤ) :
    (Φ - round Φ) ^ 2 ≤ circleEigval Φ n := by
  have h : |Φ - (round Φ : ℝ)| ≤ |Φ - (n : ℝ)| := round_le Φ n
  have h2 := mul_self_le_mul_self (abs_nonneg (Φ - (round Φ : ℝ))) h
  rw [abs_mul_abs_self, abs_mul_abs_self] at h2
  rw [circleEigval]
  nlinarith [h2]

/-- The ground level is attained, at the mode nearest the flux. -/
theorem circleEigval_round (Φ : ℝ) : circleEigval Φ (round Φ) = (Φ - round Φ) ^ 2 := by
  rw [circleEigval]
  ring

/-- ★★ **The ground level reads the flux**: it is the squared distance from the flux to the nearest
whole quantum, attained at the mode nearest it. -/
theorem isLeast_range_circleEigval (Φ : ℝ) :
    IsLeast (Set.range (circleEigval Φ)) ((Φ - round Φ) ^ 2) := by
  refine ⟨⟨round Φ, circleEigval_round Φ⟩, ?_⟩
  rintro y ⟨n, rfl⟩
  exact sq_sub_round_le_circleEigval Φ n

/-- ★★ **One whole quantum changes nothing**: adding `1` to the flux permutes the levels. -/
theorem range_circleEigval_add_one (Φ : ℝ) :
    Set.range (circleEigval (Φ + 1)) = Set.range (circleEigval Φ) := by
  have key : ∀ (Ψ : ℝ) (n : ℤ), circleEigval (Ψ + 1) n = circleEigval Ψ (n - 1) := by
    intro Ψ n
    rw [circleEigval, circleEigval]
    push_cast
    ring
  ext y
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n - 1, (key Φ n).symm⟩
  · rintro ⟨n, rfl⟩
    refine ⟨n + 1, ?_⟩
    rw [key]
    congr 1
    ring

/-- ★★ **The levels cannot see the sign of the flux**, so the ambiguity below is real. -/
theorem range_circleEigval_neg (Φ : ℝ) :
    Set.range (circleEigval (-Φ)) = Set.range (circleEigval Φ) := by
  have key : ∀ (Ψ : ℝ) (n : ℤ), circleEigval (-Ψ) n = circleEigval Ψ (-n) := by
    intro Ψ n
    rw [circleEigval, circleEigval]
    push_cast
    ring
  ext y
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨-n, (key Φ n).symm⟩
  · rintro ⟨n, rfl⟩
    refine ⟨-n, ?_⟩
    rw [key, neg_neg]

/-- ★★★ **The flux is determined by the levels**, exactly as far as it can be: two fluxes with the
same level set differ by a whole quantum, or are reflections of one another in one. With
`range_circleEigval_add_one` and `range_circleEigval_neg` the converse holds too, so this is the
continuum twin of the ring's `exists_eq_of_range_ringEigval_eq`. -/
theorem exists_eq_of_range_circleEigval_eq {Φ Φ' : ℝ}
    (h : Set.range (circleEigval Φ) = Set.range (circleEigval Φ')) :
    ∃ k : ℤ, Φ' = Φ + k ∨ Φ' = -Φ + k := by
  have hg := isLeast_range_circleEigval Φ
  have hg' := isLeast_range_circleEigval Φ'
  rw [h] at hg
  have hsq : (Φ - round Φ) ^ 2 = (Φ' - round Φ') ^ 2 :=
    le_antisymm (hg.2 hg'.1) (hg'.2 hg.1)
  have hfac : (Φ - (round Φ : ℝ) - (Φ' - (round Φ' : ℝ)))
      * (Φ - (round Φ : ℝ) + (Φ' - (round Φ' : ℝ))) = 0 := by nlinarith [hsq]
  rcases mul_eq_zero.mp hfac with heq | heq
  · exact ⟨round Φ' - round Φ, Or.inl (by push_cast; linarith)⟩
  · exact ⟨round Φ + round Φ', Or.inr (by push_cast; linarith)⟩

/-! ### The gauge that removes the flux -/

/-- The gauge factor `e^{iΦx}` that turns the twisted derivative into the plain one. -/
noncomputable def gaugeMode (Φ : ℝ) (x : ℝ) : ℂ := Complex.exp ((Φ : ℂ) * (x : ℂ) * Complex.I)

/-- ★★ **The vector potential is removable, the flux is not.** The gauge factor that undoes the
twist is a function on the circle exactly when the flux is a whole quantum; for any other flux it is
multivalued, which is why the levels move. -/
theorem gauge_periodic_iff (Φ : ℝ) :
    (∀ x : ℝ, gaugeMode Φ (x + 2 * π) = gaugeMode Φ x) ↔ ∃ k : ℤ, Φ = k := by
  constructor
  · intro h
    have h0 := h 0
    rw [gaugeMode, gaugeMode, zero_add] at h0
    have he : Complex.exp ((Φ : ℂ) * ((2 * π : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [h0]
      norm_num
    rcases Complex.exp_eq_one_iff.mp he with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hne : (2 * (π : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    have hcast : (Φ : ℂ) * (2 * (π : ℂ) * Complex.I)
        = (k : ℂ) * (2 * (π : ℂ) * Complex.I) := by
      push_cast at hk ⊢
      linear_combination hk
    exact_mod_cast mul_right_cancel₀ hne hcast
  · rintro ⟨k, rfl⟩ x
    rw [gaugeMode, gaugeMode,
      show ((k : ℝ) : ℂ) * ((x + 2 * π : ℝ) : ℂ) * Complex.I
          = ((k : ℝ) : ℂ) * (x : ℂ) * Complex.I + (k : ℂ) * (2 * π * Complex.I) from by
        push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end AharonovBohmCircle

end QuantumInfo

end
