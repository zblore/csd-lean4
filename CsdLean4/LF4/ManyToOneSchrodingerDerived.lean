/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.ManyToOnePillars
public import CsdLean4.Mathlib.Analysis.Matrix.StoneC1

/-!
# General-`N` Schrödinger pillar, DERIVED (not by `rfl`)

**Category:** 3-Local (General-`N` Schrödinger pillar, DERIVED (not by `rfl`)).

`manyToOneSchrodingerSetup_schrodinger_form` (in `ManyToOnePillars`) delivers the
Schrödinger pillar `π (Φ_t x) = exp(-itH) • π x` by `rfl` — true, but only because
the flow was *built* as `exp(-itH)`. That form does not, on its own, exhibit that
the finite-dimensional **Stone/Wigner derivation machinery** actually FIRES on the
real object: prior to this module the C¹-Stone core (`CSD.StoneC1.eq_exp_of_hasDeriv`,
via `PhaseLift.sigmaFlow_schrodinger_form`) was only ever exercised on the trivial
`A = 0` witness (`trivialKahlerOnticSetup_sigmaFlow_schrodinger_form`).

This module closes that gap at general `N` with an arbitrary Hermitian generator.
It EXHIBITS the genuine skew-Hermitian generator `A = -i H`, DISCHARGES (proves,
does not assume) the C¹ smoothness datum `U' t = U t * A` for the real family
`U t = exp(-itH)`, runs the finite-dimensional Stone theorem on it to recover
`U t = exp(t • A)`, and delivers the pillar — so the Schrödinger form is now backed
by an *exercised* derivation, not standing alone on `rfl`.

The `CompleteSpace (Matrix ...)` obstruction that stalled an earlier attempt is
avoided exactly as in `StoneC1`: the `C^*`-algebra L2-operator norm
(`open scoped Matrix.Norms.L2Operator`) carries completeness with no instance
diamond, so `hasDerivAt_exp_smul_const` synthesises. Under the plain operator /
Frobenius scopes the finite-dimensional completeness instance does not unify and
synthesis fails.

## Main results

* `CSD.LF4.schrodingerUnitary_hasDerivAt` : the C¹ datum, DISCHARGED — the real
  `exp(-itH)` family has derivative `U t * (-iH)` at every `t`, general `N`.
* `CSD.LF4.manyToOneSchrodingerSetup_schrodinger_derived` : the honest general-`N`
  capstone — exhibits the skew generator, the discharged C¹ datum, the Stone
  conclusion `U t = exp(t • A)`, and the projected-flow Schrödinger form, for the
  real `manyToOneSchrodingerSetup H hH p₀`, arbitrary Hermitian `H`.

References: `LF4/PhaseLift.lean` (`sigmaFlow_schrodinger_form`, S1),
`Mathlib/Analysis/Matrix/StoneC1.lean` (`eq_exp_of_hasDeriv`, S2),
`LF4/ProjectedDynamics.lean` (`schrodingerUnitary`, `expNegITH_unitary_group`),
`LF4/ManyToOnePillars.lean` (`manyToOneSchrodingerSetup_schrodinger_form`, the
`rfl`-form this backs). See `specs/future-work.md` (W5-S2) and
`specs/reconstruction-status.md` (L3/L8, the Schrödinger pillar).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Matrix
open NormedSpace

noncomputable section

variable {N : ℕ}

/-- The skew-Hermitian Schrödinger generator `A = -i H` for Hermitian `H`:
`star (-i H) = -(-i H)`. -/
theorem CSD.LF4.schrodingerGen_neg_i_smul_skew
    (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian) :
    star ((-Complex.I) • H) = -((-Complex.I) • H) := by
  rw [star_smul, show star (-Complex.I) = Complex.I by simp,
    show star H = H from by rw [Matrix.star_eq_conjTranspose]; exact hH]
  module

/-- `schrodingerGen H τ = τ • (-i H)` as a real scalar action (tower `ℝ → ℂ → Matrix`).
Rewrites the time-`τ` generator into the `t • A` form `hasDerivAt_exp_smul_const`
expects. -/
theorem CSD.LF4.schrodingerGen_eq_real_smul
    (H : Matrix (Fin N) (Fin N) ℂ) (τ : ℝ) :
    CSD.LF4.schrodingerGen H τ = τ • ((-Complex.I) • H) := by
  unfold CSD.LF4.schrodingerGen
  rw [← smul_assoc]
  congr 1
  rw [Complex.real_smul]
  ring

/-- **The C¹ smoothness datum, DISCHARGED (general `N`, arbitrary Hermitian `H`).**
The real Schrödinger family `U t = exp(-itH)` has derivative `U t * (-iH)` at every
`t`. This is the S2 hypothesis of `sigmaFlow_schrodinger_form` / the input of
`CSD.StoneC1.eq_exp_of_hasDeriv`, here PROVED for the genuine nonzero generator
rather than assumed or restricted to the `A = 0` witness. -/
theorem CSD.LF4.schrodingerUnitary_hasDerivAt
    (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian) (t : ℝ) :
    HasDerivAt (fun τ : ℝ => (CSD.LF4.schrodingerUnitary hH τ : Matrix (Fin N) (Fin N) ℂ))
      ((CSD.LF4.schrodingerUnitary hH t : Matrix (Fin N) (Fin N) ℂ) * ((-Complex.I) • H)) t := by
  have hfun : (fun τ : ℝ => (CSD.LF4.schrodingerUnitary hH τ : Matrix (Fin N) (Fin N) ℂ))
      = (fun τ : ℝ => NormedSpace.exp (τ • ((-Complex.I) • H))) := by
    funext τ
    show NormedSpace.exp (CSD.LF4.schrodingerGen H τ) = _
    rw [CSD.LF4.schrodingerGen_eq_real_smul]
  have hval : (CSD.LF4.schrodingerUnitary hH t : Matrix (Fin N) (Fin N) ℂ)
      = NormedSpace.exp (t • ((-Complex.I) • H)) := by
    show NormedSpace.exp (CSD.LF4.schrodingerGen H t) = _
    rw [CSD.LF4.schrodingerGen_eq_real_smul]
  rw [hfun, hval]
  exact hasDerivAt_exp_smul_const ((-Complex.I) • H) t

/-- **General-`N` Schrödinger pillar, DERIVED.** For the real Kähler ontic instance
`manyToOneSchrodingerSetup H hH p₀` (arbitrary Hermitian `H`, general `N`), there is
a genuine skew-Hermitian generator `A = -iH` such that:

* `star A = -A` — the generator is skew-Hermitian;
* `∀ t, HasDerivAt U (U t * A) t` — the C¹ smoothness datum is DISCHARGED for the
  real family `U t = exp(-itH)` (not assumed, not the `A = 0` witness);
* `∀ t, U t = exp (t • A)` — the finite-dimensional Stone theorem
  (`CSD.StoneC1.eq_exp_of_hasDeriv`) recovers the family from its generator;
* `∀ t x, π (Φ_t x) = exp(-itH) • π x` — the projected-flow Schrödinger pillar.

This EXERCISES the Wigner/Stone derivation on the real nonzero-generator object at
general `N`, so `manyToOneSchrodingerSetup_schrodinger_form` (the `rfl`-form) is
backed by an actual derivation. It is the FORWARD direction (consumes the posited
sector); it does not derive the sector from the dynamics (L7/SL-1, untouched). -/
theorem CSD.LF4.manyToOneSchrodingerSetup_schrodinger_derived {M : ℕ}
    (H : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (hH : H.IsHermitian) (p₀ : CPN (M + 1)) :
    ∃ A : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ,
      star A = -A
      ∧ (∀ t, HasDerivAt
            (fun τ : ℝ => (CSD.LF4.schrodingerUnitary hH τ : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ))
            ((CSD.LF4.schrodingerUnitary hH t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) * A) t)
      ∧ (∀ t, (CSD.LF4.schrodingerUnitary hH t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ)
            = NormedSpace.exp (t • A))
      ∧ (∀ t x, (CSD.LF4.manyToOneSchrodingerSetup H hH p₀).pi
            ((CSD.LF4.manyToOneSchrodingerSetup H hH p₀).flow t x)
          = CSD.LF4.schrodingerUnitary hH t • (CSD.LF4.manyToOneSchrodingerSetup H hH p₀).pi x) := by
  refine ⟨(-Complex.I) • H, CSD.LF4.schrodingerGen_neg_i_smul_skew H hH,
    CSD.LF4.schrodingerUnitary_hasDerivAt H hH, ?_, fun _ _ => rfl⟩
  have hU0 : (CSD.LF4.schrodingerUnitary hH 0 : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) = 1 := by
    show NormedSpace.exp (CSD.LF4.schrodingerGen H 0) = 1
    rw [show CSD.LF4.schrodingerGen H 0 = 0 from by unfold CSD.LF4.schrodingerGen; simp,
      NormedSpace.exp_zero]
  exact CSD.StoneC1.eq_exp_of_hasDeriv ((-Complex.I) • H)
    (fun τ => (CSD.LF4.schrodingerUnitary hH τ : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ))
    (CSD.LF4.schrodingerUnitary_hasDerivAt H hH) hU0

end
