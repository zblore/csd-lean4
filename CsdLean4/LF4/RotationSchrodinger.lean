import CsdLean4.LF4.NonTrivialSetup
import CsdLean4.LF4.PhaseLift
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# C2: the Schrödinger form on the non-trivial rotation flow

Connectivity fix C2 (`specs/connectivity-manifest.md`, link L3): fire the full
W-series Schrödinger capstone `sigmaFlow_schrodinger_form` on the genuine
`Φ ≠ id` instance `rotationSetup` (fix C1), NOT just the trivial `H = 0` witness.

The rotation flow `R(t) = [[cos t, −sin t],[sin t, cos t]]` on `ℂℙ¹` is a genuine
one-parameter unitary GROUP (`R(s+t) = R(s)R(t)`, so the phase cocycle is
trivial: `c = 1`, `b = 1`) with skew-Hermitian generator
`J = [[0,−1],[1,0]]` (`R(τ) = cos τ · I + sin τ · J`, whence `R'(τ) = R(τ)·J`).
The capstone therefore recovers the Hermitian generator `H = iJ = σ_y` (Pauli-Y),
landing

    `rotationSetup.pi (rotationSetup.flow t x) = exp(-it·σ_y) • rotationSetup.pi x`,

i.e. the deterministic rotation flow, projected, IS Schrödinger evolution
`exp(-it H)` for `H = σ_y ≠ 0`. This is the first fully-instantiated,
`H ≠ 0` Schrödinger statement of the corpus — the connectivity gap the audit
flagged (Schrödinger only on the trivial witness) closed for `rotationSetup`.

## Honest scope

This discharges the FS-isometry (via the unitary flow), coboundary (`b = 1`),
and C¹ (`R' = R·J`) data of `sigmaFlow_schrodinger_form` on a concrete non-trivial
flow. It is a witness that the chain fires genuinely, not a derivation of the
sector. Born-side connectivity (manifest L5/L6/L7) is untouched.

## Provenance

Foundational-triple only. Reuses `sigmaFlow_schrodinger_form` (S1×S2 capstone),
`rotationSetup`/`rotU` (C1), and standard trig derivatives; nothing re-proved.
-/

open Matrix
open scoped Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization

namespace CSD
namespace LF4

/-- The generator `J = [[0, −1],[1, 0]]` of the `ℂℙ¹` rotation flow: real
skew-symmetric, so skew-Hermitian. `iJ = σ_y` is the recovered Hamiltonian. -/
def rotGen : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

/-- `J` is skew-Hermitian: `star J = −J`. -/
lemma rotGen_star : star rotGen = -rotGen := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotGen, Matrix.star_apply, Matrix.neg_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Rotation addition: `R(s+t) = R(s) · R(t)`.** So the rotation family is a
genuine one-parameter unitary group and its phase cocycle is trivial. -/
lemma rotMat_add (s t : ℝ) : rotMat (s + t) = rotMat s * rotMat t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [rotMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val', Matrix.empty_val',
      Real.cos_add, Real.sin_add, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    push_cast <;>
    ring

/-- `R(τ) = cos τ · I + sin τ · J` (real scalar multiples). The decomposition
that gives the derivative. -/
lemma rotMat_eq_smul (t : ℝ) :
    rotMat t = Real.cos t • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Real.sin t • rotGen := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotMat, rotGen, Matrix.add_apply, Matrix.smul_apply,
      Matrix.of_apply, Complex.real_smul]

/-- `(−sin t) · I + (cos t) · J = R(t) · J`: the target derivative in matrix form. -/
lemma rotMat_smulDeriv (t : ℝ) :
    (-Real.sin t) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Real.cos t • rotGen
      = rotMat t * rotGen := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotMat, rotGen, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Complex.real_smul]

/-- **The C¹ datum: `R'(τ) = R(τ) · J`.** From `R = cos · I + sin · J` and the
scalar derivatives of `cos`, `sin`, via `HasDerivAt.smul_const`. -/
lemma rotMat_hasDerivAt (t : ℝ) :
    HasDerivAt (fun τ => rotMat τ) (rotMat t * rotGen) t := by
  rw [← rotMat_smulDeriv]
  simp only [rotMat_eq_smul]
  exact ((Real.hasDerivAt_cos t).smul_const _).add ((Real.hasDerivAt_sin t).smul_const _)

/-! ## The capstone on the rotation flow -/

/-- **C2 / connectivity link L3 (off the trivial witness): Schrödinger form on
the rotation flow.** The projected deterministic rotation flow of `rotationSetup`
is `exp(-itH)`-conjugation on rays for the Hermitian generator `H = iJ = σ_y`:

    `rotationSetup.pi (rotationSetup.flow t x) = exp(-it·σ_y) • rotationSetup.pi x`.

This is the W-series Schrödinger capstone fired on a genuine `Φ ≠ id` flow with
`H ≠ 0` — the connectivity gap (Schrödinger only on the identity witness) closed
for `rotationSetup`. -/
theorem rotationSetup_schrodinger_form
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin 2))) :
    ∃ H : Matrix (Fin 2) (Fin 2) ℂ, ∃ hH : H.IsHermitian,
      ∀ t x, (rotationSetup p₀).pi ((rotationSetup p₀).flow t x)
        = schrodingerUnitary hH t • (rotationSetup p₀).pi x := by
  refine sigmaFlow_schrodinger_form (rotationSetup p₀) rotU (fun _ _ => rfl)
    (fun _ _ => 1) ?hc (fun _ => 1) (fun _ => norm_one) (fun _ _ => by ring)
    rotGen rotGen_star ?hderiv
  case hc =>
    intro s t
    show rotMat (s + t) = (1 : ℂ) • (rotMat s * rotMat t)
    rw [one_smul]
    exact rotMat_add s t
  case hderiv =>
    intro t
    have hfun : (fun τ => ((phaseLiftFamily rotU (fun _ => 1)
          (fun _ => norm_one) τ : Matrix.unitaryGroup (Fin 2) ℂ)
          : Matrix (Fin 2) (Fin 2) ℂ))
        = fun τ => rotMat τ := by
      funext τ
      show ((1 : ℂ) • ((rotU τ : Matrix.unitaryGroup (Fin 2) ℂ)
        : Matrix (Fin 2) (Fin 2) ℂ)) = rotMat τ
      rw [one_smul]; rfl
    have hval : ((phaseLiftFamily rotU (fun _ => 1) (fun _ => norm_one) t
          : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * rotGen
        = rotMat t * rotGen := by
      show ((1 : ℂ) • ((rotU t : Matrix.unitaryGroup (Fin 2) ℂ)
        : Matrix (Fin 2) (Fin 2) ℂ)) * rotGen = rotMat t * rotGen
      rw [one_smul]; rfl
    rw [hfun, hval]
    exact rotMat_hasDerivAt t

/-- The recovered generator is non-trivial: `H = iJ = σ_y ≠ 0`, so this is a
genuine (`H ≠ 0`) Schrödinger evolution, not the trivial `exp(0) = 1`. -/
theorem rotationSetup_generator_ne_zero
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin 2))) :
    (Complex.I • rotGen) ≠ 0 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [rotGen, Matrix.smul_apply, Matrix.of_apply] at h01

end LF4
end CSD
