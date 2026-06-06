import CsdLean4.Mathlib.QuantumInfo.Hadamard

/-!
# Deutsch–Jozsa (R4)

**Category:** 3-Local (QM-validity).

The Deutsch–Jozsa algorithm (phase R4 of `specs/nqubit-register-plan.md`): one query to an
oracle for `f : {0,1}ⁿ → {0,1}` decides whether `f` is **constant** or **balanced**. The
circuit is `H^⊗n ∘ U_f ∘ H^⊗n` on `|0ⁿ⟩`, with `U_f` the phase oracle `|x⟩ ↦ (-1)^{f(x)}|x⟩`.

The amplitude of the all-zeros outcome after the circuit is `(1/2ⁿ) ∑ₓ (-1)^{f(x)}`
(`djAmplitude_zero`), so the Born probability of measuring `|0ⁿ⟩` is:

* `1` if `f` is **constant** (`deutsch_jozsa_constant`) — the amplitude is `±1`;
* `0` if `f` is **balanced** (`deutsch_jozsa_balanced`) — the amplitude is `0`.

One measurement therefore discriminates the two cases with certainty.

**Honest scope.** This is the discrimination statement, which needs only `Hn_apply_zero`
(R2) and the diagonal oracle — *not* `Hn` unitarity. Unitarity (R3, character orthogonality)
is what makes the *full* output distribution a normalised probability vector; the
`prob(0ⁿ) = 1 vs 0` discrimination here is self-contained as a squared-amplitude computation.
-/

open scoped ComplexConjugate
open QuantumInfo

namespace CSD
namespace Empirical
namespace QM
namespace DeutschJozsa

variable {n : ℕ}

/-- `(-1)^{a}` for a bit `a : Fin 2`, as a complex sign. -/
lemma neg_one_pow_fin (a : Fin 2) : (-1 : ℂ) ^ a.val = if a = 0 then 1 else -1 := by
  fin_cases a <;> simp

/-- `(√2⁻¹)² = 2⁻¹`. -/
lemma inv_sqrt2_sq : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (2 : ℂ)⁻¹ := by
  rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- `(√2⁻¹)ⁿ · (√2⁻¹)ⁿ = (2ⁿ)⁻¹`. -/
lemma inv_sqrt2_pow_mul (n : ℕ) :
    ((Real.sqrt 2 : ℂ)⁻¹) ^ n * ((Real.sqrt 2 : ℂ)⁻¹) ^ n = ((2 : ℂ) ^ n)⁻¹ := by
  rw [← mul_pow, ← sq, inv_sqrt2_sq, inv_pow]

/-- The **phase oracle** `U_f : |x⟩ ↦ (-1)^{f(x)} |x⟩` for `f : {0,1}ⁿ → {0,1}`. -/
noncomputable def phaseOracle (f : (Fin n → Fin 2) → Fin 2) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  Matrix.diagonal (fun x => (-1) ^ (f x).val)

/-- The phase oracle's action on a register state. -/
noncomputable def applyUf (f : (Fin n → Fin 2) → Fin 2) (ψ : QReg n) : QReg n :=
  Matrix.toEuclideanLin (phaseOracle f) ψ

lemma applyUf_apply (f : (Fin n → Fin 2) → Fin 2) (ψ : QReg n) (y : Fin n → Fin 2) :
    applyUf f ψ y = (-1) ^ (f y).val * ψ y := by
  rw [applyUf, Matrix.toLpLin_apply]
  simp [phaseOracle, Matrix.mulVec_diagonal]

/-- `Hn 0ⁿ y = (√2⁻¹)ⁿ` (the all-zeros row of the Hadamard transform). -/
lemma Hn_zero_apply (y : Fin n → Fin 2) :
    Hn (0 : Fin n → Fin 2) y = ((Real.sqrt 2 : ℂ)⁻¹) ^ n := by
  rw [Hn_apply, show (fun i => hadEntry ((0 : Fin n → Fin 2) i) (y i))
      = fun _ => (Real.sqrt 2 : ℂ)⁻¹ from funext fun i => by
    simp [hadEntry]]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The **Deutsch–Jozsa circuit** `H^⊗n ∘ U_f ∘ H^⊗n`. -/
noncomputable def djCircuit (f : (Fin n → Fin 2) → Fin 2) (ψ : QReg n) : QReg n :=
  applyHn (applyUf f (applyHn ψ))

/-- **The all-zeros amplitude after the circuit** is `(1/2ⁿ) ∑ₓ (-1)^{f(x)}`. -/
theorem djAmplitude_zero (f : (Fin n → Fin 2) → Fin 2) :
    djCircuit f (basisState 0) (0 : Fin n → Fin 2)
      = ((2 : ℂ) ^ n)⁻¹ * ∑ x, (-1) ^ (f x).val := by
  rw [djCircuit, applyHn_apply]
  have hterm : ∀ y : Fin n → Fin 2,
      Hn (0 : Fin n → Fin 2) y * applyUf f (applyHn (basisState 0)) y
        = ((2 : ℂ) ^ n)⁻¹ * (-1) ^ (f y).val := by
    intro y
    rw [Hn_zero_apply, applyUf_apply, Hn_apply_zero]
    rw [show ((Real.sqrt 2 : ℂ)⁻¹) ^ n * ((-1) ^ (f y).val * ((Real.sqrt 2 : ℂ)⁻¹) ^ n)
          = (((Real.sqrt 2 : ℂ)⁻¹) ^ n * ((Real.sqrt 2 : ℂ)⁻¹) ^ n) * (-1) ^ (f y).val from by
      ring]
    rw [inv_sqrt2_pow_mul]
  simp_rw [hterm]
  rw [← Finset.mul_sum]

/-- A function `f : {0,1}ⁿ → {0,1}` is **balanced** if it is `0` on exactly half its inputs. -/
def Balanced (f : (Fin n → Fin 2) → Fin 2) : Prop :=
  (Finset.univ.filter (fun x => f x = 0)).card = (Finset.univ.filter (fun x => f x = 1)).card

/-- For a balanced `f`, the signed sum vanishes: `∑ₓ (-1)^{f(x)} = 0`. -/
lemma Balanced.signSum_eq_zero {f : (Fin n → Fin 2) → Fin 2} (hf : Balanced f) :
    ∑ x, (-1 : ℂ) ^ (f x).val = 0 := by
  simp_rw [fun x => neg_one_pow_fin (f x)]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one]
  have hcompl : (Finset.univ.filter (fun x : Fin n → Fin 2 => ¬ f x = 0))
      = Finset.univ.filter (fun x => f x = 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [hcompl, hf]
  ring

/-- **Deutsch–Jozsa, balanced case:** if `f` is balanced, the probability of measuring
`|0ⁿ⟩` is `0`. -/
theorem deutsch_jozsa_balanced {f : (Fin n → Fin 2) → Fin 2} (hf : Balanced f) :
    prob (djCircuit f (basisState 0)) (0 : Fin n → Fin 2) = 0 := by
  rw [prob, djAmplitude_zero, hf.signSum_eq_zero, mul_zero, norm_zero]
  norm_num

/-- **Deutsch–Jozsa, constant case:** if `f` is constant, the probability of measuring
`|0ⁿ⟩` is `1` — the algorithm reports "constant" with certainty. -/
theorem deutsch_jozsa_constant {f : (Fin n → Fin 2) → Fin 2} {c : Fin 2} (hf : ∀ x, f x = c) :
    prob (djCircuit f (basisState 0)) (0 : Fin n → Fin 2) = 1 := by
  rw [prob, djAmplitude_zero]
  have hsum : (∑ x, (-1 : ℂ) ^ (f x).val) = (2 : ℂ) ^ n * (-1) ^ c.val := by
    simp_rw [hf, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [hsum, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n two_ne_zero), one_mul, norm_pow]
  simp