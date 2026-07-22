/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF2.POVM
import CsdLean4.LF2.EffectAux

/-!
# Empirical/QM: unambiguous state discrimination (the IDP POVM)

**Category:** 3-Local. The POVM-essential QM-validity result: distinguishing two
non-orthogonal pure states with **zero error**, at the cost of an inconclusive
outcome — provably impossible with a projective (von Neumann) measurement, the
canonical "why POVMs are needed" example (Ivanovic 1987, Dieks 1988, Peres 1988).

## Setup

Two non-orthogonal states with real overlap `s = ⟨ψ₁, ψ₂⟩ ∈ [0, 1)`:
`ψ₁ = |0⟩`, `ψ₂ = s|0⟩ + σ|1⟩` with `σ = √(1−s²)`. The conclusive effects are
scaled rank-1 projectors onto the *orthogonal complements*:

```
E₁ = a |ψ₂^⊥⟩⟨ψ₂^⊥|   ("conclude state 1"),   E₂ = a |ψ₁^⊥⟩⟨ψ₁^⊥|   ("conclude 2"),
```

with `a = 1/(1+s)` (the optimal Ivanovic–Dieks–Peres coefficient), `ψ₁^⊥ = |1⟩`,
`ψ₂^⊥ = −σ|0⟩ + s|1⟩`. The third, inconclusive, effect is the rank-1 projector
`E? = |χ?⟩⟨χ?| = I − E₁ − E₂` with `χ? = √s|0⟩ + (σ√s/(1+s))|1⟩`; its positivity
(hence the validity of the POVM) is exactly the completeness constraint, satisfied
at `a = 1/(1+s)`.

## What this file proves

- **Unambiguity** (the defining no-error property): `⟨ψ₂, E₁ ψ₂⟩ = 0` and
  `⟨ψ₁, E₂ ψ₁⟩ = 0` — outcome "1" never fires on state 2 and vice versa, because
  each conclusive effect lives on the orthogonal complement of the *other* state.
- **Success probability**: `⟨ψ₁, E₁ ψ₁⟩ = 1 − s` — the IDP success rate.
- **Completeness**: `E₁ + E₂ + |χ?⟩⟨χ?| = I` (`usd_complete`), giving the full
  three-outcome `usdPOVM : POVM 2 (Fin 3)` — a genuine non-projective POVM
  realising zero-error discrimination of the two non-orthogonal states.

The unambiguity is exactly the POVM-essential content: a projective measurement
cannot have an informative outcome that gives identically zero on a non-orthogonal
state while leaving room for a second such outcome.
-/

open Matrix
open scoped ComplexOrder

namespace CSD
namespace Empirical
namespace QM
namespace USD

open CSD.LF2

/-! ### The USD states and conclusive effects -/

variable (s : ℝ)

/-- `σ = √(1 − s²)`. -/
noncomputable def sig : ℝ := Real.sqrt (1 - s ^ 2)

/-- `ψ₁ = |0⟩`. -/
noncomputable def psi1 : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 1

/-- `ψ₂ = s|0⟩ + σ|1⟩` (overlap `⟨ψ₁,ψ₂⟩ = s`). -/
noncomputable def psi2 : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 (s : ℂ) + EuclideanSpace.single 1 ((sig s : ℝ) : ℂ)

/-- `ψ₁^⊥ = |1⟩`. -/
noncomputable def psi1perp : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 1 1

/-- `ψ₂^⊥ = −σ|0⟩ + s|1⟩`. -/
noncomputable def psi2perp : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 ((-sig s : ℝ) : ℂ) + EuclideanSpace.single 1 (s : ℂ)

lemma sig_sq (hs1 : s ≤ 1) (hs0 : -1 ≤ s) : sig s ^ 2 = 1 - s ^ 2 :=
  Real.sq_sqrt (by nlinarith)

/-! ### Component values and inner products -/

private lemma inner_two (x y : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ x y = star (x.ofLp 0) * y.ofLp 0 + star (x.ofLp 1) * y.ofLp 1 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  simp only [Pi.star_apply]; ring

private lemma psi1_ofLp : (psi1).ofLp 0 = 1 ∧ (psi1).ofLp 1 = 0 := by
  constructor <;> simp [psi1, EuclideanSpace.single]

private lemma psi1perp_ofLp : (psi1perp).ofLp 0 = 0 ∧ (psi1perp).ofLp 1 = 1 := by
  constructor <;> simp [psi1perp, EuclideanSpace.single]

private lemma psi2_ofLp : (psi2 s).ofLp 0 = (s : ℂ) ∧ (psi2 s).ofLp 1 = ((sig s : ℝ) : ℂ) := by
  constructor <;> simp [psi2, EuclideanSpace.single]

private lemma psi2perp_ofLp :
    (psi2perp s).ofLp 0 = ((-sig s : ℝ) : ℂ) ∧ (psi2perp s).ofLp 1 = (s : ℂ) := by
  constructor <;> simp [psi2perp, EuclideanSpace.single]

lemma psi1_norm : ‖psi1‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, psi1_ofLp.1, psi1_ofLp.2]
  simp

lemma psi1perp_norm : ‖psi1perp‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, psi1perp_ofLp.1, psi1perp_ofLp.2]
  simp

lemma psi2_norm (hs1 : s ≤ 1) (hs0 : -1 ≤ s) : ‖psi2 s‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, (psi2_ofLp s).1, (psi2_ofLp s).2,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
    sig_sq s hs1 hs0, show s ^ 2 + (1 - s ^ 2) = 1 by ring, Real.sqrt_one]

lemma psi2perp_norm (hs1 : s ≤ 1) (hs0 : -1 ≤ s) : ‖psi2perp s‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, (psi2perp_ofLp s).1, (psi2perp_ofLp s).2,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
    neg_sq, sig_sq s hs1 hs0, show 1 - s ^ 2 + s ^ 2 = 1 by ring, Real.sqrt_one]

/-- `⟨ψ₂, ψ₂^⊥⟩ = 0` — the orthogonality behind the unambiguity of outcome 1. -/
lemma inner_psi2_psi2perp : inner ℂ (psi2 s) (psi2perp s) = 0 := by
  rw [inner_two, (psi2_ofLp s).1, (psi2_ofLp s).2, (psi2perp_ofLp s).1, (psi2perp_ofLp s).2]
  simp only [← starRingEnd_apply, Complex.conj_ofReal]
  push_cast; ring

/-- `⟨ψ₁, ψ₁^⊥⟩ = 0` — orthogonality behind the unambiguity of outcome 2. -/
lemma inner_psi1_psi1perp : inner ℂ psi1 psi1perp = 0 := by
  rw [inner_two, psi1_ofLp.1, psi1_ofLp.2, psi1perp_ofLp.1, psi1perp_ofLp.2]; simp

/-- `⟨ψ₁, ψ₂^⊥⟩ = −σ` — the overlap driving the success probability. -/
lemma inner_psi1_psi2perp : inner ℂ psi1 (psi2perp s) = ((-sig s : ℝ) : ℂ) := by
  rw [inner_two, psi1_ofLp.1, psi1_ofLp.2, (psi2perp_ofLp s).1, (psi2perp_ofLp s).2]; simp

/-! ### The USD effects, unambiguity, and success -/

/-- The optimal IDP coefficient `a = 1/(1+s)`. -/
noncomputable def usdA : ℝ := 1 / (1 + s)

lemma usdA_nonneg (hs0 : 0 ≤ s) : 0 ≤ usdA s := by
  rw [usdA]; positivity

lemma usdA_le_one (hs0 : 0 ≤ s) : usdA s ≤ 1 := by
  rw [usdA, div_le_one (by linarith)]; linarith

/-- `E₁ = a|ψ₂^⊥⟩⟨ψ₂^⊥|` — the "conclude state 1" effect. -/
noncomputable def E1 (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : Effect 2 :=
  scaledRankOneEffect (usdA s) (usdA_nonneg s hs0) (usdA_le_one s hs0)
    (psi2perp s) (psi2perp_norm s hs1 (by linarith))

/-- `E₂ = a|ψ₁^⊥⟩⟨ψ₁^⊥|` — the "conclude state 2" effect. -/
noncomputable def E2 (hs0 : 0 ≤ s) : Effect 2 :=
  scaledRankOneEffect (usdA s) (usdA_nonneg s hs0) (usdA_le_one s hs0) psi1perp psi1perp_norm

/-- **Unambiguity (outcome 1):** `⟨ψ₂, E₁ ψ₂⟩ = 0` — concluding "state 1" never
fires on state 2, because `E₁` lives on the orthogonal complement of `ψ₂`. -/
theorem usd_unambiguous_1 (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    RCLike.re (inner ℂ (psi2 s) (Matrix.toEuclideanLin (E1 s hs0 hs1).M (psi2 s))) = 0 := by
  rw [E1, scaledRankOneEffect_M,
    scaledRankOne_quadratic (usdA s) (psi2perp s) (psi2 s)
      (psi2perp_norm s hs1 (by linarith)) (psi2_norm s hs1 (by linarith)),
    show inner ℂ (psi2 s) (psi2perp s) = 0 from inner_psi2_psi2perp s]
  simp

/-- **Unambiguity (outcome 2):** `⟨ψ₁, E₂ ψ₁⟩ = 0`. -/
theorem usd_unambiguous_2 (hs0 : 0 ≤ s) :
    RCLike.re (inner ℂ psi1 (Matrix.toEuclideanLin (E2 s hs0).M psi1)) = 0 := by
  rw [E2, scaledRankOneEffect_M,
    scaledRankOne_quadratic (usdA s) psi1perp psi1 psi1perp_norm psi1_norm,
    show inner ℂ psi1 psi1perp = 0 from inner_psi1_psi1perp]
  simp

/-- **Success probability:** `⟨ψ₁, E₁ ψ₁⟩ = 1 − s` (the Ivanovic–Dieks–Peres rate). -/
theorem usd_success (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    RCLike.re (inner ℂ psi1 (Matrix.toEuclideanLin (E1 s hs0 hs1).M psi1)) = 1 - s := by
  rw [E1, scaledRankOneEffect_M,
    scaledRankOne_quadratic (usdA s) (psi2perp s) psi1
      (psi2perp_norm s hs1 (by linarith)) psi1_norm,
    show inner ℂ psi1 (psi2perp s) = ((-sig s : ℝ) : ℂ) from inner_psi1_psi2perp s]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, show (-sig s) ^ 2 = sig s ^ 2 by rw [neg_sq],
    sig_sq s hs1 (by linarith), usdA]
  field_simp
  ring

/-! ### The inconclusive effect and the full POVM -/

/-- The inconclusive-outcome vector `χ? = √s|0⟩ + (σ√s/(1+s))|1⟩`, with
`E? = |χ?⟩⟨χ?| = I − E₁ − E₂`. -/
noncomputable def chiInc : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 ((Real.sqrt s : ℝ) : ℂ)
    + EuclideanSpace.single 1 ((sig s * Real.sqrt s / (1 + s) : ℝ) : ℂ)

private lemma chiInc_ofLp :
    (chiInc s).ofLp 0 = ((Real.sqrt s : ℝ) : ℂ)
      ∧ (chiInc s).ofLp 1 = ((sig s * Real.sqrt s / (1 + s) : ℝ) : ℂ) := by
  constructor <;> simp [chiInc, EuclideanSpace.single]

private lemma outer_apply (φ : EuclideanSpace ℂ (Fin 2)) (i j : Fin 2) :
    outerProduct φ i j = φ.ofLp i * star (φ.ofLp j) := rfl

/-- **Completeness:** `E₁ + E₂ + |χ?⟩⟨χ?| = I` at the optimal `a = 1/(1+s)`. The
trine of orthogonal-complement projectors completes to the identity. -/
lemma usd_complete (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (E1 s hs0 hs1).M + (E2 s hs0).M + outerProduct (chiInc s) = 1 := by
  have hsig : (sig s : ℂ) ^ 2 = 1 - (s : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, sig_sq s hs1 (by linarith)]; push_cast; ring
  have hsqrt : ((Real.sqrt s : ℝ) : ℂ) * ((Real.sqrt s : ℝ) : ℂ) = (s : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hs0]
  have h1s : (1 : ℂ) + (s : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add]
    exact_mod_cast ne_of_gt (by linarith : (0 : ℝ) < 1 + s)
  ext i j
  rw [E1, E2, scaledRankOneEffect_M, scaledRankOneEffect_M]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      outer_apply, (psi2perp_ofLp s).1, (psi2perp_ofLp s).2, psi1perp_ofLp.1, psi1perp_ofLp.2,
      (chiInc_ofLp s).1, (chiInc_ofLp s).2, Complex.star_def, Complex.conj_ofReal,
      map_zero, map_one, usdA]
  · rw [Matrix.one_apply_eq]; push_cast; field_simp
    linear_combination (1 + (s : ℂ)) * hsqrt + hsig
  · rw [Matrix.one_apply_ne (by decide)]; push_cast; field_simp
    linear_combination (sig s : ℂ) * hsqrt
  · rw [Matrix.one_apply_ne (by decide)]; push_cast; field_simp
    linear_combination (sig s : ℂ) * hsqrt
  · rw [Matrix.one_apply_eq]; push_cast; field_simp
    linear_combination (sig s : ℂ) ^ 2 * hsqrt + (s : ℂ) * hsig

/-- `E? = |χ?⟩⟨χ?|` as an `Effect` (the inconclusive outcome). PSD as a rank-1
projector; `≤ I` because `I − E? = E₁ + E₂` is a sum of PSD effects. -/
noncomputable def Einc (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : Effect 2 where
  M := outerProduct (chiInc s)
  isHermitian := outerProduct_isHermitian _
  nonneg := outerProduct_posSemidef _
  le_one := by
    rw [show (1 : Matrix (Fin 2) (Fin 2) ℂ) - outerProduct (chiInc s)
        = (E1 s hs0 hs1).M + (E2 s hs0).M from by rw [← usd_complete s hs0 hs1]; abel]
    exact (E1 s hs0 hs1).nonneg.add (E2 s hs0).nonneg

/-- **The USD POVM** `{E₁, E₂, E?}` — the three-outcome unambiguous-discrimination
measurement (two conclusive outcomes + one inconclusive), a genuine non-projective
POVM realising zero-error discrimination of the two non-orthogonal states. -/
noncomputable def usdPOVM (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : POVM 2 (Fin 3) where
  E := ![E1 s hs0 hs1, E2 s hs0, Einc s hs0 hs1]
  complete := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    exact usd_complete s hs0 hs1

end USD
end QM
end Empirical
end CSD
