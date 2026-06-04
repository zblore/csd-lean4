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
`ψ₂^⊥ = −σ|0⟩ + s|1⟩`. (The third, inconclusive, effect `E? = I − E₁ − E₂` completes
the POVM; its positivity is the completeness constraint, satisfied at `a = 1/(1+s)`.)

## What this file proves

- **Unambiguity** (the defining no-error property): `⟨ψ₂, E₁ ψ₂⟩ = 0` and
  `⟨ψ₁, E₂ ψ₁⟩ = 0` — outcome "1" never fires on state 2 and vice versa, because
  each conclusive effect lives on the orthogonal complement of the *other* state.
- **Success probability**: `⟨ψ₁, E₁ ψ₁⟩ = 1 − s` — the IDP success rate.

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

end USD
end QM
end Empirical
end CSD
