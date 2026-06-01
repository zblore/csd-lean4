import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import CsdLean4.LF4.MomentMarginalUniform

/-!
# LF4 general-N DH, Slice D (the crux): the ratio map sends `expHalf^{⊗N}` to Dirichlet

The general-`N` analogue of `MomentRatioUniform.lean` (the qubit's
`ratioSqNorm_map_expHalf_prod`, `Beta(1,1)=Uniform[0,1]`): the `N`-fold ratio map
`R_N(s) = (s_0/∑s, …, s_{N-2}/∑s)` pushes `expHalf^{⊗N}` to the Dirichlet(1,…,1)
law, expressed (to dodge the missing Mathlib simplex surface measure) as the
constant `(N−1)!` density on the open simplex in free coordinates `ℝ^{N-1}`.

This file builds the slice incrementally; see `specs/general-n-dh-plan.md` Slice D
for the full DAG (D.1 radial constant → D.3 the determinant `det = S^{N-1}` → D.2
diffeo → D.4 inj/image → D.5 assembly).

**D.1 (this commit): the radial moment constant.** `∫⁻_{S>0} Sⁿ e^{−S/2} = 2^{n+1}·n!`
— the `n`-th moment base (`n = N−1`) that the substituted `S`-integral collapses
to. Generalises `lintegral_radial_const` (N=2: `n=1`, `∫ S e^{−S/2} = 4 = 2²·1!`).
-/

open MeasureTheory Real Set
open scoped ENNReal

namespace CSD
namespace LF4

/-- **D.1 (radial moment, general N).** `∫⁻_{S>0} Sⁿ·e^{−S/2} dS = 2^{n+1}·n!`.
The `n`-th moment of the `Exp(1/2)` shape; with `n = N−1` it is the normalisation
the post-substitution `S`-integral collapses to in the Gamma→Dirichlet change of
variables. Routes through `integral_rpow_mul_exp_neg_mul_Ioi` (`a = n+1`, `r = 1/2`,
giving `2^{n+1}·Γ(n+1)`) + `Real.Gamma_nat_eq_factorial` + the
`ofReal`↔`lintegral` bridge, mirroring `lintegral_radial_const`. -/
theorem lintegral_radial_moment (n : ℕ) :
    ∫⁻ S in Ioi (0 : ℝ), ENNReal.ofReal (S ^ n * Real.exp (-S / 2))
      = ENNReal.ofReal ((2 : ℝ) ^ (n + 1) * (n.factorial : ℝ)) := by
  have hnonneg : ∀ S ∈ Ioi (0 : ℝ), 0 ≤ S ^ n * Real.exp (-S / 2) := by
    intro S hS; simp only [mem_Ioi] at hS; positivity
  -- Bochner value: ∫ Sⁿ e^{−S/2} = 2^{n+1}·n!.
  have hbase : ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-t / 2)
      = (2 : ℝ) ^ (n + 1) * (n.factorial : ℝ) := by
    have h := integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (r := 1 / 2)
      (by positivity) (by norm_num)
    -- RHS: (1/(1/2))^(n+1) · Γ(n+1) = 2^{n+1}·n!.
    have hRHS : ((1 : ℝ) / (1 / 2)) ^ ((n : ℝ) + 1) * Real.Gamma ((n : ℝ) + 1)
        = (2 : ℝ) ^ (n + 1) * (n.factorial : ℝ) := by
      rw [Real.Gamma_nat_eq_factorial,
        show ((1 : ℝ) / (1 / 2)) = 2 by norm_num,
        show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    rw [hRHS] at h
    rw [← h]
    -- Match integrands: t^((n+1)-1) = tⁿ, exp(-(1/2·t)) = exp(-t/2) on Ioi 0.
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    show t ^ n * Real.exp (-t / 2) = t ^ ((n : ℝ) + 1 - 1) * Real.exp (-(1 / 2 * t))
    rw [show ((n : ℝ) + 1 - 1) = (n : ℝ) by ring, Real.rpow_natCast,
      show -(1 / 2 * t) = -t / 2 by ring]
  -- Integrability of `tⁿ·e^{−t/2}` on `Ioi 0`.
  have hint : IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-t / 2)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := 1 / 2)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (le_refl 1) (by norm_num)
    apply h.congr_fun ?_ measurableSet_Ioi
    intro t _
    show t ^ (n : ℝ) * Real.exp (-(1 / 2) * t ^ (1 : ℝ)) = t ^ n * Real.exp (-t / 2)
    rw [Real.rpow_natCast, Real.rpow_one, show -(1 / 2) * t = -t / 2 by ring]
  -- Bridge `ofReal ∘ Bochner = lintegral ∘ ofReal`.
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hnonneg)),
    hbase]

end LF4
end CSD
