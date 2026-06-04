import CsdLean4.LF2.BornWrapper

/-!
# LF2: auxiliary effect constructions

**Category:** 3-Local (LF2 Effect-algebra helpers).

Shared infrastructure for building concrete (possibly non-projective) effects, used
by the Empirical POVM examples (trine, USD, …):

- `scaledRankOneEffect` — `c|φ⟩⟨φ|` as an `Effect` for `0 ≤ c ≤ 1` and unit `φ`
  (the `c = 1` case is `rankOneEffect`); PSD via `psd_smul` (the `√c·I`
  conjugation), `le_one` via the convex decomposition `(1-c)P + (1-P)`;
- `trace_outer_mul_eq_inner` — `Tr(|ψ⟩⟨ψ| · M) = ⟨ψ, M ψ⟩`, the trace-form /
  expectation bridge;
- `scaledRankOne_quadratic` — `⟨ψ, (c|φ⟩⟨φ|) ψ⟩ = c‖⟨ψ,φ⟩‖²`, the quadratic form
  (the per-outcome Born weight of a scaled rank-1 effect).
-/

open Matrix
open scoped ComplexOrder

namespace CSD
namespace LF2

variable {N : ℕ}

/-- `(c • M)` is positive semidefinite for `0 ≤ c` (real) and PSD `M`, via the
conjugation `(√c·I)ᴴ M (√c·I) = c·M`. -/
lemma psd_smul {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    ((c : ℂ) • M).PosSemidef := by
  have hstar : star ((Real.sqrt c : ℝ) : ℂ) = ((Real.sqrt c : ℝ) : ℂ) := Complex.conj_ofReal _
  have hsc : ((Real.sqrt c : ℝ) : ℂ) * ((Real.sqrt c : ℝ) : ℂ) = (c : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  have hb := hM.mul_mul_conjTranspose_same
    (((Real.sqrt c : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))
  have heq : (((Real.sqrt c : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) * M
        * (((Real.sqrt c : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ
      = (c : ℂ) • M := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul, hstar, hsc]
  rwa [heq] at hb

/-- `c|φ⟩⟨φ|` as an `Effect`, for `0 ≤ c ≤ 1` and a unit vector `φ`. The `c = 1`
case is `rankOneEffect`. -/
noncomputable def scaledRankOneEffect (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (φ : EuclideanSpace ℂ (Fin N)) (hφ : ‖φ‖ = 1) : Effect N where
  M := (c : ℂ) • outerProduct φ
  isHermitian := (outerProduct_isHermitian φ).smul (k := (c : ℂ)) (Complex.conj_ofReal c)
  nonneg := psd_smul (outerProduct_posSemidef φ) hc0
  le_one := by
    have hdecomp : (1 : Matrix (Fin N) (Fin N) ℂ) - (c : ℂ) • outerProduct φ
        = ((1 - c : ℝ) : ℂ) • outerProduct φ + (1 - outerProduct φ) := by
      rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]; abel
    rw [hdecomp]
    exact (psd_smul (outerProduct_posSemidef φ) (by linarith)).add
      (one_sub_outerProduct_posSemidef φ hφ)

@[simp] lemma scaledRankOneEffect_M (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (φ : EuclideanSpace ℂ (Fin N)) (hφ : ‖φ‖ = 1) :
    (scaledRankOneEffect c hc0 hc1 φ hφ).M = (c : ℂ) • outerProduct φ := rfl

/-- `Tr(|ψ⟩⟨ψ| · M) = ⟨ψ, M ψ⟩` — the trace-form / expectation bridge. -/
lemma trace_outer_mul_eq_inner (ψ : EuclideanSpace ℂ (Fin N))
    (M : Matrix (Fin N) (Fin N) ℂ) :
    (outerProduct ψ * M).trace = inner ℂ ψ (Matrix.toEuclideanLin M ψ) := by
  rw [Matrix.trace_mul_comm]
  have hmul : M * outerProduct ψ
      = Matrix.vecMulVec (M *ᵥ (fun i => ψ i)) (fun i => star (ψ i)) := by
    ext i j
    simp only [Matrix.mul_apply, outerProduct, Matrix.vecMulVec_apply, Matrix.mulVec,
      dotProduct, Finset.sum_mul, mul_assoc]
  rw [hmul, Matrix.trace_vecMulVec, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  rfl

/-- **Quadratic form of a scaled rank-1 effect:** `⟨ψ, (c|φ⟩⟨φ|) ψ⟩ = c‖⟨ψ,φ⟩‖²`.
The per-outcome Born weight of a scaled rank-1 effect on a unit preparation. -/
lemma scaledRankOne_quadratic (c : ℝ) (φ ψ : EuclideanSpace ℂ (Fin N))
    (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1) :
    RCLike.re (inner ℂ ψ (Matrix.toEuclideanLin ((c : ℂ) • outerProduct φ) ψ))
      = c * ‖inner ℂ ψ φ‖ ^ 2 := by
  rw [← trace_outer_mul_eq_inner, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    show RCLike.re (((c : ℝ) : ℂ) * (outerProduct ψ * outerProduct φ).trace)
        = (c : ℝ) * RCLike.re ((outerProduct ψ * outerProduct φ).trace) from
      RCLike.re_ofReal_mul c _]
  congr 1
  have hbq := born_quadratic ψ φ hψ hφ
  simpa only [traceForm, rankOneDensity, rankOneEffect] using hbq

end LF2
end CSD
