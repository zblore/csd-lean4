import CsdLean4.FND.ConditioningLuders
import CsdLean4.FND.MixedEnsemble

/-!
# FND/MixedOntic: the ontic-side mixed-state representation on the unified model (#8 C)

**Category:** 7-FND (the Choice A ontological layer).

`FiniteQMClosure` carries the Born content for PURE states only (`born_frequency` for a single `ψ`). This
module represents a MIXED state on the SAME ontic model `productDynamics H hH p₀` as a classical mixture
over ontic pure-preparations, and proves that the mixture reproduces the density-operator Born rule.

The state enters the ontic model only through the pointer/outcome structure (the `ψ`-dependent Born
region), not through the Liouville law `μL` (which is fixed). So a mixed state `ρ` is represented by
classical randomness over WHICH pure component `ψⱼ = eⱼ` (eigenvector) is in effect, weighted by the
eigenvalues `λⱼ` — the spectral ensemble of `FND/MixedEnsemble.lean` (`density_isPureEnsemble`). The
resulting mixed Born WEIGHT for pointer outcome `i` is

  `∑ⱼ λⱼ · μL(π⁻¹ bornRegion(eⱼ) i)`   (classical mixture of ontic Born-region measures)

and `mixed_ontic_born_weight` proves this equals `Tr(ρ Eᵢ)` (`traceForm ρ (rankOneEffect eᵢ)`) — the
density-operator Born probability of the standard-basis outcome `i`. So the unified model represents mixed
states, not only pure ones: mixing ontic pure-preparations by the spectral weights gives EXACTLY the
Born rule of `ρ`.

This is stated at the WEIGHT (probability) level — the same granularity as the conditioning=Lüders
correspondence (`conditioning_luders_effect_equivalence`), which is also a weight/ratio statement rather
than an LLN. A genuine mixed-state frequency LLN (redrawing the component each shot on a two-stage
mixture space) is the remaining refinement of #8 C.

Proof = the ontic weight agreement `onticRegion_measure_eq_born` (`FND/ConditioningLuders.lean`,
`μL(π⁻¹ bornRegion ψ i) = ‖⟨eᵢ,ψ⟩‖²`) composed with the spectral affine Born rule
`traceForm_eq_pureEnsemble` (`FND/MixedEnsemble.lean`) and the pure Born quadratic form `born_quadratic`
(`LF2/BornWrapper.lean`), matched up by conjugate symmetry of the inner product.

References: `FND/ConditioningLuders.lean` (`onticRegion_measure_eq_born`), `FND/MixedEnsemble.lean`
(`traceForm_eq_pureEnsemble`, `eigenvectorBasis_norm_one`, `density_isPureEnsemble`),
`LF2/BornWrapper.lean` (`traceForm`, `rankOneEffect`, `born_quadratic`); `specs/future-work.md` FND-T9.
-/

open MeasureTheory
open scoped ComplexOrder

namespace CSD.FND

open CSD.LF2 CSD.LF4

variable {M : ℕ} (H : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (hH : H.IsHermitian) (p₀ : CPN (M + 1))

/-- The eigenvectors of a density operator are nonzero (they are unit vectors). -/
theorem eigenvectorBasis_ne_zero (ρ : DensityOperator (M + 1)) (j : Fin (M + 1)) :
    ρ.isHermitian.eigenvectorBasis j ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [eigenvectorBasis_norm_one ρ j]; norm_num)

/-- The standard basis vector `eᵢ` has unit norm. -/
theorem single_norm_one (i : Fin (M + 1)) : ‖EuclideanSpace.single i (1 : ℂ)‖ = 1 := by
  rw [EuclideanSpace.norm_single, norm_one]

/-- **The ontic mixed-state Born weight (#8 C).** For any density operator `ρ` and pointer outcome `i`,
the classical mixture — over `ρ`'s spectral ensemble `(λⱼ, eⱼ)` — of the ontic Born-region measures equals
the density-operator Born probability `Tr(ρ |eᵢ⟩⟨eᵢ|)`:

  `∑ⱼ λⱼ · μL(π⁻¹ bornRegion(eⱼ) i) = traceForm ρ (rankOneEffect eᵢ)`.

So the unified model `productDynamics H hH p₀` represents mixed states: mixing its ontic pure-preparations
by the spectral weights reproduces exactly the Born rule of `ρ`. Composes the ontic weight agreement
`onticRegion_measure_eq_born` with the spectral affine Born rule `traceForm_eq_pureEnsemble` and the pure
`born_quadratic`, matched by conjugate symmetry of the inner product. -/
theorem mixed_ontic_born_weight (ρ : DensityOperator (M + 1)) (i : Fin (M + 1)) :
    ∑ j, ρ.isHermitian.eigenvalues j
        * (((productDynamics H hH p₀).muL : Measure (KSigma (M + 1)))
            ((productSector H hH p₀).pi ⁻¹'
              bornRegion (ρ.isHermitian.eigenvectorBasis j) (eigenvectorBasis_ne_zero ρ j) i)).toReal
      = traceForm ρ (rankOneEffect (EuclideanSpace.single i (1 : ℂ)) (single_norm_one i)) := by
  rw [traceForm_eq_pureEnsemble ρ (rankOneEffect (EuclideanSpace.single i (1 : ℂ)) (single_norm_one i))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [onticRegion_measure_eq_born H hH p₀ (ρ.isHermitian.eigenvectorBasis j)
        (eigenvectorBasis_ne_zero ρ j) (eigenvectorBasis_norm_one ρ j) i,
      born_quadratic (ρ.isHermitian.eigenvectorBasis j) (EuclideanSpace.single i (1 : ℂ))
        (eigenvectorBasis_norm_one ρ j) (single_norm_one i)]
  have hnorm : ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) (ρ.isHermitian.eigenvectorBasis j)‖
      = ‖inner ℂ (ρ.isHermitian.eigenvectorBasis j) (EuclideanSpace.single i (1 : ℂ))‖ := by
    rw [← inner_conj_symm (ρ.isHermitian.eigenvectorBasis j) (EuclideanSpace.single i (1 : ℂ)),
      RCLike.norm_conj]
  rw [hnorm]

end CSD.FND
