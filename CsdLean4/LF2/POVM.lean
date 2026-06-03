import CsdLean4.LF2.BornWrapper

/-!
# LF2: POVMs (positive operator-valued measures)

**Category:** 3-Local (LF2 matrix-based `POVM` built on the `Effect` type).

A **POVM** on an `N`-dimensional complex Hilbert space is a finite family of
effects `{Eᵢ}` that sum to the identity — the most general (non-projective)
quantum measurement. This file gives the type, the Born weight
`pᵢ(ψ) = ⟨ψ, Eᵢ ψ⟩`, and the completeness identity `∑ᵢ pᵢ(ψ) = ‖ψ‖²`.

This is **P.1** of the POVM tranche (`specs/povm-plan.md`): the type the Naimark
dilation (`LF4/POVMDilation.lean`) and the ontic volume reading hang off.

The Born weight is taken in the `EuclideanSpace`/`toEuclideanLin` form
`re ⟨ψ, Eᵢ ψ⟩` — matching `Empirical/QM/Bell.lean`'s expectation form and the
`fs_born_volume_ratio_N` projective-Born surface — so the dilation transfer
(`born_transfer`) composes cleanly through the matrix↔operator adjoint bridge.
-/

open Matrix
open scoped ComplexOrder

namespace CSD
namespace LF2

variable {N : ℕ} {ι : Type*} [Fintype ι]

/-- **POVM on an `N`-dimensional complex Hilbert space.** A finite family of
`Effect`s (Hermitian, `0 ≤ Eᵢ ≤ I`) that sum to the identity. The completeness
relation `∑ᵢ Eᵢ = I` is what makes `{⟨ψ, Eᵢ ψ⟩}ᵢ` a probability vector. -/
structure POVM (N : ℕ) (ι : Type*) [Fintype ι] where
  /-- The effect family. -/
  E : ι → Effect N
  /-- Completeness: the effects sum to the identity. -/
  complete : ∑ i, (E i).M = 1

namespace POVM

/-- **POVM Born weight** `pᵢ(ψ) = ⟨ψ, Eᵢ ψ⟩` (real, via `re`; `Eᵢ` Hermitian makes
the inner product real). The probability the `i`-th outcome occurs on preparation
`ψ`. -/
noncomputable def weight (P : POVM N ι) (ψ : EuclideanSpace ℂ (Fin N)) (i : ι) : ℝ :=
  RCLike.re (inner ℂ ψ (Matrix.toEuclideanLin (P.E i).M ψ))

/-- **Completeness of the Born weights.** `∑ᵢ pᵢ(ψ) = ‖ψ‖²`, so on a unit vector
the POVM Born weights form a probability distribution. Routes through `∑ᵢ Eᵢ = I`
(`complete`) and `⟨ψ, ψ⟩ = ‖ψ‖²`. -/
theorem weights_sum_eq_normSq (P : POVM N ι) (ψ : EuclideanSpace ℂ (Fin N)) :
    ∑ i, P.weight ψ i = ‖ψ‖ ^ 2 := by
  have hmap : ∑ i, Matrix.toEuclideanLin (P.E i).M ψ
      = Matrix.toEuclideanLin (∑ i, (P.E i).M) ψ := by
    rw [map_sum, LinearMap.sum_apply]
  have key : ∑ i, inner ℂ ψ (Matrix.toEuclideanLin (P.E i).M ψ) = (((‖ψ‖ ^ 2 : ℝ)) : ℂ) := by
    rw [← inner_sum, hmap, P.complete,
      show Matrix.toEuclideanLin (1 : Matrix (Fin N) (Fin N) ℂ) = LinearMap.id from
        Matrix.toLpLin_one 2,
      LinearMap.id_apply, inner_self_eq_norm_sq_to_K]
    norm_cast
  calc ∑ i, P.weight ψ i
      = RCLike.re (∑ i, inner ℂ ψ (Matrix.toEuclideanLin (P.E i).M ψ)) := by
        simp only [weight, ← RCLike.reLm_coe]
        exact (map_sum RCLike.reLm _ Finset.univ).symm
    _ = ‖ψ‖ ^ 2 := by rw [key]; exact RCLike.ofReal_re _

/-- **Born weights of a unit preparation sum to one.** -/
theorem weights_sum_eq_one (P : POVM N ι) (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1) :
    ∑ i, P.weight ψ i = 1 := by
  rw [weights_sum_eq_normSq, hψ, one_pow]

end POVM
end LF2
end CSD
