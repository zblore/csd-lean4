import CsdLean4.LF4.MomentDirichletN
import CsdLean4.LF4.MomentBornN
import CsdLean4.LF4.MomentUniform

/-!
# LF4 verification: the general-N joint-Dirichlet law recovers the qubit at N=2

A machine-checked consistency cross-check. The general-N headline
`fs_moment_joint_dirichlet_N` and the qubit `fs_moment_pushforward_uniform` were proved
by independent routes (the qubit via the `Fin 4` Gaussian marginal; the general-N via
the Gaussian→Dirichlet curry chain). This file **derives the qubit statement from the
general-N one at `M = 1`**, converting "they agree by hand" into a kernel-checked
reduction. If the general-N statement were a faithful generalisation only by accident,
this would fail to compile.

The reduction handles the two shape differences the referee flagged:
- `ratioN (momentMap p)` is the *normalised* free coordinate on `Fin 1 → ℝ`; at `N = 2`
  it equals the raw `momentMap p 0` because the moments sum to one
  (`momentMap_sum_eq_one`), composed with the `(Fin 1 → ℝ) ≃ᵐ ℝ` evaluation iso
  (`MeasurableEquiv.funUnique`, measure-preserving);
- `openSimplexFree` on `Fin 1 → ℝ` is the `funUnique`-preimage of `Ioo 0 1`, which differs
  from the qubit's `Icc 0 1` by the volume-null endpoint set (`Ioo_ae_eq_Icc`).
-/

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization

namespace CSD
namespace LF4

/-- **N=2 consistency: the qubit moment pushforward is the `M = 1` case of the joint
Dirichlet law.** Re-derives `fs_moment_pushforward_uniform` from
`fs_moment_joint_dirichlet_N (M := 1)`. Foundational-triple-only (inherits the
general-N theorem's axiom posture). -/
theorem fs_moment_pushforward_uniform_of_joint_dirichlet (p₀ : CPN 2) :
    Measure.map (fun p : CPN 2 => momentMap p 0) (fubiniStudyMeasure p₀)
      = volume.restrict (Set.Icc 0 1) := by
  set e := MeasurableEquiv.funUnique (Fin 1) ℝ with he
  -- The qubit coordinate map is the general free-coordinate map, read through `e`.
  have hfun : (fun p : CPN 2 => momentMap p 0)
      = (e ∘ (fun p : CPN 2 => ratioN (fun i => momentMap p i))) := by
    funext p
    rw [Function.comp_apply, he, MeasurableEquiv.funUnique_apply]
    show momentMap p 0 = ratioN (fun i => momentMap p i) (default : Fin 1)
    simp only [ratioN, momentMap_sum_eq_one p, div_one, Fin.default_eq_zero, Fin.castSucc_zero]
  -- `openSimplexFree` on `Fin 1 → ℝ` is the `e`-preimage of `Ioo 0 1`.
  have hpre : (openSimplexFree (M := 1)) = e ⁻¹' (Set.Ioo (0 : ℝ) 1) := by
    ext t
    simp only [openSimplexFree, Set.mem_ofPred_eq, Set.mem_preimage, he,
      MeasurableEquiv.funUnique_apply, Set.mem_Ioo, Fin.sum_univ_one, Fin.forall_fin_one,
      Fin.default_eq_zero]
  rw [hfun, ← Measure.map_map e.measurable (measurable_ratio_momentMap (M := 1)),
    fs_moment_joint_dirichlet_N (M := 1) p₀, Nat.factorial_one, Nat.cast_one, one_smul,
    hpre, ← Measure.restrict_map e.measurable measurableSet_Ioo]
  have hmp : Measure.map (⇑e) volume = volume := by
    rw [he]; exact (volume_preserving_funUnique (Fin 1) ℝ).map_eq
  rw [hmp]
  exact Measure.restrict_congr_set Ioo_ae_eq_Icc

end LF4
end CSD
