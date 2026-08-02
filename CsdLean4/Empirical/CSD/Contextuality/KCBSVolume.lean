/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.ContextVolume
public import CsdLean4.Empirical.CSD.VolumeCanonical
public import CsdLean4.Empirical.QM.KCBS
public import Mathlib.LinearAlgebra.CrossProduct

/-!
# Empirical/CSD: KCBS pentagon Born weights as Kähler volumes

**Category:** 3-Local (CSD-ontic volume reading; an instantiation of the context-generic
engine `context_born_frequency_volume`, closing the KCBS gap found by the 2026-08-02
empirical-coverage audit — the last flagship test without a CSD twin).

The **volume-ratio companion** to the QM-side KCBS inequality
(`Empirical/QM/KCBS.lean`): the five pentagon rays `kv k` violate the noncontextual bound
`2` at the apex state with quantum value `√5` (`kcbs_qm_value`, `kcbs_quantum_violation`).
Here the *per-context* Born weights of that experiment are realised as Fubini–Study
typicality volumes on the fixed ontic `Σ = ℂℙ²`.

## Construction

A KCBS context is an adjacent ray pair `{kv k, kv (k+1)}` — orthogonal by the pentagon
overlap identity (`kv_orth`) — completed to a full projective frame by the **cross product**
`kv 0 ×₃ kv 1`: orthogonal to both factors (`dot_self_cross`, `dot_cross_self`) and unit by
the Lagrange identity (`cross_dot_cross`, `1·1 − 0² = 1`). The three real vectors are
complexified (`c3`), with the inner-product transport `c3_inner` pulling every orthonormality
fact from the QM side's *real* dot products — no inner-product computation is re-proved.

## Scope and honesty

- **One representative context built** (`{kv 0, kv 1, ⋯×₃⋯}`), as for `KS18Volume`: the other
  four pentagon contexts are identical instantiations at `{kv k, kv (k+1)}`, with per-context
  orthogonality already certified for all five by `kv_orth`. Mechanical repetition, omitted.
- **Realisation, not derivation**, as for the whole volume series: Born = FS-volume is
  *derived* one layer down (`born_frequency_convergence_N_uncond`, Gleason-free) and
  *imported* here; `Φ = id` — the dynamical-layer reading of KCBS is not exercised here
  (sequential statistics live in `SequentialMeasurement.lean`).
- The KCBS *inequality* itself (noncontextual bound `2`, quantum `√5`) stays at the
  QM-validity layer; this file grounds the weights it is computed from.

## References

`Empirical/QM/KCBS.lean` (`kv`, `kv_orth`, `kv_unit`, `kv_apex_born`, `kcbs_qm_value`);
`Empirical/CSD/ContextVolume.lean` (the engine);
`Empirical/CSD/Contextuality/KS18Volume.lean` (the sibling this mirrors); `EMPIRICAL.md`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Matrix.UnitaryGroup CSD.LF4 Matrix
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace Empirical
namespace CSDBridge
namespace KCBS

open CSD.Empirical.QM.KCBS CSD.Empirical.CSDBridge.ContextVolume

/-! ### Complexification and the inner-product transport -/

/-- Componentwise complexification `ℝ³ → ℂ³`. -/
noncomputable def c3 (u : Fin 3 → ℝ) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 fun i => ((u i : ℝ) : ℂ)

/-- **Complexification transport**: the complex inner product of two complexified real vectors
is the coercion of their real dot product. Every orthonormality fact below is pulled from the
QM side through this lemma — nothing is re-proved. -/
lemma c3_inner (u v : Fin 3 → ℝ) :
    (inner ℂ (c3 u) (c3 v) : ℂ) = ((u ⬝ᵥ v : ℝ) : ℂ) := by
  rw [PiLp.inner_apply, show (u ⬝ᵥ v : ℝ) = ∑ i, u i * v i from rfl, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [c3, WithLp.ofLp_toLp]
  rw [RCLike.inner_apply, Complex.conj_ofReal]
  push_cast
  ring

/-- `dot3` is the matrix dot product (`Fin.sum_univ_three`). -/
lemma dot3_eq_dotProduct (u v : Fin 3 → ℝ) : dot3 u v = u ⬝ᵥ v := by
  rw [dot3, show (u ⬝ᵥ v : ℝ) = ∑ i, u i * v i from rfl, Fin.sum_univ_three]

/-! ### The representative pentagon context `{kv 0, kv 1, kv 0 ×₃ kv 1}` -/

/-- The completing third leg: the cross product of the first adjacent pair. -/
noncomputable def kcbsCross : Fin 3 → ℝ := crossProduct (kv 0) (kv 1)

/-- The three dot-product facts of the frame, all sourced from the QM side or the cross-product
API: unit legs, orthogonal pair, orthogonal completion, unit completion. -/
lemma kv0_dot_kv0 : kv 0 ⬝ᵥ kv 0 = 1 := by
  rw [← dot3_eq_dotProduct]; exact kv_unit 0

lemma kv1_dot_kv1 : kv 1 ⬝ᵥ kv 1 = 1 := by
  rw [← dot3_eq_dotProduct]; exact kv_unit 1

lemma kv0_dot_kv1 : kv 0 ⬝ᵥ kv 1 = 0 := by
  rw [← dot3_eq_dotProduct]
  have h := kv_orth 0
  norm_num at h
  exact h

lemma kv0_dot_cross : kv 0 ⬝ᵥ kcbsCross = 0 := dot_self_cross (kv 0) (kv 1)

lemma kv1_dot_cross : kv 1 ⬝ᵥ kcbsCross = 0 := dot_cross_self (kv 0) (kv 1)

lemma cross_dot_cross' : kcbsCross ⬝ᵥ kcbsCross = 1 := by
  rw [kcbsCross, cross_dot_cross, kv0_dot_kv0, kv1_dot_kv1, kv0_dot_kv1,
    dotProduct_comm (kv 1) (kv 0), kv0_dot_kv1]
  ring

/-- The representative KCBS context frame: the adjacent pair and its cross-product
completion, complexified. -/
noncomputable def kcbsCtxVec : Fin 3 → EuclideanSpace ℂ (Fin 3)
  | 0 => c3 (kv 0)
  | 1 => c3 (kv 1)
  | 2 => c3 kcbsCross

/-- **The representative KCBS context is orthonormal** — nine cases, each a transported real
dot-product fact. -/
lemma kcbsCtxVec_orthonormal : Orthonormal ℂ kcbsCtxVec := by
  have h00 : (inner ℂ (c3 (kv 0)) (c3 (kv 0)) : ℂ) = 1 := by
    rw [c3_inner, kv0_dot_kv0]; norm_num
  have h11 : (inner ℂ (c3 (kv 1)) (c3 (kv 1)) : ℂ) = 1 := by
    rw [c3_inner, kv1_dot_kv1]; norm_num
  have h22 : (inner ℂ (c3 kcbsCross) (c3 kcbsCross) : ℂ) = 1 := by
    rw [c3_inner, cross_dot_cross']; norm_num
  have h01 : (inner ℂ (c3 (kv 0)) (c3 (kv 1)) : ℂ) = 0 := by
    rw [c3_inner, kv0_dot_kv1]; norm_num
  have h10 : (inner ℂ (c3 (kv 1)) (c3 (kv 0)) : ℂ) = 0 := by
    rw [c3_inner, dotProduct_comm, kv0_dot_kv1]; norm_num
  have h02 : (inner ℂ (c3 (kv 0)) (c3 kcbsCross) : ℂ) = 0 := by
    rw [c3_inner, kv0_dot_cross]; norm_num
  have h20 : (inner ℂ (c3 kcbsCross) (c3 (kv 0)) : ℂ) = 0 := by
    rw [c3_inner, dotProduct_comm, kv0_dot_cross]; norm_num
  have h12 : (inner ℂ (c3 (kv 1)) (c3 kcbsCross) : ℂ) = 0 := by
    rw [c3_inner, kv1_dot_cross]; norm_num
  have h21 : (inner ℂ (c3 kcbsCross) (c3 (kv 1)) : ℂ) = 0 := by
    rw [c3_inner, dotProduct_comm, kv1_dot_cross]; norm_num
  rw [orthonormal_iff_ite]
  intro a b
  fin_cases a <;> fin_cases b
  · show (inner ℂ (c3 (kv 0)) (c3 (kv 0)) : ℂ) = _
    rw [h00]; norm_num
  · show (inner ℂ (c3 (kv 0)) (c3 (kv 1)) : ℂ) = _
    rw [h01]; norm_num
  · show (inner ℂ (c3 (kv 0)) (c3 kcbsCross) : ℂ) = _
    rw [h02]; norm_num
  · show (inner ℂ (c3 (kv 1)) (c3 (kv 0)) : ℂ) = _
    rw [h10]; norm_num
  · show (inner ℂ (c3 (kv 1)) (c3 (kv 1)) : ℂ) = _
    rw [h11]; norm_num
  · show (inner ℂ (c3 (kv 1)) (c3 kcbsCross) : ℂ) = _
    rw [h12]; norm_num
  · show (inner ℂ (c3 kcbsCross) (c3 (kv 0)) : ℂ) = _
    rw [h20]; norm_num
  · show (inner ℂ (c3 kcbsCross) (c3 (kv 1)) : ℂ) = _
    rw [h21]; norm_num
  · show (inner ℂ (c3 kcbsCross) (c3 kcbsCross) : ℂ) = _
    rw [h22]; norm_num

/-- **The representative KCBS context as a Mathlib `OrthonormalBasis`** — the projective
measurement frame fed to the engine. -/
noncomputable def kcbsContextBasis :
    OrthonormalBasis (Fin 3) ℂ (EuclideanSpace ℂ (Fin 3)) := by
  refine OrthonormalBasis.mk kcbsCtxVec_orthonormal ?_
  have hcard : Fintype.card (Fin 3) = Module.finrank ℂ (EuclideanSpace ℂ (Fin 3)) := by
    rw [Fintype.card_fin, finrank_euclideanSpace_fin]
  rw [kcbsCtxVec_orthonormal.linearIndependent.span_eq_top_of_card_eq_finrank hcard]

lemma kcbsContextBasis_apply (j : Fin 3) : kcbsContextBasis j = kcbsCtxVec j := by
  unfold kcbsContextBasis
  rw [OrthonormalBasis.coe_mk]

/-! ### The pentagon weight, transported -/

/-- The complexified apex preparation `(0,0,1)`. -/
noncomputable def apexC : EuclideanSpace ℂ (Fin 3) := c3 apex

lemma norm_apexC : ‖apexC‖ = 1 := by
  have h : (inner ℂ apexC apexC : ℂ) = ((1 : ℝ) : ℂ) := by
    rw [apexC, c3_inner, ← dot3_eq_dotProduct]
    norm_num [dot3, apex, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
  have h3 : ‖apexC‖ ^ 2 = 1 := by
    have hre := congrArg RCLike.re h
    rw [inner_self_eq_norm_sq] at hre
    simpa using hre
  apply le_antisymm <;> nlinarith [norm_nonneg apexC, h3]

/-- **The pentagon Born weight `1/√5`, at the level of the frame.** The apex overlap with the
first pentagon ray, complexified: `‖⟨kcbsContextBasis 0, apexC⟩‖² = 1/√5` — the weight whose
five-fold sum is the quantum KCBS value `√5` (`kcbs_qm_value`). -/
theorem kcbs_pentagon_weight :
    ‖(inner ℂ (kcbsContextBasis 0) apexC : ℂ)‖ ^ 2 = 1 / Real.sqrt 5 := by
  rw [kcbsContextBasis_apply]
  show ‖(inner ℂ (c3 (kv 0)) apexC : ℂ)‖ ^ 2 = 1 / Real.sqrt 5
  rw [apexC, c3_inner]
  rw [show ((kv 0 ⬝ᵥ apex : ℝ) : ℂ) = ((dot3 apex (kv 0) : ℝ) : ℂ) by
    rw [← dot3_eq_dotProduct, dot3, dot3]; push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact kv_apex_born 0

/-! ### The headline: KCBS context Born weights as FS typicality volumes -/

/-- **KCBS pentagon Born weights as Kähler volumes.** For i.i.d. trials drawing microstates
from the Fubini–Study typicality measure on the ontic `Σ = ℂℙ²`, the empirical frequencies of
the three barycentric Born regions (carved in the rotated frame `kcbsContextBasis.repr ψ`)
converge, on a single almost-sure event, to the context-dependent Born weights
`‖⟨kcbsContextBasis i, ψ⟩‖²` of measuring the unit preparation `ψ` in the representative
pentagon context `{kv 0, kv 1}`.

At `ψ = apexC`, the ray-`0` weight is the pentagon number `1/√5` (`kcbs_pentagon_weight`) —
the quantity whose five-context sum `√5` violates the noncontextual bound `2`
(`kcbs_quantum_violation`). Each weight in that violation is an ontic typicality volume on
the *fixed* `Σ`; the contextuality is *which projective carving* is measured, not a hidden
variable. The other four pentagon contexts are identical instantiations (`kv_orth` certifies
all five adjacencies). -/
theorem kcbs_context_born_frequency_volume
    (p₀ : CPN 3) (ψ : EuclideanSpace ℂ (Fin 3)) (hψ : ‖ψ‖ = 1)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 3) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ i : Fin 3,
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' bornRegion (kcbsContextBasis.repr ψ)
              (repr_ne_zero kcbsContextBasis ψ hψ) i)
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : Fin 3,
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator
                ((X k) ⁻¹' bornRegion (kcbsContextBasis.repr ψ)
                  (repr_ne_zero kcbsContextBasis ψ hψ) i)
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (kcbsContextBasis i) ψ‖ ^ 2)) :=
  context_born_frequency_volume p₀ kcbsContextBasis ψ hψ X hX hlaw hindep

/-- `kcbs_context_born_frequency_volume` on the canonical i.i.d. Fubini–Study trial witness:
the trial bundle is discharged, so the hypothesis set is Lean-inhabited, not merely
classically satisfiable. -/
theorem kcbs_context_born_frequency_volume_canonical
    (p₀ : CPN 3) (ψ : EuclideanSpace ℂ (Fin 3)) (hψ : ‖ψ‖ = 1) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀, ∀ i : Fin 3,
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator
                ((fsTrial 3 k) ⁻¹' bornRegion (kcbsContextBasis.repr ψ)
                  (repr_ne_zero kcbsContextBasis ψ hψ) i)
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (kcbsContextBasis i) ψ‖ ^ 2)) :=
  context_born_frequency_volume_canonical p₀ kcbsContextBasis ψ hψ

end KCBS
end CSDBridge
end Empirical
end CSD
