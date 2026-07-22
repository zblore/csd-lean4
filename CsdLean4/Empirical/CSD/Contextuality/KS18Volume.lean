/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Empirical.CSD.ContextVolume
import CsdLean4.Empirical.CSD.VolumeCanonical
import CsdLean4.Empirical.QM.Contextuality.KS18

/-!
# Empirical/CSD: Kochen-Specker (Cabello-18) contextual Born weights as Kähler volumes

**Category:** 3-Local (CSD-ontic volume reading; a quick-win instantiation of the
already-proved context-generic engine
`CSD.Empirical.CSDBridge.ContextVolume.context_born_frequency_volume`).

This is the **volume-ratio companion** to the *impossibility* readings of the
Kochen-Specker theorem:

- QM side (`Empirical/QM/Contextuality/KS18.lean`): the Cabello-Estebaranz-García-Alcaine
  1996 18-ray / 9-basis data, pairwise orthogonality `cabello_pairwise_orthogonal_in_basis`,
  and the no-go `ks_no_value_assignment_cabello18` / `no_value_assignment_18_9`.
- CSD impossibility side (`Empirical/CSD/Contextuality/KS18.lean`):
  `no_csd_ks_assignment_bundle` — no non-contextual ontic-outcome partition discipline
  is satisfiable.

The two halves of the KS story, told honestly:

1. **Each Cabello context carries genuine Born weights as FS typicality volumes.** Taking
   a representative context (basis `0`, the rays `{v0, v1, v2, v3}`), the four un-normalised
   real Cabello rays are complexified (`cabelloVecC`) and normalised (`ksCtxVec`) into a
   genuine `OrthonormalBasis (Fin 4) ℂ (EuclideanSpace ℂ (Fin 4))` (`ksContextBasis`).
   Orthonormality is **not re-proved**: the off-diagonal inner products are pulled from the
   QM-side `cabello_pairwise_orthogonal_in_basis` through the complexification transport
   `cabelloVecC_inner` (`⟨cabelloVecC i, cabelloVecC j⟩_ℂ = ↑⟨cabelloVec i, cabelloVec j⟩_ℝ`).
   Instantiating the engine `context_born_frequency_volume` at this basis, **every** ray's
   context-dependent Born weight `‖⟨ksContextBasis i, ψ⟩‖²` is the almost-sure limit of
   empirical frequencies of the barycentric Born region `bornRegion` on the fixed ontic
   `Σ = ℂℙ³` — a Fubini-Study typicality volume (`ks18_context_born_frequency_volume`).
2. **Yet no single non-contextual value assignment reproduces all 9 contexts jointly**
   (`ks_no_value_assignment_cabello18`, the combinatorial `9 = 2k` impossibility).

**The CSD reading of contextuality.** The context-dependence the KS theorem exploits is, on
the CSD ontology, *which projective carving of the one ontic `Σ` is measured* — not a hidden
variable. Each context's outcome weights are typicality volumes on the same `Σ = ℂℙ³`,
recomputed per measurement frame `B` (which orthonormal frame carves the moment regions).
There is no global `0/1` labelling of all 18 rays consistent across the overlapping contexts,
because no global section of the carved-volume assignment exists — exactly the combinatorial
no-go, now sitting beside a genuine per-context volume realisation.

## Scope and honesty

- **Rank-1.** The Cabello rays are rank-1, matching `context_born_frequency_volume`'s rank-1
  scope (degenerate eigenspaces would route through `block_born_frequency_volume`).
- **One representative context built.** Basis `0` is built explicitly; the other 8 Cabello
  contexts (`cabelloBasis 1 … 8`) are **identical instantiations** of the same engine at the
  corresponding orthonormal frame — the only per-context input is the 4-ray orthogonal tuple,
  already certified for all 9 bases by `cabello_pairwise_orthogonal_in_basis`. No new
  mathematics; building all 9 is mechanical repetition and is omitted.
- **Realisation, not derivation.** As for the whole `Empirical/CSD/*Volume` series and the
  engine it specialises: the Born = FS-volume identity is *derived* one layer down (the
  Duistermaat-Heckman / moment-map cluster, `LF4.born_frequency_convergence_N_uncond`,
  Gleason-free, no Born put in) and *imported* here; `Φ = id` (no dynamics exercised). The
  KS no-go itself stays at the QM-validity layer (`Empirical/QM/`).
- **Gleason-free, foundational-triple-only.** The engine is `busch_effect_gleason`-free; this
  instantiation inherits that.
-/

open MeasureTheory ProbabilityTheory Filter Matrix.UnitaryGroup CSD.LF4
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace Empirical
namespace CSDBridge
namespace KochenSpecker

open CSD.Empirical.KochenSpecker CSD.Empirical.CSDBridge.ContextVolume

/-! ### Complexification of the Cabello rays and the inner-product transport -/

/-- The complexification `ℝ⁴ → ℂ⁴` of the `i`-th un-normalised Cabello ray (componentwise
real-to-complex coercion). -/
noncomputable def cabelloVecC (i : Fin 18) : EuclideanSpace ℂ (Fin 4) :=
  WithLp.toLp 2 (fun k => ((cabelloMat i k : ℝ) : ℂ))

/-- Scalar real inner product on `ℝ` (the `RCLike.toInnerProductSpaceReal` instance produced
by `PiLp.inner_apply` on a real `EuclideanSpace`): `⟨a, b⟩_ℝ = a * b`. -/
private lemma real_scalar_inner (a b : ℝ) : (inner ℝ a b : ℝ) = a * b := by
  rw [real_inner_eq_re_inner ℝ]; simp [RCLike.inner_apply, mul_comm]

/-- Scalar complex inner product of two real coercions: `⟨↑a, ↑b⟩_ℂ = ↑(a * b)`. -/
private lemma cplx_scalar_inner (a b : ℝ) : (inner ℂ (↑a : ℂ) (↑b : ℂ) : ℂ) = ↑(a * b) := by
  rw [RCLike.inner_apply, Complex.conj_ofReal]; push_cast; ring

/-- **Complexification transport.** The complex inner product of two complexified Cabello rays
is the real-to-complex coercion of their real inner product:
`⟨cabelloVecC i, cabelloVecC j⟩_ℂ = ↑⟨cabelloVec i, cabelloVec j⟩_ℝ`. This is the bridge that
lets the QM-side orthogonality `cabello_pairwise_orthogonal_in_basis` (stated in `ℝ⁴`) feed
the complex orthonormality below **without re-proving** any inner-product computation. -/
lemma cabelloVecC_inner (i j : Fin 18) :
    (inner ℂ (cabelloVecC i) (cabelloVecC j) : ℂ)
      = ((inner ℝ (cabelloVec i) (cabelloVec j) : ℝ) : ℂ) := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [cabelloVec, cabelloVecC, WithLp.ofLp_toLp]
  rw [real_scalar_inner, cplx_scalar_inner]

/-! ### The representative context (basis 0) as an `OrthonormalBasis` -/

/-- The four ray indices of the representative Cabello context `cabelloBasis 0 = {0,1,2,3}`. -/
def ksRayIdx : Fin 4 → Fin 18 := ![0, 1, 2, 3]

/-- `‖cabelloVecC i‖² = ⟨cabelloVec i, cabelloVec i⟩_ℝ` (the complexification preserves the
squared norm), via `cabelloVecC_inner` at `i = j` and `inner_self_eq_norm_sq_to_K`. -/
lemma cabelloVecC_normSq (i : Fin 18) :
    ‖cabelloVecC i‖ ^ 2 = (inner ℝ (cabelloVec i) (cabelloVec i) : ℝ) := by
  have h1 : (inner ℂ (cabelloVecC i) (cabelloVecC i) : ℂ) = (↑‖cabelloVecC i‖) ^ 2 :=
    inner_self_eq_norm_sq_to_K _
  rw [cabelloVecC_inner] at h1
  exact_mod_cast h1.symm

/-- The four complexified rays of the representative context are nonzero (their squared norms
`1, 1, 2, 2` are positive). -/
lemma cabelloVecC_ne_zero (j : Fin 4) : cabelloVecC (ksRayIdx j) ≠ 0 := by
  intro h
  have hsq := cabelloVecC_normSq (ksRayIdx j)
  rw [h, norm_zero] at hsq
  revert hsq
  fin_cases j <;>
    (simp only [ksRayIdx, Fin.isValue, cabelloVec]
     rw [PiLp.inner_apply, Fin.sum_univ_four]
     norm_num [WithLp.ofLp_toLp, cabelloMat_row_0, cabelloMat_row_1, cabelloMat_row_2,
       cabelloMat_row_3, real_scalar_inner, Matrix.cons_val_zero, Matrix.cons_val_one,
       Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons])

/-- The normalised complexified rays of the representative context. -/
noncomputable def ksCtxVec (j : Fin 4) : EuclideanSpace ℂ (Fin 4) :=
  (↑‖cabelloVecC (ksRayIdx j)‖ : ℂ)⁻¹ • cabelloVecC (ksRayIdx j)

/-- Each normalised context ray has norm one. -/
lemma norm_ksCtxVec (j : Fin 4) : ‖ksCtxVec j‖ = 1 := by
  unfold ksCtxVec
  rw [norm_smul, norm_inv, Complex.norm_real, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (cabelloVecC_ne_zero j))

/-- **The representative Cabello context is orthonormal.** Diagonal from `norm_ksCtxVec`;
off-diagonal from the QM-side `cabello_pairwise_orthogonal_in_basis` (basis `0`) transported
through `cabelloVecC_inner` — no orthogonality is re-proved. -/
lemma ksCtxVec_orthonormal : Orthonormal ℂ ksCtxVec := by
  rw [orthonormal_iff_ite]
  intro a b
  by_cases hab : a = b
  · subst hab
    simp only [if_true]
    rw [inner_self_eq_norm_sq_to_K, norm_ksCtxVec a]
    norm_num
  · simp only [if_neg hab]
    unfold ksCtxVec
    rw [inner_smul_left, inner_smul_right, cabelloVecC_inner]
    have horth : (inner ℝ (cabelloVec (ksRayIdx a)) (cabelloVec (ksRayIdx b)) : ℝ) = 0 := by
      apply cabello_pairwise_orthogonal_in_basis 0
      · fin_cases a <;> decide
      · fin_cases b <;> decide
      · revert hab; fin_cases a <;> fin_cases b <;> simp_all <;> decide
    rw [horth]
    simp

/-- **The representative Cabello context as a Mathlib `OrthonormalBasis`.** A 4-element
orthonormal family in the 4-dimensional `EuclideanSpace ℂ (Fin 4)` spans (cardinality =
`finrank`), so `OrthonormalBasis.mk` applies. This is the projective measurement frame fed to
the engine `context_born_frequency_volume`. -/
noncomputable def ksContextBasis :
    OrthonormalBasis (Fin 4) ℂ (EuclideanSpace ℂ (Fin 4)) := by
  refine OrthonormalBasis.mk ksCtxVec_orthonormal ?_
  have hcard : Fintype.card (Fin 4) = Module.finrank ℂ (EuclideanSpace ℂ (Fin 4)) := by
    rw [Fintype.card_fin, finrank_euclideanSpace_fin]
  rw [ksCtxVec_orthonormal.linearIndependent.span_eq_top_of_card_eq_finrank hcard]

/-- `ksContextBasis i` is the `i`-th normalised Cabello ray. -/
lemma ksContextBasis_apply (j : Fin 4) : ksContextBasis j = ksCtxVec j := by
  unfold ksContextBasis
  rw [OrthonormalBasis.coe_mk]

/-! ### The headline: Cabello-context Born weights as FS typicality volumes -/

/-- **Kochen-Specker (Cabello-18) contextual Born weights as Kähler volumes.** For i.i.d.
trials drawing microstates from the Fubini-Study typicality measure on the ontic `Σ = ℂℙ³`,
the empirical frequencies of the four barycentric Born regions (carved in the rotated frame
`ksContextBasis.repr ψ`) converge, on a single almost-sure event, to the context-dependent
Born weights `‖⟨ksContextBasis i, ψ⟩‖²` of measuring the unit preparation `ψ` in the
representative Cabello context `cabelloBasis 0`.

A direct instantiation of `context_born_frequency_volume` at `M = 3`, the representative
Cabello orthonormal frame `ksContextBasis`, and an arbitrary unit `ψ` — carving-free,
Gleason-free, unconditional (every unit preparation, eigenstates of the context included), no
new mathematics. The other 8 Cabello contexts (`cabelloBasis 1 … 8`) are identical
instantiations at their orthonormal frames; their per-context orthogonality is already
certified by `cabello_pairwise_orthogonal_in_basis`.

This grounds each Cabello context's rank-1 outcome weight — the context-dependent weights that
no non-contextual hidden-variable assignment can jointly reproduce
(`ks_no_value_assignment_cabello18`) — as a genuine Fubini-Study typicality volume on the
*fixed* ontic `Σ`. The CSD reading of contextuality: context-dependence is *which projective
carving of the one Σ* is measured, not a hidden variable. -/
theorem ks18_context_born_frequency_volume
    (p₀ : CPN 4) (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ‖ψ‖ = 1)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 4) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ i : Fin 4,
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' bornRegion (ksContextBasis.repr ψ) (repr_ne_zero ksContextBasis ψ hψ) i)
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : Fin 4,
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator
                ((X k) ⁻¹' bornRegion (ksContextBasis.repr ψ)
                  (repr_ne_zero ksContextBasis ψ hψ) i)
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (ksContextBasis i) ψ‖ ^ 2)) :=
  context_born_frequency_volume p₀ ksContextBasis ψ hψ X hX hlaw hindep

/-- `ks18_context_born_frequency_volume` on the canonical i.i.d. Fubini-Study trial witness
(`fsTrialMeasure` / `fsTrial`): the trial bundle is discharged, so the hypothesis set is
Lean-inhabited, not merely classically satisfiable. Direct instantiation of
`context_born_frequency_volume_canonical`. -/
theorem ks18_context_born_frequency_volume_canonical
    (p₀ : CPN 4) (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ‖ψ‖ = 1) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀, ∀ i : Fin 4,
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator
                ((fsTrial 4 k) ⁻¹' bornRegion (ksContextBasis.repr ψ)
                  (repr_ne_zero ksContextBasis ψ hψ) i)
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (ksContextBasis i) ψ‖ ^ 2)) :=
  context_born_frequency_volume_canonical p₀ ksContextBasis ψ hψ

end KochenSpecker
end CSDBridge
end Empirical
end CSD
