/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.OnticMarginals

/-!
# SigmaLayer/LocalLuders: the local-measurement Lüders map and marginal invariance (brick 1)

**Category:** dynamical measurement — dynamical no-signalling (A6, dynamical form), brick 1
of the recorded route: *a local measurement on a composite is a block-degenerate measurement*.

A measurement of the `B` factor of `ℂ^{nA} ⊗ ℂ^{nB}` in the computational basis acts by the
**local projectors** `Pⱼ = 1_A ⊗ |fⱼ⟩⟨fⱼ|` — here in coordinate form (`localProjB`), with no
Kronecker plumbing, exactly as `OnticMarginals` handles local unitaries. The projectors are
idempotent, they resolve the identity (`sum_localProjB`), and their weights resolve the norm
(`sum_normSq_localProjB` — the Born weights of the `B`-outcomes).

★ **The marginal-invariance identity** (`reduceA_localLuders_mixture`): for every composite
preparation, the **Born-weighted mixture of the post-measurement `A`-marginals equals the
pre-measurement `A`-marginal**:

  `∑ⱼ pⱼ · reduceA [Pⱼ v] = reduceA [v]`,  `pⱼ = ‖Pⱼv‖²/‖v‖²`.

This is the statics core of **dynamical no-signalling**: whatever `B`'s apparatus does — and
the corpus's degenerate-Lüders machinery realises exactly this update dynamically — the `A`
side's density matrix, hence every `A`-side measurement statistic, is unchanged unless the
outcome is communicated. The unnormalised form (`traceRight_sum_vecOuter_localProjB`) is a
two-line entrywise computation: tracing out `B` collapses the projector sum before it can be
seen.

⚠️ **Honest scope.** (*2026-08-04: the propagator arrived in brick 2 —
`reduceA_blockLuders_mixture`, `SigmaLayer/LocalBlockBridge.lean`; the sentence below
scopes THIS module and stays true of it.*) This brick is statics: the Lüders mixture is
written down, not yet
produced by a propagator. Brick 2 wires it to the dynamical layer — the local `B`-block
structure `b = snd` under the `Fin (nA·nB) ≃ Fin nA × Fin nB` index bridge feeds
`BlockLudersObligation`, whose join witness (`joinWitness_blockLuders`) supplies the
ψ-dependent post-states dynamically; brick 3 is the eraser process (mark, then erase, as two
sequential measurements). Zero-weight outcomes are handled honestly: the `dite` branch is
multiplied by a vanishing weight, no positivity hypothesis is smuggled in.

## References

`specs/BACKLOG.md` (the dynamical no-signalling + eraser row); `specs/future-work.md`;
`specs/reconstruction-status.md` §2 (A6). Reused corpus API: `reduceA`/`rayDensity`
(`SigmaLayer/OnticMarginals.lean`), `traceRight` + linearity
(`Mathlib/LinearAlgebra/Matrix/PartialTrace.lean` staging); the operational-statics
counterparts are `csd_no_communication` (`Empirical/CSD/NoCommunication.lean`) and
`singlet_hasNoSignalling` (`SigmaLayer/CompositeAdapters.lean`).
-/

@[expose] public section

open Matrix
open scoped LinearAlgebra.Projectivization

namespace CSD.RecordLayer

variable {nA nB : ℕ}

/-! ### The local projectors -/

/-- The local `B`-projector for outcome `j`: `(Pⱼ v)(a, k) = v(a, k)` if `k = j`, else `0` —
the coordinate form of `1_A ⊗ |fⱼ⟩⟨fⱼ|`. -/
noncomputable def localProjB (j : Fin nB) (v : EuclideanSpace ℂ (Fin nA × Fin nB)) :
    EuclideanSpace ℂ (Fin nA × Fin nB) :=
  WithLp.toLp 2 fun ak => if ak.2 = j then v ak else 0

@[simp] lemma localProjB_apply (j : Fin nB) (v : EuclideanSpace ℂ (Fin nA × Fin nB))
    (ak : Fin nA × Fin nB) :
    localProjB j v ak = if ak.2 = j then v ak else 0 := rfl

lemma localProjB_idem (j : Fin nB) (v : EuclideanSpace ℂ (Fin nA × Fin nB)) :
    localProjB j (localProjB j v) = localProjB j v := by
  apply PiLp.ext
  intro ak
  by_cases h : ak.2 = j <;> simp [h]

/-- The local projectors resolve the identity. -/
lemma sum_localProjB (v : EuclideanSpace ℂ (Fin nA × Fin nB)) :
    ∑ j, localProjB j v = v := by
  apply PiLp.ext
  intro ak
  have hsum : (∑ j, localProjB j v) ak = ∑ j, localProjB j v ak :=
    map_sum (EuclideanSpace.proj (𝕜 := ℂ) ak) (fun j => localProjB j v) Finset.univ
  rw [hsum]
  simp [Finset.sum_ite_eq]

/-- **The Born weights of the `B`-outcomes resolve the norm**:
`∑ⱼ ‖Pⱼv‖² = ‖v‖²`. -/
lemma sum_normSq_localProjB (v : EuclideanSpace ℂ (Fin nA × Fin nB)) :
    ∑ j, ‖localProjB j v‖ ^ 2 = ‖v‖ ^ 2 := by
  have hnorm : ∀ w : EuclideanSpace ℂ (Fin nA × Fin nB), ‖w‖ ^ 2 = ∑ ak, ‖w ak‖ ^ 2 := by
    intro w
    rw [EuclideanSpace.norm_eq]
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  simp only [hnorm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ak _ => ?_
  simp [apply_ite (fun z : ℂ => ‖z‖ ^ 2), Finset.sum_ite_eq]

/-! ### The unnormalised outer product and the invariance identity -/

/-- The unnormalised outer product `v x · conj(v y)` — `rayDensity` before normalisation. -/
noncomputable def vecOuter (v : EuclideanSpace ℂ (Fin nA × Fin nB)) :
    Matrix (Fin nA × Fin nB) (Fin nA × Fin nB) ℂ :=
  Matrix.of fun x y => v x * star (v y)

lemma vecOuter_zero : vecOuter (0 : EuclideanSpace ℂ (Fin nA × Fin nB)) = 0 := by
  ext x y
  simp [vecOuter]

/-- ★ **Tracing out `B` collapses the local Lüders sum**:
`∑ⱼ tr_B(Pⱼv ⊗ (Pⱼv)*) = tr_B(v ⊗ v*)`. The entrywise computation at the heart of
dynamical no-signalling. -/
theorem traceRight_sum_vecOuter_localProjB (v : EuclideanSpace ℂ (Fin nA × Fin nB)) :
    ∑ j, traceRight (vecOuter (localProjB j v)) = traceRight (vecOuter v) := by
  ext a a'
  rw [Matrix.sum_apply]
  simp only [traceRight_apply, vecOuter, Matrix.of_apply, localProjB_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Finset.sum_ite_eq]

/-- `reduceA` at a representative: the normalised partial trace of the outer product. -/
lemma reduceA_mk (v : EuclideanSpace ℂ (Fin nA × Fin nB)) (hv : v ≠ 0) :
    reduceA (Projectivization.mk ℂ v hv)
      = (((‖v‖ ^ 2 : ℝ) : ℂ))⁻¹ • traceRight (vecOuter v) := by
  rw [reduceA, rayDensity_mk v hv, ← traceRight_smul]
  congr 1
  ext x y
  simp only [Matrix.of_apply, Matrix.smul_apply, vecOuter, smul_eq_mul]
  rw [div_eq_mul_inv, mul_comm]

/-- ★★ **Dynamical no-signalling, the statics core**: the Born-weighted mixture of the
post-measurement `A`-marginals of a local `B`-measurement equals the pre-measurement
`A`-marginal. Zero-weight outcomes carry weight `0` — no positivity hypothesis. -/
theorem reduceA_localLuders_mixture (v : EuclideanSpace ℂ (Fin nA × Fin nB)) (hv : v ≠ 0) :
    (∑ j, (((‖localProjB j v‖ ^ 2 / ‖v‖ ^ 2 : ℝ)) : ℂ) •
        (if h : localProjB j v = 0 then 0
         else reduceA (Projectivization.mk ℂ (localProjB j v) h)))
      = reduceA (Projectivization.mk ℂ v hv) := by
  classical
  have hv2 : ((‖v‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv))
  have hterm : ∀ j, (((‖localProjB j v‖ ^ 2 / ‖v‖ ^ 2 : ℝ)) : ℂ) •
      (if h : localProjB j v = 0 then 0
       else reduceA (Projectivization.mk ℂ (localProjB j v) h))
      = (((‖v‖ ^ 2 : ℝ) : ℂ))⁻¹ • traceRight (vecOuter (localProjB j v)) := by
    intro j
    by_cases h : localProjB j v = 0
    · rw [dif_pos h, smul_zero, h, vecOuter_zero, traceRight_zero, smul_zero]
    · rw [dif_neg h, reduceA_mk _ h, smul_smul]
      congr 1
      have hp : ((‖localProjB j v‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr h))
      rw [Complex.ofReal_div, mul_comm, ← mul_div_assoc, inv_mul_cancel₀ hp, one_div]
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.smul_sum,
    traceRight_sum_vecOuter_localProjB, ← reduceA_mk v hv]

end CSD.RecordLayer
