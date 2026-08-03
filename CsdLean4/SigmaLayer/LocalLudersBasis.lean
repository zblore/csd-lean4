/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.LocalLuders

/-!
# SigmaLayer/LocalLudersBasis: local measurements in every basis (brick 3a)

**Category:** dynamical measurement — dynamical no-signalling (A6, dynamical form), brick 3a:
the local Lüders map for an **arbitrary orthonormal basis** on the measured factor.

`LocalLuders` handled the computational-basis marker measurement. The eraser's *erase* arm
measures the marker in the `±` basis — and rather than hand-build those two projectors, this
module generalises: for any orthonormal basis `g` of the `B` factor,

  `(localProjOn g j v)(a, k) = ⟪gⱼ, v(a,·)⟫ · gⱼ(k)`

is the local projector `1_A ⊗ |gⱼ⟩⟨gⱼ|`. The computational case is recovered exactly
(`localProjOn_basisFun`). Everything brick 1 proved survives, with Parseval doing the work
the `ite`-collapse did before:

* the projectors resolve the identity (`sum_localProjOn` — basis expansion, slice by slice);
* the Born weights resolve the norm (`sum_normSq_localProjOn` — Parseval per slice);
* ★★ **marginal invariance in every basis** (`reduceA_localLudersOn_mixture`): the
  Born-weighted mixture of the post-measurement `A`-marginals equals the pre-measurement
  `A`-marginal, whatever basis `B`'s apparatus measures in. Alice cannot learn Bob's basis
  *choice* any more than his outcome — the statics core of no-signalling, now
  basis-universal.

⚠️ **Honest scope.** As in brick 1, this is the statics layer, in the states-and-weights
vocabulary that `BlockLudersObligation` names and the join witness inhabits dynamically; the
rotated block structure enters the dynamical machinery through the brick-2 index bridge
composed with the local unitary rotating `g` to the computational basis (the `RotatedSwap`
idiom) — not re-proved here. Brick 3b instantiates the `2 ⊗ 2` eraser: the computational
marker measurement (which-path, no fringe) and the `±` marker measurement (fringes restored,
the `QuantumEraserVolume` statistics).

## References

`specs/BACKLOG.md` (the dynamical no-signalling + eraser row); `specs/future-work.md`.
Reused corpus API: `localProjB`/`vecOuter`/`reduceA_mk` (`SigmaLayer/LocalLuders.lean`),
`normSq_eq_sum_mul_star` (`SigmaLayer/OnticMarginals.lean`),
`OrthonormalBasis.sum_inner_mul_inner` + `OrthonormalBasis.sum_repr'` (Mathlib).
-/

@[expose] public section

open Matrix
open scoped LinearAlgebra.Projectivization

namespace CSD.RecordLayer

variable {nA nB : ℕ}

/-! ### The B-slice and the rotated local projector -/

/-- The `B`-slice of a composite vector at `A`-index `a`. -/
noncomputable def sliceB (v : EuclideanSpace ℂ (Fin nA × Fin nB)) (a : Fin nA) :
    EuclideanSpace ℂ (Fin nB) :=
  WithLp.toLp 2 fun k => v (a, k)

@[simp] lemma sliceB_apply (v : EuclideanSpace ℂ (Fin nA × Fin nB)) (a : Fin nA)
    (k : Fin nB) : sliceB v a k = v (a, k) := rfl

/-- The local projector `1_A ⊗ |gⱼ⟩⟨gⱼ|` for an arbitrary orthonormal basis `g` of the `B`
factor: `(Pⱼ v)(a, k) = ⟪gⱼ, v(a,·)⟫ · gⱼ(k)`. -/
noncomputable def localProjOn (g : OrthonormalBasis (Fin nB) ℂ (EuclideanSpace ℂ (Fin nB)))
    (j : Fin nB) (v : EuclideanSpace ℂ (Fin nA × Fin nB)) :
    EuclideanSpace ℂ (Fin nA × Fin nB) :=
  WithLp.toLp 2 fun ak => inner ℂ (g j) (sliceB v ak.1) * g j ak.2

@[simp] lemma localProjOn_apply (g : OrthonormalBasis (Fin nB) ℂ (EuclideanSpace ℂ (Fin nB)))
    (j : Fin nB) (v : EuclideanSpace ℂ (Fin nA × Fin nB)) (ak : Fin nA × Fin nB) :
    localProjOn g j v ak = inner ℂ (g j) (sliceB v ak.1) * g j ak.2 := rfl

/-- The computational basis recovers `localProjB`. -/
theorem localProjOn_basisFun (j : Fin nB) (v : EuclideanSpace ℂ (Fin nA × Fin nB)) :
    localProjOn (EuclideanSpace.basisFun (Fin nB) ℂ) j v = localProjB j v := by
  apply PiLp.ext
  intro ak
  rw [localProjOn_apply, localProjB_apply]
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  simp only [map_one, one_mul, PiLp.single_apply]
  rcases eq_or_ne ak.2 j with h | h
  · rw [if_pos h, if_pos h, mul_one]
    show v (ak.1, j) = v ak
    rw [← h]
  · rw [if_neg h, if_neg h, mul_zero]

/-! ### Identity and norm resolution -/

/-- Parseval for a slice: the squared inner products against an orthonormal basis resolve
the squared norm. -/
lemma sum_normSq_inner_orthonormal (g : OrthonormalBasis (Fin nB) ℂ (EuclideanSpace ℂ (Fin nB)))
    (x : EuclideanSpace ℂ (Fin nB)) :
    ∑ j, ‖(inner ℂ (g j) x : ℂ)‖ ^ 2 = ‖x‖ ^ 2 := by
  have h := g.sum_inner_mul_inner x x
  have hterm : ∀ j, (inner ℂ x (g j) : ℂ) * inner ℂ (g j) x
      = ((‖(inner ℂ (g j) x : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    calc (inner ℂ x (g j) : ℂ) * inner ℂ (g j) x
        = (starRingEnd ℂ) (inner ℂ (g j) x) * inner ℂ (g j) x := by
          rw [← inner_conj_symm]
      _ = ((‖(inner ℂ (g j) x : ℂ)‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' _
      _ = _ := by push_cast; ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), inner_self_eq_norm_sq_to_K] at h
  apply Complex.ofReal_injective
  push_cast at h ⊢
  exact h

/-- **The rotated projectors resolve the identity** — basis expansion, slice by slice. -/
lemma sum_localProjOn (g : OrthonormalBasis (Fin nB) ℂ (EuclideanSpace ℂ (Fin nB)))
    (v : EuclideanSpace ℂ (Fin nA × Fin nB)) :
    ∑ j, localProjOn g j v = v := by
  apply PiLp.ext
  intro ak
  have hsum : (∑ j, localProjOn g j v) ak = ∑ j, localProjOn g j v ak :=
    map_sum (EuclideanSpace.proj (𝕜 := ℂ) ak) (fun j => localProjOn g j v) Finset.univ
  have hsum2 : (∑ j, (inner ℂ (g j) (sliceB v ak.1) : ℂ) • g j) ak.2
      = ∑ j, ((inner ℂ (g j) (sliceB v ak.1) : ℂ) • (g j : EuclideanSpace ℂ (Fin nB))) ak.2 :=
    map_sum (EuclideanSpace.proj (𝕜 := ℂ) ak.2) _ Finset.univ
  have hrepr := congrArg (fun w : EuclideanSpace ℂ (Fin nB) => w ak.2)
    (g.sum_repr' (sliceB v ak.1))
  simp only at hrepr
  rw [hsum]
  simp only [localProjOn_apply]
  have hsm : ∀ j, (inner ℂ (g j) (sliceB v ak.1) : ℂ) * g j ak.2
      = ((inner ℂ (g j) (sliceB v ak.1) : ℂ) • (g j : EuclideanSpace ℂ (Fin nB))) ak.2 :=
    fun j => rfl
  rw [Finset.sum_congr rfl (fun j _ => hsm j), ← hsum2, hrepr]
  rfl

/-- **The Born weights of the rotated outcomes resolve the norm** — Parseval per slice. -/
lemma sum_normSq_localProjOn (g : OrthonormalBasis (Fin nB) ℂ (EuclideanSpace ℂ (Fin nB)))
    (v : EuclideanSpace ℂ (Fin nA × Fin nB)) :
    ∑ j, ‖localProjOn g j v‖ ^ 2 = ‖v‖ ^ 2 := by
  have hnormAB : ∀ w : EuclideanSpace ℂ (Fin nA × Fin nB), ‖w‖ ^ 2 = ∑ ak, ‖w ak‖ ^ 2 := by
    intro w
    rw [EuclideanSpace.norm_eq]
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hnormB : ∀ w : EuclideanSpace ℂ (Fin nB), ‖w‖ ^ 2 = ∑ k, ‖w k‖ ^ 2 := by
    intro w
    rw [EuclideanSpace.norm_eq]
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hg1 : ∀ j, ∑ k, ‖(g j : EuclideanSpace ℂ (Fin nB)) k‖ ^ 2 = 1 := by
    intro j
    rw [← hnormB, g.orthonormal.1 j, one_pow]
  calc ∑ j, ‖localProjOn g j v‖ ^ 2
      = ∑ j, ∑ a, ∑ k, ‖(inner ℂ (g j) (sliceB v a) : ℂ) * g j (a, k).2‖ ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hnormAB, Fintype.sum_prod_type]
        rfl
    _ = ∑ j, ∑ a, ‖(inner ℂ (g j) (sliceB v a) : ℂ)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
        simp only [norm_mul, mul_pow]
        rw [← Finset.mul_sum, hg1 j, mul_one]
    _ = ∑ a, ∑ j, ‖(inner ℂ (g j) (sliceB v a) : ℂ)‖ ^ 2 := Finset.sum_comm
    _ = ∑ a, ‖sliceB v a‖ ^ 2 :=
        Finset.sum_congr rfl fun a _ => sum_normSq_inner_orthonormal g _
    _ = ∑ a, ∑ k, ‖v (a, k)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hnormB]
        rfl
    _ = ‖v‖ ^ 2 := by rw [hnormAB, Fintype.sum_prod_type]

/-! ### The marginal-invariance identity, in every basis -/

/-- ★ **Tracing out `B` collapses the rotated Lüders sum** — Parseval where brick 1 had the
`ite`-collapse. -/
theorem traceRight_sum_vecOuter_localProjOn
    (g : OrthonormalBasis (Fin nB) ℂ (EuclideanSpace ℂ (Fin nB)))
    (v : EuclideanSpace ℂ (Fin nA × Fin nB)) :
    ∑ j, traceRight (vecOuter (localProjOn g j v)) = traceRight (vecOuter v) := by
  ext a a'
  rw [Matrix.sum_apply]
  simp only [traceRight_apply, vecOuter, Matrix.of_apply, localProjOn_apply]
  have hg1 : ∀ j, (∑ k, (g j : EuclideanSpace ℂ (Fin nB)) k
      * star ((g j : EuclideanSpace ℂ (Fin nB)) k)) = 1 := by
    intro j
    rw [← normSq_eq_sum_mul_star, g.orthonormal.1 j]
    norm_num
  have hstep : ∀ j, (∑ k, (inner ℂ (g j) (sliceB v a) : ℂ) * g j (a, k).2
      * star ((inner ℂ (g j) (sliceB v a') : ℂ) * g j (a', k).2))
      = (inner ℂ (g j) (sliceB v a) : ℂ) * star ((inner ℂ (g j) (sliceB v a') : ℂ)) := by
    intro j
    have hk : ∀ k : Fin nB, (inner ℂ (g j) (sliceB v a) : ℂ) * g j (a, k).2
        * star ((inner ℂ (g j) (sliceB v a') : ℂ) * g j (a', k).2)
        = ((inner ℂ (g j) (sliceB v a) : ℂ) * star ((inner ℂ (g j) (sliceB v a') : ℂ)))
          * ((g j : EuclideanSpace ℂ (Fin nB)) k
            * star ((g j : EuclideanSpace ℂ (Fin nB)) k)) := by
      intro k
      rw [star_mul']
      ring
    rw [Finset.sum_congr rfl fun k _ => hk k, ← Finset.mul_sum, hg1 j, mul_one]
  rw [Finset.sum_congr rfl fun j _ => hstep j]
  have hconj : ∀ j, star ((inner ℂ (g j) (sliceB v a') : ℂ))
      = inner ℂ (sliceB v a') (g j) := by
    intro j
    rw [show star ((inner ℂ (g j) (sliceB v a') : ℂ))
        = (starRingEnd ℂ) (inner ℂ (g j) (sliceB v a')) from rfl, inner_conj_symm]
  have hfinal : (∑ j, (inner ℂ (g j) (sliceB v a) : ℂ)
      * star ((inner ℂ (g j) (sliceB v a') : ℂ)))
      = inner ℂ (sliceB v a') (sliceB v a) := by
    rw [Finset.sum_congr rfl fun j _ => by rw [hconj j, mul_comm]]
    exact g.sum_inner_mul_inner (sliceB v a') (sliceB v a)
  rw [hfinal, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [RCLike.inner_apply, sliceB_apply]
  rw [Complex.star_def]

/-- ★★ **Dynamical no-signalling, in every measurement basis**: the Born-weighted mixture of
the post-measurement `A`-marginals of a local `B`-measurement in **any** orthonormal basis
equals the pre-measurement `A`-marginal. Alice cannot detect Bob's outcome *or his choice of
basis*. Zero-weight outcomes carry weight `0` — no positivity hypothesis. -/
theorem reduceA_localLudersOn_mixture
    (g : OrthonormalBasis (Fin nB) ℂ (EuclideanSpace ℂ (Fin nB)))
    (v : EuclideanSpace ℂ (Fin nA × Fin nB)) (hv : v ≠ 0) :
    (∑ j, (((‖localProjOn g j v‖ ^ 2 / ‖v‖ ^ 2 : ℝ)) : ℂ) •
        (if h : localProjOn g j v = 0 then 0
         else reduceA (Projectivization.mk ℂ (localProjOn g j v) h)))
      = reduceA (Projectivization.mk ℂ v hv) := by
  classical
  have hterm : ∀ j, (((‖localProjOn g j v‖ ^ 2 / ‖v‖ ^ 2 : ℝ)) : ℂ) •
      (if h : localProjOn g j v = 0 then 0
       else reduceA (Projectivization.mk ℂ (localProjOn g j v) h))
      = (((‖v‖ ^ 2 : ℝ) : ℂ))⁻¹ • traceRight (vecOuter (localProjOn g j v)) := by
    intro j
    by_cases h : localProjOn g j v = 0
    · rw [dif_pos h, smul_zero, h, vecOuter_zero, traceRight_zero, smul_zero]
    · rw [dif_neg h, reduceA_mk _ h, smul_smul]
      congr 1
      have hp : ((‖localProjOn g j v‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr h))
      rw [Complex.ofReal_div, mul_comm, ← mul_div_assoc, inv_mul_cancel₀ hp, one_div]
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.smul_sum,
    traceRight_sum_vecOuter_localProjOn, ← reduceA_mk v hv]

end CSD.RecordLayer
