import CsdLean4.LF4.POVMDilation
import CsdLean4.LF4.BornFrequencyN

/-!
# LF4: POVM Born weight as a dilated rank-1 block sum (P.3a)

**Category:** 3-Local (LF4 POVM volume reading).

This is **P.3a** of the POVM tranche (`specs/povm-plan.md`): the block
decomposition that turns the Naimark Born transfer (`born_transfer`, P.2) into a
sum of **dilated computational-basis (rank-1) Born weights**:

```
pᵢ(ψ)  =  ⟨ψ, Eᵢ ψ⟩  =  ⟨Vψ, Πᵢ (Vψ)⟩  =  ∑ₙ ‖⟨e_{(n,i)}, Vψ⟩‖².
```

The ancilla-`i` projector `Πᵢ = I_N ⊗ |i⟩⟨i|` is a *coarse* (rank-`N`) outcome —
the union of the `N` computational-basis cells `{(n, i) : n}` on the dilated
space. So the POVM weight is the sum, over that block, of the dilated rank-1
Born weights, each of which the achieved general-`N` result reads as a
Fubini–Study volume on `ℂℙ^{N·|ι|−1}` (the FS-volume identification, P.3b, sits
on top of this via the `Fin N × ι ≃ Fin (N·|ι|)` reindex).
-/

open Matrix Matrix.UnitaryGroup MeasureTheory
open scoped Kronecker LinearAlgebra.Projectivization

namespace CSD
namespace LF4

open CSD.LF2

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `‖⟨e_p, w⟩‖² = ‖w_p‖²` on the dilated `EuclideanSpace ℂ (Fin N × ι)`. -/
private lemma normSq_inner_single (w : EuclideanSpace ℂ (Fin N × ι)) (p : Fin N × ι) :
    ‖inner ℂ (EuclideanSpace.single p (1 : ℂ)) w‖ ^ 2 = ‖w.ofLp p‖ ^ 2 := by
  rw [EuclideanSpace.inner_single_left, map_one, one_mul]

/-- **Action of the ancilla-`i` block projector on a coordinate.** `Πᵢ` keeps the
components whose ancilla index is `i` and zeroes the rest:
`(Πᵢ v)_{(n,j)} = if j = i then v_{(n,i)} else 0`. -/
lemma blockProj_mulVec (i : ι) (v : Fin N × ι → ℂ) (n : Fin N) (j : ι) :
    (blockProj N i *ᵥ v) (n, j) = if j = i then v (n, i) else 0 := by
  simp only [blockProj, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single n]
  · rcases eq_or_ne j i with hj | hj
    · subst hj
      rw [Finset.sum_eq_single j]
      · rw [Matrix.single_apply_same]; simp
      · intro k _ hk
        rw [Matrix.single_apply_of_col_ne _ _ (Ne.symm hk)]; ring
      · intro h; exact absurd (Finset.mem_univ j) h
    · simp only [if_neg hj]
      apply Finset.sum_eq_zero
      intro k _
      rw [Matrix.single_apply_of_row_ne (Ne.symm hj)]; ring
  · intro m _ hm
    simp only [if_neg (Ne.symm hm), zero_mul, Finset.sum_const_zero]
  · intro h; exact absurd (Finset.mem_univ n) h

/-- **Block decomposition.** The projective Born weight of `w` against the
ancilla-`i` projector is the sum of the rank-1 computational-basis Born weights
over the `i`-th block:
`re ⟨w, Πᵢ w⟩ = ∑ₙ ‖⟨e_{(n,i)}, w⟩‖²`. -/
lemma blockProj_born_eq_block_sum (i : ι) (w : EuclideanSpace ℂ (Fin N × ι)) :
    RCLike.re (inner ℂ w (Matrix.toEuclideanLin (blockProj N i) w))
      = ∑ n : Fin N, ‖inner ℂ (EuclideanSpace.single ((n, i) : Fin N × ι) (1 : ℂ)) w‖ ^ 2 := by
  have hcomp : inner ℂ w (Matrix.toEuclideanLin (blockProj N i) w)
      = ∑ n : Fin N, w.ofLp (n, i) * star (w.ofLp (n, i)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin, dotProduct,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [Matrix.toLin'_apply, Pi.star_apply]
    rw [Finset.sum_eq_single i]
    · rw [blockProj_mulVec, if_pos rfl]
    · intro j _ hj; rw [blockProj_mulVec, if_neg hj, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hcomp, map_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [normSq_inner_single, ← starRingEnd_apply, RCLike.mul_conj]
  norm_cast

/-- **POVM Born weight as a dilated rank-1 block sum (P.3a).** Composing the
Naimark Born transfer with the block decomposition: the POVM weight `pᵢ(ψ)` is the
sum, over the `i`-th ancilla block `{(n, i) : n}`, of the dilated
computational-basis Born weights of `Vψ`. Each summand is a rank-1 projective Born
weight on `ℂℙ^{N·|ι|−1}`, read as a Fubini–Study volume by the achieved
general-`N` result (P.3b). -/
theorem povm_born_eq_block_sum (P : POVM N ι) (D : NaimarkDilation P)
    (ψ : EuclideanSpace ℂ (Fin N)) (i : ι) :
    P.weight ψ i
      = ∑ n : Fin N,
          ‖inner ℂ (EuclideanSpace.single ((n, i) : Fin N × ι) (1 : ℂ))
            (Matrix.toEuclideanLin D.V ψ)‖ ^ 2 := by
  rw [D.born_transfer P ψ i, blockProj_born_eq_block_sum]

/-- **POVM Born weight as a sum of Fubini–Study volumes (P.3b).** Given a reindex
`e : Fin N × ι ≃ Fin (M+1)` of the dilated index (concretely `finProdFinEquiv`
after `ι ≃ Fin |ι|`, so `N·|ι| = M+1`) and the induced reindex isometry
`L = piLpCongrLeft e`, write `ψ' = L (Vψ)` for the reindexed dilated state on
`ℂℙ^M`. When `ψ'` is a unit, fully-generic preparation (all `M+1` amplitudes
nonzero — the dilation genericity condition), the POVM Born weight is the sum,
over the `i`-th ancilla block, of the **genuine Fubini–Study typicality volumes**
of the dilated barycentric cells:

```
pᵢ(ψ)  =  ∑ₙ  μ_FS( bornRegion ψ' (e (n, i)) ).
```

This is the headline of the ontic POVM reading: the (non-projective) POVM Born
weight is a Kähler volume on the dilated configuration space `Σ' = ℂℙ^{N·|ι|−1}`,
carving-free and **Gleason-free** — it composes the Naimark Born transfer with the
achieved general-`N` Born = FS-volume result (`bornRegion_fs_measure`), no
`busch_effect_gleason`. Honest scope: the dilation `V` is supplied (P.2), so this
relocates POVM Born onto a larger posited configuration space (system + ancilla);
genericity (`hpos`) excludes dilated states with a vanishing amplitude. -/
theorem povm_born_eq_dilated_volume {M : ℕ} (P : POVM N ι) (D : NaimarkDilation P)
    (ψ : EuclideanSpace ℂ (Fin N)) (i : ι)
    (e : (Fin N × ι) ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (hnorm : ‖LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (Matrix.toEuclideanLin D.V ψ)‖ = 1)
    (hpos : ∀ j : Fin (M + 1),
        0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ))
          (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (Matrix.toEuclideanLin D.V ψ))‖ ^ 2) :
    P.weight ψ i
      = ∑ n : Fin N,
          (fubiniStudyMeasure p₀
            (bornRegion (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (Matrix.toEuclideanLin D.V ψ))
              (by intro h; rw [h, norm_zero] at hnorm; exact one_ne_zero hnorm.symm)
              (e (n, i)))).toReal := by
  set ψ' := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (Matrix.toEuclideanLin D.V ψ) with hψ'
  have hψ'0 : ψ' ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; exact one_ne_zero hnorm.symm
  -- The reindex isometry maps the dilated cell `(n, i)` to the coordinate `e (n, i)`,
  -- preserving the Born weight.
  have hinner : ∀ n : Fin N,
      ‖inner ℂ (EuclideanSpace.single (e (n, i)) (1 : ℂ)) ψ'‖ ^ 2
        = ‖inner ℂ (EuclideanSpace.single ((n, i) : Fin N × ι) (1 : ℂ))
            (Matrix.toEuclideanLin D.V ψ)‖ ^ 2 := by
    intro n
    rw [hψ', ← EuclideanSpace.piLpCongrLeft_single e (n, i) (1 : ℂ),
      LinearIsometryEquiv.inner_map_map]
  rw [povm_born_eq_block_sum P D ψ i]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [bornRegion_fs_measure p₀ ψ' hψ'0 hnorm hpos (e (n, i)), hinner n]

end LF4
end CSD
