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

open Matrix Matrix.UnitaryGroup MeasureTheory ProbabilityTheory Filter
open scoped Kronecker LinearAlgebra.Projectivization

namespace CSD
namespace LF4

open CSD.LF2

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The reindex isometry preserves computational-basis Born weights.** For the
`piLpCongrLeft e` reindex isometry `L`, `‖⟨e_{e p}, L w⟩‖² = ‖⟨e_p, w⟩‖²` — the cell
`p` maps to the coordinate `e p` with the Born weight unchanged. -/
lemma piLpCongrLeft_inner_single_sq {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ] (e : α ≃ κ) (w : EuclideanSpace ℂ α) (p : α) :
    ‖inner ℂ (EuclideanSpace.single (e p) (1 : ℂ))
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e w)‖ ^ 2
      = ‖inner ℂ (EuclideanSpace.single p (1 : ℂ)) w‖ ^ 2 := by
  rw [← EuclideanSpace.piLpCongrLeft_single e p (1 : ℂ), LinearIsometryEquiv.inner_map_map]

/-- `‖⟨e_p, w⟩‖² = ‖w_p‖²` on the dilated `EuclideanSpace ℂ (Fin N × ι)`. -/
private lemma normSq_inner_single (w : EuclideanSpace ℂ (Fin N × ι)) (p : Fin N × ι) :
    ‖inner ℂ (EuclideanSpace.single p (1 : ℂ)) w‖ ^ 2 = ‖w.ofLp p‖ ^ 2 := by
  rw [EuclideanSpace.inner_single_left, map_one, one_mul]

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
genericity (`hpos`) excludes dilated states with a vanishing amplitude.
An hpos-free form is available: `povm_born_eq_dilated_volume_uncond`
(`BornRegionUncond.lean`). -/
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

/-- **POVM empirical frequencies as a dilated Kähler-volume convergence (P.4).**
The observable capstone. For i.i.d. trials drawing microstates from the
Fubini–Study typicality measure on the dilated ontic `Σ' = ℂℙ^{N·|ι|−1}` (the
reindexed dilated state `ψ' = L (Vψ)` being a unit, fully-generic preparation), the
empirical frequency of the `i`-th POVM outcome — the sum, over the `i`-th ancilla
block, of the dilated barycentric-cell frequencies — converges, on a single
almost-sure event, to the POVM Born weight `pᵢ(ψ)`.

Composes the general-`N` per-cell convergence `born_frequency_convergence_N` (joint
a.s. over all `M+1` cells) with the finite block sum (`tendsto_finsetSum`), landing
the limit on `pᵢ(ψ)` via the P.3a block decomposition. Carving-free, Gleason-free —
the empirical → Born chain for a general (non-projective) POVM runs entirely on the
ontic FS-volume derivation, no `busch_effect_gleason`. Honest scope: dilation
supplied; the block frequency is the sum of the cells' frequencies (the cells are
the rank-1 dilated outcomes), and genericity (`hpos`) is assumed.
An hpos-free form is available: `povm_born_frequency_volume_uncond`
(`BornRegionUncond.lean`). -/
theorem povm_born_frequency_volume {M : ℕ} (P : POVM N ι) (D : NaimarkDilation P)
    (ψ : EuclideanSpace ℂ (Fin N)) (e : (Fin N × ι) ≃ Fin (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (Matrix.toEuclideanLin D.V ψ))
    (hψ'0 : ψ' ≠ 0) (hnorm : ‖ψ'‖ = 1)
    (hpos : ∀ j : Fin (M + 1), 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ'‖ ^ 2)
    (p₀ : CPN (M + 1))
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ j : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ' hψ'0 j) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : ι,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin N,
            (∑ k ∈ Finset.range m,
                Set.indicator ((X k) ⁻¹' bornRegion ψ' hψ'0 (e (n, i))) (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds (P.weight ψ i)) := by
  filter_upwards [born_frequency_convergence_N p₀ ψ' hψ'0 hnorm hpos X hX hlaw hindep]
    with ω hω
  intro i
  have hlim := tendsto_finsetSum (Finset.univ : Finset (Fin N))
    (fun n (_ : n ∈ Finset.univ) => hω (e (n, i)))
  rwa [show (∑ n : Fin N, ‖inner ℂ (EuclideanSpace.single (e (n, i)) (1 : ℂ)) ψ'‖ ^ 2)
        = P.weight ψ i from by
      rw [povm_born_eq_block_sum P D ψ i, hψ'eq]
      exact Finset.sum_congr rfl (fun n _ => piLpCongrLeft_inner_single_sq e _ (n, i))] at hlim

end LF4
end CSD
