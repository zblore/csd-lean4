import CsdLean4.LF5.FlowBornFrequency
import CsdLean4.Mathlib.QuantumInfo.PartialTrace

/-!
# LF6-B.1: decoherence as coarse-graining over a conservative de-isolation flow

**Category:** 6-Local (the open-system / partial-trace stratum of D1 — the first
result beyond the global-beable account).

This is **LF6-B.1** of the open-system tier. In CSD, measurement is *de-isolation*:
a deterministic, FS-measure-preserving (conservative) flow couples the system to an
apparatus/environment (LF5/LF6-A). **Decoherence** is what happens when that
environment is *unmonitored*: coarse-grain (partial-trace) over the pointer, and
the system's reduced state loses its coherences. Irreversibility is then emergent —
coarse-graining over a *conservative* flow — not fundamental stochasticity. The
deterministic substrate has no intrinsic dissipation; the arrow comes entirely from
discarding the environment.

## The construction (clean path)

LF5's `vnDilationV` IS the Stinespring isometry of the measurement:
`V ψ = U_vN (ψ ⊗ a₀) = ∑ⱼ ψⱼ · (eⱼ ⊗ eⱼ)` (`vnDilationV_mulVec`: the system index
`j` is perfectly correlated with the pointer index `k`, amplitude `ψⱼ` only on the
diagonal `k = j`). Forming the dilated density `V |ψ⟩⟨ψ| Vᴴ` and tracing out the
pointer (`partialTraceRight`, the right/second `Fin N` factor) gives

```
decohereReduced ψ  =  partialTraceRight (V |ψ⟩⟨ψ| Vᴴ)  =  ∑ⱼ ‖⟨eⱼ, ψ⟩‖² • |eⱼ⟩⟨eⱼ|,
```

the Born-weighted **diagonal** mixture. The off-diagonal coherences vanish because
`⟨j| ρ_red |k⟩ = ψⱼ ψ̄ₖ · ⟨k|j⟩_ptr = ψⱼ ψ̄ₖ · δⱼₖ = 0` for `j ≠ k`. That is
decoherence, computed (not asserted) from `partialTraceRight_apply` plus the
correlated structure `V *ᵥ ψ`.

## Deliverables

- `decohereReduced` — the system's reduced state after de-isolation + pointer trace.
- `decoherence_dephases` (HEADLINE) — `decohereReduced ψ = ∑ⱼ ‖⟨eⱼ,ψ⟩‖² • |eⱼ⟩⟨eⱼ|`,
  every `ψ`. Genuinely computes the partial trace.
- `decoherence_offdiagonal_vanish` — explicit `(decohereReduced ψ) i i' = 0` for
  `i ≠ i'` (coherences gone).
- `decoherence_diagonal_born` — `(decohereReduced ψ) i i = ‖⟨eᵢ,ψ⟩‖²` (Born weights).
- `decoherence_diagonal_eq_pointer_volume` — TIES the decohered diagonal weight to the
  LF5/LF6 pointer-block **Fubini–Study volumes** (`vnDilation_pointer_volume`): the
  decohered weights ARE the FS typicality volumes (Born = FS-volume imported from the
  DH engine one layer down, Gleason-free, not re-derived).
- `deisolation_conservative` — the de-isolation `V` is an isometry `Vᴴ V = 1`
  (`vnDilationV_isom`): conservative on the joint, dissipative only on the marginal.
- `decoherence_capstone` — the four headline facts + conservativity.

## Honest scope

This is the **reduced-density-operator** level of decoherence (a standard QM-validity
object); the CSD increment is the *conservative-flow-coarse-graining reading*:
irreversibility = partial-trace over an isometric (measure-preserving) de-isolation,
no fundamental noise. The Born weights are **imported** as FS typicality volumes
(LF6-A / the moment-map / Duistermaat–Heckman cluster), not postulated and not
re-derived here.

**Explicitly DEFERRED** (not in this tranche): the continuous-time Lindblad /
T₁–T₂ semigroup; the system-marginal FS-volume-**drift** geometry (the open
symplectic drift as a measure statement on Σ); the purity/entropy-increase reading
(`Tr(ρ_red²) < 1`, deliverable 7). **Residue: A5** (the sector / FS-typicality law
is posited, reducing to D1).

All exports are foundational-triple-only (the partial-trace and dilation machinery
are measure-theoretic / linear-algebraic, off `busch_effect_gleason`).
-/

open MeasureTheory Matrix Matrix.UnitaryGroup QuantumInfo
open scoped ENNReal LinearAlgebra.Projectivization

namespace CSD
namespace LF6

open CSD.LF2 CSD.LF4 CSD.LF5

variable {N : ℕ} [NeZero N]

/-! ### Scalar bridge -/

/-- `z · z̄ = (‖z‖ : ℂ)²` for a complex scalar. Bridges the diagonal density entry
`ψⱼ · star ψⱼ` to the Born weight `‖ψⱼ‖²`. -/
private lemma mul_star_eq_normSq (z : ℂ) : z * star z = ((‖z‖ : ℂ)) ^ 2 := by
  rw [← starRingEnd_apply]
  exact RCLike.mul_conj z

/-! ### The dilated density and its right partial trace -/

/-- **The dilated measurement density `V |ψ⟩⟨ψ| Vᴴ` as a rank-1 outer product of the
correlated post-flow vector.** Using `M · vecMulVec x y = vecMulVec (M *ᵥ x) y` and
`vecMulVec x y · M = vecMulVec x (y ᵥ* M)`, the dilated density collapses to
`vecMulVec c (star c)` with `c = V *ᵥ ψ` the correlated state `∑ⱼ ψⱼ (eⱼ ⊗ eⱼ)`. -/
lemma vnDilationV_conj_outerProduct (ψ : EuclideanSpace ℂ (Fin N)) :
    vnDilationV N * outerProduct ψ * (vnDilationV N)ᴴ
      = Matrix.vecMulVec (vnDilationV N *ᵥ (fun i => ψ i))
          (fun q => star ((vnDilationV N *ᵥ (fun i => ψ i)) q)) := by
  rw [outerProduct, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 1
  funext q
  simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    star_sum, star_mul']
  exact Finset.sum_congr rfl fun n _ => by rw [mul_comm]

/-- **The system's reduced state after de-isolation + unmonitored-environment trace.**
`decohereReduced ψ := partialTraceRight (V |ψ⟩⟨ψ| Vᴴ)`, with `V = vnDilationV N` the
LF5 de-isolation isometry and the right (second `Fin N`) factor the pointer/environment
traced out. -/
noncomputable def decohereReduced (ψ : EuclideanSpace ℂ (Fin N)) : Matrix (Fin N) (Fin N) ℂ :=
  partialTraceRight (vnDilationV N * outerProduct ψ * (vnDilationV N)ᴴ)

/-- **The reduced-state entry formula (the core computation).** Tracing the pointer
out of the correlated dilated density leaves only the diagonal:
`(decohereReduced ψ) i i' = if i = i' then ψᵢ · star ψᵢ else 0`. The off-diagonal
cells are killed by the pointer δ. -/
lemma decohereReduced_apply (ψ : EuclideanSpace ℂ (Fin N)) (i i' : Fin N) :
    decohereReduced ψ i i' = if i = i' then ψ i * star (ψ i) else 0 := by
  rw [decohereReduced, vnDilationV_conj_outerProduct, partialTraceRight_apply]
  simp only [Matrix.vecMulVec_apply]
  have hc : ∀ a k : Fin N,
      (vnDilationV N *ᵥ (fun i => ψ i)) (a, k) = if k = a then ψ a else 0 :=
    fun a k => vnDilationV_mulVec (fun i => ψ i) a k
  simp only [hc]
  by_cases h : i = i'
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single i]
    · simp
    · intro k _ hk; rw [if_neg hk, zero_mul]
    · intro hni; exact absurd (Finset.mem_univ i) hni
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro k _
    rcases eq_or_ne k i with hk | hk
    · subst hk; rw [if_neg h, star_zero, mul_zero]
    · rw [if_neg hk, zero_mul]

/-! ### Off-diagonal vanishing (coherences gone) -/

/-- **The coherences vanish.** For `i ≠ i'` the reduced-state off-diagonal entry is
exactly `0`: the unmonitored pointer trace dephases the system. -/
theorem decoherence_offdiagonal_vanish (ψ : EuclideanSpace ℂ (Fin N)) {i i' : Fin N}
    (h : i ≠ i') : decohereReduced ψ i i' = 0 := by
  rw [decohereReduced_apply, if_neg h]

/-! ### Diagonal weights are the Born weights -/

/-- **The diagonal entries are the Born weights.** `(decohereReduced ψ) i i = ‖⟨eᵢ,ψ⟩‖²`. -/
theorem decoherence_diagonal_born (ψ : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    decohereReduced ψ i i
      = ((‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [decohereReduced_apply, if_pos rfl, mul_star_eq_normSq,
    EuclideanSpace.inner_single_left, map_one, one_mul]
  push_cast
  ring

/-! ### The headline: dephasing to the Born-weighted diagonal mixture -/

/-- **HEADLINE (LF6-B.1): decoherence dephases the system to the Born mixture.**
The de-isolation `V` followed by tracing out the unmonitored pointer yields the
Born-weighted diagonal mixture
`decohereReduced ψ = ∑ⱼ ‖⟨eⱼ,ψ⟩‖² • |eⱼ⟩⟨eⱼ|`, for every preparation `ψ`. Proved by
computing `partialTraceRight (V |ψ⟩⟨ψ| Vᴴ)` entrywise (`decohereReduced_apply`), not
asserted: the off-diagonal coherences are killed by the pointer δ and the diagonal
carries the Born weight `‖ψⱼ‖²`. -/
theorem decoherence_dephases (ψ : EuclideanSpace ℂ (Fin N)) :
    decohereReduced ψ
      = ∑ j : Fin N,
          (‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2 : ℝ)
            • outerProduct (EuclideanSpace.single j (1 : ℂ)) := by
  ext i i'
  rw [decohereReduced_apply, Matrix.sum_apply]
  simp only [Matrix.smul_apply, outerProduct_single, Matrix.single_apply]
  by_cases h : i = i'
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single i]
    · rw [if_pos ⟨rfl, rfl⟩, Complex.real_smul, mul_one, mul_star_eq_normSq,
        EuclideanSpace.inner_single_left, map_one, one_mul]
      push_cast; ring
    · intro j _ hj; rw [if_neg (fun hc => hj hc.1)]; exact smul_zero _
    · intro hni; exact absurd (Finset.mem_univ i) hni
  · rw [if_neg h]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    rw [if_neg (fun hc => h (hc.1.symm.trans hc.2))]; exact smul_zero _

/-! ### The decohered weights ARE the FS typicality volumes -/

/-- **The decohered diagonal weight = the LF5/LF6 pointer-block Fubini–Study volume.**
Ties the dephased mixture's Born weight `‖⟨eᵢ,ψ⟩‖²` to the de-isolation flow's
context-fixed pointer-block FS volume (`vnDilation_pointer_volume`). So the weights
into which the system decoheres are exactly the FS *typicality* volumes carved by the
measurement-flow dynamics — Born = FS-volume imported from the moment-map /
Duistermaat–Heckman cluster (Gleason-free), not postulated. -/
theorem decoherence_diagonal_eq_pointer_volume {M : ℕ}
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1)
    (e : (Fin N × Fin N) ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV N) ψ))
    (hψ'0 : ψ' ≠ 0) (i : Fin N) :
    decohereReduced ψ i i
      = ((∑ n : Fin N,
            (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, i)))).toReal : ℝ) : ℂ) := by
  rw [decoherence_diagonal_born, vnDilation_pointer_volume ψ hψ e p₀ ψ' hψ'eq hψ'0 i]

/-! ### Conservativity of the de-isolation -/

/-- **The de-isolation is conservative (an isometry).** `Vᴴ V = 1` (`vnDilationV_isom`):
the joint system-apparatus de-isolation is norm-preserving / measure-preserving. The
irreversibility in `decoherence_dephases` / `decoherence_offdiagonal_vanish` is
therefore *purely the env-trace coarse-graining*, not a non-conservative flow:
conservative on the joint, dissipative only on the marginal. -/
theorem deisolation_conservative : (vnDilationV N)ᴴ * vnDilationV N = 1 :=
  vnDilationV_isom

/-! ### Capstone -/

/-- **The LF6-B.1 capstone: decoherence = de-isolation (conservative isometry `V`) +
partial trace over the unmonitored pointer ⟹ the system decoheres to the Born
mixture.** Conjuncts:

1. dephasing: `decohereReduced ψ = ∑ⱼ ‖⟨eⱼ,ψ⟩‖² • |eⱼ⟩⟨eⱼ|` (`decoherence_dephases`);
2. coherences vanish: `(decohereReduced ψ) i i' = 0` for `i ≠ i'`
   (`decoherence_offdiagonal_vanish`);
3. diagonal weights are Born: `(decohereReduced ψ) i i = ‖⟨eᵢ,ψ⟩‖²`
   (`decoherence_diagonal_born`);
4. the de-isolation is conservative: `Vᴴ V = 1` (`deisolation_conservative`).

The Born weights are the FS typicality volumes (LF6-A, imported via
`decoherence_diagonal_eq_pointer_volume`; Born = FS-volume derived one layer down in
the DH cluster, Gleason-free). Irreversibility is coarse-graining over a conservative
flow — no fundamental stochasticity. This is reduced-density-operator-level
decoherence; the conservative-flow-coarse-graining is the CSD reading. **DEFERRED:**
continuous-time Lindblad / T₁–T₂ semigroup; the system-marginal FS-volume-drift
geometry. **Residue: A5** (the sector / FS-typicality law posited). -/
theorem decoherence_capstone (ψ : EuclideanSpace ℂ (Fin N)) :
    (decohereReduced ψ
      = ∑ j : Fin N,
          (‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2 : ℝ)
            • outerProduct (EuclideanSpace.single j (1 : ℂ)))
    ∧ (∀ i i' : Fin N, i ≠ i' → decohereReduced ψ i i' = 0)
    ∧ (∀ i : Fin N,
        decohereReduced ψ i i
          = ((‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 : ℝ) : ℂ))
    ∧ (vnDilationV N)ᴴ * vnDilationV N = 1 :=
  ⟨decoherence_dephases ψ,
   fun _ _ h => decoherence_offdiagonal_vanish ψ h,
   decoherence_diagonal_born ψ,
   deisolation_conservative⟩

end LF6
end CSD
