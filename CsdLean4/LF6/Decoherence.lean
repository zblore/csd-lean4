import CsdLean4.LF5.FlowBornFrequency
import CsdLean4.Mathlib.QuantumInfo.PartialTrace
import CsdLean4.Mathlib.QuantumInfo.Entropy

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

**LF6-B.2 (the quantitative irreversibility witness):**

- `decohereReduced_trace` — `Tr(decohereReduced ψ) = ‖ψ‖²` (a genuine density operator,
  trace one for unit `ψ`; via `partialTraceRight_trace` + `deisolation_conservative`).
- `decohere_purity_eq` — `Tr((decohereReduced ψ)²) = ∑ⱼ (‖⟨eⱼ,ψ⟩‖²)²` (purity = sum of
  squared Born weights, the reduced state being diagonal).
- `decohere_purity_le_one` — `Tr(ρ_red²).re ≤ 1` (linear entropy `1 − Tr(ρ²) ≥ 0`).
- `decohere_purity_lt_one_of_superposition` (THE WITNESS) — for a unit measurement-basis
  superposition (two distinct nonzero Born weights), `Tr(ρ_red²).re < 1`: the STRICT
  purity drop. The pure input had purity `1`; the conservative de-isolation + pointer
  trace yields a strictly mixed state. Irreversibility quantified, not narrated.
- `decoherence_irreversibility_capstone` — the four B.2 facts bundled.

## Honest scope

This is the **reduced-density-operator** level of decoherence (a standard QM-validity
object); the CSD increment is the *conservative-flow-coarse-graining reading*:
irreversibility = partial-trace over an isometric (measure-preserving) de-isolation,
no fundamental noise. The Born weights are **imported** as FS typicality volumes
(LF6-A / the moment-map / Duistermaat–Heckman cluster), not postulated and not
re-derived here.

The **purity-drop / linear-entropy** reading `Tr(ρ_red²) < 1` is now discharged
(LF6-B.2, `decohere_purity_lt_one_of_superposition`): the irreversibility is
theorem-backed, no longer only narrated.

**LF6-B.3 (the von Neumann entropy-increase witness):** the genuine Shannon /
von Neumann entropy of the Born vector `S(ρ_red) = −∑ⱼ pⱼ log pⱼ = ∑ⱼ negMulLog(pⱼ)`
(`decohere_vonNeumann_entropy_eq`, GENUINELY derived via
`decohereReduced_eq_diagonal ∘ QuantumInfo.vonNeumannEntropy_diagonal`), non-negative
(`decohere_vonNeumann_entropy_nonneg`) and, for a measurement-basis superposition (≥2
nonzero Born weights), STRICTLY positive (`decohere_vonNeumann_entropy_pos_of_superposition`).
The pure input `|ψ⟩⟨ψ|` has `S = 0` (`QuantumInfo.vonNeumannEntropy_eq_zero_of_pure`); the
conservative de-isolation + pointer trace jumps it to `S > 0`. This is the entropy-increase
irreversibility witness, completing B.1/B.2's linear-entropy / purity account. Reuses the
K1-A entropy machinery; the decohered reduced state's diagonal IS the Born vector.

**Explicitly DEFERRED** (not in this tranche): the continuous-time Lindblad /
T₁–T₂ semigroup; the system-marginal FS-volume-**drift** geometry (the open
symplectic drift as a measure statement on Σ); environment-growth / practical
no-recoherence. **Residue: A5** (the sector / FS-typicality law is posited, reducing to D1).

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

/-! ### LF6-B.2: the quantitative purity-drop / irreversibility witness

The reduced state `decohereReduced ψ` is a genuine density operator (trace one for
unit `ψ`) but, for a measurement-basis *superposition*, a **mixed** one: its purity
`Tr(ρ_red²) = ∑ⱼ pⱼ²` (with `pⱼ = ‖⟨eⱼ,ψ⟩‖²` the Born/probability vector) is strictly
below `1`. A pure input `|ψ⟩⟨ψ|` has purity `1`; the de-isolation + unmonitored-pointer
trace drops it to `∑ pⱼ² < 1`. The lost coherence has leaked into system-pointer
correlation that the marginal no longer sees. This is the *linear-entropy* /
purity quantification of the irreversibility narrated in LF6-B.1: irreversibility is
not asserted, it is the strict inequality `decohere_purity_lt_one_of_superposition`. -/

/-- The reduced state is a `Matrix.diagonal`: `decohereReduced ψ = diagonal (ψ · star ψ)`.
Repackages `decohereReduced_apply` (the dephased entrywise form) so the trace / purity
computations collapse via `Matrix.trace_diagonal` and `Matrix.diagonal_mul_diagonal`. -/
lemma decohereReduced_eq_diagonal (ψ : EuclideanSpace ℂ (Fin N)) :
    decohereReduced ψ = Matrix.diagonal (fun i => ψ i * star (ψ i)) := by
  ext i i'
  rw [decohereReduced_apply, Matrix.diagonal_apply]

omit [NeZero N] in
/-- **Parseval for the Born weights.** `∑ⱼ ‖⟨eⱼ,ψ⟩‖² = ‖ψ‖²`: the decohered diagonal
weights form a probability vector (sum `= 1` for unit `ψ`). -/
private lemma born_sum_eq_norm_sq (ψ : EuclideanSpace ℂ (Fin N)) :
    ∑ j : Fin N, ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  rw [euclidean_norm_sq_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [EuclideanSpace.inner_single_left, map_one, one_mul]

/-- Abstract probability-vector fact: `∑ pᵢ² ≤ ∑ pᵢ = 1` when `0 ≤ pᵢ` (each
`pᵢ² ≤ pᵢ` since `pᵢ ≤ 1`). -/
private lemma sum_sq_le_one_of_sum_one {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hnn : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∑ i, p i ^ 2 ≤ 1 := by
  have hle : ∀ i, p i ≤ 1 := fun i =>
    (Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)).trans_eq hsum
  calc ∑ i, p i ^ 2 ≤ ∑ i, p i :=
        Finset.sum_le_sum fun i _ => by nlinarith [hnn i, hle i]
    _ = 1 := hsum

/-- Abstract probability-vector fact (STRICT): if `≥ 2` entries are nonzero then
`∑ pᵢ² < ∑ pᵢ = 1`. Both nonzero entries satisfy `pⱼ < 1` (the other contributes a
positive amount to the unit sum), so `pⱼ² < pⱼ` strictly there; `Finset.sum_lt_sum`. -/
private lemma sum_sq_lt_one_of_two_nonzero {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ)
    (hnn : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    {j k : ι} (hjk : j ≠ k) (hj : p j ≠ 0) (hk : p k ≠ 0) :
    ∑ i, p i ^ 2 < 1 := by
  have hle : ∀ i, p i ≤ 1 := fun i =>
    (Finset.single_le_sum (fun l _ => hnn l) (Finset.mem_univ i)).trans_eq hsum
  have hjpos : 0 < p j := lt_of_le_of_ne (hnn j) (Ne.symm hj)
  have hkpos : 0 < p k := lt_of_le_of_ne (hnn k) (Ne.symm hk)
  have hpair : p j + p k ≤ 1 := by
    rw [← hsum, ← Finset.sum_pair hjk]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hnn i)
  have hjlt : p j < 1 := by linarith
  calc ∑ i, p i ^ 2 < ∑ i, p i :=
        Finset.sum_lt_sum (fun i _ => by nlinarith [hnn i, hle i])
          ⟨j, Finset.mem_univ j, by nlinarith [hjpos, hjlt]⟩
    _ = 1 := hsum

/-- **The reduced state is trace-preserving (a genuine density operator).**
`Tr(decohereReduced ψ) = ‖ψ‖²`. Via `partialTraceRight_trace` (trace-preservation of the
partial trace) + `trace_mul_comm` to cycle `Vᴴ` to the front + `deisolation_conservative`
(`Vᴴ V = 1`): `Tr(V|ψ⟩⟨ψ|Vᴴ) = Tr(Vᴴ V |ψ⟩⟨ψ|) = Tr(|ψ⟩⟨ψ|) = ‖ψ‖²`. For unit `ψ` this
is `1`. -/
theorem decohereReduced_trace (ψ : EuclideanSpace ℂ (Fin N)) :
    (decohereReduced ψ).trace = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [decohereReduced, partialTraceRight_trace, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, deisolation_conservative, Matrix.one_mul, outerProduct_trace,
    inner_self_eq_norm_sq_to_K]
  norm_cast

/-- **The purity is the sum of squared Born weights.**
`Tr((decohereReduced ψ)²) = ∑ⱼ (‖⟨eⱼ,ψ⟩‖²)²`. The reduced state is diagonal
(`decohereReduced_eq_diagonal`), so `ρ²` is diagonal with entries `pⱼ²` and its trace
collapses to `∑ⱼ pⱼ²` (`diagonal_mul_diagonal` + `trace_diagonal`). -/
theorem decohere_purity_eq (ψ : EuclideanSpace ℂ (Fin N)) :
    (decohereReduced ψ * decohereReduced ψ).trace
      = ∑ j : Fin N,
          (((‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2) ^ 2 : ℝ) : ℂ) := by
  rw [decohereReduced_eq_diagonal, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [EuclideanSpace.inner_single_left, map_one, one_mul, mul_star_eq_normSq]
  push_cast; ring

/-- **The decohered purity is at most one** (unit `ψ`): `Tr(ρ_red²) ≤ 1`, i.e. the
linear entropy `1 − Tr(ρ_red²) ≥ 0`. From `∑ pⱼ² ≤ ∑ pⱼ = 1` (probability vector). -/
theorem decohere_purity_le_one (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1) :
    (decohereReduced ψ * decohereReduced ψ).trace.re ≤ 1 := by
  rw [decohere_purity_eq, ← Complex.ofReal_sum, Complex.ofReal_re]
  exact sum_sq_le_one_of_sum_one
    (fun i => ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)
    (fun _ => sq_nonneg _) (by rw [born_sum_eq_norm_sq, hψ, one_pow])

/-- **THE WITNESS (LF6-B.2): a measurement-basis superposition strictly loses purity.**
If `ψ` has two distinct measurement-basis components `j ≠ k` with nonzero Born weight,
then `Tr((decohereReduced ψ)²) < 1` for unit `ψ`. The pure input `|ψ⟩⟨ψ|` had purity `1`;
the de-isolation (conservative isometry `V`, `deisolation_conservative`) followed by the
unmonitored-pointer trace produces a strictly mixed state. This is the *quantitative*
irreversibility / coherence-loss statement: the strict drop `1 → ∑ pⱼ² < 1` (the lost
coherence has leaked into system-pointer correlation discarded by the marginal). The
superposition hypothesis is load-bearing: at a single measurement-basis eigenstate the
purity stays `1` (no coherence to lose). Linear-entropy witness `1 − Tr(ρ_red²) > 0`; the
full von Neumann entropy increase is DONE (LF6-B.3 below,
`decohere_vonNeumann_entropy_pos_of_superposition`); the continuous-time Lindblad /
environment-growth account remains DEFERRED. -/
theorem decohere_purity_lt_one_of_superposition (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1)
    {j k : Fin N} (hjk : j ≠ k)
    (hj : ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2 ≠ 0)
    (hk : ‖inner ℂ (EuclideanSpace.single k (1 : ℂ)) ψ‖ ^ 2 ≠ 0) :
    (decohereReduced ψ * decohereReduced ψ).trace.re < 1 := by
  rw [decohere_purity_eq, ← Complex.ofReal_sum, Complex.ofReal_re]
  exact sum_sq_lt_one_of_two_nonzero
    (fun i => ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)
    (fun _ => sq_nonneg _) (by rw [born_sum_eq_norm_sq, hψ, one_pow]) hjk hj hk

/-- **The LF6-B.2 irreversibility capstone.** For a unit measurement-basis superposition
(`j ≠ k`, both Born weights nonzero):

1. `Tr(decohereReduced ψ) = 1` — the reduced state is a genuine density operator
   (`decohereReduced_trace`);
2. `Tr((decohereReduced ψ)²) = ∑ⱼ (‖⟨eⱼ,ψ⟩‖²)²` — purity = sum of squared Born weights
   (`decohere_purity_eq`);
3. `Tr((decohereReduced ψ)²).re ≤ 1` — purity ≤ 1 / linear entropy ≥ 0
   (`decohere_purity_le_one`);
4. `Tr((decohereReduced ψ)²).re < 1` — STRICT purity drop (`decohere_purity_lt_one_of_superposition`).

The pure input `|ψ⟩⟨ψ|` (purity 1) decoheres to a strictly mixed state: the
irreversibility narrated in `decoherence_capstone` is now theorem-backed (linear-entropy
witness `1 − Tr(ρ²) > 0`). The von Neumann entropy increase is DONE (LF6-B.3,
`decohere_vonNeumann_entropy_pos_of_superposition`). DEFERRED: continuous-time
Lindblad / environment growth. Residue A5 (FS-typicality posited). -/
theorem decoherence_irreversibility_capstone (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1)
    {j k : Fin N} (hjk : j ≠ k)
    (hj : ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2 ≠ 0)
    (hk : ‖inner ℂ (EuclideanSpace.single k (1 : ℂ)) ψ‖ ^ 2 ≠ 0) :
    (decohereReduced ψ).trace = 1
    ∧ (decohereReduced ψ * decohereReduced ψ).trace
        = ∑ i : Fin N,
            (((‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2) ^ 2 : ℝ) : ℂ)
    ∧ (decohereReduced ψ * decohereReduced ψ).trace.re ≤ 1
    ∧ (decohereReduced ψ * decohereReduced ψ).trace.re < 1 :=
  ⟨by rw [decohereReduced_trace, hψ, one_pow]; norm_num,
   decohere_purity_eq ψ,
   decohere_purity_le_one ψ hψ,
   decohere_purity_lt_one_of_superposition ψ hψ hjk hj hk⟩

/-! ### LF6-B.3: the von Neumann (Shannon-of-the-Born-vector) entropy-increase witness

B.2 quantified irreversibility through the linear entropy `1 − Tr(ρ_red²)`. B.3 gives the genuine
**von Neumann** entropy of the decohered reduced state. Since `decohereReduced ψ` is diagonal with
the Born vector `pⱼ = ‖⟨eⱼ,ψ⟩‖²` on the diagonal (`decohereReduced_eq_diagonal`), its von Neumann
entropy is exactly the Shannon entropy of the Born vector

  `S(ρ_red) = −∑ⱼ pⱼ log pⱼ = ∑ⱼ negMulLog(pⱼ)`,

derived (not asserted) by feeding `decohereReduced_eq_diagonal` into the K1-A general diagonal
entropy `QuantumInfo.vonNeumannEntropy_diagonal`. The pure input `|ψ⟩⟨ψ|` has `S = 0`
(`vonNeumannEntropy_eq_zero_of_pure`); the conservative de-isolation + unmonitored-pointer trace
jumps it to `S > 0` for any measurement-basis superposition. This is the entropy-increase
irreversibility witness (`0 → S > 0`), completing B.1/B.2's linear-entropy / purity account. -/

/-- The reduced state as a diagonal of the (real, non-negative) Born weights:
`decohereReduced ψ = diagonal (fun i => ↑‖⟨eᵢ,ψ⟩‖²)`. Repackages `decohereReduced_eq_diagonal`
with the diagonal entry `ψᵢ · star ψᵢ` rewritten as the real Born weight `‖⟨eᵢ,ψ⟩‖²` cast to `ℂ`,
the form `QuantumInfo.vonNeumannEntropy_diagonal` consumes. -/
lemma decohereReduced_eq_diagonal_born (ψ : EuclideanSpace ℂ (Fin N)) :
    decohereReduced ψ
      = Matrix.diagonal (fun i =>
          (RCLike.ofReal (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2) : ℂ)) := by
  rw [decohereReduced_eq_diagonal]
  congr 1
  funext i
  rw [EuclideanSpace.inner_single_left, map_one, one_mul, mul_star_eq_normSq]
  exact (RCLike.ofReal_pow _ _).symm

/-- **The reduced state is Hermitian** (a diagonal of the real Born weights). -/
lemma decohereReduced_isHermitian (ψ : EuclideanSpace ℂ (Fin N)) :
    (decohereReduced ψ).IsHermitian := by
  rw [decohereReduced_eq_diagonal]
  refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
  rw [isSelfAdjoint_iff]
  funext i
  rw [Pi.star_apply, star_mul', star_star, mul_comm]

/-- Abstract probability-vector fact (STRICT positivity of Shannon entropy): if a non-negative
vector summing to `1` has `≥ 2` nonzero entries then `0 < ∑ᵢ negMulLog(pᵢ)`. Each term is `≥ 0`
(`Real.negMulLog_nonneg`, `pᵢ ∈ [0,1]`) and the `j`-th is strictly positive since `0 < pⱼ < 1`
(the second nonzero entry `pₖ` keeps `pⱼ` off `1`), by `Real.negMulLog_pos`. -/
private lemma sum_negMulLog_pos_of_two_nonzero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hnn : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    {j k : ι} (hjk : j ≠ k) (hj : p j ≠ 0) (hk : p k ≠ 0) :
    0 < ∑ i, Real.negMulLog (p i) := by
  have hle : ∀ i, p i ≤ 1 := fun i =>
    (Finset.single_le_sum (fun l _ => hnn l) (Finset.mem_univ i)).trans_eq hsum
  have hjpos : 0 < p j := lt_of_le_of_ne (hnn j) (Ne.symm hj)
  have hkpos : 0 < p k := lt_of_le_of_ne (hnn k) (Ne.symm hk)
  have hpair : p j + p k ≤ 1 := by
    rw [← hsum, ← Finset.sum_pair hjk]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hnn i)
  have hjlt : p j < 1 := by linarith
  exact Finset.sum_pos' (fun i _ => Real.negMulLog_nonneg (hnn i) (hle i))
    ⟨j, Finset.mem_univ j, Real.negMulLog_pos hjpos hjlt⟩

/-- Entropy is independent of the supplied Hermitian witness and transports across a matrix
equality: if `ρ = σ` then `S(ρ) = S(σ)` (the eigenvalue values are matrix-determined). The
proof-irrelevance / matrix-equality hinge used to move the entropy computation onto the diagonal
form. -/
private lemma entropy_congr_of_eq {n : Type*} [Fintype n] [DecidableEq n]
    {ρ σ : Matrix n n ℂ} (heq : ρ = σ) (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    QuantumInfo.vonNeumannEntropy hρ = QuantumInfo.vonNeumannEntropy hσ := by
  subst heq
  rfl

/-- **The decohered von Neumann entropy is the Shannon entropy of the Born vector.**
`S(decohereReduced ψ) = ∑ⱼ negMulLog(‖⟨eⱼ,ψ⟩‖²) = −∑ⱼ pⱼ log pⱼ`, GENUINELY derived by transporting
along `decohereReduced_eq_diagonal_born` (the reduced state is diagonal with the Born vector on the
diagonal) into the K1-A general diagonal entropy `QuantumInfo.vonNeumannEntropy_diagonal`. The
reduced state's diagonal IS the Born vector, so its von Neumann entropy is exactly the Shannon
entropy of the Born weights. The result is independent of the supplied Hermitian witness. -/
theorem decohere_vonNeumann_entropy_eq (ψ : EuclideanSpace ℂ (Fin N))
    (hHerm : (decohereReduced ψ).IsHermitian) :
    QuantumInfo.vonNeumannEntropy hHerm
      = ∑ j : Fin N, Real.negMulLog (‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2) := by
  rw [entropy_congr_of_eq (decohereReduced_eq_diagonal_born ψ) hHerm
        ((decohereReduced_eq_diagonal_born ψ) ▸ hHerm)]
  exact QuantumInfo.vonNeumannEntropy_diagonal _

/-- **The decohered von Neumann entropy is non-negative** (unit `ψ`): `S(decohereReduced ψ) ≥ 0`.
Each `negMulLog(pⱼ) ≥ 0` since `pⱼ = ‖⟨eⱼ,ψ⟩‖² ∈ [0,1]` (the Born weights are a probability vector,
`born_sum_eq_norm_sq` + `‖ψ‖ = 1`). -/
theorem decohere_vonNeumann_entropy_nonneg (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1)
    (hHerm : (decohereReduced ψ).IsHermitian) :
    0 ≤ QuantumInfo.vonNeumannEntropy hHerm := by
  rw [decohere_vonNeumann_entropy_eq]
  refine Finset.sum_nonneg fun i _ => ?_
  refine Real.negMulLog_nonneg (sq_nonneg _) ?_
  have hle := Finset.single_le_sum
    (f := fun j => ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rwa [born_sum_eq_norm_sq, hψ, one_pow] at hle

/-- **THE WITNESS (LF6-B.3): a measurement-basis superposition has strictly positive entropy.**
If `ψ` has two distinct measurement-basis components `j ≠ k` with nonzero Born weight, then
`S(decohereReduced ψ) > 0` for unit `ψ`. The pure input `|ψ⟩⟨ψ|` has `S = 0`
(`QuantumInfo.vonNeumannEntropy_eq_zero_of_pure`); the conservative de-isolation (isometry `V`,
`deisolation_conservative`) followed by the unmonitored-pointer trace produces a mixed state with
strictly positive von Neumann entropy. This is the genuine entropy-increase irreversibility
statement, the pure→mixed jump `0 → S > 0`. The superposition hypothesis is LOAD-BEARING: at a
single measurement-basis eigenstate exactly one `pⱼ = 1` and the rest are `0`, so
`S = negMulLog(1) + ∑ negMulLog(0) = 0` (the witness correctly does not fire). Two nonzero weights
summing to `1` force each `∈ (0,1)`, where `negMulLog > 0`. The continuous-time Lindblad /
environment-growth account remains DEFERRED; residue A5 (FS-typicality posited). -/
theorem decohere_vonNeumann_entropy_pos_of_superposition (ψ : EuclideanSpace ℂ (Fin N))
    (hψ : ‖ψ‖ = 1) (hHerm : (decohereReduced ψ).IsHermitian)
    {j k : Fin N} (hjk : j ≠ k)
    (hj : ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2 ≠ 0)
    (hk : ‖inner ℂ (EuclideanSpace.single k (1 : ℂ)) ψ‖ ^ 2 ≠ 0) :
    0 < QuantumInfo.vonNeumannEntropy hHerm := by
  rw [decohere_vonNeumann_entropy_eq]
  exact sum_negMulLog_pos_of_two_nonzero
    (fun i => ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)
    (fun _ => sq_nonneg _) (by rw [born_sum_eq_norm_sq, hψ, one_pow]) hjk hj hk

/-- **The LF6-B.3 von Neumann entropy-increase capstone.** For a unit measurement-basis
superposition (`j ≠ k`, both Born weights nonzero):

1. `S(|ψ⟩⟨ψ|) = 0` — the pure input has zero entropy
   (`QuantumInfo.vonNeumannEntropy_eq_zero_of_pure`);
2. `S(decohereReduced ψ) = ∑ⱼ negMulLog(‖⟨eⱼ,ψ⟩‖²)` — the decohered state's entropy is the
   Shannon entropy of the Born vector (`decohere_vonNeumann_entropy_eq`);
3. `0 ≤ S(decohereReduced ψ)` — non-negativity (`decohere_vonNeumann_entropy_nonneg`);
4. `0 < S(decohereReduced ψ)` — STRICT entropy increase
   (`decohere_vonNeumann_entropy_pos_of_superposition`).

The pure input (`S = 0`) decoheres to a mixed state with strictly positive von Neumann entropy:
the pure→mixed jump `0 → S > 0`. This is the genuine (Shannon-of-the-Born-vector) entropy-increase
irreversibility witness, completing B.1/B.2's linear-entropy / purity account. The superposition
hypothesis is load-bearing (single eigenstate ⟹ `S = 0`). DEFERRED: continuous-time Lindblad /
environment growth. Residue A5 (FS-typicality posited). -/
theorem decoherence_vonNeumann_irreversibility_capstone (ψ : EuclideanSpace ℂ (Fin N))
    (hψ : ‖ψ‖ = 1) {j k : Fin N} (hjk : j ≠ k)
    (hj : ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2 ≠ 0)
    (hk : ‖inner ℂ (EuclideanSpace.single k (1 : ℂ)) ψ‖ ^ 2 ≠ 0) :
    QuantumInfo.vonNeumannEntropy (outerProduct_isHermitian ψ) = 0
    ∧ QuantumInfo.vonNeumannEntropy (decohereReduced_isHermitian ψ)
        = ∑ i : Fin N, Real.negMulLog (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)
    ∧ 0 ≤ QuantumInfo.vonNeumannEntropy (decohereReduced_isHermitian ψ)
    ∧ 0 < QuantumInfo.vonNeumannEntropy (decohereReduced_isHermitian ψ) :=
  ⟨QuantumInfo.vonNeumannEntropy_eq_zero_of_pure _
      (outerProduct_mul_self_of_unit_norm ψ hψ) (outerProduct_trace_of_unit_norm ψ hψ),
   decohere_vonNeumann_entropy_eq ψ (decohereReduced_isHermitian ψ),
   decohere_vonNeumann_entropy_nonneg ψ hψ (decohereReduced_isHermitian ψ),
   decohere_vonNeumann_entropy_pos_of_superposition ψ hψ (decohereReduced_isHermitian ψ)
     hjk hj hk⟩

end LF6
end CSD
