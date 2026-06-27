import CsdLean4.Empirical.CSD.ContextVolume
import CsdLean4.Empirical.CSD.VolumeCanonical
import CsdLean4.Empirical.CSD.Contextuality.MerminPeres

/-!
# Empirical/CSD: a Mermin–Peres rank-2 observable's outcome Born weights as Kähler volumes

**Category:** 3-Local (CSD-ontic volume reading; a quick-win instantiation of the
already-proved degenerate-eigenspace engine
`CSD.Empirical.CSDBridge.ContextVolume.block_born_frequency_volume`).

This is the **volume-ratio companion** to the *impossibility* readings of the
Mermin–Peres magic-square contextuality theorem:

- QM side (`Empirical/QM/Contextuality/MerminPeres.lean`): the six operator-product
  identities `mermin_peres_R0..R2`/`C0..C2` on the 3×3 two-qubit Pauli grid and the
  combinatorial no-go `no_lhv_mermin_peres`.
- CSD impossibility side (`Empirical/CSD/Contextuality/MerminPeres.lean`):
  `no_csd_mermin_peres_assignment` — no non-contextual ontic-outcome value
  assignment to the 9 grid observables is satisfiable.

This file is the complementary **volume reading**: a *single representative* grid
observable's `±1`-outcome Born weights are genuine block sums of Fubini–Study
typicality volumes on the fixed ontic `Σ = ℂℙ³`.

## The chosen observable: the non-diagonal `X ⊗ X`

The diagonal grid observable `Z ⊗ Z` is already grounded by
`ContextVolume.zz_parity_born_frequency_volume` (computational-basis eigenbasis, no
rotation). To complement it we take the most symmetric **non-diagonal** member,
`X ⊗ X`, whose eigenbasis is `H ⊗ H` applied to the computational basis — the four
product vectors `|±⟩ ⊗ |±⟩` with `|±⟩ = (|0⟩ ± |1⟩)/√2`. With the standard
`(i, j) ↦ 2i + j` flattening of `Fin 2 × Fin 2 ≃ Fin 4`, `X ⊗ X` is the
anti-diagonal `eᵢ ↦ e_{3−i}`, so its eigenvectors are the explicit `(±1/2)`-component
rays

```
v0 = ( 1,  1,  1,  1)/2   eigenvalue +1   (|++⟩)
v1 = ( 1, -1,  1, -1)/2   eigenvalue -1   (|+−⟩)
v2 = ( 1,  1, -1, -1)/2   eigenvalue -1   (|−+⟩)
v3 = ( 1, -1, -1,  1)/2   eigenvalue +1   (|−−⟩)
```

(the rows of `H ⊗ H`). Eigenvalue `+1` block `{v0, v3}`, eigenvalue `−1` block
`{v1, v2}`: the sign-parity labelling `mpXXBlk = ![0, 1, 1, 0] : Fin 4 → Fin 2`,
identical in shape to the `Z ⊗ Z` parity grouping. Orthonormality of these explicit
`(±1/2)`-component vectors is a clean `norm_num` computation (no Cabello-ray
transport needed), packaged as `mpXXBasis : OrthonormalBasis (Fin 4) ℂ …` via
`OrthonormalBasis.mk` + `span_eq_top_of_card_eq_finrank`.

**The eigenbasis identity is proved, not asserted.** `mpXXVec_eigenvector` certifies
`(σx ⊗ σx) · vᵢ = mpXXEigval i • vᵢ` against the genuine Pauli observable
`sigmaX ⊗ₖ sigmaX` of `Empirical/QM/Contextuality/MerminPeres.lean` (reindexed onto
`Fin 4` via `finProdFinEquiv`, where it is the antidiagonal `reindex_sigmaXX`), and
`mpXXBlk_eq_zero_iff_eigval_one` certifies that the collapsed `a = 0` block is exactly
the `+1` eigenspace. So the headline below lands on the *actual* `σx ⊗ σx = +1`
outcome Born weight; the kernel would reject it for any other basis.

## The two halves of the Mermin–Peres story, told honestly

1. **A rank-2 grid observable carries genuine Born weights as block sums of FS
   typicality volumes.** Instantiating `block_born_frequency_volume` at `mpXXBasis`,
   `mpXXBlk`, and the `+1` block, the `X ⊗ X = +1` outcome Born weight
   `⟨ψ, P₊ ψ⟩ = ‖⟨v0, ψ⟩‖² + ‖⟨v3, ψ⟩‖²` is the almost-sure limit of empirical
   frequencies of the block's barycentric Born regions on the fixed ontic
   `Σ = ℂℙ³` — a sum of two Fubini–Study typicality volumes
   (`mp_xx_born_frequency_volume`). The `−1` block is the identical instantiation at
   `a = 1`.
2. **Yet no single non-contextual `±1` assignment is jointly consistent across the
   square's rows and columns** (`no_lhv_mermin_peres` / `no_csd_mermin_peres_assignment`,
   the all-cells-product `+1 = −1` impossibility).

**The CSD reading of contextuality.** Each of the nine grid observables is a rank-2
carving of the *one* ontic `Σ = ℂℙ³`; its outcome weights are typicality volumes,
recomputed per observable (which orthonormal frame `B` carves the moment regions).
The context-dependence the Mermin–Peres theorem exploits is, on the CSD ontology, the
dependence of the carved-volume regions on the measurement frame — not a hidden
variable. There is no global section assigning consistent `±1` values across the
overlapping row/column contexts, exactly the combinatorial no-go, now sitting beside a
genuine per-observable volume realisation.

## Scope and honesty

- **One representative observable.** `X ⊗ X` is built explicitly; the diagonal
  `Z ⊗ Z` is `zz_parity_born_frequency_volume`. The remaining seven grid observables
  (`Z ⊗ X`, `X ⊗ Z`, `Y ⊗ Y`, …) are **identical instantiations** of the same engine
  at the corresponding `H/S`-rotated orthonormal frame — no new mathematics; building
  all nine is mechanical repetition and is omitted.
- **Realisation, not derivation.** As for the whole `Empirical/CSD/*Volume` series:
  the Born = FS-volume identity is *derived* one layer down (the Duistermaat–Heckman /
  moment-map cluster, `LF4.born_frequency_convergence_N_uncond`, Gleason-free, no Born
  put in) and *imported* here; `Φ = id` (no dynamics exercised). The Mermin–Peres
  no-go itself stays at the QM-validity layer (`Empirical/QM/`).
- **Gleason-free, foundational-triple-only.** The engine is `busch_effect_gleason`-free;
  this instantiation inherits that.
- **No genericity hypothesis.** Every unit two-qubit preparation is covered, the
  computational eigenstates and the Bell states (with vanishing rotated components)
  included.
-/

open MeasureTheory ProbabilityTheory Filter Matrix.UnitaryGroup CSD.LF4
open CSD.Empirical.MerminPeres
open scoped LinearAlgebra.Projectivization Kronecker Matrix

namespace CSD
namespace Empirical
namespace CSDBridge
namespace MerminPeres

open CSD.Empirical.CSDBridge.ContextVolume

/-! ### The `X ⊗ X` eigenbasis (`H ⊗ H`) as an `OrthonormalBasis` -/

/-- The real `(±1/2)`-component pattern of the four `X ⊗ X` eigenvectors (the rows of
`H ⊗ H`): row `i` is the `i`-th eigenvector, column `k` its `k`-th component. -/
noncomputable def mpXXReal : Fin 4 → Fin 4 → ℝ :=
  ![![1/2,  1/2,  1/2,  1/2],
    ![1/2, -1/2,  1/2, -1/2],
    ![1/2,  1/2, -1/2, -1/2],
    ![1/2, -1/2, -1/2,  1/2]]

/-- The four `X ⊗ X` eigenvectors as complex coordinate vectors in
`EuclideanSpace ℂ (Fin 4)` (real components coerced to `ℂ`). -/
noncomputable def mpXXVec (i : Fin 4) : EuclideanSpace ℂ (Fin 4) :=
  WithLp.toLp 2 (fun k => ((mpXXReal i k : ℝ) : ℂ))

/-- Scalar complex inner product of two real coercions: `⟨↑a, ↑b⟩_ℂ = ↑(a * b)`. -/
private lemma mp_scalar_inner (a b : ℝ) : (inner ℂ (↑a : ℂ) (↑b : ℂ) : ℂ) = ↑(a * b) := by
  rw [RCLike.inner_apply, Complex.conj_ofReal]; push_cast; ring

/-- **The `H ⊗ H` family is orthonormal.** A direct `norm_num` computation on the
explicit `(±1/2)`-component vectors: each squared norm is `4 · (1/2)² = 1` and each
off-diagonal inner product is a balanced `±1/4` sum equal to `0`. -/
lemma mpXXVec_orthonormal : Orthonormal ℂ mpXXVec := by
  rw [orthonormal_iff_ite]
  intro a b
  rw [PiLp.inner_apply, Fin.sum_univ_four]
  simp only [mpXXVec, WithLp.ofLp_toLp, mp_scalar_inner]
  fin_cases a <;> fin_cases b <;>
    norm_num [mpXXReal, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]

/-- **The `X ⊗ X` eigenbasis as a Mathlib `OrthonormalBasis`.** A 4-element orthonormal
family in the 4-dimensional `EuclideanSpace ℂ (Fin 4)` spans (cardinality = `finrank`),
so `OrthonormalBasis.mk` applies. This is the (degenerate) projective measurement frame
fed to the engine `block_born_frequency_volume`. -/
noncomputable def mpXXBasis :
    OrthonormalBasis (Fin 4) ℂ (EuclideanSpace ℂ (Fin 4)) := by
  refine OrthonormalBasis.mk mpXXVec_orthonormal ?_
  have hcard : Fintype.card (Fin 4) = Module.finrank ℂ (EuclideanSpace ℂ (Fin 4)) := by
    rw [Fintype.card_fin, finrank_euclideanSpace_fin]
  rw [mpXXVec_orthonormal.linearIndependent.span_eq_top_of_card_eq_finrank hcard]

/-- `mpXXBasis i` is the `i`-th `X ⊗ X` eigenvector. -/
lemma mpXXBasis_apply (i : Fin 4) : mpXXBasis i = mpXXVec i := by
  unfold mpXXBasis
  rw [OrthonormalBasis.coe_mk]

/-- The sign-parity block labelling of the `X ⊗ X` eigenbasis: eigenvalue `+1` block
`{v0, v3}` ↦ outcome `0`; eigenvalue `−1` block `{v1, v2}` ↦ outcome `1`. -/
def mpXXBlk : Fin 4 → Fin 2 := ![0, 1, 1, 0]

/-! ### The eigenbasis identity (machine-checked connection to the real `σx ⊗ σx`)

The `mpXXBasis`/`mpXXBlk` data above is named "the `X ⊗ X` eigenbasis"; this section
*proves* that identity against the genuine Pauli observable `sigmaX ⊗ₖ sigmaX` of
`Empirical/QM/Contextuality/MerminPeres.lean`, so the label is kernel-certified, not a
docstring assertion. Without these lemmas the headline would be a theorem about an
arbitrary orthonormal basis. -/

/-- The eigenvalues of the four `X ⊗ X` eigenvectors `mpXXVec`, under the
`(i, j) ↦ 2i + j` (`finProdFinEquiv`) flattening of `Fin 2 × Fin 2 ≃ Fin 4`:
`v0 ↦ +1`, `v1 ↦ −1`, `v2 ↦ −1`, `v3 ↦ +1`. -/
def mpXXEigval : Fin 4 → ℂ := ![1, -1, -1, 1]

/-- **The real `σx ⊗ σx`, reindexed under `finProdFinEquiv`, is the antidiagonal.**
A machine-checked matrix identity referencing the genuine `sigmaX ⊗ₖ sigmaX`
(from `Empirical/QM/Contextuality/MerminPeres.lean`), not a fresh literal: the four
`finProdFinEquiv.symm` index resolutions are discharged by `decide`. -/
lemma reindex_sigmaXX :
    Matrix.reindex finProdFinEquiv finProdFinEquiv (sigmaX ⊗ₖ sigmaX)
      = !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; (1 : ℂ), 0, 0, 0] := by
  ext k j
  fin_cases k <;> fin_cases j <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
      sigmaX, show (@finProdFinEquiv 2 2).symm (0 : Fin 4) = (0, 0) from by decide,
      show (@finProdFinEquiv 2 2).symm (1 : Fin 4) = (0, 1) from by decide,
      show (@finProdFinEquiv 2 2).symm (2 : Fin 4) = (1, 0) from by decide,
      show (@finProdFinEquiv 2 2).symm (3 : Fin 4) = (1, 1) from by decide]

/-- **`mpXXVec i` is a genuine eigenvector of the real `σx ⊗ σx`.** The eigen-equation
`(σx ⊗ σx) · vᵢ = mpXXEigval i • vᵢ`, stated against the actual Pauli observable
`sigmaX ⊗ₖ sigmaX` reindexed onto `Fin 4` (via `reindex_sigmaXX` it is the antidiagonal
`eᵢ ↦ e₃₋ᵢ`). This is the load-bearing faithfulness lemma: it certifies that the
named-basis `mpXXBasis` really is the `X ⊗ X` eigenbasis, so `mp_xx_born_frequency_volume`
lands on the `σx ⊗ σx` outcome Born weight rather than an arbitrary basis's weight. -/
theorem mpXXVec_eigenvector (i : Fin 4) :
    (Matrix.reindex finProdFinEquiv finProdFinEquiv (sigmaX ⊗ₖ sigmaX)) *ᵥ (mpXXVec i).ofLp
      = mpXXEigval i • (mpXXVec i).ofLp := by
  rw [reindex_sigmaXX]
  funext k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, mpXXVec, mpXXEigval, mpXXReal,
      WithLp.ofLp_toLp, Pi.smul_apply, smul_eq_mul] <;> norm_num

/-- **The `+1` block of `mpXXBlk` is exactly the `+1` eigenspace.** `mpXXBlk i = 0`
(the outcome-`0` block collapsed in `mp_xx_born_frequency_volume`) holds iff the `i`-th
eigenvalue is `+1`. Together with `mpXXVec_eigenvector` this certifies that the headline's
block weight is the `σx ⊗ σx = +1` outcome Born weight. (`mpXXEigval i = 1` is over `ℂ`,
hence not `Decidable`; closed by `simp`/`norm_num` per index.) -/
theorem mpXXBlk_eq_zero_iff_eigval_one (i : Fin 4) :
    mpXXBlk i = 0 ↔ mpXXEigval i = 1 := by
  fin_cases i <;> simp [mpXXBlk, mpXXEigval] <;> norm_num

/-! ### Earning the `Z ⊗ Z` label for the engine-file `zz_parity_born_frequency_volume`

`ContextVolume.zz_parity_born_frequency_volume` (in the engine file, which intentionally
imports no QM observables) realises the `Z ⊗ Z` parity outcome weight as a block sum of FS
volumes using `B = EuclideanSpace.basisFun (Fin 4) ℂ` (the computational basis) and block
`![0, 1, 1, 0]`, but never proves that computational basis is the `σz ⊗ σz` eigenbasis —
the same asserted-not-proved gap closed above for `X ⊗ X`. These lemmas close it here (the
only file in scope that imports the real `sigmaZ`), so the `Z ⊗ Z` label is earned by
composition: the engine's `B` is the `σz ⊗ σz` eigenbasis, and its block `{0, 3}` is the
`+1` eigenspace, both machine-checked against the genuine Pauli observable. -/

/-- The eigenvalues of the computational basis under `σz ⊗ σz`, with the `(i, j) ↦ 2i + j`
flattening: `|00⟩ ↦ +1`, `|01⟩ ↦ −1`, `|10⟩ ↦ −1`, `|11⟩ ↦ +1`. -/
def mpZZEigval : Fin 4 → ℂ := ![1, -1, -1, 1]

/-- **The real `σz ⊗ σz`, reindexed under `finProdFinEquiv`, is the diagonal.** Machine-checked
against the genuine `sigmaZ ⊗ₖ sigmaZ` (from `Empirical/QM/Contextuality/MerminPeres.lean`),
not a fresh literal. -/
lemma reindex_sigmaZZ :
    Matrix.reindex finProdFinEquiv finProdFinEquiv (sigmaZ ⊗ₖ sigmaZ)
      = !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; (0 : ℂ), 0, 0, 1] := by
  ext k j
  fin_cases k <;> fin_cases j <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
      sigmaZ, show (@finProdFinEquiv 2 2).symm (0 : Fin 4) = (0, 0) from by decide,
      show (@finProdFinEquiv 2 2).symm (1 : Fin 4) = (0, 1) from by decide,
      show (@finProdFinEquiv 2 2).symm (2 : Fin 4) = (1, 0) from by decide,
      show (@finProdFinEquiv 2 2).symm (3 : Fin 4) = (1, 1) from by decide]

/-- **The computational basis vector `eᵢ` is a genuine eigenvector of the real `σz ⊗ σz`.**
The eigen-equation `(σz ⊗ σz) · eᵢ = mpZZEigval i • eᵢ` against the actual Pauli observable
`sigmaZ ⊗ₖ sigmaZ` (reindexed onto `Fin 4`, where via `reindex_sigmaZZ` it is the diagonal).
`EuclideanSpace.single i 1 = (EuclideanSpace.basisFun (Fin 4) ℂ) i` is exactly the frame `B`
used by `zz_parity_born_frequency_volume`, so this certifies that `B` is the `σz ⊗ σz`
eigenbasis. -/
theorem mpZZVec_eigenvector (i : Fin 4) :
    (Matrix.reindex finProdFinEquiv finProdFinEquiv (sigmaZ ⊗ₖ sigmaZ)) *ᵥ
        (EuclideanSpace.single i (1 : ℂ)).ofLp
      = mpZZEigval i • (EuclideanSpace.single i (1 : ℂ)).ofLp := by
  rw [reindex_sigmaZZ]
  funext k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, mpZZEigval, EuclideanSpace.single,
      Pi.smul_apply, smul_eq_mul]

/-- **The `+1` block of the `Z ⊗ Z` parity grouping is exactly the `+1` eigenspace.** The
block `![0, 1, 1, 0] i = 0` (the outcome-`0` block collapsed in
`zz_parity_born_frequency_volume`) holds iff the `i`-th `σz ⊗ σz` eigenvalue is `+1`.
(`mpZZEigval i = 1` is over `ℂ`, hence not `Decidable`; closed by `simp`/`norm_num`.) -/
theorem mpZZBlk_eq_zero_iff_eigval_one (i : Fin 4) :
    (![0, 1, 1, 0] : Fin 4 → Fin 2) i = 0 ↔ mpZZEigval i = 1 := by
  fin_cases i <;> simp [mpZZEigval] <;> norm_num

/-! ### The headline: the `X ⊗ X = +1` Born weight as a block sum of FS volumes -/

/-- **A Mermin–Peres rank-2 observable's outcome Born weight as a derived sum of Kähler
volumes.** For i.i.d. trials drawing microstates from the Fubini–Study typicality
measure on the ontic `Σ = ℂℙ³`, the empirical frequency of the `X ⊗ X = +1`
(even-parity) outcome — the sum of the per-ray frequencies over the block
`{v0, v3}` — converges, on a single almost-sure event, to the `X ⊗ X = +1` Born
weight `‖⟨v0, ψ⟩‖² + ‖⟨v3, ψ⟩‖² = ⟨ψ, P₊ ψ⟩`, a block sum of two FS typicality volumes
on the fixed ontic `Σ = ℂℙ³`.

That this block weight genuinely is the `σx ⊗ σx = +1` outcome weight (and not an
arbitrary basis's) is **machine-checked**, not asserted in prose: `mpXXVec_eigenvector`
proves `(σx ⊗ σx) · vᵢ = mpXXEigval i • vᵢ` against the real Pauli observable
`sigmaX ⊗ₖ sigmaX`, and `mpXXBlk_eq_zero_iff_eigval_one` proves the `a = 0` block is
exactly the `+1` eigenspace.

A direct instantiation of `block_born_frequency_volume` at `M = 3`, the `X ⊗ X`
eigenframe `mpXXBasis`, the sign-parity block `mpXXBlk`, the `+1` block `a = 0`, and an
arbitrary unit `ψ` — carving-free, Gleason-free, unconditional (every unit preparation,
eigenstates included), no new mathematics. The even-parity block `{0, 3}` is collapsed
via `Finset.sum_pair` (filter = `{0, 3}` by `decide`). The `X ⊗ X = −1` outcome is the
identical instantiation at `a = 1`; the diagonal `Z ⊗ Z` companion is
`zz_parity_born_frequency_volume`.

This grounds a rank-2 Mermin–Peres grid observable's context-dependent `±1` outcome
weights — the weights that no non-contextual hidden-variable assignment can jointly
reproduce across the square (`no_lhv_mermin_peres`) — as genuine Fubini–Study
typicality volumes on the *fixed* ontic `Σ`. Honest scope: realisation not derivation
(`Φ = id`, FS regions carved in the rotated `H ⊗ H` frame); the Mermin–Peres no-go
stays at the QM-validity layer (`Empirical/QM/`). -/
theorem mp_xx_born_frequency_volume
    (p₀ : CPN 4)
    (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ‖ψ‖ = 1)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 4) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ i : Fin 4,
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' bornRegion (mpXXBasis.repr ψ) (repr_ne_zero mpXXBasis ψ hψ) i)
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun m : ℕ =>
          ∑ i ∈ Finset.univ.filter (fun i => mpXXBlk i = 0),
            (∑ k ∈ Finset.range m,
                Set.indicator
                  ((X k) ⁻¹' bornRegion (mpXXBasis.repr ψ)
                    (repr_ne_zero mpXXBasis ψ hψ) i)
                  (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (mpXXVec 0) ψ‖ ^ 2 + ‖inner ℂ (mpXXVec 3) ψ‖ ^ 2)) := by
  have h := block_born_frequency_volume p₀ mpXXBasis ψ hψ mpXXBlk 0 X hX hlaw hindep
  have hsum :
      (∑ i ∈ Finset.univ.filter (fun i => mpXXBlk i = 0),
          ‖inner ℂ (mpXXBasis i) ψ‖ ^ 2)
        = ‖inner ℂ (mpXXVec 0) ψ‖ ^ 2 + ‖inner ℂ (mpXXVec 3) ψ‖ ^ 2 := by
    rw [show (Finset.univ.filter (fun i => mpXXBlk i = 0)) = {0, 3} from by decide,
      Finset.sum_pair (by decide : (0 : Fin 4) ≠ 3),
      mpXXBasis_apply, mpXXBasis_apply]
  rw [← hsum]
  exact h

/-- `mp_xx_born_frequency_volume` on the canonical i.i.d. Fubini–Study trial witness
(`fsTrialMeasure` / `fsTrial`): the trial bundle is discharged, so the hypothesis set is
Lean-inhabited, not merely classically satisfiable. Direct instantiation of
`mp_xx_born_frequency_volume` at the canonical FS coordinate process. -/
theorem mp_xx_born_frequency_volume_canonical
    (p₀ : CPN 4)
    (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ‖ψ‖ = 1) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀,
      Tendsto
        (fun m : ℕ =>
          ∑ i ∈ Finset.univ.filter (fun i => mpXXBlk i = 0),
            (∑ k ∈ Finset.range m,
                Set.indicator
                  ((fsTrial 4 k) ⁻¹' bornRegion (mpXXBasis.repr ψ)
                    (repr_ne_zero mpXXBasis ψ hψ) i)
                  (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (mpXXVec 0) ψ‖ ^ 2 + ‖inner ℂ (mpXXVec 3) ψ‖ ^ 2)) :=
  mp_xx_born_frequency_volume p₀ ψ hψ
    (fsTrial 4) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀
      (bornRegion (mpXXBasis.repr ψ) (repr_ne_zero mpXXBasis ψ hψ))
      (bornRegion_measurable_uncond (mpXXBasis.repr ψ) (repr_ne_zero mpXXBasis ψ hψ)))

end MerminPeres
end CSDBridge
end Empirical
end CSD
