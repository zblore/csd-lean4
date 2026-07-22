/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.ContextVolume
public import CsdLean4.Empirical.CSD.VolumeCanonical
public import CsdLean4.Empirical.CSD.Contextuality.MerminPeres

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

@[expose] public section

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
lemma mp_scalar_inner (a b : ℝ) : (inner ℂ (↑a : ℂ) (↑b : ℂ) : ℂ) = ↑(a * b) := by
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

/-! ## The remaining seven square observables

The two reference cells above (`X ⊗ X`, `Z ⊗ Z`) are now extended to the **full**
nine-observable Mermin–Peres square, each with a machine-checked eigenbasis tie to the
genuine Pauli observable (the faithfulness standard set by `mpXXVec_eigenvector`).

```
            col 0        col 1        col 2
row 0     X ⊗ I        I ⊗ X        X ⊗ X      (X ⊗ X done above)
row 1     I ⊗ Z        Z ⊗ I        Z ⊗ Z      (Z ⊗ Z in ContextVolume)
row 2     X ⊗ Z        Z ⊗ X        Y ⊗ Y
```

The eigenbasis of `σ_a ⊗ σ_b` is `(U_a ⊗ U_b)` on the computational basis, `U_a`
diagonalising `σ_a` (`U_Z = I`, `U_X = H`, `U_Y` the `(1, ±i)/√2` frame). Two cells
sharing a single-qubit diagonalising frame on each factor share an eigenbasis, so the
nine observables need only **four** orthonormal frames:

- the **computational** frame `EuclideanSpace.basisFun` (both factors diagonal):
  `Z ⊗ I`, `I ⊗ Z` (and `Z ⊗ Z`);
- the **`H ⊗ I` frame** `mpHIBasis` (`|±⟩ ⊗ eⱼ`, Hadamard on the first factor, the
  second diagonal): `X ⊗ I`, `X ⊗ Z`;
- the **`I ⊗ H` frame** `mpIHBasis` (`eᵢ ⊗ |±⟩`): `I ⊗ X`, `Z ⊗ X`;
- the **`H ⊗ H` frame** `mpXXBasis` (`|±⟩ ⊗ |±⟩`): `X ⊗ X`;
- the **`U_Y ⊗ U_Y` frame** `mpYYBasis` (`|y±⟩ ⊗ |y±⟩`, the complex frame): `Y ⊗ Y`.

Each cell carries: the eigenvalue vector, the `reindex_sigma_ab` matrix identity against
the real `sigma_a ⊗ₖ sigma_b` (the four `finProdFinEquiv.symm` resolutions by `decide`),
the eigenvector lemma `mp_<ab>Vec_eigenvector` (the load-bearing faithfulness fact:
`(σ_a ⊗ σ_b) · vᵢ = eigval i • vᵢ` against the genuine Pauli observable), the
`_blk_eq_zero_iff_eigval_one` block/`+1`-eigenspace certificate, and the volume headline
`mp_<ab>_born_frequency_volume` instantiating `block_born_frequency_volume` on the `+1`
block. Honest scope is unchanged from `mp_xx_born_frequency_volume`: realisation not
derivation (`Φ = id`, FS regions carved in the rotated frame), Gleason-free,
foundational-triple-only; the Mermin–Peres no-go stays at the QM layer. -/

/-- `1/√2` (as `Real.sqrt 2 / 2`), the single-Hadamard component magnitude. -/
noncomputable def invSqrt2 : ℝ := Real.sqrt 2 / 2

/-- `(1/√2)² = 1/2`. -/
lemma invSqrt2_sq : invSqrt2 * invSqrt2 = 1 / 2 := by
  unfold invSqrt2
  rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-! ### The `H ⊗ I` frame `|±⟩ ⊗ eⱼ` (shared by `X ⊗ I` and `X ⊗ Z`) -/

/-- Real `(0, ±1/√2)`-component pattern of the `H ⊗ I` eigenvectors `|±⟩ ⊗ eⱼ`:
`v0 = |+⟩⊗e₀`, `v1 = |+⟩⊗e₁`, `v2 = |−⟩⊗e₀`, `v3 = |−⟩⊗e₁` (flatten `(i,j) ↦ 2i+j`). -/
noncomputable def mpHIReal : Fin 4 → Fin 4 → ℝ :=
  ![![invSqrt2, 0, invSqrt2, 0],
    ![0, invSqrt2, 0, invSqrt2],
    ![invSqrt2, 0, -invSqrt2, 0],
    ![0, invSqrt2, 0, -invSqrt2]]

/-- The `H ⊗ I` eigenvectors as complex coordinate vectors. -/
noncomputable def mpHIVec (i : Fin 4) : EuclideanSpace ℂ (Fin 4) :=
  WithLp.toLp 2 (fun k => ((mpHIReal i k : ℝ) : ℂ))

/-- **The `H ⊗ I` family is orthonormal.** Each squared norm is `2·(1/√2)² = 1`
(`invSqrt2_sq`); off-diagonal products cancel. -/
lemma mpHIVec_orthonormal : Orthonormal ℂ mpHIVec := by
  rw [orthonormal_iff_ite]
  intro a b
  rw [PiLp.inner_apply, Fin.sum_univ_four]
  simp only [mpHIVec, WithLp.ofLp_toLp, mp_scalar_inner]
  fin_cases a <;> fin_cases b <;>
    norm_num [mpHIReal, invSqrt2_sq, mul_neg, neg_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]

/-- The `H ⊗ I` eigenbasis as a Mathlib `OrthonormalBasis`. -/
noncomputable def mpHIBasis :
    OrthonormalBasis (Fin 4) ℂ (EuclideanSpace ℂ (Fin 4)) := by
  refine OrthonormalBasis.mk mpHIVec_orthonormal ?_
  have hcard : Fintype.card (Fin 4) = Module.finrank ℂ (EuclideanSpace ℂ (Fin 4)) := by
    rw [Fintype.card_fin, finrank_euclideanSpace_fin]
  rw [mpHIVec_orthonormal.linearIndependent.span_eq_top_of_card_eq_finrank hcard]

lemma mpHIBasis_apply (i : Fin 4) : mpHIBasis i = mpHIVec i := by
  unfold mpHIBasis; rw [OrthonormalBasis.coe_mk]

/-! ### The `I ⊗ H` frame `eᵢ ⊗ |±⟩` (shared by `I ⊗ X` and `Z ⊗ X`) -/

/-- Real `(0, ±1/√2)`-component pattern of the `I ⊗ H` eigenvectors `eᵢ ⊗ |±⟩`:
`v0 = e₀⊗|+⟩`, `v1 = e₀⊗|−⟩`, `v2 = e₁⊗|+⟩`, `v3 = e₁⊗|−⟩`. -/
noncomputable def mpIHReal : Fin 4 → Fin 4 → ℝ :=
  ![![invSqrt2, invSqrt2, 0, 0],
    ![invSqrt2, -invSqrt2, 0, 0],
    ![0, 0, invSqrt2, invSqrt2],
    ![0, 0, invSqrt2, -invSqrt2]]

/-- The `I ⊗ H` eigenvectors as complex coordinate vectors. -/
noncomputable def mpIHVec (i : Fin 4) : EuclideanSpace ℂ (Fin 4) :=
  WithLp.toLp 2 (fun k => ((mpIHReal i k : ℝ) : ℂ))

/-- **The `I ⊗ H` family is orthonormal.** -/
lemma mpIHVec_orthonormal : Orthonormal ℂ mpIHVec := by
  rw [orthonormal_iff_ite]
  intro a b
  rw [PiLp.inner_apply, Fin.sum_univ_four]
  simp only [mpIHVec, WithLp.ofLp_toLp, mp_scalar_inner]
  fin_cases a <;> fin_cases b <;>
    norm_num [mpIHReal, invSqrt2_sq, mul_neg, neg_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]

/-- The `I ⊗ H` eigenbasis as a Mathlib `OrthonormalBasis`. -/
noncomputable def mpIHBasis :
    OrthonormalBasis (Fin 4) ℂ (EuclideanSpace ℂ (Fin 4)) := by
  refine OrthonormalBasis.mk mpIHVec_orthonormal ?_
  have hcard : Fintype.card (Fin 4) = Module.finrank ℂ (EuclideanSpace ℂ (Fin 4)) := by
    rw [Fintype.card_fin, finrank_euclideanSpace_fin]
  rw [mpIHVec_orthonormal.linearIndependent.span_eq_top_of_card_eq_finrank hcard]

lemma mpIHBasis_apply (i : Fin 4) : mpIHBasis i = mpIHVec i := by
  unfold mpIHBasis; rw [OrthonormalBasis.coe_mk]

/-! ### `X ⊗ I` (`H ⊗ I` frame, eigenvalues `+1,+1,−1,−1`) -/

/-- Eigenvalues of `mpHIVec` under `σx ⊗ I` (`+1` on the `|+⟩` block). -/
def mpXIEigval : Fin 4 → ℂ := ![1, 1, -1, -1]

/-- Sign block of `X ⊗ I`: `+1` eigenspace `{0,1}` ↦ `0`, `−1` `{2,3}` ↦ `1`. -/
def mpXIBlk : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- **`σx ⊗ I` reindexed under `finProdFinEquiv`**, against the genuine `sigmaX`. -/
lemma reindex_sigmaXI :
    Matrix.reindex finProdFinEquiv finProdFinEquiv (sigmaX ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
      = !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; (0 : ℂ), 1, 0, 0] := by
  ext k j
  fin_cases k <;> fin_cases j <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
      sigmaX, show (@finProdFinEquiv 2 2).symm (0 : Fin 4) = (0, 0) from by decide,
      show (@finProdFinEquiv 2 2).symm (1 : Fin 4) = (0, 1) from by decide,
      show (@finProdFinEquiv 2 2).symm (2 : Fin 4) = (1, 0) from by decide,
      show (@finProdFinEquiv 2 2).symm (3 : Fin 4) = (1, 1) from by decide]

/-- **`mpHIVec i` is a genuine eigenvector of the real `σx ⊗ I`.** -/
theorem mpXIVec_eigenvector (i : Fin 4) :
    (Matrix.reindex finProdFinEquiv finProdFinEquiv (sigmaX ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)))
        *ᵥ (mpHIVec i).ofLp
      = mpXIEigval i • (mpHIVec i).ofLp := by
  rw [reindex_sigmaXI]
  funext k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, mpHIVec, mpXIEigval, mpHIReal,
      WithLp.ofLp_toLp, Pi.smul_apply, smul_eq_mul]

/-- The `+1` block of `mpXIBlk` is exactly the `+1` eigenspace. -/
theorem mpXIBlk_eq_zero_iff_eigval_one (i : Fin 4) :
    mpXIBlk i = 0 ↔ mpXIEigval i = 1 := by
  fin_cases i <;> simp [mpXIBlk, mpXIEigval] <;> norm_num

/-- **`X ⊗ I = +1` Born weight as a block sum of FS volumes.** Instantiation of
`block_born_frequency_volume` at `mpHIBasis`, `mpXIBlk`, `a = 0`; the `+1` block `{0,1}`
is collapsed via `Finset.sum_pair`. Eigenbasis faithfulness is `mpXIVec_eigenvector`. -/
theorem mp_xi_born_frequency_volume
    (p₀ : CPN 4)
    (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ‖ψ‖ = 1)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 4) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ i : Fin 4,
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' bornRegion (mpHIBasis.repr ψ) (repr_ne_zero mpHIBasis ψ hψ) i)
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun m : ℕ =>
          ∑ i ∈ Finset.univ.filter (fun i => mpXIBlk i = 0),
            (∑ k ∈ Finset.range m,
                Set.indicator
                  ((X k) ⁻¹' bornRegion (mpHIBasis.repr ψ)
                    (repr_ne_zero mpHIBasis ψ hψ) i)
                  (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (mpHIVec 0) ψ‖ ^ 2 + ‖inner ℂ (mpHIVec 1) ψ‖ ^ 2)) := by
  have h := block_born_frequency_volume p₀ mpHIBasis ψ hψ mpXIBlk 0 X hX hlaw hindep
  have hsum :
      (∑ i ∈ Finset.univ.filter (fun i => mpXIBlk i = 0),
          ‖inner ℂ (mpHIBasis i) ψ‖ ^ 2)
        = ‖inner ℂ (mpHIVec 0) ψ‖ ^ 2 + ‖inner ℂ (mpHIVec 1) ψ‖ ^ 2 := by
    rw [show (Finset.univ.filter (fun i => mpXIBlk i = 0)) = {0, 1} from by decide,
      Finset.sum_pair (by decide : (0 : Fin 4) ≠ 1),
      mpHIBasis_apply, mpHIBasis_apply]
  rw [← hsum]
  exact h

/-- `mp_xi_born_frequency_volume` on the canonical FS trial witness. -/
theorem mp_xi_born_frequency_volume_canonical
    (p₀ : CPN 4)
    (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ‖ψ‖ = 1) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀,
      Tendsto
        (fun m : ℕ =>
          ∑ i ∈ Finset.univ.filter (fun i => mpXIBlk i = 0),
            (∑ k ∈ Finset.range m,
                Set.indicator
                  ((fsTrial 4 k) ⁻¹' bornRegion (mpHIBasis.repr ψ)
                    (repr_ne_zero mpHIBasis ψ hψ) i)
                  (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (mpHIVec 0) ψ‖ ^ 2 + ‖inner ℂ (mpHIVec 1) ψ‖ ^ 2)) :=
  mp_xi_born_frequency_volume p₀ ψ hψ
    (fsTrial 4) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀
      (bornRegion (mpHIBasis.repr ψ) (repr_ne_zero mpHIBasis ψ hψ))
      (bornRegion_measurable_uncond (mpHIBasis.repr ψ) (repr_ne_zero mpHIBasis ψ hψ)))

/-! ### `X ⊗ Z` (`H ⊗ I` frame, eigenvalues `+1,−1,−1,+1`) -/

/-- Eigenvalues of `mpHIVec` under `σx ⊗ σz`. -/
def mpXZEigval : Fin 4 → ℂ := ![1, -1, -1, 1]

/-- Sign-parity block of `X ⊗ Z`: `+1` eigenspace `{0,3}` ↦ `0`. -/
def mpXZBlk : Fin 4 → Fin 2 := ![0, 1, 1, 0]

/-- **`σx ⊗ σz` reindexed under `finProdFinEquiv`**, against the genuine Pauli factors. -/
lemma reindex_sigmaXZ :
    Matrix.reindex finProdFinEquiv finProdFinEquiv (sigmaX ⊗ₖ sigmaZ)
      = !![0, 0, 1, 0; 0, 0, 0, -1; 1, 0, 0, 0; (0 : ℂ), -1, 0, 0] := by
  ext k j
  fin_cases k <;> fin_cases j <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
      sigmaZ, sigmaX, show (@finProdFinEquiv 2 2).symm (0 : Fin 4) = (0, 0) from by decide,
      show (@finProdFinEquiv 2 2).symm (1 : Fin 4) = (0, 1) from by decide,
      show (@finProdFinEquiv 2 2).symm (2 : Fin 4) = (1, 0) from by decide,
      show (@finProdFinEquiv 2 2).symm (3 : Fin 4) = (1, 1) from by decide]

/-- **`mpHIVec i` is a genuine eigenvector of the real `σx ⊗ σz`.** -/
theorem mpXZVec_eigenvector (i : Fin 4) :
    (Matrix.reindex finProdFinEquiv finProdFinEquiv (sigmaX ⊗ₖ sigmaZ)) *ᵥ (mpHIVec i).ofLp
      = mpXZEigval i • (mpHIVec i).ofLp := by
  rw [reindex_sigmaXZ]
  funext k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, mpHIVec, mpXZEigval, mpHIReal,
      WithLp.ofLp_toLp, Pi.smul_apply, smul_eq_mul]

/-- The `+1` block of `mpXZBlk` is exactly the `+1` eigenspace. -/
theorem mpXZBlk_eq_zero_iff_eigval_one (i : Fin 4) :
    mpXZBlk i = 0 ↔ mpXZEigval i = 1 := by
  fin_cases i <;> simp [mpXZBlk, mpXZEigval] <;> norm_num

/-- **`X ⊗ Z = +1` Born weight as a block sum of FS volumes.** Same `H ⊗ I` frame as
`X ⊗ I`, different observable (eigenvalues `+1,−1,−1,+1`); `+1` block `{0,3}`. -/
theorem mp_xz_born_frequency_volume
    (p₀ : CPN 4)
    (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ‖ψ‖ = 1)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 4) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ i : Fin 4,
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' bornRegion (mpHIBasis.repr ψ) (repr_ne_zero mpHIBasis ψ hψ) i)
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun m : ℕ =>
          ∑ i ∈ Finset.univ.filter (fun i => mpXZBlk i = 0),
            (∑ k ∈ Finset.range m,
                Set.indicator
                  ((X k) ⁻¹' bornRegion (mpHIBasis.repr ψ)
                    (repr_ne_zero mpHIBasis ψ hψ) i)
                  (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (mpHIVec 0) ψ‖ ^ 2 + ‖inner ℂ (mpHIVec 3) ψ‖ ^ 2)) := by
  have h := block_born_frequency_volume p₀ mpHIBasis ψ hψ mpXZBlk 0 X hX hlaw hindep
  have hsum :
      (∑ i ∈ Finset.univ.filter (fun i => mpXZBlk i = 0),
          ‖inner ℂ (mpHIBasis i) ψ‖ ^ 2)
        = ‖inner ℂ (mpHIVec 0) ψ‖ ^ 2 + ‖inner ℂ (mpHIVec 3) ψ‖ ^ 2 := by
    rw [show (Finset.univ.filter (fun i => mpXZBlk i = 0)) = {0, 3} from by decide,
      Finset.sum_pair (by decide : (0 : Fin 4) ≠ 3),
      mpHIBasis_apply, mpHIBasis_apply]
  rw [← hsum]
  exact h

/-- `mp_xz_born_frequency_volume` on the canonical FS trial witness. -/
theorem mp_xz_born_frequency_volume_canonical
    (p₀ : CPN 4)
    (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ‖ψ‖ = 1) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀,
      Tendsto
        (fun m : ℕ =>
          ∑ i ∈ Finset.univ.filter (fun i => mpXZBlk i = 0),
            (∑ k ∈ Finset.range m,
                Set.indicator
                  ((fsTrial 4 k) ⁻¹' bornRegion (mpHIBasis.repr ψ)
                    (repr_ne_zero mpHIBasis ψ hψ) i)
                  (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (mpHIVec 0) ψ‖ ^ 2 + ‖inner ℂ (mpHIVec 3) ψ‖ ^ 2)) :=
  mp_xz_born_frequency_volume p₀ ψ hψ
    (fsTrial 4) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀
      (bornRegion (mpHIBasis.repr ψ) (repr_ne_zero mpHIBasis ψ hψ))
      (bornRegion_measurable_uncond (mpHIBasis.repr ψ) (repr_ne_zero mpHIBasis ψ hψ)))

/-! ### `I ⊗ X` (`I ⊗ H` frame, eigenvalues `+1,−1,+1,−1`) -/

/-- Eigenvalues of `mpIHVec` under `I ⊗ σx`. -/
def mpIXEigval : Fin 4 → ℂ := ![1, -1, 1, -1]

/-- Sign block of `I ⊗ X`: `+1` eigenspace `{0,2}` ↦ `0`. -/
def mpIXBlk : Fin 4 → Fin 2 := ![0, 1, 0, 1]

/-- **`I ⊗ σx` reindexed under `finProdFinEquiv`**, against the genuine `sigmaX`. -/
lemma reindex_sigmaIX :
    Matrix.reindex finProdFinEquiv finProdFinEquiv ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ sigmaX)
      = !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; (0 : ℂ), 0, 1, 0] := by
  ext k j
  fin_cases k <;> fin_cases j <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
      sigmaX, show (@finProdFinEquiv 2 2).symm (0 : Fin 4) = (0, 0) from by decide,
      show (@finProdFinEquiv 2 2).symm (1 : Fin 4) = (0, 1) from by decide,
      show (@finProdFinEquiv 2 2).symm (2 : Fin 4) = (1, 0) from by decide,
      show (@finProdFinEquiv 2 2).symm (3 : Fin 4) = (1, 1) from by decide]

/-- **`mpIHVec i` is a genuine eigenvector of the real `I ⊗ σx`.** -/
theorem mpIXVec_eigenvector (i : Fin 4) :
    (Matrix.reindex finProdFinEquiv finProdFinEquiv ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ sigmaX))
        *ᵥ (mpIHVec i).ofLp
      = mpIXEigval i • (mpIHVec i).ofLp := by
  rw [reindex_sigmaIX]
  funext k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, mpIHVec, mpIXEigval, mpIHReal,
      WithLp.ofLp_toLp, Pi.smul_apply, smul_eq_mul]

/-- The `+1` block of `mpIXBlk` is exactly the `+1` eigenspace. -/
theorem mpIXBlk_eq_zero_iff_eigval_one (i : Fin 4) :
    mpIXBlk i = 0 ↔ mpIXEigval i = 1 := by
  fin_cases i <;> simp [mpIXBlk, mpIXEigval] <;> norm_num

/-- **`I ⊗ X = +1` Born weight as a block sum of FS volumes.** -/
theorem mp_ix_born_frequency_volume
    (p₀ : CPN 4)
    (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ‖ψ‖ = 1)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 4) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ i : Fin 4,
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' bornRegion (mpIHBasis.repr ψ) (repr_ne_zero mpIHBasis ψ hψ) i)
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun m : ℕ =>
          ∑ i ∈ Finset.univ.filter (fun i => mpIXBlk i = 0),
            (∑ k ∈ Finset.range m,
                Set.indicator
                  ((X k) ⁻¹' bornRegion (mpIHBasis.repr ψ)
                    (repr_ne_zero mpIHBasis ψ hψ) i)
                  (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (mpIHVec 0) ψ‖ ^ 2 + ‖inner ℂ (mpIHVec 2) ψ‖ ^ 2)) := by
  have h := block_born_frequency_volume p₀ mpIHBasis ψ hψ mpIXBlk 0 X hX hlaw hindep
  have hsum :
      (∑ i ∈ Finset.univ.filter (fun i => mpIXBlk i = 0),
          ‖inner ℂ (mpIHBasis i) ψ‖ ^ 2)
        = ‖inner ℂ (mpIHVec 0) ψ‖ ^ 2 + ‖inner ℂ (mpIHVec 2) ψ‖ ^ 2 := by
    rw [show (Finset.univ.filter (fun i => mpIXBlk i = 0)) = {0, 2} from by decide,
      Finset.sum_pair (by decide : (0 : Fin 4) ≠ 2),
      mpIHBasis_apply, mpIHBasis_apply]
  rw [← hsum]
  exact h

/-- `mp_ix_born_frequency_volume` on the canonical FS trial witness. -/
theorem mp_ix_born_frequency_volume_canonical
    (p₀ : CPN 4)
    (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ‖ψ‖ = 1) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀,
      Tendsto
        (fun m : ℕ =>
          ∑ i ∈ Finset.univ.filter (fun i => mpIXBlk i = 0),
            (∑ k ∈ Finset.range m,
                Set.indicator
                  ((fsTrial 4 k) ⁻¹' bornRegion (mpIHBasis.repr ψ)
                    (repr_ne_zero mpIHBasis ψ hψ) i)
                  (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (mpIHVec 0) ψ‖ ^ 2 + ‖inner ℂ (mpIHVec 2) ψ‖ ^ 2)) :=
  mp_ix_born_frequency_volume p₀ ψ hψ
    (fsTrial 4) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀
      (bornRegion (mpIHBasis.repr ψ) (repr_ne_zero mpIHBasis ψ hψ))
      (bornRegion_measurable_uncond (mpIHBasis.repr ψ) (repr_ne_zero mpIHBasis ψ hψ)))

/-! ### `Z ⊗ X` (`I ⊗ H` frame, eigenvalues `+1,−1,−1,+1`) -/

/-- Eigenvalues of `mpIHVec` under `σz ⊗ σx`. -/
def mpZXEigval : Fin 4 → ℂ := ![1, -1, -1, 1]

/-- Sign-parity block of `Z ⊗ X`: `+1` eigenspace `{0,3}` ↦ `0`. -/
def mpZXBlk : Fin 4 → Fin 2 := ![0, 1, 1, 0]

/-- **`σz ⊗ σx` reindexed under `finProdFinEquiv`**, against the genuine Pauli factors. -/
lemma reindex_sigmaZX :
    Matrix.reindex finProdFinEquiv finProdFinEquiv (sigmaZ ⊗ₖ sigmaX)
      = !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; (0 : ℂ), 0, -1, 0] := by
  ext k j
  fin_cases k <;> fin_cases j <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
      sigmaZ, sigmaX, show (@finProdFinEquiv 2 2).symm (0 : Fin 4) = (0, 0) from by decide,
      show (@finProdFinEquiv 2 2).symm (1 : Fin 4) = (0, 1) from by decide,
      show (@finProdFinEquiv 2 2).symm (2 : Fin 4) = (1, 0) from by decide,
      show (@finProdFinEquiv 2 2).symm (3 : Fin 4) = (1, 1) from by decide]

/-- **`mpIHVec i` is a genuine eigenvector of the real `σz ⊗ σx`.** -/
theorem mpZXVec_eigenvector (i : Fin 4) :
    (Matrix.reindex finProdFinEquiv finProdFinEquiv (sigmaZ ⊗ₖ sigmaX)) *ᵥ (mpIHVec i).ofLp
      = mpZXEigval i • (mpIHVec i).ofLp := by
  rw [reindex_sigmaZX]
  funext k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, mpIHVec, mpZXEigval, mpIHReal,
      WithLp.ofLp_toLp, Pi.smul_apply, smul_eq_mul]

/-- The `+1` block of `mpZXBlk` is exactly the `+1` eigenspace. -/
theorem mpZXBlk_eq_zero_iff_eigval_one (i : Fin 4) :
    mpZXBlk i = 0 ↔ mpZXEigval i = 1 := by
  fin_cases i <;> simp [mpZXBlk, mpZXEigval] <;> norm_num

/-- **`Z ⊗ X = +1` Born weight as a block sum of FS volumes.** -/
theorem mp_zx_born_frequency_volume
    (p₀ : CPN 4)
    (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ‖ψ‖ = 1)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 4) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ i : Fin 4,
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' bornRegion (mpIHBasis.repr ψ) (repr_ne_zero mpIHBasis ψ hψ) i)
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun m : ℕ =>
          ∑ i ∈ Finset.univ.filter (fun i => mpZXBlk i = 0),
            (∑ k ∈ Finset.range m,
                Set.indicator
                  ((X k) ⁻¹' bornRegion (mpIHBasis.repr ψ)
                    (repr_ne_zero mpIHBasis ψ hψ) i)
                  (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (mpIHVec 0) ψ‖ ^ 2 + ‖inner ℂ (mpIHVec 3) ψ‖ ^ 2)) := by
  have h := block_born_frequency_volume p₀ mpIHBasis ψ hψ mpZXBlk 0 X hX hlaw hindep
  have hsum :
      (∑ i ∈ Finset.univ.filter (fun i => mpZXBlk i = 0),
          ‖inner ℂ (mpIHBasis i) ψ‖ ^ 2)
        = ‖inner ℂ (mpIHVec 0) ψ‖ ^ 2 + ‖inner ℂ (mpIHVec 3) ψ‖ ^ 2 := by
    rw [show (Finset.univ.filter (fun i => mpZXBlk i = 0)) = {0, 3} from by decide,
      Finset.sum_pair (by decide : (0 : Fin 4) ≠ 3),
      mpIHBasis_apply, mpIHBasis_apply]
  rw [← hsum]
  exact h

/-- `mp_zx_born_frequency_volume` on the canonical FS trial witness. -/
theorem mp_zx_born_frequency_volume_canonical
    (p₀ : CPN 4)
    (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ‖ψ‖ = 1) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀,
      Tendsto
        (fun m : ℕ =>
          ∑ i ∈ Finset.univ.filter (fun i => mpZXBlk i = 0),
            (∑ k ∈ Finset.range m,
                Set.indicator
                  ((fsTrial 4 k) ⁻¹' bornRegion (mpIHBasis.repr ψ)
                    (repr_ne_zero mpIHBasis ψ hψ) i)
                  (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (mpIHVec 0) ψ‖ ^ 2 + ‖inner ℂ (mpIHVec 3) ψ‖ ^ 2)) :=
  mp_zx_born_frequency_volume p₀ ψ hψ
    (fsTrial 4) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀
      (bornRegion (mpIHBasis.repr ψ) (repr_ne_zero mpIHBasis ψ hψ))
      (bornRegion_measurable_uncond (mpIHBasis.repr ψ) (repr_ne_zero mpIHBasis ψ hψ)))

/-! ### `Z ⊗ I` and `I ⊗ Z` (computational frame `EuclideanSpace.basisFun`)

Both are diagonal in the computational basis, so the engine frame is
`EuclideanSpace.basisFun (Fin 4) ℂ` (no rotation), exactly as for `Z ⊗ Z`. The
eigenvector lemmas certify the computational basis vectors `EuclideanSpace.single i 1`
are genuine `σz ⊗ I` / `I ⊗ σz` eigenvectors against the real `sigmaZ`. -/

/-- Eigenvalues of the computational basis under `σz ⊗ I`. -/
def mpZIEigval : Fin 4 → ℂ := ![1, 1, -1, -1]

/-- **`σz ⊗ I` reindexed under `finProdFinEquiv` is `diag(1,1,−1,−1)`.** -/
lemma reindex_sigmaZI :
    Matrix.reindex finProdFinEquiv finProdFinEquiv (sigmaZ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
      = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; (0 : ℂ), 0, 0, -1] := by
  ext k j
  fin_cases k <;> fin_cases j <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
      sigmaZ, show (@finProdFinEquiv 2 2).symm (0 : Fin 4) = (0, 0) from by decide,
      show (@finProdFinEquiv 2 2).symm (1 : Fin 4) = (0, 1) from by decide,
      show (@finProdFinEquiv 2 2).symm (2 : Fin 4) = (1, 0) from by decide,
      show (@finProdFinEquiv 2 2).symm (3 : Fin 4) = (1, 1) from by decide]

/-- **The computational basis vector `eᵢ` is a genuine eigenvector of the real `σz ⊗ I`.** -/
theorem mpZIVec_eigenvector (i : Fin 4) :
    (Matrix.reindex finProdFinEquiv finProdFinEquiv (sigmaZ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)))
        *ᵥ (EuclideanSpace.single i (1 : ℂ)).ofLp
      = mpZIEigval i • (EuclideanSpace.single i (1 : ℂ)).ofLp := by
  rw [reindex_sigmaZI]
  funext k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, mpZIEigval, EuclideanSpace.single,
      Pi.smul_apply, smul_eq_mul]

/-- The `+1` block of the `Z ⊗ I` grouping `![0,0,1,1]` is exactly the `+1` eigenspace. -/
theorem mpZIBlk_eq_zero_iff_eigval_one (i : Fin 4) :
    (![0, 0, 1, 1] : Fin 4 → Fin 2) i = 0 ↔ mpZIEigval i = 1 := by
  fin_cases i <;> simp [mpZIEigval] <;> norm_num

/-- **`Z ⊗ I = +1` Born weight as a block sum of FS volumes** (computational frame). -/
theorem mp_zi_born_frequency_volume
    (p₀ : CPN 4)
    (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ‖ψ‖ = 1)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 4) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ i : Fin 4,
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' bornRegion ((EuclideanSpace.basisFun (Fin 4) ℂ).repr ψ)
              (repr_ne_zero (EuclideanSpace.basisFun (Fin 4) ℂ) ψ hψ) i)
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun m : ℕ =>
          ∑ i ∈ Finset.univ.filter (fun i => (![0, 0, 1, 1] : Fin 4 → Fin 2) i = 0),
            (∑ k ∈ Finset.range m,
                Set.indicator
                  ((X k) ⁻¹' bornRegion ((EuclideanSpace.basisFun (Fin 4) ℂ).repr ψ)
                    (repr_ne_zero (EuclideanSpace.basisFun (Fin 4) ℂ) ψ hψ) i)
                  (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single (0 : Fin 4) (1 : ℂ)) ψ‖ ^ 2
          + ‖inner ℂ (EuclideanSpace.single (1 : Fin 4) (1 : ℂ)) ψ‖ ^ 2)) := by
  have h := block_born_frequency_volume p₀ (EuclideanSpace.basisFun (Fin 4) ℂ) ψ hψ
    (![0, 0, 1, 1] : Fin 4 → Fin 2) 0 X hX hlaw hindep
  have hsum :
      (∑ i ∈ Finset.univ.filter (fun i => (![0, 0, 1, 1] : Fin 4 → Fin 2) i = 0),
          ‖inner ℂ ((EuclideanSpace.basisFun (Fin 4) ℂ) i) ψ‖ ^ 2)
        = ‖inner ℂ (EuclideanSpace.single (0 : Fin 4) (1 : ℂ)) ψ‖ ^ 2
          + ‖inner ℂ (EuclideanSpace.single (1 : Fin 4) (1 : ℂ)) ψ‖ ^ 2 := by
    rw [show (Finset.univ.filter (fun i => (![0, 0, 1, 1] : Fin 4 → Fin 2) i = 0))
          = {0, 1} from by decide,
      Finset.sum_pair (by decide : (0 : Fin 4) ≠ 1),
      EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_apply]
  rw [← hsum]
  exact h

/-- `mp_zi_born_frequency_volume` on the canonical FS trial witness. -/
theorem mp_zi_born_frequency_volume_canonical
    (p₀ : CPN 4)
    (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ‖ψ‖ = 1) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀,
      Tendsto
        (fun m : ℕ =>
          ∑ i ∈ Finset.univ.filter (fun i => (![0, 0, 1, 1] : Fin 4 → Fin 2) i = 0),
            (∑ k ∈ Finset.range m,
                Set.indicator
                  ((fsTrial 4 k) ⁻¹' bornRegion ((EuclideanSpace.basisFun (Fin 4) ℂ).repr ψ)
                    (repr_ne_zero (EuclideanSpace.basisFun (Fin 4) ℂ) ψ hψ) i)
                  (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single (0 : Fin 4) (1 : ℂ)) ψ‖ ^ 2
          + ‖inner ℂ (EuclideanSpace.single (1 : Fin 4) (1 : ℂ)) ψ‖ ^ 2)) :=
  mp_zi_born_frequency_volume p₀ ψ hψ
    (fsTrial 4) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀
      (bornRegion ((EuclideanSpace.basisFun (Fin 4) ℂ).repr ψ)
        (repr_ne_zero (EuclideanSpace.basisFun (Fin 4) ℂ) ψ hψ))
      (bornRegion_measurable_uncond ((EuclideanSpace.basisFun (Fin 4) ℂ).repr ψ)
        (repr_ne_zero (EuclideanSpace.basisFun (Fin 4) ℂ) ψ hψ)))

/-- Eigenvalues of the computational basis under `I ⊗ σz`. -/
def mpIZEigval : Fin 4 → ℂ := ![1, -1, 1, -1]

/-- **`I ⊗ σz` reindexed under `finProdFinEquiv` is `diag(1,−1,1,−1)`.** -/
lemma reindex_sigmaIZ :
    Matrix.reindex finProdFinEquiv finProdFinEquiv ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ sigmaZ)
      = !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; (0 : ℂ), 0, 0, -1] := by
  ext k j
  fin_cases k <;> fin_cases j <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
      sigmaZ, show (@finProdFinEquiv 2 2).symm (0 : Fin 4) = (0, 0) from by decide,
      show (@finProdFinEquiv 2 2).symm (1 : Fin 4) = (0, 1) from by decide,
      show (@finProdFinEquiv 2 2).symm (2 : Fin 4) = (1, 0) from by decide,
      show (@finProdFinEquiv 2 2).symm (3 : Fin 4) = (1, 1) from by decide]

/-- **The computational basis vector `eᵢ` is a genuine eigenvector of the real `I ⊗ σz`.** -/
theorem mpIZVec_eigenvector (i : Fin 4) :
    (Matrix.reindex finProdFinEquiv finProdFinEquiv ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ sigmaZ))
        *ᵥ (EuclideanSpace.single i (1 : ℂ)).ofLp
      = mpIZEigval i • (EuclideanSpace.single i (1 : ℂ)).ofLp := by
  rw [reindex_sigmaIZ]
  funext k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, mpIZEigval, EuclideanSpace.single,
      Pi.smul_apply, smul_eq_mul]

/-- The `+1` block of the `I ⊗ Z` grouping `![0,1,0,1]` is exactly the `+1` eigenspace. -/
theorem mpIZBlk_eq_zero_iff_eigval_one (i : Fin 4) :
    (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 0 ↔ mpIZEigval i = 1 := by
  fin_cases i <;> simp [mpIZEigval] <;> norm_num

/-- **`I ⊗ Z = +1` Born weight as a block sum of FS volumes** (computational frame). -/
theorem mp_iz_born_frequency_volume
    (p₀ : CPN 4)
    (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ‖ψ‖ = 1)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 4) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ i : Fin 4,
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' bornRegion ((EuclideanSpace.basisFun (Fin 4) ℂ).repr ψ)
              (repr_ne_zero (EuclideanSpace.basisFun (Fin 4) ℂ) ψ hψ) i)
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun m : ℕ =>
          ∑ i ∈ Finset.univ.filter (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 0),
            (∑ k ∈ Finset.range m,
                Set.indicator
                  ((X k) ⁻¹' bornRegion ((EuclideanSpace.basisFun (Fin 4) ℂ).repr ψ)
                    (repr_ne_zero (EuclideanSpace.basisFun (Fin 4) ℂ) ψ hψ) i)
                  (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single (0 : Fin 4) (1 : ℂ)) ψ‖ ^ 2
          + ‖inner ℂ (EuclideanSpace.single (2 : Fin 4) (1 : ℂ)) ψ‖ ^ 2)) := by
  have h := block_born_frequency_volume p₀ (EuclideanSpace.basisFun (Fin 4) ℂ) ψ hψ
    (![0, 1, 0, 1] : Fin 4 → Fin 2) 0 X hX hlaw hindep
  have hsum :
      (∑ i ∈ Finset.univ.filter (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 0),
          ‖inner ℂ ((EuclideanSpace.basisFun (Fin 4) ℂ) i) ψ‖ ^ 2)
        = ‖inner ℂ (EuclideanSpace.single (0 : Fin 4) (1 : ℂ)) ψ‖ ^ 2
          + ‖inner ℂ (EuclideanSpace.single (2 : Fin 4) (1 : ℂ)) ψ‖ ^ 2 := by
    rw [show (Finset.univ.filter (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 0))
          = {0, 2} from by decide,
      Finset.sum_pair (by decide : (0 : Fin 4) ≠ 2),
      EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_apply]
  rw [← hsum]
  exact h

/-- `mp_iz_born_frequency_volume` on the canonical FS trial witness. -/
theorem mp_iz_born_frequency_volume_canonical
    (p₀ : CPN 4)
    (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ‖ψ‖ = 1) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀,
      Tendsto
        (fun m : ℕ =>
          ∑ i ∈ Finset.univ.filter (fun i => (![0, 1, 0, 1] : Fin 4 → Fin 2) i = 0),
            (∑ k ∈ Finset.range m,
                Set.indicator
                  ((fsTrial 4 k) ⁻¹' bornRegion ((EuclideanSpace.basisFun (Fin 4) ℂ).repr ψ)
                    (repr_ne_zero (EuclideanSpace.basisFun (Fin 4) ℂ) ψ hψ) i)
                  (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single (0 : Fin 4) (1 : ℂ)) ψ‖ ^ 2
          + ‖inner ℂ (EuclideanSpace.single (2 : Fin 4) (1 : ℂ)) ψ‖ ^ 2)) :=
  mp_iz_born_frequency_volume p₀ ψ hψ
    (fsTrial 4) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀
      (bornRegion ((EuclideanSpace.basisFun (Fin 4) ℂ).repr ψ)
        (repr_ne_zero (EuclideanSpace.basisFun (Fin 4) ℂ) ψ hψ))
      (bornRegion_measurable_uncond ((EuclideanSpace.basisFun (Fin 4) ℂ).repr ψ)
        (repr_ne_zero (EuclideanSpace.basisFun (Fin 4) ℂ) ψ hψ)))

/-! ### `Y ⊗ Y` (the complex `U_Y ⊗ U_Y` frame `|y±⟩ ⊗ |y±⟩`)

The remaining cell. `U_Y` diagonalises `σy` with columns `|y±⟩ = (1, ±i)/√2`; the
product eigenbasis `|y±⟩ ⊗ |y±⟩` has **complex** `(±1/2, ±i/2)` components, so the
orthonormality and eigenvector proofs run over `ℂ` directly (not the real-coercion
`mp_scalar_inner` route). This closes the `Y ⊗ Y` cell — and the full square. -/

/-- The four `Y ⊗ Y` eigenvectors `|y±⟩ ⊗ |y±⟩` with explicit complex `(±1/2, ±i/2)`
components: `v0 = |y+⟩⊗|y+⟩`, `v1 = |y+⟩⊗|y−⟩`, `v2 = |y−⟩⊗|y+⟩`, `v3 = |y−⟩⊗|y−⟩`. -/
noncomputable def mpYYVec : Fin 4 → EuclideanSpace ℂ (Fin 4) :=
  ![WithLp.toLp 2 ![1/2, Complex.I/2, Complex.I/2, -1/2],
    WithLp.toLp 2 ![1/2, -Complex.I/2, Complex.I/2, 1/2],
    WithLp.toLp 2 ![1/2, Complex.I/2, -Complex.I/2, 1/2],
    WithLp.toLp 2 ![1/2, -Complex.I/2, -Complex.I/2, -1/2]]

/-- **The `U_Y ⊗ U_Y` family is orthonormal.** Direct complex computation: each squared
norm is `4·(1/2)² = 1`; off-diagonal inner products cancel (`Complex.conj_I`). -/
lemma mpYYVec_orthonormal : Orthonormal ℂ mpYYVec := by
  rw [orthonormal_iff_ite]
  intro a b
  rw [PiLp.inner_apply, Fin.sum_univ_four]
  fin_cases a <;> fin_cases b <;>
    simp only [mpYYVec, RCLike.inner_apply] <;>
    rw [Complex.ext_iff] <;>
    constructor <;>
    simp [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.normSq] <;> norm_num

/-- The `Y ⊗ Y` eigenbasis as a Mathlib `OrthonormalBasis`. -/
noncomputable def mpYYBasis :
    OrthonormalBasis (Fin 4) ℂ (EuclideanSpace ℂ (Fin 4)) := by
  refine OrthonormalBasis.mk mpYYVec_orthonormal ?_
  have hcard : Fintype.card (Fin 4) = Module.finrank ℂ (EuclideanSpace ℂ (Fin 4)) := by
    rw [Fintype.card_fin, finrank_euclideanSpace_fin]
  rw [mpYYVec_orthonormal.linearIndependent.span_eq_top_of_card_eq_finrank hcard]

lemma mpYYBasis_apply (i : Fin 4) : mpYYBasis i = mpYYVec i := by
  unfold mpYYBasis; rw [OrthonormalBasis.coe_mk]

/-- Eigenvalues of `mpYYVec` under `σy ⊗ σy` (`+1` on the `|y+y+⟩,|y−y−⟩` block). -/
def mpYYEigval : Fin 4 → ℂ := ![1, -1, -1, 1]

/-- Sign-parity block of `Y ⊗ Y`: `+1` eigenspace `{0,3}` ↦ `0`. -/
def mpYYBlk : Fin 4 → Fin 2 := ![0, 1, 1, 0]

/-- **`σy ⊗ σy` reindexed under `finProdFinEquiv`**, against the genuine `sigmaY`. -/
lemma reindex_sigmaYY :
    Matrix.reindex finProdFinEquiv finProdFinEquiv (sigmaY ⊗ₖ sigmaY)
      = !![0, 0, 0, -1; 0, 0, 1, 0; 0, 1, 0, 0; (-1 : ℂ), 0, 0, 0] := by
  ext k j
  fin_cases k <;> fin_cases j <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
      sigmaY, Complex.I_mul_I,
      show (@finProdFinEquiv 2 2).symm (0 : Fin 4) = (0, 0) from by decide,
      show (@finProdFinEquiv 2 2).symm (1 : Fin 4) = (0, 1) from by decide,
      show (@finProdFinEquiv 2 2).symm (2 : Fin 4) = (1, 0) from by decide,
      show (@finProdFinEquiv 2 2).symm (3 : Fin 4) = (1, 1) from by decide]

/-- **`mpYYVec i` is a genuine eigenvector of the real `σy ⊗ σy`.** The load-bearing
faithfulness lemma for the hard (complex) cell, against the actual Pauli observable
`sigmaY ⊗ₖ sigmaY` reindexed onto `Fin 4`. -/
theorem mpYYVec_eigenvector (i : Fin 4) :
    (Matrix.reindex finProdFinEquiv finProdFinEquiv (sigmaY ⊗ₖ sigmaY)) *ᵥ (mpYYVec i).ofLp
      = mpYYEigval i • (mpYYVec i).ofLp := by
  rw [reindex_sigmaYY]
  funext k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, mpYYVec, mpYYEigval,
      WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
      Pi.smul_apply, smul_eq_mul] <;> ring_nf

/-- The `+1` block of `mpYYBlk` is exactly the `+1` eigenspace. -/
theorem mpYYBlk_eq_zero_iff_eigval_one (i : Fin 4) :
    mpYYBlk i = 0 ↔ mpYYEigval i = 1 := by
  fin_cases i <;> simp [mpYYBlk, mpYYEigval] <;> norm_num

/-- **`Y ⊗ Y = +1` Born weight as a block sum of FS volumes.** The complex-frame cell,
completing the square. Instantiation of `block_born_frequency_volume` at `mpYYBasis`,
`mpYYBlk`, `a = 0`; the `+1` block `{0,3}`. Eigenbasis faithfulness is
`mpYYVec_eigenvector` against the genuine `σy ⊗ σy`. -/
theorem mp_yy_born_frequency_volume
    (p₀ : CPN 4)
    (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ‖ψ‖ = 1)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 4) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ i : Fin 4,
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' bornRegion (mpYYBasis.repr ψ) (repr_ne_zero mpYYBasis ψ hψ) i)
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Tendsto
        (fun m : ℕ =>
          ∑ i ∈ Finset.univ.filter (fun i => mpYYBlk i = 0),
            (∑ k ∈ Finset.range m,
                Set.indicator
                  ((X k) ⁻¹' bornRegion (mpYYBasis.repr ψ)
                    (repr_ne_zero mpYYBasis ψ hψ) i)
                  (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (mpYYVec 0) ψ‖ ^ 2 + ‖inner ℂ (mpYYVec 3) ψ‖ ^ 2)) := by
  have h := block_born_frequency_volume p₀ mpYYBasis ψ hψ mpYYBlk 0 X hX hlaw hindep
  have hsum :
      (∑ i ∈ Finset.univ.filter (fun i => mpYYBlk i = 0),
          ‖inner ℂ (mpYYBasis i) ψ‖ ^ 2)
        = ‖inner ℂ (mpYYVec 0) ψ‖ ^ 2 + ‖inner ℂ (mpYYVec 3) ψ‖ ^ 2 := by
    rw [show (Finset.univ.filter (fun i => mpYYBlk i = 0)) = {0, 3} from by decide,
      Finset.sum_pair (by decide : (0 : Fin 4) ≠ 3),
      mpYYBasis_apply, mpYYBasis_apply]
  rw [← hsum]
  exact h

/-- `mp_yy_born_frequency_volume` on the canonical FS trial witness. -/
theorem mp_yy_born_frequency_volume_canonical
    (p₀ : CPN 4)
    (ψ : EuclideanSpace ℂ (Fin 4)) (hψ : ‖ψ‖ = 1) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀,
      Tendsto
        (fun m : ℕ =>
          ∑ i ∈ Finset.univ.filter (fun i => mpYYBlk i = 0),
            (∑ k ∈ Finset.range m,
                Set.indicator
                  ((fsTrial 4 k) ⁻¹' bornRegion (mpYYBasis.repr ψ)
                    (repr_ne_zero mpYYBasis ψ hψ) i)
                  (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (mpYYVec 0) ψ‖ ^ 2 + ‖inner ℂ (mpYYVec 3) ψ‖ ^ 2)) :=
  mp_yy_born_frequency_volume p₀ ψ hψ
    (fsTrial 4) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀
      (bornRegion (mpYYBasis.repr ψ) (repr_ne_zero mpYYBasis ψ hψ))
      (bornRegion_measurable_uncond (mpYYBasis.repr ψ) (repr_ne_zero mpYYBasis ψ hψ)))

/-! ## Closure: the full nine-observable Mermin–Peres square is grounded

All nine grid observables now carry a machine-checked CSD volume reading whose eigenbasis
label is **earned**, not asserted — each via a `mp_<ab>Vec_eigenvector` lemma certifying
`(σ_a ⊗ σ_b) · vᵢ = eigval i • vᵢ` against the genuine Pauli observable
`sigma_a ⊗ₖ sigma_b` of `Empirical/QM/Contextuality/MerminPeres.lean`:

| cell    | frame                    | eigenvector lemma     | volume headline               |
|---------|--------------------------|-----------------------|-------------------------------|
| `X ⊗ I` | `mpHIBasis` (`H ⊗ I`)    | `mpXIVec_eigenvector` | `mp_xi_born_frequency_volume` |
| `I ⊗ X` | `mpIHBasis` (`I ⊗ H`)    | `mpIXVec_eigenvector` | `mp_ix_born_frequency_volume` |
| `X ⊗ X` | `mpXXBasis` (`H ⊗ H`)    | `mpXXVec_eigenvector` | `mp_xx_born_frequency_volume` |
| `I ⊗ Z` | computational           | `mpIZVec_eigenvector` | `mp_iz_born_frequency_volume` |
| `Z ⊗ I` | computational           | `mpZIVec_eigenvector` | `mp_zi_born_frequency_volume` |
| `Z ⊗ Z` | computational           | `mpZZVec_eigenvector` | `zz_parity_born_frequency_volume` |
| `X ⊗ Z` | `mpHIBasis` (`H ⊗ I`)    | `mpXZVec_eigenvector` | `mp_xz_born_frequency_volume` |
| `Z ⊗ X` | `mpIHBasis` (`I ⊗ H`)    | `mpZXVec_eigenvector` | `mp_zx_born_frequency_volume` |
| `Y ⊗ Y` | `mpYYBasis` (`U_Y ⊗ U_Y`)| `mpYYVec_eigenvector` | `mp_yy_born_frequency_volume` |

Each headline lands on the `σ_a ⊗ σ_b = +1` outcome Born weight as a block sum of two
Fubini–Study typicality volumes on the fixed ontic `Σ = ℂℙ³`, every unit two-qubit
preparation covered (no genericity hypothesis), carving-free and Gleason-free
(foundational-triple-only). The `−1` outcome of each cell is the identical instantiation
at `a = 1`.

The combinatorial no-go itself — that no single non-contextual `±1` assignment is jointly
consistent across the square's six row/column product constraints — stays at the
QM-validity layer (`no_lhv_mermin_peres`, `no_csd_mermin_peres_assignment`). The CSD
reading: each cell is a rank-2 carving of the *one* ontic `Σ`, its outcome weights are
typicality volumes recomputed per measurement frame, and the context-dependence the
theorem exploits is the dependence of the carved-volume regions on the frame — not a
hidden variable. Honest scope is unchanged: realisation, not derivation (`Φ = id`). -/

end MerminPeres
end CSDBridge
end Empirical
end CSD
