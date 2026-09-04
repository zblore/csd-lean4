/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.LocalLuders
public import CsdLean4.RecordLayer.DegenerateLuders

/-!
# SigmaLayer/LocalBlockBridge: a local measurement IS a block measurement (brick 2)

**Category:** dynamical measurement — dynamical no-signalling (A6, dynamical form), brick 2:
the index bridge that hands brick 1's statics to the dynamical block machinery.

The composite index `Fin nA × Fin nB` and the flat index `Fin (nA·nB)` are identified by
`finProdFinEquiv`. Under that identification, **the block structure of a local
`B`-measurement is the second projection** (`localBlock`), and the degenerate-Lüders
machinery's block projector **is** the local projector:

  `toComposite (blockProj localBlock j u) = localProjB j (toComposite u)`
  (`toComposite_blockProj`),

with the transport an isometric reindexing (`norm_toComposite`), so the block Born weights
are the local Born weights (`norm_blockProj_localBlock`).

★★ **Dynamical no-signalling** (`reduceA_blockLuders_mixture`): stated in the dynamics' own
vocabulary — the post-states `[blockProj localBlock j u]` and the weights `‖blockProj j u‖²/‖u‖²`
are **exactly what the join witness delivers**: `joinWitness_blockLuders` inhabits
`BlockLudersObligation localBlock`, whose conclusion says the outcome-`j`-conditioned
post-measurement marginal *is* `epistemicMeasure [blockProj localBlock j u]`, and the sector
weights are the coarse-grained Born weights (`degenerate_selector_born`). The theorem: the
Born-weighted mixture of the `A`-marginals of those dynamically-produced post-states equals
the `A`-marginal of the preparation. Alice's density matrix — hence every statistic on her
side — is invariant under Bob's measurement *as realised by the corpus's own
Liouville-preserving record dynamics*, not merely under a Lüders map written on paper.

⚠️ **Honest scope.** The composition here is at the level of the states and weights the
obligation names; the full measure-level form — pushing `reduceA` through the join
protocol's conditioned ensemble as one integral — and the eraser process (mark, then erase,
sequentially) are brick 3, the row's remaining work. `localBlock`'s blocks all have
dimension `nA`; nondegenerate `B`-measurements are the `nA = 1` corner, as expected.

## References

`specs/BACKLOG.md` (the dynamical no-signalling + eraser row); `specs/future-work.md`;
`specs/reconstruction-status.md` §2 (A6). Reused corpus API: `localProjB` +
`reduceA_localLuders_mixture` (`RecordLayer/LocalLuders.lean`), `blockProj` +
`BlockLudersObligation` (`RecordLayer/DegenerateLuders.lean`), `joinWitness_blockLuders`
(`RecordLayer/JoinLuders.lean`), `finProdFinEquiv` (Mathlib).
-/

@[expose] public section

open Matrix
open scoped LinearAlgebra.Projectivization

namespace CSD.RecordLayer

variable {nA nB : ℕ}

/-! ### The index bridge -/

/-- **The block structure of a local `B`-measurement**: under `finProdFinEquiv`, outcome
blocks are the fibres of the second projection. Every block has dimension `nA`. -/
def localBlock (nA nB : ℕ) : Fin (nA * nB) → Fin nB :=
  fun i => (finProdFinEquiv.symm i).2

/-- Transport a flat-index vector to the composite index by pulling back along
`finProdFinEquiv`. -/
noncomputable def toComposite (u : EuclideanSpace ℂ (Fin (nA * nB))) :
    EuclideanSpace ℂ (Fin nA × Fin nB) :=
  WithLp.toLp 2 fun ak => u (finProdFinEquiv ak)

@[simp] lemma toComposite_apply (u : EuclideanSpace ℂ (Fin (nA * nB)))
    (ak : Fin nA × Fin nB) : toComposite u ak = u (finProdFinEquiv ak) := rfl

lemma toComposite_zero : toComposite (0 : EuclideanSpace ℂ (Fin (nA * nB))) = 0 := by
  apply PiLp.ext
  intro ak
  rfl

lemma toComposite_eq_zero_iff (u : EuclideanSpace ℂ (Fin (nA * nB))) :
    toComposite u = 0 ↔ u = 0 := by
  constructor
  · intro h
    apply PiLp.ext
    intro i
    have h1 : toComposite u (finProdFinEquiv.symm i) = 0 := by rw [h]; rfl
    rw [toComposite_apply, Equiv.apply_symm_apply] at h1
    exact h1
  · rintro rfl
    exact toComposite_zero

lemma toComposite_ne_zero {u : EuclideanSpace ℂ (Fin (nA * nB))} (hu : u ≠ 0) :
    toComposite u ≠ 0 :=
  fun h => hu ((toComposite_eq_zero_iff u).mp h)

/-- The transport is an isometric reindexing. -/
lemma norm_toComposite (u : EuclideanSpace ℂ (Fin (nA * nB))) :
    ‖toComposite u‖ = ‖u‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact Fintype.sum_equiv finProdFinEquiv _ _ fun ak => rfl

/-! ### The bridge: block projector = local projector -/

/-- ★ **The degenerate-Lüders block projector of `localBlock` IS the local `B`-projector**,
under the index transport. A local measurement is a block-degenerate measurement — as a
definitional identity, not an analogy. -/
theorem toComposite_blockProj (j : Fin nB) (u : EuclideanSpace ℂ (Fin (nA * nB))) :
    toComposite (blockProj (localBlock nA nB) j u) = localProjB j (toComposite u) := by
  apply PiLp.ext
  intro ak
  show (blockProj (localBlock nA nB) j u) (finProdFinEquiv ak)
    = if ak.2 = j then u (finProdFinEquiv ak) else 0
  show (if localBlock nA nB (finProdFinEquiv ak) = j then u (finProdFinEquiv ak) else 0)
    = if ak.2 = j then u (finProdFinEquiv ak) else 0
  rw [localBlock, Equiv.symm_apply_apply]

/-- The block Born weights are the local Born weights. -/
lemma norm_blockProj_localBlock (j : Fin nB) (u : EuclideanSpace ℂ (Fin (nA * nB))) :
    ‖blockProj (localBlock nA nB) j u‖ = ‖localProjB j (toComposite u)‖ := by
  rw [← toComposite_blockProj, norm_toComposite]

lemma blockProj_localBlock_eq_zero_iff (j : Fin nB) (u : EuclideanSpace ℂ (Fin (nA * nB))) :
    blockProj (localBlock nA nB) j u = 0 ↔ localProjB j (toComposite u) = 0 := by
  rw [← toComposite_blockProj, toComposite_eq_zero_iff]

/-! ### Dynamical no-signalling -/

/-- ★★ **Dynamical no-signalling**: the Born-weighted mixture of the `A`-marginals of the
post-states the join witness delivers for a local `B`-measurement equals the `A`-marginal of
the preparation. The post-states `[blockProj localBlock j u]` and weights `‖·‖²/‖u‖²` are
those of `BlockLudersObligation localBlock` — inhabited dynamically by
`joinWitness_blockLuders` — and of `degenerate_selector_born`; nothing here is a paper
Lüders map. -/
theorem reduceA_blockLuders_mixture (u : EuclideanSpace ℂ (Fin (nA * nB))) (hu : u ≠ 0) :
    (∑ j, (((‖blockProj (localBlock nA nB) j u‖ ^ 2 / ‖u‖ ^ 2 : ℝ)) : ℂ) •
        (if h : blockProj (localBlock nA nB) j u = 0 then 0
         else reduceA (Projectivization.mk ℂ (toComposite (blockProj (localBlock nA nB) j u))
           (toComposite_ne_zero h))))
      = reduceA (Projectivization.mk ℂ (toComposite u) (toComposite_ne_zero hu)) := by
  classical
  have hterm : ∀ j, (((‖blockProj (localBlock nA nB) j u‖ ^ 2 / ‖u‖ ^ 2 : ℝ)) : ℂ) •
      (if h : blockProj (localBlock nA nB) j u = 0 then 0
       else reduceA (Projectivization.mk ℂ (toComposite (blockProj (localBlock nA nB) j u))
         (toComposite_ne_zero h)))
      = (((‖localProjB j (toComposite u)‖ ^ 2 / ‖toComposite u‖ ^ 2 : ℝ)) : ℂ) •
        (if h : localProjB j (toComposite u) = 0 then 0
         else reduceA (Projectivization.mk ℂ (localProjB j (toComposite u)) h)) := by
    intro j
    rw [norm_blockProj_localBlock, norm_toComposite]
    by_cases h : blockProj (localBlock nA nB) j u = 0
    · rw [dif_pos h, dif_pos ((blockProj_localBlock_eq_zero_iff j u).mp h)]
    · rw [dif_neg h, dif_neg (fun h' => h ((blockProj_localBlock_eq_zero_iff j u).mpr h'))]
      have hsub : (⟨toComposite (blockProj (localBlock nA nB) j u), toComposite_ne_zero h⟩
            : {v : EuclideanSpace ℂ (Fin nA × Fin nB) // v ≠ 0})
          = ⟨localProjB j (toComposite u),
              fun h' => h ((blockProj_localBlock_eq_zero_iff j u).mpr h')⟩ :=
        Subtype.ext (toComposite_blockProj j u)
      have hXY := congrArg (fun p : {v : EuclideanSpace ℂ (Fin nA × Fin nB) // v ≠ 0} =>
        reduceA (Projectivization.mk ℂ p.1 p.2)) hsub
      rw [show reduceA (Projectivization.mk ℂ
            (toComposite (blockProj (localBlock nA nB) j u)) (toComposite_ne_zero h))
          = reduceA (Projectivization.mk ℂ (localProjB j (toComposite u))
              (fun h' => h ((blockProj_localBlock_eq_zero_iff j u).mpr h'))) from hXY]
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  exact reduceA_localLuders_mixture (toComposite u) (toComposite_ne_zero hu)

end CSD.RecordLayer
