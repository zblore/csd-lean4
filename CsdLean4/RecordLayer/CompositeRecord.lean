/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.LocalBlockBridge
public import CsdLean4.RecordLayer.JoinClosure
public import CsdLean4.RecordLayer.EntangledRecord

/-!
# RL-1′: the composite-arena seam of Q27 — a local record on a pure composite reads the reduced state

**Category:** 7-SigmaLayer (the record layer — Q27's composite-arena form; `specs/BACKLOG.md`
▶ OPEN QUEUE #25, the residue `RecordLayer/EntangledRecord.lean` declared).

## What this closes

RL-1 answered the external reader's question at the record tier by preparing the local system
as the mixed swap preparation of the reduced state, and the honest-scope note said what that
leaves open. The ontic composite point is pure, so a sceptic can say the local system was
modelled as a classical mixture rather than measured. The corpus already has the other
construction, an apparatus coupled to one sector of the composite arena: a local measurement IS
a block-degenerate measurement (`LocalBlockBridge.lean`, `localBlock`), and the join protocol
delivers its record dynamics with the coarse Born mass `join_sector_born`. What nobody had
stated is that this mass is the reduced state's Born weight. This module states it, and then
puts the two constructions side by side in one equation.

## Main results

* `localBlock_sum_normSq` — the join protocol's block sum at `localBlock` reindexes along
  `finProdFinEquiv` to `∑ₐ ‖u(a, j)‖²`;
* `rayDensity_posSemidef`, `rayDensityIx`, `reduceBDensity` — the density of a composite ray as
  an indexed density operator, and Bob's reduced state `reduceB` as a `DensityOperator nB`
  (through `DensityOperatorIx.reducedLeft` and RL-1's `toFin`); `reduceB_diag_re` — its diagonal
  entry is `∑ₐ ‖v(a, j)‖² / ‖v‖²`;
* ★★ `composite_local_record_born` — **on the composite arena, the record weight of Bob's
  outcome `j` is the reduced state's Born weight**: for every unit composite vector `u`, the
  join protocol at `localBlock` gives the outcome-`j` sector exactly `re (reduceB [u]) j j`,
  which is `re tr(reduceB [u] · ∣j⟩⟨j∣)` (`composite_local_record_born_trace`) and
  `Tr(ρ_B ∣j⟩⟨j∣)` in the LF2 pairing (`composite_local_record_born_traceForm`);
* ★★ `composite_record_eq_mixed_record` — **the two lines meet at a theorem**: the composite-
  arena record weight (a pure composite point, an apparatus on one sector, the join protocol)
  equals the local mixed-preparation record weight (`mixedSwapPrep` at `reduceBDensity`, the
  swap protocol), outcome by outcome. The classical-mixture reading and the ontic reading give
  the same records, and now that's a proved identity rather than two numbers that happen to
  agree.

## CSD reading

Bob's apparatus couples to his sector of a pure composite point and the dynamics sorts the
composite into blocks. The block a run lands in is his record, and the weights of the blocks
are exactly the diagonal of his reduced state, so his records carry the entanglement's local
effect and nothing else. Alice's labels never enter (`reduceA_blockLuders_mixture` is the
dynamical no-signalling half of the same construction). The mixed swap preparation of RL-1 is
the epistemic description of the same records, and the two agree because both are the reduced
state's Born weights.

## ⚠️ Honest scope

* Bob's outcomes are the computational basis of his factor, the block structure `localBlock`
  fixes. A rotated local context is `basisContext` on the swap side and the corresponding block
  structure on the join side, and isn't restated here.
* The `Fin nA × Fin nB` index of the no-signalling line, not the field-configuration index of
  the CV composite arena. RL-1's `reducedDensity` and this module's `reduceBDensity` are the
  same construction on two index conventions, and a bridge between them is index plumbing
  nobody has needed.
* The follow-up after Bob's record is `joinWitness_blockLuders` at `localBlock` (the composite
  collapses to `[Πⱼ u]`); that its reduced state is Bob's Lüders-updated state is not stated.

## References

`specs/BACKLOG.md` (▶ OPEN QUEUE #25; Q27); `RecordLayer/EntangledRecord.lean` (RL-1, the
honest-scope note this discharges; `DensityOperatorIx.toFin`, `trace_mul_single'`);
`RecordLayer/LocalBlockBridge.lean` (`localBlock`, `toComposite`, `norm_blockProj_localBlock`);
`RecordLayer/LocalLuders.lean` (`localProjB`); `RecordLayer/OnticMarginals.lean` (`rayDensity`,
`reduceB`, `normSq_eq_sum_mul_star`); `RecordLayer/JoinClosure.lean` (`join_sector_born`);
`RecordLayer/MixedSwap.lean` (`mixed_swap_sector_born`); `LF2/ReducedDensity.lean`
(`DensityOperatorIx.reducedLeft`); `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Matrix
open scoped ComplexOrder
open scoped LinearAlgebra.Projectivization

namespace CSD.RecordLayer

open CSD.LF2 CSD.SigmaLayer

variable {nA nB : ℕ}

/-! ### The block sum at `localBlock` is Bob's diagonal weight -/

/-- The join protocol's block sum at `localBlock`, reindexed along `finProdFinEquiv`: the
outcome-`j` block carries `∑ₐ ‖u(a, j)‖²`. -/
lemma localBlock_sum_normSq (u : EuclideanSpace ℂ (Fin (nA * nB))) (j : Fin nB) :
    ∑ i ∈ Finset.univ.filter (fun i => localBlock nA nB i = j),
        ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) u‖ ^ 2
      = ∑ a : Fin nA, ‖u (finProdFinEquiv (a, j))‖ ^ 2 := by
  have hterm : ∀ i : Fin (nA * nB),
      ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) u‖ ^ 2 = ‖u i‖ ^ 2 := by
    intro i
    rw [EuclideanSpace.inner_single_left, map_one, one_mul]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_filter,
    ← Equiv.sum_comp (finProdFinEquiv : Fin nA × Fin nB ≃ Fin (nA * nB)),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_congr rfl fun k _ => by
    rw [show localBlock nA nB (finProdFinEquiv (a, k)) = k from by
      rw [localBlock, Equiv.symm_apply_apply]]]
  rw [Finset.sum_ite_eq' Finset.univ j (fun k => ‖u (finProdFinEquiv (a, k))‖ ^ 2),
    if_pos (Finset.mem_univ _)]

/-! ### Bob's reduced state as a density operator -/

/-- The ray density is a nonnegative multiple of `∣v⟩⟨v∣`. -/
lemma rayDensity_eq_smul (p : ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB))) :
    rayDensity p = (((‖p.rep‖ ^ 2)⁻¹ : ℝ) : ℂ) • vecMulVec (⇑p.rep) (star ⇑p.rep) := by
  ext x y
  rw [rayDensity, Matrix.of_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply,
    smul_eq_mul, div_eq_inv_mul, Complex.ofReal_inv]

/-- The ray density is positive semidefinite. -/
lemma rayDensity_posSemidef (p : ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB))) :
    (rayDensity p).PosSemidef := by
  rw [rayDensity_eq_smul]
  exact (posSemidef_vecMulVec_self_star _).smul
    (Complex.zero_le_real.mpr (inv_nonneg.mpr (sq_nonneg _)))

/-- **The density of a composite ray as an indexed density operator.** -/
noncomputable def rayDensityIx (p : ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB))) :
    DensityOperatorIx (Fin nA × Fin nB) where
  M           := rayDensity p
  isHermitian := (rayDensity_posSemidef p).isHermitian
  nonneg      := rayDensity_posSemidef p
  trace_one   := rayDensity_trace p

/-- **Bob's reduced state as a `Fin`-indexed density operator**: `reduceB`, through
`DensityOperatorIx.reducedLeft` and the identity labelling. -/
noncomputable def reduceBDensity (p : ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB))) :
    DensityOperator nB :=
  (rayDensityIx p).reducedLeft.toFin (Equiv.refl (Fin nB))

@[simp] theorem reduceBDensity_M (p : ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB))) :
    (reduceBDensity p).M = reduceB p := rfl

/-- The diagonal of Bob's reduced state at a composite vector: `∑ₐ ‖v(a, j)‖² / ‖v‖²`. -/
lemma reduceB_diag (v : EuclideanSpace ℂ (Fin nA × Fin nB)) (hv : v ≠ 0) (j : Fin nB) :
    reduceB (Projectivization.mk ℂ v hv) j j
      = (((∑ a : Fin nA, ‖v (a, j)‖ ^ 2) / ‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [reduceB, traceLeft_apply, rayDensity_mk]
  simp only [Matrix.of_apply]
  rw [← Finset.sum_div]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.star_def, Complex.mul_conj']

/-- The real part of that diagonal entry. -/
lemma reduceB_diag_re (v : EuclideanSpace ℂ (Fin nA × Fin nB)) (hv : v ≠ 0) (j : Fin nB) :
    RCLike.re (reduceB (Projectivization.mk ℂ v hv) j j)
      = (∑ a : Fin nA, ‖v (a, j)‖ ^ 2) / ‖v‖ ^ 2 := by
  rw [reduceB_diag, RCLike.re_to_complex, Complex.ofReal_re]

/-- The Born pairing of Bob's reduced state at outcome `j` is its diagonal entry. -/
theorem traceForm_reduceBDensity_single (p : ℙ ℂ (EuclideanSpace ℂ (Fin nA × Fin nB)))
    (j : Fin nB) :
    traceForm (reduceBDensity p)
        (rankOneEffect (EuclideanSpace.single j (1 : ℂ)) (single_norm_one' j))
      = RCLike.re (reduceB p j j) := by
  rw [reduceBDensity, DensityOperatorIx.traceForm_toFin_single, DensityOperatorIx.traceForm,
    trace_mul_single']
  rfl

/-! ### ★★ The composite-arena record weight is the reduced state's Born weight -/

variable [NeZero (nA * nB)]

/-- ★★ **On the composite arena, Bob's record weight is his reduced state's Born weight.** For
a unit composite vector `u`, the join protocol with the local block structure `localBlock`
gives the outcome-`j` sector exactly `re (reduceB [u]) j j`, for every composite point, entangled
included, and independently of the ancilla calibration `α`. -/
theorem composite_local_record_born (u α : EuclideanSpace ℂ (Fin (nA * nB))) (hu0 : u ≠ 0)
    (hu : ‖u‖ = 1) (j : Fin nB) :
    joinPrep (K := nB) u α hu0 ((joinProtocol (localBlock nA nB)).outcomeSector j)
      = ENNReal.ofReal (RCLike.re
          (reduceB (Projectivization.mk ℂ (toComposite u) (toComposite_ne_zero hu0)) j j)) := by
  rw [join_sector_born (localBlock nA nB) u α hu0 hu j, localBlock_sum_normSq, reduceB_diag_re,
    norm_toComposite, hu, one_pow, div_one]
  rfl

/-- The same, in the trace form `re tr(reduceB [u] · ∣j⟩⟨j∣)` RL-1's bridge reads. -/
theorem composite_local_record_born_trace (u α : EuclideanSpace ℂ (Fin (nA * nB)))
    (hu0 : u ≠ 0) (hu : ‖u‖ = 1) (j : Fin nB) :
    joinPrep (K := nB) u α hu0 ((joinProtocol (localBlock nA nB)).outcomeSector j)
      = ENNReal.ofReal (RCLike.re
          ((reduceB (Projectivization.mk ℂ (toComposite u) (toComposite_ne_zero hu0))
            * Matrix.single j j 1).trace)) := by
  rw [composite_local_record_born u α hu0 hu j, trace_mul_single']

/-- The same, as the LF2 Born pairing `Tr(ρ_B ∣j⟩⟨j∣)` of Bob's reduced density operator. -/
theorem composite_local_record_born_traceForm (u α : EuclideanSpace ℂ (Fin (nA * nB)))
    (hu0 : u ≠ 0) (hu : ‖u‖ = 1) (j : Fin nB) :
    joinPrep (K := nB) u α hu0 ((joinProtocol (localBlock nA nB)).outcomeSector j)
      = ENNReal.ofReal (traceForm
          (reduceBDensity (Projectivization.mk ℂ (toComposite u) (toComposite_ne_zero hu0)))
          (rankOneEffect (EuclideanSpace.single j (1 : ℂ)) (single_norm_one' j))) := by
  rw [composite_local_record_born u α hu0 hu j, traceForm_reduceBDensity_single]

/-! ### ★★ The two lines meet -/

variable [NeZero nB]

/-- ★★ **The composite-arena record and the mixed-preparation record agree, outcome by
outcome.** The join protocol on the pure composite point (an apparatus coupled to Bob's
sector) and the swap protocol on the mixed preparation of Bob's reduced state (RL-1's local
witness) give every outcome the same weight. The ontic reading and the classical-mixture
reading of "measure Bob's subsystem" are the same records. -/
theorem composite_record_eq_mixed_record (u α : EuclideanSpace ℂ (Fin (nA * nB)))
    (hu0 : u ≠ 0) (hu : ‖u‖ = 1) (j : Fin nB) :
    joinPrep (K := nB) u α hu0 ((joinProtocol (localBlock nA nB)).outcomeSector j)
      = mixedSwapPrep
          (reduceBDensity (Projectivization.mk ℂ (toComposite u) (toComposite_ne_zero hu0)))
          ((swapProtocol (basinIndex (momentContext nB))
            (measurable_basinIndex (momentContext nB))).outcomeSector j) := by
  rw [composite_local_record_born_traceForm u α hu0 hu j, mixed_swap_sector_born]

end CSD.RecordLayer
