/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.EntangledWeights
public import CsdLean4.LF2.MixedEnsembleIx
public import CsdLean4.RecordLayer.MixedLuders
public import CsdLean4.RecordLayer.TwoTimeLuders

/-!
# RL-1: what entanglement does to the RECORDS — the reduced state at the record tier (Q27, second half)

**Category:** 7-SigmaLayer (the record layer — Q27's mixed-tier transport and the entangled
two-time instantiation; `specs/BACKLOG.md` ▶ OPEN QUEUE #5, Q27's residue row, and the
gated list of `specs/two-time-luders-scoping.md`).

## The question, and where its first half stopped

The external reader's question (2026-08-20): for an ENTANGLED composite preparation, what
are a local context's weights? `CV/EntangledWeights.lean` answered it at the arena level —
★★ `arenaObs_leftOp_eq_reduced`, `arenaObs (leftOp A) x = re tr(reducedDM x · A)` for every
composite point, with the Bell ray's local weights exactly `1/2`. What it did **not** do, and
said so, is carry that form to the **record tier**: the dynamical measurement model
(`swapProtocol` on `SwapArena`, `mixedSwapPrep`, the two-stage arena) is `Fin`-indexed and
reads density operators through `traceForm`, while `reducedDM` lives on the field-configuration
index. This module closes that gap, and then instantiates the two-time law on it.

## Main results

**A. The transport** (index plumbing, delivered as API):

* `DensityOperatorIx.toFin` — an indexed density read on `Fin d` through a labelling
  `e : ι ≃ Fin d` of its index (the bridge `LF2/ReducedDensity.lean` said "should a bridge ever
  be needed"; this is the need); `traceForm_toFin_single` — the diagonal weights transport.
* `reducedDensityIx x` — the reduced state of a composite ray as a `DensityOperatorIx`, with
  `traceForm_reducedDensityIx : (reducedDensityIx x).traceForm A = arenaObs (leftOp A) x`;
  `reducedDensity e x : DensityOperator d` — the same, on `Fin d`, with
  `traceForm_reducedDensity_single` — the record tier's Born pairing at outcome `i` IS the
  composite arena's local observation of the pattern projector `∣e⁻¹ i⟩⟨e⁻¹ i∣`.

**B. The local record law** (Q27 at the record tier):

* ★★ `entangled_local_record_born` — **a local context's record weights on an entangled
  composite are the reduced state's Born weights, dynamically**: the mixed swap preparation
  at `reducedDensity e x` gives the outcome-`i` sector exactly
  `arenaObs (leftOp ∣e⁻¹ i⟩⟨e⁻¹ i∣) x` — for EVERY composite point, entangled included.
* ★ `entangled_local_followup` — after recording `i` on the entangled composite, follow-up
  statistics in every local context are `c'.rate [eᵢ]`: the record fixes the local
  post-state, whatever the remote sector holds (`mixed_luders_followup` consumed).
* ★ `bell_record_weight₀` / `bell_record_weight₁` — the Bell ray's local records: exactly
  `1/2` each, on the swap arena.

**C. The mixed two-time law** (generic, new — `mixedReadyPrep` had no two-time consumer):

* `mixedTwoPrep ρ` — the two-stage preparation of a MIXED system: `mixedReadyPrep ρ` with a
  calibrated bank for the first measurement, fresh ready register and calibrated bank for the
  second.
* ★★ `mixed_two_time_born` — `P(record i at t₁ ∧ record j at t₂) = Tr(ρ Πᵢ) · c₂.rate [eᵢ] j`
  for every density operator `ρ` and every second context; `mixed_two_time_first_record`
  (no retro-action), ★ `mixed_two_time_other_fate` (conditioned on record `i`, the next
  partition carries the collapsed weights `c₂.rate [eᵢ]`).

**D. The entangled two-time instantiation** (the gated item of `two-time-luders-scoping.md`):

* ★★ `entangled_two_time_born` —
  `P(local record i at t₁ ∧ record j at t₂) = arenaObs (leftOp Πᵢ) x · c₂.rate [eᵢ] j`: measure
  a subsystem of an entangled composite, then follow up, as ONE number on one arena, with the
  first factor read off the composite point through `reducedDM`;
* ★ `entangled_two_time_other_fate`, ★ `bell_two_time_born` (the Bell ray: `½ · c₂.rate [eᵢ] j`).

## CSD reading

Entanglement enters the record layer in exactly one place: the **preparation weights** of the
local swap witness are those of the reduced state, and the reduced state is mixed precisely
when the composite point is entangled (`reducedDM_join`). Everything downstream of the
weights — record creation, exclusivity, persistence, the Lüders relocation to `[eᵢ]`, the
two-time composition — is the same protocol on the same arena, untouched. So "what
entanglement does to the records" is: it supplies mixed Born weights and nothing else; the
remote sector's labels never reach the local records (`composite_no_signalling` at the
arena level, and here the weights `arenaObs (leftOp ·) x` are the only composite input).

## ⚠️ Honest scope

* The local system is prepared as `mixedSwapPrep (reducedDensity e x)` — the spectral
  two-stage sampling of the reduced state, the corpus's canonical mixed preparation
  (`MixedSwap.lean`). The theorems are identities of RECORD STATISTICS: the local witness at
  that preparation reads exactly the composite point's local observations. The ontic
  composite point is pure; an apparatus coupled to ONE SECTOR OF THE COMPOSITE ARENA is the
  corpus's OTHER line — a local measurement IS a block-degenerate measurement
  (`RecordLayer/LocalBlockBridge.lean`, `localBlock`), and the join protocol's coarse Born
  mass (`join_sector_born`) at that block map is `‖localProjB j v‖² / ‖v‖²`
  (`norm_blockProj_localBlock`). What is NOT stated anywhere is the identification of that
  composite-arena sector weight with `re tr(reduceB [v] · Πⱼ)`, the reduced-state pairing of
  `OnticMarginals.lean`; that seam is RL-1′ (priced in `specs/BACKLOG.md`), not this module.
  The two lines meet at the number, not at a shared construction.
* The first measurement is the local computational-basis context (`momentContext d` through
  the labelling `e`), the second is arbitrary — the scope of the two-stage arena
  (`TwoTimeLuders.lean`).
* Rank-one local outcomes; the labelling `e : FieldConfig K₁ N ≃ Fin d` is quantified, so no
  choice of enumeration is hidden.

## References

`specs/BACKLOG.md` (▶ OPEN QUEUE #5 = RL-1; Q27, Q25); `specs/two-time-luders-scoping.md`
(the gated list this executes); `specs/record-layer-plan.md` §4;
`CV/EntangledWeights.lean` (`reducedDM`, `arenaObs_leftOp_eq_reduced`, `reducedDM_bell`,
`bell_local_weight₀/₁`, `trace_mul_single`); `CV/CompositeArena.lean` (`leftOp`, `bellVec`);
`LF2/ReducedDensity.lean` (`DensityOperatorIx`), `LF2/MixedEnsembleIx.lean`
(`DensityOperatorIx.traceForm`); `RecordLayer/MixedSwap.lean` (`mixedSwapPrep`,
`mixed_swap_sector_born`), `RecordLayer/MixedLuders.lean` (`mixedReadyPrep`,
`mixedSwapPrep_eq_prod`, `mixed_outcome_pos`, `mixed_luders_followup`);
`RecordLayer/TwoTimeLuders.lean` (`twoStagePrep`, `two_stage_joint`,
`two_stage_first_record`, `jointRecordSector`); `RecordLayer/SwapClosure.lean`
(`swap_sector_born_ctx`); `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Matrix
open scoped ComplexOrder
open scoped LinearAlgebra.Projectivization

/-! ### Index plumbing: an indexed density read on `Fin d` -/

namespace CSD.LF2

/-- Traces are invariant under a simultaneous reindex of rows and columns. -/
lemma trace_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι ι ℂ) (e : κ ≃ ι) :
    (M.submatrix e e).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun i => M i i)

/-- `tr(M · ∣a⟩⟨a∣) = M a a` on an arbitrary finite index. -/
lemma trace_mul_single' {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (a : ι) :
    (M * Matrix.single a a 1).trace = M a a := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  have hterm : ∀ i j : ι,
      M i j * Matrix.single a a (1 : ℂ) j i
        = if j = a then (if i = a then M i j else 0) else 0 := by
    intro i j
    simp only [Matrix.single, Matrix.of_apply]
    by_cases hj : j = a <;> by_cases hi : i = a <;>
      simp_all [eq_comm]
  rw [Finset.sum_congr rfl fun i _ => by
    rw [Finset.sum_congr rfl fun j _ => hterm i j,
      Finset.sum_ite_eq' Finset.univ a (fun j => if i = a then M i j else 0),
      if_pos (Finset.mem_univ _)]]
  rw [Finset.sum_ite_eq' Finset.univ a (fun i => M i a),
    if_pos (Finset.mem_univ _)]

/-- The rank-one projector of a standard basis vector is the matrix unit `∣i⟩⟨i∣`. -/
lemma outerProduct_single {ι : Type*} [DecidableEq ι] (i : ι) :
    outerProduct (EuclideanSpace.single i (1 : ℂ)) = Matrix.single i i 1 := by
  ext j k
  simp only [outerProduct, Matrix.vecMulVec_apply, Matrix.single, Matrix.of_apply,
    PiLp.single_apply]
  by_cases hj : j = i <;> by_cases hk : k = i <;> simp_all [eq_comm]

namespace DensityOperatorIx

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- **An indexed density read on `Fin d`** through a labelling `e : ι ≃ Fin d` of its index —
the bridge between the index-parametric `DensityOperatorIx ι` and the `Fin`-indexed
`DensityOperator d` the record tier consumes. -/
noncomputable def toFin (e : ι ≃ Fin d) (ρ : DensityOperatorIx ι) : DensityOperator d where
  M           := ρ.M.submatrix e.symm e.symm
  isHermitian := ρ.isHermitian.submatrix _
  nonneg      := ρ.nonneg.submatrix _
  trace_one   := by rw [trace_submatrix_equiv, ρ.trace_one]

@[simp] theorem toFin_M (e : ι ≃ Fin d) (ρ : DensityOperatorIx ι) :
    (ρ.toFin e).M = ρ.M.submatrix e.symm e.symm := rfl

/-- **The diagonal weights transport**: the `Fin`-tier Born pairing at the basis outcome `i`
is the indexed density's pairing at the matrix unit of the label `e⁻¹ i`. -/
theorem traceForm_toFin_single (e : ι ≃ Fin d) (ρ : DensityOperatorIx ι) (i : Fin d) :
    LF2.traceForm (ρ.toFin e)
        (rankOneEffect (EuclideanSpace.single i (1 : ℂ)) (RecordLayer.single_norm_one' i))
      = ρ.traceForm (Matrix.single (e.symm i) (e.symm i) 1) := by
  have hM : (rankOneEffect (EuclideanSpace.single i (1 : ℂ))
      (RecordLayer.single_norm_one' i)).M = Matrix.single i i 1 :=
    outerProduct_single i
  rw [LF2.traceForm, traceForm, toFin_M, hM, trace_mul_single', trace_mul_single',
    Matrix.submatrix_apply]

end DensityOperatorIx
end CSD.LF2

namespace CSD.RecordLayer

open CSD.LF2 CSD.SigmaLayer CSD.CV

/-! ### The reduced state of a composite ray, at the record tier -/

variable {K₁ K₂ N d : ℕ}

/-- **The reduced state of a composite ray as an indexed density operator** — the object
`CV/EntangledWeights.lean` delivered (`reducedDM`, PSD and trace one), packaged for the LF2
mixed tier. -/
noncomputable def reducedDensityIx (x : FieldArena (K₁ + K₂) N) :
    DensityOperatorIx (FieldConfig K₁ N) where
  M           := reducedDM x
  isHermitian := (reducedDM_posSemidef x).isHermitian
  nonneg      := reducedDM_posSemidef x
  trace_one   := reducedDM_trace x

@[simp] theorem reducedDensityIx_M (x : FieldArena (K₁ + K₂) N) :
    (reducedDensityIx x).M = reducedDM x := rfl

/-- **The mixed-tier Born pairing of the reduced state is the composite arena's local
observation** — `arenaObs_leftOp_eq_reduced` read through `DensityOperatorIx.traceForm`. -/
theorem traceForm_reducedDensityIx (x : FieldArena (K₁ + K₂) N)
    (A : Matrix (FieldConfig K₁ N) (FieldConfig K₁ N) ℂ) :
    (reducedDensityIx x).traceForm A = arenaObs (leftOp A) x :=
  (arenaObs_leftOp_eq_reduced A x).symm

/-- **The reduced state on `Fin d`**, through a labelling `e` of the local configurations —
the `DensityOperator d` the swap witness and the two-stage arena consume. -/
noncomputable def reducedDensity (e : FieldConfig K₁ N ≃ Fin d) (x : FieldArena (K₁ + K₂) N) :
    DensityOperator d :=
  (reducedDensityIx x).toFin e

/-- **The record tier's Born pairing at outcome `i` is the composite arena's local observation
of the pattern projector `∣e⁻¹ i⟩⟨e⁻¹ i∣`** — the transport the Q27 first brick declared and
did not claim. -/
theorem traceForm_reducedDensity_single (e : FieldConfig K₁ N ≃ Fin d)
    (x : FieldArena (K₁ + K₂) N) (i : Fin d) :
    traceForm (reducedDensity e x)
        (rankOneEffect (EuclideanSpace.single i (1 : ℂ)) (single_norm_one' i))
      = arenaObs (leftOp (Matrix.single (e.symm i) (e.symm i) 1)) x := by
  rw [reducedDensity, DensityOperatorIx.traceForm_toFin_single, traceForm_reducedDensityIx]

/-! ### ★★ The local record law on an entangled composite -/

variable [NeZero d]

/-- ★★ **A local context's record weights on an entangled composite are the reduced state's
Born weights — dynamically.** The mixed swap preparation at the reduced state of the composite
point `x` gives the outcome-`i` sector of the local measurement protocol exactly the composite
arena's local observation `arenaObs (leftOp ∣e⁻¹ i⟩⟨e⁻¹ i∣) x`, for EVERY composite point,
entangled included: Q27's answer, stated where the records are made. -/
theorem entangled_local_record_born (e : FieldConfig K₁ N ≃ Fin d)
    (x : FieldArena (K₁ + K₂) N) (i : Fin d) :
    mixedSwapPrep (reducedDensity e x)
        ((swapProtocol (basinIndex (momentContext d))
          (measurable_basinIndex (momentContext d))).outcomeSector i)
      = ENNReal.ofReal (arenaObs (leftOp (Matrix.single (e.symm i) (e.symm i) 1)) x) := by
  rw [mixed_swap_sector_born, traceForm_reducedDensity_single]

/-- ★ **The record fixes the local post-state, whatever the remote sector holds.** After
recording `i` on the entangled composite's local sector, follow-up statistics in every local
context `c'` are the collapsed state's rates `c'.rate [eᵢ]` — `mixed_luders_followup` with the
positivity hypothesis read off the composite point. -/
theorem entangled_local_followup (e : FieldConfig K₁ N ≃ Fin d)
    (x : FieldArena (K₁ + K₂) N) (i : Fin d)
    (hpos : arenaObs (leftOp (Matrix.single (e.symm i) (e.symm i) 1)) x ≠ 0)
    (c' : ContextField d) (j : Fin d) :
    ((swapProtocol (basinIndex (momentContext d))
        (measurable_basinIndex (momentContext d))).postMeasure
          (mixedSwapPrep (reducedDensity e x)) i)
      ((fun y : SwapArena (LF4.KSigma d) d => y.1.1) ⁻¹' globalBasin c' j)
      = ENNReal.ofReal (c'.rate (vertexPoint i) j) :=
  mixed_luders_followup (reducedDensity e x) i
    (by rwa [traceForm_reducedDensity_single]) c' j

/-- ★ **The Bell ray's first local record weight, on the swap arena: exactly `1/2`.** -/
theorem bell_record_weight₀ (e : FieldConfig K₁ N ≃ Fin d)
    {x₀ x₁ : FieldConfig K₁ N} (hx : x₀ ≠ x₁) {y₀ y₁ : FieldConfig K₂ N} (hy : y₀ ≠ y₁) :
    mixedSwapPrep (reducedDensity e (Projectivization.mk ℂ (bellVec x₀ x₁ y₀ y₁)
          (bellVec_ne_zero x₀ x₁ y₀ y₁)))
        ((swapProtocol (basinIndex (momentContext d))
          (measurable_basinIndex (momentContext d))).outcomeSector (e x₀))
      = ENNReal.ofReal (1 / 2) := by
  rw [entangled_local_record_born, Equiv.symm_apply_apply, bell_local_weight₀ hx hy]

/-- ★ **The Bell ray's second local record weight, on the swap arena: exactly `1/2`.** With
`bell_record_weight₀`: entanglement maximally mixes the local RECORDS across the correlated
patterns, and the remote labels are gone. -/
theorem bell_record_weight₁ (e : FieldConfig K₁ N ≃ Fin d)
    {x₀ x₁ : FieldConfig K₁ N} (hx : x₀ ≠ x₁) {y₀ y₁ : FieldConfig K₂ N} (hy : y₀ ≠ y₁) :
    mixedSwapPrep (reducedDensity e (Projectivization.mk ℂ (bellVec x₀ x₁ y₀ y₁)
          (bellVec_ne_zero x₀ x₁ y₀ y₁)))
        ((swapProtocol (basinIndex (momentContext d))
          (measurable_basinIndex (momentContext d))).outcomeSector (e x₁))
      = ENNReal.ofReal (1 / 2) := by
  rw [entangled_local_record_born, Equiv.symm_apply_apply, bell_local_weight₁ hx hy]

/-! ### ★★ The two-time law for a mixed preparation -/

section MixedTwoTime

variable {N : ℕ} [NeZero N]

/-- **The two-stage preparation of a mixed system**: `mixedReadyPrep ρ` (the spectral mixture
of the ready preparations) with a vertex-calibrated bank for the first measurement, and a fresh
ready register with a vertex-calibrated bank for the second. -/
noncomputable def mixedTwoPrep (ρ : DensityOperator N) :
    Measure (TwoStageArena (LF4.KSigma N) N) :=
  twoStagePrep (mixedReadyPrep ρ) (fun k => epistemicMeasure (vertexPoint k)) (readyMeasure N)
    (fun k => epistemicMeasure (vertexPoint k))

instance (ρ : DensityOperator N) : IsProbabilityMeasure (mixedTwoPrep ρ) := by
  unfold mixedTwoPrep
  infer_instance

/-- ★★ **The two-time Born law for a mixed preparation, on one arena.** For every density
operator `ρ`, measured in the computational basis at `t₁` and in an ARBITRARY context `c₂` at
`t₂`:

  `P(record i at t₁ ∧ record j at t₂) = Tr(ρ Πᵢ) · c₂.rate [eᵢ] j`.

The first factor is the mixed dynamical Born weight (`mixed_swap_sector_born`); the second is the
Born weight of the collapsed state `[eᵢ]` — the record erases the classical ignorance of the
preparation (`mixed_luders_followup`'s content), now as one number on the two-stage arena. -/
theorem mixed_two_time_born (ρ : DensityOperator N) (i : Fin N)
    (hpos : traceForm ρ (rankOneEffect (EuclideanSpace.single i (1 : ℂ))
      (single_norm_one' i)) ≠ 0)
    (c₂ : ContextField N) (j : Fin N) :
    mixedTwoPrep ρ (jointRecordSector (basinIndex (momentContext N)) (basinIndex c₂) i j)
      = ENNReal.ofReal (traceForm ρ (rankOneEffect (EuclideanSpace.single i (1 : ℂ))
          (single_norm_one' i)))
        * ENNReal.ofReal (c₂.rate (vertexPoint i) j) := by
  rw [mixedTwoPrep, two_stage_joint (basinIndex (momentContext N)) (basinIndex c₂)
    (measurable_basinIndex (momentContext N)) (measurable_basinIndex c₂)
    (mixedReadyPrep ρ) (fun k => epistemicMeasure (vertexPoint k)) (readyMeasure N)
    (fun k => epistemicMeasure (vertexPoint k)) i j (mixed_outcome_pos ρ i hpos)]
  congr 1
  · have h := mixed_swap_sector_born ρ i
    rw [mixedSwapPrep_eq_prod] at h
    exact h
  · exact swap_sector_born_ctx c₂ (vertexPoint i) j

/-- The stage-1 record marginal of a mixed preparation: composing does not disturb the mixed
Born law. -/
theorem mixed_two_time_first_record (ρ : DensityOperator N) (c₂ : ContextField N)
    (i : Fin N) :
    mixedTwoPrep ρ (twoStage (basinIndex (momentContext N)) (basinIndex c₂)
      ⁻¹' recordOneEvent i)
      = ENNReal.ofReal (traceForm ρ (rankOneEffect (EuclideanSpace.single i (1 : ℂ))
          (single_norm_one' i))) := by
  rw [mixedTwoPrep, two_stage_first_record (basinIndex (momentContext N)) (basinIndex c₂)
    (measurable_basinIndex (momentContext N))
    (mixedReadyPrep ρ) (fun k => epistemicMeasure (vertexPoint k)) (readyMeasure N)
    (fun k => epistemicMeasure (vertexPoint k)) i]
  have h := mixed_swap_sector_born ρ i
  rw [mixedSwapPrep_eq_prod] at h
  exact h

/-- ★ **The fate of the other `Ω_j` for a mixed preparation.** CONDITIONED on record `i` at
`t₁`, the probability of record `j` at `t₂` is the collapsed state's rate `c₂.rate [eᵢ] j` —
independent of `ρ`: the record, not the pedigree, fixes the next partition. -/
theorem mixed_two_time_other_fate (ρ : DensityOperator N) (i : Fin N)
    (hpos : traceForm ρ (rankOneEffect (EuclideanSpace.single i (1 : ℂ))
      (single_norm_one' i)) ≠ 0)
    (c₂ : ContextField N) (j : Fin N) :
    ProbabilityTheory.cond (mixedTwoPrep ρ)
        (twoStage (basinIndex (momentContext N)) (basinIndex c₂) ⁻¹' recordOneEvent i)
        (twoStage (basinIndex (momentContext N)) (basinIndex c₂) ⁻¹' recordTwoEvent j)
      = ENNReal.ofReal (c₂.rate (vertexPoint i) j) := by
  have hmeas₁ : MeasurableSet (twoStage (basinIndex (momentContext N)) (basinIndex c₂)
      ⁻¹' recordOneEvent (Xsel := LF4.KSigma N) i) :=
    measurable_twoStage _ _ (measurable_basinIndex (momentContext N))
      (measurable_basinIndex c₂) (measurableSet_recordOneEvent i)
  rw [ProbabilityTheory.cond_apply hmeas₁, ← Set.preimage_inter,
    mixed_two_time_first_record ρ c₂ i]
  have hjoint : twoStage (basinIndex (momentContext N)) (basinIndex c₂)
      ⁻¹' (recordOneEvent i ∩ recordTwoEvent j)
      = jointRecordSector (basinIndex (momentContext N)) (basinIndex c₂) i j := rfl
  have hnn : 0 ≤ traceForm ρ (rankOneEffect (EuclideanSpace.single i (1 : ℂ))
      (single_norm_one' i)) := by
    rw [← spectral_born_eq_traceForm]
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg ((eigenvalues_isProbability ρ).1 k) (LF4.momentMap_nonneg _ i)
  rw [hjoint, mixed_two_time_born ρ i hpos c₂ j, ← mul_assoc,
    ENNReal.inv_mul_cancel (by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact lt_of_le_of_ne hnn (Ne.symm hpos))
      ENNReal.ofReal_ne_top, one_mul]

end MixedTwoTime

/-! ### ★★ The entangled two-time instantiation -/

/-- ★★ **Measure a subsystem of an entangled composite, then follow up — as one number on one
arena.** With the local system prepared at the reduced state of the composite point `x`,
measured in the local computational basis at `t₁` and in an ARBITRARY local context `c₂` at
`t₂`:

  `P(local record i at t₁ ∧ record j at t₂) = arenaObs (leftOp ∣e⁻¹ i⟩⟨e⁻¹ i∣) x · c₂.rate [eᵢ] j`.

The first factor is the composite arena's own local observation (`reducedDM` read on the
pattern projector); the second is the collapsed state's Born weight. The gated item of
`specs/two-time-luders-scoping.md`, delivered. -/
theorem entangled_two_time_born (e : FieldConfig K₁ N ≃ Fin d)
    (x : FieldArena (K₁ + K₂) N) (i : Fin d)
    (hpos : arenaObs (leftOp (Matrix.single (e.symm i) (e.symm i) 1)) x ≠ 0)
    (c₂ : ContextField d) (j : Fin d) :
    mixedTwoPrep (reducedDensity e x)
        (jointRecordSector (basinIndex (momentContext d)) (basinIndex c₂) i j)
      = ENNReal.ofReal (arenaObs (leftOp (Matrix.single (e.symm i) (e.symm i) 1)) x)
        * ENNReal.ofReal (c₂.rate (vertexPoint i) j) := by
  rw [mixed_two_time_born (reducedDensity e x) i (by rwa [traceForm_reducedDensity_single]) c₂ j,
    traceForm_reducedDensity_single]

/-- The stage-1 local record marginal on the entangled composite: the second apparatus cannot
retro-act on the reduced state's Born law. -/
theorem entangled_two_time_first_record (e : FieldConfig K₁ N ≃ Fin d)
    (x : FieldArena (K₁ + K₂) N) (c₂ : ContextField d) (i : Fin d) :
    mixedTwoPrep (reducedDensity e x) (twoStage (basinIndex (momentContext d)) (basinIndex c₂)
      ⁻¹' recordOneEvent i)
      = ENNReal.ofReal (arenaObs (leftOp (Matrix.single (e.symm i) (e.symm i) 1)) x) := by
  rw [mixed_two_time_first_record, traceForm_reducedDensity_single]

/-- ★ **The fate of the other local `Ω_j` on an entangled composite.** CONDITIONED on the local
record `i` at `t₁`, the next local partition carries the collapsed weights `c₂.rate [eᵢ]` — the
remote sector, and the entanglement, have no further say. -/
theorem entangled_two_time_other_fate (e : FieldConfig K₁ N ≃ Fin d)
    (x : FieldArena (K₁ + K₂) N) (i : Fin d)
    (hpos : arenaObs (leftOp (Matrix.single (e.symm i) (e.symm i) 1)) x ≠ 0)
    (c₂ : ContextField d) (j : Fin d) :
    ProbabilityTheory.cond (mixedTwoPrep (reducedDensity e x))
        (twoStage (basinIndex (momentContext d)) (basinIndex c₂) ⁻¹' recordOneEvent i)
        (twoStage (basinIndex (momentContext d)) (basinIndex c₂) ⁻¹' recordTwoEvent j)
      = ENNReal.ofReal (c₂.rate (vertexPoint i) j) :=
  mixed_two_time_other_fate (reducedDensity e x) i
    (by rwa [traceForm_reducedDensity_single]) c₂ j

/-- ★ **The Bell ray's two-time law**: record the first correlated pattern locally, then follow
up in any local context — `½ · c₂.rate [e_{x₀}] j`. -/
theorem bell_two_time_born (e : FieldConfig K₁ N ≃ Fin d)
    {x₀ x₁ : FieldConfig K₁ N} (hx : x₀ ≠ x₁) {y₀ y₁ : FieldConfig K₂ N} (hy : y₀ ≠ y₁)
    (c₂ : ContextField d) (j : Fin d) :
    mixedTwoPrep (reducedDensity e (Projectivization.mk ℂ (bellVec x₀ x₁ y₀ y₁)
          (bellVec_ne_zero x₀ x₁ y₀ y₁)))
        (jointRecordSector (basinIndex (momentContext d)) (basinIndex c₂) (e x₀) j)
      = ENNReal.ofReal (1 / 2) * ENNReal.ofReal (c₂.rate (vertexPoint (e x₀)) j) := by
  rw [entangled_two_time_born e _ (e x₀)
    (by rw [Equiv.symm_apply_apply, bell_local_weight₀ hx hy]; norm_num) c₂ j,
    Equiv.symm_apply_apply, bell_local_weight₀ hx hy]

end CSD.RecordLayer
