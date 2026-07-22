/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Empirical.CSD.Framework
import CsdLean4.Empirical.QM.Contextuality.KS18

/-!
# Empirical/CSD: Kochen-Specker theorem (CSD-side reading, Cabello-18)

**Category:** 3-Local (CSD-side companion to
`Empirical/QM/Contextuality/KS18.lean`).

This file is the **impossibility** reading (no non-contextual value-assignment
bundle). Its **volume companion** is `Empirical/CSD/Contextuality/KS18Volume.lean`
(`ks18_context_born_frequency_volume`), which grounds each Cabello context's Born
weights as Fubini–Study typicality volumes on the fixed `Σ = ℂℙ³`.

Pairs with `Empirical/QM/Contextuality/KS18.lean`
(Cabello-Estebaranz-García-Alcaine 1996 18-vector configuration). The
QM file establishes two theorems:

- The abstract combinatorial impossibility `no_value_assignment_18_9`:
  no `Bool` assignment on `Fin 18` can satisfy the per-basis-exactly-one
  constraint on a `Fin 9 → Finset (Fin 18)` basis family whose
  appearance count is `2`. Proof via Fubini double-count + `omega`.
- `ks_no_value_assignment_cabello18`: specialisation to the explicit
  Cabello 9-basis structure.

Plus the geometric content: 18 explicit vectors in `EuclideanSpace ℝ (Fin 4)`,
pairwise orthogonality within each of the 9 bases.

This file states the **CSD volume-ratio reading**: no global ontic-
outcome-assignment to the 18 Cabello rays satisfies "exactly one ray
per basis is the realised outcome on Σ". Under CSD, a "value
assignment to a projective ray" corresponds to designating an ontic
outcome region on Σ whose `π`-image is the ray. A non-contextual
assignment is one that does not depend on which of the (up to 2)
bases the ray appears in.

## Polarity

Negative-existential, matching the QM-side combinatorial impossibility
and the NoCloning template. The CSD-side bundle would assert the
existence of a non-contextual ontic-outcome partition; the headline
theorem refutes this for the Cabello configuration.

## What the bundle interprets

The QM-side `Fin 18 → Bool` assignment corresponds, at the CSD ontic
level, to a choice of 18 outcome regions on Σ (one per Cabello vector)
that form a non-contextual partition discipline: for each of the 9
measurement bases, the 4 outcome regions corresponding to that
basis's vectors partition Σ up to `prepMeasure`-null sets. The
non-contextual `Bool` assignment then corresponds to selecting one
region per basis as the "realised" outcome.

KS contextuality at the CSD level: no such non-contextual partition
discipline is satisfiable, because of the underlying combinatorial
impossibility.

## LF4 obligations carried

The bundle's load-bearing LF4-discharge content is **per-basis
measurable-partition discipline**: that the 4 outcome regions for
each basis form a (`prepMeasure`-)measurable partition of Σ. This is
structurally identical to the per-sector partition discipline in
`PureSingletPreparation` (Bell singlet uses a 2×2 sector
decomposition; KS uses a 4-cell partition repeated 9 times).

**Discharge route**: LF4-todo §2 (preparation-to-Hilbert correspondence)
+ §7 (projective-first outcome construction). No new LF4-todo entry
needed for this retrofit. The 4-cell partition arises from the
projective measurement structure of each basis, which is exactly what
§7 packages.

## Distinction from CHSH, GHZ, NoCloning

- **CHSH/Bell**: probabilistic; CSD-side reads as frequency convergence.
- **GHZ**: algebraic single-shot from QM expectations; specific to
  local-HV.
- **NoCloning**: Hilbert-side polarity inversion; reduces to QM
  no-cloning via direct field extraction, carries LF4-todo §13.
- **KS (this file)**: structural contextuality at the ontic-partition
  level; bundle interprets the impossibility as a non-contextual
  partition discipline, headline reduces to the abstract combinatorial
  impossibility. No new LF4-todo entry.

## Experimental verification

- Cabello-Estebaranz-García-Alcaine 1996, *Phys. Rev. Lett.* **76**, 1881.
- Kirchmair et al. 2009, *Nature* **460**, 494 (trapped ions).
- Bartosik et al. 2009, *Phys. Rev. Lett.* **103**, 040403 (neutrons).

## Honest reading

This file does not establish CSD-contextuality by an independent
ontic-level combinatorial argument. It states the CSD contextuality
theorem and reduces it to the QM-side combinatorial impossibility,
which is itself Hilbert-free. Pre-LF4 this is the right shape: the
bundle's `partition_*` fields encode "exactly one outcome per
measurement context", and the impossibility is downstream of the
abstract Fubini argument the QM-side file already provides.

Post-LF4, the bundle's `Context D` becomes concrete via the Kähler
`SectorData`, and the partition discipline becomes provable from the
projective-first outcome construction (LF4-todo §7) rather than
externally supplied. The headline theorem here is then strictly
stronger: it carries both the combinatorial impossibility content AND
the CSD partition-discipline realisability content.
-/

open MeasureTheory Set

namespace CSD
namespace Empirical
namespace CSDBridge
namespace KochenSpecker

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **PARTIALLY-DECORATIVE BUNDLE: load-bearing fields not consumed in
the headline theorem.**

The `partition_pairwise_null` and `partition_cover_null` fields are
tagged as load-bearing by their own status markers, but
`no_csd_ks_assignment_bundle` uses only the bundle's `bases_eq` field
(trivial rewrite to align with the QM-side `cabelloBasis`). The two
partition fields are **inert** in the proof. (Compare GHZ where the
entire bundle is decorative; KS is milder because `bases_eq` is at
least touched.)

See `PLACEHOLDERS.md §8` for the canonical decorative-bundle ledger.

## Original (over-claiming) docstring follows

**CSD Kochen-Specker assignment bundle.** Structural carrier for
the data of a hypothetical non-contextual ontic-outcome assignment to
the Cabello-18 configuration on a `SectorData D`.

The bundle extends `CSDBridge.Context D` (LF2-level discharge data:
`μFS`, probability witness, measure bridge) and adds:

- 18 ontic outcome regions `O : Fin 18 → D.toOntic.OutcomeRegion`,
  one per Cabello vector.
- The Cabello 9-basis structure fixed to
  `CSD.Empirical.KochenSpecker.cabelloBasis` (the explicit Finset
  family from the QM-side file).
- Two load-bearing fields encoding "each basis's 4 outcome regions
  form a measurable partition of Σ up to `prepMeasure`-null sets":
  `partition_pairwise_null` (pairwise intersections are null) and
  `partition_cover_null` (the complement of the union is null).

The pairwise-null + cover-null formulation is used instead of a
`MeasurablePartition` structure to avoid `Finset (Fin 18) → Fin 4`
indexing friction (per bridge plan risk #1 for this retrofit).

## LF4-discharge content

The `partition_*` fields are structurally identical to the per-sector
partition discipline of `LF3.PureSingletPreparation` (Bell uses a 2×2
sector decomposition; KS uses a 4-cell partition repeated 9 times).
Same discharge route via the concrete Kähler `SectorData` and the
projective-first outcome construction.

**Status: load-bearing, externally supplied, undischarged.**
LF4-todo §2 + §7. -/
structure CSDKSAssignmentBundle
    (D : CSD.LF2.SectorData SigmaSpace P G)
  extends CSD.Empirical.CSDBridge.Context D where
  /-- 18 ontic outcome regions on Σ, one per Cabello vector. -/
  O           : Fin 18 → D.toOntic.OutcomeRegion
  /-- The Cabello 9-basis combinatorial data, fixed to the QM-side file. -/
  bases       : Fin 9 → Finset (Fin 18)
  /-- Witness that the bundle's `bases` field is exactly the
      Cabello basis structure from the QM-side file. -/
  bases_eq    : bases = CSD.Empirical.KochenSpecker.cabelloBasis
  /-- **Status: load-bearing, externally supplied, undischarged.**
      LF4-todo §2 + §7. For each basis B and each pair of distinct
      vectors v, w in that basis, the intersection of their ontic
      outcome regions' pre-events is `prepMeasure`-null. -/
  partition_pairwise_null :
    ∀ B : Fin 9, ∀ {i j : Fin 18}, i ∈ bases B → j ∈ bases B → i ≠ j →
      ((D.toOntic.prepMeasure : ProbabilityMeasure SigmaSpace) : Measure SigmaSpace)
        ((O i).preEvent ∩ (O j).preEvent) = 0
  /-- **Status: load-bearing, externally supplied, undischarged.**
      LF4-todo §2 + §7. For each basis B, the union of the basis's
      ontic outcome regions' pre-events covers Σ up to
      `prepMeasure`-null sets. -/
  partition_cover_null :
    ∀ B : Fin 9,
      ((D.toOntic.prepMeasure : ProbabilityMeasure SigmaSpace) : Measure SigmaSpace)
        (Set.univ \ ⋃ v ∈ bases B, (O v).preEvent) = 0

/-- **TRANSPORT-ONLY (mostly): proof uses only `b.bases_eq` (a trivial
rewrite) and then calls QM-side `ks_no_value_assignment_cabello18` on
the bare lambda.** The bundle's `partition_*` fields are inert. See
`PLACEHOLDERS.md §8`.

**No CSD Kochen-Specker assignment bundle is satisfiable.** The
CSD volume-ratio companion to
`CSD.Empirical.KochenSpecker.ks_no_value_assignment_cabello18`.

For any bundle `b : CSDKSAssignmentBundle D` and any `Bool` assignment
`λ : Fin 18 → Bool`, the per-basis-exactly-one constraint
"for each basis B, exactly one vector in `b.bases B` has `λ v = true`"
is unsatisfiable.

Reduces to the QM-side combinatorial impossibility
`ks_no_value_assignment_cabello18` by direct extraction: the bundle's
`bases_eq` field aligns `b.bases` with `cabelloBasis`, after which the
QM-side theorem applies unchanged.

**Interpretation.** Under CSD, a non-contextual `{0, 1}`-valued
assignment to the 18 Cabello projectors corresponds to a non-contextual
choice of one ontic outcome region per measurement context (basis).
The bundle's `partition_*` fields encode the partition discipline
that makes this choice well-defined. This theorem shows: no such
choice exists, because the underlying combinatorial constraint
`9 = 2 · k` has no integer solution.

The `partition_*` fields are not used in the proof but are
load-bearing for the *interpretation* of the bundle: they certify
that "exactly one outcome per measurement" is the right shape, which
is what KS rules out. Same pattern as `CSDCloningBundle`'s tensor
structure in `Empirical/CSD/NoCloning.lean`.

**Experimental verification:** Kirchmair et al. 2009 (trapped ions);
Bartosik et al. 2009 (neutrons). -/
theorem no_csd_ks_assignment_bundle
    {D : CSD.LF2.SectorData SigmaSpace P G} :
    ¬ ∃ (b : CSDKSAssignmentBundle D) (lambda : Fin 18 → Bool),
      ∀ B : Fin 9, ((b.bases B).filter (fun v => lambda v = true)).card = 1 := by
  rintro ⟨b, lambda, h_one⟩
  apply CSD.Empirical.KochenSpecker.ks_no_value_assignment_cabello18
  refine ⟨lambda, ?_⟩
  intro B
  have := h_one B
  rwa [b.bases_eq] at this

/-! ## Geometric content re-export

The QM-side file establishes pairwise orthogonality of the 18 Cabello
vectors within each of the 9 bases. The CSD-side reading does not add
new geometric content; we re-export the QM-side theorem for symmetry
with `Empirical/CSD/Bell.lean`'s pattern of re-exporting LF3 chain
capstones into the CSD namespace. -/

/-- **TRANSPORT-ONLY: proof body is the QM-side theorem.** See
`PLACEHOLDERS.md §3`.

**Cabello-18 pairwise orthogonality (re-export).** Within each of
the 9 bases of `cabelloBasis`, any two distinct vectors are orthogonal
in ℝ⁴. Direct re-export of
`CSD.Empirical.KochenSpecker.cabello_pairwise_orthogonal_in_basis`. -/
theorem csd_cabello_orthogonal_in_basis :
    ∀ B : Fin 9, ∀ i ∈ CSD.Empirical.KochenSpecker.cabelloBasis B,
      ∀ j ∈ CSD.Empirical.KochenSpecker.cabelloBasis B, i ≠ j →
      inner ℝ (CSD.Empirical.KochenSpecker.cabelloVec i)
              (CSD.Empirical.KochenSpecker.cabelloVec j) = 0 :=
  CSD.Empirical.KochenSpecker.cabello_pairwise_orthogonal_in_basis

end KochenSpecker
end CSDBridge
end Empirical
end CSD
