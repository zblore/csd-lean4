import CsdLean4.Empirical.CSD.Framework
import CsdLean4.Empirical.QM.Multipartite.GHZ

/-!
# Empirical/CSD: GHZ paradox (CSD-side reading, Mermin all-or-nothing)

**Category:** 3-Local (CSD-side companion to
`Empirical/QM/Multipartite/GHZ.lean`).

Pairs with `Empirical/QM/Multipartite/GHZ.lean` (Phase D6, Mermin
1990 *all-or-nothing* form). The QM file establishes two distinct
content streams:

1. **Quantitative Hilbert-side expectations** on the 3-qubit GHZ state
   `(|000⟩ + |111⟩)/√2`:
   - `ghz_expectation_xxx = +1`
   - `ghz_expectation_xyy = −1`
   - `ghz_expectation_yxy = −1`
   - `ghz_expectation_yyx = −1`

2. **Algebraic LHV impossibility** (`no_lhv_assignment_for_ghz`):
   no pre-assigned ±1 values to the six measurements
   `(wing ∈ Fin 3, axis ∈ PauliAxis)` simultaneously satisfy the four
   Mermin product constraints. Pure finite-state arithmetic; the
   theorem cites only `[propext, Quot.sound]` (no `Classical.choice`).

This file states the **CSD volume-ratio reading**: no
non-contextual ontic-outcome assignment to the six measurements on
the GHZ state satisfies the four Mermin product constraints. Under
CSD, a "±1 assignment to a measurement" corresponds to designating
one of two ontic outcome regions on Σ for each (wing, axis) pair.

## Framing choice and what we do *not* do here

Per `specs/empirical-csd-bridge-plan.md` revision (Tranche 0.3),
this file takes the **KS-template option (I)**: LHV-only transport,
no tripartite LF3 chain content, four expectation values as
re-exports.

We do **not** build a tripartite LF3 chain (a `LF3/Multipartite/GHZ/`
subtree paralleling `LF3/Singlet/*`). Three reasons:

- The four `ghz_expectation_*` theorems are QM-side Born predictions
  on `EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)` and have no CSD-ontic
  content of their own. They can be re-exported with framing prose.
- The structurally honest CSD signature of GHZ is the LHV
  impossibility (algebraic contradiction, single-shot, no
  statistics), not the per-sector frequency convergence. That
  signature transports cleanly through a KS-shaped partition-
  discipline bundle.
- A full tripartite LF3 chain (`PureGHZPreparation` + `MeasurementJointEig`
  + tripartite OP.p ↔ kernel + chain capstones) is ~1 week of new
  LF3 content. Pre-LF4 it would just double the LF4 surface area
  without strengthening any current theorem. Deferred as post-LF4
  ambition, with `LF3/Singlet/*` as the eventual structural model.

## Polarity

Negative-existential, matching KS and NoCloning. The bundle would
assert the existence of a non-contextual ontic-outcome assignment;
the headline theorem refutes this for the Mermin constraints.

## LF4 obligations carried

The bundle's load-bearing LF4-discharge content is **per-(wing, axis)
measurable-partition discipline**: for each of the six measurements,
the two ±1-outcome regions on Σ partition Σ up to `prepMeasure`-null
sets. Structurally identical to `PureSingletPreparation`'s per-sector
content and `CSDKSAssignmentBundle`'s per-basis content (Bell: 2-cell
partition over `Sign × Sign`; KS: 4-cell partition repeated 9 times;
GHZ: 2-cell partition repeated 6 times).

**Discharge route**: LF4-todo §2 (preparation-to-Hilbert correspondence)
+ §7 (projective-first outcome construction). No new LF4-todo entry
needed (same as KS retrofit).

## Distinction from CHSH, NoCloning, KS

- **CHSH/Bell**: probabilistic inequality violation; CSD reads as
  frequency convergence via the LF3 chain capstones.
- **NoCloning**: Hilbert-side polarity inversion; reduces to QM
  no-cloning via direct field extraction; carries LF4-todo §13 for
  the ontic-isometry lift.
- **KS**: structural contextuality (single-system, multi-context);
  reduces to combinatorial impossibility; reuses §2 + §7.
- **GHZ (this file)**: structural non-locality (multi-system,
  algebraic single-shot); reduces to LHV impossibility; reuses §2 + §7.

## Experimental verification

- Mermin 1990: *Phys. Rev. Lett.* **65**, 3373.
- Greenberger, Horne, Zeilinger 1989: original 3-particle state.
- Pan, Bouwmeester, Daniell, Weinfurter, Zeilinger 2000:
  *Nature* **403**, 515.

## Honest reading

This file does not establish CSD-non-locality by an independent
ontic-level construction. It states the CSD non-locality theorem
and reduces it to the QM-side LHV impossibility, which is pure
finite-state arithmetic. Pre-LF4 this is the right shape: the
bundle's `partition_*` fields encode "exactly one ±1 outcome per
(wing, axis)", and the impossibility is downstream of the four
Mermin product constraints.

Post-LF4, the bundle's `Context D` becomes concrete via the Kähler
`SectorData`, and the partition discipline becomes provable from
the projective-first outcome construction. The headline theorem
is then strictly stronger: it carries both the LHV impossibility
AND the CSD partition-discipline realisability.
-/

open MeasureTheory Set

namespace CSD
namespace Empirical
namespace CSDBridge
namespace GHZ

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- **CSD GHZ LHV-assignment bundle.** Structural carrier for the
data of a hypothetical non-contextual ontic-outcome assignment to
the six (wing, axis) Mermin measurements on a `SectorData D`.

The bundle extends `CSDBridge.Context D` (LF2-level discharge data)
and adds:

- 12 ontic outcome regions `O : Fin 3 → PauliAxis → Sign → OutcomeRegion`,
  one per (wing, axis, sign) measurement outcome.
- Two load-bearing fields encoding "each (wing, axis) measurement's
  two outcome regions form a measurable partition of Σ up to
  `prepMeasure`-null sets": `partition_pairwise_null` (the two ±1
  regions intersect in a null set) and `partition_cover_null` (their
  union covers Σ up to null).

The pairwise-null + cover-null formulation matches
`CSDKSAssignmentBundle`. Structurally a 2-cell partition repeated 6
times (vs KS's 4-cell partition repeated 9 times).

## LF4-discharge content

The `partition_*` fields are structurally identical to the per-sector
partition discipline of `LF3.PureSingletPreparation` and
`CSDKSAssignmentBundle.partition_*`. Same discharge route via LF4-
todo §2 + §7.

**Status: load-bearing, externally supplied, undischarged.**
LF4-todo §2 + §7. -/
structure CSDGHZAssignmentBundle
    (D : CSD.LF2.SectorData SigmaSpace P G)
  extends CSD.Empirical.CSDBridge.Context D where
  /-- 12 ontic outcome regions: 3 wings × 2 axes × 2 signs. -/
  O : Fin 3 → CSD.Empirical.GHZ.PauliAxis → CSD.LF3.Sign →
      D.toOntic.OutcomeRegion
  /-- **Status: load-bearing, externally supplied, undischarged.**
      LF4-todo §2 + §7. For each (wing, axis) measurement, the two
      ±1-outcome regions on Σ have `prepMeasure`-null intersection. -/
  partition_pairwise_null :
    ∀ (i : Fin 3) (ax : CSD.Empirical.GHZ.PauliAxis),
      ((D.toOntic.prepMeasure : ProbabilityMeasure SigmaSpace) : Measure SigmaSpace)
        ((O i ax CSD.LF3.Sign.plus).preEvent ∩
         (O i ax CSD.LF3.Sign.minus).preEvent) = 0
  /-- **Status: load-bearing, externally supplied, undischarged.**
      LF4-todo §2 + §7. For each (wing, axis) measurement, the two
      ±1-outcome regions cover Σ up to `prepMeasure`-null sets. -/
  partition_cover_null :
    ∀ (i : Fin 3) (ax : CSD.Empirical.GHZ.PauliAxis),
      ((D.toOntic.prepMeasure : ProbabilityMeasure SigmaSpace) : Measure SigmaSpace)
        (Set.univ \ ((O i ax CSD.LF3.Sign.plus).preEvent ∪
                     (O i ax CSD.LF3.Sign.minus).preEvent)) = 0

/-- **No CSD GHZ LHV assignment is satisfiable.** The CSD volume-
ratio companion to `Empirical.GHZ.no_lhv_assignment_for_ghz`.

For any bundle `b : CSDGHZAssignmentBundle D` and any ±1 LHV
assignment `λ : Fin 3 → PauliAxis → ℤ`, the four Mermin product
constraints from `Empirical.GHZ.no_lhv_assignment_for_ghz` cannot
hold simultaneously.

Reduces to the QM-side `no_lhv_assignment_for_ghz` by direct
extraction: the bundle's structural fields are not used in the
proof; they are load-bearing for the *interpretation* of the
bundle (they certify that "exactly one ±1 outcome per (wing, axis)
measurement" is the right shape of constraint, which is what
non-contextuality means at the ontic level).

**Interpretation.** Under CSD, a non-contextual ±1 LHV assignment
corresponds to a choice of one ontic outcome region per (wing,
axis) measurement, with the partition discipline ensuring the
choice is well-defined. This theorem shows: no such choice
satisfies the four Mermin product constraints, by the same
finite-state arithmetic contradiction the QM-side file
establishes (LHS product is `1` from squares, RHS is `-1`).

Same status pattern as `CSDKSAssignmentBundle`: the `partition_*`
fields encode the *meaning* of non-contextuality at the ontic
level, but the headline proof routes through the abstract
algebraic contradiction directly.

**Experimental verification:** Pan et al. 2000, *Nature* **403**, 515. -/
theorem no_csd_ghz_lhv_bundle
    {D : CSD.LF2.SectorData SigmaSpace P G} :
    ¬ ∃ (_b : CSDGHZAssignmentBundle D)
        (lambda : Fin 3 → CSD.Empirical.GHZ.PauliAxis → ℤ),
      (∀ i ax, lambda i ax = 1 ∨ lambda i ax = -1) ∧
      lambda 0 CSD.Empirical.GHZ.PauliAxis.x *
        lambda 1 CSD.Empirical.GHZ.PauliAxis.x *
        lambda 2 CSD.Empirical.GHZ.PauliAxis.x = 1 ∧
      lambda 0 CSD.Empirical.GHZ.PauliAxis.x *
        lambda 1 CSD.Empirical.GHZ.PauliAxis.y *
        lambda 2 CSD.Empirical.GHZ.PauliAxis.y = -1 ∧
      lambda 0 CSD.Empirical.GHZ.PauliAxis.y *
        lambda 1 CSD.Empirical.GHZ.PauliAxis.x *
        lambda 2 CSD.Empirical.GHZ.PauliAxis.y = -1 ∧
      lambda 0 CSD.Empirical.GHZ.PauliAxis.y *
        lambda 1 CSD.Empirical.GHZ.PauliAxis.y *
        lambda 2 CSD.Empirical.GHZ.PauliAxis.x = -1 := by
  rintro ⟨_, lambda, hpm, hxxx, hxyy, hyxy, hyyx⟩
  exact CSD.Empirical.GHZ.no_lhv_assignment_for_ghz
    ⟨lambda, hpm, hxxx, hxyy, hyxy, hyyx⟩

/-! ## Hilbert-side expectation values (re-exports)

The four QM-side Mermin expectation theorems are Born predictions on
the 3-qubit GHZ state. They have no CSD-ontic content of their own
(the QM-side file's proofs use pure linear algebra on
`EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)`), so we re-export them
without proof content, paired with CSD framing prose. The four values
are the *inputs* to the LHV impossibility above: they pin the signs
that any non-contextual ±1 assignment would have to reproduce.

Post-LF4 with a tripartite LF3 chain (`LF3/Multipartite/GHZ/*`
paralleling `LF3/Singlet/*`), these would become per-sector frequency-
convergence claims via a tripartite `LF3_ghz_frequency_convergence*`
chain capstone. Pre-LF4, they are Hilbert-side Born values re-exported
into the CSD namespace. -/

/-- **GHZ ⟨XXX⟩ = +1 (re-export).** Born expectation of `σ_x ⊗ σ_x ⊗ σ_x`
on the GHZ state. The QM-side prediction whose CSD-side reading would,
post-LF4, become a per-sector frequency-convergence claim via a
tripartite chain capstone (deferred). -/
theorem csd_ghz_expectation_xxx :
    Complex.re (inner ℂ CSD.Empirical.GHZ.ghzState
        (Matrix.toEuclideanLin (CSD.Empirical.GHZ.sigmaDotTriple
          CSD.Empirical.Bell.chshA CSD.Empirical.Bell.chshA
          CSD.Empirical.Bell.chshA) CSD.Empirical.GHZ.ghzState)) = 1 :=
  CSD.Empirical.GHZ.ghz_expectation_xxx

/-- **GHZ ⟨XYY⟩ = −1 (re-export).** -/
theorem csd_ghz_expectation_xyy :
    Complex.re (inner ℂ CSD.Empirical.GHZ.ghzState
        (Matrix.toEuclideanLin (CSD.Empirical.GHZ.sigmaDotTriple
          CSD.Empirical.Bell.chshA CSD.Empirical.Bell.chshA'
          CSD.Empirical.Bell.chshA') CSD.Empirical.GHZ.ghzState)) = -1 :=
  CSD.Empirical.GHZ.ghz_expectation_xyy

/-- **GHZ ⟨YXY⟩ = −1 (re-export).** -/
theorem csd_ghz_expectation_yxy :
    Complex.re (inner ℂ CSD.Empirical.GHZ.ghzState
        (Matrix.toEuclideanLin (CSD.Empirical.GHZ.sigmaDotTriple
          CSD.Empirical.Bell.chshA' CSD.Empirical.Bell.chshA
          CSD.Empirical.Bell.chshA') CSD.Empirical.GHZ.ghzState)) = -1 :=
  CSD.Empirical.GHZ.ghz_expectation_yxy

/-- **GHZ ⟨YYX⟩ = −1 (re-export).** -/
theorem csd_ghz_expectation_yyx :
    Complex.re (inner ℂ CSD.Empirical.GHZ.ghzState
        (Matrix.toEuclideanLin (CSD.Empirical.GHZ.sigmaDotTriple
          CSD.Empirical.Bell.chshA' CSD.Empirical.Bell.chshA'
          CSD.Empirical.Bell.chshA) CSD.Empirical.GHZ.ghzState)) = -1 :=
  CSD.Empirical.GHZ.ghz_expectation_yyx

end GHZ
end CSDBridge
end Empirical
end CSD
