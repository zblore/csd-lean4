/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF3.ContextMap
public import CsdLean4.LF2.Preparation

/-!
# LF3 Singlet projective outcomes

**Category:** 3-Local (pre-LF4 plan Phase 6 — `MeasurementJointEig` bundle,
`SingletProjectiveOutcome` set in `P`, OP.p ↔ `P_st` identity).

`MeasurementJointEig` records four unit, distinct vectors and their
Born overlaps with the preparation vector. It does not record spin
operators, eigen-equations or pairwise orthogonality. The concrete `LF4.kJED`
constructor supplies vectors built from the genuine singlet spin calculation.

`SingletProjectiveOutcome` is an exact representative-vector preimage.
Its four regions are disjoint, and measurable when the representative map
is measurable. They need not cover the target or be nonempty; exact vector
equality also depends on phase. They are separate from the calibrated
ontic fibre regions in the LF4 singlet constructors.

The two OP identities compose the pure-state Born theorem with the
bundle's overlap identity. The trace-form route uses the proved
`LF2.PurePreparation.born_rank_one`; the direct route uses Dirac integration
via `born_rank_one_direct`. Both have only foundational axioms. The LF3
frequency capstones use the direct route through `weight_eq_P_st`.
-/

@[expose] public section

open MeasureTheory

namespace CSD
namespace LF3

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

variable {N : ℕ}

/-- Four normalized, distinct measurement vectors with prescribed singlet
    overlaps. The intended interpretation is joint spin eigenstates, as
    constructed by `LF4.kJED`; this abstract interface carries neither
    eigen-equations nor orthogonality. -/
structure MeasurementJointEig
    (ctx : MeasurementContext) (ψ : EuclideanSpace ℂ (Fin N)) where
  /-- The joint spin eigenstate at sector `(s, t)`. -/
  eig : Sign → Sign → EuclideanSpace ℂ (Fin N)
  /-- Each joint eigenstate is unit-normalised. -/
  eig_unit : ∀ s t, ‖eig s t‖ = 1
  /-- Eigenstates at distinct sectors are distinct (as vectors in
      Hilbert space). Used to derive disjointness of the projective
      outcome regions. -/
  eig_distinct : ∀ s t s' t', (s, t) ≠ (s', t') → eig s t ≠ eig s' t'
  /-- **Born identity.** The squared inner product of `ψ` with the
      `(s, t)` joint eigenstate equals the singlet kernel value. Proved
      in-corpus for the singlet (`Singlet.JointEig.singletJointEig_born`);
      supplied by callers and discharged in `LF4.kJED` after reindexing. -/
  born_eq_P_st : ∀ s t, ‖inner ℂ ψ (eig s t)‖ ^ 2 = P_st ctx.a ctx.b s t

namespace MeasurementJointEig

variable {ctx : MeasurementContext} {ψ : EuclideanSpace ℂ (Fin N)}

/-- **Singlet projective outcome region** at sector `(s, t)`. For a
    caller-supplied representative map `rep : P → EuclideanSpace ℂ (Fin N)`,
    this is the rep-preimage of the joint eigenstate `eig s t`. The
    four regions are pairwise disjoint and measurable when `rep` is.
    Exact vector equality is phase-sensitive; the regions may be empty
    and no coverage of `P` is asserted. -/
def SingletProjectiveOutcome
    (rep : P → EuclideanSpace ℂ (Fin N))
    (jed : MeasurementJointEig ctx ψ) (s t : Sign) : Set P :=
  rep ⁻¹' {jed.eig s t}

/-- Each `SingletProjectiveOutcome` is measurable when `rep` is. -/
lemma singletProjectiveOutcome_measurable
    {rep : P → EuclideanSpace ℂ (Fin N)} (hrep_meas : Measurable rep)
    (jed : MeasurementJointEig ctx ψ) (s t : Sign) :
    MeasurableSet (jed.SingletProjectiveOutcome rep s t) :=
  hrep_meas (MeasurableSet.singleton _)

omit [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace] [MeasurableSpace P]
  [Group G] [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P] in
/-- The `SingletProjectiveOutcome` family is pairwise disjoint: regions
    at distinct sectors `(s, t) ≠ (s', t')` are disjoint. Routes through
    `eig_distinct` and singleton-preimage disjointness. -/
lemma singletProjectiveOutcome_disjoint_distinct
    {rep : P → EuclideanSpace ℂ (Fin N)}
    (jed : MeasurementJointEig ctx ψ)
    {s t s' t' : Sign} (h_ne : (s, t) ≠ (s', t')) :
    Disjoint (jed.SingletProjectiveOutcome rep s t)
             (jed.SingletProjectiveOutcome rep s' t') := by
  refine Set.disjoint_iff_inter_eq_empty.mpr ?_
  ext p
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and,
             SingletProjectiveOutcome, Set.mem_preimage, Set.mem_singleton_iff]
  intro hp hp'
  exact jed.eig_distinct s t s' t' h_ne (hp.symm.trans hp')

end MeasurementJointEig

/-! ### OP.p ↔ P_st identity (option (B) chain bridge content) -/

/-- Compose the trace-form pure-state Born identity with the bundle's
    supplied overlap identity. `born_rank_one` uses the proved effect-Gleason
    representation theorem; this composition has only foundational axioms. -/
theorem OP_p_at_jointEig_eq_P_st
    (D : LF2.SectorData SigmaSpace P G) (μFS : Measure P) [IsProbabilityMeasure μFS]
    (bridge : LF2.MeasureBridgeData D μFS)
    (μprep : Measure SigmaSpace) [IsProbabilityMeasure μprep]
    {ctx : MeasurementContext}
    (PP : LF2.PurePreparation D μprep N) (hN : 2 ≤ N)
    (jed : MeasurementJointEig ctx PP.ψ)
    (s t : Sign) :
    (LF2.OperationalPackage.fromPreparation D μFS bridge μprep
        PP.rep PP.hrep_unit PP.hrep_meas).p
      (LF2.rankOneEffect (jed.eig s t) (jed.eig_unit s t))
      = P_st ctx.a ctx.b s t := by
  rw [PP.born_rank_one D μFS bridge μprep hN (jed.eig s t) (jed.eig_unit s t)]
  exact jed.born_eq_P_st s t

/-- The OP probability equals the singlet weight by direct Dirac integration
    and the bundle's supplied overlap identity. This is the route used by
    the LF3 frequency capstones; no effect-Gleason representation is needed. -/
theorem OP_p_at_jointEig_eq_P_st_direct
    (D : LF2.SectorData SigmaSpace P G) (μFS : Measure P) [IsProbabilityMeasure μFS]
    (bridge : LF2.MeasureBridgeData D μFS)
    (μprep : Measure SigmaSpace) [IsProbabilityMeasure μprep]
    {ctx : MeasurementContext}
    (PP : LF2.PurePreparation D μprep N)
    (jed : MeasurementJointEig ctx PP.ψ)
    (s t : Sign) :
    (LF2.OperationalPackage.fromPreparation D μFS bridge μprep
        PP.rep PP.hrep_unit PP.hrep_meas).p
      (LF2.rankOneEffect (jed.eig s t) (jed.eig_unit s t))
      = P_st ctx.a ctx.b s t := by
  rw [PP.born_rank_one_direct D μFS bridge μprep (jed.eig s t) (jed.eig_unit s t)]
  exact jed.born_eq_P_st s t

end LF3
end CSD
