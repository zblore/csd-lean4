import CsdLean4.LF3.ContextMap
import CsdLean4.LF2.Preparation

/-!
# LF3 Singlet projective outcomes

**Category:** 3-Local (pre-LF4 plan Phase 6 — `MeasurementJointEig` bundle,
`SingletProjectiveOutcome` set in `P`, OP.p ↔ `P_st` identity).

This module hosts the measurement-context-driven side of the pre-LF4
Option (B) chain design:

- `MeasurementJointEig ctx ψ` — a bundle of joint spin eigenstates for a
  given measurement context, with unit-norm, pairwise distinctness, and
  the Born-identity hypothesis `‖⟨ψ, eig s t⟩‖² = P_st ctx.a ctx.b s t`.
  Caller-supplied per LF4-todo §2 (preparation ↔ Hilbert correspondence)
  + §7 (projective-first outcomes); LF4 will discharge the Born
  identity via spectral construction of joint spin eigenstates.

- `SingletProjectiveOutcome` — the rep-preimage of the joint eigenstate
  point in `P`. The four (s, t)-indexed regions form a measurable,
  pairwise-disjoint family.

- `OP_p_at_jointEig_eq_P_st` — the headline algebraic identity: the
  operational-package probability of the rank-1 effect through
  `eig s t` equals `P_st ctx.a ctx.b s t`. Proof composes
  `LF2.PurePreparation.born_rank_one` (Busch-mediated chain critical
  path) with `MeasurementJointEig.born_eq_P_st`. Cites
  `busch_effect_gleason`.

- `OP_p_at_jointEig_eq_P_st_direct` — the volume-ratio direct variant.
  Uses `LF2.PurePreparation.born_rank_one_direct`; cites only the
  foundational triple.

## Design (option (B), pure/measurement separation)

Per the 2026-05-18 design decision: the LF3 chain bridge goes via OP.p
(OP integration), not via `projectiveWeight` (direct measure). This
matches CSD's volume-ratio reading — probability is the OP integral of
`effectProjFn` against the projective measure bridge — and keeps the
preparation `μprep` context-independent. Measurement-context content
lives in `MeasurementJointEig`, structurally separate from
`LF2.PurePreparation`.

The Phase 7 LF3 chain refactor will consume a `MeasurementJointEig`
bundle plus an ontic-weight ↔ OP.p bridge hypothesis on the
preparation's outcome regions. Until LF4 instantiates a concrete
`SectorData` with concrete Σ, π, Φ, μprep, the bridge stays as a
structural hypothesis on the chain capstone.
-/

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

/-- **Measurement-context joint eigenstate data.** For a measurement
    context `ctx` and a pure-state vector `ψ`, a bundle of the four
    joint spin eigenstates of `(σ_{ctx.a} ⊗ I) (I ⊗ σ_{ctx.b})` together
    with their unit-norm, pairwise distinctness, and the Born-identity
    hypothesis tying their inner product with `ψ` to the singlet kernel
    `P_st`.

    The Born identity `‖⟨ψ, eig s t⟩‖² = P_st ctx.a ctx.b s t` is the
    LF4-todo §2 (preparation ↔ Hilbert correspondence) + §7 (projective-
    first outcomes) discharge target: at LF4 instantiation time, the
    eigenstates are constructed from the spectral decomposition of the
    joint spin projector `jointSpinProj`, and the Born identity falls
    out of the rank-1 projector identity `jointSpinProj = |eig⟩⟨eig|`.
    Pre-LF4 carries this as a structural hypothesis. -/
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
      `(s, t)` joint eigenstate equals the singlet kernel value. This is
      the LF4-todo §2 + §7 discharge target carried as a hypothesis
      pre-LF4. -/
  born_eq_P_st : ∀ s t, ‖inner ℂ ψ (eig s t)‖ ^ 2 = P_st ctx.a ctx.b s t

namespace MeasurementJointEig

variable {ctx : MeasurementContext} {ψ : EuclideanSpace ℂ (Fin N)}

/-- **Singlet projective outcome region** at sector `(s, t)`. For a
    caller-supplied representative map `rep : P → EuclideanSpace ℂ (Fin N)`,
    this is the rep-preimage of the joint eigenstate `eig s t`. The
    four (s, t)-indexed regions form a measurable, pairwise-disjoint
    family of subsets of the abstract projective target `P`. -/
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

set_option linter.unusedSectionVars false in
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

/-- **Operational-package probability of the rank-1 sector effect equals
    `P_st` (Busch-mediated chain critical path).** For a pure
    preparation `PP` and joint eigenstate data `jed` keyed to `PP.ψ`,
    the OP probability of the rank-1 effect through `jed.eig s t`
    equals `P_st ctx.a ctx.b s t`. Composes
    `LF2.PurePreparation.born_rank_one` (cites `busch_effect_gleason`)
    with `MeasurementJointEig.born_eq_P_st`.

    This is the chain bridge content under the option (B) design: the
    OP integration of the rank-1 sector effect against the projective
    measure bridge gives the singlet kernel value. Spec §5.4 four-
    ingredient combinatorial framing applies. -/
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

/-- **Volume-ratio direct form (auxiliary).** Same conclusion as
    `OP_p_at_jointEig_eq_P_st`, but proved via the direct Dirac
    integration form `LF2.PurePreparation.born_rank_one_direct`. Cites
    only the foundational triple (no `busch_effect_gleason`).

    Tagged as the eventual migration target for the chain capstones
    once downstream consumers accommodate the leaner cite set; v1.00
    chain stays Busch-mediated per spec §5.4. -/
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
