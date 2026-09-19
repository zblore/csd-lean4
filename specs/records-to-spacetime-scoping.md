# From the record layer to spacetime: scoping note (BACKLOG #38 and #39)

**Status:** SCOPED 2026-09-19, after a survey of `CsdLean4/RecordLayer/` (81 modules), the composite and
multi-time record modules, the CV locality modules (`CV/ModeLocality`, `DynamicalLocality`,
`SupportSpreading`, `LiebRobinson`), and the two papers' own statements (Paper D §5.2 and §7.12). Every
claim below about the corpus was read from theorem *types*. Nothing here is built; §7 prices what could be,
and §8 says plainly what has no Lean shape.

The two rows this note serves were kept out of the repository's documents until 2026-09-19 at the author's
earlier decision and are on the board now at the author's instruction. This note is where the programme's
spacetime reading is written down in the repository for the first time, at the honesty level of every other
scoping note: **nothing of it is in Lean and nothing is claimed.**

## 1. The question

Paper D commits to this much and no more: "correspondence with spacetime coordinates is not fundamental at
this level, but arises only after further coarse-graining and effective description … additional projections
may be introduced to define effective macroscopic coordinates" (§5.2), and "spacetime relations and
relativistic structure are treated as emergent and are not derived in the present paper" (ontological
commitment 4). Its §7.12 adds the reading that row 39 states: locality on the ontic manifold, apparent
nonlocality in emergent spacetime, because "spacetime separation belongs to the emergent projected
description, whereas the underlying ontic state is unified."

The programme's own stack, as the author has stated it, goes one step further than the paper: spacetime is
to emerge **from the records**, the definite outcomes de-isolation events leave in `Σ`, which accumulate; so
spacetime is downstream of measurement. The question for this note is therefore concrete:

> Given what a record *is* in Lean, is there a relation between records, definable from the corpus's
> objects and constrained by its theorems, that could carry metric or causal structure? If so, what is the
> first brick; if not, what is missing and whose call it is.

The answer, in one line: there is a **causal** structure with a Lean shape today, and it is *relative to an
assumed interaction graph*; there is an **entanglement distance** with a Lean shape, and it is a metric on
subsystem pairs at a point, not a spacetime; and there is **no Lean shape** for emergence proper, because the
papers do not say which projection defines the macroscopic coordinates and that choice is the author's.

## 2. What a record is, in Lean

Everything the corpus calls a record reduces to the following objects.

| Object | Where | Type, in words |
|---|---|---|
| A record event | `RecordLayer/GlobalBasin.lean`, `globalBasin c i` | a measurable subset of `Σ = ℂℙⁿ⁻¹ × T²`, fixed by the apparatus context `c` and the outcome `i`, mentioning no preparation; distinct outcomes are disjoint (`globalBasin_pairwiseDisjoint`) |
| The ontic selection | `RecordLayer/GlobalRecordClosure.lean`, `globalOutcome` | which basin the microstate lies in; the record semantics `globalRecordSemantics` is a function of `(context, outcome, time)` and nothing else |
| The record's weight | `globalBasin_born` | the epistemic measure of the basin at preparation `ψ` is `‖⟨eᵢ, ψ⟩‖²` |
| How a record is made | `RecordLayer/ShearDeIsolation.lean`, `SwapWitness`, `PointerArena` | a de-isolation propagator on an arena `system × register × bank`; the register coordinate is the record |
| That it persists | `RecordLayer/RecordPersistence.lean`, `record_persists_on_interval`, `readout_persists_on_interval` | the pointer stays in the outcome's region on a time window `[T_M, T_M + τ_R]` of the flow |
| Records in sequence | `RecordLayer/NStepChain.lean`, `csd_nstep_born`; `TwoTimeLuders.lean`, `two_stage_joint`; `DrivenTwoTime.lean`, `driven_two_stage_joint` | a chain of records at flow times `t₁ < t₂ < …`, each consuming a fresh bank, with the joint law a product of per-step rates at the collapsed states |
| Records on a composite | `RecordLayer/CompositeRecord.lean`, `composite_local_record_born`; `EntangledRecord.lean`, `entangled_local_record_born`, `entangled_local_followup` | a local apparatus on one tensor sector of a composite arena; its record weights are the reduced state's Born weights, for every joint point, entangled included |

Two absences matter for this note and are visible in the types.

* **A record has no location.** The only "where" a record carries is *which tensor sector* of a composite it
  was made on (`LocalBlockBridge.lean`'s `localBlock`), an index into a factorisation the corpus posits
  (Posit 7, local tomography, `R-017`). No record carries a position, and no theorem relates two records by
  anything spatial.
* **A record's time is the flow parameter.** `t` in `globalRecordSemantics` and the readout time of the
  propagators is the external real parameter of the Hamiltonian flow. Time is not emergent anywhere in the
  corpus; it is the parameter the dynamics is written in.

So "spacetime from records" cannot mean "spacetime from properties records already have". It has to mean a
new relation, defined on records or on the sectors and contexts that make them.

## 3. Candidate relations between records

Four candidates, each assessed against the corpus as it stands.

**(a) Order from the chain.** Records are totally ordered by the flow parameter, and the chain law
composes them (`csd_nstep_born`). This is a causal order, but it is the external time, assumed and not
derived. It gives nothing toward emergence and is stated here only to rule it out.

**(b) Influence from support spreading, the coupling-graph light cone.** On the CV register the corpus
proves: observables of disjoint mode sets commute (`commute_of_disjointSupport`); the free flow never spreads
support (`commute_heisenberg_freeFieldU_pow`); an interaction with coupling graph `E` spreads support at most
one edge per period, so after `n` periods an observable's support lies in the graph ball `graphBall E S n`
(`heisenberg_graphInteractingU_pow_supportedOn`), observables whose balls are still disjoint still commute
(`commute_heisenberg_graphInteractingU_pow`), and a coupling disjoint from the support acts trivially
(`heisenberg_eq_of_disjoint`); and the continuous-time form, the linear Lieb–Robinson bound
`‖[A(t), B]‖ ≤ 4|t|‖T‖‖A‖‖B‖` with `T` the part of the generator that couples across the cut
(`norm_commutator_heisenbergFlow_le`). Non-vacuity is proved: a concrete kick spreads support
(`spreadKick_not_supportedOn`).

This is the closest thing in the corpus to a **causal structure**: "record `A` can influence record `B`
within `n` periods" is definable as "`B`'s sector lies in the `n`-ball of `A`'s sector", and the light-cone
theorem says nothing outside the ball is touched. Two honesty points, both structural. First, the graph `E`
is an input, the interaction's coupling pattern, so this is causal structure *relative to an assumed
geometry*, the same boundary as `R-015` (which interaction an apparatus realises). Second, the modes are a
tensor factorisation, so the whole construction stands on Posit 7. What is derived is the cone, given the
graph; what is not derived is the graph.

**(c) Distance from entanglement.** Paper D and the EFT departures note both say spacetime "is meant to
emerge from entanglement geometry." The corpus has the ingredients at finite dimension: reduced states of a
joint point (`reducedDM`, `reduceB`), von Neumann entropy with its bound (`vonNeumannEntropy_le_log_card`),
concavity, data processing, and strong subadditivity read in from Physlib through `csd-qit-bridge`. A mutual
information between two sectors of a joint point is therefore definable, and a candidate "distance"
`d(A, B) := −log I(A : B)` with it. What can be proved about it with what exists: nonnegativity, symmetry, the
value on product points (mutual information zero, distance infinite or maximal), and, through strong
subadditivity, monotonicity under enlarging a sector. What cannot: that it is a metric on anything larger
than a fixed point's sectors, that it is stable under the flow, or that it has any continuum limit. And the
finite arena bounds it: entropies are at most `log N`, so every such distance is bounded, and the space it
builds is compact and small.

**(d) A coarse-graining projection.** This is what Paper D actually names: "additional projections may be
introduced to define effective macroscopic coordinates relevant to observers and apparatus." In Lean that is
a map `π' : Σ → M` (or a map on records) into a finite structure carrying the coordinates, with the record
statistics factoring through it. It has a clean Lean *shape* as a structure. It has no Lean *content* until
someone says what `π'` is, and the papers do not. Which projection defines the macroscopic coordinates is,
like which interaction an apparatus realises, a modelling input. It is the author's call, not a theorem's.

## 4. What the finite arena can and cannot support

* **Compactness and finiteness.** `Σ = ℂℙⁿ⁻¹ × T²` is compact and finite-dimensional, with a finite total
  measure (`arenaVolume_univ`) and finitely many outcomes per context. Anything defined from it is bounded or
  finite: no unbounded cones, no infinite volumes, no continuum of positions. The EFT departures note already
  draws this line: finite `N` gives bounded discrete *spectra*, not a spacetime lattice, and "lattice" is the
  wrong word because a literal one breaks Lorentz invariance.
* **No Lorentz structure.** The CV rung's light cone moves one graph edge per period, a preferred frame by
  construction. Anything emergent from it is discrete and Galilean at best. Relativistic structure is
  exactly what Paper D defers and this note does not touch.
* **Time is external.** See §2. An account of emergent time would be a different programme from this one.
* **Locality on `Σ` has one available meaning.** A joint ontic point is not a pair of local points
  (`segre_not_surjective`: the Segre embedding is injective but not surjective from two levels a side), so
  "the flow is local on `Σ`" cannot mean "acts factor by factor". It can only mean what the flow provably
  is: a continuous, measure-preserving map of a connected manifold (`kMuL_map_hamiltonianFlow`,
  `arenaForm_isSymplectic`). Row 39's "Σ-local" has to be read that way or it is false on the corpus's own
  theorems.

## 5. What the existing theorems constrain

Any account of spacetime from records that the corpus would accept has to respect all of the following, and
each is a theorem rather than a wish.

1. **Local records read marginals.** `composite_local_record_born`, `entangled_local_record_born`: a local
   apparatus's record weights on a joint point are the reduced state's Born weights, and after a local record
   the follow-up statistics are the local post-state's (`entangled_local_followup`). The correlations live in
   the joint point; nothing local sees more than its marginal.
2. **No signalling.** `tensorSector_no_signalling`, and on the singlet `no_signalling_alice` / `_bob`: a
   local record's distribution does not depend on the remote context. Any emergent separation relation is
   consistent with this automatically, and nothing emergent may break it.
3. **No local explanation.** `bell_general_separation`, `general_ks_noNonContextualValuation`: no
   local-hidden-variable table and no non-contextual valuation reproduce the records. So the emergent
   description *must* be nonlocal and contextual; a spacetime in which the records looked locally explicable
   would contradict the corpus. This is the theorem-level content behind row 39's second clause.
4. **Bounded influence, given a graph.** The light-cone and Lieb–Robinson theorems of §3(b). Any candidate
   causal relation between records must be at least as coarse as the coupling graph's cones.
5. **The chain and persistence.** `csd_nstep_born`, `record_persists_on_interval`: records are made in
   sequence, persist on a window, and the joint law factors. An emergent structure that reordered records or
   let them vanish between readouts would contradict this.
6. **The cell law.** `torusGenerated_eq_momentMap` with Posit 1: the rates that define the basins are the
   moment map once the context's rates generate its pointer torus. The record's *shape* is not free; it is
   pinned by the arena's geometry and one posit. This is the one open foundations item of the whole
   programme (rows 18 and 19), and it sits underneath this note too: spacetime from records inherits every
   posit the records rest on.

## 6. Row 39, the reading: what would have to be true, and what would refute it

The reading is: entangled correlations are local in `Σ` and appear nonlocal only in emergent spacetime.

**What would have to be true.** Three things, and the corpus can name each.

* (i) There is a relation `R` on sectors or records under which the joint flow is local: influence respects
  `R`. With `R` the coupling graph, this is the light-cone theorem, so (i) is *instantiated* today, relative
  to `R` being assumed.
* (ii) `R`-distant records show Bell-violating correlations without signalling. `bell_record_weight₀` /
  `bell_record_weight₁` give the Bell ray's local record weights, `bell_general_separation` the violation,
  and the no-signalling theorems the absence of signals. So (ii) holds today for records on distinct tensor
  sectors.
* (iii) `R` is *emergent*: definable from the records rather than assumed with the interaction. This is the
  part with no theorem, and it is the whole content of the reading. Everything else in it is already a
  theorem about the assumed factorisation.

**What would refute it.** (a) A flow on `Σ` whose influence outran every graph bound: ruled out for the
graph-interacting drives by `heisenberg_graphInteractingU_pow_supportedOn`, and in continuous time by the
Lieb–Robinson bound. (b) A local record whose statistics depended on the remote context: ruled out by
no-signalling. (c) "Local in `Σ`" turning out to require a product decomposition of points: it does not, by
§4, but it does force the weaker meaning, and the reading has to be stated in that meaning.

**Verdict on the reading.** Not refuted; not established; and on the corpus's own terms it is a *conjecture
about (iii)* only, since (i) and (ii) are theorems given the factorisation. Its honest one-sentence form is:
"the corpus proves bounded influence and non-signalling correlations across an assumed tensor cut, and
conjectures that the cut is itself emergent." That sentence can be written into the documents now.

## 7. What could be built, priced

The rows are numbered `ST-1` to `ST-4`. `P` is P(success), `V` is value for the question in §1. None of them
is "spacetime emergence"; the note says so in §8.

| # | Brick | Cx | P | V | What it lands |
|---|---|---|---|---|---|
| **ST-1** | **The influence preorder on records.** On a CV-type arena with coupling graph `E`, define the relation "the record of context `c₁` on sector `S₁` can influence the record of `c₂` on `S₂` within `n` periods" as `S₂ ⊆ graphBall E S₁ n`, and prove: it is a preorder in `n`; records outside each other's `n`-balls commute and are jointly measurable (`commute_heisenberg_graphInteractingU_pow` lifted to basins); their joint record law factors. | **S–M** | high | medium: the first theorem *about records* with a causal shape, honestly labelled relative to `E` |
| **ST-2** | **Entanglement distance on the composite arena.** `mutualInfo` of two sectors of a joint point from the reduced states; `d := −log I`; nonnegativity, symmetry, the product-point value, and monotonicity under sector enlargement through the bridge's strong subadditivity. | **M–L** | medium: the bridge is external and the `log` bookkeeping in `ℝ≥0∞` is fiddly | medium: "entanglement geometry" at finite dimension, exactly as far as it goes and no further |
| **ST-3** | **The macroscopic-coordinate projection as a structure.** Paper D's `π'`: a measurable map from `Σ` to a finite structure with the record statistics factoring through it, and the two theorems that any instance must satisfy (no-signalling and the chain law survive the projection). Definitional until an instance is named. | **S** for the structure; the instance unpriced | — | low until the author names `π'`; then it is the frame everything else hangs on |
| **ST-4** | **The reading, written down.** The one-sentence form of §6 into `POSITS.md` (as a conjecture, not a posit), `CSD-CHARTER.md` and the narrative page, with the theorem citations of §5 and §6. | **S** | high | high: the programme's spacetime claim exists in the repository at the honesty level of its other claims |

`ST-4` is documentation and can land now. `ST-1` is the one Lean brick that is both honest and new. `ST-2`
is worth doing only if the author wants entanglement geometry as a research direction; it does not feed the
record layer. `ST-3` waits on a decision.

## 8. The finding

There is no Lean shape today for spacetime emerging from records, and the reason is not a missing lemma. The
papers say spacetime arises "after further coarse-graining" through "additional projections", and neither
paper nor charter says which projection. Until the author names it, the corpus can prove things *about* any
candidate (no-signalling and the chain law survive it) but cannot prove that one exists or is forced. That
is a decision, not a theorem, and this note records it as such.

What the corpus does have is the *causal* half, relative to an assumed geometry: bounded influence along a
coupling graph, non-signalling correlations across a cut, and the theorems that any local account is
impossible. Row 39's reading, restated at that level, is a conjecture about whether the cut is emergent, and
it is consistent with everything proved. The one brick worth building now is `ST-1`, which makes the causal
half a statement about records rather than about operators; the one document worth writing now is `ST-4`.

The rest of the programme's spacetime vision, Lorentzian structure, causal cones as geometry rather than
graph balls, curvature, emergent time, is not in reach of a finite compact arena and is deferred exactly as
Paper D defers it. This note is the first place that is written in the repository.

## References

`RecordLayer/{GlobalBasin, GlobalRecordClosure, RecordPersistence, NStepChain, TwoTimeLuders, DrivenTwoTime,
CompositeRecord, EntangledRecord, OnticComposite, CellLawForced}.lean`; `CV/{ModeLocality, DynamicalLocality,
SupportSpreading, LiebRobinson}.lean`; `SigmaLayer/{TensorSector, BellGenerality}.lean`;
`Empirical/QM/Bell.lean`; [`POSITS.md`](POSITS.md) (Posits 1 and 7, and "What frontier means here");
[`csd-departures-eft.md`](csd-departures-eft.md) §3 (finite `N` is not a lattice);
[`sigma-fibre-contextuality.md`](sigma-fibre-contextuality.md); [`qit-chain-scoping.md`](qit-chain-scoping.md)
(the model for this note); [`BACKLOG.md`](BACKLOG.md) rows 38 and 39; Paper D §5.2 and §7.12.
