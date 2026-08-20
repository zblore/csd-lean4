# Necessity audit: how tightly is the substrate pinned down?

Status: COMPLETE (opened and closed 2026-08-09). BACKLOG row: "Necessity audit
of the constraint set". This page is the answer to a question the corpus had
never asked of itself.

## Why this exists

The reconstruction constrains a posited ontic substrate from above: the
substrate is never observed directly, only through what it produces, so
requirements on observed behaviour are requirements on the substrate. That
method is sound, and it is the one the programme uses.

What the corpus did not record is that its results are of **mixed logical
strength**. Some force structure; some only show a posited structure suffices;
some rule structures out; some merely exhibit a witness. Counting theorems does
not measure how much has been achieved, because a hundred sufficiency results
narrow the substrate less than one forcing result. This page classifies every
constraint-bearing headline and then states what the accumulated set actually
pins down.

## The rubric

| Class | Form | What it buys |
|---|---|---|
| **NECESSITY** | The theory must exhibit `X`, therefore the structure must be `Y`. | Narrows the substrate. The strongest class. |
| **CONDITIONAL NECESSITY** | Given posit `P`, exhibiting `X` forces `Y`. | Narrows the substrate *relative to `P`*. Only as strong as `P` is motivated, so `P` must be named. |
| **SUFFICIENCY** | Given structure `Y`, the theory exhibits `X`. | Shows `Y` is *adequate*. Consistent with many other structures also being adequate, so narrows nothing by itself. |
| **IMPOSSIBILITY** | No structure of type `Z` exists. | Narrows by elimination, and transfers to rival theories of the same shape. |
| **INSTANTIATION** | Here is a witness with property `P`. | Establishes consistency and non-vacuity. Forces nothing. |

Two rules used throughout. First, classification is by the **Lean statement**,
not the docstring: where the two disagree the disagreement is itself recorded.
Second, for conditional necessity the posit is named explicitly, since an
unnamed posit is what makes a conditional result read like an unconditional one.

## The declared headlines, classified

`CsdLean4/Headlines.lean` fixes the corpus's own inventory of thirty headline
claims, CL-001 to CL-030, and its drift guard keeps that list honest. Using it
as the spine means the audit cannot be accused of sampling favourably.

| Claim | Constant | Class | Load-bearing posit |
|---|---|---|---|
| CL-001 | `LF1.OnticSetup.TrialModel.main_theorem_ae` | SUFFICIENCY | The `OnticSetup` and `TrialModel` bundles, plus pairwise independence. See the disclosure below on `hΦ_pres`. |
| CL-002 | `LF1.freq_tendsto_of_iid` | SUFFICIENCY | A shared trial law and independence. Law-agnostic; no CSD content. |
| CL-003 | `LF2.OperationalPackage.fromPreparation` | INSTANTIATION | A `def`, not a theorem. |
| CL-004 | `LF2.PurePreparation.born_rank_one_direct` | SUFFICIENCY | The Born value is read off a posited Dirac pushforward. |
| CL-005 | `LF2.OperationalPackage.effect_gleason_representation` | CONDITIONAL NECESSITY | The effect algebra on a given complex `N`-dimensional space, plus the four operational axioms. |
| CL-006 | `LF2.weights_sum_eq_one` | SUFFICIENCY | Normalisation over a posited partition. |
| CL-007 | `LF2.QuantumChannel.cptp_capstone` | SUFFICIENCY | Kraus form posited; forward direction only. |
| CL-008 | `LF3.LF3_main_theorem` | SUFFICIENCY | The `SystemApparatusSetup`. The singlet correlations are computed from it. |
| CL-009 | `LF3.LF3_singlet_frequency_convergence_born` | SUFFICIENCY | The `PureSingletPreparation` bundle, whose `bridge_op_p` field its own docstring flags as the single largest external hypothesis, to be read with the scrutiny of an axiom. |
| CL-010 | `LF4.fs_volume_eq_dirichlet` | SUFFICIENCY | None beyond the definition of the measure. Genuine Duistermaat-Heckman geometry. |
| CL-011 | `LF4.born_frequency_convergence_N` | SUFFICIENCY | The sampling law is posited, and the regions are preparation-indexed. |
| CL-012 | `LF4.fubiniStudy_forced_by_symmetry` | CONDITIONAL NECESSITY | Invariance under the group, and the group `U(N)` itself. |
| CL-013 | `LF4.obsFlow_not_ergodic` | IMPOSSIBILITY | `1 < N`. No flow of this kind selects the typicality measure. |
| CL-014 | `LF4.projectedFlow_eq_unitary_family` | SUFFICIENCY | Per-time unitarity, repackaged by choice. |
| CL-015 | `LF4.projectedFlow_phase_lift` | CONDITIONAL NECESSITY | The cocycle and its coboundary trivialisation, supplied as data. |
| CL-016 | `LF4.manyToOneSetup_born_frequency` | SUFFICIENCY | The constructed setup; trials sample the measure rather than being evolved by the flow. |
| CL-017 | `LF5.measurementFlow_realises_dilation` | SUFFICIENCY | The von Neumann coupling. Content is reindex naturality plus a definitional factorisation. |
| CL-018 | `LF5.measurement_flow_born_frequency` | SUFFICIENCY | The sector posit and i.i.d. sampling, both as hypotheses. Its docstring calls itself assembly. |
| CL-019 | `LF6.decoherence_offdiagonal_vanish` | SUFFICIENCY | The de-isolation map and partial trace. |
| CL-020 | `LF6.no_product_partition_realises_singlet` | IMPOSSIBILITY | Quantifies over any probability space. |
| CL-021 | `LF6.no_product_partition_realises_ghz` | IMPOSSIBILITY | As above, and deterministic rather than statistical. |
| CL-022 | `QuantumInfo.vonNeumannEntropy_subadditive` | CONDITIONAL NECESSITY | The density-matrix formalism. A constraint no state evades. |
| CL-023 | `QuantumInfo.strong_subadditivity_of_relEntropy_monotone` | CONDITIONAL NECESSITY | Data processing, supplied as the explicit `hDPI` premise by design. |
| CL-024 | `Projectivization.wigner_rigidity` | **NECESSITY** | Transition-probability preservation, and nothing else. |
| CL-025 | `RecordLayer.swap_luders_marginal` | SUFFICIENCY | The swap construction and the pre-loaded bank. |
| CL-026 | `RecordLayer.povm_selector_born` | SUFFICIENCY | The arena, the context field, and a Naimark dilation. |
| CL-027 | `RecordLayer.projectiveMeasurementCapstone` | INSTANTIATION | A conjunction of witness closures. |
| CL-028 | `CV.commute_of_disjointSupport` | CONDITIONAL NECESSITY | The mode-product space, and `SupportedOn` as the definition of localisation. |
| CL-029 | `Thermo.vonNeumannEntropy_le_pinching` | CONDITIONAL NECESSITY | The pointer basis, posited rather than selected by any dynamics. |
| CL-030 | `Thermo.landauer_bound` | CONDITIONAL NECESSITY | Gibbs bath, product initial state, global unitary. |

Tally: one necessity, eight conditional necessity, three impossibility, sixteen
sufficiency, two instantiation.

**The corpus's strongest-direction results are mostly not among its declared
headlines.** `Matrix.StoneC1.stone_continuous` (continuity plus the group law
plus unitarity forces `exp(t·A)`, with differentiability derived rather than
assumed) is a second unconditional necessity and is not a ledger row.
`CV.no_exact_finite_ccr`, and the three no-gos in
`SigmaLayer/MeasurementConstraints.lean`, are unconditional impossibilities with
no CSD-specific hypotheses at all, and none of them is a ledger row either. The
ledger is a record of what the programme set out to build, not a ranking by
logical force.

## Findings by layer

### The reconstruction core (LF1, LF3, LF4, staged Mathlib)

The genuinely forcing results are concentrated in the staged-Mathlib layer and
are about representation theory rather than about the substrate. Wigner rigidity
assumes only that a self-map of the projective space preserves transition
probabilities: no linearity, continuity, surjectivity, or dimension bound, and
linearity of the witness is an output. The antiunitary branch is separately
shown non-vacuous and, for `N` at least two, mutually exclusive with the unitary
branch. Stone's theorem in continuity-only form is the second. Both are textbook
"observed feature forces structure" theorems, fully formalised.

Everything that touches physics as observed runs forward. Born weights,
frequency convergence, observable expectations, and both "pillars" capstones all
have the shape: posit the sector, posit that trials are i.i.d. draws from its
measure, obtain quantum behaviour. The measure-uniqueness result is the one
place where a posit is genuinely converted into a theorem, and it is worth
naming as the template for what progress looks like: it replaces "the sampling
law is Fubini-Study" with the weaker and better-motivated "the sampling law is
invariant under the group". The matching negative is proved in the same file:
no single ontic flow forces the measure, since the flow admits other invariant
measures.

Two conditioners appear systematically wherever the corpus says "forced". The
first is the symmetry group `U(N)`, taken as given in every measure-forcing
result. The second is transition-probability preservation, taken as an explicit
hypothesis in every Wigner-selection result on a `KahlerOnticSetup`, and the
docstrings repeatedly note that it does not follow from the structure's
volume-preservation field, because a measure is not a metric. Discharging either
conditioner would convert a large block of conditional necessity into necessity.
That is the highest-value structural target this audit identifies.

**The ontic fields do almost no work.** `LF1.OnticSetup.hΦ_pres`, which is
Liouville's theorem for the ontic flow, is declared and never consumed: only
measurability is extracted from it, and `Setup.lean` discloses this in a
paragraph headed "honest disclosure". Symmetrically,
`KahlerOnticSetup.flow_preserves_volume` enters no Wigner or Schrödinger
conclusion, and `kahler_pointwise` is a proved theorem rather than a hypothesis,
so it constrains nothing about a would-be substrate. The fields that are
load-bearing are `projectable`, `pi`, and `flow`, and only in
`sigmaFlow_schrodinger_form`. The substrate as formalised is doing structural
bookkeeping; the constraints are carried by the symmetry group and by metric
preservation.

The Schrödinger chain is honest conditional necessity throughout. The projected
flow is unitary or antiunitary given transition-probability preservation; the
unitary branch is selected given a Bargmann continuity datum; the Schrödinger
form follows given a cocycle trivialisation (S1) and a C¹ generator datum (S2).
Those last two are large posits, and the modules say so.

### The operational layer (LF2)

This is the tightest link in the reconstruction, and it sits one level above the
substrate. Effect-Gleason forces every operational package to be a trace form
against a unique density operator, from constraints that are independently
motivated. But it takes the effect algebra as given. Gleason-type theorems
derive the state given the algebra; they never derive the algebra, the field, or
the dimension.

### Composite structure

`compositeAlgReconstruction` and its corollary `composite_dim_eq`
(`SigmaLayer/TensorReconstruction.lean`) are the strongest forcing results about
composition in the corpus, and they are not ledger rows. Given *any* joint
matrix algebra carrying two local embeddings that commute (locality) and
generate (local tomography), the joint algebra **is** the tensor product and its
dimension **must** be the product of the local dimensions. The quantification is
over arbitrary embeddings into an arbitrary joint algebra, so this is real
forcing rather than a property of a chosen construction, and it discharges what
was previously the posited B6 dimension field: any composite with commuting,
generating local algebras now gets its tensor dimension derived rather than
assumed.

Classification is CONDITIONAL NECESSITY, and the posit is the setting itself:
the joint system is a finite-dimensional complex matrix algebra. Within that
setting the composition rule is forced; the setting is not derived from
operational principles, so this is not the full general-probabilistic-theory
reconstruction, which is what would be needed to force complex quantum theory
over its rivals.

Worth recording because a stale cross-reference sent this audit looking in the
wrong place: the BACKLOG row that commissioned this page names
`composite_is_tensor_product` as the necessity result. It is not. Its own module
states plainly that it is the sufficiency half, that the necessity converse is
the abstract theorem in `TensorReconstruction.lean`, and that the two must be
read together. The Lean and its docstrings were right; the ledger prose pointing
at them was wrong.

### The measurement and record layer (LF5, LF6, SigmaLayer)

Sufficiency and instantiation dominate decisively. The entire positive
programme, meaning shear, swap, join, phase slot, pointer, null seam, and every
closure bundle up to the projective measurement capstone, has the form: here is
an explicitly constructed propagator on the posited arena, and it exhibits
ready, record, exclusivity, persistence, Liouville, Born, and Lüders behaviour.
These force nothing. Their real value is consistency: they show the posited
arena, plus a context-fixed rate field, plus a calibrated ready state, can carry
all the observed measurement phenomenology at once, including the state-dependent
degenerate Lüders update that the swap architecture provably cannot supply and
the join witness does.

Every Born number in this layer traces back to the moment map being the posited
rate, not to an independent derivation.

The forcing that exists here is by elimination, and it is strong.
`no_everywhere_correlation`, `no_exact_collapse`, and `collapse_accuracy_bound`
have no CSD-specific hypotheses whatever: they are pure topology and pure measure
theory. Together with `posMeasure_noRecord_pointer` they establish a real
trilemma for any record dynamics: give up exact everywhere correlation, or give
up continuity, or pay in a no-record set of positive measure and Dirac
calibration. `swap_luders_iff_calibrated` adds a scoped necessity, that the
Lüders map is calibration-encoded rather than produced by record creation,
although it is an immediate corollary of the marginal identity rather than new
mathematical content. `swap_not_blockLuders` adds a scoped impossibility
quantified over all calibrations. The LF6 no-gos are the cleanest unconditional
exclusions in the corpus, quantifying over any probability space.

### The field layer (CV) and thermodynamics

`no_exact_finite_ccr` is CSD-free and airtight: no finite matrices satisfy the
exact canonical commutation relation. `exists_unitary_compress_not_unitary`
rules out exact unitary matching between cutoffs by witness. These are the only
results in the layer whose force is model-independent.

A large body of conditional necessity follows: the locality and Lieb-Robinson
family, the Duhamel price ladder, power counting, and all four thermodynamic
entropy results. These are real theorems, but the posits are uniform and
substantial. The finite mode-product space; `SupportedOn` as *the* definition of
localisation; drives restricted to stroboscopic diagonal phases or to
free-plus-edge-supported kicks; edge-locality supplied as a hypothesis; the
generator split handed in rather than constructed; and in thermodynamics the
pointer basis, the Gibbs bath, and the product initial state.

The dispersion cluster, boost covariance, the propagator, cutoff stability, and
decimation matching are sufficiency. ~~The direction is never reversed anywhere
in this layer.~~ *(One reversal landed 2026-08-20:
`CV/DispersionEarned.lean` — covariance now IS shown to select the dispersion;
see below.)* Disjoint mode supports yield commuting algebras, but observed
locality is not shown to require the mode-product model. ~~The relativistic
dispersion is boost-covariant, but covariance is not shown to select it.~~
**Superseded 2026-08-20 (P4, `CV/DispersionEarned.lean`)**: covariance selects
it — `cone_symmetry_characterises_omega` proves `ω = √(p² + m²)` **iff** `ω`
has rest energy `m > 0` and its graph is covariant under every ray-preserving
unimodular linear symmetry of the `(E, p)` plane (with the boost form itself
derived from ray preservation, and the mass-gap hypothesis shown sharp by a
massless counterexample). Gibbs
attains the free-energy minimum, but uniqueness of the minimiser is not
extracted, so minimisation is not shown to force the Gibbs form.

### The empirical twins

Three shapes, and none constrains the substrate.

Most `Empirical/CSD/` headlines are **bundle transports**: a structure extending
the bridge context whose extra fields are all Hilbert-side, with the proof
projecting them and applying the quantum-side original. The sector datum is
never consumed, and no bundle field mentions the arena, its measure, or
equivariance. `PLACEHOLDERS.md` §7 to §10 already ledgers this across eighteen
files, and its own summary is the correct verdict: the CSD-side reading of GHZ
and Kochen-Specker is, propositionally, the quantum-side reading. The `no_csd_*`
results are formally impossibility, but since each bundle is a conjunction, the
negative existential follows from the quantum half alone, and the CSD conjunct
can only make it easier.

The `*Volume` files posit an amplitude vector, carve the outcome regions from
that vector's own moment coordinates, and invoke the volume engine. The
mathematics is genuine; the direction is sufficiency.

The one result with real forcing shape is `recordIntact_compl_measure_le`,
quantified over an arbitrary measure-preserving map and an arbitrary state. It
is conditional necessity over a genuine hypothesis class, but what it constrains
is any record dynamics whatsoever, by an ergodic-theory pigeonhole, rather than
this substrate in particular.

## Where the corpus overstates itself

These are disagreements between a docstring and the statement beneath it. The
fix is prose in every case; no Lean is wrong. They are recorded because an
unqualified word in a docstring is exactly how a conditional result comes to
read as an unconditional one.

**Scope caveats that are true but unstated.**

1. **The general-N Born regions are preparation-indexed.** In every general-N
   Born and frequency headline the outcome partition is built from the
   preparation's own moment coordinates, so the regions whose volumes equal the
   Born weights are fixed by the state rather than by a measurement context. The
   headline prose says the thesis is realised end to end for general `N` without
   noting this. The contrast is internal to the corpus and instructive:
   `qubitBorn` *is* context-fixed, its indicator built from the measurement
   direction while the density is built from the state, and its docstring says
   so correctly. This is the known record-layer frontier; the general-N
   headlines should carry the same caveat the qubit case does.
2. **Stern-Gerlach's bundle is an empty extension**, inhabited by any context,
   and its theorem takes it as an unused argument. Self-flagged in file.

**Prose stronger than the statement.**

3. **Dispersion prose treats a definition as a discovery.** The frequency is
   defined as the square root of momentum squared plus mass squared, and both
   headline identities are one line of algebra from that definition. Neither
   statement mentions propagation or speed.
4. **Unearned "must" in the cutoff prose.** `CutoffStability.lean` says graded
   interactions must be renormalised by the power `PowerCounting.lean` computes.
   That module proves an upper bound with no lower bound, so nothing forces
   renormalisation, and its own scope note concedes this while a neighbouring
   bullet still calls the cost exact. The two files disagree.
5. **The Lieb-Robinson velocity gloss.** The decay parameter is the norm of the
   whole generator, extensive in the number of edges for a local Hamiltonian, so
   the quoted time is not a system-size-independent velocity. The scope note says
   no velocity constant is extracted; the body still asserts a speed bound.
6. **Decimation's no-go is existential, its prose universal.** One witness at
   three modes to two, described as showing the effective dynamics is necessarily
   open.
7. **Einselection claims a uniqueness the Lean does not carry.** The prose says
   the pointer basis is the one basis in which the decohered state is diagonal.
   The Lean excludes the Hadamard rotation, for a qubit. There is no quantifier
   over bases.
8. **`shear_base_marginal_unchanged` is cited as a no-go**, including from a
   closure bundle and the axiom audit. The statement is a positive identity
   between two pushforwards, closed by a rewrite and `rfl`. The docstring is
   careful that *this* witness cannot supply Lüders, but its further claim that
   the tension is structural is an interpretation, not a theorem about a class of
   dynamics.
9. **`selection_is_record` is definitional.** The outcome function and the basin
   are built from the same data, so the equivalence is a repackaging rather than
   evidence that a record layer emerged.
10. **The smooth witness's "Born" is an epsilon-sandwich**, not an equality, and
    the capstone exposes it existentially.
11. **`manyToOneSchrodingerSetup_schrodinger_form` is `fun _ _ => rfl`**, true by
    construction of a setup whose flow is defined as the evolution in question.
    The docstring says "by construction", but the word "delivered" in headline
    position invites a stronger reading.
12. **Landauer's statement is broader than its prose.** There is no positivity
    hypothesis on the inverse temperature in `landauer_bound` or `bath_clausius`,
    and the relative-entropy proof never uses a sign. Separately,
    `landauer_one_bit` assumes both entropy values rather than deriving them, and
    no witness shows they are jointly satisfiable, so the corollary is not shown
    non-vacuous in file.

**Prose weaker than the statement, or stale.**

13. **"SU(N)" claimed, U(N) proved, systematically.** Section headers, theorem
    docstrings, and keyword lines across the Fubini-Study modules say `SU(N)`;
    every corresponding statement quantifies over the unitary group. Because the
    centre acts trivially on the projective space the two invariance conditions
    coincide there, so the docstring's mathematical claim is true, but the Lean
    theorem read literally assumes invariance under the larger group and is
    formally the weaker statement. Anyone citing "the SU(N)-invariant measure is
    unique" from these names is citing something the files do not state.
    **Fixed at source 2026-08-20** (surfaced independently by the author's
    definitional-precision review — this item had recorded the defect without
    queueing the fix): all module docstrings, section headers, and keyword
    lines across `FubiniStudy.lean`, `FubiniStudyUnique.lean`, `Unitary.lean`,
    `UnitaryCompact.lean`, `UnitaryHaar.lean`, `LF4/Instance.lean`, and
    `LF2/Setup.lean` now say `U(N)`, matching the quantifier, with the
    centre-acts-trivially equivalence recorded once in `FubiniStudy.lean`'s
    header; the glossary's TN1 note updated. Paper-B attributions ("SU(n)-fixed
    μ_FS") are left as the papers' own wording, which the equivalence makes
    correct.
14. **Two stale "open target" notes.** `WignerRigidity.lean` describes Wigner
    rigidity as a deferred, unproved target in its header and in a definition
    docstring, while proving it later in the same file;
    `TransitionProbability.lean` carries a section headed "open target (not
    proved here)" and predicts that Kähler structure will select the unitary
    branch, whereas the delivered proof selects neither branch and separates them
    with the Bargmann invariant instead.
15. **`TypicalityForcing.lean` is named for what its own headline disclaims**,
    the headline docstring opening by saying it is a measure characterisation and
    not the typicality forcing. A trap for anyone browsing by filename.

Set against these, a large number of docstrings are exemplary and were already
flagging the very gaps this audit looks for: `ApproxCCR`, `ModeLocality`,
`CanonicalTypicality`, `SecondLaw`, `InteractionPrice`, `RecordSemantics`,
`csdFiniteQMClosure`, `born_form_of_package` conceding a vacuous hypothesis, the
two `globalBasin` results, `OnticBorn`, `UnitarySelection`, and LF1's own
disclosure that its Liouville field is unused. Several of the overstatements
above had already been caught and annotated by the corpus's earlier audits. The
`DuistermaatHeckman` tombstone is genuine: the fact it once axiomatised is now a
proved theorem, generalised to all `N`.

## What the constraint set pins down

**Not the substrate, and nothing in the corpus claims otherwise once the
statements rather than the docstrings are read.** No theorem forces the arena.
Every Born-valued result traces its numerical content either to the moment map
being the posited rate, or to regions carved from the preparation's own moment
coordinates. The two structural fields one would expect to carry the
constraining work, Liouville preservation in LF1 and volume preservation in the
Kähler setup, are declared and never consumed.

**What is pinned, and pinned tightly, is the layer just above the substrate.**
Given only that a map preserves transition probabilities, it must be unitary or
antiunitary. Given continuity and the group law, evolution must be exponential
in a skew-Hermitian generator. Given the effect algebra and the operational
axioms, probability assignments must be trace forms. Given local algebras that
commute and generate, the composite must be the tensor product and its dimension
the product. These are genuine forcing results with independently motivated
hypotheses, and together they cover symmetry, dynamics, probability, and
composition, which is most of the structural content of quantum mechanics. They
all take the complex Hilbert space or matrix algebra as given, so the
reconstruction's tightest links start one level above the substrate and do not
reach down to it.

**Below that sits a price list, and it is real.** No finite system realises the
exact canonical commutation relation. No continuous propagator achieves exact
everywhere correlation. No measure-preserving map implements exact collapse.
Collapse accuracy is bought with ready-state improbability. No setting-local
partition of any probability space reproduces the singlet or GHZ correlations.
No unitary flow selects the typicality measure. These have few or no
CSD-specific hypotheses, so they transfer to rival theories of the same shape,
and because the substrate is seen only through what it produces, they are
constraints on the fabric in the legitimate inward direction rather than mere
scope notes.

**So the answer to the question this audit asked: the accumulated constraint set
pins the substrate down up to a large family, not uniquely, and the family is
bounded more by the exclusions than by the positive results.** The positive body
of work establishes that the posited arena is *adequate*, which is a
demonstrated-consistency result of considerable size and internal coherence, and
is not nothing: it is what makes the programme a candidate reconstruction rather
than a sketch. But adequacy is not selection. Between the representation-layer
forcing above and the no-go price list below sits a large collection of
witnesses showing the bracket is inhabited, and inhabitation does not force.

The practical use of this classification is that it says which additions would
actually narrow the space, as opposed to lengthening the theorem count. Two
kinds. First, results that run from an observed feature to a structural
requirement, in the shape Wigner rigidity already has. Second, discharge of one
of the two systematic conditioners: the symmetry group taken as given in every
measure-forcing result, and transition-probability preservation taken as a
hypothesis in every Wigner-selection result. The measure-uniqueness theorem is
the template, because it converted "the law is Fubini-Study" into the weaker
"the law is invariant under the group". Another conversion of that kind is worth
more than any number of further witnesses.

## Addendum 2026-08-13 — the extended census (Q17), and the Q18 premise conversion

The body above audited the ledger as it stood on 2026-08-09: thirty rows. Two
things have changed since, and this addendum brings the classification current
without rewriting the dated body.

### The rows the audit had not seen, classified by the same rubric

CL-031 (added 2026-08-10) and the twenty-row census extension CL-032 to CL-051
(added 2026-08-13 under the admission criteria now stated in
`VALIDATION-LEDGER.md`):

| Claim | Constant | Class | Load-bearing posit |
|---|---|---|---|
| CL-031 | `LF6.no_compatible_global_chsh_assignment_realises_singlet` | IMPOSSIBILITY | The shared-domain C1 posits; four CHSH settings only. |
| CL-032 | `Matrix.StoneC1.stone_continuous` | **NECESSITY** | Continuity, the group law, unitarity — differentiability derived. The body already named it the second unconditional necessity; it is now a row. |
| CL-033 | `CV.no_exact_finite_ccr` | IMPOSSIBILITY | Finite dimension only. CSD-free. |
| CL-034 | `RecordLayer.no_everywhere_correlation` | IMPOSSIBILITY | Continuity and connectedness only. Pure topology. |
| CL-035 | `RecordLayer.no_exact_collapse` | IMPOSSIBILITY | Measure preservation only. Pure measure theory. |
| CL-036 | `RecordLayer.collapse_accuracy_bound` | IMPOSSIBILITY | As CL-035; the quantitative price. |
| CL-037 | `SigmaLayer.compositeAlgReconstruction` | CONDITIONAL NECESSITY | The finite-dimensional complex matrix-algebra setting; commuting + generating embeddings. Classified in the body's composite section; now a row. |
| CL-038 | `RecordLayer.posMeasure_noRecord_pointer` | IMPOSSIBILITY | Scoped to the pointer arena — the trilemma's third leg with no geometric hypothesis left. |
| CL-039 | `LF4.qubitBorn` | SUFFICIENCY | Context-fixed hemispheres, spread density, FS typicality. The A7-faithful qubit case the body's first scope finding holds up as the model. |
| CL-040 | `Empirical.QuantumChaos.deficitKick_record_halfLife` | CONDITIONAL NECESSITY | The triggered-kick hypothesis class; constrains every drive in it (the `recordIntact` precedent). |
| CL-041 | `Empirical.QuantumChaos.deficitKick_phaseFlip_halfLife` | SUFFICIENCY | The phase-flip witness; the DH law computes the rate exactly. |
| CL-042 | `Empirical.QuantumChaos.ledgerEntropy_le` | CONDITIONAL NECESSITY | The register/carrier model; carrier antitonicity; below half-filling. |
| CL-043 | `Empirical.QM.QEC.shor_corrects_Z_degenerate` | SUFFICIENCY | The Shor-9 construction. |
| CL-044 | `LF6.lindbladSemigroup_hasDerivAt` | SUFFICIENCY | An arbitrary GKSL generator; CP of the exponential not claimed. |
| CL-045 | `CV.norm_commutator_velocity_le` | CONDITIONAL NECESSITY | The mode-product space and `SupportedOn`, as CL-028. |
| CL-046 | `CV.vacuum_clustering` | SUFFICIENCY | The cutoff model; forward computation. |
| CL-047 | `RecordLayer.nullSeamGenClosure` | INSTANTIATION | The third horn inhabited at every `N` — a witness closure, and honest about it. |
| CL-048 | `RecordLayer.recordKernel_eq_transProb` | SUFFICIENCY | None beyond the record-layer definitions. Its force is indirect: it is the premise-conversion enabler (below). |
| CL-049 | `RecordLayer.measure_eq_fubiniStudy_of_record_statistics_invariant` | CONDITIONAL NECESSITY | Invariance under every record-statistics-preserving symmetry — the indifference premise; the group is not named. |
| CL-050 | `RecordLayer.povm_sector_born` | SUFFICIENCY | The join arena, context field, Naimark dilation — the dynamical statement CL-026 was once over-read as. |
| CL-051 | `RecordLayer.pointer_luders_born_prep` | SUFFICIENCY | The pointer arena and calibrated bank; `2ε < rate i` makes the conditioning non-vacuous. |
| CL-052 | `LF6.c1_singlet_contextual_capstone` | INSTANTIATION | The concrete arena `(KSigma 4, kMuPsi)` and the explicit arc model. Added 2026-08-13 (Q19, author sign-off same day): the existence half CL-031 lacked, with CL-031's impossibility applied to the witness as its fourth conjunct — so the row carries the two-sided C1 separation, but its *own* logical force is the witness (the obstruction's force is CL-031's row). |

**Updated tally over the 52-row ledger: two necessity, thirteen conditional
necessity, nine impossibility, twenty-four sufficiency, four instantiation.**
The body's headline sentence — "the corpus's strongest-direction results are
mostly not among its declared headlines" — is now discharged: they are.

### The Q18 premise conversion — re-annotation, not re-classification

`RecordLayer/StatisticsRigidity.lean` (Q18, 2026-08-13) proved the kernel
identification (CL-048): the record layer's operational pairwise statistic IS
the transition probability, so *"preserves record statistics"* and *"preserves
the FS metric"* are the same predicate
(`recordStatisticsPreserving_iff_transProbPreserving`). Consequences for the
body's classifications:

* **CL-012** (`fubiniStudy_forced_by_symmetry`): stays CONDITIONAL NECESSITY,
  but the load-bearing posit has a proven conversion — via CL-049 the premise
  "invariance under the group, and the group `U(N)` itself" weakens to
  "invariance under every record-statistics-preserving symmetry", with `U(N)`
  never named and the group pinned semi-unitary by Wigner
  (`recordStatisticsPreserving_realisation`).
* **The Schrödinger chain** (CL-014/CL-015 and every Wigner-selection result on
  a `KahlerOnticSetup`): stays honest conditional necessity, but the `hTPP`
  conditioner is no longer only the geometric FS-isometry posit — it is
  consumable as the operational premise "the projected flow preserves observed
  record statistics" (`projectedFlow_unitary_of_record_statistics`), which is
  what a symmetry means operationally.
* **What did NOT change:** these are premise *conversions*, not eliminations —
  the operational premises survive as posits whose physical motivation the
  papers owe; nothing derives TPP from measure preservation (the §13.2 trap
  stands); and D1 (`G`-from-dynamics) remains open and obstructed. The body's
  closing recommendation — "another conversion of that kind is worth more than
  any number of further witnesses" — has now been executed once, in exactly the
  template it named (`specs/unitary-tpp-scoping.md`).

## References

`CsdLean4/Headlines.lean` (the claim inventory and its drift guard — thirty
rows at the body's review date, fifty-one after the 2026-08-13 census);
`specs/VALIDATION-LEDGER.md` and `specs/validation-claims.tsv` (the ledger rows
classified above, including the admission criteria added 2026-08-13);
`specs/unitary-tpp-scoping.md` (the Q11 scoping the addendum's conversion
section executes); `PLACEHOLDERS.md` §7 to §10 (the transport-only empirical
bundles); `specs/sigma-fibre-contextuality.md` (why the fibre is load-bearing);
`specs/reconstruction-status.md`; `specs/future-work.md` and `specs/BACKLOG.md`
(the open queue, including the record-layer frontier this audit's first scope
finding restates).
