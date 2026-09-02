# Q11 scoping: discharging the `U(N)` / `hTPP` conditioners (the conditionality gap)

Status: SCOPING SESSION, opened and closed 2026-08-13. BACKLOG row: **Q11**
("U(N) / hTPP discharge — the conditionality gap"). Deliverable: this map plus a
named first brick — **no theorems in this document**. Commissioned by the
necessity audit ([`necessity-audit.md`](necessity-audit.md)), whose closing
paragraph is the brief: *"discharge of one of the two systematic conditioners …
is worth more than any number of further witnesses."*

## 1. The gap, restated precisely

The necessity audit found two conditioners appearing systematically wherever the
corpus says "forced". Both have exact Lean locations:

| Conditioner | Where it enters | Guarded scope note already in file |
|---|---|---|
| **`hTPP`** — `∀ t, TransProbPreserving (d.projectedFlow t)` | `LF4/UnitarySelection.lean` (W3), consumed by `LF4/BargmannSelection.lean`; hypothesis of every Wigner-selection result on a `KahlerOnticSetup` | "It is NOT derived from `flow_preserves_volume`; deriving it would be the exact §13.2 trap" (measure ≠ metric) |
| **`G = U(N)`** — invariance under the unitary group | `fubiniStudy_forced_by_symmetry` (`LF4/TypicalityForcing.lean`), restating `fubiniStudyMeasure_unique`; taken as given in every measure-forcing result (`IsForcedKahlerVolume`, KG-1) | "the residual SO-1 primitive [is pinned] to `G` itself … `G`-from-dynamics is exactly D1, the deepest open CSD content" |

**What "discharge" means here, and what it must not mean.** The template is the
measure-uniqueness theorem itself, which the audit names as what progress looks
like: it converted *"the sampling law is Fubini–Study"* into the weaker,
better-motivated *"the sampling law is invariant under the group"*. A discharge
of the same kind is a **premise conversion**: replace a named-structure posit
with an operational premise whose motivation does not presuppose the structure.
It is *not* elimination — some premise survives, and this document says which.
Charter check ([`CSD-CHARTER.md`](CSD-CHARTER.md)): this is **constraining Σ
from above** — from what the epistemic projection must do — which the charter
marks as legitimate, valuable work; it is not the retired "derive Σ"
non-question, and it does not touch the §13.2 trap (nothing below derives
anything from measure preservation).

**Why this is not QIT territory** (the BACKLOG row's caveat, kept): a QIT
library *assumes* unitary dynamics and the tensor product and builds upward.
Both targets here sit *beneath* that floor — they are about why the sector's
symmetries are (projectively) unitary and why the sampling law is the invariant
one. No external QIT provider can supply them.

## 2. The Σ-primitives available as Lean surfaces

What a re-grounding is allowed to consume. All of these exist and are pinned:

| Primitive | Lean surface |
|---|---|
| Records in an **arbitrary** measurement context, with outcome rate `‖⟨bᵢ, ψ⟩‖²` | `RecordLayer/BasisMeasurement.lean` — `bornRateBasis`, `bornRateBasis_eq_inner_sq`, `bornMeasurementBasis_prob` |
| Frequencies → volumes (typicality is the LLN, nothing else) | `LF1.freq_tendsto_of_iid`, `LF1_main_theorem_ae` |
| The deterministic, continuous, projectable sector flow | `KahlerOnticSetup` fields `flow`, `projectable`, `pi` (the audit: the load-bearing fields) |
| Transition-probability preservation ⇒ semi-unitary, **and nothing else assumed** | `Projectivization.wigner_rigidity_unitaryGroup` (CL-024, the ledger's one unconditional necessity) |
| Branch selection from a continuity datum | `projectedFlow_unitary_of_bargmann_continuous` (`LF4/BargmannSelection.lean`) |
| Continuity + group law ⇒ `exp(t·A)` | `Matrix.StoneC1.stone_continuous` |
| The unique `U(N)`-invariant law is FS | `fubiniStudyMeasure_unique` (Phase G4) |
| Commuting + generating local algebras ⇒ tensor, dimension forced | `compositeAlgReconstruction`, `composite_dim_eq` (`SigmaLayer/TensorReconstruction.lean`) |
| Effect algebra + operational axioms ⇒ trace form, unique ρ | `OperationalPackage.effect_gleason_representation` (`LF2/EffectGleason.lean`) |

The load-bearing observation for everything below: **the record layer's
statistics are the corpus's only observables.** Everything the epistemic level
sees of Σ is a record frequency; the LLN says those frequencies are measure
volumes. So "operational" has an exact internal referent here — *statable in
terms of `bornRateBasis` and the record machinery* — and re-grounding means
rewriting a geometric hypothesis in that vocabulary.

## 3. The three derivation shapes, mapped

The row asks which operational-reconstruction shapes survive re-grounding in
Σ-primitives. Assessed at shape level against §2; vault dossiers:
`Foundations Landscape/Lucien Hardy.md`, `Giulio Chiribella.md`,
`Markus Müller.md`, `Thomas Galley.md`, `Adrian Kent.md`, and
`CSD - Intellectual Neighbours & Prior Art.md`.

### 3.1 Hardy 2001 (five reasonable axioms) — **survives, as the minimal-scope programme**

Hardy's shape: states are probability lists; `K` (degrees of freedom) vs `N`
(distinguishable states); the classical/quantum fork is decided by his fifth
axiom — *continuous reversible transformations between pure states* — which the
vault note already identifies as "CSD's SU(n) assumption in operational
clothing". Axiom by axiom against Σ:

| Hardy axiom | Fate under re-grounding |
|---|---|
| Probabilities (frequencies converge) | **Already a theorem, stronger than his axiom.** LF1's LLN + typicality: convergence is derived from i.i.d. ignorance over `Ω₀`, not posited. |
| Simplicity (`K` minimal in `N`) | **Does not survive — and is not needed.** A theory-selection meta-principle with no Σ-referent. At minimal scope the sector's dimension is part of the floor; simplicity's job (selecting `K = N²`) has no work left to do. |
| Subspaces | Supplied by the projective-sector structure itself at minimal scope. Becomes live only at maximal scope (§3.4). |
| Composites (`N = N_A N_B`, `K = K_A K_B`) | **Already landed as conditional necessity.** `compositeAlgReconstruction` + `composite_dim_eq`: commuting + generating local algebras force the tensor product and the product dimension. Re-grounding residue: motivate *generation* (local tomography) from records — **CLOSED 2026-09-02** (brick 2, `SigmaLayer/TensorTomography.lean` `recordLocallyTomographic_iff_adjoin_eq_top`: generation ⟺ record-level local tomography, both directions; [`generation-from-records-scoping.md`](generation-from-records-scoping.md)) — closed as a premise conversion: restated in record vocabulary, not motivated or derived from records. The posit itself survives as boundary `R-017`. |
| Continuous reversibility | **Survives best — it is Σ's native structure, not an operational posit.** The deterministic, continuous, Liouville-preserving flow *is* continuous reversibility; Hardy has to postulate what the substrate supplies. The derivation chain from it is already built (Wigner → Bargmann → Stone); the single missing link is why the *projected* flow preserves statistics — which is exactly the `hTPP` gap. |

**Verdict: Hardy's is the shape to run.** His axioms partition cleanly into:
already-theorems (probabilities), Σ-native structure (continuous reversibility),
already-landed (composites), and non-questions at this scope (simplicity,
subspaces). What remains of his fifth axiom after the substrate absorbs the
reversibility half is precisely the statistics-preservation premise of §4.

### 3.2 Chiribella–D'Ariano–Perinotti 2011 (informational axioms) — **the grammar does not survive**

CDP's shape: a process-theoretic circuit framework (causality, perfect
distinguishability, ideal compression, local discriminability, pure
conditioning) with **purification** as the load-bearing postulate. Assessment:

* **Ontology-free by design.** The framework has no substrate to re-ground
  *into* — the vault's positioning line ("a reconstruction with no substrate
  leaves the measurement problem untouched") is also the technical obstruction:
  re-grounding CDP means first formalising the operational circuit category
  over Σ, a framework tax with no Σ-payoff at either scope.
* **Purification is theorem-shaped in CSD, not primitive.** Mixedness is
  epistemic (ignorance over `Ω₀`); the dilation content already lives downstream
  of the sector, forward direction (`measurementFlow_realises_dilation`, the
  Naimark input of `povm_selector_born`). Taking purification as an axiom would
  *invert* the corpus's actual derivation order.
* **Causality** presupposes the operational composition structure that Σ's
  single deterministic trajectory already fixes; as a premise it has nothing to
  bite on.

**Verdict: harvest and decline.** The one CDP fragment worth having — local
discriminability — is already consumed as the generation hypothesis of
`TensorReconstruction`. Cite for positioning; do not build the framework.

### 3.3 Masanes–Müller 2011, and MGM 2019 — **the requirement style survives; the lever does not (at this scope)**

MM's shape: physical requirements (finite capacity, local tomography, subspace
equivalence, continuous reversibility with the transformation group acting
**transitively** on pure states), with the heavy lifting done by group theory:
a compact connected group transitive on pure states, plus the other
requirements, forces `PU(N)` by representation-theoretic classification.

* **The lever targets the maximal scope.** MM need the group classification
  because they do not yet have the state space. At minimal scope the sector *is*
  `ℂℙ^{N-1}` (the floor), and `wigner_rigidity_unitaryGroup` replaces the
  entire Lie-theoretic apparatus: once statistics-preservation is grounded, the
  group is forced to be semi-unitary with **no** transitivity requirement, no
  compactness datum, and no classification. Transitivity, if ever wanted, is
  preparability (every ray admits an `Ω₀`) — a Σ-primitive, not an axiom.
* **MGM 2019** (measurement postulates operationally redundant) is live-disputed
  — Kent 2025 counterexamples, MGM reply narrowing the claim — and CSD does not
  need it: the record layer derives the measurement account dynamically
  (`bornMeasurementBasis_prob`, the Lüders tranche). Nothing below relies on any
  disputed MGM step. Cite MGM **together with Kent** per the vault's must-cite
  discipline; build on neither.
* **What genuinely survives is the requirement style** — premises phrased as
  physical invariances rather than named structures. That is the same template
  the necessity audit endorses, and §4 is written in it.

### 3.4 The maximal scope, named and deferred

The full GPT-style reconstruction — force the *complex projective sector
itself* (field, dimension law, state-space geometry) from record-primitives;
what the audit's composite section says would be needed to "force complex
quantum theory over its rivals". Charter-compliant (constraint from above), and
the only reading where Hardy's simplicity/subspaces and MM's classification
lever become load-bearing. But it requires a GPT state-space formalisation that
neither Mathlib nor the corpus has, on top of the record layer. **Research/XL;
not the Q11 deliverable.** Recorded as the horizon so the minimal scope is not
mistaken for it. If it is ever opened, it is a new queue decision.

## 4. The reduction: both conditioners are one record-level premise

Both conditioners are statements about **which self-maps of the sector the
theory treats as symmetries** — `hTPP` says the dynamics are FS-isometries; the
measure premise says the sampling law is invariant under a named group of them.
The re-grounding move, in one sentence:

> **Transition probabilities are record observables** — `transProb p q` is the
> Born rate that any context containing `q` assigns to the preparation `p` —
> so *"preserves the FS metric"* (geometry) and *"preserves the record layer's
> observable statistics"* (operational) are the **same predicate**, and both
> conditioners convert:

1. **`hTPP` converts.** Define `RecordStatisticsPreserving f`: `f` preserves
   the record-statistics kernel (the context-assigned outcome rates, §5). The
   kernel-identification theorem gives
   `RecordStatisticsPreserving f ↔ TransProbPreserving f`. W3 and the Bargmann
   selection then consume the record-level premise verbatim. Status change in
   the necessity ledger: the Schrödinger chain's conditioner is no longer the
   geometric posit "the projected flow is an FS-isometry" but the operational
   posit "the projected flow preserves observed record statistics" — the
   premise a symmetry *means* operationally, and (for the dynamics) the shape
   of time-translation invariance of the record machinery.
2. **`U(N)` converts — the group becomes an output.** Replace *"the sampling
   law is `U(N)`-invariant"* with *"the sampling law is invariant under every
   record-statistics-preserving symmetry"* — epistemic indifference: the
   preparation machinery cannot weight sector configurations that **no record
   statistics distinguish**. Unitaries are statistics-preserving
   (`transProbPreserving_unitary` + the iff), so `fubiniStudyMeasure_unique`
   fires with `U(N)` never named in the premise; and Wigner closes the loop in
   the other direction — the operationally-defined symmetry group *is* the
   semi-unitary group, as a theorem rather than a choice of `G`.

**Not the §13.2 trap.** Nothing here derives TPP from `flow_preserves_volume`.
The new premise is *statistics* preservation — logically independent of
Liouville (a measure-preserving map need not preserve any context's rates), and
strictly stronger where it overlaps. The trap note in `UnitarySelection.lean`
stays exactly as written.

**The honesty clause (what survives as posit).** This is premise conversion in
the `fubiniStudy_forced_by_symmetry` template, not elimination. What remains:
(i) for the dynamics, *why the projected flow preserves record statistics* — the
operational symmetry premise, whose physical motivation (autonomy of Σ's flow +
time-translation invariance of the record machinery; ultimately the joint-arena
covariance the A1/A2 stroke work formalises) is owed by the papers, not by
Lean; (ii) for the measure, the indifference principle itself. Both are
*better-motivated* than the structures they replace — that is the entire claim,
and it is the same kind of claim the audit's template result makes. D1 proper
(`G`-from-*dynamics*) stays open and stays blocked: `obsFlow_not_uniquely_ergodic`
/ `obsFlow_continuum_invariant` show the single-flow route cannot force the
measure, and nothing here reopens it — the operational route **sidesteps** the
dynamics route rather than repairing it.

## 5. The first brick, named

**`CsdLean4/RecordLayer/StatisticsRigidity.lean`** — category 7 (the record
layer), importing `RecordLayer.BasisMeasurement` and the staged
`Projectivization.TransitionProbability` / `WignerRigidity`; the W3 wrappers may
split into a small second module if import direction demands (RecordLayer
already sits above LF1/LF4, so no cycle either way). Contents, in landing
order:

1. `exists_context_extending_ray` — every ray is an outcome of some context:
   any unit representative extends to an orthonormal basis of
   `EuclideanSpace ℂ (Fin N)` with the representative at a chosen index.
   Tool verified present: `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`
   (Mathlib `Analysis/InnerProductSpace/PiL2.lean`). No wall.
2. `recordKernel` — the operational pairwise statistic: the Born rate a context
   containing `q` assigns to `p`, defined **through the record machinery**
   (choice of extending context), with `recordKernel_well_defined` — any two
   contexts sharing the outcome ray assign the same rate. The definition never
   mentions the inner product.
3. ★★ `recordKernel_eq_transProb` — **the kernel identification**: the record
   layer's pairwise statistic *is* the transition probability. Route:
   `bornRateBasis_eq_inner_sq` + `transProb_mk` + conjugate symmetry of the
   inner product. This is the brick's headline: transition probabilities are
   observables of the record layer, as a theorem.
4. `RecordStatisticsPreserving` (def) + ★ `recordStatisticsPreserving_iff_transProbPreserving`
   — immediate from 3; stated as an iff so the operational symmetry group is
   *identified with*, not merely included in, the TPP maps.
5. ★ `projectedFlow_unitary_of_record_statistics` — W3 + Bargmann re-stated
   with the record-level premise (thin wrapper over
   `projectedFlow_unitary_of_bargmann_continuous`; labelled honestly as a
   premise conversion in its docstring).
6. ★★ `measure_eq_fubiniStudy_of_record_statistics_invariant` — any probability
   measure invariant under every `RecordStatisticsPreserving` map is
   `fubiniStudyMeasure`. Route: `transProbPreserving_unitary` + the iff +
   `fubiniStudyMeasure_unique`. `U(N)` appears in the proof, never in the
   statement — the conversion the audit asked for.
7. (If cheap) the converse inclusion making the symmetry group an exact
   theorem: every `RecordStatisticsPreserving` map is realised by a unitary or
   antiunitary (`wigner_rigidity_unitaryGroup` through the iff), and FS is
   invariant under all of them — the unitary half exists; the antiunitary half
   needs `conjProj` FS-invariance. If that lemma is missing, scope-note it and
   land forward-only; the discharge (items 5–6) does not need it.

**Sizing: M, one tranche.** Walls checked per the check-impossible-first rule:
the ONB extension exists; the identification is algebra over landed lemmas; no
parity/dimension obstruction. Forecast snags are the known module-system
defeq class around `Projectivization.rep`/`mk` (use `transProb_mk`, `show`-typed
goals, no `set`-binding of representatives — the B5-geom notes apply verbatim).
Pins go in the audit part matching `CSD.RecordLayer` (G9 classifier keys on
namespace). **Q17 pairing:** items 3 and 6 are headline-grade and must enter the
extended validation ledger under whatever admission criteria Q17 fixes; the
necessity audit's CL-012 row and Schrödinger-chain classifications should be
re-annotated (posit renamed, not removed) in the same stroke.

## 6. What this scoping does NOT claim

* No theorem is claimed proved by this document.
* **D1 stays open.** `G`-from-dynamics is untouched; the single-flow
  obstruction stands; the operational route replaces the question's premises,
  not its dynamics-side answer.
* **No elimination of posits** — two named operational premises survive (§4,
  honesty clause), and the papers owe their motivation arguments.
* **The maximal scope stays closed** (§3.4) pending a deliberate queue decision.
* Nothing here relies on MGM's disputed redundancy step, and nothing weakens
  the corpus's existing guards (`measure ≠ metric` stays; the §13.2 trap note
  stays; `SU(N)`-vs-`U(N)` docstring discipline from the audit's finding 13
  applies to any new prose).
* Neighbour discipline when this reaches the papers: MGM **with** Kent; Hardy's
  fifth axiom named as the absorbed posit; and the records-based Born
  derivation of Axelsson (arXiv 2604.07418) is a must-cite for any
  "statistics-from-records" framing (vault: `CSD - Intellectual Neighbours &
  Prior Art.md`).

## 7. Sequencing

1. **Brick 1** (`RecordLayer/StatisticsRigidity.lean`, §5) — M, next tranche.
2. **Ledger stroke** — re-annotate CL-012 and the Wigner/Schrödinger-chain rows;
   feed the two ★★ into Q17's extended census (pairs naturally with that
   session).
3. **Decide brick 2** — generation-from-records (local tomography motivated by
   the record layer, closing the composites residue of §3.1) — only after 1–2.
   **Decided "go" and LANDED 2026-09-02** as a premise conversion (restated in
   record vocabulary, not motivated or derived from records):
   `SigmaLayer/TensorTomography.lean` (`recordLocallyTomographic_iff_adjoin_eq_top`),
   scoped in [`generation-from-records-scoping.md`](generation-from-records-scoping.md).
4. **Maximal scope** — a new queue row if ever opened; not implied by 1–3.

## References

[`necessity-audit.md`](necessity-audit.md) (the commissioning finding: the two
conditioners, the conversion template); [`CSD-CHARTER.md`](CSD-CHARTER.md)
(constrain-from-above legitimacy); [`future-work.md`](future-work.md) (SO-1
retired; KG-1 `IsForcedKahlerVolume`; W-3; SL-3's §13.2 caveat; D1c rows);
[`BACKLOG.md`](BACKLOG.md) rows Q11/Q17. Lean surfaces:
`LF4/UnitarySelection.lean`, `LF4/BargmannSelection.lean`,
`LF4/TypicalityForcing.lean`, `RecordLayer/BasisMeasurement.lean`,
`Mathlib/LinearAlgebra/Projectivization/TransitionProbability.lean` /
`WignerRigidity.lean` / `FubiniStudyUnique.lean`,
`SigmaLayer/TensorReconstruction.lean`, `LF2/EffectGleason.lean`,
`Matrix/StoneC1`. Vault: `50 Constraint-Surface Dynamics/CSD - Intellectual
Neighbours & Prior Art.md` and the `Foundations Landscape/` dossiers (Hardy,
Chiribella, Müller, Galley, Kent).
