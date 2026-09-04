# Local Friendliness: scoping note

**Status:** SCOPED, `csd-foundations`-checked (14 findings folded), **BUILT and LANDED
2026-09-04**. Expert-review row **C** of `specs/BACKLOG.md` (M), twins-board row **D12**
(`qm-empirical-tests.md` §3.3).

**As landed:** `Empirical/CSD/LocalFriendliness.lean` — `FriendRecords`, `Persistent`,
`JointLawInvariant`, ★ `jointLawInvariant_of_persistent`, ★★ `not_persistent_of_jointLaw_moves`,
★ `movingRecords_not_persistent`. Three audit pins.

⚠️ **§4's deliverable was wrong and is superseded.** The `RemoteJointInvariantA` proposed there
quantifies over A's *own* setting while tracking A's *own* outcome, so it demands that A's outcome
distribution be independent of A's setting — **no measurement model satisfies it**, and both
"ordering" theorems would have been vacuous. Machine-checked with a counterexample before building.
The deeper reason: LF's `p(a₁b₁|xy) = p(a₁b₁)` is about the **friends'** outcomes, and the
two-wing vocabulary has no friends, so (iii) has no faithful formulation in it. The brick adds the
friend's reading as an object and states the assumption LF uses tacitly — **persistence** — which
is what CSD denies. See §4a.

Breadth / hardening, not reconstruction path — same standing as row B (Ozawa), and the same
discipline: the twin must not read as though CSD explained anything.

⚠️ **Two things to read before any Lean.** §2: three different statements are all called
"locality" here, the corpus proves one *conditionally*, denies another, and Local Friendliness is
about a **third** — a brick that re-exports the Bell denial would be wrong in a way that reads
plausibly. §3: why the coherent branch IS available to CSD (forward evolution, not reversal), and
what that availability rests on.

## 1. What Local Friendliness is

Bong et al. 2020 (*Nature Physics* **16**, 1199), following Brukner 2018; extended by
Cavalcanti–Wiseman 2021. An extended Wigner's-friend scenario: Alice and Bob each hold a *lab*
containing a friend who measures half of an entangled pair. Alice's setting `x` selects between
**asking the friend what they observed** and **performing a coherent measurement on the whole
lab** (which does not reveal the friend's outcome). Same for Bob.

Three assumptions:

* **Absoluteness of Observed Events (AOE)** — an observed event is a single absolute event, not
  one relative to an observer. The friend's outcome exists whether or not Alice asks for it.
* **Locality** — the probability distribution of the events in one wing is unaffected by the
  distant *setting choice*.
* **No-Superdeterminism** — any set of events on a space-like hypersurface is uncorrelated with
  settings freely chosen after it. (Measurement independence, stated over *events* rather than
  over a `λ`.)

Together these bound a polytope; quantum mechanics violates its facets, and the 2020 experiment
measured a violation with photons in the 3-setting configuration.

⚠️ **Why this is not just Bell again.** The LF assumptions contain **no hidden-variable
assumption**: nothing corresponds to `λ`, and no factorisation `P(ab|xy,λ) = P(a|x,λ)P(b|y,λ)` is
posited. The LF polytope therefore **contains** the Bell-local polytope, so an LF inequality is a
*weaker* constraint and violating one is a *stronger* result. The containment is **not strict at
two settings** per party — there the LF facets are exactly CHSH — and becomes strict once a party
has three. That is the content of Bong et al., and why their experiment is a 3-setting one.

## 2. ⚠️ Three "localities", and the corpus's position on each

This is the section a brick gets wrong.

| | Statement | Quantified over | Corpus's position |
|---|---|---|---|
| **(i) Operational no-signalling** | remote **marginals** of the realised outcomes are invariant under a distant setting change | the realised joint law | **PROVED CONDITIONALLY** — `LF3/SettingLocality.lean` `operationalNoSignalling_of_settingLocality`: a Σ-level measure-preserving-relabelling primitive *implies* remote marginal invariance. Sufficient, **not** a characterisation; whether CSD's own `Σ` satisfies it is the open half of Q10. Separately verified for the singlet kernel (`singlet_operational_no_signalling`). The predicates live in `LF3/OperationalNoSignalling.lean` |
| **(ii) Bell parameter independence** | each wing's response is a function of its own setting and the shared microstate: `RA a λ`, `RB b λ` | a hidden variable `λ` | **DENIED, as a theorem** — `LF6.no_product_partition_realises_singlet`: no such pair over *any* probability space reproduces the singlet |
| **(iii) LF Locality** | the distribution of the *observed events in a wing*, including the friend's, is unaffected by the distant setting — **even when already conditioned on other events outside that setting's future light cone**. Working consequence: the **joint** law of the two friends' outcomes is setting-independent, `p(a₁b₁\|xy) = p(a₁b₁)` | observed events, **no `λ` anywhere** | **not addressed anywhere in the corpus** |

**(i) is a marginal statement; (iii) is a joint one.** That is the separation, and it has an exact
counterpart in the corpus's own vocabulary: `RemoteSettingLocalityA` and `RemoteSettingLocalityB`
carry *independent* `reroute` families (`SettingLocality.lean`), so the primitive constrains each
wing's marginal and says nothing about the joint law of `(wingA C, wingB C)` — which is precisely
what (iii) constrains.

Consequences for the brick:

* **Re-exporting CHSH proves nothing about LF.** The Bell denial (ii) lives inside an LHV frame
  that LF explicitly refuses to assume — and it is not on the twins board anyway:
  `Empirical/CSD/Bell.lean` is TRANSPORT-ONLY re-exports of the LF3 **frequency-convergence**
  capstones, not of (ii). (`BACKLOG.md` row C and `qm-empirical-tests.md` D12 both said otherwise
  until 2026-09-04; corrected.)
* **CSD keeps (i) so far as the corpus goes** — conditionally on the Σ-primitive, and verified in
  the singlet sector. The LF denial must not contradict that, and it does not: (iii) constrains
  the cross-wing joint, which (i) says nothing about.
* **CSD keeps AOE.** A record is an ontic selection in `Σ`; the friend's outcome is a fact about
  the trajectory whether or not anyone reads it.
* **CSD keeps No-Superdeterminism by posit, not by theorem.** Measurement independence is the
  single fixed `μ` across all four contexts — "a premise, not a consequence"
  (`OperationalNoSignalling.lean`) — and `SettingLocality.lean` inherits rather than discharges
  it, exactly as in `colbeck-renner-note.md`. The elimination below therefore forces
  ¬(No-Superdeterminism ∧ Locality); the corpus *chooses* the Locality horn, and that choice must
  be stated as a choice.
* **CSD cannot take the no-single-sample-space escape.** Some readings of LF evade the polytope by
  denying that events across different setting pairs share one probability space. CSD is a single
  `Σ` with one `μ`; the joint distribution exists by construction. That closes the only other
  standard exit, and it is genuine CSD content rather than a restatement of the posit.

## 3. The coherent branch: forward evolution, not reversal

An earlier draft of this note (2026-09-04, corrected the same day) claimed a **fork**: that
`Empirical/CSD/EraserSequential.lean` `sequential_no_revival` — "un-measuring is not an operation
the dynamics has" — might mean CSD does not reproduce QM's coherent-branch statistics, hence does
not violate an LF inequality, hence is *empirically exposed* to Bong et al. **That reading was
wrong**, on two counts, and the correction is the physics of the row.

**(1) The LF coherent setting does not require reversal.** In CSD there is one trajectory and it
moves forward; running it backwards is indeed not an operation the dynamics has. But Alice's
coherent setting is not a time reversal — it is an **apparatus she applies**, a forward
interaction whose effect on the Hilbert data is some unitary. The "undo" unitary `U†` is a
unitary like any other, and its realisation is a forward Σ-flow. The record is not un-made by
going back; the trajectory moves *forward* into a configuration in which the which-path
information is no longer locally readable. Nothing in CSD forbids that.

**(2) `sequential_no_revival` is narrower than its own prose.** What it proves is that a later
**±-basis marker measurement** leaves the rate flat at `1/2` — a composed Lüders update, and a
statement that holds in ordinary quantum mechanics too. It is not a CSD-specific deviation, and
it says nothing against a forward **unitary** that restores coherence. The module's gloss
"un-measuring is not an operation the dynamics has" is true of *reversal* and over-reads as a
claim about the coherent branch.

**So CSD reproduces QM here, and the elimination of §2 fires.** With AOE kept and
No-Superdeterminism kept (by posit), an LF violation forces the denial of Locality (iii). There
is no empirical exposure to Bong et al., and the row is not a falsification story.

⚠️ **What this rests on, stated plainly.** That *every* unitary is realisable as a
measure-preserving, `π`-equivariant Σ-flow is **posited, not derived**. `CSDUnitaryBundle`
(`Empirical/CSD/Gates/Framework.lean`) carries only QM-side data — `U` and `U_isometry` — and
`PLACEHOLDERS.md` §7 says so outright: *"no field carries a Σ-side flow, no field asserts
π-equivariance, no field asserts measure-preservation. The CSD-side ontic claim lives entirely in
the docstring prose."* So the coherent branch is available to CSD **on the same posit that the
whole gates layer rests on**, with the same discharge route. That is the honest dependency, and
the twin must carry it.

*(Not to be confused with recurrence. `recordDuration` is a deliberately finite window because
"indefinite stability raises recurrence questions" — Poincaré return on a compact Σ with an
invariant probability measure, quantified by Kac's formula, which the corpus has
(`Mathlib/Dynamics/Kac.lean`). That is **spontaneous** return at an astronomically long mean time
`1/μ(A)`; it is a different mechanism from an engineered forward unitary and is not what makes
the coherent branch available.)*

## 4a. What was built instead: persistence

The assumption CSD denies is not one of LF's three as usually listed. It is a fourth the
derivation uses tacitly: that the friends' records, **once made, are fixed** — a function of the
microstate alone, unchanged by whatever the party does next.

* `FriendRecords.read : MeasurementContext → Σ → Sign × Sign` — the friends' outcomes *as read in
  a context*, because that is what the protocol does. A bare `Σ → Sign × Sign` would assume the
  answer.
* `Persistent` — the reading does not depend on the context.
* `JointLawInvariant` — LF Locality at the friend level, `p(a₁b₁|xy) = p(a₁b₁)`.
* ★ `jointLawInvariant_of_persistent` — **persistence forces LF Locality.** On a single `Σ` with a
  single `μ` the sets are literally equal. So fixed records *give* Locality; a model cannot keep
  the first and deny the second.
* ★★ `not_persistent_of_jointLaw_moves` — the elimination: a joint law that moves has
  non-persistent records.
* ★ `movingRecords_not_persistent` — non-vacuity.

**CSD keeps Absoluteness of Observed Events** (a record is a definite ontic selection at every
moment) and **denies persistence** (the trajectory moves forward under the party's operation into
a configuration where the record is no longer what it was). Definite at every moment, not
invariant across the operation. Not superdeterminism and not retrocausality: persistence fails
*forward*.

## 4. The superseded deliverable — the §2 table, machine-checked

⚠️ **This replaces the first draft's target.** That draft proposed the 2-setting LF facet plus a
modus-tollens conditional. The review's objection is decisive on both halves: at two settings LF
adds nothing over Bell (§1), and a conditional whose fields never touch `Σ` is a decorative
bundle (`PLACEHOLDERS.md` §8–§9) rather than the Ozawa pattern it claimed to follow. What row C
actually asks for — "the event-level denial as a **named theorem**" — is the table above, proved.

**`Empirical/CSD/LocalFriendliness.lean`** (or `LF3/`, if the vocabulary argues for it), in
`SharedContextOutcomeMaps` vocabulary — `F : MeasurementContext → SigmaSpace → Sign × Sign`
already has full-context arity on both wings:

```
RemoteJointInvariantA μ S : ∀ (a a' b : DetectorSetting) (s t : Sign),
  μ {l | S.wingA ⟨a,b⟩ l = s ∧ S.wingB ⟨a,b⟩ l = t}
    = μ {l | S.wingA ⟨a',b⟩ l = s ∧ S.wingB ⟨a',b⟩ l = t}
```

and three theorems ordering the table:

* ★ `remoteMarginalInvariant_of_remoteJointInvariant` — **(iii) ⇒ (i)**, by summing out the other
  wing.
* ★ `remoteJointInvariant_of_isProductPartition` — a product partition satisfies (iii), so
  **(ii) ⇒ (iii)**.
* ★★ **strictness**: outcome maps satisfying `RemoteMarginalInvariantA/B` but **violating**
  `RemoteJointInvariantA`. `translationMaps` / `translationLocality` (`SettingLocality.lean`) is
  the ready-made carrier, and `translation_wingA_setting_dependent` already proves the readout
  moves with the remote setting.

That is real Σ-side content, in one vocabulary, using only landed machinery, and it ends the
(i)/(ii)/(iii) confusion by making the ordering a theorem instead of prose. The elimination
conditional can sit on top as a *corollary* if wanted — the Ozawa shape.

⚠️ The LF inequality itself is **not** in this deliverable. If it is wanted later: the 2-setting
facet is CHSH by another name, and the 3-setting facets come from a linear program over the
polytope, which is an **L**.

**Rule of two, corrected.** `chsh_classical_bound_violated` (`Bell.lean`) is the numeric gap
`2 < 2√2` — its docstring says "purely numerical" — **not** a violation witness; and
`chshOperator` is hard-wired to the singlet `correlation`, so neither applies to an abstract LF
model. The usable handles are `chsh_singlet_at_optimal_angles`, `chsh_singlet_tsirelson_bound`,
and `E91.lhvCHSH_abs_le_two` (generic in `Λ`, instantiable at a joint outcome space).

## 5. What the twin must NOT say

* **Not** that CSD explains or predicts the LF violation. CSD reproduces the quantum statistics
  here (§3); reproducing them is not explaining them, and the denial of (iii) is a consequence of
  the elimination, not a mechanism.
* **Not** that CSD denies no-signalling. It proves (i) conditionally; "CSD denies Locality" read
  without §2's table says the opposite of what is true.
* **Not** that the Bell denial is the LF denial. (ii) and (iii) are different statements over
  different objects; the row exists because that conflation is the natural mistake — and the
  canonical files made it.
* **Not** that AOE-holding is an achievement here. It follows from the ontology.
* **Not** a transport bundle on the `Empirical/CSD/Uncertainty.lean` pattern, and **not** a
  one-line re-export on the `Empirical/CSD/Bell.lean` pattern (`PLACEHOLDERS.md` §3). The CSD file
  must consume Σ-side data or it is decorative (§8–§9).

## 6. Stop condition

If a factorisation or a `λ` appears as a **field or hypothesis** of any LF-model structure, stop
and report: the model as encoded would be Bell's, not LF's. **Deriving** a global joint
distribution from the assumptions is *not* that failure — at two settings that is exactly the
content of "the LF polytope equals the Bell polytope". The test is where the factorisation sits,
not whether it appears.

For the §4 deliverable the corresponding condition is: if the strictness witness cannot be built
from `translationMaps`, do not weaken `RemoteJointInvariantA` to make the ordering go through —
report instead. An ordering with no strictness witness is three implications that might all be
equivalences, which would say nothing.

## References

`specs/BACKLOG.md` row C; `specs/qm-empirical-tests.md` D10–D12;
`CsdLean4/LF3/SettingLocality.lean` (`operationalNoSignalling_of_settingLocality`,
`translationMaps`, `translation_wingA_setting_dependent`, and the sufficient-not-characterisation
scope); `CsdLean4/LF3/OperationalNoSignalling.lean` (the predicates; measurement independence as a
stated premise); `CsdLean4/LF3/SharedContextMap.lean` (`SharedContextOutcomeMaps`);
`CsdLean4/LF6/ForcedContextuality.lean` (`no_product_partition_realises_singlet`);
`CsdLean4/Empirical/CSD/EraserSequential.lean` (`sequential_no_revival` — §3's fork);
`CsdLean4/RecordLayer/RecordPersistence.lean` (`recordDuration`, the finite window);
`CsdLean4/Empirical/QM/Bell.lean` and `Empirical/QM/Crypto/E91.lean` (the CHSH handles);
`CsdLean4/Empirical/CSD/Ozawa.lean` (the scope-theorem pattern); `specs/colbeck-renner-note.md`
(the same unbundling discipline); `PLACEHOLDERS.md` §3, §8–§9. Source: Bong et al., *Nature
Physics* **16**, 1199 (2020); Brukner 2018; Cavalcanti–Wiseman 2021.
