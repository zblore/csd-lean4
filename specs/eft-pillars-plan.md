# EFT pillars: what stands between the corpus and a field theory

Created 2026-08-10. **Brought current 2026-08-19** (the CV ladder finished; P5's
RG half discharged; P3 reclassified from gap to ceiling — see the change log at
the end). Companion to `specs/external-library-map.md` (alignment),
`specs/cv-stage3-plan.md` / `eft-stage4-plan.md` / `eft-stage5-plan.md` /
`eft-stage6-plan.md` / `eft-stage7-plan.md` (the CV ladder as built), and
`specs/necessity-audit.md` (what the constraint set actually pins down).

**Status of the ladder this page measures against: COMPLETE.** Rows CV-1…CV-26
are all closed (Stages 4, 5, 6, 7 each COMPLETE; 26 modules in `CsdLean4/CV/`).
So this page is no longer "what stands between the corpus and Route A" — Route A
is built. What remains is P1–P4 as listed, plus the standing ceiling P3.

## 0. Alignment: the window is open *(historical — resolved 2026-08-17, see §5.2)*

Lean `v4.33.0` stable was released 2026-08-10. Toolchains verified the same day:

| Repo | Toolchain |
|---|---|
| csd-lean4 | `v4.33.0` (bumped 2026-08-10) |
| Physlib | `v4.32.0` |
| Lean-QIT | `v4.30.0` |

The recorded plan was a single jump `rc1 → 4.33.0 stable`, skipping rc2. **Done
2026-08-10**, the same day 4.33.0 released. Physlib bumps
stable-only, historically about eight days after a release, so the expected
convergence is around 2026-08-18. Lean-QIT at `4.30.0` is three minor versions
back and is not converging soon; the cited-not-imported posture on their DPI
stands.

Two things worth keeping separate. **Aligning toolchains** is cheap, reversible,
and unblocks everything later. **Adding a dependency** chains our Mathlib
cadence to theirs and should still wait for a specific theorem or API that is
actually consumed, per the four-way classification rule. Align now; depend when
there is something to import.

## 1. The fork that decides the rest

"Move toward EFT" resolves two different ways, and they have different critical
paths.

**Route A, effective field theory with spacetime given.** This is the recorded
ladder posture: finite-dimensional QM, then continuous spectra via CV, then
relativistic EFT, taking spacetime as given throughout. Here the CV chain *is*
the content, and the record layer is not on the critical path.

**Route B, the field structure of the substrate itself.** Here fields are not
objects placed on the arena; they are the rules by which the arena works, so the
target is not "build fields on Σ" but "characterise Σ's flow as
field-structured". The record layer becomes load-bearing rather than parallel.

The distinction matters because it changes what "missing" means. Under A, the
gaps are technical and mostly bounded. Under B, the central gap is conceptual
and is not a Lean brick.

**Route A now has a stated ceiling, not just gaps (added 2026-08-19).** The
factorisation item P3 is not a deferred task that better technique closes: a
chosen tensor factorisation is a construct on the *epistemic* side of the theory
(the `ℂℙⁿ⁻¹` base and its regions), and anchoring epistemic bookkeeping — however
tightly — does not manufacture a spatial referent. So Route A's spatial index is
a **label, permanently**. That is the honest price of taking spacetime as given,
and it bounds what the completed CV ladder can be claimed to have achieved. See
P3 below.

Recommendation: pursue A's bounded items for their own sake, since they harden
claims the corpus already makes, while treating pillar P1 below as the item that
serves both routes. Do **not** queue P3 as an approach to spatial structure.

## 2. The pillars

### P1. A field-structured flow (the central gap, serves both routes)

Today the arena's flow is characterised only as measure-preserving and
projectable. Explicit Hermitian generators exist in exactly two places, both on
measurement strokes: `rampedU_schrodinger` (record creation) and
`joinFlowMat_hasDerivAt` (relocation, 2026-08-10). Nothing says the flow has
*field* structure, meaning a generator decomposing into local pieces with a
locality relation among them.

The machinery for that statement already exists, but on the wrong arena.
`adIter_supportedOn_graphBall` and the Lieb-Robinson family
(`norm_commutator_spatial_factorial_le`) do exactly this decomposition for
matrix generators on the CV mode arena. The record and sector layers live on
`ℂℙ^{N-1} × T²` and its protocol arenas, where locality is a measure-and-set
notion rather than an operator-support notion.

⚠️ **The arena bridge is the bottleneck, and it surfaced twice independently on
2026-08-10.** Once when a Lieb-Robinson bound on record redundancy turned out to
be unstatable because the two layers are different mathematical categories, and
once as the reason `RelocationObstruction.lean` is scoped to one architecture.
A result that recurs as a blocker in unrelated attempts is the structural
bottleneck, not a detail. Building it is the highest-value structural item on
this page.

**THE BRIDGE IS BUILT (first arc, 2026-08-19 — `CV/ArenaBridge.lean`,
[`arena-bridge-plan.md`](arena-bridge-plan.md), 4 pins).** The translation is
three definitions and one inequality: `arenaObs A p = re tr(ρ_p A)` reads a
matrix observable as a *function on the projective arena*; `arenaObs_kick` is
the bridge identity (Schrödinger on the arena IS Heisenberg on the operator);
and CR-1's Hölder-lite bound — landed 2026-08-19 for the channel-RG arc, and
turning out to be exactly the missing category interface — makes arena
observables 1-Lipschitz in the operator norm, so the whole CV estimate stack
crosses over. Delivered on the far side: ★ exact Haag–Kastler statics on the
arena (`arenaObs_kick_of_disjointSupport`), and ★★ `arena_lightcone` — **the
very Lieb-Robinson-at-the-record-layer statement that was unstatable on
2026-08-10**, now a theorem with the CV-20 factorial tail as its bound.

**P1 remainder** (the honest-scope block of the module): (i) the fibre-active
extension — the bridge covers the projective *base*; functions on the fibred
`ℂℙ^{N-1} × T²` arenas that factor through the base inherit everything, but the
fibre-carrying content does not yet; (ii) the definitional half — a
*field-structured flow* as a structure whose generator decomposes into
`SupportedOn` pieces, stated against this transport. (ii) is now bounded rather
than research-flavoured: the transport it needed is what this arc built.

Effort: ~~L, research-flavoured but not unbounded~~ → remainder **M** (the
bottleneck half is done; what is left is a definition and its instances).

### P2. Composite arenas

The arena models one isolated sector. A field theory needs many, and a rule for
composing them.

There is a real foothold: `compositeAlgReconstruction` / `composite_dim_eq`
(`SigmaLayer/TensorReconstruction.lean`) force the tensor product and the
dimension `k = m·n` from commuting, generating local subalgebras, quantified
over arbitrary embeddings. Per `specs/necessity-audit.md` this is the strongest
composition result in the corpus, and it is conditional only on the ambient
matrix-algebra setting.

What is missing is the arena-side analogue: what the composite of two ontic
sectors *is*, and whether the algebra-side forcing transports to it.

Effort: **M–L**. The algebra half is done; the transport is the work.

### P3. The factorisation problem — a CEILING, not a gap (reclassified 2026-08-19)

CV's modes are a chosen tensor factorisation of a Hilbert space, and
`CV/ModeLocality.lean` says in terms that the position reading is a reading.
Attaching a spatial index to a chosen factorisation posits spatial structure
rather than deriving it. So inside Route A, "field on spacetime" has no referent.

**What changed.** This row previously read "until the factorisation is tied to the
arena's own structure, …", i.e. as a deep but in-principle closable gap, and was
filed as "research, not a brick". That framing was wrong in a way that invites
work: it treats the obstruction as difficulty. The obstruction is **placement**. A
tensor factorisation, and the regions defined over it, sit on the *epistemic* side
of the theory — `specs/sigma-fibre-contextuality.md` reaches the same placement
independently, finding the `ℂℙⁿ⁻¹` base to be "a lossy epistemic projection" with
the record-forming and contextual content living in the fibre above it, and for
`N ≥ 3` finding that it *must* (covariance plus non-negativity kill the
base-only alternative — not a Gleason/KS argument). Anchoring an epistemic
construct more tightly does not convert it into ontic structure.

**Consequence.** P3 is a standing statement of Route A's limit, to be cited when
scoping, not a queue item. Concretely:

* Do not propose "tie the factorisation to the arena" as an approach to spatial
  structure, and do not read a mode lattice as spacetime (the CV chain's own
  non-goals already forbid the second).
* Do not score the completed CV ladder as having earned a spatial referent. It
  earned locality *between chosen tensor factors*, which is the acceptance test of
  §4, and that is the correct and sufficient claim.
* The prior instruction — "record it, do not schedule it" — stands, and is now
  recorded for the right reason.

Effort: **not applicable** (not a work item).

### P4. Relativistic structure earned rather than defined

`omega m p := √(p² + m²)` and the standard boost are **definitions**, and
`boost_invariant` / `boost_omega` are algebra from them. The converse, that
covariance selects this dispersion, is proved nowhere. `specs/necessity-audit.md`
records the prose here as overstating the statements.

What would close it: derive the dispersion from the light-cone structure plus a
symmetry posit, or import genuine representation theory. This is the difference
between having written relativity down and having it forced.

Effort: **M**. Bounded, and it converts a sufficiency cluster into something
with direction.

### P5. Interactions past upper bounds

Stage 3 delivered the Duhamel price ladder and power counting as **upper bounds
with no matching lower bounds**, and the audit found `CutoffStability.lean` and
`PowerCounting.lean` contradicting each other on whether renormalisation is
forced. Two concrete pieces:

* **Attainment.** A lower bound, or a witness showing the linear price is
  achieved, would turn "costs at most" into "costs exactly". **STILL OPEN** (it
  stays a ledger note per the Stage-6/7 non-goals).
* ~~**An actual RG step.**~~ **DONE 2026-08-18 (CV-26, `CV/ChannelRG.lean`).** The
  lead this row named was right: `exists_unitary_compress_not_unitary` says the
  effective low-cutoff dynamics must be an open map, and that is the shape the
  result took. `channelRG_dist_le`:
  `D(C(Uⁿρ Uⁿ†), U_eff ⁿ·C(ρ)·U_eff ⁿ†) ≤ 2n·|τ|·|λ|·C` for every density
  operator, with the coarse-graining a genuine CPTP map (mode tracing, built as
  the Stinespring channel of the mode-split isometry) and the defect assembled
  from the CV-9 Duhamel price, the CV-12 telescoping, and the CR-1
  trace-distance/operator-norm bridge. Scoped first in
  `specs/channel-rg-scoping.md`. ⚠️ **One step, not a flow** — no iteration, no
  fixed point, no beta function; level decimation stays unselected pending a
  leakage estimate.

Effort: attainment **M**; the RG half is closed.

## 3. Already settled — do not redo

* Cutoff posture: `no_exact_finite_ccr` (no finite system carries exact CCR)
  plus cutoff-independence. The continuum is not required.
* Locality and the light cone, up to the textbook factorial Lieb-Robinson form.
* Interaction pricing by boundary coupling (upper bounds), power counting,
  cutoff stability, decimation no-go, the free propagator.
* Chaos diagnostics: spectral form factor, OTOC with its light-cone gate, echo
  bound, half-life sharpness.
* Both measurement strokes now have explicit Hermitian generators, on their
  respective architectures.
* **Correlators to all orders** (added 2026-08-19): vacuum clustering, the
  four-point Wick table and its packaged pairing sum, the time-separated
  four-point, and the `2n`-point moment ladder `⟨Q^{2n}⟩ = (2n−1)‼·(½)ⁿ` exact
  below the `n < N` truncation threshold (`CV/Propagator.lean`, `CV/Wick.lean`).
* **The thermal tier** (added 2026-08-19): the Gibbs field state in closed form,
  the thermal propagator with its truncation edge explicit, the `β → ∞` vacuum
  limit, and **exact KMS at the cutoff** — the corpus's first KMS statement, and
  the join of the Thermo and CV verticals (`CV/ThermalPropagator.lean`).
* **A priced channel-level RG step** (added 2026-08-19): P5's RG half, above.

## 4. Direct answers

**Is CV needed?** Yes, but as the *specification*, not the construction. The CV
results are the isolated-piece image of the rules: they say what field structure
at a cutoff must reproduce. They are the acceptance test a field-structured flow
would have to pass, which is why P1 and not more CV is the next structural step.
**Update 2026-08-19: that specification is now COMPLETE** (CV-1…CV-26). The
acceptance test exists in full — kinematics with the CCR ceiling, locality,
cones, correlators to all orders, the thermal tier with exact KMS, and a priced
RG step — so "more CV" is no longer even the tempting option. Note what
completeness does *not* buy: per P3 it does not earn a spatial referent, and per
the ladder's non-goals it is not a continuum limit and not an RG flow.

**Are records needed?** Under route A they are not on the critical path. Under
route B they are the path. Under either, the record layer is what gives the
theory contact with anything observable, so it is not optional — it is just not
what unblocks EFT specifically.

**What else is missing?** P1 (the arena bridge and a field-structured flow)
carries the weight; P2 and P4 are the bounded remainder; P5's attainment half is a
ledger note. **P3 is not "missing" — it is a ceiling** (reclassified 2026-08-19),
so the honest list of *work* is P1, P2, P4, and P5-attainment.

## 5. Sequencing

1. ~~**Now:** toolchain `rc1 → 4.33.0` stable.~~ **DONE 2026-08-10.**
2. ~~**~2026-08-18:** re-check Physlib; align, without adding a dependency.~~
   **DONE 2026-08-17** — alignment verified **byte-identical** (toolchain
   `v4.33.0`, Mathlib `db584cd6…`), two weeks ahead of this forecast; the full
   rescan ran the same day and consumed nothing, per
   `specs/external-library-map.md`. The align-don't-depend posture stands.
3. ~~**Near-term Lean:** P5's RG-as-open-map, then P4.~~ **RG half DONE
   2026-08-18** (CV-26). **P4 is now the next bounded item**: derive the
   dispersion from light-cone structure plus a symmetry posit rather than defining
   `ω = √(p² + m²)` and doing algebra from it — the difference between having
   written relativity down and having it forced.
4. **Medium-term structural:** P1, starting with the arena bridge, since it is
   the twice-observed bottleneck. With the CV specification complete and P3 closed
   as a ceiling, this is the highest-value item on the page.
5. **Alongside:** P2, which has the algebra half already proved.
6. **Recorded, never scheduled:** P3 — a ceiling, cited when scoping.

## 6. Change log

* **2026-08-19.** Brought current after the CV ladder closed. (i) Ladder status
  recorded as COMPLETE (CV-1…CV-26, Stages 4–7). (ii) **P3 reclassified from
  "deepest gap" to standing ceiling** — the obstruction is placement, not
  difficulty; a tensor factorisation is an epistemic construct and anchoring it
  does not yield a spatial referent. Route A's spatial index is a permanent label.
  (iii) P5's RG half struck as DONE by CV-26; attainment still open. (iv) §3
  gained the all-orders correlators, the thermal/KMS tier, and the priced RG step.
  (v) §5 items 2 and 3 struck; P4 named as the next bounded item, P1 as the next
  structural one.

## References

`specs/external-library-map.md`; `specs/necessity-audit.md`;
`specs/cv-stage3-plan.md`, `specs/eft-stage4-plan.md`, `specs/eft-stage5-plan.md`;
`CsdLean4/CV/ModeLocality.lean`, `CsdLean4/CV/LiebRobinson.lean`,
`CsdLean4/CV/Decimation.lean`, `CsdLean4/SigmaLayer/TensorReconstruction.lean`,
`CsdLean4/SigmaLayer/JoinGeneration.lean`; `specs/BACKLOG.md`.
