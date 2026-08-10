# EFT pillars: what stands between the corpus and a field theory

Created 2026-08-10. Companion to `specs/external-library-map.md` (alignment),
`specs/cv-stage3-plan.md` / `eft-stage4-plan.md` / `eft-stage5-plan.md` (the CV
ladder as built), and `specs/necessity-audit.md` (what the constraint set
actually pins down).

## 0. Alignment: the window is open

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

Recommendation: pursue A's bounded items for their own sake, since they harden
claims the corpus already makes, while treating pillar P1 below as the item that
serves both routes.

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

Effort: **L**, research-flavoured but not unbounded.

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

### P3. The factorisation problem (research, not a brick)

CV's modes are a chosen tensor factorisation of a Hilbert space, and
`CV/ModeLocality.lean` says in terms that the position reading is a reading.
Attaching a spatial index to a chosen factorisation posits spatial structure
rather than deriving it. Until the factorisation is tied to the arena's own
structure, "field on spacetime" has no referent inside the theory.

This is the deepest gap on the page and the one least suited to being queued as
a Lean tranche. Record it, do not schedule it.

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
  achieved, would turn "costs at most" into "costs exactly".
* **An actual RG step.** `exists_unitary_compress_not_unitary` already proves
  exact unitary matching between cutoffs is impossible, which says the effective
  low-cutoff dynamics must be an open map. That is a genuine lead rather than a
  gap: it names the shape the RG step has to have.

Effort: **M** each. P5's RG half is the most concrete unclaimed result here.

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

## 4. Direct answers

**Is CV needed?** Yes, but as the *specification*, not the construction. The CV
results are the isolated-piece image of the rules: they say what field structure
at a cutoff must reproduce. They are the acceptance test a field-structured flow
would have to pass, which is why P1 and not more CV is the next structural step.

**Are records needed?** Under route A they are not on the critical path. Under
route B they are the path. Under either, the record layer is what gives the
theory contact with anything observable, so it is not optional — it is just not
what unblocks EFT specifically.

**What else is missing?** P1 through P5, with P1 (the arena bridge and a
field-structured flow) and P3 (factorisation) carrying the weight. P4 and P5 are
the bounded ones and are where Lean work should start.

## 5. Sequencing

1. ~~**Now:** toolchain `rc1 → 4.33.0` stable.~~ **DONE 2026-08-10.**
2. **~2026-08-18:** re-check Physlib; align, still without adding a dependency
   until something is consumed.
3. **Near-term Lean:** P5's RG-as-open-map, then P4. Both bounded, both convert
   existing sufficiency claims into results with direction.
4. **Medium-term structural:** P1, starting with the arena bridge, since it is
   the twice-observed bottleneck.
5. **Alongside:** P2, which has the algebra half already proved.
6. **Recorded, unscheduled:** P3.

## References

`specs/external-library-map.md`; `specs/necessity-audit.md`;
`specs/cv-stage3-plan.md`, `specs/eft-stage4-plan.md`, `specs/eft-stage5-plan.md`;
`CsdLean4/CV/ModeLocality.lean`, `CsdLean4/CV/LiebRobinson.lean`,
`CsdLean4/CV/Decimation.lean`, `CsdLean4/SigmaLayer/TensorReconstruction.lean`,
`CsdLean4/SigmaLayer/JoinGeneration.lean`; `specs/BACKLOG.md`.
