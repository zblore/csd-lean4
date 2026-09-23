# Batch 009: finite-dimensional Busch reconstruction and its dependency guard

Date: 2026-09-23. Reviewer: Codex. Checkout: `lean4-codex-review`, branch
`codex/corpus-review`, HEAD `7ba73923` plus the recorded local edits. Lean v4.33.0;
Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

## Scope and conclusion

Full code, mathematical statement/proof, and comment review of:

- `CsdLean4/LF2/EffectGleason.lean` (the complete file, including all reconstruction stages).
- `scripts/gleason-free.lean` (the complete traversal, selection logic and run command).

Supporting edits: two axiom pins in `Tests/AxiomAudit/Foundations.lean` (partial review),
and the shell guard's explanatory comment. Supporting reads of BornWrapper, EffectAux and
operational consumers do not receive new full-review credit.

No mathematical error was found in the existing reconstruction proof. There was a real
verification-tool defect: direct use of the reconstructed density escaped the advertised
Gleason-free dependency check. There was also a redundant caller proof obligation and
several inaccurate or stale comments. These findings have different significance.

## Reconstruction: what the code proves

The input is one real-valued function on every complex matrix effect `0 ≤ E ≤ I`, with
positivity, normalization and additivity whenever the sum is an effect. Additivity covers
noncommuting pairs. The output is a unique positive semidefinite, trace-one matrix whose
trace pairing agrees with the function on every effect.

This is the finite-dimensional effect version of Busch's theorem. The effect domain is
stronger input than orthogonal-projector additivity in classical Gleason. Busch's paper
explicitly includes qubits; its broader Hilbert-space statement also treats countable
additivity. The Lean statement here is finite-dimensional and needs finite additivity.
Primary comparison: [Busch, Quantum states and generalized observables: a simple proof of
Gleason's theorem](https://arxiv.org/html/quant-ph/9909073v3).

| Stage checked | Mathematical assessment |
|---|---|
| Zero, monotonicity and scalar homogeneity | Difference/complement effects justify monotonicity; rational approximation and squeezing establish real homogeneity without a continuity premise. Zero endpoints are covered. |
| Spectral reduction | Effect eigenvalues lie in `[0,1]`; finite additivity recovers the assignment from weighted spectral projectors. |
| Outer products and parallelogram identity | Subunit vectors include zero. The two-vector PSD estimate uses the sum of squared norms; scaled additivity supplies the local quadratic identity. |
| Global quadratic form and polarization | Normalization away from zero extends homogeneously. The bounded additive-function argument supplies real linearity. Complex polarization has the correct sign and conjugate-linear first/linear second convention. |
| Matrix reconstruction | Standard-basis coefficients represent the form; spectral reduction extends the trace formula to every effect. |
| State conditions and uniqueness | Nonnegative quadratic values imply PSD; normalization gives trace one. Complex polarization determines the whole matrix, establishing uniqueness. |
| Boundary and callers | The main theorem supports dimensions one and two. Dimension zero admits no normalized package. Legacy wrapper dimension hypotheses remain for compatibility and are documented. |

The proof is a finite spectral/polarization implementation, not a line-by-line translation
of the paper's extension to a positive functional. It assumes the complex effect algebra;
it does not derive ontic regions, identify their probabilities with this assignment, or
settle arbitrary contextual hidden-variable models. Existing CSD integration obligations
remain in CR-LF2-006. Nothing found here invalidates CSD's objectives.

## Repairs

### CR-GLEASON-001: derive the redundant upper bound

Added `OperationalPackage.ofNonnegAdditive` and its projection lemma. For each effect, its
complement is an effect and additivity gives `p E + p (I - E) = 1`. Nonnegativity of the
complement therefore proves `p E ≤ 1`. Added
`effect_gleason_representation_of_nonneg_additive`, which uses that constructor and the
existing representation theorem.

This removes a caller proof obligation; it does not enlarge the mathematical solution
class or prove a new physical reconstruction principle. Existing structure fields,
consumer signatures and reconstruction proofs are retained. The only new simp rule
matches the new constructor. Two guarded axiom pins cover the new interface.

### CR-GLEASON-002: repair a confirmed guard bypass

The old guard forbade only `effect_gleason_representation` and recursed only through names
in the `CSD` namespace. An executed probe gave:

```text
headline: true
density: false
alias: false
```

Here `density` is `OperationalPackage.qdensity` and `alias` is a local definition outside
`CSD` returning that density. A proof could therefore use the construction directly while
the old guard reported no dependency on the headline theorem.

The repaired guard forbids the headline theorem, `qdensity` and `qmatrix`; traverses local
and CsdLean4-module declarations regardless of namespace; and selects declarations by
module ownership. It reads theorem proof terms explicitly. Built-in regression fixtures
check direct reconstruction, an alias outside CSD, existence of the forbidden roots, and
an allowed scalar helper (`p_zero`). The declared eleven production modules are unchanged.
External dependencies cannot import the corpus; import-hygiene checks the staged-Mathlib
boundary. This guard checks dependencies on these named reconstruction entry points, not
semantic equivalence to any imaginable alternate reconstruction proof.

The test witness `Tests/Witnesses/SingletBell.lean` remains outside this production-root
scan, as explicitly documented. Its target builds, but that alone does not give it this
proof-dependency guarantee. Structural import-negative checks remain a separate check.

### CR-GLEASON-003: comments

Corrected general outer products called rank-one projectors (zero and nonunit vectors are
allowed), homogeneity still called deferred, state conditions described as future work,
and claims that continuity was unavailable. Boundedness supplies the needed regularity;
continuity is not an extra assumption. Added the exact effect-domain and dimension scope.

## Validation

- Focused EffectGleason build passed (2709 jobs).
- `lake build --wfail CsdLean4 CsdLeanTests` passed (4330 jobs), including both batches 008
  and 009. The first run exposed line wrapping in the new long-name axiom-output fixture;
  whitespace-insensitive matching corrected it without changing the expected axiom list.
- Standalone Lean boundary/examples below passed. Both new declarations report only
  `propext`, `Classical.choice`, `Quot.sound`.
- Isolated traversal regressions passed: reconstruction roots, cross-namespace aliases,
  and allowed `p_zero`.
- `check-gleason-free.sh` passed: 260 declarations in 11 modules avoid all three
  reconstruction roots; traversal regressions passed. No forbidden route was found in
  those existing declarations. After this run, a comment alone was clarified to distinguish
  shared proof-term extraction from the new broader traversal policy.
- Eight further guards passed: doc-promises, category-tags, claims, semantic-mutations,
  references, import-hygiene, residues and import-negative. This is not a claim that every
  blocking CI check or independent mathematical sign-off has been completed.

Reproduce the boundary/examples with `lake env lean --stdin`:

```lean
import CsdLean4.LF2.EffectGleason
open CSD.LF2
open scoped ComplexOrder

example (OP : OperationalPackage 0) : False := by
  have h : (Effect.one : Effect 0) = Effect.zero :=
    Effect.ext_M (by ext i; exact Fin.elim0 i)
  have ht := OP.total_one
  rw [h, OP.p_zero] at ht
  norm_num at ht

-- Includes N = 1 and N = 2; the caller supplies no upper bound proof.
example (N : ℕ) (i : Fin N) :
    ∃! ρ : DensityOperator N, ∀ E : Effect N, (E.M i i).re = traceForm ρ E := by
  apply OperationalPackage.effect_gleason_representation_of_nonneg_additive
  · intro E
    exact (Complex.nonneg_iff.mp (E.nonneg.diag_nonneg (i := i))).1
  · simp [Effect.one]
  · intro E F h
    simp [Effect.add, Matrix.add_apply]
```

## Coverage refresh and next work

Twelve previously fully reviewed consumers and two partial entries acquire a new dependency
hash through EffectGleason. Their own reviewed source blobs are unchanged. The delta adds
an opt-in constructor/theorem and corrects prose, with no replacement of existing proofs,
instances or signatures. The successful full build validates consumers against that delta;
this report refreshes their dependency evidence without counting them as new full reviews.
The ledger preserves their earlier findings, scopes and report links.

The affected full entries are FlowChannel, Preparation, PreparationBarycenter,
PreparationQdensity, LF3/Interface, PurePreparation, SingletProjective, SingletKahler,
SingletKahlerFlow, C1BellConsistency, MeasurementFlowChannel and Tests/Witnesses/SingletBell.
The two prior partial entries are Thermo/SigmaSecondLaw and Tests/AxiomAudit/Dynamics.
Foundations receives a third partial entry.

Current full coverage is **37 of 691 Lean files (5.35%)**, with three partial entries. This is a targeted review, not a
random sample for estimating the corpus-wide defect rate. Next continue at the actual
preparation/event bridge and record interfaces (CR-LF2-006 and CR-RECORD-003); no remaining
mathematical repair was identified inside this Busch reconstruction. Batch 008 edits are
preserved; this batch does not commit, push or integrate changes from the other checkout.
