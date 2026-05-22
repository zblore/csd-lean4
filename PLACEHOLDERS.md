# PLACEHOLDERS.md

Canonical ledger of **placeholder content** in the `CsdLean4` corpus:
declarations that compile (`lake build` passes, no `sorry`, no
`admit`) but whose content is **claim-shaped without a proof**, or is
**tautological**, or is otherwise **structural scaffolding** rather
than mathematical content.

This file is the honest counterpart to `AXIOMS.md` and
`BRIDGE-OBLIGATIONS.md`:

- `AXIOMS.md` — what Lean's `#print axioms` reports (foundational
  triple + LF2's two spec-mandated axioms).
- `BRIDGE-OBLIGATIONS.md` — what *structural fields* CSD-side bridge
  bundles carry as hypotheses pending LF4 discharge.
- **This file** — what **named declarations** in the corpus are
  *placeholders* (unproved Props, tautologies, vacuous claims, or
  deferred theorems) that **a reader could otherwise mistake for
  proved content**.

Maintained under the same discipline as `BRIDGE-OBLIGATIONS.md`:
updated in the same commit as any placeholder is added, removed, or
discharged.

## Why this file exists

The architecture-discipline files (`AXIOMS.md`,
`BRIDGE-OBLIGATIONS.md`) audit two specific concerns: per-theorem
axioms (via `#print axioms`) and per-bundle load-bearing fields. Neither
catches the case of an **unproved `Prop` definition** sitting alone in
a file: a `Prop` definition has no `#print axioms` output, and an
orphan Prop (not a field of a load-bearing bundle) doesn't appear in
`BRIDGE-OBLIGATIONS.md`.

This file closes that gap. Every placeholder of the four kinds below is
catalogued explicitly with a TODO marker pointing here.

## Categories

1. **Unproved Prop definitions.** `def foo : Prop := ...` declarations
   that compile but for which **no proof of any inhabitant** exists
   anywhere in the corpus. (Examples: the eight `*_realisable_for` Props
   in `Empirical/CSD/Gates/` — see §1 below.)
2. **Tautologies.** Theorems closed by `rfl` whose statement is
   *definitionally* the form of one side, so the theorem reduces to
   `X = X`. These carry zero information but appear named because
   downstream consumers want a labelled handle. (Examples:
   `qmBellPrep_factorisation` — see §2 below.)
3. **Vacuous Props.** Props whose body contains `True` (or another
   trivially satisfied form) in the existential's body. These are
   provable by `⟨_, _, trivial⟩` and carry no real content. (Status:
   **none in current corpus** as of 2026-05-22; the previous vacuous
   `bell_prep_realisable_for ... True` was fixed in commit landing
   alongside this file.)
4. **Re-export aliases.** `theorem alias_name := original_name`
   declarations introduced solely for namespacing or for the symmetry
   of CSD-side / QM-side parallel files. Not placeholders in the
   sense of unfinished work, but worth cataloguing because a reader
   might mistake the count of "CSD-side theorems" for original
   content. (Examples: the `csd_qm*` lemmas in
   `Empirical/CSD/Gates/{SingleQubit,TwoQubit,MultiQubit}.lean` —
   see §3 below.)

## 1. Unproved Prop definitions

Eight Props, all in the Tranche 1 Tier A gate bridges, all sharing
the same LF4-todo §13.2 discharge route. Each Prop asserts:
"there exists a `CSDUnitaryBundle D N H_n` whose carried unitary `U`
equals the QM-side gate matrix's action."

Pre-LF4, no concrete `D` is constructed for which any of these holds.
The Props are **claim-shaped** placeholders for the LF4-§13.2
obligation.

| File | Prop | LF4-todo | Status |
|---|---|---|---|
| `Empirical/CSD/Gates/SingleQubit.lean` | `hadamard_realisable_for` | §13.2 | unproved |
| `Empirical/CSD/Gates/SingleQubit.lean` | `phaseS_realisable_for` | §13.2 | unproved |
| `Empirical/CSD/Gates/SingleQubit.lean` | `phaseT_realisable_for` | §13.2 | unproved |
| `Empirical/CSD/Gates/TwoQubit.lean` | `cnot_realisable_for` | §13.2 | unproved |
| `Empirical/CSD/Gates/TwoQubit.lean` | `swap_realisable_for` | §13.2 | unproved |
| `Empirical/CSD/Gates/TwoQubit.lean` | `cz_realisable_for` | §13.2 | unproved |
| `Empirical/CSD/Gates/MultiQubit.lean` | `toffoli_realisable_for` | §13.2 | unproved |
| `Empirical/CSD/Gates/MultiQubit.lean` | `fredkin_realisable_for` | §13.2 | unproved |

Plus the composite **Bell-prep realisability**:

| File | Prop | LF4-todo | Status |
|---|---|---|---|
| `Empirical/CSD/Gates/BellPrep.lean` | `bell_prep_realisable_for` | §13.2 | unproved (rewritten 2026-05-22 from the previous vacuous form `∃ b_HI b_CNOT, True` to a non-vacuous existential constraining both bundles' `U` to the QM-side matrices) |

**Each Prop carries:**

- A docstring marker `**PLACEHOLDER (Prop definition, not proved).**`.
- A `-- TODO(LF4 §13.2):` comment line immediately above the
  declaration body.
- A `See PLACEHOLDERS.md` cross-reference in the docstring.

## 2. Tautologies

| File | Theorem | Status | Replacement target |
|---|---|---|---|
| `Empirical/QM/Gates/BellPrep.lean` | `qmBellPrep_factorisation` | tautology (`qmBellPrepCircuit = qmCNOT * qmH_tensor_I`, where LHS is *defined* as RHS — reduces to `rfl`) | `qmBellPrep_yields_phiplus` (deferred; the genuine empirical identity `(toEuclideanLin qmBellPrepCircuit) qmKet00 = qmKetPhiPlus`) |
| `Empirical/CSD/Gates/BellPrep.lean` | `csd_qmBellPrep_factorisation` | re-export of the tautology under the CSD namespace; inherits the tautology label | inherits the replacement target from the QM-side row above |

**Each tautology carries:**

- A docstring marker `**TAUTOLOGY (definitional unfold).**`.
- An explicit note on what the genuine identity *would* be, and what
  is blocking its proof.
- A `-- TODO:` comment line above the unproved replacement target.

## 3. Re-export aliases

These are not placeholders for unfinished work — they are honest
re-exports of QM-side identities under the `CSD.Empirical.CSDBridge`
namespace, used for parallel-file symmetry. Catalogued here because a
naive count of "CSD-side theorems" in `Empirical/CSD/Gates/` would
overstate the original-content footprint.

| File | Alias | Re-exports | Status |
|---|---|---|---|
| `Empirical/CSD/Gates/SingleQubit.lean` | `csd_qmH_mul_self` | `QM.Gates.qmH_mul_self` | scaffolding (acceptable) |
| `Empirical/CSD/Gates/SingleQubit.lean` | `csd_qmS_sq` | `QM.Gates.qmS_sq` | scaffolding (acceptable) |
| `Empirical/CSD/Gates/SingleQubit.lean` | `csd_qmT_sq` | `QM.Gates.qmT_sq` | scaffolding (acceptable) |
| `Empirical/CSD/Gates/TwoQubit.lean` | `csd_qmCNOT_mul_self` | `QM.Gates.qmCNOT_mul_self` | scaffolding (acceptable) |
| `Empirical/CSD/Gates/TwoQubit.lean` | `csd_qmSWAP_mul_self` | `QM.Gates.qmSWAP_mul_self` | scaffolding (acceptable) |
| `Empirical/CSD/Gates/TwoQubit.lean` | `csd_qmCZ_mul_self` | `QM.Gates.qmCZ_mul_self` | scaffolding (acceptable) |
| `Empirical/CSD/Gates/MultiQubit.lean` | `csd_qmToffoli_mul_self` | `QM.Gates.qmToffoli_mul_self` | scaffolding (acceptable) |
| `Empirical/CSD/Gates/MultiQubit.lean` | `csd_qmFredkin_mul_self` | `QM.Gates.qmFredkin_mul_self` | scaffolding (acceptable) |

The pattern is mirrored in the four pre-Tranche-1 Bridge files (Bell,
NoCloning, KS18, GHZ) — those re-exports are not catalogued here because
the corresponding QM-side identities are *not tautologies*, and the
CSD-side re-exports are part of the formal interface to the LF1↔LF2↔LF3
chain capstones (Bell) or the negative-existential / partition content
(NoCloning, KS18, GHZ).

## 4. What this file does *not* catalogue

- **`:= rfl` definitional-unfold lemmas where the LHS is a derived
  definition.** These are not tautologies; they are honest
  definitional unfolds that downstream tactics need as named handles
  (the LHS is a `noncomputable def` packaging the RHS for use under a
  namespace). Examples: many of the matrix-equality identities in the
  Tranche 1 QM-side gate files.
- **Axioms.** Catalogued in `AXIOMS.md`.
- **Load-bearing bundle fields.** Catalogued in `BRIDGE-OBLIGATIONS.md`.
- **Future work / unwritten files.** Tracked in
  `specs/empirical-csd-bridge-plan.md` §4 and
  `specs/qm-empirical-tests.md`.

## 5. Discipline

Same as `BRIDGE-OBLIGATIONS.md` §1: status markers in docstrings,
TODO comments above declaration bodies, ledger updated in the same
commit as any change to placeholder content. New placeholders may only
land if simultaneously catalogued here.

## 7. Schema-mismatch bundles (third-pass audit, 2026-05-22)

A **schema-mismatch bundle** is a `structure` whose fields encode one
set of content but whose docstring claims a *different*, broader set of
content. Lean can only check the propositions encoded in the type; any
claim in the docstring that does not appear as a field is non-syntactic
and the typechecker cannot verify it.

| Structure | File | Fields in type | Claim in docstring |
|---|---|---|---|
| `CSDCloningBundle` | `Empirical/CSD/NoCloning.lean` | tensor pairing, blank state, ψ, φ, U, isometry, two cloning identities — **all QM-side data** | "the carried `U` arises as the projective-action lift of a measure-preserving π-equivariant flow on `Σ × Σ`" |
| `CSDUnitaryBundle` | `Empirical/CSD/Gates/Framework.lean` | `U : H_n → H_n`, `U_isometry` (inner-product preservation) — **only QM-side isometry** | "the carried unitary arises as the projective-action lift of a measure-preserving π-equivariant flow on `Σ^N`" |

In both cases, no field carries a `Σ`-side flow, no field asserts
`π`-equivariance, no field asserts measure-preservation. The CSD-side
ontic claim lives entirely in the docstring prose. A reader inspecting
`#check CSDCloningBundle` would see a Hilbert-space cloning data
structure plus an LF2 `Context`.

**Honest reading.** These bundles are QM-side data structures with a
CSD-namespace prefix. The "CSD-realisability" claim is not propositional.

**Discharge route.** Add real CSD-side fields (post-LF4) — e.g. a
`flow : Σ^N → Σ^N` with `flow_measure_preserving` and `flow_π_equivariant`
hypotheses whose composition under `π` projects to `U`. Until then,
each bundle's docstring carries the marker
**SCHEMA-MISMATCH: docstring claims CSD-side content the type does not carry.**

## 8. Decorative bundles (third-pass audit, 2026-05-22)

A **decorative bundle** is one quantified over in a theorem statement
(`¬ ∃ b : Bundle, ...`, or `(b : Bundle) → ...`) whose load-bearing
fields are **not consumed** in the theorem's proof. The bundle's
existence in the theorem statement adds syntactic weight without
adding proof obligations the bundle's content discharges.

| Bundle | Headline theorem | Fields used in proof | Fields tagged load-bearing but unused |
|---|---|---|---|
| `CSDGHZAssignmentBundle` | `no_csd_ghz_lhv_bundle` | **none** (bundle destructured as `⟨_, λ, ...⟩` and discarded) | `partition_pairwise_null`, `partition_cover_null` |
| `CSDKSAssignmentBundle` | `no_csd_ks_assignment_bundle` | only `bases_eq` (trivial rewrite to align with QM-side `cabelloBasis`) | `partition_pairwise_null`, `partition_cover_null` |

In the GHZ case the bundle is completely decorative: the headline
`¬ ∃ (b : Bundle) (λ : ...), MerminConstraints λ` is provably equivalent
to the QM-side `¬ ∃ λ, MerminConstraints λ` wrapped in a vacuous
quantifier, because the proof never touches `b`. In the KS case, the
proof uses `b.bases_eq` (bookkeeping) but the `partition_*` fields
are inert.

The bundle docstrings honestly state "the `partition_*` fields are
not used in the proof but are load-bearing for the *interpretation*
of the bundle". The third-pass audit insists this is not the same as
load-bearing for the *theorem*: an interpretive role does not constrain
the proof obligation.

**Honest reading.** The headline theorems' bundle quantifiers are
dead weight in the propositions Lean checks. The CSD-side reading of
GHZ and KS is, propositionally, the QM-side reading. The bundles
*describe* an interpretation; they don't *prove* anything about it.

**Discharge route.** Either (a) restate each theorem to actually
consume the `partition_*` fields in its proof body — e.g. derive the
combinatorial contradiction *via* the per-cell `prepMeasure` mass
discipline rather than around it — or (b) drop the bundle from the
theorem statement and cite the QM-side theorem with an explicit
prose-only CSD interpretation. Each decorative bundle's docstring
carries the marker
**DECORATIVE BUNDLE: load-bearing fields not consumed in any theorem.**

## 9. Packaging theorems sold as headlines (third-pass audit, 2026-05-22)

A **packaging theorem** is one whose entire proof body is an
anonymous-record `⟨conjunct1, conjunct2, ..., conjunctN⟩` over already-
exported separate theorems. The packaging adds zero new content; it
provides a labelled handle on existing material.

| Theorem | File | Conjuncts | New content |
|---|---|---|---|
| `LF3_main_theorem` | `LF3/Interface.lean` | 8 (kernel, correlation, A-marginal, B-marginal, no-signalling A, no-signalling B, pointer-completeness A, pointer-completeness B) | **zero** — all eight are exported separately as `context_singlet_kernel`, `context_correlation_eq_neg_dot`, `context_marginal_a`, `context_marginal_b`, `no_signalling_strong_readout_a`, `no_signalling_strong_readout_b`, `pointer_a_complete`, `pointer_b_complete` |
| `LF3_finite_leakage_theorem` | `LF3/Interface.lean` | 4 (sector probability, correlation, A-marginal, B-marginal deviation bounds) | **zero** — all four are exported separately as `singlet_pointer_probability_finite_leakage`, `correlation_finite_leakage_bound`, `marginal_a_finite_leakage_bound`, `marginal_b_finite_leakage_bound` |

These are not placeholders (the conjuncts are real theorems with real
proofs) but they are **packagings sold as headlines**. The "main
theorem" label oversells.

**Honest reading.** The headlines are tables-of-contents. Each
conjunct does load-bearing work; the headline composing them does not.

**Discharge route.** Either rename to `*_package` / `*_strong_readout_package`
or keep the names but add explicit `**PACKAGING-ONLY**` markers
disclosing that no proof content is added beyond the conjunction.

## 10. Hypothesis-does-the-work theorems (third-pass audit, 2026-05-22)

A **hypothesis-does-the-work** theorem `(h : P) → Q` is one where `h`
is a strong hypothesis essentially equivalent to `Q` (or its key
content) and the proof body simply unpacks `h`. Such a theorem is
*Lean-honest* if and only if `h` is explicitly catalogued as a
load-bearing obligation.

| Theorem | File | Load-bearing hypothesis | Catalogued in |
|---|---|---|---|
| `LF3_singlet_frequency_convergence_born_inner` | `LF3/Interface.lean` | `prep.jed.born_eq_P_st : ‖⟨ψ, eig s t⟩‖² = P_st` (a field of `MeasurementJointEig`) | `BRIDGE-OBLIGATIONS.md §2.1` (LF4-todo §2 + §7) |

The theorem composes `LF3_singlet_frequency_convergence` (which gives
convergence to `P_st`) with a rewrite via `prep.jed.born_eq_P_st`, so
the conclusion `Tendsto … (‖⟨ψ, eig s t⟩‖²)` is *equivalent* to the
pre-Born conclusion under the bundled identity. The Born identity is
the entire content of the rewrite step.

The disclosure already lives in the existing docstring + the
`BRIDGE-OBLIGATIONS.md` ledger. The third-pass audit adds a uniform
**HYPOTHESIS-DOES-THE-WORK** marker for consistency with §7-9.

## 11. Stale docstrings (caught by the 2026-05-22 second-pass audit)

Two files were carrying docstring text that claimed work was **deferred**
when the work had actually been completed in the same commit that
introduced the docstring. These are not placeholders — they are
misleading docstrings in the *opposite* direction (under-claiming
rather than over-claiming). Fixed in the same commit as this §6 was
added.

| File | Stale claim | Reality |
|---|---|---|
| `Empirical/QM/Bell.lean` | "The QM-application lift is deferred: it requires either Mathlib's `tsirelson_inequality` (currently blocked …) or the direct K-T construction. Neither is in scope for this commit." | `chsh_qm_tsirelson_bound` (further down in the same file) **does** discharge the construction by hand via four auxiliary lemmas (`sigmaDotLeft_sq`, `sigmaDotLeft_isHermitian`, `sigmaDotLeft_mul_sigmaDotRight`, and analogues on the right). The docstring was written before the lift was completed and never updated. |
| `Empirical/QM/Contextuality/KS18.lean` | Six separate mentions claiming "Lean formalisation [of the orthogonality verification] is deferred to a follow-up", "geometric verification is deferred to a future revision", etc. | `cabello_pairwise_orthogonal_in_basis` (in the same file's "Vector data + orthogonality verification" section) **does** verify pairwise orthogonality via a 144-case `fin_cases` + `norm_num` sweep. The docstring was written before this section was added and never updated. |

**Why this section exists.** A docstring that under-claims the file's
content is as much of an audit failure as a placeholder Prop is — the
reader's mental model of what is and isn't proved becomes wrong in
either direction. Future placeholder audits should grep for `deferred`
across the corpus and verify each occurrence either (a) cites
specific load-bearing missing content with an LF4-todo number, or
(b) describes legitimate external scope (e.g., upstreaming to Mathlib,
post-LF4 tripartite chain construction).

## 12. Discharge protocol

When a placeholder is discharged:

1. Replace the Prop definition / tautology with a real theorem statement
   and proof.
2. Remove the `PLACEHOLDER` / `TAUTOLOGY` docstring marker.
3. Remove the `-- TODO` comment.
4. Move the row in §1 / §2 above to a "Discharged" section (to be
   added on first discharge) with the commit hash.
5. If the discharge satisfies a `BRIDGE-OBLIGATIONS.md` row, update
   that row too.
