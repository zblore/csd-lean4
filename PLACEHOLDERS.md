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

## 0. Kähler-sector posit — formalizable core DISCHARGED (manifold residual remains)

| File | Field | Status |
|---|---|---|
| `LF4/KahlerOnticSetup.lean` | `IsKahlerSector : Prop` + `kahler_condition` | **FORMALIZABLE CORE DISCHARGED 2026-07-19.** No longer `True`. Every `ℂℙ`-based instance now supplies `IsKahlerSector := IsFubiniStudyKahler N` — the pointwise Fubini–Study Kähler-compatibility triple (`g = re⟪·,·⟫`, `ω = im⟪·,·⟫`, `J = i•·`, with `J² = -1`, `ω = g∘J`, `g = ω∘J`, `ω` a `(1,1)`-form, `ω u (Ju) = ‖u‖²`), PROVED axiom-free (`isFubiniStudyKahler` / `Kahler.fubiniStudy_pointwise_kahler_compatibility`). Only the **manifold** residual remains interpretive: closedness `dω = 0` and the top-power identity `ω^{∧(N-1)}/(N-1)! = μ_FS` need exterior calculus absent from Mathlib. See `specs/connectivity-manifest.md` link L1. |

The companion field `IsLiouvilleKahlerVolume` carries its formalizable core — that
the Liouville measure is a *normalized* volume (probability measure) — on **all**
concrete instances now (`unitaryFlowSetup`, `manyToOneSetup`, and the trivial
witness `trivialKahlerOnticSetup`, all `IsProbabilityMeasure`); consumed by
`unitaryFlowSetup_liouville_isProbability`. The full "top-power Kähler volume
`ω^{∧n}/n!`" reading remains the same manifold residual as `IsKahlerSector`.

**No `:= True` placeholder fields remain in the corpus** (all four de-vacuumed
2026-07-19); `scripts/check-claims.sh` enforces that a new `:= True` anywhere is
flagged as a fresh vacuity regression.

## 1. Unproved Prop definitions

Eight Props, all in the Tranche 1 Tier A gate bridges, all sharing
the same LF4-todo §13.2 discharge route. Each Prop asserts:
"there exists a `CSDUnitaryBundle D N H_n` whose carried unitary `U`
equals the QM-side gate matrix's action."

**Partially discharged 2026-07-19:** the three single-qubit gate Props
(`hadamard_/phaseS_/phaseT_realisable_for`) are now PROVED on the concrete
`cpSectorData` (`Gates/SingleQubitDischarge.lean`) — each gate's action is a genuine
`CSDUnitaryBundle` whose `U_isometry` is *derived* from the gate lying in `U(2)`
(the sector-symmetry membership), modulo A5. Honest scope (`§7` below): the bundle
type carries `U` + `U_isometry` + a `Context`, not a Σ-flow, so this discharges the
Prop *as typed*, not the stronger Σ-flow-lift prose (the open D1 gap). The remaining
five (2-qubit CNOT/SWAP/CZ, multi-qubit Toffoli/Fredkin) and Bell-prep follow the same
pattern — each gate matrix is unitary — and are the mechanical continuation.

| File | Prop | LF4-todo | Status |
|---|---|---|---|
| `Empirical/CSD/Gates/SingleQubit.lean` | `hadamard_realisable_for` | §13.2 | **DISCHARGED 2026-07-19** on `cpSectorData` (`hadamard_realisable_cpSector`, `Gates/SingleQubitDischarge.lean`); modulo A5 |
| `Empirical/CSD/Gates/SingleQubit.lean` | `phaseS_realisable_for` | §13.2 | **DISCHARGED 2026-07-19** (`phaseS_realisable_cpSector`); modulo A5 |
| `Empirical/CSD/Gates/SingleQubit.lean` | `phaseT_realisable_for` | §13.2 | **DISCHARGED 2026-07-19** (`phaseT_realisable_cpSector`); modulo A5 |
| `Empirical/CSD/Gates/TwoQubit.lean` | `cnot_realisable_for` | §13.2 | **DISCHARGED 2026-07-19** (`cnot_realisable_cpSector`, `Gates/TwoQubitDischarge.lean`); modulo A5 |
| `Empirical/CSD/Gates/TwoQubit.lean` | `swap_realisable_for` | §13.2 | **DISCHARGED 2026-07-19** (`swap_realisable_cpSector`); modulo A5 |
| `Empirical/CSD/Gates/TwoQubit.lean` | `cz_realisable_for` | §13.2 | **DISCHARGED 2026-07-19** (`cz_realisable_cpSector`); modulo A5 |
| `Empirical/CSD/Gates/MultiQubit.lean` | `toffoli_realisable_for` | §13.2 | **DISCHARGED 2026-07-19** (`toffoli_realisable_cpSector`, `Gates/MultiQubitDischarge.lean`); modulo A5 |
| `Empirical/CSD/Gates/MultiQubit.lean` | `fredkin_realisable_for` | §13.2 | **DISCHARGED 2026-07-19** (`fredkin_realisable_cpSector`); modulo A5 |

Plus the composite **Bell-prep realisability**:

| File | Prop | LF4-todo | Status |
|---|---|---|---|
| `Empirical/CSD/Gates/BellPrep.lean` | `bell_prep_realisable_for` | §13.2 | **DISCHARGED 2026-07-19** (`bell_prep_realisable_cpSector`, `Gates/BellPrepDischarge.lean`) — the ninth and last gate Prop; modulo A5 |

**Each Prop carries:**

- A docstring marker `**PLACEHOLDER (Prop definition, not proved).**`.
- A `-- TODO(LF4 §13.2):` comment line immediately above the
  declaration body.
- A `See PLACEHOLDERS.md` cross-reference in the docstring.

## 2. Tautologies

| File | Theorem | Status | Replacement / discharge |
|---|---|---|---|
| `Empirical/QM/Gates/BellPrep.lean` | `qmBellPrep_factorisation` | definitional unfold (`qmBellPrepCircuit = qmCNOT * qmH_tensor_I`, where LHS is *defined* as RHS — reduces to `rfl`). Carried as a labelled handle for downstream consumers; the genuine empirical identity is the proved theorem below. | **DISCHARGED 2026-05-22**: `qmBellPrep_yields_phiplus` proves the genuine empirical identity `(toEuclideanLin qmBellPrepCircuit) qmKet00 = qmKetPhiPlus`. The factorisation `rfl`-theorem is retained as a labelled handle on the decomposition. |
| `Empirical/CSD/Gates/BellPrep.lean` | `csd_qmBellPrep_factorisation` | re-export of the QM-side definitional unfold | inherits the QM-side row above; **TRANSPORT-ONLY** per §3 |

The genuine identity `qmBellPrep_yields_phiplus` is pinned in
`AxiomAudit.lean` and cites only the foundational triple
`[propext, Classical.choice, Quot.sound]`.

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
rather than over-claiming). Fixed in the same commit as this §11 was
added. (Section numbering skips §6 — a pre-existing cosmetic gap; the
later sections keep their numbers because docstrings cross-reference
"PLACEHOLDERS.md §7"/§8 etc. by number.)

| File | Stale claim | Reality |
|---|---|---|
| `Empirical/QM/Bell.lean` | "The QM-application lift is deferred: it requires either Mathlib's `tsirelson_inequality` (currently blocked …) or the direct K-T construction. Neither is in scope for this commit." | `chsh_qm_tsirelson_bound` (further down in the same file) **does** discharge the construction by hand via four auxiliary lemmas (`sigmaDotLeft_sq`, `sigmaDotLeft_isHermitian`, `sigmaDotLeft_mul_sigmaDotRight`, and analogues on the right). The docstring was written before the lift was completed and never updated. |
| `Empirical/QM/Contextuality/KS18.lean` | Six separate mentions claiming "Lean formalisation [of the orthogonality verification] is deferred to a follow-up", "geometric verification is deferred to a future revision", etc. | **RESOLVED 2026-05-23**: docstring cleaned in an earlier housekeeping pass; current file has only 2 "deferred" mentions and neither concerns geometric verification (one is about file-level extraction to a future `Framework/` subtree, the other is about amplitude normalisation being scale-invariant). `cabello_pairwise_orthogonal_in_basis` discharges the 144-case orthogonality sweep. Original under-claim is fixed; entry retained as historical record. |

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
