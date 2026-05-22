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

## 6. Discharge protocol

When a placeholder is discharged:

1. Replace the Prop definition / tautology with a real theorem statement
   and proof.
2. Remove the `PLACEHOLDER` / `TAUTOLOGY` docstring marker.
3. Remove the `-- TODO` comment.
4. Move the row in §1 / §2 above to a "Discharged" section (to be
   added on first discharge) with the commit hash.
5. If the discharge satisfies a `BRIDGE-OBLIGATIONS.md` row, update
   that row too.
