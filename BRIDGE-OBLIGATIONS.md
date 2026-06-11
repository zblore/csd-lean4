# BRIDGE-OBLIGATIONS.md

Ledger of every load-bearing structural field across all
`CsdLean4/Empirical/CSD/` bridge files, with its `specs/LF4-todo.md`
cross-reference. Parallel to [`AXIOMS.md`](AXIOMS.md) (per-theorem
axiom audit) and [`PLACEHOLDERS.md`](PLACEHOLDERS.md) (claim-shaped
declarations without proofs); all three are managed under the same
discipline.

This file is the canonical record of every externally-supplied
hypothesis that CSD-side bridge bundles carry pre-LF4. The intent is
intellectual honesty: a reader should be able to see, in one place,
exactly what the `Empirical/CSD/` content is and is not claiming.

## 1. Discipline (mandatory for all `Empirical/CSD/` files)

Three rules, per `specs/empirical-csd-bridge-plan.md` §5:

### 1.1 Status-marker template

Every Bridge field that is an LF4 discharge target carries:

- A dedicated docstring marker
  `**Status: load-bearing, externally supplied, undischarged.**`.
- A one-line cross-reference to a numbered item in `specs/LF4-todo.md`.

Working example: `CsdLean4/LF3/PurePreparation.lean`'s
`PureSingletPreparation.bridge_op_p` cites LF4-todo §2 + §7. This
template is mandatory for every new Bridge field.

### 1.2 No-new-obligations-without-LF4-todo-PR

New Bridge files **cannot** introduce LF4 obligations not already in
`specs/LF4-todo.md`. If a new file needs a new obligation:

1. Add the obligation to `LF4-todo.md` in a separate PR, with explicit
   justification.
2. **Then** land the Bridge file referencing the new obligation.

Prevents Bridge accretion from quietly expanding LF4 scope.

### 1.3 Ledger audit per release

This file (`BRIDGE-OBLIGATIONS.md`) is updated in the same commit as
any change to a Bridge bundle field or LF4-todo item. Audit the ledger
for drift cross-Bridge-file at each release tag.

## 2. Current load-bearing fields

### 2.1 LF3 singlet bundle (pre-existing, since 2026-05-18)

Used by `Empirical/CSD/Bell.lean` (and `Empirical/QM/Bell.lean` via
the LF3 chain capstones it re-exports).

| Bundle | Field | What it asserts | LF4-todo |
|---|---|---|---|
| `LF3.PureSingletPreparation` | `bridge_op_p` | `∀ s t, μψ((O_region s t).preEvent) = ENNReal.ofReal (OP.p (rankOneEffect (jed.eig s t)))` (posited-fibre-law form, 2026-05-25; was `prepMeasure(...)`) | §2 + §7 |
| `LF3.MeasurementJointEig` | `born_eq_P_st` | `∀ s t, ‖inner ℂ ψ (eig s t)‖ ^ 2 = P_st ctx.a ctx.b s t` | §2 + §7 |

Both fields are carried inside `CsdLean4/LF3/PurePreparation.lean` and
`CsdLean4/LF3/SingletProjective.lean` respectively. They are
re-exported into the CSD-side bridge content via the chain capstone
re-exports in `CsdLean4/Empirical/CSD/Bell.lean`.

### 2.2 LF2 measure-bridge (pre-existing, since LF2 v1.00)

Used by `Empirical/CSD/Framework.lean`'s `Context` bundle.

| Bundle | Field | What it asserts | LF4-todo |
|---|---|---|---|
| `Empirical.CSDBridge.Context` | `bridge : LF2.MeasureBridgeData D μFS` | `π_*μL = c • μFS` + G-invariance, supplied as passive data | §8 (LF4 Kähler instantiation gives the concrete `SectorData`) |

Note (updated 2026-06-11): the former constructor
`LF2.MeasureBridgeData.ofSectorData` and the `invariant_measure_uniqueness`
axiom it cited were **removed 2026-06-04** (see `AXIOMS.md §2.1`). The
`bridge` field is now plain supplied data; the concrete LF4 instances
inhabit it **axiom-free** (`cp_measure_bridge` / `k_measure_bridge`).

### 2.3 CSD cloning bundle (added 2026-05-21)

Used by `Empirical/CSD/NoCloning.lean`.

| Bundle | Field | What it asserts | LF4-todo |
|---|---|---|---|
| `Empirical.CSDBridge.NoCloning.CSDCloningBundle` | (whole bundle's CSD-realisability content) | the Hilbert-space `U` carried by the bundle arises as the projective-action lift of a measure-preserving π-equivariant flow on `Σ × Σ`, for the bundle's `SectorData D`; equivalently, `U` is "CSD-substrate-realisable" | §13 |
| `Empirical.CSDBridge.NoDeleting.CSDDeletingBundle` | (whole bundle's CSD-realisability content) | same realisability content as the cloning bundle, applied to the deletion isometry (the logical dual; Pati-Braunstein 2000) | §13.3 |
| `Empirical.CSDBridge.QuantumMoney.CSDQuantumMoneyBundle` | (whole bundle's CSD-realisability content) | same realisability content as the cloning bundle, applied to a forging isometry for the Wiesner money states `|0⟩, |+⟩` (Wiesner 1983) | §13.1 |

Unlike `PureSingletPreparation.bridge_op_p` (which is a specific
field carrying a specific identity), the `CSDCloningBundle`
load-bearing content is implicit in the act of constructing the
bundle — callers asserting "this is a `CSDCloningBundle`" implicitly
commit to LF4-todo §13's realisability claim about the bundle's `U`
field. Pre-LF4 this is structural; post-LF4 it becomes provable from
the concrete Kähler `SectorData`.

The bundle does not carry a dedicated `csd_realisation : Prop` field
because the realisability is a property of the entire (`U`, ontic
substrate, tensor structure) combination rather than a localised
identity. A structurally vacuous `True`-typed field would be an
antipattern; the docstring on the structure carries the LF4-todo §13
citation directly.

### 2.3.1 CSD observable-correspondence bundle (added 2026-05-28)

Used by `Empirical/CSD/Uncertainty.lean`.

| Bundle | Field | What it asserts | LF4-todo |
|---|---|---|---|
| `Empirical.CSDBridge.Uncertainty.CSDUncertaintyBundle` | (whole bundle's CSD-realisability content) | The Hilbert state `ψ` arises as the lift of a CSD preparation `μψ`, and each self-adjoint observable `A, B` arises as the Hilbert lift of a measurable function `Σ → ℝ` with `⟨ψ, A ψ⟩ = ∫ A_ontic dμψ` (and likewise for `B`). | §14 (new) |

Distinct realisability content from §13: §13.x is about isometries
realised as Σ-flows; §14 is about self-adjoint operators realised
as measurable Σ-valued functions. One discharge does not subsume the
other.

| Bundle | Field | What it asserts | LF4-todo |
|---|---|---|---|
| `Empirical.CSDBridge.SternGerlach.CSDSternGerlachBundle` | (whole bundle's CSD-realisability content) | The spin-1/2 SG configuration -- prep `|+_z⟩`, measurements in the `Z` and `X` bases -- is realised through CSD's ontic substrate via the §14 observable correspondence applied to `σ_z` and `σ_x`. | §14 |
| `Empirical.CSDBridge.SuperdenseCoding.CSDSuperdenseCodingBundle` | (whole bundle's CSD-realisability content) | The three encoding unitaries `X⊗I`, `Z⊗I`, `XZ⊗I` on the 2-qubit space are realised as Σ²-flows (§13.2), and the four Bell-state projectors are realised via §14. | §13.2 + §14 |
| `Empirical.CSDBridge.MerminPeres.CSDMerminPeresBundle` | (whole bundle's CSD-realisability content) | The 9 two-qubit Pauli observables in the Mermin–Peres 3×3 grid are realised as measurable Σ→ℤ functions through §14, with the carried `lambda` representing the ontic values. | §14 |
| `Empirical.CSDBridge.Hardy.CSDHardyBundle` | (whole bundle's CSD-realisability content) | The four Alice/Bob Pauli observables (`A`, `A'`, `B`, `B'`) in the Hardy 9% paradox are realised via §14; the carried `p` represents the joint `μψ`-measure of outcome quadruples. | §14 |

The SG bundle is a **tag bundle** (no fields beyond `Context D`); its
existence is the realisability assertion. Same §14 discharge route
as the uncertainty bundle.

### 2.3.2 CSD Phase-E bridges (added 2026-06-04)

Used by `Empirical/CSD/{NoBroadcasting, NoCommunication,
Resources/Teleportation, Crypto/E91}.lean`. These close the CSD-branch
coverage of the QM Phase-E (quantum-information / cryptography) tests.
Each headline theorem reduces to its QM-side theorem by field
extraction (foundational-triple only); the realisability content reuses
the existing §13 / §14 obligations (no new LF4-todo entry, per rule §1.2).

| Bundle | Field | What it asserts | LF4-todo |
|---|---|---|---|
| `Empirical.CSDBridge.NoBroadcasting.CSDNoBroadcastingBundle` | (whole bundle's CSD-realisability content) | The bipartite density operator `ρ` (with pure first-factor marginal `|ψ⟩⟨ψ|`) is realised as a CSD bipartite state on `D`, its system-marginal reduction realising the pure `ψ`-sector. | §14 |
| `Empirical.CSDBridge.NoCommunication.CSDNoCommunicationBundle` | (whole bundle's CSD-realisability content) | Alice's local unitary `U ⊗ I` is realised as a measure-preserving π-equivariant flow on her factor (§13), and Bob's observable `Q` as a CSD observable (§14). | §13 + §14 |
| `Empirical.CSDBridge.Teleportation.CSDTeleportationBundle` | (whole bundle's CSD-realisability content) | The input qubit and shared `|Φ⁺⟩` resource are realised as CSD states (§14), and the four Pauli corrections as CSD-realised unitaries (§13). Branch-conditional (measurement collapse needs LF5, as on the QM side). | §13 + §14 |

The E91 bridge (`Empirical/CSD/Crypto/E91.lean`,
`Empirical.CSDBridge.E91.CSDLHVBundle` / `csd_lhv_chsh_bound`) carries
**no** load-bearing realisability field and appears in no row above, by
design: its LHV fields are deliberately *not* asserted to be
CSD-realisable. The content is the opposite — the CHSH bound `|S| ≤ 2`
certifies that a local-realist reading of the source cannot match CSD's
*derived* Tsirelson value (`Empirical/CSD/BellVolume.lean`). The
transport is a clean reduction with no externally-supplied ontic posit.

### 2.3.3 CSD three-qubit-code bundle (added 2026-06-04)

Used by `Empirical/CSD/QEC/ThreeQubit.lean`. The first QEC reading.

| Bundle | Field | What it asserts | LF4-todo |
|---|---|---|---|
| `Empirical.CSDBridge.QEC.CSDThreeQubitBundle` | (whole bundle's CSD-realisability content) | The three-qubit bit-flip code is realised on the substrate of `D`: the codespace is a sub-surface (`ℂℙ¹ ⊂ ℂℙ⁷`) of `Σ`; the physical error is **decoherence** — the system entangling with the environment, so its coherent volume flows out of `Σ_sys` into system–environment correlation (Liouville-conserved on the joint `Σ_sys × Σ_env`, the `hΦ_pres` field; the discretised Pauli errors are the QEC basis representation); the syndrome measurement reads the environment's record and re-concentrates the system; recovery is the unitary return to the codespace. The four syndrome weights are Fubini–Study volumes. | §13 + §14, **and load-bearingly CPTP channels** (`Σ_env` + joint flow + partial trace) plus the **dynamical-origin** (`Φ ≠ id`) layer. |

This is a **tag bundle** (no fields beyond `Context D`); `csd_three_qubit_corrects_single_bitflip` transports the QM-side (discretised) correction theorem by Context extraction. The realisability here is the most directly *dynamical and channel-dependent* of all the bridge obligations: the error model **is** a CPTP channel and the "volume loss" **is** its partial-trace step — so the honest ontic statement is gated on the (not-yet-built) channels keystone, not just on `Φ ≠ id`. No new LF4-todo entry (reuses §13/§14 + the open dynamical-origin question + the channels infrastructure tranche).

### 2.4 CSD Kochen-Specker assignment bundle (added 2026-05-21)

Used by `Empirical/CSD/Contextuality/KS18.lean`.

| Bundle | Field | What it asserts | LF4-todo |
|---|---|---|---|
| `Empirical.CSDBridge.KochenSpecker.CSDKSAssignmentBundle` | `partition_pairwise_null` | For each of the 9 Cabello bases B and each pair of distinct vectors v, w in B, `prepMeasure((O v).preEvent ∩ (O w).preEvent) = 0`. | §2 + §7 |
| `Empirical.CSDBridge.KochenSpecker.CSDKSAssignmentBundle` | `partition_cover_null` | For each basis B, `prepMeasure(univ \ ⋃ v ∈ B, (O v).preEvent) = 0` (the union covers Σ up to null). | §2 + §7 |

The two `partition_*` fields together encode per-basis measurable-
partition discipline of the 18 ontic outcome regions. They are
structurally identical to the per-sector partition content of
`LF3.PureSingletPreparation` (Bell uses a 2×2 sector decomposition;
KS uses a 4-cell partition repeated 9 times). Same discharge route:
LF4-todo §2 + §7 via the concrete Kähler `SectorData` and the
projective-first outcome construction.

The pairwise-null + cover-null formulation is used in place of
`LF2.MeasurablePartition` to avoid the `Finset (Fin 18) → Fin 4`
indexing friction that the canonical-partition type would require.
The combinatorial content is unchanged.

No new LF4-todo entry was needed for this retrofit (unlike NoCloning,
which required §13 for the ontic-isometry lift).

### 2.5 CSD GHZ LHV-assignment bundle (added 2026-05-21)

Used by `Empirical/CSD/Multipartite/GHZ.lean`.

| Bundle | Field | What it asserts | LF4-todo |
|---|---|---|---|
| `Empirical.CSDBridge.GHZ.CSDGHZAssignmentBundle` | `partition_pairwise_null` | For each (wing, axis) measurement, the two ±1-outcome regions on Σ have `prepMeasure`-null intersection. | §2 + §7 |
| `Empirical.CSDBridge.GHZ.CSDGHZAssignmentBundle` | `partition_cover_null` | For each (wing, axis), the two ±1-outcome regions cover Σ up to `prepMeasure`-null. | §2 + §7 |

Structurally identical to `CSDKSAssignmentBundle.partition_*` and
`LF3.PureSingletPreparation`'s per-sector content. Same discharge
route via LF4-todo §2 + §7 (concrete Kähler `SectorData` +
projective-first outcome construction).

The bundle is a 2-cell partition (over `Sign`) repeated 6 times
(over `Fin 3 × PauliAxis`), giving 12 outcome regions total. This
sits between Bell's 2×2 sector decomposition (4 regions) and KS's
4-cell partition repeated 9 times (18 regions) on the partition-
arity spectrum. The same LF4 discharge target covers all three.

No new LF4-todo entry needed for this retrofit. A tripartite LF3
chain (`LF3/Multipartite/GHZ/*`-style content paralleling
`LF3/Singlet/*`) is explicitly deferred as post-LF4 ambition; pre-LF4
the four `csd_ghz_expectation_*` are re-exports of the QM-side
Hilbert-Born content rather than per-sector frequency-convergence
claims.

### 2.6 CSD unitary bundle (Tranche 1 Tier A gates, added 2026-05-22)

Used by `Empirical/CSD/Gates/{Framework, SingleQubit, TwoQubit,
BellPrep, MultiQubit}.lean`.

| Bundle | Field | What it asserts | LF4-todo |
|---|---|---|---|
| `Empirical.CSDBridge.Gates.CSDUnitaryBundle` | `U_isometry` | For the carried Hilbert-space unitary `U : H_n → H_n` on the N-qubit space, inner-product preservation `∀ x y, ⟨U x, U y⟩ = ⟨x, y⟩`. | §13.2 |
| `Empirical.CSDBridge.Gates.CSDUnitaryBundle` | (bundle existence, no explicit field) | The carried unitary arises as the projective-action lift of a measure-preserving π-equivariant flow on `Σ^N` for the bundle's `SectorData D`. | §13.2 |

LF4-todo §13 was renamed and subdivided in this commit's change-set:
- §13.1 (existing): cloning case (tensor `Σ × Σ`); cited by
  `CSDCloningBundle.bridge_isometry`.
- §13.2 (new): general N-qubit case; cited by `CSDUnitaryBundle`.

Both subitems share a discharge route via §2 + §7 + §8 + the
symplectomorphism-lifts-to-unitary-up-to-phase lemma (standard for
compact Kähler manifolds with isometric group actions, not currently
in Mathlib at the abstract level).

Per-gate realisability claims (`hadamard_realisable_for`,
`cnot_realisable_for`, `toffoli_realisable_for`, etc.) instantiate
the same `CSDUnitaryBundle` at the appropriate gate matrix; they
do not carry separate LF4 obligations beyond §13.2.

**Honest reading.** The nine per-gate `*_realisable_for` Props are
**unproved claim-shaped placeholders** for the LF4-§13.2 obligation:
pre-LF4, no concrete `D` exists for which any of them is shown to
hold. They are catalogued in `PLACEHOLDERS.md §1` with explicit
TODO markers, and the BellPrep tautology + its CSD re-export are
catalogued in `PLACEHOLDERS.md §2`.

This is the first **positive-existence-conditional-on-LF4** polarity
in the architecture; the previous five bundles used negative-
existential (NoCloning, KS, GHZ) or positive-frequency-convergence
(Bell) polarities. See `specs/empirical-csd-bridge-plan.md` for the
four-polarity catalogue.

## 3. Pending bridge content (planned, not yet landed)

Per `specs/empirical-csd-bridge-plan.md` §4, the following bridge
files are planned but not yet written. Each will add new load-bearing
fields that must satisfy the §1 discipline. The expected obligations
are listed here for early visibility; the actual LF4-todo amendments
will be made in the respective landing PRs.

| File | Expected new bundle(s) | Anticipated load-bearing fields | Anticipated LF4-todo |
|---|---|---|---|
| ~~`Empirical/CSD/Multipartite/GHZ.lean`~~ | ~~`PureGHZPreparation`, `TripartiteJointEig`~~ | ~~`bridge_op_p` (tripartite), `born_eq_<sigma_x>_etc`~~ | **DONE 2026-05-21** (see §2.5 above; took the KS-template LHV-only path; no new LF4-todo entry; no new LF3 tripartite chain content). |
| ~~`Empirical/CSD/Contextuality/KS18.lean`~~ | ~~`KSAssignmentBundle`~~ | ~~per-basis ontic-weight ↔ OP.p bridge (9 of them)~~ | **DONE 2026-05-21** (see §2.4 above; no new LF4-todo entry needed, reuses §2 + §7). |
| ~~`Empirical/CSD/NoCloning.lean`~~ | ~~`CSDIsometryBundle`~~ | ~~π-equivariance of isometry candidate; non-existence target~~ | **DONE 2026-05-21** (see §2.3 above; LF4-todo §13 added in the same change-set per discipline rule §1.2). |

The third item (`NoCloning`) is the only one anticipated to require a
new LF4-todo entry. Per rule §1.2, that PR must add the LF4-todo entry
*first*, with justification.

## 4. Relation to `AXIOMS.md`

`AXIOMS.md` records what Lean's `#print axioms` reports for headline
theorems. This file (`BRIDGE-OBLIGATIONS.md`) records what
*structural fields* CSD-side bridge bundles carry as hypotheses.

The two are complementary:

- `AXIOMS.md` answers "what mathematical axioms does this theorem cite?"
- `BRIDGE-OBLIGATIONS.md` answers "what physical/ontological hypotheses
  does this bundle ask the caller to supply (pending LF4)?"

A Bridge bundle's structural field that ends up extensionally invoked
inside a `#guard_msgs`-audited theorem will eventually appear in
`AXIOMS.md`'s output (if it's load-bearing for the theorem) — but only
once LF4 discharges the field with concrete content. Pre-LF4, the
field shows up only here.
