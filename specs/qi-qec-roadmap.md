# QI / QEC roadmap and project-structure plan

Forward-looking roadmap for the quantum-information, quantum-error-correction, and
quantum-algorithm branches, plus the project-structure decision for where they live. Sits
alongside [`qm-empirical-tests.md`](qm-empirical-tests.md) (reproduce QM),
[`csd-departures-eft.md`](csd-departures-eft.md) (where CSD could *differ* from QM + the EFT
tower), and [`carve-out-plan.md`](carve-out-plan.md) (the D1 frontier). Created 2026-06-04.

## 0. Where the corpus is

The Empirical suite is broad on **single-shot, static QI**: the no-go cluster
(cloning / deleting / broadcasting / communication), entanglement-resource identities
(superdense, teleportation branches, Bell / Tsirelson), contextuality (KS, Mermin-Peres,
GHZ, Hardy), uncertainty, and a full POVM tranche (trine / USD / SIC + qutrit
unsharp / SIC / MUB) backed by the Born-as-Kähler-volume derivation. Every theorem is
foundational-triple, AxiomAudit-pinned.

What is essentially absent is the part of QI that needs machinery the corpus never built:
**entropy / information measures, distance / fidelity measures, and channels (CPTP maps)**,
plus the CSD-internal **measurement-update** step.

**Load-bearing observation.** The QI program and the deepest CSD frontier (**D1**, real
measurement dynamics on `Σ`; `Φ = id` in every concrete `SectorData` instance, though LF5
now exercises `Φ_vN ≠ id` on the dilated `Σ'` at the single-system projective tier, see
`carve-out-plan.md`) converge at channels and measurement update. More no-go / POVM examples are cheap and never touch
D1. Fidelity, CPTP, and the post-measurement state are exactly where ontic dynamics on `Σ`
would have to earn its keep. After the static layer, "do QI properly" and "attack D1" stop
being separate problems.

## 1. The four keystone gaps (ranked by downstream reach)

### K1 — density-operator entropy `S(ρ) = −Tr ρ log ρ`
Unblocks: Holevo bound, Schumacher compression, accessible information, entanglement
entropy, subadditivity / strong subadditivity, data-processing inequality, quantum
thermodynamics. *Mathlib:* matrix `log` via CFC exists; spectral entropy `∑ −λᵢ log λᵢ` is
assemblable; **concavity / Klein's inequality is not in Mathlib** and is the hard lemma.
Multi-week, Cat-1 (CSD-free, upstreamable). *CSD angle:* `S(ρ)` is the entropy of the
volume distribution the state induces on `Σ`.

### K2 — CPTP channels (Kraus / Choi / Stinespring)
Unblocks: general no-communication (CPTP form; today only unitary), channel capacities,
decoherence / open systems, **and all of QEC**. *Mathlib:* nothing direct, but the two
hard primitives already exist — `canonicalNaimark` (Stinespring for measurements) and
`PartialTrace`. A `Channel` type as "isometry into system⊗env then `traceRight`" reuses the
POVM-dilation code. *CSD angle:* a channel is the environment-averaged image of a
measure-preserving flow on `Σ × Σ_env`; **this is where `Φ ≠ id` first becomes mandatory**,
i.e. the concrete on-ramp to D1.

### K3 — fidelity / trace distance
Unblocks: the *full* no-broadcasting (BCFJS commuting-states iff; today only the
pure-marginal core `pure_marginal_confinement`), no-bit-commitment, approximate-cloning
bounds, channel discrimination, QEC fidelity. *Mathlib:* trace distance `‖ρ−σ‖₁/2` is
assemblable from the trace norm; Uhlmann fidelity needs operator `√` (matrix CFC `√` is
available) plus Uhlmann's theorem (not in Mathlib). Medium difficulty, Cat-1.

**K3 metric core DONE 2026-06-05** (`CsdLean4/Mathlib/QuantumInfo/TraceDistance.lean`):
`traceNorm` (= `∑|λᵢ|`) and `traceDist` (`½‖ρ−σ‖₁`) defined; non-negativity; the
**distinguishability headline** `traceDist ρ σ = 0 ↔ ρ = σ`; **symmetry** `traceDist_comm`
(via the functional-calculus bridge `traceNorm A = Re Tr(cfc |·| A)` + `cfc_comp_neg`, so
`traceNorm(−B) = traceNorm B`); `traceNorm_of_posSemidef` (trace norm of a state = its
trace). Foundational-triple-only, AxiomAudit-pinned.
**K3 metric COMPLETE 2026-06-08** — the **triangle inequality** `traceDist_triangle`
(`D(ρ,τ) ≤ D(ρ,σ) + D(σ,τ)`) landed, reduced to trace-norm subadditivity `traceNorm_add_le`.
Since Mathlib registers no Loewner order on matrices and `sgn`/the positive projector are
discontinuous, it was proved via the Jordan decomposition built from `Matrix.IsHermitian.cfc`
(defined for any `f`): named `posPart`/`negPart`/`posProj`, the PSD-product trace linchpin
`tr_psd_mul_nonneg` (`0 ≤ Re Tr(S·P)` for PSD `S,P`, via `√S = cfc √ S`), and the operator
bound `Re Tr(A·P) ≤ Re Tr(A₊)` for `0 ≤ P ≤ I`. Foundational-triple-only, AxiomAudit-pinned
(incl. the linchpin), Tier-A adversarially audited SOUND.
**K3 data-processing DONE 2026-06-09** (`DataProcessing.lean`, `channel_traceDist_le`):
`traceDist (Φρ) (Φσ) ≤ traceDist ρ σ` for a Kraus channel Φ and Hermitian equal-trace ρ,σ —
channels cannot increase distinguishability. Built via the **channel adjoint** `Φ.adjoint P =
∑ᵢ Kᵢᴴ P Kᵢ` (`Channel.adjoint`, with `adjoint_unital`/`adjoint_posSemidef`/`adjoint_le_one` ⟹
`0≤Φ†P≤I`, and the duality `adjoint_trace_mul : Tr(P·Φρ) = Tr(Φ†P·ρ)`) + the variational
identity `traceDist = Re Tr(posPart)` for traceless difference (no `sSup`: the max is realised
at `P = posProj(Φρ−Φσ)`, pushed through the adjoint to `Q = Φ†P` with `0≤Q≤I`, then the key
bound). Foundational-triple-only, AxiomAudit-pinned, Tier-A audited SOUND (strict-decrease
witness: a collapse channel sends `traceDist 1 ↦ 0`). **So K3 is COMPLETE** (metric +
data-processing). Gleason-free, Hilbert/operator side — does not touch D1/A5.
**K3 closers DONE 2026-06-09** (`DataProcessing.lean`): `traceDist_le_one` (states ⟹
`D ≤ 1`, tight at 1 for orthogonal pure states — the bounded `[0,1]` distinguishability range)
and `traceDist_conj_unitary` (`D(UρU†,UσU†) = D(ρ,σ)`, the equality case of data-processing,
via the unitary channel both ways). Both Tier-A audited SOUND. The K3 metric-properties set is
now closed; remaining QI keystones: K1 entropy, and K4 (the Lüders / outcome-conditioned
update specifically — note the LF5 *layer* itself is built: LF5-A..F landed 2026-06-09..15,
single-system projective measurement dynamics complete; what K4 still needs is the
outcome-*conditioned* update rule below).

### K4 — measurement update / Lüders rule `ρ ↦ ΠρΠ / Tr` (the one LF5 sub-piece still open)
Unblocks: BB84 / B92 disturbance security, teleportation *collapse* (today
branch-conditional only via `teleportation_branch_recovers_input`), and the entire
weak / sequential-measurement paradox family (Zeno, quantum eraser, three-box,
Cheshire cat — `qm-empirical-tests.md` §3.1 D1-D4). **CSD-structural, not just Mathlib:**
it is the ontic-conditioning step on `Σ` (conditioning a measure on an outcome region),
so doing it honestly is a sub-problem of **D1**. This is the **LF5 layer**.

## 2. QEC (uncovered; the most self-contained large tranche)

The QEC *core* is finite linear algebra over GF(2) and the Pauli group — not analysis — so
it builds largely in the QM-validity style with no new analytic infrastructure.

- **Q1. Stabilizer formalism** (tractable now): the `n`-qubit Pauli group, commuting
  stabilizer subgroups, codespace as a joint `+1` eigenspace, logical operators. Pure group
  theory + `Fin 2` linear algebra.
- **Q2. Concrete codes** (after Q1): 3-qubit bit-flip / phase-flip (the achievable first QEC
  theorem), then Shor [[9,1,3]], Steane [[7,1,3]], the [[5,1,3]] perfect code. Each is encode
  isometry + stabilizer generators + syndrome measurement (expressible as an existing POVM) +
  recovery.
- **Q3. Knill-Laflamme conditions** `PEᵢᴴEⱼP = cᵢⱼ P`: the exact error-correctability
  criterion. General statement needs K2; the projective version is reachable after Q1.
- **Q4. Threshold / fault tolerance**: far out (concatenation + probabilistic error models).

*CSD angle (worth thinking through before the Lean):* a code is a **constraint surface inside
the constraint surface** — the codespace is a sub-`ℂℙ` of `Σ`, and recovery is a flow
returning errored microstates to it. This is the most natural place in QI for the CSD
ontology to say something the Hilbert picture does not, because "correcting an error" is
literally a dynamics-on-`Σ` statement (and thus another D1 contact point).

## 3. Other branches not yet touched

**Algorithms and state-stabilisation are special**: they are the *operational faces of the
dynamics layer*. A quantum circuit is a designed measure-preserving flow `Φ` on `Σ`, and
stabilisation is the statement that a sub-surface of `Σ` is an attractor of `Φ`. Both
therefore *exercise* D1 rather than adding static examples — see §4.

- **Algorithms as designed flows.** The success probability is a Born weight, hence a
  Fubini–Study volume; the algorithm is the flow that concentrates the typicality measure
  onto the marked region (Grover's `O(√N)` speedup = the concentration rate). The first
  family of non-trivial, non-identity `Φ` with operational meaning. Deutsch–Jozsa is cheapest
  (one query); Grover next (iteration/angle analysis); QFT/Shor far out (roots of unity +
  modular arithmetic). The `n`-qubit tensor layer is shared with QEC — build once.
- **State stabilisation** (possibly the most CSD-natural topic in QI): decoherence-free
  subspaces = noise-flow-invariant sub-surfaces; dissipative preparation = engineering a
  target sub-surface as a global **attractor** (convergence rate = the flow's spectral gap);
  Zeno stabilisation = repeated measurement-conditioning (LF5); autonomous QEC = the
  codespace as a *stable* manifold. "A state is stabilised" is awkward in Hilbert language
  (a channel fixed point) but is the natural object in CSD (an attractor of `Φ`). Needs K2 +
  K4; it *is* D1 work with a control-theory face.

| Branch | Tractability | Note |
|---|---|---|
| Algorithms (Deutsch-Jozsa, Grover, QFT, Shor) | needs `n`-qubit + oracle infra | DJ / Grover reachable after a clean `n`-qubit tensor layer; QFT / Shor far out. INFRA-blocked in `qm-empirical-tests.md` §4. Operational face of D1 (above). |
| State stabilisation (DFS, dissipative prep, Zeno, autonomous QEC) | needs K2 + K4 | **most CSD-natural** — attractor sub-surfaces of `Φ`; entirely a dynamics statement (D1). |
| Open systems / decoherence (Lindblad, pointer states, einselection) | needs K2 | **CSD-central** — the classical-limit / measurement story; ties to D1 |
| Quantum metrology (Fisher info, Heisenberg limit, Cramér-Rao) | QFI-adjacent (K1) | self-contained mid-size tranche |
| Quantum thermodynamics (Landauer, Jarzynski, fluctuation thms) | needs K1 + K2 | Landauer connects entropy to the ontic measure directly |
| Contextuality as a resource (magic-state distillation) | extends KS / MP | natural upgrade of existing no-go results |
| Relativistic QI / entanglement in QFT (Unruh, Reeh-Schlieder) | out of finite-dim scope | but this is where CSD's gravity-via-entanglement ambition lives; long-horizon |
| Continuous-variable QI (Gaussian states) | different regime | `Σ = ℂℙ^{N−1}` is finite-dim; CV is a separate ontic model, likely out of scope |

## 4. Dependency picture and recommended order

```
        K1 entropy ──► Holevo, Schumacher, entanglement entropy, thermo
        K3 fidelity ──► full no-broadcasting, no-bit-commitment, channel disc.
K2 channels ──┬──► general no-communication (CPTP), decoherence / open systems
              └──► QEC (Q3 Knill-Laflamme), capacities
K4 LF5 ───────┬──► BB84 security, teleportation collapse
   (⊂ D1)     └──► weak-measurement paradoxes (Zeno, eraser, three-box)
Q1 stabilizer ──► Q2 codes (3-qubit → Shor / Steane / 5-qubit) ──► Q3
```

Recommended order (breadth at low risk, high foundational signal):

1. **Q1 + Q2 (3-qubit code)** — self-contained, no new analysis, a real QEC first, and the
   "code = sub-surface on `Σ`" reading is genuinely novel. Best effort / payoff ratio.
2. **K2 channels** — reuses `canonicalNaimark` + `PartialTrace`; unblocks the most downstream
   (open systems, general QEC, CPTP no-communication); concrete on-ramp to D1.
3. **K1 entropy** — keystone for quantum Shannon theory; biggest standalone build, enormous
   reach.
4. **K4 / LF5** — last on the QI side, because it is the D1 frontier wearing a QI hat; doing
   it well is doing foundational CSD.

**Do not** keep adding static no-go / POVM examples. Qubit and qutrit, projective and POVM,
symmetric and not, are all done; marginal foundational signal there is ~zero. The next real
information comes from the four keystones, three of which (K2, K1, K4) are exactly where the
instance-level `Φ = id` debt finally has to be paid (LF5 has begun this: `Φ_vN ≠ id` is
exercised on the dilated `Σ'`, but the concrete `SectorData` instances still carry `Φ = id`).

## 5. Project-structure decision

### 5.1 Principle: keep the two axes orthogonal

The corpus already has two orthogonal classification axes that must not be conflated:

- **Layer axis** (vertical): `LF1 → LF2 → LF3 → LF4 (→ LF5)` foundational ontic stack;
  Cat-1 staging in `CsdLean4/Mathlib/`; predictions in `CsdLean4/Empirical/`.
- **Interpretation axis** (the two-layer model, `qm-empirical-tests.md` §0.1):
  `Empirical/QM/` (QM-validity) vs `Empirical/CSD/` (CSD-ontic). **Load-bearing — do not
  disturb.**
- **Topic** is a *secondary* axis realised as subfolders *under both* QM and CSD
  (`Multipartite/`, `Contextuality/`, `Resources/`, `Crypto/`, `Gates/`).

So the answer to "separate folder for QEC / QI / algorithms, under QM or CSD?" is: **topics
are subfolders under BOTH `QM/` and `CSD/`; shared infrastructure is NOT under `Empirical/`
at all — it follows the three-category rule.**

### 5.2 Where each kind of new code goes

| Kind | Category | Location |
|---|---|---|
| QI infrastructure: `Channel`, `Entropy`, `Fidelity`, `PauliGroup`, `Stabilizer` (CSD-free, upstreamable) | **Cat-1** | `CsdLean4/Mathlib/` staging, natural Mathlib namespaces (as `PartialTrace` already is) |
| Measurement update (ontic conditioning on `Σ`) | foundational layer | **`CsdLean4/LF5/`** (new layer sibling to LF4); it is part of the ontic stack, not a prediction |
| QEC codes, Knill-Laflamme, algorithms, Holevo / Schumacher predictions — QM-validity form | Cat-3 (Cat-2-promotable) | `CsdLean4/Empirical/QM/{QEC,Algorithms,Shannon}/` |
| The CSD-ontic reading of each (code = sub-surface, channel = env-flow, …) | Cat-3 | `CsdLean4/Empirical/CSD/{QEC,Algorithms,Shannon}/` |

Resulting shape:

```
CsdLean4/
  LF1/ … LF4/                    foundational ontic stack
  LF5/                           NEW: measurement update (ontic conditioning; ⊂ D1)
  Mathlib/                       Cat-1 staging — EXPAND:
    …/Channel.lean, Entropy.lean, Fidelity.lean, Pauli.lean, Stabilizer.lean
  Empirical/
    QM/   …existing…  + QEC/  Algorithms/  Shannon/
    CSD/  …existing…  + QEC/  Algorithms/  Shannon/
```

### 5.3 Why not a top-level `QI/` or `QEC/` sibling

A top-level `QI/` or `QEC/` directory **siblings to `QM/` and `CSD/`** would conflate the
topic axis with the interpretation axis and break the two-layer invariant (every prediction
has a QM-validity form and a CSD-ontic form). QEC is a *topic*, not an *interpretation
layer*. A `QI/` *infrastructure* sibling to `LF4/` was considered but rejected in favour of
the existing Cat-1 `Mathlib/` staging convention: channels / entropy / fidelity / Pauli are
genuinely CSD-free and Mathlib-upstreamable, so they belong in the staging tree with natural
namespaces, exactly like `PartialTrace`. If a piece turns out CSD-coupled (Cat-2/3) it moves
out to the relevant `Empirical/` or `LF` location at that point.

### 5.4 Action when implemented

When the first of these tranches lands, reflect the new topic subfolders and the `LF5/`
layer in [`../CONVENTIONS.md`](../CONVENTIONS.md) (the namespace / category authority) and
add the new modules to the explicit import list in `CsdLean4.lean` and the AxiomAudit pins.
Update [`../EMPIRICAL.md`](../EMPIRICAL.md) (the per-test index) and
[`qm-empirical-tests.md`](qm-empirical-tests.md) §7.

## 6. First recommended tranche

**Q1 + Q2 (stabilizer formalism + the 3-qubit code).** The one substantial new branch that
needs no new analytic infrastructure, gives a real QEC theorem, and has the cleanest
CSD-ontic story (the codespace as a sub-surface of `Σ`, recovery as a flow). It also forces
the first design pass on the `n`-qubit Pauli infrastructure that algorithms will reuse.
