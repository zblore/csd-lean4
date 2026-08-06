> ⚠️ HISTORICAL — layer complete; frozen execution log. Open items live in [BACKLOG.md](BACKLOG.md).
# Audit sweep — extend the adversarial audit below the Tier-A headlines

Added 2026-06-10. **Status: planned, not started.**

## Motivation

The standing verification discipline audits each tranche's **Tier-A headlines** (the
named capstone theorems) via the independent referee pass (csd-lean-auditor):
vacuity, hallucinated/weakened statements, axiom drift, coverage gaps. That pass
reads supporting material only as far as the headline's soundness requires. The
**Tier-B-and-below strata** — supporting lemmas, infrastructure modules, the Cat-1
`Mathlib/` staging tree, bridge bundles, definitional packaging — have never had a
*dedicated* adversarial pass of their own. Risks living there:

- a supporting lemma whose name/docstring claims more than its statement (latent
  over-claim that a future tranche cites at face value);
- definitional packaging that does not mean what it is named (the auditor's
  "definition drift" class), invisible while only headlines are checked;
- Cat-1 staging files diverging from Mathlib standards before upstreaming;
- structure-field hypotheses that are satisfiable-but-never-instantiated
  (vacuity one level below the pinned theorems);
- docstring honesty drift in modules last touched several tranches ago.

## Scope and method

Run csd-lean-auditor as a **per-module gap sweep** (its second designed use), not
per-theorem. Sweep order by downstream load:

1. `CsdLean4/Mathlib/` staging tree (highest reuse; upstream-facing standards);
2. `LF2/` + `LF3/` supporting strata (oldest, most cited by later layers);
3. `LF4/` non-headline modules (the moment-map cluster's helper lemmas);
4. `Empirical/` non-headline support + the `CSD/` bridge bundles (cross-check
   against `BRIDGE-OBLIGATIONS.md`);
5. `LF1/` (smallest risk; audited implicitly by every chain consumer).

Each sweep produces a findings report (severity-tagged, exact locations); repairs
land via the standard expert→auditor→commit loop, doc-currency rule applies.
Findings that are honest-scope notes (not defects) get docstring fixes only.

## Definition of done

Every module under `CsdLean4/` has either (a) a Tier-A audit on its headlines from
its landing tranche **and** a module-level sweep entry here, or (b) an explicit
skip rationale recorded here. This file carries the running ledger:

| Sweep | Modules | Status |
|---|---|---|
| 1. Mathlib staging | `CsdLean4/Mathlib/**` | **DONE 2026-06-15 — SOUND** (3 sub-sweeps: Projectivization, QuantumInfo, matrix/measure/prob) |
| 2. LF2/LF3 support | `LF2/**`, `LF3/**` | **DONE 2026-06-15 — SOUND** (2 sub-sweeps) |
| 3. LF4 non-headline | `LF4/**` (non-capstone) | **DONE 2026-06-15 — SOUND** (3 sub-sweeps: moment/Born-volume, spectral/observables, instances/POVM/singlet) |
| 4. Empirical support + bridges | `Empirical/**` | **DONE 2026-06-15 — SOUND** (2 sub-sweeps: QM 30 files, CSD 35 files) |
| 5. LF1 | `LF1/**` | **DONE 2026-06-15 — SOUND** |

**SWEEP COMPLETE 2026-06-15. The entire corpus below the Tier-A headlines (167
files, 12 sub-sweeps) is adversarially audited SOUND — zero BLOCKER, zero MAJOR.**
Every layer's non-vacuity load-bearers were independently probed (Shor ≥½, Grover,
GHZ/KS no-go non-vacuity; the moment-map/DH volume chain genuinely *derived* not
carved; the POVM Naimark dilation; the i.i.d. trial witness; LF1's SLLN and the
`hΦ_pres`-only-measurability disclosure). The carving-honesty line (Tier-2: realise
vs derive) is disclosed correctly throughout; no carved region is sold as a
derivation; every Empirical/CSD transport bundle is labelled and ledgered.

### Sweep 1+2 findings (2026-06-15) — all MINOR/NIT, zero BLOCKER/MAJOR

Every audited module is mathematically SOUND: all headlines foundational-triple-only,
`busch_effect_gleason` confined to the LF2 operational stratum (LF3 capstones independently
verified Busch-free), the load-bearing `IIDCoordinateProcess` confirmed to genuinely inhabit
the trial bundle (joint independence, degenerate-`μ` rejected, exact `hindep` shape), every
LF2/LF3 structure non-vacuously inhabited and meaning its name. Findings were all
docstring-honesty drift or upstream-bar hygiene.

**Fixed this pass (docstring/comment honesty):**
- Stale "realises the LF2 `invariant_measure_uniqueness` axiom" framing (removed 2026-06-04):
  `Mathlib/.../Projectivization/Unitary.lean`, `FubiniStudyUnique.lean`.
- Stale Busch-mediated chain description (capstones are Busch-free via `_direct` since
  2026-06-02): `LF3/Interface.lean` (architecture block + chain diagram).
- `born_eq_P_st` over-described as undischarged — it is **proved in-corpus** for the singlet
  (`Singlet.JointEig.singletJointEig_born`); only the `Fin 2×2 → Fin N` re-index is deferred:
  `LF3/SingletProjective.lean`, `BRIDGE-OBLIGATIONS.md §2.1`.
- `Channel.lean` CP claim softened (CP justified-but-not-formalised; no consumer needs it).
- `PartialTrace.lean` "arbitrary local CPTP map" → "trace-preserving Kraus family" (TP is the
  load-bearing hypothesis; CP unused in the proof).
- `LF2/MeasureBridge.lean` docstring named removed `epAction`/`onticAction` maps → `(g • ·)`.
- `Tests/AxiomAudit.lean` stale "(Data-processing deferred)" comment → DP closed (pinned below).

**Deferred to upstream-prep (Cat-1 staging hygiene; not fixed — logged for the eventual
Mathlib PR, no soundness impact):** `Register.lean` two deprecated-API uses
(`EuclideanSpace.single_apply`/`norm_single` → `PiLp.*`); `WignerRigidity.lean` dead `hf`
on the `imageVec` family (2 linter warnings; file is the §13-paused crux, left untouched);
blanket `set_option linter.unusedSectionVars false` in `Stinespring`/`CanonicalChannels`/
`PartialTrace` (prefer `omit … in`); `@[simp]` on a few `_def`/projection unfolders
(`Channel.apply_def`/`adjoint_def`, `PartialTrace.traceRight/Left_apply`,
`EffectAux.scaledRankOneEffect_M`); `Lp/Matrix.lean` `ofLp_toEuclideanLin` unpinned.

### Sweep 3+4+5 findings (2026-06-15) — all MINOR/NIT, zero BLOCKER/MAJOR

LF4 (3 sub-sweeps), Empirical QM+CSD (2), LF1 (1): all SOUND. Sweep 3a confirmed the
carving-honesty line is correct — the general-N Born = FS-volume chain is a genuine
*derivation* (cells are `replaceMap`/`apexLin` geometric images; FS measure computed through
the proved DH law `fs_moment_joint_dirichlet_N`, not asserted; the `_uncond` zero-branch
genuinely *derives* FS-measure-0). Sweep 3c confirmed the bridges (`cp/k_measure_bridge`)
non-degenerate (`c=1` between probability measures) and `ofKählerPreparation`'s `bridge_op_p`
an honest *carved realisation* with a non-circular RHS. Sweep 4a/4b confirmed Shor/Grover/GHZ
non-vacuity, the volume series lands the right Born values, and every CSD transport bundle is
labelled + ledgered. Sweep 5 confirmed LF1's `hΦ_pres`-only-measurability disclosure and the
genuine SLLN.

**Fixed this pass (docstring/comment honesty):**
- `DuistermaatHeckman.lean` header rewritten as a tombstone (present-tense "axiom" prose →
  past-tense; the DH fact was discharged to a theorem 2026-05-31).
- `GaussianFS.lean` stale "Blocker note (next step)" → RESOLVED (the ℝ-isometry route landed
  in `GaussianCPN.lean`).
- `Instance.lean` reference to the removed `invariant_measure_uniqueness` axiom → corrected
  (the non-trivial-fibre instance builds its bridge axiom-free via the product marginal).
- `SingletKahler.lean` stale "cites busch_effect_gleason via the LF3 chain" (×2: module +
  `ofKählerPreparation_singlet_frequency_convergence`) → Busch-free via the `_direct` re-route.
- `ObservableFlow.lean` over-claim softened: the `Φ ≠ id` claim is true but not separately
  witnessed (unlike `kFlow`'s `kFlow_ne_id`); the "LF5 frontier remaining" framing updated
  (LF5 single-system projective tier is now built).
- `NoCommunication.lean` stale "E3b deferred" → reduced-density form now proved.
- `MerminPeres.lean` stale "deferred to a follow-up tranche" → the R0..C2 identities are proved.
- `E91.lean` "device-independent security" → "certification (correlation level)" + honest-scope
  note (no key-rate / finite-key analysis).
- `Gates/{TwoQubit,MultiQubit}.lean` "unitarity" → "involutivity" (only `G*G=1` proved; `Gᴴ*G=1`
  holds by Hermiticity but is not separately stated).
- `QEC/{ThreeQubit,PhaseFlip}.lean` capstone docstrings clarified: the capstone bundles
  stabiliser-fixing + self-inverse recovery; the distinct-syndrome *identifiability* is the
  separate `syndrome_*` lemmas (read together for the full claim).
- `LF1/Indicators.lean` forward-reference to `T.trialMeasure` (defined downstream) clarified.

**Follow-up content tranches — DONE 2026-06-15.** The three "strengthen the witness"
items the auditors offered are now proved theorems (and the corresponding sweep docstring
caveats reverted in the same change):

1. `obsFlow_ne_id` (`LF4/ObservableFlow.lean`): the `Φ ≠ id` claim is now separately
   witnessed, mirroring `kFlow_ne_id`. Because `obsFlow` is a *diagonal phase* flow every
   computational-basis ray is a fixed eigenvector, so the witness is the **superposition**
   `|0⟩+|1⟩` ray (`obsWitnessVec`), moved by the distinct phases `1`, `-1` at
   `obsLamWitness`/`obsTWitness` (`= π`). Foundational-triple-only, AxiomAudit-pinned.
2. QEC identifiability: `errorSyndrome`/`errorSyndromePF : Fin 4 → ℂ × ℂ` +
   `three_qubit_syndromes_distinct` / `three_qubit_phaseflip_syndromes_distinct`
   (`Function.Injective`, the four `{±1}²` pairs distinct) + eigen-equation bundles
   (`three_qubit_syndrome_eigenstates`, `..._phaseflip_...`). The identifiability conjunct
   `Function.Injective errorSyndrome[PF]` is now **inside** both `three_qubit_corrects_*`
   capstones (and the CSD bridge `csd_three_qubit_corrects_single_bitflip`). Capstone names
   preserved; pins still fire.
3. Gate unitarity: `qm{CNOT,SWAP,CZ}_unitary` (TwoQubit) and `qm{Toffoli,Fredkin}_unitary`
   (MultiQubit), each `Gᴴ * G = 1` via a proved Hermiticity lemma `qmG_hermitian` (`Gᴴ = G`,
   genuine — CZ has a real `-1` diagonal entry) composed with the existing involutivity.
   AxiomAudit-pinned.

Both build targets green; all new theorems foundational-triple-only.

**Remaining sweep-1+2 upstream-prep hygiene (not done; out of scope):** deprecated API,
blanket linter disables, `@[simp]` unfolders, naming `PsiN`/`Tpi`,
`ObservableFlow.lean` deprecated `toEuclideanLin_apply`. None affect soundness.

## External review intake: codex, 2026-06-11 (triaged same day)

Five findings, classified and dispositioned (fixes landed in the codex-response
commit; verification details in the session record):

1. **Empirical/CSD transport wrappers don't certify realisability (High).**
   *Classification: known-and-ledgered by design; no over-claim found.* All five
   named files (SternGerlach, NoCommunication, Teleportation, NoCloning, Hardy)
   were re-verified to carry the full discipline: "TRANSPORT-ONLY" /
   "Transported from" docstrings, "SCHEMA-MISMATCH" markers, "Status:
   load-bearing, externally supplied, undischarged" + LF4-todo refs, and
   BRIDGE-OBLIGATIONS.md / PLACEHOLDERS.md §7 ledger rows. The proposed rename
   is **declined** — the `csd_` prefix + transport labelling + ledger is the
   established discipline (the types are honest: the bundle argument is the
   structural realisability slot, deliberately undischarged until LF4-todo
   §13/§14). Sweep 4 of this plan remains the systematic follow-up.
2. **"Derived from Kähler geometry" stronger than the formalized contract
   (High).** *Classification: agreed as a documentation-precision gap; the
   theorems themselves are unaffected (they are about `fubiniStudyMeasure` /
   Haar measures and are machine-verified as stated).* Fixed: formalisation-
   boundary notes added to `LF4/KahlerInstance.lean` and `LF4/MomentMap.lean`
   module docstrings (the latter's stale "DH pushforward not yet proved" scope
   note also corrected — it was proved 2026-05-31/06-02 by the Gaussian route)
   and a once-stated boundary paragraph added to the README headline. The
   pre-existing `AXIOMS.md §3.1` already stated this boundary at the
   `OnticSetup.μL` level.
3. **Unconditional general-N/POVM claims not in the verified library (Medium).**
   *Classification: stale at review time* — the reviewed tree predates commits
   `ea66a09`/`e5e45ce` (2026-06-11): `LF4/BornRegionUncond.lean` is tracked,
   imported by the root, AxiomAudit-pinned (8 pins), and Tier-A audited SOUND.
   *Residual DONE 2026-06-11:* the hpos call-site migration is executed — all
   downstream consumers (`Empirical/CSD/ContextVolume`, `BellVolume`,
   `GHZVolume`, and the six POVM witnesses Trine/USD/SIC/SIC3/MUB3/QutritPOVM)
   now route through the `_uncond` engine with the engine-inherited genericity
   hypotheses (`hpos`, and the Bell/GHZ angle carve-outs `hθ`/`hΦ`) dropped
   from their statements; HardyVolume left as-is (hpos discharged internally,
   no statement cost). The original `hpos` forms remain in the LF4 engine with
   docstring cross-references to the `_uncond` forms.
   A terminology note: the corpus uses "unconditional"/"`_uncond`" in two
   senses (h_uniform-discharged, 2026-05-31; hpos-free, 2026-06-11) — keep the
   distinction explicit when writing docs (now recorded in
   `LF4/MomentUniform.lean`'s module docstring).
   *Follow-up DONE 2026-06-11 (auditor recommendation of the same day):* the
   formal i.i.d. trial witness landed — the canonical coordinate process
   (`Measure.infinitePi` of `fubiniStudyMeasure p₀`; `LF4/TrialWitness.lean` +
   Cat-1 `Mathlib/Probability/IIDCoordinateProcess.lean`) inhabits the trial
   bundle `(Ω, Pr, X, hX, hlaw, hindep)` corpus-wide;
   `born_frequency_convergence_N_canonical` and
   `measurement_flow_born_frequency_canonical` (`LF5/CapstoneCanonical.lean`)
   state the volume-frequency capstones with the bundle discharged,
   conclusions verbatim. AxiomAudit-pinned, foundational-triple-only.
   *Canonical coverage completed 2026-06-15:* the witness is now wired into
   **every** remaining volume-frequency headline, not just the three above.
   `povm_born_frequency_volume_canonical` (in `LF4/TrialWitness.lean`, kept there
   to respect the `POVMVolume → BornRegionUncond → TrialWitness` import
   direction) plus the fifteen Empirical/CSD headlines (Bell, GHZ, Hardy, Malus,
   the two Stern-Gerlach, Trine, USD, SIC, SIC3, MUB3, QutritPOVM, and the three
   Context forms) centralised in `Empirical/CSD/VolumeCanonical.lean`. Each is a
   bare term-mode application of its parent with the bundle discharged at
   `fsTrialMeasure`/`fsTrial`; conclusions verbatim, AxiomAudit-pinned,
   foundational-triple-only. The qubit moment-sublevel parents (Malus, SG) take
   their region family via a `Unit`-indexed family with measurability
   `(momentMap_measurable 0) measurableSet_Iic`; all others use
   `bornRegion_measurable_uncond`. No volume-frequency headline is left merely
   classically-satisfiable. (The `block_born_frequency_volume` sum form is
   superseded by `block_born_frequency_volume_event_canonical` for the canonical
   purpose; its own `_canonical` is intentionally omitted.)
4. **`CsdLean4.Basic` API invariant broken (Medium).** *Classification: agreed,
   genuine defect.* Fixed: `Basic.lean` now imports the root module `CsdLean4`
   (verified acyclic — nothing imports `Basic`), so the documented
   reachability invariant holds structurally and cannot drift again.
5. **Axiom-posture documentation contradictions (Medium).** *Classification:
   agreed, genuine doc-currency defects (pre-dating the 2026-06-08 sweep
   rule).* Fixed: AXIOMS.md §1 stale "capstones cite Busch" sentence (false
   since the 2026-06-02 re-route), AXIOMS.md §5 dead `measure_bridge` row,
   BRIDGE-OBLIGATIONS.md §2.2 reference to the deleted
   `MeasureBridgeData.ofSectorData`, EMPIRICAL.md + specs/INDEX.md "two
   standing axioms" (one since 2026-06-04), and LF4-todo §5's stale "count
   drop happens at §8" pickup note.

## External review intake: codex, 2026-08-06 (triaged same day)

Source: `specs/FOUNDATIONAL-CODE-REVIEW.md` (full 443-module review, 12
cross-cutting findings F-01…F-12), with companion controls
`specs/VALIDATION-LEDGER.md` + `specs/validation-claims.tsv` (30 headline
claims), three new scripts (`check-module-coverage.sh`,
`check-validation-ledger.sh`, `check-semantic-mutations.sh`), and a `ci.yml`
edit. Headline: **no S4 findings** — no unsoundness, no trust escapes, no
syntactic `axiom`/`sorry`/`admit`; all S3s are claim-alignment
(prose/naming stronger than the proved type). The reviewer could not run
`lake build` (its sandbox had no network for the pinned toolchain) — a
sandbox artifact, not a repo defect. Every concrete claim below was
re-verified against the source on intake day.

1. **F-01 — LF2 bridge argument is type-level only (S3).**
   *Classification: verified accurate; known-and-documented by design;
   residual is one docstring over-claim + an open design decision.* The
   `let _ : MeasureBridgeData D μFS := bridge` binding in
   `OperationalPackage.fromPreparation` (`LF2/Preparation.lean`) is
   deliberate and documented (module docstring + 2026-06-04 history note;
   cf. 2026-06-11 intake item 5). Both-ways check: corpus-wide grep finds
   **no consumption site** of `bridge_eq` — only the field declaration and
   four axiom-free instance constructions (`SingletKahler`,
   `SingletKahlerFlow`, `KahlerWignerLift`, `Gates/WignerDischarge`).
   Residual over-claim: `born_rank_one_direct`'s docstring line "Symmetry
   enters via the `bridge` argument" asserts load-bearing status the term
   dependency does not support. Open decision (owner): drop the argument,
   or state a genuine transport theorem in which `bridge_eq` computes the
   projective probability from an ontic volume. Until decided, the current
   state is **pinned** by the reviewer's own
   `check-semantic-mutations.sh` guard (bridge accepted, not consumed;
   re-review trigger CL-003).
2. **F-02 — `effectProjFn` is the Born quadratic form by definition (S3).**
   *Classification: verified accurate; agreed as a documentation-precision
   gap (same genus as 2026-06-11 item 2); theorems unaffected.*
   `effectProjFn` is literally `RCLike.re (star v ⬝ᵥ E.M *ᵥ v)`
   (`LF2/EffectFn.lean:50`), so `born_rank_one_direct` is Dirac evaluation
   of an already-quadratic integrand — a representation/consistency layer.
   Action: reword the "volume-ratio foundational" phrasing in
   `EffectFn.lean`/`Preparation.lean` docstrings; reserve "Born from
   volume" for the LF4 engine (`MomentBornN`, `BornRegionUncond`,
   `born_frequency_convergence_N_uncond`), where a separately specified
   region's measure is genuinely computed.
3. **F-03 — LF4 Born regions are preparation-indexed (S3).**
   *Classification: verified accurate; known-and-ledgered — this IS the
   MD-1 frontier.* `bornRegion ψ` contains `ψ` by construction; the corpus
   already records this everywhere it matters (`FiniteQMClosure` docstring
   names MD-1 explicitly; `specs/reconstruction-status.md` A7 row;
   `specs/BACKLOG.md` MD-1; `specs/sigma-fibre-contextuality.md` for the
   `N ≥ 3` structure). Codex independently converged on the standing plan
   (`specs/record-layer-plan.md`): context-fixed readout as the
   measurement-facing API — done at the qubit (`qubitBorn` chain), parked
   at general `N` per the fibre-contextuality spec. No new action beyond
   the standing plan.
4. **F-04 — `KahlerOnticSetup` Prop fields don't force Kähler structure
   (S3).** *Classification: verified accurate at the type level;
   known-and-ledgered (`PLACEHOLDERS.md`, connectivity link L1); the
   interface-level weakness is real.* Both-ways check: the fields are
   labelled ABSTRACT PLACEHOLDER in the module's genuine-vs-placeholder
   ledger, and **no instance supplies `True`** — all supply the proved
   `IsFubiniStudyKahler N` core + `IsProbabilityMeasure`. But Codex's
   sharper point stands: consumers quantified over `KahlerOnticSetup`
   cannot extract those laws from `kahler_condition : IsKahlerSector`.
   Open decision (owner, fits the F1 library-grade pass): rename per Codex
   (`ProjectiveMeasureFlowSetup`) or replace the `Prop` pairs with the
   concrete pointwise-Kähler interface now that `IsFubiniStudyKahler`
   exists; the full strengthening waits on Mathlib exterior calculus.
5. **F-05 — Lüders behavior supplied by calibrated storage (S3).**
   *Classification: verified accurate; known-and-documented
   (`SwapLuders.lean` ⚠️ Scope: "The calibration is a context-fixed
   epistemic posit", A7-compatible, nullity forced by
   `no_exact_collapse`).* Codex's framing matches the module's own.
   Genuine new work item adopted: a **minimal calibration theorem**
   identifying which apparatus hypotheses are *equivalent* to Lüders
   behavior (candidate backlog row; S-size on the swap witness, where
   `swap_luders_marginal` already gives calibration ⇒ Lüders — the
   converse direction is the new content).
6. **F-06 — capstones bundle heterogeneous witnesses (S3).**
   *Classification: verified accurate; content known-and-documented
   (`FiniteQMClosure` docstring: "a concrete consistency witness, not a
   derivation"; `MeasurementCapstone` self-describes as an index); residual
   is naming.* Rename decision (witness/feature index vs. unified closure)
   deferred to the F1 library-grade pass; a genuinely unified closure
   (single arena/preparation/dynamics/measurement interface) is a
   legitimate L-size backlog candidate, not a doc fix. The
   `MeasurementCapstone` root omission is folded into F-07.
7. **F-07 — package-root and layer drift (S2).** *Classification: verified
   accurate — reproduced exactly; agreed, genuine hygiene defect.*
   Reproduction (intake day): 34 non-test modules unreachable from the
   default `CsdLean4` root (35 counting `Basic`, which is intentionally
   downstream per 2026-06-11 item 4) — concentrated in the newer
   SigmaLayer pointer/record tranche + `Empirical/CSD/Eraser*` +
   2 Mathlib support files; and exactly **16** reverse-layer imports incl.
   `LF2.MixedEnsembleIx → SigmaLayer.MixedEnsemble` and the named
   LF4/LF5/LF6 → Empirical edges. The union of the four declared roots
   does reach all 443 files (audit coverage intact), so the defect is
   consumer-root drift, not audit-coverage loss. Action: add the missing
   modules to the root (mechanical, S) and consider Codex's generated
   per-layer aggregates; move the generic Empirical/QM lemmas that
   SigmaLayer/LF4-6 consume down-layer when touched (cf. LF4-todo §10
   extraction discipline — reclassify on concrete consumer need, no bulk
   refactor).
8. **F-08 — SSA remains conditional on DPI (S3).** *Classification:
   verified accurate; known-and-documented; prose survey clean.*
   `strong_subadditivity_of_relEntropy_monotone` carries `hDPI`
   explicitly; the module documents the wall and the upstream
   `[LeanQIT2026]` discharge (cited, not imported). A prose sweep of
   README/INDEX/reconstruction-status/future-work found **no**
   unconditional "SSA proved" claim. The reviewer's mutation guard now
   pins the `hDPI` premise (CL-023). No action.
9. **F-09…F-11 — construction-vs-forcing recurrence; CV finite-cutoff;
   thermo finite-dimensional (S3/S2).** *Classification: agreed; standing
   corpus posture, no defect.* Witnesses prove consistency/realisability,
   not uniqueness — stated per-module (and proved honestly where it bites:
   `TypicalityForcing` shows the chosen flow is non-ergodic, reviewer
   verdict Pass S0). CV is finite-mode by design (QFT is outside the
   reality-scope ladder); thermo assumptions are explicit fields. Keep the
   per-module scope statements; no action.
10. **F-12 — proof-maintenance risk in very large files (S2).**
    *Classification: agreed — actionable hygiene, aligns with the adopted
    library-grade standard (CONVENTIONS §9) and the F1 Reversible API
    pass already gating B6.* Targets in size order: `WignerRigidity`
    (3,180 lines), `ShorRandomA`, `CuccaroModMul`, `MerminPeresVolume`,
    `ShorCore`, `Subadditivity`, `EffectGleason` (~1,400). The
    specialist-proof-pass recommendations coincide with
    `VALIDATION-LEDGER` CL-024/CL-005/CL-022. Fold into the F1 ratchet;
    no separate sweep.

**Reviewer-supplied controls, intake status:** the three new scripts were
re-verified logically (re-implemented independently on intake day: coverage
0 missing from the 4-root union; ledger 30/30 rows structurally valid;
mutation guards pass on the current tree — note they run Linux-only in CI
and are impractically slow under Git Bash on Windows). The `ci.yml` edit
wires them into the existing guard step and adds an advisory step for the
pre-existing vacuity/contradiction/review-surface scripts — both fine. ⚠️
It **also adds a `windows-latest` build matrix**, which roughly doubles CI
cost per push on the slowest runner class; this is a cost/benefit decision
for the owner and is left uncommitted pending that call.

**Open remainder:** per the BACKLOG-only rule, every action this intake
leaves open is tracked as `specs/BACKLOG.md` **§G (G1–G7)** — this section
records classification and verification evidence only, and is closed.

**Specialist audits (same day, 2026-08-06 — the three `specialist-review`
ledger claims, run as independent read-only deep audits, each verified
both ways on intake):** CL-005 `effect_gleason_representation` —
**VALIDATED-GRADE** (Busch 2003 hypothesis-by-hypothesis match; slightly
stronger than the reference — all `N`; proof arc standard at every stage
with boundedness legitimately replacing continuity; junk-value conventions
clean; isolation probe compiled). Residue fixed same day: four stale
AXIOMS.md §5 rows + related prose (the pre-discharge `busch_effect_gleason`
citations), direct AxiomAudit pin added. CL-024 `wigner_rigidity` —
**QUALIFIED** (no mathematical defect; hypothesis weaker than
Wigner/Bargmann — bijectivity derived; antiunitary branch compile-probe
forced at `N = 2`; up-to-phase uniqueness identified as the one substantive
undocumented omission → module scope note added same day; five
highest-risk tactic blocks named for the owner's hand pass, BACKLOG G11).
CL-022/CL-023 entropy chain — **Entropy.lean VALIDATED-GRADE;
Subadditivity/StrongSubadditivity QUALIFIED** (Klein's PD-σ hypothesis
strictly stronger than the literature support condition — sound direction,
counterexample-confirmed load-bearing; the ":624 every correlated ρ_AB"
docstring overclaim fixed same day; SSA reduction verified as exactly one
partial-trace DPI instance with correct Lieb–Ruskai index pattern;
repo-wide SSA wording sweep clean; committed non-vacuity witness
`Tests/EntropyWitness.lean` added). Ledger moves signed off by the author
same day: CL-005 → validated; CL-022, CL-023, CL-024 → qualified
(`specialist-review` count now 0).

**Resolution (same day, 2026-08-06 — decisions by the author, execution per
BACKLOG §G):** G1 resolved by the transport-theorem route
(`MeasureBridgeData.integral_comp_pi` +
`OperationalPackage.fromPreparation_liouville_apply` extensionally consume
`bridge_eq`; the over-claiming docstring line corrected; the mutation guard
now *requires* the transport theorems; CL-003 → qualified). G2 docstrings
reworded (representation layer vs LF4 Born-from-volume). G3 resolved by
tightening: `KahlerOnticSetup` now carries the concrete
`kahler_pointwise : IsFubiniStudyKahler N` and
`liouville_isProbability : IsProbabilityMeasure` fields (name kept; instances
unchanged in obligation; `liouville_isProbability` an instance). G4 landed:
`swap_luders_iff_calibrated` (post-marginal `= τ` ⟺ `ν i = τ`; CL-025
updated). G5 decided: names kept, rename on-touch (F3 class); unified
closure stays a listed candidate. G6 landed: 34 modules added to the
default root. G7 decided: `windows-latest` leg dropped, reviewer's script
wiring kept.
