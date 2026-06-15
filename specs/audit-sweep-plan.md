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

**Deferred to follow-up content tranches (the auditors offered "strengthen the theorem"
alternatives; logged, not done — these add Lean content, out of a doc-currency sweep's
scope):** add `obsFlow_ne_id` (witness the `Φ ≠ id` claim, mirroring `kFlow_ne_id`); bundle
the `syndrome_*` distinctness into the QEC capstones (or formally designate the syndrome
lemmas the load-bearing export); add `Gᴴ * G = 1` unitarity lemmas for the gates. Plus the
sweep-1+2 upstream-prep hygiene list above (deprecated API, blanket linter disables, `@[simp]`
unfolders, naming `PsiN`/`Tpi`, `ObservableFlow.lean:78` deprecated `toEuclideanLin_apply`).
None affect soundness.

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
