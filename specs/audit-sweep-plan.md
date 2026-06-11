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
| 1. Mathlib staging | `CsdLean4/Mathlib/**` | not started |
| 2. LF2/LF3 support | `LF2/**`, `LF3/**` | not started |
| 3. LF4 non-headline | `LF4/**` (non-capstone) | not started |
| 4. Empirical support + bridges | `Empirical/**` | not started |
| 5. LF1 | `LF1/**` | not started |

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
