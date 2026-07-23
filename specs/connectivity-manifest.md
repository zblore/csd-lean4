# Connectivity manifest — what actually connects, end to end

**This file is the single source of truth for connectivity claims.** No document
in this repository (README, INDEX, module docstrings, commit messages) may assert
a stronger end-to-end connection than a row here marked **CONNECTED** with a named
backing theorem. `scripts/check-connectivity.sh` enforces the parts of this that
can be checked statically. Created 2026-07-07 after a provenance audit found the
top-level "one posited object yields both pillars" claim was **not** realized in
the code.

## The honest one-paragraph status

**(Updated 2026-07-15 — supersedes the 2026-07-07 "not realized" wording, which
predated fixes C1–C7 and the Σ-layer and contradicted the CONNECTED rows below.)**
The FORWARD chain is now realized end-to-end on genuine objects. A single genuine
`Φ ≠ id` Kähler sector supports BOTH pillars together — the Schrödinger form
(`H ≠ 0`) AND the Born frequencies from sampling its own Liouville measure — first
on `rotationSetup` (C4, L6) and, at GENERAL `N` with a genuine many-to-one
`π = Prod.fst` (`Σ = ℂℙ^{N-1} × T²`, fibres `= T²`), on `manyToOneSchrodingerSetup`
with arbitrary Hermitian `H` (C7, L8). The SigmaLayer (the projective-sector ontology, Paper C) (2026-07)
then puts isolated Hamiltonian dynamics AND de-isolating measurement AND
time-indexed records AND the Born content AND the conditional state update on ONE
ontic model `(Σ, μL, Φ, π)` — the unified capstone `unified_projectiveSector_capstone`
(L9). So "a single posited Kähler sector yields both pillars, and one ontic model
carries dynamics + measurement + records + Born + update" is CONNECTED. What
remains OPEN is the ONE deep link **L7 / SO-1** (the sector-origin problem): the
sector and its Born weights are POSITED — the trials SAMPLE `μL` i.i.d. — they are
NOT *derived from* a primitive ontology / deterministic flow. Everything CONNECTED is
FORWARD (it consumes the posited sector); closing SO-1 (deriving the sector from `Φ`)
is the research-grade frontier and is NOT claimed. (SO-1 is distinct from Paper C's
Axiom A5, the projectability / quantum-effective condition that *selects* the sector.) The Kähler-geometry fields (L1) now carry their genuine
pointwise/linear core (`IsKahlerSector := IsFubiniStudyKahler`, proved); only the
manifold residual (`dω = 0`, top-power volume identity) stays an interpretive posit
(no Mathlib exterior-calculus API).

## The intended chain and per-link status

Intended dependency chain:

```
Kähler geometry (ω, complex structure)
   → compact ontic Σ + Liouville measure
   → deterministic measure-preserving flow Φ on Σ
   → projected flow φ_t on ℂℙ^{N-1}   (via π, the descent equation `projectable`)
   → {  Born rule: frequencies → FS-volume = ‖⟨e_i,ψ⟩‖²  }
   → {  Schrödinger: φ_t = exp(-itH)·  on rays              }
```

| Link | Claim | Status | Backing theorem / the gap |
|---|---|---|---|
| **L1** | Kähler geometry `⇒` the sector's fields | **PARTIAL (2026-07-07 fix C5; pointwise Kähler core DISCHARGED 2026-07-19): both geometry fields now carry genuine formalizable content; only the manifold residual remains** | `IsLiouvilleKahlerVolume` carries the formalizable core — `μ_FS` is a *normalized* volume (probability measure) — CONSUMED by `unitaryFlowSetup_liouville_isProbability` (`LF4/NonTrivialSetup.lean`). `IsKahlerSector` is **no longer `True`**: every `ℂℙ`-based instance now supplies `IsKahlerSector := IsFubiniStudyKahler N` — the pointwise Fubini–Study Kähler-compatibility triple (`g = re⟪·,·⟫`, `ω = im⟪·,·⟫`, `J = i•·`, with `J² = -1`, `ω = g∘J`, `g = ω∘J`, `ω` a `(1,1)`-form, `ω u (Ju) = ‖u‖²`), PROVED axiom-free (`CSD.LF4.isFubiniStudyKahler` / `Kahler.fubiniStudy_pointwise_kahler_compatibility`, `Mathlib/Analysis/InnerProductSpace/KahlerForm.lean`). What stays unformalizable is only the **manifold** residual: closedness `dω = 0` and the top-power identity `ω^{∧(N-1)}/(N-1)! = μ_FS` need exterior calculus absent from Mathlib. |
| **L2** | Σ + `Φ` + `π` `⇒` a well-defined projected flow | **CONNECTED (interface) but see L4** | The descent field `projectable : π(Φ_t x) = φ_t(π x)` is a genuine field and is consumed by `CSD.LF4.sigmaFlow_schrodinger_form` (`LF4/PhaseLift.lean`). Enforced by `scripts/check-sector-linkage.sh`. |
| **L3** | projected flow `⇒` Schrödinger form | **CONNECTED (2026-07-07, fix C2)** | `CSD.LF4.rotationSetup_schrodinger_form` (`LF4/RotationSchrodinger.lean`) fires `sigmaFlow_schrodinger_form` on the genuine `Φ ≠ id` `rotationSetup`: the FS-isometry (unitary flow), coboundary (`b = 1`, trivial cocycle since `R(s+t) = R(s)R(t)`), and C¹ (`R'(τ) = R(τ)·J`) data are all discharged on a non-trivial flow, recovering `H = iJ = σ_y ≠ 0` (`rotationSetup_generator_ne_zero`). The first fully-instantiated `H ≠ 0` Schrödinger statement — no longer trivial-witness-only. **General-`N` (2026-07-19):** `CSD.LF4.manyToOneSchrodingerSetup_schrodinger_derived` (`LF4/ManyToOneSchrodingerDerived.lean`) exercises the same C¹-Stone derivation on the REAL family at general `N` with ARBITRARY Hermitian `H`: `schrodingerUnitary_hasDerivAt` discharges the smoothness datum `U' t = U t·(-iH)` (via `hasDerivAt_exp_smul_const` under the `C^*` L2-operator norm), and `CSD.StoneC1.eq_exp_of_hasDeriv` recovers `U t = exp(t•A)`, `A = -iH` — so the general-`N` `manyToOneSchrodingerSetup_schrodinger_form` (`rfl`) is backed by an actual derivation, not only the `N=2 σ_y` or `A=0` witnesses. AxiomAudit-pinned. |
| **L4** | a genuine `Φ ≠ id` `KahlerOnticSetup` inhabitant exists | **CONNECTED (2026-07-07, fix C1)** | `CSD.LF4.rotationSetup` (`LF4/NonTrivialSetup.lean`) is a `KahlerOnticSetup 2` whose projected flow is the `ℂℙ¹` rotation `R(t)`; `rotationSetup_projectedFlow_ne_id` proves `∃ t, projectedFlow t ≠ id` (at `t = π/2`, `[e₀] ↦ [e₁]`). The general constructor `unitaryFlowSetup N U p₀` builds one from any unitary family (measure-preserving via `fubiniStudyMeasure_smul_invariant`). NB: `kFlow` was the wrong tool — it translates a `T²` fibre and so acts trivially on rays (`projectedFlow = id`). |
| **L5** | sector `⇒` Born frequencies (structural) | **CONNECTED (structural, 2026-07-07, fix C4)** | `unitaryFlowSetup_born_frequency` (`LF4/BothPillars.lean`) states `born_frequency_convergence_N` with the sampling law = the SECTOR FIELD `d.liouvilleMeasure` (definitionally `fubiniStudyMeasure p₀`), so the Born theorem now references the same object the Schrödinger chain consumes. CAVEAT: structural sharing only — the trials `X` still SAMPLE the measure i.i.d.; they are not evolved by `d.flow`, and the weights are not derived from the dynamics (that is L7 = C6). |
| **L6** | ONE object underlies both pillars | **CONNECTED (2026-07-07, fix C4)** | `rotationSetup_both_pillars` (`LF4/BothPillars.lean`) proves, for the SINGLE `rotationSetup p₀`, BOTH (A) Schrödinger (`π(Φ_t x) = exp(-itH)·π(x)`, `H=σ_y`) AND (B) Born (frequencies from sampling `(rotationSetup p₀).liouvilleMeasure` → `‖⟨eᵢ,ψ⟩‖²`). One `KahlerOnticSetup` instance, both pillars. |
| **L7** | Born weights derived FROM the deterministic flow | **BROKEN — the thesis frontier (SO-1, the sector-origin problem); boundary now PROVED** | The one genuine `Φ ≠ id` flow (`kFlow` on `KSigma`) yields a **generic volume-ratio** typicality law (`kFlow_frequency_convergence`), explicitly NOT a Born weight (its docstring disclaims deriving the outcome region / Born weight — "Tranche B, not this module"). The obstruction is now machine-checked: a single projective flow does not uniquely determine an invariant measure — `SigmaLayer/SectorPostulateNoGo.lean` `flow_admits_invariant_ne_fubiniStudy` / `phaseFlip_admits_invariant_ne_fubiniStudy` exhibit an invariant probability measure `≠ μ_FS` for a flow with two fixed rays (concretely `diag(1,-1)` on `ℂℙ¹`). So L7 being broken is a proved fact about the single-flow limit, not a formalisation debt. The positive companion `SigmaLayer/LocalisedTypicality.lean` shows the full `U(N)` symmetry DOES pin `μ_FS` — the frontier is exactly that gap. |
| **L8** | ONE object with a GENUINE many-to-one `π` (Paper C A3) underlies both pillars | **CONNECTED (2026-07-08, fix C7)** | `manyToOneRotationSetup_both_pillars` (`LF4/ManyToOnePillars.lean`) proves, for the SINGLE `manyToOneRotationSetup p₀` — whose `Σ = ℂℙ¹ × T²`, `π = Prod.fst` is genuinely many-to-one (fibres `= T²`, `manyToOneSetup_pi_not_injective`) AND whose projected flow is a non-trivial ray rotation (`manyToOneRotationSetup_projectedFlow_ne_id`) — BOTH (A) Schrödinger (`π(Φ_t x) = exp(-itH)·π(x)`, `H=σ_y`, inherited from `rotationSetup_schrodinger_form`) AND (B) Born (frequencies from sampling `kMuL p₀` and scoring the FIBRED region `π⁻¹'(bornRegion ψ i)` → `‖⟨eᵢ,ψ⟩‖²`, via `manyToOneSetup_born_frequency`). At GENERAL `N` with ARBITRARY Hermitian `H`: `manyToOneSchrodingerSetup_both_pillars` (`U t = exp(-itH)`). Removes the `π = id` degeneracy of L6/`rotationSetup_both_pillars` — the Paper-C A3 caveat below. AxiomAudit-pinned (foundational triple, Gleason-free). SAME standing gap as L5/L7: the Born trials still SAMPLE `kMuL` i.i.d. rather than being evolved by `d.flow`, and the fibre flow is trivial (the flow moves only the base ray). |
| **L9** | ONE ontic model carries isolated dynamics AND de-isolating measurement AND records AND Born AND state update | **CONNECTED (2026-07-17: assembled into one tiered closure `FiniteQMClosure`)** | `unified_projectiveSector_capstone` (`SigmaLayer/UnifiedMeasurement.lean`) BUNDLES the dynamics + measurement CORE on the SAME `(Σ = ℂℙ^{M}×T², μL = μFS ⊗ vol, π = Prod.fst)`: the ISOLATED dynamics is the genuine `exp(-itH)` Hamiltonian flow (`productDynamics`, measure-preserving + Schrödinger-projectable + `π_*μL = μFS`) AND a `DeisolationModel` over that same dynamics realises the de-isolation MEASUREMENT (`(measurementFlow p, θ)`, measure-preserving, a.e.-defined pointer readout `vnDeisolationModel_ae_total`, record establishment). All the remaining pieces are now ASSEMBLED with it INTO one tiered record **`FiniteQMClosure` / `unifiedFiniteQMClosure`** (`SigmaLayer/FiniteQMClosure.lean`): time-physical records — INSTANTIATED on the unified model (`unifiedFlowedSemantics` = `flowedSemantics` over the isolated `productDynamics` flow; `unified_records_persistence`: Born weight conserved + flow-covariant; `unifiedFlowedSemantics_zero`: the static `vnRecordSemanticsProd` is the `t=0` slice), #5; post-outcome preparation with proven nonzero measure (`PostMeasurement.appendFact`); Born-frequency convergence — stated ON the model (`unified_born_frequency`: i.i.d. trials of `productDynamics.muL`, frequency in `π⁻¹(bornRegion i)` → `‖⟨eᵢ,ψ⟩‖²`, for EVERY unit `ψ` — `hpos` retired via the `_uncond` engine), #2; and the state update = record conditioning = Lüders update — GENUINELY proved (`ConditioningLuders.conditioning_luders_effect_equivalence`: the ontic record-conditioning and the Lüders update give the same conditional prediction for every pointer-basis effect, via the proved weight agreement `onticRegion_measure_eq_born`; the earlier `ConditioningLink.luders_record_conditioning_correspondence` only conjoined the two Bayesian halves and ASSERTED their agreement); and mixed-state Born (`MixedOntic.mixed_ontic_born_weight` = the `mixed_born` field, #8 C: the classical mixture over `ρ`'s spectral ensemble of ontic Born-region measures reproduces `Tr(ρ Eᵢ)`, so the model carries mixed-state Born content, not only the pure `ψ`). `FiniteQMClosure` carries these eleven as fields (the tenth/eleventh being mixed-state Born as a weight `mixed_born` and as an a.s. frequency `mixed_born_frequency` / `unified_mixed_born_frequency`, `SigmaLayer/MixedFrequency.lean`: a two-stage mixture LLN converging to `Tr(ρ Eᵢ)`), each discharged by its source lemma; the Choice-A posit, QM adapters, and open residue are documented in the module header (no field is `sorry`) — so the tiers stay honest. AxiomAudit-pinned. SAME standing gap as L7: FORWARD only — consumes the posited sector; does NOT derive it (SO-1). |

**Net (updated 2026-07-08 after C1+C2+C4+C7):** **L2–L6 + L8 CONNECTED.** A single
genuine `Φ ≠ id` object (`rotationSetup`) supports BOTH pillars: the Schrödinger
form (`H = σ_y ≠ 0`) AND the Born frequencies (sampling its own `liouvilleMeasure`),
proved together in `rotationSetup_both_pillars`. And (C7, L8) a single object with
a GENUINE many-to-one `π` (`Σ = ℂℙ¹ × T²`, `π = Prod.fst`, fibres `= T²`) with a
non-trivial projected ray flow supports both pillars too
(`manyToOneRotationSetup_both_pillars`), removing the `π = id` degeneracy and
matching Paper C's A3 fibred-projection shape. Remaining:
- **L1** — the Kähler-geometry fields now carry genuine formalizable content
  (`IsKahlerSector := IsFubiniStudyKahler`, the proved pointwise FS Kähler
  compatibility; `IsLiouvilleKahlerVolume` = normalized volume). Only the
  **manifold** residual (closedness `dω=0`, top-power volume identity) stays
  unformalizable — no Mathlib exterior-calculus API.
- **L7** ★ — the DEEP gap: the Born trials sample the sector's measure i.i.d.;
  they are not *evolved by the deterministic flow*, and the Born weights are not
  *derived from the dynamics*. This is the sector-origin problem (SO-1; distinct from
  Paper C Axiom A5, the projectability condition), fix C6, research-grade. It is the one link that, if closed, would make "QM from
  deterministic dynamics" unconditional rather than "QM from the posited sector".
So the honest headline is now: **"a single posited Kähler sector object yields
both the Born rule and Schrödinger dynamics"** is CONNECTED (structurally); the
remaining frontier is deriving that sector — and the Born trials — from the
deterministic flow itself.

**Paper-C cross-check caveat (2026-07-08).** Paper C's architecture (Axiom A3)
requires the projection `π : Σ → ℂℙ^{N-1}` to be **smooth many-to-one** — `Σ` is
strictly LARGER than ray space, and each epistemic ray `[ψ]` is the image of a
whole fibre `π⁻¹([ψ])` of ontic microstates (the fibre coordinates carry the
Liouville / absolute-continuity structure). The both-pillars object
`rotationSetup` uses **`π = id`** — the DEGENERATE one-to-one case, `Σ = ` ray
space, fibres = points. So the C1/C2/C4 theorems, while valid, do NOT exercise
Paper C's genuine many-to-one ontic projection; they run on `Σ = ℂℙ^{N-1}`
directly. A genuine many-to-one `π` DOES exist in the corpus
(`KSigma = ℂℙ^{N-1} × T²`, `π = Prod.fst`, fibres `= T²`, pushforward bridge
`Prod.fst_* kMuL = μ_FS` — `KahlerFlow.lean`), but (i) it is on the older
`SectorData` track, not `KahlerOnticSetup`, and (ii) its flow `kFlow` acts
trivially on rays (`projectedFlow = id`), so Schrödinger on it is trivial. **No
single object yet has BOTH a many-to-one `π` AND a non-trivial projected flow** —
that is the fix **C7** (below), the honest next step to match Paper C's A3. Also
note: our Schrödinger route is Wigner-rigidity + phase-lift + Stone, NOT Paper
C's Ashtekar–Schilling (holomorphic-vector-field) derivation — same endpoint,
different path. Paper C itself (§A/§3.6) states `Σ`, `π`, and the quantum-effective
sector (selected by A5) are **assumed, not derived**, leaving the sector's deeper
origin (SO-1) for later work — so our posited-sector scope matches Paper C's own.

**Update (2026-07-08, fix C7 — A3 caveat RESOLVED, link L8).** The
"no single object has BOTH a many-to-one `π` AND a non-trivial projected flow"
gap is now closed. `LF4/ManyToOnePillars.lean` builds `manyToOneSetup U p₀`:
a `KahlerOnticSetup` on the fibred `Σ = ℂℙ^{N-1} × T²` with `π = Prod.fst`
(genuinely many-to-one — `manyToOneSetup_pi_not_injective`, fibres `= T²`) and a
flow `Φ_t (p, θ) = (U t • p, θ)` that ROTATES THE BASE RAY (so `projectedFlow` is
the genuine ray action, non-trivial for the rotation, unlike `kFlow`). Both
pillars fire on the concrete `N = 2` witness (`manyToOneRotationSetup_both_pillars`,
link L8): Schrödinger inherited verbatim from `rotationSetup_schrodinger_form`
(identical base ray action), Born via `manyToOneSetup_born_frequency` scoring the
FIBRED region `π⁻¹'(bornRegion ψ i)` — whose `kMuL`-volume equals the base Born
weight because the fibre volume is normalized (`Prod.fst_* kMuL = μ_FS`,
`Measure.fst_prod` / `k_measure_bridge`), reducing to `born_frequency_convergence_N`
on the projected trials. This is now on the `KahlerOnticSetup` track (not the
older `SectorData` track), so it composes with the Schrödinger chain.
**Still NOT closed by C7:** the sector-origin / weights-from-flow gap (L7 /
SO-1) — the Born trials still SAMPLE `kMuL`, and the fibre flow is trivial
(dynamics move only the base ray, not the fibre). C7 fixes the *projection shape*,
not the *dynamical origin*. Our route is still Wigner, not Ashtekar–Schilling.

## What may be claimed (until a link flips to CONNECTED)

**(Updated 2026-07-15: the "both pillars on one posited sector" claims are now
CONNECTED forward results, so they are permitted; the forbidden line has moved to
the SO-1 frontier.)**

- ✅ "CSD machine-verifies the Born rule as an FS-typicality volume (on `ℂℙ^{N-1}`
  with `μ_FS`), Gleason-free, general `N`, incl. POVMs." — a real theorem about
  the FS measure.
- ✅ "GIVEN a posited Kähler ontic sector, CSD derives finite-dim Schrödinger
  dynamics via Wigner, at general `N` with arbitrary Hermitian `H`." — a real
  conditional theorem (`sigmaFlow_schrodinger_form`), now instantiated
  non-trivially (`manyToOneSchrodingerSetup`, `H` arbitrary).
- ✅ "A single posited Kähler sector object yields BOTH the Born rule AND
  Schrödinger dynamics" — CONNECTED (L6/L8), FORWARD, at general `N`
  (`manyToOneSchrodingerSetup_both_pillars`). Must carry the posited-sector /
  SO-1-open caveat.
- ✅ "One ontic model `(Σ, μL, Φ, π)` carries isolated dynamics, de-isolating
  measurement, time-indexed records, Born frequencies and the conditional/Lüders
  state update" — CONNECTED (L9: `FiniteQMClosure` / `unifiedFiniteQMClosure` assembles the dynamics +
  measurement core, records #5, Born-freq #2 and conditioning=Lüders #3/#4 into one tiered closure), FORWARD.
- ✅ "The thermodynamics track (TH1–TH4) is proved." — real, independent.
- ❌ "CSD DERIVES the sector `(π, G)` / the Born weights FROM the deterministic
  flow" / "the sector is no longer posited" — **FORBIDDEN** (L7 / SO-1 is OPEN; the
  trials SAMPLE `μL` i.i.d., the sector is posited). Every CONNECTED claim above is
  FORWARD (consumes the posited sector).
- ❌ Any phrasing implying the Kähler differential geometry (closed 2-form,
  complex structure) is constructed / load-bearing — **FORBIDDEN** (L1: no Mathlib
  Kähler API; the VOLUME is forced, the differential-geometric fields are demoted
  interpretive posits).

## The fix course (sequenced)

**Phase 1 — make the Schrödinger pillar non-trivial (bounded).**
- **C1 (fixes L4) — DONE 2026-07-07** (`LF4/NonTrivialSetup.lean`). Built
  `unitaryFlowSetup N U p₀` (a `KahlerOnticSetup` from any unitary family,
  measure-preserving via `fubiniStudyMeasure_smul_invariant`) and the concrete
  `rotationSetup` at `N = 2` (the `ℂℙ¹` rotation flow), with
  `rotationSetup_projectedFlow_ne_id : ∃ t, projectedFlow t ≠ id`. NB: `kFlow`
  was NOT reusable — it acts trivially on rays (`projectedFlow = id`); the fix
  uses a projective *unitary* flow instead.
- **C2 (fixes L3 off-trivial) — DONE 2026-07-07** (`LF4/RotationSchrodinger.lean`).
  `rotationSetup_schrodinger_form` fires `sigmaFlow_schrodinger_form` on
  `rotationSetup`: FS-isometry (unitary flow), coboundary (`b=1`, trivial cocycle
  via `R(s+t)=R(s)R(t)`), C¹ (`R'=R·J`) all discharged; recovers `H = iJ = σ_y ≠ 0`.
  The Schrödinger form now holds on a genuine `Φ≠id` flow with `H≠0`.
- **C3 (done 2026-07-07).** Retract the overclaiming docs; add
  `scripts/check-connectivity.sh` enforcing non-trivial-instance + no-overclaim.

**Phase 2 — one object, and Kähler content (medium).**
- **C4 (fixes L5/L6 structurally) — DONE 2026-07-07** (`LF4/BothPillars.lean`).
  `unitaryFlowSetup_born_frequency` states the Born law with sampling measure =
  the sector field `d.liouvilleMeasure` (defeq `fubiniStudyMeasure`);
  `rotationSetup_both_pillars` proves Schrödinger ∧ Born on the SINGLE
  `rotationSetup` object. Structural sharing only — weights-from-flow is C6.
- **C5 (fixes L1) — DONE 2026-07-07** (`LF4/NonTrivialSetup.lean`). Made
  `IsLiouvilleKahlerVolume` carry genuine content (`IsProbabilityMeasure μ_FS`,
  the normalized-volume core) and consumed it (`unitaryFlowSetup_liouville_isProbability`).
  `IsKahlerSector` honestly demoted to an unformalizable interpretive posit
  (no Mathlib Kähler API) — documented in `PLACEHOLDERS.md` and the structure
  docstring; no doc implies the Kähler differential geometry is load-bearing.

**Phase 2b — genuine many-to-one projection (Paper C A3; medium).**
- **C7 (fixes the A3 caveat, link L8) — DONE 2026-07-08** (`LF4/ManyToOnePillars.lean`).
  `manyToOneSetup U p₀` is a `KahlerOnticSetup` on `Σ = ℂℙ^{N-1} × T²` with the
  genuine many-to-one `π = Prod.fst` (`manyToOneSetup_pi_not_injective`) AND a
  non-trivial projected ray flow (`Φ_t` rotates the base by `U t`); both pillars
  fire on the `N = 2` rotation witness (`manyToOneRotationSetup_both_pillars`) —
  Schrödinger inherited from `rotationSetup_schrodinger_form`, Born via
  `manyToOneSetup_born_frequency` scoring the fibred region `π⁻¹'(bornRegion)`.
  AxiomAudit-pinned (foundational triple). Removes the `π = id` degeneracy; does
  NOT touch L7 (Born still samples `kMuL`; fibre flow trivial).

**Phase 3 — the thesis frontier (deep; = SO-1, the sector-origin problem).**
- **C6 (fixes L7, makes L5/L6 genuine).** Derive the Born weights FROM the
  deterministic flow — the outcome-region / pointer content that `kFlow` currently
  disclaims. This is the open sector-origin problem SO-1 (`specs/carve-out-plan.md` §6,
  `future-work.md` SO-1; distinct from Paper C Axiom A5). It is the real prize and is research-grade.

**Gate:** a link's row flips to CONNECTED only when a named `sorry`-free,
AxiomAudit-pinned theorem backs it. The README claim upgrades only then.
