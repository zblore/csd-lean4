# Connectivity manifest — what actually connects, end to end

**This file is the single source of truth for connectivity claims.** No document
in this repository (README, INDEX, module docstrings, commit messages) may assert
a stronger end-to-end connection than a row here marked **CONNECTED** with a named
backing theorem. `scripts/check-connectivity.sh` enforces the parts of this that
can be checked statically. Created 2026-07-07 after a provenance audit found the
top-level "one posited object yields both pillars" claim was **not** realized in
the code.

## The honest one-paragraph status

The corpus machine-verifies the major structural theorems of finite-dimensional
QM as a set of **largely independent** results. The CSD *thesis* — that a single
deterministic Kähler ontic sector `(Σ, Φ, π)` yields BOTH the Born rule AND
Schrödinger dynamics as a connected derivation — is **NOT** formally realized
end-to-end. There is no single non-trivial object from which both pillars are
derived; the Kähler-geometry content is an unconsumed placeholder; the Schrödinger
chain is instantiated only on the identity-flow (`Φ = id`, `H = 0`) witness; and
the Born chain runs on a separate abstract measure-space engine that never sees a
sector object or a deterministic flow. What is genuinely proved is a collection of
**sound conditional theorems** plus the trivial base case; the connective tissue
is the open work below.

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
| **L1** | Kähler geometry `⇒` the sector's fields | **BROKEN — inert placeholder** | `KahlerOnticSetup.{IsKahlerSector,kahler_condition,IsLiouvilleKahlerVolume,liouville_eq_kahler_volume}` are `Prop` placeholders consumed by **no** theorem (only supplied as `True` in the trivial witness). No Kähler differential-form structure is formalized (Mathlib has no Kähler API). |
| **L2** | Σ + `Φ` + `π` `⇒` a well-defined projected flow | **CONNECTED (interface) but see L4** | The descent field `projectable : π(Φ_t x) = φ_t(π x)` is a genuine field and is consumed by `CSD.LF4.sigmaFlow_schrodinger_form` (`LF4/PhaseLift.lean`). Enforced by `scripts/check-sector-linkage.sh`. |
| **L3** | projected flow `⇒` Schrödinger form | **CONNECTED (2026-07-07, fix C2)** | `CSD.LF4.rotationSetup_schrodinger_form` (`LF4/RotationSchrodinger.lean`) fires `sigmaFlow_schrodinger_form` on the genuine `Φ ≠ id` `rotationSetup`: the FS-isometry (unitary flow), coboundary (`b = 1`, trivial cocycle since `R(s+t) = R(s)R(t)`), and C¹ (`R'(τ) = R(τ)·J`) data are all discharged on a non-trivial flow, recovering `H = iJ = σ_y ≠ 0` (`rotationSetup_generator_ne_zero`). The first fully-instantiated `H ≠ 0` Schrödinger statement — no longer trivial-witness-only. |
| **L4** | a genuine `Φ ≠ id` `KahlerOnticSetup` inhabitant exists | **CONNECTED (2026-07-07, fix C1)** | `CSD.LF4.rotationSetup` (`LF4/NonTrivialSetup.lean`) is a `KahlerOnticSetup 2` whose projected flow is the `ℂℙ¹` rotation `R(t)`; `rotationSetup_projectedFlow_ne_id` proves `∃ t, projectedFlow t ≠ id` (at `t = π/2`, `[e₀] ↦ [e₁]`). The general constructor `unitaryFlowSetup N U p₀` builds one from any unitary family (measure-preserving via `fubiniStudyMeasure_smul_invariant`). NB: `kFlow` was the wrong tool — it translates a `T²` fibre and so acts trivially on rays (`projectedFlow = id`). |
| **L5** | sector / projected flow `⇒` Born weights | **BROKEN — separate object** | The Born capstones (`born_frequency_convergence_N`, `povm_born_frequency_volume`) consume abstract i.i.d. variables on `CPN` with law `fubiniStudyMeasure`, via the generic SLLN engine. No `KahlerOnticSetup`, no `OnticSetup`, no deterministic flow appears. |
| **L6** | ONE object underlies both pillars | **BROKEN — two unlinked objects** | Schrödinger consumes `KahlerOnticSetup`; Born consumes bare `CPN + fubiniStudyMeasure`. No file shares both; no instance is fed to both. |
| **L7** | Born weights derived FROM the deterministic flow | **BROKEN — the thesis frontier (A5/D1, FND-1)** | The one genuine `Φ ≠ id` flow (`kFlow` on `KSigma`) yields a **generic volume-ratio** typicality law (`kFlow_frequency_convergence`), explicitly NOT a Born weight (its docstring disclaims deriving the outcome region / Born weight — "Tranche B, not this module"). |

**Net (updated 2026-07-07 after C1+C2):** the **Schrödinger side is now fully
connected on a non-trivial flow** — L2/L3/L4 CONNECTED: a genuine `Φ ≠ id`
`KahlerOnticSetup` (`rotationSetup`) exists, and the W-series capstone fires on
it, recovering `H = σ_y ≠ 0` (`rotationSetup_schrodinger_form`). Remaining
breaks: **L1** (Kähler-geometry fields still inert placeholders → fix C5) and the
whole **Born side L5/L6/L7** (Born uses a separate abstract `CPN + μ_FS` engine;
sharing the object = C4, deriving Born weights from the flow = C6/FND-1, the
thesis frontier). So: Schrödinger-from-a-genuine-flow is done; one-object-for-both
and Born-from-flow are the open work.

## What may be claimed (until a link flips to CONNECTED)

- ✅ "CSD machine-verifies the Born rule as an FS-typicality volume (on `ℂℙ^{N-1}`
  with `μ_FS`), Gleason-free, general `N`, incl. POVMs." — a real theorem about
  the FS measure; does NOT assert a deterministic-flow origin.
- ✅ "GIVEN a Kähler ontic sector (as hypotheses), CSD derives finite-dim
  Schrödinger dynamics via Wigner." — a real conditional theorem
  (`sigmaFlow_schrodinger_form`), currently instantiated only trivially.
- ✅ "The thermodynamics track (TH1–TH4) is proved." — real, independent.
- ❌ "A single posited object yields both the Born rule and Schrödinger dynamics
  end-to-end." — **FORBIDDEN** until L4 ∧ L5 ∧ L6 are CONNECTED.
- ❌ "The pillars stand on the same sector interface." — **FORBIDDEN** until L6.
- ❌ Any phrasing implying the Kähler geometry is load-bearing — **FORBIDDEN**
  until L1.

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
- **C4 (fixes L5/L6 structurally).** Route the Born capstone through the SAME
  `KahlerOnticSetup`/`OnticSetup` Σ that the Schrödinger side uses — a single
  instance feeding both. (Weights-from-flow is C6; this is the structural sharing.)
- **C5 (fixes L1).** Consume the Kähler-geometry fields in ≥1 theorem (e.g. tie
  `liouville_eq_kahler_volume` to `fubiniStudyMeasure`), or formally demote them to
  documented interpretive prose in `PLACEHOLDERS.md` and stop implying they matter.

**Phase 3 — the thesis frontier (deep; = FND-1 / A5→D1).**
- **C6 (fixes L7, makes L5/L6 genuine).** Derive the Born weights FROM the
  deterministic flow — the outcome-region / pointer content that `kFlow` currently
  disclaims. This is the open sector-origin problem (`specs/carve-out-plan.md` §6,
  `future-work.md` FND-1). It is the real prize and is research-grade.

**Gate:** a link's row flips to CONNECTED only when a named `sorry`-free,
AxiomAudit-pinned theorem backs it. The README claim upgrades only then.
