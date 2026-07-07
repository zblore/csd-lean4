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
| **L3** | projected flow `⇒` Schrödinger form | **CONDITIONAL (theorem real; hypotheses undischarged off trivial)** | `CSD.LF4.sigmaFlow_schrodinger_form` proves `π(Φ_t x) = exp(-itH)·π(x)` GIVEN the FS-isometry family, the coboundary datum, and the C¹ datum. Those hypotheses are discharged only for `U=1, b=1, A=0, H=0` on `trivialKahlerOnticSetup`. |
| **L4** | a genuine `Φ ≠ id` `KahlerOnticSetup` inhabitant exists | **BROKEN — trivial-witness-only** | The ONLY inhabitant of `KahlerOnticSetup` in the repo is `trivialKahlerOnticSetup` (`Φ = id`, `π = id`, Kähler props `= True`). The real `Φ ≠ id` flow `kFlow`/`KSigma` (`LF4/KahlerFlow.lean`) is wired to an LF1 `OnticSetup`/LF2 `SectorData`, NOT to `KahlerOnticSetup`. |
| **L5** | sector / projected flow `⇒` Born weights | **BROKEN — separate object** | The Born capstones (`born_frequency_convergence_N`, `povm_born_frequency_volume`) consume abstract i.i.d. variables on `CPN` with law `fubiniStudyMeasure`, via the generic SLLN engine. No `KahlerOnticSetup`, no `OnticSetup`, no deterministic flow appears. |
| **L6** | ONE object underlies both pillars | **BROKEN — two unlinked objects** | Schrödinger consumes `KahlerOnticSetup`; Born consumes bare `CPN + fubiniStudyMeasure`. No file shares both; no instance is fed to both. |
| **L7** | Born weights derived FROM the deterministic flow | **BROKEN — the thesis frontier (A5/D1, FND-1)** | The one genuine `Φ ≠ id` flow (`kFlow` on `KSigma`) yields a **generic volume-ratio** typicality law (`kFlow_frequency_convergence`), explicitly NOT a Born weight (its docstring disclaims deriving the outcome region / Born weight — "Tranche B, not this module"). |

**Net:** the only fully-connected-and-instantiated path is the **trivial** one
(`Φ = id ⇒ H = 0 ⇒ exp(0) = 1`). Every non-trivial link is broken, conditional,
or lands on a separate object.

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
- **C1 (fixes L4).** Construct a genuine `Φ ≠ id` `KahlerOnticSetup N` inhabitant,
  reusing `kFlow`/`KSigma` (the existing measure-preserving non-identity flow).
  Prove its `projectedFlow ≠ id`. This is the linchpin: without it the whole
  Schrödinger chain is vacuous beyond the base case.
- **C2 (fixes L3 off-trivial).** On the C1 instance, either discharge the FS-isometry
  / coboundary / C¹ hypotheses, or expose exactly which remain posited — so the
  Schrödinger form fires on a real flow, not `H = 0`.
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
