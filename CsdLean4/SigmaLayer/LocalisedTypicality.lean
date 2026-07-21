import CsdLean4.LF4.KahlerVolumeForced
import CsdLean4.LF4.ManyToOnePillars

/-!
# FND/LocalisedTypicality: A5 in the right appropriate places

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)).

The deep open link A5 / FND-1 (connectivity-manifest L7) asks to DERIVE the sector's typicality measure —
and hence the Born weights — from the deterministic flow. A5 does NOT need to hold universally, for every
possible measure or state; it only needs to hold where it matters: **the measure only needs to be pinned
where the dynamical symmetry acts.** This module makes that precise.

`LF4/KahlerVolumeForced.lean` already proves the Fubini–Study volume is `IsForcedKahlerVolume`: the
UNIQUE `U(N)`-invariant probability measure on `ℂℙ^{N-1}`. So:

* `forcedVolume_unique` / `region_measure_symmetry_forced` — any two measures carrying the sector's
  `U(N)` symmetry coincide on EVERY region. The Born weights depend only on the SYMMETRY, not on which
  invariant measure: one does not need to derive THE measure from the dynamics, only to know the sector
  carries the `U(N)` symmetry.
* `localised_sectorPostulate_capstone` — for the concrete unitary-flow sector: (i) its ray-space typicality measure is
  FORCED (the unique `U(N)`-invariant probability measure), (ii) the deterministic projected flow
  `U t • ·` — a one-parameter subgroup of that symmetry — PRESERVES it, and (iii) every measure sharing
  the symmetry gives the same Born weights. So A5 is discharged AT the sectors carrying the full `U(N)`
  symmetry — the right appropriate places — WITHOUT a universal derivation.

## Honest scope

This is NOT the universal A5. The residual (FND-1) is that the FLOW alone is a single one-parameter
subgroup, which does not by itself GENERATE the full `U(N)` — so "invariant under the flow" is weaker
than "invariant under `U(N)`", and forcing needs the ambient symmetry the sector CONSTRUCTION carries,
not the bare flow. What is shown here: given that symmetry (which the concrete sectors have), the
typicality measure and the Born weights are forced, not independently posited. The sector itself is still
posited (A5/FND-1); this localises where the forcing bites.

References: `specs/connectivity-manifest.md` (L7 / A5), `specs/future-work.md` (FND-1);
`LF4/KahlerVolumeForced.lean` (`IsForcedKahlerVolume`, `fubiniStudyMeasure_unique`),
`LF4/ManyToOnePillars.lean` (`manyToOneSetup`).
-/

open MeasureTheory

namespace CSD.SigmaLayer

open CSD.LF4

variable {N : ℕ}

/-- **Any two forced Kähler volumes coincide.** A measure carrying the sector's `U(N)` symmetry (a
`IsForcedKahlerVolume`) is unique — so the typicality measure is determined by `Σ = ℂℙ^{N-1}` + its
symmetry, not chosen. -/
theorem forcedVolume_unique [NeZero N] {μ ν : Measure (CPN N)}
    (hμ : IsForcedKahlerVolume μ) (hν : IsForcedKahlerVolume ν) : μ = ν :=
  (hμ.unique ν hν.isProb hν.invariant).symm

/-- **The Born weights are symmetry-forced (localized A5).** Any two `U(N)`-invariant probability
measures assign the SAME measure to every region. The Born weights (region volumes) depend only on the
sector's `U(N)` symmetry, not on which invariant measure — so deriving THE measure from the dynamics is
not needed; carrying the symmetry suffices. -/
theorem region_measure_symmetry_forced [NeZero N] {μ ν : Measure (CPN N)}
    (hμ : IsForcedKahlerVolume μ) (hν : IsForcedKahlerVolume ν) (A : Set (CPN N)) :
    μ A = ν A := by rw [forcedVolume_unique hμ hν]

/-- **Localized A5: the typicality measure is forced by the symmetry the dynamics carries.** For the
unitary-flow sector on `Σ = ℂℙ^{N-1} × T²`, the ray-space typicality measure `π_*(μL)`:

1. IS the unique `U(N)`-invariant probability measure — forced by `Σ` + its symmetry, not an independent
   posit;
2. is PRESERVED by the deterministic projected flow `U t • ·` (a one-parameter subgroup of that symmetry);
3. gives the SAME measure to every region as any other measure carrying the symmetry.

So A5 holds AT the sectors carrying the full `U(N)` symmetry — the right appropriate places — without a
universal derivation of the sector from the bare flow (that residual is FND-1). -/
theorem localised_sectorPostulate_capstone [NeZero N] (U : ℝ → Matrix.unitaryGroup (Fin N) ℂ) (p₀ : CPN N) :
    IsForcedKahlerVolume
        (Measure.map (manyToOneSetup U p₀).pi (manyToOneSetup U p₀).liouvilleMeasure)
    ∧ (∀ t, MeasurePreserving (fun p => U t • p)
        (Measure.map (manyToOneSetup U p₀).pi (manyToOneSetup U p₀).liouvilleMeasure)
        (Measure.map (manyToOneSetup U p₀).pi (manyToOneSetup U p₀).liouvilleMeasure))
    ∧ (∀ ν, IsForcedKahlerVolume ν → ∀ A,
        Measure.map (manyToOneSetup U p₀).pi (manyToOneSetup U p₀).liouvilleMeasure A = ν A) :=
  ⟨manyToOneSetup_baseVolume_isForcedKahlerVolume U p₀,
    fun t => (manyToOneSetup_baseVolume_isForcedKahlerVolume U p₀).invariant (U t),
    fun _ν hν A => region_measure_symmetry_forced
      (manyToOneSetup_baseVolume_isForcedKahlerVolume U p₀) hν A⟩

end CSD.SigmaLayer
