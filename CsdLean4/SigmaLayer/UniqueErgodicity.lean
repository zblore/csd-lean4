/-
Copyright (c) 2026 CSD contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Dynamics.Ergodic.Extreme
import CsdLean4.SigmaLayer.TheoremTargets

/-!
# FND/UniqueErgodicity: the ergodic face of A5/L7, sharpened

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)).

This module defines **unique ergodicity** (absent from Mathlib) and connects it to the
FND target scaffold `IsErgodicForOutcomeRegions` / `BornFromFlow` (`FND/TheoremTargets.lean`),
precisely locating the ergodic face of the A5/L7 frontier.

## What this establishes (and, honestly, what it does NOT)

* `UniquelyErgodic f μ` — `μ` is the UNIQUE `f`-invariant probability measure.
* `UniquelyErgodic.ergodic` — unique ergodicity implies ergodicity (the invariant-measure
  set is the singleton `{μ}`, so `μ` is an extreme point of it;
  `Ergodic.of_mem_extremePoints`). Not currently in Mathlib.
* `isErgodicForOutcomeRegions_of_ergodic` / `_of_uniquelyErgodic` — ergodicity (a fortiori
  unique ergodicity) of the time-1 flow map DISCHARGES the repo's scaffold predicate
  `IsErgodicForOutcomeRegions` (it IS Mathlib's `PreErgodic.measure_self_or_compl_eq_zero`).

**What is NOT proved here — and why.** The target `BornFromFlow` (`TheoremTargets.lean`) is
the *pointwise* (a.e.) statement `(1/n) ∑_{k<n} 𝟙_region(Φ_k x) → μL(region)`. Deriving it
from `IsErgodicForOutcomeRegions` requires the **pointwise (Birkhoff) ergodic theorem**, which
**Mathlib does not have** (it has only the von Neumann *mean* ergodic theorem,
`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`, and the Birkhoff-sum
*definitions*). So this module supplies the ergodicity side of the reduction and names the
remaining gap; it does not close `BornFromFlow`.

**Two proved facts bound what this route can ever buy — this is boundary-marking, not a route
CSD takes:**
1. A single projective *unitary* flow is provably NOT ergodic, and NOT uniquely ergodic, w.r.t.
   `μ_FS`: it conserves the Born coordinates and fixes eigen-rays, giving distinct invariant
   measures (`FND/SectorPostulateNoGo.lean` `flow_admits_invariant_ne_fubiniStudy`; `LF4/TypicalityForcing.lean`
   `obsFlow_not_ergodic`, `obsFlow_not_uniquely_ergodic`). So `UniquelyErgodic` is provably FALSE
   for the Schrödinger-type flows the sector currently carries — a candidate flow satisfying it
   must be non-unitary (de-isolation / fibre-mixing).
2. CSD's typicality is forced by the **law of large numbers** over fresh i.i.d. preparations,
   NOT by single-trajectory time averages (`specs/active-todo.md`, framing correction 2026-06-29,
   Papers A & B). The ergodic / single-trajectory account is the *optional stronger* reading, not
   the mechanism. So even a full pointwise Birkhoff theorem would sharpen A5's bracketing, not
   close the A5 residue (which is the sector/symmetry ORIGIN, `G`-from-`D1`).

References: `FND/TheoremTargets.lean` (`BornFromFlow`, `IsErgodicForOutcomeRegions`),
`FND/SectorPostulateNoGo.lean`, `LF4/TypicalityForcing.lean`, `LF4/KahlerVolumeForced.lean`
(`IsForcedKahlerVolume` — the positive companion: `μ_FS` forced by the full `U(N)` symmetry),
`specs/connectivity-manifest.md` (L7/A5), `specs/reconstruction-status.md` (T3 frontier).
-/

open MeasureTheory

namespace CSD.SigmaLayer

variable {α : Type*} [MeasurableSpace α]

/-- **Unique ergodicity.** `μ` is the UNIQUE `f`-invariant probability measure: `f` preserves
`μ`, `μ` is a probability measure, and any `f`-invariant probability measure equals `μ`. This is
the standard definition (absent from Mathlib); the classic inhabitant is an irrational rotation. -/
def UniquelyErgodic (f : α → α) (μ : Measure α) : Prop :=
  MeasurePreserving f μ μ ∧ IsProbabilityMeasure μ ∧
    ∀ ν : Measure α, MeasurePreserving f ν ν → IsProbabilityMeasure ν → ν = μ

/-- **Unique ergodicity implies ergodicity.** If `μ` is the only `f`-invariant probability
measure, the invariant-probability-measure set is the singleton `{μ}`, so `μ` is trivially an
extreme point of it, hence ergodic (`Ergodic.of_mem_extremePoints`). -/
theorem UniquelyErgodic.ergodic {f : α → α} {μ : Measure α} (h : UniquelyErgodic f μ) :
    Ergodic f μ := by
  obtain ⟨hmp, hprob, huniq⟩ := h
  apply Ergodic.of_mem_extremePoints
  rw [mem_extremePoints]
  refine ⟨⟨hmp, hprob⟩, ?_⟩
  rintro ν₁ ⟨hmp₁, hpr₁⟩ ν₂ ⟨hmp₂, hpr₂⟩ _
  exact ⟨huniq ν₁ hmp₁ hpr₁, huniq ν₂ hmp₂ hpr₂⟩

variable {Sigma : Type*} [MeasurableSpace Sigma]

/-- **Ergodicity of the time-1 flow map discharges the scaffold.** `IsErgodicForOutcomeRegions D`
(every time-1-invariant measurable set is `μL`-null or co-null) is exactly Mathlib's
`PreErgodic.measure_self_or_compl_eq_zero` for `Φ_1` on `μL`. -/
theorem isErgodicForOutcomeRegions_of_ergodic
    (D : ConstraintDynamics Sigma) (h : Ergodic (D.flow 1) (D.muL : Measure Sigma)) :
    IsErgodicForOutcomeRegions D :=
  fun _ hA hInv => h.measure_self_or_compl_eq_zero hA hInv

/-- **Unique ergodicity of the time-1 flow map discharges the scaffold** (a fortiori, via
`UniquelyErgodic.ergodic`). This is the exact hypothesis under which `BornFromFlow` would follow
from the (Mathlib-absent) pointwise Birkhoff theorem — and which the unitary no-gos provably
exclude for the current flows. -/
theorem isErgodicForOutcomeRegions_of_uniquelyErgodic
    (D : ConstraintDynamics Sigma) (h : UniquelyErgodic (D.flow 1) (D.muL : Measure Sigma)) :
    IsErgodicForOutcomeRegions D :=
  isErgodicForOutcomeRegions_of_ergodic D h.ergodic

end CSD.SigmaLayer
