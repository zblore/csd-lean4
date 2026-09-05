/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.GlobalBasin
public import CsdLean4.LF4.ManyToOnePillars

/-!
# SigmaLayer/Equivariance: the epistemic measure is carried by the flow

**Category:** 7-SigmaLayer (the projective-sector layer, Paper C).

The Bohmian comparison keeps being misread as a gap in this corpus, and the reason is that the
ingredients were scattered: the epistemic measure lives in `RecordLayer/GlobalBasin.lean`, the
Fubini–Study invariance in `Mathlib/LinearAlgebra/Projectivization/FubiniStudy.lean`, and the flow
in `LF4/ManyToOnePillars.lean`. Nobody had written the sentence they add up to. This module writes
it, so the misreading has a citable answer.

## The two statements, and they are different

★ `epistemicMeasure_equivariant` — the **epistemic** measure is *carried along*: the flow pushes
`epistemicMeasure p` forward to `epistemicMeasure (f p)`. This is the analogue of Bohmian
equivariance, `|ψ|²` carried to `|ψ_t|²`.

★★ `csd_equivariance` — on the concrete arena, both halves at once: the epistemic measure is
carried by the isolated flow to the epistemic measure at the evolved ray, **and** the typicality
measure `μL = μ_FS ⊗ vol` is invariant.

The two must not be run together. The epistemic measure moves; the typicality measure does not.

## ⚠️ What each half actually costs, which is the point of stating them separately

`epistemicMeasure_equivariant` takes **measurability and nothing else** — no measure preservation
anywhere in its hypotheses. That is not an oversight: a Dirac base pushes forward to a Dirac base
under any measurable map, and the fibre is untouched, so the epistemic half is free. Stating it with
a preservation hypothesis it does not use would have made the theorem look deeper than it is.

The typicality half is where preservation lives, and here the corpus is in a **better position than
the review that prompted this module assumed**. The review recorded `μL`-preservation as "the
structure field `ConstraintDynamics.flow_preserves` (posited)". That is true of the *abstract*
interface and false of the *concrete* arena: `manyToOneSetup` discharges `flow_preserves_volume`
with a proof (`LF4/ManyToOnePillars.lean`), namely `fubiniStudyMeasure_smul_invariant` on the base
times the identity on the fibre. So on the arena `csd_equivariance` is unconditional, and no posit
is hiding in it.

⚠️ Read this together with `SigmaLayer/SectorPostulateNoGo.lean`
(`flow_admits_invariant_ne_fubiniStudy`), which says a deterministic flow does **not** pin the
measure. The two are the honest pair: *given* the sector, evolution preserves it and carries the
epistemic measure correctly; but preservation alone does not select `μ_FS`, which is why the
measure is Posit 9 (`specs/POSITS.md`) and is forced instead by symmetry
(`fubiniStudyMeasure_unique`). Uniqueness and preservation are different claims and the no-go reads
more negatively than the position warrants when it stands alone.

## References

`RecordLayer/GlobalBasin.lean` (`epistemicMeasure`); `LF4/ManyToOnePillars.lean`
(`manyToOneSetup`, and the proof of `flow_preserves_volume`); `LF4/KahlerInstance.lean` (`kMuL`);
`Mathlib/LinearAlgebra/Projectivization/FubiniStudy.lean` (`fubiniStudyMeasure_smul_invariant`,
`fubiniStudyMeasure_unique`); `SigmaLayer/SectorPostulateNoGo.lean`
(`flow_admits_invariant_ne_fubiniStudy`); `specs/POSITS.md` (Posits 2 and 9);
`specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory

namespace CSD
namespace SigmaLayer

open LF4 RecordLayer

variable {N : ℕ}

/-- ★ **The epistemic measure is carried by a fibre-frozen map.** For any measurable base map `f`,
the lift `(p, θ) ↦ (f p, θ)` pushes `epistemicMeasure p` forward to `epistemicMeasure (f p)`.

⚠️ **No measure-preservation hypothesis appears, and none is used.** The base factor is a Dirac,
which pushes forward to a Dirac under any measurable map, and the fibre factor is untouched. This is
the honest cost of the epistemic half; the typicality half is where preservation is needed. -/
theorem epistemicMeasure_equivariant (f : CPN N → CPN N) (hf : Measurable f) (p : CPN N) :
    Measure.map (Prod.map f (id : KTorus → KTorus)) (epistemicMeasure p)
      = epistemicMeasure (f p) := by
  rw [epistemicMeasure, epistemicMeasure,
    ← Measure.map_prod_map _ _ hf measurable_id]
  simp [Measure.map_dirac' hf]

/-- ★★ **CSD equivariance on the concrete arena.** The isolated flow carries the epistemic measure
at `[ψ]` to the epistemic measure at the evolved ray, and leaves the typicality measure `μL`
invariant.

The two conjuncts are the whole point: the **epistemic** measure moves with the state (the analogue
of Bohmian equivariance) while the **typicality** measure stays put. Neither conjunct carries a
hypothesis — the first needs none, and the second is discharged by `manyToOneSetup`'s proof of
`flow_preserves_volume`, which is `fubiniStudyMeasure_smul_invariant` on the base and the identity
on the fibre. ⚠️ Preservation is *posited* only in the abstract `ConstraintDynamics` interface; on
this arena it is proved, and this theorem is unconditional.

Read with `flow_admits_invariant_ne_fubiniStudy`: preservation does not select `μ_FS`. Symmetry
does (`fubiniStudyMeasure_unique`). -/
theorem csd_equivariance {M : ℕ} (H : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (hH : H.IsHermitian)
    (p₀ : CPN (M + 1)) (t : ℝ) (p : CPN (M + 1)) :
    Measure.map ((manyToOneSchrodingerSetup H hH p₀).flow t) (epistemicMeasure p)
        = epistemicMeasure (schrodingerUnitary hH t • p)
      ∧ MeasurePreserving ((manyToOneSchrodingerSetup H hH p₀).flow t) (kMuL p₀) (kMuL p₀) := by
  refine ⟨?_, (manyToOneSchrodingerSetup H hH p₀).flow_preserves_volume t⟩
  have hmeas : Measurable (fun q : CPN (M + 1) => schrodingerUnitary hH t • q) :=
    (continuous_const_smul (schrodingerUnitary hH t)).measurable
  exact epistemicMeasure_equivariant _ hmeas p

end SigmaLayer
end CSD
