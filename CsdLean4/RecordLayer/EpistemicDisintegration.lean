/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.GlobalBasin
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.Disintegration.Unique

/-!
# Q26: the epistemic measure is a disintegration, not a definition

**Category:** 7-SigmaLayer (the record layer — BACKLOG Q26, queued 2026-08-20
from the external physicist review; `GlobalBasin.lean`'s own design note named
this gap).

**Glossary:** https://glossary.constraintsurfacedynamics.com/epistemic-measure/
Plain-language, CSD-role and formal statements of the epistemic measure, with
this module — the disintegration identification — as its Lean anchor. Kept
symmetric by `scripts/check-glossary.sh`.

`GlobalBasin.lean` TAKES the isolation-conditioned epistemic state to be
`δ_p ⊗ Haar` — a modelling choice stated as a definition, because conditioning
on a preparation conditions on a `μ_FS`-null set. This module proves the
theorem a careful reader asks for: that choice is the unique one the arena's
own measure makes. The Liouville measure `kMuL = μ_FS ⊗ vol` disintegrates
along the base projection, and its disintegration kernel is `μ_FS`-almost
everywhere the constant Haar kernel — so `δ_p ⊗ Haar` is the fibre of the
disintegration, planted at its base point, not a stipulation.

* `kMuL_fst` — the base marginal of the Liouville measure is the Fubini–Study
  measure (the `c = 1` bridge, in marginal form).
* `kMuL_eq_compProd_const` — the Liouville measure is the composition product
  of its base marginal with the CONSTANT Haar kernel.
* ★★ `kMuL_condKernel_ae` — **the identification**: the disintegration kernel
  `(kMuL).condKernel` equals Haar on the fibre, `μ_FS`-a.e. Route: Mathlib's
  kernel disintegration for standard Borel fibres
  (`Measure.compProd_fst_condKernel`) plus a.e. uniqueness
  (`eq_condKernel_of_measure_eq_compProd`) applied to the constant kernel.
* ★★ `epistemicMeasure_eq_disintegration` — **the headline**: `μ_FS`-almost
  every base point's epistemic state `δ_p ⊗ Haar` IS the Dirac mass at `p`
  paired with the Liouville measure's own disintegration kernel at `p`. The
  `GlobalBasin` definition is a derived object.
* ★ `kMuL_disintegration` — the reassembly, in `μ_FS` terms:
  `kMuL = μ_FS ⊗ₘ (kMuL).condKernel`.

The a.e. qualifier is intrinsic: a disintegration kernel is only ever
determined up to a null set of base points, so "exactly `δ_p ⊗ Haar`, for
every single `p`" is not a meaningful strengthening — the almost-everywhere
form IS the theorem.

## References

`specs/BACKLOG.md` (Q26); `RecordLayer/GlobalBasin.lean` (`epistemicMeasure`,
whose design note this supersedes); `LF4/KahlerInstance.lean` (`kMuL`);
`Mathlib/Probability/Kernel/Disintegration/` (`condKernel`, uniqueness);
`specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Matrix.UnitaryGroup ProbabilityTheory
open scoped LinearAlgebra.Projectivization ProbabilityTheory

namespace CSD.RecordLayer

variable {N : ℕ}

/-- **The base marginal of the Liouville measure is the Fubini–Study measure**
— the `c = 1` bridge read as a marginal. -/
theorem kMuL_fst (p₀ : CSD.LF4.CPN N) :
    (CSD.LF4.kMuL p₀).fst = fubiniStudyMeasure p₀ := by
  show ((fubiniStudyMeasure p₀).prod (volume : Measure CSD.LF4.KTorus)).fst
    = fubiniStudyMeasure p₀
  exact Measure.fst_prod

/-- The Liouville measure is the composition product of its base marginal with
the CONSTANT Haar kernel on the fibre. -/
theorem kMuL_eq_compProd_const (p₀ : CSD.LF4.CPN N) :
    CSD.LF4.kMuL p₀
      = (CSD.LF4.kMuL p₀).fst ⊗ₘ
          Kernel.const (CSD.LF4.CPN N) (volume : Measure CSD.LF4.KTorus) := by
  rw [Measure.compProd_const, kMuL_fst]
  rfl

/-- ★★ **The disintegration kernel of the Liouville measure is Haar on the
fibre**, `μ_FS`-almost everywhere: the identification that turns
`GlobalBasin`'s `δ_p ⊗ Haar` from a modelling choice into the fibre of the
arena's own disintegration. -/
theorem kMuL_condKernel_ae (p₀ : CSD.LF4.CPN N) :
    ∀ᵐ p ∂(fubiniStudyMeasure p₀),
      (CSD.LF4.kMuL p₀).condKernel p = (volume : Measure CSD.LF4.KTorus) := by
  have h := eq_condKernel_of_measure_eq_compProd
    (Kernel.const (CSD.LF4.CPN N) (volume : Measure CSD.LF4.KTorus))
    (kMuL_eq_compProd_const p₀)
  rw [kMuL_fst] at h
  filter_upwards [h] with p hp
  rw [Kernel.const_apply] at hp
  exact hp.symm

/-- ★★ **The epistemic measure IS the disintegration fibre** (Q26): for
`μ_FS`-almost every base point `p`, the isolation-conditioned epistemic state
`δ_p ⊗ Haar` equals the Dirac mass at `p` paired with the Liouville measure's
own disintegration kernel at `p`. -/
theorem epistemicMeasure_eq_disintegration (p₀ : CSD.LF4.CPN N) :
    ∀ᵐ p ∂(fubiniStudyMeasure p₀),
      epistemicMeasure (N := N) p
        = (Measure.dirac p).prod ((CSD.LF4.kMuL p₀).condKernel p) := by
  filter_upwards [kMuL_condKernel_ae p₀] with p hp
  rw [hp]
  rfl

/-- ★ **The reassembly**: the Liouville measure disintegrates over the
Fubini–Study base with its own conditional kernel. -/
theorem kMuL_disintegration (p₀ : CSD.LF4.CPN N) :
    CSD.LF4.kMuL p₀
      = fubiniStudyMeasure p₀ ⊗ₘ (CSD.LF4.kMuL p₀).condKernel := by
  conv_lhs => rw [← (CSD.LF4.kMuL p₀).disintegrate (CSD.LF4.kMuL p₀).condKernel]
  rw [kMuL_fst]

end CSD.RecordLayer
