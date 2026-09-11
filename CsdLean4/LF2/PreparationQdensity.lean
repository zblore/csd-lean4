/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF2.Preparation
public import CsdLean4.LF2.EffectGleason
public import CsdLean4.Mathlib.QuantumInfo.Entropy
public import CsdLean4.Mathlib.QuantumInfo.DataProcessing

/-!
# The density operator of an ontic preparation, and the QIT layer applied to it

**Category:** 3-Local (the spine from a preparation on `Σ` to the quantum-information layer; W2 of
`specs/qit-chain-scoping.md`).

Two theorems of `LF2` compose to "a preparation on `Σ` determines a density operator":
`OperationalPackage.fromPreparation` (`LF2/Preparation.lean`) turns a preparation measure `μprep` on
`Σ` into an operational package, and `effect_gleason_representation` (`LF2/EffectGleason.lean`) turns
any operational package into the unique density operator whose trace form is its effect
probabilities. Until 2026-09-11 the composition was never stated, its density operator was consumed
by no theorem of `Mathlib/QuantumInfo/`, and every entropy, distance and data-processing theorem
there was a statement about a bare matrix nothing CSD-side ever supplied. This module composes them
and applies the layer.

* `preparationDensity` — **the density operator of a preparation**, `(fromPreparation …).qdensity`;
* ★★ `preparation_traceForm` / `preparation_qdensity_unique` — **the composition**: the effect
  probabilities of a preparation are the trace form of `preparationDensity`, and it is the unique
  density operator with that property (`effect_gleason_representation` on `fromPreparation`);
* `preparationDensity_posSemidef`, `preparationDensity_trace_one`, `preparationDensity_isHermitian` —
  **the instantiation lemmas**, in the exact hypothesis forms the QIT layer takes;
* ★ `vonNeumannEntropy_preparation_nonneg`, ★ `vonNeumannEntropy_preparation_le_log` — **the von
  Neumann entropy of a preparation on `Σ`** is well-defined, non-negative, and at most `log N`;
* ★ `channel_traceDist_preparation_le` — **the data-processing inequality for two preparations**: no
  channel increases their trace distance.

Every theorem below is `effect_gleason_representation` plus one `exact`; that is the point. The
spine was two proved theorems apart, and the QIT layer's hypotheses are `DensityOperator`'s fields.

## Honest scope

⚠️ **What "preparation" means here.** A `SectorData` on an abstract `Σ`, a `MeasureBridgeData`, a
probability measure `μprep` on `Σ`, and a unit-norm measurable representative `rep : P → ℂᴺ` — the
data `fromPreparation` takes. The sector is posited (`specs/POSITS.md` Posit 2); this module does not
derive it. What it proves is: **given** the posited sector, the QIT quantities of its preparations
obey the QIT theorems.

⚠️ **Gleason witness, not yet the barycentre.** `preparationDensity` is characterised by its trace
form (uniquely), not constructed as `∫ |ψ⟩⟨ψ| ρ_ep dμ_FS`; that identification is W3 of the scoping
note. Nothing below depends on it.

⚠️ **Channels are still bare.** `channel_traceDist_preparation_le` takes any `QuantumInfo.Channel`;
that the channel *comes from* a `Σ`-flow is W5/W6.

References: `specs/qit-chain-scoping.md` (W2–W4); `LF2/Preparation.lean`, `LF2/EffectGleason.lean`;
`Mathlib/QuantumInfo/{Entropy,DataProcessing,TraceDistance}.lean`.
-/

@[expose] public section

open MeasureTheory Matrix
open scoped ComplexOrder

namespace CSD
namespace LF2

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]
  {N : ℕ}

variable (D : SectorData SigmaSpace P G) (μFS : Measure P) [IsProbabilityMeasure μFS]
  (bridge : MeasureBridgeData D μFS)
  (μprep : Measure SigmaSpace) [IsProbabilityMeasure μprep]
  (rep : P → EuclideanSpace ℂ (Fin N))
  (hrep_unit : ∀ p, ‖rep p‖ = 1) (hrep_meas : Measurable rep)

/-! ### The composition -/

/-- **The density operator of a preparation on `Σ`**: the Gleason witness of the operational
package `fromPreparation` builds from it. -/
noncomputable def preparationDensity : DensityOperator N :=
  (OperationalPackage.fromPreparation D μFS bridge μprep rep hrep_unit hrep_meas).qdensity

/-- ★★ **The effect probabilities of a preparation are the trace form of its density operator.**
`fromPreparation` composed with `p_eq_traceForm_qdensity`. -/
theorem preparation_traceForm (E : Effect N) :
    (OperationalPackage.fromPreparation D μFS bridge μprep rep hrep_unit hrep_meas).p E
      = traceForm (preparationDensity D μFS bridge μprep rep hrep_unit hrep_meas) E :=
  (OperationalPackage.fromPreparation D μFS bridge μprep rep hrep_unit hrep_meas).p_eq_traceForm_qdensity E

/-- ★★ **Uniqueness**: `preparationDensity` is the only density operator whose trace form is the
preparation's effect probabilities — `effect_gleason_representation` on `fromPreparation`. -/
theorem preparation_qdensity_unique :
    ∃! ρ : DensityOperator N, ∀ E : Effect N,
      (OperationalPackage.fromPreparation D μFS bridge μprep rep hrep_unit hrep_meas).p E
        = traceForm ρ E :=
  (OperationalPackage.fromPreparation D μFS bridge μprep rep hrep_unit hrep_meas).effect_gleason_representation

/-! ### The instantiation lemmas, in the QIT layer's hypothesis forms -/

theorem preparationDensity_isHermitian :
    (preparationDensity D μFS bridge μprep rep hrep_unit hrep_meas).M.IsHermitian :=
  (preparationDensity D μFS bridge μprep rep hrep_unit hrep_meas).isHermitian

theorem preparationDensity_posSemidef :
    (preparationDensity D μFS bridge μprep rep hrep_unit hrep_meas).M.PosSemidef :=
  (preparationDensity D μFS bridge μprep rep hrep_unit hrep_meas).nonneg

theorem preparationDensity_trace_one :
    (preparationDensity D μFS bridge μprep rep hrep_unit hrep_meas).M.trace = 1 :=
  (preparationDensity D μFS bridge μprep rep hrep_unit hrep_meas).trace_one

/-! ### The QIT layer applied to a preparation -/

/-- **The von Neumann entropy of a preparation on `Σ`.** -/
noncomputable def preparationEntropy : ℝ :=
  QuantumInfo.vonNeumannEntropy (preparationDensity_isHermitian D μFS bridge μprep rep hrep_unit hrep_meas)

/-- ★ The entropy of a preparation is non-negative (`vonNeumannEntropy_nonneg`). -/
theorem vonNeumannEntropy_preparation_nonneg :
    0 ≤ preparationEntropy D μFS bridge μprep rep hrep_unit hrep_meas :=
  QuantumInfo.vonNeumannEntropy_nonneg (preparationDensity_posSemidef D μFS bridge μprep rep hrep_unit hrep_meas)
    (preparationDensity_trace_one D μFS bridge μprep rep hrep_unit hrep_meas)

/-- ★ The entropy of a preparation on the `N`-dimensional sector is at most `log N`
(`vonNeumannEntropy_le_log_card`). -/
theorem vonNeumannEntropy_preparation_le_log :
    preparationEntropy D μFS bridge μprep rep hrep_unit hrep_meas ≤ Real.log N := by
  have h := QuantumInfo.vonNeumannEntropy_le_log_card
    (preparationDensity_posSemidef D μFS bridge μprep rep hrep_unit hrep_meas)
    (preparationDensity_trace_one D μFS bridge μprep rep hrep_unit hrep_meas)
  rw [Fintype.card_fin] at h
  exact h

/-- ★ **Data processing for two preparations on `Σ`**: for any channel `Φ`, the trace distance of
the channel outputs is at most the trace distance of the preparations' density operators
(`channel_traceDist_le`). -/
theorem channel_traceDist_preparation_le {m ι : Type*} [Fintype m] [Fintype ι] [DecidableEq m]
    (Φ : QuantumInfo.Channel (Fin N) m ι)
    (μprep' : Measure SigmaSpace) [IsProbabilityMeasure μprep'] :
    QuantumInfo.traceDist
        ((Φ.apply_isHermitian (preparationDensity_isHermitian D μFS bridge μprep rep hrep_unit hrep_meas)).sub
          (Φ.apply_isHermitian (preparationDensity_isHermitian D μFS bridge μprep' rep hrep_unit hrep_meas)))
      ≤ QuantumInfo.traceDist
          ((preparationDensity_isHermitian D μFS bridge μprep rep hrep_unit hrep_meas).sub
            (preparationDensity_isHermitian D μFS bridge μprep' rep hrep_unit hrep_meas)) :=
  QuantumInfo.channel_traceDist_le Φ
    (preparationDensity_isHermitian D μFS bridge μprep rep hrep_unit hrep_meas)
    (preparationDensity_isHermitian D μFS bridge μprep' rep hrep_unit hrep_meas)
    ((preparationDensity_trace_one D μFS bridge μprep rep hrep_unit hrep_meas).trans
      (preparationDensity_trace_one D μFS bridge μprep' rep hrep_unit hrep_meas).symm)

end LF2
end CSD
