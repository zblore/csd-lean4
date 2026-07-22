/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF4.RotationSchrodinger
import CsdLean4.LF4.BornFrequencyN

/-!
# C4: both pillars on ONE object

**Category:** 3-Local (both pillars on ONE object).

Connectivity fix C4 (`specs/connectivity-manifest.md`, links L5/L6): the audit
found the Born capstone and the Schrödinger capstone were proved about
*different, unlinked* objects — Schrödinger about a `KahlerOnticSetup`, Born
about a bare `CPN + fubiniStudyMeasure` i.i.d. engine. This module routes the
Born frequency law through the **same sector object** the Schrödinger side uses.

The hinge is definitional: `(unitaryFlowSetup N U p₀).liouvilleMeasure` IS
`fubiniStudyMeasure p₀` (the sector's posited Liouville / typicality measure), so
`born_frequency_convergence_N` applies verbatim with the sampling law stated as
the sector field `d.liouvilleMeasure`. The result:

* `unitaryFlowSetup_born_frequency` — for any `unitaryFlowSetup`, sampling its
  own `liouvilleMeasure` i.i.d. gives empirical frequencies converging a.s. to
  the Born weights.
* `rotationSetup_both_pillars` (**the C4 headline**): for the SINGLE object
  `rotationSetup p₀`, BOTH hold — (A) its projected deterministic flow is
  `exp(-itH)`-conjugation on rays (Schrödinger, `H = σ_y`, from C2), AND (B)
  sampling its `liouvilleMeasure` gives the Born frequencies. One
  `KahlerOnticSetup` instance, both pillars.

## Honest scope (the remaining gap = C6/L7, the thesis frontier)

This is STRUCTURAL sharing: the Born law now references `d.liouvilleMeasure` (the
sector's own measure), not a coincidentally-equal external measure. It does NOT
yet derive the Born trials from the deterministic flow `d.flow`, nor the Born
weights from the dynamics — the trials `X` remain an i.i.d. sampling posit
(`hlaw`, `hindep`). Deriving the outcome region / weights FROM the flow is fix C6
= the A5/D1 sector-origin problem (`future-work.md` SL-1), untouched here. So:
one object underlies both pillars (L6 CONNECTED), but the Born side still samples
the measure rather than evolving it (L7 open).

## Provenance

Foundational-triple only; Gleason-free (the Born side carries no
`busch_effect_gleason`). Reuses `born_frequency_convergence_N` and
`rotationSetup_schrodinger_form`; nothing re-proved.
-/

open MeasureTheory ProbabilityTheory Set Filter Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF4

variable {M : ℕ}

/-- **Born frequencies from the sector's own Liouville measure.** For any
`unitaryFlowSetup (M+1) U p₀`, i.i.d. trials sampled from its `liouvilleMeasure`
(which is `fubiniStudyMeasure p₀` by construction) have empirical frequencies of
the Born region converging a.s. to the Born weight `‖⟨eᵢ, ψ⟩‖²`. The sampling
law is stated as the SECTOR FIELD `d.liouvilleMeasure`, so the Born theorem now
references the same object the Schrödinger chain consumes. -/
theorem unitaryFlowSetup_born_frequency
    (U : ℝ → Matrix.unitaryGroup (Fin (M + 1)) ℂ) (p₀ : CPN (M + 1))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (hpos : ∀ j, 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = (unitaryFlowSetup (M + 1) U p₀).liouvilleMeasure)
    (hindep : ∀ i : Fin (M + 1),
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ hψ0 i) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : Fin (M + 1),
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator ((X k) ⁻¹' bornRegion ψ hψ0 i) (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)) :=
  -- `(unitaryFlowSetup …).liouvilleMeasure = fubiniStudyMeasure p₀` definitionally,
  -- so `hlaw` is accepted verbatim as the `fubiniStudyMeasure` hypothesis.
  born_frequency_convergence_N p₀ ψ hψ0 hψ hpos X hX hlaw hindep

/-- **C4 / connectivity links L5–L6: both pillars on ONE object.** For the single
`KahlerOnticSetup 2` instance `rotationSetup p₀`:

* **(A) Schrödinger** — its projected deterministic flow is `exp(-itH)`-conjugation
  on rays for a Hermitian `H` (`= σ_y`), i.e. `π(Φ_t x) = exp(-itH) • π(x)`;
* **(B) Born** — sampling its own `liouvilleMeasure` i.i.d. gives empirical
  frequencies converging a.s. to the Born weights `‖⟨eᵢ, ψ⟩‖²`.

Both statements are about the *same* `rotationSetup p₀`, with the Born sampling
law being that object's `liouvilleMeasure`. This is the structural "one posited
object underlies both pillars" claim — honestly, for a single concrete instance,
and modulo the standing C6/L7 gap (the Born trials sample the measure rather than
being evolved by the flow). -/
theorem rotationSetup_both_pillars (p₀ : CPN 2)
    (ψ : EuclideanSpace ℂ (Fin 2)) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (hpos : ∀ j, 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 2) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = (rotationSetup p₀).liouvilleMeasure)
    (hindep : ∀ i : Fin 2,
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ hψ0 i) (fun _ => (1 : ℝ))))) :
    (∃ H : Matrix (Fin 2) (Fin 2) ℂ, ∃ hH : H.IsHermitian,
        ∀ t x, (rotationSetup p₀).pi ((rotationSetup p₀).flow t x)
          = schrodingerUnitary hH t • (rotationSetup p₀).pi x)
      ∧ (∀ᵐ ω ∂ Pr, ∀ i : Fin 2,
          Tendsto
            (fun m : ℕ =>
              (∑ k ∈ Finset.range m,
                  Set.indicator ((X k) ⁻¹' bornRegion ψ hψ0 i) (fun _ => (1 : ℝ)) ω) / (m : ℝ))
            atTop
            (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2))) :=
  ⟨rotationSetup_schrodinger_form p₀,
    unitaryFlowSetup_born_frequency rotU p₀ ψ hψ0 hψ hpos X hX hlaw hindep⟩

end LF4
end CSD
