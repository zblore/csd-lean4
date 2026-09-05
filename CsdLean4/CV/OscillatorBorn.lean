/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.OscillatorSpectrum
public import CsdLean4.RecordLayer.Measurement

/-!
# CV/OscillatorBorn: the truncated mode as a record-layer measurement (EFT Stage 0)

**Category:** CV (continuous variables — the single bosonic mode).

Turns the truncated single mode of `CV/OscillatorSpectrum.lean` from an *operator algebra* into a
genuine **CSD reconstruction**, by wiring its number/energy measurement into the record layer
(`RecordLayer/Measurement.lean`) and establishing **cutoff-independence** of the Born content — Stage 0
of the EFT direction (`specs/record-layer-plan.md`; the ladder QM → CV → relativistic EFT).

The oscillator Hamiltonian is diagonal (`hamiltonian_eq_diagonal`), so the number/energy eigenbasis is
the **standard basis** of `EuclideanSpace ℂ (Fin N)`; a number/energy measurement is therefore exactly
the standard-basis record-layer measurement. Hence:

⚠️ **Born wording (CR-1 standard).** The Born content here rests on the record layer's **cell law**, which is a posit *with* a characterisation: a context field whose rates generate the coordinate phase rotations is exactly the moment map (`torusGenerated_eq_momentMap`), while torus invariance alone does not pin it (`rate_field_not_forced_by_torus_symmetry`). What stays posited is that a context's rates generate its pointer torus — `specs/POSITS.md` Posit 1. So "the Born rule is derived" is accurate only as "derived given the cell law".

* `numberBornProb` / `numberBornProb_eq` — the Born probability of finding `n` quanta (energy
  `oscEnergy n = n + ½`) is `‖⟨n|ψ⟩‖²`, the record-layer `bornRate`;
* `numberMeasurement` / `numberMeasurement_prob` — the mode's measurement *is* a record-layer
  `Measurement` (`context + unknown microstate → record`), with outcome probability `‖⟨n|ψ⟩‖²`;
* `numberMeasurement_frequency` — the oscillator's Born rule is the **law of large numbers over the
  unknown microstate** (inherited from the record layer);
* `numberState_energy_eigenstate` — the Fock state `n` is the energy eigenstate `E = oscEnergy n`, so
  number = energy measurement;
* `numberBornProb_embed` — **cutoff-independence:** raising the truncation `N → M ≥ N` (zero-padding the
  new high levels) leaves each finite level's Born probability unchanged; the mode's finite-level Born
  predictions do not depend on the cutoff (the Born analogue of `oscEnergy_cutoff_independent`).

Honest scope: this is the *single mode at a finite cutoff*. The strict continuum limit (rigged Hilbert
space / Bargmann–Fock) is deliberately not taken — the EFT posture is cutoff-independence, not the
continuum (`ApproxCCR.no_exact_finite_ccr` + `ccr_exact_on_bulk`). Multi-mode fields, relativistic
dispersion, locality, and interactions are the later EFT stages. Foundational-triple, no `sorry`.

## References
`CV/OscillatorSpectrum.lean` (`hamiltonian`, `oscEnergy`, `hamiltonian_mulVec_single`,
`oscEnergy_cutoff_independent`); `CV/ApproxCCR.lean` (the finite-CCR obstruction / bulk-exactness);
`RecordLayer/Measurement.lean` (the record layer, `bornMeasurement`, `bornMeasurement_frequency`);
`RecordLayer/BasisMeasurement.lean` (arbitrary observable, if a non-number basis is measured).
-/

@[expose] public section

open MeasureTheory
open CSD.SigmaLayer CSD.RecordLayer

namespace CSD.CV

variable {N : ℕ}

/-- **The Born probability of finding `n` quanta** (energy `oscEnergy n = n + ½`) in mode state `ψ`:
the squared amplitude `‖⟨n|ψ⟩‖²`, i.e. the record-layer `bornRate`. The number eigenbasis is the
standard basis (`hamiltonian` is diagonal), so this is the standard-basis Born weight. -/
noncomputable def numberBornProb (ψ : EuclideanSpace ℂ (Fin N)) (n : Fin N) : ℝ := bornRate ψ n

theorem numberBornProb_eq (ψ : EuclideanSpace ℂ (Fin N)) (n : Fin N) :
    numberBornProb ψ n = ‖ψ n‖ ^ 2 := rfl

/-- The number-level Born probabilities sum to `1` on a unit state. -/
theorem sum_numberBornProb_unit (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1) :
    ∑ n, numberBornProb ψ n = 1 := sum_bornRate_unit ψ hψ

/-- **The Fock state `n` is the energy eigenstate with eigenvalue `oscEnergy n = n + ½`.** So measuring
the number is measuring the energy; the Born probability of energy `oscEnergy n` is `numberBornProb ψ n`. -/
theorem numberState_energy_eigenstate (n : Fin N) :
    (hamiltonian N).mulVec (Pi.single n 1) = ((oscEnergy (n : ℕ) : ℝ) : ℂ) • (Pi.single n 1) :=
  hamiltonian_mulVec_single n

/-- **The mode's number/energy measurement, as a record-layer measurement.** The number basis is the
standard basis, so the measurement is `Measurement.bornMeasurement`: the unknown microstate selects the
recorded quantum number, the combined result is the record-layer P5 record. -/
noncomputable def numberMeasurement (ψ : EuclideanSpace ℂ (Fin N)) (t : OnticTime) : Measurement N :=
  Measurement.bornMeasurement ψ t

/-- The record-layer probability of recording `n` quanta is the oscillator Born probability. -/
theorem numberMeasurement_prob (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1) (n : Fin N)
    (t : OnticTime) :
    (numberMeasurement ψ t).prob n = ENNReal.ofReal (numberBornProb ψ n) := by
  rw [numberMeasurement, Measurement.bornMeasurement_prob ψ hψ n t, numberBornProb_eq]

/-- **The oscillator's Born rule is the law of large numbers over the unknown microstate.** For i.i.d.
typical microstates, the frequency of trials recording `n` quanta converges a.s. to the Born
probability `numberBornProb ψ n = ‖⟨n|ψ⟩‖²`. Inherited verbatim from the record layer. -/
theorem numberMeasurement_frequency (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1) (n : Fin N)
    (t : OnticTime) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hlaw : ∀ k, Measure.map (X k) P = fibreTypicality)
    (hindep : Pairwise (Function.onFun (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g P)
      (fun k => Set.indicator (X k ⁻¹' (numberMeasurement ψ t).basin n) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ P, Filter.Tendsto
      (fun m : ℕ => (∑ k ∈ Finset.range m,
        Set.indicator (X k ⁻¹' (numberMeasurement ψ t).basin n) (fun _ => (1 : ℝ)) ω) / (m : ℝ))
      Filter.atTop (nhds (numberBornProb ψ n)) :=
  Measurement.bornMeasurement_frequency ψ hψ t n X hX hlaw hindep

/-- Zero-padding embedding of a cutoff-`N` mode state into a larger cutoff `M ≥ N`: keep the low
levels, set the new high levels to `0`. -/
noncomputable def embedMode {N M : ℕ} (_h : N ≤ M) (ψ : EuclideanSpace ℂ (Fin N)) :
    EuclideanSpace ℂ (Fin M) :=
  WithLp.toLp 2 (fun j : Fin M => if hj : (j : ℕ) < N then ψ ⟨(j : ℕ), hj⟩ else 0)

/-- The embedded state agrees with `ψ` on the low levels. -/
theorem embedMode_castLE {N M : ℕ} (h : N ≤ M) (ψ : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    (embedMode h ψ) (Fin.castLE h i) = ψ i := by
  simp [embedMode, WithLp.ofLp_toLp, Fin.val_castLE, i.isLt]

/-- **Cutoff-independence of the Born content.** Raising the truncation from `N` to any `M ≥ N`
(zero-padding the new high levels) leaves each finite level's Born probability unchanged: the mode's
finite-level Born predictions do not depend on the cutoff. The Born analogue of
`oscEnergy_cutoff_independent`. -/
theorem numberBornProb_embed {N M : ℕ} (h : N ≤ M) (ψ : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    numberBornProb (embedMode h ψ) (Fin.castLE h i) = numberBornProb ψ i := by
  unfold numberBornProb bornRate
  rw [embedMode_castLE]

end CSD.CV
