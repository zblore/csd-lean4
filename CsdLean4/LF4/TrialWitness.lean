import CsdLean4.LF4.BornRegionUncond
import CsdLean4.Mathlib.Probability.IIDCoordinateProcess

/-!
# LF4: the canonical i.i.d. FS trial witness

**Category:** 3-Local (LF4 Born-from-Kähler-volume engine, trial-witness
tranche).

Every capstone of the volume-frequency series
(`born_frequency_convergence_N` / `_uncond`, `povm_born_frequency_volume`,
the LF5 `measurement_flow_born_frequency`, the `Empirical/CSD/*Volume`
witnesses) quantifies over an abstract i.i.d. trial bundle
`(Ω, Pr, X, hX, hlaw, hindep)`. Until this file no corpus theorem
*constructed* such a process: the hypothesis set was classically satisfiable
(standard product-measure existence) but not Lean-inhabited. This file closes
that vacuity-shaped residue:

* `fsTrialSpace` / `fsTrialMeasure` / `fsTrial` — the canonical process
  `Ω = ℕ → ℂℙ^{N-1}`, `Pr = Measure.infinitePi (fun _ => fubiniStudyMeasure p₀)`,
  `X n = (· n)`, with marginal law `fubiniStudyMeasure p₀`
  (`fsTrial_law`, via `Measure.infinitePi_map_eval`), joint independence
  (`fsTrial_iIndepFun`, via `iIndepFun_eval_infinitePi`), and the pairwise
  indicator independence in exactly the capstone shape
  (`fsTrial_pairwise_indepFun_indicator`).
* `born_frequency_convergence_N_canonical` — the unconditional general-`N`
  Born-frequency capstone applied to the canonical process: the statement
  quantifies only over `(p₀, ψ, hψ0, hψ)`; the entire trial bundle is
  discharged. The conclusion is verbatim that of
  `born_frequency_convergence_N_uncond` with `Pr := fsTrialMeasure p₀` and
  `X := fsTrial`.

The LF5 analogue (`measurement_flow_born_frequency_canonical`) lives in
`CsdLean4/LF5/CapstoneCanonical.lean` (LF5 imports LF4, not conversely).

## Honest scope

This is the **measure-theoretic existence** of the i.i.d. sampling law: the
canonical product-measure process witnesses that the trial hypotheses are
mutually consistent and realisable inside Lean. The **physical** reading of
repeated preparation as i.i.d. FS-typical draws remains the LF1 typicality
posit (the A5 sector/typicality datum); constructing the process does not
derive that posit. Foundational-triple-only; Gleason-free (no
`busch_effect_gleason`).
-/

open MeasureTheory ProbabilityTheory Set Filter Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization

namespace CSD
namespace LF4

variable {N : ℕ}

/-- The canonical trial space for FS-typical sampling on `ℂℙ^{N-1}`: infinite
sequences of projective points, one per trial. -/
abbrev fsTrialSpace (N : ℕ) : Type := ℕ → CPN N

/-- The canonical trial measure: the infinite product of `fubiniStudyMeasure p₀`
over the trial index. The i.i.d. sampling law itself. -/
noncomputable def fsTrialMeasure (p₀ : CPN N) : Measure (fsTrialSpace N) :=
  Measure.infinitePi (fun _ : ℕ => fubiniStudyMeasure p₀)

instance instIsProbabilityMeasureFsTrialMeasure (p₀ : CPN N) :
    IsProbabilityMeasure (fsTrialMeasure p₀) := by
  rw [fsTrialMeasure]; infer_instance

/-- The canonical trial process: trial `n` reads coordinate `n`. -/
def fsTrial (N : ℕ) (n : ℕ) : fsTrialSpace N → CPN N := fun ω => ω n

/-- Each canonical trial is measurable (`hX`). -/
theorem fsTrial_measurable (n : ℕ) : Measurable (fsTrial N n) :=
  measurable_pi_apply n

/-- Each canonical trial has law `fubiniStudyMeasure p₀` (`hlaw`). -/
theorem fsTrial_law (p₀ : CPN N) (n : ℕ) :
    Measure.map (fsTrial N n) (fsTrialMeasure p₀) = fubiniStudyMeasure p₀ :=
  Measure.infinitePi_map_eval (fun _ : ℕ => fubiniStudyMeasure p₀) n

/-- The canonical trials are jointly independent. -/
theorem fsTrial_iIndepFun (p₀ : CPN N) :
    iIndepFun (fsTrial N) (fsTrialMeasure p₀) :=
  iIndepFun_eval_infinitePi (fubiniStudyMeasure p₀)

/-- Pairwise independence of the per-trial outcome-region indicators, for any
family of measurable regions — the exact `hindep` shape every
volume-frequency capstone consumes. -/
theorem fsTrial_pairwise_indepFun_indicator (p₀ : CPN N)
    {ι : Type*} (S : ι → Set (CPN N)) (hS : ∀ i, MeasurableSet (S i)) :
    ∀ i, Pairwise
      (Function.onFun (fun f g : fsTrialSpace N → ℝ => IndepFun f g (fsTrialMeasure p₀))
        (fun n => Set.indicator ((fsTrial N n) ⁻¹' S i) (fun _ => (1 : ℝ)))) :=
  (fsTrial_iIndepFun p₀).pairwise_indepFun_indicator_preimage S hS

variable {M : ℕ}

/-- **General-`N` Born-frequency convergence on the canonical i.i.d. FS
process.** `born_frequency_convergence_N_uncond` with the trial bundle
discharged by the canonical witness: the statement quantifies only over the
reference point `p₀` and the preparation `(ψ, hψ0, hψ)`. The conclusion is
verbatim the original's with `Pr := fsTrialMeasure p₀`, `X := fsTrial (M + 1)`.
Foundational-triple-only, Gleason-free. -/
theorem born_frequency_convergence_N_canonical (p₀ : CPN (M + 1))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀, ∀ i : Fin (M + 1),
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator ((fsTrial (M + 1) k) ⁻¹' bornRegion ψ hψ0 i)
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)) :=
  born_frequency_convergence_N_uncond p₀ ψ hψ0 hψ
    (fsTrial (M + 1)) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀ (bornRegion ψ hψ0)
      (bornRegion_measurable_uncond ψ hψ0))

open CSD.LF2 in
/-- **POVM Born-frequency convergence on the canonical i.i.d. FS process (P.4).**
`povm_born_frequency_volume` with the trial bundle discharged by the canonical
witness on the dilated sector `Σ' = ℂℙ^{N·|ι|−1}`: the statement quantifies only
over `(P, D, ψ, e, ψ', hψ'eq, hψ'0, hnorm, hpos, p₀)`. The conclusion is verbatim
the original's with `Pr := fsTrialMeasure p₀`, `X := fsTrial (M + 1)`. The region
family is the dilated-state `bornRegion ψ' hψ'0` (measurability via
`bornRegion_measurable_uncond`). Foundational-triple-only, Gleason-free.

(This canonical form lives here, not in `POVMVolume.lean`, because the
import chain runs `POVMVolume → BornRegionUncond → TrialWitness`; placing it
upstream would create a cycle.) -/
theorem povm_born_frequency_volume_canonical
    {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ}
    (P : POVM N ι) (D : NaimarkDilation P)
    (ψ : EuclideanSpace ℂ (Fin N)) (e : (Fin N × ι) ≃ Fin (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (Matrix.toEuclideanLin D.V ψ))
    (hψ'0 : ψ' ≠ 0) (hnorm : ‖ψ'‖ = 1)
    (hpos : ∀ j : Fin (M + 1), 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ'‖ ^ 2)
    (p₀ : CPN (M + 1)) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀, ∀ i : ι,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin N,
            (∑ k ∈ Finset.range m,
                Set.indicator ((fsTrial (M + 1) k) ⁻¹' bornRegion ψ' hψ'0 (e (n, i)))
                  (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds (P.weight ψ i)) :=
  povm_born_frequency_volume P D ψ e ψ' hψ'eq hψ'0 hnorm hpos p₀
    (fsTrial (M + 1)) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀ (bornRegion ψ' hψ'0)
      (bornRegion_measurable_uncond ψ' hψ'0))

end LF4
end CSD
