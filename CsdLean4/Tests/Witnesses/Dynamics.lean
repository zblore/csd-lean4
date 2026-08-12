/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.KahlerFlow
public import CsdLean4.LF4.ObservableFlow
public import CsdLean4.Tests.Witnesses.IIDSampling

/-!
# WS-J witness: the dynamics assumption package has non-identity inhabitants

**Category:** Special (validation-hardening witness suite,
`specs/validation-hardening-plan.md` WS-J).

**Cite, don't construct.** The production corpus already carries genuine
non-identity measure-preserving flows threaded through concrete `SectorData`
instances — the D1c discharge (2026-06-29): `kSectorDataFlow` (free `T²`-fibre
translation, `kFlow_ne_id`) and `cpSectorDataFlow` (the observable's
Hamiltonian phase flow on the Fubini–Study base, `obsFlow_ne_id`). This module
adds **no new dynamics**. Its content is consumer-side:

* `exists_cpSectorData_nontrivial_flow` / `exists_kSectorData_nontrivial_flow`
  — the assumption package (`SectorData` with `Φ ≠ id` + Liouville
  preservation) stated as an inhabited existential, every clause supplied by a
  named production theorem;
* `qubit_dynamics_witness` — the fully concrete corollary on the qubit sector
  `ℂℙ¹` at `N = 2`;
* `cpSectorDataFlow_frequency_convergence_concrete` — **theorem-chain
  execution with honest trials**: the production frequency capstone fired on
  explicit `Measure.infinitePi` coordinate trials, with the independence
  hypothesis discharged (not assumed) via `pairwise_indepFun_comp_eval`.

The nontriviality clauses (`Φ ≠ id`) rule out exactly the degenerate
inhabitant the D1c debt was about (`Φ := id` in every pre-D1c instance).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Matrix Matrix.UnitaryGroup
open CSD.LF4

namespace CSD
namespace Tests
namespace Witnesses

variable {N : ℕ}

/-! ## Existence packaging: the inhabited dynamics package -/

/-- **The base-sector dynamics package is inhabited by a physically-meaningful
non-identity flow** (for every base point and `N ≥ 2`): a concrete `SectorData`
on `ℂℙ^{N-1}` whose flow is not the identity and preserves the Fubini–Study /
Liouville volume. Witness: the production `cpSectorDataFlow` at the production
non-triviality parameters (`obsLamWitness`, `obsTWitness`); clauses:
`cpSectorDataFlow_phi_ne_id`, `cpSectorDataFlow_phi_measurePreserving`. -/
theorem exists_cpSectorData_nontrivial_flow [NeZero N] (hN : 1 < N) (p₀ : CPN N) :
    ∃ d : CSD.LF2.SectorData (CPN N) (CPN N) (Matrix.unitaryGroup (Fin N) ℂ),
      d.toOntic.Φ ≠ id
        ∧ MeasurePreserving d.toOntic.Φ (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀) :=
  ⟨cpSectorDataFlow p₀ (obsLamWitness hN) obsTWitness,
    cpSectorDataFlow_phi_ne_id p₀ hN,
    cpSectorDataFlow_phi_measurePreserving p₀ (obsLamWitness hN) obsTWitness⟩

/-- The concrete nonzero fibre shift `(1/2, 0)` on the torus `T²`. -/
theorem halfShift_ne_zero :
    ((((1 : ℝ) / 2 : ℝ) : AddCircle (1 : ℝ)), (0 : AddCircle (1 : ℝ)))
      ≠ (0 : KTorus) := by
  intro h
  have h1 : (((1 : ℝ) / 2 : ℝ) : AddCircle (1 : ℝ)) = 0 := congrArg Prod.fst h
  rw [AddCircle.coe_eq_zero_iff] at h1
  obtain ⟨n, hn⟩ := h1
  rw [zsmul_eq_mul, mul_one] at hn
  have h2 : ((2 * n : ℤ) : ℝ) = 1 := by push_cast; linarith
  have h3 : (2 * n : ℤ) = 1 := by exact_mod_cast h2
  omega

/-- **The Kähler-sector dynamics package is inhabited** (every base point,
every `N ≥ 1`): the production `kSectorDataFlow` at the concrete nonzero
fibre shift `(1/2, 0)`; clauses: `kSectorDataFlow_phi_ne_id`,
`kSectorDataFlow_phi_measurePreserving`. -/
theorem exists_kSectorData_nontrivial_flow [NeZero N] (p₀ : CPN N) :
    ∃ d : CSD.LF2.SectorData (KSigma N) (CPN N) (Matrix.unitaryGroup (Fin N) ℂ),
      d.toOntic.Φ ≠ id
        ∧ MeasurePreserving d.toOntic.Φ (kMuL p₀) (kMuL p₀) :=
  ⟨kSectorDataFlow p₀ (((1 : ℝ) / 2 : ℝ), 0),
    kSectorDataFlow_phi_ne_id p₀ halfShift_ne_zero,
    kSectorDataFlow_phi_measurePreserving p₀ _⟩

/-- **Fully concrete corollary: nontrivial dynamics on the qubit sector.**
The dynamics package on `ℂℙ¹` (`N = 2`) is inhabited by a non-identity
Liouville-preserving flow, at every base point. -/
theorem qubit_dynamics_witness (p₀ : CPN 2) :
    ∃ d : CSD.LF2.SectorData (CPN 2) (CPN 2) (Matrix.unitaryGroup (Fin 2) ℂ),
      d.toOntic.Φ ≠ id
        ∧ MeasurePreserving d.toOntic.Φ (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀) :=
  exists_cpSectorData_nontrivial_flow one_lt_two p₀

/-! ## Theorem-chain execution: the frequency capstone on honest trials -/

/-- Indicator statistics of evolved coordinate trials are pairwise
independent: the `hindep` shape of the flow frequency capstones, discharged
on the honest product measure. -/
theorem pairwise_flow_indicator_indep {σ : Type*} [MeasurableSpace σ]
    (μ : Measure σ) [IsProbabilityMeasure μ]
    {Φ : σ → σ} (hΦ : Measurable Φ) {O : Set σ} (hO : MeasurableSet O) :
    Pairwise
      (Function.onFun
        (fun f g : (ℕ → σ) → ℝ => IndepFun f g (Measure.infinitePi fun _ : ℕ => μ))
        (fun n => Set.indicator ((Φ ∘ fun ω : ℕ → σ => ω n) ⁻¹' O)
          (fun _ => (1 : ℝ)))) := by
  have h := pairwise_indepFun_comp_eval μ
    (fun _ => Set.indicator (Φ ⁻¹' O) (fun _ => (1 : ℝ)))
    (fun _ => measurable_const.indicator (hO.preimage hΦ))
  intro i j hij
  have hi : (Set.indicator ((Φ ∘ fun ω : ℕ → σ => ω i) ⁻¹' O) (fun _ => (1 : ℝ)))
      = fun ω : ℕ → σ => Set.indicator (Φ ⁻¹' O) (fun _ => (1 : ℝ)) (ω i) := by
    funext ω
    by_cases hm : Φ (ω i) ∈ O
    · rw [Set.indicator_of_mem
          (show ω ∈ (Φ ∘ fun ω' : ℕ → σ => ω' i) ⁻¹' O from hm),
        Set.indicator_of_mem (show ω i ∈ Φ ⁻¹' O from hm)]
    · rw [Set.indicator_of_notMem
          (show ω ∉ (Φ ∘ fun ω' : ℕ → σ => ω' i) ⁻¹' O from hm),
        Set.indicator_of_notMem (show ω i ∉ Φ ⁻¹' O from hm)]
  have hj : (Set.indicator ((Φ ∘ fun ω : ℕ → σ => ω j) ⁻¹' O) (fun _ => (1 : ℝ)))
      = fun ω : ℕ → σ => Set.indicator (Φ ⁻¹' O) (fun _ => (1 : ℝ)) (ω j) := by
    funext ω
    by_cases hm : Φ (ω j) ∈ O
    · rw [Set.indicator_of_mem
          (show ω ∈ (Φ ∘ fun ω' : ℕ → σ => ω' j) ⁻¹' O from hm),
        Set.indicator_of_mem (show ω j ∈ Φ ⁻¹' O from hm)]
    · rw [Set.indicator_of_notMem
          (show ω ∉ (Φ ∘ fun ω' : ℕ → σ => ω' j) ⁻¹' O from hm),
        Set.indicator_of_notMem (show ω j ∉ Φ ⁻¹' O from hm)]
  show IndepFun
    (Set.indicator ((Φ ∘ fun ω : ℕ → σ => ω i) ⁻¹' O) (fun _ => (1 : ℝ)))
    (Set.indicator ((Φ ∘ fun ω : ℕ → σ => ω j) ⁻¹' O) (fun _ => (1 : ℝ)))
    (Measure.infinitePi fun _ : ℕ => μ)
  rw [hi, hj]
  exact h hij

/-- **WS-J theorem-chain execution.** The production flow frequency capstone
`cpSectorDataFlow_frequency_convergence` fired on **honest trials**: explicit
`Measure.infinitePi` coordinate sampling from the Fubini–Study measure, law
and independence discharged by Mathlib theorems. Empirical frequencies of any
measurable region on the states evolved by the instance's own `Φ ≠ id`
converge a.s. to the ontic volume ratio. -/
theorem cpSectorDataFlow_frequency_convergence_concrete [NeZero N]
    (p₀ : CPN N) (lam : Fin N → ℝ) (t : ℝ)
    {O : Set (CPN N)} (hO : MeasurableSet O) :
    ∀ᵐ ω ∂ (Measure.infinitePi fun _ : ℕ => fubiniStudyMeasure p₀),
      Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator
                (((cpSectorDataFlow p₀ lam t).toOntic.Φ ∘ fun ω : ℕ → CPN N => ω i) ⁻¹' O)
                (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        atTop
        (nhds (fubiniStudyMeasure p₀ O).toReal) := by
  refine cpSectorDataFlow_frequency_convergence (Ω := ℕ → CPN N)
    (Pr := Measure.infinitePi fun _ : ℕ => fubiniStudyMeasure p₀)
    p₀ lam t (fun n (ω : ℕ → CPN N) => ω n)
    (fun n => measurable_pi_apply n) (fun n => ?_) hO ?_
  · exact (measurePreserving_eval_infinitePi
      (fun _ : ℕ => fubiniStudyMeasure p₀) n).map_eq
  · exact pairwise_flow_indicator_indep (fubiniStudyMeasure p₀)
      (cpSectorDataFlow_phi_measurePreserving p₀ lam t).measurable hO

end Witnesses
end Tests
end CSD
