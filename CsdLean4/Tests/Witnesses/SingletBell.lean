/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.SingletKahler
public import CsdLean4.LF6.C1BellConsistency
public import CsdLean4.LF6.GisinTheorem
public import CsdLean4.Tests.Witnesses.IIDSampling

/-!
# WS-E/H witness: the concrete singlet preparation and the Bell obstruction

**Category:** Special (validation-hardening witness suite,
`specs/validation-hardening-plan.md` WS-E+H — the priority physics witness).

`Tests/Examples.lean`'s LF3 section is an API-shape smoke test: the chain
capstones applied to an **abstract** `PureSingletPreparation` with **abstract**
trials. The production corpus has since supplied the concrete bundle
(`LF4.ofKählerPreparation`, on `KSigma 4` — every field proved, Gleason-free),
still consumed with abstract trials. This module closes both gaps at a fully
concrete measurement context:

* `perpContext` — explicit perpendicular detector axes `a = ẑ`, `b = x̂`
  (via `LF6.detector3`), with `P_st = 1/4` **computed** for all four outcomes
  and the genericity hypothesis `hgen` **discharged**, not assumed;
* `P_st_setting_dependent` — nontriviality: the kernel is genuinely
  setting-dependent (parallel axes give `P_{++} = 0 ≠ 1/4`), so the limit
  below is not a constant of the kernel;
* `perpContext_singlet_frequency_convergence` — **the LF3 chain capstone
  on a fully concrete model**: concrete sector (`kSectorData p₀`), concrete
  preparation (`ofKählerPreparation`), concrete context (`perpContext`), and
  **honest trials** (`Measure.infinitePi` coordinate sampling from the
  preparation's own fibre law `μψ`, independence a theorem) — empirical
  per-sector frequencies converge a.s. to the singlet value `1/4`;
* `kMuPsi_no_global_chsh_assignment` / `kMuPsi_chsh_obstruction_nonvacuous` —
  **the C1 Bell obstruction instantiated on the same concrete arena**
  `(KSigma 4, kMuPsi)`: no measurable shared-context family compatible with a
  global CHSH assignment reproduces the singlet correlations there, and the
  obstruction is populated (compatible families exist), so the separation is
  genuine on the witness space, not vacuous.

**Anti-duplication scope.** Everything is cited: the chain capstone
(`ofKählerPreparation_singlet_frequency_convergence`), the obstruction
(`no_compatible_global_chsh_assignment_realises_singlet`, which reduces to
E91's `lhvCHSH_abs_le_two`), and its non-vacuity
(`compatibleGlobalCHSH_nonvacuous`). The new content is the concrete context
with `hgen` discharged, the honest trials, and the composition.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open CSD.LF3 CSD.LF4 CSD.LF6

namespace CSD
namespace Tests
namespace Witnesses

/-! ## The concrete measurement context: perpendicular axes -/

/-- The concrete measurement context with perpendicular detector axes:
`a = ẑ = (0,0,1)`, `b = x̂ = (1,0,0)`. -/
noncomputable def perpContext : MeasurementContext :=
  ⟨detector3 0 0 1 (by norm_num), detector3 1 0 0 (by norm_num)⟩

/-- The perpendicular axes have vanishing dot product. -/
theorem perpContext_dotR : dotR perpContext.a perpContext.b = 0 := by
  show dotR (detector3 0 0 1 (by norm_num)) (detector3 1 0 0 (by norm_num)) = 0
  rw [dotR]
  simp

/-- **All four singlet outcome weights at the perpendicular context are
`1/4`** — computed from the kernel, not posited. -/
theorem perpContext_P_st (s t : Sign) :
    P_st perpContext.a perpContext.b s t = 1 / 4 := by
  rw [P_st, perpContext_dotR]
  ring

/-- The genericity hypothesis of the concrete Kähler preparation, discharged:
every outcome weight at the perpendicular context is positive. -/
theorem perpContext_hgen : ∀ s t : Sign, 0 < P_st perpContext.a perpContext.b s t := by
  intro s t
  rw [perpContext_P_st]
  norm_num

/-- **Nontriviality of the kernel at the witness context.** The singlet
kernel is genuinely setting-dependent: at *parallel* axes the `(+,+)` weight
is `0`, not the perpendicular context's `1/4`. So the convergence target
below reflects the context, not a constant of the construction. -/
theorem P_st_setting_dependent :
    ∃ (a b : DetectorSetting) (s t : Sign),
      P_st a b s t ≠ P_st perpContext.a perpContext.b s t := by
  refine ⟨detector3 0 0 1 (by norm_num), detector3 0 0 1 (by norm_num),
    Sign.plus, Sign.plus, ?_⟩
  rw [perpContext_P_st, P_st]
  have hdot : dotR (detector3 0 0 1 (by norm_num)) (detector3 0 0 1 (by norm_num)) = 1 := by
    rw [dotR]
    simp
  rw [hdot]
  norm_num [Sign.val]

/-! ## WS-E: the chain capstone on the fully concrete model, honest trials -/

/-- **WS-E headline: the LF3 singlet chain on a fully concrete model.**
Concrete sector (`kSectorData p₀` on `KSigma 4`), concrete preparation
(`ofKählerPreparation` — every bundle field proved), concrete context
(`perpContext`, `hgen` discharged), honest trials (`Measure.infinitePi`
coordinate sampling from the preparation's own fibre law, independence a
Mathlib theorem): the per-sector empirical frequencies converge almost surely
to the singlet value `1/4`, for all four outcome sectors. -/
theorem perpContext_singlet_frequency_convergence (p₀ : CPN 4) :
    ∀ s t : Sign,
      ∀ᵐ ω ∂ (Measure.infinitePi fun _ : ℕ =>
          (ofKählerPreparation perpContext p₀ perpContext_hgen).μψ),
        Tendsto
          (fun M : ℕ =>
            (∑ i ∈ Finset.range M,
                Set.indicator
                  ((fun ω : ℕ → KSigma 4 => ω i) ⁻¹'
                    ((ofKählerPreparation perpContext p₀ perpContext_hgen).O_region s t).preEvent)
                  (fun _ => (1 : ℝ)) ω) / (M : ℝ))
          atTop
          (nhds (1 / 4 : ℝ)) := by
  have := (ofKählerPreparation perpContext p₀ perpContext_hgen).hμψ_prob
  have h := ofKählerPreparation_singlet_frequency_convergence perpContext p₀ perpContext_hgen
    (Ω := ℕ → KSigma 4)
    (Pr := Measure.infinitePi fun _ : ℕ =>
      (ofKählerPreparation perpContext p₀ perpContext_hgen).μψ)
    (X := fun n (ω : ℕ → KSigma 4) => ω n)
    (fun n => measurable_pi_apply n)
    (fun n => (measurePreserving_eval_infinitePi
      (fun _ : ℕ => (ofKählerPreparation perpContext p₀ perpContext_hgen).μψ) n).map_eq)
    (fun s t => pairwise_indicator_eval_indep
      (ofKählerPreparation perpContext p₀ perpContext_hgen).μψ
      (((ofKählerPreparation perpContext p₀ perpContext_hgen).O_region s t).measurable_preEvent))
  intro s t
  have hst := h s t
  rw [perpContext_P_st s t] at hst
  exact hst

/-! ## WS-H: the Bell obstruction on the same concrete arena -/

/-- **WS-H headline: the C1 CHSH obstruction on the concrete Kähler singlet
arena.** On `(KSigma 4, kMuPsi)` — the very space and fibre law the WS-E
witness samples from — no measurable shared-context outcome family compatible
with a global CHSH assignment reproduces the singlet correlations at the four
CHSH settings. Instantiates
`no_compatible_global_chsh_assignment_realises_singlet` (which reduces to
E91's `lhvCHSH_abs_le_two`); the witness contribution is tying the
obstruction to the concrete arena. -/
theorem kMuPsi_no_global_chsh_assignment :
    ∀ (S : SharedContextOutcomeMaps (KSigma 4)) (G : GlobalCHSHAssignment (KSigma 4)),
      MeasurableSharedContextOutcomeMaps S →
      CompatibleWithGlobalCHSH S G →
      ReproducesSingletAtCHSH kMuPsi S →
      False :=
  fun S G hS hcomp hrep =>
    no_compatible_global_chsh_assignment_realises_singlet kMuPsi S G hS hcomp hrep

/-- **Non-vacuity on the concrete arena.** Compatible measurable
shared-context families exist on `(KSigma 4, kMuPsi)` (with constant
correlation `1`), so `kMuPsi_no_global_chsh_assignment` is a genuine
separation there, not an artefact of an unsatisfiable predicate. Instantiates
`compatibleGlobalCHSH_nonvacuous`. -/
theorem kMuPsi_chsh_obstruction_nonvacuous :
    ∃ (S : SharedContextOutcomeMaps (KSigma 4)) (G : GlobalCHSHAssignment (KSigma 4)),
      MeasurableSharedContextOutcomeMaps S ∧ CompatibleWithGlobalCHSH S G ∧
      ∀ i j : Fin 2,
        ∫ l, ((S.wingA (chshContext i j) l).val : ℝ)
            * ((S.wingB (chshContext i j) l).val : ℝ) ∂kMuPsi = 1 :=
  compatibleGlobalCHSH_nonvacuous kMuPsi

end Witnesses
end Tests
end CSD
