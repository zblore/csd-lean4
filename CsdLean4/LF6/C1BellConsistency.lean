/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF3.SharedContextMap
public import CsdLean4.LF6.ForcedContextuality

/-!
# LF6/C1BellConsistency: no compatible global CHSH assignment

**Category:** 6-Entanglement (the C1 four-answer obstruction).

`LF3/ContextMap.lean` used to claim that `ContextIndexedOutcomeMaps` and
`GlobalCHSHAssignment` "being different types carries the Bell-consistency
content". **That is false**: different structures establish only definitional
separation. This module supplies the actual obstruction, on the shared state
space `Λ` that C1 posits.

* `CompatibleWithGlobalCHSH` — at each of the four CHSH contexts, the joint
  outcome's components *are* the global assignment's setting-local responses.
* ★★ `no_compatible_global_chsh_assignment_realises_singlet` — no measurable
  shared-context outcome family compatible with any global assignment
  reproduces the singlet correlations at the four CHSH settings.
* `compatibleGlobalCHSH_nonvacuous` — the predicate is inhabited, so the no-go
  is a **separation** and not an artefact of an unsatisfiable hypothesis. This
  mirrors `productPartition_nonvacuous`, which exists for the same reason.

## What is and is not assumed

Measurability is assumed **only** of the object C1 posits, the shared-context
outcome family `F`. The four setting-local responses of the global assignment
are *derived* measurable from that plus compatibility, via
`SharedContextOutcomeMaps.measurable_wingA/B`. Nothing here assumes the global
assignment is measurable.

Only the **four CHSH settings** are constrained. The theorem does not require
the singlet to be reproduced at every detector setting, so it is strictly weaker
in hypothesis than `no_product_partition_realises_singlet` and does not subsume
it.

## References

`LF3/SharedContextMap.lean`; `LF3/ContextMap.lean` (`GlobalCHSHAssignment`);
`LF6/ForcedContextuality.lean` (`no_product_partition_realises_singlet`);
`Empirical/QM/Crypto/E91.lean` (`lhvCHSH_abs_le_two`);
`specs/c1-correction-plan.md` §3 D1, D2.
-/

@[expose] public section

open MeasureTheory
open CSD.LF3

namespace CSD.LF6

open CSD.Empirical.QM.E91 CSD.Empirical.Bell

variable {Λ : Type*} [MeasurableSpace Λ]

/-- The A-wing setting selected by `i : Fin 2` in the CHSH quadruple. -/
noncomputable def chshSettingA (i : Fin 2) : DetectorSetting :=
  if i = 0 then chshA else chshA'

/-- The B-wing setting selected by `j : Fin 2` in the CHSH quadruple. -/
noncomputable def chshSettingB (j : Fin 2) : DetectorSetting :=
  if j = 0 then chshB else chshB'

/-- The four CHSH measurement contexts. -/
noncomputable def chshContext (i j : Fin 2) : MeasurementContext :=
  ⟨chshSettingA i, chshSettingB j⟩

/-- The global assignment's A-wing response at index `i`. -/
def globalA (G : GlobalCHSHAssignment Λ) (i : Fin 2) (l : Λ) : Sign :=
  if i = 0 then G.A1 l else G.A2 l

/-- The global assignment's B-wing response at index `j`. -/
def globalB (G : GlobalCHSHAssignment Λ) (j : Fin 2) (l : Λ) : Sign :=
  if j = 0 then G.B1 l else G.B2 l

/-- **Compatibility.** At each of the four CHSH contexts the shared-context
outcome map's components are exactly the global assignment's setting-local
responses. This is compatibility of the local *components*, not merely the
existence of some map carrying four context-labelled results. -/
def CompatibleWithGlobalCHSH (S : SharedContextOutcomeMaps Λ)
    (G : GlobalCHSHAssignment Λ) : Prop :=
  ∀ (i j : Fin 2) (l : Λ), S.F (chshContext i j) l = (globalA G i l, globalB G j l)

/-- **Reproducing the singlet at the four CHSH contexts.** -/
noncomputable def ReproducesSingletAtCHSH (μ : Measure Λ)
    (S : SharedContextOutcomeMaps Λ) : Prop :=
  ∀ i j : Fin 2,
    ∫ l, ((S.wingA (chshContext i j) l).val : ℝ) * ((S.wingB (chshContext i j) l).val : ℝ) ∂μ
      = correlation (chshSettingA i) (chshSettingB j)

/-! ### The obstruction -/

omit [MeasurableSpace Λ] in
/-- Compatibility identifies the A-wing component with the global response. -/
lemma wingA_eq_globalA {S : SharedContextOutcomeMaps Λ} {G : GlobalCHSHAssignment Λ}
    (hcomp : CompatibleWithGlobalCHSH S G) (i j : Fin 2) (l : Λ) :
    S.wingA (chshContext i j) l = globalA G i l := by
  rw [SharedContextOutcomeMaps.wingA, hcomp i j l]

omit [MeasurableSpace Λ] in
/-- Compatibility identifies the B-wing component with the global response. -/
lemma wingB_eq_globalB {S : SharedContextOutcomeMaps Λ} {G : GlobalCHSHAssignment Λ}
    (hcomp : CompatibleWithGlobalCHSH S G) (i j : Fin 2) (l : Λ) :
    S.wingB (chshContext i j) l = globalB G j l := by
  rw [SharedContextOutcomeMaps.wingB, hcomp i j l]

/-- ★★ **The C1 four-answer obstruction.**

No measurable shared-context outcome family compatible with any global CHSH
assignment reproduces the singlet correlations at the four CHSH settings.

Measurability is assumed only of `S` — the object C1 posits — and the four
setting-local responses are derived from it. -/
theorem no_compatible_global_chsh_assignment_realises_singlet
    (μ : Measure Λ) [IsProbabilityMeasure μ]
    (S : SharedContextOutcomeMaps Λ) (G : GlobalCHSHAssignment Λ)
    (hS : MeasurableSharedContextOutcomeMaps S)
    (hcomp : CompatibleWithGlobalCHSH S G)
    (hrep : ReproducesSingletAtCHSH μ S) :
    False := by
  refine absurd (lhvCHSH_abs_le_two (Λ := Λ) (SettingA := Fin 2) (SettingB := Fin 2) μ
    (fun i l => ((globalA G i l).val : ℝ)) (fun j l => ((globalB G j l).val : ℝ))
    ?_ ?_ ?_ ?_ 0 1 0 1) ?_
  · -- A-wing measurability, DERIVED from `hS` and compatibility
    intro i
    have h := S.measurable_wingA_val hS (chshContext i 0)
    have he : (fun l => ((S.wingA (chshContext i 0) l).val : ℝ))
        = fun l => ((globalA G i l).val : ℝ) := by
      funext l; rw [wingA_eq_globalA hcomp i 0 l]
    rwa [he] at h
  · -- B-wing measurability, DERIVED
    intro j
    have h := S.measurable_wingB_val hS (chshContext 0 j)
    have he : (fun l => ((S.wingB (chshContext 0 j) l).val : ℝ))
        = fun l => ((globalB G j l).val : ℝ) := by
      funext l; rw [wingB_eq_globalB hcomp 0 j l]
    rwa [he] at h
  · exact fun i l => sign_val_eq_one_or _
  · exact fun j l => sign_val_eq_one_or _
  · -- the CHSH combination is the singlet's, which exceeds the LHV cap
    have hcorr : ∀ i j : Fin 2,
        lhvCorrelation μ (fun i l => ((globalA G i l).val : ℝ))
          (fun j l => ((globalB G j l).val : ℝ)) i j
          = correlation (chshSettingA i) (chshSettingB j) := by
      intro i j
      rw [← hrep i j]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun l => ?_))
      simp only [wingA_eq_globalA hcomp, wingB_eq_globalB hcomp]
    have hval : lhvCHSH μ (fun i l => ((globalA G i l).val : ℝ))
        (fun j l => ((globalB G j l).val : ℝ)) 0 1 0 1
        = chshOperator chshA chshA' chshB chshB' := by
      unfold lhvCHSH chshOperator
      rw [hcorr 0 0, hcorr 0 1, hcorr 1 0, hcorr 1 1]
      simp only [chshSettingA, chshSettingB]
      norm_num
    rw [hval, chsh_singlet_at_optimal_angles]
    have hpos : (0 : ℝ) < 2 * Real.sqrt 2 := by positivity
    rw [abs_neg, abs_of_pos hpos]
    have h1 : (1 : ℝ) < Real.sqrt 2 := by
      have h := Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (1 : ℝ) < 2)
      rwa [Real.sqrt_one] at h
    intro hle
    linarith

/-! ### Non-vacuity -/

/-- **Non-vacuity of the obstruction.** Compatible measurable shared-context
families *exist* and reproduce *some* correlation — just not the singlet's. The
all-`plus` family is compatible with the all-`plus` global assignment and has
constant correlation `1`; the singlet correlation `−a·b` is non-constant, so it
does not reproduce the singlet.

So `no_compatible_global_chsh_assignment_realises_singlet` is a genuine
**separation** and not an artefact of an unsatisfiable predicate. This mirrors
`productPartition_nonvacuous`, which exists for exactly the same reason. -/
theorem compatibleGlobalCHSH_nonvacuous (μ : Measure Λ) [IsProbabilityMeasure μ] :
    ∃ (S : SharedContextOutcomeMaps Λ) (G : GlobalCHSHAssignment Λ),
      MeasurableSharedContextOutcomeMaps S ∧ CompatibleWithGlobalCHSH S G ∧
      ∀ i j : Fin 2,
        ∫ l, ((S.wingA (chshContext i j) l).val : ℝ)
            * ((S.wingB (chshContext i j) l).val : ℝ) ∂μ = 1 := by
  refine ⟨⟨fun _ _ => (Sign.plus, Sign.plus)⟩,
    ⟨fun _ => Sign.plus, fun _ => Sign.plus, fun _ => Sign.plus, fun _ => Sign.plus⟩,
    fun _ => measurable_const, ?_, ?_⟩
  · intro i j l
    fin_cases i <;> fin_cases j <;> rfl
  · intro i j
    show ∫ _ : Λ, ((Sign.plus.val : ℝ) * (Sign.plus.val : ℝ)) ∂μ = 1
    simp [Sign.val]

end CSD.LF6

