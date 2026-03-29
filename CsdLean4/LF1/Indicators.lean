import CsdLean4.LF1.Trials
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory ProbabilityTheory Set

namespace CSD
namespace LF1

namespace OnticSetup

variable {Sigma : Type*} [MeasurableSpace Sigma] [Nonempty Sigma] (S : OnticSetup Sigma)

namespace TrialModel

variable {S}
variable {Ω : Type*} [MeasurableSpace Ω]
variable (T : S.TrialModel Ω)

/--
The indicator random variable for outcome region `O` on trial `n`.

Takes value `1` when the `n`-th sampled initial condition lies in the pullback
event associated with `O`, and `0` otherwise.
-/
noncomputable def indicatorRV (O : S.OutcomeRegion) (n : ℕ) : Ω → ℝ :=
  Set.indicator (T.trialEvent (S := S) O n) (fun _ => (1 : ℝ))

/-- Measurability of the indicator random variable. -/
lemma measurable_indicatorRV (O : S.OutcomeRegion) (n : ℕ) :
    Measurable (T.indicatorRV (S := S) O n) := by
  unfold indicatorRV
  exact measurable_const.indicator (T.measurable_trialEvent (S := S) O n)

/-- The indicator random variable takes value `1` on the event. -/
lemma indicatorRV_of_mem (O : S.OutcomeRegion) (n : ℕ) {ω : Ω}
    (hω : ω ∈ T.trialEvent (S := S) O n) :
    T.indicatorRV (S := S) O n ω = 1 := by
  unfold indicatorRV
  exact Set.indicator_of_mem hω (fun _ => (1 : ℝ))

/-- The indicator random variable takes value `0` off the event. -/
lemma indicatorRV_of_not_mem (O : S.OutcomeRegion) (n : ℕ) {ω : Ω}
    (hω : ω ∉ T.trialEvent (S := S) O n) :
    T.indicatorRV (S := S) O n ω = 0 := by
  unfold indicatorRV
  exact Set.indicator_of_notMem hω (fun _ => (1 : ℝ))

/-- Pointwise nonnegativity of the indicator random variable. -/
lemma indicatorRV_nonneg (O : S.OutcomeRegion) (n : ℕ) (ω : Ω) :
    0 ≤ T.indicatorRV (S := S) O n ω := by
  by_cases hω : ω ∈ T.trialEvent (S := S) O n
  · rw [T.indicatorRV_of_mem (S := S) O n hω]; norm_num
  · rw [T.indicatorRV_of_not_mem (S := S) O n hω]

/-- Pointwise upper bound by `1`. -/
lemma indicatorRV_le_one (O : S.OutcomeRegion) (n : ℕ) (ω : Ω) :
    T.indicatorRV (S := S) O n ω ≤ 1 := by
  by_cases hω : ω ∈ T.trialEvent (S := S) O n
  · rw [T.indicatorRV_of_mem (S := S) O n hω]
  · rw [T.indicatorRV_of_not_mem (S := S) O n hω]; norm_num

/-- The indicator random variable is bounded in absolute value by `1`. -/
lemma norm_indicatorRV_le_one (O : S.OutcomeRegion) (n : ℕ) (ω : Ω) :
    ‖T.indicatorRV (S := S) O n ω‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (T.indicatorRV_nonneg (S := S) O n ω)]
  exact T.indicatorRV_le_one (S := S) O n ω

/-- The indicator random variable is a.e. strongly measurable w.r.t. the trial measure. -/
lemma aestronglyMeasurable_indicatorRV (O : S.OutcomeRegion) (n : ℕ) :
    AEStronglyMeasurable (T.indicatorRV (S := S) O n)
      ((T.P : ProbabilityMeasure Ω) : Measure Ω) :=
  (T.measurable_indicatorRV (S := S) O n).aestronglyMeasurable

/--
The empirical average of the first `N` indicator variables for outcome `O`.
This is the object whose almost sure convergence is studied in `Convergence.lean`.
-/
noncomputable def empiricalFreq (O : S.OutcomeRegion) (N : ℕ) : Ω → ℝ :=
  fun ω => (∑ j ∈ Finset.range N, T.indicatorRV (S := S) O j ω) / N

/--
The indicator random variable is integrable with respect to the trial measure.

This follows from boundedness: `‖indicatorRV O n ω‖ ≤ 1` and the fact that
`T.trialMeasure` is a finite (probability) measure.
-/
lemma indicatorRV_integrable (O : S.OutcomeRegion) (n : ℕ) :
    Integrable (T.indicatorRV (S := S) O n) ((T.P : ProbabilityMeasure Ω) : Measure Ω) :=
  (integrable_const (1 : ℝ)).mono
    (T.measurable_indicatorRV (S := S) O n).aestronglyMeasurable
    (ae_of_all _ (fun ω => by
      simp only [norm_one]
      exact T.norm_indicatorRV_le_one (S := S) O n ω))

/--
All indicator random variables for a fixed outcome region have the same distribution.

This follows from `T.hLaw`: every trial `X n` has the same law (`prepMeasure`), so
the pushforward of the composed indicator through each `X n` is identical.
-/
lemma indicatorRV_identDistrib (O : S.OutcomeRegion) (n : ℕ) :
    IdentDistrib
      (T.indicatorRV (S := S) O n)
      (T.indicatorRV (S := S) O 0)
      ((T.P : ProbabilityMeasure Ω) : Measure Ω)
      ((T.P : ProbabilityMeasure Ω) : Measure Ω) := by
  -- Strategy: factor indicatorRV O m = f ∘ X m, where f is the fixed Sigma-valued indicator.
  -- Then identical distribution of X n and X 0 (both have law prepMeasure, by T.hLaw)
  -- lifts to identical distribution of f ∘ X n and f ∘ X 0 via IdentDistrib.comp.
  let f := Set.indicator (O.preEvent (S := S)) (fun _ => (1 : ℝ))
  have hfact : ∀ m, T.indicatorRV (S := S) O m = f ∘ T.X m := fun m => by
    funext ω
    simp only [indicatorRV, trialEvent, Function.comp, f]
    by_cases hω : T.X m ω ∈ O.preEvent (S := S)
    · rw [Set.indicator_of_mem (Set.mem_preimage.mpr hω), Set.indicator_of_mem hω]
    · rw [Set.indicator_of_notMem (fun h => hω (Set.mem_preimage.mp h)),
          Set.indicator_of_notMem hω]
  -- X n and X 0 are identically distributed: both have law prepMeasure
  have hXident : IdentDistrib (T.X n) (T.X 0)
        ((T.P : ProbabilityMeasure Ω) : Measure Ω)
        ((T.P : ProbabilityMeasure Ω) : Measure Ω) :=
    ⟨(T.measurable_X n).aemeasurable, (T.measurable_X 0).aemeasurable,
     by rw [T.hLaw n, T.hLaw 0]⟩
  -- Apply f to both sides
  rw [hfact n, hfact 0]
  exact hXident.comp (measurable_const.indicator (O.measurable_preEvent (S := S)))

end TrialModel

end OnticSetup

end LF1
end CSD
