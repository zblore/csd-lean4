/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.KahlerFlow
public import CsdLean4.Mathlib.Dynamics.CompactGroupNoMixing
public import CsdLean4.Mathlib.Dynamics.CorrelationDecayWitness

/-!
# The Kähler fibre flow cannot mix either

**Category:** 3-CSD. This closes the second half of `W1`
(`specs/q12-fibre-mechanism-scoping.md`), and it is the `Q12-w` brick that scoping doc lists.

`W1` claims that **no flow the corpus defines** can supply the mixing hypothesis E4 needs. It was
half a theorem. The unitary base action was proved
(`CSD.Thermo.not_hasCorrelationDecay_blockPop_of_unitary`); the `T²` fibre shift `kFlow` was
asserted by analogy — "the identical argument applies" — and `kProjectedFlow` is `id`, which is the
periodic case. ★★ `not_hasCorrelationDecay_kFlow` supplies the missing half, so `W1` is now a
theorem across every flow the corpus has.

## What made it cheap

`MeasureTheory.not_hasCorrelationDecay_of_compactAddGroup` — the general statement extracted from
the unitary proof — does the work, and `to_additive` is what lets the *same* proof cover a
multiplicative group action and an **additive** torus shift. Three inputs remain:

* `kFlow_iterate` — iterating the shift `n` times is shifting by `n • sh`, which is the `hpow` the
  general theorem asks for;
* `abs_fibreCorr_sub_le` — a uniform modulus. The exact correlation is not needed: shifting moves
  the observable by `Re((e(v) − 1)·e(x))`, so the correlation moves by at most `‖e(v) − 1‖`, which
  is continuous and vanishes at `0`. That is `continuousAt_correlation_of_abs_sub_le_add`'s
  hypothesis, and it dodges every Fubini argument;
* `integral_fibreObs` and `integral_fibreObs_sq` — the variance, which does need the product
  structure, but only through `Measure.map_fst_prod` / `Measure.map_snd_prod` and `integral_map`.

The observable `fibreObs` is `cos 2π` of the first fibre angle, reused from
`MeasureTheory.circObs`. It was built as the *witness* observable for the doubling map (E5); here it
plays the opposite role, certifying that the fibre flow's correlations **cannot** decay. Same
function, opposite verdict — the difference is entirely in the map.

## ⚠️ What this does and does not close

It closes the **statement** of `W1`: the corpus's `Σ`-dynamics is compact-group translation
throughout, and compact-group translation cannot mix. It does **not** say CSD cannot have a mixing
de-isolation flow — it says no such flow is currently *in* the corpus, and that any escape must
leave compact-group translations. `Q12-d`'s route 2 (finite-horizon decorrelation,
`MeasureTheory.HasCorrelationDecayUpTo`) is untouched by this and remains the recommended escape:
this theorem kills the *asymptotic* antecedent only.

Reference: `specs/q12-fibre-mechanism-scoping.md` (`W1`, `Q12-w`, `Q12-d`);
`specs/equilibration-arc-plan.md` (E4/E6); `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace CSD
namespace LF4

variable {N : ℕ}

/-- **The fibre observable**: `cos 2π` of the first `T²` angle, as a function on `Σ`.

Reused from `MeasureTheory.circObs`, which the E5 witness built for the doubling map. It is the
simplest observable that sees the fibre and averages to zero. -/
noncomputable def fibreObs (p : KSigma N) : ℝ := MeasureTheory.circObs p.2.1

@[simp] lemma fibreObs_apply (p : KSigma N) : fibreObs p = MeasureTheory.circObs p.2.1 := rfl

lemma measurable_fibreObs : Measurable (fibreObs (N := N)) :=
  MeasureTheory.measurable_circObs.comp (measurable_fst.comp measurable_snd)

lemma abs_fibreObs_le_one (p : KSigma N) : |fibreObs p| ≤ 1 :=
  MeasureTheory.abs_circObs_le_one _

/-- **Iterating the shift is shifting by the multiple** — the `hpow` hypothesis of
`MeasureTheory.not_hasCorrelationDecay_of_compactAddGroup`. -/
lemma kFlow_iterate (sh : KTorus) (n : ℕ) (p : KSigma N) :
    (kFlow sh)^[n] p = kFlow (n • sh) p := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [kFlow_apply, succ_nsmul', Prod.mk.injEq, true_and]
    rw [add_assoc]

/-! ### The fibre marginal, and the variance it gives -/

/-- `Σ`'s first fibre angle is uniform: the pushforward of `μL` along it is Lebesgue on the circle.

Both projections are probability-measure marginals, so this is `Measure.map_snd_prod` followed by
`Measure.map_fst_prod`. -/
lemma map_fibreCoord (p₀ : CPN N) :
    (kMuL p₀).map (fun p : KSigma N => p.2.1) = (volume : Measure MeasureTheory.Circ) := by
  have hmeas : Measurable (fun p : KSigma N => p.2.1) := measurable_fst.comp measurable_snd
  have hstep : (fun p : KSigma N => p.2.1) = Prod.fst ∘ Prod.snd := rfl
  rw [hstep, ← Measure.map_map measurable_fst measurable_snd, kMuL, Measure.map_snd_prod,
    measure_univ, one_smul, Measure.volume_eq_prod, Measure.map_fst_prod, measure_univ, one_smul]

/-- Integrals of fibre functions reduce to integrals on the circle. -/
lemma integral_fibreCoord (p₀ : CPN N) {F : MeasureTheory.Circ → ℝ} (hF : Measurable F)
    (hbd : ∀ z, |F z| ≤ 1) :
    ∫ p, F p.2.1 ∂(kMuL p₀) = ∫ z, F z ∂(volume : Measure MeasureTheory.Circ) := by
  have hmeas : Measurable (fun p : KSigma N => p.2.1) := measurable_fst.comp measurable_snd
  have hint : Integrable F (volume : Measure MeasureTheory.Circ) :=
    Integrable.of_bound hF.aestronglyMeasurable 1
      (ae_of_all _ (fun z => by rw [Real.norm_eq_abs]; exact hbd z))
  rw [← map_fibreCoord (N := N) p₀, integral_map hmeas.aemeasurable hF.aestronglyMeasurable]

lemma integral_fibreObs (p₀ : CPN N) : ∫ p, fibreObs (N := N) p ∂(kMuL p₀) = 0 := by
  simp only [fibreObs_apply]
  rw [integral_fibreCoord p₀ MeasureTheory.measurable_circObs MeasureTheory.abs_circObs_le_one,
    MeasureTheory.integral_circObs]

lemma integral_fibreObs_sq (p₀ : CPN N) :
    ∫ p, fibreObs (N := N) p * fibreObs p ∂(kMuL p₀) = 1 / 2 := by
  have hbd : ∀ z : MeasureTheory.Circ,
      |MeasureTheory.circObs z * MeasureTheory.circObs z| ≤ 1 := by
    intro z
    rw [abs_mul]
    exact mul_le_one₀ (MeasureTheory.abs_circObs_le_one z) (abs_nonneg _)
      (MeasureTheory.abs_circObs_le_one z)
  have hm : Measurable
      (fun z : MeasureTheory.Circ => MeasureTheory.circObs z * MeasureTheory.circObs z) :=
    MeasureTheory.measurable_circObs.mul MeasureTheory.measurable_circObs
  simp only [fibreObs_apply]
  rw [integral_fibreCoord p₀ hm hbd, MeasureTheory.integral_circObs_sq]

/-- The fibre observable has nonzero variance: `⟨f²⟩ = 1/2` while `⟨f⟩ = 0`. -/
lemma fibreObs_variance_ne (p₀ : CPN N) :
    ∫ p, fibreObs (N := N) p * fibreObs p ∂(kMuL p₀)
      ≠ (∫ q, fibreObs (N := N) q ∂(kMuL p₀)) ^ 2 := by
  rw [integral_fibreObs_sq, integral_fibreObs]
  norm_num

/-! ### The modulus, and the no-go -/

/-- The deviation of a shift from the identity, as the character sees it. -/
noncomputable def shiftDev (v : KTorus) : ℝ := ‖fourier 1 v.1 - 1‖

@[simp] lemma shiftDev_apply (v : KTorus) : shiftDev v = ‖fourier 1 v.1 - 1‖ := rfl

lemma continuous_shiftDev : Continuous shiftDev :=
  (((fourier 1).continuous.comp continuous_fst).sub continuous_const).norm

@[simp] lemma shiftDev_zero : shiftDev 0 = 0 := by simp [shiftDev]

/-- ★ **The correlation moves by at most `shiftDev v`.** Shifting the fibre replaces the character
`e(x)` by `e(v)·e(x)`, so the observable moves by `Re((e(v) − 1)·e(x))`, whose size is `‖e(v) − 1‖`
because characters have modulus one. The uniform bound then integrates directly.

This is what makes the exact correlation unnecessary — continuity at `0` is all the general no-go
asks for. -/
lemma abs_fibreCorr_sub_le (p₀ : CPN N) (v : KTorus) :
    |(∫ p, fibreObs (N := N) p * fibreObs (kFlow v p) ∂(kMuL p₀))
        - (∫ p, fibreObs (N := N) p * fibreObs p ∂(kMuL p₀))| ≤ shiftDev v := by
  have hpt : ∀ p : KSigma N,
      ‖fibreObs p * fibreObs (kFlow v p) - fibreObs p * fibreObs p‖ ≤ shiftDev v := by
    intro p
    have hchar : fibreObs (kFlow v p) - fibreObs p
        = ((fourier 1 v.1 - 1) * fourier 1 p.2.1).re := by
      simp only [fibreObs_apply, kFlow_apply, MeasureTheory.circObs, Prod.fst_add,
        MeasureTheory.fourier_arg_add, sub_mul, one_mul, Complex.sub_re]
    have hbound : |fibreObs (kFlow v p) - fibreObs p| ≤ shiftDev v := by
      rw [hchar]
      refine le_trans (Complex.abs_re_le_norm _) ?_
      rw [norm_mul, MeasureTheory.norm_fourier_one, mul_one, shiftDev_apply]
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
    calc |fibreObs p| * |fibreObs (kFlow v p) - fibreObs p|
        ≤ 1 * shiftDev v :=
          mul_le_mul (abs_fibreObs_le_one p) hbound (abs_nonneg _) zero_le_one
      _ = shiftDev v := one_mul _
  have hcoord : Measurable (fun p : KSigma N => p.2.1) := measurable_fst.comp measurable_snd
  have hm1 : Measurable (fun p : KSigma N => fibreObs p * fibreObs (kFlow v p)) :=
    (MeasureTheory.measurable_circObs.comp hcoord).mul
      (MeasureTheory.measurable_circObs.comp ((measurable_const_add v.1).comp hcoord))
  have hm2 : Measurable (fun p : KSigma N => fibreObs p * fibreObs p) :=
    (MeasureTheory.measurable_circObs.comp hcoord).mul
      (MeasureTheory.measurable_circObs.comp hcoord)
  have hbd1 : ∀ p : KSigma N, ‖fibreObs p * fibreObs (kFlow v p)‖ ≤ 1 := by
    intro p
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_one₀ (abs_fibreObs_le_one p) (abs_nonneg _) (abs_fibreObs_le_one _)
  have hbd2 : ∀ p : KSigma N, ‖fibreObs p * fibreObs p‖ ≤ 1 := by
    intro p
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_one₀ (abs_fibreObs_le_one p) (abs_nonneg _) (abs_fibreObs_le_one p)
  rw [← integral_sub
    (Integrable.of_bound hm1.aestronglyMeasurable 1 (ae_of_all _ hbd1))
    (Integrable.of_bound hm2.aestronglyMeasurable 1 (ae_of_all _ hbd2))]
  simpa using norm_integral_le_of_norm_le_const (μ := kMuL p₀) (ae_of_all _ hpt)

/-- ★★ **`W1`'s missing half: the Kähler fibre flow cannot have decaying correlations.**

For any base point and any shift `sh`, the fibre observable has no summable decay envelope along
`kFlow sh`. With `CSD.Thermo.not_hasCorrelationDecay_blockPop_of_unitary` for the base action and
`HasCorrelationDecay.integral_mul_self_eq_of_periodic` for `kProjectedFlow = id`, **every flow the
corpus defines is now covered by a theorem**, which is what `W1` asserted and half-proved.

⚠️ Read it as a limitation on the *route*, not on CSD. Mixing systems exist —
`MeasureTheory.circ_hasCorrelationDecay` is one — and they are precisely the ones that are not
compact-group translations. What is ruled out is deriving the first-passage race from *asymptotic*
mixing of any dynamics the corpus currently has; the finite-horizon escape
(`MeasureTheory.HasCorrelationDecayUpTo`, `Q12-d` route 2) is untouched. -/
theorem not_hasCorrelationDecay_kFlow (p₀ : CPN N) (sh : KTorus) {ε : ℕ → ℝ}
    (hsum : Summable ε) :
    ¬ MeasureTheory.HasCorrelationDecay (kMuL p₀) (kFlow sh) (fibreObs (N := N)) ε :=
  MeasureTheory.not_hasCorrelationDecay_of_compactAddGroup (kMuL p₀) kFlow fibreObs sh
    (fun n p => kFlow_iterate sh n p)
    (MeasureTheory.continuousAt_correlation_of_abs_sub_le_add _ _ _ continuous_shiftDev
      shiftDev_zero (fun p => by simp) (abs_fibreCorr_sub_le p₀))
    (fibreObs_variance_ne p₀) hsum

end LF4
end CSD
