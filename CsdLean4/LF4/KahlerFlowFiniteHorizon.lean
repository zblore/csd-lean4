/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.KahlerFlowNoMixing
public import Mathlib.NumberTheory.WellApproximable

/-!
# The fibre flow has no finite-horizon escape either

**Category:** 3-CSD. This closes `Q12-d`'s **route 2** for the corpus's own fibre flow.

`W1` (`KahlerFlowNoMixing.lean`) kills the *asymptotic* mixing hypothesis for every flow the corpus
defines. The escape the scoping doc recommends is `Q12-d` route 2: weaken mixing to **finite-horizon
decorrelation** (`MeasureTheory.HasCorrelationDecayUpTo`), on the physical grounds that a real
environment decorrelates on a timescale rather than asymptotically, and that a unitary flow on a
large space can decorrelate for a long time before it recurs.

★★ `exists_lag_le_envelope` says that escape is **not available to `kFlow`**. The reason is
quantitative recurrence: **Dirichlet's approximation theorem** (`AddCircle.exists_norm_nsmul_le`)
returns `j • sh` to within `1/(n+1)` of the identity at some lag `j ≤ n`, for *every* shift. So the
correlation is back near its lag-zero value `1/2` at a lag bounded by a number depending only on how
close you want to get — and, crucially, **not on the horizon**. Enlarging `T` buys nothing, because
the return has already happened well inside it.

## What is uniform, and why that is the point

The lag bound `n` depends on `δ` alone: not on the shift `sh`, not on the base point `p₀`, and not
on the horizon `T`. Route 2's physical picture is "a big system wanders for a long time before
coming back". A torus shift has no such room — Dirichlet caps the return time — and the theorem says
so with a bound that is blind to every parameter one might hope to tune.

## ⚠️ Scope

* This is about **`kFlow`**, not about finite-horizon decorrelation in general. Route 2's engine
  (`blockPop_timeAverage_le_of_finiteHorizon`) is untouched and still correct; what is ruled out is
  instantiating its antecedent on the Kähler fibre shift. A flow with genuine room to wander is
  exactly what the corpus does not have.
* It is a statement about **the fibre observable**. A different observable could have smaller
  variance, but not zero — `fibreObs_variance_ne` — and the argument only needs the return.
* Nothing here says CSD cannot have a de-isolation flow with finite-horizon decorrelation. It says
  no flow currently in the corpus is one, which — with `W1` — leaves `Q12-d` with **no route that
  the corpus's present Σ-vocabulary can supply.**

Reference: `specs/q12-fibre-mechanism-scoping.md` (`Q12-d` route 2, `W1`);
`specs/equilibration-arc-plan.md` (E4/E6); `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace CSD
namespace LF4

variable {N : ℕ}

/-! ### The character's modulus of continuity at the identity -/

/-- The first character's deviation from `1`, on the circle. `shiftDev` is this read off the first
fibre angle. -/
noncomputable def charDev (x : MeasureTheory.Circ) : ℝ := ‖fourier 1 x - 1‖

@[simp] lemma charDev_apply (x : MeasureTheory.Circ) : charDev x = ‖fourier 1 x - 1‖ := rfl

@[simp] lemma charDev_zero : charDev 0 = 0 := by simp [charDev]

lemma continuous_charDev : Continuous charDev :=
  ((fourier 1).continuous.sub continuous_const).norm

lemma shiftDev_eq_charDev (v : KTorus) : shiftDev v = charDev v.1 := rfl

/-- **The modulus of continuity at the identity**: a small shift moves the character little. -/
lemma exists_charDev_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : MeasureTheory.Circ, ‖x‖ < η → charDev x < δ := by
  have hcont : ContinuousAt charDev 0 := continuous_charDev.continuousAt
  obtain ⟨η, hη, hx⟩ := Metric.continuousAt_iff.mp hcont δ hδ
  refine ⟨η, hη, fun x hxlt => ?_⟩
  have h := hx (by rwa [dist_eq_norm, sub_zero])
  rw [charDev_zero, Real.dist_eq, sub_zero] at h
  exact lt_of_le_of_lt (le_abs_self _) h

/-! ### Dirichlet: every shift returns, at a lag that does not depend on the shift -/

/-- ★ **The Dirichlet lag.** For any `δ > 0` there is a bound `n` — depending on `δ` alone — such
that **every** shift `sh` returns within `δ` of the identity, as the character sees it, at some lag
`j ≤ n`.

Uniformity in `sh` is what Dirichlet's theorem gives and what the finite-horizon argument needs:
there is no shift, however finely tuned, whose first near-return can be pushed past `n`. -/
lemma exists_dirichlet_lag {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ ∀ sh : KTorus, ∃ j, 1 ≤ j ∧ j ≤ n ∧ shiftDev (j • sh) < δ := by
  obtain ⟨η, hη, hchar⟩ := exists_charDev_lt hδ
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (1 / η)
  refine ⟨n₀ + 1, Nat.succ_pos _, fun sh => ?_⟩
  obtain ⟨j, hjmem, hj⟩ := AddCircle.exists_norm_nsmul_le sh.1 (Nat.succ_pos n₀)
  rw [mem_Icc] at hjmem
  refine ⟨j, hjmem.1, hjmem.2, ?_⟩
  -- the Dirichlet quality is below the modulus
  have hquality : (1 : ℝ) / ((n₀ : ℝ) + 1 + 1) < η := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hη] at hn₀
    nlinarith [hn₀, hη]
  have hjnorm : ‖j • sh.1‖ < η := by
    refine lt_of_le_of_lt ?_ hquality
    push_cast at hj ⊢
    linarith [hj]
  have hfst : (j • sh).1 = j • sh.1 := rfl
  rw [shiftDev_eq_charDev, hfst]
  exact hchar _ hjnorm

/-! ### The finite-horizon no-go -/

/-- ★★ **Finite-horizon decorrelation fails for the fibre flow too, and the horizon cannot help.**

For every `δ > 0` there is a lag bound `n` — depending on `δ` **alone** — such that on any horizon
`T > n`, a finite-horizon envelope for `kFlow sh` must already exceed `1/2 − δ` at some lag in
`[1, n]`. The bound is blind to the shift, to the base point, and to `T`.

This is `Q12-d` route 2 closed for `kFlow`. The escape's picture is a system that wanders long
enough to decorrelate before recurring; **Dirichlet caps the wandering**, so a torus shift never gets
the room. -/
theorem exists_lag_le_envelope {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ ∀ (p₀ : CPN N) (sh : KTorus) (ε : ℕ → ℝ) (T : ℕ), n < T →
      MeasureTheory.HasCorrelationDecayUpTo (kMuL p₀) (kFlow sh) (fibreObs (N := N)) ε T →
      ∃ j, 1 ≤ j ∧ j ≤ n ∧ 1 / 2 - δ ≤ ε j := by
  obtain ⟨n, hn, hlag⟩ := exists_dirichlet_lag hδ
  refine ⟨n, hn, fun p₀ sh ε T hT hdec => ?_⟩
  obtain ⟨j, hj1, hjn, hjd⟩ := hlag sh
  refine ⟨j, hj1, hjn, ?_⟩
  -- at lag `j` the correlation is still within `δ` of its lag-zero value `1/2`
  have hiter : (fun x : KSigma N => fibreObs x * fibreObs ((kFlow sh)^[j] x))
      = fun x : KSigma N => fibreObs x * fibreObs (kFlow (j • sh) x) :=
    funext fun x => by rw [kFlow_iterate]
  have hcorr : 1 / 2 - δ < ∫ x, fibreObs (N := N) x * fibreObs ((kFlow sh)^[j] x) ∂(kMuL p₀) := by
    have hbd := lt_of_le_of_lt (abs_fibreCorr_sub_le p₀ (j • sh)) hjd
    rw [abs_lt] at hbd
    rw [hiter, integral_fibreObs_sq p₀] at *
    linarith [hbd.1]
  -- and decay at the pair `(0, j)` bounds it by the envelope
  have hdj := hdec 0 j (by omega) (by omega)
  rw [show Nat.dist 0 j = j by simp [Nat.dist]] at hdj
  simp only [Function.iterate_zero_apply, integral_fibreObs] at hdj
  rw [show ((0 : ℝ)) ^ 2 = 0 by norm_num, sub_zero] at hdj
  have hle := le_abs_self (∫ x, fibreObs (N := N) x * fibreObs ((kFlow sh)^[j] x) ∂(kMuL p₀))
  linarith [hle, hdj, hcorr]

/-- ★★ The same statement with a number in it: there is a lag `n` such that **no** horizon past `n`
admits an envelope smaller than `1/4` throughout `[1, n]`. -/
theorem exists_lag_envelope_ge_quarter :
    ∃ n : ℕ, 0 < n ∧ ∀ (p₀ : CPN N) (sh : KTorus) (ε : ℕ → ℝ) (T : ℕ), n < T →
      MeasureTheory.HasCorrelationDecayUpTo (kMuL p₀) (kFlow sh) (fibreObs (N := N)) ε T →
      ∃ j, 1 ≤ j ∧ j ≤ n ∧ (1 : ℝ) / 4 ≤ ε j := by
  obtain ⟨n, hn, h⟩ := exists_lag_le_envelope (N := N) (δ := 1 / 4) (by norm_num)
  refine ⟨n, hn, fun p₀ sh ε T hT hdec => ?_⟩
  obtain ⟨j, h1, h2, h3⟩ := h p₀ sh ε T hT hdec
  exact ⟨j, h1, h2, by linarith⟩

end LF4
end CSD
