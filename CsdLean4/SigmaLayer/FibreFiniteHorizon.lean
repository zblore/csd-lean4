/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.FibreCoarseArrow
public import CsdLean4.Mathlib.Dynamics.CorrelationDecay

/-!
# Finite-horizon equilibration of the fibre cells

**Category:** 7-SigmaLayer.
BACKLOG #118(ii) — the one clause of `R-019`'s convergence half that row calls "plausibly a brick".

#18 proved the monotone decrease and showed it is *not* the content of relaxation: it holds for the
translation, which provably cannot decorrelate. #118 split what is left into three, and only (ii) was
priced as a brick — the **finite-horizon** statement, conditional on
`HasCorrelationDecayUpTo` rather than on asymptotic mixing. This is that statement, on the fibre.

* `fibreCellInd` — a cell's indicator as a bounded observable on `Σ`, with
  ★ `integral_fibreCellInd` identifying its space average as the **Haar cell law's** mass at that
  cell, which is what makes the conclusion a statement about the coarse-grained law;
* ★★★ `integral_birkhoffAverage_fibreCellInd_sub_sq_le` — **at horizon `T`, the mean-square
  deviation of a cell's time-averaged occupation from its Haar value is at most `(2/T)·Σ_{u<T} ε u`**;
* ★★★ `integral_sum_birkhoffAverage_fibreCellInd_sub_sq_le` — summed over all `(m+1)²` cells, which
  is the row's "rate in terms of the cell count `m`": the bound carries a factor `(m+1)²`;
* ★★★ `tendsto_integral_birkhoffAverage_fibreCellInd_sub_sq` — with a summable envelope the
  deviation tends to `0`, which is the convergence #118 asks for, in the finite-horizon reading.

## What this is and is not

⚠️ **It is time-averaged, not instantaneous — and that is the real finding.** The Cesàro estimate
controls the Birkhoff average over `[0, T)`, so what equilibrates here is a cell's *time-averaged*
occupation. `R-019` asks for the *law at step `n`* to approach Haar, which is a mixing statement, not
an ergodic one. So the finite-horizon escape buys an ergodic conclusion and leaves the mixing one
untouched: it is genuinely weaker than `R-019`, exactly as #118 recorded, and no amount of
sharpening the envelope closes that gap.

⚠️ **The hypothesis is assumed, not derived.** Whether the fibre's *cell indicators* satisfy
`HasCorrelationDecayUpTo` is #118(i), a genuine mathematical question: the corpus has decay for the
single observable `catObs` (`catStroke_hasCorrelationDecay`, finitely supported), and extending it to
indicators is a statement about the cat map's spectral gap on indicator functions, which nothing here
supplies. Everything below travels with its hypothesis.

⚠️ **The cell count costs `(m+1)²`.** The summed bound degrades quadratically in the fineness of the
coarse-graining, so a finite-horizon statement at fixed horizon is *not* uniform in `m`. `R-019`'s
"rate set by the cell size" would need the envelope itself to improve with `m`, and that is not
available.

⚠️ **Not the `klDiv` form.** `R-019`'s second clause is about relative entropy. Since the Haar cell
law is uniform on these cells, `klDiv ≤ χ²` would convert the bound above at the cost of one more
factor `(m+1)²` — but it needs the time-averaged occupations packaged as a *measure*, measurably in
the base point, which is a restatement rather than new mathematics and is **#130**.

⚠️ **Not a Track B prediction.** Nothing here exhibits a fibre out of equilibrium returning to it,
and the translation comparison of #18 still applies: this theorem's hypothesis is what distinguishes
the maps, not its conclusion.

References: [`FibreCoarseArrow.lean`](FibreCoarseArrow.lean) (#18, `fibreCell`, `fibreStroke`),
[`CorrelationDecay.lean`](../Mathlib/Dynamics/CorrelationDecay.lean)
(`HasCorrelationDecayUpTo`, the Cesàro estimate),
[`KahlerFlowFiniteHorizon.lean`](../LF4/KahlerFlowFiniteHorizon.lean) (the same hypothesis for
`kFlow`, where Dirichlet obstructs it), [`MovingFibreWitness.lean`](MovingFibreWitness.lean)
(`relaxation_requires_hyperbolic_fibre`); `specs/BACKLOG.md` #118, #18, #130;
`specs/residues.tsv` `R-019`.
-/

@[expose] public section

open MeasureTheory InformationTheory Filter Set

noncomputable section

namespace CSD.SigmaLayer

open LF4

/-! ### A cell's indicator as an observable -/

/-- The indicator of one fibre cell, as a bounded real observable on `Σ`. -/
noncomputable def fibreCellInd {N : ℕ} (m : ℕ) (c : Fin (m + 1) × Fin (m + 1))
    (p : KSigma N) : ℝ :=
  Set.indicator (fibreCell (N := N) m ⁻¹' {c}) (fun _ => (1 : ℝ)) p

theorem measurableSet_fibreCell_preimage {N : ℕ} (m : ℕ) (c : Fin (m + 1) × Fin (m + 1)) :
    MeasurableSet (fibreCell (N := N) m ⁻¹' {c}) :=
  (measurable_fibreCell m) (measurableSet_singleton c)

theorem measurable_fibreCellInd {N : ℕ} (m : ℕ) (c : Fin (m + 1) × Fin (m + 1)) :
    Measurable (fibreCellInd (N := N) m c) :=
  measurable_const.indicator (measurableSet_fibreCell_preimage m c)

theorem abs_fibreCellInd_le {N : ℕ} (m : ℕ) (c : Fin (m + 1) × Fin (m + 1)) (p : KSigma N) :
    |fibreCellInd m c p| ≤ 1 := by
  classical
  rw [fibreCellInd, Set.indicator_apply]
  split_ifs <;> simp

/-- ★ **The space average is the Haar cell law's mass at the cell** — which is what makes the
estimates below statements about the coarse-grained law rather than about an arbitrary observable. -/
theorem integral_fibreCellInd {N : ℕ} (p₀ : CPN N) (m : ℕ) (c : Fin (m + 1) × Fin (m + 1)) :
    ∫ p, fibreCellInd m c p ∂(kMuL p₀)
      = (coarseLaw (kMuL p₀) (fibreCell (N := N) m) {c}).toReal := by
  have hfun : (fun p : KSigma N => fibreCellInd (N := N) m c p)
      = Set.indicator (fibreCell (N := N) m ⁻¹' {c}) (fun _ => (1 : ℝ)) := rfl
  rw [hfun, integral_indicator (measurableSet_fibreCell_preimage m c), setIntegral_const,
    coarseLaw_apply _ (measurable_fibreCell m) (measurableSet_singleton c), smul_eq_mul, mul_one,
    measureReal_def]

/-! ### The finite-horizon estimate on the fibre -/

/-- The stroke is measurable, which the Cesàro estimate needs. -/
theorem measurable_fibreStroke {N : ℕ} : Measurable (fibreStroke (N := N)) :=
  measurable_id.prodMap MeasureTheory.measurable_cat

/-- The space average is stationary along the stroke, because the stroke preserves `kMuL`. -/
theorem integral_iterate_fibreCellInd {N : ℕ} (p₀ : CPN N) (m : ℕ)
    (c : Fin (m + 1) × Fin (m + 1)) (t : ℕ) :
    ∫ p, fibreCellInd m c (fibreStroke^[t] p) ∂(kMuL p₀)
      = ∫ p, fibreCellInd m c p ∂(kMuL p₀) :=
  integral_iterate_of_measurePreserving (fibreStroke_measurePreserving p₀)
    (measurable_fibreCellInd m c).aestronglyMeasurable t

/-- ★★★ **Finite-horizon equilibration of one cell.** At horizon `T`, the mean-square deviation of
the cell's time-averaged occupation from its Haar value is at most `(2/T)·Σ_{u<T} ε u`.

The hypothesis is finite-horizon decay for that cell's indicator, which is #118(i) and is assumed
here. -/
theorem integral_birkhoffAverage_fibreCellInd_sub_sq_le {N : ℕ} (p₀ : CPN N) (m : ℕ)
    (c : Fin (m + 1) × Fin (m + 1)) {ε : ℕ → ℝ} {T : ℕ}
    (hdec : HasCorrelationDecayUpTo (kMuL p₀) fibreStroke (fibreCellInd m c) ε T) (hT : 0 < T) :
    ∫ p, (birkhoffAverage ℝ fibreStroke (fibreCellInd m c) T p
        - (coarseLaw (kMuL p₀) (fibreCell (N := N) m) {c}).toReal) ^ 2 ∂(kMuL p₀)
      ≤ 2 * (T : ℝ)⁻¹ * ∑ u ∈ Finset.range T, ε u := by
  rw [← integral_fibreCellInd p₀ m c]
  exact integral_birkhoffAverage_sub_sq_le_cesaro measurable_fibreStroke
    (measurable_fibreCellInd m c) zero_le_one (abs_fibreCellInd_le m c)
    (integral_iterate_fibreCellInd p₀ m c) hdec hT

/-- ★★★ **The rate in the cell count.** Summed over all `(m+1)²` cells under a common envelope the
bound carries a factor `(m+1)²`: a finite-horizon statement at fixed horizon is **not** uniform in
the fineness of the coarse-graining. -/
theorem integral_sum_birkhoffAverage_fibreCellInd_sub_sq_le {N : ℕ} (p₀ : CPN N) (m : ℕ)
    {ε : ℕ → ℝ} {T : ℕ}
    (hdec : ∀ c : Fin (m + 1) × Fin (m + 1),
      HasCorrelationDecayUpTo (kMuL p₀) fibreStroke (fibreCellInd m c) ε T) (hT : 0 < T) :
    ∑ c : Fin (m + 1) × Fin (m + 1),
        ∫ p, (birkhoffAverage ℝ fibreStroke (fibreCellInd m c) T p
          - (coarseLaw (kMuL p₀) (fibreCell (N := N) m) {c}).toReal) ^ 2 ∂(kMuL p₀)
      ≤ (m + 1) ^ 2 * (2 * (T : ℝ)⁻¹ * ∑ u ∈ Finset.range T, ε u) := by
  have hcard : (Finset.univ : Finset (Fin (m + 1) × Fin (m + 1))).card = (m + 1) ^ 2 := by
    simp [Finset.card_univ, pow_two]
  calc ∑ c : Fin (m + 1) × Fin (m + 1),
          ∫ p, (birkhoffAverage ℝ fibreStroke (fibreCellInd m c) T p
            - (coarseLaw (kMuL p₀) (fibreCell (N := N) m) {c}).toReal) ^ 2 ∂(kMuL p₀)
      ≤ ∑ _c : Fin (m + 1) × Fin (m + 1), 2 * (T : ℝ)⁻¹ * ∑ u ∈ Finset.range T, ε u :=
        Finset.sum_le_sum fun c _ =>
          integral_birkhoffAverage_fibreCellInd_sub_sq_le p₀ m c (hdec c) hT
    _ = (m + 1) ^ 2 * (2 * (T : ℝ)⁻¹ * ∑ u ∈ Finset.range T, ε u) := by
        rw [Finset.sum_const, hcard]
        ring

/-! ### The convergence, under a summable envelope -/

/-- ★★★ **The convergence #118 asks for, in the finite-horizon reading.** With asymptotic decay and
a summable envelope the time-averaged occupation of a cell converges in `L²` to its Haar value.

This is the honest target #118(ii) named: equilibration *conditional on decay*, time-averaged, with
the hypothesis doing the work. -/
theorem tendsto_integral_birkhoffAverage_fibreCellInd_sub_sq {N : ℕ} (p₀ : CPN N) (m : ℕ)
    (c : Fin (m + 1) × Fin (m + 1)) {ε : ℕ → ℝ}
    (hdec : HasCorrelationDecay (kMuL p₀) fibreStroke (fibreCellInd m c) ε)
    (hsum : Summable ε) :
    Tendsto (fun T : ℕ => ∫ p, (birkhoffAverage ℝ fibreStroke (fibreCellInd m c) T p
        - (coarseLaw (kMuL p₀) (fibreCell (N := N) m) {c}).toReal) ^ 2 ∂(kMuL p₀))
      atTop (nhds 0) := by
  rw [← integral_fibreCellInd p₀ m c]
  exact tendsto_integral_birkhoffAverage_sub_sq measurable_fibreStroke
    (measurable_fibreCellInd m c) zero_le_one (abs_fibreCellInd_le m c)
    (integral_iterate_fibreCellInd p₀ m c) hdec hsum

end CSD.SigmaLayer

end

end
