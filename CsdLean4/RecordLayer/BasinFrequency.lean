/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.GlobalBasin
public import CsdLean4.LF4.BornFrequencyPartition
public import CsdLean4.LF4.BornRegionUncond
public import CsdLean4.LF4.POVMVolume

/-!
# RecordLayer/BasinFrequency: frequencies converge to Born on the fibred arena

**Category:** 7-SigmaLayer (the record layer).

The corpus's frequency theorems all live on the **base**: i.i.d. draws from `fubiniStudyMeasure` on
`ℂℙ^{N−1}`, with events `bornRegion ψ _ i` (`born_frequency_convergence_N` and its `_uncond`
variants, 32 call sites across `Empirical/` and `LF6/`). The canonical A7 reading is **fibred**
(`globalBasin`, author decision 2026-08-02), and on that side there was no frequency theorem at all —
only the single-draw weight `globalBasin_born`.

That absence is what made the base-to-fibre migration look mechanical when it is not: the weights do
agree (`globalBasin_born`), but a frequency statement is an almost-sure limit over draws from a
*different measure on a different space*, so no amount of rewriting turns one into the other. This
module supplies the missing theorem, and with it the migration becomes an application rather than a
re-derivation.

## What is proved

★★ `globalBasin_born_frequency` — for i.i.d. draws from `epistemicMeasure [ψ]` on the fibred arena
`KSigma N`, the empirical frequencies of the global basins converge almost surely to the Born
weights `‖⟨eᵢ, ψ⟩‖²`.

★ `globalBasin_born_frequency_context` — the same for an arbitrary `ContextField`, converging to its
own rates. `globalBasin_prob` is generic in the field, so the frequency statement is too; the Born
case is the `momentContext` instance.

## ⚠️ It needs no positivity hypothesis, and that is not an accident

The base-side `born_frequency_convergence_N` carries `hpos : ∀ j, 0 < ‖⟨eⱼ, ψ⟩‖²` — a genericity
condition that had to be removed later by a separate engine (`BornRegionUncond.lean`). The fibred
statement never needs it: `globalBasin_born` holds unconditionally, and turning it into a real
number needs only `0 ≤ ‖·‖²`. Vanishing amplitudes give null basins whose frequencies converge to
`0`, which is their Born weight. So the fibred route is unconditional **by construction** rather
than by repair.

## The migration bridge

★ `globalBasin_toReal_eq_bornRegion_toReal` — the two routes give the *same number*, unconditionally.
This is the second half of the CR-4 toolkit: the frequency theorem above handles the a.s.-limit
statements, this handles the weight statements, and together they turn the base-to-fibre migration
into rewriting rather than re-deriving.

⚠️ Note which side needs what. The base-side value is `bornRegion_fs_measure_uncond`, itself the
repaired form of `bornRegion_fs_measure`, which carries a genericity hypothesis `hpos`. The fibred
side is `globalBasin_born` and needs nothing. So the bridge is stated unconditionally, and migrating
a statement across it can only *drop* hypotheses, never add them.

## References

`RecordLayer/GlobalBasin.lean` (`globalBasin`, `epistemicMeasure`, `globalBasin_prob`,
`globalBasin_born`, `momentContext`); `LF4/BornFrequencyPartition.lean`
(`born_frequency_convergence_partition` — the generic engine, in `SigmaSpace` and `μ`);
`LF4/BornFrequencyN.lean` (`born_frequency_convergence_N`, the base-side twin);
`specs/POSITS.md` (Posit 1 — the cell law the rates rest on); `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Filter Topology Matrix.UnitaryGroup

namespace CSD
namespace RecordLayer

open LF4
open CSD.LF2

variable {N : ℕ}

/-- ★ **Frequencies converge to the context's rates, on the fibred arena.** For i.i.d. draws from
`epistemicMeasure p` on `KSigma N`, the empirical frequency of the basin of outcome `i` converges
almost surely to that context field's rate at `p`.

Generic in the `ContextField`, exactly as `globalBasin_prob` is. -/
theorem globalBasin_born_frequency_context (c : ContextField N) (p : CPN N)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → KSigma N) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = epistemicMeasure p)
    (hindep : ∀ i : Fin N,
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n => Set.indicator ((X n) ⁻¹' globalBasin c i) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : Fin N,
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator ((X k) ⁻¹' globalBasin c i) (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (c.rate p i)) :=
  LF4.born_frequency_convergence_partition (globalBasin c)
    (fun i => measurableSet_globalBasin c i)
    (fun i => c.rate p i)
    (fun i => by rw [globalBasin_prob c i p, ENNReal.toReal_ofReal (c.nonneg p i)])
    X hX hlaw hindep

/-- ★★ **Born frequencies on the fibred arena.** For i.i.d. draws from `epistemicMeasure [ψ]`, the
empirical frequencies of the global basins converge almost surely to the Born weights
`‖⟨eᵢ, ψ⟩‖²`.

⚠️ **No positivity hypothesis.** The base-side twin `born_frequency_convergence_N` carries one and
needed a separate engine to shed it; here vanishing amplitudes give null basins whose frequencies
converge to `0`, which is their Born weight. Unconditional by construction. -/
theorem globalBasin_born_frequency (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → KSigma N) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = epistemicMeasure (Projectivization.mk ℂ ψ hψ0))
    (hindep : ∀ i : Fin N,
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
          (fun n => Set.indicator ((X n) ⁻¹' globalBasin (momentContext N) i)
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : Fin N,
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator ((X k) ⁻¹' globalBasin (momentContext N) i)
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)) :=
  LF4.born_frequency_convergence_partition (globalBasin (momentContext N))
    (fun i => measurableSet_globalBasin _ i)
    (fun i => ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)
    (fun i => by
      rw [globalBasin_born ψ hψ0 hψ i, ENNReal.toReal_ofReal (by positivity)])
    X hX hlaw hindep

/-! ### The POVM engine, on the fibred arena -/

/-- ★★ **POVM frequencies on the fibred arena.** The Naimark-dilated twin of
`LF4.povm_born_frequency_volume_uncond`: for i.i.d. draws from `epistemicMeasure [ψ']`, the summed
block frequencies converge to the POVM weight `P.weight ψ i`.

This is the engine the six POVM volume entries (trine, USD, SIC, SIC3, MUB3, qutrit-POVM) delegate
to, so migrating it carries all of them. Body is the base-side proof with one substitution: the
fibred frequency theorem in place of `born_frequency_convergence_N_uncond`. Everything after —
summing the block and identifying it with the POVM weight — is unchanged, because that part is
about the *dilated vector*, not about which measure the trials are drawn from. -/
theorem povm_born_frequency_basin {M : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : POVM N ι) (D : LF4.NaimarkDilation P)
    (ψ : EuclideanSpace ℂ (Fin N)) (e : (Fin N × ι) ≃ Fin (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (Matrix.toEuclideanLin D.V ψ))
    (hψ'0 : ψ' ≠ 0) (hnorm : ‖ψ'‖ = 1)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → KSigma (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = epistemicMeasure (Projectivization.mk ℂ ψ' hψ'0))
    (hindep : ∀ j : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => ProbabilityTheory.IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' globalBasin (momentContext (M + 1)) j)
          (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : ι,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin N,
            (∑ k ∈ Finset.range m,
                Set.indicator ((X k) ⁻¹' globalBasin (momentContext (M + 1)) (e (n, i)))
                  (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds (P.weight ψ i)) := by
  filter_upwards [globalBasin_born_frequency ψ' hψ'0 hnorm X hX hlaw hindep] with ω hω
  intro i
  have hlim := tendsto_finsetSum (Finset.univ : Finset (Fin N))
    (fun n (_ : n ∈ Finset.univ) => hω (e (n, i)))
  rwa [show (∑ n : Fin N, ‖inner ℂ (EuclideanSpace.single (e (n, i)) (1 : ℂ)) ψ'‖ ^ 2)
        = P.weight ψ i from by
      rw [LF4.povm_born_eq_block_sum P D ψ i, hψ'eq]
      exact Finset.sum_congr rfl (fun n _ => LF4.piLpCongrLeft_inner_single_sq e _ (n, i))] at hlim

/-! ### The migration bridge -/

/-- ★ **The two routes give the same number.** The fibred basin measure and the base-only Born-region
measure agree, unconditionally — both are `‖⟨eᵢ, ψ⟩‖²`.

This is what makes the base-to-fibre migration a rewrite. ⚠️ The base side arrives via
`bornRegion_fs_measure_uncond`, the repaired form of `bornRegion_fs_measure` (which carries a
genericity hypothesis `hpos`); the fibred side needs nothing. So crossing this bridge can only drop
hypotheses. -/
theorem globalBasin_toReal_eq_bornRegion_toReal {M : ℕ} (p₀ : CPN (M + 1))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) (i : Fin (M + 1)) :
    (epistemicMeasure (Projectivization.mk ℂ ψ hψ0)
        (globalBasin (momentContext (M + 1)) i)).toReal
      = (fubiniStudyMeasure p₀ (bornRegion ψ hψ0 i)).toReal := by
  rw [globalBasin_born ψ hψ0 hψ i,
    ENNReal.toReal_ofReal (by positivity),
    LF4.bornRegion_fs_measure_uncond p₀ ψ hψ0 hψ i]

end RecordLayer
end CSD
