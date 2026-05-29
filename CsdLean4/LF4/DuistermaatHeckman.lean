import CsdLean4.LF4.QubitBornFrequency

/-!
# LF4: the Duistermaat–Heckman pushforward axiom (qubit instance)

This file names, as a documented Mathlib-external **axiom**, the classical
geometric fact that discharges the `h_uniform` hypothesis of
`fs_born_volume_ratio_qubit` and `qubit_born_frequency_convergence`, making the
qubit Born-from-Kähler-volume results **unconditional**.

## The axiom

`fs_moment_pushforward_uniform`: the moment-map coordinate pushes the genuine
Fubini–Study measure on `ℂℙ¹` to the uniform measure on the polytope `[0,1]`:

```
(fun p => momentMap p 0)∗ fubiniStudyMeasure p₀ = volume.restrict [0,1].
```

This is the `N = 2` instance of **Duistermaat–Heckman** (the moment map of a
toric Kähler manifold pushes the Liouville measure to Lebesgue on the moment
polytope); equivalently, by `momentMap_pushforward_eq_haar_marginal`, it is
"`|U₀₀|²` is `Uniform[0,1]` for Haar `U(2)`" — **Archimedes' hat-box theorem** on
the Bloch sphere. It is classically true and elementary; the only reason it is an
axiom here is that the supporting measure theory (sphere/Dirichlet pushforwards)
is **not yet in Mathlib**.

## Why this is an honest boundary, not a Born import

Unlike `busch_effect_gleason` — which encodes the Born/trace-form rule itself —
this axiom is a **pure geometry statement about `μ_FS` and the moment map**; the
Born rule `‖⟨e₀, ψ⟩‖²` does not appear in it. The qubit results derive Born from
`{` Fubini–Study Kähler volume `+` this Duistermaat–Heckman geometry `+` the
*proved* moment-map identity `momentMap_mk_eq_inner_sq` `}`. So Born is genuinely
derived from the Kähler structure, with the geometric input named — paralleling
how `invariant_measure_uniqueness` is a named Mathlib-external boundary.

Everything is finite-dimensional (`ℂℙ¹`, `U(2)`); this does not touch CSD's
finiteness.

## Discharge path (plan B)

`momentMap_pushforward_eq_haar_marginal` (`MomentMarginal.lean`) already reduces
this axiom, in Lean, to the Haar marginal `|U₀₀|² ~ Uniform[0,1]`. Discharging it
is the scheduled Mathlib-infrastructure build (sphere/Gaussian/`Beta(1,1)`); see
`specs/carve-out-plan.md` Tranche M, plan B.
-/

open MeasureTheory ProbabilityTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF4

/-- **Duistermaat–Heckman / Archimedes axiom (qubit instance).** The moment-map
coordinate pushes the Fubini–Study measure on `ℂℙ¹` to the uniform measure on
`[0,1]`. Classically true (the `N=2` DH pushforward / Archimedes' hat-box);
Mathlib-external. A geometry fact about `μ_FS`, **not** a Born import. Discharge
target of plan B (`specs/carve-out-plan.md`). -/
axiom fs_moment_pushforward_uniform (p₀ : CPN 2) :
    Measure.map (fun p => momentMap p 0) (fubiniStudyMeasure p₀)
      = (volume : Measure ℝ).restrict (Set.Icc 0 1)

/-- **Unconditional qubit Born = Fubini–Study volume ratio on `ℂℙ¹`.** The
genuine `fubiniStudyMeasure` of the moment sublevel set at `[ψ]` equals the Born
weight `‖⟨e₀, ψ⟩‖²`. Cites the foundational triple + `fs_moment_pushforward_uniform`
(the DH/Archimedes geometry axiom); **no** `busch_effect_gleason`. -/
theorem fs_born_volume_ratio_qubit_uncond
    (p₀ : CPN 2) (ψ : EuclideanSpace ℂ (Fin 2)) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) :
    fubiniStudyMeasure p₀
        {p : CPN 2 | momentMap p 0 ≤ momentMap (Projectivization.mk ℂ ψ hψ0) 0}
      = ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single 0 (1 : ℂ)) ψ‖ ^ 2) :=
  fs_born_volume_ratio_qubit p₀ ψ hψ0 hψ (fs_moment_pushforward_uniform p₀)

/-- **Unconditional Busch-free qubit Born frequency convergence.** For i.i.d.
trials from the Fubini–Study measure on `ℂℙ¹`, the empirical frequency of the
moment sublevel outcome converges almost surely to the Born weight `‖⟨e₀, ψ⟩‖²`.
Cites the foundational triple + `fs_moment_pushforward_uniform`; **no**
`busch_effect_gleason`. The CSD thesis realised unconditionally for the qubit:
deterministic typicality + Born = Kähler volume ⟹ frequencies → Born. -/
theorem qubit_born_frequency_convergence_uncond
    (p₀ : CPN 2) (ψ : EuclideanSpace ℂ (Fin 2)) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 2) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep :
      Pairwise
        (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
          (fun n => Set.indicator
            ((X n) ⁻¹' {p : CPN 2 | momentMap p 0 ≤ momentMap (Projectivization.mk ℂ ψ hψ0) 0})
            (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr,
      Filter.Tendsto
        (fun M : ℕ =>
          (∑ i ∈ Finset.range M,
              Set.indicator
                ((X i) ⁻¹' {p : CPN 2 | momentMap p 0 ≤ momentMap (Projectivization.mk ℂ ψ hψ0) 0})
                (fun _ => (1 : ℝ)) ω) / (M : ℝ))
        Filter.atTop
        (nhds (‖inner ℂ (EuclideanSpace.single 0 (1 : ℂ)) ψ‖ ^ 2)) :=
  qubit_born_frequency_convergence p₀ ψ hψ0 hψ (fs_moment_pushforward_uniform p₀) X hX hlaw hindep

end LF4
end CSD
