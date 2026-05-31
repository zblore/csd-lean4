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

/-! ## Discharged (2026-05-31): no longer an axiom.

The Duistermaat–Heckman / Archimedes fact for the qubit —
`(momentMap · 0)∗ fubiniStudyMeasure p₀ = volume.restrict (Icc 0 1)` — was carried
here as `axiom fs_moment_pushforward_uniform`. It is now a *theorem* of the same
name, proved in `CsdLean4/LF4/MomentUniform.lean` (plan B: Gaussian-induced `μ_FS`
+ moment-marginal change of variables), alongside the foundational-triple-only
unconditional qubit Born results `fs_born_volume_ratio_qubit_uncond` and
`qubit_born_frequency_convergence_uncond`. This file no longer introduces any
axiom; its content moved downstream to break the import cycle (the discharge needs
`GaussianCP`/`MomentRatioUniform`, which would cycle if proved here). -/

end LF4
end CSD
