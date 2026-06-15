import CsdLean4.LF4.QubitBornFrequency

/-!
# LF4: the Duistermaat–Heckman pushforward (qubit instance) — TOMBSTONE

**This file is a tombstone. It introduces NO axiom.** It formerly named, as a
Mathlib-external `axiom fs_moment_pushforward_uniform`, the qubit
Duistermaat–Heckman / Archimedes hat-box fact

```
(fun p => momentMap p 0)∗ fubiniStudyMeasure p₀ = volume.restrict [0,1]
```

(the `N = 2` instance: the moment map pushes the Fubini–Study measure on `ℂℙ¹`
to Lebesgue on the polytope `[0,1]`; equivalently `|U₀₀|² ~ Uniform[0,1]` for
Haar `U(2)`). That axiom was **discharged 2026-05-31** — it is now a *theorem*
of the same name, proved in `CsdLean4/LF4/MomentUniform.lean` via the Gaussian
route (Gaussian-induced `μ_FS` + moment-marginal change of variables), alongside
the foundational-triple-only `fs_born_volume_ratio_qubit_uncond` and
`qubit_born_frequency_convergence_uncond`. The general-`N` extension
(`fs_moment_joint_dirichlet_N`, `MomentDirichletN.lean`) is likewise a theorem.

The content moved downstream to break an import cycle (the discharge needs
`GaussianCP` / `MomentRatioUniform`, which would cycle if proved here). The
honest-boundary framing it once carried — that this is a pure geometry statement
about `μ_FS` and the moment map, in which the Born rule does not appear, so the
qubit Born value is genuinely derived from the Kähler structure — now holds
*unconditionally*, since the geometric input is proved rather than posited. See
the dated note below and `specs/carve-out-plan.md` Tranche M (plan B, CLOSED).
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
