import CsdLean4.LF4.BornFS
import CsdLean4.LF4.MomentPushforward

/-!
# LF4 plan B (step 1): the moment marginal as a Haar marginal

Plan B is to discharge the hypothesis `h_uniform` of `fs_born_volume_ratio_qubit`
and `qubit_born_frequency_convergence`, i.e. to *prove*

```
(fun p => momentMap p 0)∗ fubiniStudyMeasure p₀ = uniform on [0,1].
```

Everything is finite-dimensional (`CPN N = ℂℙ^{N-1}`, `U(N)`); plan B is purely a
finite-dimensional measure computation — it does not touch CSD's finiteness.

This file lands the first, committable half: the **measure-level reduction**.
Since `fubiniStudyMeasure p₀ = (orbitMap p₀)∗ unitaryHaarProb` and
`momentMap (U • p₀) i = ‖(U·rep)ᵢ‖²/‖U·rep‖²` (`momentMap_orbit`), the moment
marginal *is* the Haar law of the squared-modulus ratio of `U` acting on a
representative:

```
(momentMap · i)∗ fubiniStudyMeasure p₀
  = (fun U => ‖(U·rep)ᵢ‖²/‖U·rep‖²)∗ unitaryHaarProb.
```

So `h_uniform` (for `i = 0`, `N = 2`) reduces exactly to: the Haar law of
`U ↦ ‖(U·rep)₀‖²/‖U·rep‖²` on `U(2)` is `Uniform[0,1]`. With a unit
representative `‖U·rep‖ = ‖rep‖`, this is "`|U₀₀|²` (the first squared-modulus of a
Haar-random unit column) is `Uniform[0,1]`" — the `Beta(1,1)` / Archimedes fact.

**Remaining (the hard core).** Proving that Haar marginal is uniform is the
genuine analytic content with no current Mathlib support: it routes through
either (Haar-orbit → uniform `S³`) + (uniform `S³` → `Uniform[0,1]`), or the
complex-Gaussian route (normalised Gaussian → uniform sphere; `|z₀|²/‖z‖² ~
Beta(1,1)`). Tools: `MeasureTheory.Constructions.HaarToSphere`,
`Probability.Distributions.Beta`/`Gaussian`. This is a multi-session build; see
`specs/carve-out-plan.md` Tranche M, plan B.
-/

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF4

variable {N : ℕ}

/-- **Plan B, step 1 (the reduction).** The moment-coordinate marginal of the
Fubini–Study measure equals the Haar law of the squared-modulus ratio of `U`
acting on a representative of `p₀`. Reduces `h_uniform` to a concrete
distributional statement about Haar unitaries. -/
theorem momentMap_pushforward_eq_haar_marginal (p₀ : CPN N) (i : Fin N) :
    Measure.map (fun p => momentMap p i) (fubiniStudyMeasure p₀)
      = Measure.map
          (fun U : Matrix.unitaryGroup (Fin N) ℂ =>
            ‖(Matrix.toEuclideanLin U.val p₀.rep) i‖ ^ 2
              / ‖Matrix.toEuclideanLin U.val p₀.rep‖ ^ 2)
          unitaryHaarProb := by
  rw [show fubiniStudyMeasure p₀ = Measure.map (orbitMap p₀) unitaryHaarProb from rfl,
      Measure.map_map (momentMap_measurable i) (orbit_map_measurable p₀)]
  congr 1
  funext U
  exact momentMap_orbit U p₀ i

end LF4
end CSD
