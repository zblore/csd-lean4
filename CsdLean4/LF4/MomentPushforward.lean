import CsdLean4.LF4.MomentMap
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudy

/-!
# LF4 Tranche M slice 2 (reduction): the moment map along the unitary orbit

To upgrade `born_eq_volume_ratio` from a Lebesgue ratio on the moment polytope to
a genuine **Fubini–Study volume ratio on the ontic Kähler `Σ = ℂℙ^{N-1}`**, the
one missing analytic input is the Duistermaat–Heckman pushforward

```
Φ∗ fubiniStudyMeasure = uniform on the simplex Δ_{N-1}.
```

The project's `fubiniStudyMeasure p₀` is the pushforward of the Haar probability
measure `unitaryHaarProb` under the orbit map `U ↦ U • p₀`
(`FubiniStudy.lean`). So `Φ∗ fubiniStudyMeasure` is the law, under Haar, of
`U ↦ momentMap (U • p₀)`. This file records the pointwise bridge that makes that
reduction precise: along the orbit, the moment map is the squared-modulus profile
of the acted representative.

**Consequence (the precise remaining target).** With `momentMap_orbit`, the
keystone becomes a concrete distributional statement about Haar unitaries: for a
unit representative, `momentMap (U • p₀) i = ‖(U · rep) i‖²` (since unitaries
preserve the norm), so

```
Φ∗ fubiniStudyMeasure = uniform_Δ   ⟺   (U ↦ (‖(U·rep)ᵢ‖²)ᵢ)∗ unitaryHaarProb = uniform_Δ,
```

i.e. **the squared-moduli of a Haar-random unit column are uniform on the
simplex** — the Dirichlet`(1,…,1)` law. For `N = 2` this is the single fact
"`|U₀₀|²` is `Uniform[0,1]` for Haar `U(2)`" (equivalently Archimedes' hat-box
theorem on the Bloch sphere). This is a genuine measure-theoretic computation with
no current Mathlib support (no sphere change-of-variables / Dirichlet law); it is
**not** a one-line Archimedes invocation given how `fubiniStudyMeasure` is built.
See `specs/carve-out-plan.md` Tranche M slice 2.

**Category:** 1-Mathlib adjacent; kept in `CSD.LF4` for the carve-out programme.
-/

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF4

variable {N : ℕ}

/-- **The moment map along the unitary orbit.** For `U : U(N)` and a projective
point `p₀`, the moment coordinate at `U • p₀` is the squared-modulus profile of
`U` acting on a representative of `p₀`. This is the bridge reducing the
Fubini–Study pushforward `Φ∗ fubiniStudyMeasure` to the Haar law of the
squared-moduli of `U · rep` (the Dirichlet keystone). -/
theorem momentMap_orbit (U : Matrix.unitaryGroup (Fin N) ℂ) (p₀ : CPN N) (i : Fin N) :
    momentMap (U • p₀) i
      = ‖(Matrix.toEuclideanLin U.val p₀.rep) i‖ ^ 2
          / ‖Matrix.toEuclideanLin U.val p₀.rep‖ ^ 2 := by
  have hne := Matrix.UnitaryGroup.toEuclideanLin_unitary_apply_ne_zero U p₀.rep_nonzero
  have hmk : U • p₀ = Projectivization.mk ℂ (Matrix.toEuclideanLin U.val p₀.rep) hne := by
    conv_lhs => rw [← p₀.mk_rep]
    rfl
  rw [hmk, momentMap_mk]

end LF4
end CSD
