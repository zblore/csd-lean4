import CsdLean4.FND.IsolationPreparation
import CsdLean4.LF4.KahlerOnticSetup

/-!
# FND/ChoiceASector: the Choice A projective sector and its projective law

**Category:** 7-FND (the Choice A ontological layer).

Postulates P7, P8, P9: for each finite dimension `N` the operational pure-state target is `CP^{N-1}`
(`ProjectiveState N`), and there is a measurable projection `pi : Sigma -> CP^{N-1}` which need NOT be
injective (many-to-one is intended). The projective probability law is the pushforward of an ontic
measure under `pi`.

## Anti-circularity

`ChoiceASector` carries NO Born equality, NO Fubini-Study equality, NO unitarity. It is the projection
`pi` and its measurability only. The Born rule, the Fubini-Study bridge and unitary projected dynamics
are theorem targets or named bridge assumptions elsewhere, never fields here.

## Adapters into the existing setups

`kahlerConstraintDynamics` and `kahlerChoiceASector` recover the FND structures from
`LF4.KahlerOnticSetup`. The `ConstraintDynamics` adapter is PARTIAL: `KahlerOnticSetup` does not carry
the one-parameter-group laws (`flow_zero`, `flow_add`), so they are taken as explicit inputs, and it
does not guarantee finiteness of `liouvilleMeasure`, so `IsFiniteMeasure` is required. `KahlerOnticSetup`'s
`IsKahlerSector` and `IsLiouvilleKahlerVolume` fields are documented placeholders (see
`LF4/KahlerOnticSetup.lean`). The projection adapter is total: `pi` is dynamics independent.
-/

open MeasureTheory
open scoped LinearAlgebra.Projectivization

namespace CSD.FND

universe u

/-- **The Choice A projective pure-state target (postulate P7):** `CP^{N-1}`. Definitionally the LF4
`CPN N = ℙ ℂ (EuclideanSpace ℂ (Fin N))`; named here for the FND layer. -/
abbrev ProjectiveState (N : ℕ) := ℙ ℂ (EuclideanSpace ℂ (Fin N))

/-- **The Choice A sector (postulates P8, P9).** A measurable projection from the ontic state space to
the projective pure-state target. It need not be injective; a many-to-one `pi` is intended and
supported. No Born rule is placed here. -/
structure ChoiceASector (N : ℕ) {Sigma : Type u} [MeasurableSpace Sigma]
    (_D : ConstraintDynamics Sigma) where
  /-- P8: the measurable projection onto the projective sector. -/
  pi : Sigma → ProjectiveState N
  /-- The projection is measurable. -/
  measurable_pi : Measurable pi

namespace ChoiceASector

variable {N : ℕ} {Sigma : Type u} [MeasurableSpace Sigma] {D : ConstraintDynamics Sigma}

/-- **The projective law of an ontic measure.** The pushforward `pi_* mu` on the projective sector.
Not identified with the Fubini-Study measure without a separate bridge (`FND/MeasureBridge.lean`). -/
noncomputable def projectiveLaw (Q : ChoiceASector N D) (mu : Measure Sigma) :
    Measure (ProjectiveState N) :=
  Measure.map Q.pi mu

/-- The projective law evaluated on a measurable set is the ontic measure of its preimage. -/
theorem projectiveLaw_apply (Q : ChoiceASector N D) (mu : Measure Sigma)
    {B : Set (ProjectiveState N)} (hB : MeasurableSet B) :
    Q.projectiveLaw mu B = mu (Q.pi ⁻¹' B) := by
  rw [projectiveLaw, Measure.map_apply Q.measurable_pi hB]

/-- **The projective preparation law.** The pushforward under `pi` of the normalised conditional ontic
preparation measure (`Preparation.conditionalMeasure`). -/
noncomputable def projectivePreparationLaw [Nonempty Sigma] (Q : ChoiceASector N D)
    (P : Preparation D) : Measure (ProjectiveState N) :=
  Q.projectiveLaw ((P.conditionalMeasure : ProbabilityMeasure Sigma) : Measure Sigma)

end ChoiceASector

/-! ### Adapters from the existing `LF4.KahlerOnticSetup` -/

/-- **Partial adapter `KahlerOnticSetup -> ConstraintDynamics`.** Recovers the FND canonical core from a
Kähler setup, given the one-parameter-group laws (`hzero`, `hadd`) that `KahlerOnticSetup` does not carry
and `IsFiniteMeasure` on its `liouvilleMeasure`. Measurability of the flow is derived from
`flow_preserves_volume`; measure preservation is inherited directly. -/
def kahlerConstraintDynamics {N : ℕ} (K : CSD.LF4.KahlerOnticSetup N)
    [hfin : IsFiniteMeasure K.liouvilleMeasure]
    (hzero : ∀ x, K.flow 0 x = x)
    (hadd : ∀ s t x, K.flow (s + t) x = K.flow s (K.flow t x)) :
    ConstraintDynamics K.Sigma where
  muL := ⟨K.liouvilleMeasure, hfin⟩
  flow := K.flow
  measurable_flow := fun t => (K.flow_preserves_volume t).measurable
  flow_zero := hzero
  flow_add := hadd
  flow_preserves := K.flow_preserves_volume

/-- **Total adapter `KahlerOnticSetup -> ChoiceASector`.** Recovers the projection for any
`ConstraintDynamics` on the same `Sigma` (the projection `pi` is independent of the dynamics). -/
def kahlerChoiceASector {N : ℕ} (K : CSD.LF4.KahlerOnticSetup N)
    {D : ConstraintDynamics K.Sigma} : ChoiceASector N D where
  pi := K.pi
  measurable_pi := K.pi_measurable

end CSD.FND
