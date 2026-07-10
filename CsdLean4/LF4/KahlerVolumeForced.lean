import CsdLean4.LF4.ManyToOnePillars
import CsdLean4.LF4.NonTrivialSetup
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudyUnique

/-!
# Moving up the chain: the Kähler-sector VOLUME is forced, not posited

`KahlerOnticSetup` carries two abstract-placeholder pairs (see `KahlerOnticSetup.lean`):

* `IsKahlerSector` / `kahler_condition` — "`Σ` has a closed 2-form `ω` compatible with a complex
  structure `J`". Genuinely **blocked**: Mathlib has no symplectic/Kähler-form API (KG-1 / link L1).
  Stays an honest `True` posit; nothing here changes that.
* `IsLiouvilleKahlerVolume` / `liouville_eq_kahler_volume` — "`liouvilleMeasure` is the top-power
  Kähler volume `ω^{∧n}/n!`". Until now its only formalised content was the *normalisation* core
  (`IsProbabilityMeasure`, fix C5). **This module upgrades that content** from "it is *a* probability
  measure" to "it is *the* volume forced by the space and its symmetry".

## The upgrade — `IsForcedKahlerVolume`

On the ray space `ℂℙ^{N-1}` the top-power Kähler volume is not a free choice: `ℂℙ^{N-1}` is the
compact homogeneous space `U(N)/(U(1)×U(N-1))`, and its Riemannian/symplectic (Fubini–Study) volume is
**the unique `U(N)`-invariant probability measure**. That uniqueness is already proved axiom-free
(`fubiniStudyMeasure_unique`). So we bundle the intrinsic characterisation

    IsForcedKahlerVolume μ  :=  (μ a probability measure)
                             ∧ (μ is U(N)-invariant)
                             ∧ (μ is the UNIQUE such measure),

and prove `fubiniStudyMeasure` satisfies it (`fubiniStudyMeasure_isForcedKahlerVolume`). This is the
measure-theoretic content of "`μ = ω^{∧n}/n!`": the Kähler volume is **determined by `Σ` and its
`U(N)`-symmetry**, an *outcome* of the space, not posited data. It is exactly the physically
load-bearing half of the Kähler posit — the volume is what the Born reading (typicality = volume
ratio) consumes; the differential-geometric 2-form packaging is the part that stays blocked (KG-1).

## Delivered on the concrete sectors

* `unitaryFlowSetup_liouville_isForcedKahlerVolume` — the `π = id` sector's Liouville measure (`= μ_FS`)
  IS the forced Kähler volume: the sector's volume is fully determined, not chosen.
* `manyToOneSetup_baseVolume_isForcedKahlerVolume` — on the genuine many-to-one Kähler instance
  `Σ = ℂℙ^{N-1} × T²`, the ray-space volume `π_*(liouvilleMeasure)` (the Kähler volume of the base
  that the Born rule scores) is the forced FS volume.
* `manyToOneSetup_liouville_eq_product` — the full `Σ`-volume `kMuL = μ_FS ⊗ vol_{T²}` is exhibited as
  the product of the two canonical invariant volumes (the forced FS volume on the base, Haar on the
  fibre) — so the whole Liouville measure is built from forced factor volumes.

## Honest scope

This discharges the **formalisable core** of `IsLiouvilleKahlerVolume` (volume forced by symmetry),
not the full differential-geometric `IsKahlerSector` (the 2-form), which remains Mathlib-blocked. And
it is FORWARD: it characterises the *posited* sector volume intrinsically; it does NOT derive the
`U(N)`-symmetry itself from the deterministic dynamics (that reverse — deriving `G` — is FND-1,
untouched). "The volume is forced by the symmetry" still takes the symmetry `G = U(N)` as given.
-/

open MeasureTheory Matrix.UnitaryGroup

namespace CSD
namespace LF4

variable {N : ℕ}

/-- **The Kähler volume, characterised intrinsically.** A measure `μ` on the ray space `ℂℙ^{N-1}` is
the *forced* Kähler/Liouville volume when it is a `U(N)`-invariant probability measure AND the UNIQUE
such measure. On the compact homogeneous space `ℂℙ^{N-1} = U(N)/(U(1)×U(N-1))` this pins `μ` to the
Fubini–Study volume with no free choice — the measure-theoretic content of "`μ = ω^{∧n}/n!`", an
outcome of the space and its symmetry rather than posited data. -/
structure IsForcedKahlerVolume (μ : Measure (CPN N)) : Prop where
  /-- `μ` is normalised (a probability measure). -/
  isProb : IsProbabilityMeasure μ
  /-- `μ` is invariant under the `U(N)` sector symmetry. -/
  invariant : ∀ U : Matrix.unitaryGroup (Fin N) ℂ, MeasurePreserving (fun p => U • p) μ μ
  /-- `μ` is the UNIQUE `U(N)`-invariant probability measure — the volume is forced, not chosen. -/
  unique : ∀ ν : Measure (CPN N), IsProbabilityMeasure ν →
    (∀ U : Matrix.unitaryGroup (Fin N) ℂ, MeasurePreserving (fun p => U • p) ν ν) → ν = μ

/-- **The Fubini–Study measure IS the forced Kähler volume.** `μ_FS` is a `U(N)`-invariant
probability measure (`fubiniStudyMeasure_smul_invariant`) and the UNIQUE such
(`fubiniStudyMeasure_unique`). So the Kähler volume of the ray space is completely determined by the
space `ℂℙ^{N-1}` and its `U(N)`-symmetry — the intrinsic discharge of the `IsLiouvilleKahlerVolume`
posit's formalisable content. -/
theorem fubiniStudyMeasure_isForcedKahlerVolume [NeZero N] (p₀ : CPN N) :
    IsForcedKahlerVolume (fubiniStudyMeasure p₀) where
  isProb := inferInstance
  invariant := fun U =>
    ⟨(continuous_const_smul U).measurable, fubiniStudyMeasure_smul_invariant U p₀⟩
  unique := fun ν hν hν_inv => by
    haveI := hν
    exact fubiniStudyMeasure_unique p₀ ν (fun U => (hν_inv U).map_eq)

/-- **The `π = id` sector's Liouville volume is forced.** For `unitaryFlowSetup N U p₀` the Liouville
measure is `μ_FS`, which is the forced Kähler volume — the sector's typicality measure is fully
determined by `Σ = ℂℙ^{N-1}` and its `U(N)`-symmetry, not a posited probability measure. -/
theorem unitaryFlowSetup_liouville_isForcedKahlerVolume [NeZero N]
    (U : ℝ → Matrix.unitaryGroup (Fin N) ℂ) (p₀ : CPN N) :
    IsForcedKahlerVolume (unitaryFlowSetup N U p₀).liouvilleMeasure :=
  fubiniStudyMeasure_isForcedKahlerVolume p₀

/-- The many-to-one Kähler instance's ray-space volume is the FS volume: `π_*(kMuL) = μ_FS`, the
marginal bridge `Prod.fst_* (μ_FS ⊗ vol) = μ_FS` (`Measure.fst_prod`, the fibre volume normalised). -/
theorem manyToOneSetup_baseVolume_eq_fubiniStudy [NeZero N]
    (U : ℝ → Matrix.unitaryGroup (Fin N) ℂ) (p₀ : CPN N) :
    Measure.map (manyToOneSetup U p₀).pi (manyToOneSetup U p₀).liouvilleMeasure
      = fubiniStudyMeasure p₀ := by
  show Measure.map Prod.fst (kMuL p₀) = fubiniStudyMeasure p₀
  rw [kMuL, ← Measure.fst, Measure.fst_prod]

/-- **The many-to-one Kähler instance's ray-space volume is forced.** On `Σ = ℂℙ^{N-1} × T²` with the
genuine many-to-one `π = pr₁`, the volume of the ray space `π_*(liouvilleMeasure)` — exactly the
Kähler volume the Born rule scores — is the forced Fubini–Study volume. So the operational Kähler
volume of this fibred sector is an outcome of the base geometry, not posited. -/
theorem manyToOneSetup_baseVolume_isForcedKahlerVolume [NeZero N]
    (U : ℝ → Matrix.unitaryGroup (Fin N) ℂ) (p₀ : CPN N) :
    IsForcedKahlerVolume
      (Measure.map (manyToOneSetup U p₀).pi (manyToOneSetup U p₀).liouvilleMeasure) := by
  rw [manyToOneSetup_baseVolume_eq_fubiniStudy]
  exact fubiniStudyMeasure_isForcedKahlerVolume p₀

/-- **The full `Σ`-volume is a product of forced factor volumes.** The Liouville measure of the
many-to-one Kähler instance is `kMuL = μ_FS ⊗ vol_{T²}` — the product of the forced Fubini–Study
volume on the base (`fubiniStudyMeasure_isForcedKahlerVolume`) and the canonical Haar volume on the
`T²` fibre. So the whole Kähler `Σ`-volume is assembled from canonically-determined factor volumes,
not posited. -/
theorem manyToOneSetup_liouville_eq_product [NeZero N]
    (U : ℝ → Matrix.unitaryGroup (Fin N) ℂ) (p₀ : CPN N) :
    (manyToOneSetup U p₀).liouvilleMeasure
      = (fubiniStudyMeasure p₀).prod (volume : Measure KTorus) :=
  rfl

end LF4
end CSD

