/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.KahlerVolumeForced
public import CsdLean4.LF4.ProjectiveManifold
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudyMass
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudySymplectic
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceSchrodingerFlow

/-!
# The sector is the standard object: `KahlerOnticSetup`'s `ℂℙⁿ` instances, wired to the manifold layer

**Category:** 3-Local (the `ℂℙⁿ` instances of `KahlerOnticSetup` meet the manifold layer; W1 of
`specs/generator-layer-scoping.md` §9).

**TERM-SCOPE(Kahler)** **TERM-SCOPE(Liouville)** **TERM-SCOPE(Hamiltonian)** — this module is where the
two senses of each word meet: the *posited* sense (`KahlerOnticSetup`'s fields) and the *standard* sense (the manifold
layer). `specs/TERMS.md` records what is backed.

Until 2026-09-10 the sector was carried as posited data: `KahlerOnticSetup` (`LF4/KahlerOnticSetup.lean`)
asserts a pointwise Kähler triple on the flat model (`kahler_pointwise : IsFubiniStudyKahler N`), a
probability measure (`liouvilleMeasure`), and its preservation by the flow (`flow_preserves_volume`), and
the strongest thing the corpus could say about the measure was that symmetry forces it
(`IsForcedKahlerVolume`, `LF4/KahlerVolumeForced.lean`). Meanwhile the manifold layer built the standard
objects on `ℂℙⁿ = ℙ ℂ (Ambient n)` — which **is** the sector's target `ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))`,
definitionally — and never cited them back. This module closes that gap. For the two concrete `ℂℙⁿ`
sectors (`unitaryFlowSetup`, `Σ = ℂℙⁿ`, `π = id`; `manyToOneSetup`, `Σ = ℂℙⁿ × T²`) and the inhabitation
witness (`trivialKahlerOnticSetup`):

* ★★★ `unitaryFlowSetup_liouvilleMeasure_eq_fsVolumeNormalized` / `trivialKahlerOnticSetup_…` — **the
  Liouville measure IS the normalised symplectic volume of the Kähler form**: `liouvilleMeasure =
  fsVolumeNormalized n`, the normalised measure of the top power `ω_FS^{∧n}` of `fsForm`
  (`fsVolumeNormalized_eq_fubiniStudyMeasure`, step (3) of the manifold programme);
* ★★ `fsVolume_eq_smul_unitaryFlowSetup_liouvilleMeasure` — with the constant: `ω_FS^{∧n} = (4π)ⁿ ·
  liouvilleMeasure` (`fsVolume_eq_smul_fubiniStudyMeasure`);
* ★★ `unitaryFlowSetup_flow_measurePreserving_fsVolume` — **the sector's flow preserves the symplectic
  volume itself**, not only its normalisation: every time-`t` map `U t • ·` preserves `fsVolume n`
  (`fsVolume_map_smul`). The posited field `flow_preserves_volume` is, on this sector, a theorem about
  the top power of the Kähler form;
* ★★★ `fsVolumeNormalized_isForcedKahlerVolume` — **the two characterisations of the volume coincide**:
  the normalised top power of `ω_FS` is the unique `U(n+1)`-invariant probability measure. Symmetry
  (`LF4`) and the Kähler form (the manifold layer) pin the same measure;
* ★★ `manyToOneSetup_liouvilleMeasure_eq_fsVolumeNormalized_prod`,
  `manyToOneSetup_map_pi_liouvilleMeasure_eq_fsVolumeNormalized`,
  `manyToOneSetup_flow_measurePreserving_fsVolume_prod` — the same three facts on the genuine
  many-to-one sector `ℂℙⁿ × T²`: `kMuL = fsVolumeNormalized n ⊗ Haar`, the base marginal is the
  symplectic volume, and the flow preserves `fsVolume n ⊗ Haar`;
* ★★★ `unitaryFlowSetup_isKahler_liouville` / `manyToOneSetup_isKahler_liouville` — **the sector is the
  standard object**, in one statement: its target is a Kähler manifold (`fsForm_isKahler`, G14a), its
  Liouville measure is the normalised top power of that Kähler form, and its flow preserves that
  volume;
* ★★ `manyToOneSetup_pi_contMDiff` (Q33, 2026-09-11) — **the sector projection is analytic** on the
  arena manifold `ℂℙⁿ × T²` (`LF4/ProjectiveManifold.lean`, `ksigma_isManifold`): Paper C's A3;
* **Q29(e) (2026-09-12).** `manyToOneSchrodingerSetup_projectedFlow_eq_hamiltonianFlow`,
  `manyToOneSchrodingerSetup_flow_eq_hamiltonianFlow` — the general-`N` Schrödinger sector's flow is
  the Hamiltonian flow of `-2⟨H⟩` on the base (`hamiltonianFlow_schrodingerHamiltonian`), the
  identity on the fibre; ★★★ `manyToOneSchrodingerSetup_flow_preserves_volume_derived`, ★★
  `unitaryFlowSetup_schrodingerUnitary_flow_preserves_volume_derived` — **the posited field
  `flow_preserves_volume` is a theorem on these sectors by Liouville's theorem for the Hamiltonian
  flow** (Q29, `fsVolumeNormalized_map_schrodingerUnitary_smul`), not by unitary invariance; the
  field is not consumed in the proof.

## Honest scope

⚠️ **The structure is unchanged.** `KahlerOnticSetup` still posits its fields for an abstract `Σ`; this
module proves, for the `ℂℙⁿ` instances, that the posited data *are* the standard objects. The pointwise
field `kahler_pointwise : IsFubiniStudyKahler N` lives on the ambient `ℂ^{N}` (`Kahler.fundamentalForm`
on `EuclideanSpace ℂ (Fin N)`), the manifold predicate `fsForm_isKahler` on the sector's target
`ℂℙⁿ` itself (tangent model `ℂⁿ`, `N = n + 1`); they are different spaces, and no implication between
them is stated. `flow_preserves_volume` remains a field: what this module adds is that on `ℂℙⁿ` the
measure it preserves is `ω_FS^{∧n}`, that the preservation is the unitary invariance of that top power
for an arbitrary unitary family, and that for the Schrödinger family `exp(-itH)` it is also Liouville's
theorem for the Hamiltonian flow of `-2⟨H⟩` (the `_derived` twins).

⚠️ **Posit 3 (`specs/POSITS.md`) is untouched.** The flows here are unitary, hence Hamiltonian
(`schrodingerField_isHamiltonianVectorField`, G13) and volume-preserving both by invariance and by the
manifold-level Liouville theorem (Q29, `HamiltonianFlowVolume.lean`); the constraint dynamics'
measurement pieces are not globally Hamiltonian, which is what keeps the field a posit.

⚠️ **`n + 1`, not `N`.** The manifold layer indexes `ℂℙⁿ` by the chart dimension `n`; the sector by the
ambient dimension `N`. Every statement here is at `N = n + 1`, which is every `N ≥ 1`; `N = 0` has an
empty sector and no chart.

References: `specs/generator-layer-scoping.md` (§9, W1); `specs/connectivity-manifest.md` (link L1);
`specs/TERMS.md` (Kähler, Liouville, Fubini–Study, symplectic); `specs/POSITS.md` (Posits 2, 3);
`LF4/KahlerOnticSetup.lean`, `LF4/NonTrivialSetup.lean`, `LF4/ManyToOnePillars.lean`,
`LF4/KahlerVolumeForced.lean` (the sector side); `Mathlib/Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudyVolume.lean`,
`…Mass.lean`, `…Symplectic.lean` (the manifold side); `specs/future-work.md` (KG-1).
-/

@[expose] public section

open MeasureTheory Matrix.UnitaryGroup Projectivization DifferentialForm
open scoped ENNReal Real

namespace CSD
namespace LF4

variable {n : ℕ}

/-! ### The `π = id` sector -/

/-- ★★★ **The Liouville measure of the `π = id` sector IS the normalised symplectic volume of the
Kähler form**: `unitaryFlowSetup (n + 1) U p₀` has `liouvilleMeasure = μ_FS = fsVolumeNormalized n`, the
normalised measure of the top power `ω_FS^{∧n}` of `fsForm`. -/
theorem unitaryFlowSetup_liouvilleMeasure_eq_fsVolumeNormalized
    (U : ℝ → Matrix.unitaryGroup (Fin (n + 1)) ℂ) (p₀ : CPN (n + 1)) :
    (unitaryFlowSetup (n + 1) U p₀).liouvilleMeasure = fsVolumeNormalized n :=
  (fsVolumeNormalized_eq_fubiniStudyMeasure p₀).symm

/-- The inhabitation witness's Liouville measure is the normalised symplectic volume too. -/
theorem trivialKahlerOnticSetup_liouvilleMeasure_eq_fsVolumeNormalized (p₀ : CPN (n + 1)) :
    (trivialKahlerOnticSetup (n + 1) p₀).liouvilleMeasure = fsVolumeNormalized n :=
  (fsVolumeNormalized_eq_fubiniStudyMeasure p₀).symm

/-- ★★ **With the constant**: the top power of the Kähler form is `(4π)ⁿ` times the sector's Liouville
measure. -/
theorem fsVolume_eq_smul_unitaryFlowSetup_liouvilleMeasure
    (U : ℝ → Matrix.unitaryGroup (Fin (n + 1)) ℂ) (p₀ : CPN (n + 1)) :
    fsVolume n = ENNReal.ofReal ((4 * π) ^ n) • (unitaryFlowSetup (n + 1) U p₀).liouvilleMeasure :=
  fsVolume_eq_smul_fubiniStudyMeasure p₀

/-- ★★ **The sector's flow preserves the symplectic volume itself**: every time-`t` map of
`unitaryFlowSetup` preserves `fsVolume n`, the un-normalised measure of `ω_FS^{∧n}`
(`fsVolume_map_smul`). -/
theorem unitaryFlowSetup_flow_measurePreserving_fsVolume
    (U : ℝ → Matrix.unitaryGroup (Fin (n + 1)) ℂ) (p₀ : CPN (n + 1)) (t : ℝ) :
    MeasurePreserving ((unitaryFlowSetup (n + 1) U p₀).flow t) (fsVolume n) (fsVolume n) := by
  show MeasurePreserving (fun p : CPN (n + 1) => U t • p) (fsVolume n) (fsVolume n)
  exact ⟨(continuous_const_smul (U t)).measurable, fsVolume_map_smul (U t)⟩

/-- ★★★ **The forced Kähler volume IS the symplectic volume.** `fsVolumeNormalized n`, the normalised
top power of `ω_FS`, satisfies `IsForcedKahlerVolume`: it is the unique `U(n + 1)`-invariant
probability measure. The symmetry characterisation of the sector's volume (`LF4`) and its Kähler-form
characterisation (the manifold layer) pin the same measure. -/
theorem fsVolumeNormalized_isForcedKahlerVolume (n : ℕ) :
    IsForcedKahlerVolume (fsVolumeNormalized n) := by
  rw [fsVolumeNormalized_eq_fubiniStudyMeasure (origin 0)]
  exact fubiniStudyMeasure_isForcedKahlerVolume (origin 0)

/-- ★★★ **The `π = id` sector is the standard object**: its target is a Kähler manifold
(`fsForm_isKahler`), its Liouville measure is the normalised top power of that Kähler form, and its
flow preserves that volume. -/
theorem unitaryFlowSetup_isKahler_liouville
    (U : ℝ → Matrix.unitaryGroup (Fin (n + 1)) ℂ) (p₀ : CPN (n + 1)) :
    IsKahler (fsForm (n := n)) fsJ modelJ ∧
      (unitaryFlowSetup (n + 1) U p₀).liouvilleMeasure = fsVolumeNormalized n ∧
      ∀ t, MeasurePreserving ((unitaryFlowSetup (n + 1) U p₀).flow t) (fsVolume n) (fsVolume n) :=
  ⟨fsForm_isKahler n, unitaryFlowSetup_liouvilleMeasure_eq_fsVolumeNormalized U p₀,
    unitaryFlowSetup_flow_measurePreserving_fsVolume U p₀⟩

/-! ### The many-to-one sector `ℂℙⁿ × T²` -/

/-- ★★ **The many-to-one sector's Liouville measure is the symplectic volume of the base tensored
with Haar on the fibre**: `kMuL p₀ = fsVolumeNormalized n ⊗ vol_{T²}`. -/
theorem manyToOneSetup_liouvilleMeasure_eq_fsVolumeNormalized_prod
    (U : ℝ → Matrix.unitaryGroup (Fin (n + 1)) ℂ) (p₀ : CPN (n + 1)) :
    (manyToOneSetup U p₀).liouvilleMeasure
      = (fsVolumeNormalized n).prod (volume : Measure KTorus) := by
  show (fubiniStudyMeasure p₀).prod (volume : Measure KTorus) = _
  rw [fsVolumeNormalized_eq_fubiniStudyMeasure p₀]

/-- ★★ **The base marginal of the many-to-one sector's Liouville measure is the symplectic volume**:
`π_* kMuL = fsVolumeNormalized n`. -/
theorem manyToOneSetup_map_pi_liouvilleMeasure_eq_fsVolumeNormalized
    (U : ℝ → Matrix.unitaryGroup (Fin (n + 1)) ℂ) (p₀ : CPN (n + 1)) :
    Measure.map (manyToOneSetup U p₀).pi (manyToOneSetup U p₀).liouvilleMeasure
      = fsVolumeNormalized n := by
  rw [manyToOneSetup_baseVolume_eq_fubiniStudy U p₀, fsVolumeNormalized_eq_fubiniStudyMeasure p₀]

/-- ★★ **The many-to-one sector's flow preserves the symplectic volume tensored with Haar**. -/
theorem manyToOneSetup_flow_measurePreserving_fsVolume_prod
    (U : ℝ → Matrix.unitaryGroup (Fin (n + 1)) ℂ) (p₀ : CPN (n + 1)) (t : ℝ) :
    MeasurePreserving ((manyToOneSetup U p₀).flow t)
      ((fsVolume n).prod (volume : Measure KTorus)) ((fsVolume n).prod (volume : Measure KTorus)) := by
  show MeasurePreserving (Prod.map (fun p : CPN (n + 1) => U t • p) (id : KTorus → KTorus))
    ((fsVolume n).prod (volume : Measure KTorus)) ((fsVolume n).prod (volume : Measure KTorus))
  have hbase : MeasurePreserving (fun p : CPN (n + 1) => U t • p) (fsVolume n) (fsVolume n) :=
    ⟨(continuous_const_smul (U t)).measurable, fsVolume_map_smul (U t)⟩
  exact hbase.prod (MeasurePreserving.id (volume : Measure KTorus))

/-- ★★★ **The many-to-one sector is the standard object**: its target is a Kähler manifold, its
Liouville measure is the normalised top power of the Kähler form tensored with Haar, and its flow
preserves that volume. -/
theorem manyToOneSetup_isKahler_liouville
    (U : ℝ → Matrix.unitaryGroup (Fin (n + 1)) ℂ) (p₀ : CPN (n + 1)) :
    IsKahler (fsForm (n := n)) fsJ modelJ ∧
      (manyToOneSetup U p₀).liouvilleMeasure = (fsVolumeNormalized n).prod (volume : Measure KTorus) ∧
      ∀ t, MeasurePreserving ((manyToOneSetup U p₀).flow t)
        ((fsVolume n).prod (volume : Measure KTorus)) ((fsVolume n).prod (volume : Measure KTorus)) :=
  ⟨fsForm_isKahler n, manyToOneSetup_liouvilleMeasure_eq_fsVolumeNormalized_prod U p₀,
    manyToOneSetup_flow_measurePreserving_fsVolume_prod U p₀⟩

/-! ### The sector projection is smooth (Q33) -/

open scoped Manifold ContDiff in
/-- ★★ **The many-to-one sector's projection is analytic**: `(manyToOneSetup U p₀).pi = Prod.fst`
on the arena manifold `KSigma (n+1) = ℂℙⁿ × T²` (`ksigma_isManifold`), by `contMDiff_fst`. This is
Paper C's A3, "smooth many-to-one projection", which `reconstruction-status.md` §2a had carried
as blocked on an absent API; the measurability the proofs use is unchanged. -/
theorem manyToOneSetup_pi_contMDiff (U : ℝ → Matrix.unitaryGroup (Fin (n + 1)) ℂ)
    (p₀ : CPN (n + 1)) :
    ContMDiff ((modelWithCornersSelf ℝ (Fin n → ℂ)).prod ((𝓡 1).prod (𝓡 1)))
      (modelWithCornersSelf ℝ (Fin n → ℂ)) ω
      (fun p : KSigma (n + 1) => (manyToOneSetup U p₀).pi p) := by
  show ContMDiff _ _ ω (Prod.fst : KSigma (n + 1) → CPN (n + 1))
  exact contMDiff_ksigma_fst n

/-! ### The Schrödinger sector's flow is the Hamiltonian flow, and the posited field is derived (Q29(e)) -/

/-- The projected flow of the general-`N` Schrödinger sector is the Hamiltonian flow of `-2⟨H⟩`. -/
theorem manyToOneSchrodingerSetup_projectedFlow_eq_hamiltonianFlow
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hH : H.IsHermitian) (p₀ : CPN (n + 1)) (t : ℝ)
    (p : CPN (n + 1)) :
    (manyToOneSchrodingerSetup H hH p₀).projectedFlow t p
      = (fsForm_isSymplectic n).hamiltonianFlow (contMDiff_schrodingerHamiltonian H) t p :=
  (hamiltonianFlow_schrodingerHamiltonian hH t p).symm

/-- The flow of the general-`N` Schrödinger sector is the Hamiltonian flow of `-2⟨H⟩` on the base,
the identity on the fibre. -/
theorem manyToOneSchrodingerSetup_flow_eq_hamiltonianFlow
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hH : H.IsHermitian) (p₀ : CPN (n + 1)) (t : ℝ)
    (x : KSigma (n + 1)) :
    (manyToOneSchrodingerSetup H hH p₀).flow t x
      = ((fsForm_isSymplectic n).hamiltonianFlow (contMDiff_schrodingerHamiltonian H) t x.1, x.2) := by
  show (schrodingerUnitary hH t • x.1, x.2) = _
  rw [hamiltonianFlow_schrodingerHamiltonian hH t x.1]

/-- ★★★ **The posited field, derived.** On the general-`N` Schrödinger sector the field
`flow_preserves_volume` is a theorem: the flow preserves the Liouville measure because its base is
the Hamiltonian flow of `-2⟨H⟩` and Liouville's theorem holds on `ℂℙⁿ`
(`fsVolumeNormalized_map_schrodingerUnitary_smul`, from `fsVolume_map_hamiltonianFlow`), not
because `exp(-itH)` is unitary. The field itself is not consumed. -/
theorem manyToOneSchrodingerSetup_flow_preserves_volume_derived
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hH : H.IsHermitian) (p₀ : CPN (n + 1)) (t : ℝ) :
    MeasurePreserving ((manyToOneSchrodingerSetup H hH p₀).flow t)
      (manyToOneSchrodingerSetup H hH p₀).liouvilleMeasure
      (manyToOneSchrodingerSetup H hH p₀).liouvilleMeasure := by
  rw [manyToOneSchrodingerSetup, manyToOneSetup_liouvilleMeasure_eq_fsVolumeNormalized_prod]
  show MeasurePreserving
    (Prod.map (fun p : CPN (n + 1) => schrodingerUnitary hH t • p) (id : KTorus → KTorus)) _ _
  have hbase : MeasurePreserving (fun p : CPN (n + 1) => schrodingerUnitary hH t • p)
      (fsVolumeNormalized n) (fsVolumeNormalized n) :=
    ⟨(continuous_const_smul _).measurable, fsVolumeNormalized_map_schrodingerUnitary_smul hH t⟩
  exact hbase.prod (MeasurePreserving.id _)

/-- ★★ The same on the `π = id` sector driven by `exp(-itH)`. -/
theorem unitaryFlowSetup_schrodingerUnitary_flow_preserves_volume_derived
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hH : H.IsHermitian) (p₀ : CPN (n + 1)) (t : ℝ) :
    MeasurePreserving ((unitaryFlowSetup (n + 1) (schrodingerUnitary hH) p₀).flow t)
      (unitaryFlowSetup (n + 1) (schrodingerUnitary hH) p₀).liouvilleMeasure
      (unitaryFlowSetup (n + 1) (schrodingerUnitary hH) p₀).liouvilleMeasure := by
  rw [unitaryFlowSetup_liouvilleMeasure_eq_fsVolumeNormalized]
  show MeasurePreserving (fun p : CPN (n + 1) => schrodingerUnitary hH t • p) _ _
  exact ⟨(continuous_const_smul _).measurable, fsVolumeNormalized_map_schrodingerUnitary_smul hH t⟩

end LF4
end CSD
