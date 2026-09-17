/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.PreparationDensity
public import CsdLean4.LF2.PreparationBarycenter
public import CsdLean4.LF4.KahlerWignerLift
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitSection

/-!
# The two preparation interfaces agree: the ρ_ep of Q28 is the density in W3's formula

**Category:** 7-SigmaLayer (the seam between `SigmaLayer.Preparation` / `ProjectiveSector` and
`LF2.SectorData` / `fromPreparation`; item 4 of the 2026-09-11 QIT follow-ups).

The corpus carries two preparation interfaces. The SigmaLayer core (`ConstraintDynamics`,
`Preparation`, `ProjectiveSector`) has region preparations, their conditional Liouville laws, and
Q28's theorem that the projective law of a region preparation is `μFS.withDensity ρ_ep`
(`projectivePreparationLaw_withDensity`). The LF2 interface (`SectorData`, `MeasureBridgeData`,
`fromPreparation`) has the density operator of a preparation and, since W3, its entrywise
`ρ_ep` form `preparationDensity_apply_rnDeriv`, which took absolute continuity of the projective
law as a *hypothesis*. Until 2026-09-11 nothing composed the two. This module does:

* `ProjectiveSector.toSectorData`, `ProjectiveSector.toMeasureBridgeData` — the adapter: a
  projective sector, a region preparation and the group data LF2's `SectorData` asks for
  (a measurable Liouville-invariant `G`-action on `Σ`, intertwined by the projection with a
  measurable transitive action on the target, `μFS` invariant) assemble into an LF2 sector with
  its bridge;
* ★★ `preparationDensity_apply_rhoEp` — **the seam**: for a region preparation with a bridge, the
  LF2 density operator of its conditional law is `∫ ρ_ep(ψ) ψⱼ conj ψₖ dμFS(ψ)` with `ρ_ep` **Q28's
  Radon–Nikodym density** (`ProjectiveSector.preparationDensity`). The absolute continuity is
  the theorem `projectivePreparationLaw_absolutelyContinuous`, no longer a hypothesis;
* ★★ `kahler_preparationDensity_apply`, `kahler_preparationDensity_apply_unitSection` — **on the
  Kähler arena the seam closes with no hypotheses**: for any dynamics on `ℂℙ^{N−1} × T²` carrying
  the Liouville measure and any region preparation, the corpus's `kSectorData` / `kBridgeData`
  (`c = 1`) density operator is `∫ ρ_ep |ψ⟩⟨ψ| dμ_FS` with `ρ_ep` the density of
  `kahler_preparation_density` against the Fubini–Study measure, and with the canonical measurable
  unit section as representative not even a representative is chosen.

## Honest scope

The adapter takes the `G`-action as data because the SigmaLayer core has none and LF2's
`SectorData` requires one; on the Kähler arena it is the unitary group and already built
(`kSectorData`). The adapter's ontic setup fixes a time `t` (`Preparation.toOnticSetup`); the
density operator does not depend on it. Nothing here changes the posits: the sector and its
Liouville law remain Posits 2 and 3 of `specs/POSITS.md`.

References: `specs/qit-chain-scoping.md`; `SigmaLayer/PreparationDensity.lean` (Q28);
`LF2/PreparationBarycenter.lean` (W3); `LF4/KahlerInstance.lean` (`kSectorData`),
`LF4/KahlerWignerLift.lean` (`kBridgeData`); `SigmaLayer/Adapters.lean`.
-/

@[expose] public section

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped ComplexOrder LinearAlgebra.Projectivization


namespace CSD.SigmaLayer

variable {Sigma : Type*} [MeasurableSpace Sigma] [Nonempty Sigma] {N : ℕ}
variable {D : ConstraintDynamics Sigma}

/-! ### The adapter: a projective sector with group data is an LF2 sector -/

/-- **The LF2 adapter.** A SigmaLayer projective sector, a region preparation (for the LF1 ontic
setup at time `t`), and the group data LF2's `SectorData` asks for — a measurable, Liouville-
invariant `G`-action on `Σ` intertwined by `pi` with a measurable transitive action on the
projective target — assemble into an `LF2.SectorData`. -/
def ProjectiveSector.toSectorData (Q : ProjectiveSector N D) (P : Preparation D) (t : OnticTime)
    {G : Type*} [Group G] [MulAction G Sigma] [MulAction G (ProjectiveState N)]
    [MulAction.IsPretransitive G (ProjectiveState N)]
    (hσ : ∀ g : G, Measurable ((g • ·) : Sigma → Sigma))
    (hP : ∀ g : G, Measurable ((g • ·) : ProjectiveState N → ProjectiveState N))
    (hinv : ∀ g : G, MeasurePreserving ((g • ·) : Sigma → Sigma) (D.muL : Measure Sigma)
      (D.muL : Measure Sigma))
    (hequiv : ∀ (g : G) (x : Sigma), Q.pi (g • x) = g • Q.pi x) :
    CSD.LF2.SectorData Sigma (ProjectiveState N) G where
  toOntic := P.toOnticSetup t
  π := Q.pi
  measurable_π := Q.measurable_pi
  measurable_smul_σ := hσ
  measurable_smul_P := hP
  hμL_inv := hinv
  hπ_equiv := hequiv

/-- The adapter's measure bridge: the SigmaLayer bridge `pi_* muL = c • μFS` and `G`-invariance
of `μFS` are LF2's `MeasureBridgeData`. -/
def ProjectiveSector.toMeasureBridgeData (Q : ProjectiveSector N D) (P : Preparation D)
    (t : OnticTime) {G : Type*} [Group G] [MulAction G Sigma] [MulAction G (ProjectiveState N)]
    [MulAction.IsPretransitive G (ProjectiveState N)]
    (hσ : ∀ g : G, Measurable ((g • ·) : Sigma → Sigma))
    (hP : ∀ g : G, Measurable ((g • ·) : ProjectiveState N → ProjectiveState N))
    (hinv : ∀ g : G, MeasurePreserving ((g • ·) : Sigma → Sigma) (D.muL : Measure Sigma)
      (D.muL : Measure Sigma))
    (hequiv : ∀ (g : G) (x : Sigma), Q.pi (g • x) = g • Q.pi x)
    (μFS : Measure (ProjectiveState N)) (c : ENNReal)
    (hbridge : Q.projectiveLaw (D.muL : Measure Sigma) = c • μFS)
    (hFS_inv : ∀ g : G, MeasurePreserving ((g • ·) : ProjectiveState N → ProjectiveState N)
      μFS μFS) :
    CSD.LF2.MeasureBridgeData (Q.toSectorData P t hσ hP hinv hequiv) μFS where
  is_inv := hFS_inv
  c := c
  bridge_eq := hbridge

/-! ### The seam: the ρ_ep of Q28 is the density in W3's formula -/

/-- ★★ **The two preparation interfaces agree on the density operator.** For a region preparation
`P` of the SigmaLayer with a bridge `pi_* muL = c • μFS`, the LF2 density operator of its
conditional law (W3's barycentre) is, entrywise, `∫ ρ_ep(ψ) ψⱼ conj ψₖ dμFS(ψ)` with `ρ_ep` **the
Radon–Nikodym density of Q28** (`ProjectiveSector.preparationDensity`). The absolute continuity
W3's `ρ_ep` form took as a hypothesis is here the theorem
`projectivePreparationLaw_absolutelyContinuous`. -/
theorem preparationDensity_apply_rhoEp (Q : ProjectiveSector N D) (P : Preparation D)
    (t : OnticTime) {G : Type*} [Group G] [MulAction G Sigma] [MulAction G (ProjectiveState N)]
    [MulAction.IsPretransitive G (ProjectiveState N)]
    (hσ : ∀ g : G, Measurable ((g • ·) : Sigma → Sigma))
    (hP : ∀ g : G, Measurable ((g • ·) : ProjectiveState N → ProjectiveState N))
    (hinv : ∀ g : G, MeasurePreserving ((g • ·) : Sigma → Sigma) (D.muL : Measure Sigma)
      (D.muL : Measure Sigma))
    (hequiv : ∀ (g : G) (x : Sigma), Q.pi (g • x) = g • Q.pi x)
    (μFS : Measure (ProjectiveState N)) [IsProbabilityMeasure μFS] (c : ENNReal)
    (hbridge : Q.projectiveLaw (D.muL : Measure Sigma) = c • μFS)
    (hFS_inv : ∀ g : G, MeasurePreserving ((g • ·) : ProjectiveState N → ProjectiveState N)
      μFS μFS)
    (rep : ProjectiveState N → EuclideanSpace ℂ (Fin N)) (hrep_unit : ∀ p, ‖rep p‖ = 1)
    (hrep_meas : Measurable rep) (j k : Fin N) :
    (CSD.LF2.preparationDensity (Q.toSectorData P t hσ hP hinv hequiv) μFS
        (Q.toMeasureBridgeData P t hσ hP hinv hequiv μFS c hbridge hFS_inv)
        ((P.conditionalMeasure : ProbabilityMeasure Sigma) : Measure Sigma)
        rep hrep_unit hrep_meas).M j k
      = ∫ ψ, (Q.preparationDensity P μFS ψ).toReal • ((rep ψ) j * star ((rep ψ) k)) ∂μFS := by
  have habs : Measure.map (Q.toSectorData P t hσ hP hinv hequiv).π
      ((P.conditionalMeasure : ProbabilityMeasure Sigma) : Measure Sigma) ≪ μFS :=
    Q.projectivePreparationLaw_absolutelyContinuous P hbridge
  exact CSD.LF2.preparationDensity_apply_rnDeriv (Q.toSectorData P t hσ hP hinv hequiv) μFS
    (Q.toMeasureBridgeData P t hσ hP hinv hequiv μFS c hbridge hFS_inv) _ rep hrep_unit hrep_meas
    habs j k

/-! ### The Kähler arena: the seam at `c = 1` -/

/-- ★★ **On the Kähler arena the seam closes with no hypotheses.** For any dynamics on
`Σ = ℂℙ^{N−1} × T²` carrying the Liouville measure and any region preparation `P`, the LF2
density operator of `P` (with respect to the corpus's `kSectorData` and its axiom-free bridge
`kBridgeData`, `c = 1`) is `∫ ρ_ep(ψ) |ψ⟩⟨ψ| dμ_FS(ψ)` entrywise, with `ρ_ep` the Q28 density of
`kahler_preparation_density` against THE Fubini–Study measure. -/
theorem kahler_preparationDensity_apply (p₀ : CSD.LF4.CPN N) [NeZero N]
    (D : ConstraintDynamics (CSD.LF4.KSigma N))
    (hmuL : (D.muL : Measure (CSD.LF4.KSigma N)) = CSD.LF4.kMuL p₀)
    (P : Preparation D)
    (rep : CSD.LF4.CPN N → EuclideanSpace ℂ (Fin N)) (hrep_unit : ∀ p, ‖rep p‖ = 1)
    (hrep_meas : Measurable rep) (j k : Fin N) :
    (CSD.LF2.preparationDensity (CSD.LF4.kSectorData p₀) (fsMeasure p₀)
        (CSD.LF4.kBridgeData p₀)
        ((P.conditionalMeasure : ProbabilityMeasure (CSD.LF4.KSigma N)) : Measure (CSD.LF4.KSigma N))
        rep hrep_unit hrep_meas).M j k
      = ∫ ψ, ((kahlerFstSector D).preparationDensity P (fsMeasure p₀) ψ).toReal
          • ((rep ψ) j * star ((rep ψ) k)) ∂(fsMeasure p₀) := by
  have habs : Measure.map (CSD.LF4.kSectorData p₀).π
      ((P.conditionalMeasure : ProbabilityMeasure (CSD.LF4.KSigma N)) : Measure (CSD.LF4.KSigma N))
        ≪ fsMeasure p₀ :=
    (kahler_preparation_density p₀ D hmuL P).1
  exact CSD.LF2.preparationDensity_apply_rnDeriv (CSD.LF4.kSectorData p₀) (fsMeasure p₀)
    (CSD.LF4.kBridgeData p₀) _ rep hrep_unit hrep_meas habs j k

/-- The Kähler seam with the canonical measurable unit section as representative: no
representative hypothesis either. -/
theorem kahler_preparationDensity_apply_unitSection (p₀ : CSD.LF4.CPN N) [NeZero N]
    (D : ConstraintDynamics (CSD.LF4.KSigma N))
    (hmuL : (D.muL : Measure (CSD.LF4.KSigma N)) = CSD.LF4.kMuL p₀)
    (P : Preparation D) (j k : Fin N) :
    (CSD.LF2.preparationDensity (CSD.LF4.kSectorData p₀) (fsMeasure p₀)
        (CSD.LF4.kBridgeData p₀)
        ((P.conditionalMeasure : ProbabilityMeasure (CSD.LF4.KSigma N)) : Measure (CSD.LF4.KSigma N))
        Projectivization.unitSection Projectivization.norm_unitSection
        Projectivization.measurable_unitSection).M j k
      = ∫ ψ, ((kahlerFstSector D).preparationDensity P (fsMeasure p₀) ψ).toReal
          • ((Projectivization.unitSection ψ) j * star ((Projectivization.unitSection ψ) k))
          ∂(fsMeasure p₀) :=
  kahler_preparationDensity_apply p₀ D hmuL P Projectivization.unitSection
    Projectivization.norm_unitSection Projectivization.measurable_unitSection j k

end CSD.SigmaLayer
