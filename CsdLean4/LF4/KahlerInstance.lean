/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF2.Setup
public import CsdLean4.LF4.Instance
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitaryTransitive
public import Mathlib.MeasureTheory.Group.AddCircle
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# LF4 §8: a non-trivial-fibre compact-Kähler `SectorData`

**Category:** 3-Local (a non-trivial-fibre compact-Kähler `SectorData`).

Builds the first `SectorData` with **non-trivial fibres**, faithful to the
Σ0 / Paper A ontology (`Σ` a finite compact symplectic Kähler space):

```
Σ = ℂℙ^{N-1} × T²,   T² = (ℝ/ℤ)²   (flat complex torus, compact Kähler);
π = pr₁ : Σ → ℂℙ^{N-1};
μL = μFS ⊗ vol_{T²}   (the product Kähler/Liouville volume);
G = U(N) acting on the base ℂℙ^{N-1}, trivially on the fibre T².
```

The base `ℂℙ^{N-1}` carries the quantum-state geometry and the Fubini–Study
measure bridge; the fibre `T²` is the internal ("hidden phase") degree of
freedom whose volume fractions realise the Born weights downstream
(`LF4/SingletKahler.lean`). Both factors are genuinely compact Kähler, so
`Σ` is compact Kähler and the flat product volume is its Liouville measure.

**Why a torus and not `ℂℙ^M`.** Carving the FS measure on `ℂℙ^M` into regions
of prescribed volume needs the atomless intermediate-value theorem, which is
not in Mathlib (and FS-atomlessness is itself a Haar-of-subgroup argument). The
flat torus is equally compact Kähler but its uniform volume carves into arcs
elementarily — so the Born-weight regions are genuine flat-Kähler volumes with
no measure-isomorphism machinery.

**Bridge is axiom-free for this instance.** `π∗μL = μFS` is the product
marginal (`Measure.fst_prod`, `c = 1`), citing only the foundational triple —
`invariant_measure_uniqueness` is **not** needed here (cf. `LF4/Instance.lean`).

**Formalisation boundary (honest scope).** "Compact Kähler" above is the
*mathematical reading* of these objects, not a formalised structure: in Lean,
`KSigma` is a product **type** and `kMuL` a product **measure**. No manifold
structure, symplectic form, or Kähler metric is constructed, and `kMuL` is not
*derived* from a volume form — Mathlib has no Kähler API, and the corpus does
not build one. What **is** machine-verified is the measure-theoretic content:
`fubiniStudyMeasure` (the Haar-on-`U(N)` pushforward, which mathematically *is*
the FS Kähler volume), its `U(N)`-invariance and uniqueness, the product
marginal bridge, and everything downstream. The identification of these
measures with Kähler/Liouville volume forms is interpretive prose backed by
standard differential geometry, not by Lean. Cf. `AXIOMS.md §3.1`
(preparation-measure origin) for the same boundary stated at the
`OnticSetup.μL` level.
-/

@[expose] public section

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF4

variable {N : ℕ} [NeZero N]

/-- `Fact (0 < 1)`, needed for `AddCircle 1`'s Haar measure to be a probability
measure. -/
instance : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- `AddCircle 1`'s Haar `volume` is a probability measure (`volume univ = 1`). -/
instance instProbAddCircleOne : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  ⟨by rw [AddCircle.measure_univ, ENNReal.ofReal_one]⟩

/-- The flat complex torus `T² = (ℝ/ℤ)²` (compact Kähler), the internal fibre. -/
abbrev KTorus : Type := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-- The total ontic space `Σ = ℂℙ^{N-1} × T²`. -/
abbrev KSigma (N : ℕ) : Type := CPN N × KTorus

/-- The product (Kähler/Liouville) volume `μL = μFS ⊗ vol_{T²}`. -/
noncomputable def kMuL (p₀ : CPN N) : Measure (KSigma N) :=
  (fubiniStudyMeasure p₀).prod (volume : Measure KTorus)

instance instProbKTorusVolume : IsProbabilityMeasure (volume : Measure KTorus) := by
  unfold KTorus
  infer_instance

instance instProbKMuL (p₀ : CPN N) : IsProbabilityMeasure (kMuL p₀) := by
  unfold kMuL
  infer_instance

/-- `U(N)` acts on `Σ = ℂℙ^{N-1} × T²` through the base factor only. -/
noncomputable instance instSMulKSigma : SMul (Matrix.unitaryGroup (Fin N) ℂ) (KSigma N) :=
  ⟨fun U p => (U • p.1, p.2)⟩

omit [NeZero N] in
@[simp] lemma kSigma_smul_def (U : Matrix.unitaryGroup (Fin N) ℂ) (p : KSigma N) :
    U • p = (U • p.1, p.2) := rfl

noncomputable instance instMulActionKSigma :
    MulAction (Matrix.unitaryGroup (Fin N) ℂ) (KSigma N) where
  one_smul p := by
    change ((1 : Matrix.unitaryGroup (Fin N) ℂ) • p.1, p.2) = p
    rw [_root_.one_smul]
  mul_smul U V p := by
    change ((U * V) • p.1, p.2) = (U • V • p.1, p.2)
    rw [SemigroupAction.mul_smul]

/-- The minimal product `OnticSetup`: `μL` is the product Kähler volume, the
flow is the identity, the preparation region is everything. -/
noncomputable def kOnticSetup (p₀ : CPN N) : CSD.LF1.OnticSetup (KSigma N) where
  μL := ⟨kMuL p₀, inferInstance⟩
  Φ := id
  hΦ_pres := MeasurePreserving.id _
  Ω0 := Set.univ
  hΩ0_meas := MeasurableSet.univ
  hΩ0_nonzero := by
    show (kMuL p₀) Set.univ ≠ 0
    rw [measure_univ]; exact one_ne_zero

/-- **Non-trivial-fibre compact-Kähler `SectorData`.** `Σ = ℂℙ^{N-1} × T²`,
`P = ℂℙ^{N-1}`, `G = U(N)`, `π = pr₁`. -/
noncomputable def kSectorData (p₀ : CPN N) :
    CSD.LF2.SectorData (KSigma N) (CPN N) (Matrix.unitaryGroup (Fin N) ℂ) where
  toOntic := kOnticSetup p₀
  π := Prod.fst
  measurable_π := measurable_fst
  measurable_smul_σ := fun U =>
    (((continuous_const_smul U).comp continuous_fst).prodMk continuous_snd).measurable
  measurable_smul_P := fun U => (continuous_const_smul U).measurable
  hμL_inv := fun U => by
    show MeasurePreserving (fun p : KSigma N => U • p) (kMuL p₀) (kMuL p₀)
    have hbase : MeasurePreserving (fun q : CPN N => U • q) (fubiniStudyMeasure p₀)
        (fubiniStudyMeasure p₀) :=
      ⟨(continuous_const_smul U).measurable, fubiniStudyMeasure_smul_invariant U p₀⟩
    have heq : (fun p : KSigma N => U • p)
        = Prod.map (fun q : CPN N => U • q) (id : KTorus → KTorus) := by
      funext p; rw [kSigma_smul_def]; rfl
    rw [heq]
    exact hbase.prod (MeasurePreserving.id _)
  hπ_equiv := fun U x => by rw [kSigma_smul_def]

/-- **Axiom-free measure bridge for the product instance.** `π∗μL = μFS`
(`c = 1`), since the torus volume is a probability measure and `π = pr₁`. -/
theorem k_measure_bridge (p₀ : CPN N) :
    ∃ c : ENNReal,
      Measure.map (kSectorData p₀).π ((kSectorData p₀).μL : Measure (KSigma N))
        = c • fubiniStudyMeasure p₀ := by
  refine ⟨1, ?_⟩
  rw [one_smul]
  show Measure.map Prod.fst (kMuL p₀) = fubiniStudyMeasure p₀
  rw [kMuL, ← Measure.fst, Measure.fst_prod]

end LF4
end CSD
