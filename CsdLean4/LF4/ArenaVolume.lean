/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.ArenaSymplectic
public import CsdLean4.Mathlib.Geometry.Manifold.FormInvariance
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudyInvariance
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The arena volume is the corpus's `μ_FS ⊗ vol_{T²}`

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 3-Local (the corpus's arena, assembled from Category-1 pieces).

`specs/BACKLOG.md` ▶ OPEN QUEUE #29. `ArenaSymplectic.lean` gave the arena `ℂℙᴺ × T²` its
symplectic form and the top-form measure `arenaVolume` of `arenaForm^(N+1)`, and proved Liouville
for that measure; the record layer's Liouville statements live on the corpus's `kMuL = μ_FS ⊗ vol`
(`KahlerInstance.lean`). This module identifies the two, up to the constant that is the arena
volume's total mass, by uniqueness rather than by the binomial expansion of the top power:

* ★ `arenaVolume_map_smul` — **the arena volume is invariant under `U(N+1)` acting on the
  sector**: the action preserves `ω_FS` in charts (`preservesLocalRep_fsForm_smul`), the identity
  preserves the torus form, and a product of chart-preserving maps preserves the product form and
  its top power (`PreservesLocalRep.prodMap`, `.wedgePow`, `.map_topFormMeasure`);
* ★ `arenaVolume_map_addLeft` — **the arena volume is invariant under translation of the torus**:
  translation is a chart translation of the translation atlas
  (`AddCircle.isChartTranslation_addLeft`), so it preserves the constant area form;
* ★★★ `arenaVolume_eq_smul_kMuL` — **`arenaVolume = c · (μ_FS ⊗ vol_{T²})`** with
  `c = arenaVolume univ`: the sector marginal of the normalised arena volume is a `U(N+1)`-invariant
  probability measure, hence `μ_FS` (`fsMeasure_unique`); each torus slice is a
  translation-invariant finite measure on the compact group `T²`, hence a multiple of Haar
  (`isAddInvariant_eq_smul_of_compactSpace`); rectangles then determine the product
  (`Measure.prod_eq`).

So Liouville on the arena (`arenaVolume_map_hamiltonianFlow`) is Liouville for the corpus's
`kMuL`, and the flow of every sector energy, in particular the Schrödinger flow
(`hamiltonianFlow_sectorEnergy_schrodinger`), preserves `kMuL` as a manifold-level theorem.

## Honest scope

⚠️ **The constant is the total mass, not `(N+1)·(4π)^N`.** `arenaVolume_eq_smul_kMuL` reads
`arenaVolume N = arenaVolume N univ • kMuL p₀`; the constant is finite
(`isFiniteMeasure_arenaVolume`) but its value, and with it the non-vanishing of `arenaVolume`,
is not computed here. Both follow from the binomial identity
`(π₁^* α + π₂^* β)^{N+1} = (N+1) · π₁^* α^N ∧ π₂^* β` for the flat top power, which is not in the
corpus (`ProductForm.lean`, honest scope). If `arenaVolume N = 0` the identity holds with `c = 0`;
that case is not excluded here.

⚠️ **Invariance is proved for the two group actions the identification needs**, `U(N+1) × id`
and `id × T²`; no other symplectomorphism of the arena is read in charts.

References: `LF4/ArenaSymplectic.lean` (`arenaVolume`, Liouville on the arena);
`LF4/KahlerInstance.lean` (`kMuL`); `LF4/KahlerVolumeForced.lean`
(`manyToOneSetup_liouville_eq_product`); `Geometry/Manifold/FormInvariance.lean`;
`LinearAlgebra/Projectivization/FubiniStudyUnique.lean` (`fsMeasure_unique`);
`Mathlib/MeasureTheory/Measure/Haar/Unique.lean`; `specs/BACKLOG.md` (#29);
`specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open Projectivization DifferentialForm MeasureTheory Matrix.UnitaryGroup
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace CSD
namespace LF4

/-! ### Finiteness -/

/-- ★ The arena volume is a finite measure (the arena is compact, the density continuous). -/
instance isFiniteMeasure_arenaVolume (N : ℕ) : IsFiniteMeasure (arenaVolume N) :=
  isFiniteMeasure_topFormMeasure (arenaModelHaar N) (arenaBasis N) _
    (wedgePow (arenaForm N) (N + 1)).contMDiff_toFun (arenaChartCover N)

/-! ### The two invariances -/

/-- The unitary action on the sector, read on the arena, preserves the arena form in charts. -/
theorem preservesLocalRep_arenaForm_smul (N : ℕ) (U : Matrix.unitaryGroup (Fin (N + 1)) ℂ) :
    PreservesLocalRep (fun p => arenaForm N p)
      (Prod.map (fun x : CPN (N + 1) => U • x) (id : KTorus → KTorus)) :=
  PreservesLocalRep.prodMap (α := fun x => fsForm (n := N) x)
    (β := fun y => AddCircle.torusAreaForm (T := 1) (T' := 1) y)
    (preservesLocalRep_fsForm_smul U) (preservesLocalRep_id _)

/-- Translation of the torus, read on the arena, preserves the arena form in charts. -/
theorem preservesLocalRep_arenaForm_addLeft (N : ℕ) (θ : KTorus) :
    PreservesLocalRep (fun p => arenaForm N p)
      (Prod.map (id : CPN (N + 1) → CPN (N + 1)) (fun y : KTorus => θ + y)) :=
  PreservesLocalRep.prodMap (α := fun x => fsForm (n := N) x)
    (β := fun y => AddCircle.torusAreaForm (T := 1) (T' := 1) y)
    (preservesLocalRep_id _)
    (preservesLocalRep_constFamily TorusForm.areaForm
      ((AddCircle.isChartTranslation_addLeft θ.1).prodMap
        (AddCircle.isChartTranslation_addLeft θ.2)))

/-- ★ **The arena volume is invariant under `U(N+1)` acting on the sector.** -/
theorem arenaVolume_map_smul (N : ℕ) (U : Matrix.unitaryGroup (Fin (N + 1)) ℂ) :
    Measure.map (fun p : KSigma (N + 1) => U • p) (arenaVolume N) = arenaVolume N :=
  PreservesLocalRep.map_topFormMeasure (arenaModelHaar N) (arenaBasis N) (arenaChartCover N)
    ((Homeomorph.smul U).prodCongr (Homeomorph.refl KTorus))
    ((preservesLocalRep_arenaForm_smul N U).wedgePow (N + 1))

/-- ★ **The arena volume is invariant under translation of the torus.** -/
theorem arenaVolume_map_addLeft (N : ℕ) (θ : KTorus) :
    Measure.map (fun p : KSigma (N + 1) => (p.1, θ + p.2)) (arenaVolume N) = arenaVolume N :=
  PreservesLocalRep.map_topFormMeasure (arenaModelHaar N) (arenaBasis N) (arenaChartCover N)
    ((Homeomorph.refl (CPN (N + 1))).prodCongr (Homeomorph.addLeft θ))
    ((preservesLocalRep_arenaForm_addLeft N θ).wedgePow (N + 1))

/-! ### The identification -/

theorem measurable_kSigma_smul (N : ℕ) (U : Matrix.unitaryGroup (Fin (N + 1)) ℂ) :
    Measurable (fun p : KSigma (N + 1) => U • p) :=
  (((continuous_const_smul U).comp continuous_fst).prodMk continuous_snd).measurable

theorem measurable_kSigma_addLeft (N : ℕ) (θ : KTorus) :
    Measurable (fun p : KSigma (N + 1) => (p.1, θ + p.2)) :=
  (continuous_fst.prodMk (continuous_const.add continuous_snd)).measurable

/-- ★★★ **The arena volume is the corpus's `μ_FS ⊗ vol_{T²}` up to its total mass**:
`arenaVolume N = arenaVolume N univ • kMuL p₀`, for every base point `p₀`. -/
theorem arenaVolume_eq_smul_kMuL (N : ℕ) (p₀ : CPN (N + 1)) :
    arenaVolume N = arenaVolume N Set.univ • kMuL p₀ := by
  by_cases h0 : arenaVolume N Set.univ = 0
  · rw [h0, zero_smul]
    exact Measure.measure_univ_eq_zero.1 h0
  have hct : arenaVolume N Set.univ ≠ ⊤ := measure_ne_top _ _
  -- the normalised arena volume
  set ν : Measure (KSigma (N + 1)) := (arenaVolume N Set.univ)⁻¹ • arenaVolume N with hν
  have : IsProbabilityMeasure ν :=
    ⟨by rw [hν, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 hct]⟩
  have hνU : ∀ U : Matrix.unitaryGroup (Fin (N + 1)) ℂ,
      Measure.map (fun p : KSigma (N + 1) => U • p) ν = ν := fun U => by
    rw [hν, Measure.map_smul, arenaVolume_map_smul]
  have hνθ : ∀ θ : KTorus,
      Measure.map (fun p : KSigma (N + 1) => (p.1, θ + p.2)) ν = ν := fun θ => by
    rw [hν, Measure.map_smul, arenaVolume_map_addLeft]
  -- the sector marginal is a `U(N+1)`-invariant probability measure, hence Fubini–Study
  set μ₁ : Measure (CPN (N + 1)) := ν.map Prod.fst with hμ₁
  have : IsProbabilityMeasure μ₁ :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hμ₁U : ∀ U : Matrix.unitaryGroup (Fin (N + 1)) ℂ,
      Measure.map (fun x => U • x) μ₁ = μ₁ := fun U => by
    rw [hμ₁, Measure.map_map (continuous_const_smul U).measurable measurable_fst]
    have h : ((fun x : CPN (N + 1) => U • x) ∘ Prod.fst)
        = Prod.fst ∘ (fun p : KSigma (N + 1) => U • p) := rfl
    rw [h, ← Measure.map_map measurable_fst (measurable_kSigma_smul N U), hνU U]
  have hFS : μ₁ = fsMeasure p₀ := fsMeasure_unique p₀ μ₁ hμ₁U
  -- each torus slice is translation-invariant, hence a multiple of Haar
  have : Measure.IsAddHaarMeasure (volume : Measure KTorus) :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (AddCircle (1 : ℝ)))
      (volume : Measure (AddCircle (1 : ℝ)))
  have hrect : ∀ A : Set (CPN (N + 1)), MeasurableSet A → ∀ B : Set KTorus, MeasurableSet B →
      ν (A ×ˢ B) = fsMeasure p₀ A * volume B := by
    intro A hA B hB
    set σ : Measure KTorus := (ν.restrict (A ×ˢ Set.univ)).map Prod.snd with hσ
    have hσB : ∀ B : Set KTorus, MeasurableSet B → σ B = ν (A ×ˢ B) := fun B hB => by
      rw [hσ, Measure.map_apply measurable_snd hB, Measure.restrict_apply (measurable_snd hB)]
      congr 1
      ext ⟨x, y⟩
      simp [and_comm]
    have : σ.IsAddLeftInvariant := ⟨fun θ => by
      have h1 : ((fun y : KTorus => θ + y) ∘ Prod.snd)
          = Prod.snd ∘ (fun p : KSigma (N + 1) => (p.1, θ + p.2)) := rfl
      have h2 : (ν.restrict (A ×ˢ Set.univ)).map (fun p : KSigma (N + 1) => (p.1, θ + p.2))
          = ν.restrict (A ×ˢ Set.univ) := by
        have h3 : (fun p : KSigma (N + 1) => (p.1, θ + p.2)) ⁻¹' (A ×ˢ Set.univ)
            = A ×ˢ Set.univ := by
          ext ⟨x, y⟩
          simp
        conv_lhs => rw [← h3]
        rw [← Measure.restrict_map (measurable_kSigma_addLeft N θ) (hA.prod MeasurableSet.univ),
          hνθ θ]
      rw [hσ, Measure.map_map (measurable_const_add θ) measurable_snd, h1,
        ← Measure.map_map measurable_snd (measurable_kSigma_addLeft N θ), h2]⟩
    have hσ_eq := Measure.isAddInvariant_eq_smul_of_compactSpace σ volume
    have hσuniv : σ Set.univ = fsMeasure p₀ A := by
      rw [hσB _ MeasurableSet.univ, ← hFS, hμ₁, Measure.map_apply measurable_fst hA,
        Set.prod_univ]
    rw [← hσB B hB, ← hσuniv, hσ_eq, Measure.smul_apply, Measure.smul_apply, measure_univ,
      ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, mul_one]
  -- rectangles determine the product
  have hprod : (fsMeasure p₀).prod (volume : Measure KTorus) = ν :=
    Measure.prod_eq fun A B hA hB => hrect A hA B hB
  calc arenaVolume N = arenaVolume N Set.univ • ν := by
        rw [hν, smul_smul, ENNReal.mul_inv_cancel h0 hct, one_smul]
    _ = arenaVolume N Set.univ • kMuL p₀ := by rw [← hprod]; rfl

/-- ★★ **Liouville for the corpus's `kMuL`, at manifold level**: the Hamiltonian flow of every
smooth `H` on the arena preserves `μ_FS ⊗ vol_{T²}` scaled by the arena volume's mass. -/
theorem kMuL_smul_map_hamiltonianFlow (N : ℕ) (p₀ : CPN (N + 1)) {H : KSigma (N + 1) → ℝ}
    (hH : ContMDiff 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) ∞ H) (t : ℝ) :
    Measure.map ((arenaForm_isSymplectic N).hamiltonianFlow hH t)
        (arenaVolume N Set.univ • kMuL p₀)
      = arenaVolume N Set.univ • kMuL p₀ := by
  rw [← arenaVolume_eq_smul_kMuL N p₀]
  exact arenaVolume_map_hamiltonianFlow hH t

end LF4
end CSD

end
