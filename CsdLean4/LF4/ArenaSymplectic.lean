/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.ProjectiveManifold
public import CsdLean4.Mathlib.Geometry.Manifold.ProductForm
public import CsdLean4.Mathlib.Geometry.Manifold.TranslationAtlasForm
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudySymplectic
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudyVolume
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceTorusVolume
public import CsdLean4.Mathlib.Geometry.Manifold.HamiltonianFlowVolume
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceSchrodingerFlow

/-!
# The arena `ℂℙⁿ × T²` as a symplectic manifold, and Hamiltonian generation on it

**TERM-SCOPE(Hamiltonian)** **TERM-SCOPE(Kahler)** — this module uses the *restricted* senses of
"Hamiltonian" and "Kahler"; `specs/TERMS.md` records what is backed and what is not.

**Category:** 3-Local (the corpus's arena, assembled from Category-1 pieces).

`R-016′` (`specs/BACKLOG.md` ▶ OPEN QUEUE #7): the arena-level `ι_X ω = dH`. Until now the
programme's arena `KSigma (N+1) = ℂℙᴺ × T²` was a manifold (Q33, `ProjectiveManifold.lean`) with
no symplectic form, and every "Hamiltonian" statement about a flow on it was either chart-level
(`RecordLayer/HamiltonianShift.lean`) or prose. This module gives the arena its form and states
the generator identity on it.

* `arenaForm N` — **the arena's symplectic form** `π₁^* ω_FS + π₂^* (dθ₁ ∧ dθ₂)`, a `C^∞` 2-form
  on `KSigma (N + 1)` over the normed model `(Fin N → ℂ) × (ℝ × ℝ)` (the product charted on the
  product normed space, `ProductSelfModel.lean`; the torus charted by translation,
  `Instances/AddCircleTranslation.lean`);
* ★★★ `arenaForm_isSymplectic` — **the arena is a symplectic manifold**: the form is closed and
  non-degenerate, as the sum of the Fubini–Study form and the torus area form
  (`IsSymplectic.prodForm`);
* `arenaChartCover`, `arenaBasis`, `arenaVolume` — the finite chart cover, a real basis of the
  model, and the top-form measure of `arenaForm^(N+1)`;
* ★★ `arenaVolume_map_hamiltonianFlow` — **Liouville on the arena**: the Hamiltonian flow of every
  smooth `H : KSigma (N+1) → ℝ` preserves `arenaVolume`, an instance of
  `IsSymplectic.map_hamiltonianFlow_topFormMeasure_wedgePow`;
* ★★ `isHamiltonianVectorField_sectorEnergy` — **`ι_X ω = dH` on the arena for a sector energy**:
  for `H : ℂℙᴺ → ℝ` with Hamiltonian vector field `X` on `ℂℙᴺ`, the field `(X, 0)` is the
  Hamiltonian vector field of `H ∘ π₁` on the arena; `hamiltonianVectorField_sectorEnergy` is the
  uniqueness reading (`X_{H∘π₁} = (X_H, 0)`);
* ★★★ `hamiltonianFlow_sectorEnergy` — **the flow of a sector energy on the arena is the sector's
  flow with the torus fixed**, by uniqueness of integral curves on the compact Hausdorff arena;
* ★★★ `hamiltonianFlow_sectorEnergy_schrodinger` — **the isolated ontic dynamics is a
  Hamiltonian flow on the arena**: the Schrödinger unitary of a Hermitian `H`, acting on the
  sector with the torus fixed, is the arena's Hamiltonian flow of `−2⟨H⟩ ∘ π₁` (Q29(e) lifted to
  the arena; A2's vector-field equation, arena level);
* ★★ `isLocallyHamiltonian_torusStrokeField` — **the rigid torus stroke `(0, a)` is locally
  Hamiltonian on the arena**: `ι_{(0,a)} ω` is a constant form on the torus factor, so
  `d (ι_X ω) = 0`.

## Honest scope

⚠️ **The arena's measure here is the top-form measure of `arenaForm^(N+1)`.** It is the corpus's
`μ_FS ⊗ vol` (`LF4/KahlerInstance.lean`) up to its total mass: `LF4/ArenaVolume.lean` proves
`arenaVolume N = arenaVolume N univ • kMuL p₀` by uniqueness of the invariant measures
(`arenaVolume_eq_smul_kMuL`), so Liouville here is Liouville for `kMuL` there
(`kMuL_smul_map_hamiltonianFlow`); the mass is `(N+1)·(4π)^N` (`arenaVolume_univ`), so the
identification holds with its constant visible (`arenaVolume_eq_ofReal_smul_kMuL`) and Liouville
holds for `kMuL` itself (`kMuL_map_hamiltonianFlow`).

⚠️ **The torus stroke is locally Hamiltonian here; its flux obstruction is the next module.**
`isLocallyHamiltonian_torusStrokeField` is the positive half of
`RecordLayer/PiecewiseHamiltonian.lean`'s "symplectic, not globally Hamiltonian" at manifold
level; the negative half, that no `H` has `(0, a)` as its Hamiltonian vector field for `a ≠ 0`, is
`LF4/ArenaStrokeFlux.lean` (`not_isHamiltonianVectorField_torusStrokeField`).

⚠️ **The measurement propagators are not read on the arena.** Nothing here identifies `jointLift`
or `hamiltonianShift` with a time-`1` map of a flow on `arenaForm`'s arena; that identification is
the content of the residue this module narrows (⚠️ RESIDUE(R-016)).

References: `Geometry/Manifold/ProductForm.lean`; `Geometry/Manifold/TranslationAtlasForm.lean`;
`Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudySymplectic.lean` (`fsForm_isSymplectic`);
`Geometry/Manifold/HamiltonianVectorField.lean` (`IsHamiltonianVectorField`, uniqueness);
`Geometry/Manifold/HamiltonianFlowVolume.lean` (Liouville); `LF4/ProjectiveManifold.lean` (Q33);
`specs/reconstruction-status.md` (A2); `specs/BACKLOG.md` (`R-016′`);
`specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open Projectivization DifferentialForm MeasureTheory
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace CSD
namespace LF4

instance instFactZeroLtOne : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- The arena's normed model: the model of `ℂℙᴺ` times the model of the torus. -/
abbrev ArenaModel (N : ℕ) : Type := (Fin N → ℂ) × (ℝ × ℝ)

/-! ### The arena as a manifold over its normed model -/

/-- The torus charted by translation, over `ℝ × ℝ`, is an analytic manifold. -/
theorem ktorus_isManifold_translation : IsManifold 𝓘(ℝ, ℝ × ℝ) ω KTorus :=
  inferInstance

/-- ★ **The arena `KSigma (N+1) = ℂℙᴺ × T²` is an analytic manifold over its normed model**,
the product charted on the product normed space. -/
theorem ksigma_isManifold_arenaModel (N : ℕ) :
    IsManifold 𝓘(ℝ, ArenaModel N) ω (KSigma (N + 1)) :=
  inferInstance

/-! ### The symplectic form -/

/-- **The arena's symplectic form** `π₁^* ω_FS + π₂^* (dθ₁ ∧ dθ₂)`. -/
def arenaForm (N : ℕ) : DifferentialForm 𝓘(ℝ, ArenaModel N) (KSigma (N + 1)) ∞ (Fin 2) ℝ :=
  prodForm (fsForm (n := N)) (AddCircle.torusAreaForm (T := 1) (T' := 1))

theorem arenaForm_apply (N : ℕ) (p : KSigma (N + 1)) :
    arenaForm N p
      = ContinuousAlternatingMap.prodSum (toFlat (fsForm (n := N) p.1)) TorusForm.areaForm := rfl

/-- ★★★ **The arena is a symplectic manifold.** -/
theorem arenaForm_isSymplectic (N : ℕ) : (arenaForm N).IsSymplectic :=
  (fsForm_isSymplectic N).prodForm AddCircle.torusAreaForm_isSymplectic

/-! ### The chart cover, the basis, and the arena volume -/

/-- A finite cover of the arena by chart domains: the affine charts of `ℂℙᴺ` times the two
translation charts of each circle. -/
def arenaChartCover (N : ℕ) : ChartCover (ArenaModel N) (KSigma (N + 1)) :=
  (affineChartCover N).prod
    (AddCircle.translationChartCover.prod AddCircle.translationChartCover)

/-- A real basis of the arena's model, indexed by `Fin (2 * (N + 1))`: the standard basis of the
sector factor followed by the two coordinate vectors of the torus factor (`prodTorusBasis`,
`Instances/ProjectiveSpaceTorusVolume.lean`). -/
def arenaBasis (N : ℕ) : Module.Basis (Fin (2 * (N + 1))) ℝ (ArenaModel N) :=
  prodTorusBasis N

/-- The Haar measure on the arena's model, as the explicit product of the factors' Lebesgue
measures (instance search does not see `volume` on a product as `Measure.prod`). -/
def arenaModelHaar (N : ℕ) : Measure (ArenaModel N) :=
  (volume : Measure (Fin N → ℂ)).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))

instance instIsAddHaarMeasure_arenaModelHaar (N : ℕ) : (arenaModelHaar N).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- **The arena volume**: the top-form measure of `arenaForm^(N+1)`. -/
def arenaVolume (N : ℕ) : Measure (KSigma (N + 1)) :=
  topFormMeasure (arenaModelHaar N) (arenaBasis N) (fun x => wedgePow (arenaForm N) (N + 1) x)
    (arenaChartCover N)

/-- ★★ **Liouville on the arena.** The Hamiltonian flow of every smooth `H` on the arena
preserves the arena volume. -/
theorem arenaVolume_map_hamiltonianFlow {N : ℕ} {H : KSigma (N + 1) → ℝ}
    (hH : ContMDiff 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) ∞ H) (t : ℝ) :
    Measure.map ((arenaForm_isSymplectic N).hamiltonianFlow hH t) (arenaVolume N)
      = arenaVolume N :=
  (arenaForm_isSymplectic N).map_hamiltonianFlow_topFormMeasure_wedgePow (arenaModelHaar N) hH
    (N + 1) (arenaBasis N) (arenaChartCover N) t

/-! ### Sector energies: `ι_X ω = dH` on the arena -/

/-- A function on the sector, read on the arena. -/
def sectorEnergy {N : ℕ} (H : CPN (N + 1) → ℝ) : KSigma (N + 1) → ℝ := fun p => H p.1

theorem sectorEnergy_apply {N : ℕ} (H : CPN (N + 1) → ℝ) (p : KSigma (N + 1)) :
    sectorEnergy H p = H p.1 := rfl

/-- A `C^∞` sector energy is `C^∞` on the arena. -/
theorem contMDiff_sectorEnergy {N : ℕ} {H : CPN (N + 1) → ℝ}
    (hH : ContMDiff 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) ∞ H) :
    ContMDiff 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) ∞ (sectorEnergy H) := by
  show ContMDiff 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) ∞ (H ∘ Prod.fst)
  exact hH.comp
    (Prod.contMDiff_fst_self (E := Fin N → ℂ) (F := ℝ × ℝ) (M := CPN (N + 1)) (N := KTorus))

/-- The derivative of a sector energy on the arena is the derivative on the sector, read on the
first component. -/
theorem mfderiv_sectorEnergy {N : ℕ} {H : CPN (N + 1) → ℝ}
    (hH : ContMDiff 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) ∞ H) (p : KSigma (N + 1)) :
    mfderiv 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) (sectorEnergy H) p
      = (mfderiv 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) H p.1).comp
          (ContinuousLinearMap.fst ℝ (Fin N → ℂ) (ℝ × ℝ)) :=
  (((hH p.1).mdifferentiableAt (by simp)).hasMFDerivAt.comp p
    (Prod.hasMFDerivAt_fst_self (E := Fin N → ℂ) (F := ℝ × ℝ) p)).mfderiv

/-- ★★ **`ι_X ω = dH` on the arena for a sector energy.** If `X` is a Hamiltonian vector field of
`H` on `ℂℙᴺ` for the Fubini–Study form, then `(X, 0)` is a Hamiltonian vector field of `H ∘ π₁` on
the arena for `arenaForm`. -/
theorem isHamiltonianVectorField_sectorEnergy {N : ℕ} {H : CPN (N + 1) → ℝ}
    (hH : ContMDiff 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) ∞ H)
    {X : ∀ x : CPN (N + 1), TangentSpace 𝓘(ℝ, Fin N → ℂ) x}
    (hX : IsHamiltonianVectorField (fun x => fsForm (n := N) x) X H) :
    IsHamiltonianVectorField (fun p => arenaForm N p)
      (fun p : KSigma (N + 1) => ((X p.1, (0 : ℝ × ℝ)) : TangentSpace 𝓘(ℝ, ArenaModel N) p))
      (sectorEnergy H) := by
  intro p v
  have hv := hX p.1 (v : ArenaModel N).1
  have hz : TorusForm.areaForm ![(0 : ℝ × ℝ), (v : ArenaModel N).2] = 0 :=
    ContinuousMultilinearMap.map_coord_zero _ 0 rfl
  have h1 : (arenaForm N p) ![((X p.1 : Fin N → ℂ), (0 : ℝ × ℝ)), v]
      = toFlat (fsForm (n := N) p.1) ![(X p.1 : Fin N → ℂ), (v : ArenaModel N).1]
        + TorusForm.areaForm ![(0 : ℝ × ℝ), (v : ArenaModel N).2] :=
    ContinuousAlternatingMap.prodSum_pair (toFlat (fsForm (n := N) p.1)) TorusForm.areaForm
      ((X p.1 : Fin N → ℂ), (0 : ℝ × ℝ)) (v : ArenaModel N)
  have h2 : mfderiv 𝓘(ℝ, ArenaModel N) 𝓘(ℝ, ℝ) (sectorEnergy H) p v
      = mfderiv 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) H p.1 (v : ArenaModel N).1 := by
    rw [mfderiv_sectorEnergy hH p]; rfl
  refine h1.trans ?_
  rw [hz, add_zero]
  exact hv.trans h2.symm

/-- ★★ **`X_{H ∘ π₁} = (X_H, 0)`**: the Hamiltonian vector field of a sector energy on the arena
is the sector's Hamiltonian vector field with no torus component (uniqueness for the symplectic
`arenaForm`). -/
theorem hamiltonianVectorField_sectorEnergy {N : ℕ} {H : CPN (N + 1) → ℝ}
    (hH : ContMDiff 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) ∞ H) (p : KSigma (N + 1)) :
    (arenaForm_isSymplectic N).hamiltonianVectorField (sectorEnergy H) p
      = (((fsForm_isSymplectic N).hamiltonianVectorField H p.1, (0 : ℝ × ℝ)) :
          TangentSpace 𝓘(ℝ, ArenaModel N) p) := by
  have h := isHamiltonianVectorField_sectorEnergy hH
    ((fsForm_isSymplectic N).hamiltonianVectorField_isHamiltonianVectorField H)
  exact (congrFun (h.eq_hamiltonianVectorField (arenaForm_isSymplectic N).nondegenerate) p).symm

/-! ### The flow of a sector energy: the sector's flow, the torus fixed -/

/-- The curve `t ↦ (flow_H t x, θ)` is an integral curve of `(X_H, 0)` on the arena. -/
theorem isMIntegralCurve_sectorFlow {N : ℕ} {H : CPN (N + 1) → ℝ}
    (hH : ContMDiff 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) ∞ H) (x : CPN (N + 1)) (θ : KTorus) :
    IsMIntegralCurve (fun t : ℝ => (((fsForm_isSymplectic N).hamiltonianFlow hH t x, θ) :
        KSigma (N + 1)))
      ((arenaForm_isSymplectic N).hamiltonianVectorField (sectorEnergy H)) := by
  intro t
  have h₁ := isMIntegralCurve_integralFlow
    ((fsForm_isSymplectic N).contMDiff_hamiltonianVectorField_tangent hH) x t
  have h₂ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) (fun _ : ℝ => θ) t
      (0 : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace 𝓘(ℝ, ℝ × ℝ) θ) :=
    hasMFDerivAt_const θ t
  have h := h₁.prodMk_self h₂
  rw [hamiltonianVectorField_sectorEnergy hH]
  have hclm : ((1 : ℝ →L[ℝ] ℝ).smulRight ((fsForm_isSymplectic N).hamiltonianVectorField H
        (integralFlow ((fsForm_isSymplectic N).contMDiff_hamiltonianVectorField_tangent hH)
          t x))).prod
        (0 : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace 𝓘(ℝ, ℝ × ℝ) θ)
      = (1 : ℝ →L[ℝ] ℝ).smulRight
          ((((fsForm_isSymplectic N).hamiltonianVectorField H
            (integralFlow ((fsForm_isSymplectic N).contMDiff_hamiltonianVectorField_tangent hH)
              t x) : Fin N → ℂ), (0 : ℝ × ℝ)) :
            TangentSpace 𝓘(ℝ, ArenaModel N)
              ((integralFlow ((fsForm_isSymplectic N).contMDiff_hamiltonianVectorField_tangent hH)
                t x, θ) : KSigma (N + 1))) := by
    refine ContinuousLinearMap.ext fun s => Prod.ext ?_ ?_
    · rfl
    · exact (smul_zero s).symm
  exact h.congr_deriv hclm

/-- ★★★ **The Hamiltonian flow of a sector energy on the arena is the sector's Hamiltonian flow
with the torus fixed**: `φ^{H∘π₁}_t (x, θ) = (φ^H_t x, θ)`. Uniqueness of integral curves on the
(Hausdorff, compact) arena. -/
theorem hamiltonianFlow_sectorEnergy {N : ℕ} {H : CPN (N + 1) → ℝ}
    (hH : ContMDiff 𝓘(ℝ, Fin N → ℂ) 𝓘(ℝ, ℝ) ∞ H) (t : ℝ) (x : CPN (N + 1)) (θ : KTorus) :
    (arenaForm_isSymplectic N).hamiltonianFlow (contMDiff_sectorEnergy hH) t (x, θ)
      = ((fsForm_isSymplectic N).hamiltonianFlow hH t x, θ) := by
  have h := integralFlow_eq_of_isMIntegralCurve
    ((arenaForm_isSymplectic N).contMDiff_hamiltonianVectorField_tangent
      (contMDiff_sectorEnergy hH))
    (isMIntegralCurve_sectorFlow hH x θ) (x := (x, θ))
    (by simp only [IsSymplectic.hamiltonianFlow, integralFlow_zero])
  exact (congrFun h t).symm

/-- ★★★ **The isolated ontic dynamics is a Hamiltonian flow on the arena** (A2's vector-field
equation, arena level): for a Hermitian `H`, the Hamiltonian flow on `ℂℙᴺ × T²` of the sector
energy `−2⟨H⟩ ∘ π₁` is the Schrödinger unitary on the sector with the torus fixed. -/
theorem hamiltonianFlow_sectorEnergy_schrodinger {N : ℕ}
    {H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} (hH : H.IsHermitian) (t : ℝ)
    (x : CPN (N + 1)) (θ : KTorus) :
    (arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_sectorEnergy (contMDiff_schrodingerHamiltonian H)) t (x, θ)
      = (Matrix.schrodingerUnitary hH t • x, θ) := by
  rw [hamiltonianFlow_sectorEnergy (contMDiff_schrodingerHamiltonian H),
    hamiltonianFlow_schrodingerHamiltonian hH]

/-! ### The torus stroke: locally Hamiltonian on the arena -/

/-- **The rigid torus translation field** `(0, a)` on the arena: the generator of the record
layer's fibre strokes (`RecordLayer/PiecewiseHamiltonian.lean`), read on the arena. -/
def torusStrokeField (N : ℕ) (a : ℝ × ℝ) (p : KSigma (N + 1)) :
    TangentSpace 𝓘(ℝ, ArenaModel N) p :=
  ((0 : Fin N → ℂ), a)

/-- The interior product `ι_{(0,a)} arenaForm` is the constant 1-form `dθ ↦ area (a, dθ)` on the
torus factor, pulled back to the arena. -/
theorem interiorProduct_arenaForm_torusStrokeField (N : ℕ) (a : ℝ × ℝ) :
    interiorProduct (fun p => arenaForm N p) (torusStrokeField N a)
      = prodFamily
          (fun x : CPN (N + 1) => (0 : TangentSpace 𝓘(ℝ, Fin N → ℂ) x [⋀^Fin 1]→L[ℝ]
            Bundle.Trivial (CPN (N + 1)) ℝ x))
          (constFamily (ContinuousAlternatingMap.curryLeft (E := ℝ × ℝ) (F := ℝ)
            TorusForm.areaForm a)) := by
  funext p
  -- the identity on the flat model, where every piece is visible
  have key : ∀ w : Fin 1 → ArenaModel N,
      ContinuousAlternatingMap.prodSum (toFlat (fsForm (n := N) p.1)) TorusForm.areaForm
        (Matrix.vecCons (((0 : Fin N → ℂ), a) : ArenaModel N) w)
      = ContinuousAlternatingMap.prodSum (0 : (Fin N → ℂ) [⋀^Fin 1]→L[ℝ] ℝ)
        (ContinuousAlternatingMap.curryLeft (E := ℝ × ℝ) (F := ℝ) TorusForm.areaForm a) w := by
    intro w
    rw [ContinuousAlternatingMap.prodSum_apply, ContinuousAlternatingMap.prodSum_apply,
      ContinuousAlternatingMap.curryLeft_apply_apply, ContinuousAlternatingMap.coe_zero,
      Pi.zero_apply, zero_add]
    have h1 : (fun i => (Matrix.vecCons (((0 : Fin N → ℂ), a) : ArenaModel N) w i).1)
        = Matrix.vecCons (0 : Fin N → ℂ) (fun i => (w i).1) := by
      funext i; fin_cases i <;> rfl
    have h2 : (fun i => (Matrix.vecCons (((0 : Fin N → ℂ), a) : ArenaModel N) w i).2)
        = Matrix.vecCons a (fun i => (w i).2) := by
      funext i; fin_cases i <;> rfl
    have h0 : toFlat (fsForm (n := N) p.1)
        (Matrix.vecCons (0 : Fin N → ℂ) (fun i => (w i).1)) = 0 :=
      ContinuousMultilinearMap.map_coord_zero _ 0 rfl
    rw [h1, h2, h0, zero_add]
  exact ContinuousAlternatingMap.ext fun v => key v

/-- ★★ **The torus stroke is locally Hamiltonian on the arena**: `d (ι_{(0,a)} ω) = 0`. Its
interior product is a constant form on the torus factor, whose exterior derivative vanishes. -/
theorem isLocallyHamiltonian_torusStrokeField (N : ℕ) (a : ℝ × ℝ) :
    IsLocallyHamiltonian (fun p => arenaForm N p) (torusStrokeField N a) := by
  intro p
  rw [interiorProduct_arenaForm_torusStrokeField,
    mextDerivFamily_prodFamily contMDiff_zeroFamily (contMDiff_constFamily _) p,
    mextDerivFamily_zeroFamily, mextDerivFamily_constFamily]
  exact ContinuousAlternatingMap.prodSum_zero_zero

end LF4
end CSD

end
