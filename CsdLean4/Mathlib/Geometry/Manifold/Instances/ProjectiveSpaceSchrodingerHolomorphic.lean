/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceSchrodingerFlow
public import CsdLean4.Mathlib.Geometry.Manifold.HolomorphicVectorField

/-!
# The Schrödinger field on `ℂℙⁿ` is holomorphic, and its flow is holomorphic and Killing

**TERM-SCOPE(Hamiltonian)** **TERM-SCOPE(Kahler)** — this module uses the *restricted* senses of
"Hamiltonian" and "Kähler"; `specs/TERMS.md` records what is backed and what is not.

**Category:** 1-Mathlib (CSD-free; upstream target `Mathlib.Geometry.Manifold.Instances`).

KG-3′ (`specs/BACKLOG.md` #30). `ProjectiveSpaceFubiniStudySymplectic.lean` made `ℂℙⁿ` a Kähler
manifold with `J = i·` in every chart (`fsForm_isKahler`), and `ProjectiveSpaceSchrodingerFlow.lean`
made the Schrödinger flow `p ↦ exp(-itH) • p` the Hamiltonian flow of `−2⟨H⟩` for the Fubini–Study
form. The one step of the Ashtekar–Schilling route that the flow's unitarity carries but no
theorem yet stated is that this Hamiltonian vector field is *holomorphic*, equivalently (by the
Kähler compatibility) *Killing*. Both are here:

* ★ `hasMFDerivAt_smul`, `isHolomorphicMap_smul` — **the unitary action on `ℂℙⁿ` is a
  holomorphic map**: in charts it is `uTrans U`, `ℂ`-differentiable, so its manifold derivative
  commutes with `J = i·`;
* ★ `fsForm_smul_mfderiv` — **the unitary action is symplectic at bundle level**,
  `U^* ω_FS = ω_FS` (`fsModelForm_uTrans` read through the tangent spaces);
* ★ `fsMetric_smul_mfderiv` — **the unitary action is an isometry of the Fubini–Study metric**
  `g = ω_FS (J ·, ·)` (`IsAlmostKahler.metric_mfderiv_eq`);
* ★★ `isHolomorphicMap_hamiltonianFlow_schrodinger`, `fsMetric_hamiltonianFlow_schrodinger` —
  **the Hamiltonian flow of `−2⟨H⟩` is holomorphic and Killing at every time**, through
  `hamiltonianFlow_schrodingerHamiltonian`;
* `chartField_schrodingerField` — the Schrödinger field read in *any* affine chart is
  `schrodingerChartField` in that chart (uniqueness of the local Hamiltonian vector);
* `differentiableAt_schrodingerChartField` — the chart field is `ℂ`-differentiable (it is a
  quadratic polynomial with complex coefficients);
* ★★ `isHolomorphicVectorField_schrodingerField` — **`X_{−2⟨H⟩}` is a holomorphic vector field
  of the Kähler manifold `ℂℙⁿ`**: in every chart its derivative commutes with `i·`.

## Honest scope

⚠️ **Holomorphic in the atlas sense** (`IsHolomorphicVectorField`, `HolomorphicVectorField.lean`):
the chart-by-chart statement, which on the holomorphic atlas of `ℂℙⁿ` is the standard notion. No
Lie derivative `L_X J` is built; the flow-level statements need none.

⚠️ **Hermitian `H` only**, as everywhere in the Schrödinger module (`hH : H.IsHermitian`); the
chart-field lemmas hold for any `H`.

References: `Geometry/Manifold/Instances/ProjectiveSpaceSchrodingerFlow.lean`
(`schrodingerField`, `hamiltonianFlow_schrodingerHamiltonian`);
`Geometry/Manifold/Instances/ProjectiveSpaceFubiniStudySymplectic.lean` (`fsJ`, `fsForm_isKahler`,
`fderiv_chart_transition_smul_I`); `Geometry/Manifold/Instances/ProjectiveSpaceUnitaryAction.lean`
(`uTrans`, `fsModelForm_uTrans`); `Geometry/Manifold/HolomorphicVectorField.lean`;
`specs/BACKLOG.md` (#30); `specs/future-work.md` (KG-3).
-/

@[expose] public section

noncomputable section

open Bundle Filter Topology Set
open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix
open Kahler DifferentialForm Matrix.UnitaryGroup

namespace Projectivization

variable {n : ℕ}

/-! ### The unitary action is holomorphic, symplectic and Killing -/

/-- The chart point of `x` lies in the domain where the chart expression of `U •` from the chart
at `x` to the chart at `U • x` is defined. -/
theorem chartFun_mem_uDomain (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (x : ℙ ℂ (Ambient n)) :
    toEuclideanLinearEquiv U (insertOne (idx x) (chartFun (idx x) x)) (idx (U • x)) ≠ 0 := by
  have hx : (chartAt (Fin n → ℂ) x).symm (chartFun (idx x) x) = x :=
    chartInv_chartFun (idx x) x (idx_spec x)
  refine (smul_symm_mem_source_iff U x (U • x) (chartFun (idx x) x)).1 ?_
  rw [hx]
  exact mem_chart_source _ (U • x)

/-- The chart expression of the unitary action is `ℂ`-differentiable at the chart point. -/
theorem differentiableAt_uTrans_chartFun (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ)
    (x : ℙ ℂ (Ambient n)) :
    DifferentiableAt ℂ (uTrans U (idx x) (idx (U • x))) (chartFun (idx x) x) :=
  ((contDiffOn_uTrans U (idx x) (idx (U • x))).contDiffAt
    ((isOpen_uDomain U (idx x) (idx (U • x))).mem_nhds (chartFun_mem_uDomain U x))).differentiableAt
    (by simp)

/-- ★ **The manifold derivative of the unitary action** is the real restriction of the complex
derivative of its chart expression `uTrans U`. -/
theorem hasMFDerivAt_smul (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (x : ℙ ℂ (Ambient n)) :
    HasMFDerivAt (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ (Fin n → ℂ))
      (fun p : ℙ ℂ (Ambient n) => U • p) x
      ((fderiv ℂ (uTrans U (idx x) (idx (U • x))) (chartFun (idx x) x)).restrictScalars ℝ) := by
  refine ⟨(continuous_const_smul U).continuousAt, ?_⟩
  have hw : writtenInExtChartAt (modelWithCornersSelf ℝ (Fin n → ℂ))
      (modelWithCornersSelf ℝ (Fin n → ℂ)) x (fun p : ℙ ℂ (Ambient n) => U • p)
      = uTrans U (idx x) (idx (U • x)) := by
    rw [← chartAt_smul_comp_symm U x (U • x)]
    funext w
    simp only [writtenInExtChartAt, Function.comp, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id]
  rw [hw]
  simp only [modelWithCornersSelf_coe, Set.range_id, extChartAt_coe, Function.comp_apply, id]
  exact ((differentiableAt_uTrans_chartFun U x).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt

theorem mfderiv_smul_eq (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (x : ℙ ℂ (Ambient n)) :
    mfderiv (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ (Fin n → ℂ))
        (fun p : ℙ ℂ (Ambient n) => U • p) x
      = (fderiv ℂ (uTrans U (idx x) (idx (U • x))) (chartFun (idx x) x)).restrictScalars ℝ :=
  (hasMFDerivAt_smul U x).mfderiv

/-- ★ **The unitary action is a holomorphic map of `ℂℙⁿ`**: its derivative commutes with
`J = i·`. -/
theorem isHolomorphicMap_smul (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) :
    IsHolomorphicMap fsJ (fun p : ℙ ℂ (Ambient n) => U • p) := by
  refine ⟨fun x => (hasMFDerivAt_smul U x).mdifferentiableAt, fun x v => ?_⟩
  rw [mfderiv_smul_eq]
  exact map_smul (fderiv ℂ (uTrans U (idx x) (idx (U • x))) (chartFun (idx x) x)) Complex.I
    (tangentToModel v)

/-- ★ **The unitary action is symplectic at bundle level**: `U^* ω_FS = ω_FS`, read on the
tangent spaces. -/
theorem fsForm_smul_mfderiv (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (x : ℙ ℂ (Ambient n))
    (a b : TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ)) x) :
    fsForm (U • x)
        ![mfderiv (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ (Fin n → ℂ))
            (fun p : ℙ ℂ (Ambient n) => U • p) x a,
          mfderiv (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ (Fin n → ℂ))
            (fun p : ℙ ℂ (Ambient n) => U • p) x b]
      = fsForm x ![a, b] := by
  rw [mfderiv_smul_eq]
  have hR : fderiv ℝ (uTrans U (idx x) (idx (U • x))) (chartFun (idx x) x)
      = (fderiv ℂ (uTrans U (idx x) (idx (U • x))) (chartFun (idx x) x)).restrictScalars ℝ :=
    ((differentiableAt_uTrans_chartFun U x).hasFDerivAt.restrictScalars ℝ).fderiv
  have h := fsModelForm_uTrans U (idx x) (idx (U • x)) (chartFun_mem_uDomain U x)
  rw [hR] at h
  have hu : uTrans U (idx x) (idx (U • x)) (chartFun (idx x) x) = chartFun (idx (U • x)) (U • x) := by
    rw [← chartFun_smul_chartInv, chartInv_chartFun _ _ (idx_spec x)]
  show fsModelForm (chartFun (idx (U • x)) (U • x)) ![_, _] = fsModelForm (chartFun (idx x) x) ![a, b]
  rw [← hu, ← h, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- ★ **The unitary action is an isometry of the Fubini–Study metric** `g = ω_FS (J ·, ·)`:
symplectic and holomorphic, hence Killing. -/
theorem fsMetric_smul_mfderiv (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (x : ℙ ℂ (Ambient n))
    (a b : TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ)) x) :
    (fsForm_isAlmostKahler n).metric (U • x)
        (mfderiv (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ (Fin n → ℂ))
          (fun p : ℙ ℂ (Ambient n) => U • p) x a)
        (mfderiv (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ (Fin n → ℂ))
          (fun p : ℙ ℂ (Ambient n) => U • p) x b)
      = (fsForm_isAlmostKahler n).metric x a b :=
  (fsForm_isAlmostKahler n).metric_mfderiv_eq (isHolomorphicMap_smul U) (fsForm_smul_mfderiv U)
    x a b

/-! ### The Hamiltonian flow of `−2⟨H⟩` is holomorphic and Killing -/

theorem hamiltonianFlow_schrodingerHamiltonian_eq {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (t : ℝ) :
    (fsForm_isSymplectic n).hamiltonianFlow (contMDiff_schrodingerHamiltonian H) t
      = fun p : ℙ ℂ (Ambient n) => CSD.LF4.schrodingerUnitary hH t • p :=
  funext (hamiltonianFlow_schrodingerHamiltonian hH t)

/-- ★★ **The Hamiltonian flow of `−2⟨H⟩` on `ℂℙⁿ` is holomorphic at every time**: its derivative
commutes with `J = i·`. -/
theorem isHolomorphicMap_hamiltonianFlow_schrodinger {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (t : ℝ) :
    IsHolomorphicMap fsJ
      ((fsForm_isSymplectic n).hamiltonianFlow (contMDiff_schrodingerHamiltonian H) t) := by
  rw [hamiltonianFlow_schrodingerHamiltonian_eq hH t]
  exact isHolomorphicMap_smul _

/-- ★★ **The Hamiltonian flow of `−2⟨H⟩` on `ℂℙⁿ` is Killing at every time**: it preserves the
Fubini–Study metric. -/
theorem fsMetric_hamiltonianFlow_schrodinger {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (t : ℝ) (x : ℙ ℂ (Ambient n))
    (a b : TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ)) x) :
    (fsForm_isAlmostKahler n).metric
        ((fsForm_isSymplectic n).hamiltonianFlow (contMDiff_schrodingerHamiltonian H) t x)
        (mfderiv (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ (Fin n → ℂ))
          ((fsForm_isSymplectic n).hamiltonianFlow (contMDiff_schrodingerHamiltonian H) t) x a)
        (mfderiv (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ (Fin n → ℂ))
          ((fsForm_isSymplectic n).hamiltonianFlow (contMDiff_schrodingerHamiltonian H) t) x b)
      = (fsForm_isAlmostKahler n).metric x a b := by
  rw [hamiltonianFlow_schrodingerHamiltonian_eq hH t]
  exact fsMetric_smul_mfderiv _ x a b

/-! ### The Schrödinger field is a holomorphic vector field -/

/-- The Schrödinger field read in the affine chart at `x₀` is `schrodingerChartField` in that
chart, at every point of the chart: both are the local Hamiltonian vector of `−2⟨H⟩` for the
model form, which is unique. -/
theorem chartField_schrodingerField {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (x₀ : ℙ ℂ (Ambient n)) (w : Fin n → ℂ) :
    chartField (schrodingerField H) x₀ w = schrodingerChartField H (idx x₀) w := by
  have hw : w ∈ (chartAt (Fin n → ℂ) x₀).target := Set.mem_univ w
  have hnd := (fsForm_isSymplectic n).nondegenerate
  rw [schrodingerField_eq_hamiltonianVectorField hH, IsSymplectic.hamiltonianVectorField,
    chartField_hamiltonianVectorField (fsForm (n := n)) (schrodingerHamiltonian H) hnd
      (contMDiff_schrodingerHamiltonian H) x₀ hw,
    localHamiltonianVector, inverse_curryLeft_apply _ (localRep_nondegenerate _ hnd x₀ hw)]
  symm
  apply eq_flatVec
  intro u
  have h1 : localRep (fun x => fsForm (n := n) x) x₀ w = fsModelForm w := localRep_fsSection' x₀ w
  have h2 : (schrodingerHamiltonian H ∘ (chartAt (Fin n → ℂ) x₀).symm)
      = schrodingerChartHam H (idx x₀) :=
    funext fun w => schrodingerHamiltonian_chartInv H (idx x₀) w
  rw [h1, h2, (hasFDerivAt_schrodingerChartHam H (idx x₀) w).fderiv]
  exact fsModelForm_schrodingerChartField hH (idx x₀) w u

/-- The entry `k` of `H (insertOne i w)` is a `ℂ`-affine function of `w`. -/
theorem differentiableAt_mulVec_insertOne (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i k : Fin (n + 1)) (w : Fin n → ℂ) :
    DifferentiableAt ℂ (fun w : Fin n → ℂ => (H *ᵥ (insertOne i w).ofLp) k) w := by
  have h : (fun w : Fin n → ℂ => (H *ᵥ (insertOne i w).ofLp) k)
      = fun w => ∑ l, H k l * i.insertNth 1 w l := by
    funext w
    rfl
  rw [h]
  refine DifferentiableAt.fun_sum fun l _ => (differentiableAt_const _).mul ?_
  rcases Fin.eq_self_or_eq_succAbove i l with rfl | ⟨j, rfl⟩
  · simp only [Fin.insertNth_apply_same]
    exact differentiableAt_const _
  · simp only [Fin.insertNth_apply_succAbove]
    exact differentiableAt_apply j w

/-- The Schrödinger chart field is `ℂ`-differentiable: a quadratic polynomial in `w` with complex
coefficients. -/
theorem differentiableAt_schrodingerChartField (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) (w : Fin n → ℂ) :
    DifferentiableAt ℂ (schrodingerChartField H i) w := by
  refine differentiableAt_pi.2 fun j => ?_
  simp only [schrodingerChartField]
  exact (differentiableAt_const _).mul
    ((differentiableAt_mulVec_insertOne H i _ w).sub
      ((differentiableAt_mulVec_insertOne H i i w).mul (differentiableAt_apply j w)))

/-- ★★ **The Schrödinger field is a holomorphic vector field of the Kähler manifold `ℂℙⁿ`**: in
every affine chart its derivative commutes with `J = i·`. With
`schrodingerField_eq_hamiltonianVectorField`, the Hamiltonian vector field of `−2⟨H⟩` is
holomorphic. -/
theorem isHolomorphicVectorField_schrodingerField {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) : IsHolomorphicVectorField modelJ (schrodingerField H) := by
  intro x₀ w _
  have hc : chartField (schrodingerField H) x₀ = schrodingerChartField H (idx x₀) :=
    funext (chartField_schrodingerField hH x₀)
  rw [hc]
  have hd := differentiableAt_schrodingerChartField H (idx x₀) w
  have hR : HasFDerivAt (schrodingerChartField H (idx x₀))
      ((fderiv ℂ (schrodingerChartField H (idx x₀)) w).restrictScalars ℝ) w :=
    hd.hasFDerivAt.restrictScalars ℝ
  refine ⟨hR.differentiableAt, fun v => ?_⟩
  rw [hR.fderiv, modelJ_apply, modelJ_apply]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul]

end Projectivization

end
