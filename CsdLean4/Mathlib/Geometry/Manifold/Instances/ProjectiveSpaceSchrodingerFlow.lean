/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceMomentMap
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudySymplectic
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceHamiltonianFlow
public import CsdLean4.Mathlib.Analysis.Matrix.SchrodingerUnitary
public import Mathlib.Analysis.Matrix.Hermitian

/-!
# The Schrödinger flow on `ℂℙⁿ` is Hamiltonian, with Hamiltonian `-2 ⟨H⟩`

**TERM-SCOPE(Kahler)** **TERM-SCOPE(Hamiltonian)** **TERM-SCOPE(MomentMap)** — this module uses
the *restricted* senses of these words; `specs/TERMS.md` records what is backed and what is not.

**Category:** 1-Mathlib (1-Mathlib-staging in its mathematics; it consumes the corpus's).
`Matrix.schrodingerUnitary` (the unitary `exp(-itH)`) and its derivative
`Matrix.schrodingerUnitary_hasDerivAt` as the flow whose generator it identifies.

Brick **G13** of `specs/generator-layer-scoping.md` (with the G2, G3, G4, G16 and G19 corollaries): the `U(n+1)` moment map. For a Hermitian
`H`, the unitary flow `p ↦ exp(-itH) • p` on `ℂℙⁿ` — the corpus's projected Schrödinger flow — is
Hamiltonian for the Fubini–Study form, and its Hamiltonian is `-2 ⟨H⟩`, the expectation value
`⟪z, Hz⟫ / ‖z‖²` up to the form's convention. Brick G6 (the torus) is the diagonal case.

* `expectation H p = ⟪z, Hz⟫.re / ‖z‖²` — the expectation value on rays (`expectation_mk`,
  `continuous_expectation`); `schrodingerHamiltonian H = -2 • expectation H`;
* `insertZeroCLM i` — the tangent lift of the affine chart (`0` in slot `i`), an `ℝ`-linear map;
  `insertOne i w = insertOne i 0 + insertZeroCLM i w`, so `hasFDerivAt_insertOne`; and the lift
  preserves the inner products the model form is written in (`inner_insertZeroCLM_insertZeroCLM`,
  `inner_insertZeroCLM_insertOne`, `norm_sq_insertOne_toLpCLM`);
* `schrodingerChartField H i w` — the velocity in chart `i`, `-i ((Hv)_{sⱼ} - (Hv)_i wⱼ)` for
  `v = insertOne i w`; ★ `hasDerivAt_chartFun_schrodingerUnitary` — **it is the velocity of the
  flow**: the `t`-derivative at `0` of `t ↦ chartFun i (exp(-itH) • chartInv i w)`;
* `schrodingerChartHam`, `hasFDerivAt_schrodingerChartHam` — the chart Hamiltonian
  `-2 ⟪v, Hv⟫.re / ‖v‖²` and its derivative, through `HasFDerivAt.inner` along the affine lift;
* ★★ `fsModelForm_schrodingerChartField` — **the chart identity `ω_w (X_w, u) = dH_w u`**, proved
  in the ambient inner product: the lifted velocity is `-i (Hv - (Hv)_i v)`, the `(Hv)_i` terms
  cancel, and what remains is the symmetry of `H` and `Im (i z) = Re z`;
* ★★★ `schrodingerField_isHamiltonianVectorField` — **`IsHamiltonianVectorField fsForm
  (schrodingerField H) (schrodingerHamiltonian H)`: the Schrödinger flow on `ℂℙⁿ` is Hamiltonian
  for the Fubini–Study form, with `-2 ⟨H⟩` as its Hamiltonian**;
* `schrodingerChartField_neg_diagonal`, `schrodingerHamiltonian_neg_diagonal` — for
  `H = -diag θ` the field and the Hamiltonian are G6's `torusChartField` and `torusHamiltonian`:
  the torus is the diagonal case;
* `torusField_eq_hamiltonianVectorField`, `schrodingerField_eq_hamiltonianVectorField` — both
  fields are **the** Hamiltonian vector fields `(ω♭)⁻¹ dH` of their Hamiltonians for the symplectic
  form `fsForm` (G2's existence-and-uniqueness construction, `IsSymplectic.hamiltonianVectorField`);
* `contDiff_schrodingerChartHam`, ★ `contMDiff_schrodingerHamiltonian`, ★ `contMDiff_torusHamiltonian`
  (both Hamiltonians are `C^m` on `ℂℙⁿ` for every order `m`, so `C^∞` and real-analytic at once —
  one statement each since 2026-09-16), and ★★ `contMDiff_schrodingerField`, ★★
  `contMDiff_torusField` — **both fields are `C^∞` vector fields**, `C^∞` sections of the tangent
  bundle, by G2's identification and G3's smoothness theorem;
* `exists_isMIntegralCurveAt_schrodingerField`, `isMIntegralCurve_schrodingerField_eq`, ★★
  `expectation_eq_of_isMIntegralCurve_schrodingerField` (**`⟨H⟩` is conserved** along every
  integral curve of the field), ★★★ `isMIntegralCurve_schrodingerUnitary_smul` — **the
  Schrödinger flow `t ↦ exp(-itH) • p` is the integral curve of its field**, for every `p` — and
  ★★ `expectation_schrodingerUnitary_smul` (`⟨H⟩` is conserved by the flow), all G4;
* **G16 (2026-09-10).** Given ★★★ `isMIntegralCurve_torusUnitary_smul` — **the torus orbit
  `t ↦ diag(e^{itθ}) • p` is the integral curve of `torusField θ`** — which lives with the field in
  `ProjectiveSpaceMomentMap.lean` since 2026-09-16 (it uses only the moment-map module's own
  `hasDerivAt_chartFun_torusUnitary` and group law `torusUnitary_add_smul`):
  `isMIntegralCurve_torusField_eq`, ★★ `eq_torusUnitary_smul_of_isMIntegralCurve` (every integral
  curve through `p` at `0` IS the orbit); ★★ `torusHamiltonian_eq_of_isMIntegralCurve_torusField`
  and ★★ `torusHamiltonian_torusUnitary_smul` (**`2 ∑ θₖ μₖ` is conserved** along the curves and by
  the flow);
* **G19 (2026-09-10).** ★★ `contMDiff_omega_schrodingerField`, ★★ `contMDiff_omega_torusField` —
  **both fields are analytic
  vector fields**, `C^ω` sections of the tangent bundle: the Hamiltonian vector fields of `C^ω`
  energies for the `C^ω` form `fsFormAnalytic` (G12), by G19's `contMDiff_omega_hamiltonianVectorField`;
* **Q29(e) (2026-09-12).** ★★ `hamiltonianFlow_schrodingerHamiltonian`, ★★
  `hamiltonianFlow_torusHamiltonian` — **the Schrödinger flow and the torus flow ARE the Hamiltonian
  flows** `IsSymplectic.hamiltonianFlow` (`HamiltonianFlowVolume.lean`) of `-2⟨H⟩` and of
  `2 ∑ θₖ μₖ`: the manifold flow of the Hamiltonian vector field is `p ↦ exp(-itH) • p`, by
  uniqueness of integral curves (`integralFlow_eq_of_isMIntegralCurve`); hence ★★
  `fsVolume_map_schrodingerUnitary_smul`, `fsVolumeNormalized_map_schrodingerUnitary_smul` —
  **Liouville for the Schrödinger flow from the Hamiltonian**, a corollary of the manifold-level
  theorem `fsVolume_map_hamiltonianFlow` (Q29(d′)), not of unitary invariance.

## Honest scope

⚠️ **The sign and the factor are conventions.** `fsChartForm` carries the `-4` of its potential,
which makes the generator of the torus `2 · momentMap` (G6); the corpus's Schrödinger flow is
`exp(-itH)`, so its Hamiltonian is `-2 ⟨H⟩`. Nothing here rescales either; the statement shows
both.

⚠️ **The flow is consumed, not built.** `Matrix.schrodingerUnitary` and its derivative come from
`Analysis/Matrix/SchrodingerUnitary.lean`, under the `L2Operator` matrix norm (the one under which
`hasDerivAt_exp_smul_const` synthesises); this module opens that scope and adds nothing to it.

⚠️ **Two routes to Liouville, both in the corpus.** `fsVolume_map_torusUnitary_smul` (G10) and
`fsVolume_map_smul` (W1 on the sectors) are unitary invariance; `fsVolume_map_schrodingerUnitary_smul`
here is the manifold-level flow theorem (Q29, formerly G5) applied through the identification of the
flows. They prove the same equation by independent arguments; the second is the one that generalises
to a non-unitary Hamiltonian flow.

⚠️ **Posits untouched.** Posit 1 asserts that the dynamics generates the pointer torus; this
module says which Hamiltonian a *given* unitary flow has, for every Hermitian `H`, and does not
touch what generates it.

References: `specs/generator-layer-scoping.md` (G13, G6); `Instances/ProjectiveSpaceMomentMap.lean`
(`torusChartField`, `torusHamiltonian`, `torusField_isHamiltonianVectorField`);
`Geometry/Manifold/HamiltonianVectorField.lean` (G1); `Instances/ProjectiveSpaceFubiniStudyMass.lean`
(`fsModelForm_apply`, `toLpCLM_apply`); `Instances/ProjectiveSpaceUnitaryAction.lean`
(`chartFun_smul_chartInv`); `Analysis/Matrix/SchrodingerUnitary.lean` (`schrodingerUnitary`,
`expNegITH_unitary_group`, `schrodingerUnitary_hasDerivAt`);
`specs/TERMS.md` (Hamiltonian, moment map); `specs/POSITS.md` (Posit 1); `specs/future-work.md`.
-/

@[expose] public section

open scoped Manifold ContDiff LinearAlgebra.Projectivization Matrix Matrix.Norms.L2Operator
open Kahler DifferentialForm

noncomputable section

namespace Projectivization

variable {n : ℕ}

/-! ### The expectation value, on rays -/

/-- `⟨H⟩` at a ray: `⟪z, Hz⟫.re / ‖z‖²`, on any representative. -/
def expectation (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (p : ℙ ℂ (Ambient n)) : ℝ :=
  (inner ℂ p.rep (Matrix.toEuclideanLin H p.rep)).re / ‖p.rep‖ ^ 2

theorem expectation_ratio_smul (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (c : ℂ) (hc : c ≠ 0)
    (v : Ambient n) :
    (inner ℂ (c • v) (Matrix.toEuclideanLin H (c • v))).re / ‖c • v‖ ^ 2
      = (inner ℂ v (Matrix.toEuclideanLin H v)).re / ‖v‖ ^ 2 := by
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', norm_smul,
    mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.2 hc))

/-- The expectation value at a representative. -/
theorem expectation_mk (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ψ : Ambient n) (hψ : ψ ≠ 0) :
    expectation H (mk ℂ ψ hψ) = (inner ℂ ψ (Matrix.toEuclideanLin H ψ)).re / ‖ψ‖ ^ 2 := by
  obtain ⟨a, ha⟩ := (mk_eq_mk_iff ℂ (mk ℂ ψ hψ).rep ψ (rep_nonzero _) hψ).mp (mk_rep _)
  unfold expectation
  rw [← ha]
  simp only [Units.smul_def]
  exact expectation_ratio_smul H (↑a) (Units.ne_zero a) ψ

theorem continuous_expectation (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Continuous (expectation (n := n) H) := by
  rw [continuous_iff_continuous_comp_mk']
  have hcomp : (expectation H ∘ (mk' ℂ : _ → ℙ ℂ (Ambient n)))
      = fun v : {v : Ambient n // v ≠ 0} =>
          (inner ℂ (v : Ambient n) (Matrix.toEuclideanLin H v)).re / ‖(v : Ambient n)‖ ^ 2 := by
    funext v
    exact expectation_mk H v v.2
  rw [hcomp]
  have hT : Continuous (Matrix.toEuclideanLin H) := LinearMap.continuous_of_finiteDimensional _
  have hnum : Continuous fun v : {v : Ambient n // v ≠ 0} =>
      (inner ℂ (v : Ambient n) (Matrix.toEuclideanLin H v)).re :=
    Complex.continuous_re.comp
      ((continuous_inner (𝕜 := ℂ)).comp
        (continuous_subtype_val.prodMk (hT.comp continuous_subtype_val)))
  have hden : Continuous fun v : {v : Ambient n // v ≠ 0} => ‖(v : Ambient n)‖ ^ 2 :=
    continuous_subtype_val.norm.pow 2
  exact hnum.div hden fun v => pow_ne_zero _ (norm_ne_zero_iff.mpr v.2)

/-- The Hamiltonian of the Schrödinger flow `exp(-itH)`: `-2 ⟨H⟩`. -/
def schrodingerHamiltonian (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (p : ℙ ℂ (Ambient n)) : ℝ :=
  -2 * expectation H p

theorem continuous_schrodingerHamiltonian (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Continuous (schrodingerHamiltonian (n := n) H) :=
  continuous_const.mul (continuous_expectation H)

/-! ### The tangent lift of the affine chart -/

/-- Insert `0` in slot `i`, as an `ℝ`-linear map: the lift of chart tangent vectors. -/
def insertZeroCLM (i : Fin (n + 1)) : (Fin n → ℂ) →L[ℝ] Ambient n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => WithLp.toLp 2 (i.insertNth 0 u)
      map_add' := fun u u' => by
        ext k
        rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨j, rfl⟩ <;> simp
      map_smul' := fun c u => by
        ext k
        rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨j, rfl⟩ <;> simp }

theorem insertZeroCLM_apply (i : Fin (n + 1)) (u : Fin n → ℂ) :
    insertZeroCLM i u = WithLp.toLp 2 (i.insertNth 0 u) := rfl

@[simp] theorem insertZeroCLM_apply_same (i : Fin (n + 1)) (u : Fin n → ℂ) :
    insertZeroCLM i u i = 0 := by
  simp [insertZeroCLM_apply]

@[simp] theorem insertZeroCLM_apply_succAbove (i : Fin (n + 1)) (u : Fin n → ℂ) (j : Fin n) :
    insertZeroCLM i u (i.succAbove j) = u j := by
  simp [insertZeroCLM_apply]

theorem insertOne_eq_add (i : Fin (n + 1)) (w : Fin n → ℂ) :
    insertOne i w = insertOne i 0 + insertZeroCLM i w := by
  ext k
  rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨j, rfl⟩ <;> simp [insertOne]

theorem hasFDerivAt_insertOne (i : Fin (n + 1)) (w : Fin n → ℂ) :
    HasFDerivAt (insertOne i) (insertZeroCLM i) w := by
  have h : insertOne (n := n) i = fun w => insertOne i 0 + insertZeroCLM i w :=
    funext (insertOne_eq_add i)
  rw [h]
  exact (insertZeroCLM i).hasFDerivAt.const_add _

theorem inner_insertZeroCLM_insertZeroCLM (i : Fin (n + 1)) (u u' : Fin n → ℂ) :
    inner ℂ (insertZeroCLM i u) (insertZeroCLM i u') = inner ℂ (toLpCLM u) (toLpCLM u') := by
  simp only [PiLp.inner_apply]
  rw [Fin.sum_univ_succAbove _ i]
  simp

theorem inner_insertZeroCLM_insertOne (i : Fin (n + 1)) (u w : Fin n → ℂ) :
    inner ℂ (insertZeroCLM i u) (insertOne i w) = inner ℂ (toLpCLM u) (toLpCLM w) := by
  simp only [PiLp.inner_apply]
  rw [Fin.sum_univ_succAbove _ i]
  simp

theorem inner_insertOne_insertZeroCLM (i : Fin (n + 1)) (w u : Fin n → ℂ) :
    inner ℂ (insertOne i w) (insertZeroCLM i u) = inner ℂ (toLpCLM w) (toLpCLM u) := by
  simp only [PiLp.inner_apply]
  rw [Fin.sum_univ_succAbove _ i]
  simp

theorem norm_sq_insertOne_toLpCLM (i : Fin (n + 1)) (w : Fin n → ℂ) :
    ‖insertOne i w‖ ^ 2 = 1 + ‖toLpCLM w‖ ^ 2 := by
  rw [norm_sq_insertOne, EuclideanSpace.norm_sq_eq]
  simp

/-! ### The velocity and the Hamiltonian in the chart -/

/-- The velocity of `t ↦ exp(-itH) • p` in chart `i`: `-i ((Hv)_{sⱼ} - (Hv)_i wⱼ)`,
`v = insertOne i w`. -/
def schrodingerChartField (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1))
    (w : Fin n → ℂ) : Fin n → ℂ :=
  fun j => -Complex.I * ((H *ᵥ (insertOne i w).ofLp) (i.succAbove j)
    - (H *ᵥ (insertOne i w).ofLp) i * w j)

/-- The lift of the chart velocity to the ambient space: `-i (Hv - (Hv)_i v)`. -/
theorem insertZeroCLM_schrodingerChartField (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) (w : Fin n → ℂ) :
    insertZeroCLM i (schrodingerChartField H i w)
      = (-Complex.I) • (Matrix.toEuclideanLin H (insertOne i w)
          - (H *ᵥ (insertOne i w).ofLp) i • insertOne i w) := by
  ext k
  rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨j, rfl⟩
  · simp
  · simp [schrodingerChartField]

/-- The chart Hamiltonian `-2 ⟪v, Hv⟫.re / ‖v‖²`. -/
def schrodingerChartHam (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1))
    (w : Fin n → ℂ) : ℝ :=
  -2 * ((inner ℂ (insertOne i w) (Matrix.toEuclideanLin H (insertOne i w))).re
    * (‖insertOne i w‖ ^ 2)⁻¹)

theorem schrodingerHamiltonian_chartInv (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) (w : Fin n → ℂ) :
    schrodingerHamiltonian H (chartInv i w) = schrodingerChartHam H i w := by
  unfold schrodingerHamiltonian schrodingerChartHam chartInv
  rw [expectation_mk, div_eq_mul_inv]

theorem norm_sq_insertOne_pos (i : Fin (n + 1)) (w : Fin n → ℂ) : 0 < ‖insertOne i w‖ ^ 2 :=
  pow_pos (norm_pos_iff.2 (insertOne_ne_zero i w)) 2

/-- The derivative of the chart Hamiltonian, by the product and inverse rules from
`HasFDerivAt.inner` along the affine lift. -/
def schrodingerChartHamDeriv (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1))
    (w : Fin n → ℂ) : (Fin n → ℂ) →L[ℝ] ℝ :=
  (-2 : ℝ) • ((inner ℂ (insertOne i w) (Matrix.toEuclideanLin H (insertOne i w))).re
      • ((ContinuousLinearMap.toSpanSingleton ℝ (-((‖insertOne i w‖ ^ 2) ^ 2)⁻¹)).comp
          (Complex.reCLM.comp ((fderivInnerCLM ℂ (insertOne i w, insertOne i w)).comp
            ((insertZeroCLM i).prod (insertZeroCLM i)))))
    + (‖insertOne i w‖ ^ 2)⁻¹
      • (Complex.reCLM.comp ((fderivInnerCLM ℂ
          (insertOne i w, Matrix.toEuclideanCLM (𝕜 := ℂ) H (insertOne i w))).comp
            ((insertZeroCLM i).prod
              (((Matrix.toEuclideanCLM (𝕜 := ℂ) H).restrictScalars ℝ).comp (insertZeroCLM i))))))

theorem hasFDerivAt_schrodingerChartHam (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) (w : Fin n → ℂ) :
    HasFDerivAt (schrodingerChartHam H i) (schrodingerChartHamDeriv H i w) w := by
  unfold schrodingerChartHam schrodingerChartHamDeriv
  have hv : HasFDerivAt (insertOne i) (insertZeroCLM i) w := hasFDerivAt_insertOne i w
  have hTv : HasFDerivAt (fun w => Matrix.toEuclideanCLM (𝕜 := ℂ) H (insertOne i w))
      (((Matrix.toEuclideanCLM (𝕜 := ℂ) H).restrictScalars ℝ).comp (insertZeroCLM i)) w :=
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) H).restrictScalars ℝ).hasFDerivAt.comp w hv
  have hN : HasFDerivAt
      (fun w => (inner ℂ (insertOne i w) (Matrix.toEuclideanCLM (𝕜 := ℂ) H (insertOne i w))).re)
      (Complex.reCLM.comp ((fderivInnerCLM ℂ
          (insertOne i w, Matrix.toEuclideanCLM (𝕜 := ℂ) H (insertOne i w))).comp
            ((insertZeroCLM i).prod
              (((Matrix.toEuclideanCLM (𝕜 := ℂ) H).restrictScalars ℝ).comp (insertZeroCLM i))))) w :=
    Complex.reCLM.hasFDerivAt.comp w (hv.inner (𝕜 := ℂ) hTv)
  have hD : HasFDerivAt (fun w => ‖insertOne i w‖ ^ 2)
      (Complex.reCLM.comp ((fderivInnerCLM ℂ (insertOne i w, insertOne i w)).comp
        ((insertZeroCLM i).prod (insertZeroCLM i)))) w := by
    refine (Complex.reCLM.hasFDerivAt.comp w (hv.inner (𝕜 := ℂ) hv)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => ?_)
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) (insertOne i y)).symm
  have hinv : HasFDerivAt (fun w => (‖insertOne i w‖ ^ 2)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-((‖insertOne i w‖ ^ 2) ^ 2)⁻¹)).comp
        (Complex.reCLM.comp ((fderivInnerCLM ℂ (insertOne i w, insertOne i w)).comp
          ((insertZeroCLM i).prod (insertZeroCLM i))))) w :=
    (hasFDerivAt_inv (norm_sq_insertOne_pos i w).ne').comp w hD
  exact (hN.mul hinv).const_mul (-2)

theorem schrodingerChartHamDeriv_apply (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) (w u : Fin n → ℂ) :
    schrodingerChartHamDeriv H i w u
      = -2 * ((inner ℂ (insertOne i w) (Matrix.toEuclideanLin H (insertOne i w))).re
            * (-((‖insertOne i w‖ ^ 2) ^ 2)⁻¹
              * (inner ℂ (insertOne i w) (insertZeroCLM i u)
                  + inner ℂ (insertZeroCLM i u) (insertOne i w)).re)
          + (‖insertOne i w‖ ^ 2)⁻¹
            * (inner ℂ (insertOne i w) (Matrix.toEuclideanLin H (insertZeroCLM i u))
                + inner ℂ (insertZeroCLM i u) (Matrix.toEuclideanLin H (insertOne i w))).re) := by
  have hc : ∀ z, Matrix.toEuclideanCLM (𝕜 := ℂ) H z = Matrix.toEuclideanLin H z := fun _ => rfl
  simp only [schrodingerChartHamDeriv, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.toSpanSingleton_apply,
    fderivInnerCLM_apply, Complex.reCLM_apply, ContinuousLinearMap.coe_restrictScalars',
    smul_eq_mul, hc]
  ring

/-! ### The chart identity `ι_X ω = dH`, in the ambient inner product -/

/-- ★★ **The chart identity**: the Fubini–Study model form pairs the Schrödinger velocity with `u`
exactly as the derivative of the chart Hamiltonian does. Lifted to the ambient space, the velocity
is `-i (Hv - (Hv)_i v)`; the `(Hv)_i` terms cancel, and what remains is `Im (i z) = Re z` together
with the symmetry of `H`. -/
theorem fsModelForm_schrodingerChartField {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (i : Fin (n + 1)) (w u : Fin n → ℂ) :
    fsModelForm w ![schrodingerChartField H i w, u] = schrodingerChartHamDeriv H i w u := by
  rw [fsModelForm_apply, schrodingerChartHamDeriv_apply, ← inner_insertZeroCLM_insertZeroCLM i,
    ← inner_insertZeroCLM_insertOne i, ← inner_insertOne_insertZeroCLM i, ← norm_sq_insertOne_toLpCLM i,
    insertZeroCLM_schrodingerChartField]
  have hT : (Matrix.toEuclideanLin H).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.2 hH
  set v := insertOne i w with hv
  set y := insertZeroCLM i u with hy
  set c : ℂ := (H *ᵥ v.ofLp) i with hc
  set T := Matrix.toEuclideanLin H with hTdef
  have h1 : inner ℂ v (T y) = inner ℂ (T v) y := (hT v y).symm
  have h2 : inner ℂ y (T v) = (starRingEnd ℂ) (inner ℂ (T v) y) := (inner_conj_symm _ _).symm
  have h3 : inner ℂ y v = (starRingEnd ℂ) (inner ℂ v y) := (inner_conj_symm _ _).symm
  have h4 : (inner ℂ (T v) v).im = 0 := Complex.conj_eq_iff_im.1 (hT.conj_inner_sym v v)
  have h5 : (inner ℂ v (T v)).re = (inner ℂ (T v) v).re := by
    rw [← inner_conj_symm (T v) v, Complex.conj_re]
  have he1 : (inner ℂ v v).re = ‖v‖ ^ 2 := by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) v
  have he2 : (inner ℂ v v).im = 0 := by simpa using inner_self_im (𝕜 := ℂ) v
  have hne : ‖v‖ ^ 2 ≠ 0 := (norm_sq_insertOne_pos i w).ne'
  simp only [inner_smul_left, inner_sub_left, Complex.conj_neg_I, h1, h2, h3, h5]
  set a := inner ℂ (T v) y with ha
  set b := inner ℂ v y with hb
  set d := inner ℂ (T v) v with hd
  set e := inner ℂ v v with he
  simp only [Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, h4, he1, he2]
  field_simp
  ring

/-! ### The manifold statement -/

/-- The velocity field of the Schrödinger flow `p ↦ exp(-itH) • p` on `ℂℙⁿ`, read in the chart at
each point. -/
def schrodingerField (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (x : ℙ ℂ (Ambient n)) :
    TangentSpace (modelWithCornersSelf ℝ (Fin n → ℂ)) x :=
  schrodingerChartField H (idx x) (chartFun (idx x) x)

theorem hasMFDerivAt_schrodingerHamiltonian (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (x : ℙ ℂ (Ambient n)) :
    HasMFDerivAt (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ ℝ)
      (schrodingerHamiltonian H) x (schrodingerChartHamDeriv H (idx x) (chartFun (idx x) x)) := by
  refine ⟨(continuous_schrodingerHamiltonian H).continuousAt, ?_⟩
  have hw : writtenInExtChartAt (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ ℝ) x
      (schrodingerHamiltonian H) = schrodingerChartHam H (idx x) := by
    funext w
    simp only [writtenInExtChartAt, Function.comp, extChartAt_model_space_eq_id,
      PartialEquiv.refl_coe, id, extChartAt_coe_symm, modelWithCornersSelf_coe_symm]
    exact schrodingerHamiltonian_chartInv H (idx x) w
  rw [hw]
  exact (hasFDerivAt_schrodingerChartHam H (idx x) (chartFun (idx x) x)).hasFDerivWithinAt

/-- ★★★ **The Schrödinger flow on `ℂℙⁿ` is Hamiltonian for the Fubini–Study form, with `-2 ⟨H⟩`
as its Hamiltonian**: `ι_X ω_FS = dH` on the manifold, for every Hermitian `H`. -/
theorem schrodingerField_isHamiltonianVectorField {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) :
    IsHamiltonianVectorField (fun x => fsForm x) (schrodingerField H)
      (schrodingerHamiltonian H) := by
  intro x v
  rw [(hasMFDerivAt_schrodingerHamiltonian H x).mfderiv]
  exact fsModelForm_schrodingerChartField hH (idx x) (chartFun (idx x) x) v

/-! ### The field is the velocity of the flow -/

/-- The entry `k` of `M *ᵥ v`, as an `ℝ`-linear functional of the matrix. -/
def mulVecEntryCLM (v : Fin (n + 1) → ℂ) (k : Fin (n + 1)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ →L[ℝ] ℂ :=
  (LinearMap.toContinuousLinearMap
    { toFun := fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => (M *ᵥ v) k
      map_add' := fun M M' => by simp [Matrix.add_mulVec]
      map_smul' := fun c M => by simp [Matrix.smul_mulVec] } :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ →L[ℂ] ℂ).restrictScalars ℝ

theorem mulVecEntryCLM_apply (v : Fin (n + 1) → ℂ) (k : Fin (n + 1))
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : mulVecEntryCLM v k M = (M *ᵥ v) k := rfl

theorem schrodingerUnitary_zero_val {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) :
    (Matrix.schrodingerUnitary hH 0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = 1 :=
  congrArg Subtype.val (Matrix.expNegITH_unitary_group hH).2

theorem schrodingerUnitary_zero_val' {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) : Matrix.schrodingerUnitary hH 0 = 1 :=
  (Matrix.expNegITH_unitary_group hH).2

/-- ★ **The field is the velocity of the flow**: at every chart point, `schrodingerChartField` is
the `t`-derivative at `0` of `t ↦ exp(-itH) • p`, read in the chart. -/
theorem hasDerivAt_chartFun_schrodingerUnitary {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (i : Fin (n + 1)) (w : Fin n → ℂ) :
    HasDerivAt (fun t : ℝ => chartFun i (Matrix.schrodingerUnitary hH t • chartInv i w))
      (schrodingerChartField H i w) 0 := by
  simp_rw [chartFun_smul_chartInv]
  refine hasDerivAt_pi.2 fun j => ?_
  have hentry : ∀ k, HasDerivAt
      (fun t : ℝ => ((Matrix.schrodingerUnitary hH t : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        *ᵥ (insertOne i w).ofLp) k)
      (-Complex.I * (H *ᵥ (insertOne i w).ofLp) k) 0 := by
    intro k
    have h := (mulVecEntryCLM (insertOne i w).ofLp k).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (Matrix.schrodingerUnitary_hasDerivAt H hH 0)
    refine h.congr_deriv ?_
    rw [mulVecEntryCLM_apply, schrodingerUnitary_zero_val hH, one_mul, Matrix.smul_mulVec]
    simp
  have hnum := hentry (i.succAbove j)
  have hden := hentry i
  have hden0 : ((Matrix.schrodingerUnitary hH 0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      *ᵥ (insertOne i w).ofLp) i = 1 := by
    rw [schrodingerUnitary_zero_val hH, Matrix.one_mulVec]
    exact insertOne_apply_same i w
  have hnum0 : ((Matrix.schrodingerUnitary hH 0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      *ᵥ (insertOne i w).ofLp) (i.succAbove j) = w j := by
    rw [schrodingerUnitary_zero_val hH, Matrix.one_mulVec]
    exact insertOne_apply_succAbove i w j
  show HasDerivAt (fun t : ℝ =>
    ((Matrix.schrodingerUnitary hH t : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        *ᵥ (insertOne i w).ofLp) (i.succAbove j)
      / ((Matrix.schrodingerUnitary hH t : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        *ᵥ (insertOne i w).ofLp) i) (schrodingerChartField H i w j) 0
  refine (hnum.div hden (by rw [hden0]; exact one_ne_zero)).congr_deriv ?_
  rw [hden0, hnum0]
  simp only [schrodingerChartField]
  ring

/-! ### The torus is the diagonal case (G6) -/

theorem schrodingerChartField_neg_diagonal (θ : Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (w : Fin n → ℂ) :
    schrodingerChartField (-(Matrix.diagonal fun k => (θ k : ℂ))) i w = torusChartField i θ w := by
  funext j
  simp only [schrodingerChartField, torusChartField, Matrix.neg_mulVec, Matrix.mulVec_diagonal,
    Pi.neg_apply, insertOne_apply_same, insertOne_apply_succAbove, Complex.ofReal_sub]
  ring

theorem schrodingerHamiltonian_neg_diagonal (θ : Fin (n + 1) → ℝ) :
    schrodingerHamiltonian (-(Matrix.diagonal fun k => (θ k : ℂ)))
      = torusHamiltonian (n := n) θ := by
  funext p
  unfold schrodingerHamiltonian expectation torusHamiltonian momentMap
  have hrep : ∀ k, (Matrix.toEuclideanLin (-(Matrix.diagonal fun k => (θ k : ℂ))) p.rep) k
      = -((θ k : ℂ) * p.rep k) := fun k => by
    show ((-(Matrix.diagonal fun k => (θ k : ℂ))) *ᵥ p.rep.ofLp) k = _
    rw [Matrix.neg_mulVec, Pi.neg_apply, Matrix.mulVec_diagonal]
  have hk : ∀ k, (inner ℂ (p.rep k) (-((θ k : ℂ) * p.rep k))).re = -(θ k * ‖p.rep k‖ ^ 2) := by
    intro k
    rw [RCLike.inner_apply, neg_mul, mul_assoc, mul_comm (p.rep k), Complex.conj_mul',
      Complex.neg_re, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [PiLp.inner_apply, Complex.re_sum]
  simp_rw [hrep, hk]
  simp only [Finset.sum_neg_distrib, neg_div, mul_neg, neg_mul, neg_neg, Finset.sum_div,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ### Both fields are THE Hamiltonian vector fields of their Hamiltonians (G2) -/

/-- The torus field is the Hamiltonian vector field `(ω♭)⁻¹ dH` of `torusHamiltonian θ` for the
symplectic form `fsForm` (G2 + G6). -/
theorem torusField_eq_hamiltonianVectorField (θ : Fin (n + 1) → ℝ) :
    torusField θ = (fsForm_isSymplectic n).hamiltonianVectorField (torusHamiltonian θ) :=
  (torusField_isHamiltonianVectorField θ).eq_isSymplectic_hamiltonianVectorField
    (fsForm_isSymplectic n)

/-- The Schrödinger field is the Hamiltonian vector field `(ω♭)⁻¹ dH` of `-2 ⟨H⟩` for the
symplectic form `fsForm` (G2 + G13). -/
theorem schrodingerField_eq_hamiltonianVectorField {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) :
    schrodingerField H = (fsForm_isSymplectic n).hamiltonianVectorField (schrodingerHamiltonian H) :=
  (schrodingerField_isHamiltonianVectorField hH).eq_isSymplectic_hamiltonianVectorField
    (fsForm_isSymplectic n)

/-! ### The Hamiltonians are `C^m` for every order `m` (so `C^∞` and `C^ω`), and both fields are
`C^∞` vector fields (G3) -/

/-- The chart Hamiltonian is `C^m` for every order `m` (`∞` and `ω` included): inner-product
calculus along the affine lift, every step generic in the order. -/
theorem contDiff_schrodingerChartHam {m : WithTop ℕ∞} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) : ContDiff ℝ m (schrodingerChartHam H i) := by
  have hv : ContDiff ℝ m (insertOne (n := n) i) := by
    have h : insertOne (n := n) i = fun w => insertOne i 0 + insertZeroCLM i w :=
      funext (insertOne_eq_add i)
    rw [h]
    exact contDiff_const.add (insertZeroCLM i).contDiff
  have hT : ContDiff ℝ m (fun w => Matrix.toEuclideanCLM (𝕜 := ℂ) H (insertOne i w)) :=
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) H).restrictScalars ℝ).contDiff.comp hv
  have hN : ContDiff ℝ m
      (fun w => (inner ℂ (insertOne i w) (Matrix.toEuclideanCLM (𝕜 := ℂ) H (insertOne i w))).re) :=
    Complex.reCLM.contDiff.comp (hv.inner (𝕜 := ℂ) hT)
  have hD : ContDiff ℝ m (fun w => ‖insertOne i w‖ ^ 2) := by
    have e : (fun w => ‖insertOne i w‖ ^ 2)
        = fun w => (inner ℂ (insertOne i w) (insertOne i w)).re :=
      funext fun w => by simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (insertOne i w)).symm
    rw [e]
    exact Complex.reCLM.contDiff.comp (hv.inner (𝕜 := ℂ) hv)
  have hinv : ContDiff ℝ m (fun w => (‖insertOne i w‖ ^ 2)⁻¹) :=
    hD.inv fun w => (norm_sq_insertOne_pos i w).ne'
  exact contDiff_const.mul (hN.mul hinv)

/-- ★ The Hamiltonian of the Schrödinger flow is `C^m` on `ℂℙⁿ` for every order `m` (`C^∞` and
real-analytic in particular). -/
theorem contMDiff_schrodingerHamiltonian {m : WithTop ℕ∞}
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ContMDiff (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ ℝ) m
      (schrodingerHamiltonian (n := n) H) := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨(continuous_schrodingerHamiltonian H).continuousAt, ?_⟩
  have hw : (extChartAt (modelWithCornersSelf ℝ ℝ) (schrodingerHamiltonian H x)
      ∘ schrodingerHamiltonian H ∘ (extChartAt (modelWithCornersSelf ℝ (Fin n → ℂ)) x).symm)
      = schrodingerChartHam H (idx x) := by
    funext w
    simp only [Function.comp, extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id,
      extChartAt_coe_symm, modelWithCornersSelf_coe_symm]
    exact schrodingerHamiltonian_chartInv H (idx x) w
  rw [hw, modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ]
  exact (contDiff_schrodingerChartHam H (idx x)).contDiffAt

/-- ★ The Hamiltonian of the torus action is `C^m` on `ℂℙⁿ` for every order `m` (the diagonal
case). -/
theorem contMDiff_torusHamiltonian {m : WithTop ℕ∞} (θ : Fin (n + 1) → ℝ) :
    ContMDiff (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ ℝ) m
      (torusHamiltonian (n := n) θ) := by
  rw [← schrodingerHamiltonian_neg_diagonal]
  exact contMDiff_schrodingerHamiltonian _

/-- ★★ **The Schrödinger vector field on `ℂℙⁿ` is a `C^m` vector field for every infinite order
`m`** (`∞` and `ω`): it is the Hamiltonian vector field of a `C^m` energy for the `C^ω` form
    `fsForm`
(G2), and those are `C^m` (G3, `contMDiff_hamiltonianVectorField_of_contMDiff`). -/
theorem contMDiff_schrodingerField_of_le {m : WithTop ℕ∞} (hm : m + 1 ≤ m)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : H.IsHermitian) :
    ContMDiff (𝓘(ℝ, Fin n → ℂ))
      ((𝓘(ℝ, Fin n → ℂ)).prod (𝓘(ℝ, Fin n → ℂ))) m
      (fun x : ℙ ℂ (Ambient n) => Bundle.TotalSpace.mk' (Fin n → ℂ) x (schrodingerField H x)) := by
  rw [schrodingerField_eq_hamiltonianVectorField hH]
  exact contMDiff_hamiltonianVectorField_of_contMDiff fsForm _ hm
    (contMDiff_omega_fsSection.of_le le_top) (fsForm_isSymplectic n).nondegenerate
    (contMDiff_schrodingerHamiltonian H)

/-- ★★ **The Schrödinger vector field on `ℂℙⁿ` is a `C^∞` vector field** (a `C^∞` section of the
tangent bundle). -/
theorem contMDiff_schrodingerField {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) :
    ContMDiff (𝓘(ℝ, Fin n → ℂ))
      ((𝓘(ℝ, Fin n → ℂ)).prod (𝓘(ℝ, Fin n → ℂ))) ∞
      (fun x : ℙ ℂ (Ambient n) => Bundle.TotalSpace.mk' (Fin n → ℂ) x (schrodingerField H x)) :=
  contMDiff_schrodingerField_of_le (by simp) hH

/-- ★★ **The torus vector field on `ℂℙⁿ` is a `C^m` vector field for every infinite order `m`.** -/
theorem contMDiff_torusField_of_le {m : WithTop ℕ∞} (hm : m + 1 ≤ m) (θ : Fin (n + 1) → ℝ) :
    ContMDiff (𝓘(ℝ, Fin n → ℂ))
      ((𝓘(ℝ, Fin n → ℂ)).prod (𝓘(ℝ, Fin n → ℂ))) m
      (fun x : ℙ ℂ (Ambient n) => Bundle.TotalSpace.mk' (Fin n → ℂ) x (torusField θ x)) := by
  rw [torusField_eq_hamiltonianVectorField]
  exact contMDiff_hamiltonianVectorField_of_contMDiff fsForm _ hm
    (contMDiff_omega_fsSection.of_le le_top) (fsForm_isSymplectic n).nondegenerate
    (contMDiff_torusHamiltonian θ)

/-- ★★ **The torus vector field on `ℂℙⁿ` is a `C^∞` vector field.** -/
theorem contMDiff_torusField (θ : Fin (n + 1) → ℝ) :
    ContMDiff (𝓘(ℝ, Fin n → ℂ))
      ((𝓘(ℝ, Fin n → ℂ)).prod (𝓘(ℝ, Fin n → ℂ))) ∞
      (fun x : ℙ ℂ (Ambient n) => Bundle.TotalSpace.mk' (Fin n → ℂ) x (torusField θ x)) :=
  contMDiff_torusField_of_le (by simp) θ

/-! ### Integral curves on `ℂℙⁿ`: the Schrödinger flow is one, and `⟨H⟩` is conserved (G4) -/

/-- Local existence of integral curves of the Schrödinger field, through every point. -/
theorem exists_isMIntegralCurveAt_schrodingerField {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (x₀ : ℙ ℂ (Ambient n)) (t₀ : ℝ) :
    ∃ γ : ℝ → ℙ ℂ (Ambient n), γ t₀ = x₀ ∧ IsMIntegralCurveAt γ (schrodingerField H) t₀ := by
  rw [schrodingerField_eq_hamiltonianVectorField hH]
  exact (fsForm_isSymplectic n).exists_isMIntegralCurveAt_hamiltonianVectorField _
    (contMDiff_schrodingerHamiltonian H) x₀ t₀

/-- Uniqueness of global integral curves of the Schrödinger field. -/
theorem isMIntegralCurve_schrodingerField_eq {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) {γ γ' : ℝ → ℙ ℂ (Ambient n)} (hγ : IsMIntegralCurve γ (schrodingerField H))
    (hγ' : IsMIntegralCurve γ' (schrodingerField H)) {t₀ : ℝ} (h : γ t₀ = γ' t₀) : γ = γ' := by
  rw [schrodingerField_eq_hamiltonianVectorField hH] at hγ hγ'
  exact (fsForm_isSymplectic n).isMIntegralCurve_hamiltonianVectorField_eq _
    (contMDiff_schrodingerHamiltonian H) hγ hγ' h

/-- ★★ **`⟨H⟩` is conserved** along every integral curve of the Schrödinger field. -/
theorem expectation_eq_of_isMIntegralCurve_schrodingerField
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : H.IsHermitian) {γ : ℝ → ℙ ℂ (Ambient n)}
    (hγ : IsMIntegralCurve γ (schrodingerField H)) (t s : ℝ) :
    expectation H (γ t) = expectation H (γ s) := by
  have h := (schrodingerField_isHamiltonianVectorField hH).comp_eq_of_isMIntegralCurve hγ
    (fun x => (contMDiff_schrodingerHamiltonian (m := ∞) H x).mdifferentiableAt (by simp)) t s
  exact mul_left_cancel₀ (by norm_num : (-2 : ℝ) ≠ 0) h

/-- ★★★ **The Schrödinger flow is the integral curve of its field**: `t ↦ exp(-itH) • p` is a
global integral curve of `schrodingerField H`, for every `p`. In the chart at `exp(-itH) • p` the
curve is `s ↦ chartFun (exp(-i(s-t)H) • q)`, whose derivative at `s = t` is the chart velocity
(`hasDerivAt_chartFun_schrodingerUnitary`, shifted by the group law `expNegITH_unitary_group`). -/
theorem isMIntegralCurve_schrodingerUnitary_smul {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (p : ℙ ℂ (Ambient n)) :
    IsMIntegralCurve (fun t : ℝ => Matrix.schrodingerUnitary hH t • p) (schrodingerField H) := by
  have hUmat : Continuous
      fun t : ℝ => (Matrix.schrodingerUnitary hH t : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :=
    continuous_iff_continuousAt.2 fun t => (Matrix.schrodingerUnitary_hasDerivAt H hH
        t).continuousAt
  have hU : Continuous fun t : ℝ => Matrix.schrodingerUnitary hH t := hUmat.subtype_mk _
  have hcont : Continuous fun t : ℝ => Matrix.schrodingerUnitary hH t • p := hU.smul
      continuous_const
  intro t
  refine ⟨hcont.continuousAt, ?_⟩
  -- the curve in the chart at `q := exp(-itH) • p`
  have hq : chartInv (idx (Matrix.schrodingerUnitary hH t • p))
      (chartFun (idx (Matrix.schrodingerUnitary hH t • p)) (Matrix.schrodingerUnitary hH t • p))
      = Matrix.schrodingerUnitary hH t • p :=
    chartInv_chartFun _ _ (idx_spec _)
  have hfun : (fun s : ℝ => chartFun (idx (Matrix.schrodingerUnitary hH t • p))
        (Matrix.schrodingerUnitary hH s • p))
      = fun s : ℝ => chartFun (idx (Matrix.schrodingerUnitary hH t • p))
        (Matrix.schrodingerUnitary hH (s - t) • chartInv (idx (Matrix.schrodingerUnitary hH t • p))
          (chartFun (idx (Matrix.schrodingerUnitary hH t • p))
            (Matrix.schrodingerUnitary hH t • p))) := by
    funext s
    rw [hq, ← mul_smul, ← (Matrix.expNegITH_unitary_group hH).1, sub_add_cancel]
  have hd : HasDerivAt (fun s : ℝ => chartFun (idx (Matrix.schrodingerUnitary hH t • p))
      (Matrix.schrodingerUnitary hH s • p))
      (schrodingerField H (Matrix.schrodingerUnitary hH t • p)) t := by
    rw [hfun]
    have h0 := hasDerivAt_chartFun_schrodingerUnitary hH
      (idx (Matrix.schrodingerUnitary hH t • p))
      (chartFun (idx (Matrix.schrodingerUnitary hH t • p)) (Matrix.schrodingerUnitary hH t • p))
    have h1 : HasDerivAt (fun s : ℝ => s - t) 1 t :=
      (hasDerivAt_sub_const_iff t).2 (hasDerivAt_id' t)
    have h0' : HasDerivAt (fun τ : ℝ => chartFun (idx (Matrix.schrodingerUnitary hH t • p))
        (Matrix.schrodingerUnitary hH τ • chartInv (idx (Matrix.schrodingerUnitary hH t • p))
          (chartFun (idx (Matrix.schrodingerUnitary hH t • p))
            (Matrix.schrodingerUnitary hH t • p))))
        (schrodingerChartField H (idx (Matrix.schrodingerUnitary hH t • p))
          (chartFun (idx (Matrix.schrodingerUnitary hH t • p))
            (Matrix.schrodingerUnitary hH t • p))) (t - t) := by
      rw [sub_self]
      exact h0
    have h2 := HasDerivAt.scomp (h := fun s : ℝ => s - t) (x := t) h0' h1
    exact h2.congr_deriv (one_smul ℝ _)
  have hw : writtenInExtChartAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ (Fin n → ℂ)) t
      (fun s : ℝ => Matrix.schrodingerUnitary hH s • p)
      = fun s : ℝ => chartFun (idx (Matrix.schrodingerUnitary hH t • p))
          (Matrix.schrodingerUnitary hH s • p) := by
    funext s
    simp only [writtenInExtChartAt, Function.comp, extChartAt_model_space_eq_id,
      PartialEquiv.refl_symm, PartialEquiv.refl_coe, id, extChartAt_coe, modelWithCornersSelf_coe]
    rfl
  rw [hw]
  exact hd.hasFDerivAt.hasFDerivWithinAt

/-- ★★ **`⟨H⟩` is conserved by the Schrödinger flow**: `⟨H⟩_{exp(-itH) • p} = ⟨H⟩_p`. -/
theorem expectation_schrodingerUnitary_smul {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (p : ℙ ℂ (Ambient n)) (t : ℝ) :
    expectation H (Matrix.schrodingerUnitary hH t • p) = expectation H p := by
  have h := expectation_eq_of_isMIntegralCurve_schrodingerField hH
    (isMIntegralCurve_schrodingerUnitary_smul hH p) t 0
  rwa [schrodingerUnitary_zero_val' hH, one_smul] at h

/-! ### The torus orbits are integral curves of the torus field (G16)

`continuous_torusUnitary_smul` and `isMIntegralCurve_torusUnitary_smul` moved to
`ProjectiveSpaceMomentMap.lean` on 2026-09-16 (they use nothing from this file, and the
moment-map module's docstring cites them); the uniqueness corollaries stay here. -/

/-- Uniqueness of global integral curves of the torus field. -/
theorem isMIntegralCurve_torusField_eq (θ : Fin (n + 1) → ℝ) {γ γ' : ℝ → ℙ ℂ (Ambient n)}
    (hγ : IsMIntegralCurve γ (torusField θ)) (hγ' : IsMIntegralCurve γ' (torusField θ)) {t₀ : ℝ}
    (h : γ t₀ = γ' t₀) : γ = γ' := by
  rw [torusField_eq_hamiltonianVectorField] at hγ hγ'
  exact (fsForm_isSymplectic n).isMIntegralCurve_hamiltonianVectorField_eq _
    (contMDiff_torusHamiltonian θ) hγ hγ' h

/-- ★★ **The torus orbit is THE integral curve**: every global integral curve of the torus field
through `p` at time `0` is `t ↦ diag(e^{itθ}) • p`. -/
theorem eq_torusUnitary_smul_of_isMIntegralCurve (θ : Fin (n + 1) → ℝ) {γ : ℝ → ℙ ℂ (Ambient n)}
    (hγ : IsMIntegralCurve γ (torusField θ)) {p : ℙ ℂ (Ambient n)} (h0 : γ 0 = p) :
    γ = fun t : ℝ => torusUnitary (t • θ) • p :=
  isMIntegralCurve_torusField_eq θ hγ (isMIntegralCurve_torusUnitary_smul θ p) (t₀ := 0) (by
    show γ 0 = torusUnitary ((0 : ℝ) • θ) • p
    rw [h0, zero_smul, torusUnitary_zero, one_smul])

/-- ★★ **The torus Hamiltonian `2 ∑ θₖ μₖ` is conserved** along every integral curve of the torus
field. -/
theorem torusHamiltonian_eq_of_isMIntegralCurve_torusField (θ : Fin (n + 1) → ℝ)
    {γ : ℝ → ℙ ℂ (Ambient n)} (hγ : IsMIntegralCurve γ (torusField θ)) (t s : ℝ) :
    torusHamiltonian θ (γ t) = torusHamiltonian θ (γ s) :=
  (torusField_isHamiltonianVectorField θ).comp_eq_of_isMIntegralCurve hγ
    (mdifferentiable_torusHamiltonian θ) t s

/-- ★★ **The torus Hamiltonian is conserved by the torus flow**:
`2 ∑ θₖ μₖ (diag(e^{itθ}) • p) = 2 ∑ θₖ μₖ (p)`. -/
theorem torusHamiltonian_torusUnitary_smul (θ : Fin (n + 1) → ℝ) (p : ℙ ℂ (Ambient n)) (t : ℝ) :
    torusHamiltonian θ (torusUnitary (t • θ) • p) = torusHamiltonian θ p := by
  have h := torusHamiltonian_eq_of_isMIntegralCurve_torusField θ
    (isMIntegralCurve_torusUnitary_smul θ p) t 0
  rwa [zero_smul, torusUnitary_zero, one_smul] at h

/-! ### Both fields are analytic (G19)

The `ω` case of `contMDiff_schrodingerField_of_le` / `contMDiff_torusField_of_le`: one proof with
the `C^∞` case since 2026-09-17. -/

/-- ★★ **The Schrödinger vector field on `ℂℙⁿ` is an analytic vector field.** -/
theorem contMDiff_omega_schrodingerField {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) :
    ContMDiff (𝓘(ℝ, Fin n → ℂ))
      ((𝓘(ℝ, Fin n → ℂ)).prod (𝓘(ℝ, Fin n → ℂ))) ω
      (fun x : ℙ ℂ (Ambient n) => Bundle.TotalSpace.mk' (Fin n → ℂ) x (schrodingerField H x)) :=
  contMDiff_schrodingerField_of_le le_top hH

/-- ★★ **The torus vector field on `ℂℙⁿ` is an analytic vector field.** -/
theorem contMDiff_omega_torusField (θ : Fin (n + 1) → ℝ) :
    ContMDiff (𝓘(ℝ, Fin n → ℂ))
      ((𝓘(ℝ, Fin n → ℂ)).prod (𝓘(ℝ, Fin n → ℂ))) ω
      (fun x : ℙ ℂ (Ambient n) => Bundle.TotalSpace.mk' (Fin n → ℂ) x (torusField θ x)) :=
  contMDiff_torusField_of_le le_top θ

/-! ### The flows are the Hamiltonian flows, and Liouville from the Hamiltonian (Q29(e)) -/

section HamiltonianFlows

open MeasureTheory

/-- ★★ **The Schrödinger flow IS the Hamiltonian flow of `-2⟨H⟩`**: for Hermitian `H`, the manifold
flow of the Hamiltonian vector field of `schrodingerHamiltonian H` is `p ↦ exp(-itH) • p`, by
uniqueness of integral curves. -/
theorem hamiltonianFlow_schrodingerHamiltonian {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (t : ℝ) (p : ℙ ℂ (Ambient n)) :
    (fsForm_isSymplectic n).hamiltonianFlow (contMDiff_schrodingerHamiltonian H) t p
      = Matrix.schrodingerUnitary hH t • p := by
  have hγ : IsMIntegralCurve (fun t : ℝ => Matrix.schrodingerUnitary hH t • p)
      ((fsForm_isSymplectic n).hamiltonianVectorField (schrodingerHamiltonian H)) := by
    rw [← schrodingerField_eq_hamiltonianVectorField hH]
    exact isMIntegralCurve_schrodingerUnitary_smul hH p
  have h0 : (fun t : ℝ => Matrix.schrodingerUnitary hH t • p) 0 = p := by
    simp only [(Matrix.expNegITH_unitary_group hH).2, one_smul]
  have h := integralFlow_eq_of_isMIntegralCurve
    ((fsForm_isSymplectic n).contMDiff_hamiltonianVectorField_tangent
      (contMDiff_schrodingerHamiltonian H)) hγ h0
  exact (congrFun h t).symm

/-- ★★ **The torus flow IS the Hamiltonian flow of `2 ∑ θₖ μₖ`**: the manifold flow of the
Hamiltonian vector field of `torusHamiltonian θ` is `p ↦ diag(e^{itθ}) • p`. -/
theorem hamiltonianFlow_torusHamiltonian (θ : Fin (n + 1) → ℝ) (t : ℝ) (p : ℙ ℂ (Ambient n)) :
    (fsForm_isSymplectic n).hamiltonianFlow (contMDiff_torusHamiltonian θ) t p
      = torusUnitary (t • θ) • p := by
  have hγ : IsMIntegralCurve (fun t : ℝ => torusUnitary (t • θ) • p)
      ((fsForm_isSymplectic n).hamiltonianVectorField (torusHamiltonian θ)) := by
    rw [← torusField_eq_hamiltonianVectorField θ]
    exact isMIntegralCurve_torusUnitary_smul θ p
  have h0 : (fun t : ℝ => torusUnitary (t • θ) • p) 0 = p := by
    simp only [zero_smul, torusUnitary_zero, one_smul]
  have h := integralFlow_eq_of_isMIntegralCurve
    ((fsForm_isSymplectic n).contMDiff_hamiltonianVectorField_tangent
      (contMDiff_torusHamiltonian θ)) hγ h0
  exact (congrFun h t).symm

/-- ★★ **Liouville for the Schrödinger flow, from the Hamiltonian**: `p ↦ exp(-itH) • p` preserves
the Fubini–Study volume because it is the Hamiltonian flow of `-2⟨H⟩`
(`fsVolume_map_hamiltonianFlow`), not because it is unitary (`fsVolume_map_smul`). -/
theorem fsVolume_map_schrodingerUnitary_smul {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (t : ℝ) :
    Measure.map (fun p : ℙ ℂ (Ambient n) => Matrix.schrodingerUnitary hH t • p) (fsVolume n)
      = fsVolume n := by
  rw [show (fun p : ℙ ℂ (Ambient n) => Matrix.schrodingerUnitary hH t • p)
      = (fsForm_isSymplectic n).hamiltonianFlow (contMDiff_schrodingerHamiltonian H) t from
    funext fun p => (hamiltonianFlow_schrodingerHamiltonian hH t p).symm]
  exact fsVolume_map_hamiltonianFlow _ t

/-- The same for the normalised volume, `fsMeasure p₀`. -/
theorem fsVolumeNormalized_map_schrodingerUnitary_smul {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : H.IsHermitian) (t : ℝ) :
    Measure.map (fun p : ℙ ℂ (Ambient n) => Matrix.schrodingerUnitary hH t • p)
      (fsVolumeNormalized n) = fsVolumeNormalized n := by
  rw [fsVolumeNormalized,
    Measure.map_smul' _ _ (f := fun p : ℙ ℂ (Ambient n) => Matrix.schrodingerUnitary hH t • p)
      (Homeomorph.smul (Matrix.schrodingerUnitary hH t)).continuous.measurable,
    fsVolume_map_schrodingerUnitary_smul]

end HamiltonianFlows

end Projectivization
