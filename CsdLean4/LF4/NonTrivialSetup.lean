/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.LF4.KahlerOnticSetup
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudy
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.TransitionProbability

/-!
# A genuine `Φ ≠ id` `KahlerOnticSetup` inhabitant (connectivity fix C1)

**Category:** 3-Local (A genuine `Φ ≠ id` `KahlerOnticSetup` inhabitant (connectivity fix C1)).

`trivialKahlerOnticSetup` (`LF4/KahlerOnticSetup.lean`) is the identity-flow
witness (`Φ = id`, `projectedFlow = id`): the whole W-series Schrödinger chain,
instantiated on it, collapses to `exp(0) = 1`. The 2026-07-07 connectivity audit
(`specs/connectivity-manifest.md`, link L4) flagged this as the load-bearing gap
— the only inhabitant of `KahlerOnticSetup` was trivial, so the Schrödinger
pillar was never exercised on a non-trivial flow.

This module supplies a genuine one whose **projected flow moves the rays**.

* `unitaryFlowSetup N U p₀` : for ANY one-parameter family of unitaries
  `U : ℝ → unitaryGroup (Fin N) ℂ`, the `KahlerOnticSetup N` with
  `Σ = ℂℙ^{N-1}`, `π = id`, `flow t = projectedFlow t = (U t • ·)`, and Liouville
  measure the Fubini–Study measure. Measure-preservation is exactly the
  `U(N)`-invariance of `μ_FS` (`fubiniStudyMeasure_smul_invariant`); the descent
  equation `projectable` holds by `rfl` (`π = id`, `flow = projectedFlow`).
  Unlike `kFlow` (which translates a `T²` fibre and so acts trivially on rays),
  the projected flow here IS the unitary action on `ℂℙ^{N-1}`.

* `rotationSetup p₀` : the concrete non-trivial witness at `N = 2`, with
  `U t` the real rotation `R(t) = [[cos t, −sin t],[sin t, cos t]]` (unitary, no
  matrix exponential needed). `rotationSetup_projectedFlow_ne_id` proves
  `∃ t, projectedFlow t ≠ id` — at `t = π/2` the flow sends the ray `[e₀]` to
  `[e₁] ≠ [e₀]`. This is the first `KahlerOnticSetup` inhabitant whose projected
  dynamics is genuinely `≠ id`; it flips connectivity link L4.

## Honest scope

This is a non-trivial *instance*, not the derivation of the sector. The flow is a
posited measure-preserving unitary family (any `U` works); showing that the
W-series recovers its Hermitian generator on this instance is the follow-on C2.
The Kähler-geometry fields remain honest `True` placeholders (link L1).

## Provenance

Foundational-triple only. Reuses `KahlerOnticSetup`, the projectivization unitary
action, and `fubiniStudyMeasure_smul_invariant`; nothing is re-proved.
-/

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF4

/-! ## The general unitary-flow constructor -/

/-- **A `KahlerOnticSetup` from any one-parameter unitary family.** `Σ = ℂℙ^{N-1}`,
`π = id`, `flow t = projectedFlow t = (U t • ·)`, Liouville measure `= μ_FS`.
Measure-preserving because `μ_FS` is `U(N)`-invariant.

The Kähler-geometry placeholder fields (fix C5, connectivity link L1):
* `IsLiouvilleKahlerVolume` now carries the **formalizable core** of "Liouville
  = Kähler volume" — that `μ_FS` is a *normalized* volume, i.e. a probability
  measure (`∫ ω^n/n! = 1`). This is genuine, checkable content, and it is
  consumed by `unitaryFlowSetup_liouville_isProbability`, so the field is no
  longer inert.
* `IsKahlerSector := IsFubiniStudyKahler N` now carries the **genuine formalizable
  core**: the pointwise Fubini–Study Kähler compatibility on the tangent model
  (proved, `isFubiniStudyKahler`), no longer `True`. Only the manifold closedness
  `dω = 0` (no Mathlib API) stays the honestly-named residual. -/
noncomputable def unitaryFlowSetup (N : ℕ)
    (U : ℝ → Matrix.unitaryGroup (Fin N) ℂ)
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    KahlerOnticSetup N where
  Sigma := ℙ ℂ (EuclideanSpace ℂ (Fin N))
  compact_sigma := inferInstance
  IsKahlerSector := IsFubiniStudyKahler N
  kahler_condition := isFubiniStudyKahler N
  liouvilleMeasure := fubiniStudyMeasure p₀
  IsLiouvilleKahlerVolume := IsProbabilityMeasure (fubiniStudyMeasure p₀)
  liouville_eq_kahler_volume := inferInstance
  pi := id
  pi_measurable := measurable_id
  flow := fun t p => U t • p
  flow_preserves_volume := fun t =>
    ⟨(continuous_const_smul (U t)).measurable, fubiniStudyMeasure_smul_invariant (U t) p₀⟩
  projectedFlow := fun t p => U t • p
  projectable := fun _ _ => rfl

@[simp] lemma unitaryFlowSetup_projectedFlow (N : ℕ)
    (U : ℝ → Matrix.unitaryGroup (Fin N) ℂ)
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N))) (t : ℝ)
    (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    (unitaryFlowSetup N U p₀).projectedFlow t p = U t • p := rfl

/-! ## The concrete rotation witness at `N = 2` -/

/-- The real rotation matrix `R(t) = [[cos t, −sin t],[sin t, cos t]]` over `ℂ`. -/
noncomputable def rotMat (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos t : ℂ), -(Real.sin t : ℂ); (Real.sin t : ℂ), (Real.cos t : ℂ)]

/-- `R(t)` is unitary: `star R(t) * R(t) = 1`, by `sin² + cos² = 1`. -/
lemma rotMat_mem_unitaryGroup (t : ℝ) : rotMat t ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [rotMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val', Matrix.empty_val',
      Matrix.one_apply, RCLike.star_def, Complex.conj_ofReal, map_neg,
      Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    norm_num <;>
    (first | linear_combination Complex.sin_sq_add_cos_sq (t : ℂ) | ring)

/-- `R(t)` as a bundled unitary-group element. -/
noncomputable def rotU (t : ℝ) : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨rotMat t, rotMat_mem_unitaryGroup t⟩

/-- The concrete **non-trivial** `KahlerOnticSetup 2`: the rotation flow on
`ℂℙ¹`. Its projected flow moves rays (`rotationSetup_projectedFlow_ne_id`). -/
noncomputable def rotationSetup (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin 2))) :
    KahlerOnticSetup 2 :=
  unitaryFlowSetup 2 rotU p₀

/-- `R(π/2) = [[0, −1],[1, 0]]`, so it sends the first basis vector `e₀` to the
second `e₁`. -/
lemma rotMat_pi_div_two_mulVec_e0 :
    (rotMat (Real.pi / 2)).toEuclideanLin (EuclideanSpace.single 0 (1 : ℂ))
      = EuclideanSpace.single 1 (1 : ℂ) := by
  rw [Matrix.toLpLin_apply]
  congr 1
  rw [PiLp.ofLp_single]
  ext i
  fin_cases i <;>
    simp [rotMat, Matrix.mulVec, dotProduct,
      Real.cos_pi_div_two, Real.sin_pi_div_two, Pi.single_apply]

/-- **C1 / connectivity link L4: the projected flow is genuinely `≠ id`.** For
the rotation setup, `projectedFlow (π/2)` sends `[e₀]` to `[e₁] ≠ [e₀]`, so it is
not the identity map on rays. This is the first `KahlerOnticSetup` inhabitant
with non-trivial projected dynamics. -/
theorem rotationSetup_projectedFlow_ne_id
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin 2))) :
    ∃ t : ℝ, (rotationSetup p₀).projectedFlow t ≠ id := by
  refine ⟨Real.pi / 2, ?_⟩
  intro hid
  -- Evaluate at the ray `[e₀]`.
  have he0 : (EuclideanSpace.single 0 (1 : ℂ) : EuclideanSpace ℂ (Fin 2)) ≠ 0 := by
    simp [PiLp.single_eq_zero_iff]
  have he1 : (EuclideanSpace.single 1 (1 : ℂ) : EuclideanSpace ℂ (Fin 2)) ≠ 0 := by
    simp [PiLp.single_eq_zero_iff]
  have hflow : (rotationSetup p₀).projectedFlow (Real.pi / 2)
        (Projectivization.mk ℂ (EuclideanSpace.single 0 (1 : ℂ)) he0)
      = Projectivization.mk ℂ (EuclideanSpace.single 1 (1 : ℂ)) he1 := by
    rw [rotationSetup, unitaryFlowSetup_projectedFlow]
    rw [show (rotU (Real.pi / 2)) • Projectivization.mk ℂ (EuclideanSpace.single 0 (1:ℂ)) he0
          = Projectivization.mk ℂ
              (Matrix.toEuclideanLin (rotU (Real.pi / 2)).val
                (EuclideanSpace.single 0 (1:ℂ))) _
        from Projectivization.smul_mk_eq_mk_toEuclideanLin _ he0]
    rw [Projectivization.mk_eq_mk_iff']
    exact ⟨1, by rw [one_smul]; exact rotMat_pi_div_two_mulVec_e0.symm⟩
  -- `hid` forces the flow to fix `[e₀]`, contradicting `[e₁] ≠ [e₀]`.
  rw [hid, id_eq] at hflow
  -- `mk e₁ = mk e₀` would make `e₁` a scalar multiple of `e₀`, impossible.
  rw [Projectivization.mk_eq_mk_iff'] at hflow
  obtain ⟨a, ha⟩ := hflow
  have h0 := congrFun (congrArg (fun v => (WithLp.ofLp v : Fin 2 → ℂ)) ha) 0
  simp at h0

/-! ## Consuming the Kähler-volume field (connectivity fix C5, link L1) -/

/-- **The `IsLiouvilleKahlerVolume` field is load-bearing.** It carries the
formalizable core of the "Liouville = Kähler volume" posit — that the sector's
typicality measure is a *normalized* volume (a probability measure) — and this
theorem CONSUMES `d.liouville_eq_kahler_volume` to expose it. Before fix C5 the
Kähler-geometry fields were inert placeholders read by no theorem (connectivity
link L1); this makes the volume field genuine. (`IsKahlerSector` remains an
honestly-unformalizable posit — no Mathlib Kähler API.) -/
theorem unitaryFlowSetup_liouville_isProbability (N : ℕ)
    (U : ℝ → Matrix.unitaryGroup (Fin N) ℂ)
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    IsProbabilityMeasure (unitaryFlowSetup N U p₀).liouvilleMeasure :=
  (unitaryFlowSetup N U p₀).liouville_eq_kahler_volume

end LF4
end CSD
