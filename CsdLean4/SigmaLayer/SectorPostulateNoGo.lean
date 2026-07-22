/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.NonTrivialSetup
public import CsdLean4.LF4.Instance
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudy
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudyUnique

/-!
# SigmaLayer/SectorPostulateNoGo: the single-flow limit — a deterministic flow does not pin the sector

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)).

The localized A5 result (`SigmaLayer/LocalisedTypicality.lean`) shows the typicality measure is forced by the
`U(N)` SYMMETRY. This module makes precise WHY the *universal* A5 — deriving the Born measure `μ_FS` from
a single deterministic flow — is not reachable: **a single projective flow does not uniquely determine an
invariant measure**, so it cannot single out `μ_FS`.

The mechanism: a fixed ray of the flow supports an invariant Dirac measure. A projective unitary flow
with two DISTINCT fixed rays therefore has (at least) two distinct invariant probability measures — so
its invariant measure is not unique, and at least one of them is not `μ_FS`
(`flow_admits_invariant_ne_fubiniStudy`). Since a projective flow with an eigen-ray always has such
Diracs, and every unitary on `ℂ^N` (`N ≥ 2`) has orthogonal eigen-rays (spectral theorem), the
conclusion is generic; `phaseFlip_admits_invariant_ne_fubiniStudy` exhibits it on a concrete NON-trivial
flow (the phase-flip `diag(1,-1)` on `ℂℙ¹`).

## What this establishes

`μ_FS` is invariant under the flow (`fubiniStudyMeasure_smul_invariant`), but it is NOT distinguished
among the flow's invariant measures — the flow admits others. So "A5 is posited" is not a temporary
formalisation gap but a proved statement about the limit: the deterministic flow underdetermines the
sector's typicality measure. Pinning `μ_FS` needs the full `U(N)` symmetry (`IsForcedKahlerVolume`'s
uniqueness), which a single one-parameter flow does not carry. This matches Paper C (§1.4): `Σ`, `π`, the
A5 sector are assumed, not derived.

References: `specs/connectivity-manifest.md` (L7 / A5), `specs/reconstruction-status.md` (frontier),
`SigmaLayer/LocalisedTypicality.lean` (`region_measure_symmetry_forced`, the positive companion),
`LF4/KahlerVolumeForced.lean` (`IsForcedKahlerVolume`).
-/

@[expose] public section

open MeasureTheory Matrix Matrix.UnitaryGroup CSD.LF4
open scoped LinearAlgebra.Projectivization

namespace CSD.SigmaLayer

variable {N : ℕ}

/-- **The single-flow limit (no-go for universal A5).** If a projective unitary flow `x ↦ V • x` fixes
two DISTINCT rays `p ≠ q`, it admits an invariant probability measure that is NOT the Fubini–Study /
Born measure. The two fixed-ray Diracs are both invariant and distinct, so at least one differs from
`μ_FS`. Hence the flow does not uniquely determine the sector's typicality measure. -/
theorem flow_admits_invariant_ne_fubiniStudy (p₀ : CPN N)
    (V : Matrix.unitaryGroup (Fin N) ℂ) {p q : CPN N} (hpq : p ≠ q)
    (hp : V • p = p) (hq : V • q = q) :
    ∃ μ : Measure (CPN N), IsProbabilityMeasure μ
      ∧ MeasurePreserving (fun x => V • x) μ μ ∧ μ ≠ fubiniStudyMeasure p₀ := by
  have hmeas : Measurable (fun x : CPN N => V • x) := (continuous_const_smul V).measurable
  have hinv : ∀ {r : CPN N}, V • r = r →
      MeasurePreserving (fun x => V • x) (Measure.dirac r) (Measure.dirac r) :=
    fun {r} hr => ⟨hmeas, (Measure.map_dirac' hmeas r).trans (congrArg Measure.dirac hr)⟩
  have hdne : Measure.dirac p ≠ Measure.dirac q := fun h => hpq (dirac_eq_dirac_iff.mp h)
  by_cases hfs : Measure.dirac p = fubiniStudyMeasure p₀
  · exact ⟨Measure.dirac q, inferInstance, hinv hq, fun h => hdne (hfs.trans h.symm)⟩
  · exact ⟨Measure.dirac p, inferInstance, hinv hp, hfs⟩

/-- The phase-flip unitary `diag(1, -1)` on `ℂ²` (a genuine `Φ ≠ id` element: it fixes the poles
`[e₀], [e₁]` but moves `[e₀ + e₁]`). -/
noncomputable def phaseFlip : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨Matrix.diagonal (fun i => if i = 1 then (-1 : ℂ) else 1), by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal_apply]⟩

/-- `phaseFlip` fixes the ray of a standard basis vector. -/
theorem phaseFlip_smul_single (i : Fin 2)
    (hi : (EuclideanSpace.single i (1 : ℂ) : EuclideanSpace ℂ (Fin 2)) ≠ 0) :
    phaseFlip • Projectivization.mk ℂ (EuclideanSpace.single i (1 : ℂ)) hi
      = Projectivization.mk ℂ (EuclideanSpace.single i (1 : ℂ)) hi := by
  rw [show phaseFlip • Projectivization.mk ℂ (EuclideanSpace.single i (1 : ℂ)) hi
        = Projectivization.mk ℂ
            (Matrix.toEuclideanLin phaseFlip.val (EuclideanSpace.single i (1 : ℂ))) _
      from Projectivization.smul_mk_eq_mk_toEuclideanLin _ hi]
  rw [Projectivization.mk_eq_mk_iff']
  refine ⟨Units.mk0 (if i = 1 then (-1 : ℂ) else 1) (by fin_cases i <;> norm_num), ?_⟩
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [phaseFlip, Matrix.toLpLin_apply, Matrix.mulVec_single, EuclideanSpace.single]

/-- **The no-go on a concrete non-trivial flow.** The phase-flip flow `x ↦ phaseFlip • x` on `ℂℙ¹`
admits an invariant probability measure other than `μ_FS`: it fixes the two distinct poles `[e₀], [e₁]`,
whose Diracs are invariant and distinct. So even a genuine `Φ ≠ id` deterministic flow does not pin the
Born measure. -/
theorem phaseFlip_admits_invariant_ne_fubiniStudy (p₀ : CPN 2) :
    ∃ μ : Measure (CPN 2), IsProbabilityMeasure μ
      ∧ MeasurePreserving (fun x => phaseFlip • x) μ μ ∧ μ ≠ fubiniStudyMeasure p₀ := by
  have he0 : (EuclideanSpace.single 0 (1 : ℂ) : EuclideanSpace ℂ (Fin 2)) ≠ 0 := by
    simp [PiLp.single_eq_zero_iff]
  have he1 : (EuclideanSpace.single 1 (1 : ℂ) : EuclideanSpace ℂ (Fin 2)) ≠ 0 := by
    simp [PiLp.single_eq_zero_iff]
  refine flow_admits_invariant_ne_fubiniStudy p₀ phaseFlip (p := Projectivization.mk ℂ _ he0)
    (q := Projectivization.mk ℂ _ he1) ?_ (phaseFlip_smul_single 0 he0) (phaseFlip_smul_single 1 he1)
  intro h
  rw [Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  have h0 := congrFun (congrArg (fun v => (WithLp.ofLp v : Fin 2 → ℂ)) ha) 0
  simp [EuclideanSpace.single, PiLp.smul_apply] at h0

end CSD.SigmaLayer
