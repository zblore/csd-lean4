import CsdLean4.LF4.ObservableFlow
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudyUnique
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.MeasureSpace

/-!
# A5 onramp: where the Fubini–Study typicality measure comes from

This file isolates the honest content of the A5 datum (`SectorData.(π, G)`,
`AXIOMS.md §3.3`) at the level of the **typicality measure**: which measure is
forced as the ontic typicality law on the sector `Σ = ℂℙ^{N-1}`, and by what.

## The two honest results

**(A) Typicality is FORCED by the sector symmetry `G = U(N)`.**
`fubiniStudy_forced_by_symmetry` restates the corpus's axiom-free uniqueness
theorem `fubiniStudyMeasure_unique` (Phase G4,
`Mathlib/LinearAlgebra/Projectivization/FubiniStudyUnique.lean`) as a
typicality-derivation: **any** `U(N)`-invariant probability measure on the sector
**is** the Fubini–Study measure. So the Born = FS-volume measure (the input to the
Duistermaat–Heckman cluster `fs_born_volume_ratio_N` / `born_frequency_convergence_N`)
is *derived* from the sector symmetry — the A5 `(π, G)` datum — not posited as an
independent typicality law. The derivation is via the **symmetry group**, not via
any single flow.

**(B) A single ontic flow does NOT force FS (the obstruction).**
`obsFlow_not_uniquely_ergodic` exhibits, for `obsFlow` (the diagonal-phase
Hamiltonian flow `t ↦ exp(i t Â)` of `LF4/ObservableFlow.lean`), **two distinct**
`obsFlow`-invariant probability measures: the Fubini–Study measure and the Dirac
measure `δ_{[eⱼ]}` at a computational-basis eigenstate ray. Because `obsFlow` is a
diagonal phase flow, every basis ray `[eⱼ]` is an eigenvector and is a fixed point
(`obsFlow_fixes_eigenstate`), so `δ_{[eⱼ]}` is invariant
(`dirac_eigenstate_obsFlow_invariant`); and `δ_{[eⱼ]} ≠ μFS` because FS is
`U(N)`-invariant while `δ_{[eⱼ]}` is moved by a unitary swapping `[eⱼ] ↔ [eₖ]`.
Hence `obsFlow` is not uniquely ergodic: a single deterministic flow cannot single
out FS. This is *why* the concrete instances `cpSectorDataFlow` / `kSectorDataFlow`
(D1c-1/2), whose `Φ` is one such flow, do not discharge A5.

## Honest scope (the whole point — claim NOTHING more)

This tranche does **not** close A5. It (i) shows the typicality measure FS is
*forced by the sector symmetry* `G = U(N)` (a derivation, reusing the uniqueness
theorem), (ii) proves *no single ontic flow* can do the same (the obstruction), and
(iii) thereby **pins the residual A5 primitive to `G` itself**: the symmetry group
`U(N)` is the datum from which typicality follows, and `G`-from-dynamics — deriving
the `U(N)`-symmetry of the ontic flow from the deterministic substrate — is exactly
**D1**, the deepest open content (`Φ = id` in every concrete `SectorData`, or a
single non-ergodic phase flow in D1c). We claim **nothing** about deriving `G`.

`a5_onramp` conjoins (A) and (B). Foundational-triple-only (no `busch_effect_gleason`);
`invariant_measure_uniqueness_cpn` / `fubiniStudyMeasure_unique` are axiom-free.
-/

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF4

variable {N : ℕ} [NeZero N]

/-! ## Computational-basis eigenstate rays -/

omit [NeZero N] in
/-- The computational-basis vector `eⱼ = single j 1` is nonzero. -/
lemma cpBasisVec_ne_zero (j : Fin N) : (EuclideanSpace.single j (1 : ℂ)) ≠ 0 := by
  intro h
  have h2 : (EuclideanSpace.single j (1 : ℂ)) j = (0 : EuclideanSpace ℂ (Fin N)) j := by
    rw [h]
  rw [EuclideanSpace.single_apply] at h2
  simp at h2

/-- The computational-basis eigenstate **ray** `[eⱼ] ∈ ℂℙ^{N-1}`. -/
noncomputable def cpBasisRay (j : Fin N) : CPN N :=
  Projectivization.mk ℂ (EuclideanSpace.single j (1 : ℂ)) (cpBasisVec_ne_zero j)

omit [NeZero N] in
/-- Distinct indices give distinct basis rays (`[eⱼ] ≠ [eₖ]` for `j ≠ k`): if they
were equal, some scalar `a` would satisfy `a • eₖ = eⱼ`, impossible at coordinate
`j` (`0 = a·0 ≠ 1`). -/
lemma cpBasisRay_ne (j k : Fin N) (hjk : j ≠ k) : cpBasisRay j ≠ cpBasisRay k := by
  intro he
  rw [cpBasisRay, cpBasisRay] at he
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' ℂ _ _ (cpBasisVec_ne_zero j) (cpBasisVec_ne_zero k)).mp he
  -- `a • eₖ` vanishes at coordinate `j` (since `j ≠ k`); but `ha` makes it `eⱼ`, value `1` there.
  have hj : (a • EuclideanSpace.single k (1 : ℂ)) j = 0 := by
    simp only [PiLp.smul_apply, EuclideanSpace.single_apply, if_neg hjk, smul_zero]
  rw [ha, EuclideanSpace.single_apply, if_pos rfl] at hj
  exact one_ne_zero hj

/-! ## (B) — the eigenstate ray is a fixed point of `obsFlow` -/

/-- **The diagonal-phase flow fixes every computational-basis ray.**
`obsFlow λ t [eⱼ] = [eⱼ]`: the diagonal `obsUnitary λ t` scales `eⱼ` by the unit
phase `obsPhase λ t j`, which is the same projective ray. (This is exactly why the
`Φ ≠ id` witness `obsFlow_ne_id` must use a *superposition* ray, never a basis ray.) -/
theorem obsFlow_fixes_eigenstate (lam : Fin N → ℝ) (t : ℝ) (j : Fin N) :
    obsFlow lam t (cpBasisRay j) = cpBasisRay j := by
  rw [cpBasisRay]
  simp only [obsFlow]
  rw [smul_mk_eq_mk]
  refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨obsPhase lam t j, ?_⟩
  ext i
  rw [obsUnitary_toEuclideanLin_apply]
  simp only [PiLp.smul_apply, EuclideanSpace.single_apply, smul_eq_mul]
  split_ifs with h
  · rw [h]
  · ring

/-- **The Dirac measure at an eigenstate ray is `obsFlow`-invariant.**
Immediate from `Measure.map_dirac` and the fixed-point `obsFlow_fixes_eigenstate`. -/
theorem dirac_eigenstate_obsFlow_invariant (lam : Fin N → ℝ) (t : ℝ) (j : Fin N) :
    Measure.map (obsFlow lam t) (Measure.dirac (cpBasisRay j))
      = Measure.dirac (cpBasisRay j) := by
  have hmeas : Measurable (obsFlow lam t) :=
    (continuous_const_smul (obsUnitary lam t)).measurable
  rw [Measure.map_dirac' hmeas, obsFlow_fixes_eigenstate lam t j]

/-! ## Dirac injectivity on the (Hausdorff Borel) sector -/

omit [NeZero N] in
/-- Distinct points give distinct Dirac measures on `ℂℙ^{N-1}` (singletons are
measurable: `Projectivization.instMeasurableSingletonClass`). -/
lemma dirac_ne_of_ne {p q : CPN N} (h : p ≠ q) :
    (Measure.dirac p : Measure (CPN N)) ≠ Measure.dirac q := by
  intro he
  have hms : MeasurableSet ({q} : Set (CPN N)) := measurableSet_singleton q
  have h1 : (Measure.dirac p : Measure (CPN N)) {q} = 1 := by
    rw [he]; exact (dirac_eq_one_iff_mem hms).mpr rfl
  rw [dirac_eq_one_iff_mem hms] at h1
  exact h h1

/-! ## (A) — typicality is forced by the sector symmetry `G = U(N)` -/

/-- **(A) Typicality is forced by the sector symmetry.** Any `U(N)`-invariant
probability measure on the sector `Σ = ℂℙ^{N-1}` **is** the Fubini–Study measure.
A restatement of the axiom-free `fubiniStudyMeasure_unique` (Phase G4) as the
typicality-derivation: the Born = FS-volume measure consumed downstream is *derived*
from the `A5` `(π, G)` sector datum, not posited. The derivation is via the symmetry
*group*, not via any single flow (contrast (B) below). -/
theorem fubiniStudy_forced_by_symmetry (p₀ : CPN N)
    (μ : Measure (CPN N)) [IsProbabilityMeasure μ]
    (hμ_inv : ∀ U : Matrix.unitaryGroup (Fin N) ℂ,
        MeasurePreserving (fun p => U • p) μ μ) :
    μ = fubiniStudyMeasure p₀ :=
  fubiniStudyMeasure_unique p₀ μ (fun U => (hμ_inv U).map_eq)

/-! ## (B) — a single ontic flow does not force FS -/

/-- **(B) The honest negative.** `obsFlow` is **not uniquely ergodic**: it admits at
least two distinct invariant probability measures — the Fubini–Study measure `μFS`
(invariant by `obsFlow_measurePreserving`) and the Dirac measure `δ_{[e₀]}` at a
computational-basis eigenstate ray (invariant by `dirac_eigenstate_obsFlow_invariant`,
since the diagonal phase flow fixes basis rays). They differ: FS is `U(N)`-invariant
while `δ_{[e₀]}` is moved to `δ_{[e₁]}` by a unitary swapping the two rays
(transitivity of the `U(N)`-action), and distinct rays give distinct Dirac measures.

So **no single deterministic ontic flow forces FS** — only the full sector symmetry
`G = U(N)` does (result (A)). This is the obstruction behind the naive
"single ergodic flow whose unique invariant measure is `μFS`" picture, and the reason
`cpSectorDataFlow` / `kSectorDataFlow` (D1c) do not discharge A5. -/
theorem obsFlow_not_uniquely_ergodic (hN : 1 < N) (p₀ : CPN N) (lam : Fin N → ℝ) (t : ℝ) :
    ∃ μ ν : Measure (CPN N),
      IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
      Measure.map (obsFlow lam t) μ = μ ∧
      Measure.map (obsFlow lam t) ν = ν ∧ μ ≠ ν := by
  refine ⟨fubiniStudyMeasure p₀, Measure.dirac (cpBasisRay (obsIdx0 hN)),
    inferInstance, inferInstance, ?_, ?_, ?_⟩
  · -- μFS is obsFlow-invariant (the Liouville / FS-invariance content).
    exact (obsFlow_measurePreserving lam t p₀).map_eq
  · -- δ_{[e₀]} is obsFlow-invariant (basis ray is a fixed point).
    exact dirac_eigenstate_obsFlow_invariant lam t (obsIdx0 hN)
  · -- μFS ≠ δ_{[e₀]}: otherwise the swap unitary moves a U(N)-invariant Dirac.
    intro hμν
    have hqr : cpBasisRay (obsIdx0 hN) ≠ cpBasisRay (obsIdx1 hN) :=
      cpBasisRay_ne _ _ (obsIdx0_ne_obsIdx1 hN)
    obtain ⟨U, hU⟩ := MulAction.exists_smul_eq (Matrix.unitaryGroup (Fin N) ℂ)
      (cpBasisRay (obsIdx0 hN)) (cpBasisRay (obsIdx1 hN))
    have hFSinv := fubiniStudyMeasure_smul_invariant U p₀
    rw [hμν, Measure.map_dirac' (continuous_const_smul U).measurable] at hFSinv
    -- hFSinv : δ_{U•[e₀]} = δ_{[e₀]}, and U•[e₀] = [e₁].
    have hru : (Measure.dirac (cpBasisRay (obsIdx1 hN)) : Measure (CPN N))
        = Measure.dirac (cpBasisRay (obsIdx0 hN)) := by
      have hstep : (Measure.dirac (cpBasisRay (obsIdx1 hN)) : Measure (CPN N))
          = Measure.dirac ((fun p => U • p) (cpBasisRay (obsIdx0 hN))) := by
        congr 1; exact hU.symm
      rw [hstep, hFSinv]
    exact (dirac_ne_of_ne hqr.symm) hru

/-! ## Capstone -/

/-- **A5 onramp.** Conjunction of the two honest results:

* **(A)** `fubiniStudy_forced_by_symmetry`: any `U(N)`-invariant typicality law on the
  sector `ℂℙ^{N-1}` **is** the Fubini–Study measure — so Born = FS-volume is *derived*
  from the sector symmetry `G = U(N)`, not posited.
* **(B)** `obsFlow_not_uniquely_ergodic`: a single ontic flow (`obsFlow`) does **not**
  force FS — it has at least two distinct invariant probability measures.

**Honest framing.** Typicality (FS) is derived **from the symmetry group `G`**, not
from any single flow; the residual A5 primitive is therefore `G = U(N)` **itself**,
which reduces to **D1** (deriving the `U(N)`-symmetry of the ontic dynamics from the
deterministic substrate — *not done*, the deepest open content). This does **not**
close A5; it locates the typicality derivation in the symmetry and pins the residue. -/
theorem a5_onramp (hN : 1 < N) (p₀ : CPN N) (lam : Fin N → ℝ) (t : ℝ) :
    (∀ (μ : Measure (CPN N)), IsProbabilityMeasure μ →
        (∀ U : Matrix.unitaryGroup (Fin N) ℂ, MeasurePreserving (fun p => U • p) μ μ) →
        μ = fubiniStudyMeasure p₀)
    ∧
    (∃ μ ν : Measure (CPN N),
        IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
        Measure.map (obsFlow lam t) μ = μ ∧
        Measure.map (obsFlow lam t) ν = ν ∧ μ ≠ ν) := by
  refine ⟨fun μ hp h => ?_, obsFlow_not_uniquely_ergodic hN p₀ lam t⟩
  haveI := hp
  exact fubiniStudy_forced_by_symmetry p₀ μ h

end LF4
end CSD
