import CsdLean4.LF2.Setup
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudyUnique

/-!
# LF4 §8: the first concrete ontic-shell instantiation

This file discharges the *structural* part of LF4 §8 (`specs/LF4-todo.md`):
it exhibits a concrete `CSD.LF2.SectorData`, proving that LF2's abstract
framework is **inhabited** (it had never been instantiated), and that the
sector-conditional measure bridge holds **axiom-free** for the instance.
For this base case (`π = id`) the bridge is the trivial `c = 1` identity;
the non-trivial-fibre Phase 2 (`ℂℙ^{N-1} × ℂℙ^{N-1}`, `π = pr₁`) is where
`invariant_measure_uniqueness_cpn` is actually exercised to discharge the
LF2 spec axiom `invariant_measure_uniqueness` on the instance.

## The instance

`cpSectorData p₀` is the minimal shell:

- `Σ = P = ℂℙ^{N-1} = ℙ ℂ (EuclideanSpace ℂ (Fin N))`;
- `G = U(N) = Matrix.unitaryGroup (Fin N) ℂ`, acting on `ℂℙ^{N-1}` as usual;
- `π = id`;
- `μL = fubiniStudyMeasure p₀` (the SU(N)-invariant Borel probability
  measure), `Φ = id`, `Ω₀ = univ`.

**Honest scope.** This is the *base case*. With `π = id` the projection has
trivial (point) fibres, so there is no unresolved ontic structure and the
bridge constant is `c = 1`. The value here is exactly: (i) LF2's
`SectorData` is now proven non-vacuous, and (ii) `cp_measure_bridge` is
axiom-free, demonstrating that the LF2 axiom is dischargeable in the
concrete `ℂℙ^{N-1}` / `U(N)` setting. A non-trivial-fibre instance
(`ℂℙ^{N-1} × ℂℙ^{N-1}`, `π = pr₁`) and, separately, the de-isolation
dynamics that turn volume ratios into Born weights, are future work; this
shell is the scaffold they attach to. It does **not** by itself reproduce
any Born prediction.
-/

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace LF4

variable {N : ℕ} [NeZero N]

/-- `ℂℙ^{N-1}`. -/
abbrev CPN (N : ℕ) := ℙ ℂ (EuclideanSpace ℂ (Fin N))

/-- `ℂℙ^{N-1}` is nonempty for `N ≥ 1` (it carries projective rays of a
nonzero space). -/
instance instNonemptyCPN : Nonempty (CPN N) := by
  haveI : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩⟩
  haveI : Nontrivial (EuclideanSpace ℂ (Fin N)) := inferInstance
  infer_instance

/-- The minimal ontic-shell `OnticSetup`: `μL` is Fubini–Study, the flow is
the identity, and the preparation region is everything. -/
noncomputable def cpOnticSetup (p₀ : CPN N) : CSD.LF1.OnticSetup (CPN N) where
  μL := ⟨fubiniStudyMeasure p₀, inferInstance⟩
  Φ := id
  hΦ_pres := MeasurePreserving.id _
  Ω0 := Set.univ
  hΩ0_meas := MeasurableSet.univ
  hΩ0_nonzero := by
    show (fubiniStudyMeasure p₀) Set.univ ≠ 0
    rw [measure_univ]; exact one_ne_zero

/-- **First concrete `SectorData`.** `Σ = P = ℂℙ^{N-1}`, `G = U(N)`,
`π = id`. Witnesses that LF2's abstract framework is inhabited. -/
noncomputable def cpSectorData (p₀ : CPN N) :
    CSD.LF2.SectorData (CPN N) (CPN N) (Matrix.unitaryGroup (Fin N) ℂ) where
  toOntic := cpOnticSetup p₀
  π := id
  measurable_π := measurable_id
  measurable_smul_σ := fun U => (continuous_const_smul U).measurable
  measurable_smul_P := fun U => (continuous_const_smul U).measurable
  hμL_inv := fun U =>
    ⟨(continuous_const_smul U).measurable, fubiniStudyMeasure_smul_invariant U p₀⟩
  hπ_equiv := fun _ _ => rfl

/-- **Axiom-free measure bridge for the instance.** `π∗μL = c · μFS` with
`c = 1` (since `π = id` and `μL = μFS`). Proved via `Measure.map_id`, so it
cites only the foundational triple — no LF2 axiom. -/
theorem cp_measure_bridge (p₀ : CPN N) :
    ∃ c : ENNReal,
      Measure.map (cpSectorData p₀).π ((cpSectorData p₀).μL : Measure (CPN N))
        = c • fubiniStudyMeasure p₀ := by
  have hμ : Measure.map (cpSectorData p₀).π ((cpSectorData p₀).μL : Measure (CPN N))
      = fubiniStudyMeasure p₀ := by
    show Measure.map id (fubiniStudyMeasure p₀) = fubiniStudyMeasure p₀
    rw [Measure.map_id]
  exact ⟨1, by rw [hμ, one_smul]⟩

end LF4
end CSD
