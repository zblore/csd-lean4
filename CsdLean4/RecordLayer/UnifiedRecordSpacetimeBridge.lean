/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedRadarGeometry
public import CsdLean4.RecordLayer.ActivatedWrite

/-!
# From the point of `Σ` to the operational geometry: the identifications

**Category:** 7-SigmaLayer (the record layer). BACKLOG #432 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Task 11 of the research delivery
plan of 2026-11-16. No new assumption beyond UA-18.

`csd_operational_lorentz_from_records` (#431, #432) is stated for `wallRunAt`. This module
identifies what `wallRunAt` is in each layer of the architecture, so that the chain from one
point of the arena to the comparison of the two observers' coordinates can be followed
without a change of model.

* **Ontic and geometric layers.** `triRun_eq_arenaFlow`, `wallRunAt_orbit`
  — the run is one orbit, from one point of the five-pointer arena `PentaSigma`, of the
  Hamiltonian flow of the energy `fiveCoupledEnergy` for the symplectic form `pentaForm`
  (#404's arena, UA-18). `triFlow_map_pentaMuL`, `wallFlow_map_pentaMuL` — that flow
  preserves the measure `μ_FS ⊗ vol⁵` of the arena, for the walled chain's matrices.
* **Measurement layer.** `IsTickCount.exists_crossings` — a count `N` of a pointer is `N`
  successive passages of that one orbit from the pointer's ready region to its display
  region and no `N + 1`; `pointerReady_disjoint_pointerDisplay` — the two regions are
  disjoint, so a tick distinguishes them.
* **Operational and spacetime layers.** `WallRadarGeometry` (#432): the five counts, the two
  observers' coordinates `restEvent`, `movingEvent` built from them, their comparison by the
  boost and the comparison of their intervals.

## Exact scope

* **Identifications, not new estimates.** The first two are definitional equalities; the
  measure statement is `pentaMuL_map_fiveCoupledFlow` for matrices shown Hermitian here.
* **The counts are properties of one orbit.** No probability enters the statement of
  `csd_operational_lorentz_from_records`: no Born weight is used or derived. The obstruction
  of UD-45 to UD-53 (the statistics of the drift coupling are not the quantum ones) stands
  as recorded and is not touched by this module.
* **The preparation is a product ray** of three packets with five pointer angles in an open
  set. Nothing here says that preparation is typical for the arena's measure.
* **The pointer's regions are the arcs `readyArc 2` and `displayArc`** of
  `ActivatedWrite.lean`; a count is read off the orbit, no register of the arena holds it.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-45, UD-53, UD-164, UD-201, UD-202);
`RecordLayer/UnifiedRadarGeometry.lean` (#431, #432: `csd_operational_lorentz_from_records`,
`WallRadarGeometry`); `RecordLayer/UnifiedWallOpen.lean` (#430: `wallRunAt`);
`RecordLayer/UnifiedTriCarrier.lean` (#405: `triRun`); `RecordLayer/UnifiedTriFibre.lean`
(#430: the gates are Hermitian); `LF4/PentaCoupledFlow.lean` (#404: `PentaSigma`, `pentaForm`,
`fiveCoupledEnergy`, `fiveCoupledFlow`, `pentaMuL_map_fiveCoupledFlow`);
`RecordLayer/UnifiedDiracClockTicks.lean` (#358: `HasTicks`, `IsTickCount`);
`RecordLayer/ActivatedWrite.lean` (`readyArc_disjoint_displayArc`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

/-! ### The measurement layer -/

/-- **A count is a number of crossings of one orbit.** If a history has the count `N` at `T`,
there are `N` successive pairs of times `a_i < b_i ≤ T` at which it is in the resting set and
then in the displaying set, and there are not `N + 1`. -/
theorem IsTickCount.exists_crossings {X : Type*} {rest disp : Set X} {γ : ℝ → X} {T : ℝ}
    {N : ℕ} (h : IsTickCount rest disp γ T N) :
    (∃ a b : ℕ → ℝ,
      (∀ i, i < N → 0 ≤ a i ∧ a i < b i ∧ b i ≤ T ∧ γ (a i) ∈ rest ∧ γ (b i) ∈ disp)
        ∧ ∀ i, i + 1 < N → b i < a (i + 1))
      ∧ ¬ HasTicks rest disp γ T (N + 1) :=
  ⟨h.1, h.2⟩

/-- **A pointer's two regions are disjoint**: the states of the arena in which the last
pointer is ready and those in which it displays. -/
theorem pointerReady_disjoint_pointerDisplay (D : ℕ) :
    Disjoint {x : PentaSigma D | x.2 ∈ readyArc 2} {x : PentaSigma D | x.2 ∈ displayArc} :=
  Set.disjoint_left.2 fun _ h1 h2 => Set.disjoint_left.1 readyArc_disjoint_displayArc h1 h2

/-! ### The ontic and geometric layers -/

section Tri

variable {ι κa κb S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κa] [DecidableEq κa]
  [Fintype κb] [DecidableEq κb] [Fintype S] [DecidableEq S] {N : ℕ}
  (e : ι × (κa × κb) ≃ Fin (N + 1)) (M₀ : Matrix ι ι ℂ) (A₀ : Matrix κa κa ℂ)
  (B₀ : Matrix κb κb ℂ) (σ : ι → S) (α : κa → S) (β : κb → S)
  (r₁ r₂ r₃ r₄ r₅ : S → S → Prop) [DecidableRel r₁] [DecidableRel r₂] [DecidableRel r₃]
  [DecidableRel r₄] [DecidableRel r₅] (Ya : Matrix κa κa ℂ) (Yb : Matrix κb κb ℂ)
  {f g k l r : ℝ → ℝ}

omit [Fintype S] [DecidableEq S] in
/-- ★ **The run of three carriers is one orbit of a Hamiltonian flow.** `triRun` at the flow
time `t` is the Hamiltonian flow, for the symplectic form `pentaForm` of the five-pointer
arena, of the energy `fiveCoupledEnergy` of the three carriers' matrix and the five gates,
applied to one point: the product ray with the five pointer angles. -/
theorem triRun_eq_arenaFlow (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hr : Function.Periodic r 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k)
    (hcl : ContDiff ℝ ∞ l) (hcr : ContDiff ℝ ∞ r) (p : GenArena ι) (qa : GenArena κa)
    (qb : GenArena κb) (θ ψ χ ξ ζ : KTorus) (t : ℝ) :
    triRun e M₀ A₀ B₀ σ α β r₁ r₂ r₃ r₄ r₅ Ya Yb hf hg hk hl hr hc hcg hck hcl hcr p qa qb
        θ ψ χ ξ ζ t
      = (pentaForm_isSymplectic N).hamiltonianFlow
          (contMDiff_fiveCoupledEnergy
            (Matrix.reindex e e (compositeH M₀ (compositeH A₀ B₀)))
            (Matrix.reindex e e
              (gateOp σ (fun k : κa × κb => β k.2) r₁ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)))
            (Matrix.reindex e e
              (gateOp σ (fun k : κa × κb => β k.2) r₂ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)))
            (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ gateOp α β r₃ Yb))
            (Matrix.reindex e e
              (gateOp σ (fun k : κa × κb => α k.1) r₄ (Ya ⊗ₖ (1 : Matrix κb κb ℂ))))
            (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ gateOpL α β r₅ Ya))
            hf hg hk hl hr hc hcg hck hcl hcr) t
          (((((idxArenaEquiv e (prodRay p (prodRay qa qb)), θ), ψ), χ), ξ), ζ) :=
  rfl

variable {M₀ A₀ B₀ σ α β r₁ r₂ r₃ r₄ r₅ Ya Yb}

omit [Fintype S] [DecidableEq S] in
/-- ★ **The flow of three carriers and five gates preserves the arena's measure**
`μ_FS ⊗ vol⁵`, when the carriers' matrices and the two gated operators are Hermitian and the
gated operators do not move their carriers between sites. -/
theorem triFlow_map_pentaMuL (hM : M₀.IsHermitian) (hA : A₀.IsHermitian) (hB : B₀.IsHermitian)
    (hYa : Ya.IsHermitian) (hYas : ∀ i j, α i ≠ α j → Ya i j = 0) (hYb : Yb.IsHermitian)
    (hYbs : ∀ i j, β i ≠ β j → Yb i j = 0) (hf : Function.Periodic f 1)
    (hg : Function.Periodic g 1) (hk : Function.Periodic k 1) (hl : Function.Periodic l 1)
    (hr : Function.Periodic r 1) (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g)
    (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l) (hcr : ContDiff ℝ ∞ r)
    (p₀ : CPN (N + 1)) (t : ℝ) :
    Measure.map
        (fiveCoupledFlow (Matrix.reindex e e (compositeH M₀ (compositeH A₀ B₀)))
          (Matrix.reindex e e
            (gateOp σ (fun k : κa × κb => β k.2) r₁ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)))
          (Matrix.reindex e e
            (gateOp σ (fun k : κa × κb => β k.2) r₂ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)))
          (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ gateOp α β r₃ Yb))
          (Matrix.reindex e e
            (gateOp σ (fun k : κa × κb => α k.1) r₄ (Ya ⊗ₖ (1 : Matrix κb κb ℂ))))
          (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ gateOpL α β r₅ Ya))
          hf hg hk hl hr hc hcg hck hcl hcr t) (pentaMuL p₀)
      = pentaMuL p₀ :=
  pentaMuL_map_fiveCoupledFlow
    ((compositeH_isHermitian hM (compositeH_isHermitian hA hB)).submatrix _)
    ((gateOp_snd_isHermitian (κa := κa) σ β r₁ hYb hYbs).submatrix _)
    ((gateOp_snd_isHermitian (κa := κa) σ β r₂ hYb hYbs).submatrix _)
    ((kronecker_isHermitian Matrix.isHermitian_one
      (gateOp_isHermitian α β r₃ hYb hYbs)).submatrix _)
    ((gateOp_fst_isHermitian (κb := κb) σ α r₄ hYa hYas).submatrix _)
    ((kronecker_isHermitian Matrix.isHermitian_one
      (gateOpL_isHermitian α β r₅ hYa hYas)).submatrix _)
    hf hg hk hl hr hc hcg hck hcl hcr p₀ t

end Tri

/-- ★★ **The walled chain's run is one orbit of the arena's Hamiltonian flow, and that flow
preserves the arena's measure.** For every labelling `e`, messenger ray, clock rays and five
pointer angles: `wallRunAt` is `t ↦ Φ_t x₀` for one map `Φ_t` of `PentaSigma D` and the one
point `x₀` made of the product ray and the five angles; and `Φ_t` preserves `μ_FS ⊗ vol⁵`. -/
theorem wallRunAt_orbit (n N M : ℕ) (μ Δ w gA gB : ℝ) {D : ℕ}
    (e : (ZMod (M + 1) × Fin 2) × (((ZMod (M + 1) × Fin 2) × Fin 2)
      × ((ZMod (M + 1) × Fin 2) × Fin 2)) ≃ Fin (D + 1)) :
    ∃ Φ : ℝ → PentaSigma D → PentaSigma D,
      (∀ (p : GenArena (ZMod (M + 1) × Fin 2))
          (qa qb : GenArena ((ZMod (M + 1) × Fin 2) × Fin 2)) (θ ψ χ ξ ζ : KTorus) (t : ℝ),
        wallRunAt n N M μ Δ w gA gB e p qa qb θ ψ χ ξ ζ t
          = Φ t (((((idxArenaEquiv e (prodRay p (prodRay qa qb)), θ), ψ), χ), ξ), ζ))
      ∧ ∀ (p₀ : CPN (D + 1)) (t : ℝ), Measure.map (Φ t) (pentaMuL p₀) = pentaMuL p₀ :=
  ⟨_, fun _ _ _ _ _ _ _ _ _ => rfl, fun p₀ t =>
    triFlow_map_pentaMuL e
      (diracHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) μ)
      (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
      (deviceHam_isHermitian (L := M + 1) (ringHop (1200 * n * N) M) 1 (1 + Δ))
      (levelSwap_isHermitian (ZMod (M + 1) × Fin 2)) levelSwap_apply_eq_zero_of_site_ne
      (levelSwap_isHermitian (ZMod (M + 1) × Fin 2)) levelSwap_apply_eq_zero_of_site_ne
      (scaledTrainF_periodic gB) (scaledTrainF_periodic gB) (scaledTrainF_periodic gB)
      (scaledTrainF_periodic gA) (scaledTrainF_periodic gA)
      (contDiff_scaledTrainF gB) (contDiff_scaledTrainF gB) (contDiff_scaledTrainF gB)
      (contDiff_scaledTrainF gA) (contDiff_scaledTrainF gA) p₀ t⟩

end CSD.RecordLayer

end
