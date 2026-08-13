/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DegenerateLuders
public import CsdLean4.LF4.TypicalityForcing

/-!
# SigmaLayer/PointerArena: the compact Kähler pointer — arena, regions, ready state (brick 0)

**Category:** dynamical measurement — the smooth-Hamiltonian witness route
(`specs/pointer-witness-plan.md` brick 0; the ★ L backlog item, route confirmed 2026-08-03).

The torus-flux correction (2026-08-02, `SigmaLayer/PiecewiseHamiltonian.lean`) showed the landed
witnesses' register translations are symplectic but **not globally Hamiltonian** on `T²`
(`ι_Xω = a·dp` closed-not-exact, `∮dp ≠ 0`). The confirmed repair replaces the torus **register**
with a projective pointer `ℂℙ^K = ℙ(ℂ^{K+1})` — compact Kähler with `H¹ = 0`, where unitary
one-parameter groups are globally Hamiltonian flows. This module is the kinematic floor of that
witness:

* `Pointer K` — the pointer manifold `ℂℙ^K`; `readyState = [f₀]` and, for each outcome
  `j : Fin K`, `recordState j = [f_{j+1}]` (reusing `vertexPoint`/`momentMap_vertex`);
* `recordRegion j = {q | 1/2 < m_{j+1}(q)}` and `readyRegion δ = {q | 1 − δ < m₀(q)}` via the
  pointer moment map — **open** (so a continuous propagator can land in them stably),
  measurable, pairwise disjoint, each containing its vertex, each of **positive Fubini–Study
  measure** (`fubiniStudyMeasure_pos_of_isOpen`, full support);
* `PointerArena N K = KSigma N × Pointer K` with `pointerLiouville = kMuL ⊗ μ_FS^{ptr}`, a
  probability measure; the arena-level ready/record cylinders and their measures.

⚠️ **Honest scope.** Kinematics only: no propagator, no Hamiltonian, and no record is *created*
here — that is bricks 1–4 of `pointer-witness-plan.md`. The `1/2` threshold makes disjointness a
one-line simplex fact (two moment coordinates cannot both exceed `1/2`); nothing downstream may
read `q ∈ recordRegion j` as "the pointer IS `[f_{j+1}]`" — **transition states** (all moment
coordinates `≤ 1/2`) are legitimate pointer points lying *outside every region by design*, which
is exactly the exceptional room `no_everywhere_correlation`
(`SigmaLayer/MeasurementConstraints.lean`) forces every continuous exact-record dynamics to
have. Contrast the piecewise horn: the openness of these regions is the property whose torus
analogue (discrete register arcs) fed `shearEvolve_not_continuous`
(`SigmaLayer/ShearDiscontinuity.lean`).

## References

`specs/pointer-witness-plan.md` (the brick ladder and the trade-off table);
`specs/BACKLOG.md` (the ★ L row); `specs/future-work.md`; second external review 2026-08-02
(steps 1–3). Reused corpus API: `vertexPoint` (`SigmaLayer/SwapLuders.lean`),
`momentMap_vertex` (`SigmaLayer/DegenerateLuders.lean`), the `momentMap` simplex facts
(`LF4/MomentMap.lean`), `fubiniStudyMeasure_pos_of_isOpen` (`LF4/TypicalityForcing.lean`),
`kMuL` (`LF4/KahlerInstance.lean`).
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory Matrix.UnitaryGroup

variable {K : ℕ}

/-- The pointer manifold `ℂℙ^K = ℙ(ℂ^{K+1})`: one ready direction `f₀` and `K` record
directions `f₁, …, f_K`. Compact Kähler with `H¹ = 0` — the property that makes unitary
one-parameter groups globally Hamiltonian, killing the torus-flux obstruction. -/
abbrev Pointer (K : ℕ) := LF4.CPN (K + 1)

/-- The ready state: the vertex ray `[f₀]`. -/
noncomputable def readyState : Pointer K := vertexPoint 0

/-- The record state for outcome `j`: the vertex ray `[f_{j+1}]`. -/
noncomputable def recordState (j : Fin K) : Pointer K := vertexPoint j.succ

/-- Two moment coordinates at distinct indices sum to at most `1` — the simplex fact behind
every disjointness statement below. -/
lemma momentMap_add_le_one (q : Pointer K) {i j : Fin (K + 1)} (hij : i ≠ j) :
    LF4.momentMap q i + LF4.momentMap q j ≤ 1 := by
  calc LF4.momentMap q i + LF4.momentMap q j
      = ∑ k ∈ ({i, j} : Finset (Fin (K + 1))), LF4.momentMap q k :=
        (Finset.sum_pair hij).symm
    _ ≤ ∑ k, LF4.momentMap q k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun k _ _ => LF4.momentMap_nonneg q k)
    _ = 1 := LF4.momentMap_sum_eq_one q

/-! ### Record regions -/

/-- The record region for outcome `j`: pointer states whose `f_{j+1}` moment coordinate
dominates, `m_{j+1}(q) > 1/2`. Open by design — a continuous propagator can land in it with a
stable margin. -/
def recordRegion (j : Fin K) : Set (Pointer K) :=
  {q | 1 / 2 < LF4.momentMap q j.succ}

theorem isOpen_recordRegion (j : Fin K) : IsOpen (recordRegion (K := K) j) :=
  isOpen_lt continuous_const (LF4.continuous_momentMap j.succ)

theorem measurableSet_recordRegion (j : Fin K) :
    MeasurableSet (recordRegion (K := K) j) :=
  (isOpen_recordRegion j).measurableSet

/-- **Distinct record regions are disjoint**: two moment coordinates cannot both exceed
`1/2`. -/
theorem recordRegion_pairwiseDisjoint :
    Pairwise (Function.onFun Disjoint (recordRegion (K := K))) := by
  intro j l hjl
  rw [Function.onFun, Set.disjoint_left]
  intro q hqj hql
  have hij : (j.succ : Fin (K + 1)) ≠ l.succ := fun h => hjl (Fin.succ_injective _ h)
  have hle := momentMap_add_le_one q hij
  have h1 : (1 / 2 : ℝ) < LF4.momentMap q j.succ := hqj
  have h2 : (1 / 2 : ℝ) < LF4.momentMap q l.succ := hql
  linarith

/-- The record state lies in its own record region. -/
theorem recordState_mem_recordRegion (j : Fin K) :
    recordState j ∈ recordRegion (K := K) j := by
  show (1 / 2 : ℝ) < LF4.momentMap (vertexPoint j.succ) j.succ
  rw [momentMap_vertex, if_pos rfl]
  norm_num

/-- Every record region has positive Fubini–Study measure (openness + full support). -/
theorem recordRegion_pos (q₀ : Pointer K) (j : Fin K) :
    fubiniStudyMeasure q₀ (recordRegion (K := K) j) ≠ 0 :=
  LF4.fubiniStudyMeasure_pos_of_isOpen q₀ (isOpen_recordRegion j)
    ⟨recordState j, recordState_mem_recordRegion j⟩

/-! ### The ready region -/

/-- The ready region at margin `δ`: pointer states with `m₀(q) > 1 − δ`. A genuinely open
neighbourhood of the ready state — the positive-measure ready region the landing theorem
(brick 3) will start from. -/
def readyRegion (δ : ℝ) : Set (Pointer K) :=
  {q | 1 - δ < LF4.momentMap q 0}

theorem isOpen_readyRegion (δ : ℝ) : IsOpen (readyRegion (K := K) δ) :=
  isOpen_lt continuous_const (LF4.continuous_momentMap 0)

theorem measurableSet_readyRegion (δ : ℝ) :
    MeasurableSet (readyRegion (K := K) δ) :=
  (isOpen_readyRegion δ).measurableSet

theorem readyState_mem_readyRegion {δ : ℝ} (hδ : 0 < δ) :
    readyState ∈ readyRegion (K := K) δ := by
  show (1 - δ : ℝ) < LF4.momentMap (vertexPoint 0) 0
  rw [momentMap_vertex, if_pos rfl]
  linarith

/-- The ready region has positive Fubini–Study measure for every positive margin. -/
theorem readyRegion_pos (q₀ : Pointer K) {δ : ℝ} (hδ : 0 < δ) :
    fubiniStudyMeasure q₀ (readyRegion (K := K) δ) ≠ 0 :=
  LF4.fubiniStudyMeasure_pos_of_isOpen q₀ (isOpen_readyRegion δ)
    ⟨readyState, readyState_mem_readyRegion hδ⟩

/-- With margin `δ ≤ 1/2`, the ready region is disjoint from every record region: being ready
and carrying a record exclude each other. -/
theorem readyRegion_disjoint_recordRegion {δ : ℝ} (hδ : δ ≤ 1 / 2) (j : Fin K) :
    Disjoint (readyRegion (K := K) δ) (recordRegion j) := by
  rw [Set.disjoint_left]
  intro q h0 hj
  have h0j : (0 : Fin (K + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
  have hle := momentMap_add_le_one q h0j
  have h1 : (1 - δ : ℝ) < LF4.momentMap q 0 := h0
  have h2 : (1 / 2 : ℝ) < LF4.momentMap q j.succ := hj
  linarith

/-! ### The arena -/

variable {N : ℕ} [NeZero N]

/-- The pointer arena: the ontic sector `Σ = ℂℙ^{N-1} × T²` (base + selector fibre) times the
pointer `ℂℙ^K`. A product of compact Kähler manifolds, real dimension `2(N−1) + 2 + 2K` —
even, with no odd factor for the parity check to catch. -/
abbrev PointerArena (N K : ℕ) := LF4.KSigma N × Pointer K

/-- The arena Liouville measure `μL = (μ_FS ⊗ vol_{T²}) ⊗ μ_FS^{ptr}`. -/
noncomputable def pointerLiouville (p₀ : LF4.CPN N) (q₀ : Pointer K) :
    Measure (PointerArena N K) :=
  (LF4.kMuL p₀).prod (fubiniStudyMeasure q₀)

instance (p₀ : LF4.CPN N) (q₀ : Pointer K) :
    IsProbabilityMeasure (pointerLiouville p₀ q₀) := by
  unfold pointerLiouville
  infer_instance

/-- The arena-level ready cylinder: pointer in the ready region, sector free. -/
def arenaReady (N : ℕ) (δ : ℝ) : Set (PointerArena N K) :=
  Set.univ ×ˢ readyRegion δ

/-- The arena-level record cylinder for outcome `j`. -/
def arenaRecord (N : ℕ) (j : Fin K) : Set (PointerArena N K) :=
  Set.univ ×ˢ recordRegion j

omit [NeZero N] in
theorem measurableSet_arenaReady (δ : ℝ) :
    MeasurableSet (arenaReady (K := K) N δ) :=
  MeasurableSet.univ.prod (measurableSet_readyRegion δ)

omit [NeZero N] in
theorem measurableSet_arenaRecord (j : Fin K) :
    MeasurableSet (arenaRecord (K := K) N j) :=
  MeasurableSet.univ.prod (measurableSet_recordRegion j)

omit [NeZero N] in
/-- The arena ready cylinder's Liouville measure is the pointer-side FS measure of the ready
region (the sector factor integrates to `1`). -/
theorem pointerLiouville_arenaReady (p₀ : LF4.CPN N) (q₀ : Pointer K) (δ : ℝ) :
    pointerLiouville p₀ q₀ (arenaReady N δ)
      = fubiniStudyMeasure q₀ (readyRegion (K := K) δ) := by
  rw [pointerLiouville, arenaReady, Measure.prod_prod, measure_univ, one_mul]

omit [NeZero N] in
/-- **The apparatus-ready state has positive Liouville measure** — the structural property the
`GlobalBasin` arena provably lacks (`globalBasin_ae_total`: a.e. every point there already
carries a record) and the reason the pointer factor exists at all. -/
theorem arenaReady_pos (p₀ : LF4.CPN N) (q₀ : Pointer K) {δ : ℝ} (hδ : 0 < δ) :
    pointerLiouville p₀ q₀ (arenaReady N δ) ≠ 0 := by
  rw [pointerLiouville_arenaReady]
  exact readyRegion_pos q₀ hδ

end CSD.RecordLayer
