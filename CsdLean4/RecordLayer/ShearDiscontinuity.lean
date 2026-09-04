/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DegenerateLuders
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Topology
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# SigmaLayer/ShearDiscontinuity: the measurement propagator is provably not continuous

**Category:** dynamical measurement / classification (machine-checking an external review's
claim, 2026-08-02).

## The claim, and why it matters

The external review of the dynamical arc observed: the shear witness's measurement-interval
propagator displaces the register by `shearAmt (basinIndex x)` — an amount depending on a
*discrete* index that jumps across basin seams — so the propagator cannot be continuous, and
therefore **cannot be the time slice of any ordinary (continuous, let alone smooth Hamiltonian)
flow**. The earlier classification of "Hamiltonian generation" as *scoped on Mathlib's missing
manifold API* was therefore misjustified: writing down `H_int = g(t)·Â_sel ⊗ P̂_R` does not make
the witness its flow — the flow of that (bounded, self-adjoint) generator is continuous, and the
witness is not.

This module machine-checks the review's claim: ★ `shearEvolve_not_continuous`.

## What this does and does not say

* It **confirms** the witness is a measurable, measure-preserving, *piecewise* map — not a
  continuous flow. The scope claims of `ShearWitness.lean` (which never asserted continuity)
  stand; the *classification* of the Hamiltonian-origin row is what changes.
* ⚠️ *Corrected 2026-08-02 (second external review) — the original text here overread the
  no-go.* `no_everywhere_correlation` forces an **exceptional (non-correlating) set**: a
  continuous propagator cannot have its whole connected ready image inside `⋃ᵢ Bᵢ` while
  meeting two of them. It does **not** force the propagator to be discontinuous — a
  *continuous* (even smooth, globally Hamiltonian) propagator that sends the seams to
  transition states *outside* `⋃ᵢ Bᵢ` remains mathematically open. What this module proves is
  only that **this witness** is discontinuous. *Corrected 2026-08-04 (codebase audit).* — the continuous route was
  **delivered twice on 2026-08-03**: the ε-corridor pointer witness
  (`continuous_pointerEvolve`, `RecordLayer/PointerWeights.lean`) and the exact-Born third
  horn (`nullSeamClosure`, `RecordLayer/NullSeamWitness.lean`, whose seams map to the
  kissing state outside every record region). This module's negative result stands, and is
  what makes its witness one horn of a trilemma rather than a defect.
* The two recorded repair routes (`specs/BACKLOG.md`): **(1)** smooth corridor regularisation —
  records and Born correct up to `ε`, priced by `collapse_accuracy_bound`; **(2)** classify the
  measurement dynamics **piecewise, with a null seam set** (standard in dynamics: billiards,
  impact systems), justified physically by the forced-seam no-go. ⚠️ Route (2) was taken
  (`RecordLayer/PiecewiseHamiltonian.lean`) and its name corrected the same evening: the pieces
  are rigid **symplectic** translations, *not* flows of global Hamiltonians (`ι_Xω = a·dp` is
  closed but not exact on `T²`). Route (1) was then delivered separately as the compact-Kähler
  pointer witness. Both stand, as two horns of the trilemma named above — this is no longer an
  open choice between repairs.

## Supporting results

* `Projectivization.connectedSpace_of_isConnected_nonzero` + the instance here: **`ℂℙ^{N-1}` is
  connected** (nonzero vectors of a rank-`2N > 1` real space are connected), hence so is
  `KSigma N` — the topological input that makes a locally constant nontrivial index impossible.
* `vertex_mem_globalBasin` — explicit basin inhabitants at the vertices (every fibre point of a
  vertex lies in its full-width cell), giving `basinIndex` at least two values when `N ≥ 2`.
* `pshift_shearAmt_inj` — the `N` shear displacements are pairwise distinct points of the
  register torus, so the propagator's register marginal takes `≥ 2` values.

## References

`RecordLayer/ShearWitness.lean` (`shearEvolve`, `pshift`, `shearAmt`);
`RecordLayer/MeasurementConstraints.lean` (`no_everywhere_correlation` — the forced-seam no-go);
`RecordLayer/DynamicBorn.lean` (`basinIndex`, `basinIndex_eq_of_mem`);
`RecordLayer/DegenerateLuders.lean` (`vertexPoint`, `momentMap_vertex`);
`Mathlib/LinearAlgebra/Projectivization/Topology.lean` (connectedness, staged);
`specs/reconstruction-status.md` §2a (A2 row); `specs/BACKLOG.md` (the reopened row).
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

variable {N : ℕ}

/-! ### `ℂℙ^{N-1}` and `KSigma N` are connected -/

instance [NeZero N] : ConnectedSpace (LF4.CPN N) := by
  apply Projectivization.connectedSpace_of_isConnected_nonzero
  have hN : 1 ≤ N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hfr : Module.finrank ℝ (EuclideanSpace ℂ (Fin N)) = 2 * N := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin N)),
      Complex.finrank_real_complex, finrank_euclideanSpace_fin]
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℂ (Fin N)) := by
    rw [← Module.finrank_eq_rank, hfr]
    exact_mod_cast (by omega : 1 < 2 * N)
  have h0 := isConnected_compl_singleton_of_one_lt_rank hrank (0 : EuclideanSpace ℂ (Fin N))
  simpa [Set.compl_singleton_eq] using h0

/-! ### Basin inhabitants at the vertices -/

/-- Every fibre point over a vertex lies in that vertex's basin: the vertex's cell has full
width, and `rep` lands in `Ioc 0 1` by construction. -/
lemma vertex_mem_globalBasin [NeZero N] (j : Fin N) (θ : LF4.KTorus) :
    ((vertexPoint j, θ) : LF4.KSigma N) ∈ globalBasin (momentContext N) j := by
  show θ.1 ∈ circleCell ((momentContext N).rate (vertexPoint j)) j
  rw [momentContext_rate]
  have hlo : loSum (LF4.momentMap (vertexPoint j)) j = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [momentMap_vertex]
    rw [Finset.mem_filter] at hk
    exact if_neg (fun h => absurd hk.2 (by rw [h]; exact lt_irrefl _))
  have hone : LF4.momentMap (vertexPoint j) j = 1 := by
    rw [momentMap_vertex, if_pos rfl]
  show rep θ.1 ∈ Ioc (loSum (LF4.momentMap (vertexPoint j)) j)
    (loSum (LF4.momentMap (vertexPoint j)) j + LF4.momentMap (vertexPoint j) j)
  rw [hlo, hone, zero_add]
  have hrep := (AddCircle.equivIoc (1 : ℝ) 0 θ.1).2
  simpa [rep] using hrep

/-! ### The shear displacements are pairwise distinct -/

lemma shearAmt_mem_Ico (K : ℕ) (i : Fin K) : shearAmt K i ∈ Ico (0 : ℝ) 1 := by
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  constructor
  · unfold shearAmt shearGap
    positivity
  · unfold shearAmt shearGap
    rw [mul_one_div, div_lt_one hK]
    have hi : ((i : ℕ) : ℝ) < (K : ℝ) := by exact_mod_cast i.isLt
    linarith

/-- Distinct outcomes displace the register to distinct points. -/
lemma pshift_shearAmt_inj (K : ℕ) (r : LF4.KTorus) {i j : Fin K}
    (h : pshift (shearAmt K i) r = pshift (shearAmt K j) r) : i = j := by
  have h1 : ((shearAmt K i : ℝ) : AddCircle (1 : ℝ)) = ((shearAmt K j : ℝ) : AddCircle (1 : ℝ)) := by
    have := congrArg Prod.fst h
    simpa [pshift] using this
  have hIco : ∀ m : Fin K, shearAmt K m ∈ Ico (0 : ℝ) (0 + 1) := by
    intro m
    simpa using shearAmt_mem_Ico K m
  rw [AddCircle.coe_eq_coe_iff_of_mem_Ico (hIco i) (hIco j)] at h1
  unfold shearAmt shearGap at h1
  have hg : (0 : ℝ) < 1 / ((K : ℝ) + 1) := by positivity
  have hval : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by
    have := mul_right_cancel₀ (ne_of_gt hg) h1
    linarith
  exact Fin.ext (by exact_mod_cast hval)

/-! ### The headline -/

/-- **★ The shear witness's measurement propagator is not continuous.** Over the full
measurement interval, the propagator displaces the register by `shearAmt (basinIndex x)`. If it
were continuous, the register marginal at a fixed ready register would be a continuous map from
the *connected* space `KSigma N` onto `≥ 2` distinct points, whose fibres would give a clopen
partition — impossible. So the witness is a measurable, measure-preserving, **piecewise** map,
not a time slice of any continuous flow. *(Correction 2026-08-02: the no-go forces an exceptional
non-correlating set, not discontinuity — see the module header; a continuous propagator with
seams mapped outside the pointer regions was open when that was written and is now
**delivered**: `continuous_pointerEvolve` and `nullSeamClosure`, both 2026-08-03. *Corrected 2026-08-04 (codebase audit).*)* -/
theorem shearEvolve_not_continuous [NeZero N] (hN : 2 ≤ N) :
    ¬ Continuous (shearEvolve (basinIndex (momentContext N)) (0 : ℝ) 1) := by
  intro hcont
  classical
  set idx : LF4.KSigma N → Fin N := basinIndex (momentContext N) with hidx
  set r₀ : LF4.KTorus := (0, 0) with hr₀
  set g : LF4.KSigma N → LF4.KTorus := fun x => pshift (shearAmt N (idx x)) r₀ with hg
  have hgeq : (fun x : LF4.KSigma N => (shearEvolve idx 0 1 (x, r₀)).2) = g := by
    funext x
    simp [shearEvolve, elapsed, g]
  have hgc : Continuous g := by
    rw [← hgeq]
    exact (hcont.comp (Continuous.prodMk continuous_id continuous_const)).snd
  -- the two witnesses
  have h2 : (1 : ℕ) < N := hN
  set j0 : Fin N := ⟨0, by omega⟩ with hj0
  set j1 : Fin N := ⟨1, by omega⟩ with hj1
  have hj01 : j0 ≠ j1 := by
    intro h
    exact absurd (congrArg Fin.val h) (by simp [j0, j1])
  have hx0 : idx (vertexPoint j0, r₀) = j0 :=
    basinIndex_eq_of_mem (vertex_mem_globalBasin j0 r₀)
  have hx1 : idx (vertexPoint j1, r₀) = j1 :=
    basinIndex_eq_of_mem (vertex_mem_globalBasin j1 r₀)
  -- the fibre over the j0-displacement is exactly the j0-basin, closed and open
  have hfibre : g ⁻¹' {pshift (shearAmt N j0) r₀} = idx ⁻¹' {j0} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, g]
    constructor
    · intro h
      exact pshift_shearAmt_inj N r₀ h
    · intro h
      rw [h]
  have hclosed : IsClosed (idx ⁻¹' {j0}) := by
    rw [← hfibre]
    exact isClosed_singleton.preimage hgc
  have hopen : IsOpen (idx ⁻¹' {j0}) := by
    rw [← isClosed_compl_iff]
    have hcompl : (idx ⁻¹' {j0})ᶜ
        = g ⁻¹' ((fun i => pshift (shearAmt N i) r₀) '' {i : Fin N | i ≠ j0}) := by
      ext x
      simp only [mem_compl_iff, mem_preimage, mem_singleton_iff, mem_image, mem_ofPred_eq, g]
      constructor
      · intro h
        exact ⟨idx x, h, rfl⟩
      · rintro ⟨i, hi, hix⟩
        intro h0
        exact hi (pshift_shearAmt_inj N r₀ hix.symm ▸ h0 ▸ rfl)
    rw [hcompl]
    exact (((Set.toFinite _).image _).isClosed).preimage hgc
  -- clopen, nonempty, proper: contradiction with connectedness
  have hclopen : IsClopen (idx ⁻¹' {j0}) := ⟨hclosed, hopen⟩
  rcases isClopen_iff.mp hclopen with hempty | huniv
  · have hm : ((vertexPoint j0, r₀) : LF4.KSigma N) ∈ idx ⁻¹' {j0} := by
      simp [hx0]
    rw [hempty] at hm
    exact Set.notMem_empty _ hm
  · have hm : ((vertexPoint j1, r₀) : LF4.KSigma N) ∈ idx ⁻¹' {j0} := by
      rw [huniv]
      exact mem_univ _
    have h10 : j1 = j0 := by simpa [hx1] using hm
    exact hj01 h10.symm

end CSD.RecordLayer
