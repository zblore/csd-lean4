/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.CliffordTDensity
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# SU(2) is compact, so the Clifford+T words contain a finite `ε`-net

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).
BACKLOG #113, the second brick of #74's split.

Solovay–Kitaev's base case needs a **finite** set of words within `ε₀` of every target. #81 gives
density (`det_one_mem_cliffordTLim`), and density alone gives *one word per target* — a set with no
finiteness and no bound. Compactness is what upgrades it, and that is all this file does.

## What is proved

* ★★ `IsCompact.exists_finite_net` — the general statement, in any metric space: **a compact set
  inside the closure of `D` is covered by finitely many `ε`-balls centred in `D`**. Density plus
  compactness gives a finite net; neither alone does;
* ★ `isClosed_unitaryGroup` — the unitary group of any finite index type is closed, as the preimage
  of `{1}` under `U ↦ U⋆U`. Mathlib has `IsCompact.matrix` for entrywise-compact sets but nothing
  about the unitary group, so this is new here;
* ★★ `isCompact_su2Set` — **the special unitary `2 × 2` matrices are compact**: closed (the unitary
  condition and `det = 1` are both closed conditions) and inside the closed unit ball, because a
  unitary has operator norm `1` in the C\*-norm;
* ★★★ `exists_finite_cliffordT_net` — **the base case**: for every `ε > 0` there is a `Finset` of
  genuine Clifford+T *words* such that every determinant-one unitary is within `ε` of one of them.

## Honest scope

⚠️ **Existence, not construction.** The net comes from `elim_finite_subcover`, so nothing here
bounds its cardinality or the length of its words. That is not a gap to be filled later by the same
argument: it is *why* Solovay–Kitaev needs a recursion on top of the net (#115), and why the net is
the `O(1)` base of the algorithm rather than the algorithm.

⚠️ **`ε₀` is not calibrated.** The recursion needs the base accuracy to be below the contraction
threshold of #112 (`δ < 1/2`); this file produces a net for *every* `ε`, and choosing the one the
recursion wants is #115's business.

⚠️ **The route is not the one #113 recorded.** The row proposed the `su2` parametrisation — SU(2) as
the continuous image of the unit sphere in `ℝ⁴` — which would need the *surjectivity* of that
parametrisation onto the determinant-one unitaries, and the corpus has no such statement. Closed and
bounded in a finite-dimensional space is shorter and needs nothing new, so that is what is used; the
sphere picture appears nowhere below.

⚠️ **Modulo phase is not addressed.** The net is for `det = 1`; the phase quotient of
`exists_phase_mem_cliffordTLim` is untouched, as in #81.

References: C. Dawson, M. Nielsen, *The Solovay-Kitaev algorithm*, Quantum Inf. Comput. 6 (2006) 81,
§3 (the `ε₀`-net as the base case); M. Nielsen, I. Chuang, *Quantum Computation and Quantum
Information*, Appendix 3; `CliffordTDensity.lean` (#81), `GroupCommutator.lean` (#112);
`specs/BACKLOG.md` #113, #74, #81, #112, #115, #116.
-/

@[expose] public section

open Matrix Metric Set

open scoped Matrix.Norms.L2Operator

/-! ### Density plus compactness gives a finite net -/

/-- ★★ **A compact set inside the closure of `D` has a finite `ε`-net drawn from `D`.** Density on
its own gives one point of `D` per target; compactness is what makes finitely many of them enough. -/
theorem IsCompact.exists_finite_net {X : Type*} [MetricSpace X] {K D : Set X} (hK : IsCompact K)
    (hKD : K ⊆ closure D) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset X, (↑F : Set X) ⊆ D ∧ ∀ x ∈ K, ∃ y ∈ F, dist x y < ε := by
  have hcover : K ⊆ ⋃ y ∈ D, ball y ε := by
    intro x hx
    obtain ⟨y, hyD, hdist⟩ := Metric.mem_closure_iff.1 (hKD hx) ε hε
    exact mem_biUnion hyD (by rwa [mem_ball])
  obtain ⟨b, hbD, hbfin, hbcover⟩ :=
    hK.elim_finite_subcover_image (fun _ _ => isOpen_ball) hcover
  refine ⟨hbfin.toFinset, ?_, ?_⟩
  · intro y hy
    exact hbD (hbfin.mem_toFinset.1 hy)
  · intro x hx
    obtain ⟨y, hyb, hxy⟩ := Set.mem_iUnion₂.1 (hbcover hx)
    exact ⟨y, hbfin.mem_toFinset.2 hyb, mem_ball.1 hxy⟩

namespace QuantumInfo.SU2

/-! ### The unitary group is closed -/

/-- ★ **The unitary group is closed**, as the preimage of `{1}` under `U ↦ U U⋆`. -/
theorem isClosed_unitaryGroup {n : Type*} [Fintype n] [DecidableEq n] :
    IsClosed (Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ)) := by
  have hset : (Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ))
      = (fun U : Matrix n n ℂ => U * star U) ⁻¹' {1} := by
    ext U
    simp [Matrix.mem_unitaryGroup_iff]
  rw [hset]
  exact isClosed_singleton.preimage (continuous_id.mul continuous_star)

/-! ### SU(2) is compact -/

/-- The determinant-one unitaries: the target set Solovay–Kitaev approximates. -/
def su2Set : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {U | U ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ U.det = 1}

theorem isClosed_su2Set : IsClosed su2Set := by
  have hset : su2Set = (Matrix.unitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ))
      ∩ (fun U : Matrix (Fin 2) (Fin 2) ℂ => U.det) ⁻¹' {1} := rfl
  rw [hset]
  exact isClosed_unitaryGroup.inter (isClosed_singleton.preimage continuous_id.matrix_det)

/-- A unitary has operator norm `1`, so the target set sits in the closed unit ball. -/
theorem su2Set_subset_closedBall :
    su2Set ⊆ closedBall (0 : Matrix (Fin 2) (Fin 2) ℂ) 1 := by
  intro U hU
  rw [mem_closedBall_zero_iff, CStarRing.norm_of_mem_unitary hU.1]

/-- ★★ **The special unitary `2 × 2` matrices are compact**: closed, and bounded because a unitary
has operator norm `1`. -/
theorem isCompact_su2Set : IsCompact su2Set :=
  (isCompact_closedBall (0 : Matrix (Fin 2) (Fin 2) ℂ) 1).of_isClosed_subset
    isClosed_su2Set su2Set_subset_closedBall

/-! ### The base case -/

/-- #81's density, as an inclusion of sets. -/
theorem su2Set_subset_closure_cliffordT :
    su2Set ⊆ closure (cliffordT : Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
  fun _ hU => det_one_mem_cliffordTLim hU.1 hU.2

/-- ★★★ **The base case of Solovay–Kitaev.** For every `ε > 0` there are **finitely many** genuine
Clifford+T words such that every determinant-one unitary is within `ε` of one of them.

Density (#81) gives one word per target; compactness of the target set turns that into a finite
list. ⚠️ Existence only — the net's size and its words' lengths are not bounded here, which is
exactly why the recursion is needed on top of it. -/
theorem exists_finite_cliffordT_net {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset (Matrix (Fin 2) (Fin 2) ℂ),
      (∀ A ∈ F, A ∈ cliffordT) ∧ ∀ U ∈ su2Set, ∃ A ∈ F, dist U A < ε := by
  obtain ⟨F, hFsub, hFnet⟩ :=
    isCompact_su2Set.exists_finite_net su2Set_subset_closure_cliffordT hε
  exact ⟨F, fun A hA => hFsub hA, hFnet⟩

end QuantumInfo.SU2

end
