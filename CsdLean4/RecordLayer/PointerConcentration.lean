/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.MacrostateStability

/-!
# Where the overwhelming majority comes from: nearness to a pointer ray

**Category:** 7-SigmaLayer (the record layer — Paper C A7).
BACKLOG #105(a), out of #103.

[`MacrostateStability.lean`](MacrostateStability.lean) (#103) proved the majority half of what makes
#102's record string *macroscopic*, but **conditionally**: ★★ `measure_robustBasin_ge_one_sub` needs
`1 − ε ≤ c.rate p i`, and #103 recorded why the hypothesis cannot be dropped — `globalBasin_prob`
makes a cell's measure *exactly* its Born weight, so no cell is overwhelming unless the weights are.
"Overwhelmingly many microstates share the record" is therefore a statement about the **preparation
and the apparatus**, not about the coordinate.

This file supplies the hypothesis for the canonical apparatus, and gives it a geometric reading.

## What is proved

* `offPointer i ψ` — the component of a preparation orthogonal to the `i`-th **pointer ray**, with
  ★ `norm_offPointer_sq`: `‖offPointer i ψ‖² = ‖ψ‖² − ‖ψ i‖²`, so the defect *is* the missing Born
  weight;
* ★ `momentMap_mk_eq_coord_sq` — for a unit preparation the canonical context's rate is the squared
  coordinate, and hence ★★ `one_sub_le_momentMap_of_near_pointer`: **a preparation within `√ε` of the
  pointer ray has rate at least `1 − ε` there**. This is the concentration hypothesis, read as a
  distance;
* ★★★ `measure_robustBasin_ge_of_near_pointer` and the distance form ★★★
  `measure_robustBasin_ge_of_dist_le` — **near a pointer ray the record macrostate is both
  overwhelming and robust**: the cell of outcome `i`, restricted to the microstates robust to a
  record write of size `δ`, carries all but `ε + δ` of the epistemic measure. This is #105's
  statement for the canonical apparatus, obtained by feeding the geometry into #103;
* ★★ `measure_globalBasin_ge_of_near_pointer` — the same without the robustness margin, and ★★★
  `measure_map_recordMacro_ge_of_near_pointer` — **the macroscopic law of #102's record string puts
  all but `ε` of its mass on one string**, which is the form "almost every microstate records the
  same outcome" takes in the macroscopic law;
* ★ `offPointer_single` and ★★ `measure_robustBasin_ge_of_pointer` — **non-vacuity**: at the pointer
  state itself the defect is zero and the robust cell carries `1 − δ`, so the hypothesis is
  satisfiable and the bound is not empty.

## Honest scope

⚠️ **Nothing here drives the base to a pointer ray.** The concentration is a property of *where the
preparation sits*, supplied as a hypothesis with a geometric meaning; no dynamics is shown to produce
it, and that — a decoherence or pointer-selection model whose rate field concentrates — is BACKLOG
#106 and is the hard half of #105. Reading any statement below as "decoherence gives the macrostate"
would be exactly the overclaim this file is written to avoid.

⚠️ **It is still not `fs_chebyshev_concentration`.**
[`Thermo/CanonicalTypicality.lean`](../Thermo/CanonicalTypicality.lean) concentrates a *base
statistic* over the projective space with a polynomial rate; this file is about one preparation's
weight vector at one base point. The two are different statements about different objects and no
theorem joins them.

⚠️ **Only the canonical pointer basis.** `momentContext` is the standard-basis context, so "pointer
ray" means a coordinate ray of `EuclideanSpace ℂ (Fin N)`. A general apparatus enters by transporting
the base point with the corresponding unitary, and **that transport is not constructed here**: no
`ContextField` built from an arbitrary orthonormal basis appears in the corpus, so nothing below is
stated for one.

⚠️ **A near-pointer preparation is a special preparation.** For a generic superposition no cell is
overwhelming, and that is correct physics rather than a gap: the bound degrades exactly as the Born
weights spread, and `measure_robustBasin_ge_of_dist_le` is vacuous once `r² + δ ≥ 1`. The content is
the *rate* at which macroscopicity is bought with nearness to the pointer, not a claim that record
macrostates are generically overwhelming.

⚠️ **One context.** The statements are about a single context's basin, not about a record string of
several contexts; #103's `measure_robustBasin_ge_one_sub` is per-context and so is everything here.
Nothing is claimed about a joint cell of two contexts, where #102's contextuality warning applies.

References: [`records-to-spacetime-scoping.md`](../../specs/records-to-spacetime-scoping.md) `ST-3`;
[`future-work.md`](../../specs/future-work.md); `MacrostateStability.lean` (#103),
`RecordMacrostate.lean` (#102), `GlobalBasin.lean`, `LF4/MomentMap.lean`;
`specs/BACKLOG.md` #105, #106, #103, #102.
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

variable {N : ℕ}

/-! ### The defect from a pointer ray -/

/-- **The component of a preparation orthogonal to the `i`-th pointer ray.** Its norm measures how
far the preparation is from being a definite pointer state for the canonical apparatus. -/
noncomputable def offPointer (i : Fin N) (ψ : EuclideanSpace ℂ (Fin N)) :
    EuclideanSpace ℂ (Fin N) :=
  ψ - (ψ i) • EuclideanSpace.single i (1 : ℂ)

theorem offPointer_apply (i : Fin N) (ψ : EuclideanSpace ℂ (Fin N)) (j : Fin N) :
    offPointer i ψ j = if j = i then 0 else ψ j := by
  classical
  by_cases h : j = i
  · subst h
    simp [offPointer]
  · simp [offPointer, h]

/-- ★ **The defect is exactly the missing Born weight.** Parseval in coordinates: removing the
pointer component removes `‖ψ i‖²` from the squared norm and nothing else. -/
theorem norm_offPointer_sq (i : Fin N) (ψ : EuclideanSpace ℂ (Fin N)) :
    ‖offPointer i ψ‖ ^ 2 = ‖ψ‖ ^ 2 - ‖ψ i‖ ^ 2 := by
  classical
  rw [LF4.euclidean_norm_sq_eq_sum, LF4.euclidean_norm_sq_eq_sum,
    Finset.sum_congr rfl fun j _ => by rw [offPointer_apply i ψ j],
    ← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]
  have hsum : ∀ j ∈ Finset.univ.erase i,
      ‖if j = i then (0 : ℂ) else ψ j‖ ^ 2 = ‖ψ j‖ ^ 2 := by
    intro j hj
    rw [if_neg (Finset.ne_of_mem_erase hj)]
  rw [Finset.sum_congr rfl hsum]
  simp

@[simp] theorem offPointer_single (i : Fin N) :
    offPointer i (EuclideanSpace.single i (1 : ℂ)) = 0 := by
  classical
  ext j
  rw [offPointer_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-! ### Nearness to a pointer ray is the concentration hypothesis -/

/-- ★ **The canonical context's rate at a unit preparation is the squared coordinate.** -/
theorem momentMap_mk_eq_coord_sq (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (i : Fin N) : LF4.momentMap (Projectivization.mk ℂ ψ hψ0) i = ‖ψ i‖ ^ 2 := by
  rw [LF4.momentMap_mk_eq_inner_sq ψ hψ0 hψ i, EuclideanSpace.inner_single_left, map_one, one_mul]

/-- ★★ **A preparation within `√ε` of the pointer ray has rate at least `1 − ε` there.** This is the
concentration hypothesis of #103, with a geometric reading: the weight that is missing from the
pointer outcome is exactly the squared distance to its ray. -/
theorem one_sub_le_momentMap_of_near_pointer {ψ : EuclideanSpace ℂ (Fin N)} (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (i : Fin N) {ε : ℝ} (hnear : ‖offPointer i ψ‖ ^ 2 ≤ ε) :
    1 - ε ≤ LF4.momentMap (Projectivization.mk ℂ ψ hψ0) i := by
  rw [momentMap_mk_eq_coord_sq ψ hψ0 hψ i]
  have h := norm_offPointer_sq i ψ
  rw [hψ, one_pow] at h
  linarith [h ▸ hnear]

/-! ### The macrostate near a pointer ray -/

/-- ★★★ **Near a pointer ray the record macrostate is overwhelming and robust.** The cell of outcome
`i`, cut down to the microstates robust to a record write of size `δ`, carries all but `ε + δ` of the
epistemic measure — where `ε` bounds the squared distance from the preparation to the pointer ray.
This is #105's statement for the canonical apparatus: the two halves of "macroscopic" — many
microstates, and stable ones — hold together, with the geometry of the preparation as the only
input. -/
theorem measure_robustBasin_ge_of_near_pointer {ψ : EuclideanSpace ℂ (Fin N)} (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (i : Fin N) {δ ε : ℝ} (hδ : 0 ≤ δ) (hnear : ‖offPointer i ψ‖ ^ 2 ≤ ε) :
    ENNReal.ofReal (1 - ε - δ)
      ≤ epistemicMeasure (Projectivization.mk ℂ ψ hψ0) (robustBasin (momentContext N) δ i) := by
  refine measure_robustBasin_ge_one_sub (momentContext N) hδ i _ ?_
  rw [momentContext_rate]
  exact one_sub_le_momentMap_of_near_pointer hψ0 hψ i hnear

/-- ★★★ **The same, read as a distance.** A preparation within `r` of the pointer ray gives a robust
macrostate cell of measure at least `1 − r² − δ`. ⚠️ Vacuous once `r² + δ ≥ 1`: macroscopicity is
bought with nearness to the pointer, at this rate and no better. -/
theorem measure_robustBasin_ge_of_dist_le {ψ : EuclideanSpace ℂ (Fin N)} (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (i : Fin N) {δ r : ℝ} (hδ : 0 ≤ δ) (hr : ‖offPointer i ψ‖ ≤ r) :
    ENNReal.ofReal (1 - r ^ 2 - δ)
      ≤ epistemicMeasure (Projectivization.mk ℂ ψ hψ0) (robustBasin (momentContext N) δ i) :=
  measure_robustBasin_ge_of_near_pointer hψ0 hψ i hδ
    (pow_le_pow_left₀ (norm_nonneg _) hr 2)

/-- ★★ **Without the robustness margin**: the basin of the pointer outcome carries all but `ε`. -/
theorem measure_globalBasin_ge_of_near_pointer {ψ : EuclideanSpace ℂ (Fin N)} (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (i : Fin N) {ε : ℝ} (hnear : ‖offPointer i ψ‖ ^ 2 ≤ ε) :
    ENNReal.ofReal (1 - ε)
      ≤ epistemicMeasure (Projectivization.mk ℂ ψ hψ0) (globalBasin (momentContext N) i) := by
  rw [globalBasin_prob, momentContext_rate]
  exact ENNReal.ofReal_le_ofReal (one_sub_le_momentMap_of_near_pointer hψ0 hψ i hnear)

/-- ★★★ **The macroscopic law puts all but `ε` of its mass on one record string.** #102's
`recordMacro` for the one-context family, read at a near-pointer preparation: almost every microstate
records the same outcome, in the macroscopic law rather than microscopically. -/
theorem measure_map_recordMacro_ge_of_near_pointer {ψ : EuclideanSpace ℂ (Fin N)} (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (i : Fin N) {ε : ℝ} (hnear : ‖offPointer i ψ‖ ^ 2 ≤ ε) :
    ENNReal.ofReal (1 - ε)
      ≤ ((epistemicMeasure (Projectivization.mk ℂ ψ hψ0)).map
            (recordMacro (fun _ : Fin 1 => momentContext N)).toFun)
          {v : Fin 1 → Fin (N + 1) | v 0 = i.succ} := by
  rw [measure_map_recordMacro_singleton (momentContext N) i _, momentContext_rate]
  exact ENNReal.ofReal_le_ofReal (one_sub_le_momentMap_of_near_pointer hψ0 hψ i hnear)

/-- ★★ **Non-vacuity: at the pointer state the robust cell carries `1 − δ`.** The hypothesis of the
theorems above is satisfiable with `ε = 0`, so the bounds are not empty. -/
theorem measure_robustBasin_ge_of_pointer (i : Fin N) {δ : ℝ} (hδ : 0 ≤ δ)
    (hψ0 : (EuclideanSpace.single i (1 : ℂ) : EuclideanSpace ℂ (Fin N)) ≠ 0) :
    ENNReal.ofReal (1 - δ)
      ≤ epistemicMeasure (Projectivization.mk ℂ _ hψ0)
          (robustBasin (momentContext N) δ i) := by
  have h := measure_robustBasin_ge_of_near_pointer (ψ := EuclideanSpace.single i (1 : ℂ)) hψ0
    (by simp) i (ε := 0) hδ (by simp)
  simpa using h

end CSD.RecordLayer

end
