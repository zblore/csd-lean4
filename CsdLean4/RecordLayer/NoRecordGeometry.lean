/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.SharpenedNoGo
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudy

/-!
# RecordLayer/NoRecordGeometry: the no-record set is inside the closure of its interior

**Category:** 7-SigmaLayer (regularity of pointer record-region complements).

## The gap this closes

`posMeasure_noRecord_of_correlates` (`SharpenedNoGo.lean`) assumes that the complement of
two disjoint open sets is contained in the closure of its interior (`hreg`). This module
proves regularity of the full no-record set, then groups one record region against all
the others to obtain a positive-measure set of inputs whose outputs avoid every record.
Continuity, openness, an open preconnected ready set and attainment of two distinct
outcomes remain hypotheses of the resulting theorem.

## The construction: feed weight into the ready component

For `q = [v]` with the relevant record moments `m_{j+1}(q) ≤ 1/2`, perturb `v` by replacing
its ready component `v 0` with a slightly larger one (`feedReady`):

* every **record numerator** `‖v (j+1)‖²` is untouched (`feedReady_succ`),
* the **norm strictly grows** (`norm_sq_feedReady_gt`),
* hence every positive relevant record moment **strictly decreases**, and all relevant
  moments are `< 1/2` (a moment with zero numerator stays `0 < 1/2`).

The replacement family is phase-preserving where it matters: if `v 0 ≠ 0` we scale it by
`1 + 1/(n+1)` (same phase, so convergence to `v` is immediate — no chart argument); if
`v 0 = 0` we insert the real weight `1/(n+1)` (converging to `0 = v 0`). Either way
`feedReady v (c n) → v`, so the perturbed rays converge to `q` through the continuous
quotient map `Projectivization.mk'`, and `q` lies in the closure of the strict set
(`mem_closure_of_tendsto`).

★ `mk_mem_closure_strictNoRecord` / `noRecord_subset_closure_strict` — the core, for an
  arbitrary index set `S` (so one proof serves both consumers below).
★ `noRecord_subset_closure_interior` — the B5-geom statement: the full no-record set
  `(⋃ j, recordRegion j)ᶜ` is contained in the closure of its interior.
★★ `posMeasure_noRecord_pointer` — ready inputs whose outputs lie in the interior of the
  complement of **all record regions** have positive Fubini–Study measure, under
  the stated dynamical and ready-set hypotheses. The geometric regularity input is proved.
* `not_ae_record_pointer` — exact records cannot hold almost everywhere for Fubini–Study
  measure restricted to that ready set, under the same hypotheses.

## Honest scope

The closure lemmas cover both the full no-record set and a selected pair's complement.
The final positive-measure theorem uses the **full complement** for arbitrary `K`;
the two selected indices witness attainment of distinct outcomes, not exhaustion of them.

The obstruction is conditional on the propagator and ready-set
hypotheses. It does not classify alternative calibrations or prove that Dirac calibration
is necessary. General trilemma exhaustiveness over other arenas is not proved here.

## References

`specs/BACKLOG.md` B5, B5-geom (historical motivation) and Q13 (general trilemma exhaustiveness);
`specs/future-work.md`;
`RecordLayer/SharpenedNoGo.lean` (`posMeasure_noRecord_of_correlates`, whose `hreg` this
discharges); `RecordLayer/PointerArena.lean` (`recordRegion`, the moment-region geometry);
`RecordLayer/NullSeamWitness.lean` (the Dirac-calibrated witness);
`docs/TOUR.md` §"Which horn is the right one?".
-/

@[expose] public section

namespace CSD.RecordLayer

open Filter Topology MeasureTheory Matrix.UnitaryGroup

variable {K : ℕ}

/-! ### The perturbation: feed weight into the ready component -/

/-- Replace the ready component of `v` by `c`, leaving every record component untouched.
The later lemmas choose replacements of strictly larger norm converging to `v 0`, so
boundary no-record rays are approximated by rays in the strict no-record set. -/
noncomputable def feedReady (v : EuclideanSpace ℂ (Fin (K + 1))) (c : ℂ) :
    EuclideanSpace ℂ (Fin (K + 1)) :=
  WithLp.toLp 2 (Function.update (WithLp.ofLp v) 0 c)

/-- Components away from the ready index are untouched. -/
lemma feedReady_of_ne (v : EuclideanSpace ℂ (Fin (K + 1))) (c : ℂ) {i : Fin (K + 1)}
    (hi : i ≠ 0) : feedReady v c i = v i := by
  show Function.update (WithLp.ofLp v) 0 c i = v i
  exact Function.update_of_ne hi c (WithLp.ofLp v)

/-- Record components are untouched: the record numerators are fixed. -/
lemma feedReady_succ (v : EuclideanSpace ℂ (Fin (K + 1))) (c : ℂ) (j : Fin K) :
    feedReady v c j.succ = v j.succ :=
  feedReady_of_ne v c (Fin.succ_ne_zero j)

/-- The ready component is replaced. -/
lemma feedReady_zero (v : EuclideanSpace ℂ (Fin (K + 1))) (c : ℂ) :
    feedReady v c 0 = c := rfl

/-- Feeding the original component back is the identity. -/
lemma feedReady_self (v : EuclideanSpace ℂ (Fin (K + 1))) : feedReady v (v 0) = v :=
  congrArg (WithLp.toLp 2) (Function.update_eq_self 0 (WithLp.ofLp v))

/-- **The norm strictly grows** when the ready component does: split the sum at `0`; the
erased part is untouched. -/
lemma norm_sq_feedReady_gt (v : EuclideanSpace ℂ (Fin (K + 1))) {c : ℂ}
    (hc : ‖v 0‖ < ‖c‖) : ‖v‖ ^ 2 < ‖feedReady v c‖ ^ 2 := by
  have herase : ∑ i ∈ Finset.univ.erase 0, ‖feedReady v c i‖ ^ 2
      = ∑ i ∈ Finset.univ.erase 0, ‖v i‖ ^ 2 :=
    Finset.sum_congr rfl fun i hi => by
      rw [feedReady_of_ne v c (Finset.ne_of_mem_erase hi)]
  calc ‖v‖ ^ 2
      = ‖v 0‖ ^ 2 + ∑ i ∈ Finset.univ.erase 0, ‖v i‖ ^ 2 := by
        rw [LF4.euclidean_norm_sq_eq_sum]
        exact (Finset.add_sum_erase Finset.univ (fun i => ‖v i‖ ^ 2)
          (Finset.mem_univ (0 : Fin (K + 1)))).symm
    _ < ‖c‖ ^ 2 + ∑ i ∈ Finset.univ.erase 0, ‖v i‖ ^ 2 := by
        have hsq : ‖v 0‖ ^ 2 < ‖c‖ ^ 2 :=
          pow_lt_pow_left₀ hc (norm_nonneg _) two_ne_zero
        linarith
    _ = ‖feedReady v c 0‖ ^ 2 + ∑ i ∈ Finset.univ.erase 0, ‖feedReady v c i‖ ^ 2 := by
        rw [feedReady_zero, herase]
    _ = ‖feedReady v c‖ ^ 2 := by
        rw [LF4.euclidean_norm_sq_eq_sum]
        exact Finset.add_sum_erase Finset.univ (fun i => ‖feedReady v c i‖ ^ 2)
          (Finset.mem_univ (0 : Fin (K + 1)))

/-- The perturbed vector is nonzero: its norm-square strictly exceeds a nonnegative one. -/
lemma feedReady_ne_zero (v : EuclideanSpace ℂ (Fin (K + 1))) {c : ℂ}
    (hc : ‖v 0‖ < ‖c‖) : feedReady v c ≠ 0 := by
  intro h0
  have h := norm_sq_feedReady_gt v hc
  rw [h0, norm_zero] at h
  nlinarith [sq_nonneg ‖v‖]

/-- As the fed component tends to `v 0`, the perturbed vectors tend to `v`. -/
lemma tendsto_feedReady (v : EuclideanSpace ℂ (Fin (K + 1))) {c : ℕ → ℂ}
    (hlim : Tendsto c atTop (𝓝 (v 0))) :
    Tendsto (fun n => feedReady v (c n)) atTop (𝓝 v) := by
  have hcont : Continuous fun z : ℂ => feedReady v z := by
    unfold feedReady
    fun_prop
  have h := (hcont.tendsto (v 0)).comp hlim
  rwa [feedReady_self] at h

/-! ### The closure argument on rays -/

/-- ★ **The core**: a ray whose `S`-indexed record moments are all `≤ 1/2` lies in the
closure of the set where they are all `< 1/2`, along any feeding family that strictly
enlarges the ready component while converging to it. The record numerators are fixed
(`feedReady_succ`) while the norm strictly grows (`norm_sq_feedReady_gt`), so positive
relevant moments decrease and zero moments remain below `1/2`; convergence passes through
`Projectivization.mk'`. -/
theorem mk_mem_closure_strictNoRecord (S : Set (Fin K))
    (v : EuclideanSpace ℂ (Fin (K + 1))) (hv : v ≠ 0)
    (hle : ∀ j ∈ S, LF4.momentMap (Projectivization.mk ℂ v hv) j.succ ≤ 1 / 2)
    (c : ℕ → ℂ) (hgt : ∀ n, ‖v 0‖ < ‖c n‖) (hlim : Tendsto c atTop (𝓝 (v 0))) :
    Projectivization.mk ℂ v hv ∈
      closure {q : Pointer K | ∀ j ∈ S, LF4.momentMap q j.succ < 1 / 2} := by
  have hne : ∀ n, feedReady v (c n) ≠ 0 := fun n => feedReady_ne_zero v (hgt n)
  refine mem_closure_of_tendsto
    (f := fun n => Projectivization.mk ℂ (feedReady v (c n)) (hne n)) (b := atTop) ?_ ?_
  · -- the perturbed rays converge to the ray, via the nonzero subtype and `mk'`
    have hsub : Tendsto (fun n => (⟨feedReady v (c n), hne n⟩ :
        {u : EuclideanSpace ℂ (Fin (K + 1)) // u ≠ 0})) atTop (𝓝 ⟨v, hv⟩) :=
      tendsto_subtype_rng.mpr (tendsto_feedReady v hlim)
    exact (Projectivization.continuous_mk'.tendsto ⟨v, hv⟩).comp hsub
  · -- every perturbed ray lies in the strict set
    refine Eventually.of_forall fun n => ?_
    intro j hj
    rw [LF4.momentMap_mk, feedReady_succ]
    rcases eq_or_ne (v j.succ) 0 with hz | hz
    · rw [hz, norm_zero, zero_pow two_ne_zero, zero_div]
      norm_num
    · have h1 : 0 < ‖v j.succ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz) 2
      have h2 : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv) 2
      have h4 := div_lt_div_of_pos_left h1 h2 (norm_sq_feedReady_gt v (hgt n))
      have h5 := hle j hj
      rw [LF4.momentMap_mk] at h5
      linarith

/-- ★ **The `≤`-set is inside the closure of the `<`-set**, for any index set `S` of record
moments. The two feeding branches: if `v 0 = 0`, insert the real weight `1/(n+1)`; else
scale `v 0` by `1 + 1/(n+1)` — phase-preserving, so the limit is immediate. -/
theorem noRecord_subset_closure_strict (S : Set (Fin K)) :
    {q : Pointer K | ∀ j ∈ S, LF4.momentMap q j.succ ≤ 1 / 2} ⊆
      closure {q : Pointer K | ∀ j ∈ S, LF4.momentMap q j.succ < 1 / 2} := by
  intro q
  induction q using Projectivization.ind with
  | h v hv =>
    intro hq
    rcases eq_or_ne (v 0) 0 with h0 | h0
    · -- ready component vanishes: feed in the real weight `1/(n+1)`
      refine mk_mem_closure_strictNoRecord S v hv hq
        (fun n => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) (fun n => ?_) ?_
      · rw [h0, norm_zero, Complex.norm_real]
        exact norm_pos_iff.mpr (by positivity)
      · rw [h0]
        have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h2 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop
            (𝓝 ((0 : ℝ) : ℂ)) := (Complex.continuous_ofReal.tendsto 0).comp h1
        rwa [Complex.ofReal_zero] at h2
    · -- ready component present: scale it by `1 + 1/(n+1)`, keeping the phase
      refine mk_mem_closure_strictNoRecord S v hv hq
        (fun n => (1 + 1 / ((n : ℝ) + 1)) • v 0) (fun n => ?_) ?_
      · have ht : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
        have hv0 : 0 < ‖v 0‖ := norm_pos_iff.mpr h0
        nlinarith
      · have h1 : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
        rw [add_zero] at h1
        have h2 := h1.smul_const (v 0)
        rwa [one_smul] at h2

/-! ### The record-region geometry, discharged -/

/-- ★ **B5-geom**: the full no-record set is contained in the closure of its interior. A
state with every record moment `≤ 1/2` is approximated by states with every record moment
`< 1/2` — obtained by feeding weight toward the ready vertex — and the strict set is open,
hence inside the interior. -/
theorem noRecord_subset_closure_interior :
    (⋃ j, recordRegion (K := K) j)ᶜ ⊆
      closure (interior ((⋃ j, recordRegion (K := K) j)ᶜ)) := by
  intro q hq
  have hq' : ∀ m ∈ (Set.univ : Set (Fin K)), LF4.momentMap q m.succ ≤ 1 / 2 := by
    intro m _
    by_contra hgt
    rw [not_le] at hgt
    exact hq (Set.mem_iUnion.mpr ⟨m, hgt⟩)
  have hcl := noRecord_subset_closure_strict (Set.univ : Set (Fin K)) hq'
  refine closure_mono (interior_maximal ?_ ?_) hcl
  · -- the strict set avoids every record region
    intro p hp hmem
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hmem
    have h1 : LF4.momentMap p m.succ < 1 / 2 := hp m (Set.mem_univ m)
    have h2 : (1 : ℝ) / 2 < LF4.momentMap p m.succ := hm
    linarith
  · -- and it is open: a finite intersection of open moment sublevels
    have hset : {p : Pointer K | ∀ m ∈ (Set.univ : Set (Fin K)),
        LF4.momentMap p m.succ < 1 / 2}
        = ⋂ m : Fin K, {p : Pointer K | LF4.momentMap p m.succ < 1 / 2} := by
      ext p
      simp
    rw [hset]
    exact isOpen_iInter_of_finite fun m =>
      isOpen_lt (LF4.continuous_momentMap m.succ) continuous_const

/-- ★ The pair form `posMeasure_noRecord_of_correlates` consumes: the complement of a union
of two record regions is regular (contained in the closure of its interior). -/
theorem recordRegion_pair_compl_regular (j l : Fin K) :
    (recordRegion (K := K) j ∪ recordRegion l)ᶜ ⊆
      closure (interior ((recordRegion (K := K) j ∪ recordRegion l)ᶜ)) := by
  intro q hq
  have hq' : ∀ m ∈ ({j, l} : Set (Fin K)), LF4.momentMap q m.succ ≤ 1 / 2 := by
    intro m hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    by_contra hgt
    rw [not_le] at hgt
    rcases hm with rfl | rfl
    · exact hq (Set.mem_union_left _ hgt)
    · exact hq (Set.mem_union_right _ hgt)
  have hcl := noRecord_subset_closure_strict ({j, l} : Set (Fin K)) hq'
  have hset : {p : Pointer K | ∀ m ∈ ({j, l} : Set (Fin K)),
      LF4.momentMap p m.succ < 1 / 2}
      = {p : Pointer K | LF4.momentMap p j.succ < 1 / 2} ∩
        {p : Pointer K | LF4.momentMap p l.succ < 1 / 2} := by
    ext p
    simp
  rw [hset] at hcl
  refine closure_mono (interior_maximal ?_ ?_) hcl
  · intro p hp hmem
    obtain ⟨hpj, hpl⟩ := hp
    have hj' : LF4.momentMap p j.succ < 1 / 2 := hpj
    have hl' : LF4.momentMap p l.succ < 1 / 2 := hpl
    rcases (Set.mem_union _ _ _).mp hmem with hj | hl
    · have h2 : (1 : ℝ) / 2 < LF4.momentMap p j.succ := hj
      linarith
    · have h2 : (1 : ℝ) / 2 < LF4.momentMap p l.succ := hl
      linarith
  · exact (isOpen_lt (LF4.continuous_momentMap j.succ) continuous_const).inter
      (isOpen_lt (LF4.continuous_momentMap l.succ) continuous_const)

/-- **Positive measure of ready inputs whose outputs avoid every record region.**
Assume a continuous open map reaches two distinct outcomes from an open preconnected
ready set `A`. Group one record region against the union of all the others, then apply
`posMeasure_noRecord_of_correlates` using `noRecord_subset_closure_interior`.
The resulting exceptional set avoids all `K` records, including when `K > 2`. -/
theorem posMeasure_noRecord_pointer (q₀ : Pointer K)
    {Φ : Pointer K → Pointer K} (hopen : IsOpenMap Φ) (hcont : Continuous Φ)
    {A : Set (Pointer K)} (hA : IsOpen A) (hconn : IsPreconnected A)
    {j l : Fin K} (hjl : j ≠ l)
    (hmeetj : ∃ x ∈ A, Φ x ∈ recordRegion j) (hmeetl : ∃ x ∈ A, Φ x ∈ recordRegion l) :
    fsMeasure q₀
      (A ∩ Φ ⁻¹' interior ((⋃ i, recordRegion (K := K) i)ᶜ)) ≠ 0 := by
  let rest : Set (Pointer K) := ⋃ i : {i : Fin K // i ≠ j}, recordRegion i.val
  have hrest : IsOpen rest := isOpen_iUnion fun i => isOpen_recordRegion i.val
  have hdisj : Disjoint (recordRegion j) rest := by
    apply Set.disjoint_iUnion_right.mpr
    intro i
    exact recordRegion_pairwiseDisjoint i.property.symm
  have hunion : recordRegion j ∪ rest = ⋃ i, recordRegion (K := K) i := by
    ext q
    constructor
    · rintro (hq | hq)
      · exact Set.mem_iUnion.mpr ⟨j, hq⟩
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hq
        exact Set.mem_iUnion.mpr ⟨i.val, hi⟩
    · intro hq
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hq
      by_cases hij : i = j
      · exact Or.inl (hij ▸ hi)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i, hij⟩, hi⟩)
  have hreg : (recordRegion j ∪ rest)ᶜ ⊆ closure (interior ((recordRegion j ∪ rest)ᶜ)) := by
    rw [hunion]
    exact noRecord_subset_closure_interior
  have hmeetrest : ∃ x ∈ A, Φ x ∈ rest := by
    obtain ⟨x, hx, hxl⟩ := hmeetl
    exact ⟨x, hx, Set.mem_iUnion.mpr ⟨⟨l, hjl.symm⟩, hxl⟩⟩
  have h := posMeasure_noRecord_of_correlates
    (fun _ hW hWne => LF4.fsMeasure_pos_of_isOpen q₀ hW hWne)
    hopen hcont hA hconn (isOpen_recordRegion j) hrest hdisj hreg hmeetj hmeetrest
  simpa only [hunion] using h

/-- Under the same hypotheses, exact records cannot hold almost everywhere on the ready
set with respect to restricted Fubini–Study measure. This applies to all `K` outcomes;
it does not classify alternative ready sets, measures or propagators. -/
theorem not_ae_record_pointer (q₀ : Pointer K)
    {Φ : Pointer K → Pointer K} (hopen : IsOpenMap Φ) (hcont : Continuous Φ)
    {A : Set (Pointer K)} (hA : IsOpen A) (hconn : IsPreconnected A)
    {j l : Fin K} (hjl : j ≠ l)
    (hmeetj : ∃ x ∈ A, Φ x ∈ recordRegion j) (hmeetl : ∃ x ∈ A, Φ x ∈ recordRegion l) :
    ¬ ∀ᵐ q ∂(fsMeasure q₀).restrict A, Φ q ∈ ⋃ i, recordRegion (K := K) i := by
  rw [ae_restrict_iff' hA.measurableSet]
  intro h
  have hnull : fsMeasure q₀
      {q | q ∈ A ∧ Φ q ∉ ⋃ i, recordRegion (K := K) i} = 0 := by
    simpa only [ae_iff, Classical.not_imp] using h
  apply posMeasure_noRecord_pointer q₀ hopen hcont hA hconn hjl hmeetj hmeetl
  refine measure_mono_null ?_ hnull
  intro q hq
  have hout : Φ q ∈ interior ((⋃ i, recordRegion (K := K) i)ᶜ) := hq.2
  exact ⟨hq.1, interior_subset hout⟩

end CSD.RecordLayer
