/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.SingletSkewTables
public import CsdLean4.LF6.C1BellConsistency
public import CsdLean4.RecordLayer.GalileanTransformation

/-!
# Which wing Σ selects first decides the individual outcomes of an entangled pair

**Category:** 7-SigmaLayer (the record layer). BACKLOG #288; #290.

## The question

Every record-layer slicing theorem so far (`sigma_record_write_order_indep`,
`chain_record_kick_order`, `twoRecordLaw_props`) concerns records that are local functions of the
ontic state, or the QM statistics of an entangled pair. Neither can show a preferred slicing. The
place one could show up is the **individual outcomes of an entangled pair**, selected by Σ. The
corpus's two-wing selection is the I3 skew partition (`SkewFibrePartition.lean`). The first wing
reads its own arc. The second reads its arc *conditional on the first's cell*. That module's doc
says "the order (A first, B conditional) is the chain rule's arbitrary choice and carries no
physical content; the mirror construction with the roles swapped realises the same joint law." This
file tests that claim. The joint *law* is the same; the individual *outcomes* are not.

## What is proved

* `JointRates.transpose`, `skewCellRev` (**the mirror selection**: B reads its arc first, A
  conditional on B's cell); ★★ `volume_skewCellRev` (**same Born weights** as the A-first cell).
  So no statistic of the joint outcomes tells the two orders apart.
* ★★★ `rate_eq_mul_of_selection_order_indep` (**if the two orders give the same joint outcome at
  almost every ontic point, the table is a product of its marginals**);
  ★★★ `selection_order_dependent` (**contrapositive: for any correlated table, the set of ontic
  points whose joint outcome depends on which wing is read first has positive measure**);
  ★★★ `singlet_selection_order_dependent` (the singlet at any context with `a·b ≠ 0`).
* ★★★ `no_order_indep_local_first_selection` (**the general form, not tied to I3**): take two
  selections of a pair's outcomes on any shared ontic space, one with A written first and one with
  B written first. Suppose each first writer's outcome depends only on its own setting, and the
  A-first selection reproduces the singlet's CHSH correlations. Then the two selections cannot agree
  at almost every ontic point at all four CHSH contexts. Order-independent individual outcomes with
  local first writes would be a local hidden-variable model, which Bell excludes; the proof is the
  corpus's C1 no-go (`no_compatible_global_chsh_assignment_realises_singlet`).

## What this decides

For a Bell pair, CSD's selection faces a fork at the level of individual outcomes. Either:

1. **the first write reads only its own wing**, as every local record write in the corpus does
   (`sigma_record_write_order_indep`, `recordStroke_comm_kick_of_factorised`). Then the individual
   outcomes depend on which wing the selection takes first. If that is the ontic time's order, it is
   a **hidden preferred slicing**, as Bohmian outcomes depend on the foliation. The statistics hide
   it (`volume_skewCell`, `volume_skewCellRev`, `operationalNoSignalling_skew_singlet`); or
2. **the first write reads the remote setting too.** Then no order is needed, but the first wing's
   individual outcome depends on the other wing's setting (parameter dependence), again hidden from
   the statistics.

The corpus's selections are on branch 1, with A first fixed by convention: the I3 cells, and the C1
model `singletContextualModel`, whose cells are ordered A-major. ⚠️ **What fixes the first wing is
not in the corpus.** The record layer is kinematic (no `H_int` generates the cells), so nothing ties
the first wing to the ontic time. That is a foundations decision, recorded as a row. This file
proves that the choice is **not** physically empty: it fixes the individual outcomes.

## The ontic time decides (#290, the author's choice (a))

The author's decision (2026-11-04): **the wing written first in ontic time is selected first.** "It
all comes back to QM and the actual microstate being unknown until measured. But the detail sets the
outcome." The individual outcome is a deterministic function of the ontic point and the ontic write
order (`onticCell`). Records do not reveal the point, and they see only its Born volumes, which do
not depend on the order. So the ontic slicing is hidden in exactly the way the microstate is.

* `onticCell` (**the selection by ontic write order**; ties go to A), ★★ `volume_onticCell` (**Born
  weights, whatever the order and the frame**);
* ★ `lorentzBoost_time_sub` (the boosted time difference of two writes);
* ★★★ `timelike_order_boost_invariant`, ★★★ `timelike_onticCell_boost` (**writes at timelike or null
  separation keep their order under every boost of the preparation, so their individual outcomes are
  the same in every frame**);
* ★★ `exists_boost_reverses_spacelike` (**for writes at spacelike separation, some boost of the
  preparation, with `u = (Δt + |Δx|)/(2Δx)`, reverses their ontic order**);
* ★★★ `spacelike_boost_changes_outcomes` (**for a correlated table and spacelike writes, some boost
  of the preparation changes the individual outcomes on a set of ontic points of positive measure,
  while every outcome's probability is unchanged**); ★★★ `singlet_spacelike_boost_changes_outcomes`.

So CSD carries a hidden preferred slicing in the sense of Bohmian mechanics. It touches only the
individual outcomes of spacelike-separated entangled writes, and no record statistic shows it (#285,
#287, and `volume_onticCell` here).

## Honest scope

* "Boost" is a boost of the **preparation** relative to the ontic frame, the frame whose time is the
  ontic time, as in #287's "a preparation and its boost". Re-describing a fixed experiment in
  another frame changes nothing, because the ontic order is the ontic frame's.
* The I3 theorems are on the fibre `T²` with the tables as data (as `SkewFibrePartition.lean`).
* "Agree" is almost-everywhere agreement under the measure the statistics use; disagreement is on a
  set of positive measure, so it is not a null-set artefact.
* The general theorem is Bell's theorem read as a statement about selection order. Its premises are
  the locality of the first write (in each order) and the reproduction of the singlet's CHSH
  correlations. It uses no I3 structure.
* Which branch CSD takes is the author's decision, branch 1 with the ontic order (#290); the
  theorems prove its consequences and do not derive it. The record layer stays kinematic: no `H_int`
  generates the cells.

## References

`SkewFibrePartition.lean` (`skewCell`, `volume_skewCell`, `volume_prodPartition_eq_mul`,
`wingAFibre`); `SingletSkewTables.lean` (`singletJointRates`, `singletJointRates_rowSum`,
`singletJointRates_colSum`); `LF6/C1BellConsistency.lean`
(`no_compatible_global_chsh_assignment_realises_singlet`, `singletContextualModel`);
`SlicingIndependence.lean` (`twoRecordLaw_props`); `CV/SigmaSlicing.lean`
(`sigma_record_write_order_indep`); `specs/BACKLOG.md` #288, ~~#285~~, ~~#287~~, #39;
`specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace CSD.RecordLayer

open LF3

/-! ### The mirror selection: B first -/

namespace JointRates

variable {m n : ℕ} (q : JointRates m n)

/-- **The table with the wings' roles swapped.** -/
def transpose : JointRates n m where
  rate := fun t s => q.rate s t
  nonneg := fun t s => q.nonneg s t
  sum_one := by rw [Finset.sum_comm]; exact q.sum_one

@[simp] theorem transpose_rate (t : Fin n) (s : Fin m) : q.transpose.rate t s = q.rate s t := rfl

/-- The swapped table's first marginal is B's marginal. -/
theorem transpose_rowSum : q.transpose.rowSum = q.colSum := rfl

end JointRates

variable {m n : ℕ}

/-- **The mirror I3 cell: B is read first.** B's arc in the second torus coordinate is that of its
marginal. A's arc in the first coordinate is that of its rate *conditional on B's cell*. It is the
A-first `skewCell` of the swapped table, with the torus coordinates swapped back. -/
def skewCellRev (q : JointRates m n) (s : Fin m) (t : Fin n) : Set LF4.KTorus :=
  Prod.swap ⁻¹' skewCell q.transpose t s

theorem measurableSet_skewCellRev (q : JointRates m n) (s : Fin m) (t : Fin n) :
    MeasurableSet (skewCellRev q s t) :=
  measurable_swap (measurableSet_skewCell _ t s)

/-- ★★ **The mirror selection has the same Born weights.** The B-first cell of the outcome pair has
area the joint probability, as the A-first cell does (`volume_skewCell`). So no statistic of the
joint outcomes distinguishes the orders. -/
theorem volume_skewCellRev (q : JointRates m n) (s : Fin m) (t : Fin n) :
    (volume : Measure LF4.KTorus) (skewCellRev q s t) = ENNReal.ofReal (q.rate s t) := by
  have hmp : MeasurePreserving (Prod.swap : LF4.KTorus → LF4.KTorus) volume volume := by
    rw [Measure.volume_eq_prod]
    exact Measure.measurePreserving_swap
  rw [skewCellRev, hmp.measure_preimage (measurableSet_skewCell _ t s).nullMeasurableSet,
    volume_skewCell]
  rfl

/-! ### The individual outcomes depend on the order -/

/-- ★★★ **Order-independent individual outcomes force a product table.** If the A-first and the
B-first selections give the same joint outcome at almost every ontic point, the joint law is the
product of its marginals: there is no correlation to carry.

Proof: an A-first cell lies in A's marginal arc times the circle, and a B-first cell in the circle
times B's marginal arc. If the cells agree almost everywhere, each joint probability is at most the
product of the marginals (`volume_prodPartition_eq_mul`). Both sides sum to one, so they are
equal. -/
theorem rate_eq_mul_of_selection_order_indep (q : JointRates m n)
    (h : ∀ s t, skewCell q s t =ᵐ[volume] skewCellRev q s t) (s : Fin m) (t : Fin n) :
    q.rate s t = q.rowSum s * q.colSum t := by
  have hle : ∀ s t, q.rate s t ≤ q.rowSum s * q.colSum t := by
    intro s t
    have hsub : skewCell q s t ∩ skewCellRev q s t
        ⊆ (circleCell q.rowSum s ×ˢ (univ : Set CircleFibre))
          ∩ ((univ : Set CircleFibre) ×ˢ circleCell q.transpose.rowSum t) :=
      fun x hx => ⟨⟨hx.1.1, trivial⟩, ⟨trivial, hx.2.1⟩⟩
    have hvol : (volume : Measure LF4.KTorus) (skewCell q s t)
        ≤ ENNReal.ofReal (q.rowSum s * q.colSum t) := by
      calc (volume : Measure LF4.KTorus) (skewCell q s t)
          = volume (skewCell q s t ∩ skewCell q s t) := by rw [Set.inter_self]
        _ = volume (skewCell q s t ∩ skewCellRev q s t) :=
            measure_congr (Filter.EventuallyEqSet.inter (Filter.EventuallyEq.refl _ _) (h s t))
        _ ≤ _ := measure_mono hsub
        _ = ENNReal.ofReal (q.rowSum s * q.colSum t) := by
            rw [volume_prodPartition_eq_mul,
              volume_circleCell _ q.rowSum_nonneg q.loSum_rowSum_le_one s,
              volume_circleCell _ q.transpose.rowSum_nonneg q.transpose.loSum_rowSum_le_one t,
              ← ENNReal.ofReal_mul (q.rowSum_nonneg s)]
            rfl
    rw [volume_skewCell] at hvol
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (q.rowSum_nonneg s) (q.colSum_nonneg t))).1 hvol
  have hsum : ∑ st : Fin m × Fin n, q.rate st.1 st.2
      = ∑ st : Fin m × Fin n, q.rowSum st.1 * q.colSum st.2 := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, q.sum_one]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    rw [q.sum_rowSum, q.sum_colSum, one_mul]
  have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) fun st _ => hle st.1 st.2).1 hsum
  exact this (s, t) (Finset.mem_univ _)

/-- ★★★ **For a correlated table, the order decides the outcome on a set of positive measure.** If
some joint probability differs from the product of its marginals, then for some outcome pair the
ontic points whose joint outcome changes with the order (the symmetric difference of the A-first
and the B-first cell) carry positive measure. -/
theorem selection_order_dependent (q : JointRates m n) {s₀ : Fin m} {t₀ : Fin n}
    (hne : q.rate s₀ t₀ ≠ q.rowSum s₀ * q.colSum t₀) :
    ∃ s t, 0 < (volume : Measure LF4.KTorus) (symmDiff (skewCell q s t) (skewCellRev q s t)) := by
  by_contra hc
  simp only [not_exists, not_lt] at hc
  refine hne (rate_eq_mul_of_selection_order_indep q (fun s t => ?_) s₀ t₀)
  exact measure_symmDiff_eq_zero_iff.1 (nonpos_iff_eq_zero.1 (hc s t))

/-- **The singlet's table is correlated** at any context with `a · b ≠ 0`:
`P₊₊ = (1 − a·b)/4`, while the marginals are `1/2`. -/
theorem singletJointRates_correlated (a b : DetectorSetting) (hab : dotR a b ≠ 0) :
    (singletJointRates a b).rate 0 0
      ≠ (singletJointRates a b).rowSum 0 * (singletJointRates a b).colSum 0 := by
  rw [singletJointRates_rowSum, singletJointRates_colSum, singletJointRates_rate, signOfFin_zero,
    P_st]
  intro h
  apply hab
  have : (Sign.plus.val : ℝ) = 1 := rfl
  rw [this] at h
  linarith

/-- ★★★ **The singlet: the order decides the individual outcomes.** At any context with
`a · b ≠ 0`, the singlet's table is correlated (`P₊₊ = (1 − a·b)/4`, marginals `1/2`), so the
A-first and B-first selections disagree on a set of ontic points of positive measure. -/
theorem singlet_selection_order_dependent (a b : DetectorSetting) (hab : dotR a b ≠ 0) :
    ∃ s t, 0 < (volume : Measure LF4.KTorus)
      (symmDiff (skewCell (singletJointRates a b) s t)
        (skewCellRev (singletJointRates a b) s t)) :=
  selection_order_dependent (singletJointRates a b) (singletJointRates_correlated a b hab)

/-! ### The general form: local first writes cannot be order independent -/

open LF6 in
/-- ★★★ **No order-independent selection with local first writes reproduces the singlet.**
`SA` is a selection of a pair's joint outcomes on a shared ontic space with **A written first**, and
`SB` one with **B written first**. A's outcome under `SA` depends only on A's setting, and B's under
`SB` only on B's: the first write in each order is local. If `SA` reproduces the singlet's CHSH
correlations, the two selections cannot agree almost everywhere at all four CHSH contexts.

Proof: if they agreed, A's outcome from `SA` and B's from `SB` would form a global assignment of
setting-local responses compatible with an outcome family almost-everywhere equal to `SA`. That
family reproduces the same correlations, which the corpus's C1 no-go
(`no_compatible_global_chsh_assignment_realises_singlet`) excludes. -/
theorem no_order_indep_local_first_selection {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure Λ) [IsProbabilityMeasure μ]
    (SA SB : SharedContextOutcomeMaps Λ)
    (hSA : MeasurableSharedContextOutcomeMaps SA) (hSB : MeasurableSharedContextOutcomeMaps SB)
    (hlocA : ∀ C C' : MeasurementContext, C.a = C'.a → ∀ l, SA.wingA C l = SA.wingA C' l)
    (hlocB : ∀ C C' : MeasurementContext, C.b = C'.b → ∀ l, SB.wingB C l = SB.wingB C' l)
    (hrep : ReproducesSingletAtCHSH μ SA) :
    ¬ ∀ i j : Fin 2, SA.F (chshContext i j) =ᵐ[μ] SB.F (chshContext i j) := by
  intro hagree
  let S : SharedContextOutcomeMaps Λ := ⟨fun C l => (SA.wingA C l, SB.wingB C l)⟩
  let G : GlobalCHSHAssignment Λ :=
    ⟨SA.wingA (chshContext 0 0), SA.wingA (chshContext 1 0),
      SB.wingB (chshContext 0 0), SB.wingB (chshContext 0 1)⟩
  have hS : MeasurableSharedContextOutcomeMaps S := fun C =>
    (SA.measurable_wingA hSA C).prodMk (SB.measurable_wingB hSB C)
  have hcomp : CompatibleWithGlobalCHSH S G := by
    intro i j l
    refine Prod.ext ?_ ?_
    · show SA.wingA (chshContext i j) l = globalA G i l
      fin_cases i <;> simp only [globalA, G] <;> simp <;> exact hlocA _ _ (by rfl) l
    · show SB.wingB (chshContext i j) l = globalB G j l
      fin_cases j <;> simp only [globalB, G] <;> simp <;> exact hlocB _ _ (by rfl) l
  have hrepS : ReproducesSingletAtCHSH μ S := by
    intro i j
    rw [← hrep i j]
    refine integral_congr_ae ((hagree i j).mono fun l hl => ?_)
    show ((SA.wingA (chshContext i j) l).val : ℝ) * ((SB.wingB (chshContext i j) l).val : ℝ)
      = ((SA.wingA (chshContext i j) l).val : ℝ) * ((SA.wingB (chshContext i j) l).val : ℝ)
    simp only [SharedContextOutcomeMaps.wingB, hl]
  exact no_compatible_global_chsh_assignment_realises_singlet μ S G hS hcomp hrepS

/-! ### The ontic time decides: the selection by ontic write order (#290) -/

/-- **The selection by ontic write order.** `eA` and `eB` are A's and B's record writes as events
`(t, x)` in the ontic frame. The wing written first in ontic time is read first (ties go to A).
The individual outcome at an ontic point is the cell containing it. -/
def onticCell (q : JointRates m n) (eA eB : ℝ × ℝ) (s : Fin m) (t : Fin n) : Set LF4.KTorus :=
  if eA.1 ≤ eB.1 then skewCell q s t else skewCellRev q s t

/-- ★★ **Born weights, whatever the order and the frame.** -/
theorem volume_onticCell (q : JointRates m n) (eA eB : ℝ × ℝ) (s : Fin m) (t : Fin n) :
    (volume : Measure LF4.KTorus) (onticCell q eA eB s t) = ENNReal.ofReal (q.rate s t) := by
  unfold onticCell
  split_ifs
  · exact volume_skewCell q s t
  · exact volume_skewCellRev q s t

/-- ★ **The boosted time difference of two writes.** -/
theorem lorentzBoost_time_sub (u : ℝ) (eA eB : ℝ × ℝ) :
    (lorentzBoost 1 u eB).1 - (lorentzBoost 1 u eA).1
      = ((eB.1 - eA.1) - u * (eB.2 - eA.2)) / Real.sqrt (1 - u ^ 2 / 1 ^ 2) := by
  simp only [lorentzBoost]
  ring

/-- ★★★ **Timelike or null writes keep their order under every boost.** If B's write is later than
A's by at least their spatial separation, it is later in every boosted preparation. -/
theorem timelike_order_boost_invariant {u : ℝ} (hu : |u| < 1) {eA eB : ℝ × ℝ}
    (hpos : 0 < eB.1 - eA.1) (h : |eB.2 - eA.2| ≤ eB.1 - eA.1) :
    (lorentzBoost 1 u eA).1 < (lorentzBoost 1 u eB).1 := by
  have hs := sqrt_one_sub_pos (c := 1) (v := u) hu
  have hux : u * (eB.2 - eA.2) < eB.1 - eA.1 := by
    calc u * (eB.2 - eA.2) ≤ |u * (eB.2 - eA.2)| := le_abs_self _
      _ = |u| * |eB.2 - eA.2| := abs_mul _ _
      _ ≤ |u| * (eB.1 - eA.1) := mul_le_mul_of_nonneg_left h (abs_nonneg u)
      _ < 1 * (eB.1 - eA.1) := mul_lt_mul_of_pos_right hu hpos
      _ = eB.1 - eA.1 := one_mul _
  have := lorentzBoost_time_sub u eA eB
  have hd : 0 < ((eB.1 - eA.1) - u * (eB.2 - eA.2)) / Real.sqrt (1 - u ^ 2 / 1 ^ 2) :=
    div_pos (by linarith) hs
  linarith

/-- ★★★ **Timelike or null writes: the individual outcomes are the same in every frame.** -/
theorem timelike_onticCell_boost (q : JointRates m n) {u : ℝ} (hu : |u| < 1) {eA eB : ℝ × ℝ}
    (hpos : 0 < eB.1 - eA.1) (h : |eB.2 - eA.2| ≤ eB.1 - eA.1) (s : Fin m) (t : Fin n) :
    onticCell q (lorentzBoost 1 u eA) (lorentzBoost 1 u eB) s t = onticCell q eA eB s t := by
  have h1 := timelike_order_boost_invariant hu hpos h
  have h2 : eA.1 ≤ eB.1 := by linarith
  simp [onticCell, h1.le, h2]

/-- ★★ **Spacelike writes: some boost of the preparation reverses their ontic order.** With
`Δt = t_B − t_A`, `Δx = x_B − x_A` and `|Δt| < |Δx|`, the boost `u = (Δt + |Δx|)/(2Δx)` has
`|u| < 1` and puts B's write first. -/
theorem exists_boost_reverses_spacelike {eA eB : ℝ × ℝ}
    (h : |eB.1 - eA.1| < |eB.2 - eA.2|) :
    ∃ u, |u| < 1 ∧ (lorentzBoost 1 u eB).1 < (lorentzBoost 1 u eA).1 := by
  set a := eB.1 - eA.1
  set b := eB.2 - eA.2
  have hb : 0 < |b| := lt_of_le_of_lt (abs_nonneg a) h
  have hb0 : b ≠ 0 := abs_pos.1 hb
  obtain ⟨ha1, ha2⟩ := abs_lt.1 h
  have hu : |(a + |b|) / (2 * b)| < 1 := by
    rw [abs_div, abs_mul, abs_two, abs_of_pos (by linarith : 0 < a + |b|),
      div_lt_one (by positivity)]
    linarith
  refine ⟨_, hu, ?_⟩
  have hs := sqrt_one_sub_pos (c := 1) hu
  have hub : (a + |b|) / (2 * b) * b = (a + |b|) / 2 := by field_simp
  have hd : (a - (a + |b|) / (2 * b) * b) / Real.sqrt (1 - ((a + |b|) / (2 * b)) ^ 2 / 1 ^ 2)
      < 0 := div_neg_of_neg_of_pos (by rw [hub]; linarith) hs
  have := lorentzBoost_time_sub ((a + |b|) / (2 * b)) eA eB
  linarith

/-- ★★★ **Spacelike writes: a boost of the preparation changes the individual outcomes, and no
statistic.** For a correlated table and two writes at spacelike separation, there is a boost of the
preparation under which every outcome keeps its probability, while for some outcome pair the ontic
points whose outcome changes carry positive measure. -/
theorem spacelike_boost_changes_outcomes (q : JointRates m n) {s₀ : Fin m} {t₀ : Fin n}
    (hne : q.rate s₀ t₀ ≠ q.rowSum s₀ * q.colSum t₀) {eA eB : ℝ × ℝ} (hle : eA.1 ≤ eB.1)
    (h : |eB.1 - eA.1| < |eB.2 - eA.2|) :
    ∃ u, |u| < 1 ∧
      (∀ s t, (volume : Measure LF4.KTorus)
          (onticCell q (lorentzBoost 1 u eA) (lorentzBoost 1 u eB) s t)
        = volume (onticCell q eA eB s t)) ∧
      ∃ s t, 0 < (volume : Measure LF4.KTorus) (symmDiff (onticCell q eA eB s t)
        (onticCell q (lorentzBoost 1 u eA) (lorentzBoost 1 u eB) s t)) := by
  obtain ⟨u, hu, hrev⟩ := exists_boost_reverses_spacelike h
  refine ⟨u, hu, fun s t => by rw [volume_onticCell, volume_onticCell], ?_⟩
  have h1 : ∀ s t, onticCell q eA eB s t = skewCell q s t := fun s t => by simp [onticCell, hle]
  have h2 : ∀ s t, onticCell q (lorentzBoost 1 u eA) (lorentzBoost 1 u eB) s t
      = skewCellRev q s t := fun s t => by simp [onticCell, not_le.2 hrev]
  simp only [h1, h2]
  exact selection_order_dependent q hne

/-- ★★★ **The singlet: spacelike writes, a boost changes the individual outcomes and no
statistic**, at any context with `a · b ≠ 0`. -/
theorem singlet_spacelike_boost_changes_outcomes (a b : DetectorSetting) (hab : dotR a b ≠ 0)
    {eA eB : ℝ × ℝ} (hle : eA.1 ≤ eB.1) (h : |eB.1 - eA.1| < |eB.2 - eA.2|) :
    ∃ u, |u| < 1 ∧
      (∀ s t, (volume : Measure LF4.KTorus)
          (onticCell (singletJointRates a b) (lorentzBoost 1 u eA) (lorentzBoost 1 u eB) s t)
        = volume (onticCell (singletJointRates a b) eA eB s t)) ∧
      ∃ s t, 0 < (volume : Measure LF4.KTorus) (symmDiff
        (onticCell (singletJointRates a b) eA eB s t)
        (onticCell (singletJointRates a b) (lorentzBoost 1 u eA) (lorentzBoost 1 u eB) s t)) :=
  spacelike_boost_changes_outcomes _ (singletJointRates_correlated a b hab) hle h

end CSD.RecordLayer
