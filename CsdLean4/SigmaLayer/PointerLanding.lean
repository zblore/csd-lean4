/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.PointerWeights

/-!
# SigmaLayer/PointerLanding: the landing theorem (brick 3)

**Category:** dynamical measurement — the smooth-Hamiltonian witness route
(`specs/pointer-witness-plan.md` brick 3).

The geometry brick: it discharges the two distance hypotheses that `pointerEvolve_pure`
(brick 2b) left open, and lands the ready pointer in the record region.

* **Midpoint separation** (`cellMid_dist_ge`): distinct CDF-cell midpoints on the circle are
  at least `(rⱼ + r_k)/2` apart. The circle distance is bounded below through
  `UnitAddCircle.norm_eq` (`‖↑x‖ = |x − round x|`) and an elementary case analysis on
  `round` (`abs_sub_round_ge`); the two real-line gap bounds are the `loSum` interval
  inequalities that already order the corpus's CDF cells. By the triangle inequality, a
  point of the `ε`-shrunk cell of `j` is then at distance `≥ r_k/2` from every other
  midpoint (`shrunk_dist_other`) — so on the shrunk cell the weight vector is **pure**, and
  no per-cell inclusion geometry is ever needed.
* **Record transport is exact in the moment map** (`momentMap_pointerRot_smul`):
  `m_{j+1}(Uⱼ(π/2) • q) = m₀(q)` — the quarter rotation carries the ready weight to the
  record weight *pointwise on the whole pointer*, so the open ready region maps into the
  open record region with margin to spare (`pointerRot_smul_mem_recordRegion`, `δ ≤ 1/2`).
* ★ **The landing theorem** (`pointer_landing`): sector in the shrunk cell of `j` + pointer
  ready ⇒ the propagator lands the point in `arenaRecord j` — a record is **created** by a
  continuous, Liouville-preserving propagator, with the ontic sector selecting the outcome.
  The sector coordinate is conserved (`pointerEvolve_fst`), and the outcome is exclusive
  (`recordRegion_pairwiseDisjoint`, brick 0).
* **The Born seed** (`volume_shrunkCell_slice`): at every base point the shrunk cell's
  fibre slice carries selector volume **exactly `rⱼ − 2ε`** (`AddCircle.volume_closedBall`)
  — the `ε`-Born accounting input for brick 4. With `Σⱼ rⱼ = 1` and the record regions
  pairwise disjoint, the sector sandwich `rⱼ − 2ε ≤ sector ≤ rⱼ + 2(N−1)ε` will follow
  without any upper-bound cell geometry.

⚠️ **Honest scope.** Landing is stated for the shrunk-ball event, whose slice volume is
`rⱼ − 2ε`, not the full `circleCell` of volume `rⱼ` — the deficit is the transition
corridor forced by `no_everywhere_correlation`, priced explicitly by the witness parameter
`ε`, never hidden. No protocol packaging, sector accounting, or LLN here — that is brick 4.
Corridor points (slice measure `≤ 2Nε`) receive **partial** rotations: legitimate pointer
states outside every record region; nothing is claimed about them beyond measure
preservation.

## References

`specs/pointer-witness-plan.md` (bricks 3, 4); `specs/BACKLOG.md` (the ★ L row);
`specs/future-work.md`. Reused corpus API: `pointerEvolve_pure`/`pointerWeights`
(`SigmaLayer/PointerWeights.lean`), `loSum_add_le_loSum`/`loSum_add_self_le_one`
(`SigmaLayer/BornFibrePartition.lean`), `circleFibre_volume_univ`
(`SigmaLayer/TorusFibre.lean`), `Projectivization.inner_toEuclideanLin_unitary`
(transition-probability staging), `UnitAddCircle.norm_eq` + `AddCircle.volume_closedBall`
(Mathlib).
-/

@[expose] public section

namespace CSD.RecordLayer

open MeasureTheory Matrix Matrix.UnitaryGroup

/-! ### The circle-distance lower bound -/

/-- If `s` is below both integer-gap witnesses of `c ∈ [−1, 0]` — the gap to `0` and the
gap to `−1` — then `s ≤ |c − round c|`: whatever integer `round` picks is one of those two
or lies at distance `≥ 1`. -/
lemma abs_sub_round_ge {c s : ℝ} (hc0 : -1 ≤ c) (hc1 : c ≤ 0)
    (h0 : s ≤ -c) (h1 : s ≤ 1 + c) : s ≤ |c - round c| := by
  have hs1 : s ≤ 1 := by linarith
  rcases (by omega : round c ≤ -2 ∨ round c = -1 ∨ round c = 0 ∨ 1 ≤ round c)
    with hm | hm | hm | hm
  · have hmr : ((round c : ℤ) : ℝ) ≤ -2 := by exact_mod_cast hm
    calc s ≤ 1 := hs1
      _ ≤ c - (round c : ℝ) := by linarith
      _ ≤ |c - round c| := le_abs_self _
  · rw [hm]
    push_cast
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ c - (-1))]
    linarith
  · rw [hm]
    push_cast
    rw [sub_zero, abs_of_nonpos hc1]
    linarith
  · have hmr : (1 : ℝ) ≤ ((round c : ℤ) : ℝ) := by exact_mod_cast hm
    calc s ≤ 1 := hs1
      _ ≤ (round c : ℝ) - c := by linarith
      _ ≤ |c - round c| := by rw [abs_sub_comm]; exact le_abs_self _

/-- The circle distance between two coe points is bounded below by any `s ≥ 0` that fits
in both the direct gap and the wrap-around gap. -/
lemma dist_coe_circle_ge {a b s : ℝ} (hs : 0 ≤ s) (hd : a + s ≤ b) (hw : b + s ≤ 1 + a) :
    s ≤ dist ((a : ℝ) : CircleFibre) ((b : ℝ) : CircleFibre) := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]
  exact abs_sub_round_ge (by linarith) (by linarith) (by linarith) (by linarith)

variable {N : ℕ}

/-- **Midpoint separation**: distinct CDF-cell midpoints are at least the mean of the two
cell widths apart on the circle — both the direct gap (the `loSum` ordering) and the
wrap-around gap (total mass `1`) are that large. -/
theorem cellMid_dist_ge {r : Fin N → ℝ} (hr : ∀ i, 0 ≤ r i) (hsum : ∑ i, r i = 1)
    {j k : Fin N} (hjk : j ≠ k) :
    (r j + r k) / 2 ≤ dist (cellMid r j) (cellMid r k) := by
  have main : ∀ {j k : Fin N}, (j : ℕ) < (k : ℕ) →
      (r j + r k) / 2 ≤ dist (cellMid r j) (cellMid r k) := by
    intro j k hlt
    have hloj : 0 ≤ loSum r j := Finset.sum_nonneg fun i _ => hr i
    have hjk1 : loSum r j + r j ≤ loSum r k := loSum_add_le_loSum r hr hlt
    have hk1 : loSum r k + r k ≤ 1 := loSum_add_self_le_one r hr hsum k
    have hrj := hr j
    have hrk := hr k
    exact dist_coe_circle_ge (by positivity) (by linarith) (by linarith)
  rcases Nat.lt_or_ge (j : ℕ) (k : ℕ) with h | h
  · exact main h
  · have hne : (k : ℕ) ≠ (j : ℕ) := fun hkj => hjk (Fin.ext hkj.symm)
    have h' : (k : ℕ) < (j : ℕ) := lt_of_le_of_ne h hne
    have hmain := main h'
    rw [dist_comm] at hmain
    linarith

/-- **Points of the shrunk cell of `j` are far from every other midpoint** — triangle
inequality from the midpoint separation; the strict `ε`-shrinking is exactly what pays for
it. -/
theorem shrunk_dist_other {r : Fin N → ℝ} (hr : ∀ i, 0 ≤ r i) (hsum : ∑ i, r i = 1)
    {θ : CircleFibre} {j : Fin N} {ε : ℝ} (hε : 0 < ε)
    (hθ : dist θ (cellMid r j) ≤ r j / 2 - ε) {k : Fin N} (hkj : k ≠ j) :
    r k / 2 ≤ dist θ (cellMid r k) := by
  have hmid := cellMid_dist_ge hr hsum (hkj.symm)
  have htri := dist_triangle (cellMid r j) θ (cellMid r k)
  have hcomm : dist (cellMid r j) θ = dist θ (cellMid r j) := dist_comm _ _
  linarith

/-! ### Record transport in the moment map -/

variable {K : ℕ}

/-- **The quarter turn carries the ready weight to the record weight, exactly**:
`m_{j+1}(Uⱼ(π/2) • q) = m₀(q)` for every pointer state `q`. -/
theorem momentMap_pointerRot_smul (j : Fin K) (q : Pointer K) :
    LF4.momentMap (pointerRotU (Real.pi / 2) j • q) j.succ = LF4.momentMap q 0 := by
  conv_lhs => rw [← q.mk_rep]
  conv_rhs => rw [← q.mk_rep]
  rw [Projectivization.smul_mk_eq_mk_toEuclideanLin _ q.rep_nonzero,
    LF4.momentMap_mk, LF4.momentMap_mk]
  have hrow : ∀ k, (pointerRotU (Real.pi / 2) j).val j.succ k
      = if k = 0 then -Complex.I else 0 := by
    intro k
    simp only [pointerRotU, pointerRot, Real.cos_pi_div_two, Real.sin_pi_div_two,
      Complex.ofReal_zero, Complex.ofReal_one, mul_one, zero_sub, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, pointerPlane, pointerH,
      Matrix.single_apply]
    rcases eq_or_ne k 0 with rfl | hk0
    · simp [(succ_ne_zero' j).symm, succ_ne_zero' j]
    · rcases eq_or_ne k j.succ with rfl | hkj
      · simp [succ_ne_zero' j, (succ_ne_zero' j).symm]
      · simp [hk0, Ne.symm hk0, Ne.symm hkj]
  have hnum : (Matrix.toEuclideanLin (pointerRotU (Real.pi / 2) j).val q.rep) j.succ
      = -(Complex.I * q.rep 0) := by
    show ((pointerRotU (Real.pi / 2) j).val *ᵥ _) j.succ = _
    simp [Matrix.mulVec, dotProduct, hrow, ite_mul, zero_mul, Finset.sum_ite_eq']
  have hden : ‖Matrix.toEuclideanLin (pointerRotU (Real.pi / 2) j).val q.rep‖ ^ 2
      = ‖q.rep‖ ^ 2 := by
    have h := Projectivization.inner_toEuclideanLin_unitary
      (pointerRotU (Real.pi / 2) j) q.rep q.rep
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    exact_mod_cast h
  rw [hnum, hden]
  congr 1
  rw [norm_neg, norm_mul, Complex.norm_I, one_mul]

/-- **The open ready region lands inside the open record region** with margin: for
`δ ≤ 1/2`, `m₀(q) > 1 − δ` gives `m_{j+1}(Uⱼ(π/2) • q) > 1 − δ ≥ 1/2`. -/
theorem pointerRot_smul_mem_recordRegion {δ : ℝ} (hδ : δ ≤ 1 / 2) {q : Pointer K}
    (hq : q ∈ readyRegion δ) (j : Fin K) :
    pointerRotU (Real.pi / 2) j • q ∈ recordRegion j := by
  show (1 : ℝ) / 2 < LF4.momentMap (pointerRotU (Real.pi / 2) j • q) j.succ
  rw [momentMap_pointerRot_smul]
  have h : (1 : ℝ) - δ < LF4.momentMap q 0 := hq
  linarith

/-! ### The landing theorem -/

/-- The `ε`-shrunk cell of outcome `j`, as a sector event: base + selector points whose
first fibre coordinate lies within `rⱼ/2 − ε` of the `j`-th cell midpoint, rates read at
the ontic base point. This is exactly the region where the weight field is pure. -/
def shrunkCell (c : ContextField N) (ε : ℝ) (j : Fin N) : Set (LF4.KSigma N) :=
  {x | dist x.2.1 (cellMid (c.rate x.1) j) ≤ c.rate x.1 j / 2 - ε}

theorem measurableSet_shrunkCell (c : ContextField N) (ε : ℝ) (j : Fin N) :
    MeasurableSet (shrunkCell c ε j) := by
  have hmid : Measurable fun x : LF4.KSigma N => cellMid (c.rate x.1) j := by
    unfold cellMid
    show Measurable fun x : LF4.KSigma N =>
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
        (loSum (c.rate x.1) j + c.rate x.1 j / 2))
    exact Measurable.comp (AddCircle.continuous_mk' (p := (1 : ℝ))).measurable
      (((c.measurable_loSum j).comp measurable_fst).add
        (((c.measurable_rate j).comp measurable_fst).div_const 2))
  have hdist : Measurable fun x : LF4.KSigma N =>
      dist x.2.1 (cellMid (c.rate x.1) j) :=
    (measurable_fst.comp measurable_snd).dist hmid
  exact measurableSet_le hdist
    ((((c.measurable_rate j).comp measurable_fst).div_const 2).sub measurable_const)

/-- ★ **The landing theorem**: sector in the shrunk cell of outcome `j`, pointer ready
(margin `δ ≤ 1/2`) — the continuous, Liouville-preserving propagator lands the point in the
record cylinder of `j`. The ontic sector selects the outcome; the pointer records it. -/
theorem pointer_landing (c : ContextField N) {ε δ : ℝ} (hε : 0 < ε) (hδ : δ ≤ 1 / 2)
    {y : PointerArena N N} {j : Fin N}
    (hsec : y.1 ∈ shrunkCell c ε j) (hready : y.2 ∈ readyRegion δ) :
    pointerEvolve c ε y ∈ arenaRecord N j := by
  have hj : dist y.1.2.1 (cellMid (c.rate y.1.1) j) ≤ c.rate y.1.1 j / 2 - ε := hsec
  have hk : ∀ k, k ≠ j → c.rate y.1.1 k / 2 ≤ dist y.1.2.1 (cellMid (c.rate y.1.1) k) :=
    fun k hkj => shrunk_dist_other (c.nonneg y.1.1) (c.sum_one y.1.1) hε hj hkj
  rw [pointerEvolve_pure c hε hj hk]
  exact Set.mem_prod.mpr ⟨Set.mem_univ _, pointerRot_smul_mem_recordRegion hδ hready j⟩

/-! ### The Born seed: the shrunk slice volume -/

/-- **The selector volume of the shrunk cell's fibre slice is exactly `rⱼ − 2ε`**, at every
base point (when `rⱼ < 2ε` both sides are `0`) — the lower Born bound brick 4 integrates. The `2ε` deficit is
the transition corridor, priced and visible. -/
theorem volume_shrunkCell_slice (c : ContextField N) {ε : ℝ} (hε : 0 ≤ ε)
    (p : LF4.CPN N) (j : Fin N) :
    (volume : Measure LF4.KTorus)
        {θ : LF4.KTorus | dist θ.1 (cellMid (c.rate p) j) ≤ c.rate p j / 2 - ε}
      = ENNReal.ofReal (c.rate p j - 2 * ε) := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have hset : {θ : LF4.KTorus | dist θ.1 (cellMid (c.rate p) j) ≤ c.rate p j / 2 - ε}
      = Metric.closedBall (cellMid (c.rate p) j) (c.rate p j / 2 - ε) ×ˢ Set.univ := by
    ext θ
    simp [Metric.mem_closedBall, Set.mem_prod]
  have hle1 : c.rate p j ≤ 1 := by
    have hsum := c.sum_one p
    have hle := Finset.single_le_sum (f := fun i => c.rate p i)
      (fun i _ => c.nonneg p i) (Finset.mem_univ j)
    linarith
  rw [hset, Measure.volume_eq_prod, Measure.prod_prod, circleFibre_volume_univ, mul_one,
    AddCircle.volume_closedBall,
    show 2 * (c.rate p j / 2 - ε) = c.rate p j - 2 * ε from by ring,
    min_eq_right (by linarith)]

end CSD.RecordLayer
