/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TorusFibre

/-!
# A non-product record partition of `T²`: option I3

**Category:** 7-SigmaLayer (the record layer — Paper C A7).
BACKLOG #134, taken at the author's decision by the **I3** route; bears on #131 obligation (3) and
#132.

## The question this answers, and the theorem that forces the answer

`torusCell`'s `mem_torusCell_iff` records that the Born partition reads `θ₁` and ignores `θ₂` — "the
symplectic partner carries no record content". Option I1 (#131 blocker (I)) keeps that and obtains
the two wings by coarsening one selector. The objection it concedes is that `x.2.2` stays inert. I3
is the other route: give the second coordinate record content.

**It is not a free choice.** ★★★ `volume_prodPartition_eq_mul` says that if A's region is a
`θ₁`-set and B's region a `θ₂`-set then the joint law is *exactly* the product of the marginals, and
★★★ `not_exists_prodPartition_of_ne_mul` turns that around: **a joint law that is not the product of
its own marginals has no product partition of the fibre at all.** Correlation therefore *forces* one
wing's region to read both coordinates. That is the fibre-level analogue of
`LF6.no_product_partition_realises_singlet`, proved here by Fubini rather than assumed, and it is
the reason I3 exists.

## What is proved

* `JointRates m n` — a joint rate table of one joint context, with every A-marginal positive so the
  conditional law is defined;
* `skewCell q s t` — **the I3 cell**: A's arc in `θ₁`, and in `θ₂` the arc of the *conditional* rate
  `q s t / rowSum q s`. The cells are rectangles, but the **partition is not a product**: the
  `θ₂`-arc moves with `s`;
* ★★★ `volume_skewCell` — **exact Born weights**, `volume (skewCell q s t) = q s t`, for an
  arbitrary joint law. So I3 realises *any* correlation, the singlet's included, with no error term;
* ★★★ `volume_wingAFibre` and ★★★ `volume_wingBFibre` — **both marginals come out right**:
  `rowSum q s` and `colSum q t`. B's is the non-trivial one — the construction never mentions
  `colSum`, so **no-signalling for B is a theorem about the geometry**, not something arranged;
* ★★★ `not_exists_sndSet_of_condRate_ne` — **`x.2.1` is load-bearing for B's record**: when the
  conditional law genuinely depends on A's cell, *no* `θ₂`-set describes B's region. Together with
  the no-go above this is an equivalence in spirit: correlation and `θ₂`-nonlocality of B's region
  are the same fact;
* `skewCell_pairwiseDisjoint`, `skewCell_ae_total`, ★ `wingAFibre_inter_wingBFibre` — it is a
  partition, it covers `T²` up to a null set, and the two wing regions meet in exactly one cell.

## The finding: I2 and I3 are the same construction

#132 listed **I2** (chained selectors — a second selector whose rates depend on the first's outcome)
and **I3** (a non-product partition of `T²`) as two alternatives. They are not two. A partition of
`T²` that carries correlation must, by the no-go above, have a wing reading both coordinates; writing
the joint law as marginal-times-conditional is then the chain rule, and `condRate` *is* that
conditional. So the construction below is simultaneously I2 and I3, and the author's choice is
**binary** — I1's single coarsened selector, or this — not ternary. The order (A first, B
conditional) is the chain rule's arbitrary choice and carries no physical content; the mirror
construction with the roles swapped realises the same joint law.

## Honest scope

⚠️ **This is the fibre only.** The rates are an argument; nothing here is attached to a base point,
so there is no `ContextField`, no `globalBasin` and no `epistemicMeasure`. Coupling it to the base —
a joint-context field and its skew basin, which is what would let this replace `globalBasin` — is the
continuation, priced as #135.

⚠️ **No `P_st`, no Bell.** The joint law is arbitrary. The singlet is not mentioned, and nothing here
computes a CHSH value or claims a Bell violation. What is shown is that the *fibre* can carry any
joint law exactly, and that it must be non-product to do so.

⚠️ **`rowPos` is a restriction.** An A-outcome of probability zero has no conditional law, and the
construction asks for strictly positive A-marginals. For the singlet this always holds (`1/2` at
every setting pair), including at the perfectly (anti)correlated endpoints where individual joint
weights vanish.

⚠️ **I3 does not make the two wings symmetric.** A's region *is* a `θ₁`-set; it is B's that reads
both coordinates. The no-go only forces *one* wing to be non-local, and the chain rule picks which.
Calling the result "two independent selectors" would be wrong: there are two coordinates, both
load-bearing, and one conditional dependence between them.

⚠️ **Nothing here is a claim about `Σ`'s dynamics.** Whether a flow writes these cells is
`MacrostateStability`'s and `LF6`'s business and is untouched.

References: [`TorusFibre.lean`](TorusFibre.lean) (`torusCell`, `mem_torusCell_iff` — the statement
this file is the alternative to), [`CircleFibre.lean`](CircleFibre.lean) (`circleCell`,
`volume_circleCell`, `loSum`), [`BornFibrePartition.lean`](BornFibrePartition.lean) (`loSum`),
[`TwoWingCoarsening.lean`](TwoWingCoarsening.lean) (option I1, the alternative),
`LF6/ForcedContextuality.lean` (`no_product_partition_realises_singlet`, the base-level analogue of
this file's no-go); `specs/BACKLOG.md` #134, #132, #131 obligation (3), #135;
`specs/sigma-fibre-contextuality.md` (probabilities Born, regions contextual).
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace CSD.RecordLayer

/-! ### A product fibre partition cannot correlate -/

/-- ★★★ **A product fibre partition factorises the joint law, exactly.** If one wing's region is a
`θ₁`-set and the other's a `θ₂`-set, the measure of their intersection is the product of their
measures — by Fubini, with no hypothesis on the sets beyond measurability of the ambient product
measure. This is why `x.2.2` has to acquire record content before the fibre can correlate. -/
theorem volume_prodPartition_eq_mul (S T : Set CircleFibre) :
    (volume : Measure LF4.KTorus) ((S ×ˢ (univ : Set CircleFibre)) ∩ ((univ : Set CircleFibre) ×ˢ T))
      = (volume : Measure CircleFibre) S * (volume : Measure CircleFibre) T := by
  rw [Set.prod_inter_prod, Set.inter_univ, Set.univ_inter, Measure.volume_eq_prod,
    Measure.prod_prod]

/-- ★★★ **No product partition of the fibre carries a correlated joint law.** A joint law that
differs from the product of its own marginals at even one cell cannot be realised by a `θ₁`-reading
wing and a `θ₂`-reading wing. The fibre-level analogue of
`LF6.no_product_partition_realises_singlet`, and the reason option I3 is needed at all. -/
theorem not_exists_prodPartition_of_ne_mul {m n : ℕ} (q : Fin m → Fin n → ℝ)
    (hq : ∀ s t, 0 ≤ q s t) {s₀ : Fin m} {t₀ : Fin n}
    (hne : q s₀ t₀ ≠ (∑ t, q s₀ t) * ∑ s, q s t₀) :
    ¬∃ (S : Fin m → Set CircleFibre) (T : Fin n → Set CircleFibre),
        (∀ s, (volume : Measure CircleFibre) (S s) = ENNReal.ofReal (∑ t, q s t)) ∧
        (∀ t, (volume : Measure CircleFibre) (T t) = ENNReal.ofReal (∑ s, q s t)) ∧
        ∀ s t, (volume : Measure LF4.KTorus)
            ((S s ×ˢ (univ : Set CircleFibre)) ∩ ((univ : Set CircleFibre) ×ˢ T t))
          = ENNReal.ofReal (q s t) := by
  rintro ⟨S, T, hS, hT, hjoint⟩
  have hrow : (0 : ℝ) ≤ ∑ t, q s₀ t := Finset.sum_nonneg fun t _ => hq s₀ t
  have hcol : (0 : ℝ) ≤ ∑ s, q s t₀ := Finset.sum_nonneg fun s _ => hq s t₀
  have hkey : ENNReal.ofReal (q s₀ t₀)
      = ENNReal.ofReal ((∑ t, q s₀ t) * ∑ s, q s t₀) := by
    rw [← hjoint s₀ t₀, volume_prodPartition_eq_mul, hS s₀, hT t₀,
      ← ENNReal.ofReal_mul hrow]
  exact hne ((ENNReal.ofReal_eq_ofReal_iff (hq s₀ t₀) (mul_nonneg hrow hcol)).1 hkey)

/-! ### A joint rate table -/

/-- **The joint outcome probabilities of one joint context**, with every A-marginal strictly
positive so that the conditional law of B given A's cell is defined. -/
structure JointRates (m n : ℕ) where
  /-- The joint probability of the outcome pair. -/
  rate : Fin m → Fin n → ℝ
  /-- Joint probabilities are non-negative. -/
  nonneg : ∀ s t, 0 ≤ rate s t
  /-- Every A-marginal is strictly positive, so the conditional law is defined. -/
  rowPos : ∀ s, 0 < ∑ t, rate s t
  /-- The table is normalised. -/
  sum_one : ∑ s, ∑ t, rate s t = 1

namespace JointRates

variable {m n : ℕ} (q : JointRates m n)

/-- **A's marginal.** -/
def rowSum (s : Fin m) : ℝ := ∑ t, q.rate s t

/-- **B's marginal.** -/
def colSum (t : Fin n) : ℝ := ∑ s, q.rate s t

/-- **The conditional law of B given A's cell** — the dependence that carries the correlation. -/
def condRate (s : Fin m) (t : Fin n) : ℝ := q.rate s t / q.rowSum s

theorem rowSum_pos (s : Fin m) : 0 < q.rowSum s := q.rowPos s

theorem rowSum_nonneg (s : Fin m) : 0 ≤ q.rowSum s := (q.rowSum_pos s).le

theorem colSum_nonneg (t : Fin n) : 0 ≤ q.colSum t :=
  Finset.sum_nonneg fun s _ => q.nonneg s t

theorem sum_rowSum : ∑ s, q.rowSum s = 1 := q.sum_one

theorem sum_colSum : ∑ t, q.colSum t = 1 := by
  show ∑ t, ∑ s, q.rate s t = 1
  rw [Finset.sum_comm]
  exact q.sum_one

theorem condRate_nonneg (s : Fin m) (t : Fin n) : 0 ≤ q.condRate s t :=
  div_nonneg (q.nonneg s t) (q.rowSum_nonneg s)

theorem sum_condRate (s : Fin m) : ∑ t, q.condRate s t = 1 := by
  show ∑ t, q.rate s t / q.rowSum s = 1
  rw [← Finset.sum_div, show (∑ t, q.rate s t) = q.rowSum s from rfl]
  exact div_self (ne_of_gt (q.rowSum_pos s))

theorem rowSum_mul_condRate (s : Fin m) (t : Fin n) :
    q.rowSum s * q.condRate s t = q.rate s t := by
  have h : q.rowSum s ≠ 0 := ne_of_gt (q.rowSum_pos s)
  show q.rowSum s * (q.rate s t / q.rowSum s) = q.rate s t
  field_simp

theorem loSum_rowSum_le_one (s : Fin m) : loSum q.rowSum s + q.rowSum s ≤ 1 :=
  loSum_add_self_le_one _ q.rowSum_nonneg q.sum_rowSum s

theorem loSum_condRate_le_one (s : Fin m) (t : Fin n) :
    loSum (q.condRate s) t + q.condRate s t ≤ 1 :=
  loSum_add_self_le_one _ (q.condRate_nonneg s) (q.sum_condRate s) t

end JointRates

/-! ### The I3 cell -/

variable {m n : ℕ}

/-- **The I3 cell**: A's arc in the first torus coordinate, and in the second the arc of the
*conditional* rate. Each cell is a rectangle, but the **partition is not a product** — the
`θ₂`-arc moves with `s`, and that is what carries the correlation. -/
def skewCell (q : JointRates m n) (s : Fin m) (t : Fin n) : Set LF4.KTorus :=
  circleCell q.rowSum s ×ˢ circleCell (q.condRate s) t

@[simp] theorem mem_skewCell_iff (q : JointRates m n) (s : Fin m) (t : Fin n) (x : LF4.KTorus) :
    x ∈ skewCell q s t ↔ x.1 ∈ circleCell q.rowSum s ∧ x.2 ∈ circleCell (q.condRate s) t :=
  Iff.rfl

theorem measurableSet_skewCell (q : JointRates m n) (s : Fin m) (t : Fin n) :
    MeasurableSet (skewCell q s t) :=
  (measurableSet_circleCell _ s).prod (measurableSet_circleCell _ t)

/-- ★★★ **Exact Born weights, for an arbitrary joint law.** The cell's area is the joint
probability: `rowSum · condRate = rate`. So I3 realises *any* correlation on the fibre with no error
term — the singlet's included. -/
theorem volume_skewCell (q : JointRates m n) (s : Fin m) (t : Fin n) :
    (volume : Measure LF4.KTorus) (skewCell q s t) = ENNReal.ofReal (q.rate s t) := by
  rw [skewCell, Measure.volume_eq_prod, Measure.prod_prod,
    volume_circleCell _ q.rowSum_nonneg q.loSum_rowSum_le_one s,
    volume_circleCell _ (q.condRate_nonneg s) (q.loSum_condRate_le_one s) t,
    ← ENNReal.ofReal_mul (q.rowSum_nonneg s), q.rowSum_mul_condRate]

/-- **Distinct outcome pairs are mutually exclusive.** Two cases: different A-outcomes already
separate in `θ₁`; the same A-outcome with different B-outcomes separate in `θ₂`, because within one
A-cell the conditional rate vector is the same. -/
theorem skewCell_pairwiseDisjoint (q : JointRates m n) :
    Pairwise (Function.onFun Disjoint fun st : Fin m × Fin n => skewCell q st.1 st.2) := by
  intro st st' hne
  refine Set.disjoint_left.mpr fun x hx hx' => ?_
  by_cases hs : st.1 = st'.1
  · have ht : st.2 ≠ st'.2 := fun h => hne (Prod.ext hs h)
    have h1 : x.2 ∈ circleCell (q.condRate st.1) st.2 := hx.2
    have h2 : x.2 ∈ circleCell (q.condRate st.1) st'.2 := by
      rw [hs]; exact hx'.2
    exact Set.disjoint_left.mp
      (circleCell_pairwiseDisjoint _ (q.condRate_nonneg st.1) ht) h1 h2
  · exact Set.disjoint_left.mp
      (circleCell_pairwiseDisjoint _ q.rowSum_nonneg hs) hx.1 hx'.1

/-! ### The two wing regions -/

/-- **A's record region**: A recorded `s`, whatever B recorded. -/
def wingAFibre (q : JointRates m n) (s : Fin m) : Set LF4.KTorus :=
  ⋃ t, skewCell q s t

/-- **B's record region**: B recorded `t`, whatever A recorded. -/
def wingBFibre (q : JointRates m n) (t : Fin n) : Set LF4.KTorus :=
  ⋃ s, skewCell q s t

/-- ★ **The two wing regions meet in exactly one cell** — not merely up to a null set. So the joint
outcome really is the pair of wing outcomes. -/
theorem wingAFibre_inter_wingBFibre (q : JointRates m n) (s : Fin m) (t : Fin n) :
    wingAFibre q s ∩ wingBFibre q t = skewCell q s t := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hxA, hxB⟩
    obtain ⟨t', hxt'⟩ := Set.mem_iUnion.1 hxA
    obtain ⟨s', hxs'⟩ := Set.mem_iUnion.1 hxB
    have hss : s' = s := by
      by_contra hc
      exact Set.disjoint_left.mp
        (circleCell_pairwiseDisjoint _ q.rowSum_nonneg hc) hxs'.1 hxt'.1
    have htt : t' = t := by
      by_contra hc
      refine Set.disjoint_left.mp
        (circleCell_pairwiseDisjoint _ (q.condRate_nonneg s) hc) hxt'.2 ?_
      have := hxs'.2
      rw [hss] at this
      exact this
    rw [← htt]
    exact hxt'
  · intro x hx
    exact ⟨Set.mem_iUnion.2 ⟨t, hx⟩, Set.mem_iUnion.2 ⟨s, hx⟩⟩

/-- ★★★ **A's marginal is `rowSum`.** -/
theorem volume_wingAFibre (q : JointRates m n) (s : Fin m) :
    (volume : Measure LF4.KTorus) (wingAFibre q s) = ENNReal.ofReal (q.rowSum s) := by
  classical
  have hdisj : Pairwise (Function.onFun Disjoint fun t => skewCell q s t) := by
    intro t t' ht
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    exact Set.disjoint_left.mp
      (circleCell_pairwiseDisjoint _ (q.condRate_nonneg s) ht) hx.2 hx'.2
  rw [wingAFibre, measure_iUnion hdisj (fun t => measurableSet_skewCell q s t), tsum_fintype,
    Finset.sum_congr rfl fun t (_ : t ∈ Finset.univ) => volume_skewCell q s t,
    ← ENNReal.ofReal_sum_of_nonneg fun t _ => q.nonneg s t]
  rfl

/-- ★★★ **B's marginal is `colSum` — no-signalling for B, as a theorem about the geometry.** The
construction never mentions `colSum`: B's cells were built from the *conditional* rates, and summing
them over A's cells returns B's marginal because `rowSum · condRate = rate`. Nothing was arranged to
make this come out. -/
theorem volume_wingBFibre (q : JointRates m n) (t : Fin n) :
    (volume : Measure LF4.KTorus) (wingBFibre q t) = ENNReal.ofReal (q.colSum t) := by
  classical
  have hdisj : Pairwise (Function.onFun Disjoint fun s => skewCell q s t) := by
    intro s s' hs
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    exact Set.disjoint_left.mp
      (circleCell_pairwiseDisjoint _ q.rowSum_nonneg hs) hx.1 hx'.1
  rw [wingBFibre, measure_iUnion hdisj (fun s => measurableSet_skewCell q s t), tsum_fintype,
    Finset.sum_congr rfl fun s (_ : s ∈ Finset.univ) => volume_skewCell q s t,
    ← ENNReal.ofReal_sum_of_nonneg fun s _ => q.nonneg s t]
  rfl

/-! ### `x.2.1` is load-bearing for B's record -/

/-- ★★★ **B's record region is not a `θ₂`-set.** If some single second-coordinate set `T` described
B's outcome `t` across all of A's cells, then the conditional law of B given A would be the same in
every A-cell. So exactly when the conditional law genuinely depends on A's cell — exactly when there
is correlation — **the first torus coordinate is load-bearing for B's record**, and the partition is
not a product.

With `volume_prodPartition_eq_mul` this is the two sides of one fact: correlation and the
`θ₂`-nonlocality of B's region are the same thing. -/
theorem not_exists_sndSet_of_condRate_ne (q : JointRates m n) {s₁ s₂ : Fin m} {t : Fin n}
    (hne : q.condRate s₁ t ≠ q.condRate s₂ t) :
    ¬∃ T : Set CircleFibre, ∀ s, skewCell q s t = circleCell q.rowSum s ×ˢ T := by
  rintro ⟨T, hT⟩
  have hfst : ∀ s : Fin m, (circleCell q.rowSum s).Nonempty := by
    intro s
    refine nonempty_of_measure_ne_zero (μ := (volume : Measure CircleFibre)) ?_
    rw [volume_circleCell _ q.rowSum_nonneg q.loSum_rowSum_le_one s]
    exact ne_of_gt (ENNReal.ofReal_pos.2 (q.rowSum_pos s))
  have hTeq : ∀ s : Fin m, T = circleCell (q.condRate s) t := by
    intro s
    obtain ⟨x, hx⟩ := hfst s
    ext y
    constructor
    · intro hy
      have hmem : (x, y) ∈ circleCell q.rowSum s ×ˢ T := ⟨hx, hy⟩
      rw [← hT s] at hmem
      exact hmem.2
    · intro hy
      have hmem : (x, y) ∈ skewCell q s t := ⟨hx, hy⟩
      rw [hT s] at hmem
      exact hmem.2
  have hcells : circleCell (q.condRate s₁) t = circleCell (q.condRate s₂) t :=
    (hTeq s₁).symm.trans (hTeq s₂)
  have h12 : ENNReal.ofReal (q.condRate s₁ t) = ENNReal.ofReal (q.condRate s₂ t) := by
    rw [← volume_circleCell _ (q.condRate_nonneg s₁) (q.loSum_condRate_le_one s₁) t,
      ← volume_circleCell _ (q.condRate_nonneg s₂) (q.loSum_condRate_le_one s₂) t, hcells]
  exact hne ((ENNReal.ofReal_eq_ofReal_iff (q.condRate_nonneg s₁ t)
    (q.condRate_nonneg s₂ t)).1 h12)

/-! ### Totality -/

/-- **The cells cover `T²` up to a null set**, so a.e. microstate of the fibre yields a joint
record. -/
theorem skewCell_ae_total (q : JointRates m n) :
    (volume : Measure LF4.KTorus)
        (univ \ ⋃ st : Fin m × Fin n, skewCell q st.1 st.2) = 0 := by
  classical
  have hmeas : ∀ st : Fin m × Fin n, MeasurableSet (skewCell q st.1 st.2) :=
    fun st => measurableSet_skewCell q st.1 st.2
  have hcover : (volume : Measure LF4.KTorus)
      (⋃ st : Fin m × Fin n, skewCell q st.1 st.2) = 1 := by
    rw [measure_iUnion (skewCell_pairwiseDisjoint q) hmeas, tsum_fintype,
      Finset.sum_congr rfl fun st (_ : st ∈ Finset.univ) => volume_skewCell q st.1 st.2,
      ← ENNReal.ofReal_sum_of_nonneg fun st _ => q.nonneg st.1 st.2]
    rw [show ∑ st : Fin m × Fin n, q.rate st.1 st.2 = ∑ s, ∑ t, q.rate s t from
      Fintype.sum_prod_type' _, q.sum_one, ENNReal.ofReal_one]
  rw [measure_sdiff (subset_univ _) (MeasurableSet.iUnion hmeas).nullMeasurableSet
      (by rw [hcover]; exact ENNReal.one_ne_top),
    measure_univ, hcover, tsub_self]

end CSD.RecordLayer

end

end
