/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.PointerConcentration
public import CsdLean4.Thermo.CanonicalTypicality

/-!
# The typicality price of a majority record

**Category:** 7-SigmaLayer (the record layer — Paper C A7).
BACKLOG #140, out of the scope note [`MacrostateStability.lean`](MacrostateStability.lean) and
[`PointerConcentration.lean`](PointerConcentration.lean) share.

Both of those files end on the same unfinished sentence.
[`MacrostateStability.lean`](MacrostateStability.lean) (#103) proves its majority half only under
`1 − ε ≤ c.rate p i`, and says of the Fubini–Study statistics that "those are statements about
**base statistics**, they live at a different place in `Σ`, and **no theorem joins them** to the
fibre bound proved here". [`PointerConcentration.lean`](PointerConcentration.lean) (#105) supplies
the hypothesis **geometrically** — nearness to a pointer ray — and records in prose that "for a
generic superposition no cell is overwhelming, and that is correct physics rather than a gap".

This file turns that prose into a theorem, and the answer is quantitative and negative: **base
typicality does not supply #103's hypothesis, it argues against it**, with a price that vanishes
like `1/N`.

## What is proved

* ★★ `fsMeasure_momentMap_dev_le` — **one outcome's weight concentrates at `1/N`**.
  `fs_chebyshev_concentration` is stated for a linear statistic `∑ λₖ xₖ`; at the selector
  `λ = δᵢ` it becomes a statement about a single Born weight, which is the form the record layer
  consumes: a Fubini–Study preparation has `|momentMap p i − 1/N| < t` outside a set of measure at
  most `(N − 1)/(N²(N + 1)t²)`.
* ★★★ `fsMeasure_momentMap_ge_le` — **the majority hypothesis is atypical**: the preparations whose
  outcome `i` carries weight `1 − ε` or more have Fubini–Study measure at most
  `(N − 1)/(N²(N + 1)(1 − ε − 1/N)²)`, which is `O(1/N²)` for fixed `ε`. The inclusion is the whole
  proof — a weight at least `1 − ε` is a deviation of at least `1 − ε − 1/N` from the typical value.
* ★★★ `fsMeasure_exists_momentMap_ge_le` and its clean reading
  ★★ `fsMeasure_exists_momentMap_ge_le_inv` — **typically no outcome at all is a majority**. The
  union bound over the `N` outcomes costs one factor `N`, leaving `O(1/N)`, so the statement
  survives being asked of the whole context rather than of a chosen outcome.
* ★★★ `fsMeasure_exists_majority_basin_le` — **the join, in #103's own vocabulary**: the
  preparations at which *some* basin of the canonical context carries epistemic measure `1 − ε` or
  more have Fubini–Study measure at most `1/(N(1 − ε − 1/N)²)`. This is the theorem #103's scope
  note says is missing, and it goes through `globalBasin_prob` — a cell's measure *is* its Born
  weight, so a statement about weights is a statement about cells with nothing in between.
* ★★ `tendsto_majorityBound` — **and the price vanishes**: for any `ε < 1` the bound tends to `0`
  as the dimension grows. So the majority hypothesis is not merely untypical at fixed `N`; it
  becomes arbitrarily untypical.

## What this says about #103 and #105, and what it does not

**It explains why #105 had to be geometric.** #103's hypothesis cannot be bought from base
typicality in any dimension, so a route to it has to say *where the preparation sits* — which is
exactly what `one_sub_le_momentMap_of_near_pointer` does. The two files are consistent and this one
prices the gap between them.

⚠️ **It is not a refutation of anything.** #105's hypothesis is about a *particular* preparation,
and a laboratory preparation is prepared, not sampled: `measure_robustBasin_ge_of_pointer` exhibits
the pointer state itself, so the exceptional set below is **nonempty at every `N`** and nothing here
makes the majority half vacuous. "Atypical" is a statement about Fubini–Study measure, not about
attainability.

⚠️ **The Born weights are untouched.** `globalBasin_prob` is exact at every base point, and nothing
below perturbs it. What is atypical is *one cell dominating*, not the cell law.

⚠️ **One context, and one rate field.** Everything is stated for `momentContext` — the standard-basis
context whose rate is the moment map. `CellLawFreedom.lean` exhibits a second, genuinely different
rate field (`sqContext`), and no statement here covers it: the Chebyshev input is about the moment
map specifically. Nor is anything claimed about a record *string* of several contexts; like #103's
and #105's majority statements, this is per-context.

⚠️ **Nothing about the fibre.** `measure_recordString_ne_le`'s `k·N·δ` relabelling bound is a
statement about writes on the fibre and is not joined to anything here. The join this file makes is
between the base statistics and the *majority* half of #103, which is the half whose hypothesis was
unsupplied — the robustness half needs no hypothesis and is already unconditional.

⚠️ **Polynomial, because its input is.** The rate is Chebyshev-grade because
`fs_chebyshev_concentration` is: an exponential (Lévy) bound would sharpen every constant below and
is the named residual of [`Thermo/CanonicalTypicality.lean`](../Thermo/CanonicalTypicality.lean),
inside BACKLOG #24. Nothing here needs it.

⚠️ **The hypothesis `1/N < 1 − ε` is real.** Below it the statement is empty rather than false: a
"majority" threshold at or under the typical weight `1/N` is no threshold at all, and at `N = 1` the
single outcome always has weight `1`.

References: [`records-to-spacetime-scoping.md`](../../specs/records-to-spacetime-scoping.md) `ST-3`;
[`future-work.md`](../../specs/future-work.md); `MacrostateStability.lean` (#103),
`PointerConcentration.lean` (#105), `GlobalBasin.lean`, `CellLawFreedom.lean`,
`Thermo/CanonicalTypicality.lean`; `specs/BACKLOG.md` #140, #103, #105, #100.
-/

@[expose] public section

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization BigOperators

namespace CSD.RecordLayer

open CSD.LF4 CSD.Thermo

variable {N : ℕ}

/-! ### One Born weight, read off the linear statistic -/

/-- ★★ **One outcome's weight concentrates at `1/N`.**

`fs_chebyshev_concentration` bounds the deviation of a *linear* diagonal statistic `∑ λₖ xₖ` from
its mean. At the selector `λ = δᵢ` the statistic is the single Born weight `momentMap p i`, its
mean is `1/N`, and the variance constant collapses to `(N − 1)/(N²(N + 1))`. This is the form the
record layer consumes, since a context's basin is indexed by one outcome. -/
theorem fsMeasure_momentMap_dev_le [NeZero N] (p₀ : CPN N) (i : Fin N) {t : ℝ} (ht : 0 < t) :
    (fsMeasure p₀) {p | t ≤ |momentMap p i - (N : ℝ)⁻¹|}
      ≤ ENNReal.ofReal (((N : ℝ) - 1) / ((N : ℝ) ^ 2 * ((N : ℝ) + 1)) / t ^ 2) := by
  have h := fs_chebyshev_concentration p₀ (fun k => if k = i then (1 : ℝ) else 0) ht
  have hpt : ∀ p : CPN N,
      (∑ k, (if k = i then (1 : ℝ) else 0) * momentMap p k) = momentMap p i := by
    intro p
    simp
  have hs : (∑ k : Fin N, (if k = i then (1 : ℝ) else 0)) = 1 := by simp
  have hq : (∑ k : Fin N, (if k = i then (1 : ℝ) else 0) ^ 2) = 1 := by simp
  simp only [hpt, hs, hq, mul_one, one_pow, one_div] at h
  exact h

/-! ### The majority hypothesis -/

/-- ★★★ **#103's majority hypothesis is atypical.**

A weight of `1 − ε` or more is a deviation of at least `1 − ε − 1/N` from the typical value, so the
Chebyshev bound applies directly. For fixed `ε` the right-hand side is `O(1/N²)`. -/
theorem fsMeasure_momentMap_ge_le [NeZero N] (p₀ : CPN N) (i : Fin N) {ε : ℝ}
    (hε : (N : ℝ)⁻¹ < 1 - ε) :
    (fsMeasure p₀) {p | 1 - ε ≤ momentMap p i}
      ≤ ENNReal.ofReal
          (((N : ℝ) - 1) / ((N : ℝ) ^ 2 * ((N : ℝ) + 1)) / (1 - ε - (N : ℝ)⁻¹) ^ 2) := by
  refine le_trans (measure_mono ?_) (fsMeasure_momentMap_dev_le p₀ i (by linarith))
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ momentMap p i - (N : ℝ)⁻¹)]
  linarith

/-- ★★★ **Typically no outcome of the context is a majority.** The union bound over the `N`
outcomes costs one factor `N`, so the price is `O(1/N)` rather than `O(1/N²)` — still vanishing,
and now a statement about the whole context rather than about a chosen outcome. -/
theorem fsMeasure_exists_momentMap_ge_le [NeZero N] (p₀ : CPN N) {ε : ℝ}
    (hε : (N : ℝ)⁻¹ < 1 - ε) :
    (fsMeasure p₀) {p | ∃ i, 1 - ε ≤ momentMap p i}
      ≤ ENNReal.ofReal
          (((N : ℝ) - 1) / ((N : ℝ) * ((N : ℝ) + 1)) / (1 - ε - (N : ℝ)⁻¹) ^ 2) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (0 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (1 : ℕ) ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast this
    linarith
  have ht : (0 : ℝ) < 1 - ε - (N : ℝ)⁻¹ := by linarith
  have hcover : {p : CPN N | ∃ i, 1 - ε ≤ momentMap p i}
      = ⋃ i : Fin N, {p : CPN N | 1 - ε ≤ momentMap p i} := by
    ext p; simp
  rw [hcover]
  refine le_trans (measure_iUnion_le _) ?_
  rw [tsum_fintype]
  calc ∑ i : Fin N, (fsMeasure p₀) {p : CPN N | 1 - ε ≤ momentMap p i}
      ≤ ∑ _i : Fin N, ENNReal.ofReal
          (((N : ℝ) - 1) / ((N : ℝ) ^ 2 * ((N : ℝ) + 1)) / (1 - ε - (N : ℝ)⁻¹) ^ 2) :=
        Finset.sum_le_sum fun i _ => fsMeasure_momentMap_ge_le p₀ i hε
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

/-- ★★ **The clean reading: the price is at most `1/N` over the squared margin.** `(N − 1)/(N(N+1))`
is at most `1/N`, which is the form the row states and the form the limit is taken in. -/
theorem fsMeasure_exists_momentMap_ge_le_inv [NeZero N] (p₀ : CPN N) {ε : ℝ}
    (hε : (N : ℝ)⁻¹ < 1 - ε) :
    (fsMeasure p₀) {p | ∃ i, 1 - ε ≤ momentMap p i}
      ≤ ENNReal.ofReal ((N : ℝ)⁻¹ / (1 - ε - (N : ℝ)⁻¹) ^ 2) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have ht : (0 : ℝ) < 1 - ε - (N : ℝ)⁻¹ := by linarith
  refine le_trans (fsMeasure_exists_momentMap_ge_le p₀ hε) (ENNReal.ofReal_le_ofReal ?_)
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hD : (0 : ℝ) < (N : ℝ) * ((N : ℝ) + 1) := by positivity
  have hinv : (N : ℝ)⁻¹ = ((N : ℝ) + 1) / ((N : ℝ) * ((N : ℝ) + 1)) := by
    field_simp
  rw [hinv]
  exact div_le_div_of_nonneg_right (by linarith) hD.le

/-! ### The join: the basins of the canonical context -/

/-- ★★★ **The join #103's scope note says is missing.**

The preparations at which *some* basin of the canonical context carries epistemic measure `1 − ε` or
more have Fubini–Study measure at most `1/(N(1 − ε − 1/N)²)`. Nothing mediates between the weight
statement and the cell statement: `globalBasin_prob` makes a cell's measure *exactly* its rate, and
`momentContext_rate` makes that rate the moment map. -/
theorem fsMeasure_exists_majority_basin_le [NeZero N] (p₀ : CPN N) {ε : ℝ}
    (hε : (N : ℝ)⁻¹ < 1 - ε) :
    (fsMeasure p₀)
        {p | ∃ i, ENNReal.ofReal (1 - ε)
          ≤ epistemicMeasure p (globalBasin (momentContext N) i)}
      ≤ ENNReal.ofReal ((N : ℝ)⁻¹ / (1 - ε - (N : ℝ)⁻¹) ^ 2) := by
  have hset : {p : CPN N | ∃ i, ENNReal.ofReal (1 - ε)
        ≤ epistemicMeasure p (globalBasin (momentContext N) i)}
      = {p : CPN N | ∃ i, 1 - ε ≤ momentMap p i} := by
    ext p
    simp only [Set.mem_ofPred_eq, globalBasin_prob, momentContext_rate]
    exact exists_congr fun i => ENNReal.ofReal_le_ofReal_iff (momentMap_nonneg p i)
  rw [hset]
  exact fsMeasure_exists_momentMap_ge_le_inv p₀ hε

/-- ★★ **The price vanishes with the dimension.** For any threshold `1 − ε` with `ε < 1` the
typicality bound tends to `0`, so the majority hypothesis is not merely untypical at a given `N` —
it becomes arbitrarily untypical as the arena grows. -/
theorem tendsto_majorityBound {ε : ℝ} (hε : ε < 1) :
    Filter.Tendsto (fun N : ℕ => (N : ℝ)⁻¹ / (1 - ε - (N : ℝ)⁻¹) ^ 2)
      Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun N : ℕ => (N : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have h2 : Filter.Tendsto (fun N : ℕ => (1 - ε - (N : ℝ)⁻¹) ^ 2) Filter.atTop
      (nhds ((1 - ε) ^ 2)) := by
    have hsub : Filter.Tendsto (fun N : ℕ => 1 - ε - (N : ℝ)⁻¹) Filter.atTop (nhds (1 - ε)) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ) - ε) (f := Filter.atTop (α := ℕ))).sub h1
    exact hsub.pow 2
  have hne : ((1 - ε) ^ 2) ≠ 0 := pow_ne_zero 2 (ne_of_gt (by linarith : (0 : ℝ) < 1 - ε))
  simpa only [Pi.div_def, zero_div] using h1.div h2 hne

end CSD.RecordLayer

end
