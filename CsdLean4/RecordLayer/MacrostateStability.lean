/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.RecordMacrostate

/-!
# Dynamical stability of record macrostates

**Category:** 7-SigmaLayer (the record layer — Paper C A7).
BACKLOG #103, the physics half of #38's candidate (5).

[`RecordMacrostate.lean`](RecordMacrostate.lean) (#102) built the macroscopic coordinate: the
**record string** of a finite indexed family of contexts, with no-signalling and the Born chain law
both verified for it. What makes a coordinate *macroscopic* is not its construction but its
**stability**, and #103 opened with the warning that stability here **cannot mean invariance** —
finite unitary dynamics on `Σ`'s base is almost periodic and supplies no mixing
(`not_hasCorrelationDecay_blockPop_of_unitary`). The brick chosen is therefore the
**measure-theoretic** one, in two halves that pull in opposite directions and are both proved:

* **the macroscopic law is *exactly* invariant.** ★★★ `map_recordString_sigmaShift`: a record write
  translates the record coordinate of the fibre, so it preserves the epistemic measure
  (★ `measurePreserving_sigmaShift`), and therefore the **distribution** of the record string is
  unchanged — for *every* write size, with no error term;
* **the pointwise assignment is robust to first order in the write.** ★★★
  `measure_recordString_ne_le`: the set of microstates whose record string a write of size `δ`
  *changes* has epistemic measure at most `k · N · δ` for a family of `k` contexts over `N`
  outcomes. So the records do move — but only on a set that shrinks linearly with the write
  (★ `tendsto_measure_recordString_ne`), which is the honest sense in which the cells are stable.

The mechanism is arithmetic on the fibre, and the whole file rests on one lemma:

* ★ `rep_add_coe` (in [`CircleFibre.lean`](CircleFibre.lean)) — a translation that does not wrap
  adds to the canonical representative. A write therefore pushes a microstate **towards the upper
  endpoint of its own arc**, and the only microstates it can relabel are the ones within `δ` of that
  endpoint;
* `robustBasin`, `edgeBand` — the `δ`-interior of a basin and the last `δ` of its arc, with
  ★ `globalBasin_subset_robustBasin_union_edgeBand` splitting every basin into the two;
* ★★ `sigmaShift_mem_globalBasin` — **the margin lemma**: a write of size `δ` cannot move a
  microstate out of a basin it is `δ`-robustly inside — and hence ★★ `outcomeCode_sigmaShift`,
  ★★★ `recordString_sigmaShift`, ★★ `recordMacro_sigmaShift` at the macrostate level;
* `measure_edgeBand_le` — the band's measure is at most `δ`, by `volume_rep_preimage_Ioc`;
* ★★ `measure_robustBasin_ge` — **robustness is controlled by the Born weight**:
  `rate p i − δ ≤ μ(δ-interior of the basin of i)`. A record whose Born weight is large is robust to
  writes far larger than a record whose weight is small, and a cell of weight below `δ` is given no
  robustness at all. That is the sense in which *macroscopic* records are the stable ones;
* ★★ `measure_robustBasin_ge_one_sub` — **the majority half, conditional on concentration**: once the
  context's weights concentrate (`1 − ε ≤ rate p i`) the shared-and-robust cell carries all but
  `ε + δ`. By `globalBasin_prob` a cell's measure is *exactly* its Born weight, so **no cell is
  overwhelming unless the weights are** — "overwhelmingly many microstates share the record" is a
  property of the preparation and the context, not of the coordinate, and that is the honest reading
  of #103's second half;
* ★★★ `measure_exists_recordString_ne_le` and ★★★ `measure_drift_recordString_ne_le` — the bound is
  **uniform over a whole horizon**: the exceptional set is the same one for every write in `[0, δ]`,
  so for a drift of the record coordinate at rate `ω` the record string survives the entire interval
  `[0, T]` outside a set of measure `k · N · ω · T`. This is "persistence over a horizon" in the
  words of #103, obtained without a second argument.

## Honest scope

⚠️ **This is not invariance and contains no mixing claim.** No cell is shown to be an invariant set,
no flow is shown to mix, and nothing here contradicts
`not_hasCorrelationDecay_blockPop_of_unitary`: the exact statement is invariance of the *law* plus an
`O(δ)` bound on the microstates that get relabelled. The two are compatible precisely because the
law is a pushforward and the relabelling is a pointwise fact.

⚠️ **Only the record coordinate moves.** `sigmaShift` fixes the base and the symplectic partner of
the fibre. A flow that moves the **base** changes the arcs themselves, and a `ContextField` is only
assumed *measurable*, so its arcs may move discontinuously with the base: that case is **not covered
here**. It is BACKLOG #104, landed the same day as
[`BaseMotionStability.lean`](BaseMotionStability.lean), which carries the margin argument over with a
hypothesis bounding the arcs' displacement — no metric on the base required.

⚠️ **The write below is a constant translation**, so nothing in *this* file is stated for the
base-dependent write of `CV/RecordInfluence.lean`'s `recordStroke`. That is a limit of this file and
not an obstruction: `MeasurableSingletonClass (LF4.CPN N)` **is** available at the pin, so the
epistemic measure is concentrated on the fibre over its preparation and a base-dependent write agrees
with a constant one almost everywhere. [`BaseMotionStability.lean`](BaseMotionStability.lean) (#104)
proves exactly that (`ae_fst_eq`, `map_sigmaMove_id`) and covers the base-dependent case.

⚠️ **The majority half is conditional, and its hypothesis is not supplied.**
`measure_robustBasin_ge_one_sub` assumes the concentration `1 − ε ≤ rate p i`; nothing here derives
it, and by `globalBasin_prob` it cannot be derived from the coordinate, since a cell's measure *is*
its Born weight. Where such a rate field comes from — pointer states, decoherence, or the dynamics —
is BACKLOG #105. ⚠️ It is **not** the same thing as `fs_chebyshev_concentration`
([`Thermo/CanonicalTypicality.lean`](../Thermo/CanonicalTypicality.lean), a polynomial rate) or the
conditional time-averaged equilibration of [`Thermo/Equilibration.lean`](../Thermo/Equilibration.lean):
those are statements about **base statistics**, they live at a different place in `Σ`, and no theorem
below joins them to the fibre bound proved here.

⚠️ **The bound degrades with the family and the alphabet** and is not claimed uniform in `k` or `N`:
it is `k · N · δ`, each factor from a union bound (one band per outcome, one context per index), and
no better constant is claimed. In particular records of small Born weight are genuinely fragile —
`measure_robustBasin_ge` is vacuous once `δ` exceeds the weight — and that is a feature of the
construction, not a gap in the proof.

⚠️ **No dynamics of `Σ` is derived.** Translation of the record coordinate is the dynamics the record
medium *has* in this corpus (`measurePreserving_fibreShift`), not a flow derived from an interaction
Hamiltonian; nothing here claims it is the physical evolution.

References: [`records-to-spacetime-scoping.md`](../../specs/records-to-spacetime-scoping.md) `ST-3`;
[`future-work.md`](../../specs/future-work.md); `RecordMacrostate.lean` (#102),
`MacroProjection.lean` (#99), `CircleFibre.lean`, `GlobalBasin.lean`,
[`CV/RecordInfluence.lean`](../CV/RecordInfluence.lean) (`fibreShift`);
`specs/BACKLOG.md` #103, #104, #105, #38, #100.
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

variable {N : ℕ}

/-! ### A record write as a translation of the record coordinate -/

/-- **A record write of size `δ`**: translation of the *record* coordinate of `Σ`'s fibre, leaving
the base and the symplectic partner untouched. This is the dynamics the record medium has — the
`recordStroke` of `CV/RecordInfluence.lean` acts on the fibre exactly this way. -/
def sigmaShift (δ : ℝ) (x : LF4.KSigma N) : LF4.KSigma N :=
  (x.1, (x.2.1 + (δ : AddCircle (1 : ℝ)), x.2.2))

@[simp] theorem sigmaShift_fst (δ : ℝ) (x : LF4.KSigma N) : (sigmaShift δ x).1 = x.1 := rfl

@[simp] theorem sigmaShift_record (δ : ℝ) (x : LF4.KSigma N) :
    (sigmaShift δ x).2.1 = x.2.1 + (δ : AddCircle (1 : ℝ)) := rfl

@[simp] theorem sigmaShift_partner (δ : ℝ) (x : LF4.KSigma N) :
    (sigmaShift δ x).2.2 = x.2.2 := rfl

@[simp] theorem sigmaShift_zero : sigmaShift (0 : ℝ) = (id : LF4.KSigma N → LF4.KSigma N) := by
  funext x
  simp [sigmaShift]

/-- Writes compose by adding their sizes: the family `sigmaShift` is a one-parameter group. -/
theorem sigmaShift_sigmaShift (δ₁ δ₂ : ℝ) (x : LF4.KSigma N) :
    sigmaShift δ₁ (sigmaShift δ₂ x) = sigmaShift (δ₂ + δ₁) x := by
  simp [sigmaShift, add_assoc]

theorem measurable_sigmaShift (δ : ℝ) : Measurable (sigmaShift (N := N) δ) :=
  measurable_fst.prodMk
    (((measurable_fst.comp measurable_snd).add_const _).prodMk
      (measurable_snd.comp measurable_snd))

/-- ★ **A record write preserves the epistemic measure.** The base is a point and the record
coordinate carries Haar measure, which translation preserves. This is what makes the macroscopic law
*exactly* invariant (`map_recordString_sigmaShift`) however large the write. -/
theorem measurePreserving_torusShift (δ : ℝ) :
    MeasurePreserving
      (Prod.map (fun θ : AddCircle (1 : ℝ) => θ + (δ : AddCircle (1 : ℝ)))
        (id : AddCircle (1 : ℝ) → AddCircle (1 : ℝ)))
      (volume : Measure LF4.KTorus) (volume : Measure LF4.KTorus) := by
  have h1 : MeasurePreserving (fun θ : AddCircle (1 : ℝ) => θ + (δ : AddCircle (1 : ℝ)))
      (volume : Measure (AddCircle (1 : ℝ))) volume := measurePreserving_add_right volume _
  rw [Measure.volume_eq_prod]
  exact h1.prod (MeasurePreserving.id _)

theorem measurePreserving_sigmaShift (δ : ℝ) (p : LF4.CPN N) :
    MeasurePreserving (sigmaShift (N := N) δ) (epistemicMeasure p) (epistemicMeasure p) := by
  have h2 := measurePreserving_torusShift δ
  have hfun : sigmaShift (N := N) δ
      = Prod.map (id : LF4.CPN N → LF4.CPN N)
          (Prod.map (fun θ : AddCircle (1 : ℝ) => θ + (δ : AddCircle (1 : ℝ)))
            (id : AddCircle (1 : ℝ) → AddCircle (1 : ℝ))) := by
    funext x
    rfl
  rw [epistemicMeasure, hfun]
  exact (MeasurePreserving.id (Measure.dirac p)).prod h2

/-! ### The arc a context assigns, its robust interior and its boundary band -/

/-- The **upper endpoint** of the arc a context assigns to outcome `i`, read at a microstate's own
base point. A write pushes the record coordinate towards it, so it is the only endpoint the
stability bounds have to watch. -/
noncomputable def cellTop (c : ContextField N) (i : Fin N) (x : LF4.KSigma N) : ℝ :=
  loSum (c.rate x.1) i + c.rate x.1 i

@[simp] theorem cellTop_sigmaShift (c : ContextField N) (δ : ℝ) (i : Fin N) (x : LF4.KSigma N) :
    cellTop c i (sigmaShift δ x) = cellTop c i x := rfl

theorem cellTop_le_one (c : ContextField N) (i : Fin N) (x : LF4.KSigma N) :
    cellTop c i x ≤ 1 := c.loSum_le_one x.1 i

theorem measurable_cellTop (c : ContextField N) (i : Fin N) : Measurable (cellTop c i) :=
  ((c.measurable_loSum i).comp measurable_fst).add ((c.measurable_rate i).comp measurable_fst)

theorem measurable_repRecord : Measurable fun x : LF4.KSigma N => rep x.2.1 :=
  measurable_rep.comp (measurable_fst.comp measurable_snd)

/-- The basin, written out as two inequalities on the record coordinate — the form every margin
argument below consumes. -/
theorem mem_globalBasin_iff (c : ContextField N) (i : Fin N) (x : LF4.KSigma N) :
    x ∈ globalBasin c i ↔
      loSum (c.rate x.1) i < rep x.2.1 ∧ rep x.2.1 ≤ cellTop c i x := by
  simp [globalBasin, circleCell, cellTop]

/-- **The `δ`-robust interior of a basin**: the microstates of the basin whose record coordinate is
at distance at least `δ` from the arc's *upper* endpoint, the endpoint a write pushes towards. -/
noncomputable def robustBasin (c : ContextField N) (δ : ℝ) (i : Fin N) : Set (LF4.KSigma N) :=
  {x | loSum (c.rate x.1) i < rep x.2.1 ∧ rep x.2.1 + δ ≤ cellTop c i x}

/-- **The `δ`-boundary band of a basin**: the last `δ` of its arc, the only part of the basin a write
of size `δ` can push out. -/
noncomputable def edgeBand (c : ContextField N) (δ : ℝ) (i : Fin N) : Set (LF4.KSigma N) :=
  {x | cellTop c i x - δ < rep x.2.1 ∧ rep x.2.1 ≤ cellTop c i x}

theorem measurableSet_robustBasin (c : ContextField N) (δ : ℝ) (i : Fin N) :
    MeasurableSet (robustBasin c δ i) :=
  (measurableSet_lt ((c.measurable_loSum i).comp measurable_fst) measurable_repRecord).inter
    (measurableSet_le (measurable_repRecord.add_const δ) (measurable_cellTop c i))

theorem measurableSet_edgeBand (c : ContextField N) (δ : ℝ) (i : Fin N) :
    MeasurableSet (edgeBand c δ i) :=
  (measurableSet_lt ((measurable_cellTop c i).sub_const δ) measurable_repRecord).inter
    (measurableSet_le measurable_repRecord (measurable_cellTop c i))

theorem robustBasin_subset_globalBasin (c : ContextField N) {δ : ℝ} (hδ : 0 ≤ δ) (i : Fin N) :
    robustBasin c δ i ⊆ globalBasin c i := by
  intro x hx
  obtain ⟨hlo, hhi⟩ := hx
  rw [mem_globalBasin_iff]
  exact ⟨hlo, by linarith⟩

theorem robustBasin_mono (c : ContextField N) {δ δ' : ℝ} (h : δ' ≤ δ) (i : Fin N) :
    robustBasin c δ i ⊆ robustBasin c δ' i := by
  intro x hx
  obtain ⟨hlo, hhi⟩ := hx
  exact ⟨hlo, by linarith⟩

/-- ★ **Every basin splits into its robust interior and its boundary band.** The dichotomy the
measure bounds run on: a microstate of the basin either has margin `δ` to the upper endpoint, or lies
in the last `δ` of the arc. -/
theorem globalBasin_subset_robustBasin_union_edgeBand (c : ContextField N) (δ : ℝ) (i : Fin N) :
    globalBasin c i ⊆ robustBasin c δ i ∪ edgeBand c δ i := by
  intro x hx
  rw [mem_globalBasin_iff] at hx
  by_cases h : rep x.2.1 + δ ≤ cellTop c i x
  · exact Or.inl ⟨hx.1, h⟩
  · exact Or.inr ⟨by linarith [not_le.1 h], hx.2⟩

/-! ### The margin lemma -/

/-- ★★ **The margin lemma.** A record write of size `δ` cannot move a microstate out of a basin it
is `δ`-robustly inside: the write adds `δ` to the record coordinate's representative
(`rep_add_coe`, available because the shifted representative is still inside one turn), and the
margin is exactly what keeps the sum below the arc's upper endpoint. -/
theorem sigmaShift_mem_globalBasin (c : ContextField N) {δ : ℝ} (hδ : 0 ≤ δ) (i : Fin N)
    {x : LF4.KSigma N} (hx : x ∈ robustBasin c δ i) : sigmaShift δ x ∈ globalBasin c i := by
  obtain ⟨hlo, hhi⟩ := hx
  have hmem : rep x.2.1 + δ ∈ Ioc (0 : ℝ) 1 :=
    ⟨by linarith [rep_pos x.2.1], le_trans hhi (cellTop_le_one c i x)⟩
  rw [mem_globalBasin_iff]
  simp only [sigmaShift_fst, sigmaShift_record, cellTop_sigmaShift, rep_add_coe hmem]
  exact ⟨by linarith, hhi⟩

/-- ★★ **A record write does not change the outcome a context assigns** to a microstate robustly
inside one of its basins. -/
theorem outcomeCode_sigmaShift (c : ContextField N) {δ : ℝ} (hδ : 0 ≤ δ) {i : Fin N}
    {x : LF4.KSigma N} (hx : x ∈ robustBasin c δ i) :
    outcomeCode c (sigmaShift δ x) = outcomeCode c x := by
  rw [(outcomeCode_eq_succ_iff c (sigmaShift δ x) i).2 (sigmaShift_mem_globalBasin c hδ i hx),
    (outcomeCode_eq_succ_iff c x i).2 (robustBasin_subset_globalBasin c hδ i hx)]

/-- ★★★ **A record write leaves the whole record string intact** on a microstate that is robustly
inside a basin of *every* context of the family. The macrostate of #102 is unchanged — not because
the cell is invariant, but because the microstate had margin. -/
theorem recordString_sigmaShift {k : ℕ} (c : Fin k → ContextField N) {δ : ℝ} (hδ : 0 ≤ δ)
    {x : LF4.KSigma N} (hx : ∀ j, ∃ i, x ∈ robustBasin (c j) δ i) :
    recordString c (sigmaShift δ x) = recordString c x := by
  funext j
  obtain ⟨i, hi⟩ := hx j
  exact outcomeCode_sigmaShift (c j) hδ hi

/-- **The margin bought at size `δ` covers every smaller write**, since the robust interior only
grows as the margin demanded shrinks. This is why one exceptional set serves a whole horizon. -/
theorem recordString_sigmaShift_of_le {k : ℕ} (c : Fin k → ContextField N) {δ s : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ δ) {x : LF4.KSigma N}
    (hx : ∀ j, ∃ i, x ∈ robustBasin (c j) δ i) :
    recordString c (sigmaShift s x) = recordString c x :=
  recordString_sigmaShift c hs0 fun j => (hx j).imp fun i hi => robustBasin_mono (c j) hs i hi

/-- ★★ **The macrostate of #102 itself is preserved**, stated on `recordMacro` so that it is
literally the macroscopic coordinate of candidate (5) that the write leaves alone. -/
theorem recordMacro_sigmaShift {k : ℕ} (c : Fin k → ContextField N) {δ : ℝ} (hδ : 0 ≤ δ)
    {x : LF4.KSigma N} (hx : ∀ j, ∃ i, x ∈ robustBasin (c j) δ i) :
    (recordMacro c).toFun (sigmaShift δ x) = (recordMacro c).toFun x :=
  recordString_sigmaShift c hδ hx

/-! ### The measure of the boundary band -/

/-- ★ **Any `rep`-preimage of an interval has measure at most the interval's length**, with no
containment hypothesis at all: the representative's range `(0, 1]` clips the overhang at both ends.
The boundary bands of the stability bounds are intervals that need not sit inside one turn, so this
is the form they consume. -/
theorem volume_rep_preimage_Ioc_le (a b : ℝ) :
    (volume : Measure CircleFibre) (rep ⁻¹' Ioc a b) ≤ ENNReal.ofReal (b - a) := by
  have hclip : rep ⁻¹' Ioc a b = rep ⁻¹' Ioc (max 0 a) (min 1 b) := by
    ext θ
    simp only [Set.mem_preimage, Set.mem_Ioc, max_lt_iff, le_min_iff]
    exact ⟨fun h => ⟨⟨rep_pos θ, h.1⟩, ⟨rep_le_one θ, h.2⟩⟩, fun h => ⟨h.1.2, h.2.2⟩⟩
  rw [hclip, volume_rep_preimage_Ioc (le_max_left 0 a) (min_le_left 1 b)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := min_le_right (1 : ℝ) b
  have h2 := le_max_right (0 : ℝ) a
  linarith

/-- **The boundary band is small.** Its slice over the preparation is the last `δ` of one arc, so its
epistemic measure is at most `δ` — the single quantitative input to every bound below. -/
theorem measure_edgeBand_le (c : ContextField N) (δ : ℝ) (i : Fin N)
    (p : LF4.CPN N) : epistemicMeasure p (edgeBand c δ i) ≤ ENNReal.ofReal δ := by
  have hmeas : MeasurableSet (edgeBand c δ i) := measurableSet_edgeBand c δ i
  rw [epistemicMeasure, Measure.prod_apply hmeas,
    lintegral_dirac' _ (measurable_measure_prodMk_left hmeas)]
  have hslice : Prod.mk p ⁻¹' edgeBand c δ i
      = (rep ⁻¹' Ioc (loSum (c.rate p) i + c.rate p i - δ) (loSum (c.rate p) i + c.rate p i))
        ×ˢ (univ : Set (AddCircle (1 : ℝ))) := by
    ext θ
    simp [edgeBand, cellTop, Set.mem_prod]
  rw [hslice, Measure.volume_eq_prod, Measure.prod_prod, circleFibre_volume_univ, mul_one]
  have h := volume_rep_preimage_Ioc_le (loSum (c.rate p) i + c.rate p i - δ)
    (loSum (c.rate p) i + c.rate p i)
  rwa [show loSum (c.rate p) i + c.rate p i - (loSum (c.rate p) i + c.rate p i - δ) = δ from by
    ring] at h

/-- ★★ **Robustness is controlled by the Born weight.** The `δ`-robust interior of the basin of `i`
has epistemic measure at least `rate p i − δ`. A record of large Born weight survives writes far
larger than one of small weight, and a cell of weight below `δ` is granted no robustness at all: the
*macroscopic* records — the heavy ones — are the stable ones, quantitatively. -/
theorem measure_robustBasin_ge (c : ContextField N) {δ : ℝ} (hδ : 0 ≤ δ) (i : Fin N)
    (p : LF4.CPN N) :
    ENNReal.ofReal (c.rate p i - δ) ≤ epistemicMeasure p (robustBasin c δ i) := by
  have hsplit : epistemicMeasure p (globalBasin c i)
      ≤ epistemicMeasure p (robustBasin c δ i) + epistemicMeasure p (edgeBand c δ i) :=
    le_trans (measure_mono (globalBasin_subset_robustBasin_union_edgeBand c δ i))
      (measure_union_le _ _)
  rw [globalBasin_prob] at hsplit
  have hb : ENNReal.ofReal (c.rate p i)
      ≤ epistemicMeasure p (robustBasin c δ i) + ENNReal.ofReal δ :=
    le_trans hsplit (add_le_add (le_refl _) (measure_edgeBand_le c δ i p))
  rw [ENNReal.ofReal_sub _ hδ]
  exact tsub_le_iff_right.2 hb

/-- ★★ **The overwhelming-majority half, conditional on concentration.** If a context's weights
concentrate at the preparation — `1 − ε ≤ rate p i`, which is what a pointer-like apparatus is
supposed to produce — then the microstates that *share* outcome `i` **and** are robust to writes of
size `δ` carry all but `ε + δ` of the epistemic measure. This is "overwhelmingly many microstates
share the record" with the concentration as an explicit **hypothesis**: by `globalBasin_prob` the
cell of outcome `i` has measure *exactly* `rate p i`, so **no cell is overwhelming unless the Born
weights are** — a property of the preparation and the context, never of the coordinate. Supplying
that hypothesis from the dynamics is BACKLOG #105; `fs_chebyshev_concentration` is a statement about
base statistics and is not it. -/
theorem measure_robustBasin_ge_one_sub (c : ContextField N) {δ ε : ℝ} (hδ : 0 ≤ δ) (i : Fin N)
    (p : LF4.CPN N) (hconc : 1 - ε ≤ c.rate p i) :
    ENNReal.ofReal (1 - ε - δ) ≤ epistemicMeasure p (robustBasin c δ i) :=
  le_trans (ENNReal.ofReal_le_ofReal (by linarith)) (measure_robustBasin_ge c hδ i p)

/-! ### The microstates a write can relabel -/

/-- **The microstates a write of size `δ` can relabel**, for one context: those outside every basin
(a null set) and those in some basin's boundary band. -/
noncomputable def unstableSet (c : ContextField N) (δ : ℝ) : Set (LF4.KSigma N) :=
  (⋃ i, globalBasin c i)ᶜ ∪ ⋃ i, edgeBand c δ i

/-- Outside the unstable set a microstate has margin `δ` in some basin — the converse direction the
measure bounds need. -/
theorem exists_robustBasin_of_notMem_unstableSet (c : ContextField N) (δ : ℝ)
    {x : LF4.KSigma N} (hx : x ∉ unstableSet c δ) : ∃ i, x ∈ robustBasin c δ i := by
  rw [unstableSet, Set.mem_union, not_or] at hx
  obtain ⟨h1, h2⟩ := hx
  have h1' : x ∈ ⋃ i, globalBasin c i := by simpa using h1
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 h1'
  refine ⟨i, ?_⟩
  rcases globalBasin_subset_robustBasin_union_edgeBand c δ i hi with h | h
  · exact h
  · exact absurd (Set.mem_iUnion.2 ⟨i, h⟩) h2

/-- **The unstable set of one context has measure at most `N · δ`**: one band per outcome, plus the
null set where no basin contains the microstate (`globalBasin_ae_total`). -/
theorem measure_unstableSet_le (c : ContextField N) (δ : ℝ) (p : LF4.CPN N) :
    epistemicMeasure p (unstableSet c δ) ≤ (N : ENNReal) * ENNReal.ofReal δ := by
  have h0 : epistemicMeasure p (⋃ i, globalBasin c i)ᶜ = 0 := by
    have h := globalBasin_ae_total c p
    rwa [Set.compl_eq_univ_sdiff]
  calc epistemicMeasure p (unstableSet c δ)
      ≤ epistemicMeasure p (⋃ i, globalBasin c i)ᶜ
          + epistemicMeasure p (⋃ i, edgeBand c δ i) := measure_union_le _ _
    _ = epistemicMeasure p (⋃ i, edgeBand c δ i) := by rw [h0, zero_add]
    _ ≤ ∑ i, epistemicMeasure p (edgeBand c δ i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin N, ENNReal.ofReal δ :=
        Finset.sum_le_sum fun i _ => measure_edgeBand_le c δ i p
    _ = (N : ENNReal) * ENNReal.ofReal δ := by simp [Finset.sum_const, nsmul_eq_mul]

/-! ### Quantitative stability of the record macrostate -/

/-- ★★★ **Quantitative stability of record macrostates.** The microstates whose **record string** a
write of size `δ` changes have epistemic measure at most `k · N · δ`, for a family of `k` contexts
over `N` outcomes. This is the measure-theoretic statement #103 asked for: the cells are not
invariant, but the set of microstates that cross a cell boundary shrinks linearly with the write. -/
theorem measure_recordString_ne_le {k : ℕ} (c : Fin k → ContextField N) {δ : ℝ} (hδ : 0 ≤ δ)
    (p : LF4.CPN N) :
    epistemicMeasure p {x | recordString c (sigmaShift δ x) ≠ recordString c x}
      ≤ (k : ENNReal) * ((N : ENNReal) * ENNReal.ofReal δ) := by
  have hsub : {x : LF4.KSigma N | recordString c (sigmaShift δ x) ≠ recordString c x}
      ⊆ ⋃ j, unstableSet (c j) δ := by
    intro x hx
    by_contra hmem
    simp only [Set.mem_iUnion, not_exists] at hmem
    exact hx (recordString_sigmaShift c hδ
      fun j => exists_robustBasin_of_notMem_unstableSet (c j) δ (hmem j))
  calc epistemicMeasure p {x | recordString c (sigmaShift δ x) ≠ recordString c x}
      ≤ epistemicMeasure p (⋃ j, unstableSet (c j) δ) := measure_mono hsub
    _ ≤ ∑ j, epistemicMeasure p (unstableSet (c j) δ) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin k, ((N : ENNReal) * ENNReal.ofReal δ) :=
        Finset.sum_le_sum fun j _ => measure_unstableSet_le (c j) δ p
    _ = (k : ENNReal) * ((N : ENNReal) * ENNReal.ofReal δ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- ★★★ **One exceptional set serves the whole horizon.** The microstates whose record string is
changed by *some* write of size at most `δ` have the same bound: the margin bought at `δ` covers
every smaller write, so no second argument and no union over times is needed. -/
theorem measure_exists_recordString_ne_le {k : ℕ} (c : Fin k → ContextField N) (δ : ℝ)
    (p : LF4.CPN N) :
    epistemicMeasure p
        {x | ∃ s ∈ Icc (0 : ℝ) δ, recordString c (sigmaShift s x) ≠ recordString c x}
      ≤ (k : ENNReal) * ((N : ENNReal) * ENNReal.ofReal δ) := by
  have hsub : {x : LF4.KSigma N |
        ∃ s ∈ Icc (0 : ℝ) δ, recordString c (sigmaShift s x) ≠ recordString c x}
      ⊆ ⋃ j, unstableSet (c j) δ := by
    intro x hx
    obtain ⟨s, hs, hne⟩ := hx
    by_contra hmem
    simp only [Set.mem_iUnion, not_exists] at hmem
    exact hne (recordString_sigmaShift_of_le c hs.1 hs.2
      fun j => exists_robustBasin_of_notMem_unstableSet (c j) δ (hmem j))
  calc epistemicMeasure p
        {x | ∃ s ∈ Icc (0 : ℝ) δ, recordString c (sigmaShift s x) ≠ recordString c x}
      ≤ epistemicMeasure p (⋃ j, unstableSet (c j) δ) := measure_mono hsub
    _ ≤ ∑ j, epistemicMeasure p (unstableSet (c j) δ) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin k, ((N : ENNReal) * ENNReal.ofReal δ) :=
        Finset.sum_le_sum fun j _ => measure_unstableSet_le (c j) δ p
    _ = (k : ENNReal) * ((N : ENNReal) * ENNReal.ofReal δ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- ★★★ **Persistence over a horizon.** Under a drift of the record coordinate at rate `ω`, the
record string of the family survives the *entire* interval `[0, T]` outside a set of epistemic
measure at most `k · N · ω · T`. This is #103's "persistence over a horizon", with the horizon
appearing only through the total drift. -/
theorem measure_drift_recordString_ne_le {k : ℕ} (c : Fin k → ContextField N) {ω : ℝ}
    (hω : 0 ≤ ω) (T : ℝ) (p : LF4.CPN N) :
    epistemicMeasure p
        {x | ∃ t ∈ Icc (0 : ℝ) T, recordString c (sigmaShift (ω * t) x) ≠ recordString c x}
      ≤ (k : ENNReal) * ((N : ENNReal) * ENNReal.ofReal (ω * T)) := by
  refine le_trans (measure_mono ?_) (measure_exists_recordString_ne_le c (ω * T) p)
  intro x hx
  obtain ⟨t, ht, hne⟩ := hx
  exact ⟨ω * t, ⟨mul_nonneg hω ht.1, mul_le_mul_of_nonneg_left ht.2 hω⟩, hne⟩

/-- ★ **The relabelled set vanishes as the write shrinks.** The qualitative form of the bound: in the
limit of small writes the record macrostate is stable almost everywhere. -/
theorem tendsto_measure_recordString_ne {k : ℕ} (c : Fin k → ContextField N) (p : LF4.CPN N) :
    Filter.Tendsto
      (fun δ : ℝ => epistemicMeasure p {x | recordString c (sigmaShift δ x) ≠ recordString c x})
      (nhdsWithin 0 (Ici 0)) (nhds 0) := by
  have hofReal : Filter.Tendsto (fun δ : ℝ => ENNReal.ofReal δ) (nhdsWithin 0 (Ici 0))
      (nhds 0) := by
    have h : Filter.Tendsto (fun δ : ℝ => δ) (nhdsWithin 0 (Ici (0 : ℝ))) (nhds 0) :=
      nhdsWithin_le_nhds
    simpa using ENNReal.tendsto_ofReal h
  have h1 : Filter.Tendsto (fun δ : ℝ => (N : ENNReal) * ENNReal.ofReal δ)
      (nhdsWithin 0 (Ici (0 : ℝ))) (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hofReal (Or.inr (by simp))
  have hbound : Filter.Tendsto
      (fun δ : ℝ => (k : ENNReal) * ((N : ENNReal) * ENNReal.ofReal δ))
      (nhdsWithin 0 (Ici (0 : ℝ))) (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul h1 (Or.inr (by simp))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Filter.Eventually.of_forall fun δ => zero_le)
    (eventually_mem_nhdsWithin.mono fun δ hδ => measure_recordString_ne_le c hδ p)

/-! ### Exact invariance of the macroscopic law -/

/-- ★★★ **The macroscopic law is exactly invariant under a record write.** The write preserves the
epistemic measure, so the **distribution** of the record string is unchanged — for every write size,
with no error term and no margin hypothesis. Together with `measure_recordString_ne_le` this is the
honest content of "the record macrostates are stable": the macroscopic *statistics* do not move at
all, while the macrostate of an individual microstate moves only on a set of measure `O(δ)`. -/
theorem map_recordString_sigmaShift {k : ℕ} (c : Fin k → ContextField N) (δ : ℝ)
    (p : LF4.CPN N) :
    (epistemicMeasure p).map (fun x => recordString c (sigmaShift δ x))
      = (epistemicMeasure p).map (recordString c) := by
  rw [show (fun x : LF4.KSigma N => recordString c (sigmaShift δ x))
        = recordString c ∘ sigmaShift δ from rfl,
    ← Measure.map_map (measurable_recordString c) (measurable_sigmaShift δ),
    (measurePreserving_sigmaShift δ p).map_eq]

end CSD.RecordLayer

end
