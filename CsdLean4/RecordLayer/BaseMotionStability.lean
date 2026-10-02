/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.MacrostateStability

/-!
# Stability of record macrostates under motion of the base

**Category:** 7-SigmaLayer (the record layer — Paper C A7).
BACKLOG #104, out of #103.

[`MacrostateStability.lean`](MacrostateStability.lean) (#103) proved the stability of #102's record
string under motion of the **fibre**: the macroscopic law exactly invariant, the pointwise string
unchanged outside a set of epistemic measure `k·N·δ`. That is the only channel a record *write*
opens. A flow of `Σ` also moves the **base**, and then the arcs themselves move, because
`globalBasin c i` is cut out by the rate field *at the microstate's own base point*. This file
carries the margin argument over that motion.

## What the hypothesis is, and what it is not

The displacement of the arcs is a **hypothesis**, stated directly on the endpoints:

* `arcLo`, `arcHi` — the two endpoints of a context's arc, as functions of the base point;
* `ArcShift c ε p q` — every arc of `c` moves by at most `ε` between the base points `p` and `q`.
  ⚠️ **This needs no metric on the base**, and so no continuity of the rate field either. #104's row
  text proposed a `LipschitzWith` hypothesis; the endpoint form is strictly weaker, available at the
  pin, and is what the margin argument actually consumes;
* ★ `arcShift_of_rate_close` — if the *rates* move by at most `η` coordinatewise then
  `ArcShift c ((N+1)·η)`, since each endpoint is a sum of at most `N + 1` rates. A modulus of
  continuity on the rate field enters here and nowhere else.

## What is proved

* `sigmaMove f g` — **a move of `Σ`**: a measurable motion `f` of the base together with a
  **base-dependent** record write `g`. `sigmaMove id (fun _ => δ)` is #103's `sigmaShift`;
* ★ `ae_fst_eq` — the epistemic measure lives on the fibre over its own preparation, and hence
  ★★★ `map_sigmaMove`: **the epistemic law is carried exactly to the law at the moved base**,
  `(epistemicMeasure p).map (sigmaMove f g) = epistemicMeasure (f p)`. This is the right form of
  #103's exact half once the base moves: the macroscopic law is *not* invariant — the Born weights
  are those of the moved base point — and the transport is still exact, with no error term. The
  `f = id` case ★★ `map_sigmaMove_id` **discharges a caveat of #103**: a base-*dependent* write, the
  `recordStroke` of `CV/RecordInfluence.lean`, preserves the epistemic law exactly;
* `robustBasin₂ c δ ε i` — the **two-sided** robust interior: margin `ε` at the lower endpoint and
  `δ + ε` at the upper one. Two-sided because a base motion can move the lower endpoint *up*, which a
  record write alone never does (`robustBasin₂_zero` recovers #103's one-sided set at `ε = 0`);
* ★★ `sigmaMove_mem_globalBasin` — **the margin lemma with the base in motion**, and hence
  ★★ `outcomeCode_sigmaMove`, ★★★ `recordString_sigmaMove` and ★★ `recordMacro_sigmaMove`;
* ★★★ `measure_recordString_ne_sigmaMove_le` — **the microstates a move relabels have epistemic
  measure at most `k·N·(δ + 2ε)`**, and ★★ `measure_recordString_ne_sigmaMove_rate_le` gives the
  same in terms of the rate displacement, `k·N·(δ + 2(N+1)η)`;
* ★★ `measure_robustBasin₂_ge` — robustness is still controlled by the **Born weight**:
  `rate p i − (δ + 2ε)` bounds the two-sided robust interior below;
* ★★★ `measure_exists_recordString_ne_flow_le` — **one exceptional set serves a whole flow.** For a
  one-parameter family of moves whose write stays in `[0, δ]` and whose arc displacement stays below
  `ε` over `[0, T]`, the record string survives the *entire* horizon outside that same
  `k·N·(δ + 2ε)`. This is what #103's drift corollary becomes once the base is allowed to move, and
  it needs no new argument: the robust set does not depend on the parameter.

## Honest scope

⚠️ **The arc displacement is assumed, not derived.** Nothing here shows that any particular flow of
`Σ` — least of all a Hamiltonian one — moves the arcs by a bounded amount, and `ContextField` still
carries no regularity beyond measurability. What `arcShift_of_rate_close` buys is the reduction of
the hypothesis to a modulus of continuity on the rate field; supplying *that* for the canonical
`momentContext` is not done here, and `LF4.momentMap` has no recorded modulus.

⚠️ **The motion of the base is an arbitrary measurable map, not a flow.** `f` is not assumed
invertible, measure-preserving, continuous, or part of a one-parameter group, and no generator is
constructed. `measure_exists_recordString_ne_flow_le` quantifies over a family of such maps; calling
it a flow is a convenience of the name, not a claim about its structure.

⚠️ **Still not invariance, and still no mixing.** As in #103, no cell is shown to be an invariant
set and `not_hasCorrelationDecay_blockPop_of_unitary` is untouched. Note the exact half is *weaker*
here than in #103 and deliberately so: the law moves to `epistemicMeasure (f p)`, so a base motion
changes the macroscopic statistics, which is what it should do.

⚠️ **The bound degrades as `k·N`, and in `N` again through the rates.** `δ + 2(N+1)η` carries a
second factor of `N`, so the rate field has to be *uniformly* close for a large alphabet. No better
constant is claimed, and records of Born weight below `δ + 2ε` are granted no robustness at all.

⚠️ **The typicality half is untouched.** As in #103, "overwhelmingly many microstates share it" is
conditional on concentration of the weights and is BACKLOG #105; nothing here supplies it, and
`fs_chebyshev_concentration` is still a statement about base statistics.

References: [`records-to-spacetime-scoping.md`](../../specs/records-to-spacetime-scoping.md) `ST-3`;
[`future-work.md`](../../specs/future-work.md); `MacrostateStability.lean` (#103),
`RecordMacrostate.lean` (#102), `MacroProjection.lean` (#99), `GlobalBasin.lean`,
[`CV/RecordInfluence.lean`](../CV/RecordInfluence.lean) (`fibreShift`, `recordStroke`);
`specs/BACKLOG.md` #104, #103, #105, #100.
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

variable {N : ℕ}

/-! ### The arc endpoints as functions of the base point -/

/-- The **lower endpoint** of the arc a context assigns to outcome `i`, as a function of the base
point. `globalBasin` reads the rate field at the microstate's own base, so moving the base moves this
endpoint — which is what #103 did not have to consider. -/
noncomputable def arcLo (c : ContextField N) (i : Fin N) (p : LF4.CPN N) : ℝ :=
  loSum (c.rate p) i

/-- The **upper endpoint** of the arc, as a function of the base point. Agrees with #103's `cellTop`
read at `x.1`. -/
noncomputable def arcHi (c : ContextField N) (i : Fin N) (p : LF4.CPN N) : ℝ :=
  loSum (c.rate p) i + c.rate p i

theorem cellTop_eq_arcHi (c : ContextField N) (i : Fin N) (x : LF4.KSigma N) :
    cellTop c i x = arcHi c i x.1 := rfl

theorem arcHi_le_one (c : ContextField N) (i : Fin N) (p : LF4.CPN N) : arcHi c i p ≤ 1 :=
  c.loSum_le_one p i

theorem arcLo_nonneg (c : ContextField N) (i : Fin N) (p : LF4.CPN N) : 0 ≤ arcLo c i p := by
  rw [arcLo, loSum]
  exact Finset.sum_nonneg fun j _ => c.nonneg p j

theorem measurable_arcLo (c : ContextField N) (i : Fin N) : Measurable (arcLo c i) :=
  c.measurable_loSum i

theorem measurable_arcHi (c : ContextField N) (i : Fin N) : Measurable (arcHi c i) :=
  (c.measurable_loSum i).add (c.measurable_rate i)

/-- The basin, written in the endpoint functions — the form the base-motion argument consumes. -/
theorem mem_globalBasin_iff_arc (c : ContextField N) (i : Fin N) (x : LF4.KSigma N) :
    x ∈ globalBasin c i ↔ arcLo c i x.1 < rep x.2.1 ∧ rep x.2.1 ≤ arcHi c i x.1 :=
  mem_globalBasin_iff c i x

/-! ### The displacement of the arcs -/

/-- **The arcs of `c` move by at most `ε` between the base points `p` and `q`.** This is the whole
hypothesis the base-motion bound needs: it mentions **no metric on the base**, hence no continuity of
the rate field, only that the endpoints do not travel far. -/
def ArcShift (c : ContextField N) (ε : ℝ) (p q : LF4.CPN N) : Prop :=
  ∀ i, |arcLo c i q - arcLo c i p| ≤ ε ∧ |arcHi c i q - arcHi c i p| ≤ ε

theorem arcShift_refl (c : ContextField N) {ε : ℝ} (hε : 0 ≤ ε) (p : LF4.CPN N) :
    ArcShift c ε p p := fun i => by
  simp only [sub_self, abs_zero]
  exact ⟨hε, hε⟩

theorem ArcShift.mono {c : ContextField N} {ε ε' : ℝ} {p q : LF4.CPN N} (h : ArcShift c ε p q)
    (hle : ε ≤ ε') : ArcShift c ε' p q :=
  fun i => ⟨le_trans (h i).1 hle, le_trans (h i).2 hle⟩

/-- **A partial sum of rates moves by at most `n · η`** when each rate does. The arithmetic behind
`arcShift_of_rate_close`. -/
theorem abs_loSum_sub_le {n : ℕ} (r r' : Fin n → ℝ) {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ j, |r' j - r j| ≤ η) (i : Fin n) : |loSum r' i - loSum r i| ≤ (n : ℝ) * η := by
  classical
  have hsub : loSum r' i - loSum r i
      = ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < (i : ℕ)), (r' j - r j) := by
    rw [loSum, loSum, Finset.sum_sub_distrib]
  have hcard : ((Finset.univ.filter fun j : Fin n => (j : ℕ) < (i : ℕ)).card : ℝ) ≤ (n : ℝ) := by
    have hc : (Finset.univ.filter fun j : Fin n => (j : ℕ) < (i : ℕ)).card ≤ n := by
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n)) _
    exact_mod_cast hc
  rw [hsub]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ η fun j _ => h j) ?_
  calc (Finset.univ.filter fun j : Fin n => (j : ℕ) < (i : ℕ)).card • η
      = ((Finset.univ.filter fun j : Fin n => (j : ℕ) < (i : ℕ)).card : ℝ) * η := by
        simp [nsmul_eq_mul]
    _ ≤ (n : ℝ) * η := mul_le_mul_of_nonneg_right hcard hη

/-- ★ **A modulus of continuity on the rate field bounds the arc displacement.** Each endpoint is a
sum of at most `N + 1` rates, so rates within `η` put the arcs within `(N+1)·η`. This is the only
place a regularity assumption on `ContextField` would enter, and #104's row proposed it as a
`LipschitzWith` hypothesis; the endpoint form `ArcShift` is weaker and is what the margin lemma
uses. -/
theorem arcShift_of_rate_close (c : ContextField N) {η : ℝ} (hη : 0 ≤ η) {p q : LF4.CPN N}
    (h : ∀ j, |c.rate q j - c.rate p j| ≤ η) : ArcShift c (((N : ℝ) + 1) * η) p q := by
  intro i
  have hlo : |arcLo c i q - arcLo c i p| ≤ (N : ℝ) * η :=
    abs_loSum_sub_le (c.rate p) (c.rate q) hη h i
  refine ⟨le_trans hlo (mul_le_mul_of_nonneg_right (by linarith) hη), ?_⟩
  have hhi : arcHi c i q - arcHi c i p
      = (arcLo c i q - arcLo c i p) + (c.rate q i - c.rate p i) := by
    simp only [arcHi, arcLo]
    ring
  rw [hhi]
  refine le_trans (abs_add_le _ _) ?_
  calc |arcLo c i q - arcLo c i p| + |c.rate q i - c.rate p i|
      ≤ (N : ℝ) * η + η := add_le_add hlo (h i)
    _ = ((N : ℝ) + 1) * η := by ring

/-! ### A move of `Σ`: the base travels and a record is written -/

/-- **A move of `Σ`**: a motion `f` of the ontic base point together with a **base-dependent** record
write `g`, the amount written into the record coordinate at each base point. `sigmaMove id
(fun _ => δ)` is #103's `sigmaShift`, and `sigmaMove id g` is the base-dependent write of
`CV/RecordInfluence.lean`'s `recordStroke`. -/
def sigmaMove (f : LF4.CPN N → LF4.CPN N) (g : LF4.CPN N → ℝ) (x : LF4.KSigma N) :
    LF4.KSigma N :=
  (f x.1, (x.2.1 + ((g x.1 : ℝ) : AddCircle (1 : ℝ)), x.2.2))

@[simp] theorem sigmaMove_fst (f : LF4.CPN N → LF4.CPN N) (g : LF4.CPN N → ℝ)
    (x : LF4.KSigma N) : (sigmaMove f g x).1 = f x.1 := rfl

@[simp] theorem sigmaMove_record (f : LF4.CPN N → LF4.CPN N) (g : LF4.CPN N → ℝ)
    (x : LF4.KSigma N) :
    (sigmaMove f g x).2.1 = x.2.1 + ((g x.1 : ℝ) : AddCircle (1 : ℝ)) := rfl

@[simp] theorem sigmaMove_partner (f : LF4.CPN N → LF4.CPN N) (g : LF4.CPN N → ℝ)
    (x : LF4.KSigma N) : (sigmaMove f g x).2.2 = x.2.2 := rfl

theorem sigmaMove_id_const (δ : ℝ) :
    sigmaMove (id : LF4.CPN N → LF4.CPN N) (fun _ => δ) = sigmaShift (N := N) δ := rfl

theorem measurable_sigmaMove {f : LF4.CPN N → LF4.CPN N} {g : LF4.CPN N → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (sigmaMove f g) :=
  (hf.comp measurable_fst).prodMk
    (((measurable_fst.comp measurable_snd).add
      (AddCircle.measurable_mk'.comp (hg.comp measurable_fst))).prodMk
      (measurable_snd.comp measurable_snd))

/-! ### The epistemic law transports exactly -/

/-- ★ **The epistemic measure lives on the fibre over its own preparation.** Available because
`LF4.CPN N` has measurable singletons, which is what lets a *base-dependent* write be replaced by a
constant one almost everywhere. -/
theorem ae_fst_eq (p : LF4.CPN N) : ∀ᵐ x ∂(epistemicMeasure p), x.1 = p := by
  rw [MeasureTheory.ae_iff]
  have hmeas : MeasurableSet {x : LF4.KSigma N | ¬ x.1 = p} :=
    measurable_fst (measurableSet_singleton p).compl
  rw [epistemicMeasure, Measure.prod_apply hmeas,
    lintegral_dirac' _ (measurable_measure_prodMk_left hmeas)]
  have hempty : Prod.mk p ⁻¹' {x : LF4.KSigma N | ¬ x.1 = p} = (∅ : Set LF4.KTorus) := by
    ext θ
    simp
  rw [hempty, measure_empty]

/-- ★★★ **The epistemic law is carried exactly to the law at the moved base.** The write translates
the record coordinate, which Haar measure absorbs; the base map carries the Dirac factor to the Dirac
factor at `f p`. So the macroscopic law after a move is the macroscopic law of the moved preparation —
**not** the same law, and the transport is nevertheless exact, with no error term and no margin
hypothesis. This is #103's exact half in the form it takes once the base is allowed to move. -/
theorem map_sigmaMove {f : LF4.CPN N → LF4.CPN N} (hf : Measurable f) (g : LF4.CPN N → ℝ)
    (p : LF4.CPN N) :
    (epistemicMeasure p).map (sigmaMove f g) = epistemicMeasure (f p) := by
  have hae : sigmaMove f g =ᵐ[epistemicMeasure p] sigmaMove f (fun _ => g p) := by
    filter_upwards [ae_fst_eq p] with x hx
    simp only [sigmaMove, hx]
  have hprod : sigmaMove f (fun _ => g p)
      = Prod.map f (Prod.map (fun θ : AddCircle (1 : ℝ) => θ + ((g p : ℝ) : AddCircle (1 : ℝ)))
          (id : AddCircle (1 : ℝ) → AddCircle (1 : ℝ))) := by
    funext x
    rfl
  have htorus := measurePreserving_torusShift (g p)
  calc (epistemicMeasure p).map (sigmaMove f g)
      = (epistemicMeasure p).map (sigmaMove f (fun _ => g p)) := Measure.map_congr hae
    _ = ((Measure.dirac p).prod (volume : Measure LF4.KTorus)).map
          (Prod.map f (Prod.map
            (fun θ : AddCircle (1 : ℝ) => θ + ((g p : ℝ) : AddCircle (1 : ℝ)))
            (id : AddCircle (1 : ℝ) → AddCircle (1 : ℝ)))) := by rw [epistemicMeasure, hprod]
    _ = ((Measure.dirac p).map f).prod ((volume : Measure LF4.KTorus).map _) :=
        (Measure.map_prod_map _ _ hf htorus.measurable).symm
    _ = (Measure.dirac (f p)).prod (volume : Measure LF4.KTorus) := by
        rw [Measure.map_dirac, htorus.map_eq]
    _ = epistemicMeasure (f p) := rfl

/-- ★★ **A base-dependent record write preserves the epistemic law exactly.** The `f = id` case, and
the discharge of #103's caveat: `CV/RecordInfluence.lean`'s `recordStroke` translates the fibre by an
amount read off the base, and that is covered. -/
theorem map_sigmaMove_id (g : LF4.CPN N → ℝ) (p : LF4.CPN N) :
    (epistemicMeasure p).map (sigmaMove id g) = epistemicMeasure p :=
  map_sigmaMove measurable_id g p

/-! ### The two-sided robust interior -/

/-- **The `(δ, ε)`-robust interior of a basin**: margin `ε` at the lower endpoint and `δ + ε` at the
upper one. **Two-sided**, because a base motion can move the lower endpoint *up*, which a record
write alone never does. -/
noncomputable def robustBasin₂ (c : ContextField N) (δ ε : ℝ) (i : Fin N) : Set (LF4.KSigma N) :=
  {x | arcLo c i x.1 + ε < rep x.2.1 ∧ rep x.2.1 + (δ + ε) ≤ arcHi c i x.1}

/-- **The `ε`-boundary band at the lower endpoint**: the first `ε` of the arc, the part a base motion
can push out from below. -/
noncomputable def lowerBand (c : ContextField N) (ε : ℝ) (i : Fin N) : Set (LF4.KSigma N) :=
  {x | arcLo c i x.1 < rep x.2.1 ∧ rep x.2.1 ≤ arcLo c i x.1 + ε}

theorem robustBasin₂_zero (c : ContextField N) (δ : ℝ) (i : Fin N) :
    robustBasin₂ c δ 0 i = robustBasin c δ i := by
  ext x
  simp only [robustBasin₂, robustBasin, Set.mem_ofPred_eq, add_zero]
  rfl

theorem measurableSet_robustBasin₂ (c : ContextField N) (δ ε : ℝ) (i : Fin N) :
    MeasurableSet (robustBasin₂ c δ ε i) :=
  (measurableSet_lt (((measurable_arcLo c i).comp measurable_fst).add_const ε)
      measurable_repRecord).inter
    (measurableSet_le (measurable_repRecord.add_const (δ + ε))
      ((measurable_arcHi c i).comp measurable_fst))

theorem measurableSet_lowerBand (c : ContextField N) (ε : ℝ) (i : Fin N) :
    MeasurableSet (lowerBand c ε i) :=
  (measurableSet_lt ((measurable_arcLo c i).comp measurable_fst) measurable_repRecord).inter
    (measurableSet_le measurable_repRecord
      (((measurable_arcLo c i).comp measurable_fst).add_const ε))

theorem robustBasin₂_subset_globalBasin (c : ContextField N) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (i : Fin N) : robustBasin₂ c δ ε i ⊆ globalBasin c i := by
  intro x hx
  obtain ⟨hlo, hhi⟩ := hx
  rw [mem_globalBasin_iff_arc]
  exact ⟨by linarith, by linarith⟩

theorem robustBasin₂_mono (c : ContextField N) {δ δ' ε ε' : ℝ} (hδ : δ' ≤ δ) (hε : ε' ≤ ε)
    (i : Fin N) : robustBasin₂ c δ ε i ⊆ robustBasin₂ c δ' ε' i := by
  intro x hx
  obtain ⟨hlo, hhi⟩ := hx
  exact ⟨by linarith, by linarith⟩

/-- ★ **Every basin splits into its two-sided robust interior and its two boundary bands.** -/
theorem globalBasin_subset_robustBasin₂_union (c : ContextField N) (δ ε : ℝ) (i : Fin N) :
    globalBasin c i ⊆ robustBasin₂ c δ ε i ∪ lowerBand c ε i ∪ edgeBand c (δ + ε) i := by
  intro x hx
  rw [mem_globalBasin_iff_arc] at hx
  by_cases hlow : rep x.2.1 ≤ arcLo c i x.1 + ε
  · exact Or.inl (Or.inr ⟨hx.1, hlow⟩)
  · by_cases hhigh : rep x.2.1 + (δ + ε) ≤ arcHi c i x.1
    · exact Or.inl (Or.inl ⟨not_le.1 hlow, hhigh⟩)
    · exact Or.inr ⟨by
        have := not_le.1 hhigh
        have harc : cellTop c i x = arcHi c i x.1 := rfl
        rw [harc]
        linarith, by
        have harc : cellTop c i x = arcHi c i x.1 := rfl
        rw [harc]
        exact hx.2⟩

/-! ### The margin lemma with the base in motion -/

/-- ★★ **The margin lemma under a move of `Σ`.** A move whose write is at most `δ` and whose arcs
travel at most `ε` cannot take a microstate out of a basin it is `(δ, ε)`-robustly inside. Both
endpoints are in play: the lower one is cleared by the margin `ε`, the upper one by `δ + ε`. -/
theorem sigmaMove_mem_globalBasin (c : ContextField N) {f : LF4.CPN N → LF4.CPN N}
    {g : LF4.CPN N → ℝ} {δ ε : ℝ} (i : Fin N) {x : LF4.KSigma N}
    (hg0 : 0 ≤ g x.1) (hgδ : g x.1 ≤ δ) (harc : ArcShift c ε x.1 (f x.1))
    (hx : x ∈ robustBasin₂ c δ ε i) : sigmaMove f g x ∈ globalBasin c i := by
  obtain ⟨hlo, hhi⟩ := hx
  obtain ⟨h1, h2⟩ := harc i
  obtain ⟨h1a, h1b⟩ := abs_le.1 h1
  obtain ⟨h2a, h2b⟩ := abs_le.1 h2
  have hmem : rep x.2.1 + g x.1 ∈ Ioc (0 : ℝ) 1 :=
    ⟨by linarith [rep_pos x.2.1], by
      have := arcHi_le_one c i x.1
      linarith⟩
  rw [mem_globalBasin_iff_arc]
  simp only [sigmaMove_fst, sigmaMove_record, rep_add_coe hmem]
  exact ⟨by linarith, by linarith⟩

/-- ★★ **A move does not change the outcome a context assigns** to a microstate robustly inside one
of its basins. -/
theorem outcomeCode_sigmaMove (c : ContextField N) {f : LF4.CPN N → LF4.CPN N}
    {g : LF4.CPN N → ℝ} {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) {i : Fin N} {x : LF4.KSigma N}
    (hg0 : 0 ≤ g x.1) (hgδ : g x.1 ≤ δ) (harc : ArcShift c ε x.1 (f x.1))
    (hx : x ∈ robustBasin₂ c δ ε i) :
    outcomeCode c (sigmaMove f g x) = outcomeCode c x := by
  rw [(outcomeCode_eq_succ_iff c (sigmaMove f g x) i).2
      (sigmaMove_mem_globalBasin c i hg0 hgδ harc hx),
    (outcomeCode_eq_succ_iff c x i).2 (robustBasin₂_subset_globalBasin c hδ hε i hx)]

/-- ★★★ **A move of `Σ` leaves the whole record string intact** on a microstate robustly inside a
basin of every context of the family. -/
theorem recordString_sigmaMove {k : ℕ} (c : Fin k → ContextField N)
    {f : LF4.CPN N → LF4.CPN N} {g : LF4.CPN N → ℝ} {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    {x : LF4.KSigma N} (hg0 : 0 ≤ g x.1) (hgδ : g x.1 ≤ δ)
    (harc : ∀ j, ArcShift (c j) ε x.1 (f x.1))
    (hx : ∀ j, ∃ i, x ∈ robustBasin₂ (c j) δ ε i) :
    recordString c (sigmaMove f g x) = recordString c x := by
  funext j
  obtain ⟨i, hi⟩ := hx j
  exact outcomeCode_sigmaMove (c j) hδ hε hg0 hgδ (harc j) hi

/-- ★★ **The macrostate of #102 is preserved under a move of `Σ`**, stated on `recordMacro`. -/
theorem recordMacro_sigmaMove {k : ℕ} (c : Fin k → ContextField N)
    {f : LF4.CPN N → LF4.CPN N} {g : LF4.CPN N → ℝ} {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    {x : LF4.KSigma N} (hg0 : 0 ≤ g x.1) (hgδ : g x.1 ≤ δ)
    (harc : ∀ j, ArcShift (c j) ε x.1 (f x.1))
    (hx : ∀ j, ∃ i, x ∈ robustBasin₂ (c j) δ ε i) :
    (recordMacro c).toFun (sigmaMove f g x) = (recordMacro c).toFun x :=
  recordString_sigmaMove c hδ hε hg0 hgδ harc hx

/-! ### The measure of the two bands -/

/-- **The lower band is small**: its slice over the preparation is the first `ε` of one arc. -/
theorem measure_lowerBand_le (c : ContextField N) (ε : ℝ) (i : Fin N) (p : LF4.CPN N) :
    epistemicMeasure p (lowerBand c ε i) ≤ ENNReal.ofReal ε := by
  have hmeas : MeasurableSet (lowerBand c ε i) := measurableSet_lowerBand c ε i
  rw [epistemicMeasure, Measure.prod_apply hmeas,
    lintegral_dirac' _ (measurable_measure_prodMk_left hmeas)]
  have hslice : Prod.mk p ⁻¹' lowerBand c ε i
      = (rep ⁻¹' Ioc (arcLo c i p) (arcLo c i p + ε)) ×ˢ (univ : Set (AddCircle (1 : ℝ))) := by
    ext θ
    simp [lowerBand, Set.mem_prod]
  rw [hslice, Measure.volume_eq_prod, Measure.prod_prod, circleFibre_volume_univ, mul_one]
  have h := volume_rep_preimage_Ioc_le (arcLo c i p) (arcLo c i p + ε)
  rwa [show arcLo c i p + ε - arcLo c i p = ε from by ring] at h

/-- ★★ **Robustness is still controlled by the Born weight.** The two-sided robust interior of the
basin of `i` has epistemic measure at least `rate p i − (δ + 2ε)`: a record of large Born weight
survives a move whose write and whose arc displacement are both small compared with its weight, and a
cell of weight below `δ + 2ε` is granted nothing. -/
theorem measure_robustBasin₂_ge (c : ContextField N) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (i : Fin N) (p : LF4.CPN N) :
    ENNReal.ofReal (c.rate p i - (δ + 2 * ε)) ≤ epistemicMeasure p (robustBasin₂ c δ ε i) := by
  have hsplit : epistemicMeasure p (globalBasin c i)
      ≤ epistemicMeasure p (robustBasin₂ c δ ε i ∪ lowerBand c ε i)
        + epistemicMeasure p (edgeBand c (δ + ε) i) :=
    le_trans (measure_mono (globalBasin_subset_robustBasin₂_union c δ ε i))
      (measure_union_le _ _)
  have hb : ENNReal.ofReal (c.rate p i)
      ≤ epistemicMeasure p (robustBasin₂ c δ ε i) + ENNReal.ofReal ε
        + ENNReal.ofReal (δ + ε) := by
    rw [← globalBasin_prob c i p]
    refine le_trans hsplit (add_le_add ?_ (measure_edgeBand_le c (δ + ε) i p))
    exact le_trans (measure_union_le _ _)
      (add_le_add (le_refl _) (measure_lowerBand_le c ε i p))
  have hsum : ENNReal.ofReal ε + ENNReal.ofReal (δ + ε) = ENNReal.ofReal (δ + 2 * ε) := by
    rw [← ENNReal.ofReal_add hε (by linarith)]
    congr 1
    ring
  rw [ENNReal.ofReal_sub _ (by linarith)]
  refine tsub_le_iff_right.2 ?_
  rw [← hsum, ← add_assoc]
  exact hb

/-! ### The microstates a move can relabel -/

/-- **The microstates a move of size `(δ, ε)` can relabel**, for one context: those outside every
basin (a null set) and those in either boundary band. -/
noncomputable def unstableSet₂ (c : ContextField N) (δ ε : ℝ) : Set (LF4.KSigma N) :=
  (⋃ i, globalBasin c i)ᶜ ∪ (⋃ i, lowerBand c ε i) ∪ ⋃ i, edgeBand c (δ + ε) i

theorem exists_robustBasin₂_of_notMem_unstableSet₂ (c : ContextField N) (δ ε : ℝ)
    {x : LF4.KSigma N} (hx : x ∉ unstableSet₂ c δ ε) : ∃ i, x ∈ robustBasin₂ c δ ε i := by
  rw [unstableSet₂, Set.mem_union, Set.mem_union, not_or, not_or] at hx
  obtain ⟨⟨h1, h2⟩, h3⟩ := hx
  have h1' : x ∈ ⋃ i, globalBasin c i := by simpa using h1
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 h1'
  refine ⟨i, ?_⟩
  rcases globalBasin_subset_robustBasin₂_union c δ ε i hi with h | h
  · rcases h with h | h
    · exact h
    · exact absurd (Set.mem_iUnion.2 ⟨i, h⟩) h2
  · exact absurd (Set.mem_iUnion.2 ⟨i, h⟩) h3

/-- **One context's unstable set has measure at most `N · (δ + 2ε)`**: two bands per outcome, plus
the null set where no basin contains the microstate. -/
theorem measure_unstableSet₂_le (c : ContextField N) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (p : LF4.CPN N) :
    epistemicMeasure p (unstableSet₂ c δ ε) ≤ (N : ENNReal) * ENNReal.ofReal (δ + 2 * ε) := by
  have h0 : epistemicMeasure p (⋃ i, globalBasin c i)ᶜ = 0 := by
    have h := globalBasin_ae_total c p
    rwa [Set.compl_eq_univ_sdiff]
  have hlow : epistemicMeasure p (⋃ i, lowerBand c ε i)
      ≤ (N : ENNReal) * ENNReal.ofReal ε := by
    calc epistemicMeasure p (⋃ i, lowerBand c ε i)
        ≤ ∑ i, epistemicMeasure p (lowerBand c ε i) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _i : Fin N, ENNReal.ofReal ε :=
          Finset.sum_le_sum fun i _ => measure_lowerBand_le c ε i p
      _ = (N : ENNReal) * ENNReal.ofReal ε := by simp [Finset.sum_const, nsmul_eq_mul]
  have hhigh : epistemicMeasure p (⋃ i, edgeBand c (δ + ε) i)
      ≤ (N : ENNReal) * ENNReal.ofReal (δ + ε) := by
    calc epistemicMeasure p (⋃ i, edgeBand c (δ + ε) i)
        ≤ ∑ i, epistemicMeasure p (edgeBand c (δ + ε) i) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _i : Fin N, ENNReal.ofReal (δ + ε) :=
          Finset.sum_le_sum fun i _ => measure_edgeBand_le c (δ + ε) i p
      _ = (N : ENNReal) * ENNReal.ofReal (δ + ε) := by simp [Finset.sum_const, nsmul_eq_mul]
  have hsum : (N : ENNReal) * ENNReal.ofReal ε + (N : ENNReal) * ENNReal.ofReal (δ + ε)
      = (N : ENNReal) * ENNReal.ofReal (δ + 2 * ε) := by
    rw [← mul_add, ← ENNReal.ofReal_add hε (by linarith)]
    congr 2
    ring
  calc epistemicMeasure p (unstableSet₂ c δ ε)
      ≤ epistemicMeasure p ((⋃ i, globalBasin c i)ᶜ ∪ ⋃ i, lowerBand c ε i)
          + epistemicMeasure p (⋃ i, edgeBand c (δ + ε) i) := measure_union_le _ _
    _ ≤ (epistemicMeasure p (⋃ i, globalBasin c i)ᶜ + epistemicMeasure p (⋃ i, lowerBand c ε i))
          + epistemicMeasure p (⋃ i, edgeBand c (δ + ε) i) :=
        add_le_add (measure_union_le _ _) (le_refl _)
    _ = epistemicMeasure p (⋃ i, lowerBand c ε i)
          + epistemicMeasure p (⋃ i, edgeBand c (δ + ε) i) := by rw [h0, zero_add]
    _ ≤ (N : ENNReal) * ENNReal.ofReal ε + (N : ENNReal) * ENNReal.ofReal (δ + ε) :=
        add_le_add hlow hhigh
    _ = (N : ENNReal) * ENNReal.ofReal (δ + 2 * ε) := hsum

/-! ### Quantitative stability under a move of `Σ` -/

/-- ★★★ **Quantitative stability of record macrostates under a move of `Σ`.** The microstates whose
record string a move changes have epistemic measure at most `k · N · (δ + 2ε)`, where `δ` bounds the
record write and `ε` bounds the travel of the arcs. At `ε = 0` this is #103's bound; the extra `2ε` is
the price of letting the base move, and it is two-sided because both endpoints travel. -/
theorem measure_recordString_ne_sigmaMove_le {k : ℕ} (c : Fin k → ContextField N)
    {f : LF4.CPN N → LF4.CPN N} {g : LF4.CPN N → ℝ} {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hg : ∀ q, g q ∈ Icc (0 : ℝ) δ) (harc : ∀ j q, ArcShift (c j) ε q (f q)) (p : LF4.CPN N) :
    epistemicMeasure p {x | recordString c (sigmaMove f g x) ≠ recordString c x}
      ≤ (k : ENNReal) * ((N : ENNReal) * ENNReal.ofReal (δ + 2 * ε)) := by
  have hsub : {x : LF4.KSigma N | recordString c (sigmaMove f g x) ≠ recordString c x}
      ⊆ ⋃ j, unstableSet₂ (c j) δ ε := by
    intro x hx
    by_contra hmem
    simp only [Set.mem_iUnion, not_exists] at hmem
    exact hx (recordString_sigmaMove c hδ hε (hg x.1).1 (hg x.1).2 (fun j => harc j x.1)
      fun j => exists_robustBasin₂_of_notMem_unstableSet₂ (c j) δ ε (hmem j))
  calc epistemicMeasure p {x | recordString c (sigmaMove f g x) ≠ recordString c x}
      ≤ epistemicMeasure p (⋃ j, unstableSet₂ (c j) δ ε) := measure_mono hsub
    _ ≤ ∑ j, epistemicMeasure p (unstableSet₂ (c j) δ ε) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin k, ((N : ENNReal) * ENNReal.ofReal (δ + 2 * ε)) :=
        Finset.sum_le_sum fun j _ => measure_unstableSet₂_le (c j) hδ hε p
    _ = (k : ENNReal) * ((N : ENNReal) * ENNReal.ofReal (δ + 2 * ε)) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- ★★ **The same bound in terms of a modulus of continuity on the rate field.** Rates within `η`
coordinatewise put the arcs within `(N+1)·η`, so the relabelled set has measure at most
`k · N · (δ + 2(N+1)η)`. ⚠️ Note the **second** factor of `N`: for a large alphabet the rate field has
to be uniformly close, not merely close. -/
theorem measure_recordString_ne_sigmaMove_rate_le {k : ℕ} (c : Fin k → ContextField N)
    {f : LF4.CPN N → LF4.CPN N} {g : LF4.CPN N → ℝ} {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hg : ∀ q, g q ∈ Icc (0 : ℝ) δ)
    (hrate : ∀ j q i, |(c j).rate (f q) i - (c j).rate q i| ≤ η) (p : LF4.CPN N) :
    epistemicMeasure p {x | recordString c (sigmaMove f g x) ≠ recordString c x}
      ≤ (k : ENNReal) * ((N : ENNReal) * ENNReal.ofReal (δ + 2 * (((N : ℝ) + 1) * η))) :=
  measure_recordString_ne_sigmaMove_le c hδ
    (by positivity) hg (fun j q => arcShift_of_rate_close (c j) hη (hrate j q)) p

/-- ★★★ **One exceptional set serves a whole flow.** For a one-parameter family of moves whose write
stays in `[0, δ]` and whose arcs stay within `ε` over the horizon `[0, T]`, the record string survives
the **entire** horizon outside a set of measure `k · N · (δ + 2ε)` — the same set, because the robust
interior does not depend on the parameter. This is #103's drift corollary once the base is allowed to
move, and it needs no new argument. ⚠️ `F s` is an arbitrary measurable motion of the base: no group
law, no invertibility and no generator is assumed, so "flow" names the shape, not a structure. -/
theorem measure_exists_recordString_ne_flow_le {k : ℕ} (c : Fin k → ContextField N)
    (F : ℝ → LF4.CPN N → LF4.CPN N) (G : ℝ → LF4.CPN N → ℝ) {T δ ε : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hG : ∀ s ∈ Icc (0 : ℝ) T, ∀ q, G s q ∈ Icc (0 : ℝ) δ)
    (harc : ∀ s ∈ Icc (0 : ℝ) T, ∀ j q, ArcShift (c j) ε q (F s q)) (p : LF4.CPN N) :
    epistemicMeasure p {x | ∃ s ∈ Icc (0 : ℝ) T,
        recordString c (sigmaMove (F s) (G s) x) ≠ recordString c x}
      ≤ (k : ENNReal) * ((N : ENNReal) * ENNReal.ofReal (δ + 2 * ε)) := by
  have hsub : {x : LF4.KSigma N | ∃ s ∈ Icc (0 : ℝ) T,
        recordString c (sigmaMove (F s) (G s) x) ≠ recordString c x}
      ⊆ ⋃ j, unstableSet₂ (c j) δ ε := by
    intro x hx
    obtain ⟨s, hs, hne⟩ := hx
    by_contra hmem
    simp only [Set.mem_iUnion, not_exists] at hmem
    exact hne (recordString_sigmaMove c hδ hε (hG s hs x.1).1 (hG s hs x.1).2
      (fun j => harc s hs j x.1)
      fun j => exists_robustBasin₂_of_notMem_unstableSet₂ (c j) δ ε (hmem j))
  calc epistemicMeasure p {x | ∃ s ∈ Icc (0 : ℝ) T,
        recordString c (sigmaMove (F s) (G s) x) ≠ recordString c x}
      ≤ epistemicMeasure p (⋃ j, unstableSet₂ (c j) δ ε) := measure_mono hsub
    _ ≤ ∑ j, epistemicMeasure p (unstableSet₂ (c j) δ ε) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin k, ((N : ENNReal) * ENNReal.ofReal (δ + 2 * ε)) :=
        Finset.sum_le_sum fun j _ => measure_unstableSet₂_le (c j) hδ hε p
    _ = (k : ENNReal) * ((N : ENNReal) * ENNReal.ofReal (δ + 2 * ε)) := by
        simp [Finset.sum_const, nsmul_eq_mul]

end CSD.RecordLayer

end
