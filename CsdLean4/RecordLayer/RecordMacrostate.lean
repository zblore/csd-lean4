/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.MacroProjection

/-!
# `ST-3`'s instance: the record string as a macroscopic coordinate

**Category:** 7-SigmaLayer (the record layer — Paper C A7).
BACKLOG #102, candidate (5) of #38 at the author's decision (2026-10-02).

[`MacroProjection.lean`](MacroProjection.lean) (#99) built the frame: `π'` as a measurable map to a
finite structure, the factoring criterion, and the two theorems any instance owes. The constraint
recorded in #38 is what picks the instance: ★ `factorsThrough_iff` says `π'` may coarse-grain
everything **except** the record outcomes of the family whose statistics it carries, because a basin
`globalBasin c i = {x | x.2.1 ∈ circleCell (c.rate x.1) i}` depends on the base through the rate field
and on the fibre angle. The coordinate that satisfies that by construction is the **record string**:

* `outcomeCode c` — the outcome a context assigns to a microstate, `i.succ` on the basin of `i` and
  `0` on the null set where no basin contains it (`globalBasin_ae_total`), kept as a value so the
  coordinate is total; its fibres are the basins (`preimage_outcomeCode_succ`) and their complement,
  so it is measurable;
* `recordString`, ★★ `recordMacro` — the outcome each context of a **finite, indexed** family assigns,
  as a `MacroProjection` onto `Fin k → Fin (N+1)`. The family is indexed, so the string remembers
  *which* context gave *which* outcome: this is the order-retaining coarse reading candidate (5) asks
  for, and the reason a histogram was rejected;
* ★★ `globalBasin_eq_preimage` — every record event of the family factors through the string, with
  the coordinate set written out, which is what makes #99's theorems available here;
* ★ `recordString_coarsen` — dropping contexts coarsens the coordinate, so the macrostates form a
  lattice under refinement with one cell per string;
* ★★★ `noSignalling_pairFamily` — **no-signalling holds for the record family, exactly**: summing the
  second context's outcomes returns the first context's basin whatever the second context is, because
  any context's basins a.e. exhaust `Σ`. #99's first requirement is **verified** here, not merely
  transported;
* ★★★ `nstep_born_recordMacro` — **the Born chain law holds verbatim in the macroscopic law**: #99's
  `nstep_born_map` applied to the string, so the product of macroscopic weights along a chain of
  contexts from the family is the same chain rate. #99's second requirement, verified;
* ★★ `measure_map_recordMacro_singleton` — a one-context macrostate carries the **Born weight**: the
  macroscopic law is Born on its own terms.

## Honest scope

⚠️ **This is the construction, not the physics.** What makes a coordinate *macroscopic* is that its
cells are **stable** — that the same cell persists under the flow and that overwhelmingly many
microstates share it. **Neither is proved here**, and candidate (5)'s content is exactly that: BACKLOG
#103 carries it, with the warning that stability cannot mean invariance, since finite unitary dynamics
is almost periodic and supplies no mixing (`not_hasCorrelationDecay_blockPop_of_unitary`).

⚠️ **No product law for multi-context cells, and that is contextuality showing.** Every context in
the family reads the **same** fibre angle through its **own** base-dependent arcs, so a joint cell is
an intersection of arcs and its measure is not a product of rates. Only the one-context cell is
claimed to carry the Born weight; nothing here says two contexts' outcomes are independent, and
nothing here is a non-contextual value assignment — the outcome a context assigns depends on that
context's rate field at the base, which is where CSD's contextuality lives.

⚠️ **The family is fixed and finite, and no canonical family is claimed.** Which coarse readings are
the physical ones is not settled by anything here; the lattice of `recordString_coarsen` is the space
of choices, not a selection among them.

⚠️ **`M` is a set of labels.** No geometry, order or topology on the macrostates is constructed. The
causal order candidate (2) would add — the event order of `CV/RecordCausalOrder.lean` — is extra
structure on `M` and is not built here; neither is the cone containment of #98.

References: [`records-to-spacetime-scoping.md`](../../specs/records-to-spacetime-scoping.md) `ST-3`;
`MacroProjection.lean` (#99), `GlobalBasin.lean`, `NStepChain.lean`; `specs/BACKLOG.md` #102, #38,
#103.
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

variable {N : ℕ}

/-! ### The outcome a context assigns to a microstate -/

open Classical in
/-- **The outcome code of a context at a microstate**: `i.succ` when the microstate lies in the basin
of outcome `i`, and `0` when it lies in none — a null set by `globalBasin_ae_total`, kept as a value
so the coordinate is total. -/
noncomputable def outcomeCode (c : ContextField N) (x : LF4.KSigma N) : Fin (N + 1) :=
  if h : ∃ i, x ∈ globalBasin c i then (h.choose).succ else 0

theorem outcomeCode_eq_succ_iff (c : ContextField N) (x : LF4.KSigma N) (i : Fin N) :
    outcomeCode c x = i.succ ↔ x ∈ globalBasin c i := by
  classical
  constructor
  · intro h
    rw [outcomeCode] at h
    by_cases hex : ∃ j, x ∈ globalBasin c j
    · rw [dif_pos hex] at h
      have : hex.choose = i := Fin.succ_injective N h
      rw [← this]
      exact hex.choose_spec
    · rw [dif_neg hex] at h
      exact absurd h.symm (Fin.succ_ne_zero i)
  · intro hx
    have hex : ∃ j, x ∈ globalBasin c j := ⟨i, hx⟩
    rw [outcomeCode, dif_pos hex]
    have huniq : hex.choose = i := by
      by_contra hne
      exact Set.disjoint_left.mp (globalBasin_pairwiseDisjoint c hne) hex.choose_spec hx
    rw [huniq]

theorem preimage_outcomeCode_succ (c : ContextField N) (i : Fin N) :
    outcomeCode c ⁻¹' {i.succ} = globalBasin c i := by
  ext x
  simpa using outcomeCode_eq_succ_iff c x i

theorem preimage_outcomeCode_zero (c : ContextField N) :
    outcomeCode c ⁻¹' {0} = (⋃ i, globalBasin c i)ᶜ := by
  classical
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion]
  constructor
  · intro h hmem
    obtain ⟨i, hi⟩ := hmem
    rw [(outcomeCode_eq_succ_iff c x i).2 hi] at h
    exact Fin.succ_ne_zero i h
  · intro h
    rw [outcomeCode, dif_neg]
    exact fun hex => h ⟨hex.choose, hex.choose_spec⟩

theorem measurable_outcomeCode (c : ContextField N) : Measurable (outcomeCode c) := by
  classical
  refine measurable_to_countable' fun v => ?_
  refine Fin.cases ?_ ?_ v
  · rw [preimage_outcomeCode_zero]
    exact (MeasurableSet.iUnion (measurableSet_globalBasin c)).compl
  · intro i
    rw [preimage_outcomeCode_succ]
    exact measurableSet_globalBasin c i

/-! ### The record string, as a macroscopic coordinate -/

/-- **The record string of a finite family of contexts**: the outcome each context in the family
assigns to the microstate. The family is *indexed*, so the string remembers which context gave which
outcome — this is the order-retaining coarse reading that candidate (5) of #38 asks for, and not a
histogram. -/
noncomputable def recordString {k : ℕ} (c : Fin k → ContextField N) (x : LF4.KSigma N) :
    Fin k → Fin (N + 1) := fun j => outcomeCode (c j) x

/-- ★★ **The record string is a macroscopic-coordinate projection** in the sense of #99: a measurable
map from `Σ` to a finite structure. -/
noncomputable def recordMacro {k : ℕ} (c : Fin k → ContextField N) :
    MacroProjection (LF4.KSigma N) (Fin k → Fin (N + 1)) where
  toFun := recordString c
  measurable_toFun := measurable_pi_iff.2 fun j => measurable_outcomeCode (c j)

theorem recordMacro_toFun {k : ℕ} (c : Fin k → ContextField N) :
    (recordMacro c).toFun = recordString c := rfl

theorem measurable_recordString {k : ℕ} (c : Fin k → ContextField N) :
    Measurable (recordString c) := (recordMacro c).measurable_toFun

/-- ★★ **Every record event of the family factors through the string**, with the coordinate set
written out: this is what makes #99's two theorems available for this instance. -/
theorem globalBasin_eq_preimage {k : ℕ} (c : Fin k → ContextField N) (j : Fin k) (i : Fin N) :
    globalBasin (c j) i = (recordMacro c).toFun ⁻¹' {v : Fin k → Fin (N + 1) | v j = i.succ} := by
  ext x
  simpa [recordMacro, recordString] using (outcomeCode_eq_succ_iff (c j) x i).symm

theorem factorsThrough_globalBasin {k : ℕ} (c : Fin k → ContextField N) (j : Fin k) (i : Fin N) :
    FactorsThrough (recordString c) (globalBasin (c j) i) :=
  ⟨{v : Fin k → Fin (N + 1) | v j = i.succ}, globalBasin_eq_preimage c j i⟩

/-- ★ **Coarsening**: dropping contexts from the family coarsens the coordinate — the sub-family's
string is a function of the full family's. The macrostates of #38's candidate (5) therefore form a
lattice under refinement, with one cell per record string. -/
theorem recordString_coarsen {k l : ℕ} (c : Fin k → ContextField N) (σ : Fin l → Fin k)
    {x y : LF4.KSigma N} (h : recordString c x = recordString c y) :
    recordString (c ∘ σ) x = recordString (c ∘ σ) y := by
  funext j
  exact congrFun h (σ j)

/-! ### The two theorems #99 asks of an instance, verified here -/

/-- The two-party record family of two contexts: both outcomes read off one microstate. -/
noncomputable def pairFamily (c₁ c₂ : ContextField N) (o₁ o₂ : Fin N) : Set (LF4.KSigma N) :=
  globalBasin c₁ o₁ ∩ globalBasin c₂ o₂

/-- ★★★ **No-signalling holds for the record family, exactly.** Summing the second context's outcomes
returns the first context's basin whatever the second context is, because the basins of any context
a.e. exhaust `Σ` (`globalBasin_ae_total`). This is #99's first requirement, *verified* for candidate
(5) rather than merely transported. -/
theorem noSignalling_pairFamily (p : LF4.CPN N) (c₁ : ContextField N) (o₁ : Fin N) :
    ∀ c₂ c₂' : ContextField N,
      epistemicMeasure p (⋃ o₂ : Fin N, pairFamily c₁ c₂ o₁ o₂)
        = epistemicMeasure p (⋃ o₂ : Fin N, pairFamily c₁ c₂' o₁ o₂) := by
  have key : ∀ c₂ : ContextField N,
      epistemicMeasure p (⋃ o₂ : Fin N, pairFamily c₁ c₂ o₁ o₂)
        = epistemicMeasure p (globalBasin c₁ o₁) := by
    intro c₂
    have hunion : (⋃ o₂ : Fin N, pairFamily c₁ c₂ o₁ o₂)
        = globalBasin c₁ o₁ ∩ (⋃ o₂ : Fin N, globalBasin c₂ o₂) := by
      ext x
      simp only [pairFamily, Set.mem_iUnion, Set.mem_inter_iff]
      tauto
    have hnull : epistemicMeasure p (⋃ o₂ : Fin N, globalBasin c₂ o₂)ᶜ = 0 := by
      have h := globalBasin_ae_total c₂ p
      rwa [Set.compl_eq_univ_sdiff]
    have hsub : globalBasin c₁ o₁
        ⊆ (globalBasin c₁ o₁ ∩ (⋃ o₂ : Fin N, globalBasin c₂ o₂))
          ∪ (⋃ o₂ : Fin N, globalBasin c₂ o₂)ᶜ := by
      intro x hx
      by_cases hmem : x ∈ ⋃ o₂ : Fin N, globalBasin c₂ o₂
      · exact Or.inl ⟨hx, hmem⟩
      · exact Or.inr hmem
    rw [hunion]
    refine le_antisymm (measure_mono Set.inter_subset_left) ?_
    calc epistemicMeasure p (globalBasin c₁ o₁)
        ≤ epistemicMeasure p ((globalBasin c₁ o₁ ∩ (⋃ o₂ : Fin N, globalBasin c₂ o₂))
            ∪ (⋃ o₂ : Fin N, globalBasin c₂ o₂)ᶜ) := measure_mono hsub
      _ ≤ epistemicMeasure p (globalBasin c₁ o₁ ∩ (⋃ o₂ : Fin N, globalBasin c₂ o₂))
            + epistemicMeasure p (⋃ o₂ : Fin N, globalBasin c₂ o₂)ᶜ := measure_union_le _ _
      _ = epistemicMeasure p (globalBasin c₁ o₁ ∩ (⋃ o₂ : Fin N, globalBasin c₂ o₂)) := by
            rw [hnull, add_zero]
  intro c₂ c₂'
  rw [key c₂, key c₂']

/-- ★★★ **The Born chain law holds verbatim in the macroscopic law of the record string.** Each step's
basin factors through the coordinate, so #99's `nstep_born_map` applies: the product of the
macroscopic weights along a chain of contexts drawn from the family is the chain rate, unchanged. This
is #99's second requirement, verified for candidate (5). -/
theorem nstep_born_recordMacro {k : ℕ} (c : Fin k → ContextField N) (jdx : ℕ → Fin k)
    (p : LF4.CPN N) (i : ℕ → Fin N) (n : ℕ) :
    (∏ m ∈ Finset.range n,
        ((epistemicMeasure (chainState p i m)).map (recordMacro c).toFun)
          {v : Fin k → Fin (N + 1) | v (jdx m) = (i m).succ})
      = ENNReal.ofReal (chainRate p (fun m => c (jdx m)) i n) :=
  nstep_born_map (fun _ => recordMacro c) p (fun m => c (jdx m)) i n
    (fun m => {v : Fin k → Fin (N + 1) | v (jdx m) = (i m).succ})
    (fun m => globalBasin_eq_preimage c (jdx m) (i m))

/-- ★★ **A one-context macrostate carries the Born weight**: the macroscopic law of the record string
assigns the cell `{outcome i}` exactly the rate the context gives the preparation. The macroscopic
law is Born on its own terms. -/
theorem measure_map_recordMacro_singleton (c : ContextField N) (i : Fin N) (p : LF4.CPN N) :
    ((epistemicMeasure p).map (recordMacro (fun _ : Fin 1 => c)).toFun)
        {v : Fin 1 → Fin (N + 1) | v 0 = i.succ}
      = ENNReal.ofReal (c.rate p i) := by
  rw [← measure_eq_map_of_factorsThrough (recordMacro (fun _ : Fin 1 => c)) (epistemicMeasure p)
    (globalBasin_eq_preimage (fun _ : Fin 1 => c) 0 i)]
  exact globalBasin_prob c i p

end CSD.RecordLayer

end
