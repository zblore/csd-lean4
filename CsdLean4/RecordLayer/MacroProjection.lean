/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.NStepChain

/-!
# `ST-3`: the macroscopic-coordinate projection as a structure

**Category:** 7-SigmaLayer (the record layer — Paper C A7).
BACKLOG #99, the structure half of `ST-3`.

Paper D says spacetime arises "after further coarse-graining" through "additional projections", and
neither paper nor charter says **which** projection. That is a decision, not a lemma, and
`specs/records-to-spacetime-scoping.md` §8 records it as one; `specs/BACKLOG.md` #38 lists the five
candidates. This module builds the **frame** every candidate has to fit, and nothing else:

* `MacroProjection X M` — a measurable map from the ontic space to a finite structure. That is all
  `π'` is, as a structure;
* `FactorsThrough π B` — the record event `B` is a union of fibres, with ★ `factorsThrough_iff`:
  **it cannot distinguish two microstates with the same macroscopic coordinate.** This is the form in
  which a candidate is checked, and it is closed under complement, union and indexed union;
* ★★ `measure_eq_map_of_factorsThrough` — **the engine**: an event that factors has the same
  probability in the macroscopic law (the pushforward `μ.map π'`) as in the microscopic one. Every
  identity between probabilities of factoring events therefore transports verbatim, which is what
  "the record statistics factor through `π'`" has to mean;
* `patternMap`, `patternProjection` — the **membership pattern** of a finite record family, a
  `MacroProjection` onto `Fin k → Bool` (★ `factorsThrough_patternMap`), with the universal property
  ★★ `patternMap_eq_of_factorsThrough`: **it is the coarsest coordinate the family factors through**,
  so any other such coordinate refines it. "The statistics factor through `π'`" always has a
  canonical minimal solution;
* ★★★ `noSignalling_map_iff` — **no-signalling survives the projection**, in both directions: for a
  two-party family of factoring events, the macroscopic law satisfies no-signalling exactly when the
  microscopic law does;
* ★★★ `nstep_born_map` — **the chain law survives the projection**: `csd_nstep_born`'s product of
  record weights along a chain of contexts is the chain rate, and when each step's basin factors, the
  same product computed with pushforward measures of coordinate sets is the same number.

Those last two are the two theorems the scoping note asks of any instance.

## Honest scope

⚠️ **This is a frame, not a projection.** Nothing here names `π'`, constructs a macrostate, or shows
that a projection with any further property exists. The instance is BACKLOG #102 and waits on the
author's choice among #38's five candidates; `patternProjection` is **not** that choice — it is the
tautological coarsest solution for a family of events already in hand, which is why it carries no
physics.

⚠️ **The two transport theorems are conservative on purpose.** They say nothing is lost and nothing
is gained: a factoring projection neither destroys no-signalling nor creates it, and the same for the
chain law. That is the content the note asked for — a constraint every candidate satisfies — and it
must not be read as evidence for any candidate.

⚠️ **`NoSignalling` here is a statement about measures of record events**, the form that transports.
The corpus's dynamical no-signalling (`CV/CompositeArena.lean`'s `composite_no_signalling`) is an
observable-level statement about kicks; the bridge between the two is the record-weight construction
of `RecordLayer/`, not this file.

⚠️ `M` is finite with measurable singletons, which is what "a finite structure" means here and what
makes every coordinate set measurable. No topology, order or geometry on `M` is assumed — a
macroscopic *geometry* would be further structure on `M` that nothing here provides.

References: [`records-to-spacetime-scoping.md`](../../specs/records-to-spacetime-scoping.md) `ST-3`
and §8; `RecordLayer/NStepChain.lean` (`csd_nstep_born`), `RecordLayer/GlobalBasin.lean`
(`globalBasin`, `epistemicMeasure`); `specs/BACKLOG.md` #99, #38, #102.
-/

@[expose] public section

open MeasureTheory

namespace CSD.RecordLayer

/-! ### Factoring through a coordinate -/

section Factoring

variable {X : Type*} {M : Type*}

/-- **A record event factors through the coordinates**: it is a union of fibres, i.e. membership is
decided by the macroscopic coordinate alone. -/
def FactorsThrough (π : X → M) (B : Set X) : Prop := ∃ S : Set M, B = π ⁻¹' S

/-- ★ **The pointwise characterisation**: an event factors through the coordinates exactly when it
cannot distinguish two microstates with the same coordinate. This is the form in which the candidates
of #38 are checked. -/
theorem factorsThrough_iff {π : X → M} {B : Set X} :
    FactorsThrough π B ↔ ∀ x y : X, π x = π y → (x ∈ B ↔ y ∈ B) := by
  constructor
  · rintro ⟨S, rfl⟩ x y hxy
    simp only [Set.mem_preimage, hxy]
  · intro h
    refine ⟨π '' B, Set.eq_of_subset_of_subset (fun x hx => ⟨x, hx, rfl⟩) ?_⟩
    rintro x ⟨y, hy, hxy⟩
    exact (h y x hxy).1 hy

theorem factorsThrough_compl {π : X → M} {B : Set X} (h : FactorsThrough π B) :
    FactorsThrough π Bᶜ := by
  obtain ⟨S, rfl⟩ := h
  exact ⟨Sᶜ, rfl⟩

theorem factorsThrough_union {π : X → M} {B C : Set X} (hB : FactorsThrough π B)
    (hC : FactorsThrough π C) : FactorsThrough π (B ∪ C) := by
  obtain ⟨S, rfl⟩ := hB
  obtain ⟨T, rfl⟩ := hC
  exact ⟨S ∪ T, rfl⟩

theorem factorsThrough_iUnion {ι : Type*} {π : X → M} {B : ι → Set X}
    (h : ∀ i, FactorsThrough π (B i)) : FactorsThrough π (⋃ i, B i) := by
  choose S hS using h
  refine ⟨⋃ i, S i, ?_⟩
  simp only [Set.preimage_iUnion, hS]

open Classical in
/-- The **membership pattern** of a finite family of record events: the coarsest macroscopic
coordinate from which the family can be read off. -/
noncomputable def patternMap {k : ℕ} (B : Fin k → Set X) (x : X) : Fin k → Bool :=
  fun i => if x ∈ B i then true else false

/-- ★ Every event of a finite family factors through the family's own pattern. -/
theorem factorsThrough_patternMap {k : ℕ} (B : Fin k → Set X) (i : Fin k) :
    FactorsThrough (patternMap B) (B i) := by
  classical
  refine factorsThrough_iff.2 fun x y hxy => ?_
  have h := congrFun hxy i
  simp only [patternMap] at h
  by_cases hx : x ∈ B i
  · by_cases hy : y ∈ B i
    · exact iff_of_true hx hy
    · simp [hx, hy] at h
  · by_cases hy : y ∈ B i
    · simp [hx, hy] at h
    · exact iff_of_false hx hy

/-- ★★ **The universal property**: the pattern map is the *coarsest* macroscopic coordinate through
which a finite record family factors — any other such coordinate refines it, in the sense that two
microstates it identifies have the same pattern. So "the statistics factor through `π'`" always has a
canonical minimal solution, and a candidate of #38 is a coarsening of this one. -/
theorem patternMap_eq_of_factorsThrough {k : ℕ} {B : Fin k → Set X} {π : X → M}
    (h : ∀ i, FactorsThrough π (B i)) {x y : X} (hxy : π x = π y) :
    patternMap B x = patternMap B y := by
  classical
  funext i
  have hiff := (factorsThrough_iff.1 (h i)) x y hxy
  simp only [patternMap]
  by_cases hx : x ∈ B i
  · rw [if_pos hx, if_pos (hiff.1 hx)]
  · rw [if_neg hx, if_neg (fun hy => hx (hiff.2 hy))]

end Factoring

/-! ### The structure -/

section Macro

variable {X : Type*} [MeasurableSpace X] {M : Type*} [MeasurableSpace M]

/-- **A macroscopic-coordinate projection**: a measurable map from the ontic space to a finite
structure. Paper D's `π'`, as a structure and nothing more — which candidate map it is, is the
decision `specs/BACKLOG.md` #38 records and this file does not make. -/
structure MacroProjection (X : Type*) [MeasurableSpace X] (M : Type*) [MeasurableSpace M] where
  /-- The coordinate map. -/
  toFun : X → M
  /-- It is measurable, so it pushes measures forward. -/
  measurable_toFun : Measurable toFun

instance : CoeFun (MacroProjection X M) (fun _ => X → M) := ⟨MacroProjection.toFun⟩

variable [Fintype M] [MeasurableSingletonClass M]

theorem measurableSet_of_fintype (S : Set M) : MeasurableSet S := (Set.toFinite S).measurableSet

/-- ★★ **The engine of `ST-3`**: an event that factors through the coordinates has the same
probability in the macroscopic law — the pushforward — as in the microscopic one. Every identity
between probabilities of factoring events therefore transports verbatim, which is what "the record
statistics factor through `π'`" has to mean. -/
theorem measure_eq_map_of_factorsThrough (π : MacroProjection X M) (μ : Measure X) {B : Set X}
    {S : Set M} (hB : B = π.toFun ⁻¹' S) : μ B = (μ.map π.toFun) S := by
  rw [Measure.map_apply π.measurable_toFun (measurableSet_of_fintype S), hB]

/-- The pattern map of a measurable family is a `MacroProjection` onto a finite structure. -/
noncomputable def patternProjection {k : ℕ} (B : Fin k → Set X)
    (hB : ∀ i, MeasurableSet (B i)) : MacroProjection X (Fin k → Bool) where
  toFun := patternMap B
  measurable_toFun := by
    classical
    refine measurable_pi_iff.2 fun i => ?_
    exact Measurable.ite (hB i) measurable_const measurable_const

/-! ### The two theorems any instance must satisfy -/

/-- **No-signalling for a record-event family**: the first party's record weights do not depend on
the second party's context. Stated as an identity between probabilities, which is the form that
transports. -/
def NoSignalling {C₁ O₁ C₂ O₂ : Type*} (μ : Measure X) (B : C₁ → O₁ → C₂ → O₂ → Set X) : Prop :=
  ∀ (c₁ : C₁) (o₁ : O₁) (c₂ c₂' : C₂), μ (⋃ o₂ : O₂, B c₁ o₁ c₂ o₂) = μ (⋃ o₂ : O₂, B c₁ o₁ c₂' o₂)

/-- ★★★ **No-signalling survives the projection**, in both directions: if every record event of a
two-party family factors through the macroscopic coordinates, the macroscopic law — the pushforward —
satisfies no-signalling exactly when the microscopic law does. Nothing is lost and nothing is gained,
which is the first of the two theorems `ST-3` asks of any candidate `π'`. -/
theorem noSignalling_map_iff {C₁ O₁ C₂ O₂ : Type*} (π : MacroProjection X M) (μ : Measure X)
    {B : C₁ → O₁ → C₂ → O₂ → Set X} {S : C₁ → O₁ → C₂ → O₂ → Set M}
    (hB : ∀ c₁ o₁ c₂ o₂, B c₁ o₁ c₂ o₂ = π.toFun ⁻¹' S c₁ o₁ c₂ o₂) :
    NoSignalling μ B ↔
      ∀ (c₁ : C₁) (o₁ : O₁) (c₂ c₂' : C₂), (μ.map π.toFun) (⋃ o₂ : O₂, S c₁ o₁ c₂ o₂)
        = (μ.map π.toFun) (⋃ o₂ : O₂, S c₁ o₁ c₂' o₂) := by
  have key : ∀ (c₁ : C₁) (o₁ : O₁) (c₂ : C₂),
      μ (⋃ o₂ : O₂, B c₁ o₁ c₂ o₂) = (μ.map π.toFun) (⋃ o₂ : O₂, S c₁ o₁ c₂ o₂) := by
    intro c₁ o₁ c₂
    refine measure_eq_map_of_factorsThrough π μ ?_
    rw [Set.preimage_iUnion]
    exact Set.iUnion_congr fun o₂ => hB c₁ o₁ c₂ o₂
  constructor
  · intro h c₁ o₁ c₂ c₂'
    rw [← key c₁ o₁ c₂, ← key c₁ o₁ c₂']
    exact h c₁ o₁ c₂ c₂'
  · intro h c₁ o₁ c₂ c₂'
    rw [key c₁ o₁ c₂, key c₁ o₁ c₂']
    exact h c₁ o₁ c₂ c₂'

/-- ★★★ **The chain law survives the projection.** `csd_nstep_born` says the product of the record
weights along a chain of contexts is the chain rate. If each step's basin factors through the
macroscopic coordinates, the same product computed in the **macroscopic** law — each factor a
pushforward measure of a set of coordinates — is the same number. The CSD chain law is therefore a
statement about macrostates whenever the basins are macroscopic, which is the second of the two
theorems `ST-3` asks of any candidate `π'`. -/
theorem nstep_born_map {N : ℕ} (π : ℕ → MacroProjection (LF4.KSigma N) M) (p : LF4.CPN N)
    (c : ℕ → ContextField N) (i : ℕ → Fin N) (n : ℕ) (S : ℕ → Set M)
    (hfac : ∀ k, globalBasin (c k) (i k) = (π k).toFun ⁻¹' S k) :
    (∏ k ∈ Finset.range n,
        ((epistemicMeasure (chainState p i k)).map (π k).toFun) (S k))
      = ENNReal.ofReal (chainRate p c i n) := by
  rw [← csd_nstep_born p c i n]
  refine Finset.prod_congr rfl fun k _ => ?_
  exact (measure_eq_map_of_factorsThrough (π k) (epistemicMeasure (chainState p i k)) (hfac k)).symm

end Macro

end CSD.RecordLayer

end
