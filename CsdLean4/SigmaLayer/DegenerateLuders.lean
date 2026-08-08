/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.SwapLuders

/-!
# SigmaLayer/DegenerateLuders: the degenerate case — the problem made precise, the boundary proved

**Category:** 7-SigmaLayer (the record layer — the open frontier, stated).

## What changes at higher rank

At rank one, the Lüders channel is measure-and-reprepare: the post-state is the *fixed* basis vertex
`[eᵢ]`, whatever the preparation, and `swap_luders_born` delivers exactly that. At higher rank it is
not: the Lüders post-state is the **normalised projection** `[Πᵢψ]`, which *depends on the
preparation* — a superposition inside the block survives, with its internal coherence intact. That
`ψ`-dependence is the entire difficulty, and this module does three things about it:

1. **states the obligation precisely** (`BlockLudersObligation`, the §8.3 `_statement` pattern);
2. **proves the boundary**: the calibrated-swap witness — *any* fixed calibration — cannot satisfy
   it for a block of dimension ≥ 2 (`swap_not_blockLuders`). The fixed-calibration architecture is
   refuted for degenerate measurements, as a theorem rather than a scope note;
3. **proves the positive half that does survive**: the degenerate **selector Born weights** are
   right — the block-selector's outcome sectors carry exactly the `blockField` rates
   (`degenerate_selector_born`). Statistics generalise; the *update* is what does not.

## ✅ How it was closed (the route, and how the anticipated wall dissolved)

A degenerate witness must relocate the base point `[ψ] ↦ [Πᵢψ]` — a `ψ`-dependent target — while
preserving measure globally. `no_exact_collapse` still governs: pointwise across preparations the
map loses base dimensions, so the lost data must be *stored*, not destroyed. The natural
construction is the **projective join**: `ℂℙ^{N-1}` decomposes (off a null set) as
`join(ℂℙ^{dᵢ-1}, ℂℙ^{N-dᵢ-1})` — block component, complement component, mixing angle, relative
phase — with the update keeping the block component and banking the rest. The wall is the
Fubini–Study measure decomposition under the join, which is unformalised geometry. **Effort L**;
recorded in `specs/BACKLOG.md`.

*Corrected 2026-08-04 (codebase audit).* The sentence "nothing in this module claims progress" stood long after the
construction landed. **`BlockLudersObligation` — defined right here — is inhabited** by
`joinWitness_blockLuders` (`SigmaLayer/JoinLuders.lean`), packaged as
`degenerateMeasurementClosure` (`SigmaLayer/JoinClosure.lean`). The anticipated wall (an
FS *measure decomposition* under the join) was **dissolved rather than crossed**: the pair
arena simply *is* the projective join `ℙ(ℂ^{N+N})`, the update is a permutation unitary on
it, and Liouville preservation is FS unitary invariance — no disintegration needed.

## References

`SigmaLayer/SwapLuders.lean` (`swap_luders_marginal` — whose *preparation-independence* is exactly
what this module turns against the fixed-calibration architecture);
`SigmaLayer/OutcomeField.lean` (`blockField` — the kinematic form of the degenerate rates this
module's `degenerate_selector_born` makes dynamical); `CONVENTIONS.md` §8.3 (the `_statement`
discipline); `specs/BACKLOG.md` (the ★★ row's open item (i)).
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {N K : ℕ}

/-! ### The block projector -/

/-- **The block projector** `Πᵢ` of a degeneracy map `b`: keep the coordinates whose basis
directions belong to outcome `i`, kill the rest. -/
def blockProj (b : Fin N → Fin K) (i : Fin K) :
    EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) where
  toFun ψ := WithLp.toLp 2 (fun j => if b j = i then ψ j else 0)
  map_add' ψ φ := by
    apply PiLp.ext
    intro j
    show (if b j = i then (ψ + φ) j else 0)
      = (if b j = i then ψ j else 0) + (if b j = i then φ j else 0)
    by_cases h : b j = i <;> simp [h, PiLp.add_apply]
  map_smul' c ψ := by
    apply PiLp.ext
    intro j
    show (if b j = i then (c • ψ) j else 0) = c • (if b j = i then ψ j else 0)
    by_cases h : b j = i <;> simp [h, PiLp.smul_apply]

theorem blockProj_apply (b : Fin N → Fin K) (i : Fin K) (ψ : EuclideanSpace ℂ (Fin N))
    (j : Fin N) : blockProj b i ψ j = if b j = i then ψ j else 0 := rfl

/-- A basis vertex inside the block is fixed by its block projector. -/
theorem blockProj_single {b : Fin N → Fin K} {i : Fin K} {j : Fin N} (hb : b j = i) :
    blockProj b i (EuclideanSpace.single j (1 : ℂ)) = EuclideanSpace.single j (1 : ℂ) := by
  apply PiLp.ext
  intro k
  show (if b k = i then (EuclideanSpace.single j (1:ℂ) : EuclideanSpace ℂ (Fin N)) k else 0)
    = (EuclideanSpace.single j (1:ℂ) : EuclideanSpace ℂ (Fin N)) k
  by_cases hk : k = j
  · subst hk
    simp [hb]
  · by_cases hbk : b k = i <;> simp [hbk, hk]

theorem single_ne_zero' (j : Fin N) : (EuclideanSpace.single j (1 : ℂ)) ≠ 0 := by
  intro h
  have := congrFun (congrArg (fun v : EuclideanSpace ℂ (Fin N) => (v : Fin N → ℂ)) h) j
  simp at this

/-! ### Vertex facts -/

variable [NeZero N]

omit [NeZero N] in
/-- **The moment map at a vertex is the vertex's indicator**: `momentMap [eⱼ] k = δⱼₖ`. -/
theorem momentMap_vertex (j k : Fin N) :
    LF4.momentMap (vertexPoint j) k = if k = j then 1 else 0 := by
  unfold vertexPoint
  rw [LF4.momentMap_mk _ (single_ne_zero' j)]
  have hnorm : ‖(EuclideanSpace.single j (1:ℂ) : EuclideanSpace ℂ (Fin N))‖ = 1 := by
    simp
  rw [hnorm]
  by_cases hk : k = j
  · subst hk
    simp
  · simp [hk]

omit [NeZero N] in
/-- Distinct vertices are distinct projective points. -/
theorem vertexPoint_injective : Function.Injective (vertexPoint (N := N)) := by
  intro j1 j2 h
  by_contra hne
  rw [vertexPoint, vertexPoint, Projectivization.mk_eq_mk_iff] at h
  obtain ⟨a, ha⟩ := h
  have h1 := congrArg (fun v : EuclideanSpace ℂ (Fin N) => v j1) ha
  simp only [PiLp.smul_apply, PiLp.single_apply,
    if_neg hne, smul_eq_mul, mul_zero, Units.smul_def] at h1
  exact one_ne_zero h1.symm

omit [NeZero N] in
/-- Distinct base points give distinct epistemic measures — evaluate on the base singleton. -/
theorem epistemicMeasure_injective {p q : LF4.CPN N} (h : p ≠ q) :
    epistemicMeasure p ≠ epistemicMeasure q := by
  intro heq
  have hp : epistemicMeasure p ({p} ×ˢ (univ : Set LF4.KTorus)) = 1 := by
    rw [epistemicMeasure, Measure.prod_prod, measure_univ, mul_one,
      Measure.dirac_apply' _ (measurableSet_singleton p)]
    simp
  have hq : epistemicMeasure q ({p} ×ˢ (univ : Set LF4.KTorus)) = 0 := by
    rw [epistemicMeasure, Measure.prod_prod,
      Measure.dirac_apply' _ (measurableSet_singleton p)]
    simp [Ne.symm h]
  rw [heq, hq] at hp
  exact one_ne_zero hp.symm

/-! ### The block selector, and its dynamical Born weights -/

/-- **The block selector**: the degenerate measurement's outcome index — read the fine-grained
basin, then coarse-grain by the degeneracy map. -/
noncomputable def blockIndex (b : Fin N → Fin K) : LF4.KSigma N → Fin K :=
  fun x => b (basinIndex (momentContext N) x)

theorem measurable_blockIndex (b : Fin N → Fin K) : Measurable (blockIndex b) :=
  (Measurable.of_discrete (f := b)).comp (measurable_basinIndex (momentContext N))

/-- **★ The degenerate SELECTOR Born weights.** (*Renamed in prose 2026-08-04:* this is the
kinematic selector statement — the `epistemicMeasure` of a selector fibre — not the
protocol-level *dynamical* Born, which is `join_sector_born` in `JoinClosure.lean`. The
distinction is the corpus's own, stated in `SwapClosure.lean`.) The block-selector's outcome-`i` sector carries
exactly the coarse-grained Born weight — the sum of the fine-grained weights over the block. With
`momentMap_mk_eq_inner_sq` this is `(blockField b).rate` at the preparation: the kinematic
`blockField` of `OutcomeField.lean`, now realised by a *selector*. Statistics generalise to
degenerate measurements; it is the *update* that does not (see the no-go below). -/
theorem degenerate_selector_born (b : Fin N → Fin K) (ψ : EuclideanSpace ℂ (Fin N))
    (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) (i : Fin K) :
    epistemicMeasure (Projectivization.mk ℂ ψ hψ0) (blockIndex b ⁻¹' {i})
      = ENNReal.ofReal (∑ j ∈ Finset.univ.filter (fun j => b j = i),
          ‖inner ℂ (EuclideanSpace.single j (1 : ℂ)) ψ‖ ^ 2) := by
  classical
  have hdecomp : blockIndex b ⁻¹' {i}
      = ⋃ j ∈ Finset.univ.filter (fun j => b j = i),
          basinIndex (momentContext N) ⁻¹' {j} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Finset.mem_filter,
      Finset.mem_univ, true_and, blockIndex]
    constructor
    · intro h
      exact ⟨basinIndex (momentContext N) x, h, rfl⟩
    · rintro ⟨j, hbj, hj⟩
      rw [hj, hbj]
  rw [hdecomp, measure_biUnion_finset ?_ ?_]
  · rw [Finset.sum_congr rfl fun j hj => shear_selector_born ψ hψ0 hψ j,
      ← ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
  · intro j₁ _ j₂ _ hne
    refine Set.disjoint_left.mpr fun x hx1 hx2 => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx1 hx2
    exact hne (hx1 ▸ hx2)
  · intro j _
    exact measurable_basinIndex (momentContext N) (measurableSet_singleton j)

/-! ### The obligation, and the boundary -/

/-- **What degenerate Lüders demands** — statement only, the `_statement` pattern of
`CONVENTIONS.md` §8.3. A family of post-measurement system marginals implements block-Lüders for
the degeneracy map `b` when, whenever the preparation has a component in block `i`, the
post-outcome-`i` marginal is the epistemic state of the **normalised block projection** `[Πᵢψ]`.

★ The right-hand side depends on `ψ` — that is the entire content, and precisely what a fixed
calibration cannot produce. A fixed *ray-level* calibration cannot produce it
(`swap_not_blockLuders`, below) — but the phase-carrying **join** witness does:
`joinWitness_blockLuders` (`SigmaLayer/JoinLuders.lean`) inhabits this for **every** block
structure, including blocks of dimension ≥ 2. (*Corrected 2026-08-04 (codebase audit).* — this line read "nothing in the
corpus inhabits this", which the corpus itself had already contradicted.) -/
def BlockLudersObligation (b : Fin N → Fin K)
    (postMarg : (ψ : EuclideanSpace ℂ (Fin N)) → ψ ≠ 0 → Fin K → Measure (LF4.KSigma N)) :
    Prop :=
  ∀ (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0) (i : Fin K)
    (h : blockProj b i ψ ≠ 0),
    postMarg ψ hψ0 i = epistemicMeasure (Projectivization.mk ℂ (blockProj b i ψ) h)

/-- The apparatus-ready register state: Haar conditioned on the ready arc. -/
noncomputable def readyMeasure (K : ℕ) : Measure LF4.KTorus :=
  ProbabilityTheory.cond (volume : Measure LF4.KTorus) (readyArc K)

instance : IsProbabilityMeasure (readyMeasure K) :=
  ProbabilityTheory.cond_isProbabilityMeasure volume_readyArc_ne_zero

/-- The swap witness's post-measurement system marginal, for the block selector with calibration
`ν`: prepare `[ψ]` with a ready register and calibrated bank, run the protocol, condition on the
outcome, project to the system. -/
noncomputable def swapPostMarg (b : Fin N → Fin K) (ν : Fin K → Measure (LF4.KSigma N))
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ0 : ψ ≠ 0) (i : Fin K) : Measure (LF4.KSigma N) :=
  Measure.map (fun y : SwapArena (LF4.KSigma N) K => y.1.1)
    ((swapProtocol (blockIndex b) (measurable_blockIndex b)).postMeasure
      (((epistemicMeasure (Projectivization.mk ℂ ψ hψ0)).prod (readyMeasure K)).prod
        (Measure.pi ν)) i)

/-- A vertex preparation inside block `i` gives outcome `i` with nonzero probability. -/
theorem vertex_outcome_pos (b : Fin N → Fin K) {i : Fin K} {j : Fin N} (hb : b j = i) :
    ((epistemicMeasure (vertexPoint j)).prod (readyMeasure K))
      ((shearProtocol (blockIndex b) (measurable_blockIndex b)).outcomeSector i) ≠ 0 := by
  classical
  -- The selector-and-ready set sits inside the outcome sector, and has measure one.
  have hsub : selReady (blockIndex b) i
      ⊆ (shearProtocol (blockIndex b) (measurable_blockIndex b)).outcomeSector i :=
    shear_correlates (blockIndex b) (measurable_blockIndex b) i
  have hprod : selReady (blockIndex b) i
      = {x : LF4.KSigma N | blockIndex b x = i} ×ˢ readyArc K := by
    ext x
    simp [selReady, Set.mem_prod]
  have hbase : epistemicMeasure (vertexPoint j) {x : LF4.KSigma N | blockIndex b x = i} ≠ 0 := by
    have hmono : basinIndex (momentContext N) ⁻¹' {j}
        ⊆ {x : LF4.KSigma N | blockIndex b x = i} := by
      intro x hx
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
      show b (basinIndex (momentContext N) x) = i
      rw [hx, hb]
    have hfibre : epistemicMeasure (vertexPoint j)
        (basinIndex (momentContext N) ⁻¹' {j}) = 1 := by
      rw [measure_basinIndex_fibre, globalBasin_prob, momentContext_rate]
      simp [momentMap_vertex]
    have hge : (1 : ENNReal)
        ≤ epistemicMeasure (vertexPoint j) {x : LF4.KSigma N | blockIndex b x = i} := by
      rw [← hfibre]
      exact measure_mono hmono
    intro h0
    rw [h0] at hge
    exact absurd hge (by simp)
  have hready : readyMeasure K (readyArc K) ≠ 0 := by
    rw [readyMeasure, ProbabilityTheory.cond_apply measurableSet_readyArc, Set.inter_self]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
      volume_readyArc_ne_zero
  intro h0
  have hle : ((epistemicMeasure (vertexPoint j)).prod (readyMeasure K))
      (selReady (blockIndex b) i)
      ≤ ((epistemicMeasure (vertexPoint j)).prod (readyMeasure K))
        ((shearProtocol (blockIndex b) (measurable_blockIndex b)).outcomeSector i) :=
    measure_mono hsub
  rw [h0, le_zero_iff, hprod, Measure.prod_prod] at hle
  exact absurd hle (mul_ne_zero hbase hready)

/-- **★★ The boundary theorem: no fixed calibration implements degenerate Lüders.**

For any block of dimension ≥ 2 — two basis directions `j₁ ≠ j₂ with b j₁ = b j₂ = i` — the
calibrated-swap witness fails `BlockLudersObligation`, **whatever the calibration `ν`**.

The proof turns `swap_luders_marginal`'s virtue against it: the swap's post-marginal is the *fixed*
slot state `ν i`, independent of the preparation, while the obligation at the two vertex
preparations demands the two *distinct* states `epistemicMeasure [eⱼ₁]` and `epistemicMeasure
[eⱼ₂]`. So the fixed-calibration architecture is refuted for degenerate measurements — as a
theorem, not a scope note. A degenerate witness must make the relocation *depend on the
preparation's block component*; see the module docstring for the projective-join route. -/
theorem swap_not_blockLuders (b : Fin N → Fin K) {i : Fin K} {j₁ j₂ : Fin N}
    (hb₁ : b j₁ = i) (hb₂ : b j₂ = i) (hne : j₁ ≠ j₂)
    (ν : Fin K → Measure (LF4.KSigma N)) [∀ k, IsProbabilityMeasure (ν k)] :
    ¬ BlockLudersObligation b (swapPostMarg b ν) := by
  intro hob
  -- The obligation at the two vertex preparations.
  have key : ∀ (j : Fin N), b j = i →
      swapPostMarg b ν (EuclideanSpace.single j 1) (single_ne_zero' j) i
        = epistemicMeasure (vertexPoint j) := by
    intro j hbj
    have h := hob (EuclideanSpace.single j 1) (single_ne_zero' j) i
      (by rw [blockProj_single hbj]; exact single_ne_zero' j)
    rw [h]
    congr 1
    unfold vertexPoint
    rw [Projectivization.mk_eq_mk_iff]
    exact ⟨1, by simp [blockProj_single hbj]⟩
  -- But the swap's post-marginal is the fixed slot state, for both.
  have marg : ∀ (j : Fin N), b j = i →
      swapPostMarg b ν (EuclideanSpace.single j 1) (single_ne_zero' j) i = ν i := by
    intro j hbj
    rw [swapPostMarg]
    exact swap_luders_marginal (blockIndex b) (measurable_blockIndex b)
      ((epistemicMeasure (Projectivization.mk ℂ (EuclideanSpace.single j 1)
        (single_ne_zero' j))).prod (readyMeasure K)) ν i
      (vertex_outcome_pos b hbj)
  have h1 := (marg j₁ hb₁).symm.trans (key j₁ hb₁)
  have h2 := (marg j₂ hb₂).symm.trans (key j₂ hb₂)
  exact epistemicMeasure_injective (fun h => hne (vertexPoint_injective h))
    (h1.symm.trans h2)

end CSD.RecordLayer
