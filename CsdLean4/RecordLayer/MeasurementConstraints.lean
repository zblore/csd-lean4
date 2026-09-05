/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.GlobalBasin

/-!
# SigmaLayer/MeasurementConstraints: what a dynamical measurement witness must satisfy

**Category:** 7-SigmaLayer (the record layer — constraints on the *unbuilt* dynamical layer).

**Glossary:** https://glossary.constraintsurfacedynamics.com/collapse/
Plain-language, CSD-role and formal statements of collapse, with
this module as its Lean anchor. Kept symmetric by `scripts/check-glossary.sh`.

**Glossary:** https://glossary.constraintsurfacedynamics.com/measurement-problem/
Plain-language, CSD-role and formal statements of the measurement problem, with
this module as its Lean anchor. Kept symmetric by `scripts/check-glossary.sh`.

## Why this exists, and what it is not

`GlobalRecordClosure` supplies a context-fixed partition, but `globalBasin_ae_total` shows the
basins cover `Σ` up to a null set — so **a.e. point already carries a record**, and there is no
apparatus-ready state of positive measure. A flow cannot *create* a record in such a space. The
proposed repair (external review, 2026-08-01) separates the hidden **selector** from a pointer
**register**:

  `Σ_meas = ℂℙⁿ⁻¹ × T²_λ × T²_R`   (real dimension `2n+2` — even, compact, a Kähler product)

with a ready region `R₀ ⊆ T²_R` disjoint from the pointer regions `Bᵢ(M) ⊆ T²_R`, and a two-time
propagator `Φ` carrying `Sᵢ(M) × R₀` into `Bᵢ(M)`.

**This file builds none of that.** It derives *necessary conditions* on any such witness, from
measure preservation and continuity alone — before a Hamiltonian exists. The point is to fail
cheaply if the architecture is inconsistent, the way the `ℂℙⁿ⁻¹ × S¹` parity argument would have
failed cheaply had anyone run it (`specs/reconstruction-status.md` §2a).

⚠️ Nothing here asserts that a witness **exists**. These are constraints a witness must meet.

## What is proved

* `pointer_region_measure_ge` — measure preservation forces
  `μ_sel(Sᵢ) · μ_R(R₀) ≤ μ_R(Bᵢ)`. **The check comes back NEGATIVE: this does not obstruct.**
  ⚠️ *Not formalised here:* the selector sectors should carry equal **Liouville** weight `1/n` — the
  moment coordinates sum to `1` (`momentMap_sum_eq_one`) and `μ_FS` is `U(N)`-invariant, so they are
  exchangeable and each integrates to `1/n`. Granting that, the bound reads `μ_R(Bᵢ) ≥ μ_R(R₀)/n`,
  satisfiable with room to spare. The theorem below is proved in full generality and does **not**
  depend on that evaluation; only this numerical gloss does. Reported as a green light, not as a
  strong constraint — see the honest reading below.
* `ready_region_measure_le` — summing gives `μ_R(R₀) ≤ ∑ᵢ μ_R(Bᵢ) ≤ 1`. Weak, and stated so that
  the weakness is on the record rather than dressed up.
* `no_everywhere_correlation` — **the constraint with teeth.** If the correlation held
  *everywhere* rather than a.e., a connected `S ×ˢ R₀` would have connected image, which cannot
  meet two disjoint open pointer regions. So an everywhere-version is **impossible** for any
  continuous `Φ` whenever `n ≥ 2`.
  ⚠️ **It prices the everywhere case and nothing more.** It does not bound the measure of the
  exceptional set, and it does not rule out an a.e. correlation whose exceptional set has positive
  measure. Do not cite it for either. The theorem that forces *positive* measure is
  `posMeasure_noRecord_pointer` (`RecordLayer/NoRecordGeometry.lean`), which is about the pointer's
  own geometry; `SigmaLayer/FiniteQMClosure.lean` occupies the a.e.-with-a-null-seam position that
  this theorem leaves open, and names it as the seams horn.

## ★ The finding that matters for the implementation

**The "almost everywhere" in the correlation theorem is load-bearing, not a technical convenience.**
`no_everywhere_correlation` shows the exceptional set is *necessarily non-empty*: it must contain
the seams between the selector sectors, and its image is what threads through the gaps between the
pointer regions. Two consequences for anyone building the witness:

1. Any candidate `H_int` advertised as producing an **exact** correlation on all of `Σ_sel × R₀` is
   wrong, and can be rejected without examining it.
2. The construction must *say what happens on the seam*. A witness that leaves the boundary
   unspecified has not addressed the hardest part of its own statement.

## Honest reading of the negative result

The measure constraints being satisfiable is worth something — it means the architecture is not
dead on arrival, so the concrete `H_int` is worth attempting. It is **not** evidence that a witness
exists. Measure preservation is a weak invariant; the real obstructions, if any, will be symplectic
and topological, and only `no_everywhere_correlation` here is of that kind.

## References

`RecordLayer/GlobalBasin.lean` (`globalBasin`, `globalBasin_ae_total` — the a.e.-totality that
forces the selector/register split); `RecordLayer/DeIsolationFlow.lean` (the open `H_int(M)`
obligation these constrain); `specs/BACKLOG.md`.
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

/-! ### The measure constraint -/

/-- **A pointer region must be at least as large as the selector weight it receives.**

If the propagator `Φ` preserves the Liouville measure and carries `S ×ˢ R₀` into the states whose
pointer coordinate lies in `B`, then `μ_sel(S) · μ_R(R₀) ≤ μ_R(B)`.

The proof is the one-line measure-theoretic core of the whole consistency question: the correlation
requirement is exactly `S ×ˢ R₀ ⊆ Φ ⁻¹' (univ ×ˢ B)`, and measure preservation turns the measure of
that preimage into `μ_R(B)`. No injectivity of `Φ` is needed — only that it preserves measure. -/
theorem pointer_region_measure_ge
    {Xsel Xreg : Type*} [MeasurableSpace Xsel] [MeasurableSpace Xreg]
    {μs : Measure Xsel} {μr : Measure Xreg} [SFinite μs] [SFinite μr] [IsProbabilityMeasure μs]
    {Φ : Xsel × Xreg → Xsel × Xreg}
    (hΦ : MeasurePreserving Φ (μs.prod μr) (μs.prod μr))
    {S : Set Xsel} {R₀ B : Set Xreg} (hB : MeasurableSet B)
    (hcorr : S ×ˢ R₀ ⊆ Φ ⁻¹' ((univ : Set Xsel) ×ˢ B)) :
    μs S * μr R₀ ≤ μr B := by
  have h1 : (μs.prod μr) (S ×ˢ R₀) ≤ (μs.prod μr) (Φ ⁻¹' ((univ : Set Xsel) ×ˢ B)) :=
    measure_mono hcorr
  rw [hΦ.measure_preimage (MeasurableSet.univ.prod hB).nullMeasurableSet,
    Measure.prod_prod, Measure.prod_prod, measure_univ, one_mul] at h1
  exact h1

/-- **The ready region is bounded by the total pointer budget.** Summing
`pointer_region_measure_ge` over a family of selector sectors whose weights sum to `1`.

⚠️ **This constraint is weak and is recorded as such.** It says only `μ_R(R₀) ≤ ∑ᵢ μ_R(Bᵢ)`, and
since the `Bᵢ` are disjoint subsets of a probability space the right-hand side is at most `1`. It
does not meaningfully restrict the construction; it is stated so that the weakness is visible rather
than inferred. -/
theorem ready_region_measure_le
    {Xsel Xreg : Type*} [MeasurableSpace Xsel] [MeasurableSpace Xreg] {n : ℕ}
    {μs : Measure Xsel} {μr : Measure Xreg} [SFinite μs] [SFinite μr] [IsProbabilityMeasure μs]
    {Φ : Xsel × Xreg → Xsel × Xreg}
    (hΦ : MeasurePreserving Φ (μs.prod μr) (μs.prod μr))
    {S : Fin n → Set Xsel} {R₀ : Set Xreg} {B : Fin n → Set Xreg}
    (hB : ∀ i, MeasurableSet (B i))
    (hcorr : ∀ i, S i ×ˢ R₀ ⊆ Φ ⁻¹' ((univ : Set Xsel) ×ˢ B i))
    (hweights : ∑ i, μs (S i) = 1) :
    μr R₀ ≤ ∑ i, μr (B i) := by
  calc μr R₀ = (∑ i, μs (S i)) * μr R₀ := by rw [hweights, one_mul]
    _ = ∑ i, μs (S i) * μr R₀ := by rw [Finset.sum_mul]
    _ ≤ ∑ i, μr (B i) :=
        Finset.sum_le_sum fun i _ => pointer_region_measure_ge hΦ (hB i) (hcorr i)

/-! ### The topological constraint — the one with teeth -/

/-- **★ An *everywhere* correlation is impossible.**

If `Φ` is continuous and the source `S ×ˢ R₀` is preconnected, its image is preconnected, so it
cannot meet two *disjoint open* pointer regions. Since a measurement with `n ≥ 2` outcomes requires
the image to reach at least two of them, no continuous propagator can satisfy the correlation
requirement **everywhere** on a connected ready set.

★ **Therefore the `a.e.` qualifier in the correlation theorem is mathematically necessary, not a
technical convenience.** The exceptional set must be non-empty — it contains the seams between
selector sectors, and its image is what threads through the gaps between pointer regions. Any
proposed `H_int` advertised as giving an exact, everywhere correlation is wrong on these grounds
alone, without inspecting it.

Stated for two regions, which is all an impossibility needs. -/
theorem no_everywhere_correlation
    {Xsel Xreg : Type*} [TopologicalSpace Xsel] [TopologicalSpace Xreg]
    {Φ : Xsel × Xreg → Xsel × Xreg} (hcont : Continuous Φ)
    {S : Set Xsel} {R₀ : Set Xreg} (hconn : IsPreconnected (S ×ˢ R₀))
    {U V : Set (Xsel × Xreg)} (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hsub : Φ '' (S ×ˢ R₀) ⊆ U ∪ V)
    (hmeetU : ∃ x ∈ S ×ˢ R₀, Φ x ∈ U)
    (hmeetV : ∃ x ∈ S ×ˢ R₀, Φ x ∈ V) :
    False := by
  have himg : IsPreconnected (Φ '' (S ×ˢ R₀)) := hconn.image Φ hcont.continuousOn
  obtain ⟨xu, hxu, hxuU⟩ := hmeetU
  obtain ⟨xv, hxv, hxvV⟩ := hmeetV
  have hne : (Φ '' (S ×ˢ R₀) ∩ U).Nonempty := ⟨Φ xu, ⟨xu, hxu, rfl⟩, hxuU⟩
  have hin : Φ '' (S ×ˢ R₀) ⊆ U := himg.subset_left_of_subset_union hU hV hUV hsub hne
  exact (hUV.le_bot ⟨hin ⟨xv, hxv, rfl⟩, hxvV⟩ : Φ xv ∈ (⊥ : Set (Xsel × Xreg)))

/-! ### The collapse no-gos (2026-08-01)

Constraints on the *Lüders* half of the dynamical layer, derived before any collapse witness is
built — the same cheap-failure discipline as above. The upshot of the pair: **exact pointwise
collapse is impossible for a measure-preserving dynamics, and approximate collapse is paid for in
ready-state improbability.** So any exact-Lüders witness must implement collapse as a measure-zero
*relocation* (the epistemic Dirac slice moves) rather than a contraction of positive-measure sets.

The continuous-collapse twin of `no_everywhere_correlation` — a continuous map cannot carry a
connected ready set into disjoint neighbourhoods of the `N` basis vertices — is an *instantiation*
of that theorem (take `U`, `V` to be the neighbourhoods), not a new statement; no separate
declaration is added for it. -/

/-- **★ No-go A: exact pointwise collapse is impossible.**

If a measure-preserving `Φ` sends a positive-measure set `C` (the collapsing states) into a null
target `T` (e.g. `{[e₁],…,[e_N]} × anything`, null because `μ_FS` is nonatomic), that contradicts
measure preservation outright: `0 < μ C ≤ μ (Φ⁻¹ T) = μ T = 0`.

Consequence: "conditioned on the outcome, the base moves **to** `[eᵢ]`" can hold only on a
Liouville-null set of states — which the epistemic `δ_[ψ] ⊗ Haar` slice is. Collapse must be
**relocation of a null slice, not contraction of a positive-measure one**. -/
theorem no_exact_collapse
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {Φ : X → X} (hΦ : MeasurePreserving Φ μ μ)
    {C T : Set X} (hT : NullMeasurableSet T μ) (hTnull : μ T = 0)
    (hsub : C ⊆ Φ ⁻¹' T) (hCpos : μ C ≠ 0) : False := by
  apply hCpos
  have h := (measure_mono hsub).trans (le_of_eq (hΦ.measure_preimage hT))
  exact le_zero_iff.mp (h.trans (le_of_eq hTnull))

/-- **★ No-go B: collapse accuracy is bought with ready-state improbability.**

The mirror of `pointer_region_measure_ge` with the roles of base and register exchanged: if the
correlation drives the *base* into an `ε`-target `B` (a small neighbourhood of a vertex), then
`μ_sel(S) · μ_R(R₀) ≤ μ_sel(B)`. Summed over outcomes (with the selector weights summing to `1`)
this reads `μ_R(R₀) ≤ ∑ᵢ μ_sel(Bᵢ)` — **the apparatus-ready region must shrink as the collapse
targets do**, and exact collapse (`ε → 0`) forces a null ready set.

This is Landauer's cost appearing as a measure inequality, and it *retroactively justifies* the
corpus's Dirac-calibration convention: an exactly calibrated apparatus is a null set because it has
to be. -/
theorem collapse_accuracy_bound
    {Xsel Xreg : Type*} [MeasurableSpace Xsel] [MeasurableSpace Xreg]
    {μs : Measure Xsel} {μr : Measure Xreg} [SFinite μs] [SFinite μr] [IsProbabilityMeasure μr]
    {Φ : Xsel × Xreg → Xsel × Xreg}
    (hΦ : MeasurePreserving Φ (μs.prod μr) (μs.prod μr))
    {S B : Set Xsel} {R₀ : Set Xreg} (hB : MeasurableSet B)
    (hcorr : S ×ˢ R₀ ⊆ Φ ⁻¹' (B ×ˢ (univ : Set Xreg))) :
    μs S * μr R₀ ≤ μs B := by
  have h1 : (μs.prod μr) (S ×ˢ R₀) ≤ (μs.prod μr) (Φ ⁻¹' (B ×ˢ (univ : Set Xreg))) :=
    measure_mono hcorr
  rw [hΦ.measure_preimage (hB.prod MeasurableSet.univ).nullMeasurableSet,
    Measure.prod_prod, Measure.prod_prod, measure_univ, mul_one] at h1
  exact h1

end CSD.RecordLayer
