import CsdLean4.LF5.SyndromeFlow
import CsdLean4.LF5.FlowBornFrequency
import CsdLean4.LF5.PointerOutcome
import CsdLean4.LF4.BornRegionDisjoint

/-!
# LF5: syndrome-granularity frequency + outcome map (QEC, projective tier)

**Category:** 3-Local (LF5 measurement-dynamics layer, QEC tranche).

This module **completes the QEC syndrome tranche** by mirroring the
pointer-level LF5-D (`vnDilation_pointer_frequency`) and LF5-F
(`vnPointerOutcome` / `measurement_flow_outcome_frequency`) results at
**syndrome granularity** for the three-qubit bit-flip code (`N = 8`). It is a
**pure mechanical coarse-graining** of the existing engines by the parity
classifier `synClass : Fin 8 → Fin 4` (`LF5/SyndromeFlow.lean`): no new
dilation, no new flow, no new physics. The module only imports and assembles.

## What is delivered

* `syndrome_flow_born_frequency` (+ `_canonical`): a.s., for every syndrome
  `s : Fin 4`, the syndrome-class block frequency — the double sum over the
  pointers `i ∈ class s` and the apparatus index `n : Fin 8` of the per-cell
  empirical frequencies — converges to `syndromeWeight ψ s` (the block sum of
  the computational-basis Born weights, `SyndromeFlow.lean`). Proof: a finite
  class sum (`tendsto_finset_sum`) of the per-pointer
  `vnDilation_pointer_frequency` limits, landing on `syndromeWeight` via
  `syndromeWeight_eq_pointer_sum`.
* `synOutcome` + `synOutcome_preimage_some`: the per-microstate **syndrome**
  outcome map `CPN (M+1) → Option (Fin 4)`, `vnPointerOutcome` post-composed
  with the ψ-INDEPENDENT parity classifier `synClass`; its `some s` fibre is the
  syndrome-class block union `⋃_{i ∈ class s} ⋃_n bornRegion ψ' (e (n,i))`.
* `syndrome_flow_outcome_frequency` (+ `_canonical`): a.s., for every syndrome
  `s`, the frequency of trials whose microstate's *syndrome* outcome is `s` — a
  **single** event per syndrome, `(X k) ⁻¹' (synOutcome ⁻¹' {some s})`, not a
  sum — converges to `syndromeWeight ψ s`. Mirrors
  `measurement_flow_outcome_frequency`: union-indicator split over the
  genuinely disjoint class cells (`bornRegion_pairwiseDisjoint` + `e`
  injectivity), landing on the block-sum limit of `syndrome_flow_born_frequency`.

## Honest scope

Unchanged from `SyndromeFlow.lean`. Projective / **coherent-error tier only**.
The Born **numbers** are reused from the FS-volume = Born engine
(`vnDilation_pointer_volume` / `vnDilation_pointer_frequency`), not re-derived;
this module just coarse-grains the pointer index by the fixed `synClass`. The FS
typicality law on the dilated sector (**A5**) is posited. The syndrome partition
into blocks is `synClass`, a fixed **ψ-independent** function (the pre-registered
tripwire: `ψ`/`ψ'` enter only the cell *shapes* `bornRegion ψ'`, never the index
sets). The **decoherence / partial-trace** origin of incoherent errors is **NOT**
here — gated entangled tier (`specs/lf5-plan.md` §0; Bell forces non-locality).

Mirrors the register-Σ honesty conventions of the LF5 module docstrings.

Reference: `specs/lf5-plan.md`; `specs/carve-out-plan.md` §6.
-/

open MeasureTheory ProbabilityTheory Filter Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization

namespace CSD
namespace LF5

open CSD.LF2 CSD.LF4

variable {M : ℕ}

/-! ## Syndrome weight as an inner-product block sum (helper) -/

/-- **Syndrome weight = the block sum of computational-basis Born weights**, in
inner-product form. This is literally `syndromeWeight_eq_pointer_sum`
(`SyndromeFlow.lean`), surfaced here under the name used by the part-(A) limit
identity: the limit of the syndrome-class block frequency is
`∑_{i ∈ class s} ‖⟨eᵢ, ψ⟩‖²`, which this identifies with `syndromeWeight ψ s`. -/
theorem syndromeWeight_eq_inner_sum (ψ : EuclideanSpace ℂ (Fin 8)) (s : Fin 4) :
    syndromeWeight ψ s
      = ∑ i ∈ Finset.univ.filter (fun i => synClass i = s),
          ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 :=
  syndromeWeight_eq_pointer_sum ψ s

/-! ## (A) Syndrome-class block frequencies converge to the syndrome weight -/

/-- **Syndrome-class block frequencies → syndrome weight, every unit `ψ`.** For
i.i.d. FS-typical trials on the dilated `ℂℙ^{63}` (the A5 posit on the enlarged
`N = 8` sector), almost surely **every** syndrome `s : Fin 4` has its
syndrome-class block frequency — the double sum, over the pointers `i ∈ class s`
and the apparatus index `n : Fin 8`, of the per-cell empirical frequencies
`(∑_{k<m} indicator((X k)⁻¹' bornRegion ψ' (e (n, i))) ω) / m` — converging to
`syndromeWeight ψ s`.

Proof: `filter_upwards` on `vnDilation_pointer_frequency`; the a.s. ω gives, for
each pointer `i`, convergence of the pointer-`i` block frequency to `‖⟨eᵢ,ψ⟩‖²`.
Sum over the class `Finset.univ.filter (synClass · = s)` by `tendsto_finset_sum`
(continuity of finite addition); the limit `∑_{i ∈ class s} ‖⟨eᵢ,ψ⟩‖²` is
`syndromeWeight ψ s` (`syndromeWeight_eq_inner_sum`). The syndrome-block
frequency function is presented as a finite class sum of the per-pointer block
frequency functions, so `tendsto_finset_sum` applies termwise. -/
theorem syndrome_flow_born_frequency
    (ψ : EuclideanSpace ℂ (Fin 8)) (hψ : ‖ψ‖ = 1)
    (e : (Fin 8 × Fin 8) ≃ Fin (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV 8) ψ))
    (hψ'0 : ψ' ≠ 0)
    (p₀ : CPN (M + 1))
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ j : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ' hψ'0 j) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ s : Fin 4,
      Tendsto
        (fun m : ℕ =>
          ∑ i ∈ Finset.univ.filter (fun i => synClass i = s),
            ∑ n : Fin 8,
              (∑ k ∈ Finset.range m,
                  Set.indicator ((X k) ⁻¹' bornRegion ψ' hψ'0 (e (n, i))) (fun _ => (1 : ℝ)) ω)
                / (m : ℝ))
        atTop
        (nhds (syndromeWeight ψ s)) := by
  filter_upwards [vnDilation_pointer_frequency (N := 8) ψ hψ e ψ' hψ'eq hψ'0 p₀ X hX hlaw hindep]
    with ω hω s
  rw [syndromeWeight_eq_inner_sum]
  exact tendsto_finset_sum _ (fun i _ => hω i)

/-- **Syndrome-class block frequencies → syndrome weight, on the canonical i.i.d.
FS trial process.** `syndrome_flow_born_frequency` with the trial bundle
discharged by the canonical coordinate process (`fsTrialMeasure` / `fsTrial`),
mirroring `measurement_flow_born_frequency_canonical`. -/
theorem syndrome_flow_born_frequency_canonical
    (ψ : EuclideanSpace ℂ (Fin 8)) (hψ : ‖ψ‖ = 1)
    (e : (Fin 8 × Fin 8) ≃ Fin (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV 8) ψ))
    (hψ'0 : ψ' ≠ 0)
    (p₀ : CPN (M + 1)) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀, ∀ s : Fin 4,
      Tendsto
        (fun m : ℕ =>
          ∑ i ∈ Finset.univ.filter (fun i => synClass i = s),
            ∑ n : Fin 8,
              (∑ k ∈ Finset.range m,
                  Set.indicator ((fsTrial (M + 1) k) ⁻¹' bornRegion ψ' hψ'0 (e (n, i)))
                    (fun _ => (1 : ℝ)) ω)
                / (m : ℝ))
        atTop
        (nhds (syndromeWeight ψ s)) :=
  syndrome_flow_born_frequency ψ hψ e ψ' hψ'eq hψ'0 p₀
    (fsTrial (M + 1)) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀ (bornRegion ψ' hψ'0)
      (bornRegion_measurable_uncond ψ' hψ'0))

/-! ## (B) The per-microstate syndrome outcome map -/

/-- **The per-microstate syndrome outcome map.** The syndrome class of the
microstate's cell: `vnPointerOutcome` post-composed with the parity classifier
`synClass`. Equivalently `(bornOutcome ψ' hψ'0 ·).map (synClass ∘ (e.symm ·).2)`.
The pointer→syndrome coarse-graining `synClass` and the block assignment
`c ↦ (e.symm c).2` are both **ψ-independent and context-fixed** — only the
measurement context `e` enters, never the preparation. Deterministic and total
off an FS-null set (inherited from `bornOutcome`). -/
noncomputable def synOutcome
    (ψ' : EuclideanSpace ℂ (Fin (M + 1))) (hψ'0 : ψ' ≠ 0)
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1)) :
    CPN (M + 1) → Option (Fin 4) :=
  fun p => (vnPointerOutcome ψ' hψ'0 e p).map synClass

/-- **The syndrome-`s` fibre is the syndrome-class block union.** The set of
microstates whose syndrome outcome is `s` is the union over the pointers
`i ∈ class s` and the apparatus index `n` of the dilated Born cells
`bornRegion ψ' hψ'0 (e (n, i))`. Via `vnPointerOutcome_preimage_some` and the
`Option.map` fibre algebra over the (`ψ`-independent) classifier `synClass`. -/
theorem synOutcome_preimage_some
    (ψ' : EuclideanSpace ℂ (Fin (M + 1))) (hψ'0 : ψ' ≠ 0)
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1)) (s : Fin 4) :
    synOutcome ψ' hψ'0 e ⁻¹' {some s}
      = ⋃ i ∈ Finset.univ.filter (fun i => synClass i = s),
          ⋃ n : Fin 8, bornRegion ψ' hψ'0 (e (n, i)) := by
  ext p
  rw [Set.mem_preimage, Set.mem_singleton_iff, synOutcome, Option.map_eq_some_iff,
    Set.mem_iUnion₂]
  constructor
  · rintro ⟨i, hi, his⟩
    -- `vnPointerOutcome p = some i` ⇒ `p ∈ pointer-i block`; `synClass i = s`
    have hmem : p ∈ vnPointerOutcome ψ' hψ'0 e ⁻¹' {some i} := hi
    rw [vnPointerOutcome_preimage_some, Set.mem_iUnion] at hmem
    obtain ⟨n, hn⟩ := hmem
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, his⟩, ?_⟩
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  · rintro ⟨i, hi, hn⟩
    rw [Finset.mem_filter] at hi
    rw [Set.mem_iUnion] at hn
    obtain ⟨n, hn⟩ := hn
    refine ⟨i, ?_, hi.2⟩
    -- `p ∈ pointer-i block` ⇒ `vnPointerOutcome p = some i`
    show p ∈ vnPointerOutcome ψ' hψ'0 e ⁻¹' {some i}
    rw [vnPointerOutcome_preimage_some, Set.mem_iUnion]
    exact ⟨n, hn⟩

/-! ## (C) Syndrome outcome frequencies converge to the syndrome weight -/

/-- **LF5-F (syndrome) outcome-frequency capstone: per-microstate syndrome
outcomes commit the syndrome-class frequencies.** With the LF5-D/E set-up (unit
`ψ`, dilated state `ψ' = piLpCongrLeft e (Vψ)`) at `N = 8`, for i.i.d. FS-typical
trials on the dilated `ℂℙ^{63}`, almost surely **every** syndrome `s : Fin 4`
has the frequency of trials whose microstate's *syndrome* outcome is `s` — a
**single** event per syndrome, `(X k) ⁻¹' (synOutcome ⁻¹' {some s})`, not a sum
of per-cell frequencies — converging to `syndromeWeight ψ s`.

This is the syndrome-granularity analogue of `measurement_flow_outcome_frequency`.
Proof: rewrite the outcome event into the syndrome-class block union
(`synOutcome_preimage_some` + `Set.preimage_iUnion`), turn the union indicator
into the sum over the genuinely disjoint cells indexed by
`{(i, n) : i ∈ class s}` via `indicator_iUnion_disjoint` + `bornRegion_pairwiseDisjoint`
(disjointness across BOTH `i` and `n`: `(n, i) ↦ e (n, i)` is injective), then
land on part (A)'s block-sum limit `syndrome_flow_born_frequency`. -/
theorem syndrome_flow_outcome_frequency
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1))
    (ψ : EuclideanSpace ℂ (Fin 8)) (hψ : ‖ψ‖ = 1)
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV 8) ψ))
    (hψ'0 : ψ' ≠ 0)
    (p₀ : CPN (M + 1))
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ j : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ' hψ'0 j) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ s : Fin 4,
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator ((X k) ⁻¹' (synOutcome ψ' hψ'0 e ⁻¹' {some s}))
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (syndromeWeight ψ s)) := by
  filter_upwards [syndrome_flow_born_frequency ψ hψ e ψ' hψ'eq hψ'0 p₀ X hX hlaw hindep]
    with ω hω s
  -- the class-block cell index `{(n, i) : i ∈ class s}` (apparatus n, pointer i)
  set t : Finset (Fin 8 × Fin 8) :=
    Finset.univ ×ˢ Finset.univ.filter (fun i => synClass i = s) with ht
  -- the cells over `t` are pairwise disjoint: `(n, i) ↦ e (n, i)` injective
  have hdisj : ∀ k, (↑t : Set (Fin 8 × Fin 8)).PairwiseDisjoint
      (fun q => (X k) ⁻¹' bornRegion ψ' hψ'0 (e q)) := by
    intro k q _ q' _ hqq'
    apply Disjoint.preimage
    exact bornRegion_pairwiseDisjoint ψ' hψ'0 (fun h => hqq' (e.injective h))
  -- rewrite the outcome event into the disjoint class-block union over `t`
  have hpre : ∀ k, (X k) ⁻¹' (synOutcome ψ' hψ'0 e ⁻¹' {some s})
      = ⋃ q ∈ t, (X k) ⁻¹' bornRegion ψ' hψ'0 (e q) := by
    intro k
    rw [synOutcome_preimage_some, Set.preimage_iUnion₂]
    -- ⋃_{i ∈ class s} ⋃_n preimage(e (n,i)) = ⋃_{q ∈ t} preimage(e q), t = univ ×ˢ class
    ext x
    rw [Set.mem_iUnion₂, Set.mem_iUnion₂]
    constructor
    · rintro ⟨i, hi, hx⟩
      rw [Set.preimage_iUnion, Set.mem_iUnion] at hx
      obtain ⟨n, hn⟩ := hx
      refine ⟨(n, i), ?_, hn⟩
      rw [ht, Finset.mem_product]
      exact ⟨Finset.mem_univ _, hi⟩
    · rintro ⟨q, hq, hn⟩
      rw [ht, Finset.mem_product] at hq
      refine ⟨q.2, hq.2, ?_⟩
      rw [Set.preimage_iUnion, Set.mem_iUnion]
      exact ⟨q.1, hn⟩
  -- indicator of the disjoint union = sum of the cell indicators over `t`
  have hsum_ind : ∀ k ω0, Set.indicator ((X k) ⁻¹' (synOutcome ψ' hψ'0 e ⁻¹' {some s}))
        (fun _ => (1 : ℝ)) ω0
      = ∑ q ∈ t, Set.indicator ((X k) ⁻¹' bornRegion ψ' hψ'0 (e q)) (fun _ => (1 : ℝ)) ω0 := by
    intro k ω0
    rw [hpre k]
    exact indicator_iUnion_disjoint t _ (hdisj k) _ ω0
  -- assemble: outcome-event frequency = block-sum frequency = part (A)'s limit
  have hfreq_eq : ∀ m : ℕ,
      (∑ k ∈ Finset.range m,
          Set.indicator ((X k) ⁻¹' (synOutcome ψ' hψ'0 e ⁻¹' {some s}))
            (fun _ => (1 : ℝ)) ω) / (m : ℝ)
      = ∑ i ∈ Finset.univ.filter (fun i => synClass i = s),
          ∑ n : Fin 8,
            (∑ k ∈ Finset.range m,
                Set.indicator ((X k) ⁻¹' bornRegion ψ' hψ'0 (e (n, i)))
                  (fun _ => (1 : ℝ)) ω)
              / (m : ℝ) := by
    intro m
    -- numerator: ∑_k indicator(outcome event) = ∑_k ∑_{q ∈ t} indicator(cell q)
    rw [Finset.sum_congr rfl (fun k _ => hsum_ind k ω)]
    -- ∑_k ∑_{q ∈ t} = ∑_{q ∈ t} ∑_k, then split t = univ ×ˢ class, swap to ∑_{i ∈ class} ∑_n
    rw [Finset.sum_comm, ht, Finset.sum_product, Finset.sum_comm (s := Finset.univ)]
    -- (∑_{i ∈ class} ∑_n ∑_k ...) / m = ∑_{i ∈ class} ∑_n (∑_k ...) / m
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_div]
  simp_rw [hfreq_eq]
  exact hω s

/-- **LF5-F (syndrome) outcome-frequency capstone on the canonical i.i.d. FS
trial process.** `syndrome_flow_outcome_frequency` with the trial bundle
discharged by the canonical coordinate process (`fsTrialMeasure` / `fsTrial`),
mirroring `measurement_flow_outcome_frequency_canonical`. -/
theorem syndrome_flow_outcome_frequency_canonical
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1))
    (ψ : EuclideanSpace ℂ (Fin 8)) (hψ : ‖ψ‖ = 1)
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV 8) ψ))
    (hψ'0 : ψ' ≠ 0)
    (p₀ : CPN (M + 1)) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀, ∀ s : Fin 4,
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator ((fsTrial (M + 1) k) ⁻¹' (synOutcome ψ' hψ'0 e ⁻¹' {some s}))
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (syndromeWeight ψ s)) :=
  syndrome_flow_outcome_frequency e ψ hψ ψ' hψ'eq hψ'0 p₀
    (fsTrial (M + 1)) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀ (bornRegion ψ' hψ'0)
      (bornRegion_measurable_uncond ψ' hψ'0))

end LF5
end CSD
