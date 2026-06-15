import CsdLean4.LF5.CapstoneCanonical
import CsdLean4.LF4.BornRegionDisjoint

/-!
# LF5: the per-microstate pointer-outcome map and the outcome-frequency capstone

**Category:** 3-Local (LF5 measurement-dynamics layer, outcome-map tranche).

This is **LF5-F** (LF5 half) of `specs/lf5-plan.md`: the upgrade of the LF5
capstone from outcome *statistics* (a sum of per-cell block frequencies,
`measurement_flow_born_frequency` conjunct (5)) to a deterministic per-microstate
outcome *function*, the genuine realisation of the contextual outcome-map slot.

The engine half (`CsdLean4/LF4/BornRegionDisjoint.lean`) supplies the
pairwise-disjointness of the `bornRegion` cells (so the moment-subdivision is a
genuine partition), the per-microstate `bornOutcome : CPN (M+1) → Option (Fin (M+1))`
(`some i` on cell `i`, total off an FS-null set), and the indicator-of-disjoint-
union bridge. This module lifts that cell map to the **pointer** map and lands the
single-event outcome-frequency limit.

## What is delivered

* `vnPointerOutcome` — `CPN (M+1) → Option (Fin N)`, the apparatus/pointer index
  of the microstate's cell: `bornOutcome` post-composed with the ψ-independent,
  context-fixed block assignment `c ↦ (e.symm c).2` (the second factor of the
  `Fin N × Fin N` reindex). The block assignment is the **audited tripwire**: it
  does not depend on the preparation, only on the fixed measurement context `e`.
* `vnPointerOutcome_preimage_some` — the `some i` fibre is the pointer-`i` block
  union `⋃ n, bornRegion ψ' hψ'0 (e (n, i))`.
* `measurement_flow_outcome_frequency` — the conjunct-(5) **upgrade**: the
  frequency of trials whose microstate's *outcome* is pointer `i` (a single
  event per pointer, not a sum of cell frequencies) converges a.s. to the Born
  weight `‖⟨eᵢ, ψ⟩‖²`. Conjuncts (1)-(4) of `measurement_flow_born_frequency`
  are unchanged; see that theorem for them.
* `measurement_flow_outcome_frequency_canonical` — the same on the canonical
  i.i.d. FS trial process (`fsTrialMeasure` / `fsTrial`).

## The ContextMap slot, now realised

`LF3/ContextMap.lean`'s `ContextIndexedOutcomeMaps` carries an abstract per-context
outcome map `F : (ctx) → Domain ctx → Sign × Sign`. For the single-system
measurement, LF5 now realises that slot **both dynamically and definitionally**:

* per-context state space = the dilated `Σ' = ℂℙ^{N·N−1}`;
* outcome map = `vnPointerOutcome` — deterministic (one cell per microstate, by
  `bornRegion_pairwiseDisjoint`), total off an FS-null set
  (`bornOutcome_ae_isSome`), measurable fibres (`bornOutcome_measurable`);
* the context enters only through the fixed vN coupling (the flow `Φ_vN`) plus
  the **ψ-independent** block assignment `c ↦ (e.symm c).2`.

The outcome is **fixed by the microstate** (deterministic given `(ψ, context)`),
the de-isolation reading required. Honest residue, unchanged from LF5-D/E: the
cell *shapes* (`bornRegion ψ'`) remain `ψ'`-dependent — the engine's realisation
mechanism, with measures forced by the Kähler geometry, not carved; the Born
*number* is from the FS-volume engine; A5 is posited; entanglement is deferred
(Bell forces a non-local de-isolation map). Single-system projective tier only.

Reference: `specs/lf5-plan.md` (LF5-F); the owed-since-`aeece86` outcome map.
-/

open MeasureTheory ProbabilityTheory Filter Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization

namespace CSD
namespace LF5

open CSD.LF2 CSD.LF4

variable {N M : ℕ}

/-- **The per-microstate pointer-outcome map.** The apparatus/pointer index of
the microstate's cell: `some ((e.symm c).2)` when the microstate lands in cell
`c`, `none` off the union. The block assignment `c ↦ (e.symm c).2` (the second,
apparatus, factor of the `Fin N × Fin N` reindex) is **ψ-independent and
context-fixed** — it depends only on the measurement context `e`, not on the
preparation. Deterministic and total off an FS-null set (inherited from
`bornOutcome`). -/
noncomputable def vnPointerOutcome
    (ψ' : EuclideanSpace ℂ (Fin (M + 1))) (hψ'0 : ψ' ≠ 0)
    (e : Fin N × Fin N ≃ Fin (M + 1)) :
    CPN (M + 1) → Option (Fin N) :=
  fun p => (bornOutcome ψ' hψ'0 p).map (fun c => (e.symm c).2)

/-- **The pointer-`i` fibre is the pointer-`i` block union.** The set of
microstates whose outcome is pointer `i` is the union over the apparatus index
`n` of the dilated Born cells `bornRegion ψ' hψ'0 (e (n, i))`. Via
`bornOutcome_preimage_some` and the `Option.map` fibre algebra + `e`
bijectivity. -/
theorem vnPointerOutcome_preimage_some
    (ψ' : EuclideanSpace ℂ (Fin (M + 1))) (hψ'0 : ψ' ≠ 0)
    (e : Fin N × Fin N ≃ Fin (M + 1)) (i : Fin N) :
    vnPointerOutcome ψ' hψ'0 e ⁻¹' {some i}
      = ⋃ n : Fin N, bornRegion ψ' hψ'0 (e (n, i)) := by
  ext p
  simp only [vnPointerOutcome, Set.mem_preimage, Set.mem_singleton_iff,
    Option.map_eq_some_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨c, hc, hci⟩
    -- `bornOutcome p = some c` ⇒ `p ∈ cell c`; `(e.symm c).2 = i` ⇒ `c = e (n, i)`
    rw [bornOutcome_eq_some_iff] at hc
    refine ⟨(e.symm c).1, ?_⟩
    rwa [show e ((e.symm c).1, i) = c from by
      rw [← hci, Prod.mk.eta, Equiv.apply_symm_apply]]
  · rintro ⟨n, hn⟩
    refine ⟨e (n, i), ?_, ?_⟩
    · rw [bornOutcome_eq_some_iff]; exact hn
    · rw [Equiv.symm_apply_apply]

/-- **LF5-F outcome-frequency capstone: per-microstate pointer outcomes commit
the Born frequencies.** With the LF5-D/E set-up (unit `ψ`, dilated state
`ψ' = piLpCongrLeft e (Vψ)`), for i.i.d. FS-typical trials on the dilated
`ℂℙ^{N·N−1}`, almost surely **every** pointer `i` has the frequency of trials
whose microstate's *outcome* is pointer `i` — a **single** event per pointer,
`(X k) ⁻¹' (vnPointerOutcome ⁻¹' {some i})`, not a sum of per-cell frequencies —
converging to the Born weight `‖⟨eᵢ, ψ⟩‖²`.

This is the conjunct-(5) **upgrade** of `measurement_flow_born_frequency`:
from outcome statistics (a sum of cell-indicator frequencies) to a deterministic
per-microstate outcome function. Conjuncts (1)-(4) (`Φ_vN ≠ id`,
measure-preservation, context-fixedness, committed volume = Born) are unchanged;
see `measurement_flow_born_frequency` for them.

Proof: rewrite the outcome event into the pointer-block union
(`vnPointerOutcome_preimage_some`), turn the union indicator into the block sum
(`indicator_iUnion_disjoint` + pairwise disjointness of the block cells, a
sub-family of `bornRegion_pairwiseDisjoint`), and land on
`vnDilation_pointer_frequency`. -/
theorem measurement_flow_outcome_frequency
    [NeZero N] (hN : 1 < N)
    (e : Fin N × Fin N ≃ Fin (M + 1))
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1)
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV N) ψ))
    (hψ'0 : ψ' ≠ 0)
    (p₀ : CPN (M + 1))
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ j : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ' hψ'0 j) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ i : Fin N,
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator ((X k) ⁻¹' (vnPointerOutcome ψ' hψ'0 e ⁻¹' {some i}))
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)) := by
  filter_upwards [vnDilation_pointer_frequency ψ hψ e ψ' hψ'eq hψ'0 p₀ X hX hlaw hindep]
    with ω hω i
  -- rewrite the single outcome event into the block union, then split the
  -- indicator over the disjoint block, matching the block-sum form of `hω i`.
  have hpre : ∀ k, (X k) ⁻¹' (vnPointerOutcome ψ' hψ'0 e ⁻¹' {some i})
      = ⋃ n : Fin N, (X k) ⁻¹' bornRegion ψ' hψ'0 (e (n, i)) := by
    intro k
    rw [vnPointerOutcome_preimage_some, Set.preimage_iUnion]
  -- the block cells are pairwise disjoint (sub-family of bornRegion_pairwiseDisjoint)
  have hdisj : ∀ k, ((Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint
      (fun n => (X k) ⁻¹' bornRegion ψ' hψ'0 (e (n, i))) := by
    intro k n _ n' _ hnn'
    apply Disjoint.preimage
    exact bornRegion_pairwiseDisjoint ψ' hψ'0
      (fun h => hnn' (by
        have := e.injective (by rw [h] : e (n, i) = e (n', i))
        exact (Prod.ext_iff.mp this).1))
  -- indicator of the disjoint union = sum of block indicators
  have hsum_ind : ∀ k ω0, Set.indicator ((X k) ⁻¹' (vnPointerOutcome ψ' hψ'0 e ⁻¹' {some i}))
        (fun _ => (1 : ℝ)) ω0
      = ∑ n : Fin N,
          Set.indicator ((X k) ⁻¹' bornRegion ψ' hψ'0 (e (n, i))) (fun _ => (1 : ℝ)) ω0 := by
    intro k ω0
    rw [hpre k,
      show (⋃ n : Fin N, (X k) ⁻¹' bornRegion ψ' hψ'0 (e (n, i)))
          = ⋃ n ∈ (Finset.univ : Finset (Fin N)),
              (X k) ⁻¹' bornRegion ψ' hψ'0 (e (n, i)) from by
        simp only [Finset.mem_univ, Set.iUnion_true]]
    exact indicator_iUnion_disjoint Finset.univ _ (hdisj k) _ ω0
  -- assemble: the outcome-event frequency = the block-sum frequency = `hω i`
  have hfreq_eq : ∀ m : ℕ,
      (∑ k ∈ Finset.range m,
          Set.indicator ((X k) ⁻¹' (vnPointerOutcome ψ' hψ'0 e ⁻¹' {some i}))
            (fun _ => (1 : ℝ)) ω) / (m : ℝ)
      = ∑ n : Fin N,
          (∑ k ∈ Finset.range m,
              Set.indicator ((X k) ⁻¹' bornRegion ψ' hψ'0 (e (n, i)))
                (fun _ => (1 : ℝ)) ω) / (m : ℝ) := by
    intro m
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => hsum_ind k ω)
  simp_rw [hfreq_eq]
  exact hω i

/-- **LF5-F outcome-frequency capstone on the canonical i.i.d. FS trial process.**
`measurement_flow_outcome_frequency` with the trial bundle discharged by the
canonical coordinate process (`fsTrialMeasure` / `fsTrial`), mirroring
`measurement_flow_born_frequency_canonical`. -/
theorem measurement_flow_outcome_frequency_canonical
    [NeZero N] (hN : 1 < N)
    (e : Fin N × Fin N ≃ Fin (M + 1))
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1)
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV N) ψ))
    (hψ'0 : ψ' ≠ 0)
    (p₀ : CPN (M + 1)) :
    ∀ᵐ ω ∂ fsTrialMeasure p₀, ∀ i : Fin N,
      Tendsto
        (fun m : ℕ =>
          (∑ k ∈ Finset.range m,
              Set.indicator ((fsTrial (M + 1) k) ⁻¹' (vnPointerOutcome ψ' hψ'0 e ⁻¹' {some i}))
                (fun _ => (1 : ℝ)) ω) / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)) :=
  measurement_flow_outcome_frequency hN e ψ hψ ψ' hψ'eq hψ'0 p₀
    (fsTrial (M + 1)) fsTrial_measurable (fsTrial_law p₀)
    (fsTrial_pairwise_indepFun_indicator p₀ (bornRegion ψ' hψ'0)
      (bornRegion_measurable_uncond ψ' hψ'0))

end LF5
end CSD
