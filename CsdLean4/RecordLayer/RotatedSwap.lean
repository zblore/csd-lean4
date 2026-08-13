/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.SwapClosure
public import CsdLean4.RecordLayer.RotatedContext

/-!
# SigmaLayer/RotatedSwap: the first measurement in any basis — the unitary-covariance law

**Category:** 7-SigmaLayer (dynamical measurement — the covariance extension).

## What this closes

`RotatedContext.lean` built the rotated context field and extended the sequential layer's
*follow-up* reads to arbitrary bases; the **first** measurement stayed hardwired to the
computational basis (selector `basinIndex (momentContext N)`, bank calibrated on the
computational vertices). That asymmetry — the reason `BB84Sequential` had to run the *dual*
round — ends here:

* ★ `sector_born_ctx` / `prep_outcome_pos_ctx` / `readyBankPrep_selReadyBank` — the
  swap-arena Born and conditioning-positivity lemmas, **generic in the context field and the
  bank calibration**. The `momentContext` instances in `SwapClosure.lean` predate these and
  stand; the generic forms subsume them.
* ★ `rotated_swap_luders_born` — the Lüders update for a **first measurement in any
  orthonormal basis** `bON`: selector `basinIndex (basisContext bON)`, bank calibrated on the
  rotated vertices `[bONᵢ]`; conditioned on outcome `i`, follow-up statistics for any context
  are the collapsed state's rates `c'.rate [bONᵢ]`. Pure instantiation: `swap_luders_marginal`
  was always selector- and calibration-generic — the missing pieces were only the rotated
  Born accounting.
* ★★ `measurement_covariance` — **the unitary-covariance law, in closure form**: for *every*
  orthonormal basis and every state, the full six-fact measurement closure
  (`RotatedSwapClosure`: ready ⇒ no record, record created, exclusivity, persistence,
  dynamical Born `‖⟨bONᵢ, ψ⟩‖²`, Lüders to `[bONᵢ]`) holds on the swap arena. The apparatus
  basis is a *parameter of the context field*, not a preferred structure of `Σ`.

## What this retires

The `BB84Sequential` dual-round caveat (the primal round Alice-Z/Eve-X is now directly
formalisable — see the corollary there), and the "arbitrary bases by unitary covariance" item
of the extension list. Remaining extension items (mixed preparations in the dynamical model,
POVM/instrument dynamics) stay recorded in `specs/BACKLOG.md`.

## References

`SigmaLayer/SwapClosure.lean` (`readyPrep`, `selReadyBank` machinery, the `momentContext`
instance); `SigmaLayer/SwapLuders.lean` (`swap_luders_marginal` — the generic engine);
`SigmaLayer/RotatedContext.lean` (`basisContext`, `basisContext_rate_mk`);
`specs/BACKLOG.md`.
-/

@[expose] public section

open MeasureTheory Set

namespace CSD.RecordLayer

variable {N : ℕ} [NeZero N]

/-! ### The rotated vertices and bank -/

/-- The `i`-th rotated vertex: the basis ray `[bONᵢ]`. -/
noncomputable def basisPoint (bON : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (i : Fin N) : LF4.CPN N :=
  Projectivization.mk ℂ (bON i) (bON.orthonormal.ne_zero i)

/-- The rotated calibrated bank: slot `k` prepared at `[bONₖ]`. -/
noncomputable def rotatedBank (bON : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    Measure (Fin N → LF4.KSigma N) :=
  Measure.pi fun k => epistemicMeasure (basisPoint bON k)

instance (bON : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    IsProbabilityMeasure (rotatedBank bON) := by
  unfold rotatedBank
  infer_instance

/-! ### The context-generic swap-arena accounting -/

/-- The ready preparation weights the selector-and-ready-and-bank set with the context's rate —
for **any** context field and **any** probability bank. Generalises `swapPrep_selReadyBank`. -/
lemma readyBankPrep_selReadyBank (c : ContextField N)
    (ν : Fin N → Measure (LF4.KSigma N)) [∀ k, IsProbabilityMeasure (ν k)]
    (p : LF4.CPN N) (i : Fin N) :
    ((readyPrep p).prod (Measure.pi ν)) (selReadyBank (basinIndex c) i)
      = ENNReal.ofReal (c.rate p i) := by
  have h1 : selReadyBank (basinIndex c) i
      = (({x : LF4.KSigma N | basinIndex c x = i} ×ˢ readyArc N)
          ×ˢ (univ : Set (Fin N → LF4.KSigma N))) := by
    ext x
    simp [selReadyBank, Set.mem_prod]
  rw [readyPrep, h1, Measure.prod_prod, Measure.prod_prod]
  have hset : {x : LF4.KSigma N | basinIndex c x = i} = basinIndex c ⁻¹' {i} := rfl
  rw [hset, measure_basinIndex_fibre, globalBasin_prob, readyMeasure_readyArc,
    measure_univ, mul_one, mul_one]

lemma readyBankPrep_cover (c : ContextField N)
    (ν : Fin N → Measure (LF4.KSigma N)) [∀ k, IsProbabilityMeasure (ν k)] (p : LF4.CPN N) :
    ∑ i, ((readyPrep p).prod (Measure.pi ν)) (selReadyBank (basinIndex c) i) = 1 := by
  simp_rw [readyBankPrep_selReadyBank]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => c.nonneg p i), c.sum_one p,
    ENNReal.ofReal_one]

/-- **★ The context-generic dynamical Born**: the outcome sector's measure is the context's
rate at the preparation, for any context field and bank. -/
theorem sector_born_ctx (c : ContextField N)
    (ν : Fin N → Measure (LF4.KSigma N)) [∀ k, IsProbabilityMeasure (ν k)]
    (p : LF4.CPN N) (i : Fin N) :
    ((readyPrep p).prod (Measure.pi ν))
      ((swapProtocol (basinIndex c) (measurable_basinIndex c)).outcomeSector i)
      = ENNReal.ofReal (c.rate p i) := by
  rw [(swapProtocol (basinIndex c)
      (measurable_basinIndex c)).measure_outcomeSector_eq_of_correlates
    (measurableSet_selReadyBank c) (selReadyBank_pairwiseDisjoint c)
    (readyBankPrep_cover c ν p)
    (swap_correlates (basinIndex c) (measurable_basinIndex c)) i]
  exact readyBankPrep_selReadyBank c ν p i

/-- **The context-generic conditioning positivity**: the outcome sector has nonzero measure
whenever the context's rate does. Generalises `prep_outcome_pos`. -/
theorem prep_outcome_pos_ctx (c : ContextField N) (p : LF4.CPN N) (i : Fin N)
    (hpos : c.rate p i ≠ 0) :
    readyPrep p
      ((shearProtocol (basinIndex c) (measurable_basinIndex c)).outcomeSector i) ≠ 0 := by
  classical
  have hsub : selReady (basinIndex c) i
      ⊆ (shearProtocol (basinIndex c) (measurable_basinIndex c)).outcomeSector i :=
    shear_correlates (basinIndex c) (measurable_basinIndex c) i
  have hprod : selReady (basinIndex c) i
      = {x : LF4.KSigma N | basinIndex c x = i} ×ˢ readyArc N := by
    ext x
    simp [selReady, Set.mem_prod]
  have hbase : epistemicMeasure p {x : LF4.KSigma N | basinIndex c x = i} ≠ 0 := by
    have hset : {x : LF4.KSigma N | basinIndex c x = i} = basinIndex c ⁻¹' {i} := rfl
    rw [hset, measure_basinIndex_fibre, globalBasin_prob]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact lt_of_le_of_ne (c.nonneg p i) (Ne.symm hpos)
  have hready : readyMeasure N (readyArc N) ≠ 0 := by
    rw [readyMeasure_readyArc]
    exact one_ne_zero
  intro h0
  have hle : readyPrep p (selReady (basinIndex c) i)
      ≤ readyPrep p
        ((shearProtocol (basinIndex c) (measurable_basinIndex c)).outcomeSector i) :=
    measure_mono hsub
  rw [h0, le_zero_iff, hprod, readyPrep, Measure.prod_prod] at hle
  exact absurd hle (mul_ne_zero hbase hready)

/-! ### ★ Lüders for a first measurement in any basis -/

/-- **★ The rotated Lüders update.** First measurement in the basis `bON` (selector = the
rotated context's basins, bank calibrated on the rotated vertices), conditioned on outcome
`i`: the follow-up outcome-`j` probability for **any** context field `c'` is the collapsed
state's rate `c'.rate [bONᵢ] j`. -/
theorem rotated_swap_luders_born (bON : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    {ψ : EuclideanSpace ℂ (Fin N)} (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) (i : Fin N)
    (hpos : ‖(inner ℂ (bON i) ψ : ℂ)‖ ^ 2 ≠ 0) (c' : ContextField N) (j : Fin N) :
    ((swapProtocol (basinIndex (basisContext bON))
        (measurable_basinIndex (basisContext bON))).postMeasure
      ((readyPrep (Projectivization.mk ℂ ψ hψ0)).prod (rotatedBank bON)) i)
      ((fun y : SwapArena (LF4.KSigma N) N => y.1.1) ⁻¹' globalBasin c' j)
      = ENNReal.ofReal (c'.rate (basisPoint bON i) j) := by
  have hrate : (basisContext bON).rate (Projectivization.mk ℂ ψ hψ0) i ≠ 0 := by
    rw [basisContext_rate_mk bON ψ hψ0 hψ i]
    exact hpos
  have hmarg := swap_luders_marginal (basinIndex (basisContext bON))
    (measurable_basinIndex (basisContext bON)) (readyPrep (Projectivization.mk ℂ ψ hψ0))
    (fun k => epistemicMeasure (basisPoint bON k)) i
    (prep_outcome_pos_ctx (basisContext bON) (Projectivization.mk ℂ ψ hψ0) i hrate)
  have hmeas_proj : Measurable (fun y : SwapArena (LF4.KSigma N) N => y.1.1) :=
    measurable_fst.comp measurable_fst
  rw [← Measure.map_apply hmeas_proj (measurableSet_globalBasin c' j)]
  rw [show (rotatedBank bON) = Measure.pi (fun k => epistemicMeasure (basisPoint bON k))
    from rfl, hmarg]
  exact globalBasin_prob c' j (basisPoint bON i)

/-! ### ★★ The covariance law, in closure form -/

/-- **The rotated measurement closure**: the six dynamical facts for a first measurement in
the orthonormal basis `bON`. -/
structure RotatedSwapClosure (bON : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ψ : EuclideanSpace ℂ (Fin N)) : Prop where
  /-- Ready ⇒ no record. -/
  ready_no_record : ∀ x : SwapArena (LF4.KSigma N) N, x.1.2 ∈ readyArc N →
    (swapProtocol (basinIndex (basisContext bON))
      (measurable_basinIndex (basisContext bON))).readout x = none
  /-- A record is created, and it is the rotated-basin outcome the selector fixed. -/
  record_created : ∀ (i : Fin N) (x : SwapArena (LF4.KSigma N) N),
    x ∈ selReadyBank (basinIndex (basisContext bON)) i →
    (swapProtocol (basinIndex (basisContext bON))
      (measurable_basinIndex (basisContext bON))).readout
        ((swapProtocol (basinIndex (basisContext bON))
          (measurable_basinIndex (basisContext bON))).evolve 0 1 x) = some i
  /-- Distinct outcomes are exclusive. -/
  outcomes_exclusive : Pairwise (Function.onFun Disjoint
    (swapProtocol (basinIndex (basisContext bON))
      (measurable_basinIndex (basisContext bON))).outcomeSector)
  /-- The record persists across the operational window. -/
  record_persists : ∀ (i : Fin N) (x : SwapArena (LF4.KSigma N) N)
    (t : CSD.SigmaLayer.OnticTime),
    x ∈ (swapProtocol (basinIndex (basisContext bON))
      (measurable_basinIndex (basisContext bON))).outcomeSector i →
    1 ≤ t → t ≤ 1 + 1 →
    (swapProtocol (basinIndex (basisContext bON))
      (measurable_basinIndex (basisContext bON))).readout
        ((swapProtocol (basinIndex (basisContext bON))
          (measurable_basinIndex (basisContext bON))).evolve 0 t x) = some i
  /-- **The dynamical Born in the rotated basis**: the outcome sector's measure is
  `‖⟨bONᵢ, ψ⟩‖²`. -/
  sector_born : ∀ (hψ0 : ψ ≠ 0), ‖ψ‖ = 1 → ∀ i : Fin N,
    ((readyPrep (Projectivization.mk ℂ ψ hψ0)).prod (rotatedBank bON))
      ((swapProtocol (basinIndex (basisContext bON))
        (measurable_basinIndex (basisContext bON))).outcomeSector i)
      = ENNReal.ofReal (‖(inner ℂ (bON i) ψ : ℂ)‖ ^ 2)
  /-- **The rotated Lüders update**, conditioning licensed by the rotated Born weight. -/
  luders_followup : ∀ (hψ0 : ψ ≠ 0), ‖ψ‖ = 1 → ∀ i : Fin N,
    ‖(inner ℂ (bON i) ψ : ℂ)‖ ^ 2 ≠ 0 →
    ∀ (c' : ContextField N) (j : Fin N),
    ((swapProtocol (basinIndex (basisContext bON))
        (measurable_basinIndex (basisContext bON))).postMeasure
      ((readyPrep (Projectivization.mk ℂ ψ hψ0)).prod (rotatedBank bON)) i)
      ((fun y : SwapArena (LF4.KSigma N) N => y.1.1) ⁻¹' globalBasin c' j)
      = ENNReal.ofReal (c'.rate (basisPoint bON i) j)

/-- **★★ The unitary-covariance law**: the measurement closure holds for **every** orthonormal
basis and every state — the apparatus basis is a parameter of the context field, not a
preferred structure of `Σ`. -/
theorem measurement_covariance (bON : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (ψ : EuclideanSpace ℂ (Fin N)) : RotatedSwapClosure bON ψ where
  ready_no_record _ hx :=
    (swapProtocol _ _).readout_ready_eq_none hx
  record_created i _ hx :=
    (swapProtocol _ _).readout_evolve_outcomeSector
      (swap_correlates (basinIndex (basisContext bON))
        (measurable_basinIndex (basisContext bON)) i hx)
  outcomes_exclusive := (swapProtocol _ _).outcomeSector_pairwiseDisjoint
  record_persists _ _ _ hx ht₁ ht₂ :=
    (swapProtocol _ _).readout_persists_on_interval
      (swap_pointerInvariant _ _) hx ht₁ ht₂
  sector_born hψ0 hψ i := by
    rw [show (rotatedBank bON)
      = Measure.pi (fun k => epistemicMeasure (basisPoint bON k)) from rfl,
      sector_born_ctx (basisContext bON)
        (fun k => epistemicMeasure (basisPoint bON k))
        (Projectivization.mk ℂ ψ hψ0) i,
      basisContext_rate_mk bON ψ hψ0 hψ i]
  luders_followup hψ0 hψ i hpos c' j :=
    rotated_swap_luders_born bON hψ0 hψ i hpos c' j

end CSD.RecordLayer
