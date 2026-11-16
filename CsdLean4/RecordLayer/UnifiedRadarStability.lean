/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedRadarSkeleton

/-!
# Histories are stable under a small change of the displacement

**Category:** 7-SigmaLayer (the record layer). BACKLOG #427 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Task 9 of the research delivery
plan of 2026-11-16 (an open set of pointer angles), first part. No new assumption; real
analysis only.

Off the fibres where the profiles vanish the carrier is driven by the pointers, and each
pointer's displacement changes. This module proves that the two kinds of history of #402
survive a change of the displacement that starts within `η₀` and then drifts at a rate at
most `λ`: the errors grow by `η₀ + λ t`, the speeds by `λ`.

* `abs_sub_le_of_drift` — a displacement that starts within `η₀` and drifts at rate `λ` stays
  within `η₀ + λ t`;
* ★★ `IsGatedHistory.of_drift` — a gated history, perturbed;
* ★★ `IsAwayHistory.of_drift` — an away history, perturbed.

## Exact scope

* **The closing bounds need slack that the structures do not keep.** A history records that
  the displacement moves by at most `1/6` while its gate is closed. The perturbed
  displacement moves by that plus the drift, so the theorems take the true bound `c₀` of
  the unperturbed displacement as a hypothesis, with `c₀ + λ (t_c − t_b) ≤ 1/6`.
* **The band of the away history is a hypothesis again**, for the enlarged error.
* **Nothing about the flow.** That the pointers' displacements off the zero fibres are such
  perturbations is not proved here.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-163, UD-164, UD-196, UD-197); `RecordLayer/UnifiedRadarSkeleton.lean`
(#402: `IsGatedHistory`, `IsAwayHistory`); `RecordLayer/UnifiedRadarRun.lean` (#426:
`radar_family_lorentz`, the statement these lemmas are to extend).
-/

@[expose] public section

noncomputable section

namespace CSD.RecordLayer

/-- A displacement that starts within `η₀` of another and drifts from it at a rate at most
`lam` stays within `η₀ + lam · t` of it. -/
theorem abs_sub_le_of_drift {D D' : ℝ → ℝ} {lam η₀ T : ℝ}
    (hlip : ∀ s t, 0 ≤ s → s ≤ t → t ≤ T → |(D' t - D t) - (D' s - D s)| ≤ lam * (t - s))
    (h0 : |D' 0 - D 0| ≤ η₀) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ T) :
    |D' t - D t| ≤ η₀ + lam * t := by
  have h1 := hlip 0 t le_rfl ht0 ht
  rw [sub_zero] at h1
  rw [abs_le] at h0 h1 ⊢
  constructor <;> linarith only [h0.1, h0.2, h1.1, h1.2]

/-- ★★ **A gated history, perturbed.** If `D` has a gated history, moves by at most `c₀`
while its gate is closed, and `D'` starts within `η₀` of `D` and drifts from it at a rate at
most `lam` up to `t_c`: then `D'` has a gated history with error `δ + η₀ + lam · t_c` and
speed `v + lam`, provided the error stays below `1/12` and `c₀ + lam (t_c − t_b) ≤ 1/6`. -/
theorem IsGatedHistory.of_drift {D D' : ℝ → ℝ} {R δ v ta tb tc c₀ lam η₀ : ℝ}
    (h : IsGatedHistory D R δ v ta tb tc)
    (hcl : ∀ s t, tb ≤ s → s ≤ t → t ≤ tc → |D t - D s| ≤ c₀) (hlam : 0 ≤ lam)
    (hlip : ∀ s t, 0 ≤ s → s ≤ t → t ≤ tc → |(D' t - D t) - (D' s - D s)| ≤ lam * (t - s))
    (h0 : |D' 0 - D 0| ≤ η₀) (hδ : δ + η₀ + lam * tc < 1 / 12)
    (hc : c₀ + lam * (tc - tb) ≤ 1 / 6) :
    IsGatedHistory D' R (δ + η₀ + lam * tc) (v + lam) ta tb tc := by
  have hη : 0 ≤ η₀ := (abs_nonneg _).trans h0
  have htc : 0 ≤ tc := h.ta_nonneg.trans (h.ta_le.trans h.tb_le)
  refine ⟨h.rate_pos, ?_, hδ, h.ta_nonneg, h.ta_le, h.tb_le, fun t ht0 hta => ?_,
    fun s t hs hst ht => ?_, fun s t hs hst ht => ?_⟩
  · have := h.err_nonneg
    have := mul_nonneg hlam htc
    linarith only [h.err_nonneg, hη, this]
  · have ht : t ≤ tc := hta.trans (h.ta_le.trans h.tb_le)
    have h1 := abs_sub_le_of_drift hlip h0 ht0 ht
    have h2 := h.swing t ht0 hta
    have h3 : lam * t ≤ lam * tc := mul_le_mul_of_nonneg_left ht hlam
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2, h3]
  · have h1 := hlip s t (h.ta_nonneg.trans hs) hst (ht.trans h.tb_le)
    have h2 := h.mid s t hs hst ht
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]
  · have hs0 : 0 ≤ s := (h.ta_nonneg.trans h.ta_le).trans hs
    have h1 := hlip s t hs0 hst ht
    have h2 := hcl s t hs hst ht
    have h3 : lam * (t - s) ≤ lam * (tc - tb) :=
      mul_le_mul_of_nonneg_left (by linarith only [hs, ht]) hlam
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2, h3, hc]

/-- ★★ **An away history, perturbed.** If `D` has an away history, moves by at most `c₁`
while its gate is closed again on `[t₄, t₅]`, and `D'` starts within `ρ₀` of `D` and drifts
from it at a rate at most `lam` up to `t₅`: then `D'` has an away history with the same
offset, start error `η₀ + ρ₀ + lam · t₅`, error `η + ρ₀ + lam · t₅` and speed `v + lam`,
provided both errors stay below `1/12`, the band holds for the enlarged error, and
`c₁ + lam (t₅ − t₄) ≤ 1/6`. -/
theorem IsAwayHistory.of_drift {D D' : ℝ → ℝ} {R c v η₀ η ta tb t3 t4 t5 c₁ lam ρ₀ : ℝ}
    (h : IsAwayHistory D R c v η₀ η ta tb t3 t4 t5)
    (hcl : ∀ a b, t4 ≤ a → a ≤ b → b ≤ t5 → |D b - D a| ≤ c₁) (hlam : 0 ≤ lam)
    (hlip : ∀ s t, 0 ≤ s → s ≤ t → t ≤ t5 → |(D' t - D t) - (D' s - D s)| ≤ lam * (t - s))
    (h0 : |D' 0 - D 0| ≤ ρ₀) (hη₀ : η₀ + ρ₀ + lam * t5 < 1 / 12)
    (hη : η + ρ₀ + lam * t5 < 1 / 12)
    (hband : (-1 / 6 + (η + ρ₀ + lam * t5) < 1 / 12 - c
        ∧ 1 / 12 - c ≤ 1 / 6 - (η + ρ₀ + lam * t5))
      ∨ (-1 / 2 + (η + ρ₀ + lam * t5) < 1 / 12 - c
        ∧ 1 / 12 - c < -1 / 6 - (η + ρ₀ + lam * t5)))
    (hc : c₁ + lam * (t5 - t4) ≤ 1 / 6) :
    IsAwayHistory D' R c (v + lam) (η₀ + ρ₀ + lam * t5) (η + ρ₀ + lam * t5) ta tb t3 t4
      t5 := by
  have hρ : 0 ≤ ρ₀ := (abs_nonneg _).trans h0
  have h3 : 0 ≤ t3 := (h.ta_nonneg.trans h.ta_le).trans h.tb_le
  have h4 : 0 ≤ t4 := h3.trans h.t3_le
  have h5 : 0 ≤ t5 := h4.trans h.t4_le
  have hl5 : 0 ≤ lam * t5 := mul_nonneg hlam h5
  have near : ∀ t, 0 ≤ t → t ≤ t5 → |D' t - D t| ≤ ρ₀ + lam * t5 := fun t ht0 ht =>
    (abs_sub_le_of_drift hlip h0 ht0 ht).trans
      (by linarith only [mul_le_mul_of_nonneg_left ht hlam])
  have step : ∀ a b, 0 ≤ a → a ≤ b → b ≤ t5 → ∀ B, |D b - D a| ≤ B →
      |D' b - D' a| ≤ B + lam * (b - a) := by
    intro a b ha hab hb B hB
    have h1 := hlip a b ha hab hb
    rw [abs_le] at h1 hB ⊢
    constructor <;> linarith only [h1.1, h1.2, hB.1, hB.2]
  refine ⟨h.rate_pos, h.ta_nonneg, h.ta_le, h.tb_le, h.t3_le, h.t4_le, hη₀,
    fun t ht0 hta => ?_, fun a b ha hab hb => ?_, ?_, hη, fun t htb ht3 => ?_, hband,
    fun a b ha hab hb => ?_, fun a b ha hab hb => ?_⟩
  · have ht : t ≤ t5 := hta.trans (h.ta_le.trans (h.tb_le.trans (h.t3_le.trans h.t4_le)))
    have h1 := near t ht0 ht
    have h2 := h.closed0 t ht0 hta
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]
  · have h1 := step a b (h.ta_nonneg.trans ha) hab
      (hb.trans (h.tb_le.trans (h.t3_le.trans h.t4_le))) _ (h.mid1 a b ha hab hb)
    linarith only [h1]
  · linarith only [h.err_nonneg, hρ, hl5]
  · have ht0 : 0 ≤ t := (h.ta_nonneg.trans h.ta_le).trans htb
    have h1 := near t ht0 (ht3.trans (h.t3_le.trans h.t4_le))
    have h2 := h.swing t htb ht3
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]
  · have h1 := step a b (h3.trans ha) hab (hb.trans h.t4_le) _ (h.mid2 a b ha hab hb)
    linarith only [h1]
  · have h1 := step a b (h4.trans ha) hab hb _ (hcl a b ha hab hb)
    have h2 : lam * (b - a) ≤ lam * (t5 - t4) :=
      mul_le_mul_of_nonneg_left (by linarith only [ha, hb]) hlam
    linarith only [h1, h2, hc]

end CSD.RecordLayer

end
