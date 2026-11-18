/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedTriFibre
public import CsdLean4.RecordLayer.UnifiedRayDrift

/-!
# The radar counts from turned rays

**Category:** 7-SigmaLayer. BACKLOG #438, second brick (Task 2 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream R; obligation
UO-25, item (2)).

`RecordLayer/UnifiedRayDrift.lean` shows that one history survives a small turn of the
carrier's ray. `penta_radar_lorentz_near` (`RecordLayer/UnifiedTriFibre.lean`) gives the five
counts and the Lorentz statement from any ray whose five displacements have the histories,
for pointer angles within a radius of the start. Here the two are joined.

* ★★★ `penta_radar_lorentz_near_ray` — let the five displacements along the free orbit from
  a ray `P` have the histories of #402 with a slack `s` below every margin. Then from `P`
  turned by any unitary `W` with `‖W − 1‖ ≤ r_W`, `4 γ S r_W T ≤ s/2`, and from every five
  pointer angles within `ρ` of the start (`ρ ≤ s/8`, `ρ C T ≤ s/8`, `ρ C (K₁ + K₂) ≤ ϵ`), the
  five pointers have counts and the counts satisfy the Lorentz statement, with the errors
  of #402 at speeds enlarged by `4 γ S r_W`, plus `ϵ`.

## Honest scope

⚠️ **Conditional on the histories at `P`.** For the family of `radar_family_lorentz` the five
histories and their slack are inside that theorem's proof and are not exposed as a
statement. Until they are, this theorem is not instantiated for the family.

⚠️ **No measure is computed and no preparation is built.** That the rays `P` turned by such
`W` have positive Fubini–Study measure is owed, and so is the `HistoryPreparation`.

⚠️ **The radius in the rays is of order `s / (γ S T)`**: it shrinks as the run gets longer.

⚠️ **The run is the five-pointer flow for any carrier and observables.** For three carriers a
turned ray is in general not a product of their rays; nothing here needs it to be.

References: `specs/BACKLOG.md` #438, ~~#436~~, ~~#430~~;
`specs/unified-record-spacetime-plan.md` (UO-25, UD-199, UD-205, UD-213, UD-214);
`RecordLayer/UnifiedRayDrift.lean` (`IsGatedHistory.of_ray`, `IsAwayHistory.of_ray`,
`abs_freeShift_ray_sub_le`); `RecordLayer/UnifiedTriFibre.lean` (`penta_radar_lorentz_near`,
`tri_radar_lorentz_near`, `NearStart`); `RecordLayer/UnifiedFibreRadar.lean`
(`penta_radar_lorentz_fibre`); `RecordLayer/UnifiedRadarRun.lean` (`radar_family_lorentz`);
`specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology Kronecker

namespace CSD.RecordLayer

variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
  {H G₁ G₂ G₃ G₄ G₅ : Matrix ν ν ℂ}

/-- ★★★ **M6 from the top from turned rays and nearby pointer angles.** As
`penta_radar_lorentz_near`, with the ray turned: let the five displacements along the free
orbit from `P` have the histories of #402 with a slack `s` below every margin, the
observables have norm at most `S`, the strengths size at most `γ` and the windows end by `T`.
Then for every unitary `W` with `‖W − 1‖ ≤ r_W`, `4 γ S r_W T ≤ s/2`, and every `ρ > 0` with
`ρ ≤ s/8`, `ρ C T ≤ s/8`, `ρ C (K₁ + K₂) ≤ ϵ`: from the ray `P` turned by `W` and every five
pointer angles within `ρ` of `(1/12, 0)` the five pointers have counts, and the counts
satisfy the Lorentz statement with the errors of #402 at the speeds enlarged by `4 γ S r_W`,
plus `ϵ`. -/
theorem penta_radar_lorentz_near_ray (hH : H.IsHermitian) (hG₁ : G₁.IsHermitian)
    (hG₂ : G₂.IsHermitian) (hG₃ : G₃.IsHermitian) (hG₄ : G₄.IsHermitian)
    (hG₅ : G₅.IsHermitian) (g₁ g₂ g₃ g₄ g₅ : ℝ) (P : GenArena ν)
    {v R₀ RB κ TE TR TRet TM tE tR tRet tMB tMA τE τR τRet τMB τMA : ℝ}
    {δe ve tbe tce c vr η₀ η t4 t5 δμ vμ tbμ tcμ δρ vρ tbρ tcρ δm vm tbm tcm : ℝ}
    {ce cr cμ cρ cm : ℝ}
    (hv0 : 0 ≤ v) (hv : v < 1) (hR₀ : 0 < R₀)
    (hκ : |RB - Real.sqrt (1 - v ^ 2) * R₀| ≤ κ * R₀)
    (hE : TR - TE = v * (TM - TE)) (hRet : TRet - TR = v * (TM - TRet))
    (hτE : |tE - TE| ≤ τE) (hτRet : |tRet - TRet| ≤ τRet) (hτMB : |tMB - TM| ≤ τMB)
    (hτR : |tR - TR| ≤ τR) (hτMA : |tMA - TM| ≤ τMA)
    (He : IsGatedHistory (freeShift hH G₁ (-g₁) P) RB δe ve tE tbe tce)
    (Hr : IsAwayHistory (freeShift hH G₂ (-g₂) P) RB c vr η₀ η tE tbe tRet t4 t5)
    (Hμ : IsGatedHistory (freeShift hH G₃ (-g₃) P) RB δμ vμ tMB tbμ tcμ)
    (Hρ : IsGatedHistory (freeShift hH G₄ (-g₄) P) R₀ δρ vρ tR tbρ tcρ)
    (Hm : IsGatedHistory (freeShift hH G₅ (-g₅) P) R₀ δm vm tMA tbm tcm)
    (hce : ∀ s t, tbe ≤ s → s ≤ t → t ≤ tce →
      |freeShift hH G₁ (-g₁) P t - freeShift hH G₁ (-g₁) P s| ≤ ce)
    (hcr : ∀ s t, t4 ≤ s → s ≤ t → t ≤ t5 →
      |freeShift hH G₂ (-g₂) P t - freeShift hH G₂ (-g₂) P s| ≤ cr)
    (hcμ : ∀ s t, tbμ ≤ s → s ≤ t → t ≤ tcμ →
      |freeShift hH G₃ (-g₃) P t - freeShift hH G₃ (-g₃) P s| ≤ cμ)
    (hcρ : ∀ s t, tbρ ≤ s → s ≤ t → t ≤ tcρ →
      |freeShift hH G₄ (-g₄) P t - freeShift hH G₄ (-g₄) P s| ≤ cρ)
    (hcm : ∀ s t, tbm ≤ s → s ≤ t → t ≤ tcm →
      |freeShift hH G₅ (-g₅) P t - freeShift hH G₅ (-g₅) P s| ≤ cm)
    {ϵ S γ T s ρ : ℝ}
    (hS1 : ‖G₁‖ ≤ S) (hS2 : ‖G₂‖ ≤ S) (hS3 : ‖G₃‖ ≤ S) (hS4 : ‖G₄‖ ≤ S) (hS5 : ‖G₅‖ ≤ S)
    (hγ1 : |g₁| ≤ γ) (hγ2 : |g₂| ≤ γ) (hγ3 : |g₃| ≤ γ) (hγ4 : |g₄| ≤ γ) (hγ5 : |g₅| ≤ γ)
    (hT1 : tce ≤ T) (hT2 : t5 ≤ T) (hT3 : tcμ ≤ T) (hT4 : tcρ ≤ T) (hT5 : tcm ≤ T)
    (sp : 0 < s) (q1 : s ≤ 1 / 12 - δe) (q2 : s ≤ 1 / 12 - η₀) (q3 : s ≤ 1 / 12 - η)
    (q4 : s ≤ 1 / 12 - c - (-1 / 6 + η)) (q5 : s ≤ 1 / 6 - η - (1 / 12 - c))
    (q6 : s ≤ 1 / 12 - δμ) (q7 : s ≤ 1 / 12 - δρ) (q8 : s ≤ 1 / 12 - δm)
    (q9 : s ≤ 1 / 6 - ce) (q10 : s ≤ 1 / 6 - cr) (q11 : s ≤ 1 / 6 - cμ)
    (q12 : s ≤ 1 / 6 - cρ) (q13 : s ≤ 1 / 6 - cm) (W : Matrix.unitaryGroup ν ℂ) {rW : ℝ}
    (hW : ‖W.val - 1‖ ≤ rW) (hrW : 4 * γ * S * rW * T ≤ s / 2)
    (hρ0 : 0 < ρ) (hρs : ρ ≤ s / 8)
    (hρA' : ρ * ((20 * γ ^ 2 * S ^ 2 * T + 14 * γ * S) * T) ≤ s / 8)
    (hρB' : ρ * ((20 * γ ^ 2 * S ^ 2 * T + 14 * γ * S) * ((6 * Real.pi * (((tbe - tE) / R₀ + ((tbe
        - tE) + ((tbe - tE) + (t4 - tRet))) / R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2)))
      + (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) / R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))))) ≤ ϵ) :
    ∀ (N : ℕ) (e : ν ≃ Fin (N + 1)) (θ ψ χ ξ ζ : KTorus),
      NearStart ρ θ → NearStart ρ ψ → NearStart ρ χ → NearStart ρ ξ → NearStart ρ ζ →
      ∀ se, tbe ≤ se → se ≤ tce → ∀ sr, t4 ≤ sr → sr ≤ t5 → ∀ sμ, tbμ ≤ sμ → sμ ≤ tcμ →
      ∀ sρ, tbρ ≤ sρ → sρ ≤ tcρ → ∀ sm, tbm ≤ sm → sm ≤ tcm →
      ∃ Ne Nr Nμ Nρ Nm : ℕ,
        IsTickCount {x : PentaSigma N | x.1.1.1.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.1.1.1.2 ∈ displayArc}
            (fun t => fiveCoupledFlow (Matrix.reindex e e H) (Matrix.reindex e e G₁)
              (Matrix.reindex e e G₂) (Matrix.reindex e e G₃) (Matrix.reindex e e G₄)
              (Matrix.reindex e e G₅) (scaledTrainF_periodic g₁) (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅) t
              (((((idxArenaEquiv e (arenaKick W P), θ), ψ), χ), ξ), ζ)) se Ne
        ∧ IsTickCount {x : PentaSigma N | x.1.1.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.1.1.2 ∈ displayArc}
            (fun t => fiveCoupledFlow (Matrix.reindex e e H) (Matrix.reindex e e G₁)
              (Matrix.reindex e e G₂) (Matrix.reindex e e G₃) (Matrix.reindex e e G₄)
              (Matrix.reindex e e G₅) (scaledTrainF_periodic g₁) (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅) t
              (((((idxArenaEquiv e (arenaKick W P), θ), ψ), χ), ξ), ζ)) sr Nr
        ∧ IsTickCount {x : PentaSigma N | x.1.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.1.2 ∈ displayArc}
            (fun t => fiveCoupledFlow (Matrix.reindex e e H) (Matrix.reindex e e G₁)
              (Matrix.reindex e e G₂) (Matrix.reindex e e G₃) (Matrix.reindex e e G₄)
              (Matrix.reindex e e G₅) (scaledTrainF_periodic g₁) (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅) t
              (((((idxArenaEquiv e (arenaKick W P), θ), ψ), χ), ξ), ζ)) sμ Nμ
        ∧ IsTickCount {x : PentaSigma N | x.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.2 ∈ displayArc}
            (fun t => fiveCoupledFlow (Matrix.reindex e e H) (Matrix.reindex e e G₁)
              (Matrix.reindex e e G₂) (Matrix.reindex e e G₃) (Matrix.reindex e e G₄)
              (Matrix.reindex e e G₅) (scaledTrainF_periodic g₁) (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅) t
              (((((idxArenaEquiv e (arenaKick W P), θ), ψ), χ), ξ), ζ)) sρ Nρ
        ∧ IsTickCount {x : PentaSigma N | x.2 ∈ readyArc 2}
            {x : PentaSigma N | x.2 ∈ displayArc}
            (fun t => fiveCoupledFlow (Matrix.reindex e e H) (Matrix.reindex e e G₁)
              (Matrix.reindex e e G₂) (Matrix.reindex e e G₃) (Matrix.reindex e e G₄)
              (Matrix.reindex e e G₅) (scaledTrainF_periodic g₁) (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅) t
              (((((idxArenaEquiv e (arenaKick W P), θ), ψ), χ), ξ), ζ)) sm Nm
        ∧ |(lorentzBoost 1 (-v)
                ((Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀, 0)).1
              - (((Ne : ℝ) * (2 * Real.pi) / R₀
                    + ((Ne : ℝ) * (2 * Real.pi) + (Nr : ℝ) * (2 * Real.pi)) / R₀) / 2
                  - (Nμ : ℝ) * (2 * Real.pi) / R₀)|
            ≤ ((gatedErr (ve + 4 * γ * S * rW) tE tbe / R₀ + κ * tE + τE)
                + ((gatedErr (ve + 4 * γ * S * rW) tE tbe + awayErr (vr
                    + 4 * γ * S * rW) tE tbe tRet t4 + RB * (tbe - tE)) / R₀
                    + κ * tRet + τRet)) / 2
              + (gatedErr (vμ + 4 * γ * S * rW) tMB tbμ / R₀ + κ * tMB + τMB)
              + ((gatedErr (vρ + 4 * γ * S * rW) tR tbρ / R₀ + τR) + (gatedErr (vm
                  + 4 * γ * S * rW) tMA tbm / R₀ + τMA))
                / Real.sqrt (1 - v ^ 2) + ϵ
        ∧ |(lorentzBoost 1 (-v)
                ((Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀, 0)).2
              - (-((((Ne : ℝ) * (2 * Real.pi) + (Nr : ℝ) * (2 * Real.pi)) / R₀
                    - (Ne : ℝ) * (2 * Real.pi) / R₀) / 2))|
            ≤ ((gatedErr (ve + 4 * γ * S * rW) tE tbe / R₀ + κ * tE + τE)
                + ((gatedErr (ve + 4 * γ * S * rW) tE tbe + awayErr (vr
                    + 4 * γ * S * rW) tE tbe tRet t4 + RB * (tbe - tE)) / R₀
                    + κ * tRet + τRet)) / 2
              + v * ((gatedErr (vρ + 4 * γ * S * rW) tR tbρ / R₀ + τR) + (gatedErr (vm
                  + 4 * γ * S * rW) tMA tbm / R₀ + τMA))
                / Real.sqrt (1 - v ^ 2) + ϵ
        ∧ |(Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀ - (tR - tMA)|
            ≤ (gatedErr (vρ + 4 * γ * S * rW) tR tbρ + gatedErr (vm
                + 4 * γ * S * rW) tMA tbm) / R₀ + ϵ := by
  have hγ0 : 0 ≤ γ := (abs_nonneg _).trans hγ1
  have hS0 : 0 ≤ S := (norm_nonneg _).trans hS1
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = 4 * γ * S * rW := ⟨_, rfl⟩
  have hlam0 : 0 ≤ lam := by
    have hr0 : 0 ≤ rW := (norm_nonneg _).trans hW
    rw [hlam]
    positivity
  have rate : ∀ {g : ℝ} {G : Matrix ν ν ℂ}, |g| ≤ γ → ‖G‖ ≤ S →
      4 * |(-g)| * ‖G‖ * ‖W.val - 1‖ ≤ lam := by
    intro g G hg hG
    rw [hlam, abs_neg]
    have h1 : |g| * ‖G‖ ≤ γ * S := mul_le_mul hg hG (norm_nonneg _) hγ0
    have h2 : |g| * ‖G‖ * ‖W.val - 1‖ ≤ γ * S * rW :=
      mul_le_mul h1 hW (norm_nonneg _) (mul_nonneg hγ0 hS0)
    linarith only [h2]
  have hlT : lam * T ≤ s / 2 := by
    rw [hlam]
    exact hrW
  have mono : ∀ t : ℝ, t ≤ T → lam * t ≤ s / 2 := fun t ht =>
    (mul_le_mul_of_nonneg_left ht hlam0).trans hlT
  have mono2 : ∀ t t' : ℝ, 0 ≤ t' → t ≤ T → lam * (t - t') ≤ s / 2 := fun t t' ht' ht =>
    (mul_le_mul_of_nonneg_left (by linarith only [ht', ht]) hlam0).trans hlT
  have htbe0 : 0 ≤ tbe := He.ta_nonneg.trans He.ta_le
  have ht40 : 0 ≤ t4 := (htbe0.trans Hr.tb_le).trans Hr.t3_le
  have htbμ0 : 0 ≤ tbμ := Hμ.ta_nonneg.trans Hμ.ta_le
  have htbρ0 : 0 ≤ tbρ := Hρ.ta_nonneg.trans Hρ.ta_le
  have htbm0 : 0 ≤ tbm := Hm.ta_nonneg.trans Hm.ta_le
  have closed : ∀ {g : ℝ} {G : Matrix ν ν ℂ} {tb tc c₀ : ℝ}, |g| ≤ γ → ‖G‖ ≤ S →
      (∀ a b, tb ≤ a → a ≤ b → b ≤ tc →
        |freeShift hH G (-g) P b - freeShift hH G (-g) P a| ≤ c₀) →
      ∀ a b, tb ≤ a → a ≤ b → b ≤ tc →
        |freeShift hH G (-g) (arenaKick W P) b - freeShift hH G (-g) (arenaKick W P) a|
          ≤ c₀ + lam * (tc - tb) := by
    intro g G tb tc c₀ hg hG hcl a b ha hab hb
    refine (abs_freeShift_ray_sub_le hH G (-g) W P hab).trans ?_
    have h1 := hcl a b ha hab hb
    have h2 := mul_le_mul_of_nonneg_right (rate hg hG) (sub_nonneg.2 hab)
    have h3 : lam * (b - a) ≤ lam * (tc - tb) :=
      mul_le_mul_of_nonneg_left (by linarith only [ha, hb]) hlam0
    linarith only [h1, h2, h3]
  have He' := IsGatedHistory.of_ray hH W He hce (rate hγ1 hS1)
    (by linarith only [mono tce hT1, q1, sp])
    (by linarith only [mono2 tce tbe htbe0 hT1, q9, sp])
  have Hr' := IsAwayHistory.of_ray hH W Hr hcr (rate hγ2 hS2)
    (by linarith only [mono t5 hT2, q2, sp]) (by linarith only [mono t5 hT2, q3, sp])
    (Or.inl ⟨by linarith only [mono t5 hT2, q4, sp], by linarith only [mono t5 hT2, q5, sp]⟩)
    (by linarith only [mono2 t5 t4 ht40 hT2, q10, sp])
  have Hμ' := IsGatedHistory.of_ray hH W Hμ hcμ (rate hγ3 hS3)
    (by linarith only [mono tcμ hT3, q6, sp])
    (by linarith only [mono2 tcμ tbμ htbμ0 hT3, q11, sp])
  have Hρ' := IsGatedHistory.of_ray hH W Hρ hcρ (rate hγ4 hS4)
    (by linarith only [mono tcρ hT4, q7, sp])
    (by linarith only [mono2 tcρ tbρ htbρ0 hT4, q12, sp])
  have Hm' := IsGatedHistory.of_ray hH W Hm hcm (rate hγ5 hS5)
    (by linarith only [mono tcm hT5, q8, sp])
    (by linarith only [mono2 tcm tbm htbm0 hT5, q13, sp])
  have key := penta_radar_lorentz_near hH hG₁ hG₂ hG₃ hG₄ hG₅ g₁ g₂ g₃ g₄ g₅ (arenaKick W P)
    hv0 hv hR₀ hκ hE hRet hτE hτRet hτMB hτR hτMA He' Hr' Hμ' Hρ' Hm'
    (closed hγ1 hS1 hce) (closed hγ2 hS2 hcr) (closed hγ3 hS3 hcμ) (closed hγ4 hS4 hcρ)
    (closed hγ5 hS5 hcm) hS1 hS2 hS3 hS4 hS5 hγ1 hγ2 hγ3 hγ4 hγ5 hT1 hT2 hT3 hT4 hT5
    (s := s / 2) (ϵ := ϵ) (ρ := ρ) (by linarith only [sp])
    (by linarith only [mono tce hT1, q1]) (by linarith only [mono t5 hT2, q2])
    (by linarith only [mono t5 hT2, q3]) (by linarith only [mono t5 hT2, q4])
    (by linarith only [mono t5 hT2, q5]) (by linarith only [mono tcμ hT3, q6])
    (by linarith only [mono tcρ hT4, q7]) (by linarith only [mono tcm hT5, q8])
    (by linarith only [mono2 tce tbe htbe0 hT1, q9])
    (by linarith only [mono2 t5 t4 ht40 hT2, q10])
    (by linarith only [mono2 tcμ tbμ htbμ0 hT3, q11])
    (by linarith only [mono2 tcρ tbρ htbρ0 hT4, q12])
    (by linarith only [mono2 tcm tbm htbm0 hT5, q13]) hρ0 (by linarith only [hρs])
    (by linarith only [hρA']) hρB'
  subst hlam
  exact key

end CSD.RecordLayer

end
