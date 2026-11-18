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
  turned by any unitary `W` with `‖W − 1‖ ≤ r_W`, `4 γ S r_W T ≤ s/2`,
  `4 γ S r_W (K₁ + K₂) ≤ ϵ'`, and from every five pointer angles within `ρ` of the start
  (`ρ ≤ s/8`, `ρ C T ≤ s/8`, `ρ C (K₁ + K₂) ≤ ϵ`), the five pointers have counts and the
  counts satisfy the Lorentz statement with the errors of #402 enlarged by `ϵ + ϵ'`.
* ★★★ `tri_radar_lorentz_near_ray` — the same for the composite of three carriers and the
  five gates of `triRun`, from their product ray turned by a unitary of the composite.

## Honest scope

⚠️ **Conditional on the histories at `P`.** The walled chain and the family are instantiated
in `RecordLayer/UnifiedWallRay.lean` and `RecordLayer/UnifiedRadarRay.lean`.

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
Then for every unitary `W` with `‖W − 1‖ ≤ r_W`, `4 γ S r_W T ≤ s/2`,
`4 γ S r_W (K₁ + K₂) ≤ ϵ'`, and every `ρ > 0` with `ρ ≤ s/8`, `ρ C T ≤ s/8`,
`ρ C (K₁ + K₂) ≤ ϵ`: from the ray `P` turned by `W` and every five pointer angles within `ρ`
of `(1/12, 0)` the five pointers have counts, and the counts satisfy the Lorentz statement
with the errors of #402 enlarged by `ϵ + ϵ'`. -/
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
    {ϵ ϵ' S γ T s ρ : ℝ}
    (hS1 : ‖G₁‖ ≤ S) (hS2 : ‖G₂‖ ≤ S) (hS3 : ‖G₃‖ ≤ S) (hS4 : ‖G₄‖ ≤ S) (hS5 : ‖G₅‖ ≤ S)
    (hγ1 : |g₁| ≤ γ) (hγ2 : |g₂| ≤ γ) (hγ3 : |g₃| ≤ γ) (hγ4 : |g₄| ≤ γ) (hγ5 : |g₅| ≤ γ)
    (hT1 : tce ≤ T) (hT2 : t5 ≤ T) (hT3 : tcμ ≤ T) (hT4 : tcρ ≤ T) (hT5 : tcm ≤ T)
    (sp : 0 < s) (q1 : s ≤ 1 / 12 - δe) (q2 : s ≤ 1 / 12 - η₀) (q3 : s ≤ 1 / 12 - η)
    (q4 : s ≤ 1 / 12 - c - (-1 / 6 + η)) (q5 : s ≤ 1 / 6 - η - (1 / 12 - c))
    (q6 : s ≤ 1 / 12 - δμ) (q7 : s ≤ 1 / 12 - δρ) (q8 : s ≤ 1 / 12 - δm)
    (q9 : s ≤ 1 / 6 - ce) (q10 : s ≤ 1 / 6 - cr) (q11 : s ≤ 1 / 6 - cμ)
    (q12 : s ≤ 1 / 6 - cρ) (q13 : s ≤ 1 / 6 - cm) (W : Matrix.unitaryGroup ν ℂ) {rW : ℝ}
    (hW : ‖W.val - 1‖ ≤ rW) (hrW : 4 * γ * S * rW * T ≤ s / 2)
    (hrB : 4 * γ * S * rW * ((6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE)
        + (t4 - tRet))) /
      R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2)))
      + (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
      R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2)))) ≤ ϵ')
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
            ≤ ((gatedErr ve tE tbe / R₀ + κ * tE + τE)
                + ((gatedErr ve tE tbe + awayErr vr tE tbe tRet t4 + RB * (tbe - tE)) / R₀
                    + κ * tRet + τRet)) / 2
              + (gatedErr vμ tMB tbμ / R₀ + κ * tMB + τMB)
              + ((gatedErr vρ tR tbρ / R₀ + τR) + (gatedErr vm tMA tbm / R₀ + τMA))
                / Real.sqrt (1 - v ^ 2) + ϵ + ϵ'
        ∧ |(lorentzBoost 1 (-v)
                ((Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀, 0)).2
              - (-((((Ne : ℝ) * (2 * Real.pi) + (Nr : ℝ) * (2 * Real.pi)) / R₀
                    - (Ne : ℝ) * (2 * Real.pi) / R₀) / 2))|
            ≤ ((gatedErr ve tE tbe / R₀ + κ * tE + τE)
                + ((gatedErr ve tE tbe + awayErr vr tE tbe tRet t4 + RB * (tbe - tE)) / R₀
                    + κ * tRet + τRet)) / 2
              + v * ((gatedErr vρ tR tbρ / R₀ + τR) + (gatedErr vm tMA tbm / R₀ + τMA))
                / Real.sqrt (1 - v ^ 2) + ϵ + ϵ'
        ∧ |(Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀ - (tR - tMA)|
            ≤ (gatedErr vρ tR tbρ + gatedErr vm tMA tbm) / R₀ + ϵ + ϵ' := by
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
  have hrB' : lam * ((6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
      R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2)))
      + (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
      R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2)))) ≤ ϵ' := by
    rw [hlam]
    exact hrB
  have hsq : 0 < Real.sqrt (1 - v ^ 2) := Real.sqrt_pos.2 (by nlinarith only [hv0, hv])
  have ka : 0 ≤ (tbe - tE) / R₀ := div_nonneg (sub_nonneg.2 He.ta_le) hR₀.le
  have kb : 0 ≤ ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) / R₀ :=
    div_nonneg (by linarith only [He.ta_le, Hr.t3_le]) hR₀.le
  have km : 0 ≤ (tbμ - tMB) / R₀ := div_nonneg (sub_nonneg.2 Hμ.ta_le) hR₀.le
  have kr : 0 ≤ (tbρ - tR) / R₀ := div_nonneg (sub_nonneg.2 Hρ.ta_le) hR₀.le
  have kq : 0 ≤ (tbm - tMA) / R₀ := div_nonneg (sub_nonneg.2 Hm.ta_le) hR₀.le
  have hK1 : 0 ≤ (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
      R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))) :=
    mul_nonneg (by positivity) (add_nonneg (add_nonneg (div_nonneg (add_nonneg ka kb)
      (by norm_num)) km) (div_nonneg (add_nonneg kr kq) hsq.le))
  have hK2 : 0 ≤ (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
      R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))) :=
    mul_nonneg (by positivity) (add_nonneg (div_nonneg (add_nonneg ka kb) (by norm_num))
      (div_nonneg (mul_nonneg hv0 (add_nonneg kr kq)) hsq.le))
  have hk1 : lam * (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
      R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))) ≤ ϵ' := by
    have := mul_nonneg hlam0 hK2
    have e : lam * ((6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
      R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2)))
      + (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
      R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))))
        = lam * (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
      R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2)))
          + lam * (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
      R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))) := by ring
    linarith only [this, e, hrB']
  have hk2 : lam * (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
      R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))) ≤ ϵ' := by
    have := mul_nonneg hlam0 hK1
    have e : lam * ((6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
      R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2)))
      + (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
      R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))))
        = lam * (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
      R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2)))
          + lam * (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
      R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))) := by ring
    linarith only [this, e, hrB']
  intro N e θ ψ χ ξ ζ hθ hψ hχ hξ hζ se h1 h2 sr h3 h4 sμ h5 h6 sρ h7 h8 sm h9 h10
  obtain ⟨Ne, Nr, Nμ, Nρ, Nm, c1, c2, c3, c4, c5, c6, c7, c8⟩ :=
    key N e θ ψ χ ξ ζ hθ hψ hχ hξ hζ se h1 h2 sr h3 h4 sμ h5 h6 sρ h7 h8 sm h9 h10
  refine ⟨Ne, Nr, Nμ, Nρ, Nm, c1, c2, c3, c4, c5, c6.trans ?_, c7.trans ?_, c8.trans ?_⟩
  · simp only [gatedErr_add, awayErr_add]
    have key : ∀ x₁ x₂ x₃ x₄ x₅ : ℝ,
        (((x₁ + 6 * Real.pi * lam * (tbe - tE)) / R₀ + κ * tE + τE)
          + (((x₁ + 6 * Real.pi * lam * (tbe - tE)) + (x₂ + 6 * Real.pi * lam * ((tbe -
              tE) + (t4 - tRet))) + RB * (tbe - tE)) / R₀
            + κ * tRet + τRet)) / 2
          + ((x₃ + 6 * Real.pi * lam * (tbμ - tMB)) / R₀ + κ * tMB + τMB)
          + (((x₄ + 6 * Real.pi * lam * (tbρ - tR)) / R₀ + τR)
            + ((x₅ + 6 * Real.pi * lam * (tbm - tMA)) / R₀ + τMA)) / Real.sqrt (1 - v ^ 2)
        = ((x₁ / R₀ + κ * tE + τE)
          + ((x₁ + x₂ + RB * (tbe - tE)) / R₀
            + κ * tRet + τRet)) / 2
          + (x₃ / R₀ + κ * tMB + τMB)
          + ((x₄ / R₀ + τR)
            + (x₅ / R₀ + τMA)) / Real.sqrt (1 - v ^ 2)
          + lam * (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
              R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))) := by
      intro x₁ x₂ x₃ x₄ x₅
      ring
    rw [key]
    linarith only [hk1]
  · simp only [gatedErr_add, awayErr_add]
    have key : ∀ x₁ x₂ x₄ x₅ : ℝ,
        (((x₁ + 6 * Real.pi * lam * (tbe - tE)) / R₀ + κ * tE + τE)
          + (((x₁ + 6 * Real.pi * lam * (tbe - tE)) + (x₂ + 6 * Real.pi * lam * ((tbe -
              tE) + (t4 - tRet))) + RB * (tbe - tE)) / R₀
            + κ * tRet + τRet)) / 2
          + v * (((x₄ + 6 * Real.pi * lam * (tbρ - tR)) / R₀ + τR)
            + ((x₅ + 6 * Real.pi * lam * (tbm - tMA)) / R₀ + τMA)) / Real.sqrt (1 - v ^ 2)
        = ((x₁ / R₀ + κ * tE + τE)
          + ((x₁ + x₂ + RB * (tbe - tE)) / R₀
            + κ * tRet + τRet)) / 2
          + v * ((x₄ / R₀ + τR)
            + (x₅ / R₀ + τMA)) / Real.sqrt (1 - v ^ 2)
          + lam * (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
              R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))) := by
      intro x₁ x₂ x₄ x₅
      ring
    rw [key]
    linarith only [hk2]
  · simp only [gatedErr_add]
    have hs1 : Real.sqrt (1 - v ^ 2) ≤ 1 := by
      have h := Real.sqrt_le_sqrt (by nlinarith only [sq_nonneg v] : 1 - v ^ 2 ≤ 1)
      rwa [Real.sqrt_one] at h
    have y1 : (tbρ - tR) / R₀ + (tbm - tMA) / R₀
        ≤ ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2) := by
      rw [le_div_iff₀ hsq]
      nlinarith only [add_nonneg kr kq, hs1]
    have y2 : (tbρ - tR) / R₀ + (tbm - tMA) / R₀
        ≤ ((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) / R₀) / 2
          + (tbμ - tMB) / R₀
          + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2) := by
      linarith only [y1, div_nonneg (add_nonneg ka kb) (by norm_num : (0 : ℝ) ≤ 2), km]
    have y3 : lam * (6 * Real.pi * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀))
        ≤ lam * (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
            R₀) / 2
          + (tbμ - tMB) / R₀
          + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left y2 (by positivity)) hlam0
    have key : ∀ x y : ℝ,
        (x + 6 * Real.pi * lam * (tbρ - tR)
            + (y + 6 * Real.pi * lam * (tbm - tMA))) / R₀
          = (x + y) / R₀
            + lam * (6 * Real.pi * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀)) := by
      intro x y
      ring
    rw [key]
    linarith only [y3, hk1]

section TriRay

variable {ι κa κb S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κa] [DecidableEq κa]
  [Fintype κb] [DecidableEq κb] [Fintype S] [DecidableEq S] [Nonempty ι] [Nonempty κa]
  [Nonempty κb] {M₀ : Matrix ι ι ℂ} {A₀ : Matrix κa κa ℂ}
  {B₀ : Matrix κb κb ℂ} {σ : ι → S} {α : κa → S} {β : κb → S}
  {r₁ r₂ r₃ r₄ r₅ : S → S → Prop} [DecidableRel r₁] [DecidableRel r₂] [DecidableRel r₃]
  [DecidableRel r₄] [DecidableRel r₅] {Ya : Matrix κa κa ℂ} {Yb : Matrix κb κb ℂ}

/-- ★★★ **M6 from the top from turned rays and nearby pointer angles, for three carriers and
five gates.** `penta_radar_lorentz_near_ray` for the composite of three carriers and the five
gates of `triRun`: from the product ray of the three carriers turned by any unitary `W` of the
composite with `‖W − 1‖ ≤ r_W`, and every five pointer angles within `ρ` of `(1/12, 0)`, the
five pointers have counts and the counts satisfy the Lorentz statement with the errors of
#402 enlarged by `ϵ + ϵ'`. The turned ray is in general not a product ray, so the run is
written as the five-pointer flow from it; for `W = 1` it is `triRun`. -/
theorem tri_radar_lorentz_near_ray (hM : M₀.IsHermitian) (hA : A₀.IsHermitian)
    (hB : B₀.IsHermitian) (hYa : Ya.IsHermitian) (hYas : ∀ i j, α i ≠ α j → Ya i j = 0)
    (hYb : Yb.IsHermitian) (hYbs : ∀ i j, β i ≠ β j → Yb i j = 0) (g₁ g₂ g₃ g₄ g₅ : ℝ)
    (p : GenArena ι) (qa : GenArena κa) (qb : GenArena κb)
    {v R₀ RB κ TE TR TRet TM tE tR tRet tMB tMA τE τR τRet τMB τMA : ℝ}
    {δe ve tbe tce c vr η₀ η t4 t5 δμ vμ tbμ tcμ δρ vρ tbρ tcρ δm vm tbm tcm : ℝ}
    {ce cr cμ cρ cm : ℝ}
    (hv0 : 0 ≤ v) (hv : v < 1) (hR₀ : 0 < R₀)
    (hκ : |RB - Real.sqrt (1 - v ^ 2) * R₀| ≤ κ * R₀)
    (hE : TR - TE = v * (TM - TE)) (hRet : TRet - TR = v * (TM - TRet))
    (hτE : |tE - TE| ≤ τE) (hτRet : |tRet - TRet| ≤ τRet) (hτMB : |tMB - TM| ≤ τMB)
    (hτR : |tR - TR| ≤ τR) (hτMA : |tMA - TM| ≤ τMA)
    (He : IsGatedHistory (coincShift hM hB (gateOp σ β r₁ Yb) (-g₁) p qb) RB δe ve tE tbe tce)
    (Hr : IsAwayHistory (coincShift hM hB (gateOp σ β r₂ Yb) (-g₂) p qb) RB c vr η₀ η tE tbe
      tRet t4 t5)
    (Hμ : IsGatedHistory (coincShift hA hB (gateOp α β r₃ Yb) (-g₃) qa qb) RB δμ vμ tMB tbμ
      tcμ)
    (Hρ : IsGatedHistory (coincShift hM hA (gateOp σ α r₄ Ya) (-g₄) p qa) R₀ δρ vρ tR tbρ tcρ)
    (Hm : IsGatedHistory
      (coincShift hB hA (gateOp β α (fun s s' => r₅ s' s) Ya) (-g₅) qb qa) R₀ δm vm tMA tbm
      tcm)
    (hce : ∀ s t, tbe ≤ s → s ≤ t → t ≤ tce →
      |coincShift hM hB (gateOp σ β r₁ Yb) (-g₁) p qb t
        - coincShift hM hB (gateOp σ β r₁ Yb) (-g₁) p qb s| ≤ ce)
    (hcr : ∀ s t, t4 ≤ s → s ≤ t → t ≤ t5 →
      |coincShift hM hB (gateOp σ β r₂ Yb) (-g₂) p qb t
        - coincShift hM hB (gateOp σ β r₂ Yb) (-g₂) p qb s| ≤ cr)
    (hcμ : ∀ s t, tbμ ≤ s → s ≤ t → t ≤ tcμ →
      |coincShift hA hB (gateOp α β r₃ Yb) (-g₃) qa qb t
        - coincShift hA hB (gateOp α β r₃ Yb) (-g₃) qa qb s| ≤ cμ)
    (hcρ : ∀ s t, tbρ ≤ s → s ≤ t → t ≤ tcρ →
      |coincShift hM hA (gateOp σ α r₄ Ya) (-g₄) p qa t
        - coincShift hM hA (gateOp σ α r₄ Ya) (-g₄) p qa s| ≤ cρ)
    (hcm : ∀ s t, tbm ≤ s → s ≤ t → t ≤ tcm →
      |coincShift hB hA (gateOp β α (fun s s' => r₅ s' s) Ya) (-g₅) qb qa t
        - coincShift hB hA (gateOp β α (fun s s' => r₅ s' s) Ya) (-g₅) qb qa s| ≤ cm)
    {ϵ ϵ' S γ T s ρ : ℝ}
    (hS1 : ‖gateOp σ (fun k : κa × κb => β k.2) r₁ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)‖ ≤ S)
    (hS2 : ‖gateOp σ (fun k : κa × κb => β k.2) r₂ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)‖ ≤ S)
    (hS3 : ‖(1 : Matrix ι ι ℂ) ⊗ₖ gateOp α β r₃ Yb‖ ≤ S)
    (hS4 : ‖gateOp σ (fun k : κa × κb => α k.1) r₄ (Ya ⊗ₖ (1 : Matrix κb κb ℂ))‖ ≤ S)
    (hS5 : ‖(1 : Matrix ι ι ℂ) ⊗ₖ gateOpL α β r₅ Ya‖ ≤ S)
    (hγ1 : |g₁| ≤ γ) (hγ2 : |g₂| ≤ γ) (hγ3 : |g₃| ≤ γ) (hγ4 : |g₄| ≤ γ) (hγ5 : |g₅| ≤ γ)
    (hT1 : tce ≤ T) (hT2 : t5 ≤ T) (hT3 : tcμ ≤ T) (hT4 : tcρ ≤ T) (hT5 : tcm ≤ T)
    (sp : 0 < s) (q1 : s ≤ 1 / 12 - δe) (q2 : s ≤ 1 / 12 - η₀) (q3 : s ≤ 1 / 12 - η)
    (q4 : s ≤ 1 / 12 - c - (-1 / 6 + η)) (q5 : s ≤ 1 / 6 - η - (1 / 12 - c))
    (q6 : s ≤ 1 / 12 - δμ) (q7 : s ≤ 1 / 12 - δρ) (q8 : s ≤ 1 / 12 - δm)
    (q9 : s ≤ 1 / 6 - ce) (q10 : s ≤ 1 / 6 - cr) (q11 : s ≤ 1 / 6 - cμ)
    (q12 : s ≤ 1 / 6 - cρ) (q13 : s
        ≤ 1 / 6 - cm) (W : Matrix.unitaryGroup (ι × (κa × κb)) ℂ) {rW : ℝ}
    (hW : ‖W.val - 1‖ ≤ rW) (hrW : 4 * γ * S * rW * T ≤ s / 2)
    (hrB : 4 * γ * S * rW * ((6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE)
        + (t4 - tRet))) /
      R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2)))
      + (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) /
      R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2)))) ≤ ϵ')
    (hρ0 : 0 < ρ) (hρs : ρ ≤ s / 8)
    (hρA' : ρ * ((20 * γ ^ 2 * S ^ 2 * T + 14 * γ * S) * T) ≤ s / 8)
    (hρB' : ρ * ((20 * γ ^ 2 * S ^ 2 * T + 14 * γ * S) * ((6 * Real.pi * (((tbe - tE) / R₀ + ((tbe
        - tE) + ((tbe - tE) + (t4 - tRet))) / R₀) / 2
      + (tbμ - tMB) / R₀ + ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2)))
      + (6 * Real.pi * (((tbe - tE) / R₀ + ((tbe - tE) + ((tbe - tE) + (t4 - tRet))) / R₀) / 2
      + v * ((tbρ - tR) / R₀ + (tbm - tMA) / R₀) / Real.sqrt (1 - v ^ 2))))) ≤ ϵ) :
    ∀ (N : ℕ) (e : ι × (κa × κb) ≃ Fin (N + 1)) (θ ψ χ ξ ζ : KTorus),
      NearStart ρ θ → NearStart ρ ψ → NearStart ρ χ → NearStart ρ ξ → NearStart ρ ζ →
      ∀ se, tbe ≤ se → se ≤ tce → ∀ sr, t4 ≤ sr → sr ≤ t5 → ∀ sμ, tbμ ≤ sμ → sμ ≤ tcμ →
      ∀ sρ, tbρ ≤ sρ → sρ ≤ tcρ → ∀ sm, tbm ≤ sm → sm ≤ tcm →
      ∃ Ne Nr Nμ Nρ Nm : ℕ,
        IsTickCount {x : PentaSigma N | x.1.1.1.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.1.1.1.2 ∈ displayArc}
            (fun t => fiveCoupledFlow (Matrix.reindex e e (compositeH M₀ (compositeH A₀ B₀)))
              (Matrix.reindex e e
                (gateOp σ (fun k : κa × κb => β k.2) r₁ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)))
              (Matrix.reindex e e
                (gateOp σ (fun k : κa × κb => β k.2) r₂ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)))
              (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ gateOp α β r₃ Yb))
              (Matrix.reindex e e
                (gateOp σ (fun k : κa × κb => α k.1) r₄ (Ya ⊗ₖ (1 : Matrix κb κb ℂ))))
              (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ gateOpL α β r₅ Ya))
              (scaledTrainF_periodic g₁) (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅) t
              (((((idxArenaEquiv e (arenaKick W (prodRay p (prodRay qa qb))), θ), ψ), χ), ξ),
                ζ)) se Ne
        ∧ IsTickCount {x : PentaSigma N | x.1.1.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.1.1.2 ∈ displayArc}
            (fun t => fiveCoupledFlow (Matrix.reindex e e (compositeH M₀ (compositeH A₀ B₀)))
              (Matrix.reindex e e
                (gateOp σ (fun k : κa × κb => β k.2) r₁ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)))
              (Matrix.reindex e e
                (gateOp σ (fun k : κa × κb => β k.2) r₂ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)))
              (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ gateOp α β r₃ Yb))
              (Matrix.reindex e e
                (gateOp σ (fun k : κa × κb => α k.1) r₄ (Ya ⊗ₖ (1 : Matrix κb κb ℂ))))
              (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ gateOpL α β r₅ Ya))
              (scaledTrainF_periodic g₁) (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅) t
              (((((idxArenaEquiv e (arenaKick W (prodRay p (prodRay qa qb))), θ), ψ), χ), ξ),
                ζ)) sr Nr
        ∧ IsTickCount {x : PentaSigma N | x.1.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.1.2 ∈ displayArc}
            (fun t => fiveCoupledFlow (Matrix.reindex e e (compositeH M₀ (compositeH A₀ B₀)))
              (Matrix.reindex e e
                (gateOp σ (fun k : κa × κb => β k.2) r₁ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)))
              (Matrix.reindex e e
                (gateOp σ (fun k : κa × κb => β k.2) r₂ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)))
              (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ gateOp α β r₃ Yb))
              (Matrix.reindex e e
                (gateOp σ (fun k : κa × κb => α k.1) r₄ (Ya ⊗ₖ (1 : Matrix κb κb ℂ))))
              (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ gateOpL α β r₅ Ya))
              (scaledTrainF_periodic g₁) (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅) t
              (((((idxArenaEquiv e (arenaKick W (prodRay p (prodRay qa qb))), θ), ψ), χ), ξ),
                ζ)) sμ Nμ
        ∧ IsTickCount {x : PentaSigma N | x.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.2 ∈ displayArc}
            (fun t => fiveCoupledFlow (Matrix.reindex e e (compositeH M₀ (compositeH A₀ B₀)))
              (Matrix.reindex e e
                (gateOp σ (fun k : κa × κb => β k.2) r₁ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)))
              (Matrix.reindex e e
                (gateOp σ (fun k : κa × κb => β k.2) r₂ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)))
              (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ gateOp α β r₃ Yb))
              (Matrix.reindex e e
                (gateOp σ (fun k : κa × κb => α k.1) r₄ (Ya ⊗ₖ (1 : Matrix κb κb ℂ))))
              (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ gateOpL α β r₅ Ya))
              (scaledTrainF_periodic g₁) (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅) t
              (((((idxArenaEquiv e (arenaKick W (prodRay p (prodRay qa qb))), θ), ψ), χ), ξ),
                ζ)) sρ Nρ
        ∧ IsTickCount {x : PentaSigma N | x.2 ∈ readyArc 2}
            {x : PentaSigma N | x.2 ∈ displayArc}
            (fun t => fiveCoupledFlow (Matrix.reindex e e (compositeH M₀ (compositeH A₀ B₀)))
              (Matrix.reindex e e
                (gateOp σ (fun k : κa × κb => β k.2) r₁ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)))
              (Matrix.reindex e e
                (gateOp σ (fun k : κa × κb => β k.2) r₂ ((1 : Matrix κa κa ℂ) ⊗ₖ Yb)))
              (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ gateOp α β r₃ Yb))
              (Matrix.reindex e e
                (gateOp σ (fun k : κa × κb => α k.1) r₄ (Ya ⊗ₖ (1 : Matrix κb κb ℂ))))
              (Matrix.reindex e e ((1 : Matrix ι ι ℂ) ⊗ₖ gateOpL α β r₅ Ya))
              (scaledTrainF_periodic g₁) (scaledTrainF_periodic g₂)
              (scaledTrainF_periodic g₃) (scaledTrainF_periodic g₄) (scaledTrainF_periodic g₅)
              (contDiff_scaledTrainF g₁) (contDiff_scaledTrainF g₂) (contDiff_scaledTrainF g₃)
              (contDiff_scaledTrainF g₄) (contDiff_scaledTrainF g₅) t
              (((((idxArenaEquiv e (arenaKick W (prodRay p (prodRay qa qb))), θ), ψ), χ), ξ),
                ζ)) sm Nm
        ∧ |(lorentzBoost 1 (-v)
                ((Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀, 0)).1
              - (((Ne : ℝ) * (2 * Real.pi) / R₀
                    + ((Ne : ℝ) * (2 * Real.pi) + (Nr : ℝ) * (2 * Real.pi)) / R₀) / 2
                  - (Nμ : ℝ) * (2 * Real.pi) / R₀)|
            ≤ ((gatedErr ve tE tbe / R₀ + κ * tE + τE)
                + ((gatedErr ve tE tbe + awayErr vr tE tbe tRet t4 + RB * (tbe - tE)) / R₀
                    + κ * tRet + τRet)) / 2
              + (gatedErr vμ tMB tbμ / R₀ + κ * tMB + τMB)
              + ((gatedErr vρ tR tbρ / R₀ + τR) + (gatedErr vm tMA tbm / R₀ + τMA))
                / Real.sqrt (1 - v ^ 2) + ϵ + ϵ'
        ∧ |(lorentzBoost 1 (-v)
                ((Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀, 0)).2
              - (-((((Ne : ℝ) * (2 * Real.pi) + (Nr : ℝ) * (2 * Real.pi)) / R₀
                    - (Ne : ℝ) * (2 * Real.pi) / R₀) / 2))|
            ≤ ((gatedErr ve tE tbe / R₀ + κ * tE + τE)
                + ((gatedErr ve tE tbe + awayErr vr tE tbe tRet t4 + RB * (tbe - tE)) / R₀
                    + κ * tRet + τRet)) / 2
              + v * ((gatedErr vρ tR tbρ / R₀ + τR) + (gatedErr vm tMA tbm / R₀ + τMA))
                / Real.sqrt (1 - v ^ 2) + ϵ + ϵ'
        ∧ |(Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀ - (tR - tMA)|
            ≤ (gatedErr vρ tR tbρ + gatedErr vm tMA tbm) / R₀ + ϵ + ϵ' := by
  have hAB := compositeH_isHermitian hA hB
  have hH := compositeH_isHermitian hM hAB
  have hG₁ := gateOp_snd_isHermitian (κa := κa) σ β r₁ hYb hYbs
  have hG₂ := gateOp_snd_isHermitian (κa := κa) σ β r₂ hYb hYbs
  have hG₃ : ((1 : Matrix ι ι ℂ) ⊗ₖ gateOp α β r₃ Yb).IsHermitian :=
    kronecker_isHermitian Matrix.isHermitian_one (gateOp_isHermitian α β r₃ hYb hYbs)
  have hG₄ := gateOp_fst_isHermitian (κb := κb) σ α r₄ hYa hYas
  have hG₅ : ((1 : Matrix ι ι ℂ) ⊗ₖ gateOpL α β r₅ Ya).IsHermitian :=
    kronecker_isHermitian Matrix.isHermitian_one (gateOpL_isHermitian α β r₅ hYa hYas)
  rw [← freeShift_tri_gate_snd σ β r₁ hM hA hB Yb (-g₁) p qa qb] at He hce
  rw [← freeShift_tri_gate_snd σ β r₂ hM hA hB Yb (-g₂) p qa qb] at Hr hcr
  rw [← freeShift_tri_pair α β r₃ hM hA hB Yb (-g₃) p qa qb] at Hμ hcμ
  rw [← freeShift_tri_gate_fst σ α r₄ hM hA hB Ya (-g₄) p qa qb] at Hρ hcρ
  rw [← freeShift_tri_pairL α β r₅ hM hA hB Ya (-g₅) p qa qb] at Hm hcm
  exact penta_radar_lorentz_near_ray hH hG₁ hG₂ hG₃ hG₄ hG₅ g₁ g₂ g₃ g₄ g₅
    (prodRay p (prodRay qa qb)) hv0 hv hR₀ hκ hE hRet hτE hτRet hτMB hτR hτMA He Hr Hμ Hρ Hm
    hce hcr hcμ hcρ hcm hS1 hS2 hS3 hS4 hS5 hγ1 hγ2 hγ3 hγ4 hγ5 hT1 hT2 hT3 hT4 hT5 sp q1 q2
    q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 W hW hrW hrB hρ0 hρs hρA' hρB'

end TriRay

end CSD.RecordLayer

end
