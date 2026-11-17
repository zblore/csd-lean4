/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.UnifiedFibreRun

/-!
# M6 from the top, for the five-pointer flow from any pointer angles

**Category:** 7-SigmaLayer (the record layer). BACKLOG #429 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Task 9 of the research delivery
plan of 2026-11-16 (an open set of pointer angles), fourth part. No new assumption beyond
UA-18.

`penta_radar_lorentz` (#404) is stated on the fibres where the five profiles vanish and for
pointers started at `1/12`. This module states it for **any** pointer angles: the carrier
then moves by the free flow of the constant matrix `fibreH` (#428), and a pointer started at
`1/12 + η_i` is, as seen from `1/12`, displaced by `η_i` plus its displacement along that
orbit.

* `pshift_eq_of_start` — a pointer started at `1/12 + η` and displaced by `d` is the pointer
  started at `1/12` displaced by `η + d`;
* ★★★ `penta_radar_lorentz_fibre` — if the five offset displacements have the histories of
  #402, the five pointers have counts and the counts satisfy the Lorentz statement.

## Exact scope

* **Conditional on the five histories of the offset displacements along the orbit of
  `fibreH`.** They are those of the coupled flow, not of the uncoupled one. That they hold
  near the fibres where the profiles vanish (from #426, #427 and #428) is not proved here.
* **The moving angle of each pointer is `1/12 + η_i` as a class modulo `1`**; nothing is
  assumed about the size of `η_i` here, the histories carry it.
* **All five observables Hermitian.**

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-18, UO-16, UD-164, UD-168, UD-197, UD-198, UD-199); `RecordLayer/UnifiedFibreRun.lean`
(#428: `pentaRun_fibre`, `fibreH`); `RecordLayer/UnifiedPentaRun.lean` (#404:
`penta_radar_lorentz`, `freeShift`); `RecordLayer/UnifiedRadarSkeleton.lean` (#402:
`radar_lorentz_of_histories`); `RecordLayer/UnifiedRadarStability.lean` (#427: the histories
of perturbed displacements).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-- A pointer started at `1/12 + η` and displaced by `d` is the pointer started at `1/12`
with the same conserved angle, displaced by `η + d`. -/
theorem pshift_eq_of_start {θ : KTorus} {η : ℝ}
    (hθ : θ.1 = ((1 / 12 + η : ℝ) : AddCircle (1 : ℝ))) (d : ℝ) :
    pshift d θ = pshift (η + d) ((((1 / 12 : ℝ) : CircleFibre)), θ.2) := by
  refine Prod.ext ?_ rfl
  show θ.1 + (d : AddCircle (1 : ℝ))
    = ((1 / 12 : ℝ) : AddCircle (1 : ℝ)) + ((η + d : ℝ) : AddCircle (1 : ℝ))
  rw [hθ, AddCircle.coe_add, AddCircle.coe_add, add_assoc]

section Indexed

variable {ν : Type*} [Fintype ν] [DecidableEq ν] {N : ℕ} (e : ν ≃ Fin (N + 1))
  {H G₁ G₂ G₃ G₄ G₅ : Matrix ν ν ℂ} {f g k l r : ℝ → ℝ}

/-- ★★★ **M6 from the top, for the five-pointer flow from any pointer angles.** The flow of
UA-18's arena for a carrier with any index type and five Hermitian observables, from any ray,
the five pointers started at `1/12 + η_i` with any conserved angles. If the five offset
displacements `η_i + freeShift G_i` along the free orbit of the fibre's matrix `fibreH` have
the histories of `radar_lorentz_of_histories` (#402), with the rate and the times as there:
then at every choice of flow times in the five reading windows the five pointers have counts,
and those counts satisfy the Lorentz statement with the errors of #402. -/
theorem penta_radar_lorentz_fibre (hH : H.IsHermitian) (hG₁ : G₁.IsHermitian)
    (hG₂ : G₂.IsHermitian) (hG₃ : G₃.IsHermitian) (hG₄ : G₄.IsHermitian)
    (hG₅ : G₅.IsHermitian) (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hr : Function.Periodic r 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k)
    (hcl : ContDiff ℝ ∞ l) (hcr : ContDiff ℝ ∞ r) (p : GenArena ν) {θ ψ χ ξ ζ : KTorus}
    (hF : (fibreH H G₁ G₂ G₃ G₄ G₅ (hf.lift θ.2) (hg.lift ψ.2) (hk.lift χ.2) (hl.lift ξ.2)
      (hr.lift ζ.2)).IsHermitian)
    {ηe ηr ημ ηρ ηm : ℝ}
    (hθ1 : θ.1 = ((1 / 12 + ηe : ℝ) : AddCircle (1 : ℝ)))
    (hψ1 : ψ.1 = ((1 / 12 + ηr : ℝ) : AddCircle (1 : ℝ)))
    (hχ1 : χ.1 = ((1 / 12 + ημ : ℝ) : AddCircle (1 : ℝ)))
    (hξ1 : ξ.1 = ((1 / 12 + ηρ : ℝ) : AddCircle (1 : ℝ)))
    (hζ1 : ζ.1 = ((1 / 12 + ηm : ℝ) : AddCircle (1 : ℝ)))
    {v R₀ RB κ TE TR TRet TM tE tR tRet tMB tMA τE τR τRet τMB τMA : ℝ}
    {δe ve tbe tce c vr η₀ η t4 t5 δμ vμ tbμ tcμ δρ vρ tbρ tcρ δm vm tbm tcm : ℝ}
    (hv0 : 0 ≤ v) (hv : v < 1) (hR₀ : 0 < R₀)
    (hκ : |RB - Real.sqrt (1 - v ^ 2) * R₀| ≤ κ * R₀)
    (hE : TR - TE = v * (TM - TE)) (hRet : TRet - TR = v * (TM - TRet))
    (hτE : |tE - TE| ≤ τE) (hτRet : |tRet - TRet| ≤ τRet) (hτMB : |tMB - TM| ≤ τMB)
    (hτR : |tR - TR| ≤ τR) (hτMA : |tMA - TM| ≤ τMA)
    (He : IsGatedHistory (fun t => ηe + freeShift hF G₁ (hf.deriv_periodic.lift θ.2) p t) RB
      δe ve tE tbe tce)
    (Hr : IsAwayHistory (fun t => ηr + freeShift hF G₂ (hg.deriv_periodic.lift ψ.2) p t) RB c
      vr η₀ η tE tbe tRet t4 t5)
    (Hμ : IsGatedHistory (fun t => ημ + freeShift hF G₃ (hk.deriv_periodic.lift χ.2) p t) RB
      δμ vμ tMB tbμ tcμ)
    (Hρ : IsGatedHistory (fun t => ηρ + freeShift hF G₄ (hl.deriv_periodic.lift ξ.2) p t) R₀
      δρ vρ tR tbρ tcρ)
    (Hm : IsGatedHistory (fun t => ηm + freeShift hF G₅ (hr.deriv_periodic.lift ζ.2) p t) R₀
      δm vm tMA tbm tcm) :
    ∀ se, tbe ≤ se → se ≤ tce → ∀ sr, t4 ≤ sr → sr ≤ t5 → ∀ sμ, tbμ ≤ sμ → sμ ≤ tcμ →
      ∀ sρ, tbρ ≤ sρ → sρ ≤ tcρ → ∀ sm, tbm ≤ sm → sm ≤ tcm →
      ∃ Ne Nr Nμ Nρ Nm : ℕ,
        IsTickCount {x : PentaSigma N | x.1.1.1.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.1.1.1.2 ∈ displayArc}
            (fun t => fiveCoupledFlow (Matrix.reindex e e H) (Matrix.reindex e e G₁)
              (Matrix.reindex e e G₂) (Matrix.reindex e e G₃) (Matrix.reindex e e G₄)
              (Matrix.reindex e e G₅) hf hg hk hl hr hc hcg hck hcl hcr t
              (((((idxArenaEquiv e p, θ), ψ), χ), ξ), ζ)) se Ne
        ∧ IsTickCount {x : PentaSigma N | x.1.1.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.1.1.2 ∈ displayArc}
            (fun t => fiveCoupledFlow (Matrix.reindex e e H) (Matrix.reindex e e G₁)
              (Matrix.reindex e e G₂) (Matrix.reindex e e G₃) (Matrix.reindex e e G₄)
              (Matrix.reindex e e G₅) hf hg hk hl hr hc hcg hck hcl hcr t
              (((((idxArenaEquiv e p, θ), ψ), χ), ξ), ζ)) sr Nr
        ∧ IsTickCount {x : PentaSigma N | x.1.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.1.2 ∈ displayArc}
            (fun t => fiveCoupledFlow (Matrix.reindex e e H) (Matrix.reindex e e G₁)
              (Matrix.reindex e e G₂) (Matrix.reindex e e G₃) (Matrix.reindex e e G₄)
              (Matrix.reindex e e G₅) hf hg hk hl hr hc hcg hck hcl hcr t
              (((((idxArenaEquiv e p, θ), ψ), χ), ξ), ζ)) sμ Nμ
        ∧ IsTickCount {x : PentaSigma N | x.1.2 ∈ readyArc 2}
            {x : PentaSigma N | x.1.2 ∈ displayArc}
            (fun t => fiveCoupledFlow (Matrix.reindex e e H) (Matrix.reindex e e G₁)
              (Matrix.reindex e e G₂) (Matrix.reindex e e G₃) (Matrix.reindex e e G₄)
              (Matrix.reindex e e G₅) hf hg hk hl hr hc hcg hck hcl hcr t
              (((((idxArenaEquiv e p, θ), ψ), χ), ξ), ζ)) sρ Nρ
        ∧ IsTickCount {x : PentaSigma N | x.2 ∈ readyArc 2}
            {x : PentaSigma N | x.2 ∈ displayArc}
            (fun t => fiveCoupledFlow (Matrix.reindex e e H) (Matrix.reindex e e G₁)
              (Matrix.reindex e e G₂) (Matrix.reindex e e G₃) (Matrix.reindex e e G₄)
              (Matrix.reindex e e G₅) hf hg hk hl hr hc hcg hck hcl hcr t
              (((((idxArenaEquiv e p, θ), ψ), χ), ξ), ζ)) sm Nm
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
                / Real.sqrt (1 - v ^ 2)
        ∧ |(lorentzBoost 1 (-v)
                ((Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀, 0)).2
              - (-((((Ne : ℝ) * (2 * Real.pi) + (Nr : ℝ) * (2 * Real.pi)) / R₀
                    - (Ne : ℝ) * (2 * Real.pi) / R₀) / 2))|
            ≤ ((gatedErr ve tE tbe / R₀ + κ * tE + τE)
                + ((gatedErr ve tE tbe + awayErr vr tE tbe tRet t4 + RB * (tbe - tE)) / R₀
                    + κ * tRet + τRet)) / 2
              + v * ((gatedErr vρ tR tbρ / R₀ + τR) + (gatedErr vm tMA tbm / R₀ + τMA))
                / Real.sqrt (1 - v ^ 2)
        ∧ |(Nρ : ℝ) * (2 * Real.pi) / R₀ - (Nm : ℝ) * (2 * Real.pi) / R₀ - (tR - tMA)|
            ≤ (gatedErr vρ tR tbρ + gatedErr vm tMA tbm) / R₀ := by
  have key := pentaRun_fibre e hH hG₁ hG₂ hG₃ hG₄ hG₅ hf hg hk hl hr hc hcg hck hcl hcr p θ ψ
    χ ξ ζ hF
  have hrep : rep (((1 / 12 : ℝ) : CircleFibre)) = 1 / 12 :=
    rep_coe_of_mem_Ioc ⟨by norm_num, by norm_num⟩
  exact radar_lorentz_of_histories (X := PentaSigma N)
    (πe := fun x => x.1.1.1.1.2) (πr := fun x => x.1.1.1.2) (πμ := fun x => x.1.1.2)
    (πρ := fun x => x.1.2) (πm := fun x => x.2)
    (γ := fun t => fiveCoupledFlow (Matrix.reindex e e H) (Matrix.reindex e e G₁)
      (Matrix.reindex e e G₂) (Matrix.reindex e e G₃) (Matrix.reindex e e G₄)
      (Matrix.reindex e e G₅) hf hg hk hl hr hc hcg hck hcl hcr t
      (((((idxArenaEquiv e p, θ), ψ), χ), ξ), ζ))
    (qe := ((((1 / 12 : ℝ) : CircleFibre)), θ.2)) (qr := ((((1 / 12 : ℝ) : CircleFibre)), ψ.2))
    (qμ := ((((1 / 12 : ℝ) : CircleFibre)), χ.2)) (qρ := ((((1 / 12 : ℝ) : CircleFibre)), ξ.2))
    (qm := ((((1 / 12 : ℝ) : CircleFibre)), ζ.2))
    hv0 hv hR₀ hκ hE hRet hτE hτRet hτMB hτR hτMA hrep hrep hrep hrep hrep
    (fun t _ _ => by
      show (fiveCoupledFlow _ _ _ _ _ _ hf hg hk hl hr hc hcg hck hcl hcr t _).1.1.1.1.2 = _
      rw [key t]
      exact pshift_eq_of_start hθ1 _)
    (fun t _ _ => by
      show (fiveCoupledFlow _ _ _ _ _ _ hf hg hk hl hr hc hcg hck hcl hcr t _).1.1.1.2 = _
      rw [key t]
      exact pshift_eq_of_start hψ1 _)
    (fun t _ _ => by
      show (fiveCoupledFlow _ _ _ _ _ _ hf hg hk hl hr hc hcg hck hcl hcr t _).1.1.2 = _
      rw [key t]
      exact pshift_eq_of_start hχ1 _)
    (fun t _ _ => by
      show (fiveCoupledFlow _ _ _ _ _ _ hf hg hk hl hr hc hcg hck hcl hcr t _).1.2 = _
      rw [key t]
      exact pshift_eq_of_start hξ1 _)
    (fun t _ _ => by
      show (fiveCoupledFlow _ _ _ _ _ _ hf hg hk hl hr hc hcg hck hcl hcr t _).2 = _
      rw [key t]
      exact pshift_eq_of_start hζ1 _)
    He Hr Hμ Hρ Hm

end Indexed

end CSD.RecordLayer

end
