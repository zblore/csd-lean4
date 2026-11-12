/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.ProductFlow
public import CsdLean4.RecordLayer.UnifiedDepartureArrival
public import CsdLean4.RecordLayer.UnifiedCountAtWrite

/-!
# A clock on its own carrier beside a messenger: one flow, two records, two counts

**TERM-SCOPE(Hamiltonian)** — this module uses the *restricted* sense of "Hamiltonian";
`specs/TERMS.md` records what is backed and what is not.

**Category:** 7-SigmaLayer (the record layer). BACKLOG #372 — the first brick of milestone **M6**
of the author's programme "From `Σ` to physical spacetime", after the author's decision of
2026-11-11 under UO-16: the clock is a second carrier, not a level of the messenger, and it is
the tick clock of #358.

Until now the only clock in a run with a position record was the carrier's own level (#360,
#366, #369): a messenger that travels would carry the count with it. Here the clock is a
separate device. The arena is

  `(ℂℙ^{2M+1} × T² × T²) × (ℂℙ^{4M_c+3} × T²)`,

the messenger with its two region pointers (the arena of #367) beside the two-level clock device
with its tick pointer (the arena of #357 and #358). The joint energy `clockMessengerEnergy` is
the sum of the two energies, with no term between the factors. Its Hamiltonian flow
`clockMessengerFlow`, for the product form, is the pair of the two flows
(`clockMessengerFlow_apply`), by `LF4/ProductFlow.lean`. It preserves the product of the two
arena measures (`map_clockMessengerFlow`).

**One run.** From the messenger's start of #367 and the clock's train start of #358
(`clockMessenger_departure_arrival_counts`): along the one orbit of `clockMessengerFlow` there
are flow times `τ_d ≤ 625π/3 ≤ τ_a` at which the departure readout and the arrival readout are
written, each a record write of the joint flow; the clock's history is a swing, so it has a tick
count `N_d` at `τ_d` and `N_a` at `τ_a`; and

  `|(N_a − N_d) (2π/R) − (τ_a − τ_d)| ≤ 4π/R`.

The count difference is a number of tick records of a device that is not the messenger.

## Exact scope

* **No coupling between the clock and the messenger.** The clock's history does not depend on
  the messenger's state, and the messenger's does not depend on the clock's
  (`clockMessengerFlow_fst`, `clockMessengerFlow_snd`). The clock is beside the messenger's
  departure region only in the sense that both are in one arena. Nothing places it there. The
  coupling of the clock to a detector is the next brick.
* **The counts are aligned by the flow parameter.** `N_d` is the clock's count at the flow time
  `τ_d` at which the departure write completes. No degree of freedom holds the pair (record,
  count), and no record reads the count. That is access to UA-7, as in #366.
* **The two writes do not certify a transit.** They are the writes of #367: each readout crosses
  a threshold of accumulated weight in its region. The departure statement has an empty "before"
  clause. See the scope of `RecordLayer/UnifiedDepartureArrival.lean`.
* **The clock is the exact instance of #358**: one momentum mode, the profile `trainF`, the
  fibre `θ₂ = 0`, the start a quarter turn early. That start is one point of the clock's arena.
  No measure of clock starts is stated.
* **The clock is at rest or moving as its mode says.** Its rate `R` is the dilated rate of the
  mode `m` on its own ring. The clock's ring and the messenger's ring are two rings; no distance
  between a clock site and a messenger site is defined.
* **The interval bound is two ticks**, `4π/R`, and it compares the count difference with a
  difference of flow times. It is not a statement about distance and no speed appears.
* **Definite facts, not statistics.** The measure statement is invariance only.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-7,
UA-12, UA-13, UA-16, UO-14, UO-16, UD-103, UD-104); `LF4/ProductFlow.lean`
(`hamiltonianFlow_prodEnergy`, `measurePreserving_hamiltonianFlow_prodEnergy`);
`RecordLayer/UnifiedDepartureArrival.lean` (`regionTwoFlow`, `regionTwoFlow_departure_arrival`,
`departureArrivalFibres`); `RecordLayer/UnifiedDiracClock.lean` (`clockPointerFlow`,
`clockPointerEnergy`, `kMuL_map_clockPointerFlow`); `RecordLayer/UnifiedDiracClockTicks.lean`
(`IsSwing`, `IsTickCount`, `isSwing_clockPointerFlow_train`, `tickReady`, `tickDisplay`);
`RecordLayer/UnifiedCountAtWrite.lean` (`IsSwing.abs_tickTime_sub_sub_le`);
`LF4/CrossCoupledFlow.lean` (`CrossSigma`, `crossForm`: the same arena with a coupling);
`RecordLayer/ClockAndEcho.lean` (#202: an earlier clock beside an echo, on two-site arenas).
-/

@[expose] public section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization

namespace CSD.RecordLayer

/-! ### A swing read on the second factor -/

/-- A swing of a history is a swing of any history that has it as its second component. -/
theorem IsSwing.prodMk_snd {X Y : Type*} {rest disp : Set Y} {γ : ℝ → Y} {R c d T : ℝ}
    (h : IsSwing rest disp γ R c d T) (δ : ℝ → X) :
    IsSwing (Prod.snd ⁻¹' rest) (Prod.snd ⁻¹' disp) (fun t => (δ t, γ t)) R c d T :=
  ⟨h.rate_pos, h.neg_one_lt, h.thresh_le, h.rest_of_cos, h.disp_of_cos, h.le_cos_of_rest,
    h.cos_lt_of_disp⟩

/-! ### The arena, the energy and the flow -/

section Arena

variable {M Mc : ℕ} {f h fc : ℝ → ℝ} (J μ g₁ g₂ : ℝ) (A B : Finset (ZMod (M + 1)))
  (Jc μ₀ μ₁ gc : ℝ) (hf : Function.Periodic f 1) (hh : Function.Periodic h 1)
  (hfc : Function.Periodic fc 1)

variable (Mc) in
/-- **The joint energy of a messenger with two region pointers and a clock device with its tick
pointer**: the sum of the two energies. No term joins the two factors. -/
noncomputable def clockMessengerEnergy : CrossSigma (2 * M + 1) (4 * Mc + 3) → ℝ :=
  prodEnergy
    (twoCoupledEnergy (Matrix.reindex (diracIdx M) (diracIdx M) (diracHam J μ))
      (Matrix.reindex (diracIdx M) (diracIdx M) ((g₁ : ℂ) • regionProj A))
      (Matrix.reindex (diracIdx M) (diracIdx M) ((g₂ : ℂ) • regionProj B)) hf hh)
    (clockPointerEnergy Mc Jc μ₀ μ₁ gc hfc)

variable (Mc) in
/-- The joint energy is smooth for smooth profiles. -/
theorem contMDiff_clockMessengerEnergy (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hcc : ContDiff ℝ ∞ fc) :
    ContMDiff 𝓘(ℝ, CrossModel (2 * M + 1) (4 * Mc + 3)) 𝓘(ℝ, ℝ) ∞
      (clockMessengerEnergy Mc J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hfc) :=
  contMDiff_prodEnergy (contMDiff_twoCoupledEnergy _ _ _ hf hh hc hch)
    (contMDiff_clockPointerEnergy Jc μ₀ μ₁ gc hfc hcc)

variable (Mc) in
/-- ★ **The joint flow of the messenger and the clock**: the Hamiltonian flow of
`clockMessengerEnergy` for the form `echoForm ⊕ arenaForm`. -/
noncomputable def clockMessengerFlow (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hcc : ContDiff ℝ ∞ fc) (t : ℝ) :
    CrossSigma (2 * M + 1) (4 * Mc + 3) → CrossSigma (2 * M + 1) (4 * Mc + 3) :=
  (crossForm_isSymplectic (2 * M + 1) (4 * Mc + 3)).hamiltonianFlow
    (contMDiff_clockMessengerEnergy Mc J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hfc hc hch hcc) t

/-- ★★★ **The messenger and the clock move side by side.** The joint flow is the messenger's
flow with its two pointers on the first factor and the clock's flow with its tick pointer on the
second. -/
theorem clockMessengerFlow_apply (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hcc : ContDiff ℝ ∞ fc) (t : ℝ) (x : EchoSigma (2 * M + 1)) (y : KSigma (4 * Mc + 3 + 1)) :
    clockMessengerFlow Mc J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hfc hc hch hcc t (x, y)
      = (regionTwoFlow J μ g₁ g₂ A B hf hh hc hch t x,
          clockPointerFlow Mc Jc μ₀ μ₁ gc hfc hcc t y) :=
  hamiltonianFlow_prodEnergy (echoForm_isSymplectic (2 * M + 1))
    (arenaForm_isSymplectic (4 * Mc + 3)) (contMDiff_twoCoupledEnergy _ _ _ hf hh hc hch)
    (contMDiff_clockPointerEnergy Jc μ₀ μ₁ gc hfc hcc) t x y

/-- ★ **The messenger does not feel the clock.** -/
theorem clockMessengerFlow_fst (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hcc : ContDiff ℝ ∞ fc) (t : ℝ) (z : CrossSigma (2 * M + 1) (4 * Mc + 3)) :
    (clockMessengerFlow Mc J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hfc hc hch hcc t z).1
      = regionTwoFlow J μ g₁ g₂ A B hf hh hc hch t z.1 := by
  obtain ⟨x, y⟩ := z
  rw [clockMessengerFlow_apply]

/-- ★ **The clock does not feel the messenger.** -/
theorem clockMessengerFlow_snd (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hcc : ContDiff ℝ ∞ fc) (t : ℝ) (z : CrossSigma (2 * M + 1) (4 * Mc + 3)) :
    (clockMessengerFlow Mc J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hfc hc hch hcc t z).2
      = clockPointerFlow Mc Jc μ₀ μ₁ gc hfc hcc t z.2 := by
  obtain ⟨x, y⟩ := z
  rw [clockMessengerFlow_apply]

/-- ★★ **The joint flow preserves the product of the two arena measures.** -/
theorem map_clockMessengerFlow (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    (hcc : ContDiff ℝ ∞ fc) (p₀ : CPN (2 * M + 1 + 1)) (q₀ : CPN (4 * Mc + 3 + 1)) (t : ℝ) :
    Measure.map (clockMessengerFlow Mc J μ g₁ g₂ A B Jc μ₀ μ₁ gc hf hh hfc hc hch hcc t)
        ((echoMuL p₀).prod (kMuL q₀))
      = (echoMuL p₀).prod (kMuL q₀) := by
  have : SFinite (echoMuL p₀) := by
    unfold echoMuL
    infer_instance
  exact (measurePreserving_hamiltonianFlow_prodEnergy (echoForm_isSymplectic (2 * M + 1))
    (arenaForm_isSymplectic (4 * Mc + 3)) (contMDiff_twoCoupledEnergy _ _ _ hf hh hc hch)
    (contMDiff_clockPointerEnergy Jc μ₀ μ₁ gc hfc hcc) (echoMuL p₀) (kMuL q₀) t
    ⟨measurable_twoCoupledFlow _ _ _ hf hh hc hch t,
      echoMuL_map_twoCoupledFlow ((diracHam_isHermitian J μ).submatrix _)
        ((regionProj_smul_isHermitian g₁ A).submatrix _)
        ((regionProj_smul_isHermitian g₂ B).submatrix _) hf hh hc hch p₀ t⟩
    ⟨measurable_clockPointerFlow Jc μ₀ μ₁ gc hfc hcc t,
      kMuL_map_clockPointerFlow Jc μ₀ μ₁ gc hfc hcc q₀ t⟩).map_eq

end Arena

/-! ### One run: departure, arrival, and the clock's count at each -/

section Run

variable {M Mc : ℕ} {f h : ℝ → ℝ} (g₁ g₂ : ℝ) (hf : Function.Periodic f 1)
  (hh : Function.Periodic h 1) (hL : 640000 ≤ M + 1)

/-- ★★★ **A departure record, an arrival record, and the count of a separate clock at each, in
one run.** On the arena of a messenger beside a clock device, from the messenger's start of
`regionTwoFlow_departure_arrival` and the clock's train start: along the one orbit of
`clockMessengerFlow` the departure readout is written by a flow time `τ_d ≤ 625π/3` and the
arrival readout by a flow time `τ_a` with `625π/3 ≤ τ_a ≤ 4375π/3`; the clock has a tick count
`N_d` at `τ_d` and `N_a` at `τ_a`; and the count difference times the clock's period is within
two periods of `τ_a − τ_d`. The times are flow times (UA-7). -/
theorem clockMessenger_departure_arrival_counts (hc : ContDiff ℝ ∞ f) (hch : ContDiff ℝ ∞ h)
    {θ ψ : KTorus} (hθ : θ ∈ readyArc 2) (hψ : ψ ∈ readyArc 2)
    (hx : (θ.2, ψ.2) ∈ departureArrivalFibres g₁ g₂ hf hh)
    (Jc : ℝ) {μ₀ μ₁ : ℝ} (h0 : 0 < μ₀) (h01 : μ₀ < μ₁) (h10 : μ₁ < 2 * μ₀) (m : ℤ)
    {β : ℤ → ℂ} (hβ : β m ≠ 0) {R : ℝ}
    (hRe : R = levelClockRate μ₀ μ₁ (2 * Jc * Real.sin (angleZ (Mc + 1) m))) {gc : ℝ}
    (hg : gc = R * ‖β m‖ ^ 2
      / (16 * (deviceCoherence (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β 0)).re))
    {z₀ : CrossSigma (2 * M + 1) (4 * Mc + 3)}
    (hz₀ : z₀ = (((idxArenaEquiv (diracIdx M)
          (chainRay (crossPacket (L := M + 1) 0) (crossPacket_ne_zero hL)), θ), ψ),
        (clockArenaEquiv Mc (deviceRay (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β
          (-(Real.pi / (2 * R)))) (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _)),
          ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ)))))) :
    ∃ (τd τa : ℝ) (Nd Na : ℕ), 0 ≤ τd ∧ τd ≤ 625 * Real.pi / 3 ∧ 625 * Real.pi / 3 ≤ τa
      ∧ τa ≤ 4375 * Real.pi / 3
      ∧ IsRecordWrite
          (fun t => echoFstShown (2 * M + 1)
            (clockMessengerFlow Mc (crossHop (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
              (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh trainF_periodic hc hch contDiff_trainF t
              z₀).1)
          0 0 τd (1 / (3 * rateAt g₁ 1 hf θ.2)) true
      ∧ IsRecordWrite
          (fun t => echoSiteShown (2 * M + 1)
            (clockMessengerFlow Mc (crossHop (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
              (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh trainF_periodic hc hch contDiff_trainF t
              z₀).1)
          0 (625 * Real.pi / 3) τa (1 / (3 * rateAt g₂ 1 hh ψ.2)) true
      ∧ IsTickCount (Prod.snd ⁻¹' tickReady Mc) (Prod.snd ⁻¹' tickDisplay Mc)
          (fun t => clockMessengerFlow Mc (crossHop (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
            (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh trainF_periodic hc hch contDiff_trainF t z₀)
          τd Nd
      ∧ IsTickCount (Prod.snd ⁻¹' tickReady Mc) (Prod.snd ⁻¹' tickDisplay Mc)
          (fun t => clockMessengerFlow Mc (crossHop (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
            (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh trainF_periodic hc hch contDiff_trainF t z₀)
          τa Na
      ∧ |((Na : ℝ) - Nd) * (2 * Real.pi / R) - (τa - τd)| ≤ 4 * Real.pi / R := by
  subst hz₀
  obtain ⟨τd, τa, hd0, hd1, ha0, ha1, wd, wa⟩ :=
    regionTwoFlow_departure_arrival g₁ g₂ hf hh hL hc hch hθ hψ hx
  have hpos : (0 : ℝ) ≤ 625 * Real.pi / 3 := by positivity
  have hτa : 0 ≤ τa := hpos.trans ha0
  -- the two histories of the joint flow
  have e₁ : ∀ t, (clockMessengerFlow Mc (crossHop (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ
        (farHalf (M + 1)) Jc μ₀ μ₁ gc hf hh trainF_periodic hc hch contDiff_trainF t
        (((idxArenaEquiv (diracIdx M)
          (chainRay (crossPacket (L := M + 1) 0) (crossPacket_ne_zero hL)), θ), ψ),
        (clockArenaEquiv Mc (deviceRay (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β
          (-(Real.pi / (2 * R)))) (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _)),
          ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))))))
      = (regionTwoFlow (crossHop (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) hf hh
            hc hch t ((idxArenaEquiv (diracIdx M)
              (chainRay (crossPacket (L := M + 1) 0) (crossPacket_ne_zero hL)), θ), ψ),
          clockPointerFlow Mc Jc μ₀ μ₁ gc trainF_periodic contDiff_trainF t
            (clockArenaEquiv Mc (deviceRay (devicePacket (L := Mc + 1) Jc μ₀ μ₁ {m} β
              (-(Real.pi / (2 * R)))) (devicePacket_single_ne_zero h0 (h0.trans h01) m hβ _)),
              ((((1 / 12 : ℝ) : CircleFibre)), (0 : AddCircle (1 : ℝ))))) := fun t =>
    clockMessengerFlow_apply _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t _ _
  simp only [e₁]
  -- the clock's swing, read on the joint history
  have sd := (isSwing_clockPointerFlow_train (M := Mc) Jc h0 h01 h10 m hβ hRe hg τd).prodMk_snd
    (fun t => regionTwoFlow (crossHop (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) hf
      hh hc hch t ((idxArenaEquiv (diracIdx M)
        (chainRay (crossPacket (L := M + 1) 0) (crossPacket_ne_zero hL)), θ), ψ))
  have sa := (isSwing_clockPointerFlow_train (M := Mc) Jc h0 h01 h10 m hβ hRe hg τa).prodMk_snd
    (fun t => regionTwoFlow (crossHop (M + 1)) 3 g₁ g₂ (farHalf (M + 1))ᶜ (farHalf (M + 1)) hf
      hh hc hch t ((idxArenaEquiv (diracIdx M)
        (chainRay (crossPacket (L := M + 1) 0) (crossPacket_ne_zero hL)), θ), ψ))
  obtain ⟨Nd, hNd⟩ := sd.exists_tickCount hd0
  obtain ⟨Na, hNa⟩ := sa.exists_tickCount hτa
  exact ⟨τd, τa, Nd, Na, hd0, hd1, ha0, ha1, wd, wa, hNd, hNa,
    sd.abs_tickTime_sub_sub_le sa hd0 hτa hNd hNa⟩

end Run

end CSD.RecordLayer

end
