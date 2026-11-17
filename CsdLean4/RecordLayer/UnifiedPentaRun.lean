/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.PentaCoupledFlow
public import CsdLean4.RecordLayer.UnifiedRadarSkeleton

/-!
# The five-pointer run: the flow of UA-18's arena on the fibres where the profiles vanish

**Category:** 7-SigmaLayer (the record layer). BACKLOG #404 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; item R1 of the list under
UD-164, first half. No new assumption beyond UA-18.

The top-down statement of #402 is about any run with five pointers. This module puts it on
the five-pointer arena of UA-18 (#389): it solves the flow from a ray on the fibres where
all five profiles vanish, and reads the five pointers.

* `freeTurn` — a pointer's turning along the uncoupled orbit: `z ∫₀ᵗ −2⟨B⟩`;
* `twoCoupledFlow_of_lift_eq_zero`, `threeCoupledFlow_of_lift_eq_zero`,
  `fourCoupledFlow_of_lift_eq_zero`, ★★ `fiveCoupledFlow_of_lift_eq_zero` — on the fibres
  where all the profiles vanish the ray moves by the uncoupled Schrödinger unitary and each
  pointer is turned by `freeTurn` of its own observable;
* `idxArenaEquiv_kick_free`, `freeShift`, `freeTurn_reindex` — the same for a carrier with any
  finite index type;
* ★★ `pentaRun_eq` — the five-pointer flow of a carrier with any index type, from a ray:
  pointer `i` is at `pshift (freeShift G_i z_i p t)` of its start;
* ★★★ `penta_radar_lorentz` — the top-down statement of #402 for this flow: if the five
  displacements `freeShift G_i` have the five histories, with the rate and the times as in
  #402, the five counts of the five pointers of the flow of UA-18's arena satisfy the Lorentz
  statement with the errors of #402.

## Exact scope

* **Half of R1.** What is done: the run of #402 is now the flow of the arena of UA-18 (d),
  and the five displacements are named integrals along the carrier's uncoupled orbit. What
  is not done: that those integrals have the five histories. For a carrier that is a product
  of a messenger and a composite of two clocks, each `freeShift` of a gate is a `coincShift`
  of #393, for which #394, #399 and #400 give the histories from where the carriers are;
  that step is not taken here.
* **Any carrier and any five Hermitian observables.** Nothing here uses three carriers, the
  chain, the walls or coincidence gates; the five observables are arbitrary.
* **Only the fibres where all five profiles vanish.** There the carrier is not acted on by
  the pointers. This is a null set of fibres (R7 of the list is untouched).
* **Conditional as #402**: the five histories, the four times with their relations and
  tolerances, and the rate of the moving clock are hypotheses. R2 to R7 are untouched.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md` (UA-18,
UO-16, UD-139, UD-145, UD-163, UD-164, UD-167, UD-168); `LF4/PentaCoupledFlow.lean` (#389:
`fiveCoupledFlow`, `fiveCoupledFlow_fst_of_lift_eq_zero`,
`fiveCoupledFlow_snd_of_lift_eq_zero`); `LF4/QuadCoupledFlow.lean`,
`LF4/TriCoupledFlow.lean`, `LF4/EchoVolume.lean` (`twoCoupledFlow_apply`);
`RecordLayer/UnifiedRadarSkeleton.lean` (#402: `radar_lorentz_of_histories`);
`RecordLayer/UnifiedDiracClock.lean` (`idxArenaEquiv_kick`, `schrodingerHamiltonian_reindex`,
`idxFreeU`); `RecordLayer/UnifiedCoincidenceFlow.lean` (#393: `coincShift`).
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Projectivization Matrix.UnitaryGroup MeasureTheory NormedSpace Set
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator LinearAlgebra.Projectivization
open scoped Topology

namespace CSD.RecordLayer

/-! ### The flows on the fibres where the profiles vanish -/

section Fibre

variable {N : ℕ} {f g k l r : ℝ → ℝ} {A BA BB BC BD BE : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}

/-- **A pointer's turning along the uncoupled orbit**: `z` times the accumulated `−2⟨B⟩` along
the Schrödinger orbit of `A` from the ray `x`. -/
def freeTurn (hA : A.IsHermitian) (B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (z : ℝ)
    (x : CPN (N + 1)) (t : ℝ) : ℝ :=
  z * ∫ u in (0 : ℝ)..t, schrodingerHamiltonian B (Matrix.schrodingerUnitary hA u • x)

/-- On the fibre where both profiles vanish the two-pointer matrix is the uncoupled one. -/
theorem twoCoupledMatrix_of_lift_eq_zero (hf : Function.Periodic f 1)
    (hg : Function.Periodic g 1) {φ ψ : AddCircle (1 : ℝ)} (hφ : hf.lift φ = 0)
    (hψ : hg.lift ψ = 0) : twoCoupledMatrix A BA BB hf hg φ ψ = A := by
  rw [twoCoupledMatrix, coupledMatrix, hφ, hψ]
  simp

/-- **The two-pointer flow on the fibre where both profiles vanish.** -/
theorem twoCoupledFlow_of_lift_eq_zero (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (x : CPN (N + 1)) {θ ψ : KTorus}
    (hθ : hf.lift θ.2 = 0) (hψ : hg.lift ψ.2 = 0) (t : ℝ) :
    twoCoupledFlow A BA BB hf hg hc hcg t ((x, θ), ψ)
      = ((Matrix.schrodingerUnitary hA t • x,
          pshift (freeTurn hA BA (hf.deriv_periodic.lift θ.2) x t) θ),
         pshift (freeTurn hA BB (hg.deriv_periodic.lift ψ.2) x t) ψ) := by
  have hU := schrodingerUnitary_congr (twoCoupledMatrix_of_lift_eq_zero (A := A) (BA := BA)
    (BB := BB) hf hg hθ hψ) (twoCoupledMatrix_isHermitian hA hBA hBB hf hg θ.2 ψ.2) hA
  rw [twoCoupledFlow_apply hA hBA hBB hf hg hc hcg]
  simp only [twoAccumA, twoAccumB, hU]
  rfl

/-- **The three-pointer flow on the fibre where the three profiles vanish.** -/
theorem threeCoupledFlow_of_lift_eq_zero (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g)
    (hck : ContDiff ℝ ∞ k) (x : CPN (N + 1)) {θ ψ χ : KTorus} (hθ : hf.lift θ.2 = 0)
    (hψ : hg.lift ψ.2 = 0) (hχ : hk.lift χ.2 = 0) (t : ℝ) :
    threeCoupledFlow A BA BB BC hf hg hk hc hcg hck t (((x, θ), ψ), χ)
      = (((Matrix.schrodingerUnitary hA t • x,
            pshift (freeTurn hA BA (hf.deriv_periodic.lift θ.2) x t) θ),
          pshift (freeTurn hA BB (hg.deriv_periodic.lift ψ.2) x t) ψ),
         pshift (freeTurn hA BC (hk.deriv_periodic.lift χ.2) x t) χ) := by
  rw [threeCoupledFlow_apply]
  simp only [hχ, Complex.ofReal_zero, zero_smul, add_zero,
    twoCoupledFlow_of_lift_eq_zero hA hBA hBB hf hg hc hcg x hθ hψ]
  rfl

/-- **The four-pointer flow on the fibre where the four profiles vanish.** -/
theorem fourCoupledFlow_of_lift_eq_zero (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hc : ContDiff ℝ ∞ f)
    (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l) (x : CPN (N + 1))
    {θ ψ χ ξ : KTorus} (hθ : hf.lift θ.2 = 0) (hψ : hg.lift ψ.2 = 0) (hχ : hk.lift χ.2 = 0)
    (hξ : hl.lift ξ.2 = 0) (t : ℝ) :
    fourCoupledFlow A BA BB BC BD hf hg hk hl hc hcg hck hcl t ((((x, θ), ψ), χ), ξ)
      = ((((Matrix.schrodingerUnitary hA t • x,
              pshift (freeTurn hA BA (hf.deriv_periodic.lift θ.2) x t) θ),
            pshift (freeTurn hA BB (hg.deriv_periodic.lift ψ.2) x t) ψ),
           pshift (freeTurn hA BC (hk.deriv_periodic.lift χ.2) x t) χ),
         pshift (freeTurn hA BD (hl.deriv_periodic.lift ξ.2) x t) ξ) := by
  refine Prod.ext ?_ ?_
  · rw [fourCoupledFlow_fst_of_lift_eq_zero A BA BB BC BD hf hg hk hl hc hcg hck hcl t _ hξ,
      threeCoupledFlow_of_lift_eq_zero hA hBA hBB hf hg hk hc hcg hck x hθ hψ hχ]
  · rw [fourCoupledFlow_snd_of_lift_eq_zero A BA BB BC BD hf hg hk hl hc hcg hck hcl t _ hξ]
    simp only [triRayEnergy, echoRayEnergy,
      threeCoupledFlow_of_lift_eq_zero hA hBA hBB hf hg hk hc hcg hck x hθ hψ hχ]
    rfl

/-- ★★ **The five-pointer flow on the fibre where all five profiles vanish.** The ray moves by
the uncoupled Schrödinger unitary of `A`, and each pointer is turned by its profile's
derivative times the accumulated `−2⟨B⟩` of its own observable along that orbit. -/
theorem fiveCoupledFlow_of_lift_eq_zero (hA : A.IsHermitian) (hBA : BA.IsHermitian)
    (hBB : BB.IsHermitian) (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hr : Function.Periodic r 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k)
    (hcl : ContDiff ℝ ∞ l) (hcr : ContDiff ℝ ∞ r) (x : CPN (N + 1))
    {θ ψ χ ξ ζ : KTorus} (hθ : hf.lift θ.2 = 0) (hψ : hg.lift ψ.2 = 0) (hχ : hk.lift χ.2 = 0)
    (hξ : hl.lift ξ.2 = 0) (hζ : hr.lift ζ.2 = 0) (t : ℝ) :
    fiveCoupledFlow A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr t
        (((((x, θ), ψ), χ), ξ), ζ)
      = (((((Matrix.schrodingerUnitary hA t • x,
                pshift (freeTurn hA BA (hf.deriv_periodic.lift θ.2) x t) θ),
              pshift (freeTurn hA BB (hg.deriv_periodic.lift ψ.2) x t) ψ),
             pshift (freeTurn hA BC (hk.deriv_periodic.lift χ.2) x t) χ),
            pshift (freeTurn hA BD (hl.deriv_periodic.lift ξ.2) x t) ξ),
         pshift (freeTurn hA BE (hr.deriv_periodic.lift ζ.2) x t) ζ) := by
  refine Prod.ext ?_ ?_
  · rw [fiveCoupledFlow_fst_of_lift_eq_zero A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr
        t _ hζ,
      fourCoupledFlow_of_lift_eq_zero hA hBA hBB hf hg hk hl hc hcg hck hcl x hθ hψ hχ hξ]
  · rw [fiveCoupledFlow_snd_of_lift_eq_zero A BA BB BC BD BE hf hg hk hl hr hc hcg hck hcl hcr
        t _ hζ]
    simp only [quadRayEnergy, triRayEnergy, echoRayEnergy,
      fourCoupledFlow_of_lift_eq_zero hA hBA hBB hf hg hk hl hc hcg hck hcl x hθ hψ hχ hξ]
    rfl

end Fibre

/-! ### A carrier with any index type -/

section Indexed

variable {ν : Type*} [Fintype ν] [DecidableEq ν] {N : ℕ} (e : ν ≃ Fin (N + 1))
  {H : Matrix ν ν ℂ}

/-- The transported uncoupled orbit is the Schrödinger orbit of the reindexed matrix. -/
theorem idxArenaEquiv_kick_free (hH : H.IsHermitian) (t : ℝ) (p : GenArena ν) :
    idxArenaEquiv e (arenaKick (idxFreeU hH t) p)
      = Matrix.schrodingerUnitary (hH.reindex e) t • (idxArenaEquiv e p : CPN (N + 1)) := by
  have hf : Function.Periodic (fun _ : ℝ => (0 : ℝ)) 1 := fun _ => rfl
  have h0 : (0 : Matrix ν ν ℂ).IsHermitian := Matrix.isHermitian_zero
  have h := idxArenaEquiv_kick e hH h0 hf (0 : AddCircle (1 : ℝ)) t p
  have e1 : idxCarrierU hH h0 hf (0 : AddCircle (1 : ℝ)) t = idxFreeU hH t := by
    apply Subtype.ext
    rw [idxCarrierU_val, idxFreeU_val, idxCoupledH]
    simp
  have e2 : coupledMatrix (Matrix.reindex e e H) (Matrix.reindex e e (0 : Matrix ν ν ℂ)) hf
      (0 : AddCircle (1 : ℝ)) = Matrix.reindex e e H := by
    simp [coupledMatrix]
  rw [e1] at h
  rw [h, schrodingerUnitary_congr e2
    (coupledMatrix_isHermitian (hH.reindex e) (h0.reindex e) hf _) (hH.reindex e)]

/-- **A pointer's lifted displacement along the uncoupled orbit of a carrier**: `−2 z` times
the accumulated expectation of `G`, `z` the derivative of the pointer's profile at its
conserved angle. -/
def freeShift (hH : H.IsHermitian) (G : Matrix ν ν ℂ) (z : ℝ) (p : GenArena ν) (t : ℝ) : ℝ :=
  -2 * z * ∫ u in (0 : ℝ)..t, arenaObs G (arenaKick (idxFreeU hH u) p)

/-- The turning of the reindexed pointer is the displacement along the carrier's orbit. -/
theorem freeTurn_reindex (hH : H.IsHermitian) (G : Matrix ν ν ℂ) (z : ℝ) (p : GenArena ν)
    (t : ℝ) :
    freeTurn (hH.reindex e) (Matrix.reindex e e G) z (idxArenaEquiv e p) t
      = freeShift hH G z p t := by
  rw [freeTurn, freeShift]
  simp only [← idxArenaEquiv_kick_free e hH, schrodingerHamiltonian_reindex]
  rw [intervalIntegral.integral_const_mul]
  ring

variable {G₁ G₂ G₃ G₄ G₅ : Matrix ν ν ℂ} {f g k l r : ℝ → ℝ}

/-- ★★ **The five-pointer run of a carrier.** The flow of the five-pointer arena of UA-18 for
a carrier with any index type and five Hermitian observables, from a ray on the fibre where
all five profiles vanish: the carrier moves by its uncoupled propagator, and pointer `i` is
at `pshift (freeShift G_i z_i p t)` of its start. -/
theorem pentaRun_eq (hH : H.IsHermitian) (hG₁ : G₁.IsHermitian) (hG₂ : G₂.IsHermitian)
    (hf : Function.Periodic f 1) (hg : Function.Periodic g 1) (hk : Function.Periodic k 1)
    (hl : Function.Periodic l 1) (hr : Function.Periodic r 1) (hc : ContDiff ℝ ∞ f)
    (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k) (hcl : ContDiff ℝ ∞ l)
    (hcr : ContDiff ℝ ∞ r) (p : GenArena ν) {θ ψ χ ξ ζ : KTorus} (hθ : hf.lift θ.2 = 0)
    (hψ : hg.lift ψ.2 = 0) (hχ : hk.lift χ.2 = 0) (hξ : hl.lift ξ.2 = 0)
    (hζ : hr.lift ζ.2 = 0) (t : ℝ) :
    fiveCoupledFlow (Matrix.reindex e e H) (Matrix.reindex e e G₁) (Matrix.reindex e e G₂)
        (Matrix.reindex e e G₃) (Matrix.reindex e e G₄) (Matrix.reindex e e G₅)
        hf hg hk hl hr hc hcg hck hcl hcr t (((((idxArenaEquiv e p, θ), ψ), χ), ξ), ζ)
      = (((((idxArenaEquiv e (arenaKick (idxFreeU hH t) p),
                pshift (freeShift hH G₁ (hf.deriv_periodic.lift θ.2) p t) θ),
              pshift (freeShift hH G₂ (hg.deriv_periodic.lift ψ.2) p t) ψ),
             pshift (freeShift hH G₃ (hk.deriv_periodic.lift χ.2) p t) χ),
            pshift (freeShift hH G₄ (hl.deriv_periodic.lift ξ.2) p t) ξ),
         pshift (freeShift hH G₅ (hr.deriv_periodic.lift ζ.2) p t) ζ) := by
  rw [fiveCoupledFlow_of_lift_eq_zero (hH.reindex e) (hG₁.reindex e) (hG₂.reindex e) hf hg hk
    hl hr hc hcg hck hcl hcr _ hθ hψ hχ hξ hζ]
  rw [freeTurn_reindex e hH G₁, freeTurn_reindex e hH G₂, freeTurn_reindex e hH G₃,
    freeTurn_reindex e hH G₄, freeTurn_reindex e hH G₅, idxArenaEquiv_kick_free e hH]

/-! ### M6 from the top, on the five-pointer arena -/

/-- ★★★ **M6 from the top, for the flow of the five-pointer arena.** The flow of UA-18's
arena for a carrier with any index type and five Hermitian observables, from a ray on the
fibre where all five profiles vanish, the five pointers started at `1/12`. If the five
displacements `freeShift G_i` have the histories of `radar_lorentz_of_histories` (#402):
the first, third, fourth and fifth gated (`B`'s emission and meeting, `A`'s relay and
meeting), the second away (`B`'s return); with the rate and the times as there: then at every
choice of flow times in the five reading windows the five pointers have counts, and those
counts satisfy the Lorentz statement with the errors of #402. -/
theorem penta_radar_lorentz (hH : H.IsHermitian) (hG₁ : G₁.IsHermitian)
    (hG₂ : G₂.IsHermitian) (hf : Function.Periodic f 1) (hg : Function.Periodic g 1)
    (hk : Function.Periodic k 1) (hl : Function.Periodic l 1) (hr : Function.Periodic r 1)
    (hc : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) (hck : ContDiff ℝ ∞ k)
    (hcl : ContDiff ℝ ∞ l) (hcr : ContDiff ℝ ∞ r) (p : GenArena ν) {θ ψ χ ξ ζ : KTorus}
    (hθ : hf.lift θ.2 = 0) (hψ : hg.lift ψ.2 = 0) (hχ : hk.lift χ.2 = 0)
    (hξ : hl.lift ξ.2 = 0) (hζ : hr.lift ζ.2 = 0)
    (hθ1 : rep θ.1 = 1 / 12) (hψ1 : rep ψ.1 = 1 / 12) (hχ1 : rep χ.1 = 1 / 12)
    (hξ1 : rep ξ.1 = 1 / 12) (hζ1 : rep ζ.1 = 1 / 12)
    {v R₀ RB κ TE TR TRet TM tE tR tRet tMB tMA τE τR τRet τMB τMA : ℝ}
    {δe ve tbe tce c vr η₀ η t4 t5 δμ vμ tbμ tcμ δρ vρ tbρ tcρ δm vm tbm tcm : ℝ}
    (hv0 : 0 ≤ v) (hv : v < 1) (hR₀ : 0 < R₀)
    (hκ : |RB - Real.sqrt (1 - v ^ 2) * R₀| ≤ κ * R₀)
    (hE : TR - TE = v * (TM - TE)) (hRet : TRet - TR = v * (TM - TRet))
    (hτE : |tE - TE| ≤ τE) (hτRet : |tRet - TRet| ≤ τRet) (hτMB : |tMB - TM| ≤ τMB)
    (hτR : |tR - TR| ≤ τR) (hτMA : |tMA - TM| ≤ τMA)
    (He : IsGatedHistory (freeShift hH G₁ (hf.deriv_periodic.lift θ.2) p) RB δe ve tE tbe tce)
    (Hr : IsAwayHistory (freeShift hH G₂ (hg.deriv_periodic.lift ψ.2) p) RB c vr η₀ η tE tbe
      tRet t4 t5)
    (Hμ : IsGatedHistory (freeShift hH G₃ (hk.deriv_periodic.lift χ.2) p) RB δμ vμ tMB tbμ
      tcμ)
    (Hρ : IsGatedHistory (freeShift hH G₄ (hl.deriv_periodic.lift ξ.2) p) R₀ δρ vρ tR tbρ
      tcρ)
    (Hm : IsGatedHistory (freeShift hH G₅ (hr.deriv_periodic.lift ζ.2) p) R₀ δm vm tMA tbm
      tcm) :
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
  have key := pentaRun_eq (G₃ := G₃) (G₄ := G₄) (G₅ := G₅) e hH hG₁ hG₂ hf hg hk hl hr hc hcg
    hck hcl hcr p hθ hψ hχ hξ hζ
  exact radar_lorentz_of_histories (X := PentaSigma N)
    (πe := fun x => x.1.1.1.1.2) (πr := fun x => x.1.1.1.2) (πμ := fun x => x.1.1.2)
    (πρ := fun x => x.1.2) (πm := fun x => x.2)
    (γ := fun t => fiveCoupledFlow (Matrix.reindex e e H) (Matrix.reindex e e G₁)
      (Matrix.reindex e e G₂) (Matrix.reindex e e G₃) (Matrix.reindex e e G₄)
      (Matrix.reindex e e G₅) hf hg hk hl hr hc hcg hck hcl hcr t
      (((((idxArenaEquiv e p, θ), ψ), χ), ξ), ζ))
    hv0 hv hR₀ hκ hE hRet hτE hτRet hτMB hτR hτMA hθ1 hψ1 hχ1 hξ1 hζ1
    (fun t _ _ => by
      show (fiveCoupledFlow _ _ _ _ _ _ hf hg hk hl hr hc hcg hck hcl hcr t _).1.1.1.1.2 = _
      rw [key t])
    (fun t _ _ => by
      show (fiveCoupledFlow _ _ _ _ _ _ hf hg hk hl hr hc hcg hck hcl hcr t _).1.1.1.2 = _
      rw [key t])
    (fun t _ _ => by
      show (fiveCoupledFlow _ _ _ _ _ _ hf hg hk hl hr hc hcg hck hcl hcr t _).1.1.2 = _
      rw [key t])
    (fun t _ _ => by
      show (fiveCoupledFlow _ _ _ _ _ _ hf hg hk hl hr hc hcg hck hcl hcr t _).1.2 = _
      rw [key t])
    (fun t _ _ => by
      show (fiveCoupledFlow _ _ _ _ _ _ hf hg hk hl hr hc hcg hck hcl hcr t _).2 = _
      rw [key t])
    He Hr Hμ Hρ Hm

end Indexed

end CSD.RecordLayer

end
