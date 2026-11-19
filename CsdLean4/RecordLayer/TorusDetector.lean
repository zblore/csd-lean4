/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.GraphDetector
public import CsdLean4.RecordLayer.DiracArrival
public import CsdLean4.CV.DiracPacketWindowD

/-!
# A detector on the torus displays a packet that stays in its box

**Category:** 7-SigmaLayer. BACKLOG #297, third brick (Task 9 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream S; plan
`specs/unified-records-spacetime-task-plans.md` §7, item 3).

`RecordLayer/GraphDetector.lean` shows a detector displays when the occupancy of its sites
stays above `q`, as a hypothesis. Here the hypothesis is met by a packet of the lattice Dirac
field of any dimension, from the box weights of `CV/DiracPacketWindowD.lean`.

* ★★ `exp_mulVec_packetD` — the propagator `exp (−i t H)` carries the packet at `0` to the
  packet at `t`;
* ★★ `arenaObs_siteSetProj_mk` — the expectation of the projector on a set of sites at the
  ray of a vector is the vector's weight on those sites over its norm;
* ★★ `arenaObs_siteSetProj_packetD` — along the free orbit of a packet's ray the occupancy
  of a set of sites is the packet's weight on it over its norm;
* ★★★ `torusDetector_displayed_of_packet` — on a fibre where the profile vanishes and the
  rate `κ = −2 f'(θ₂)` is non-negative, a ready pointer coupled to the projector on `X` is
  displayed at `t` when the packet keeps a fraction `q` of its weight on `X` up to `t`,
  `1/3 ≤ κ q t` and `κ t ≤ 2/3`;
* ★★★ `torusDetector_displayed_flatPacket` — for the flat packet of UD-222, whose moving box
  stays inside `X` up to `t`, with
  `q = 1 − Σ_i (1/N_i + η + t (2π/L) windowStepErrD_i) / (1 − γ_i)`.

## Honest scope

⚠️ **On the fibres where the profile vanishes.** There the carrier moves freely. They are a
null set of the pointer's conserved angle. Off them the detector's own coupling acts on the
packet and nothing is said here.

⚠️ **The packet must stay in the detector's box for the whole write**, from flow time `0` to
`t`. A packet that arrives from outside is not treated: the window from arrival to display
is not composed with `torusDetector_not_displayed`.

⚠️ **A display at one time, not a tick count.** No `TickReadout` for this arena.

⚠️ **Flow times.**

References: `specs/BACKLOG.md` #297, #296; `specs/unified-record-spacetime-plan.md` (UD-221,
UD-222, UD-231, UD-234); `specs/unified-records-spacetime-task-plans.md` (§7);
`RecordLayer/GraphDetector.lean` (`graphDetector_displayed`, `siteSetProj`);
`RecordLayer/DiracArrival.lean` (`exp_mulVec_of_mulVec_eq_smul`); `CV/DiracPacketD.lean`
(`packetD`, `dispE_modeSD_castZ`); `CV/DiracPacketWindowD.lean`
(`regionWeightD_flatPacket_compl_movedBoxD_le_window`); `CV/DiracPacketBoxD.lean`
(`regionWeightD`, `regionWeightD_add_compl`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 Matrix NormedSpace
open scoped Manifold ContDiff Matrix.Norms.L2Operator

namespace CSD.RecordLayer

variable {κ S : Type*} [Fintype κ] [DecidableEq κ] [Fintype S] [DecidableEq S] {L : ℕ}
  [NeZero L] {α : κ → Matrix S S ℂ} {β : Matrix S S ℂ}

/-- ★★ **The propagator carries a packet**: `exp (−i t H)` applied to the packet at flow time
`0` is the packet at `t`. -/
theorem exp_mulVec_packetD (h : IsCliffordFamily α β) (J μ : ℝ) (e₀ : S → ℂ)
    (W : Finset (κ → ℤ)) (c : (κ → ℤ) → ℂ) (t : ℝ) :
    exp (t • ((-Complex.I) • latticeDiracHam (L := L) α β J μ))
        *ᵥ packetD (L := L) α β J μ e₀ W c 0
      = packetD (L := L) α β J μ e₀ W c t := by
  unfold packetD
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hm : (t • ((-Complex.I) • latticeDiracHam (L := L) α β J μ))
        *ᵥ diracModeD α β J μ (castZ L m) e₀
      = (-(Complex.I * latticeED J μ (angleZD L m)) * t)
        • diracModeD α β J μ (castZ L m) e₀ := by
    rw [← smul_assoc, Complex.real_smul, Matrix.smul_mulVec,
      latticeDiracHam_mulVec_diracModeD h, dispE_modeSD_castZ, smul_smul]
    congr 1
    ring
  rw [Matrix.mulVec_smul, exp_mulVec_of_mulVec_eq_smul hm, smul_smul,
    ← Complex.exp_eq_exp_ℂ]
  congr 1
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]

/-- ★★ **The occupancy of a set of sites at the ray of a vector** is the vector's weight on
those sites over its norm. -/
theorem arenaObs_siteSetProj_mk (X : Finset (κ → ZMod L))
    [DecidablePred (· ∈ (X : Set (κ → ZMod L)))]
    {v : EuclideanSpace ℂ ((κ → ZMod L) × S)} (hv : v ≠ 0) :
    arenaObs (siteSetProj Prod.fst (X : Set (κ → ZMod L))) (Projectivization.mk ℂ v hv)
      = regionWeightD (fun p => v p) X / ‖v‖ ^ 2 := by
  have hterm : ∀ p : (κ → ZMod L) × S,
      (inner ℂ (v p)
        (Matrix.toEuclideanLin (siteSetProj Prod.fst (X : Set (κ → ZMod L))) v p)).re
        = if p.1 ∈ X then ‖v p‖ ^ 2 else 0 := fun p => by
    rw [toEuclideanLin_coord, siteSetProj, Matrix.mulVec_diagonal]
    by_cases hp : p.1 ∈ X
    · have hp' : p.1 ∈ (X : Set (κ → ZMod L)) := hp
      simp only [hp, hp', ↓reduceIte, one_mul]
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    · have hp' : p.1 ∉ (X : Set (κ → ZMod L)) := hp
      simp only [hp, hp', ↓reduceIte, zero_mul, inner_zero_right, Complex.zero_re]
  rw [arenaObs_mk_eq_inner]
  congr 1
  rw [PiLp.inner_apply, Complex.re_sum]
  simp only [hterm]
  rw [Fintype.sum_prod_type, regionWeightD]
  calc ∑ x, ∑ s, (if x ∈ X then ‖v (x, s)‖ ^ 2 else 0)
      = ∑ x, if x ∈ X then siteWeightD (fun p => v p) x else 0 :=
        Finset.sum_congr rfl fun x _ => by
          by_cases hx : x ∈ X <;> simp [hx, siteWeightD]
    _ = ∑ x ∈ X, siteWeightD (fun p => v p) x := by
        rw [← Finset.sum_subset (Finset.subset_univ X) (fun x _ hx => by simp [hx])]
        exact Finset.sum_congr rfl fun x hx => by simp [hx]

/-- ★★ **Along the free orbit of a packet's ray the occupancy of a set of sites is the
packet's weight on it over its norm.** -/
theorem arenaObs_siteSetProj_packetD (h : IsCliffordFamily α β) (J μ : ℝ) (e₀ : S → ℂ)
    (W : Finset (κ → ℤ)) (c : (κ → ℤ) → ℂ)
    (hp : (WithLp.toLp 2 (packetD (L := L) α β J μ e₀ W c 0) :
      EuclideanSpace ℂ ((κ → ZMod L) × S)) ≠ 0)
    (X : Finset (κ → ZMod L)) [DecidablePred (· ∈ (X : Set (κ → ZMod L)))] (s : ℝ) :
    arenaObs (siteSetProj Prod.fst (X : Set (κ → ZMod L)))
        (arenaKick (idxFreeU (latticeDiracHam_isHermitian h J μ) s)
          (Projectivization.mk ℂ _ hp))
      = regionWeightD (packetD (L := L) α β J μ e₀ W c s) X
        / (chainInnerD (packetD (L := L) α β J μ e₀ W c 0)
            (packetD (L := L) α β J μ e₀ W c 0)).re := by
  have hU : ((idxFreeU (latticeDiracHam_isHermitian (L := L) h J μ) s).val)ᴴ
      * (idxFreeU (latticeDiracHam_isHermitian (L := L) h J μ) s).val = 1 := by
    have hmem := (idxFreeU (latticeDiracHam_isHermitian (L := L) h J μ) s).property
    rwa [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hmem
  rw [arenaKick_mk _ hp, arenaObs_siteSetProj_mk, Matrix.norm_toEuclideanLin_of_isom hU,
    EuclideanSpace.norm_sq_eq, re_chainInnerD_self]
  congr 2
  funext p
  rw [toEuclideanLin_coord, idxFreeU_val]
  exact congrFun (exp_mulVec_packetD h J μ e₀ W c s) p

variable {f : ℝ → ℝ} {N : ℕ} [Nonempty S]

/-- ★★★ **A detector on the torus displays a packet that stays on its sites.** The pointer
is coupled to the projector on the sites `X`. On a fibre where the profile vanishes and the
rate `κ = −2 f'(θ₂)` is non-negative, from a ready pointer and the ray of a packet: if the
packet keeps at least the fraction `q` of its weight on `X` at every flow time up to `t ≥ 0`,
with `1/3 ≤ κ q t` and `κ t ≤ 2/3`, the pointer is displayed at `t`. -/
theorem torusDetector_displayed_of_packet (e : (κ → ZMod L) × S ≃ Fin (N + 1))
    (h : IsCliffordFamily α β) (J μ : ℝ) (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f)
    (e₀ : S → ℂ) (W : Finset (κ → ℤ)) (c : (κ → ℤ) → ℂ)
    (hp : (WithLp.toLp 2 (packetD (L := L) α β J μ e₀ W c 0) :
      EuclideanSpace ℂ ((κ → ZMod L) × S)) ≠ 0)
    (X : Finset (κ → ZMod L)) [DecidablePred (· ∈ (X : Set (κ → ZMod L)))] {θ : KTorus}
    (hθ : θ ∈ readyArc 2) (h0 : hf.lift θ.2 = 0)
    (hκ : 0 ≤ -2 * hf.deriv_periodic.lift θ.2) {q t : ℝ} (ht : 0 ≤ t)
    (hq : ∀ s, 0 ≤ s → s ≤ t →
      q * (chainInnerD (packetD (L := L) α β J μ e₀ W c 0)
          (packetD (L := L) α β J μ e₀ W c 0)).re
        ≤ regionWeightD (packetD (L := L) α β J μ e₀ W c s) X)
    (hlo : 1 / 3 ≤ -2 * hf.deriv_periodic.lift θ.2 * q * t)
    (hhi : -2 * hf.deriv_periodic.lift θ.2 * t ≤ 2 / 3) :
    ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy (Matrix.reindex e e (latticeDiracHam (L := L) α β J μ))
          (Matrix.reindex e e (siteSetProj Prod.fst (X : Set (κ → ZMod L)))) hf hc) t
        (idxArenaEquiv e (Projectivization.mk ℂ _ hp), θ)).2 ∈ displayArc := by
  have hn0 : 0 < (chainInnerD (packetD (L := L) α β J μ e₀ W c 0)
      (packetD (L := L) α β J μ e₀ W c 0)).re := by
    rw [re_chainInnerD_self, ← EuclideanSpace.norm_sq_eq
      (WithLp.toLp 2 (packetD (L := L) α β J μ e₀ W c 0))]
    exact pow_pos (norm_pos_iff.2 hp) 2
  refine graphDetector_displayed e (latticeDiracHam_isHermitian h J μ)
    (siteSetProj_isHermitian _ _) hf hc hθ hκ ht (fun s hs hst => ?_) (fun s _ _ => ?_)
    hlo hhi
  · rw [idxCarrierU_of_lift_eq_zero _ _ hf h0, arenaObs_siteSetProj_packetD h J μ e₀ W c hp,
      le_div_iff₀ hn0]
    exact hq s hs hst
  · exact (le_abs_self _).trans ((abs_arenaObs_le _ _).trans (norm_siteSetProj_le _ _))

/-- ★★★ **A detector on the torus displays the flat packet whose box stays inside it.** For
the flat packet of the lattice Dirac field with `μ > 0` on a window of `N_i < L` momenta per
axis within `w_i` of `k₀`, and a detector on sites `X` that contain the packet's moving box
at every flow time up to `t ≥ 0`: on a fibre where the profile vanishes and
`κ = −2 f'(θ₂) ≥ 0`, a ready pointer is displayed at `t` when `1/3 ≤ κ q t` and `κ t ≤ 2/3`,
with `q = 1 − Σ_i (1/N_i + η + t (2π/L) windowStepErrD_i) / (1 − γ_i)`. -/
theorem torusDetector_displayed_flatPacket (e : (κ → ZMod L) × S ≃ Fin (N + 1))
    (h : IsCliffordFamily α β) {e₀ : S → ℂ} (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1)
    {J μ : ℝ} (hμ : 0 < μ) (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f)
    (lo : κ → ℤ) {Nw : κ → ℕ} (hN : ∀ j, 0 < Nw j) (hNL : ∀ j, Nw j < L) (k₀ : κ → ℝ)
    {w : κ → ℝ} (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ m ∈ boxWindowD lo Nw, ∀ j, |angleZD L m j - k₀ j| ≤ w j) {γ : κ → ℝ}
    (hγ : ∀ i, γ i < 1)
    (hp : (WithLp.toLp 2 (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
      (unitAmpD L J μ (flatAmpD lo Nw)) 0) : EuclideanSpace ℂ ((κ → ZMod L) × S)) ≠ 0)
    (X : Finset (κ → ZMod L)) [DecidablePred (· ∈ (X : Set (κ → ZMod L)))] {θ : KTorus}
    (hθ : θ ∈ readyArc 2) (h0 : hf.lift θ.2 = 0)
    (hκ : 0 ≤ -2 * hf.deriv_periodic.lift θ.2) {t : ℝ} (ht : 0 ≤ t)
    (hbox : ∀ s, 0 ≤ s → s ≤ t → movedBoxD L J μ k₀ (fun _ => 1) γ s ⊆ X)
    (hlo : 1 / 3 ≤ -2 * hf.deriv_periodic.lift θ.2
      * (1 - ∑ i, (1 / Nw i + alignDefect L J μ
          + t * (2 * Real.pi / L * windowStepErrD J μ w i (2 * Real.pi / L))) / (1 - γ i)) * t)
    (hhi : -2 * hf.deriv_periodic.lift θ.2 * t ≤ 2 / 3) :
    ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy (Matrix.reindex e e (latticeDiracHam (L := L) α β J μ))
          (Matrix.reindex e e (siteSetProj Prod.fst (X : Set (κ → ZMod L)))) hf hc) t
        (idxArenaEquiv e (Projectivization.mk ℂ _ hp), θ)).2 ∈ displayArc := by
  obtain ⟨-, hD⟩ := noWrapD_distinctD_of_box (L := L) (W := boxWindowD lo Nw) (lo := lo)
    (fun m hm j => by
      have a := (Fintype.mem_piFinset.1 hm) j
      have b := hNL j
      simp only [Finset.mem_Ico] at a
      omega)
  have hnorm : ∀ s : ℝ, (chainInnerD
      (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw) (unitAmpD L J μ (flatAmpD lo Nw)) s)
      (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw) (unitAmpD L J μ (flatAmpD lo Nw)) s)).re
        = 1 := fun s => by
    rw [chainInnerD_packetD_unitAmpD h he hn hμ hD, sum_flatAmpD_sq lo hN, Complex.ofReal_re]
  refine torusDetector_displayed_of_packet e h J μ hf hc e₀ _ _ hp X hθ h0 hκ ht
    (fun s hs hst => ?_) hlo hhi
  rw [hnorm 0, mul_one]
  have hcompl := regionWeightD_flatPacket_compl_movedBoxD_le_window (L := L) (J := J) h he hn hμ
    lo hN hNL k₀ hw0 hw s hγ
  have hsplit := regionWeightD_add_compl
    (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw) (unitAmpD L J μ (flatAmpD lo Nw)) s)
    (movedBoxD L J μ k₀ (fun _ => 1) γ s)
  rw [hnorm s] at hsplit
  have hmono := regionWeightD_mono
    (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw) (unitAmpD L J μ (flatAmpD lo Nw)) s)
    (hbox s hs hst)
  have hsum : ∑ i, (1 / (Nw i : ℝ) + alignDefect L J μ
        + |s| * (2 * Real.pi / L * windowStepErrD J μ w i (2 * Real.pi / L))) / (1 - γ i)
      ≤ ∑ i, (1 / (Nw i : ℝ) + alignDefect L J μ
        + t * (2 * Real.pi / L * windowStepErrD J μ w i (2 * Real.pi / L))) / (1 - γ i) := by
    refine Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_right ?_ (sub_pos.2 (hγ i)).le
    have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have h2 : 0 ≤ 2 * Real.pi / L := div_nonneg (by positivity) hL.le
    have hc0 : 0 ≤ 2 * Real.pi / L * windowStepErrD J μ w i (2 * Real.pi / L) :=
      mul_nonneg h2 (windowStepErrD_nonneg hμ hw0 i h2)
    rw [abs_of_nonneg hs]
    have := mul_le_mul_of_nonneg_right hst hc0
    linarith
  linarith

end CSD.RecordLayer

end
