/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TorusArrivalBox
public import CsdLean4.RecordLayer.UnifiedGatedReading

/-!
# The flat packet's occupancy of a set of sites, as lemmas

**Category:** 7-SigmaLayer (the record layer). BACKLOG #437 (obligation UO-26, the mechanism
of UA-22; link L2 of the skeleton, `specs/unified-record-spacetime-plan.md` §9.4; route (γ5c)
of the task plans).

The statements about the released return (UD-276, UD-279) take bounds on a carrier's free
occupancy of a set of sites as hypotheses. For the flat packet of the lattice Dirac field
those bounds were proved inside `torusDetector_arrival_flatPacket` (UD-243) and were not
statements of their own. Here they are:

* `arenaObs_siteSetProj`, ★ `arenaObs_siteSetProj_nonneg`, ★ `arenaObs_siteSetProj_le_one` —
  the occupancy of a set of sites is in `[0, 1]` **at every ray**, for any site map;
* `re_chainInnerD_flatPacket`, `arenaObs_siteSetProj_flatPacket` — along the free orbit of
  the flat packet's ray the occupancy is the packet's weight on the sites;
* ★★ `arenaObs_flatPacket_le_of_disjoint` — at most `flatTailD s` while the moving box misses
  the sites;
* ★★ `le_arenaObs_flatPacket_of_subset` — at least `1 − flatTailD s` while the moving box
  lies in them;
* ★★★ `arenaObs_arrivalBox_le`, ★★★ `le_arenaObs_arrivalBox` — **for the packet and the box
  of UD-245 (`L = 8M`, `M ≥ 4·10⁶`): at most `1/10` up to the free time `M/4`, at least
  `9/10` from `M` to `2M`.**

## Honest scope

⚠️ **Nothing new about the packet.** These are the estimates of UD-243 and UD-245 restated
as lemmas about `arenaObs` along `idxFreeU`, the form the released return's hypotheses have.

⚠️ **Free times.** The time `s` is the carrier's own free time. In the released return it
is the clock `returnClock`, not the flow time.

⚠️ **No instance of the released return here.** That is route (γ5d).

References: `specs/BACKLOG.md` #437; `specs/unified-record-spacetime-plan.md` (UA-22, UO-26,
UD-243, UD-245, UD-276, UD-279, UD-281); `specs/unified-records-spacetime-task-plans.md`
(§9, route (γ5c)); `RecordLayer/TorusArrival.lean` (`torusDetector_arrival_flatPacket`,
`flatTailD`); `RecordLayer/TorusArrivalBox.lean` (`arrivalBox`,
`arrivalBox_disjoint_movedBoxD`, `movedBoxD_subset_arrivalBox`);
`RecordLayer/TorusArrivalInstance.lean` (`flatTailD_instance_le`);
`RecordLayer/TorusDetector.lean` (`arenaObs_siteSetProj_packetD`);
`RecordLayer/UnifiedReleasedBounds.lean` (`returnDetectorShift_le_of_clock`,
`le_returnDetectorShift_of_clock`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 CSD.SigmaLayer Matrix Set MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator

namespace CSD.RecordLayer

/-! ### A set of sites, at every ray -/

section SiteSet

variable {V n : Type*} [Fintype n] [DecidableEq n]

/-- The occupancy of a set of sites is the sum of the moment coordinates of the indices on
it. -/
theorem arenaObs_siteSetProj (σ : n → V) (X : Set V) [DecidablePred (· ∈ X)]
    (p : GenArena n) :
    arenaObs (siteSetProj σ X) p = ∑ i, if σ i ∈ X then momentMap p i else 0 := by
  have hc : (fun i : n => if σ i ∈ X then (1 : ℂ) else 0)
      = fun i => (((if σ i ∈ X then (1 : ℝ) else 0 : ℝ)) : ℂ) := by
    funext i
    split_ifs <;> simp
  rw [siteSetProj, hc, arenaObs_diagonal_ofReal]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- ★ The occupancy of a set of sites is not negative, at every ray. -/
theorem arenaObs_siteSetProj_nonneg (σ : n → V) (X : Set V) [DecidablePred (· ∈ X)]
    (p : GenArena n) : 0 ≤ arenaObs (siteSetProj σ X) p := by
  rw [arenaObs_siteSetProj]
  refine Finset.sum_nonneg fun i _ => ?_
  split_ifs
  · exact momentMap_nonneg p i
  · exact le_rfl

/-- ★ The occupancy of a set of sites is at most `1`, at every ray. -/
theorem arenaObs_siteSetProj_le_one (σ : n → V) (X : Set V) [DecidablePred (· ∈ X)]
    (p : GenArena n) : arenaObs (siteSetProj σ X) p ≤ 1 := by
  rw [arenaObs_siteSetProj, ← momentMap_sum_eq_one p]
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs
  · exact le_rfl
  · exact momentMap_nonneg p i

end SiteSet

/-! ### The flat packet on the torus -/

section Torus

variable {κ S : Type*} [Fintype κ] [DecidableEq κ] [Fintype S] [DecidableEq S] {L : ℕ}
  [NeZero L] {α : κ → Matrix S S ℂ} {β : Matrix S S ℂ}

/-- The flat packet has norm `1` at every time. -/
theorem re_chainInnerD_flatPacket (h : IsCliffordFamily α β) {e₀ : S → ℂ}
    (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1) {J μ : ℝ} (hμ : 0 < μ) (lo : κ → ℤ)
    {Nw : κ → ℕ} (hN : ∀ j, 0 < Nw j) (hNL : ∀ j, Nw j < L) (s : ℝ) :
    (chainInnerD
      (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw) (unitAmpD L J μ (flatAmpD lo Nw)) s)
      (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw) (unitAmpD L J μ (flatAmpD lo Nw)) s)).re
        = 1 := by
  obtain ⟨-, hD⟩ := noWrapD_distinctD_of_box (L := L) (W := boxWindowD lo Nw) (lo := lo)
    (fun m hm j => by
      have a := (Fintype.mem_piFinset.1 hm) j
      have b := hNL j
      simp only [Finset.mem_Ico] at a
      omega)
  rw [chainInnerD_packetD_unitAmpD h he hn hμ hD, sum_flatAmpD_sq lo hN, Complex.ofReal_re]

/-- Along the free orbit of the flat packet's ray, the occupancy of a set of sites is the
packet's weight on it. -/
theorem arenaObs_siteSetProj_flatPacket (h : IsCliffordFamily α β) {e₀ : S → ℂ}
    (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1) {J μ : ℝ} (hμ : 0 < μ) (lo : κ → ℤ)
    {Nw : κ → ℕ} (hN : ∀ j, 0 < Nw j) (hNL : ∀ j, Nw j < L)
    (hp : (WithLp.toLp 2 (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
      (unitAmpD L J μ (flatAmpD lo Nw)) 0) : EuclideanSpace ℂ ((κ → ZMod L) × S)) ≠ 0)
    (X : Finset (κ → ZMod L)) [DecidablePred (· ∈ (X : Set (κ → ZMod L)))] (s : ℝ) :
    arenaObs (siteSetProj Prod.fst (X : Set (κ → ZMod L)))
        (arenaKick (idxFreeU (latticeDiracHam_isHermitian (L := L) h J μ) s)
          (Projectivization.mk ℂ _ hp))
      = regionWeightD (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
          (unitAmpD L J μ (flatAmpD lo Nw)) s) X := by
  rw [arenaObs_siteSetProj_packetD h J μ e₀ _ _ hp X s,
    re_chainInnerD_flatPacket h he hn hμ lo hN hNL 0, div_one]

/-- ★★ **While the moving box misses the sites, the flat packet's occupancy of them is at
most the tail.** At a free time `s ≥ 0`. -/
theorem arenaObs_flatPacket_le_of_disjoint (h : IsCliffordFamily α β) {e₀ : S → ℂ}
    (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1) {J μ : ℝ} (hμ : 0 < μ) (lo : κ → ℤ)
    {Nw : κ → ℕ} (hN : ∀ j, 0 < Nw j) (hNL : ∀ j, Nw j < L) (k₀ : κ → ℝ) {w : κ → ℝ}
    (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ m ∈ boxWindowD lo Nw, ∀ j, |angleZD L m j - k₀ j| ≤ w j) {γ : κ → ℝ}
    (hγ : ∀ i, γ i < 1)
    (hp : (WithLp.toLp 2 (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
      (unitAmpD L J μ (flatAmpD lo Nw)) 0) : EuclideanSpace ℂ ((κ → ZMod L) × S)) ≠ 0)
    (X : Finset (κ → ZMod L)) [DecidablePred (· ∈ (X : Set (κ → ZMod L)))] {s : ℝ}
    (hs : 0 ≤ s) (hout : Disjoint X (movedBoxD L J μ k₀ (fun _ => 1) γ s)) :
    arenaObs (siteSetProj Prod.fst (X : Set (κ → ZMod L)))
        (arenaKick (idxFreeU (latticeDiracHam_isHermitian (L := L) h J μ) s)
          (Projectivization.mk ℂ _ hp))
      ≤ flatTailD L J μ Nw w γ s := by
  rw [arenaObs_siteSetProj_flatPacket h he hn hμ lo hN hNL hp X s]
  have hh := regionWeightD_flatPacket_compl_movedBoxD_le_window (L := L) (J := J) h he hn hμ
    lo hN hNL k₀ hw0 hw s hγ
  rw [abs_of_nonneg hs] at hh
  rw [flatTailD]
  exact (regionWeightD_mono _ (le_compl_iff_disjoint_right.2 hout)).trans hh

/-- ★★ **While the moving box lies in the sites, the flat packet's occupancy of them is at
least `1` less the tail.** At a free time `s ≥ 0`. -/
theorem le_arenaObs_flatPacket_of_subset (h : IsCliffordFamily α β) {e₀ : S → ℂ}
    (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1) {J μ : ℝ} (hμ : 0 < μ) (lo : κ → ℤ)
    {Nw : κ → ℕ} (hN : ∀ j, 0 < Nw j) (hNL : ∀ j, Nw j < L) (k₀ : κ → ℝ) {w : κ → ℝ}
    (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ m ∈ boxWindowD lo Nw, ∀ j, |angleZD L m j - k₀ j| ≤ w j) {γ : κ → ℝ}
    (hγ : ∀ i, γ i < 1)
    (hp : (WithLp.toLp 2 (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
      (unitAmpD L J μ (flatAmpD lo Nw)) 0) : EuclideanSpace ℂ ((κ → ZMod L) × S)) ≠ 0)
    (X : Finset (κ → ZMod L)) [DecidablePred (· ∈ (X : Set (κ → ZMod L)))] {s : ℝ}
    (hs : 0 ≤ s) (hin : movedBoxD L J μ k₀ (fun _ => 1) γ s ⊆ X) :
    1 - flatTailD L J μ Nw w γ s
      ≤ arenaObs (siteSetProj Prod.fst (X : Set (κ → ZMod L)))
        (arenaKick (idxFreeU (latticeDiracHam_isHermitian (L := L) h J μ) s)
          (Projectivization.mk ℂ _ hp)) := by
  rw [arenaObs_siteSetProj_flatPacket h he hn hμ lo hN hNL hp X s]
  have hh := regionWeightD_flatPacket_compl_movedBoxD_le_window (L := L) (J := J) h he hn hμ
    lo hN hNL k₀ hw0 hw s hγ
  rw [abs_of_nonneg hs] at hh
  have hsplit := regionWeightD_add_compl (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
    (unitAmpD L J μ (flatAmpD lo Nw)) s) (movedBoxD L J μ k₀ (fun _ => 1) γ s)
  rw [re_chainInnerD_flatPacket h he hn hμ lo hN hNL s] at hsplit
  have hm := regionWeightD_mono (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
    (unitAmpD L J μ (flatAmpD lo Nw)) s) hin
  rw [flatTailD]
  linarith

end Torus

/-! ### The packet and the box of the arrival instance -/

section Box

variable {L : ℕ} [NeZero L]

/-- ★★★ **Up to the free time `M/4` the packet of UD-245 has at most `1/10` of its weight on
`arrivalBox`.** Two dimensions, `L = 8M` sites per axis with `M ≥ 4·10⁶`, `J = 2`, `μ = 1`,
`σ_x`, `σ_y` with `σ_z`, the flat packet of `400` momenta per axis starting at `(M, 0)`. -/
theorem arenaObs_arrivalBox_le {M : ℕ} (hL : L = 8 * M) (hM : 4000000 ≤ M) {s : ℝ}
    (h0 : 0 ≤ s) (h1 : s ≤ M / 4) :
    arenaObs (siteSetProj Prod.fst (arrivalBox L : Set (Fin 2 → ZMod L)))
        (arenaKick (idxFreeU (latticeDiracHam_isHermitian (L := L) cliffordTwo 2 1) s)
          (Projectivization.mk ℂ _ (arrivalPacket_ne_zero hL hM))) ≤ 1 / 10 := by
  have hMr : (4000000 : ℝ) ≤ M := by exact_mod_cast hM
  exact (arenaObs_flatPacket_le_of_disjoint cliffordTwo pauli_two_mulVec_spinUp
    star_spinUp_dotProduct one_pos (![(M : ℤ), 0] : Fin 2 → ℤ) (fun _ => by norm_num)
    (fun _ => by omega) (![Real.pi / 4, 0] : Fin 2 → ℝ)
    (w := fun _ => 400 * (2 * Real.pi / L)) (fun _ => by positivity)
    (abs_angleZD_arrival_le hL hM) (γ := fun _ => 3 / 4) (fun _ => by norm_num)
    (arrivalPacket_ne_zero hL hM) (arrivalBox L) h0
    (arrivalBox_disjoint_movedBoxD hL hM h0 h1)).trans
    (flatTailD_instance_le hL hM (by linarith))

/-- ★★★ **From the free time `M` to `2M` the packet of UD-245 has at least `9/10` of its
weight on `arrivalBox`.** The same packet and box. -/
theorem le_arenaObs_arrivalBox {M : ℕ} (hL : L = 8 * M) (hM : 4000000 ≤ M) {s : ℝ}
    (h1 : (M : ℝ) ≤ s) (h2 : s ≤ 2 * M) :
    9 / 10 ≤ arenaObs (siteSetProj Prod.fst (arrivalBox L : Set (Fin 2 → ZMod L)))
        (arenaKick (idxFreeU (latticeDiracHam_isHermitian (L := L) cliffordTwo 2 1) s)
          (Projectivization.mk ℂ _ (arrivalPacket_ne_zero hL hM))) := by
  have hMr : (4000000 : ℝ) ≤ M := by exact_mod_cast hM
  have hs : 0 ≤ s := by linarith
  have key := le_arenaObs_flatPacket_of_subset cliffordTwo pauli_two_mulVec_spinUp
    star_spinUp_dotProduct one_pos (![(M : ℤ), 0] : Fin 2 → ℤ) (fun _ => by norm_num)
    (fun _ => by omega) (![Real.pi / 4, 0] : Fin 2 → ℝ)
    (w := fun _ => 400 * (2 * Real.pi / L)) (fun _ => by positivity)
    (abs_angleZD_arrival_le hL hM) (γ := fun _ => 3 / 4) (fun _ => by norm_num)
    (arrivalPacket_ne_zero hL hM) (arrivalBox L) hs
    (movedBoxD_subset_arrivalBox hL hM h1 h2)
  have ht := flatTailD_instance_le (L := L) hL hM (τ := s) (by linarith)
  linarith

end Box

end CSD.RecordLayer

end
