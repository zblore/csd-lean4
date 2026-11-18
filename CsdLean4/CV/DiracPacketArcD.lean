/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.DiracPacketBoxD

/-!
# The box of arcs about a packet

**Category:** 3-Local (CV). BACKLOG #296, third part (Task 8 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream S; milestone
M7, obligation UO-17; remainder (a′) of the row).

`CV/DiracPacketBoxD.lean` bounds a packet's weight outside a box whose sides are a
hypothesis: outside the side of the axis `i`, `Re(ū_i e^{2πik/L}) ≤ γ_i`. Here the sides are
built: the arc of positions about the direction, as `chordArc` is on the ring
(`RecordLayer/DiracObservers.lean`).

* `arcSideD`, `mem_arcSideD`, `re_le_of_notMem_arcSideD`,
  ★ `mem_arcSideD_expI` (the arc about `e^{iφ}` with `γ = cos δ` is the positions with
  `cos(2πk/L − φ) > cos δ`: those within the angle `δ` of `φ`);
* `arcBoxD`, `mem_arcBoxD`, ★★★ `regionWeightD_compl_arcBoxD_le`, ★★ `le_regionWeightD_arcBoxD`
  (the bound of `regionWeightD_compl_box_le` for the box of arcs, with no hypothesis on the
  sides; any state);
* `movedBoxD`, ★★★ `regionWeightD_packetD_compl_movedBoxD_le`,
  ★★★ `le_regionWeightD_packetD_movedBoxD` (**the box of arcs about the directions turned at
  the group velocity holds the packet**, `μ > 0`).

## Honest scope

⚠️ **The sides are the largest ones the bound allows, by definition.** The content is that
the box is now a named set of sites with a description in angles, and the two theorems carry
no hypothesis on it. The bound itself is that of `CV/DiracPacketBoxD.lean`.

⚠️ **Not an interval of sites.** `mem_arcSideD_expI` describes the arc by a cosine. That it is
a run of consecutive sites, and its length, are not shown.

⚠️ **Nothing is shown small.** The starting term and the drift error are still not evaluated
for a window; that is the limit in physical units, open in #296. `μ > 0` for the moving box.

⚠️ **No record is read**, and nothing is on the arena of UA-18.

References: `specs/BACKLOG.md` #296; `specs/unified-record-spacetime-plan.md` (UO-17, UD-209,
UD-210, UD-217); `CV/DiracPacketBoxD.lean` (`regionWeightD_compl_box_le`,
`regionWeightD_packetD_compl_box_le`, `movedDirD`); `CV/DiracPacket.lean`
(`re_star_exp_mul_toCircle`); `RecordLayer/DiracObservers.lean`
(`regionWeight_compl_chordArc_le`); `specs/future-work.md`.
-/

@[expose] public section

open Complex Matrix

noncomputable section

namespace CSD.CV

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [DecidableEq S]
  {L : ℕ} [NeZero L]

/-! ### The arc of one axis -/

/-- **The arc of positions about a direction**: the positions `k` of one axis with
`Re(ū e^{2πik/L}) > γ`. For `u = e^{iφ}` and `γ = cos δ` these are the positions within the
angle `δ` of `φ`. -/
def arcSideD (u : ℂ) (γ : ℝ) : Finset (ZMod L) :=
  Finset.univ.filter fun k => γ < (star u * (ZMod.toCircle k : ℂ)).re

theorem mem_arcSideD {u : ℂ} {γ : ℝ} {k : ZMod L} :
    k ∈ arcSideD u γ ↔ γ < (star u * (ZMod.toCircle k : ℂ)).re := by
  simp [arcSideD]

/-- Outside the arc the position is at `Re ≤ γ` from the direction. -/
theorem re_le_of_notMem_arcSideD {u : ℂ} {γ : ℝ} {k : ZMod L} (hk : k ∉ arcSideD u γ) :
    (star u * (ZMod.toCircle k : ℂ)).re ≤ γ :=
  not_lt.1 fun h => hk (mem_arcSideD.2 h)

/-- ★ **The arc about `e^{iφ}` of half-width `δ`** is the positions with
`cos(2πk/L − φ) > cos δ`. -/
theorem mem_arcSideD_expI {φ δ : ℝ} {k : ZMod L} :
    k ∈ arcSideD (exp (I * (φ : ℂ))) (Real.cos δ)
      ↔ Real.cos δ < Real.cos (2 * Real.pi * k.val / L - φ) := by
  rw [mem_arcSideD, re_star_exp_mul_toCircle]

/-! ### The box of arcs -/

/-- **The box of arcs**: the sites whose position along each axis `i` is in the arc about
`u i`. -/
def arcBoxD (u : ι → ℂ) (γ : ι → ℝ) : Finset (ι → ZMod L) :=
  Fintype.piFinset fun i => arcSideD (u i) (γ i)

theorem mem_arcBoxD {u : ι → ℂ} {γ : ι → ℝ} {x : ι → ZMod L} :
    x ∈ arcBoxD u γ ↔ ∀ i, γ i < (star (u i) * (ZMod.toCircle (x i) : ℂ)).re := by
  simp [arcBoxD, Fintype.mem_piFinset, mem_arcSideD]

omit [DecidableEq S] in
/-- ★★★ **The weight outside the box of arcs**, with no hypothesis on the sides: for unit
directions `u i` and `γ i < 1`, it is at most the sum over the axes of
`(⟨ψ, ψ⟩ − Re(ū_i T_i)) / (1 − γ_i)`. -/
theorem regionWeightD_compl_arcBoxD_le (ψ : (ι → ZMod L) × S → ℂ) {u : ι → ℂ}
    (hu : ∀ i, ‖u i‖ = 1) {γ : ι → ℝ} (hγ : ∀ i, γ i < 1) :
    regionWeightD ψ (arcBoxD u γ)ᶜ
      ≤ ∑ i, ((chainInnerD ψ ψ).re - (star (u i) * transPhaseD i ψ).re) / (1 - γ i) :=
  regionWeightD_compl_box_le ψ hu hγ fun _ _ hk => re_le_of_notMem_arcSideD hk

omit [DecidableEq S] in
/-- ★★ **The box of arcs holds the rest.** -/
theorem le_regionWeightD_arcBoxD (ψ : (ι → ZMod L) × S → ℂ) {u : ι → ℂ}
    (hu : ∀ i, ‖u i‖ = 1) {γ : ι → ℝ} (hγ : ∀ i, γ i < 1) :
    (chainInnerD ψ ψ).re
        - ∑ i, ((chainInnerD ψ ψ).re - (star (u i) * transPhaseD i ψ).re) / (1 - γ i)
      ≤ regionWeightD ψ (arcBoxD u γ) :=
  le_regionWeightD_box ψ hu hγ fun _ _ hk => re_le_of_notMem_arcSideD hk

/-! ### The box that moves with the packet -/

variable (α : ι → Matrix S S ℂ) (β : Matrix S S ℂ)

/-- **The box of arcs about the moved directions**: at the time `t`, the arcs about the
directions `u i` turned by `(2π/L) v_i(k₀) t`. -/
def movedBoxD (L : ℕ) [NeZero L] (J μ : ℝ) (k₀ : ι → ℝ) (u : ι → ℂ) (γ : ι → ℝ) (t : ℝ) :
    Finset (ι → ZMod L) :=
  arcBoxD (fun i => movedDirD L J μ k₀ i (u i) t) γ

/-- ★★★ **A packet's weight outside the box that moves with it**, with no hypothesis on the
sides: for `μ > 0`, a window without wrap-around and with distinct momenta, unit directions
`u i` and `γ i < 1`, at the time `t` it is at most the sum over the axes of
`(⟨ψ₀, ψ₀⟩ − Re(ū_i T_i(0)) + |t| · driftErrorD_i) / (1 − γ_i)`. -/
theorem regionWeightD_packetD_compl_movedBoxD_le {J μ : ℝ} (hμ : 0 < μ) (e₀ : S → ℂ)
    {W : Finset (ι → ℤ)} (hW : ∀ i, NoWrapD L W i) (hD : DistinctD L W) (c : (ι → ℤ) → ℂ)
    (k₀ : ι → ℝ) (t : ℝ) {u : ι → ℂ} (hu : ∀ i, ‖u i‖ = 1) {γ : ι → ℝ} (hγ : ∀ i, γ i < 1) :
    regionWeightD (packetD (L := L) α β J μ e₀ W c t) (movedBoxD L J μ k₀ u γ t)ᶜ
      ≤ ∑ i, ((chainInnerD (packetD (L := L) α β J μ e₀ W c 0)
                  (packetD (L := L) α β J μ e₀ W c 0)).re
              - (star (u i) * transPhaseD i (packetD (L := L) α β J μ e₀ W c 0)).re
              + |t| * driftErrorD (L := L) α β J μ e₀ W c i k₀) / (1 - γ i) :=
  regionWeightD_packetD_compl_box_le (L := L) (J := J) α β hμ e₀ hW hD c k₀ t hu hγ
    fun _ _ hk => re_le_of_notMem_arcSideD hk

/-- ★★★ **The box that moves with the packet holds it.** -/
theorem le_regionWeightD_packetD_movedBoxD {J μ : ℝ} (hμ : 0 < μ) (e₀ : S → ℂ)
    {W : Finset (ι → ℤ)} (hW : ∀ i, NoWrapD L W i) (hD : DistinctD L W) (c : (ι → ℤ) → ℂ)
    (k₀ : ι → ℝ) (t : ℝ) {u : ι → ℂ} (hu : ∀ i, ‖u i‖ = 1) {γ : ι → ℝ} (hγ : ∀ i, γ i < 1) :
    (chainInnerD (packetD (L := L) α β J μ e₀ W c 0) (packetD (L := L) α β J μ e₀ W c 0)).re
        - ∑ i, ((chainInnerD (packetD (L := L) α β J μ e₀ W c 0)
                    (packetD (L := L) α β J μ e₀ W c 0)).re
                - (star (u i) * transPhaseD i (packetD (L := L) α β J μ e₀ W c 0)).re
                + |t| * driftErrorD (L := L) α β J μ e₀ W c i k₀) / (1 - γ i)
      ≤ regionWeightD (packetD (L := L) α β J μ e₀ W c t) (movedBoxD L J μ k₀ u γ t) :=
  le_regionWeightD_packetD_box (L := L) (J := J) α β hμ e₀ hW hD c k₀ t hu hγ
    fun _ _ hk => re_le_of_notMem_arcSideD hk

end CSD.CV

end
