/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.DiracPacketD

/-!
# The weight of a packet outside a box of sites

**Category:** 3-Local (CV). BACKLOG #296, second part (Task 8 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream S; milestone M7,
obligation UO-17).

`CV/DiracPacketD.lean` reads a packet's place by one translation phase for each axis and shows
each phase drifting at its component of the group velocity. A phase measures localisation
along one axis. A coincidence gate reads the weight in a region. Here the `d` phases bound the
weight outside a box of sites, as `regionWeight_mul_le` (`RecordLayer/DiracArrival.lean`) does
for an arc of the ring.

## Weights on sites and regions

* `siteWeightD`, `siteWeightD_nonneg`, `regionWeightD`, `regionWeightD_nonneg`,
  `regionWeightD_mono`, `re_chainInnerD_self`, `sum_siteWeightD`, `regionWeightD_add_compl`;
* `slabD`, `mem_slabD`, ★ `regionWeightD_compl_piFinset_le` (**outside a box is inside some
  axis's outer slab**: a union bound over the axes).

## The translation phases bound the weight

* `transPhaseD_eq_sum` (`T_i = Σ_x w_x e^{2πi x_i/L}`);
* ★★ `regionWeightD_mul_le` (the weight where `Re(ū e^{2πi x_i/L}) ≤ γ`, times `1 − γ`, is at
  most `⟨ψ, ψ⟩ − Re(ū T_i)`);
* ★★★ `regionWeightD_compl_box_le` (**the weight outside a box is at most the sum over the
  axes of `(⟨ψ, ψ⟩ − Re(ū_i T_i)) / (1 − γ_i)`**), ★★ `le_regionWeightD_box`. For any state.

## The packet in a box that moves at the group velocity

* `re_star_mul_ge_of_norm_sub_le`, `movedDirD`, `norm_movedDirD`,
  ★★ `re_movedDirD_transPhaseD_ge` (the component of `T_i(t)` along the moved direction drops
  by at most `|t|` times the drift error);
* ★★★ `regionWeightD_packetD_compl_box_le` (**at the time `t` the packet's weight outside the
  moved box is at most `Σ_i (⟨ψ₀, ψ₀⟩ − Re(ū_i T_i(0)) + |t| · driftErrorD_i) / (1 − γ_i)`**),
  ★★★ `le_regionWeightD_packetD_box` (**the moving box holds the packet**).

## Honest scope

⚠️ **A union bound.** The bound is a sum over the axes, so it grows with their number. It is
not shown to be sharp.

⚠️ **`μ > 0` for the moving box**, through `transPhaseD_drift`. The statements for any state
(`regionWeightD_compl_box_le`, `le_regionWeightD_box`) have no `μ` in them.

⚠️ **The sides are hypotheses.** `hA` asks that every position outside `A i` is at
`Re(ū_i(t) e^{2πik/L}) ≤ γ_i`. No side is constructed here; on the ring that is `chordArc`
(`RecordLayer/DiracObservers.lean`).

⚠️ **Nothing is small yet.** The bound contains `⟨ψ₀, ψ₀⟩ − Re(ū_i T_i(0))` and the drift
error. Neither is evaluated for a window: no limit in physical units, no error free of `L`,
no flat window. A gate's budget is not met by this module.

⚠️ **No record is read**, and nothing is on the arena of UA-18.

References: `specs/BACKLOG.md` #296, ~~#294~~, ~~#295~~;
`specs/unified-record-spacetime-plan.md` (UO-17, UD-209, UD-210);
`specs/beyond-1p1-scoping.md`; `specs/unified-m7-feasibility.md` (§3, §6, §9);
`CV/DiracPacketD.lean` (`packetD`, `transPhaseD`, `transPhaseD_drift`,
`chainInnerD_packetD_self`, `driftErrorD`, `NoWrapD`, `DistinctD`);
`RecordLayer/DiracArrival.lean` (`regionWeight`, `regionWeight_mul_le`,
`regionWeight_ringPacket_le`); `RecordLayer/DiracObservers.lean`
(`regionWeight_compl_chordArc_le`); R. Resta, PRL 80 (1998) 1800; `specs/future-work.md`.
-/

@[expose] public section

open Complex Matrix

noncomputable section

namespace CSD.CV

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [DecidableEq S]
  {L : ℕ} [NeZero L]

/-! ### Weights on sites and regions -/

/-- **The weight of a state at a site of the torus**: the squared norms of its components. -/
def siteWeightD (ψ : (ι → ZMod L) × S → ℂ) (x : ι → ZMod L) : ℝ := ∑ s, ‖ψ (x, s)‖ ^ 2

omit [Fintype ι] [DecidableEq ι] [DecidableEq S] [NeZero L] in
theorem siteWeightD_nonneg (ψ : (ι → ZMod L) × S → ℂ) (x : ι → ZMod L) :
    0 ≤ siteWeightD ψ x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **The weight of a state on a region of sites.** -/
def regionWeightD (ψ : (ι → ZMod L) × S → ℂ) (A : Finset (ι → ZMod L)) : ℝ :=
  ∑ x ∈ A, siteWeightD ψ x

omit [Fintype ι] [DecidableEq ι] [DecidableEq S] [NeZero L] in
theorem regionWeightD_nonneg (ψ : (ι → ZMod L) × S → ℂ) (A : Finset (ι → ZMod L)) :
    0 ≤ regionWeightD ψ A :=
  Finset.sum_nonneg fun x _ => siteWeightD_nonneg ψ x

omit [Fintype ι] [DecidableEq ι] [DecidableEq S] [NeZero L] in
theorem regionWeightD_mono (ψ : (ι → ZMod L) × S → ℂ) {A B : Finset (ι → ZMod L)}
    (h : A ⊆ B) : regionWeightD ψ A ≤ regionWeightD ψ B :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun x _ _ => siteWeightD_nonneg ψ x

omit [DecidableEq S] in
theorem re_chainInnerD_self (ψ : (ι → ZMod L) × S → ℂ) :
    (chainInnerD ψ ψ).re = ∑ p, ‖ψ p‖ ^ 2 := by
  rw [chainInnerD, Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

omit [DecidableEq S] in
/-- The sites' weights add up to the norm. -/
theorem sum_siteWeightD (ψ : (ι → ZMod L) × S → ℂ) :
    ∑ x, siteWeightD ψ x = (chainInnerD ψ ψ).re := by
  rw [re_chainInnerD_self, Fintype.sum_prod_type]
  rfl

omit [DecidableEq S] in
/-- **A region and its complement hold the whole norm.** -/
theorem regionWeightD_add_compl (ψ : (ι → ZMod L) × S → ℂ) (A : Finset (ι → ZMod L)) :
    regionWeightD ψ A + regionWeightD ψ Aᶜ = (chainInnerD ψ ψ).re := by
  rw [regionWeightD, regionWeightD, Finset.sum_add_sum_compl, sum_siteWeightD]

/-- **The slab of the axis `i` over a set of positions**: the sites whose coordinate along `i`
is in the set. -/
def slabD (i : ι) (A : Finset (ZMod L)) : Finset (ι → ZMod L) :=
  Finset.univ.filter fun x => x i ∈ A

theorem mem_slabD {i : ι} {A : Finset (ZMod L)} {x : ι → ZMod L} :
    x ∈ slabD i A ↔ x i ∈ A := by
  simp [slabD]

omit [DecidableEq S] in
/-- ★ **Outside a box is inside some axis's outer slab**: the weight outside the box with sides
`A i` is at most the sum over the axes of the weight where the coordinate `i` is outside `A i`. -/
theorem regionWeightD_compl_piFinset_le (ψ : (ι → ZMod L) × S → ℂ)
    (A : ι → Finset (ZMod L)) :
    regionWeightD ψ (Fintype.piFinset A)ᶜ ≤ ∑ i, regionWeightD ψ (slabD i (A i)ᶜ) := by
  have h0 : ∀ (x : ι → ZMod L) (i : ι),
      0 ≤ (if x i ∈ (A i)ᶜ then siteWeightD ψ x else 0) := fun x i => by
    split_ifs
    exacts [siteWeightD_nonneg ψ x, le_rfl]
  calc regionWeightD ψ (Fintype.piFinset A)ᶜ
      ≤ ∑ x ∈ (Fintype.piFinset A)ᶜ, ∑ i, if x i ∈ (A i)ᶜ then siteWeightD ψ x else 0 := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [Finset.mem_compl, Fintype.mem_piFinset] at hx
        push Not at hx
        obtain ⟨i, hi⟩ := hx
        refine le_trans ?_ (Finset.single_le_sum
          (f := fun i => if x i ∈ (A i)ᶜ then siteWeightD ψ x else 0)
          (fun j _ => h0 x j) (Finset.mem_univ i))
        simp [hi]
    _ ≤ ∑ x, ∑ i, if x i ∈ (A i)ᶜ then siteWeightD ψ x else 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ =>
          Finset.sum_nonneg fun i _ => h0 x i
    _ = ∑ i, regionWeightD ψ (slabD i (A i)ᶜ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [regionWeightD, slabD, Finset.sum_filter]

/-! ### The translation phases bound the weight -/

omit [DecidableEq S] in
/-- **The translation phase of an axis is the sites' weights on the unit circle**:
`T_i = Σ_x w_x e^{2πi x_i/L}`. -/
theorem transPhaseD_eq_sum (i : ι) (ψ : (ι → ZMod L) × S → ℂ) :
    transPhaseD i ψ = ∑ x, (siteWeightD ψ x : ℂ) * (ZMod.toCircle (x i) : ℂ) := by
  rw [transPhaseD, chainInnerD, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [siteWeightD, Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  change star (ψ (x, s)) * ((ZMod.toCircle (x i) : ℂ) * ψ (x, s)) = _
  rw [Complex.star_def]
  have h := Complex.conj_mul' (ψ (x, s))
  push_cast
  linear_combination (ZMod.toCircle (x i) : ℂ) * h

omit [DecidableEq S] in
/-- ★★ **Weight far from a direction along one axis is bounded by that axis's translation
phase**: for a unit `u` and a region `B` whose sites all have `Re(ū e^{2πi x_i/L}) ≤ γ`, the
weight on `B` times `1 − γ` is at most `⟨ψ, ψ⟩ − Re(ū T_i)`. -/
theorem regionWeightD_mul_le (ψ : (ι → ZMod L) × S → ℂ) (i : ι) {u : ℂ} (hu : ‖u‖ = 1)
    {B : Finset (ι → ZMod L)} {γ : ℝ}
    (hB : ∀ x ∈ B, (star u * (ZMod.toCircle (x i) : ℂ)).re ≤ γ) :
    regionWeightD ψ B * (1 - γ) ≤ (chainInnerD ψ ψ).re - (star u * transPhaseD i ψ).re := by
  have hle1 : ∀ k : ZMod L, (star u * (ZMod.toCircle k : ℂ)).re ≤ 1 := fun k =>
    (Complex.re_le_norm _).trans (by rw [norm_mul, norm_star, hu, Circle.norm_coe, one_mul])
  have hterm : ∀ x : ι → ZMod L,
      (star u * ((siteWeightD ψ x : ℂ) * (ZMod.toCircle (x i) : ℂ))).re
        = siteWeightD ψ x * (star u * (ZMod.toCircle (x i) : ℂ)).re := fun x => by
    rw [show star u * ((siteWeightD ψ x : ℂ) * (ZMod.toCircle (x i) : ℂ))
        = (siteWeightD ψ x : ℂ) * (star u * (ZMod.toCircle (x i) : ℂ)) by ring,
      Complex.re_ofReal_mul]
  rw [transPhaseD_eq_sum, Finset.mul_sum, Complex.re_sum, ← sum_siteWeightD]
  simp only [hterm]
  rw [← Finset.sum_sub_distrib]
  calc regionWeightD ψ B * (1 - γ)
      = ∑ x ∈ B, siteWeightD ψ x * (1 - γ) := by rw [regionWeightD, Finset.sum_mul]
    _ ≤ ∑ x ∈ B, (siteWeightD ψ x
          - siteWeightD ψ x * (star u * (ZMod.toCircle (x i) : ℂ)).re) :=
        Finset.sum_le_sum fun x hx => by
          have := mul_le_mul_of_nonneg_left (hB x hx) (siteWeightD_nonneg ψ x)
          linarith
    _ ≤ ∑ x, (siteWeightD ψ x
          - siteWeightD ψ x * (star u * (ZMod.toCircle (x i) : ℂ)).re) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => by
          have := mul_le_mul_of_nonneg_left (hle1 (x i)) (siteWeightD_nonneg ψ x)
          linarith

omit [DecidableEq S] in
/-- ★★★ **The weight outside a box is bounded by the `d` translation phases.** For a unit
direction `u i` on each axis and sides `A i` outside which `Re(ū_i e^{2πik/L}) ≤ γ_i < 1`, the
weight outside the box is at most the sum over the axes of
`(⟨ψ, ψ⟩ − Re(ū_i T_i)) / (1 − γ_i)`. -/
theorem regionWeightD_compl_box_le (ψ : (ι → ZMod L) × S → ℂ) {u : ι → ℂ}
    (hu : ∀ i, ‖u i‖ = 1) {A : ι → Finset (ZMod L)} {γ : ι → ℝ} (hγ : ∀ i, γ i < 1)
    (hA : ∀ i, ∀ k ∉ A i, (star (u i) * (ZMod.toCircle k : ℂ)).re ≤ γ i) :
    regionWeightD ψ (Fintype.piFinset A)ᶜ
      ≤ ∑ i, ((chainInnerD ψ ψ).re - (star (u i) * transPhaseD i ψ).re) / (1 - γ i) := by
  refine (regionWeightD_compl_piFinset_le ψ A).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [le_div_iff₀ (sub_pos.2 (hγ i))]
  refine regionWeightD_mul_le ψ i (hu i) fun x hx => hA i (x i) ?_
  exact Finset.mem_compl.1 (mem_slabD.1 hx)

omit [DecidableEq S] in
/-- ★★ **The box holds the rest**: under the hypotheses of `regionWeightD_compl_box_le`, the
weight in the box is at least the norm less that sum. -/
theorem le_regionWeightD_box (ψ : (ι → ZMod L) × S → ℂ) {u : ι → ℂ}
    (hu : ∀ i, ‖u i‖ = 1) {A : ι → Finset (ZMod L)} {γ : ι → ℝ} (hγ : ∀ i, γ i < 1)
    (hA : ∀ i, ∀ k ∉ A i, (star (u i) * (ZMod.toCircle k : ℂ)).re ≤ γ i) :
    (chainInnerD ψ ψ).re
        - ∑ i, ((chainInnerD ψ ψ).re - (star (u i) * transPhaseD i ψ).re) / (1 - γ i)
      ≤ regionWeightD ψ (Fintype.piFinset A) := by
  have h1 := regionWeightD_add_compl ψ (Fintype.piFinset A)
  have h2 := regionWeightD_compl_box_le ψ hu hγ hA
  linarith

/-! ### The packet in a box that moves at the group velocity -/

omit [NeZero L] in
/-- A phase that is within `ε` of a rotated one has nearly its component along the rotated
direction. -/
theorem re_star_mul_ge_of_norm_sub_le {e u T T₀ : ℂ} {ε : ℝ} (he : ‖e‖ = 1) (hu : ‖u‖ = 1)
    (h : ‖T - e * T₀‖ ≤ ε) : (star u * T₀).re - ε ≤ (star (e * u) * T).re := by
  have hee : star e * e = 1 := by
    rw [Complex.star_def, Complex.conj_mul', he]
    norm_num
  have hsplit : star (e * u) * T = star (e * u) * (T - e * T₀) + star u * T₀ := by
    rw [star_mul']
    linear_combination (star u * T₀) * hee
  have hnorm : ‖star (e * u) * (T - e * T₀)‖ = ‖T - e * T₀‖ := by
    rw [norm_mul, norm_star, norm_mul, he, hu, one_mul, one_mul]
  have hre := Complex.abs_re_le_norm (star (e * u) * (T - e * T₀))
  rw [hnorm] at hre
  rw [hsplit, Complex.add_re]
  linarith [neg_abs_le (star (e * u) * (T - e * T₀)).re]

variable (α : ι → Matrix S S ℂ) (β : Matrix S S ℂ)

/-- **The direction a packet's phase along the axis `i` is carried to**: the starting direction
`u` turned by `(2π/L) v_i(k₀) t`. -/
def movedDirD (L : ℕ) (J μ : ℝ) (k₀ : ι → ℝ) (i : ι) (u : ℂ) (t : ℝ) : ℂ :=
  exp (I * (((2 * Real.pi / L * groupVelD J μ k₀ i : ℝ) : ℂ) * t)) * u

omit [DecidableEq ι] [NeZero L] in
theorem norm_movedDirD (J μ : ℝ) (k₀ : ι → ℝ) (i : ι) {u : ℂ} (hu : ‖u‖ = 1) (t : ℝ) :
    ‖movedDirD L J μ k₀ i u t‖ = 1 := by
  rw [movedDirD, norm_mul, hu, mul_one,
    show I * (((2 * Real.pi / L * groupVelD J μ k₀ i : ℝ) : ℂ) * t)
      = ((2 * Real.pi / L * groupVelD J μ k₀ i * t : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

/-- ★★ **The component of the phase along the moved direction drops by at most the drift**:
for `μ > 0`, `Re(ū(t) T_i(t)) ≥ Re(ū T_i(0)) − |t| · driftErrorD`. -/
theorem re_movedDirD_transPhaseD_ge {J μ : ℝ} (hμ : 0 < μ) (e₀ : S → ℂ)
    {W : Finset (ι → ℤ)} {i : ι} (hW : NoWrapD L W i) (c : (ι → ℤ) → ℂ) (k₀ : ι → ℝ)
    {u : ℂ} (hu : ‖u‖ = 1) (t : ℝ) :
    (star u * transPhaseD i (packetD (L := L) α β J μ e₀ W c 0)).re
        - |t| * driftErrorD (L := L) α β J μ e₀ W c i k₀
      ≤ (star (movedDirD L J μ k₀ i u t)
          * transPhaseD i (packetD (L := L) α β J μ e₀ W c t)).re := by
  have he : ‖exp (I * (((2 * Real.pi / L * groupVelD J μ k₀ i : ℝ) : ℂ) * t))‖ = 1 := by
    have := norm_movedDirD (L := L) J μ k₀ i (u := 1) (by simp) t
    rwa [movedDirD, mul_one] at this
  exact re_star_mul_ge_of_norm_sub_le he hu
    (transPhaseD_drift (L := L) (J := J) α β hμ e₀ hW c k₀ t)

/-- ★★★ **A packet's weight outside a box that moves at the group velocity.** For `μ > 0`, a
window without wrap-around on any axis and with distinct momenta, a unit direction `u i` for
each axis, and sides `A i` outside which the moved direction has
`Re(ū_i(t) e^{2πik/L}) ≤ γ_i < 1`: at the time `t` the weight outside the box is at most the
sum over the axes of `(⟨ψ₀, ψ₀⟩ − Re(ū_i T_i(0)) + |t| · driftErrorD_i) / (1 − γ_i)`. -/
theorem regionWeightD_packetD_compl_box_le {J μ : ℝ} (hμ : 0 < μ) (e₀ : S → ℂ)
    {W : Finset (ι → ℤ)} (hW : ∀ i, NoWrapD L W i) (hD : DistinctD L W) (c : (ι → ℤ) → ℂ)
    (k₀ : ι → ℝ) (t : ℝ) {u : ι → ℂ} (hu : ∀ i, ‖u i‖ = 1) {A : ι → Finset (ZMod L)}
    {γ : ι → ℝ} (hγ : ∀ i, γ i < 1)
    (hA : ∀ i, ∀ k ∉ A i,
      (star (movedDirD L J μ k₀ i (u i) t) * (ZMod.toCircle k : ℂ)).re ≤ γ i) :
    regionWeightD (packetD (L := L) α β J μ e₀ W c t) (Fintype.piFinset A)ᶜ
      ≤ ∑ i, ((chainInnerD (packetD (L := L) α β J μ e₀ W c 0)
                  (packetD (L := L) α β J μ e₀ W c 0)).re
              - (star (u i) * transPhaseD i (packetD (L := L) α β J μ e₀ W c 0)).re
              + |t| * driftErrorD (L := L) α β J μ e₀ W c i k₀) / (1 - γ i) := by
  have hN : chainInnerD (packetD (L := L) α β J μ e₀ W c t) (packetD (L := L) α β J μ e₀ W c t)
      = chainInnerD (packetD (L := L) α β J μ e₀ W c 0) (packetD (L := L) α β J μ e₀ W c 0) := by
    rw [chainInnerD_packetD_self α β J μ e₀ hD c t, chainInnerD_packetD_self α β J μ e₀ hD c 0]
  refine (regionWeightD_compl_box_le _ (fun i => norm_movedDirD J μ k₀ i (hu i) t) hγ hA).trans
    (Finset.sum_le_sum fun i _ => ?_)
  rw [hN]
  have h := re_movedDirD_transPhaseD_ge (L := L) (J := J) α β hμ e₀ (hW i) c k₀ (hu i) t
  exact div_le_div_of_nonneg_right (by linarith) (sub_pos.2 (hγ i)).le

/-- ★★★ **The moving box holds the packet**: under the hypotheses of
`regionWeightD_packetD_compl_box_le`, the weight in the box at the time `t` is at least the
norm less that sum. -/
theorem le_regionWeightD_packetD_box {J μ : ℝ} (hμ : 0 < μ) (e₀ : S → ℂ)
    {W : Finset (ι → ℤ)} (hW : ∀ i, NoWrapD L W i) (hD : DistinctD L W) (c : (ι → ℤ) → ℂ)
    (k₀ : ι → ℝ) (t : ℝ) {u : ι → ℂ} (hu : ∀ i, ‖u i‖ = 1) {A : ι → Finset (ZMod L)}
    {γ : ι → ℝ} (hγ : ∀ i, γ i < 1)
    (hA : ∀ i, ∀ k ∉ A i,
      (star (movedDirD L J μ k₀ i (u i) t) * (ZMod.toCircle k : ℂ)).re ≤ γ i) :
    (chainInnerD (packetD (L := L) α β J μ e₀ W c 0) (packetD (L := L) α β J μ e₀ W c 0)).re
        - ∑ i, ((chainInnerD (packetD (L := L) α β J μ e₀ W c 0)
                    (packetD (L := L) α β J μ e₀ W c 0)).re
                - (star (u i) * transPhaseD i (packetD (L := L) α β J μ e₀ W c 0)).re
                + |t| * driftErrorD (L := L) α β J μ e₀ W c i k₀) / (1 - γ i)
      ≤ regionWeightD (packetD (L := L) α β J μ e₀ W c t) (Fintype.piFinset A) := by
  have h1 := regionWeightD_add_compl (packetD (L := L) α β J μ e₀ W c t) (Fintype.piFinset A)
  have h2 := regionWeightD_packetD_compl_box_le (L := L) (J := J) α β hμ e₀ hW hD c k₀ t hu hγ hA
  rw [chainInnerD_packetD_self α β J μ e₀ hD c t,
    ← chainInnerD_packetD_self α β J μ e₀ hD c 0] at h1
  linarith

end CSD.CV

end
