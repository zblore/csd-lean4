/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.TorusArrival

/-!
# Arrival and display on the torus: an instance with numbers

**Category:** 7-SigmaLayer. BACKLOG #297, fifth brick (Task 9 of the author's plan "Unified
records, quantum measurement and emergent spacetime" of 2026-11-18, workstream S; plan
`specs/unified-records-spacetime-task-plans.md` §7, item 3).

`RecordLayer/TorusArrival.lean` proves arrival, display and the two recorded counts from
hypotheses on the packet's moving box and three inequalities. Here the hypotheses are met.

## The detector swept by the box

* `re_star_mul_gt_of_re_gt` — two unit directions that both see a unit point within `γ ≥ 0`
  have `Re(ū u') > 2γ² − 1`;
* `re_star_movedDirD_mul`, ★★ `movedBoxD_disjoint` — the moving box at two flow times is
  disjoint from itself when it has turned, along one axis, by an angle whose cosine is at
  most `2γ² − 1`;
* `sweptBoxD`, `mem_sweptBoxD` — the sites the moving box covers at some flow time of
  `[t₂, t]`;
* ★★★ `torusDetector_arrival_sweptBox` — the theorem of UD-242 for the detector on those
  sites, with the box hypotheses replaced by one condition on a cosine.

## The numbers

* `flatPacketD_ne_zero` — the flat packet is not zero;
* `groupVelD_instance` — `J = 2`, `μ = 1`, `k₀ = (π/4, 0)`: the group velocity along the
  first axis is `8/3`;
* `flatTailD_fin_two`, `flatTailD_instance_le` — the tail is at most `1/10` up to `9M/4`;
* ★★★ `torusDetector_arrival_instance` — **two dimensions, `L = 8M` sites per axis with
  `M ≥ 4·10⁶`, `400` momenta per axis starting at `(M, 0)`, sides `γ = 3/4`, the detector on
  the sites swept during `[9M/8, 9M/4]`, the pointer's rate `8π/(75M)`: the pointer is not
  displayed up to the flow time `3M/8`, it is displayed at `9M/4`, and the counts `0` at
  `3M/8` and `1` at `9M/4` are a record history of the start.**

## Honest scope

⚠️ **On the fibres where the profile vanishes**, a null set of the pointer's conserved angle.
The profile and the fibre are hypotheses: `f(θ₂) = 0` and `−2 f'(θ₂) = 8π/(75M)`. No profile
with these two values is exhibited here.

⚠️ **The Clifford family and the spinor `e₀` are hypotheses** (`IsCliffordFamily α β`,
`β e₀ = e₀`, `‖e₀‖ = 1`). None is exhibited here.

⚠️ **The detector is the set of sites the box sweeps.** It is not a box of sites given in
advance, and its number of sites is not computed.

⚠️ **Between `3M/8` and `9M/8` nothing is said about the display.** No time of arrival.

⚠️ **Not composed with the bound against the graph distance** (`torusDetector_not_displayed`).

⚠️ **Flow times.**

References: `specs/BACKLOG.md` #297; `specs/unified-record-spacetime-plan.md` (UD-222,
UD-242, UD-243); `specs/unified-records-spacetime-task-plans.md` (§7);
`RecordLayer/TorusArrival.lean` (`torusDetector_arrival_flatPacket`, `flatTailD`,
`arenaReadout`); `CV/DiracPacketArcD.lean` (`movedBoxD`, `arcBoxD`, `mem_arcBoxD`);
`CV/DiracPacketBoxD.lean` (`movedDirD`, `norm_movedDirD`); `CV/DiracAnisotropy.lean`
(`groupVelD`, `latticeED_sq`); `CV/DiracPacketLimitD.lean` (`chainInnerD_packetD_unitAmpD`,
`sum_flatAmpD_sq`); `specs/future-work.md`.
-/

@[expose] public section

noncomputable section

open CSD.CV CSD.LF4 CSD.SigmaLayer Matrix Set MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator

namespace CSD.RecordLayer

/-! ### The detector swept by the box -/

/-- The real inequality behind `re_star_mul_gt_of_re_gt`. -/
theorem two_mul_sq_sub_one_lt {P Q P' Q' γ : ℝ} (hγ : 0 ≤ γ) (h1 : γ < P) (h2 : γ < Q)
    (hP : P ^ 2 + P' ^ 2 = 1) (hQ : Q ^ 2 + Q' ^ 2 = 1) :
    2 * γ ^ 2 - 1 < P * Q + P' * Q' := by
  have hPQ : γ ^ 2 < P * Q := by
    nlinarith [mul_pos (sub_pos.2 h1) (sub_pos.2 h2), mul_nonneg hγ (sub_pos.2 h1).le,
      mul_nonneg hγ (sub_pos.2 h2).le]
  have hp2 : 1 - P ^ 2 < 1 - γ ^ 2 := by nlinarith
  have hq2 : 1 - Q ^ 2 < 1 - γ ^ 2 := by nlinarith
  have hp0 : 0 ≤ 1 - P ^ 2 := by nlinarith [sq_nonneg P']
  have hq0 : 0 ≤ 1 - Q ^ 2 := by nlinarith [sq_nonneg Q']
  have hlt : (1 - P ^ 2) * (1 - Q ^ 2) < (1 - γ ^ 2) * (1 - γ ^ 2) :=
    mul_lt_mul'' hp2 hq2 hp0 hq0
  have hsq : (P' * Q') ^ 2 = (1 - P ^ 2) * (1 - Q ^ 2) := by
    rw [mul_pow, show P' ^ 2 = 1 - P ^ 2 by linarith, show Q' ^ 2 = 1 - Q ^ 2 by linarith]
  by_contra hn
  rw [not_lt] at hn
  have h3 : 1 - γ ^ 2 ≤ -(P' * Q') := by linarith
  have h4 := mul_self_le_mul_self (by linarith : (0 : ℝ) ≤ 1 - γ ^ 2) h3
  nlinarith [h4, hsq, hlt]

/-- Two unit directions that both see a unit point within `γ ≥ 0` are within `2γ² − 1` of
each other. -/
theorem re_star_mul_gt_of_re_gt {u u' z : ℂ} (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) (hz : ‖z‖ = 1)
    {γ : ℝ} (hγ : 0 ≤ γ) (h1 : γ < (star u * z).re) (h2 : γ < (star u' * z).re) :
    2 * γ ^ 2 - 1 < (star u * u').re := by
  have nsq : ∀ w : ℂ, ‖w‖ = 1 → w.re * w.re + w.im * w.im = 1 := fun w hw => by
    rw [← Complex.normSq_apply, ← Complex.sq_norm, hw, one_pow]
  have ha := nsq u hu
  have hc := nsq u' hu'
  have hx := nsq z hz
  have e : ∀ v w : ℂ, (star v * w).re = v.re * w.re + v.im * w.im := fun v w => by
    rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [e] at h1 h2 ⊢
  have hP : (u.re * z.re + u.im * z.im) ^ 2 + (u.re * z.im - u.im * z.re) ^ 2 = 1 := by
    have : (u.re * z.re + u.im * z.im) ^ 2 + (u.re * z.im - u.im * z.re) ^ 2
        = (u.re * u.re + u.im * u.im) * (z.re * z.re + z.im * z.im) := by ring
    rw [this, ha, hx, mul_one]
  have hQ : (u'.re * z.re + u'.im * z.im) ^ 2 + (u'.re * z.im - u'.im * z.re) ^ 2 = 1 := by
    have : (u'.re * z.re + u'.im * z.im) ^ 2 + (u'.re * z.im - u'.im * z.re) ^ 2
        = (u'.re * u'.re + u'.im * u'.im) * (z.re * z.re + z.im * z.im) := by ring
    rw [this, hc, hx, mul_one]
  have key := two_mul_sq_sub_one_lt hγ h1 h2 hP hQ
  have hid : (u.re * z.re + u.im * z.im) * (u'.re * z.re + u'.im * z.im)
        + (u.re * z.im - u.im * z.re) * (u'.re * z.im - u'.im * z.re)
      = u.re * u'.re + u.im * u'.im := by
    have : (u.re * z.re + u.im * z.im) * (u'.re * z.re + u'.im * z.im)
          + (u.re * z.im - u.im * z.re) * (u'.re * z.im - u'.im * z.re)
        = (u.re * u'.re + u.im * u'.im) * (z.re * z.re + z.im * z.im) := by ring
    rw [this, hx, mul_one]
  linarith

section Swept

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {L : ℕ} [NeZero L]

omit [DecidableEq κ] [NeZero L] in
/-- The moving direction at two flow times: the angle between them is the drift over the
difference of the times. -/
theorem re_star_movedDirD_mul (J μ : ℝ) (k₀ : κ → ℝ) (i : κ) (s s' : ℝ) :
    (star (movedDirD L J μ k₀ i 1 s) * movedDirD L J μ k₀ i 1 s').re
      = Real.cos (2 * Real.pi / L * groupVelD J μ k₀ i * (s' - s)) := by
  rw [movedDirD, movedDirD, mul_one, mul_one, Complex.star_def, ← Complex.exp_conj,
    ← Complex.exp_add]
  have hh : (starRingEnd ℂ) (Complex.I * (((2 * Real.pi / L * groupVelD J μ k₀ i : ℝ) : ℂ) * s))
        + Complex.I * (((2 * Real.pi / L * groupVelD J μ k₀ i : ℝ) : ℂ) * s')
      = ((2 * Real.pi / L * groupVelD J μ k₀ i * (s' - s) : ℝ) : ℂ) * Complex.I := by
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [hh, Complex.exp_ofReal_mul_I_re]

/-- ★★ **The moving box at two flow times is disjoint from itself once it has turned far
enough along one axis**: when the cosine of the drift angle along `a` over the difference of
the times is at most `2 γ_a² − 1`, with `γ_a ≥ 0`. -/
theorem movedBoxD_disjoint (J μ : ℝ) (k₀ : κ → ℝ) {γ : κ → ℝ} (a : κ) (hγ : 0 ≤ γ a)
    {s s' : ℝ}
    (hcos : Real.cos (2 * Real.pi / L * groupVelD J μ k₀ a * (s' - s)) ≤ 2 * γ a ^ 2 - 1) :
    Disjoint (movedBoxD L J μ k₀ (fun _ => 1) γ s) (movedBoxD L J μ k₀ (fun _ => 1) γ s') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  have hx1 : x ∈ arcBoxD (fun i => movedDirD L J μ k₀ i 1 s) γ := hx
  have hx2 : x ∈ arcBoxD (fun i => movedDirD L J μ k₀ i 1 s') γ := hx'
  have h1 : γ a < (star (movedDirD L J μ k₀ a 1 s) * (ZMod.toCircle (x a) : ℂ)).re :=
    mem_arcBoxD.1 hx1 a
  have h2 : γ a < (star (movedDirD L J μ k₀ a 1 s') * (ZMod.toCircle (x a) : ℂ)).re :=
    mem_arcBoxD.1 hx2 a
  have key := re_star_mul_gt_of_re_gt (norm_movedDirD (L := L) J μ k₀ a norm_one s)
    (norm_movedDirD (L := L) J μ k₀ a norm_one s') (Circle.norm_coe _) hγ h1 h2
  rw [re_star_movedDirD_mul] at key
  linarith

open Classical in
/-- **The sites swept by the moving box** during the flow times `[t₂, t]`. -/
def sweptBoxD (L : ℕ) [NeZero L] (J μ : ℝ) (k₀ γ : κ → ℝ) (t₂ t : ℝ) :
    Finset (κ → ZMod L) :=
  Finset.univ.filter fun x => ∃ s, t₂ ≤ s ∧ s ≤ t ∧ x ∈ movedBoxD L J μ k₀ (fun _ => 1) γ s

theorem mem_sweptBoxD {J μ : ℝ} {k₀ γ : κ → ℝ} {t₂ t : ℝ} {x : κ → ZMod L} :
    x ∈ sweptBoxD L J μ k₀ γ t₂ t
      ↔ ∃ s, t₂ ≤ s ∧ s ≤ t ∧ x ∈ movedBoxD L J μ k₀ (fun _ => 1) γ s := by
  unfold sweptBoxD
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] {α : κ → Matrix S S ℂ}
  {β : Matrix S S ℂ} {f : ℝ → ℝ} {N : ℕ}

omit [Nonempty S] in
/-- ★★★ **Arrival and display for the detector on the swept sites.** The statement of
`torusDetector_arrival_flatPacket` for the detector on the sites the moving box covers during
`[t₂, t]`. The two hypotheses on the box are replaced by one: along an axis `a` with
`γ_a ≥ 0`, between any flow time of `[0, t₁]` and any of `[t₂, t]` the drift angle has cosine
at most `2 γ_a² − 1`. -/
theorem torusDetector_arrival_sweptBox (e : (κ → ZMod L) × S ≃ Fin (N + 1))
    (h : IsCliffordFamily α β) {e₀ : S → ℂ} (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1)
    {J μ : ℝ} (hμ : 0 < μ) (hf : Function.Periodic f 1) (hc : ContDiff ℝ ∞ f)
    (p₀ : CPN (N + 1)) (lo : κ → ℤ) {Nw : κ → ℕ} (hN : ∀ j, 0 < Nw j) (hNL : ∀ j, Nw j < L)
    (k₀ : κ → ℝ) {w : κ → ℝ} (hw0 : ∀ j, 0 ≤ w j)
    (hw : ∀ m ∈ boxWindowD lo Nw, ∀ j, |angleZD L m j - k₀ j| ≤ w j) {γ : κ → ℝ}
    (hγ : ∀ i, γ i < 1)
    (hp : (WithLp.toLp 2 (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
      (unitAmpD L J μ (flatAmpD lo Nw)) 0) : EuclideanSpace ℂ ((κ → ZMod L) × S)) ≠ 0)
    (a : κ) (hγa : 0 ≤ γ a) {θ : KTorus} (hθ : θ ∈ readyArc 2) (h0 : hf.lift θ.2 = 0)
    (hκ : 0 ≤ -2 * hf.deriv_periodic.lift θ.2) {t₁ t₂ t : ℝ} (h1 : 0 ≤ t₁) (h12 : t₁ ≤ t₂)
    (h2 : t₂ ≤ t)
    (hcos : ∀ s s', 0 ≤ s → s ≤ t₁ → t₂ ≤ s' → s' ≤ t →
      Real.cos (2 * Real.pi / L * groupVelD J μ k₀ a * (s' - s)) ≤ 2 * γ a ^ 2 - 1)
    (hbefore : -2 * hf.deriv_periodic.lift θ.2 * (flatTailD L J μ Nw w γ t₁ * t₁) ≤ 1 / 6)
    (hlo : 1 / 3 ≤ -2 * hf.deriv_periodic.lift θ.2
      * ((1 - flatTailD L J μ Nw w γ t) * (t - t₂)))
    (hhi : -2 * hf.deriv_periodic.lift θ.2
      * (flatTailD L J μ Nw w γ t₁ * t₁ + (t - t₁)) ≤ 2 / 3) :
    ((∀ u, 0 ≤ u → u ≤ t₁ →
      ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy (Matrix.reindex e e (latticeDiracHam (L := L) α β J μ))
          (Matrix.reindex e e (siteSetProj Prod.fst
            (sweptBoxD L J μ k₀ γ t₂ t : Set (κ → ZMod L)))) hf hc) u
        (idxArenaEquiv e (Projectivization.mk ℂ _ hp), θ)).2 ∉ displayArc)
      ∧ ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy (Matrix.reindex e e (latticeDiracHam (L := L) α β J μ))
          (Matrix.reindex e e (siteSetProj Prod.fst
            (sweptBoxD L J μ k₀ γ t₂ t : Set (κ → ZMod L)))) hf hc) t
        (idxArenaEquiv e (Projectivization.mk ℂ _ hp), θ)).2 ∈ displayArc)
      ∧ ((idxArenaEquiv e (Projectivization.mk ℂ _ hp), θ) : KSigma (N + 1))
        ∈ compatibleSet (arenaReadout (contMDiff_coupledEnergy
            (Matrix.reindex e e (latticeDiracHam (L := L) α β J μ))
            (Matrix.reindex e e (siteSetProj Prod.fst
              (sweptBoxD L J μ k₀ γ t₂ t : Set (κ → ZMod L)))) hf hc) p₀).semantics
          [TickReadout.startFact () t₁ 0, TickReadout.startFact () t 1] :=
  torusDetector_arrival_flatPacket e h he hn hμ hf hc p₀ lo hN hNL k₀ hw0 hw hγ hp
    (sweptBoxD L J μ k₀ γ t₂ t) hθ h0 hκ h1 h12 h2
    (fun s hs hs1 => Finset.disjoint_left.2 fun x hx hxs => by
      obtain ⟨s', hs'1, hs'2, hx'⟩ := mem_sweptBoxD.1 hx
      exact Finset.disjoint_left.1
        (movedBoxD_disjoint J μ k₀ a hγa (hcos s s' hs hs1 hs'1 hs'2)) hxs hx')
    (fun s hs hst x hx => mem_sweptBoxD.2 ⟨s, hs, hst, hx⟩) hbefore hlo hhi

omit [Nonempty S] in
/-- **The flat packet is not zero.** -/
theorem flatPacketD_ne_zero (h : IsCliffordFamily α β) {e₀ : S → ℂ} (he : β *ᵥ e₀ = e₀)
    (hn : star e₀ ⬝ᵥ e₀ = 1) {J μ : ℝ} (hμ : 0 < μ) (lo : κ → ℤ) {Nw : κ → ℕ}
    (hN : ∀ j, 0 < Nw j) (hNL : ∀ j, Nw j < L) :
    (WithLp.toLp 2 (packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
      (unitAmpD L J μ (flatAmpD lo Nw)) 0) : EuclideanSpace ℂ ((κ → ZMod L) × S)) ≠ 0 := by
  obtain ⟨-, hD⟩ := noWrapD_distinctD_of_box (L := L) (W := boxWindowD lo Nw) (lo := lo)
    (fun m hm j => by
      have a := (Fintype.mem_piFinset.1 hm) j
      have b := hNL j
      simp only [Finset.mem_Ico] at a
      omega)
  intro hz
  have hnorm := chainInnerD_packetD_unitAmpD (L := L) (J := J) h he hn hμ hD (flatAmpD lo Nw) 0
  have hzero : packetD (L := L) α β J μ e₀ (boxWindowD lo Nw)
      (unitAmpD L J μ (flatAmpD lo Nw)) 0 = 0 := by
    have := congrArg WithLp.ofLp hz
    simpa using this
  rw [hzero, sum_flatAmpD_sq lo hN] at hnorm
  simp [chainInnerD] at hnorm

end Swept

/-! ### The numbers -/

/-- For `J = 2`, `μ = 1` and the central momentum `(π/4, 0)` the group velocity along the
first axis is `8/3`. -/
theorem groupVelD_instance :
    groupVelD 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 0 = 8 / 3 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq : latticeED 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) ^ 2
      = 1 ^ 2 + ((2 * 2 * Real.sin (Real.pi / 4)) ^ 2 + (2 * 2 * Real.sin 0) ^ 2) := by
    rw [latticeED_sq, Fin.sum_univ_two]
    rfl
  rw [Real.sin_pi_div_four, Real.sin_zero] at hsq
  have hE : latticeED 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) = 3 :=
    (sq_eq_sq₀ (latticeED_nonneg _ _ _) (by norm_num)).1 (by rw [hsq]; nlinarith [h2])
  show 2 * 2 * (2 * 2 * Real.sin (Real.pi / 4)) * Real.cos (Real.pi / 4)
      / latticeED 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) = 8 / 3
  rw [hE, Real.sin_pi_div_four, Real.cos_pi_div_four]
  have : 2 * 2 * (2 * 2 * (Real.sqrt 2 / 2)) * (Real.sqrt 2 / 2) = 8 := by nlinarith [h2]
  rw [this]

/-- The tail of the flat packet with `400` momenta per axis, of width `400 · 2π/L`, sides
`3/4`, `J = 2`, `μ = 1`, in two dimensions. -/
theorem flatTailD_fin_two (L : ℕ) [NeZero L] (τ : ℝ) :
    flatTailD L 2 1 (fun _ : Fin 2 => 400) (fun _ => 400 * (2 * Real.pi / L))
        (fun _ => 3 / 4) τ
      = 8 * (1 / 400 + 4 * (2 * Real.pi / L) ^ 2 + 20836 * τ * (2 * Real.pi / L) ^ 2) := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  simp only [flatTailD, alignDefect, windowStepErrD, Fin.sum_univ_two, abs_two]
  push_cast
  field_simp
  ring

/-- With `L = 8M` and `M ≥ 4·10⁶` that tail is at most `1/10` up to the flow time `9M/4`. -/
theorem flatTailD_instance_le {L : ℕ} [NeZero L] {M : ℕ} (hL : L = 8 * M)
    (hM : 4000000 ≤ M) {τ : ℝ} (hτ : τ ≤ 9 * M / 4) :
    flatTailD L 2 1 (fun _ : Fin 2 => 400) (fun _ => 400 * (2 * Real.pi / L))
        (fun _ => 3 / 4) τ ≤ 1 / 10 := by
  have hMr : (4000000 : ℝ) ≤ M := by exact_mod_cast hM
  have hLr : (L : ℝ) = 8 * M := by rw [hL, Nat.cast_mul]; norm_num
  have hh : 2 * Real.pi / (L : ℝ) * M = Real.pi / 4 := by
    rw [hLr]
    field_simp
    ring
  rw [flatTailD_fin_two]
  generalize 2 * Real.pi / (L : ℝ) = x at hh ⊢
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have hpos : 0 < x := by
    by_contra hx
    rw [not_lt] at hx
    nlinarith
  have h5 : x * 4000000 ≤ x * M := mul_le_mul_of_nonneg_left hMr hpos.le
  have hs : x ≤ 2 / 10 ^ 7 := by linarith
  have h6 : τ * x ^ 2 ≤ 9 * Real.pi / 16 * x := by
    calc τ * x ^ 2 ≤ 9 * M / 4 * x ^ 2 := mul_le_mul_of_nonneg_right hτ (sq_nonneg x)
      _ = 9 / 4 * (x * M) * x := by ring
      _ = 9 * Real.pi / 16 * x := by rw [hh]; ring
  have h7 : 9 * Real.pi / 16 * x ≤ 9 * 3.15 / 16 * (2 / 10 ^ 7) :=
    mul_le_mul (by linarith) hs hpos.le (by norm_num)
  have h8 : x ^ 2 ≤ x := by nlinarith
  linarith

section Instance

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] {L : ℕ} [NeZero L]
  {α : Fin 2 → Matrix S S ℂ} {β : Matrix S S ℂ} {f : ℝ → ℝ} {N : ℕ}

omit [Nonempty S] in
/-- ★★★ **Arrival and display on the torus, with numbers.** Two dimensions, `L = 8M` sites
per axis with `M ≥ 4·10⁶`, `J = 2`, `μ = 1`. The flat packet has `400` momenta per axis
starting at `(M, 0)`, about the central momentum `(π/4, 0)`; the sides of its moving box are
`γ = 3/4`. The detector is on the sites the box sweeps during `[9M/8, 9M/4]`. On a fibre
where the profile vanishes and the rate is `−2 f'(θ₂) = 8π/(75M)`, from a ready pointer: the
pointer is not displayed at any flow time up to `3M/8`, it is displayed at `9M/4`, and the
counts `0` at `3M/8` and `1` at `9M/4` are a record history of the run's start. -/
theorem torusDetector_arrival_instance {M : ℕ} (hL : L = 8 * M) (hM : 4000000 ≤ M)
    (e : (Fin 2 → ZMod L) × S ≃ Fin (N + 1)) (h : IsCliffordFamily α β) {e₀ : S → ℂ}
    (he : β *ᵥ e₀ = e₀) (hn : star e₀ ⬝ᵥ e₀ = 1) (hf : Function.Periodic f 1)
    (hc : ContDiff ℝ ∞ f) (p₀ : CPN (N + 1))
    (hp : (WithLp.toLp 2 (packetD (L := L) α β 2 1 e₀
        (boxWindowD (![(M : ℤ), 0] : Fin 2 → ℤ) fun _ => 400)
        (unitAmpD L 2 1 (flatAmpD (![(M : ℤ), 0] : Fin 2 → ℤ) fun _ => 400)) 0) :
      EuclideanSpace ℂ ((Fin 2 → ZMod L) × S)) ≠ 0)
    {θ : KTorus} (hθ : θ ∈ readyArc 2) (h0 : hf.lift θ.2 = 0)
    (hrate : -2 * hf.deriv_periodic.lift θ.2 = 8 * Real.pi / (75 * M)) :
    ((∀ u, 0 ≤ u → u ≤ 3 * (M : ℝ) / 8 →
      ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy (Matrix.reindex e e (latticeDiracHam (L := L) α β 2 1))
          (Matrix.reindex e e (siteSetProj Prod.fst
            (sweptBoxD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) (fun _ => 3 / 4)
              (9 * (M : ℝ) / 8) (9 * (M : ℝ) / 4) : Set (Fin 2 → ZMod L)))) hf hc) u
        (idxArenaEquiv e (Projectivization.mk ℂ _ hp), θ)).2 ∉ displayArc)
      ∧ ((arenaForm_isSymplectic N).hamiltonianFlow
        (contMDiff_coupledEnergy (Matrix.reindex e e (latticeDiracHam (L := L) α β 2 1))
          (Matrix.reindex e e (siteSetProj Prod.fst
            (sweptBoxD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) (fun _ => 3 / 4)
              (9 * (M : ℝ) / 8) (9 * (M : ℝ) / 4) : Set (Fin 2 → ZMod L)))) hf hc)
        (9 * (M : ℝ) / 4)
        (idxArenaEquiv e (Projectivization.mk ℂ _ hp), θ)).2 ∈ displayArc)
      ∧ ((idxArenaEquiv e (Projectivization.mk ℂ _ hp), θ) : KSigma (N + 1))
        ∈ compatibleSet (arenaReadout (contMDiff_coupledEnergy
            (Matrix.reindex e e (latticeDiracHam (L := L) α β 2 1))
            (Matrix.reindex e e (siteSetProj Prod.fst
              (sweptBoxD L 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) (fun _ => 3 / 4)
                (9 * (M : ℝ) / 8) (9 * (M : ℝ) / 4) : Set (Fin 2 → ZMod L)))) hf hc)
            p₀).semantics
          [TickReadout.startFact () (3 * (M : ℝ) / 8) 0,
            TickReadout.startFact () (9 * (M : ℝ) / 4) 1] := by
  have hMr : (4000000 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hLr : (L : ℝ) = 8 * M := by rw [hL, Nat.cast_mul]; norm_num
  have hL0 : (0 : ℝ) < L := by rw [hLr]; linarith
  have hh : 2 * Real.pi / (L : ℝ) * M = Real.pi / 4 := by
    rw [hLr]
    field_simp
    ring
  have hπ1 := Real.pi_gt_d2
  have hπ2 := Real.pi_lt_d2
  have hw : ∀ m ∈ boxWindowD (![(M : ℤ), 0] : Fin 2 → ℤ) (fun _ => 400), ∀ j,
      |angleZD L m j - (![Real.pi / 4, 0] : Fin 2 → ℝ) j| ≤ 400 * (2 * Real.pi / L) := by
    intro m hm j
    have hmj := Fintype.mem_piFinset.1 hm j
    simp only [Finset.mem_Ico] at hmj
    have hk : (![Real.pi / 4, 0] : Fin 2 → ℝ) j
        = 2 * Real.pi * (((![(M : ℤ), 0] : Fin 2 → ℤ) j : ℤ) : ℝ) / L := by
      fin_cases j
      · simp only [Fin.zero_eta, Matrix.cons_val_zero, Int.cast_natCast]
        rw [hLr]
        field_simp
        ring
      · simp
    have hd0 : (0 : ℝ) ≤ (m j : ℝ) - (((![(M : ℤ), 0] : Fin 2 → ℤ) j : ℤ) : ℝ) :=
      sub_nonneg.2 (by exact_mod_cast hmj.1)
    have hd1 : (m j : ℝ) - (((![(M : ℤ), 0] : Fin 2 → ℤ) j : ℤ) : ℝ) ≤ 400 := by
      have h' : (m j : ℝ) < (((![(M : ℤ), 0] : Fin 2 → ℤ) j : ℤ) : ℝ) + 400 := by
        exact_mod_cast hmj.2
      linarith
    have hc0 : 0 ≤ 2 * Real.pi / (L : ℝ) := by positivity
    show |2 * Real.pi * (m j : ℝ) / L - (![Real.pi / 4, 0] : Fin 2 → ℝ) j| ≤ _
    rw [hk, ← sub_div, ← mul_sub, abs_of_nonneg (by positivity)]
    calc 2 * Real.pi * ((m j : ℝ) - (((![(M : ℤ), 0] : Fin 2 → ℤ) j : ℤ) : ℝ)) / L
        = 2 * Real.pi / L * ((m j : ℝ) - (((![(M : ℤ), 0] : Fin 2 → ℤ) j : ℤ) : ℝ)) := by
          ring
      _ ≤ 2 * Real.pi / L * 400 := mul_le_mul_of_nonneg_left hd1 hc0
      _ = 400 * (2 * Real.pi / L) := by ring
  have hκ : 0 ≤ -2 * hf.deriv_periodic.lift θ.2 := by
    rw [hrate]
    positivity
  have hT := flatTailD_instance_le (L := L) hL hM (τ := 9 * (M : ℝ) / 4) le_rfl
  have hε := flatTailD_instance_le (L := L) hL hM (τ := 3 * (M : ℝ) / 8) (by linarith)
  have hcos : ∀ s s' : ℝ, 0 ≤ s → s ≤ 3 * (M : ℝ) / 8 → 9 * (M : ℝ) / 8 ≤ s' →
      s' ≤ 9 * (M : ℝ) / 4 →
      Real.cos (2 * Real.pi / L * groupVelD 2 1 (![Real.pi / 4, 0] : Fin 2 → ℝ) 0 * (s' - s))
        ≤ 2 * (3 / 4 : ℝ) ^ 2 - 1 := by
    intro s s' hs hs1 hs'1 hs'2
    rw [groupVelD_instance]
    have hc0 : 0 ≤ 2 * Real.pi / (L : ℝ) * (8 / 3) := by positivity
    have e1 : 2 * Real.pi / (L : ℝ) * (8 / 3) * (3 * M / 4) = Real.pi / 2 := by
      have : 2 * Real.pi / (L : ℝ) * (8 / 3) * (3 * M / 4)
          = 2 * (2 * Real.pi / (L : ℝ) * M) := by ring
      rw [this, hh]
      ring
    have e2 : 2 * Real.pi / (L : ℝ) * (8 / 3) * (9 * M / 4) = Real.pi + Real.pi / 2 := by
      have : 2 * Real.pi / (L : ℝ) * (8 / 3) * (9 * M / 4)
          = 6 * (2 * Real.pi / (L : ℝ) * M) := by ring
      rw [this, hh]
      ring
    have hlow := mul_le_mul_of_nonneg_left (by linarith : 3 * (M : ℝ) / 4 ≤ s' - s) hc0
    have hupp := mul_le_mul_of_nonneg_left (by linarith : s' - s ≤ 9 * (M : ℝ) / 4) hc0
    rw [e1] at hlow
    rw [e2] at hupp
    have := Real.cos_nonpos_of_pi_div_two_le_of_le hlow hupp
    linarith
  have r1 : ∀ ε : ℝ, 8 * Real.pi / (75 * (M : ℝ)) * (ε * (3 * M / 8)) = Real.pi / 25 * ε :=
    fun ε => by
      field_simp
      ring
  have r2 : ∀ q : ℝ, 8 * Real.pi / (75 * (M : ℝ)) * (q * (9 * M / 4 - 9 * M / 8))
      = 3 * Real.pi / 25 * q := fun q => by
    field_simp
    ring
  have r3 : ∀ ε : ℝ, 8 * Real.pi / (75 * (M : ℝ)) * (ε * (3 * M / 8) + (9 * M / 4 - 3 * M / 8))
      = Real.pi / 25 * (ε + 5) := fun ε => by
    field_simp
    ring
  refine torusDetector_arrival_sweptBox e h he hn one_pos hf hc p₀ _ (fun _ => by norm_num)
    (fun _ => by omega) _ (fun _ => by positivity) hw (fun _ => by norm_num) hp 0
    (by norm_num) hθ h0 hκ (by positivity) (by linarith) (by linarith) hcos ?_ ?_ ?_
  · rw [hrate, r1]
    have := mul_le_mul_of_nonneg_left hε (by positivity : (0 : ℝ) ≤ Real.pi / 25)
    linarith
  · rw [hrate, r2]
    have := mul_le_mul_of_nonneg_left (by linarith : (9 / 10 : ℝ) ≤ 1 - flatTailD L 2 1
      (fun _ : Fin 2 => 400) (fun _ => 400 * (2 * Real.pi / L)) (fun _ => 3 / 4)
      (9 * (M : ℝ) / 4)) (by positivity : (0 : ℝ) ≤ 3 * Real.pi / 25)
    linarith
  · rw [hrate, r3]
    have := mul_le_mul_of_nonneg_left (by linarith : flatTailD L 2 1
      (fun _ : Fin 2 => 400) (fun _ => 400 * (2 * Real.pi / L)) (fun _ => 3 / 4)
      (3 * (M : ℝ) / 8) + 5 ≤ 51 / 10) (by positivity : (0 : ℝ) ≤ Real.pi / 25)
    linarith

end Instance

end CSD.RecordLayer

end
