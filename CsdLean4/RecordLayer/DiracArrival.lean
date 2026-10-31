/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracDetector
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A distant detector written on the packet's arrival

**Category:** 7-SigmaLayer (the record layer). BACKLOG #265 (residue of #252's smallest part).

#252's `dirac_detector` wrote the detector where a two-mode packet's weight starts, on an arena that
carried only the window's amplitudes. Here the arena is **the whole chain**, every state of `ℂ^{2L}`
evolved by `e^{−itH}`, with a detector on every region of sites. A detector **half a ring away** is
written **on the packet's arrival**: not before it can be near, and by the time it is predicted
inside.

## The whole chain

* ★ `exp_mulVec_of_mulVec_eq_smul` — the exponential of a matrix acts on an eigenvector by the
  exponential of its eigenvalue (the series, mapped by `M ↦ M v`);
* `chainProp` (`e^{−itH}`), `chainProp_zero`, `chainProp_add`, `continuous_chainProp`,
  ★ `chainProp_mulVec_mode`, ★★ `chainProp_packet` — **the whole chain carries every packet exactly**;
* `regionWeight`, `regionWeight_nonneg`, `sum_siteWeight`, `regionWeight_add_compl`, `WholeArena`
  (the state × a register for every region), `wholeFlow`, `state_wholeFlow`, `register_wholeFlow`,
  `wholeFlow_zero`, `wholeFlow_add`, `continuous_wholeFlow`, ★ `measurable_wholeFlow`, `wholeEvolve`,
  `wholeEvolve_self`, `wholeEvolve_comp`, `integral_regionWeight_mono`, `regionRead`,
  `measurable_regionRead`; ★★★ `regionDetector` — **a region's detector as an `ActualOccurrence`**
  of the whole chain's evolution.

## Where the weight can be

* ★ `transPhase_eq_sum` — the translation phase is the sites' weights on the unit circle,
  `T = Σ_k w_k e^{2πik/L}`;
* ★★ `regionWeight_mul_le` — **a region whose sites all lie at `Re(ū e^{2πik/L}) ≤ γ` from a
  direction `u` holds at most `(⟨ψ, ψ⟩ − Re(ū T))/(1 − γ)`**; `re_star_exp_mul_toCircle`;
* along a packet of ~~#261~~'s `dirac_packet_limit`, with `Ω = (2π/ℓ) v(p₀)`:
  ★★ `regionWeight_ringPacket_le` — **far from the predicted direction `Ωt` there is little
  weight**, at most `(1 − Re T(0) + |t| · limitErr)/(1 − γ)`; ★★ `le_regionWeight_ringPacket` —
  **a region holding every site near it has nearly all of it**; `re_transPhase_ringPacket_ge`.

## A packet crossing to the far half

* `cos_le_half`, `farHalf` (the sites at angle `[π/2, 3π/2]`), `crossPacket` (`16` momenta `m/1000`,
  `4000 ≤ m < 4016`, on a ring of length `ℓ = 2000π`, `c = 1`, `μ = 3`, flat amplitudes), `crossHop`,
  `vRel_cross` (`v = 4/5`), `omega_cross` (`Ω = 1/1250`), `cross_spread`, `cross_win`, `cross_norm`;
  ★ `cross_budget` — **over the crossing the error budget stays below `1/8`** with at least
  `640000` sites; `angle_farHalf`;
* ★★ `regionWeight_cross_far` (**at most a quarter of the weight on the far half for
  `0 ≤ t ≤ 625π/3`**), ★★ `regionWeight_cross_near` (**at least three quarters for
  `3125π/3 ≤ t ≤ 4375π/3`**); `chainProp_crossPacket`, `cross_before`, `cross_after`;
  ★★★ `crossDetector`;
* ★★★ `dirac_arrival` — **the capstone**: the whole chain carries the packet, normalised, at
  `v = 4/5`; the far half's detector is an actual occurrence written over `[625π/3, 4375π/3]`. The
  far half begins `d = 500π` (a quarter ring) from the start: the predicted arrival `d/v = 625π`
  lies inside the interval, which opens at `(d − ℓ/6)/v`.

## The findings

1. **The candidate's packet writes a distant record on its arrival**, on the arena of the whole chain:
   the detector half a ring away is not written while the packet cannot be near, and is written once it
   is predicted inside.
2. **The translation phase alone locates the weight.** `|T|` close to `1` forces the weight into an
   arc about `arg T`; the drift theorem moves that arc at `v`. No site-by-site propagation is used.

## Honest scope

⚠️ **Little weight, not none.** The before-bound says the far half holds at most a quarter of the
packet's weight before `625π/3`; the threshold is set above what that can deliver. It is not a
light-cone statement: a packet of `16` modes is spread over the ring, and no bound vanishing outside a
cone is proved.

⚠️ **The resolution is coarse.** The detector covers half the ring and the write interval
`[625π/3, 4375π/3]` brackets the arrival `625π` within a factor of seven; the concentration at
`cos ≤ 1/2` is `±ℓ/6`. Narrow detectors and a sharp arrival time need a better-localised packet
(#263) or a causal bound → #268.

⚠️ **The detector law is stated, not generated** (test detectors, no back-reaction — #251), and
every region's register rises with its Born weight: an intensity, not one click (#266).

⚠️ **The instance is one set of numbers**: `ℓ = 2000π`, at least `640000` sites, `16` modes; the
general bounds (`regionWeight_ringPacket_le`, `le_regionWeight_ringPacket`) hold for any packet of
`dirac_packet_limit`.

References: `specs/BACKLOG.md` #265, #252, #261, #263, #256, #251, #266, #268, #39;
`RecordLayer/DiracDetector.lean` (`siteWeight`, `packetDetector`); `CV/DiracPacketLimit.lean`
(`dirac_packet_limit`, `ringPacket`, `limitErr`, `re_transPhase_unitAmp_ge`, `flat_sums`);
`CV/DiracPacket.lean` (`packet`, `transPhase`, `transMul`); `CV/DiracClockChain.lean` (`diracHam`,
`diracHam_mulVec_diracMode`); `RecordLayer/RecordOccurrence.lean` (`ActualOccurrence`); R. Resta,
PRL 80 (1998) 1800 (the position on a ring as a phase).
-/

@[expose] public section

open MeasureTheory Set CSD.CV Complex
open scoped Matrix Matrix.Norms.L2Operator

namespace CSD.RecordLayer

open CSD.SigmaLayer

/-! ### The exponential on an eigenvector -/

/-- ★ **The exponential of a matrix acts on an eigenvector by the exponential of its eigenvalue.** -/
theorem exp_mulVec_of_mulVec_eq_smul {m : Type*} [Fintype m] [DecidableEq m] {A : Matrix m m ℂ}
    {v : m → ℂ} {c : ℂ} (h : A *ᵥ v = c • v) :
    NormedSpace.exp A *ᵥ v = NormedSpace.exp c • v := by
  have hpow : ∀ n : ℕ, (A ^ n) *ᵥ v = c ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul, pow_succ, mul_comm]
  have hA := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  have hc := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c
  let g : Matrix m m ℂ →+ (m → ℂ) :=
    { toFun := fun M => M *ᵥ v
      map_zero' := Matrix.zero_mulVec v
      map_add' := fun M N => Matrix.add_mulVec M N v }
  have hg : Continuous g := Continuous.matrix_mulVec continuous_id continuous_const
  have h1 := hA.map g hg
  have h2 := hc.smul_const v
  refine h1.unique ?_
  convert h2 using 1
  funext n
  simp only [Function.comp_apply, g, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.smul_mulVec,
    hpow, smul_smul, smul_eq_mul]

variable {L : ℕ} [NeZero L]

/-! ### The whole chain -/

/-- **The whole chain's evolution** `e^{−itH}` on `ℂ^{2L}`. -/
noncomputable def chainProp (J μ t : ℝ) : Matrix (ZMod L × Fin 2) (ZMod L × Fin 2) ℂ :=
  NormedSpace.exp ((-(I * t)) • diracHam J μ)

theorem chainProp_zero (J μ : ℝ) : chainProp (L := L) J μ 0 = 1 := by
  simp [chainProp]

theorem chainProp_add (J μ s t : ℝ) :
    chainProp (L := L) J μ (s + t) = chainProp J μ t * chainProp J μ s := by
  rw [chainProp, chainProp, chainProp, ← Matrix.exp_add_of_commute _ _
    (((Commute.refl (diracHam (L := L) J μ)).smul_left _).smul_right _), ← add_smul]
  congr 1
  push_cast
  ring_nf

theorem continuous_chainProp (J μ : ℝ) : Continuous fun t => chainProp (L := L) J μ t := by
  have h : Continuous fun u : ℂ => NormedSpace.exp (u • diracHam (L := L) J μ) :=
    continuous_iff_continuousAt.2 fun u =>
      (hasDerivAt_exp_smul_const' (𝕂 := ℂ) (diracHam (L := L) J μ) u).continuousAt
  exact h.comp (by fun_prop)

/-- ★ **A mode evolves by its phase on the whole chain.** -/
theorem chainProp_mulVec_mode (J μ t : ℝ) (m : ℤ) :
    chainProp (L := L) J μ t *ᵥ diracMode J μ (m : ZMod L)
      = exp (-(I * bandE J μ (angleZ L m)) * t) • diracMode J μ (m : ZMod L) := by
  have h : ((-(I * t)) • diracHam (L := L) J μ) *ᵥ diracMode J μ (m : ZMod L)
      = (-(I * t) * bandE J μ (angleZ L m)) • diracMode J μ (m : ZMod L) := by
    rw [Matrix.smul_mulVec, diracHam_mulVec_diracMode, dispE_modeS_intCast, smul_smul]
  rw [chainProp, exp_mulVec_of_mulVec_eq_smul h, ← Complex.exp_eq_exp_ℂ]
  congr 2
  ring

/-- ★★ **The whole chain carries every packet**: `e^{−itH}` applied to the packet at time `0` is the
packet at time `t`. -/
theorem chainProp_packet (J μ : ℝ) (W : Finset ℤ) (a : ℤ → ℂ) (t : ℝ) :
    chainProp (L := L) J μ t *ᵥ packet (L := L) J μ W a 0 = packet (L := L) J μ W a t := by
  unfold packet
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.mulVec_smul, chainProp_mulVec_mode, smul_smul]
  congr 1
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]

/-! ### Regions and the whole-chain arena -/

/-- **The weight of a chain state on a region of sites.** -/
noncomputable def regionWeight (ψ : ZMod L × Fin 2 → ℂ) (A : Finset (ZMod L)) : ℝ :=
  ∑ k ∈ A, siteWeight ψ k

omit [NeZero L] in
theorem regionWeight_nonneg (ψ : ZMod L × Fin 2 → ℂ) (A : Finset (ZMod L)) :
    0 ≤ regionWeight ψ A :=
  Finset.sum_nonneg fun k _ => siteWeight_nonneg ψ k

/-- The sites' weights add up to the norm. -/
theorem sum_siteWeight (ψ : ZMod L × Fin 2 → ℂ) :
    ∑ k, siteWeight ψ k = (chainInner ψ ψ).re := by
  rw [re_chainInner_self, Fintype.sum_prod_type]
  rfl

/-- **A region and its complement hold the whole norm.** -/
theorem regionWeight_add_compl (ψ : ZMod L × Fin 2 → ℂ) (A : Finset (ZMod L)) :
    regionWeight ψ A + regionWeight ψ Aᶜ = (chainInner ψ ψ).re := by
  rw [regionWeight, regionWeight, Finset.sum_add_sum_compl, sum_siteWeight]

/-- **The detector arena on the whole chain**: the chain's state and a register for every region. -/
abbrev WholeArena (L : ℕ) : Type := (ZMod L × Fin 2 → ℂ) × (Finset (ZMod L) → ℝ)

theorem continuous_chainProp_mulVec (J μ : ℝ) :
    Continuous fun p : (ZMod L × Fin 2 → ℂ) × ℝ => chainProp (L := L) J μ p.2 *ᵥ p.1 :=
  Continuous.matrix_mulVec ((continuous_chainProp J μ).comp continuous_snd) continuous_fst

omit [NeZero L] in
theorem continuous_regionWeight (A : Finset (ZMod L)) :
    Continuous fun ψ : ZMod L × Fin 2 → ℂ => regionWeight ψ A :=
  continuous_finsetSum _ fun k _ => continuous_siteWeight k

section Flow

variable (J μ g : ℝ)

/-- **The whole chain with its region detectors**: the state evolves by `e^{−itH}`, and the register
of region `A` integrates the state's weight on `A` with gain `g`. -/
noncomputable def wholeFlow (t : ℝ) (x : WholeArena L) : WholeArena L :=
  (chainProp J μ t *ᵥ x.1,
    fun A => x.2 A + g * ∫ s in (0 : ℝ)..t, regionWeight (chainProp J μ s *ᵥ x.1) A)

theorem state_wholeFlow (t : ℝ) (x : WholeArena L) :
    (wholeFlow J μ g t x).1 = chainProp J μ t *ᵥ x.1 := rfl

theorem register_wholeFlow (t : ℝ) (x : WholeArena L) (A : Finset (ZMod L)) :
    (wholeFlow J μ g t x).2 A
      = x.2 A + g * ∫ s in (0 : ℝ)..t, regionWeight (chainProp J μ s *ᵥ x.1) A := rfl

theorem continuous_regionWeight_chainProp (ψ : ZMod L × Fin 2 → ℂ) (A : Finset (ZMod L)) :
    Continuous fun s => regionWeight (chainProp (L := L) J μ s *ᵥ ψ) A :=
  (continuous_regionWeight A).comp
    ((continuous_chainProp_mulVec J μ).comp (continuous_const.prodMk continuous_id))

theorem wholeFlow_zero (x : WholeArena L) : wholeFlow J μ g 0 x = x := by
  ext
  · simp [wholeFlow, chainProp_zero]
  · simp [wholeFlow]

theorem wholeFlow_add (s t : ℝ) (x : WholeArena L) :
    wholeFlow J μ g (s + t) x = wholeFlow J μ g t (wholeFlow J μ g s x) := by
  ext A
  · simp only [wholeFlow, chainProp_add, Matrix.mulVec_mulVec]
  · simp only [wholeFlow, Matrix.mulVec_mulVec, ← chainProp_add]
    have hi : ∀ a b : ℝ, IntervalIntegrable
        (fun u => regionWeight (chainProp (L := L) J μ u *ᵥ x.1) A) volume a b :=
      fun a b => (continuous_regionWeight_chainProp J μ x.1 A).intervalIntegrable a b
    have hs : (∫ u in (0 : ℝ)..t, regionWeight (chainProp (L := L) J μ (s + u) *ᵥ x.1) A)
        = ∫ u in s..s + t, regionWeight (chainProp (L := L) J μ u *ᵥ x.1) A := by
      rw [intervalIntegral.integral_comp_add_left
        (fun u => regionWeight (chainProp (L := L) J μ u *ᵥ x.1) A) s, add_zero]
    rw [hs, ← intervalIntegral.integral_add_adjacent_intervals (hi 0 s) (hi s (s + t))]
    ring

theorem continuous_wholeFlow (t : ℝ) : Continuous (wholeFlow (L := L) J μ g t) := by
  refine Continuous.prodMk ?_ ?_
  · exact (continuous_chainProp_mulVec J μ).comp (continuous_fst.prodMk continuous_const)
  · refine continuous_pi fun A => ((continuous_apply A).comp continuous_snd).add
      (continuous_const.mul ?_)
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (x : WholeArena L) s => regionWeight (chainProp J μ s *ᵥ x.1) A) ?_ 0 t
    exact (continuous_regionWeight A).comp
      ((continuous_chainProp_mulVec J μ).comp (continuous_fst.fst.prodMk continuous_snd))

/-- ★ **Each step is measurable.** -/
theorem measurable_wholeFlow (t : ℝ) : Measurable (wholeFlow (L := L) J μ g t) :=
  (continuous_wholeFlow J μ g t).measurable

/-- The two-time evolution. -/
noncomputable def wholeEvolve (s t : OnticTime) : WholeArena L → WholeArena L :=
  wholeFlow J μ g (t - s)

theorem wholeEvolve_self (t : OnticTime) :
    wholeEvolve J μ g t t = (id : WholeArena L → WholeArena L) := by
  funext x
  simp only [wholeEvolve, sub_self, wholeFlow_zero, id]

theorem wholeEvolve_comp (s t u : OnticTime) :
    wholeEvolve J μ g t u ∘ wholeEvolve J μ g s t
      = (wholeEvolve J μ g s u : WholeArena L → WholeArena L) := by
  funext x
  simp only [wholeEvolve, Function.comp]
  rw [show u - s = (t - s) + (u - t) by ring, wholeFlow_add]

theorem integral_regionWeight_mono (ψ : ZMod L × Fin 2 → ℂ) (A : Finset (ZMod L)) {t₁ t : ℝ}
    (h : t₁ ≤ t) :
    (∫ s in (0 : ℝ)..t₁, regionWeight (chainProp (L := L) J μ s *ᵥ ψ) A)
      ≤ ∫ s in (0 : ℝ)..t, regionWeight (chainProp (L := L) J μ s *ᵥ ψ) A := by
  have hi : ∀ u v : ℝ, IntervalIntegrable
      (fun s => regionWeight (chainProp (L := L) J μ s *ᵥ ψ) A) volume u v :=
    fun u v => (continuous_regionWeight_chainProp J μ ψ A).intervalIntegrable u v
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 t₁) (hi t₁ t)]
  have := intervalIntegral.integral_nonneg (μ := volume) h fun u _ =>
    regionWeight_nonneg (chainProp (L := L) J μ u *ᵥ ψ) A
  linarith

/-- **The region detector's readout**: `1` once the register of `A` has reached `θ`. -/
noncomputable def regionRead (θ : ℝ) (A : Finset (ZMod L)) (x : WholeArena L) : ℕ :=
  if θ ≤ x.2 A then 1 else 0

omit [NeZero L] in
theorem measurable_regionRead (θ : ℝ) (A : Finset (ZMod L)) :
    Measurable (regionRead (L := L) θ A) := by
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le measurable_const ((measurable_pi_apply A).comp measurable_snd)

/-- ★★★ **A region's detector as an actual occurrence of the whole chain's evolution**: prepared at
zero, not written while its register is below `θ` (`hbefore`), written once it reaches it
(`hafter`), and held for any window. -/
noncomputable def regionDetector (θ : ℝ) (A : Finset (ZMod L)) (ψ : ZMod L × Fin 2 → ℂ)
    (det₀ : Finset (ZMod L) → ℝ) (hdet : det₀ A = 0) {τ₀ τ₁ w : ℝ} (hτ₀ : 0 ≤ τ₀) (hτ : τ₀ ≤ τ₁)
    (hw : 0 ≤ w) (hg : 0 ≤ g)
    (hbefore : ∀ t, 0 ≤ t → t < τ₀ →
      g * ∫ s in (0 : ℝ)..t, regionWeight (chainProp (L := L) J μ s *ᵥ ψ) A < θ)
    (hafter : θ ≤ g * ∫ s in (0 : ℝ)..τ₁, regionWeight (chainProp (L := L) J μ s *ᵥ ψ) A) :
    ActualOccurrence (WholeArena L) ℕ L where
  evolve := wholeEvolve J μ g
  evolve_self := wholeEvolve_self J μ g
  evolve_comp := wholeEvolve_comp J μ g
  measurable_evolve := fun s t => measurable_wholeFlow J μ g (t - s)
  readout := regionRead θ A
  measurable_readout := measurable_regionRead θ A
  ready := {x | x.2 A = 0}
  measurableSet_ready := measurableSet_eq_fun ((measurable_pi_apply A).comp measurable_snd)
    measurable_const
  prep := (ψ, det₀)
  prep_mem := hdet
  site := A.image siteFin
  start := 0
  value := 1
  writeStart := τ₀
  writeEnd := τ₁
  window := w
  isWrite :=
    { start_le := hτ₀
      interval := hτ
      window_nonneg := hw
      before := fun t ht0 ht => by
        show regionRead θ A (wholeFlow J μ g (t - 0) (ψ, det₀)) ≠ 1
        rw [sub_zero, regionRead, register_wholeFlow]
        show (if θ ≤ det₀ A + _ then 1 else 0) ≠ 1
        rw [hdet, zero_add]
        split_ifs with h
        · exact absurd h (not_le.2 (hbefore t ht0 ht))
        · decide
      holds := fun t ht₁ _ => by
        show regionRead θ A (wholeFlow J μ g (t - 0) (ψ, det₀)) = 1
        rw [sub_zero, regionRead, register_wholeFlow]
        show (if θ ≤ det₀ A + _ then 1 else 0) = 1
        rw [hdet, zero_add]
        split_ifs with h
        · rfl
        refine absurd (hafter.trans ?_) h
        exact mul_le_mul_of_nonneg_left (integral_regionWeight_mono J μ ψ A ht₁) hg }

end Flow

/-! ### Where the weight can be -/

/-- **The translation phase is the sites' weights on the unit circle**: `T = Σ_k w_k e^{2πik/L}`. -/
theorem transPhase_eq_sum (ψ : ZMod L × Fin 2 → ℂ) :
    transPhase ψ = ∑ k, (siteWeight ψ k : ℂ) * (ZMod.toCircle k : ℂ) := by
  rw [transPhase, chainInner, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [siteWeight, Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [transMul, Complex.star_def]
  have h := Complex.conj_mul' (ψ (k, c))
  push_cast
  linear_combination (ZMod.toCircle k : ℂ) * h

/-- ★★ **Weight far from a direction is bounded by the translation phase**: for a unit `u` and a
region `B` whose sites all make `Re(ū e^{2πik/L}) ≤ γ`, the weight on `B` times `1 − γ` is at most
`⟨ψ, ψ⟩ − Re(ū T)`. The farther `T` points from the sites of `B`, the less weight is on `B`. -/
theorem regionWeight_mul_le (ψ : ZMod L × Fin 2 → ℂ) {u : ℂ} (hu : ‖u‖ = 1)
    {B : Finset (ZMod L)} {γ : ℝ} (hB : ∀ k ∈ B, (star u * (ZMod.toCircle k : ℂ)).re ≤ γ) :
    regionWeight ψ B * (1 - γ) ≤ (chainInner ψ ψ).re - (star u * transPhase ψ).re := by
  have hle1 : ∀ k : ZMod L, (star u * (ZMod.toCircle k : ℂ)).re ≤ 1 := fun k =>
    (Complex.re_le_norm _).trans (by rw [norm_mul, norm_star, hu, Circle.norm_coe, one_mul])
  have hterm : ∀ k : ZMod L, (star u * ((siteWeight ψ k : ℂ) * (ZMod.toCircle k : ℂ))).re
      = siteWeight ψ k * (star u * (ZMod.toCircle k : ℂ)).re := fun k => by
    rw [show star u * ((siteWeight ψ k : ℂ) * (ZMod.toCircle k : ℂ))
        = (siteWeight ψ k : ℂ) * (star u * (ZMod.toCircle k : ℂ)) by ring, Complex.re_ofReal_mul]
  rw [transPhase_eq_sum, Finset.mul_sum, Complex.re_sum, ← sum_siteWeight]
  simp only [hterm]
  rw [← Finset.sum_sub_distrib]
  calc regionWeight ψ B * (1 - γ)
      = ∑ k ∈ B, siteWeight ψ k * (1 - γ) := by rw [regionWeight, Finset.sum_mul]
    _ ≤ ∑ k ∈ B, (siteWeight ψ k - siteWeight ψ k * (star u * (ZMod.toCircle k : ℂ)).re) :=
        Finset.sum_le_sum fun k hk => by
          have := mul_le_mul_of_nonneg_left (hB k hk) (siteWeight_nonneg ψ k)
          linarith
    _ ≤ ∑ k, (siteWeight ψ k - siteWeight ψ k * (star u * (ZMod.toCircle k : ℂ)).re) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => by
          have := mul_le_mul_of_nonneg_left (hle1 k) (siteWeight_nonneg ψ k)
          linarith

/-- The direction `e^{iφ}` read against site `k`: `Re(e^{−iφ} e^{2πik/L}) = cos(2πk/L − φ)`. -/
theorem re_star_exp_mul_toCircle (φ : ℝ) (k : ZMod L) :
    (star (exp (I * (φ : ℂ))) * (ZMod.toCircle k : ℂ)).re
      = Real.cos (2 * Real.pi * k.val / L - φ) := by
  rw [ZMod.toCircle_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  have h : (starRingEnd ℂ) (I * (φ : ℂ)) + 2 * (Real.pi : ℂ) * I * (k.val : ℂ) / (L : ℂ)
      = ((2 * Real.pi * k.val / L - φ : ℝ) : ℂ) * I := by
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [h, Complex.exp_ofReal_mul_I_re]

/-! ### The packet's weight, region by region -/

/-- ★★ **Far from where the packet is predicted to be, it has little weight.** For a packet of
`dirac_packet_limit` and a region `B` whose sites all lie at `cos(2πk/L − Ωt) ≤ γ < 1` from the
predicted direction `Ωt`, `Ω = (2π/ℓ) v(p₀)`, the weight on `B` times `1 − γ` is at most
`1 − Re T(0) + |t| · limitErr`. -/
theorem regionWeight_ringPacket_le {c μ ℓ P D p₀ : ℝ} (hc : 0 < c) (hμ : 0 < μ) (hℓ : 0 < ℓ)
    (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D) {W : Finset ℤ} {lo : ℤ}
    (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L) (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D)
    (β : ℤ → ℂ) (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) {B : Finset (ZMod L)} {γ : ℝ} (t : ℝ)
    (hB : ∀ k ∈ B, Real.cos (2 * Real.pi * k.val / L - 2 * Real.pi / ℓ * vRel c μ (c * p₀) * t)
      ≤ γ) :
    regionWeight (ringPacket (L := L) c μ ℓ W β t) B * (1 - γ)
      ≤ 1 - (transPhase (ringPacket (L := L) c μ ℓ W β 0)).re
        + |t| * limitErr c μ ℓ D P (ℓ / L) := by
  obtain ⟨hn, -, hdrift, -, -⟩ := dirac_packet_limit hc hμ hℓ hp₀ hD0 hWin hWD β hβ
  set Ω := 2 * Real.pi / ℓ * vRel c μ (c * p₀)
  set u : ℂ := exp (I * ((Ω * t : ℝ) : ℂ))
  have hu : ‖u‖ = 1 := by
    simp only [u]
    rw [show I * ((Ω * t : ℝ) : ℂ) = ((Ω * t : ℝ) : ℂ) * I by ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hu' : exp (I * (((Ω : ℝ) : ℂ) * t)) = u := by
    simp only [u]
    push_cast
    ring_nf
  have hB' : ∀ k ∈ B, (star u * (ZMod.toCircle k : ℂ)).re ≤ γ := fun k hk => by
    rw [re_star_exp_mul_toCircle]
    exact hB k hk
  have h := regionWeight_mul_le (ringPacket (L := L) c μ ℓ W β t) hu hB'
  rw [hn t, Complex.one_re] at h
  set T0 := transPhase (ringPacket (L := L) c μ ℓ W β 0)
  set Tt := transPhase (ringPacket (L := L) c μ ℓ W β t)
  have hsu : star u * u = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hu]
    norm_num
  have hsplit : (star u * Tt).re = T0.re + (star u * (Tt - u * T0)).re := by
    rw [mul_sub, ← mul_assoc, hsu, one_mul, Complex.sub_re]
    ring
  have hbound : -(|t| * limitErr c μ ℓ D P (ℓ / L)) ≤ (star u * (Tt - u * T0)).re := by
    have h1 := Complex.abs_re_le_norm (star u * (Tt - u * T0))
    rw [norm_mul, norm_star, hu, one_mul] at h1
    have h2 := hdrift t
    rw [hu'] at h2
    have h3 := neg_abs_le (star u * (Tt - u * T0)).re
    linarith
  linarith

/-- ★★ **Near where the packet is predicted to be, a region has nearly all the weight**: if every
site outside `A` lies at `cos(2πk/L − Ωt) ≤ γ < 1`, the weight on `A` is at least
`1 − (1 − Re T(0) + |t| · limitErr)/(1 − γ)`. -/
theorem le_regionWeight_ringPacket {c μ ℓ P D p₀ : ℝ} (hc : 0 < c) (hμ : 0 < μ) (hℓ : 0 < ℓ)
    (hp₀ : |p₀| ≤ P) (hD0 : 0 ≤ D) {W : Finset ℤ} {lo : ℤ}
    (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L) (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D)
    (β : ℤ → ℂ) (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1) {A : Finset (ZMod L)} {γ : ℝ} (hγ : γ < 1)
    (t : ℝ)
    (hA : ∀ k ∉ A, Real.cos (2 * Real.pi * k.val / L - 2 * Real.pi / ℓ * vRel c μ (c * p₀) * t)
      ≤ γ) :
    1 - (1 - (transPhase (ringPacket (L := L) c μ ℓ W β 0)).re
        + |t| * limitErr c μ ℓ D P (ℓ / L)) / (1 - γ)
      ≤ regionWeight (ringPacket (L := L) c μ ℓ W β t) A := by
  have h := regionWeight_ringPacket_le hc hμ hℓ hp₀ hD0 hWin hWD β hβ (B := Aᶜ) t
    fun k hk => hA k (Finset.mem_compl.1 hk)
  have hsum := regionWeight_add_compl (ringPacket (L := L) c μ ℓ W β t) A
  rw [(dirac_packet_limit hc hμ hℓ hp₀ hD0 hWin hWD β hβ).1 t, Complex.one_re] at hsum
  have hpos : 0 < 1 - γ := by linarith
  rw [← le_div_iff₀ hpos] at h
  linarith

/-- **The packet's localisation, as a real part**: for real nonnegative coefficients,
`Re T(0) ≥ (1 − (πc/(ℓμ))²) Σ_m β_{m+1} β_m`. -/
theorem re_transPhase_ringPacket_ge {c μ ℓ : ℝ} (hμ : 0 < μ) (hℓ : 0 < ℓ) {W : Finset ℤ}
    (hW : NoWrap L W) (β : ℤ → ℝ) (hβ : ∀ m, 0 ≤ β m) :
    (1 - (Real.pi * c / (ℓ * μ)) ^ 2) * ∑ m ∈ W.filter (fun m => m + 1 ∈ W), β (m + 1) * β m
      ≤ (transPhase (ringPacket (L := L) c μ ℓ W (fun m => (β m : ℂ)) 0)).re := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have h := re_transPhase_unitAmp_ge (L := L) (J := scaledHop c (ℓ / L)) hμ hW β hβ
  have he : 2 * Real.pi * scaledHop c (ℓ / L) / (L * μ) = Real.pi * c / (ℓ * μ) := by
    rw [scaledHop]
    field_simp
  rwa [he] at h

/-! ### A packet crossing to the far half of the ring -/

/-- `cos x ≤ 1/2` whenever `π/3 ≤ |x| ≤ 5π/3`. -/
theorem cos_le_half {x : ℝ} (h1 : Real.pi / 3 ≤ |x|) (h2 : |x| ≤ 5 * Real.pi / 3) :
    Real.cos x ≤ 1 / 2 := by
  rw [← Real.cos_abs]
  have hhalf : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  by_cases hx : |x| ≤ Real.pi
  · rw [← hhalf]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hx h1
  · rw [← Real.cos_two_pi_sub, ← hhalf]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)

/-- **The far half of the ring**: the sites at angle `2πk/L ∈ [π/2, 3π/2]`. -/
def farHalf (L : ℕ) [NeZero L] : Finset (ZMod L) :=
  Finset.univ.filter fun k => L ≤ 4 * k.val ∧ 4 * k.val ≤ 3 * L

/-- **The crossing packet**: the `16` momenta `m/1000`, `4000 ≤ m < 4016`, of a ring of physical
length `ℓ = 2000π`, with `c = 1`, rest energy `μ = 3` and flat amplitudes: momentum about `p₀ = 4`,
velocity `4/5`. -/
noncomputable def crossPacket (t : ℝ) : ZMod L × Fin 2 → ℂ :=
  ringPacket (L := L) 1 3 (2000 * Real.pi) (Finset.Ico 4000 (4000 + (16 : ℕ)))
    (fun _ => ((1 / Real.sqrt (16 : ℕ) : ℝ) : ℂ)) t

/-- Its hop on `L` sites: `J = c/(2a)`, `a = 2000π/L`. -/
noncomputable def crossHop (L : ℕ) : ℝ := scaledHop 1 (2000 * Real.pi / L)

theorem vRel_cross : vRel 1 3 (1 * 4) = 4 / 5 := by
  rw [vRel, dispE, show (3 : ℝ) ^ 2 + (1 * 4) ^ 2 = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- The packet's predicted angular velocity on the ring: `Ω = (2π/ℓ) v = 1/1250`. -/
theorem omega_cross : 2 * Real.pi / (2000 * Real.pi) * vRel 1 3 (1 * 4) = 1 / 1250 := by
  rw [vRel_cross]
  field_simp
  norm_num

omit [NeZero L] in
theorem cross_spread : ∀ m ∈ Finset.Ico (4000 : ℤ) (4000 + (16 : ℕ)),
    |2 * Real.pi * m / (2000 * Real.pi) - 4| ≤ 16 / 1000 := by
  intro m hm
  rw [Finset.mem_Ico] at hm
  have hm' : (4000 : ℝ) ≤ m ∧ (m : ℝ) ≤ 4015 := by
    constructor <;> exact_mod_cast (by omega)
  rw [show 2 * Real.pi * m / (2000 * Real.pi) = m / 1000 by field_simp; ring, abs_le]
  constructor <;> linarith [hm'.1, hm'.2]

section Cross

variable (hL : 640000 ≤ L)
include hL

omit [NeZero L] in
theorem cross_win : ∀ m ∈ Finset.Ico (4000 : ℤ) (4000 + (16 : ℕ)), 4000 ≤ m ∧ m + 1 < 4000 + L := by
  intro m hm
  rw [Finset.mem_Ico] at hm
  constructor <;> omega

theorem cross_norm : ∑ _m ∈ Finset.Ico (4000 : ℤ) (4000 + (16 : ℕ)),
    ‖((1 / Real.sqrt (16 : ℕ) : ℝ) : ℂ)‖ ^ 2 = 1 :=
  (flat_packet_localised (L := L) (c := 1) (μ := 3) (ℓ := 2000 * Real.pi) (by norm_num)
    (by positivity) 4000
    (by norm_num) (by omega)).1

/-- **The crossing packet's error budget stays below `1/8`** over the crossing:
`1 − Re T(0) + t · limitErr ≤ 1/8` for `0 ≤ t ≤ 4375π/3`. -/
theorem cross_budget {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 4375 * Real.pi / 3) :
    1 - (transPhase (crossPacket (L := L) 0)).re
      + |t| * limitErr 1 3 (2000 * Real.pi) (16 / 1000) 4 (2000 * Real.pi / L) ≤ 1 / 8 := by
  have hπ := Real.pi_pos
  have hπ2 : Real.pi < 63 / 20 := by
    have := Real.pi_lt_d2
    norm_num at this ⊢
    linarith
  have hLr : (640000 : ℝ) ≤ L := by exact_mod_cast hL
  -- the initial localisation
  obtain ⟨hW, -⟩ := noWrap_distinct_of_window (L := L) (cross_win hL)
  have hRe := re_transPhase_ringPacket_ge (L := L) (c := 1) (μ := 3) (ℓ := 2000 * Real.pi)
    (by norm_num) (by positivity) hW (fun _ => 1 / Real.sqrt (16 : ℕ)) (fun _ => by positivity)
  rw [(flat_sums 4000 (N := 16) (by norm_num)).2] at hRe
  have h6 : Real.pi * 1 / (2000 * Real.pi * 3) = 1 / 6000 := by field_simp; ring
  rw [h6] at hRe
  have hRe' : 15 / 16 - 1 / 10 ^ 7 ≤ (transPhase (crossPacket (L := L) 0)).re := by
    refine le_trans ?_ hRe
    norm_num
  -- the error rate
  set a := 2000 * Real.pi / L
  have ha0 : 0 ≤ a := by positivity
  have ha : a ≤ (63 / 20) / 320 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have herr : limitErr 1 3 (2000 * Real.pi) (16 / 1000) 4 a
      = 1 / 1000 * (17 / 3000 + 104 / 9 * a ^ 2) := by
    unfold limitErr
    field_simp
    ring
  have herr0 : 0 ≤ 1 / 1000 * (17 / 3000 + 104 / 9 * a ^ 2) := by positivity
  have hterm : |t| * limitErr 1 3 (2000 * Real.pi) (16 / 1000) 4 a
      ≤ 4375 * (63 / 20) / 3 * (1 / 1000 * (17 / 3000 + 104 / 9 * ((63 / 20) / 320) ^ 2)) := by
    rw [herr, abs_of_nonneg ht0]
    have ht' : t ≤ 4375 * (63 / 20) / 3 := by linarith
    have ha2 : a ^ 2 ≤ ((63 / 20) / 320) ^ 2 := pow_le_pow_left₀ ha0 ha 2
    calc t * (1 / 1000 * (17 / 3000 + 104 / 9 * a ^ 2))
        ≤ 4375 * (63 / 20) / 3 * (1 / 1000 * (17 / 3000 + 104 / 9 * a ^ 2)) :=
          mul_le_mul_of_nonneg_right ht' herr0
      _ ≤ _ := by gcongr
  have hnum : 4375 * (63 / 20) / 3 * (1 / 1000 * (17 / 3000 + 104 / 9 * ((63 / 20) / 320) ^ 2)) ≤ 1 / 32 :=
    by norm_num
  linarith

/-- The far half's angles: `π/2 ≤ 2πk/L ≤ 3π/2` on it, and `[0, π/2) ∪ (3π/2, 2π)` off it. -/
theorem angle_farHalf (k : ZMod L) :
    (k ∈ farHalf L → Real.pi / 2 ≤ 2 * Real.pi * k.val / L ∧ 2 * Real.pi * k.val / L ≤ 3 * Real.pi / 2)
    ∧ (k ∉ farHalf L → (0 ≤ 2 * Real.pi * k.val / L ∧ 2 * Real.pi * k.val / L < Real.pi / 2)
        ∨ (3 * Real.pi / 2 < 2 * Real.pi * k.val / L ∧ 2 * Real.pi * k.val / L < 2 * Real.pi)) := by
  have hπ := Real.pi_pos
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hk : (k.val : ℝ) < L := by exact_mod_cast k.val_lt
  have hk0 : (0 : ℝ) ≤ k.val := by positivity
  have e : 2 * Real.pi * k.val / L = 2 * Real.pi * (k.val / L) := by ring
  rw [e]
  constructor
  · intro hk'
    simp only [farHalf, Finset.mem_filter, Finset.mem_univ, true_and] at hk'
    have h1 : (L : ℝ) ≤ 4 * k.val := by exact_mod_cast hk'.1
    have h2 : 4 * (k.val : ℝ) ≤ 3 * L := by exact_mod_cast hk'.2
    have q1 : 1 / 4 ≤ (k.val : ℝ) / L := by rw [le_div_iff₀ hLpos]; linarith
    have q2 : (k.val : ℝ) / L ≤ 3 / 4 := by rw [div_le_iff₀ hLpos]; linarith
    constructor <;> nlinarith
  · intro hk'
    simp only [farHalf, Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_le] at hk'
    have q0 : 0 ≤ (k.val : ℝ) / L := by positivity
    have q3 : (k.val : ℝ) / L < 1 := by rw [div_lt_iff₀ hLpos]; linarith
    rcases hk' with h | h
    · have h' : 4 * (k.val : ℝ) < L := by exact_mod_cast h
      have q : (k.val : ℝ) / L < 1 / 4 := by rw [div_lt_iff₀ hLpos]; linarith
      exact Or.inl ⟨by positivity, by nlinarith⟩
    · have h' : 3 * (L : ℝ) < 4 * k.val := by exact_mod_cast h
      have q : 3 / 4 < (k.val : ℝ) / L := by rw [lt_div_iff₀ hLpos]; linarith
      exact Or.inr ⟨by nlinarith, by nlinarith⟩

/-- ★★ **Before the packet can be near, the far half holds at most a quarter of its weight**: for
`0 ≤ t ≤ 625π/3`. -/
theorem regionWeight_cross_far {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 625 * Real.pi / 3) :
    regionWeight (crossPacket (L := L) t) (farHalf L) ≤ 1 / 4 := by
  have hπ := Real.pi_pos
  have h := regionWeight_ringPacket_le (L := L) (c := 1) (μ := 3) (ℓ := 2000 * Real.pi) (P := 4)
    (D := 16 / 1000) (p₀ := 4) (by norm_num) (by norm_num) (by positivity) (by norm_num)
    (by norm_num) (cross_win hL) cross_spread _ (cross_norm hL) (B := farHalf L) (γ := 1 / 2) t
    (fun k hk => by
      rw [omega_cross]
      obtain ⟨h1, h2⟩ := (angle_farHalf hL k).1 hk
      apply cos_le_half <;> rw [abs_of_nonneg (by nlinarith)] <;> nlinarith)
  have hb := cross_budget hL ht0 (by linarith)
  unfold crossPacket at hb h ⊢
  linarith

/-- ★★ **Once the packet is predicted inside, the far half holds at least three quarters of its
weight**: for `3125π/3 ≤ t ≤ 4375π/3`. -/
theorem regionWeight_cross_near {t : ℝ} (ht0 : 3125 * Real.pi / 3 ≤ t) (ht : t ≤ 4375 * Real.pi / 3) :
    3 / 4 ≤ regionWeight (crossPacket (L := L) t) (farHalf L) := by
  have hπ := Real.pi_pos
  have h := le_regionWeight_ringPacket (L := L) (c := 1) (μ := 3) (ℓ := 2000 * Real.pi) (P := 4)
    (D := 16 / 1000) (p₀ := 4) (by norm_num) (by norm_num) (by positivity) (by norm_num)
    (by norm_num) (cross_win hL) cross_spread _ (cross_norm hL) (A := farHalf L)
    (γ := 1 / 2) (by norm_num) t
    (fun k hk => by
      rw [omega_cross]
      apply cos_le_half
      · rcases (angle_farHalf hL k).2 hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [abs_of_neg (by nlinarith)]; nlinarith
        · rw [abs_of_pos (by nlinarith)]; nlinarith
      · rcases (angle_farHalf hL k).2 hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [abs_of_neg (by nlinarith)]; nlinarith
        · rw [abs_of_pos (by nlinarith)]; nlinarith)
  have hb := cross_budget hL (by linarith) ht
  unfold crossPacket at hb h ⊢
  have : (1 - (transPhase (ringPacket (L := L) 1 3 (2000 * Real.pi) (Finset.Ico 4000 (4000 + (16 : ℕ)))
      (fun _ => ((1 / Real.sqrt (16 : ℕ) : ℝ) : ℂ)) 0)).re
      + |t| * limitErr 1 3 (2000 * Real.pi) (16 / 1000) 4 (2000 * Real.pi / L)) / (1 - 1 / 2)
      ≤ 1 / 4 := by
    rw [div_le_iff₀ (by norm_num)]
    linarith
  linarith

end Cross

/-- The whole chain carries the crossing packet. -/
theorem chainProp_crossPacket (t : ℝ) :
    chainProp (L := L) (crossHop L) 3 t *ᵥ crossPacket (L := L) 0 = crossPacket t := by
  unfold crossPacket ringPacket crossHop
  exact chainProp_packet _ _ _ _ t

section Detector

variable (hL : 640000 ≤ L)
include hL

theorem cross_before {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 625 * Real.pi / 3) :
    1 * ∫ s in (0 : ℝ)..t,
        regionWeight (chainProp (L := L) (crossHop L) 3 s *ᵥ crossPacket (L := L) 0) (farHalf L)
      < 625 * Real.pi / 12 := by
  have h := intervalIntegral.integral_mono_on ht0
    ((continuous_regionWeight_chainProp (crossHop L) 3 (crossPacket (L := L) 0)
      (farHalf L)).intervalIntegrable 0 t)
    (intervalIntegrable_const (μ := volume) (c := (1 / 4 : ℝ)))
    fun s hs => by
      rw [chainProp_crossPacket]
      exact regionWeight_cross_far hL hs.1 (hs.2.trans ht.le)
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
  linarith

theorem cross_after :
    625 * Real.pi / 12 ≤ 1 * ∫ s in (0 : ℝ)..(4375 * Real.pi / 3),
        regionWeight (chainProp (L := L) (crossHop L) 3 s *ᵥ crossPacket (L := L) 0) (farHalf L) := by
  have hπ := Real.pi_pos
  have hc := continuous_regionWeight_chainProp (crossHop L) 3 (crossPacket (L := L) 0) (farHalf L)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 3125 * Real.pi / 3)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h0 := intervalIntegral.integral_nonneg (μ := volume) (by positivity : (0 : ℝ) ≤ 3125 * Real.pi / 3)
    fun s _ => regionWeight_nonneg (chainProp (L := L) (crossHop L) 3 s *ᵥ crossPacket (L := L) 0)
      (farHalf L)
  have h1 := intervalIntegral.integral_mono_on (by linarith : 3125 * Real.pi / 3 ≤ 4375 * Real.pi / 3)
    (intervalIntegrable_const (μ := volume) (c := (3 / 4 : ℝ))) (hc.intervalIntegrable _ _)
    fun s hs => by
      rw [chainProp_crossPacket]
      exact regionWeight_cross_near hL hs.1 hs.2
  rw [intervalIntegral.integral_const, smul_eq_mul] at h1
  linarith

/-- ★★★ **The far half's detector, written on the packet's arrival**: gain `1`, threshold `625π/12`,
an actual occurrence of the whole chain's evolution, not written before `625π/3` and written by
`4375π/3`, then held for any window. -/
noncomputable def crossDetector {w : ℝ} (hw : 0 ≤ w) : ActualOccurrence (WholeArena L) ℕ L :=
  regionDetector (crossHop L) 3 1 (625 * Real.pi / 12) (farHalf L) (crossPacket (L := L) 0) 0 rfl
    (τ₀ := 625 * Real.pi / 3) (τ₁ := 4375 * Real.pi / 3) (by positivity)
    (by nlinarith [Real.pi_pos]) hw zero_le_one (fun _ ht0 ht => cross_before hL ht0 ht)
    (cross_after hL)

/-- ★★★ **A distant detector written on the packet's arrival** (BACKLOG #265). On a ring of physical
length `ℓ = 2000π` with at least `640000` sites, the packet of `16` momenta about `p₀ = 4`
(`c = 1`, `μ = 3`), carried by the whole chain's evolution `e^{−itH}`:

* the whole chain carries the packet exactly, and it stays normalised;
* it moves at `v = 4/5` (`c = 1`), turning on the ring at `Ω = 1/1250`;
* while it cannot yet be near — `0 ≤ t ≤ 625π/3` — the far half of the ring holds at most a quarter of
  its weight; once it is predicted inside — `3125π/3 ≤ t ≤ 4375π/3` — at least three quarters;
* the far half's detector is an actual occurrence written over `[625π/3, 4375π/3]`.

The far half begins a quarter ring, `d = 500π`, from the packet's start: at `v = 4/5` its predicted
arrival is `d/v = 625π`, inside the interval. The interval opens at `(d − ℓ/6)/v`, `ℓ/6` being the
packet's spread at the concentration `cos ≤ 1/2`. -/
theorem dirac_arrival {w : ℝ} (hw : 0 ≤ w) :
    let o := crossDetector hL hw
    o.writeStart = 625 * Real.pi / 3 ∧ o.writeEnd = 4375 * Real.pi / 3 ∧ o.value = 1
    ∧ o.site = (farHalf L).image siteFin
    ∧ (∀ t, chainProp (L := L) (crossHop L) 3 t *ᵥ crossPacket (L := L) 0 = crossPacket t)
    ∧ (∀ t, chainInner (crossPacket (L := L) t) (crossPacket t) = 1)
    ∧ vRel 1 3 (1 * 4) = 4 / 5
    ∧ 2 * Real.pi / (2000 * Real.pi) * vRel 1 3 (1 * 4) = 1 / 1250
    ∧ (∀ t, 0 ≤ t → t ≤ 625 * Real.pi / 3 → regionWeight (crossPacket (L := L) t) (farHalf L) ≤ 1 / 4)
    ∧ (∀ t, 3125 * Real.pi / 3 ≤ t → t ≤ 4375 * Real.pi / 3 →
        3 / 4 ≤ regionWeight (crossPacket (L := L) t) (farHalf L)) :=
  ⟨rfl, rfl, rfl, rfl, chainProp_crossPacket,
    (dirac_packet_limit (L := L) (c := 1) (μ := 3) (ℓ := 2000 * Real.pi) (P := 4) (D := 16 / 1000)
      (p₀ := 4) (by norm_num) (by norm_num) (by positivity) (by norm_num) (by norm_num)
      (cross_win hL) cross_spread _ (cross_norm hL)).1,
    vRel_cross, omega_cross, fun _ h0 h1 => regionWeight_cross_far hL h0 h1,
    fun _ h0 h1 => regionWeight_cross_near hL h0 h1⟩

end Detector

end CSD.RecordLayer

end
