/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.RecordOccurrence
public import CsdLean4.CV.DiracPacketLimit

/-!
# A Dirac packet writes a site detector

**Category:** 7-SigmaLayer (the record layer). BACKLOG #252, its smallest part: one Dirac packet
writes one local detector record, for the test candidate (B).

~~#250~~ built the packet of the lattice Dirac chain and ~~#261~~ normalised it; ~~#242~~ wrote the
control's passages as record occurrences (#191). Here the candidate's packet and its detectors are
**one measurable two-time evolution of one arena**, and the packet's passage through a site is an
`ActualOccurrence` of it, with a concrete moving instance.

## The arena

* `siteWeight` (the weight `Σ_c ‖ψ(k, c)‖²` of a chain state on a site), `siteWeight_nonneg`,
  `re_chainInner_self`, `siteWeight_le` (a site holds at most the whole norm),
  `continuous_siteWeight`; ★ `siteWeight_packet_le` — a packet's weight on any site is at most its
  norm `Σ_m (‖a_m‖ ‖mode_m‖)²`, at every time;
* `phaseAmp` (the window's amplitudes advanced by their phases), `phaseAmp_zero`, `phaseAmp_add`,
  `packet_phaseAmp` — **the amplitude flow is the chain's Schrödinger evolution on the window**: the
  packet built from the advanced amplitudes is the packet advanced in time; `continuous_packet`,
  `continuous_siteWeight_packet`;
* `DetArena` (amplitudes × a register at every site), `detFlow` (the register at `k` integrates the
  packet's weight on `k` with gain `g`), `amp_detFlow`, `register_detFlow`, `detFlow_zero`,
  `detFlow_add`, `continuous_detFlow`, ★ `measurable_detFlow`, `detEvolve`, `detEvolve_self`,
  `detEvolve_comp`.

## The write

* `integral_siteWeight_mono` (the register is monotone), `integral_siteWeight_le`;
  ★★ `register_lt_of_lt` — **no detector is written before `θ / (g ⟨ψ, ψ⟩)`**;
* `detRead`, `measurable_detRead`, `siteFin`; ★★★ `packetDetector` — **the packet's passage through
  site `k` as an `ActualOccurrence`**: the detector, prepared at zero, is not written while its
  register is below the threshold and is written once it reaches it, then holds for any window.

## A moving instance

* `twoMode` (momenta `0` and `1` on `12` sites, `J = 4`, `μ = 3`, unit amplitudes: band energies `3`
  and `5`, spinors `(6, 0)` and `(8, 4)`), `beat`, `modeS_intCast`, `angleZ_twelve_one`,
  `bandE_twoMode_zero`, `bandE_twoMode_one`, `twoMode_apply`, `norm_beat`;
* ★★ `siteWeight_twoMode` — **the weight on site `k` is `116 + 96 cos(πk/6 − 2t)`**;
  ★★ `siteWeight_twoMode_succ` — **it moves one site every `π/12`**; `chainInner_twoMode` (norm
  `1392`);
* `beat_zero`, `beat_six`, `hasDerivAt_register`, `integral_twoMode`, `register_twoMode_zero`
  (`g (116t + 48 sin 2t)`), `register_twoMode_six` (`g (116t − 48 sin 2t)`); ★★★ `twoModeDetector`
  — the detector at site `0` written at exactly `π/4`;
* ★★★ `dirac_detector` — **the capstone**: the arena carries the packet, which solves the lattice
  Dirac equation; its weight is a travelling wave at `12/π` sites per unit time, below the chain's
  `c = 2J = 8`; the detector at site `0`, threshold `g (29π + 48)`, is an actual occurrence written
  at `π/4`, while the register at the opposite site `6` is then `g (29π − 48)`, below it.

## The findings

1. **The candidate's packet writes records on its own arena.** The amplitudes evolve by the chain's
   Dirac Hamiltonian and the registers integrate the packet's site weight; the write is discharged
   from that evolution, with its interval explicit.
2. **A packet of finite norm writes nothing at once**: no register of gain `g` reaches `θ` before
   `θ / (g ⟨ψ, ψ⟩)`, whatever the site.
3. **Where the record is written depends on where the packet is.** In the instance, the detector
   at the weight's starting peak reaches the threshold at `π/4`; the one opposite has not.

## Honest scope

⚠️ **The arena is the window, not the whole chain.** It carries the amplitudes of the window's
upper-band modes, an invariant subspace of the chain on which `packet_phaseAmp` and
`hasDerivAt_packet` make the flow the Dirac evolution. The whole chain, with `e^{−iHt}` on all of
`ℂ^{2L}`, and a distant detector written on the packet's arrival are
`RecordLayer/DiracArrival.lean` (`chainProp_packet`, `dirac_arrival`, BACKLOG #265).

⚠️ **The detector law is stated, not generated.** The register integrates the site weight `‖ψ_k‖²`
with a gain; there is no coupling Hamiltonian and no back-reaction on the packet (#251). These are
test detectors, as in ~~#242~~.

⚠️ **An intensity, not a click.** Every site's register rises with that site's weight; the
threshold fixes when one is written, not that only one is. A single site selected by the ontic
state, with Born frequencies, is the record layer's selection and is not modelled here.

⚠️ **The instance's motion is a two-mode beat.** It spans the ring, moves at the finite-difference
velocity `ΔE/Δθ = 12/π`, not at the group velocity of a narrow packet (its momentum-`0` mode has
group velocity `0`), and the written detector is where the weight starts, not a distant one written
on arrival. The two-level clock readout of #252 is not treated (#262).

References: `specs/BACKLOG.md` #252, #250, #261, #242, #251, #262, #191, #39;
`CV/DiracPacket.lean` (`packet`, `hasDerivAt_packet`, `noWrap_distinct_of_window`);
`CV/DiracPacketLimit.lean` (`chainInner_packet_self`, `modeNorm`, `sq_spinNorm`);
`CV/DiracClockChain.lean` (`diracHam`, `diracMode`, `planeWave`);
`RecordLayer/RecordOccurrence.lean` (`ActualOccurrence`, `IsRecordWrite`);
`RecordLayer/TransportedClock.lean` (`passageWrite`, the control's passage).
-/

@[expose] public section

open MeasureTheory Set CSD.CV Complex

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {L : ℕ} [NeZero L]

/-! ### The weight on a site -/

/-- **The weight of a chain state on site `k`**: `Σ_c ‖ψ(k, c)‖²`, both components. -/
noncomputable def siteWeight (ψ : ZMod L × Fin 2 → ℂ) (k : ZMod L) : ℝ :=
  ∑ c : Fin 2, ‖ψ (k, c)‖ ^ 2

omit [NeZero L] in
theorem siteWeight_nonneg (ψ : ZMod L × Fin 2 → ℂ) (k : ZMod L) : 0 ≤ siteWeight ψ k :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem re_chainInner_self (ψ : ZMod L × Fin 2 → ℂ) :
    (chainInner ψ ψ).re = ∑ p, ‖ψ p‖ ^ 2 := by
  rw [chainInner, Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

/-- **A site holds at most the whole norm.** -/
theorem siteWeight_le (ψ : ZMod L × Fin 2 → ℂ) (k : ZMod L) :
    siteWeight ψ k ≤ (chainInner ψ ψ).re := by
  rw [re_chainInner_self, Fintype.sum_prod_type]
  exact Finset.single_le_sum (f := fun j => ∑ c : Fin 2, ‖ψ (j, c)‖ ^ 2)
    (fun j _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ k)

omit [NeZero L] in
theorem continuous_siteWeight (k : ZMod L) :
    Continuous fun ψ : ZMod L × Fin 2 → ℂ => siteWeight ψ k := by
  unfold siteWeight
  fun_prop

/-- ★ **A packet's weight on any site is at most its norm** `Σ_m (‖a_m‖ ‖mode_m‖)²`, at every
time. -/
theorem siteWeight_packet_le (J μ : ℝ) {W : Finset ℤ} (hD : Distinct L W) (a : ℤ → ℂ) (t : ℝ)
    (k : ZMod L) :
    siteWeight (packet (L := L) J μ W a t) k ≤ ∑ m ∈ W, (‖a m‖ * modeNorm L J μ m) ^ 2 := by
  have h := siteWeight_le (packet (L := L) J μ W a t) k
  rwa [chainInner_packet_self J μ hD, Complex.ofReal_re] at h

/-! ### The amplitude flow -/

/-- **The window's amplitudes after `t`**: each mode advanced by its phase `e^{−iE_m t}`. -/
noncomputable def phaseAmp (L : ℕ) (J μ t : ℝ) (a : ℤ → ℂ) : ℤ → ℂ := fun m =>
  a m * exp (-(I * bandE J μ (angleZ L m)) * t)

omit [NeZero L] in
theorem phaseAmp_zero (J μ : ℝ) (a : ℤ → ℂ) : phaseAmp L J μ 0 a = a := by
  funext m
  simp [phaseAmp]

omit [NeZero L] in
theorem phaseAmp_add (J μ s t : ℝ) (a : ℤ → ℂ) :
    phaseAmp L J μ (s + t) a = phaseAmp L J μ t (phaseAmp L J μ s a) := by
  funext m
  simp only [phaseAmp]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **The amplitude flow is the chain's Schrödinger evolution on the window**: the packet built from
the advanced amplitudes is the packet advanced in time (`hasDerivAt_packet`). -/
theorem packet_phaseAmp (J μ : ℝ) (W : Finset ℤ) (a : ℤ → ℂ) (s t : ℝ) :
    packet (L := L) J μ W (phaseAmp L J μ s a) t = packet (L := L) J μ W a (s + t) := by
  unfold packet
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  rw [phaseAmp, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem continuous_packet (J μ : ℝ) (W : Finset ℤ) :
    Continuous fun p : (ℤ → ℂ) × ℝ => packet (L := L) J μ W p.1 p.2 := by
  unfold packet
  fun_prop

theorem continuous_siteWeight_packet (J μ : ℝ) (W : Finset ℤ) (a : ℤ → ℂ) (k : ZMod L) :
    Continuous fun s => siteWeight (packet (L := L) J μ W a s) k :=
  (continuous_siteWeight k).comp
    ((continuous_packet J μ W).comp (continuous_const.prodMk continuous_id))

/-! ### The arena -/

/-- **The detector arena**: the window's amplitudes and a register at every site. -/
abbrev DetArena (L : ℕ) : Type := (ℤ → ℂ) × (ZMod L → ℝ)

section Flow

variable (J μ g : ℝ) (W : Finset ℤ)

/-- **The packet with its site detectors**: the amplitudes advance by their phases, and the register
at site `k` integrates the packet's weight on `k` with gain `g`. -/
noncomputable def detFlow (t : ℝ) (x : DetArena L) : DetArena L :=
  (phaseAmp L J μ t x.1,
    fun k => x.2 k + g * ∫ s in (0 : ℝ)..t, siteWeight (packet (L := L) J μ W x.1 s) k)

theorem amp_detFlow (t : ℝ) (x : DetArena L) : (detFlow J μ g W t x).1 = phaseAmp L J μ t x.1 :=
  rfl

theorem register_detFlow (t : ℝ) (x : DetArena L) (k : ZMod L) :
    (detFlow J μ g W t x).2 k
      = x.2 k + g * ∫ s in (0 : ℝ)..t, siteWeight (packet (L := L) J μ W x.1 s) k :=
  rfl

theorem detFlow_zero (x : DetArena L) : detFlow J μ g W 0 x = x := by
  ext
  · simp [detFlow, phaseAmp_zero]
  · simp [detFlow]

theorem detFlow_add (s t : ℝ) (x : DetArena L) :
    detFlow J μ g W (s + t) x = detFlow J μ g W t (detFlow J μ g W s x) := by
  ext k
  · simp only [detFlow, phaseAmp_add]
  · simp only [detFlow, packet_phaseAmp]
    have hi : ∀ a b : ℝ, IntervalIntegrable
        (fun u => siteWeight (packet (L := L) J μ W x.1 u) k) volume a b :=
      fun a b => (continuous_siteWeight_packet J μ W x.1 k).intervalIntegrable a b
    have hs : (∫ u in (0 : ℝ)..t, siteWeight (packet (L := L) J μ W x.1 (s + u)) k)
        = ∫ u in s..s + t, siteWeight (packet (L := L) J μ W x.1 u) k := by
      rw [intervalIntegral.integral_comp_add_left
        (fun u => siteWeight (packet (L := L) J μ W x.1 u) k) s, add_zero]
    rw [hs, ← intervalIntegral.integral_add_adjacent_intervals (hi 0 s) (hi s (s + t))]
    ring

theorem continuous_detFlow (t : ℝ) : Continuous (detFlow (L := L) J μ g W t) := by
  refine Continuous.prodMk ?_ ?_
  · exact continuous_pi fun m =>
      ((continuous_apply m).comp continuous_fst).mul continuous_const
  · refine continuous_pi fun k => ((continuous_apply k).comp continuous_snd).add
      (continuous_const.mul ?_)
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (x : DetArena L) s => siteWeight (packet (L := L) J μ W x.1 s) k) ?_ 0 t
    exact (continuous_siteWeight k).comp
      ((continuous_packet J μ W).comp (continuous_fst.fst.prodMk continuous_snd))

/-- ★ **Each step is measurable.** -/
theorem measurable_detFlow (t : ℝ) : Measurable (detFlow (L := L) J μ g W t) :=
  (continuous_detFlow J μ g W t).measurable

/-- The two-time evolution. -/
noncomputable def detEvolve (s t : OnticTime) : DetArena L → DetArena L :=
  detFlow J μ g W (t - s)

theorem detEvolve_self (t : OnticTime) :
    detEvolve J μ g W t t = (id : DetArena L → DetArena L) := by
  funext x
  simp only [detEvolve, sub_self, detFlow_zero, id]

theorem detEvolve_comp (s t u : OnticTime) :
    detEvolve J μ g W t u ∘ detEvolve J μ g W s t
      = (detEvolve J μ g W s u : DetArena L → DetArena L) := by
  funext x
  simp only [detEvolve, Function.comp]
  rw [show u - s = (t - s) + (u - t) by ring, detFlow_add]

/-! ### The registers -/

theorem integral_siteWeight_mono (a : ℤ → ℂ) (k : ZMod L) {t₁ t : ℝ} (h : t₁ ≤ t) :
    (∫ s in (0 : ℝ)..t₁, siteWeight (packet (L := L) J μ W a s) k)
      ≤ ∫ s in (0 : ℝ)..t, siteWeight (packet (L := L) J μ W a s) k := by
  have hi : ∀ u v : ℝ, IntervalIntegrable
      (fun s => siteWeight (packet (L := L) J μ W a s) k) volume u v :=
    fun u v => (continuous_siteWeight_packet J μ W a k).intervalIntegrable u v
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 t₁) (hi t₁ t)]
  have := intervalIntegral.integral_nonneg (μ := volume) h fun u _ =>
    siteWeight_nonneg (packet (L := L) J μ W a u) k
  linarith

theorem integral_siteWeight_le {W : Finset ℤ} (hD : Distinct L W) (a : ℤ → ℂ) (k : ZMod L)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, siteWeight (packet (L := L) J μ W a s) k)
      ≤ t * ∑ m ∈ W, (‖a m‖ * modeNorm L J μ m) ^ 2 := by
  have h := intervalIntegral.integral_mono_on ht
    ((continuous_siteWeight_packet J μ W a k).intervalIntegrable 0 t)
    (intervalIntegrable_const (μ := volume) (c := ∑ m ∈ W, (‖a m‖ * modeNorm L J μ m) ^ 2))
    fun s _ => siteWeight_packet_le J μ hD a s k
  simpa using h

/-- ★★ **No detector is written before `θ / (g ⟨ψ, ψ⟩)`**: a register of gain `g` reaches the
threshold `θ` no sooner than the whole norm, delivered at full rate, would take it there. -/
theorem register_lt_of_lt {W : Finset ℤ} (hD : Distinct L W) (a : ℤ → ℂ) (k : ZMod L) {θ : ℝ}
    (hg : 0 < g) (hN : 0 < ∑ m ∈ W, (‖a m‖ * modeNorm L J μ m) ^ 2) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < θ / (g * ∑ m ∈ W, (‖a m‖ * modeNorm L J μ m) ^ 2)) :
    g * ∫ s in (0 : ℝ)..t, siteWeight (packet (L := L) J μ W a s) k < θ := by
  rw [lt_div_iff₀ (mul_pos hg hN)] at ht
  calc g * ∫ s in (0 : ℝ)..t, siteWeight (packet (L := L) J μ W a s) k
      ≤ g * (t * ∑ m ∈ W, (‖a m‖ * modeNorm L J μ m) ^ 2) :=
        mul_le_mul_of_nonneg_left (integral_siteWeight_le J μ hD a k ht0) hg.le
    _ < θ := by linarith

/-! ### The write -/

/-- **The detector's readout**: `1` once the register at `k` has reached the threshold `θ`. -/
noncomputable def detRead (θ : ℝ) (k : ZMod L) (x : DetArena L) : ℕ :=
  if θ ≤ x.2 k then 1 else 0

omit [NeZero L] in
theorem measurable_detRead (θ : ℝ) (k : ZMod L) : Measurable (detRead (L := L) θ k) := by
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le measurable_const ((measurable_pi_apply k).comp measurable_snd)

/-- The site `k` as an element of `Fin L`. -/
def siteFin (k : ZMod L) : Fin L := ⟨k.val, k.val_lt⟩

/-- ★★★ **The packet's passage through site `k` as an actual occurrence**: the detector at `k`,
prepared at zero, is not written while its register is below the threshold (`hbefore`) and is
written once it has reached it (`hafter`); it then holds the record for any window, its register
being monotone. -/
noncomputable def packetDetector (θ : ℝ) (k : ZMod L) (a : ℤ → ℂ) (det₀ : ZMod L → ℝ)
    (hdet : det₀ k = 0) {τ₀ τ₁ w : ℝ} (hτ₀ : 0 ≤ τ₀) (hτ : τ₀ ≤ τ₁) (hw : 0 ≤ w) (hg : 0 ≤ g)
    (hbefore : ∀ t, 0 ≤ t → t < τ₀ →
      g * ∫ s in (0 : ℝ)..t, siteWeight (packet (L := L) J μ W a s) k < θ)
    (hafter : θ ≤ g * ∫ s in (0 : ℝ)..τ₁, siteWeight (packet (L := L) J μ W a s) k) :
    ActualOccurrence (DetArena L) ℕ L where
  evolve := detEvolve J μ g W
  evolve_self := detEvolve_self J μ g W
  evolve_comp := detEvolve_comp J μ g W
  measurable_evolve := fun s t => measurable_detFlow J μ g W (t - s)
  readout := detRead θ k
  measurable_readout := measurable_detRead θ k
  ready := {x | x.2 k = 0}
  measurableSet_ready := measurableSet_eq_fun ((measurable_pi_apply k).comp measurable_snd)
    measurable_const
  prep := (a, det₀)
  prep_mem := hdet
  site := {siteFin k}
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
        show detRead θ k (detFlow J μ g W (t - 0) (a, det₀)) ≠ 1
        rw [sub_zero, detRead, register_detFlow]
        show (if θ ≤ det₀ k + _ then 1 else 0) ≠ 1
        rw [hdet, zero_add]
        split_ifs with h
        · exact absurd h (not_le.2 (hbefore t ht0 ht))
        · decide
      holds := fun t ht₁ _ => by
        show detRead θ k (detFlow J μ g W (t - 0) (a, det₀)) = 1
        rw [sub_zero, detRead, register_detFlow]
        show (if θ ≤ det₀ k + _ then 1 else 0) = 1
        rw [hdet, zero_add]
        split_ifs with h
        · rfl
        refine absurd (hafter.trans ?_) h
        exact (mul_le_mul_of_nonneg_left
          (integral_siteWeight_mono J μ W a k ht₁) hg) }

end Flow

/-! ### A moving two-mode packet -/

section TwoMode

/-- **The two-mode packet**: momenta `0` and `1` on a ring of `12` sites, hop `J = 4`, rest energy
`μ = 3`, unit amplitudes. Its band energies are `3` and `5`, its spinors `(6, 0)` and `(8, 4)`. -/
noncomputable def twoMode (t : ℝ) : ZMod 12 × Fin 2 → ℂ := packet (L := 12) 4 3 {0, 1} 1 t

/-- The beat of the two modes at site `k`: `e^{2πik/12} e^{−2it}`. -/
noncomputable def beat (k : ZMod 12) (t : ℝ) : ℂ :=
  (ZMod.toCircle k : ℂ) * exp ((-(2 * t) : ℝ) * I)

theorem modeS_intCast (J : ℝ) (m : ℤ) :
    modeS J (m : ZMod L) = 2 * J * Real.sin (angleZ L m) := by
  rw [modeS, latticeAngle_intCast_sin]

theorem angleZ_twelve_one : angleZ 12 1 = Real.pi / 6 := by
  rw [angleZ]
  push_cast
  ring

theorem bandE_twoMode_zero : bandE 4 3 (angleZ 12 0) = 3 := by
  rw [bandE, angleZ, dispE]
  simp only [Int.cast_zero, mul_zero, zero_div, Real.sin_zero]
  rw [show (3 : ℝ) ^ 2 + 0 ^ 2 = 3 ^ 2 by ring, Real.sqrt_sq (by norm_num)]

theorem bandE_twoMode_one : bandE 4 3 (angleZ 12 1) = 5 := by
  rw [bandE, angleZ_twelve_one, Real.sin_pi_div_six, dispE]
  rw [show (3 : ℝ) ^ 2 + (2 * 4 * (1 / 2)) ^ 2 = 5 ^ 2 by ring, Real.sqrt_sq (by norm_num)]

theorem twoMode_apply (t : ℝ) (k : ZMod 12) :
    twoMode t (k, 0) = exp (-(I * 3) * t) * (6 + 8 * beat k t)
      ∧ twoMode t (k, 1) = exp (-(I * 3) * t) * (4 * beat k t) := by
  have hm0 : modeS 4 ((0 : ℤ) : ZMod 12) = 0 := by
    rw [modeS_intCast]
    simp [angleZ]
  have hm1 : modeS 4 ((1 : ℤ) : ZMod 12) = 4 := by
    rw [modeS_intCast, angleZ_twelve_one, Real.sin_pi_div_six]
    norm_num
  have hd0 : dispE 3 0 = 3 := by
    rw [← hm0, dispE_modeS_intCast, bandE_twoMode_zero]
  have hd1 : dispE 3 4 = 5 := by
    rw [← hm1, dispE_modeS_intCast, bandE_twoMode_one]
  have he : exp (-(I * (5 : ℝ)) * t) = exp (-(I * 3) * t) * exp ((-(2 * t) : ℝ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hp0 : planeWave ((0 : ℤ) : ZMod 12) k = 1 := by
    simp [planeWave]
  have hp1 : planeWave ((1 : ℤ) : ZMod 12) k = (ZMod.toCircle k : ℂ) := by
    simp [planeWave]
  unfold twoMode packet
  rw [Finset.sum_pair (by norm_num : (0 : ℤ) ≠ 1)]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, one_mul,
    diracMode, hp0, hp1, hm0, hm1, hd0, hd1, bandE_twoMode_zero, bandE_twoMode_one]
  refine ⟨?_, ?_⟩ <;> simp only [Fin.isValue, ite_true, show (1 : Fin 2) ≠ 0 by decide,
    ite_false] <;> rw [he, beat] <;> push_cast <;> ring

theorem norm_beat (k : ZMod 12) (t : ℝ) : ‖beat k t‖ = 1 := by
  rw [beat, norm_mul, Circle.norm_coe, norm_exp_ofReal_mul_I, one_mul]

/-- ★★ **The packet's weight on site `k` is a travelling wave**: `116 + 96 cos(πk/6 − 2t)`, written
as `116 + 96 Re(e^{2πik/12} e^{−2it})`. -/
theorem siteWeight_twoMode (t : ℝ) (k : ZMod 12) :
    siteWeight (twoMode t) k = 116 + 96 * (beat k t).re := by
  obtain ⟨h0, h1⟩ := twoMode_apply t k
  have he : ‖exp (-(I * 3) * (t : ℂ))‖ = 1 := by
    rw [show -(I * 3) * (t : ℂ) = ((-(3 * t) : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I]
  have hn : (beat k t).re * (beat k t).re + (beat k t).im * (beat k t).im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, norm_beat]
    norm_num
  simp only [siteWeight, Fin.sum_univ_two]
  rw [h0, h1, norm_mul, norm_mul, he, one_mul, one_mul, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp
  linear_combination 80 * hn

/-- ★★ **The weight moves one site every `π/12`**: velocity `12/π` sites per unit time. -/
theorem siteWeight_twoMode_succ (t : ℝ) (k : ZMod 12) :
    siteWeight (twoMode (t + Real.pi / 12)) (k + 1) = siteWeight (twoMode t) k := by
  have h1 : (ZMod.toCircle (1 : ZMod 12) : ℂ) = exp ((Real.pi / 6 : ℝ) * I) := by
    have := ZMod.toCircle_intCast (N := 12) 1
    simp only [Int.cast_one] at this
    rw [this]
    congr 1
    push_cast
    ring
  rw [siteWeight_twoMode, siteWeight_twoMode, beat, beat, AddChar.map_add_eq_mul, Circle.coe_mul,
    h1, mul_assoc, ← Complex.exp_add]
  congr 4
  push_cast
  ring_nf

theorem beat_zero (t : ℝ) : (beat 0 t).re = Real.cos (2 * t) := by
  rw [beat, AddChar.map_zero_eq_one, Circle.coe_one, one_mul, exp_ofReal_mul_I_re, Real.cos_neg]

theorem beat_six (t : ℝ) : (beat 6 t).re = -Real.cos (2 * t) := by
  have h6 : (ZMod.toCircle (6 : ZMod 12) : ℂ) = -1 := by
    have := ZMod.toCircle_natCast (N := 12) 6
    simp only [Nat.cast_ofNat] at this
    rw [this, show 2 * (Real.pi : ℂ) * I * 6 / 12 = Real.pi * I by ring, Complex.exp_pi_mul_I]
  rw [beat, h6, neg_one_mul, Complex.neg_re, exp_ofReal_mul_I_re, Real.cos_neg]

theorem hasDerivAt_register (c s : ℝ) :
    HasDerivAt (fun s => 116 * s + c * 48 * Real.sin (2 * s)) (116 + c * 96 * Real.cos (2 * s))
      s := by
  have h := ((hasDerivAt_id' s).const_mul 116).add
    ((((hasDerivAt_id' s).const_mul 2).sin).const_mul (c * 48))
  convert h using 1
  ring

theorem integral_twoMode (c : ℝ) (k : ZMod 12) (hk : ∀ s, (beat k s).re = c * Real.cos (2 * s))
    (t : ℝ) :
    ∫ s in (0 : ℝ)..t, siteWeight (twoMode s) k = 116 * t + c * 48 * Real.sin (2 * t) := by
  have hw : ∀ s, siteWeight (twoMode s) k = 116 + c * 96 * Real.cos (2 * s) := fun s => by
    rw [siteWeight_twoMode, hk]
    ring
  simp_rw [hw]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_register c s)
    ((by fun_prop : Continuous fun s => 116 + c * 96 * Real.cos (2 * s)).intervalIntegrable _ _)]
  simp

/-- **The register at site `0`** (where the packet is concentrated at `t = 0`):
`g (116 t + 48 sin 2t)`. -/
theorem register_twoMode_zero (g t : ℝ) :
    (detFlow (L := 12) 4 3 g {0, 1} t (1, 0)).2 0 = g * (116 * t + 48 * Real.sin (2 * t)) := by
  rw [register_detFlow]
  show 0 + g * ∫ s in (0 : ℝ)..t, siteWeight (twoMode s) 0 = _
  rw [integral_twoMode 1 0 (fun s => by rw [beat_zero, one_mul])]
  ring

/-- **The register at site `6`**, the opposite side of the ring: `g (116 t − 48 sin 2t)`. -/
theorem register_twoMode_six (g t : ℝ) :
    (detFlow (L := 12) 4 3 g {0, 1} t (1, 0)).2 6 = g * (116 * t - 48 * Real.sin (2 * t)) := by
  rw [register_detFlow]
  show 0 + g * ∫ s in (0 : ℝ)..t, siteWeight (twoMode s) 6 = _
  rw [integral_twoMode (-1) 6 (fun s => by rw [beat_six]; ring)]
  ring

/-- ★★★ **The two-mode packet writes the detector at site `0` at exactly `π/4`**: gain `g > 0`,
threshold `g (29π + 48)`, any window. -/
noncomputable def twoModeDetector {g : ℝ} (hg : 0 < g) {w : ℝ} (hw : 0 ≤ w) :
    ActualOccurrence (DetArena 12) ℕ 12 :=
  packetDetector 4 3 g {0, 1} (g * (29 * Real.pi + 48)) 0 1 0 rfl
    (by positivity : (0 : ℝ) ≤ Real.pi / 4) le_rfl hw hg.le
    (fun t _ ht => by
      have h := register_twoMode_zero g t
      rw [register_detFlow] at h
      have h' : g * ∫ s in (0 : ℝ)..t, siteWeight (packet (L := 12) 4 3 {0, 1} 1 s) 0
          = g * (116 * t + 48 * Real.sin (2 * t)) := by simpa using h
      rw [h']
      refine mul_lt_mul_of_pos_left ?_ hg
      nlinarith [Real.sin_le_one (2 * t)])
    (by
      have h := register_twoMode_zero g (Real.pi / 4)
      rw [register_detFlow] at h
      have h' : g * ∫ s in (0 : ℝ)..Real.pi / 4, siteWeight (packet (L := 12) 4 3 {0, 1} 1 s) 0
          = g * (116 * (Real.pi / 4) + 48 * Real.sin (2 * (Real.pi / 4))) := by simpa using h
      rw [h', show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two]
      ring_nf
      exact le_rfl)

/-- **The two-mode packet's norm** is `12 (36 + 80) = 1392` at every time. -/
theorem chainInner_twoMode (t : ℝ) : chainInner (twoMode t) (twoMode t) = 1392 := by
  have hD := (noWrap_distinct_of_window (L := 12) (W := {0, 1}) (lo := 0) (by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl <;> norm_num)).2
  have h0 : angleZ 12 0 = 0 := by simp [angleZ]
  rw [twoMode, chainInner_packet_self 4 3 hD, Finset.sum_pair (by norm_num : (0 : ℤ) ≠ 1)]
  simp only [Pi.one_apply, norm_one, one_mul, modeNorm, mul_pow, sq_spinNorm, bandE_twoMode_zero,
    bandE_twoMode_one]
  simp only [h0, angleZ_twelve_one, Real.sin_zero, Real.sin_pi_div_six]
  rw [Real.sq_sqrt (by positivity)]
  push_cast
  norm_num

/-- ★★★ **One Dirac packet writes one site detector** (BACKLOG #252, its smallest part). On a ring
of `12` sites with hop `J = 4` and rest energy `μ = 3`, the packet of momenta `0` and `1` with unit
amplitudes, carried by the arena with a detector of gain `g > 0` on every site:

* the arena carries the packet: its amplitudes at `t` build the packet at `t`, which solves the
  lattice Dirac equation `i ψ' = H ψ`;
* the packet's norm is `1392`, and its weight on site `k` is `116 + 96 cos(πk/6 − 2t)`, a travelling
  wave moving one site every `π/12` — a velocity `12/π`, below the chain's `c = 2J = 8`;
* the detector at site `0`, where the weight starts at its peak, with threshold `g (29π + 48)`, is
  an actual occurrence written at exactly `π/4` and held for any window; its register then equals
  the threshold, while the register at the opposite site `6` is `g (29π − 48)`, below it. -/
theorem dirac_detector {g : ℝ} (hg : 0 < g) {w : ℝ} (hw : 0 ≤ w) :
    let o := twoModeDetector hg hw
    o.writeStart = Real.pi / 4 ∧ o.writeEnd = Real.pi / 4 ∧ o.value = 1 ∧ o.site = {siteFin 0}
    ∧ (∀ t, packet (L := 12) 4 3 {0, 1} (detFlow (L := 12) 4 3 g {0, 1} t (1, 0)).1 0 = twoMode t)
    ∧ (∀ t, HasDerivAt twoMode ((-I) • (diracHam 4 3).mulVec (twoMode t)) t)
    ∧ (∀ t, chainInner (twoMode t) (twoMode t) = 1392)
    ∧ (∀ t k, siteWeight (twoMode t) k = 116 + 96 * (beat k t).re)
    ∧ (∀ t k, siteWeight (twoMode (t + Real.pi / 12)) (k + 1) = siteWeight (twoMode t) k)
    ∧ 12 / Real.pi < 2 * 4
    ∧ (detFlow (L := 12) 4 3 g {0, 1} (Real.pi / 4) (1, 0)).2 0 = g * (29 * Real.pi + 48)
    ∧ (detFlow (L := 12) 4 3 g {0, 1} (Real.pi / 4) (1, 0)).2 6 < g * (29 * Real.pi + 48) := by
  refine ⟨rfl, rfl, rfl, rfl, fun t => ?_, fun t => hasDerivAt_packet 4 3 {0, 1} 1 t,
    chainInner_twoMode, siteWeight_twoMode, siteWeight_twoMode_succ, ?_, ?_, ?_⟩
  · rw [amp_detFlow, packet_phaseAmp, add_zero]
    rfl
  · rw [div_lt_iff₀ Real.pi_pos]
    nlinarith [Real.two_le_pi]
  · rw [register_twoMode_zero, show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two]
    ring
  · rw [register_twoMode_six, show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two]
    nlinarith

end TwoMode

end CSD.RecordLayer

end
