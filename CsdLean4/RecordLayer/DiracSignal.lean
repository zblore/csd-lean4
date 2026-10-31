/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracTiming

/-!
# A one-way signal on the Dirac chain, read from its records

**Category:** 7-SigmaLayer (the record layer). BACKLOG #269 (split from #256).

One messenger, two detectors at rest, one evolution. ~~#268~~'s `sharpDetector` records the
packet's arrival on the arc half a ring away; here a second detector of the same law, on the arc
where the packet starts, records its departure. The two records are **matched** — the same
evolution from the same preparation — and **ordered**, and the speed read off them, the arcs'
separation over the interval between the writes, lies in `[144/201, 72/79]`: it contains the
packet's velocity `4/5` and stays **below `c = 1`**.

## The start arc

* `nearArc` (the sites within angle `π/20` of the start, width `ℓ/20`), `angle_nearArc`;
  ★ `separation_arcs` — **every site of the start arc is between `9π/10` and `11π/10` in angle from
  every site of the far arc**: at least `0.45 ℓ` apart along the ring either way;
* `regionWeight_sharp_le_one`; ★★ `regionWeight_sharp_start` — **the start arc holds at least
  `9/10` of the weight for `0 ≤ t ≤ π·10⁹/32`**; `start_before`, `start_after`;
  ★★★ `startDetector` — the start arc's detector, an actual occurrence written over
  `[π·10⁹/40, π·10⁹/36]`.

## The signal

* ★★★ `dirac_signal` — **the departure and arrival records are matched** (same evolution, same
  preparation), **ordered** (the departure's write ends before the arrival's begins), and the speed
  bracket read off them — at least `0.45 ℓ` over the longest interval between the writes, at most
  `ℓ/2` over the shortest — is `[144/201, 72/79] ∋ 4/5`, inside `(0, 1)`.

## Honest scope

⚠️ **The speed is read off the records' timing, not measured by a clock.** The write intervals are
in the chain's time; a clock carried by an observer (#262, #253) is not involved, and both detectors
are at rest in the chain's frame.

⚠️ **One way, no return.** The exchange of #256 needs the messenger back (#270), and its Doppler
factor needs moving observers (#253).

⚠️ **The bracket is wide** (`0.72` to `0.91`): the arcs are `ℓ/20` wide and the arrival is timed to
`1/8` (~~#268~~). Its upper end below `1` is what the records show: this messenger is slower than
`c`.

⚠️ **The detector law is stated** (test detectors, an intensity — #251, #266).

References: `specs/BACKLOG.md` #269, #256, #268, #265, #270, #253, #39;
`RecordLayer/DiracTiming.lean` (`sharpDetector`, `sharpPacket`, `farArc`, `sharp_budget`,
`cos_pi_div_forty_le`, `cos_le_cos_of_abs`); `RecordLayer/DiracArrival.lean` (`regionDetector`,
`le_regionWeight_ringPacket`, `regionWeight_add_compl`).
-/

@[expose] public section

open MeasureTheory Set CSD.CV Complex
open scoped Matrix

namespace CSD.RecordLayer

open CSD.SigmaLayer

variable {L : ℕ} [NeZero L]

/-- **The start arc**, of width `ℓ/20`: the sites within angle `π/20` of the packet's start. -/
def nearArc (L : ℕ) [NeZero L] : Finset (ZMod L) :=
  Finset.univ.filter fun k => 40 * k.val ≤ L ∨ 39 * L ≤ 40 * k.val

section Signal

variable (hL : 10 ^ 13 ≤ L)
include hL

/-- The start arc's angles: within `π/20` of `0` on it, in `(π/20, 39π/20)` off it. -/
theorem angle_nearArc (k : ZMod L) :
    (k ∈ nearArc L → (0 ≤ 2 * Real.pi * k.val / L ∧ 2 * Real.pi * k.val / L ≤ Real.pi / 20)
        ∨ (39 * Real.pi / 20 ≤ 2 * Real.pi * k.val / L ∧ 2 * Real.pi * k.val / L < 2 * Real.pi))
    ∧ (k ∉ nearArc L → Real.pi / 20 < 2 * Real.pi * k.val / L
        ∧ 2 * Real.pi * k.val / L < 39 * Real.pi / 20) := by
  have hπ := Real.pi_pos
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hk : (k.val : ℝ) < L := by exact_mod_cast k.val_lt
  have e : 2 * Real.pi * k.val / L = 2 * Real.pi * (k.val / L) := by ring
  have q0 : 0 ≤ (k.val : ℝ) / L := by positivity
  have q3 : (k.val : ℝ) / L < 1 := by rw [div_lt_iff₀ hLpos]; linarith
  rw [e]
  constructor
  · intro hk'
    simp only [nearArc, Finset.mem_filter, Finset.mem_univ, true_and] at hk'
    rcases hk' with h | h
    · have h' : 40 * (k.val : ℝ) ≤ L := by exact_mod_cast h
      have q : (k.val : ℝ) / L ≤ 1 / 40 := by rw [div_le_iff₀ hLpos]; linarith
      exact Or.inl ⟨by positivity, by nlinarith⟩
    · have h' : 39 * (L : ℝ) ≤ 40 * k.val := by exact_mod_cast h
      have q : 39 / 40 ≤ (k.val : ℝ) / L := by rw [le_div_iff₀ hLpos]; linarith
      exact Or.inr ⟨by nlinarith, by nlinarith⟩
  · intro hk'
    simp only [nearArc, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_le] at hk'
    have h1 : (L : ℝ) < 40 * k.val := by exact_mod_cast hk'.1
    have h2 : 40 * (k.val : ℝ) < 39 * L := by exact_mod_cast hk'.2
    have q1 : 1 / 40 < (k.val : ℝ) / L := by rw [lt_div_iff₀ hLpos]; linarith
    have q2 : (k.val : ℝ) / L < 39 / 40 := by rw [div_lt_iff₀ hLpos]; linarith
    constructor <;> nlinarith

/-- ★ **The two arcs are far apart**: every site of the start arc is between `9π/10` and `11π/10` in
angle from every site of the far arc — at least `9π/10` around the ring either way. -/
theorem separation_arcs {k j : ZMod L} (hk : k ∈ nearArc L) (hj : j ∈ farArc L) :
    9 * Real.pi / 10 ≤ |2 * Real.pi * j.val / L - 2 * Real.pi * k.val / L|
      ∧ |2 * Real.pi * j.val / L - 2 * Real.pi * k.val / L| ≤ 11 * Real.pi / 10 := by
  have hπ := Real.pi_pos
  obtain ⟨hj1, hj2⟩ := (angle_farArc hL j).1 hj
  rcases (angle_nearArc hL k).1 hk with ⟨hk1, hk2⟩ | ⟨hk1, hk2⟩
  · rw [abs_of_nonneg (by linarith)]
    constructor <;> linarith
  · rw [abs_of_nonpos (by linarith)]
    constructor <;> linarith

/-- The packet is normalised, so no region holds more than its whole weight. -/
theorem regionWeight_sharp_le_one (t : ℝ) (A : Finset (ZMod L)) :
    regionWeight (sharpPacket (L := L) t) A ≤ 1 := by
  have hn := (dirac_packet_limit (L := L) (c := 1) (μ := 3) (ℓ := 2 * Real.pi * 10 ^ 9) (P := 4)
    (D := 10000 / 10 ^ 9) (p₀ := 4) (by norm_num) (by norm_num) (by positivity) (by norm_num)
    (by norm_num) (sharp_win hL) sharp_spread _ (sharp_norm hL)).1 t
  have hs := regionWeight_add_compl (sharpPacket (L := L) t) A
  have hc := regionWeight_nonneg (sharpPacket (L := L) t) Aᶜ
  unfold sharpPacket at hs hc ⊢
  rw [hn, Complex.one_re] at hs
  linarith

/-- ★★ **At the start the start arc holds at least `9/10` of the weight**: for
`0 ≤ t ≤ π·10⁹/32`. -/
theorem regionWeight_sharp_start {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ Real.pi * 10 ^ 9 / 32) :
    9 / 10 ≤ regionWeight (sharpPacket (L := L) t) (nearArc L) := by
  have hπ := Real.pi_pos
  have hc := cos_pi_div_forty_le
  have h := le_regionWeight_ringPacket (L := L) (c := 1) (μ := 3) (ℓ := 2 * Real.pi * 10 ^ 9)
    (P := 4) (D := 10000 / 10 ^ 9) (p₀ := 4) (by norm_num) (by norm_num) (by positivity)
    (by norm_num) (by norm_num) (sharp_win hL) sharp_spread _ (sharp_norm hL) (A := nearArc L)
    (γ := Real.cos (Real.pi / 40)) (by linarith) t
    (fun k hk => by
      rw [omega_sharp]
      obtain ⟨h1, h2⟩ := (angle_nearArc hL k).2 hk
      apply cos_le_cos_of_abs (by positivity) <;> rw [abs_of_pos (by nlinarith)] <;> nlinarith)
  have hb := sharp_budget hL ht0 (by nlinarith)
  unfold sharpPacket at hb h ⊢
  set E := 1 - (transPhase (ringPacket (L := L) 1 3 (2 * Real.pi * 10 ^ 9)
      (Finset.Ico (4 * 10 ^ 9) (4 * 10 ^ 9 + (10000 : ℕ)))
      (fun _ => ((1 / Real.sqrt (10000 : ℕ) : ℝ) : ℂ)) 0)).re
    + |t| * limitErr 1 3 (2 * Real.pi * 10 ^ 9) (10000 / 10 ^ 9) 4 (2 * Real.pi * 10 ^ 9 / L)
  have hE : E / (1 - Real.cos (Real.pi / 40)) ≤ 1 / 10 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

theorem start_before {t : ℝ} (ht0 : 0 ≤ t) (ht : t < Real.pi * 10 ^ 9 / 40) :
    1 * ∫ s in (0 : ℝ)..t,
        regionWeight (chainProp (L := L) (sharpHop L) 3 s *ᵥ sharpPacket (L := L) 0) (nearArc L)
      < Real.pi * 10 ^ 9 / 40 := by
  have h := intervalIntegral.integral_mono_on ht0
    ((continuous_regionWeight_chainProp (sharpHop L) 3 (sharpPacket (L := L) 0)
      (nearArc L)).intervalIntegrable 0 t)
    (intervalIntegrable_const (μ := volume) (c := (1 : ℝ)))
    fun s _ => by
      rw [chainProp_sharpPacket]
      exact regionWeight_sharp_le_one hL s _
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one] at h
  linarith

theorem start_after :
    Real.pi * 10 ^ 9 / 40 ≤ 1 * ∫ s in (0 : ℝ)..(Real.pi * 10 ^ 9 / 36),
        regionWeight (chainProp (L := L) (sharpHop L) 3 s *ᵥ sharpPacket (L := L) 0) (nearArc L) := by
  have hπ := Real.pi_pos
  have h := intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ Real.pi * 10 ^ 9 / 36)
    (intervalIntegrable_const (μ := volume) (c := (9 / 10 : ℝ)))
    ((continuous_regionWeight_chainProp (sharpHop L) 3 (sharpPacket (L := L) 0)
      (nearArc L)).intervalIntegrable _ _)
    fun s hs => by
      rw [chainProp_sharpPacket]
      exact regionWeight_sharp_start hL hs.1 (by nlinarith [hs.2])
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
  nlinarith

/-- ★★★ **The start arc's detector, written on the packet's departure**: the same law as the far
arc's (gain `1`), threshold `π·10⁹/40`, an actual occurrence of the same evolution written over
`[π·10⁹/40, π·10⁹/36]`. -/
noncomputable def startDetector {w : ℝ} (hw : 0 ≤ w) : ActualOccurrence (WholeArena L) ℕ L :=
  regionDetector (sharpHop L) 3 1 (Real.pi * 10 ^ 9 / 40) (nearArc L) (sharpPacket (L := L) 0) 0
    rfl (τ₀ := Real.pi * 10 ^ 9 / 40) (τ₁ := Real.pi * 10 ^ 9 / 36) (by positivity)
    (by nlinarith [Real.pi_pos]) hw zero_le_one (fun _ ht0 ht => start_before hL ht0 ht)
    (start_after hL)

/-- ★★★ **A one-way signal on the Dirac chain, read from its records** (BACKLOG #269). The start
arc's and the far arc's detectors, half a ring apart:

* **matched**: the same evolution of the whole chain from the same preparation — one messenger;
* **ordered**: the departure's write `[π·10⁹/40, π·10⁹/36]` ends before the arrival's
  `[9π·10⁹/8, 41π·10⁹/32]` begins;
* **separated**: every site of one arc is at least `9π/10` in angle (`0.45 ℓ`) from every site of
  the other, either way around the ring, and at most `ℓ/2`;
* **the speed read off the records** — at least `0.45 ℓ = 0.9π·10⁹` over the longest interval
  between the writes, at most `ℓ/2 = π·10⁹` over the shortest — lies in `[144/201, 72/79]`, which
  contains the packet's velocity `4/5` and lies inside `(0, 1)`: **below `c`**. -/
theorem dirac_signal {w : ℝ} (hw : 0 ≤ w) :
    let oA := startDetector hL hw
    let oB := sharpDetector hL hw
    oA.evolve = oB.evolve ∧ oA.prep = oB.prep
    ∧ oA.writeEnd < oB.writeStart
    ∧ (∀ k ∈ nearArc L, ∀ j ∈ farArc L,
        9 * Real.pi / 10 ≤ |2 * Real.pi * j.val / L - 2 * Real.pi * k.val / L|
          ∧ |2 * Real.pi * j.val / L - 2 * Real.pi * k.val / L| ≤ 2 * Real.pi - 9 * Real.pi / 10)
    ∧ 9 * Real.pi * 10 ^ 9 / 10 / (oB.writeEnd - oA.writeStart) = 144 / 201
    ∧ Real.pi * 10 ^ 9 / (oB.writeStart - oA.writeEnd) = 72 / 79
    ∧ (0 : ℝ) < 144 / 201 ∧ (144 / 201 : ℝ) ≤ 4 / 5 ∧ (4 / 5 : ℝ) ≤ 72 / 79 ∧ (72 / 79 : ℝ) < 1 := by
  have hπ := Real.pi_pos
  refine ⟨rfl, rfl, ?_, fun k hk j hj => ?_, ?_, ?_, by norm_num, by norm_num, by norm_num,
    by norm_num⟩
  · show Real.pi * 10 ^ 9 / 36 < 9 * Real.pi * 10 ^ 9 / 8
    nlinarith
  · obtain ⟨h1, h2⟩ := separation_arcs hL hk hj
    exact ⟨h1, by linarith⟩
  · show 9 * Real.pi * 10 ^ 9 / 10 / (41 * Real.pi * 10 ^ 9 / 32 - Real.pi * 10 ^ 9 / 40)
      = 144 / 201
    field_simp
    ring
  · show Real.pi * 10 ^ 9 / (9 * Real.pi * 10 ^ 9 / 8 - Real.pi * 10 ^ 9 / 36) = 72 / 79
    field_simp
    ring

end Signal

end CSD.RecordLayer

end
