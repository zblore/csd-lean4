/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracArrival

/-!
# A sharp arrival on the Dirac chain

**Category:** 7-SigmaLayer (the record layer). BACKLOG #268 (residue of ~~#265~~), done ahead of the
one-way signal of #256 so that its records read a speed.

~~#265~~'s `dirac_arrival` wrote a detector covering half the ring, bracketing the arrival within a
factor of seven, and its before-bound was "at most a quarter of the weight". Here: (a) **a detector of
width `ℓ/20`** half a ring away, written within a window of width `1/8` of the arrival time around
it; (b) **a causal bound**: the weight a localised state puts at distance `D` is exponentially small
in `D` until a time linear in `D`.

## A narrow detector

* `cos_le_cos_of_abs`, `cos_le_taylor`, `cos_pi_div_twenty_le` (`cos(π/20) ≤ 1 − 3/250`),
  `cos_pi_div_forty_le` (`cos(π/40) ≤ 1 − 3/1000`);
* `farArc` (the sites at angle `[19π/20, 21π/20]`, width `ℓ/20`), `sharpPacket` (`10⁴` momenta `m/10⁹`
  about `p₀ = 4` on a ring of length `ℓ = 2π·10⁹`, `c = 1`, `μ = 3`, flat amplitudes), `sharpHop`,
  `omega_sharp` (`Ω = 4/(5·10⁹)`), `sharp_spread`, `chainProp_sharpPacket`, `sharp_win`,
  `sharp_norm`; ★ `sharp_budget` — **the error budget stays below `2·10⁻⁴`** over the crossing with at
  least `10¹³` sites; `angle_farArc`;
* ★★ `regionWeight_sharp_far` (**at most `1/60` on the arc for `t ≤ 9π·10⁹/8`**),
  ★★ `regionWeight_sharp_near` (**at least `9/10` for `39π·10⁹/32 ≤ t ≤ 41π·10⁹/32`**),
  `sharp_before`, `sharp_after`; ★★★ `sharpDetector` — **the arc's detector, an actual occurrence
  written over `[9π·10⁹/8, 41π·10⁹/32]`**, around the predicted arrival `5π·10⁹/4`.

## A causal bound

* `diracHam_mulVec_apply` (the Hamiltonian on a site); `VanishesNear`;
  ★ `VanishesNear.diracHam_mulVec` — **the Hamiltonian moves the support by at most one site**;
  `pow_mulVec_eq_zero`; `norm_diracHam_mulVec_le` (`|Hφ| ≤ (2|J| + |μ|) sup |φ|`),
  `norm_pow_mulVec_le`;
* ★★ `norm_chainProp_mulVec_le` — **a state vanishing within distance `D` of `k` reaches `k` with
  amplitude at most `(h|t|)^D / D! · e^{h|t|} · sup |ψ|`**, `h = 2|J| + |μ|` (the exponential series'
  first `D` terms vanish at `k`);
* ★★ `siteWeight_chainProp_le` — **while `4e h |t| ≤ D` the weight at `k` is below `2B² 8^{−D}`**;
  ★★ `register_cone_le` — the detector at `k` has gathered at most `g t · 2B² 8^{−D}`.

## The capstone

* ★★★ `dirac_timing` — the narrow arc's detector written within `[9π·10⁹/8, 41π·10⁹/32]` around the
  arrival `5π·10⁹/4`, the arc's weight bounds, and the causal bound for every state, hop and rest
  energy.

## The findings

1. **The arrival is timed to `1/8`** by a detector of width `ℓ/20`, at the price of a packet of `10⁴`
   modes on a ring of `10¹³` sites: localisation (`1 − 1/N`) and dispersion (`(c²/μ) N k`) pull
   against each other, and the ring must be long for both to be small.
2. **The lattice has a cone, of `4e(2|J| + |μ|)` sites per unit time** — in physical units
   `4e(c + aμ)`, about `11c`: a strict, if generous, causal bound. The packets themselves move below
   `c` (~~#246~~); the cone is what the dynamics guarantees for every state.

## Honest scope

⚠️ **The two halves are separate.** The narrow detector is for the spread-out packet (it has weight
everywhere, little far away); the causal bound is for states that vanish near a site at `t = 0`. A
localised packet that both moves at `v` and has nothing ahead of its cone is not built.

⚠️ **The cone is generous**: `4e(c + aμ) ≈ 11c` against the packets' `v < c`; it is the
exponential series' bound, not a Lieb–Robinson velocity optimised for this chain.

⚠️ **The instance is one set of numbers**, and the detector law is stated (test detectors, an
intensity — #251, #266).

References: `specs/BACKLOG.md` #268, #265, #256, #263, #246, #251, #266, #39;
`RecordLayer/DiracArrival.lean` (`regionDetector`, `regionWeight_ringPacket_le`,
`le_regionWeight_ringPacket`, `chainProp`, `exp_mulVec_of_mulVec_eq_smul`);
`CV/DiracPacketLimit.lean` (`dirac_packet_limit`, `flat_sums`); `CV/DiracClockChain.lean`
(`diracHam`, `diracHam_apply_eq_zero`); E. H. Lieb, D. W. Robinson, Commun. Math. Phys. 28 (1972) 251.
-/

@[expose] public section

open MeasureTheory Set CSD.CV Complex
open scoped Matrix

namespace CSD.RecordLayer

open CSD.SigmaLayer

/-! ### Cosines -/

/-- `cos x ≤ cos δ` whenever `δ ≤ |x| ≤ 2π − δ`, for `0 ≤ δ`. -/
theorem cos_le_cos_of_abs {δ x : ℝ} (hδ0 : 0 ≤ δ) (h1 : δ ≤ |x|)
    (h2 : |x| ≤ 2 * Real.pi - δ) : Real.cos x ≤ Real.cos δ := by
  rw [← Real.cos_abs]
  by_cases hx : |x| ≤ Real.pi
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hδ0 hx h1
  · rw [← Real.cos_two_pi_sub]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hδ0 (by linarith) (by linarith)

/-- An upper bound for `cos x` from its Taylor polynomial, for `0 ≤ x ≤ 1`. -/
theorem cos_le_taylor {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 * (5 / 96) := by
  have h := Real.cos_bound (x := x) (by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0] at h
  linarith [(abs_le.1 h).2]

theorem cos_pi_div_twenty_le : Real.cos (Real.pi / 20) ≤ 1 - 3 / 250 := by
  have hπ1 := Real.pi_gt_d2
  have hπ2 := Real.pi_lt_d2
  have hx0 : (0 : ℝ) ≤ Real.pi / 20 := by positivity
  have h := cos_le_taylor hx0 (by linarith)
  have ha : (3.14 / 20 : ℝ) ≤ Real.pi / 20 := by linarith
  have hb : Real.pi / 20 ≤ (3.15 / 20 : ℝ) := by linarith
  have h2 : (3.14 / 20 : ℝ) ^ 2 ≤ (Real.pi / 20) ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have h4 : (Real.pi / 20) ^ 4 ≤ (3.15 / 20 : ℝ) ^ 4 := pow_le_pow_left₀ hx0 hb 4
  norm_num at h2 h4 ⊢
  linarith

theorem cos_pi_div_forty_le : Real.cos (Real.pi / 40) ≤ 1 - 3 / 1000 := by
  have hπ1 := Real.pi_gt_d2
  have hπ2 := Real.pi_lt_d2
  have hx0 : (0 : ℝ) ≤ Real.pi / 40 := by positivity
  have h := cos_le_taylor hx0 (by linarith)
  have ha : (3.14 / 40 : ℝ) ≤ Real.pi / 40 := by linarith
  have hb : Real.pi / 40 ≤ (3.15 / 40 : ℝ) := by linarith
  have h2 : (3.14 / 40 : ℝ) ^ 2 ≤ (Real.pi / 40) ^ 2 := pow_le_pow_left₀ (by norm_num) ha 2
  have h4 : (Real.pi / 40) ^ 4 ≤ (3.15 / 40 : ℝ) ^ 4 := pow_le_pow_left₀ hx0 hb 4
  norm_num at h2 h4 ⊢
  linarith

variable {L : ℕ} [NeZero L]

/-! ### A well-localised packet and a narrow detector -/

/-- **The arc half a ring away**, of width `ℓ/20`: the sites at angle `[19π/20, 21π/20]`. -/
def farArc (L : ℕ) [NeZero L] : Finset (ZMod L) :=
  Finset.univ.filter fun k => 19 * L ≤ 40 * k.val ∧ 40 * k.val ≤ 21 * L

/-- **The sharp packet**: the `10⁴` momenta `m/10⁹`, `4·10⁹ ≤ m < 4·10⁹ + 10⁴`, of a ring of
physical length `ℓ = 2π·10⁹`, with `c = 1`, `μ = 3` and flat amplitudes: momentum about `p₀ = 4`,
velocity `4/5`. -/
noncomputable def sharpPacket (t : ℝ) : ZMod L × Fin 2 → ℂ :=
  ringPacket (L := L) 1 3 (2 * Real.pi * 10 ^ 9)
    (Finset.Ico (4 * 10 ^ 9) (4 * 10 ^ 9 + (10000 : ℕ)))
    (fun _ => ((1 / Real.sqrt (10000 : ℕ) : ℝ) : ℂ)) t

/-- Its hop on `L` sites. -/
noncomputable def sharpHop (L : ℕ) : ℝ := scaledHop 1 (2 * Real.pi * 10 ^ 9 / L)

/-- Its predicted angular velocity on the ring: `Ω = (2π/ℓ) v = 4/(5·10⁹)`. -/
theorem omega_sharp : 2 * Real.pi / (2 * Real.pi * 10 ^ 9) * vRel 1 3 (1 * 4) = 4 / (5 * 10 ^ 9) := by
  rw [vRel_cross]
  field_simp

omit [NeZero L] in
theorem sharp_spread : ∀ m ∈ Finset.Ico (4 * 10 ^ 9 : ℤ) (4 * 10 ^ 9 + (10000 : ℕ)),
    |2 * Real.pi * m / (2 * Real.pi * 10 ^ 9) - 4| ≤ 10000 / 10 ^ 9 := by
  intro m hm
  rw [Finset.mem_Ico] at hm
  have hm' : (4 * 10 ^ 9 : ℝ) ≤ m ∧ (m : ℝ) ≤ 4 * 10 ^ 9 + 9999 := by
    constructor <;> exact_mod_cast (by omega)
  rw [show 2 * Real.pi * m / (2 * Real.pi * 10 ^ 9) = m / 10 ^ 9 by field_simp, abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ (by norm_num)]
    nlinarith [hm'.1]
  · rw [sub_le_iff_le_add, div_le_iff₀ (by norm_num)]
    nlinarith [hm'.2]

/-- The whole chain carries the sharp packet. -/
theorem chainProp_sharpPacket (t : ℝ) :
    chainProp (L := L) (sharpHop L) 3 t *ᵥ sharpPacket (L := L) 0 = sharpPacket t := by
  unfold sharpPacket ringPacket sharpHop
  exact chainProp_packet _ _ _ _ t

section Sharp

variable (hL : 10 ^ 13 ≤ L)
include hL

omit [NeZero L] in
theorem sharp_win : ∀ m ∈ Finset.Ico (4 * 10 ^ 9 : ℤ) (4 * 10 ^ 9 + (10000 : ℕ)),
    4 * 10 ^ 9 ≤ m ∧ m + 1 < 4 * 10 ^ 9 + L := by
  intro m hm
  rw [Finset.mem_Ico] at hm
  constructor <;> omega

theorem sharp_norm : ∑ _m ∈ Finset.Ico (4 * 10 ^ 9 : ℤ) (4 * 10 ^ 9 + (10000 : ℕ)),
    ‖((1 / Real.sqrt (10000 : ℕ) : ℝ) : ℂ)‖ ^ 2 = 1 :=
  (flat_packet_localised (L := L) (c := 1) (μ := 3) (ℓ := 2 * Real.pi * 10 ^ 9) (by norm_num)
    (by positivity) (4 * 10 ^ 9) (by norm_num) (by omega)).1

/-- **The sharp packet's error budget stays below `2·10⁻⁴`** over its crossing,
`0 ≤ t ≤ 41π·10⁹/32`, on at least `10¹³` sites. -/
theorem sharp_budget {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 41 * Real.pi * 10 ^ 9 / 32) :
    1 - (transPhase (sharpPacket (L := L) 0)).re
      + |t| * limitErr 1 3 (2 * Real.pi * 10 ^ 9) (10000 / 10 ^ 9) 4 (2 * Real.pi * 10 ^ 9 / L)
      ≤ 2 / 10 ^ 4 := by
  have hπ := Real.pi_pos
  have hπ2 : Real.pi < 63 / 20 := by
    have := Real.pi_lt_d2
    norm_num at this ⊢
    linarith
  have hLr : (10 ^ 13 : ℝ) ≤ L := by exact_mod_cast hL
  obtain ⟨hW, -⟩ := noWrap_distinct_of_window (L := L) (sharp_win hL)
  have hRe := re_transPhase_ringPacket_ge (L := L) (c := 1) (μ := 3) (ℓ := 2 * Real.pi * 10 ^ 9)
    (by norm_num) (by positivity) hW (fun _ => 1 / Real.sqrt (10000 : ℕ)) (fun _ => by positivity)
  rw [(flat_sums (4 * 10 ^ 9) (N := 10000) (by norm_num)).2] at hRe
  have h6 : Real.pi * 1 / (2 * Real.pi * 10 ^ 9 * 3) = 1 / (6 * 10 ^ 9) := by field_simp; ring
  rw [h6] at hRe
  have hRe' : 1 - 1 / 10000 - 1 / 10 ^ 18 ≤ (transPhase (sharpPacket (L := L) 0)).re := by
    refine le_trans ?_ hRe
    norm_num
  set a := 2 * Real.pi * 10 ^ 9 / L
  have ha0 : 0 ≤ a := by positivity
  have ha : a ≤ 63 / 100000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have herr : limitErr 1 3 (2 * Real.pi * 10 ^ 9) (10000 / 10 ^ 9) 4 a
      = 1 / 10 ^ 9 * ((10000 + 1) / (3 * 10 ^ 9) + 104 / 9 * a ^ 2) := by
    unfold limitErr
    field_simp
    ring
  have herr0 : 0 ≤ 1 / 10 ^ 9 * ((10000 + 1) / (3 * 10 ^ 9) + 104 / 9 * a ^ 2) := by positivity
  have hterm : |t| * limitErr 1 3 (2 * Real.pi * 10 ^ 9) (10000 / 10 ^ 9) 4 a
      ≤ 41 * (63 / 20) * 10 ^ 9 / 32
        * (1 / 10 ^ 9 * ((10000 + 1) / (3 * 10 ^ 9) + 104 / 9 * (63 / 100000) ^ 2)) := by
    rw [herr, abs_of_nonneg ht0]
    have ht' : t ≤ 41 * (63 / 20) * 10 ^ 9 / 32 := by nlinarith
    have ha2 : a ^ 2 ≤ (63 / 100000) ^ 2 := pow_le_pow_left₀ ha0 ha 2
    calc t * (1 / 10 ^ 9 * ((10000 + 1) / (3 * 10 ^ 9) + 104 / 9 * a ^ 2))
        ≤ 41 * (63 / 20) * 10 ^ 9 / 32 * (1 / 10 ^ 9 * ((10000 + 1) / (3 * 10 ^ 9) + 104 / 9 * a ^ 2)) :=
          mul_le_mul_of_nonneg_right ht' herr0
      _ ≤ _ := by gcongr
  have hnum : 41 * (63 / 20) * 10 ^ 9 / 32
      * (1 / 10 ^ 9 * ((10000 + 1) / (3 * 10 ^ 9) + 104 / 9 * (63 / 100000 : ℝ) ^ 2))
      ≤ 9 / 10 ^ 5 := by norm_num
  linarith

/-- The arc's angles: `[19π/20, 21π/20]` on it, `[0, 19π/20) ∪ (21π/20, 2π)` off it. -/
theorem angle_farArc (k : ZMod L) :
    (k ∈ farArc L → 19 * Real.pi / 20 ≤ 2 * Real.pi * k.val / L
      ∧ 2 * Real.pi * k.val / L ≤ 21 * Real.pi / 20)
    ∧ (k ∉ farArc L → (0 ≤ 2 * Real.pi * k.val / L ∧ 2 * Real.pi * k.val / L < 19 * Real.pi / 20)
        ∨ (21 * Real.pi / 20 < 2 * Real.pi * k.val / L
          ∧ 2 * Real.pi * k.val / L < 2 * Real.pi)) := by
  have hπ := Real.pi_pos
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hk : (k.val : ℝ) < L := by exact_mod_cast k.val_lt
  have e : 2 * Real.pi * k.val / L = 2 * Real.pi * (k.val / L) := by ring
  rw [e]
  constructor
  · intro hk'
    simp only [farArc, Finset.mem_filter, Finset.mem_univ, true_and] at hk'
    have h1 : 19 * (L : ℝ) ≤ 40 * k.val := by exact_mod_cast hk'.1
    have h2 : 40 * (k.val : ℝ) ≤ 21 * L := by exact_mod_cast hk'.2
    have q1 : 19 / 40 ≤ (k.val : ℝ) / L := by rw [le_div_iff₀ hLpos]; linarith
    have q2 : (k.val : ℝ) / L ≤ 21 / 40 := by rw [div_le_iff₀ hLpos]; linarith
    constructor <;> nlinarith
  · intro hk'
    simp only [farArc, Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_le] at hk'
    have q0 : 0 ≤ (k.val : ℝ) / L := by positivity
    have q3 : (k.val : ℝ) / L < 1 := by rw [div_lt_iff₀ hLpos]; linarith
    rcases hk' with h | h
    · have h' : 40 * (k.val : ℝ) < 19 * L := by exact_mod_cast h
      have q : (k.val : ℝ) / L < 19 / 40 := by rw [div_lt_iff₀ hLpos]; linarith
      exact Or.inl ⟨by positivity, by nlinarith⟩
    · have h' : 21 * (L : ℝ) < 40 * k.val := by exact_mod_cast h
      have q : 21 / 40 < (k.val : ℝ) / L := by rw [lt_div_iff₀ hLpos]; linarith
      exact Or.inr ⟨by nlinarith, by nlinarith⟩

/-- ★★ **Before the packet can be near, the arc holds at most `1/60` of its weight**: for
`0 ≤ t ≤ 9π·10⁹/8`. -/
theorem regionWeight_sharp_far {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 9 * Real.pi * 10 ^ 9 / 8) :
    regionWeight (sharpPacket (L := L) t) (farArc L) ≤ 1 / 60 := by
  have hπ := Real.pi_pos
  have h := regionWeight_ringPacket_le (L := L) (c := 1) (μ := 3) (ℓ := 2 * Real.pi * 10 ^ 9)
    (P := 4) (D := 10000 / 10 ^ 9) (p₀ := 4) (by norm_num) (by norm_num) (by positivity)
    (by norm_num) (by norm_num) (sharp_win hL) sharp_spread _ (sharp_norm hL) (B := farArc L)
    (γ := Real.cos (Real.pi / 20)) t
    (fun k hk => by
      rw [omega_sharp]
      obtain ⟨h1, h2⟩ := (angle_farArc hL k).1 hk
      apply cos_le_cos_of_abs (by positivity) <;>
        rw [abs_of_nonneg (by nlinarith)] <;> nlinarith)
  have hb := sharp_budget hL ht0 (by nlinarith)
  have hc := cos_pi_div_twenty_le
  have hw := regionWeight_nonneg (sharpPacket (L := L) t) (farArc L)
  unfold sharpPacket at hb h hw ⊢
  nlinarith

/-- ★★ **Once the packet is predicted inside, the arc holds at least `9/10` of its weight**: for
`39π·10⁹/32 ≤ t ≤ 41π·10⁹/32`. -/
theorem regionWeight_sharp_near {t : ℝ} (ht0 : 39 * Real.pi * 10 ^ 9 / 32 ≤ t)
    (ht : t ≤ 41 * Real.pi * 10 ^ 9 / 32) :
    9 / 10 ≤ regionWeight (sharpPacket (L := L) t) (farArc L) := by
  have hπ := Real.pi_pos
  have hc := cos_pi_div_forty_le
  have h := le_regionWeight_ringPacket (L := L) (c := 1) (μ := 3) (ℓ := 2 * Real.pi * 10 ^ 9)
    (P := 4) (D := 10000 / 10 ^ 9) (p₀ := 4) (by norm_num) (by norm_num) (by positivity)
    (by norm_num) (by norm_num) (sharp_win hL) sharp_spread _ (sharp_norm hL) (A := farArc L)
    (γ := Real.cos (Real.pi / 40)) (by linarith) t
    (fun k hk => by
      rw [omega_sharp]
      apply cos_le_cos_of_abs (by positivity)
      · rcases (angle_farArc hL k).2 hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [abs_of_neg (by nlinarith)]; nlinarith
        · rw [abs_of_pos (by nlinarith)]; nlinarith
      · rcases (angle_farArc hL k).2 hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [abs_of_neg (by nlinarith)]; nlinarith
        · rw [abs_of_pos (by nlinarith)]; nlinarith)
  have hb := sharp_budget hL (by nlinarith) ht
  unfold sharpPacket at hb h ⊢
  set E := 1 - (transPhase (ringPacket (L := L) 1 3 (2 * Real.pi * 10 ^ 9)
      (Finset.Ico (4 * 10 ^ 9) (4 * 10 ^ 9 + (10000 : ℕ)))
      (fun _ => ((1 / Real.sqrt (10000 : ℕ) : ℝ) : ℂ)) 0)).re
    + |t| * limitErr 1 3 (2 * Real.pi * 10 ^ 9) (10000 / 10 ^ 9) 4 (2 * Real.pi * 10 ^ 9 / L)
  have hq : 3 / 1000 ≤ 1 - Real.cos (Real.pi / 40) := by linarith
  have hE : E / (1 - Real.cos (Real.pi / 40)) ≤ 1 / 10 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

theorem sharp_before {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 9 * Real.pi * 10 ^ 9 / 8) :
    1 * ∫ s in (0 : ℝ)..t,
        regionWeight (chainProp (L := L) (sharpHop L) 3 s *ᵥ sharpPacket (L := L) 0) (farArc L)
      < Real.pi * 10 ^ 9 / 32 := by
  have hπ := Real.pi_pos
  have h := intervalIntegral.integral_mono_on ht0
    ((continuous_regionWeight_chainProp (sharpHop L) 3 (sharpPacket (L := L) 0)
      (farArc L)).intervalIntegrable 0 t)
    (intervalIntegrable_const (μ := volume) (c := (1 / 60 : ℝ)))
    fun s hs => by
      rw [chainProp_sharpPacket]
      exact regionWeight_sharp_far hL hs.1 (hs.2.trans ht.le)
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
  nlinarith

theorem sharp_after :
    Real.pi * 10 ^ 9 / 32 ≤ 1 * ∫ s in (0 : ℝ)..(41 * Real.pi * 10 ^ 9 / 32),
        regionWeight (chainProp (L := L) (sharpHop L) 3 s *ᵥ sharpPacket (L := L) 0) (farArc L) := by
  have hπ := Real.pi_pos
  have hc := continuous_regionWeight_chainProp (sharpHop L) 3 (sharpPacket (L := L) 0) (farArc L)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 39 * Real.pi * 10 ^ 9 / 32)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h0 := intervalIntegral.integral_nonneg (μ := volume)
    (by positivity : (0 : ℝ) ≤ 39 * Real.pi * 10 ^ 9 / 32)
    fun s _ => regionWeight_nonneg (chainProp (L := L) (sharpHop L) 3 s *ᵥ sharpPacket (L := L) 0)
      (farArc L)
  have h1 := intervalIntegral.integral_mono_on
    (by nlinarith : 39 * Real.pi * 10 ^ 9 / 32 ≤ 41 * Real.pi * 10 ^ 9 / 32)
    (intervalIntegrable_const (μ := volume) (c := (9 / 10 : ℝ))) (hc.intervalIntegrable _ _)
    fun s hs => by
      rw [chainProp_sharpPacket]
      exact regionWeight_sharp_near hL hs.1 hs.2
  rw [intervalIntegral.integral_const, smul_eq_mul] at h1
  nlinarith

/-- ★★★ **The narrow arc's detector, written on the packet's arrival**: gain `1`, threshold
`π·10⁹/32`, an actual occurrence of the whole chain's evolution written over
`[9π·10⁹/8, 41π·10⁹/32]`. -/
noncomputable def sharpDetector {w : ℝ} (hw : 0 ≤ w) : ActualOccurrence (WholeArena L) ℕ L :=
  regionDetector (sharpHop L) 3 1 (Real.pi * 10 ^ 9 / 32) (farArc L) (sharpPacket (L := L) 0) 0 rfl
    (τ₀ := 9 * Real.pi * 10 ^ 9 / 8) (τ₁ := 41 * Real.pi * 10 ^ 9 / 32) (by positivity)
    (by nlinarith [Real.pi_pos]) hw zero_le_one (fun _ ht0 ht => sharp_before hL ht0 ht)
    (sharp_after hL)

end Sharp

/-! ### A causal bound -/

/-- **The Dirac Hamiltonian on a site**: the hop from the two neighbours' other component, and the
rest energy with its sign. -/
theorem diracHam_mulVec_apply (J μ : ℝ) (φ : ZMod L × Fin 2 → ℂ) (j : ZMod L) (a : Fin 2) :
    (diracHam J μ *ᵥ φ) (j, a)
      = (J : ℂ) * (-I) * (φ (j + 1, 1 - a) - φ (j - 1, 1 - a))
        + (μ : ℂ) * (if a = 0 then 1 else -1) * φ (j, a) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, diracHam, Matrix.of_apply,
    Fin.sum_univ_two]
  simp only [add_mul, sub_mul, mul_sub, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, mul_assoc]
  fin_cases a
  · simp [diracSx, diracSz]
    ring
  · simp [diracSx, diracSz]

/-- `φ` vanishes on every site within distance `< n` of `k`. -/
def VanishesNear (φ : ZMod L × Fin 2 → ℂ) (k : ZMod L) (n : ℕ) : Prop :=
  ∀ m : ℕ, m < n → ∀ c, φ (k + m, c) = 0 ∧ φ (k - m, c) = 0

/-- **Locality**: the Hamiltonian moves a state's support by at most one site. -/
theorem VanishesNear.diracHam_mulVec {φ : ZMod L × Fin 2 → ℂ} {k : ZMod L} {n : ℕ}
    (h : VanishesNear φ k (n + 1)) (J μ : ℝ) : VanishesNear (diracHam J μ *ᵥ φ) k n := by
  intro m hm c
  rw [diracHam_mulVec_apply, diracHam_mulVec_apply]
  have hp : k + (m : ZMod L) + 1 = k + ((m + 1 : ℕ) : ZMod L) := by push_cast; ring
  have hq : k - (m : ZMod L) - 1 = k - ((m + 1 : ℕ) : ZMod L) := by push_cast; ring
  have h1 : φ (k + (m : ZMod L) - 1, 1 - c) = 0 ∧ φ (k - (m : ZMod L) + 1, 1 - c) = 0 := by
    rcases m with _ | m'
    · simp only [Nat.cast_zero, add_zero, sub_zero]
      have := h 1 (by omega) (1 - c)
      simp only [Nat.cast_one] at this
      exact ⟨this.2, this.1⟩
    · have e1 : k + ((m' + 1 : ℕ) : ZMod L) - 1 = k + (m' : ZMod L) := by push_cast; ring
      have e2 : k - ((m' + 1 : ℕ) : ZMod L) + 1 = k - (m' : ZMod L) := by push_cast; ring
      rw [e1, e2]
      exact ⟨(h m' (by omega) _).1, (h m' (by omega) _).2⟩
  rw [hp, hq, (h (m + 1) (by omega) _).1, (h (m + 1) (by omega) _).2, h1.1, h1.2,
    (h m (by omega) c).1, (h m (by omega) c).2]
  simp

/-- The `n`-th power of the Hamiltonian vanishes at `k` while `n` is below the distance. -/
theorem pow_mulVec_eq_zero {ψ : ZMod L × Fin 2 → ℂ} {k : ZMod L} {D : ℕ}
    (h : VanishesNear ψ k D) (J μ : ℝ) {n : ℕ} (hn : n < D) (c : Fin 2) :
    (diracHam J μ ^ n *ᵥ ψ) (k, c) = 0 := by
  have key : ∀ n, n ≤ D → VanishesNear (diracHam J μ ^ n *ᵥ ψ) k (D - n) := by
    intro n
    induction n with
    | zero => intro _; simpa using h
    | succ n ih =>
      intro hn
      have h' := ih (by omega)
      rw [show D - n = (D - (n + 1)) + 1 by omega] at h'
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      exact h'.diracHam_mulVec J μ
  have := (key n hn.le) 0 (by omega) c
  simpa using this.1

/-- **The Hamiltonian's size on states**: `|(H φ)(p)| ≤ (2|J| + |μ|) · sup |φ|`. -/
theorem norm_diracHam_mulVec_le (J μ : ℝ) {φ : ZMod L × Fin 2 → ℂ} {B : ℝ}
    (hB : ∀ q, ‖φ q‖ ≤ B) (p : ZMod L × Fin 2) :
    ‖(diracHam J μ *ᵥ φ) p‖ ≤ (2 * |J| + |μ|) * B := by
  obtain ⟨j, a⟩ := p
  rw [diracHam_mulVec_apply]
  have hs : ‖((if a = 0 then 1 else -1 : ℂ))‖ = 1 := by split_ifs <;> simp
  calc ‖(J : ℂ) * (-I) * (φ (j + 1, 1 - a) - φ (j - 1, 1 - a))
        + (μ : ℂ) * (if a = 0 then 1 else -1) * φ (j, a)‖
      ≤ ‖(J : ℂ) * (-I) * (φ (j + 1, 1 - a) - φ (j - 1, 1 - a))‖
        + ‖(μ : ℂ) * (if a = 0 then 1 else -1) * φ (j, a)‖ := norm_add_le _ _
    _ ≤ |J| * (B + B) + |μ| * B := by
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, norm_mul, norm_mul, hs, mul_one, Complex.norm_real, Real.norm_eq_abs]
        gcongr
        · exact (norm_sub_le _ _).trans (add_le_add (hB _) (hB _))
        · exact hB _
    _ = (2 * |J| + |μ|) * B := by ring

theorem norm_pow_mulVec_le (J μ : ℝ) {ψ : ZMod L × Fin 2 → ℂ} {B : ℝ} (hB : ∀ q, ‖ψ q‖ ≤ B)
    (n : ℕ) (p : ZMod L × Fin 2) :
    ‖(diracHam J μ ^ n *ᵥ ψ) p‖ ≤ (2 * |J| + |μ|) ^ n * B := by
  induction n generalizing p with
  | zero => simpa using hB p
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, pow_succ, mul_comm _ (2 * |J| + |μ|), mul_assoc]
    exact norm_diracHam_mulVec_le J μ ih p

open scoped Matrix.Norms.L2Operator in
/-- ★★ **The causal bound**: a state vanishing within distance `D` of site `k`, of size at most `B`
everywhere, reaches `k` under `e^{−itH}` with amplitude at most
`(h|t|)^D / D! · e^{h|t|} · B`, `h = 2|J| + |μ|`: the exponential series' terms below order `D`
vanish there (`pow_mulVec_eq_zero`). -/
theorem norm_chainProp_mulVec_le (J μ : ℝ) {ψ : ZMod L × Fin 2 → ℂ} {k : ZMod L} {D : ℕ}
    (hv : VanishesNear ψ k D) {B : ℝ} (hB : ∀ q, ‖ψ q‖ ≤ B) (t : ℝ) (c : Fin 2) :
    ‖(chainProp J μ t *ᵥ ψ) (k, c)‖
      ≤ ((2 * |J| + |μ|) * |t|) ^ D / D.factorial * Real.exp ((2 * |J| + |μ|) * |t|) * B := by
  set h := 2 * |J| + |μ|
  set x := h * |t|
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (k, c))
  have hx0 : 0 ≤ x := by positivity
  set A : Matrix (ZMod L × Fin 2) (ZMod L × Fin 2) ℂ := (-(I * t)) • diracHam J μ
  have hA := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  let g : Matrix (ZMod L × Fin 2) (ZMod L × Fin 2) ℂ →+ ℂ :=
    { toFun := fun M => (M *ᵥ ψ) (k, c)
      map_zero' := by simp
      map_add' := fun M N => by simp [Matrix.add_mulVec] }
  have hg : Continuous g :=
    (continuous_apply (k, c)).comp (Continuous.matrix_mulVec continuous_id continuous_const)
  have h1 := hA.map g hg
  set f : ℕ → ℂ := fun n => g (((n.factorial : ℂ))⁻¹ • A ^ n)
  have hf : ∀ n, f n = ((n.factorial : ℂ))⁻¹ * (-(I * t)) ^ n * (diracHam J μ ^ n *ᵥ ψ) (k, c) :=
    fun n => by
      simp only [f, g, AddMonoidHom.coe_mk, ZeroHom.coe_mk, A, smul_pow, Matrix.smul_mulVec,
        smul_smul, Pi.smul_apply, smul_eq_mul]
  have hzero : ∀ n < D, f n = 0 := fun n hn => by
    rw [hf, pow_mulVec_eq_zero hv J μ hn c, mul_zero]
  have h1' : HasSum f (g (NormedSpace.exp A)) := h1
  have hshift := (hasSum_nat_add_iff' D).2 h1'
  rw [Finset.sum_eq_zero fun n hn => hzero n (Finset.mem_range.1 hn), sub_zero] at hshift
  have hbound : ∀ j : ℕ, ‖f (j + D)‖ ≤ x ^ D / D.factorial * B * (x ^ j / j.factorial) := by
    intro j
    rw [hf, norm_mul, norm_mul, norm_inv, Complex.norm_natCast, norm_pow, norm_neg, norm_mul,
      Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hp := norm_pow_mulVec_le J μ hB (j + D) (k, c)
    have hfac : (j.factorial : ℝ) * D.factorial ≤ (j + D).factorial := by
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add j D)
    have hjD : (0 : ℝ) < j.factorial * D.factorial := by positivity
    calc ((j + D).factorial : ℝ)⁻¹ * |t| ^ (j + D) * ‖(diracHam J μ ^ (j + D) *ᵥ ψ) (k, c)‖
        ≤ ((j + D).factorial : ℝ)⁻¹ * |t| ^ (j + D) * (h ^ (j + D) * B) := by gcongr
      _ = x ^ (j + D) * B / (j + D).factorial := by simp only [x]; rw [mul_pow]; ring
      _ ≤ x ^ (j + D) * B / (j.factorial * D.factorial) :=
          div_le_div_of_nonneg_left (by positivity) hjD hfac
      _ = x ^ D / D.factorial * B * (x ^ j / j.factorial) := by rw [pow_add]; field_simp
  have hsum : HasSum (fun j : ℕ => x ^ D / D.factorial * B * (x ^ j / j.factorial))
      (x ^ D / D.factorial * B * Real.exp x) := by
    have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x
    rw [← Real.exp_eq_exp_ℝ] at this
    exact this.mul_left _
  have := hshift.norm_le_of_bounded hsum hbound
  calc ‖(chainProp J μ t *ᵥ ψ) (k, c)‖ = ‖g (NormedSpace.exp A)‖ := rfl
    _ ≤ x ^ D / D.factorial * B * Real.exp x := this
    _ = _ := by ring

/-- ★★ **Inside a time linear in the distance, the weight is exponentially small**: if
`4e (2|J| + |μ|) |t| ≤ D`, the state's weight at `k` is at most `2 B² 8^{−D}`. -/
theorem siteWeight_chainProp_le (J μ : ℝ) {ψ : ZMod L × Fin 2 → ℂ} {k : ZMod L} {D : ℕ}
    (hv : VanishesNear ψ k D) {B : ℝ} (hB : ∀ q, ‖ψ q‖ ≤ B) {t : ℝ}
    (ht : 4 * Real.exp 1 * ((2 * |J| + |μ|) * |t|) ≤ D) :
    siteWeight (chainProp (L := L) J μ t *ᵥ ψ) k ≤ 2 * B ^ 2 * (1 / 8) ^ D := by
  set x := (2 * |J| + |μ|) * |t|
  have hx0 : 0 ≤ x := by positivity
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (k, 0))
  have he1 : 2 ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  -- `x^D / D! ≤ (e x / D)^D ≤ 4^{−D}`
  have hA : x ^ D / D.factorial ≤ (1 / 4) ^ D := by
    rcases Nat.eq_zero_or_pos D with hD | hD
    · subst hD
      simp
    · have hDr : (0 : ℝ) < D := by exact_mod_cast hD
      have hst := Real.pow_div_factorial_le_exp (D : ℝ) hDr.le D
      have hf : (0 : ℝ) < D.factorial := by positivity
      have hex : Real.exp 1 * x / D ≤ 1 / 4 := by
        rw [div_le_iff₀ hDr]
        linarith
      have hex0 : 0 ≤ Real.exp 1 * x / D := by positivity
      have hst' : (D : ℝ) ^ D / D.factorial ≤ Real.exp 1 ^ D := by rwa [Real.exp_one_pow]
      calc x ^ D / D.factorial
          = (Real.exp 1 * x / D) ^ D * ((D : ℝ) ^ D / D.factorial) / Real.exp 1 ^ D := by
            rw [div_pow, mul_pow]
            field_simp
            simp only [x, mul_pow]
            ring
        _ ≤ (Real.exp 1 * x / D) ^ D * Real.exp 1 ^ D / Real.exp 1 ^ D := by gcongr
        _ = (Real.exp 1 * x / D) ^ D := by field_simp
        _ ≤ (1 / 4) ^ D := pow_le_pow_left₀ hex0 hex D
  -- `e^{2x} ≤ 2^D`
  have hE : Real.exp x ^ 2 ≤ 2 ^ D := by
    rw [← Real.exp_nat_mul]
    have hl : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have := Real.one_sub_inv_le_log_of_pos (x := 2) two_pos
      norm_num at this ⊢
      linarith
    have hx8 : x ≤ D / 8 := by
      rw [le_div_iff₀ (by norm_num)]
      nlinarith
    calc Real.exp (((2 : ℕ) : ℝ) * x) ≤ Real.exp (D * Real.log 2) :=
          Real.exp_le_exp.2 (by push_cast; nlinarith)
      _ = Real.exp (Real.log 2) ^ D := Real.exp_nat_mul _ D
      _ = 2 ^ D := by rw [Real.exp_log two_pos]
  have hamp : ∀ c, ‖(chainProp (L := L) J μ t *ᵥ ψ) (k, c)‖
      ≤ x ^ D / D.factorial * Real.exp x * B := fun c => norm_chainProp_mulVec_le J μ hv hB t c
  have hA0 : 0 ≤ x ^ D / D.factorial := by positivity
  calc siteWeight (chainProp (L := L) J μ t *ᵥ ψ) k
      ≤ 2 * (x ^ D / D.factorial * Real.exp x * B) ^ 2 := by
        rw [siteWeight, Fin.sum_univ_two]
        have h0 := pow_le_pow_left₀ (norm_nonneg _) (hamp 0) 2
        have h1 := pow_le_pow_left₀ (norm_nonneg _) (hamp 1) 2
        linarith
    _ = 2 * B ^ 2 * ((x ^ D / D.factorial) ^ 2 * Real.exp x ^ 2) := by ring
    _ ≤ 2 * B ^ 2 * (((1 / 4) ^ D) ^ 2 * 2 ^ D) := by
        gcongr
    _ = 2 * B ^ 2 * (1 / 8) ^ D := by
        rw [← pow_mul, mul_comm D 2, pow_mul, ← mul_pow]
        norm_num

/-- ★★ **A detector beyond the cone is not written early**: for a state vanishing within distance
`D` of site `k`, of size at most `B`, the register of the detector at `k` (gain `g ≥ 0`) has
gathered at most `g t · 2B² 8^{−D}` by any time `t ≤ D / (4e(2|J| + |μ|))`. -/
theorem register_cone_le (J μ : ℝ) {g : ℝ} (hg : 0 ≤ g) {ψ : ZMod L × Fin 2 → ℂ} {k : ZMod L}
    {D : ℕ} (hv : VanishesNear ψ k D) {B : ℝ} (hB : ∀ q, ‖ψ q‖ ≤ B) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : 4 * Real.exp 1 * ((2 * |J| + |μ|) * t) ≤ D) :
    g * ∫ s in (0 : ℝ)..t, regionWeight (chainProp (L := L) J μ s *ᵥ ψ) {k}
      ≤ g * (t * (2 * B ^ 2 * (1 / 8) ^ D)) := by
  refine mul_le_mul_of_nonneg_left ?_ hg
  have h := intervalIntegral.integral_mono_on ht0
    ((continuous_regionWeight_chainProp J μ ψ {k}).intervalIntegrable 0 t)
    (intervalIntegrable_const (μ := volume) (c := 2 * B ^ 2 * (1 / 8) ^ D))
    fun s hs => by
      rw [regionWeight, Finset.sum_singleton]
      refine siteWeight_chainProp_le J μ hv hB ?_
      rw [abs_of_nonneg hs.1]
      have : (2 * |J| + |μ|) * s ≤ (2 * |J| + |μ|) * t :=
        mul_le_mul_of_nonneg_left hs.2 (by positivity)
      nlinarith [Real.exp_pos 1]
  rwa [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h

/-- ★★★ **A sharp arrival and a causal bound** (BACKLOG #268). On a ring of physical length
`ℓ = 2π·10⁹` with at least `10¹³` sites, the packet of `10⁴` momenta about `p₀ = 4` (`c = 1`,
`μ = 3`, `v = 4/5`), carried by the whole chain:

* while it cannot be near — `0 ≤ t ≤ 9π·10⁹/8` — the arc of width `ℓ/20` half a ring away holds at
  most `1/60` of its weight; once it is predicted inside — `39π·10⁹/32 ≤ t ≤ 41π·10⁹/32` — at least
  `9/10`;
* the arc's detector is an actual occurrence written over `[9π·10⁹/8, 41π·10⁹/32]`, which contains
  the predicted arrival `(ℓ/2)/v = 5π·10⁹/4` and has width `1/8` of it;
* **the causal bound**: for any hop `J`, rest energy `μ` and state vanishing within distance `D` of a
  site, of size at most `B`, the weight at that site stays below `2B² 8^{−D}` while
  `4e(2|J| + |μ|)|t| ≤ D` — a cone of `4e(2|J| + |μ|)` sites per unit time. -/
theorem dirac_timing (hL : 10 ^ 13 ≤ L) {w : ℝ} (hw : 0 ≤ w) :
    let o := sharpDetector hL hw
    o.writeStart = 9 * Real.pi * 10 ^ 9 / 8 ∧ o.writeEnd = 41 * Real.pi * 10 ^ 9 / 32
    ∧ o.value = 1 ∧ o.site = (farArc L).image siteFin
    ∧ (∀ t, chainProp (L := L) (sharpHop L) 3 t *ᵥ sharpPacket (L := L) 0 = sharpPacket t)
    ∧ 2 * Real.pi / (2 * Real.pi * 10 ^ 9) * vRel 1 3 (1 * 4) = 4 / (5 * 10 ^ 9)
    ∧ (9 * Real.pi * 10 ^ 9 / 8 ≤ 5 * Real.pi * 10 ^ 9 / 4
        ∧ 5 * Real.pi * 10 ^ 9 / 4 ≤ 41 * Real.pi * 10 ^ 9 / 32)
    ∧ (∀ t, 0 ≤ t → t ≤ 9 * Real.pi * 10 ^ 9 / 8 →
        regionWeight (sharpPacket (L := L) t) (farArc L) ≤ 1 / 60)
    ∧ (∀ t, 39 * Real.pi * 10 ^ 9 / 32 ≤ t → t ≤ 41 * Real.pi * 10 ^ 9 / 32 →
        9 / 10 ≤ regionWeight (sharpPacket (L := L) t) (farArc L))
    ∧ (∀ (J μ : ℝ) (ψ : ZMod L × Fin 2 → ℂ) (k : ZMod L) (D : ℕ), VanishesNear ψ k D →
        ∀ B : ℝ, (∀ q, ‖ψ q‖ ≤ B) → ∀ t : ℝ, 4 * Real.exp 1 * ((2 * |J| + |μ|) * |t|) ≤ D →
          siteWeight (chainProp (L := L) J μ t *ᵥ ψ) k ≤ 2 * B ^ 2 * (1 / 8) ^ D) := by
  have hπ := Real.pi_pos
  exact ⟨rfl, rfl, rfl, rfl, chainProp_sharpPacket, omega_sharp, ⟨by nlinarith, by nlinarith⟩,
    fun _ h0 h1 => regionWeight_sharp_far hL h0 h1, fun _ h0 h1 => regionWeight_sharp_near hL h0 h1,
    fun J μ _ _ _ hv _ hB _ ht => siteWeight_chainProp_le J μ hv hB ht⟩

end CSD.RecordLayer

end
