/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracRadar
public import CsdLean4.CV.DiracMassless

/-!
# Where a massless messenger is

**Category:** 7-SigmaLayer (the record layer). BACKLOG #278, second landing, first part.

The first landing (`CV/DiracMassless.lean`) bounds a massless packet's translation phase. Here that
becomes **where** the packet is: its weight off a chord arc about its predicted position, and on it
(`regionWeight_mul_le` is state-generic, so the massive arguments of `DiracArrival.lean` and
`DiracObservers.lean` carry over). Then the messenger the moving observer `B` will send in the next
parts: the massless packet on the moving window (modes about momentum `4`, `2·10⁶` of them), delayed
so that it starts at `B`'s position at `t = 0` and reaches `A` at `3·10¹³`.

## Where a massless packet is

* ★ `regionWeight_massless_le`, ★ `le_regionWeight_massless` (a region where the packet is not
  predicted has little weight; where it is, nearly all),
  ★★ `regionWeight_compl_chordArc_massless_le` (off the chord-`ρ` arc about a point `η`-close to its
  predicted position).

## `B`'s messenger

* `bMessWin`, `rightWindow_bMessWin`, `bMess_win`, `bMess` (the massless packet on the moving
  window, delayed by `3·10¹³`), `bMess_norm`; `bMessRate` (its rate `10⁻¹³ cos(4a)`),
  ★ `abs_bMessRate_sub_le` (**within `4·10⁻²³` of `10⁻¹³`**), `bMess_re_transPhase_zero`
  (`1 − 1/N`);
* ★★ `bMess_tail` — **for `0 ≤ t ≤ 8·10¹³` the messenger's weight off the chord-`1/20` arc about
  `e^{i·10⁻¹³(t − 3·10¹³)}` is at most `10⁻³`**; ★★ `bMess_near` — **on that arc, at least
  `1 − 10⁻³`**.

## Honest scope

⚠️ **The position is predicted at speed `1` in the chain's frame**: the rate is `10⁻¹³ cos(4a)`, and
the difference (`≤ 3.2·10⁻²³` per unit time) is charged to the chord, not hidden.

References: `specs/BACKLOG.md` #278, #274, #270, #259; `CV/DiracMassless.lean`
(`dirac_massless_limit`, `re_transPhase_unitAmp_zero`, `masslessErr`);
`RecordLayer/DiracArrival.lean` (`regionWeight_mul_le`, `regionWeight_ringPacket_le`,
`re_star_exp_mul_toCircle`); `RecordLayer/DiracObservers.lean` (`regionWeight_compl_chordArc_le`,
`re_star_mul_eq_chord`, `chordArc`);
`RecordLayer/DiracTwin.lean` (`moving_win`, `moving_spread`, `twinAmp`, `twin_norm`);
`RecordLayer/DiracRateTicks.lean` (`norm_exp_I_mul_sub_le`).
-/

@[expose] public section

open Set Complex CSD.CV CSD.SigmaLayer

namespace CSD.RecordLayer

variable {L : ℕ} [NeZero L]

/-! ### Where a massless packet is -/

section Packet

variable {c ℓ D p₀ : ℝ} {W : Finset ℤ} {lo : ℤ}

/-- ★ **Away from where a massless packet is predicted, a region has little weight.** -/
theorem regionWeight_massless_le (hc : 0 < c) (hℓ : 0 < ℓ) (hD0 : 0 ≤ D)
    (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L) (hR : RightWindow L W)
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D) (β : ℤ → ℂ) (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1)
    {B : Finset (ZMod L)} {γ : ℝ} (t : ℝ)
    (hB : ∀ k ∈ B, Real.cos (2 * Real.pi * k.val / L
      - 2 * Real.pi / ℓ * (c * Real.cos (ℓ / L * p₀)) * t) ≤ γ) :
    regionWeight (ringPacket (L := L) c 0 ℓ W β t) B * (1 - γ)
      ≤ 1 - (transPhase (ringPacket (L := L) c 0 ℓ W β 0)).re
        + |t| * masslessErr c ℓ D (ℓ / L) := by
  obtain ⟨hn, -, -, hdrift, -, -⟩ := dirac_massless_limit hc hℓ hD0 hWin hR hWD β hβ
  set Ω := 2 * Real.pi / ℓ * (c * Real.cos (ℓ / L * p₀))
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
  have h := regionWeight_mul_le (ringPacket (L := L) c 0 ℓ W β t) hu hB'
  rw [hn t, Complex.one_re] at h
  set T0 := transPhase (ringPacket (L := L) c 0 ℓ W β 0)
  set Tt := transPhase (ringPacket (L := L) c 0 ℓ W β t)
  have hsu : star u * u = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hu]
    norm_num
  have hsplit : (star u * Tt).re = T0.re + (star u * (Tt - u * T0)).re := by
    rw [mul_sub, ← mul_assoc, hsu, one_mul, Complex.sub_re]
    ring
  have hbound : -(|t| * masslessErr c ℓ D (ℓ / L)) ≤ (star u * (Tt - u * T0)).re := by
    have h1 := Complex.abs_re_le_norm (star u * (Tt - u * T0))
    rw [norm_mul, norm_star, hu, one_mul] at h1
    have h2 := hdrift t
    rw [hu'] at h2
    have h3 := neg_abs_le (star u * (Tt - u * T0)).re
    linarith
  linarith

/-- ★ **Where a massless packet is predicted, a region has nearly all the weight.** -/
theorem le_regionWeight_massless (hc : 0 < c) (hℓ : 0 < ℓ) (hD0 : 0 ≤ D)
    (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L) (hR : RightWindow L W)
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D) (β : ℤ → ℂ) (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1)
    {A : Finset (ZMod L)} {γ : ℝ} (hγ : γ < 1) (t : ℝ)
    (hA : ∀ k ∉ A, Real.cos (2 * Real.pi * k.val / L
      - 2 * Real.pi / ℓ * (c * Real.cos (ℓ / L * p₀)) * t) ≤ γ) :
    1 - (1 - (transPhase (ringPacket (L := L) c 0 ℓ W β 0)).re
        + |t| * masslessErr c ℓ D (ℓ / L)) / (1 - γ)
      ≤ regionWeight (ringPacket (L := L) c 0 ℓ W β t) A := by
  have h := regionWeight_massless_le hc hℓ hD0 hWin hR hWD β hβ (B := Aᶜ) t
    fun k hk => hA k (Finset.mem_compl.1 hk)
  have hsum := regionWeight_add_compl (ringPacket (L := L) c 0 ℓ W β t) A
  rw [(dirac_massless_limit hc hℓ hD0 hWin hR hWD β hβ).1 t, Complex.one_re] at hsum
  have hpos : 0 < 1 - γ := by linarith
  rw [← le_div_iff₀ hpos] at h
  linarith

/-- ★★ **Off the chord arc about its predicted position**: if `e^{iΩt}` is within `η ≤ ρ` of `z`,
the weight off the chord-`ρ` arc about `z`, times `(ρ − η)²/2`, is at most the budget. -/
theorem regionWeight_compl_chordArc_massless_le (hc : 0 < c) (hℓ : 0 < ℓ) (hD0 : 0 ≤ D)
    (hWin : ∀ m ∈ W, lo ≤ m ∧ m + 1 < lo + L) (hR : RightWindow L W)
    (hWD : ∀ m ∈ W, |2 * Real.pi * m / ℓ - p₀| ≤ D) (β : ℤ → ℂ) (hβ : ∑ m ∈ W, ‖β m‖ ^ 2 = 1)
    {z : ℂ} {ρ η : ℝ} (hηρ : η ≤ ρ) (t : ℝ)
    (hz : ‖exp (I * ((2 * Real.pi / ℓ * (c * Real.cos (ℓ / L * p₀)) * t : ℝ) : ℂ)) - z‖ ≤ η) :
    regionWeight (ringPacket (L := L) c 0 ℓ W β t) (chordArc z ρ)ᶜ * ((ρ - η) ^ 2 / 2)
      ≤ 1 - (transPhase (ringPacket (L := L) c 0 ℓ W β 0)).re
        + |t| * masslessErr c ℓ D (ℓ / L) := by
  have h := regionWeight_massless_le hc hℓ hD0 hWin hR hWD β hβ
    (B := (chordArc z ρ)ᶜ) (γ := 1 - (ρ - η) ^ 2 / 2) t fun k hk => by
      rw [Finset.mem_compl, mem_chordArc, not_le] at hk
      rw [← re_star_exp_mul_toCircle, re_star_mul_eq_chord (Circle.norm_coe _)
        (norm_exp_I_mul_ofReal_eq_one _)]
      have hd : ρ - η ≤ ‖(ZMod.toCircle k : ℂ)
          - exp (I * ((2 * Real.pi / ℓ * (c * Real.cos (ℓ / L * p₀)) * t : ℝ) : ℂ))‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub (ZMod.toCircle k : ℂ)
          (exp (I * ((2 * Real.pi / ℓ * (c * Real.cos (ℓ / L * p₀)) * t : ℝ) : ℂ))) z
        linarith
      have hsq := pow_le_pow_left₀ (by linarith) hd 2
      linarith
  rwa [show 1 - (1 - (ρ - η) ^ 2 / 2) = (ρ - η) ^ 2 / 2 by ring] at h

end Packet

/-! ### `B`'s messenger -/

/-- The moving window: `2·10⁶` modes about momentum `4`. -/
def bMessWin : Finset ℤ := Finset.Ico (4 * 10 ^ 13 : ℤ) (4 * 10 ^ 13 + (2000000 : ℕ))

section Messenger

variable (hL : 10 ^ 19 ≤ L)
include hL

omit [NeZero L] in
/-- The moving window holds right-movers. -/
theorem rightWindow_bMessWin : RightWindow L bMessWin := by
  intro m hm
  rw [bMessWin, Finset.mem_Ico] at hm
  have hLr : (10 ^ 19 : ℝ) ≤ L := by exact_mod_cast hL
  have hm0 : (4 * 10 ^ 13 : ℝ) ≤ m := by exact_mod_cast hm.1
  have hm1 : (m : ℝ) ≤ 4 * 10 ^ 13 + 2000000 := by
    have : m < 4 * 10 ^ 13 + (2000000 : ℕ) := hm.2
    have : (m : ℝ) < 4 * 10 ^ 13 + 2000000 := by exact_mod_cast this
    linarith
  have hLpos : (0 : ℝ) < L := by linarith [show (0 : ℝ) < 10 ^ 19 by norm_num]
  constructor
  · unfold angleZ
    have : (0 : ℝ) < m := by linarith
    positivity
  · unfold angleZ
    rw [div_lt_iff₀ hLpos]
    nlinarith [Real.pi_pos]

/-- **`B`'s messenger**: the massless packet on the moving window, delayed so that it reaches `A`
(site `0`) at `3·10¹³`. -/
noncomputable def bMess (t : ℝ) : ZMod L × Fin 2 → ℂ :=
  ringPacket (L := L) 1 0 (2 * Real.pi * 10 ^ 13) bMessWin twinAmp (t - 3 * 10 ^ 13)

omit [NeZero L] in
theorem bMess_win : ∀ m ∈ bMessWin, 4 * 10 ^ 13 ≤ m ∧ m + 1 < 4 * 10 ^ 13 + L := by
  intro m hm
  rw [bMessWin, Finset.mem_Ico] at hm
  constructor
  · exact hm.1
  · have : (2000000 : ℤ) < L := by
      have : (2000000 : ℕ) < L := lt_of_lt_of_le (by norm_num) hL
      exact_mod_cast this
    push_cast at hm
    omega

theorem bMess_norm (t : ℝ) : chainInner (bMess (L := L) t) (bMess t) = 1 :=
  (dirac_massless_limit (L := L) (c := 1) (ℓ := 2 * Real.pi * 10 ^ 13) (D := 2 / 10 ^ 7)
    (p₀ := 4) one_pos (by positivity) (by positivity) (bMess_win hL) (rightWindow_bMessWin hL)
    moving_spread twinAmp (twin_norm hL _)).1 _

omit hL in
/-- **The messenger's rate** `10⁻¹³ cos(4a)`. -/
noncomputable def bMessRate (L : ℕ) : ℝ :=
  2 * Real.pi / (2 * Real.pi * 10 ^ 13) * (1 * Real.cos (2 * Real.pi * 10 ^ 13 / L * 4))

omit [NeZero L] in
/-- ★ **The messenger's rate is `10⁻¹³` to `4·10⁻²³`.** -/
theorem abs_bMessRate_sub_le : |bMessRate L - 1 / 10 ^ 13| ≤ 4 / 10 ^ 23 := by
  have hLr : (10 ^ 19 : ℝ) ≤ L := by exact_mod_cast hL
  have hπ2 : Real.pi < 63 / 20 := by
    have := Real.pi_lt_d2
    norm_num at this ⊢
    linarith
  set a := 2 * Real.pi * 10 ^ 13 / L
  have ha0 : 0 < a := by positivity
  have ha : a ≤ 63 / 10 ^ 7 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have e : bMessRate L = 1 / 10 ^ 13 * Real.cos (a * 4) := by
    rw [bMessRate, one_mul, show 2 * Real.pi / (2 * Real.pi * 10 ^ 13) = 1 / 10 ^ 13 by
      field_simp]
  rw [e]
  have h1 := Real.one_sub_sq_div_two_le_cos (x := a * 4)
  have h2 := Real.cos_le_one (a * 4)
  rw [abs_le]
  constructor <;> nlinarith

omit hL in
/-- The messenger's initial localisation: `Re T(0) = 1 − 1/N`. -/
theorem bMess_re_transPhase_zero (hL : 10 ^ 19 ≤ L) :
    (transPhase (ringPacket (L := L) 1 0 (2 * Real.pi * 10 ^ 13) bMessWin twinAmp 0)).re
      = 1 - 1 / (2000000 : ℕ) := by
  obtain ⟨hW, -⟩ := noWrap_distinct_of_window (L := L) (bMess_win hL)
  have hLpos : (0 : ℝ) < L := by
    have : (10 ^ 19 : ℝ) ≤ L := by exact_mod_cast hL
    linarith [show (0 : ℝ) < 10 ^ 19 by norm_num]
  have hJ : 0 < scaledHop 1 (2 * Real.pi * 10 ^ 13 / L) := by
    unfold scaledHop
    positivity
  have h := re_transPhase_unitAmp_zero (L := L) (J := scaledHop 1 (2 * Real.pi * 10 ^ 13 / L)) hJ
    (rightWindow_bMessWin hL) hW (fun _ => 1 / Real.sqrt (2000000 : ℕ))
  obtain ⟨-, h2⟩ := flat_sums (4 * 10 ^ 13) (N := 2000000) (by norm_num)
  rw [ringPacket]
  exact h.trans h2

/-- ★★ **Where `B`'s messenger is**: for `0 ≤ t ≤ 8·10¹³`, its weight off the chord-`1/20` arc
about `e^{i·10⁻¹³(t − 3·10¹³)}` is at most `10⁻³`. -/
theorem bMess_tail {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 8 * 10 ^ 13) :
    regionWeight (bMess (L := L) t)
        (chordArc (exp (I * ((1 / 10 ^ 13 * (t - 3 * 10 ^ 13) : ℝ) : ℂ))) (1 / 20))ᶜ
      ≤ 1 / 1000 := by
  have hLr : (10 ^ 19 : ℝ) ≤ L := by exact_mod_cast hL
  have hπ2 : Real.pi < 63 / 20 := by
    have := Real.pi_lt_d2
    norm_num at this ⊢
    linarith
  set s := t - 3 * 10 ^ 13 with hs
  have hs_abs : |s| ≤ 5 * 10 ^ 13 := by rw [abs_le]; constructor <;> linarith
  have hrate := abs_bMessRate_sub_le hL
  have hz : ‖exp (I * ((bMessRate L * s : ℝ) : ℂ))
      - exp (I * ((1 / 10 ^ 13 * s : ℝ) : ℂ))‖ ≤ 1 / 10 ^ 8 := by
    have h := norm_exp_I_mul_sub_le (bMessRate L) (1 / 10 ^ 13) s
    rw [show I * ((bMessRate L * s : ℝ) : ℂ) = I * (((bMessRate L : ℝ) : ℂ) * (s : ℂ)) by
        push_cast; ring,
      show I * ((1 / 10 ^ 13 * s : ℝ) : ℂ) = I * (((1 / 10 ^ 13 : ℝ) : ℂ) * (s : ℂ)) by
        push_cast; ring]
    refine h.trans ?_
    calc |s| * |bMessRate L - 1 / 10 ^ 13| ≤ 5 * 10 ^ 13 * (4 / 10 ^ 23) :=
          mul_le_mul hs_abs hrate (abs_nonneg _) (by norm_num)
      _ ≤ 1 / 10 ^ 8 := by norm_num
  have h := regionWeight_compl_chordArc_massless_le (L := L) (c := 1) (ℓ := 2 * Real.pi * 10 ^ 13)
    (D := 2 / 10 ^ 7) (p₀ := 4) one_pos (by positivity) (by positivity) (bMess_win hL)
    (rightWindow_bMessWin hL) moving_spread twinAmp (twin_norm hL _)
    (z := exp (I * ((1 / 10 ^ 13 * s : ℝ) : ℂ))) (ρ := 1 / 20) (η := 1 / 10 ^ 8) (by norm_num) s hz
  rw [bMess_re_transPhase_zero hL] at h
  set a := 2 * Real.pi * 10 ^ 13 / L
  have ha0 : 0 < a := by positivity
  have ha : a ≤ 63 / 10 ^ 7 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hE : |s| * masslessErr 1 (2 * Real.pi * 10 ^ 13) (2 / 10 ^ 7) a ≤ 1 / 10 ^ 10 := by
    have e : masslessErr 1 (2 * Real.pi * 10 ^ 13) (2 / 10 ^ 7) a
        = 1 / 10 ^ 13 * a * (2 / 10 ^ 7 + 1 / 10 ^ 13) := by
      rw [masslessErr]
      field_simp
    rw [e]
    have h1 : 0 ≤ 1 / 10 ^ 13 * a * (2 / 10 ^ 7 + 1 / 10 ^ 13) := by positivity
    calc |s| * (1 / 10 ^ 13 * a * (2 / 10 ^ 7 + 1 / 10 ^ 13))
        ≤ 5 * 10 ^ 13 * (1 / 10 ^ 13 * (63 / 10 ^ 7) * (2 / 10 ^ 7 + 1 / 10 ^ 13)) := by
          gcongr
      _ ≤ 1 / 10 ^ 10 := by norm_num
  have hnn := regionWeight_nonneg (bMess (L := L) t)
    (chordArc (exp (I * ((1 / 10 ^ 13 * s : ℝ) : ℂ))) (1 / 20))ᶜ
  unfold bMess at hnn ⊢
  rw [← hs] at hnn ⊢
  have hN : ((2000000 : ℕ) : ℝ) = 2000000 := by norm_num
  rw [hN] at h
  set w := regionWeight (ringPacket (L := L) 1 0 (2 * Real.pi * 10 ^ 13) bMessWin twinAmp s)
    (chordArc (exp (I * ((1 / 10 ^ 13 * s : ℝ) : ℂ))) (1 / 20))ᶜ
  have hK : (1 / 800 : ℝ) * (99 / 100) ≤ (1 / 20 - 1 / 10 ^ 8) ^ 2 / 2 := by norm_num
  have h3 := mul_le_mul_of_nonneg_left hK hnn
  nlinarith

/-- ★★ **…and on that arc it has nearly all its weight.** -/
theorem bMess_near {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 8 * 10 ^ 13) :
    1 - 1 / 1000 ≤ regionWeight (bMess (L := L) t)
        (chordArc (exp (I * ((1 / 10 ^ 13 * (t - 3 * 10 ^ 13) : ℝ) : ℂ))) (1 / 20)) := by
  have h := bMess_tail hL ht0 ht
  have hsum := regionWeight_add_compl (bMess (L := L) t)
    (chordArc (exp (I * ((1 / 10 ^ 13 * (t - 3 * 10 ^ 13) : ℝ) : ℂ))) (1 / 20))
  rw [bMess_norm hL t, Complex.one_re] at hsum
  linarith

end Messenger

end CSD.RecordLayer

end
