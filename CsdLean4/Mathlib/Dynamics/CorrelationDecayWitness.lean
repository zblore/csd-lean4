/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Dynamics.CorrelationDecay
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Group.Measure

/-!
# A non-vacuity witness for `HasCorrelationDecay`

**Category:** 1-Mathlib. The equilibration arc's E5(a)
(`specs/equilibration-arc-plan.md`): E4 is a conditional, so somebody must show its antecedent
is satisfiable at all — otherwise the whole arc is a theorem about the empty set.

## Why the witness has to look like this

`HasCorrelationDecay` with a **summable** envelope forces the correlations to converge to
`⟨f⟩²`, so there is no way to cheat by choosing `ε` large. Two consequences pin the shape of any
witness:

* `HasCorrelationDecay.integral_mul_self_eq_of_periodic` — a **periodic** map forces `⟨f²⟩ = ⟨f⟩²`,
  i.e. an a.e. constant observable.
* Every measure-preserving map of a **finite or countable** probability space is periodic on its
  support (mass is preserved and the atoms have positive mass), so no atomic space carries a
  witness.

So a genuine witness needs a **non-atomic** space and a genuinely non-periodic map. The doubling
map on the circle is the minimal such object, and this file uses it.

## The construction, and why it needs no Fourier analysis

`Circ = ℝ ⧸ ℤ` with its normalized Haar measure, `doubling x = 2x`, and the observable
`circObs x = Re e^{2πix} = cos 2πx`. Every correlation is computed by the **sign-flip argument
already used throughout `Q24`**, not by integration:

* rotating by `2^{-(s+1)}` sends `2^s x ↦ 2^s x + 1/2`, and `circObs` is odd under the half-turn,
  so the `s`-factor flips sign;
* the same rotation sends `2^t x ↦ 2^t x + 2^{t-s-1}`, an *integer*, hence unchanged, so for
  `s < t` the `t`-factor is fixed.

The integrand is therefore odd under a measure-preserving translation, so its integral is zero:
correlations vanish **exactly**, at every lag `≥ 1`. The same trick with a quarter-turn (which
exchanges real and imaginary parts) gives `⟨circObs²⟩ = 1/2` with no integral evaluated either —
the quarter-phase move of `Q24`'s `phaseFlip`.

## What is proved

* ★★ `circ_hasCorrelationDecay` — the antecedent holds with the finitely-supported envelope
  `ε = fun u => if u = 0 then 1 else 0`, which is `circ_summable`;
* ★ `integral_circObs_sq` — `⟨circObs²⟩ = 1/2`, and `integral_circObs` — `⟨circObs⟩ = 0`;
* ★★ `circ_nontrivial` — hence `⟨f²⟩ ≠ ⟨f⟩²`: the witness is **not** the trivial constant
  observable, which is exactly what non-vacuity requires;
* ★ `doubling_not_periodic` — a free corollary, and a consistency check on the no-go: the
  doubling map cannot be periodic, since it carries a non-constant observable with decay.

## ⚠️ Honest scope

* This witnesses the **engine**, not CSD. It says `HasCorrelationDecay` is satisfiable; it says
  nothing about whether any Σ-flow satisfies it. Indeed
  `CSD.Thermo.not_hasCorrelationDecay_blockPop_of_periodic` shows periodic Σ-flows **cannot**.
* The witness is a classical chaotic map, deliberately: the point is that the antecedent is a
  real condition met by real systems, not that the circle models a Σ.

Reference: `specs/equilibration-arc-plan.md` (E5); `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory AddCircle Complex

namespace MeasureTheory

/-! ### The circle, the doubling map, and the observable -/

/-- The circle `ℝ ⧸ ℤ` with its normalized Haar measure. -/
abbrev Circ := AddCircle (1 : ℝ)

instance : IsProbabilityMeasure (volume : Measure Circ) :=
  ⟨by simp⟩

/-- The doubling map `x ↦ 2x`, the standard non-periodic measure-preserving map. -/
noncomputable def doubling : Circ → Circ := fun x => (2 : ℕ) • x

/-- The witness observable `cos 2πx`, written as the real part of the first character. -/
noncomputable def circObs : Circ → ℝ := fun x => (fourier 1 x).re

/-- The half-turn, under which `circObs` is odd. -/
noncomputable def halfTurn : Circ := ((1 / 2 : ℝ) : Circ)

/-- The quarter-turn, which exchanges the real and imaginary parts of the character. -/
noncomputable def quarterTurn : Circ := ((1 / 4 : ℝ) : Circ)

lemma doubling_iterate (u : ℕ) (x : Circ) : doubling^[u] x = (2 ^ u : ℕ) • x := by
  induction u with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, doubling, smul_smul]
      congr 1
      ring

lemma measurable_doubling : Measurable doubling := (continuous_nsmul 2).measurable

lemma fourier_arg_add (x y : Circ) : fourier 1 (x + y) = fourier 1 x * fourier 1 y := by
  rw [fourier_one, fourier_one, fourier_one, toCircle_add, Circle.coe_mul]

lemma norm_fourier_one (x : Circ) : ‖fourier 1 x‖ = 1 := by
  rw [fourier_one]; exact Circle.norm_coe _

lemma measurable_circObs : Measurable circObs :=
  (Complex.continuous_re.comp (fourier 1).continuous).measurable

lemma abs_circObs_le_one (x : Circ) : |circObs x| ≤ 1 := by
  have h : |(fourier 1 x).re| ≤ ‖fourier 1 x‖ := Complex.abs_re_le_norm _
  rw [norm_fourier_one] at h
  exact h

lemma integrable_circObs : Integrable circObs volume :=
  Integrable.of_bound measurable_circObs.aestronglyMeasurable 1
    (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; exact abs_circObs_le_one x))

/-! ### The two turns -/

lemma fourier_halfTurn : fourier 1 halfTurn = -1 := by
  rw [halfTurn, fourier_coe_apply]
  norm_num
  rw [show (2 : ℂ) * Real.pi * I * (1 / 2) = Real.pi * I by ring, Complex.exp_pi_mul_I]

lemma fourier_quarterTurn : fourier 1 quarterTurn = I := by
  rw [quarterTurn, fourier_coe_apply]
  norm_num
  rw [show (2 : ℂ) * Real.pi * I * (1 / 4) = Real.pi / 2 * I by ring, Complex.exp_mul_I]
  simp

/-- **`circObs` is odd under the half-turn** — the engine of every vanishing below. -/
lemma circObs_add_halfTurn (x : Circ) : circObs (x + halfTurn) = - circObs x := by
  rw [circObs, circObs, fourier_arg_add, fourier_halfTurn, mul_neg_one, Complex.neg_re]

/-- Under the quarter-turn the observable becomes (minus) the imaginary part. -/
lemma circObs_add_quarterTurn (x : Circ) : circObs (x + quarterTurn) = -(fourier 1 x).im := by
  rw [circObs, fourier_arg_add, fourier_quarterTurn, Complex.mul_I_re]

lemma measurePreserving_rot (a : Circ) :
    MeasurePreserving (fun x : Circ => x + a) volume volume :=
  measurePreserving_add_right volume a

/-! ### The rotation that flips one factor and fixes the other -/

/-- The rotation used at a pair of times `s < t`: by `2^{-(s+1)}`. -/
noncomputable def flipPoint (s : ℕ) : Circ := ((((2 ^ (s + 1) : ℕ) : ℝ))⁻¹ : ℝ)

/-- It sends `2^s x` to `2^s x + 1/2`, so the `s`-factor flips sign. -/
lemma doubling_iterate_add_flipPoint (s : ℕ) (x : Circ) :
    doubling^[s] (x + flipPoint s) = doubling^[s] x + halfTurn := by
  rw [doubling_iterate, doubling_iterate, flipPoint, halfTurn, smul_add, ← AddCircle.coe_nsmul]
  congr 2
  rw [nsmul_eq_mul]
  push_cast
  field_simp
  ring

/-- It fixes `2^t x` whenever `t > s`, because `2^t / 2^{s+1}` is then a whole number. -/
lemma doubling_iterate_add_flipPoint_of_lt {s t : ℕ} (hst : s < t) (x : Circ) :
    doubling^[t] (x + flipPoint s) = doubling^[t] x := by
  obtain ⟨d, rfl⟩ : ∃ d, t = (s + 1) + d := ⟨t - (s + 1), by omega⟩
  rw [doubling_iterate, doubling_iterate, smul_add, flipPoint, ← AddCircle.coe_nsmul]
  have hz : ((((2 ^ (s + 1 + d) : ℕ) • (((2 ^ (s + 1) : ℕ) : ℝ))⁻¹ : ℝ)) : Circ) = 0 := by
    have hval : ((2 ^ (s + 1 + d) : ℕ) • (((2 ^ (s + 1) : ℕ) : ℝ))⁻¹ : ℝ)
        = ((2 ^ d : ℕ) : ℝ) := by
      rw [nsmul_eq_mul]
      push_cast
      rw [pow_add]
      field_simp
    rw [hval, AddCircle.coe_eq_zero_iff]
    exact ⟨((2 ^ d : ℕ) : ℤ), by simp [zsmul_eq_mul]⟩
  rw [hz, add_zero]

/-! ### ★ The correlations, all by symmetry -/

lemma integrable_circObs_iterate (t : ℕ) :
    Integrable (fun x : Circ => circObs (doubling^[t] x)) volume :=
  Integrable.of_bound
    (measurable_circObs.comp (measurable_doubling.iterate t)).aestronglyMeasurable 1
    (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; exact abs_circObs_le_one _))

lemma integrable_circObs_pair (s t : ℕ) :
    Integrable (fun x : Circ => circObs (doubling^[s] x) * circObs (doubling^[t] x)) volume :=
  Integrable.of_bound
    ((measurable_circObs.comp (measurable_doubling.iterate s)).mul
      (measurable_circObs.comp (measurable_doubling.iterate t))).aestronglyMeasurable 1
    (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_one₀ (abs_circObs_le_one _) (abs_nonneg _) (abs_circObs_le_one _)))

/-- ★ **The mean is zero at every time**, by the half-turn. -/
lemma integral_circObs_iterate (t : ℕ) : ∫ x, circObs (doubling^[t] x) ∂volume = 0 := by
  refine integral_eq_zero_of_measurePreserving_neg (measurePreserving_rot (flipPoint t))
    (integrable_circObs_iterate t) (fun x => ?_)
  rw [doubling_iterate_add_flipPoint, circObs_add_halfTurn]

lemma integral_circObs : ∫ x, circObs x ∂volume = 0 := by
  simpa using integral_circObs_iterate 0

/-- ★★ **The correlations vanish exactly at every nonzero lag.** For `s < t` the rotation by
`2^{-(s+1)}` flips the `s`-factor and fixes the `t`-factor, so the integrand is odd. -/
lemma integral_circObs_pair_of_lt {s t : ℕ} (hst : s < t) :
    ∫ x, circObs (doubling^[s] x) * circObs (doubling^[t] x) ∂volume = 0 := by
  refine integral_eq_zero_of_measurePreserving_neg (measurePreserving_rot (flipPoint s))
    (integrable_circObs_pair s t) (fun x => ?_)
  rw [doubling_iterate_add_flipPoint, doubling_iterate_add_flipPoint_of_lt hst,
    circObs_add_halfTurn]
  ring

/-! ### ★★ The witness -/

/-- The envelope: everything is exact after lag zero. -/
noncomputable def circEnv : ℕ → ℝ := fun u => if u = 0 then 1 else 0

theorem circ_summable : Summable circEnv :=
  summable_of_ne_finset_zero (s := {0}) (fun b hb => by
    simp only [Finset.mem_singleton] at hb
    simp [circEnv, hb])

/-- ★★ **The antecedent is satisfiable.** The doubling map on the circle, with the observable
`cos 2πx`, has correlation decay with a finitely-supported envelope. -/
theorem circ_hasCorrelationDecay : HasCorrelationDecay volume doubling circObs circEnv := by
  intro s t
  rw [integral_circObs]
  rcases lt_trichotomy s t with h | h | h
  · rw [integral_circObs_pair_of_lt h]
    simp [circEnv, Nat.dist_eq_sub_of_le h.le, Nat.sub_eq_zero_iff_le, h.not_ge]
  · subst h
    rw [Nat.dist_self]
    simp only [circEnv]
    have hb : ‖∫ x, circObs (doubling^[s] x) * circObs (doubling^[s] x) ∂volume‖
        ≤ 1 * (volume (Set.univ : Set Circ)).toReal :=
      norm_integral_le_of_norm_le_const (ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_one₀ (abs_circObs_le_one _) (abs_nonneg _) (abs_circObs_le_one _)))
    simpa using hb
  · rw [integral_congr_ae (ae_of_all _ (fun x : Circ =>
      mul_comm (circObs (doubling^[s] x)) (circObs (doubling^[t] x)))),
      integral_circObs_pair_of_lt h]
    simp [circEnv, Nat.dist_eq_sub_of_le_right h.le, Nat.sub_eq_zero_iff_le, h.not_ge]

/-! ### ★ Non-vacuity: the observable is not constant -/

lemma integrable_circObs_sq :
    Integrable (fun x : Circ => circObs x * circObs x) volume := by
  simpa using integrable_circObs_pair 0 0

lemma integrable_fourierIm_sq :
    Integrable (fun x : Circ => (fourier 1 x).im * (fourier 1 x).im) volume := by
  have hm : Measurable (fun x : Circ => (fourier 1 x).im) :=
    (Complex.continuous_im.comp (fourier 1).continuous).measurable
  have hb : ∀ x : Circ, |(fourier 1 x).im| ≤ 1 := by
    intro x
    have h : |(fourier 1 x).im| ≤ ‖fourier 1 x‖ := Complex.abs_im_le_norm _
    rwa [norm_fourier_one] at h
  exact Integrable.of_bound (hm.mul hm).aestronglyMeasurable 1
    (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_one₀ (hb x) (abs_nonneg _) (hb x)))

/-- ★ **`⟨circObs²⟩ = 1/2`** — by the quarter-turn, which exchanges the real and imaginary parts,
plus `|e^{2πix}| = 1`. No integral is evaluated. -/
lemma integral_circObs_sq : ∫ x, circObs x * circObs x ∂volume = 1 / 2 := by
  have hq : ∫ x : Circ, (fourier 1 x).im * (fourier 1 x).im ∂volume
      = ∫ x : Circ, circObs x * circObs x ∂volume := by
    have h := integral_comp_of_measurePreserving (measurePreserving_rot quarterTurn)
      integrable_circObs_sq.aestronglyMeasurable
    rw [← h]
    exact integral_congr_ae (ae_of_all _ (fun x => by
      dsimp only
      rw [circObs_add_quarterTurn]
      ring))
  have hone : ∫ x : Circ, (circObs x * circObs x + (fourier 1 x).im * (fourier 1 x).im) ∂volume
      = 1 := by
    rw [integral_congr_ae (ae_of_all _ (fun x : Circ => by
      show circObs x * circObs x + (fourier 1 x).im * (fourier 1 x).im = 1
      rw [circObs, ← Complex.normSq_apply, Complex.normSq_eq_norm_sq, norm_fourier_one]
      norm_num))]
    simp
  rw [integral_add integrable_circObs_sq integrable_fourierIm_sq, hq] at hone
  linarith

/-- ★★ **The witness is non-trivial**: `⟨f²⟩ ≠ ⟨f⟩²`, so `circObs` is not a.e. constant. This is
what makes `circ_hasCorrelationDecay` a genuine non-vacuity certificate rather than a restatement
of "constants have no correlations". -/
theorem circ_nontrivial :
    ∫ x, circObs x * circObs x ∂volume ≠ (∫ y, circObs y ∂volume) ^ 2 := by
  rw [integral_circObs_sq, integral_circObs]
  norm_num

/-- ★ **A free corollary, and a consistency check on the no-go.** The doubling map is not
periodic — if it were, the periodic no-go would force `circObs` to be constant, contradicting
`circ_nontrivial`. -/
theorem doubling_not_periodic : ¬ ∃ k : ℕ, 0 < k ∧ doubling^[k] = id := by
  rintro ⟨k, hk, hper⟩
  exact circ_nontrivial
    (circ_hasCorrelationDecay.integral_mul_self_eq_of_periodic hk hper circ_summable)

end MeasureTheory
