/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF6.MaxEntangledDeisolationFlow
public import CsdLean4.Mathlib.Probability.CGLMP

/-!
# LF6-D (QM side): the maximally-entangled qutrit violates the CGLMP inequality

**Category:** 6-Local (the `d = 3`-intrinsic Bell violation for `Ψ_3`, the QM-side
payoff of the CGLMP infrastructure `Mathlib/Probability/CGLMP.lean`).

The LF6-D non-factorisation of the general `d × d` maximally-entangled state `Ψ_d`
(`no_product_partition_realises_maxEntangled`) was, up to this file, forced through the
CHSH-violating `2 × 2` Schmidt (`Φ⁺`) sector: a genuinely derived violation, but a
two-outcome (CHSH) one, so not `d`-intrinsic. This module discharges the genuinely
`d = 3` CGLMP violation for the maximally-entangled qutrit, closing that gap for `d = 3`.

## What is proved

Under the standard CGLMP phase-basis measurements on `Ψ_3` (Alice offsets
`α₁ = 0, α₂ = 1/2`; Bob offsets `β₁ = -1/4, β₂ = 1/4`), the joint outcome-difference
Born probabilities `pQM x y c = P(A_x − B_y = c)` are **computed from the Hilbert space**
(`pQM` is the marginal sum of the genuine squared overlaps
`bornPair x y k l = ‖⟨outcome_{k,l}, Ψ_3⟩‖²`, `bornPair_value` its closed form via the
roots-of-unity geometric sum). The four CGLMP-`positive` entries are `(4 + 2√3)/9`, the
four `negative` entries `1/9`, giving the exact CGLMP value

```
I_3 = cglmp 3 pQM = (12 + 8√3)/9 ≈ 2.8729                    (cglmp_maxEntangled_qutrit_eq)
```

which exceeds the local-hidden-variable bound `2` (`cglmp_maxEntangled_qutrit_gt_two`),
contradicting `ProbabilityTheory.CGLMP.cglmp_lhv_bound_three` (`I_3 ≤ 2` for every
deterministic LHV model). Hence **no** local-hidden-variable model reproduces `Ψ_3`'s
actual CGLMP outcome-difference statistics
(`no_lhv_realises_maxEntangled_cglmp`): a genuinely `d = 3`-intrinsic Bell force, not the
`2 × 2` `Φ⁺` CHSH sector.

## Honest scope

- The violation is a **genuine computation** from `Ψ_3`'s actual Born probabilities under
  real qutrit measurements: `bornPair` is a squared inner product with `maxEntangled 3`,
  the outcome vectors are the CGLMP phase-basis measurement vectors (`aVec_unit`,
  `bVec_unit`: unit vectors), and `pQM x y c` is the genuine outcome-difference marginal
  (`pQM`, `pQM_eq_pair`: `Born` depends only on `k − l` by `bornPair_periodic`). The
  value `(12 + 8√3)/9` is not asserted; every step is derived, the `√3` irrational
  (no rational analogue violates — half-integer offsets give exactly `2`).
- The LHV bound `I_3 ≤ 2` is imported from `cglmp_lhv_bound_three` (the `d = 3` finite
  optimisation, `decide` over the 81 strategies). This file supplies the QM side.
- `d = 3` only. The general-`d` (`d ≥ 4`) CGLMP violation for `Ψ_d` remains the residual.
- Foundational-triple-only (no `busch_effect_gleason`; the geometric sums and the finite
  LHV optimisation are both Gleason-free).

Reference: Collins, Gisin, Linden, Massar, Popescu, *Phys. Rev. Lett.* **88**, 040404
(2002). `specs/lf6-plan.md` (LF6-D).
-/

@[expose] public section

open Complex MeasureTheory ProbabilityTheory ProbabilityTheory.CGLMP
open CSD.LF6

namespace CSD
namespace LF6
namespace CGLMPQutrit

/-! ### The CGLMP qutrit measurement settings -/

/-- Alice's phase offset `α_x`: setting `false` (`A₁`) → `0`, `true` (`A₂`) → `1/2`. -/
noncomputable def alphaOff (x : Bool) : ℝ := if x then 1/2 else 0
/-- Bob's phase offset `β_y`: setting `false` (`B₁`) → `-1/4`, `true` (`B₂`) → `1/4`. -/
noncomputable def betaOff (y : Bool) : ℝ := if y then 1/4 else -1/4
/-- The combined offset `δ = α_x − β_y`. -/
noncomputable def deltaOff (x y : Bool) : ℝ := alphaOff x - betaOff y

/-- Alice's phase-basis angle `2π·j·(k + α_x)/3` for outcome `k`, component `j`. -/
noncomputable def aAngle (x : Bool) (k : ZMod 3) (j : Fin 3) : ℝ :=
  2 * Real.pi * (j.val : ℝ) * ((k.val : ℝ) + alphaOff x) / 3
/-- Bob's phase-basis angle `−2π·j·(l + β_y)/3` for outcome `l`, component `j`. -/
noncomputable def bAngle (y : Bool) (l : ZMod 3) (j : Fin 3) : ℝ :=
  - (2 * Real.pi * (j.val : ℝ) * ((l.val : ℝ) + betaOff y) / 3)

/-- Alice's CGLMP phase-basis measurement vector `|k⟩_{A,x} = (1/√3) ∑_j ω^{j(k+α_x)} |j⟩`
(`ω = e^{2πi/3}`), a unit vector (`aVec_unit`). -/
noncomputable def aVec (x : Bool) (k : ZMod 3) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (fun j => (Real.sqrt 3 : ℂ)⁻¹ * Complex.exp ((aAngle x k j : ℝ) * Complex.I))
/-- Bob's CGLMP phase-basis measurement vector
`|l⟩_{B,y} = (1/√3) ∑_j ω^{-j(l+β_y)} |j⟩`, a unit vector (`bVec_unit`). -/
noncomputable def bVec (y : Bool) (l : ZMod 3) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (fun j => (Real.sqrt 3 : ℂ)⁻¹ * Complex.exp ((bAngle y l j : ℝ) * Complex.I))
/-- The joint measurement outcome vector `|k⟩_{A,x} ⊗ |l⟩_{B,y}` on
`EuclideanSpace ℂ (Fin 3 × Fin 3)`. -/
noncomputable def outcome (x y : Bool) (k l : ZMod 3) : EuclideanSpace ℂ (Fin 3 × Fin 3) :=
  WithLp.toLp 2 (fun p => aVec x k p.1 * bVec y l p.2)

/-- **The joint Born probability** `P(A_x = k, B_y = l) = ‖⟨outcome_{k,l}, Ψ_3⟩‖²`: the
genuine squared overlap of the outcome vector with the maximally-entangled qutrit
`maxEntangled 3`. -/
noncomputable def bornPair (x y : Bool) (k l : ZMod 3) : ℝ :=
  ‖inner ℂ (outcome x y k l) (maxEntangled 3)‖ ^ 2

/-- The base phase `φ = −2π·((k − l) + δ)/3` of the amplitude geometric sum. -/
noncomputable def baseAngle (x y : Bool) (k l : ZMod 3) : ℝ :=
  - (2 * Real.pi * ((k.val : ℝ) - (l.val : ℝ) + deltaOff x y) / 3)

/-! ### The outcome vectors are unit vectors (genuine measurements) -/

/-- Alice's outcome vectors are unit vectors: `‖·‖² = ∑_j 1/3 = 1`. -/
lemma aVec_unit (x : Bool) (k : ZMod 3) : ‖aVec x k‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hj : ∀ j : Fin 3, ‖(aVec x k) j‖ ^ 2 = 1/3 := by
    intro j
    show ‖(Real.sqrt 3 : ℂ)⁻¹ * Complex.exp ((aAngle x k j : ℝ) * Complex.I)‖ ^ 2 = 1/3
    rw [norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_exp_ofReal_mul_I]
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num
  rw [Finset.sum_congr rfl (fun j _ => hj j), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  norm_num

/-- Bob's outcome vectors are unit vectors. -/
lemma bVec_unit (y : Bool) (l : ZMod 3) : ‖bVec y l‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hj : ∀ j : Fin 3, ‖(bVec y l) j‖ ^ 2 = 1/3 := by
    intro j
    show ‖(Real.sqrt 3 : ℂ)⁻¹ * Complex.exp ((bAngle y l j : ℝ) * Complex.I)‖ ^ 2 = 1/3
    rw [norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_exp_ofReal_mul_I]
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num
  rw [Finset.sum_congr rfl (fun j _ => hj j), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  norm_num

/-! ### The Born probability closed form (roots-of-unity geometric sum) -/

/-- The inner product with `Ψ_3` collapses onto the diagonal: only the `(i,i)` amplitudes
survive the maximally-entangled contraction. -/
lemma inner_outcome_collapse (x y : Bool) (k l : ZMod 3) :
    inner ℂ (outcome x y k l) (maxEntangled 3)
      = ((Real.sqrt 3 : ℂ))⁻¹ * ∑ i : Fin 3, (starRingEnd ℂ) ((outcome x y k l) (i,i)) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fintype.sum_prod_type,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hterm : ∀ j : Fin 3, (maxEntangled 3).ofLp (i, j) * (star (outcome x y k l).ofLp (i,j))
      = if i = j then ((Real.sqrt 3 : ℂ))⁻¹ * (starRingEnd ℂ) ((outcome x y k l) (i,i)) else 0 := by
    intro j
    rw [show (maxEntangled 3).ofLp (i,j) = (maxEntangled 3) (i,j) from rfl, maxEntangled_apply]
    by_cases h : i = j
    · subst h; simp [Pi.star_apply]
    · rw [if_neg (by simpa using h), if_neg h, zero_mul]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite_eq Finset.univ i]
  simp

/-- `‖1 + e^{iθ} + e^{2iθ}‖² = 3 + 4cos θ + 2cos 2θ` (the `d = 3` geometric-sum modulus). -/
lemma normSq_geom (θ : ℝ) :
    Complex.normSq (1 + Complex.exp (θ * Complex.I) + (Complex.exp (θ * Complex.I))^2)
      = 3 + 4 * Real.cos θ + 2 * Real.cos (2*θ) := by
  have hc2 : Real.cos (2*θ) = 2 * (Real.cos θ)^2 - 1 := Real.cos_two_mul θ
  have hpy : (Real.sin θ)^2 + (Real.cos θ)^2 = 1 := Real.sin_sq_add_cos_sq θ
  rw [Complex.exp_mul_I, Complex.normSq_apply]
  simp only [pow_two, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.cos_ofReal_im, Complex.sin_ofReal_im]
  rw [hc2]; nlinarith [hpy]

/-- **The joint Born probability closed form.** From the diagonal collapse, the conjugated
amplitudes are `(1/3)·(e^{iφ})^i`, `φ = baseAngle`; the geometric sum and `normSq_geom`
give `bornPair = (1/27)(3 + 4cos φ + 2cos 2φ)`. -/
lemma bornPair_value (x y : Bool) (k l : ZMod 3) :
    bornPair x y k l
      = (1/27) * (3 + 4 * Real.cos (baseAngle x y k l)
          + 2 * Real.cos (2 * baseAngle x y k l)) := by
  have hsqrt : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hconj : ∀ i : Fin 3, (starRingEnd ℂ) ((outcome x y k l) (i,i))
      = (1/3 : ℂ) * (Complex.exp ((baseAngle x y k l : ℝ) * Complex.I)) ^ (i.val) := by
    intro i
    show (starRingEnd ℂ) (aVec x k i * bVec y l i) = _
    rw [map_mul]
    show (starRingEnd ℂ) ((Real.sqrt 3 : ℂ)⁻¹ * Complex.exp ((aAngle x k i : ℝ) * Complex.I))
        * (starRingEnd ℂ) ((Real.sqrt 3 : ℂ)⁻¹ * Complex.exp ((bAngle y l i : ℝ) * Complex.I)) = _
    rw [map_mul, map_mul]
    have hs : (starRingEnd ℂ) ((Real.sqrt 3 : ℂ)⁻¹) = ((Real.sqrt 3 : ℂ))⁻¹ := by
      rw [map_inv₀, Complex.conj_ofReal]
    have hea : (starRingEnd ℂ) (Complex.exp ((aAngle x k i : ℝ) * Complex.I))
        = Complex.exp ((-(aAngle x k i) : ℝ) * Complex.I) := by
      rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_I]
    have heb : (starRingEnd ℂ) (Complex.exp ((bAngle y l i : ℝ) * Complex.I))
        = Complex.exp ((-(bAngle y l i) : ℝ) * Complex.I) := by
      rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_I]
    rw [hs, hea, heb]
    rw [show ((Real.sqrt 3 : ℂ))⁻¹ * Complex.exp ((-(aAngle x k i) : ℝ) * Complex.I)
          * (((Real.sqrt 3 : ℂ))⁻¹ * Complex.exp ((-(bAngle y l i) : ℝ) * Complex.I))
        = (((Real.sqrt 3 : ℂ))⁻¹ * ((Real.sqrt 3 : ℂ))⁻¹)
          * (Complex.exp ((-(aAngle x k i) : ℝ) * Complex.I)
              * Complex.exp ((-(bAngle y l i) : ℝ) * Complex.I)) by ring]
    rw [← Complex.exp_add]
    have hinv : ((Real.sqrt 3 : ℂ))⁻¹ * ((Real.sqrt 3 : ℂ))⁻¹ = (1/3 : ℂ) := by
      rw [← mul_inv]
      rw [show (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = ((Real.sqrt 3 * Real.sqrt 3 : ℝ) : ℂ) by
        push_cast; ring]
      rw [show (Real.sqrt 3 * Real.sqrt 3 : ℝ) = 3 by nlinarith [hsqrt]]
      norm_num
    rw [hinv]
    congr 1
    have hexp : (-(aAngle x k i) : ℝ) * Complex.I + (-(bAngle y l i) : ℝ) * Complex.I
        = ((i.val : ℂ)) * ((baseAngle x y k l : ℝ) * Complex.I) := by
      have hreal : (-(aAngle x k i) : ℝ) + (-(bAngle y l i) : ℝ)
          = (i.val : ℝ) * baseAngle x y k l := by
        simp only [aAngle, bAngle, baseAngle, deltaOff]; ring
      rw [← add_mul, ← Complex.ofReal_add, hreal]; push_cast; ring
    rw [hexp, Complex.exp_nat_mul]
  rw [bornPair, inner_outcome_collapse]
  rw [Finset.sum_congr rfl (fun i _ => hconj i)]
  rw [← Finset.mul_sum]
  rw [show (∑ i : Fin 3, (Complex.exp ((baseAngle x y k l : ℝ) * Complex.I)) ^ (i.val))
        = 1 + Complex.exp ((baseAngle x y k l : ℝ) * Complex.I)
            + (Complex.exp ((baseAngle x y k l : ℝ) * Complex.I))^2 by
      rw [Fin.sum_univ_three]; simp]
  set w := Complex.exp ((baseAngle x y k l : ℝ) * Complex.I) with hw
  rw [show ((Real.sqrt 3 : ℂ))⁻¹ * ((1/3 : ℂ) * (1 + w + w^2))
        = ((Real.sqrt 3 : ℂ)⁻¹ * (1/3)) * (1 + w + w^2) by ring]
  rw [norm_mul, mul_pow]
  rw [show ‖(1 : ℂ) + w + w^2‖ ^ 2 = Complex.normSq (1 + w + w^2) by rw [Complex.sq_norm]]
  rw [hw, normSq_geom]
  rw [show ‖(Real.sqrt 3 : ℂ)⁻¹ * (1/3 : ℂ)‖ ^ 2 = (1/27 : ℝ) by
      rw [norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [show ‖(1/3 : ℂ)‖ = (1/3 : ℝ) by
        rw [show (1/3 : ℂ) = ((1/3 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs]; norm_num]
      rw [inv_pow, hsqrt]; norm_num]

/-- **The joint Born probability depends only on the outcome difference `k − l`** (mod 3):
the geometric-sum phase is periodic in the integer difference. This is the genuine
"outcome-difference" structure of the CGLMP measurement. -/
lemma bornPair_periodic (x y : Bool) (k l : ZMod 3) :
    bornPair x y k l = bornPair x y (k - l) 0 := by
  rw [bornPair_value, bornPair_value]
  have hdvd : ∀ a b : ZMod 3, (3 : ℤ) ∣ ((a.val : ℤ) - (b.val : ℤ) - ((a - b).val : ℤ)) := by
    decide
  obtain ⟨m, hm⟩ := hdvd k l
  have hmR : ((k.val : ℝ)) - (l.val : ℝ) - ((k - l).val : ℝ) = 3 * (m : ℝ) := by
    exact_mod_cast hm
  have h0 : ((0 : ZMod 3).val : ℝ) = 0 := by simp
  have hbase : baseAngle x y k l = baseAngle x y (k - l) 0 + ((-m : ℤ) : ℝ) * (2 * Real.pi) := by
    simp only [baseAngle, h0]
    push_cast
    linear_combination (-(2 * Real.pi / 3)) * hmR
  rw [hbase, Real.cos_add_int_mul_two_pi]
  rw [show 2 * (baseAngle x y (k - l) 0 + ((-m : ℤ) : ℝ) * (2 * Real.pi))
        = 2 * baseAngle x y (k - l) 0 + ((2 * -m : ℤ) : ℝ) * (2 * Real.pi) by push_cast; ring]
  rw [Real.cos_add_int_mul_two_pi]

/-! ### The CGLMP Born table `pQM` -/

/-- **The genuine CGLMP outcome-difference Born table for `Ψ_3`:**
`pQM x y c = P(A_x − B_y = c)`, the sum over outcome pairs `(k, l)` with `k − l = c` of
the joint Born probabilities `bornPair x y k l`. -/
noncomputable def pQM (x y : Bool) (c : ZMod 3) : ℝ :=
  ∑ l : ZMod 3, bornPair x y (c + l) l

/-- The outcome-difference marginal collapses (via periodicity) to three copies of a
single representative Born probability. -/
lemma pQM_eq (x y : Bool) (c : ZMod 3) : pQM x y c = 3 * bornPair x y c 0 := by
  unfold pQM
  have hterm : ∀ l : ZMod 3, bornPair x y (c + l) l = bornPair x y c 0 := by
    intro l; rw [bornPair_periodic]; congr 1; ring
  rw [Finset.sum_congr rfl (fun l _ => hterm l), Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul]
  norm_num

/-- `pQM x y (k − l) = 3 · bornPair x y k l` for any representative pair. -/
lemma pQM_eq_pair (x y : Bool) (k l : ZMod 3) :
    pQM x y (k - l) = 3 * bornPair x y k l := by
  rw [pQM_eq, bornPair_periodic x y k l]

/-- Evaluation helper: `pQM x y (k − l)` from a computed base angle and its cosines. -/
lemma pQM_eval (x y : Bool) (k l : ZMod 3) (θ cθ c2θ : ℝ)
    (hθ : baseAngle x y k l = θ) (h1 : Real.cos θ = cθ) (h2 : Real.cos (2 * θ) = c2θ) :
    pQM x y (k - l) = 3 * ((1/27) * (3 + 4 * cθ + 2 * c2θ)) := by
  rw [pQM_eq_pair, bornPair_value, hθ, h1, h2]

/-! ### The eight CGLMP-relevant Born values

Four `positive` entries `(4 + 2√3)/9` (base angle `± π/6`), four `negative` entries `1/9`
(base angle `± π/2`), evaluated at the small representatives `k − l ∈ {-1, 0, 1}`. -/

lemma pQM_ff_0 : pQM false false 0 = (4 + 2 * Real.sqrt 3) / 9 := by
  have h := pQM_eval false false 0 0 (-(Real.pi/6)) (Real.sqrt 3/2) (1/2)
    (by simp only [baseAngle, deltaOff, alphaOff, betaOff, ZMod.val_zero]; norm_num; ring)
    (by rw [Real.cos_neg]; exact Real.cos_pi_div_six)
    (by rw [show 2 * (-(Real.pi/6)) = -(Real.pi/3) by ring, Real.cos_neg]
        exact Real.cos_pi_div_three)
  simp only [sub_zero] at h; rw [h]; ring

lemma pQM_ff_2 : pQM false false 2 = 1 / 9 := by
  have h := pQM_eval false false 0 1 (Real.pi/2) 0 (-1)
    (by simp only [baseAngle, deltaOff, alphaOff, betaOff]
        rw [show (ZMod.val (0:ZMod 3)) = 0 from by decide,
            show (ZMod.val (1:ZMod 3)) = 1 from by decide]
        push_cast; ring)
    Real.cos_pi_div_two
    (by rw [show 2 * (Real.pi/2) = Real.pi by ring]; exact Real.cos_pi)
  rw [show (2 : ZMod 3) = 0 - 1 from by decide, h]; ring

lemma pQM_tt_0 : pQM true true 0 = (4 + 2 * Real.sqrt 3) / 9 := by
  have h := pQM_eval true true 0 0 (-(Real.pi/6)) (Real.sqrt 3/2) (1/2)
    (by simp only [baseAngle, deltaOff, alphaOff, betaOff, ZMod.val_zero]; norm_num; ring)
    (by rw [Real.cos_neg]; exact Real.cos_pi_div_six)
    (by rw [show 2 * (-(Real.pi/6)) = -(Real.pi/3) by ring, Real.cos_neg]
        exact Real.cos_pi_div_three)
  simp only [sub_zero] at h; rw [h]; ring

lemma pQM_tt_2 : pQM true true 2 = 1 / 9 := by
  have h := pQM_eval true true 0 1 (Real.pi/2) 0 (-1)
    (by simp only [baseAngle, deltaOff, alphaOff, betaOff]
        rw [show (ZMod.val (0:ZMod 3)) = 0 from by decide,
            show (ZMod.val (1:ZMod 3)) = 1 from by decide]
        push_cast; ring)
    Real.cos_pi_div_two
    (by rw [show 2 * (Real.pi/2) = Real.pi by ring]; exact Real.cos_pi)
  rw [show (2 : ZMod 3) = 0 - 1 from by decide, h]; ring

lemma pQM_tf_2 : pQM true false 2 = (4 + 2 * Real.sqrt 3) / 9 := by
  have h := pQM_eval true false 0 1 (Real.pi/6) (Real.sqrt 3/2) (1/2)
    (by simp only [baseAngle, deltaOff, alphaOff, betaOff]
        rw [show (ZMod.val (0:ZMod 3)) = 0 from by decide,
            show (ZMod.val (1:ZMod 3)) = 1 from by decide]
        push_cast; ring)
    Real.cos_pi_div_six
    (by rw [show 2 * (Real.pi/6) = Real.pi/3 by ring]; exact Real.cos_pi_div_three)
  rw [show (2 : ZMod 3) = 0 - 1 from by decide, h]; ring

lemma pQM_tf_0 : pQM true false 0 = 1 / 9 := by
  have h := pQM_eval true false 0 0 (-(Real.pi/2)) 0 (-1)
    (by simp only [baseAngle, deltaOff, alphaOff, betaOff, ZMod.val_zero]; norm_num; ring)
    (by rw [Real.cos_neg]; exact Real.cos_pi_div_two)
    (by rw [show 2 * (-(Real.pi/2)) = -Real.pi by ring, Real.cos_neg]; exact Real.cos_pi)
  simp only [sub_zero] at h; rw [h]; ring

lemma pQM_ft_0 : pQM false true 0 = (4 + 2 * Real.sqrt 3) / 9 := by
  have h := pQM_eval false true 0 0 (Real.pi/6) (Real.sqrt 3/2) (1/2)
    (by simp only [baseAngle, deltaOff, alphaOff, betaOff, ZMod.val_zero]; norm_num; ring)
    Real.cos_pi_div_six
    (by rw [show 2 * (Real.pi/6) = Real.pi/3 by ring]; exact Real.cos_pi_div_three)
  simp only [sub_zero] at h; rw [h]; ring

lemma pQM_ft_1 : pQM false true 1 = 1 / 9 := by
  have h := pQM_eval false true 1 0 (-(Real.pi/2)) 0 (-1)
    (by simp only [baseAngle, deltaOff, alphaOff, betaOff]
        rw [show (ZMod.val (0:ZMod 3)) = 0 from by decide,
            show (ZMod.val (1:ZMod 3)) = 1 from by decide]
        push_cast; ring)
    (by rw [Real.cos_neg]; exact Real.cos_pi_div_two)
    (by rw [show 2 * (-(Real.pi/2)) = -Real.pi by ring, Real.cos_neg]; exact Real.cos_pi)
  simp only [sub_zero] at h; rw [h]; ring

/-! ### The CGLMP value and the violation -/

/-- The CGLMP bracket at `k = 0` on the `Ψ_3` Born table: `4·(4+2√3)/9 − 4·(1/9)`. -/
lemma bracket_val :
    cglmpBracket 3 pQM 0 = 4 * ((4 + 2 * Real.sqrt 3) / 9) - 4 * (1 / 9 : ℝ) := by
  simp only [cglmpBracket, Nat.cast_zero]
  rw [show (-(0 + 1) : ZMod 3) = 2 from by decide, show (-0 - 1 : ZMod 3) = 2 from by decide,
    show (0 + 1 : ZMod 3) = 1 from by decide, show (-0 : ZMod 3) = 0 from by decide]
  rw [pQM_ff_0, pQM_tf_2, pQM_tt_0, pQM_ft_0, pQM_ff_2, pQM_tf_0, pQM_tt_2, pQM_ft_1]
  ring

/-- **The maximally-entangled qutrit CGLMP value.** `I_3 = (12 + 8√3)/9 ≈ 2.8729`,
computed from `Ψ_3`'s actual Born probabilities under the CGLMP phase-basis
measurements. -/
theorem cglmp_maxEntangled_qutrit_eq : cglmp 3 pQM = (12 + 8 * Real.sqrt 3) / 9 := by
  rw [cglmp, show (3 / 2 : ℕ) = 1 from rfl, Finset.sum_range_one, bracket_val]
  push_cast; ring

/-- **The qutrit CGLMP violation (QM side).** `Ψ_3` violates the CGLMP inequality: its
CGLMP value `(12 + 8√3)/9 ≈ 2.8729` exceeds the local-hidden-variable bound `2`. Genuinely
`d = 3`-intrinsic (the `√3` is irrational; no rational / half-integer setting choice
violates). -/
theorem cglmp_maxEntangled_qutrit_gt_two : cglmp 3 pQM > 2 := by
  rw [cglmp_maxEntangled_qutrit_eq]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  rw [gt_iff_lt, lt_div_iff₀ (by norm_num : (0:ℝ) < 9)]
  nlinarith [h3, hnn]

/-- **The `d = 3`-intrinsic no-go (LF6-D, CGLMP routing).** No local-hidden-variable
model `(Λ, μ, A, B)` reproduces `Ψ_3`'s actual CGLMP outcome-difference Born statistics
`pQM`: such a model would have CGLMP value `cglmpLHV = cglmp 3 pQM = (12 + 8√3)/9 > 2`,
contradicting the LHV bound `cglmp_lhv_bound_three` (`I_3 ≤ 2`). This is the genuinely
`d = 3` Bell force for the maximally-entangled qutrit, superseding the `2 × 2` `Φ⁺` CHSH
sector of `no_product_partition_realises_maxEntangled`. -/
theorem no_lhv_realises_maxEntangled_cglmp {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure Λ) [IsProbabilityMeasure μ] (A B : Bool → Λ → ZMod 3)
    (hA : ∀ x, Measurable (A x)) (hB : ∀ y, Measurable (B y))
    (hRep : lhvTable μ A B = pQM) : False := by
  have hle := cglmp_lhv_bound_three μ A B hA hB
  rw [cglmpLHV, hRep] at hle
  have hgt := cglmp_maxEntangled_qutrit_gt_two
  linarith

end CGLMPQutrit
end LF6
end CSD
