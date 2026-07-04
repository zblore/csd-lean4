import CsdLean4.Mathlib.Probability.CGLMP
import CsdLean4.LF6.MaxEntangledDeisolationFlow
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# LF6-D (QM side, general `d`): `Ψ_d` violates the CGLMP inequality for every `d ≥ 2`

**Category:** 6-Local (the general-`d`-intrinsic Bell violation for `Ψ_d`, the QM-side
payoff of the CGLMP infrastructure `Mathlib/Probability/CGLMP.lean`, extending the
`d = 3` qutrit violation `CGLMPQutrit.cglmp_maxEntangled_qutrit_gt_two` to ALL `d ≥ 2`).

## What is proved (general `d`, no dimension restriction)

Under the standard CGLMP phase-basis measurements on `Ψ_d = maxEntangled d` (Alice offsets
`α₁ = 0, α₂ = 1/2`; Bob offsets `β₁ = -1/4, β₂ = 1/4`), the joint outcome-difference Born
probabilities `pQM x y c = P(A_x − B_y = c)` are **computed from the Hilbert space** for
arbitrary `d`:

- `pQM_closed` : `pQM x y c = 1 / (2 d² sin²(π(c.val + δ_xy)/d))`, the standard
  maximally-entangled CGLMP closed form, DERIVED via the `d`-th-roots-of-unity Dirichlet /
  Fejér kernel `dirichlet_kernel` (`‖∑_{j<d} e^{ijφ}‖² = sin²(dφ/2)/sin²(φ/2)`), the
  quarter-integer numerator `sin²(π(m+δ)) = 1/2` (`sin_sq_pi_delta`), and the diagonal
  contraction with `Ψ_d` (`inner_outcome_collapse`, `hconj_term`). No value asserted.

- `cglmpBracket_closed` : the CGLMP bracket at index `k` in closed form
  `(2/d²)(csc²(π(k+1/4)/d) − csc²(π(k+3/4)/d))` (`bracketClosed`); hence
  `cglmp_maxEntangled_qudit_closed` gives the full general-`d` CGLMP value as
  `∑_{k<⌊d/2⌋} (1 − 2k/(d−1)) · bracketClosed d k`.

- `cglmp_maxEntangled_qudit_gt_two (hd : 2 ≤ d)` : **the general-`d` violation**
  `cglmp d pQM > 2`. This is a genuine analytic inequality on the `d`-dependent trig sum,
  proved for EVERY `d ≥ 2`: every bracket term is nonnegative (`bracketClosed_nonneg`,
  via `sin` monotonicity on `(0, π/2]`) and every coefficient is nonnegative
  (`coeff_nonneg`), so the sum dominates its `k = 0` term (`Finset.single_le_sum`), and the
  `k = 0` term alone exceeds `2` (`bracket_zero_gt_two`) via `sin x ≤ x` on the `π/(4d)` arm
  and Jordan's inequality `sin x ≥ 2x/π` (`jordan_sin`, from `strictConcaveOn_sin_Icc`) on
  the `3π/(4d)` arm, giving the uniform bound `bracketClosed d 0 ≥ 32/π² − 8/9 > 2`
  (`π < 3.15`). No monotonicity in `d` needed; the single `k = 0` term suffices for all `d`.

- `no_lhv_realises_maxEntangled_cglmp_d (hd : 2 ≤ d)` : **the general-`d` Bell force.** No
  local-hidden-variable model reproducing `Ψ_d`'s CGLMP statistics `pQM` exists: it would
  have `cglmpLHV = cglmp d pQM > 2`, contradicting `cglmp_lhv_bound` (`I_d ≤ 2`). Together
  with the general-`d` LHV bound this closes the statistical non-locality axis at FULL
  dimensional generality (matching the `GHZ_n` deterministic axis).

## Honest scope

- Genuine computation from `Ψ_d`'s actual Born probabilities: `bornPair` is a squared inner
  product with `maxEntangled d`, the outcome vectors are unit CGLMP phase-basis vectors, and
  `pQM` is the genuine outcome-difference marginal. The closed form is derived, not asserted.
- The `> 2` bound is a REAL analytic proof valid for every `d ≥ 2` (not `decide` over a
  finite dimension range, not axiomatised). It uses only the `k = 0` bracket term plus
  nonnegativity of the tail; the CGLMP value increases towards `≈ 2.9696` as `d → ∞`, but
  only the uniform lower bound `32/π² − 8/9 ≈ 2.35` is needed.
- Foundational-triple-only (no `busch_effect_gleason`; the roots-of-unity sums, the trig
  inequalities, and the finite LHV optimisation are all Gleason-free).

Reference: Collins, Gisin, Linden, Massar, Popescu, *Phys. Rev. Lett.* **88**, 040404
(2002). `specs/lf6-plan.md` (LF6-D).
-/

open Real Complex
open CSD.LF6

namespace CSD
namespace LF6
namespace CGLMPQudit

lemma norm_exp_sub_one_sq (θ : ℝ) :
    ‖Complex.exp ((θ:ℂ)*Complex.I) - 1‖^2 = 4 * Real.sin (θ/2)^2 := by
  rw [Complex.sq_norm, Complex.exp_mul_I, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
    Complex.cos_ofReal_im, Complex.sin_ofReal_im]
  have hc2 : Real.cos θ = 1 - 2 * Real.sin (θ/2)^2 := by
    have h1 := Real.cos_two_mul (θ/2); have h2 := Real.sin_sq_add_cos_sq (θ/2)
    have h3 : (2:ℝ)*(θ/2) = θ := by ring
    rw [h3] at h1; nlinarith [h1, h2]
  nlinarith [hc2, Real.sin_sq_add_cos_sq θ]

lemma dirichlet_kernel (φ : ℝ) (hs : Real.sin (φ/2) ≠ 0) (n : ℕ) :
    ‖∑ j ∈ Finset.range n, Complex.exp ((φ:ℂ)*Complex.I)^j‖^2
      = Real.sin ((n:ℝ)*φ/2)^2 / Real.sin (φ/2)^2 := by
  have hw1 : Complex.exp ((φ:ℂ)*Complex.I) ≠ 1 := by
    intro hcon; apply hs
    have hre : Real.cos φ = 1 := by
      have := congrArg Complex.re hcon
      rwa [Complex.exp_ofReal_mul_I_re, Complex.one_re] at this
    have hc2 : Real.cos φ = 1 - 2 * Real.sin (φ/2)^2 := by
      have h1 := Real.cos_two_mul (φ/2); have h2 := Real.sin_sq_add_cos_sq (φ/2)
      have h3 : (2:ℝ)*(φ/2) = φ := by ring
      rw [h3] at h1; nlinarith [h1, h2]
    nlinarith [hre, hc2]
  have hnum : ‖Complex.exp ((φ:ℂ)*Complex.I)^n - 1‖^2 = 4 * Real.sin ((n:ℝ)*φ/2)^2 := by
    have hpow : Complex.exp ((φ:ℂ)*Complex.I)^n = Complex.exp ((((n:ℝ)*φ : ℝ):ℂ)*Complex.I) := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    rw [hpow, norm_exp_sub_one_sq]
  have hden : ‖Complex.exp ((φ:ℂ)*Complex.I) - 1‖^2 = 4 * Real.sin (φ/2)^2 := norm_exp_sub_one_sq φ
  rw [geom_sum_eq hw1 n, norm_div, div_pow, hnum, hden]
  field_simp

noncomputable def alphaOff (x : Bool) : ℝ := if x then 1/2 else 0
noncomputable def betaOff (y : Bool) : ℝ := if y then 1/4 else -1/4
noncomputable def deltaOff (x y : Bool) : ℝ := alphaOff x - betaOff y

lemma sin_sq_pi_delta (x y : Bool) (m : ℤ) :
    Real.sin (π * ((m:ℝ) + deltaOff x y))^2 = 1/2 := by
  have hsin0 : Real.sin (π * (m:ℝ)) = 0 := by rw [mul_comm]; exact Real.sin_int_mul_pi m
  have hcos1 : Real.cos (π*(m:ℝ))^2 = 1 := by
    have := Real.sin_sq_add_cos_sq (π*(m:ℝ)); rw [hsin0] at this; nlinarith [this]
  have key : Real.sin (π * ((m:ℝ) + deltaOff x y))^2
      = Real.cos (π*(m:ℝ))^2 * Real.sin (π * deltaOff x y)^2 := by
    rw [mul_add, Real.sin_add, hsin0]; ring
  rw [key, hcos1, one_mul]
  cases x <;> cases y <;> simp only [deltaOff, alphaOff, betaOff, Bool.false_eq_true, if_true, if_false]
  · rw [show π * ((0:ℝ) - -1/4) = π/4 by ring, Real.sin_pi_div_four, div_pow,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  · rw [show π * ((0:ℝ) - 1/4) = -(π/4) by ring, Real.sin_neg, neg_pow, Real.sin_pi_div_four,
      div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  · rw [show π * ((1:ℝ)/2 - -1/4) = π - (π/4) by ring, Real.sin_pi_sub, Real.sin_pi_div_four,
      div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  · rw [show π * ((1:ℝ)/2 - 1/4) = π/4 by ring, Real.sin_pi_div_four, div_pow,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num

lemma deltaOff_not_int (x y : Bool) (N : ℤ) : deltaOff x y ≠ (N:ℝ) := by
  cases x <;> cases y <;> simp only [deltaOff, alphaOff, betaOff, Bool.false_eq_true, if_true, if_false]
  · intro hN; have hi : (4*N:ℤ) = 1 := by
      have : ((4*N:ℤ):ℝ)=1 := by push_cast; linarith [hN]
      exact_mod_cast this
    omega
  · intro hN; have hi : (4*N:ℤ) = -1 := by
      have : ((4*N:ℤ):ℝ)=(-1) := by push_cast; linarith [hN]
      exact_mod_cast this
    omega
  · intro hN; have hi : (4*N:ℤ) = 3 := by
      have : ((4*N:ℤ):ℝ)=3 := by push_cast; linarith [hN]
      exact_mod_cast this
    omega
  · intro hN; have hi : (4*N:ℤ) = 1 := by
      have : ((4*N:ℤ):ℝ)=1 := by push_cast; linarith [hN]
      exact_mod_cast this
    omega

variable (d : ℕ)

noncomputable def aAngle (x : Bool) (k : ZMod d) (j : Fin d) : ℝ :=
  2 * Real.pi * (j.val : ℝ) * ((k.val : ℝ) + alphaOff x) / d
noncomputable def bAngle (y : Bool) (l : ZMod d) (j : Fin d) : ℝ :=
  - (2 * Real.pi * (j.val : ℝ) * ((l.val : ℝ) + betaOff y) / d)
noncomputable def aVec (x : Bool) (k : ZMod d) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 (fun j => (Real.sqrt d : ℂ)⁻¹ * Complex.exp ((aAngle d x k j : ℝ) * Complex.I))
noncomputable def bVec (y : Bool) (l : ZMod d) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 (fun j => (Real.sqrt d : ℂ)⁻¹ * Complex.exp ((bAngle d y l j : ℝ) * Complex.I))
noncomputable def outcome (x y : Bool) (k l : ZMod d) : EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 (fun p => aVec d x k p.1 * bVec d y l p.2)
noncomputable def bornPair (x y : Bool) (k l : ZMod d) : ℝ :=
  ‖inner ℂ (outcome d x y k l) (maxEntangled d)‖ ^ 2
noncomputable def baseAngle (x y : Bool) (k l : ZMod d) : ℝ :=
  - (2 * Real.pi * ((k.val : ℝ) - (l.val : ℝ) + deltaOff x y) / d)

variable [NeZero d]

lemma sin_sq_shift (b : ℝ) (t : ℤ) :
    Real.sin (π*(b + d*t)/d)^2 = Real.sin (π*b/d)^2 := by
  have hd : (d:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  rw [show π*(b + d*t)/d = π*b/d + (t:ℝ)*π by field_simp, Real.sin_add,
    show Real.sin ((t:ℝ)*π) = 0 from Real.sin_int_mul_pi t]
  have hc1 : Real.cos ((t:ℝ)*π)^2 = 1 := by
    have := Real.sin_sq_add_cos_sq ((t:ℝ)*π); rw [Real.sin_int_mul_pi t] at this; nlinarith [this]
  rw [mul_zero, add_zero, mul_pow, hc1, mul_one]

lemma sin_denom_ne' (x y : Bool) (m : ℤ) :
    Real.sin (π*((m:ℝ)+deltaOff x y)/d) ≠ 0 := by
  intro h
  rw [Real.sin_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have hd0 : (d:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hpi : (π:ℝ) ≠ 0 := Real.pi_ne_zero
  rw [eq_div_iff hd0] at hn
  have h2 : π*((m:ℝ)+deltaOff x y) = π*((n:ℝ)*d) := by rw [← hn]; ring
  have hX : (m:ℝ)+deltaOff x y = (n:ℝ)*d := mul_left_cancel₀ hpi h2
  have hX' : deltaOff x y = (n:ℝ)*d - (m:ℝ) := by linarith [hX]
  refine deltaOff_not_int x y (n*(d:ℤ) - m) ?_
  rw [hX']; push_cast; ring

omit [NeZero d] in
lemma inner_outcome_collapse (x y : Bool) (k l : ZMod d) :
    inner ℂ (outcome d x y k l) (maxEntangled d)
      = ((Real.sqrt d : ℂ))⁻¹ * ∑ i : Fin d, (starRingEnd ℂ) ((outcome d x y k l) (i,i)) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hterm : ∀ j : Fin d, (maxEntangled d).ofLp (i, j) * (star (outcome d x y k l).ofLp (i,j))
      = if i = j then ((Real.sqrt d : ℂ))⁻¹ * (starRingEnd ℂ) ((outcome d x y k l) (i,i)) else 0 := by
    intro j
    rw [show (maxEntangled d).ofLp (i,j) = (maxEntangled d) (i,j) from rfl, maxEntangled_apply]
    by_cases h : i = j
    · subst h; simp [Pi.star_apply]
    · rw [if_neg (by simpa using h), if_neg h, zero_mul]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite_eq Finset.univ i]
  simp

omit [NeZero d] in
lemma hconj_term (x y : Bool) (k l : ZMod d) (i : Fin d) :
    (starRingEnd ℂ) ((outcome d x y k l) (i,i))
      = (1/d : ℂ) * (Complex.exp ((baseAngle d x y k l : ℝ) * Complex.I)) ^ (i.val) := by
  have hsqrt : (Real.sqrt d : ℝ) ^ 2 = d := Real.sq_sqrt (by positivity)
  show (starRingEnd ℂ) (aVec d x k i * bVec d y l i) = _
  rw [map_mul]
  show (starRingEnd ℂ) ((Real.sqrt d : ℂ)⁻¹ * Complex.exp ((aAngle d x k i : ℝ) * Complex.I))
      * (starRingEnd ℂ) ((Real.sqrt d : ℂ)⁻¹ * Complex.exp ((bAngle d y l i : ℝ) * Complex.I)) = _
  rw [map_mul, map_mul]
  have hs : (starRingEnd ℂ) ((Real.sqrt d : ℂ)⁻¹) = ((Real.sqrt d : ℂ))⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal]
  have hea : (starRingEnd ℂ) (Complex.exp ((aAngle d x k i : ℝ) * Complex.I))
      = Complex.exp ((-(aAngle d x k i) : ℝ) * Complex.I) := by
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_I]
  have heb : (starRingEnd ℂ) (Complex.exp ((bAngle d y l i : ℝ) * Complex.I))
      = Complex.exp ((-(bAngle d y l i) : ℝ) * Complex.I) := by
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_I]
  rw [hs, hea, heb]
  rw [show ((Real.sqrt d : ℂ))⁻¹ * Complex.exp ((-(aAngle d x k i) : ℝ) * Complex.I)
        * (((Real.sqrt d : ℂ))⁻¹ * Complex.exp ((-(bAngle d y l i) : ℝ) * Complex.I))
      = (((Real.sqrt d : ℂ))⁻¹ * ((Real.sqrt d : ℂ))⁻¹)
        * (Complex.exp ((-(aAngle d x k i) : ℝ) * Complex.I)
            * Complex.exp ((-(bAngle d y l i) : ℝ) * Complex.I)) by ring]
  rw [← Complex.exp_add]
  have hinv : ((Real.sqrt d : ℂ))⁻¹ * ((Real.sqrt d : ℂ))⁻¹ = (1/d : ℂ) := by
    rw [← mul_inv]
    rw [show (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) = ((Real.sqrt d * Real.sqrt d : ℝ) : ℂ) by
      push_cast; ring]
    rw [show (Real.sqrt d * Real.sqrt d : ℝ) = d by nlinarith [hsqrt]]
    norm_num
  rw [hinv]
  congr 1
  have hexp : (-(aAngle d x k i) : ℝ) * Complex.I + (-(bAngle d y l i) : ℝ) * Complex.I
      = ((i.val : ℂ)) * ((baseAngle d x y k l : ℝ) * Complex.I) := by
    have hreal : (-(aAngle d x k i) : ℝ) + (-(bAngle d y l i) : ℝ)
        = (i.val : ℝ) * baseAngle d x y k l := by
      simp only [aAngle, bAngle, baseAngle, deltaOff]; field_simp; ring
    rw [← add_mul, ← Complex.ofReal_add, hreal]; push_cast; ring
  rw [hexp, Complex.exp_nat_mul]

lemma bornPair_closed (x y : Bool) (k l : ZMod d) :
    bornPair d x y k l
      = 1 / (2 * (d:ℝ)^3 * Real.sin (π * ((k.val:ℝ) - (l.val:ℝ) + deltaOff x y) / d)^2) := by
  have hd0 : (d:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hdpos : (0:ℝ) < d := by positivity
  set n : ℤ := (k.val:ℤ) - (l.val:ℤ) with hn
  set M : ℝ := (k.val:ℝ) - (l.val:ℝ) + deltaOff x y with hM
  have hMcast : M = (n:ℝ) + deltaOff x y := by rw [hM, hn]; push_cast; ring
  have hb2 : baseAngle d x y k l / 2 = -(π*M/d) := by
    simp only [baseAngle, hM]; field_simp
  have hdb2 : (d:ℝ)*baseAngle d x y k l/2 = -(π*M) := by
    simp only [baseAngle, hM]; field_simp
  have hden_ne : Real.sin (π*M/d) ≠ 0 := by
    rw [hMcast]; exact sin_denom_ne' d x y n
  have hbase_ne : Real.sin (baseAngle d x y k l/2) ≠ 0 := by
    rw [hb2, Real.sin_neg]; exact neg_ne_zero.mpr hden_ne
  have hnum : Real.sin ((d:ℝ)*baseAngle d x y k l/2)^2 = 1/2 := by
    rw [hdb2, Real.sin_neg, neg_sq, hMcast, sin_sq_pi_delta]
  have hden : Real.sin (baseAngle d x y k l/2)^2 = Real.sin (π*M/d)^2 := by
    rw [hb2, Real.sin_neg, neg_sq]
  rw [bornPair, inner_outcome_collapse, Finset.sum_congr rfl (fun i _ => hconj_term d x y k l i),
    ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun j => (Complex.exp ((baseAngle d x y k l:ℝ)*Complex.I))^j) d]
  rw [norm_mul, mul_pow, norm_mul, mul_pow]
  have hnS : ‖∑ j ∈ Finset.range d, Complex.exp ((baseAngle d x y k l:ℝ)*Complex.I)^j‖^2
      = (1/2) / Real.sin (π*M/d)^2 := by
    rw [dirichlet_kernel (baseAngle d x y k l) hbase_ne d, hnum, hden]
  rw [hnS]
  have hn1 : ‖((Real.sqrt d:ℂ))⁻¹‖^2 = (d:ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      inv_pow, Real.sq_sqrt (le_of_lt hdpos)]
  have hn2 : ‖(1/(d:ℂ))‖^2 = ((d:ℝ)^2)⁻¹ := by
    rw [show (1/(d:ℂ)) = ((d:ℝ):ℂ)⁻¹ by push_cast; ring, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (le_of_lt hdpos), inv_pow]
  rw [hn1, hn2]
  field_simp

/-! ### Jordan + reduction infra -/

lemma jordan_sin (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ π/2) : 2*x/π ≤ Real.sin x := by
  have hpi : 0 < π := Real.pi_pos
  have hconc := (strictConcaveOn_sin_Icc).concaveOn
  set t : ℝ := 2*x/π with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hpi]; linarith
  have hmem0 : (0:ℝ) ∈ Set.Icc 0 π := ⟨le_refl _, le_of_lt hpi⟩
  have hmemp : (π/2:ℝ) ∈ Set.Icc 0 π := ⟨by positivity, by linarith⟩
  have hcomb := hconc.2 hmem0 hmemp (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
  have harg : (1 - t) • (0:ℝ) + t • (π/2) = x := by
    simp only [smul_eq_mul, mul_zero, zero_add]; rw [ht]; field_simp
  rw [harg] at hcomb
  simp only [smul_eq_mul, Real.sin_zero, mul_zero, zero_add,
    show Real.sin (π/2) = 1 from Real.sin_pi_div_two, mul_one] at hcomb
  exact hcomb

omit [NeZero d] in
lemma sin_sq_neg (r : ℝ) : Real.sin (π*(-r)/d)^2 = Real.sin (π*r/d)^2 := by
  rw [show π*(-r)/d = -(π*r/d) by ring, Real.sin_neg]; ring

lemma val_congr (c : ZMod d) (n : ℤ) (h : (n : ZMod d) = c) : ∃ t : ℤ, (c.val : ℤ) = n + d * t := by
  have hz : (((c.val : ℤ) - n : ℤ) : ZMod d) = 0 := by
    push_cast; rw [ZMod.natCast_val, ZMod.cast_id, h]; ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  obtain ⟨t, ht⟩ := hz
  exact ⟨t, by linarith [ht]⟩

lemma denom_reduce (c : ZMod d) (n : ℤ) (r δ : ℝ) (hc : (n : ZMod d) = c)
    (heq : (n:ℝ) + δ = r ∨ (n:ℝ) + δ = -r) :
    Real.sin (π*((c.val:ℝ)+δ)/d)^2 = Real.sin (π*r/d)^2 := by
  obtain ⟨t, ht⟩ := val_congr d c n hc
  have hvr : (c.val:ℝ) = (n:ℝ) + d*t := by exact_mod_cast ht
  rcases heq with he | he
  · rw [show (c.val:ℝ)+δ = r + d*t by rw [hvr]; linarith [he]]; exact sin_sq_shift d r t
  · rw [show (c.val:ℝ)+δ = -r + d*t by rw [hvr]; linarith [he]]
    rw [sin_sq_shift d (-r) t]; exact sin_sq_neg d r

lemma vals_diff_congr (a b : ZMod d) (n : ℤ) (h : (n : ZMod d) = a - b) :
    ∃ t : ℤ, ((a.val : ℤ) - (b.val : ℤ)) = n + d * t := by
  have hz : ((((a.val:ℤ) - (b.val:ℤ)) - n : ℤ) : ZMod d) = 0 := by
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id]
    rw [h]; ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  obtain ⟨t, ht⟩ := hz
  exact ⟨t, by linarith [ht]⟩

lemma denom_diff_reduce (a b : ZMod d) (n : ℤ) (δ : ℝ) (h : (n : ZMod d) = a - b) :
    Real.sin (π*(((a.val:ℝ)-(b.val:ℝ))+δ)/d)^2 = Real.sin (π*((n:ℝ)+δ)/d)^2 := by
  obtain ⟨t, ht⟩ := vals_diff_congr d a b n h
  have hvr : (a.val:ℝ) - (b.val:ℝ) = (n:ℝ) + d*t := by exact_mod_cast ht
  rw [show ((a.val:ℝ)-(b.val:ℝ))+δ = ((n:ℝ)+δ) + d*t by rw [hvr]; ring]
  exact sin_sq_shift d ((n:ℝ)+δ) t

/-! ### pQM and its closed form -/

noncomputable def pQM (x y : Bool) (c : ZMod d) : ℝ := ∑ l : ZMod d, bornPair d x y (c+l) l

lemma pQM_closed (x y : Bool) (c : ZMod d) :
    pQM d x y c = 1/(2*(d:ℝ)^2*Real.sin (π*((c.val:ℝ)+deltaOff x y)/d)^2) := by
  have hd0 : (d:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hsc : Real.sin (π*((c.val:ℝ)+deltaOff x y)/d) ≠ 0 := by
    have h := sin_denom_ne' d x y (c.val:ℤ)
    rwa [show (((c.val:ℤ)):ℝ) = (c.val:ℝ) by push_cast; ring] at h
  have hterm : ∀ l : ZMod d, bornPair d x y (c+l) l
      = 1/(2*(d:ℝ)^3*Real.sin (π*((c.val:ℝ)+deltaOff x y)/d)^2) := by
    intro l
    rw [bornPair_closed]
    rw [denom_diff_reduce d (c+l) l (c.val:ℤ) (deltaOff x y)
      (by push_cast; simp only [ZMod.natCast_val, ZMod.cast_id]; ring)]
    rw [show (((c.val:ℤ)):ℝ) = (c.val:ℝ) by push_cast; ring]
  rw [pQM, Finset.sum_congr rfl (fun l _ => hterm l), Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul]
  rw [pow_succ]
  field_simp

lemma pQM_reduce (x y : Bool) (c : ZMod d) (n : ℤ) (r : ℝ) (hc : (n : ZMod d) = c)
    (heq : (n:ℝ) + deltaOff x y = r ∨ (n:ℝ) + deltaOff x y = -r) :
    pQM d x y c = 1/(2*(d:ℝ)^2*Real.sin (π*r/d)^2) := by
  rw [pQM_closed, denom_reduce d c n r (deltaOff x y) hc heq]

/-! ### The bracket closed form -/

noncomputable def bracketClosed (k : ℕ) : ℝ :=
  (2/(d:ℝ)^2) * (1/Real.sin (π*((k:ℝ)+1/4)/d)^2 - 1/Real.sin (π*((k:ℝ)+3/4)/d)^2)

lemma cglmpBracket_closed (k : ℕ) :
    ProbabilityTheory.CGLMP.cglmpBracket d (pQM d) k = bracketClosed d k := by
  have e1 : pQM d false false (k:ZMod d) = 1/(2*(d:ℝ)^2*Real.sin (π*((k:ℝ)+1/4)/d)^2) :=
    pQM_reduce d false false _ (k:ℤ) _ (by push_cast; ring)
      (Or.inl (by simp only [deltaOff, alphaOff, betaOff]; push_cast; ring))
  have e2 : pQM d true false (-((k:ZMod d)+1)) = 1/(2*(d:ℝ)^2*Real.sin (π*((k:ℝ)+1/4)/d)^2) :=
    pQM_reduce d true false _ (-(k+1):ℤ) _ (by push_cast; ring)
      (Or.inr (by simp only [deltaOff, alphaOff, betaOff]; push_cast; ring))
  have e3 : pQM d true true (k:ZMod d) = 1/(2*(d:ℝ)^2*Real.sin (π*((k:ℝ)+1/4)/d)^2) :=
    pQM_reduce d true true _ (k:ℤ) _ (by push_cast; ring)
      (Or.inl (by simp only [deltaOff, alphaOff, betaOff]; push_cast; ring))
  have e4 : pQM d false true (-(k:ZMod d)) = 1/(2*(d:ℝ)^2*Real.sin (π*((k:ℝ)+1/4)/d)^2) :=
    pQM_reduce d false true _ (-k:ℤ) _ (by push_cast; ring)
      (Or.inr (by simp only [deltaOff, alphaOff, betaOff]; push_cast; ring))
  have e5 : pQM d false false (-(k:ZMod d)-1) = 1/(2*(d:ℝ)^2*Real.sin (π*((k:ℝ)+3/4)/d)^2) :=
    pQM_reduce d false false _ (-(k+1):ℤ) _ (by push_cast; ring)
      (Or.inr (by simp only [deltaOff, alphaOff, betaOff]; push_cast; ring))
  have e6 : pQM d true false (k:ZMod d) = 1/(2*(d:ℝ)^2*Real.sin (π*((k:ℝ)+3/4)/d)^2) :=
    pQM_reduce d true false _ (k:ℤ) _ (by push_cast; ring)
      (Or.inl (by simp only [deltaOff, alphaOff, betaOff]; push_cast; ring))
  have e7 : pQM d true true (-(k:ZMod d)-1) = 1/(2*(d:ℝ)^2*Real.sin (π*((k:ℝ)+3/4)/d)^2) :=
    pQM_reduce d true true _ (-(k+1):ℤ) _ (by push_cast; ring)
      (Or.inr (by simp only [deltaOff, alphaOff, betaOff]; push_cast; ring))
  have e8 : pQM d false true ((k:ZMod d)+1) = 1/(2*(d:ℝ)^2*Real.sin (π*((k:ℝ)+3/4)/d)^2) :=
    pQM_reduce d false true _ (k+1:ℤ) _ (by push_cast; ring)
      (Or.inl (by simp only [deltaOff, alphaOff, betaOff]; push_cast; ring))
  simp only [ProbabilityTheory.CGLMP.cglmpBracket, e1, e2, e3, e4, e5, e6, e7, e8, bracketClosed]
  ring

/-! ### Nonnegativity of coefficients and bracket terms -/

omit [NeZero d] in
lemma coeff_nonneg (hd : 2 ≤ d) (k : ℕ) (hk : k < d/2) : 0 ≤ 1 - 2*(k:ℝ)/((d:ℝ)-1) := by
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (0:ℝ) < (d:ℝ)-1 := by linarith
  have h2k : (2*k:ℝ) ≤ (d:ℝ)-2 := by
    have h1 : 2*(k+1) ≤ d := by omega
    have h2 : (2*(k+1):ℝ) ≤ (d:ℝ) := by exact_mod_cast h1
    push_cast at h2; linarith
  rw [sub_nonneg, div_le_one hd1]; linarith [h2k]

omit [NeZero d] in
lemma bracketClosed_nonneg (hd : 2 ≤ d) (k : ℕ) (hk : k < d/2) : 0 ≤ bracketClosed d k := by
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0:ℝ) < d := by linarith
  have hpi := Real.pi_pos
  have h2k : (2*k:ℝ) ≤ (d:ℝ)-2 := by
    have h1 : 2*(k+1) ≤ d := by omega
    have h2 : (2*(k+1):ℝ) ≤ (d:ℝ) := by exact_mod_cast h1
    push_cast at h2; linarith
  have haA : (0:ℝ) < π*((k:ℝ)+1/4)/d := by positivity
  have haB : (0:ℝ) < π*((k:ℝ)+3/4)/d := by positivity
  have hBle : π*((k:ℝ)+3/4)/d ≤ π/2 := by rw [div_le_iff₀ hd0]; nlinarith [hpi, h2k]
  have haltpi : π*((k:ℝ)+1/4)/d < π := by
    have : π*((k:ℝ)+1/4)/d < π*((k:ℝ)+3/4)/d := by
      rw [div_lt_div_iff_of_pos_right hd0]; nlinarith [hpi, hd0]
    linarith [hBle, hpi]
  have hBltpi : π*((k:ℝ)+3/4)/d < π := by linarith [hBle, hpi]
  have hsA_pos : 0 < Real.sin (π*((k:ℝ)+1/4)/d) := Real.sin_pos_of_pos_of_lt_pi haA haltpi
  have hsB_pos : 0 < Real.sin (π*((k:ℝ)+3/4)/d) := Real.sin_pos_of_pos_of_lt_pi haB hBltpi
  have hab : π*((k:ℝ)+1/4)/d < π*((k:ℝ)+3/4)/d := by
    rw [div_lt_div_iff_of_pos_right hd0]; nlinarith [hpi, hd0]
  have haAle : π*((k:ℝ)+1/4)/d ≤ π/2 := le_of_lt (lt_of_lt_of_le hab hBle)
  have hmono : Real.sin (π*((k:ℝ)+1/4)/d) < Real.sin (π*((k:ℝ)+3/4)/d) := by
    apply Real.strictMonoOn_sin
    · exact ⟨by linarith [haA, hpi], haAle⟩
    · exact ⟨by linarith [haB, hpi], hBle⟩
    · exact hab
  have hsq : Real.sin (π*((k:ℝ)+1/4)/d)^2 ≤ Real.sin (π*((k:ℝ)+3/4)/d)^2 := by
    nlinarith [hmono, hsA_pos, hsB_pos]
  unfold bracketClosed
  apply mul_nonneg (by positivity)
  rw [sub_nonneg]
  exact one_div_le_one_div_of_le (by positivity) hsq

/-! ### The k=0 bracket exceeds 2 (the analytic lower bound) -/

omit [NeZero d] in
lemma bracket_zero_gt_two (hd : 2 ≤ d) : 2 < bracketClosed d 0 := by
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0:ℝ) < d := by linarith
  have hdne : (d:ℝ) ≠ 0 := ne_of_gt hd0
  have hpi := Real.pi_pos
  have hpine : (π:ℝ) ≠ 0 := ne_of_gt hpi
  have hpiu : π < 3.15 := Real.pi_lt_d2
  have hp2 : (0:ℝ) < π^2 := by positivity
  have hAeq : π*(((0:ℕ):ℝ)+1/4)/d = π/(4*d) := by push_cast; ring
  have hBeq : π*(((0:ℕ):ℝ)+3/4)/d = 3*π/(4*d) := by push_cast; ring
  have haA : (0:ℝ) < π/(4*d) := by positivity
  have hAltpi : π/(4*d) < π := by rw [div_lt_iff₀ (by positivity)]; nlinarith [hpi, hdR]
  have hsA_pos : 0 < Real.sin (π/(4*d)) := Real.sin_pos_of_pos_of_lt_pi haA hAltpi
  have hsAub : Real.sin (π/(4*d))*(4*d) < π := (lt_div_iff₀ (by positivity)).mp (Real.sin_lt haA)
  have haB : (0:ℝ) < 3*π/(4*d) := by positivity
  have hBltpi : 3*π/(4*d) < π := by rw [div_lt_iff₀ (by positivity)]; nlinarith [hpi, hdR]
  have hsB_pos : 0 < Real.sin (3*π/(4*d)) := Real.sin_pos_of_pos_of_lt_pi haB hBltpi
  have hBle : 3*π/(4*d) ≤ π/2 := by rw [div_le_iff₀ (by positivity)]; nlinarith [hpi, hdR]
  have hsBlb : 3/(2*d) ≤ Real.sin (3*π/(4*d)) := by
    have hj := jordan_sin (3*π/(4*d)) (le_of_lt haB) hBle
    rwa [show 2*(3*π/(4*d))/π = 3/(2*d) by field_simp; ring] at hj
  have hsBlb2 : (3:ℝ) ≤ Real.sin (3*π/(4*d))*(2*d) := by
    rw [div_le_iff₀ (by positivity)] at hsBlb; linarith [hsBlb]
  have hxnn : 0 ≤ Real.sin (π/(4*d))*(4*d) := by positivity
  have hA : 16*(d:ℝ)^2/π^2 ≤ 1/Real.sin (π/(4*d))^2 := by
    rw [div_le_div_iff₀ hp2 (by positivity : (0:ℝ) < Real.sin (π/(4*d))^2)]
    nlinarith [mul_self_lt_mul_self hxnn hsAub]
  have hB : 1/Real.sin (3*π/(4*d))^2 ≤ 4*(d:ℝ)^2/9 := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < Real.sin (3*π/(4*d))^2) (by norm_num : (0:ℝ) < 9)]
    nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 3) hsBlb2]
  rw [bracketClosed, hAeq, hBeq]
  have hprod : (0:ℝ) < 2/(d:ℝ)^2 := by positivity
  have hstep : (2/(d:ℝ)^2) * (16*(d:ℝ)^2/π^2 - 4*(d:ℝ)^2/9)
      ≤ (2/(d:ℝ)^2) * (1/Real.sin (π/(4*d))^2 - 1/Real.sin (3*π/(4*d))^2) :=
    mul_le_mul_of_nonneg_left (by linarith [hA, hB]) (le_of_lt hprod)
  have heq : (2/(d:ℝ)^2) * (16*(d:ℝ)^2/π^2 - 4*(d:ℝ)^2/9) = 32/π^2 - 8/9 := by
    field_simp; ring
  have hfin : (2:ℝ) < 32/π^2 - 8/9 := by
    have h288 : 26*π^2 < 288 := by nlinarith [hpiu, hpi]
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hp2]; nlinarith [h288]
  linarith [hstep, heq, hfin]

/-! ### The general-d CGLMP violation and the Bell force -/

/-- **The general-`d` closed-form CGLMP value for `Ψ_d`.** The CGLMP functional on `Ψ_d`'s
Born table is the `⌊d/2⌋`-term weighted sum of the Dirichlet-kernel brackets
`(2/d²)(csc²(π(k+1/4)/d) − csc²(π(k+3/4)/d))`, the standard maximally-entangled CGLMP value.
Derived (`cglmpBracket_closed`), not asserted. -/
theorem cglmp_maxEntangled_qudit_closed :
    ProbabilityTheory.CGLMP.cglmp d (pQM d)
      = ∑ k ∈ Finset.range (d/2), (1 - 2*(k:ℝ)/((d:ℝ)-1)) * bracketClosed d k := by
  rw [ProbabilityTheory.CGLMP.cglmp]
  exact Finset.sum_congr rfl (fun k _ => by rw [cglmpBracket_closed])

/-- **The general-`d` CGLMP violation (QM side).** For every `d ≥ 2`, `Ψ_d = maxEntangled d`
violates the CGLMP inequality: its CGLMP value exceeds the local-hidden-variable bound `2`.
A genuine analytic inequality on the `d`-dependent Dirichlet-kernel trig sum, proved for ALL
`d ≥ 2` (the sum dominates its `k = 0` term, and that term alone is `≥ 32/π² − 8/9 > 2`
uniformly in `d`). Extends the `d = 3` qutrit result
`CGLMPQutrit.cglmp_maxEntangled_qutrit_gt_two` to full dimensional generality. -/
theorem cglmp_maxEntangled_qudit_gt_two (hd : 2 ≤ d) :
    ProbabilityTheory.CGLMP.cglmp d (pQM d) > 2 := by
  rw [ProbabilityTheory.CGLMP.cglmp]
  have hmem : (0:ℕ) ∈ Finset.range (d/2) := by rw [Finset.mem_range]; omega
  have hsum : ∀ k ∈ Finset.range (d/2),
      0 ≤ (1 - 2*(k:ℝ)/((d:ℝ)-1)) * ProbabilityTheory.CGLMP.cglmpBracket d (pQM d) k := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [cglmpBracket_closed]
    exact mul_nonneg (coeff_nonneg d hd k hk) (bracketClosed_nonneg d hd k hk)
  have hle := Finset.single_le_sum hsum hmem
  have hf0 : (1 - 2*((0:ℕ):ℝ)/((d:ℝ)-1)) * ProbabilityTheory.CGLMP.cglmpBracket d (pQM d) 0
      = bracketClosed d 0 := by rw [cglmpBracket_closed]; norm_num
  rw [hf0] at hle
  linarith [hle, bracket_zero_gt_two d hd]

theorem no_lhv_realises_maxEntangled_cglmp_d (hd : 2 ≤ d)
    {Λ : Type*} [MeasurableSpace Λ] (μ : MeasureTheory.Measure Λ)
    [MeasureTheory.IsProbabilityMeasure μ]
    (A B : Bool → Λ → ZMod d) (hA : ∀ x, Measurable (A x)) (hB : ∀ y, Measurable (B y))
    (hRep : ProbabilityTheory.CGLMP.lhvTable μ A B = pQM d) : False := by
  have hle := ProbabilityTheory.CGLMP.cglmp_lhv_bound μ hd A B hA hB
  rw [ProbabilityTheory.CGLMP.cglmpLHV, hRep] at hle
  linarith [cglmp_maxEntangled_qudit_gt_two d hd]

end CGLMPQudit
end LF6
end CSD
