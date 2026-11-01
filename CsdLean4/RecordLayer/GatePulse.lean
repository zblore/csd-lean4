/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.GatedFlow
public import CsdLean4.RecordLayer.DiracArrival
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# A gated pulse that flips the band

**Category:** 7-SigmaLayer (the record layer). BACKLOG #274, second landing (the first of the
relay's three).

The relay of #274 returns a messenger from a moving observer `B`. A momentum kick does not do it on
the Dirac chain: the spinor angle is `asin v`, so turning `v = 3/5` into `v = −4/5` puts half the
weight into the lower band. What does it is a **band flip in place**: `σ_y` acts on the spinor at
every site and anticommutes with the Dirac Hamiltonian, so it sends the upper-band mode of momentum
`m` to the lower-band mode of the same momentum, whose group velocity is reversed. A short gated
pulse `Ψ' = −i (H + c(t) σ_y) Ψ` with `∫ c = π/2` flips a messenger co-moving with `B` into a
messenger moving back from `B`'s position.

## The pulse, for any anticommuting involution

For `H`, `V` Hermitian with `VH = −HV`, `V² = 1`, and a curve `Ψ' = −i (H + c(t) V) Ψ`:

* `sqNorm` (the squared `ℓ²` norm), `hasDerivAt_mulVec`, `hasDerivAt_star_dotProduct`,
  `star_mulVec_dotProduct`, `im_star_dotProduct_mulVec_self` (a Hermitian form is real);
* ★★ `sqNorm_mulVec_const` — **`‖HΨ‖²` is conserved by the gated evolution** (`V` commutes with
  `H²`);
* `gateRot V θ = cos θ · 1 − i sin θ · V` (the closed form of `e^{−iθV}`), `gateRot_mulVec`,
  `gateRot_zero_mulVec`, `gateRot_mulVec_gateRot_neg`, ★ `sqNorm_gateRot_mulVec` (it is unitary);
* ★★★ `sqNorm_sub_gateRot_le` — **the pulse bound**:
  `‖Ψ(T) − e^{−iC(T)V} Ψ(0)‖² ≤ T² ‖HΨ(0)‖²`, `C(T) = ∫₀ᵀ c`. The proof rotates the frame,
  `S(t) = e^{iC(t)V} Ψ(t)`: its velocity is `−i e^{iC V} HΨ`, of norm `‖HΨ(0)‖`, so `S` moves at
  most `T‖HΨ(0)‖` from `Ψ(0)` (the mean value inequality in `EuclideanSpace`), and `e^{−iC V}` is
  unitary. No Grönwall factor, and no Lipschitz constant of `H` enters;
* `integral_gate_eq` — **the gate design**: for `c = Φ'(r) · r'` the accumulated pulse is
  `Φ(r(T)) − Φ(r(0))` exactly, whatever the register's speed.

## `σ_y` on the Dirac chain

* `diracSy`, `spinY`, `spinY_mulVec_apply`, ★ `spinY_isHermitian`, ★ `spinY_mulVec_spinY` (an
  involution), ★★ `spinY_mulVec_diracHam_mulVec` — **it anticommutes with `H`**;
* ★ `diracHam_mulVec_spinY_diracMode` (`σ_y ψ_m` is an eigenvector of energy `−E_m`),
  `chainProp_mulVec_spinY_mode`, ★★ `chainProp_spinY_packet` — **the flipped packet runs
  backward**: `e^{−itH} σ_y ψ(0) = σ_y ψ(−t)`, so it moves at `−v` from where it was;
* ★ `siteWeight_spinY` — **site densities are invariant**: a detector integrating them, and `B`'s
  encounter register, do not see the flip.

## The bundles

★★★ `gate_pulse` (the generic pulse) and ★★★ `dirac_band_flip` (`σ_y` on the chain).

## Honest scope

⚠️ **The flip is approximate**: the error is `T‖HΨ₀‖` for a pulse of duration `T`; the register
sets `T` (`δ_r / w`), and the instance (next landing) takes it small against the encounter window.
`‖HΨ₀‖` is the messenger's energy, `≤ √(μ² + c²p²)` on its window.

⚠️ **A curve, not yet the arena.** The theorem is for any curve solving the gated equation with a
scalar coefficient `c(t)`; the relay arena (`B`'s device, the messenger, `B`'s register, with `c`
read off the state) is the next landing, where it is this theorem applied to the messenger block of
`gatedFlow`'s orbit.

⚠️ **Nothing is a record here.** Emission, reception, return and the two-way factor are the third
landing.

References: `specs/BACKLOG.md` #274, #256, #270, #39; `RecordLayer/GatedFlow.lean`
(`gatedFlow`, `star_dotProduct_self_eq`); `RecordLayer/DiracArrival.lean` (`chainProp`,
`chainProp_mulVec_mode`, `exp_mulVec_of_mulVec_eq_smul`); `CV/DiracClockChain.lean` (`diracHam`,
`diracHam_mulVec_diracMode`, `diracHam_isHermitian`); `RecordLayer/DiracDetector.lean`
(`siteWeight`).
-/

@[expose] public section

open Set MeasureTheory Complex CSD.CV
open scoped Matrix

namespace CSD.RecordLayer

open CSD.SigmaLayer

/-! ### The squared norm and derivatives -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The squared `ℓ²` norm** of a state. -/
noncomputable def sqNorm (v : ι → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

omit [DecidableEq ι] in
theorem sqNorm_nonneg (v : ι → ℂ) : 0 ≤ sqNorm v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq ι] in
theorem sqNorm_eq_re (v : ι → ℂ) : sqNorm v = (star v ⬝ᵥ v).re := by
  rw [star_dotProduct_self_eq, Complex.ofReal_re, sqNorm]

omit [DecidableEq ι] in
theorem sqNorm_eq_norm_toLp (v : ι → ℂ) :
    sqNorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, sqNorm]

omit [DecidableEq ι] in
theorem sqNorm_smul (a : ℂ) (v : ι → ℂ) : sqNorm (a • v) = ‖a‖ ^ 2 * sqNorm v := by
  simp only [sqNorm, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

omit [DecidableEq ι] in
theorem hasDerivAt_mulVec {f : ℝ → ι → ℂ} {f' : ι → ℂ} {t : ℝ} (A : Matrix ι ι ℂ)
    (hf : HasDerivAt f f' t) : HasDerivAt (fun t => A *ᵥ f t) (A *ᵥ f') t := by
  rw [hasDerivAt_pi] at hf ⊢
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact HasDerivAt.fun_sum fun j _ => (hf j).const_mul (A i j)

omit [DecidableEq ι] in
theorem hasDerivAt_star_dotProduct {u w : ℝ → ι → ℂ} {u' w' : ι → ℂ} {t : ℝ}
    (hu : HasDerivAt u u' t) (hw : HasDerivAt w w' t) :
    HasDerivAt (fun t => star (u t) ⬝ᵥ w t) (star u' ⬝ᵥ w t + star (u t) ⬝ᵥ w') t := by
  have hc := fun i => hasDerivAt_pi.1 hu i
  have hd := fun i => hasDerivAt_pi.1 hw i
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => ((hc i).star).mul (hd i)
  simp only [dotProduct, Pi.star_apply]
  rw [← Finset.sum_add_distrib]
  exact hs

omit [DecidableEq ι] in
/-- Moving a Hermitian matrix across the form. -/
theorem star_mulVec_dotProduct {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (u w : ι → ℂ) :
    star (A *ᵥ u) ⬝ᵥ w = star u ⬝ᵥ (A *ᵥ w) := by
  rw [Matrix.star_mulVec, hA.eq, ← Matrix.dotProduct_mulVec]

omit [DecidableEq ι] in
/-- A Hermitian form is real. -/
theorem im_star_dotProduct_mulVec_self {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (v : ι → ℂ) :
    (star v ⬝ᵥ (A *ᵥ v)).im = 0 := by
  have h := hA.star_dotProduct_mulVec_comm v v
  rw [Complex.star_def] at h
  exact Complex.conj_eq_iff_im.1 h

/-! ### `‖HΨ‖` is conserved -/

variable {H V : Matrix ι ι ℂ}

omit [DecidableEq ι] in
/-- ★★ **The gated evolution conserves `‖HΨ‖²`** when `V` anticommutes with `H`: `V` then commutes
with `H²`. -/
theorem sqNorm_mulVec_const (hH : H.IsHermitian) (hV : V.IsHermitian)
    (hVH : ∀ v, V *ᵥ (H *ᵥ v) = -(H *ᵥ (V *ᵥ v))) {c : ℝ → ℝ} {Ψ : ℝ → ι → ℂ}
    (hΨ : ∀ t, HasDerivAt Ψ ((-I) • ((H + ((c t : ℝ) : ℂ) • V) *ᵥ Ψ t)) t) (t : ℝ) :
    sqNorm (H *ᵥ Ψ t) = sqNorm (H *ᵥ Ψ 0) := by
  set F : ℝ → ℂ := fun t => star (H *ᵥ Ψ t) ⬝ᵥ (H *ᵥ Ψ t) with hF
  have hd : ∀ t, HasDerivAt F 0 t := by
    intro t
    have h1 := hasDerivAt_mulVec H (hΨ t)
    have h2 := hasDerivAt_star_dotProduct h1 h1
    set u := H *ᵥ Ψ t with hu
    set z := star u ⬝ᵥ (H *ᵥ ((H + ((c t : ℝ) : ℂ) • V) *ᵥ Ψ t)) with hz
    have hz_im : z.im = 0 := by
      have e1 : (star u ⬝ᵥ (H *ᵥ u)).im = 0 := im_star_dotProduct_mulVec_self hH u
      have e2 : (star u ⬝ᵥ (H *ᵥ (V *ᵥ Ψ t))).im = 0 := by
        have hconj : star (star u ⬝ᵥ (H *ᵥ (V *ᵥ Ψ t))) = star u ⬝ᵥ (H *ᵥ (V *ᵥ Ψ t)) := by
          rw [← Matrix.star_dotProduct, star_mulVec_dotProduct hH, star_mulVec_dotProduct hV, hu,
            hVH, hVH, Matrix.mulVec_neg, neg_neg, ← star_mulVec_dotProduct hH]
        rw [Complex.star_def] at hconj
        exact Complex.conj_eq_iff_im.1 hconj
      rw [hz, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
        dotProduct_add, dotProduct_smul, Complex.add_im, smul_eq_mul, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, e1, e2]
      ring
    have hzs : star z = z := by
      rw [Complex.star_def]
      exact Complex.conj_eq_iff_im.2 hz_im
    convert h2 using 1
    rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, star_neg,
      show star I = -I from Complex.conj_I, neg_neg,
      Matrix.star_dotProduct (H *ᵥ ((H + ((c t : ℝ) : ℂ) • V) *ᵥ Ψ t)) u, ← hz, hzs,
      smul_eq_mul, smul_eq_mul]
    ring
  have hconst : ∀ t, F t = F 0 := fun t =>
    is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t 0
  have h := hconst t
  simp only [hF] at h
  rw [sqNorm_eq_re, sqNorm_eq_re, h]

/-! ### The rotation `e^{−iθV}` -/

/-- **The gate rotation** `e^{−iθV} = cos θ · 1 − i sin θ · V` for an involution `V`. -/
noncomputable def gateRot (V : Matrix ι ι ℂ) (θ : ℝ) : Matrix ι ι ℂ :=
  ((Real.cos θ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) - (I * ((Real.sin θ : ℝ) : ℂ)) • V

theorem gateRot_mulVec (V : Matrix ι ι ℂ) (θ : ℝ) (v : ι → ℂ) :
    gateRot V θ *ᵥ v = ((Real.cos θ : ℝ) : ℂ) • v - (I * ((Real.sin θ : ℝ) : ℂ)) • (V *ᵥ v) := by
  simp only [gateRot, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem gateRot_zero_mulVec (V : Matrix ι ι ℂ) (v : ι → ℂ) : gateRot V 0 *ᵥ v = v := by
  simp [gateRot_mulVec]

/-- `e^{−iθV} e^{iθV} = 1`. -/
theorem gateRot_mulVec_gateRot_neg (hV2 : ∀ v, V *ᵥ (V *ᵥ v) = v) (θ : ℝ) (v : ι → ℂ) :
    gateRot V θ *ᵥ (gateRot V (-θ) *ᵥ v) = v := by
  rw [gateRot_mulVec, gateRot_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
    hV2, Real.cos_neg, Real.sin_neg]
  have hcs : ((Real.cos θ : ℝ) : ℂ) ^ 2 + ((Real.sin θ : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_neg]
  linear_combination (v i) * hcs - ((Real.sin θ : ℝ) : ℂ) ^ 2 * (v i) * Complex.I_sq

omit [DecidableEq ι] in
/-- The form of `V` is real. -/
theorem star_dotProduct_mulVec_self_real (hV : V.IsHermitian) (v : ι → ℂ) :
    star (star v ⬝ᵥ (V *ᵥ v)) = star v ⬝ᵥ (V *ᵥ v) := by
  rw [Complex.star_def]
  exact Complex.conj_eq_iff_im.2 (im_star_dotProduct_mulVec_self hV v)

/-- ★ **The gate rotation is unitary.** -/
theorem sqNorm_gateRot_mulVec (hV : V.IsHermitian) (hV2 : ∀ v, V *ᵥ (V *ᵥ v) = v) (θ : ℝ)
    (v : ι → ℂ) : sqNorm (gateRot V θ *ᵥ v) = sqNorm v := by
  rw [sqNorm_eq_re, sqNorm_eq_re, gateRot_mulVec]
  set a : ℂ := ((Real.cos θ : ℝ) : ℂ)
  set b : ℂ := I * ((Real.sin θ : ℝ) : ℂ)
  set z := star v ⬝ᵥ (V *ᵥ v) with hz
  have h1 : star (V *ᵥ v) ⬝ᵥ (V *ᵥ v) = star v ⬝ᵥ v := by
    rw [star_mulVec_dotProduct hV, hV2]
  have h2 : star (V *ᵥ v) ⬝ᵥ v = z := by
    rw [star_mulVec_dotProduct hV]
  have hzr := star_dotProduct_mulVec_self_real hV v
  simp only [star_sub, star_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul]
  rw [h1, h2, ← hz]
  have hsa : star a = a := by simp only [a, Complex.star_def, Complex.conj_ofReal]
  have hsb : star b = -b := by
    simp only [b, star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hcs : a ^ 2 + (-(b ^ 2)) = 1 := by
    simp only [a, b]
    have := Real.cos_sq_add_sin_sq θ
    have h' : ((Real.cos θ : ℝ) : ℂ) ^ 2 + ((Real.sin θ : ℝ) : ℂ) ^ 2 = 1 := by exact_mod_cast this
    linear_combination h' - ((Real.sin θ : ℝ) : ℂ) ^ 2 * Complex.I_sq
  rw [hsa, hsb]
  simp only [smul_eq_mul]
  congr 1
  linear_combination (star v ⬝ᵥ v) * hcs

/-! ### The pulse bound -/

/-- ★★★ **The pulse bound**: for Hermitian `H`, `V` with `VH = −HV` and `V² = 1`, a curve
`Ψ' = −i (H + c(t) V) Ψ` stays within `T ‖HΨ(0)‖` of the rotated state `e^{−iC(T)V} Ψ(0)`,
`C(T) = ∫₀ᵀ c`. -/
theorem sqNorm_sub_gateRot_le (hH : H.IsHermitian) (hV : V.IsHermitian)
    (hVH : ∀ v, V *ᵥ (H *ᵥ v) = -(H *ᵥ (V *ᵥ v))) (hV2 : ∀ v, V *ᵥ (V *ᵥ v) = v)
    {c : ℝ → ℝ} (hc : Continuous c) {Ψ : ℝ → ι → ℂ}
    (hΨ : ∀ t, HasDerivAt Ψ ((-I) • ((H + ((c t : ℝ) : ℂ) • V) *ᵥ Ψ t)) t) {T : ℝ} (hT : 0 ≤ T) :
    sqNorm (Ψ T - gateRot V (∫ s in (0 : ℝ)..T, c s) *ᵥ Ψ 0) ≤ T ^ 2 * sqNorm (H *ᵥ Ψ 0) := by
  set C : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, c s with hCdef
  have hC : ∀ t, HasDerivAt C (c t) t := fun t => (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hC0 : C 0 = 0 := intervalIntegral.integral_same
  -- the rotating frame
  set S : ℝ → ι → ℂ := fun t => ((Real.cos (C t) : ℝ) : ℂ) • Ψ t
    + (I * ((Real.sin (C t) : ℝ) : ℂ)) • (V *ᵥ Ψ t) with hSdef
  have hSrot : ∀ t, S t = gateRot V (-(C t)) *ᵥ Ψ t := fun t => by
    rw [gateRot_mulVec, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    simp only [hSdef]
    rw [sub_eq_add_neg, ← neg_smul]
    congr 2
    ring
  set D : ℝ → ι → ℂ := fun t => (-I) • (gateRot V (-(C t)) *ᵥ (H *ᵥ Ψ t)) with hDdef
  have hS : ∀ t, HasDerivAt S (D t) t := by
    intro t
    have hcos : HasDerivAt (fun t => ((Real.cos (C t) : ℝ) : ℂ))
        (((-Real.sin (C t) * c t : ℝ) : ℂ)) t := ((hC t).cos).ofReal_comp
    have hsin : HasDerivAt (fun t => I * ((Real.sin (C t) : ℝ) : ℂ))
        (I * ((Real.cos (C t) * c t : ℝ) : ℂ)) t := ((hC t).sin).ofReal_comp.const_mul I
    have h1 := hcos.smul (hΨ t)
    have h2 := hsin.smul (hasDerivAt_mulVec V (hΨ t))
    have h := h1.add h2
    convert h using 1
    funext i
    simp only [hDdef, gateRot_mulVec, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.mulVec_add, Matrix.mulVec_smul, hVH, hV2, Pi.neg_apply, Complex.ofReal_mul]
    linear_combination (((Real.sin (C t) : ℝ) : ℂ) * ((c t : ℝ) : ℂ) * Ψ t i) * Complex.I_sq
  -- the velocity has constant norm
  have hDnorm : ∀ t, sqNorm (D t) = sqNorm (H *ᵥ Ψ 0) := fun t => by
    rw [hDdef]
    simp only
    rw [sqNorm_smul, norm_neg, Complex.norm_I, one_pow, one_mul, sqNorm_gateRot_mulVec hV hV2,
      sqNorm_mulVec_const hH hV hVH hΨ]
  -- the mean value inequality in `EuclideanSpace`
  set Θ : ℝ → EuclideanSpace ℂ ι := fun t => WithLp.toLp 2 (S t) with hΘ
  have hΘd : ∀ t, HasDerivAt Θ (WithLp.toLp 2 (D t)) t := fun t => by
    have h := ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ℂ)).symm.toContinuousLinearMap.restrictScalars
      ℝ).hasFDerivAt.comp_hasDerivAt t (hS t)
    simpa [Function.comp_def, hΘ] using h
  set M : ℝ := Real.sqrt (sqNorm (H *ᵥ Ψ 0)) with hM
  have hbound : ∀ x ∈ Ico (0 : ℝ) T, ‖WithLp.toLp 2 (D x)‖ ≤ M := fun x _ => by
    rw [EuclideanSpace.norm_eq, hM]
    exact le_of_eq (congrArg Real.sqrt (hDnorm x))
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := Θ)
    (f' := fun t => WithLp.toLp 2 (D t)) (a := 0) (b := T) (C := M)
    (fun x _ => (hΘd x).hasDerivWithinAt) hbound T ⟨hT, le_rfl⟩
  rw [sub_zero] at hmvt
  -- unwind
  have hS0 : S 0 = Ψ 0 := by
    simp only [hSdef, hC0, Real.cos_zero, Real.sin_zero, Complex.ofReal_one, Complex.ofReal_zero,
      mul_zero, one_smul, zero_smul, add_zero]
  have hΘsub : ‖Θ T - Θ 0‖ ^ 2 = sqNorm (S T - Ψ 0) := by
    rw [hΘ]
    simp only
    rw [← WithLp.toLp_sub, ← sqNorm_eq_norm_toLp, hS0]
  have hkey : sqNorm (Ψ T - gateRot V (C T) *ᵥ Ψ 0) = sqNorm (S T - Ψ 0) := by
    have e : Ψ T - gateRot V (C T) *ᵥ Ψ 0 = gateRot V (C T) *ᵥ (S T - Ψ 0) := by
      rw [Matrix.mulVec_sub, hSrot, gateRot_mulVec_gateRot_neg hV2]
    rw [e, sqNorm_gateRot_mulVec hV hV2]
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hmvt 2
  rw [hΘsub, mul_pow, hM, Real.sq_sqrt (sqNorm_nonneg _)] at hsq
  show sqNorm (Ψ T - gateRot V (C T) *ᵥ Ψ 0) ≤ T ^ 2 * sqNorm (H *ᵥ Ψ 0)
  rw [hkey]
  linarith

/-! ### The gate design -/

/-- **The gate design**: for `c = Φ'(r) · r'` along a register `r`, the accumulated pulse is
`Φ(r(T)) − Φ(r(0))` exactly, whatever the register's speed. -/
theorem integral_gate_eq {Φ φ : ℝ → ℝ} (hΦ : ∀ r, HasDerivAt Φ (φ r) r) {r w : ℝ → ℝ}
    (hr : ∀ t, HasDerivAt r (w t) t) (hcont : Continuous fun t => φ (r t) * w t) (T : ℝ) :
    ∫ s in (0 : ℝ)..T, φ (r s) * w s = Φ (r T) - Φ (r 0) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Φ ∘ r)
    (fun s _ => (hΦ (r s)).comp s (hr s)) (hcont.intervalIntegrable _ _)

/-- ★★★ **The gated pulse** (BACKLOG #274, generic part). For Hermitian `H`, `V` with `VH = −HV`,
`V² = 1`, and a curve `Ψ' = −i (H + c(t) V) Ψ` with `c` continuous:

* `‖HΨ(t)‖² = ‖HΨ(0)‖²` for all `t`;
* `e^{−iθV} = cos θ − i sin θ V` is unitary;
* `‖Ψ(T) − e^{−iC(T)V} Ψ(0)‖² ≤ T² ‖HΨ(0)‖²` for `T ≥ 0`, `C(T) = ∫₀ᵀ c`;
* for `c = Φ'(r) r'`, `C(T) = Φ(r(T)) − Φ(r(0))`. -/
theorem gate_pulse (hH : H.IsHermitian) (hV : V.IsHermitian)
    (hVH : ∀ v, V *ᵥ (H *ᵥ v) = -(H *ᵥ (V *ᵥ v))) (hV2 : ∀ v, V *ᵥ (V *ᵥ v) = v)
    {c : ℝ → ℝ} (hc : Continuous c) {Ψ : ℝ → ι → ℂ}
    (hΨ : ∀ t, HasDerivAt Ψ ((-I) • ((H + ((c t : ℝ) : ℂ) • V) *ᵥ Ψ t)) t) :
    (∀ t, sqNorm (H *ᵥ Ψ t) = sqNorm (H *ᵥ Ψ 0))
    ∧ (∀ θ v, sqNorm (gateRot V θ *ᵥ v) = sqNorm v)
    ∧ (∀ T, 0 ≤ T →
        sqNorm (Ψ T - gateRot V (∫ s in (0 : ℝ)..T, c s) *ᵥ Ψ 0) ≤ T ^ 2 * sqNorm (H *ᵥ Ψ 0))
    ∧ ∀ (Φ φ : ℝ → ℝ), (∀ r, HasDerivAt Φ (φ r) r) → ∀ r w : ℝ → ℝ, (∀ t, HasDerivAt r (w t) t) →
        (∀ t, c t = φ (r t) * w t) → ∀ T, (∫ s in (0 : ℝ)..T, c s) = Φ (r T) - Φ (r 0) :=
  ⟨sqNorm_mulVec_const hH hV hVH hΨ, sqNorm_gateRot_mulVec hV hV2,
    fun _ hT => sqNorm_sub_gateRot_le hH hV hVH hV2 hc hΨ hT,
    fun Φ φ hΦ r w hr hcw T => by
      have e : c = fun t => φ (r t) * w t := funext hcw
      rw [e]
      exact integral_gate_eq hΦ hr (e ▸ hc) T⟩

end Generic

/-! ### `σ_y` on the Dirac chain -/

section Dirac

variable {L : ℕ} [NeZero L]

/-- `σ_y`. -/
def diracSy : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- **`σ_y` at every site**: the band flip. -/
def spinY : Matrix (ZMod L × Fin 2) (ZMod L × Fin 2) ℂ :=
  Matrix.of fun p q => (if q.1 = p.1 then 1 else 0) * diracSy p.2 q.2

theorem spinY_mulVec_apply (v : ZMod L × Fin 2 → ℂ) (j : ZMod L) :
    (spinY *ᵥ v) (j, 0) = -I * v (j, 1) ∧ (spinY *ᵥ v) (j, 1) = I * v (j, 0) := by
  constructor <;>
  · simp only [Matrix.mulVec, dotProduct, spinY, Matrix.of_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, diracSy, ite_mul, one_mul, zero_mul]
    simp [Finset.sum_ite_eq']

omit [NeZero L] in
/-- ★ `σ_y` is Hermitian. -/
theorem spinY_isHermitian : Matrix.IsHermitian (spinY (L := L)) := by
  ext ⟨j, a⟩ ⟨j', b⟩
  simp only [Matrix.conjTranspose_apply, spinY, Matrix.of_apply]
  have e3 : (j = j') = (j' = j) := propext eq_comm
  simp only [e3]
  fin_cases a <;> fin_cases b <;> simp [diracSy] <;> split_ifs <;> simp

/-- ★ `σ_y` is an involution. -/
theorem spinY_mulVec_spinY (v : ZMod L × Fin 2 → ℂ) : spinY *ᵥ (spinY *ᵥ v) = v := by
  funext ⟨j, a⟩
  fin_cases a
  · show (spinY *ᵥ (spinY *ᵥ v)) (j, 0) = v (j, 0)
    rw [(spinY_mulVec_apply _ j).1, (spinY_mulVec_apply v j).2]
    linear_combination (-(v (j, 0))) * Complex.I_sq
  · show (spinY *ᵥ (spinY *ᵥ v)) (j, 1) = v (j, 1)
    rw [(spinY_mulVec_apply _ j).2, (spinY_mulVec_apply v j).1]
    linear_combination (-(v (j, 1))) * Complex.I_sq

/-- The Dirac Hamiltonian, site by site. -/
theorem diracHam_mulVec_apply_two (J μ : ℝ) (v : ZMod L × Fin 2 → ℂ) (j : ZMod L) :
    (diracHam J μ *ᵥ v) (j, 0) = (J : ℂ) * (-I) * (v (j + 1, 1) - v (j - 1, 1)) + (μ : ℂ) * v (j, 0)
    ∧ (diracHam J μ *ᵥ v) (j, 1)
      = (J : ℂ) * (-I) * (v (j + 1, 0) - v (j - 1, 0)) - (μ : ℂ) * v (j, 1) := by
  constructor <;>
  · simp only [Matrix.mulVec, dotProduct, diracHam, Matrix.of_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, diracSx, diracSz]
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_mul, mul_assoc,
      Finset.sum_ite_eq', mul_sub]
    ring

/-- ★★ **`σ_y` anticommutes with the Dirac Hamiltonian.** -/
theorem spinY_mulVec_diracHam_mulVec (J μ : ℝ) (v : ZMod L × Fin 2 → ℂ) :
    spinY *ᵥ (diracHam J μ *ᵥ v) = -(diracHam J μ *ᵥ (spinY *ᵥ v)) := by
  funext ⟨j, a⟩
  fin_cases a
  · show (spinY *ᵥ (diracHam J μ *ᵥ v)) (j, 0) = -((diracHam J μ *ᵥ (spinY *ᵥ v)) (j, 0))
    rw [(spinY_mulVec_apply _ j).1, (diracHam_mulVec_apply_two J μ v j).2,
      (diracHam_mulVec_apply_two J μ _ j).1, (spinY_mulVec_apply v (j + 1)).2,
      (spinY_mulVec_apply v (j - 1)).2, (spinY_mulVec_apply v j).1]
    ring
  · show (spinY *ᵥ (diracHam J μ *ᵥ v)) (j, 1) = -((diracHam J μ *ᵥ (spinY *ᵥ v)) (j, 1))
    rw [(spinY_mulVec_apply _ j).2, (diracHam_mulVec_apply_two J μ v j).1,
      (diracHam_mulVec_apply_two J μ _ j).2, (spinY_mulVec_apply v (j + 1)).1,
      (spinY_mulVec_apply v (j - 1)).1, (spinY_mulVec_apply v j).2]
    ring

/-- ★ **The flipped mode is an eigenvector of energy `−E_m`.** -/
theorem diracHam_mulVec_spinY_diracMode (J μ : ℝ) (n : ZMod L) :
    diracHam J μ *ᵥ (spinY *ᵥ diracMode J μ n)
      = ((-dispE μ (modeS J n) : ℝ) : ℂ) • (spinY *ᵥ diracMode J μ n) := by
  have h := spinY_mulVec_diracHam_mulVec J μ (diracMode (L := L) J μ n)
  rw [diracHam_mulVec_diracMode, Matrix.mulVec_smul] at h
  rw [← neg_neg (diracHam J μ *ᵥ (spinY *ᵥ diracMode J μ n)), ← h, Complex.ofReal_neg, neg_smul]

/-- The flipped mode runs backward. -/
theorem chainProp_mulVec_spinY_mode (J μ t : ℝ) (m : ℤ) :
    chainProp (L := L) J μ t *ᵥ (spinY *ᵥ diracMode J μ (m : ZMod L))
      = exp (I * bandE J μ (angleZ L m) * t) • (spinY *ᵥ diracMode J μ (m : ZMod L)) := by
  have h : ((-(I * t)) • diracHam (L := L) J μ) *ᵥ (spinY *ᵥ diracMode J μ (m : ZMod L))
      = (-(I * t) * -bandE J μ (angleZ L m)) • (spinY *ᵥ diracMode J μ (m : ZMod L)) := by
    rw [Matrix.smul_mulVec, diracHam_mulVec_spinY_diracMode, dispE_modeS_intCast, smul_smul]
    push_cast
    ring_nf
  rw [chainProp, exp_mulVec_of_mulVec_eq_smul h, ← Complex.exp_eq_exp_ℂ]
  congr 2
  ring

/-- ★★ **The flipped packet runs backward**: `e^{−itH} σ_y ψ(0) = σ_y ψ(−t)`. It moves at `−v`
from where the packet was. -/
theorem chainProp_spinY_packet (J μ : ℝ) (W : Finset ℤ) (a : ℤ → ℂ) (t : ℝ) :
    chainProp (L := L) J μ t *ᵥ (spinY *ᵥ packet (L := L) J μ W a 0)
      = spinY *ᵥ packet (L := L) J μ W a (-t) := by
  unfold packet
  rw [Matrix.mulVec_sum, Matrix.mulVec_sum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, chainProp_mulVec_spinY_mode,
    smul_smul]
  congr 1
  rw [mul_assoc, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-- ★ **Site densities do not see the flip.** -/
theorem siteWeight_spinY (v : ZMod L × Fin 2 → ℂ) (k : ZMod L) :
    siteWeight (spinY *ᵥ v) k = siteWeight v k := by
  simp only [siteWeight, Fin.sum_univ_two]
  rw [(spinY_mulVec_apply v k).1, (spinY_mulVec_apply v k).2, norm_mul, norm_mul, norm_neg,
    Complex.norm_I, one_mul, one_mul, add_comm]

/-- ★★★ **The band flip on the Dirac chain** (BACKLOG #274). `σ_y` at every site is Hermitian, an
involution, anticommutes with the Dirac Hamiltonian, leaves every site density unchanged, and sends
a packet to one that runs backward: `e^{−itH} σ_y ψ(0) = σ_y ψ(−t)`. -/
theorem dirac_band_flip (J μ : ℝ) :
    Matrix.IsHermitian (spinY (L := L))
    ∧ (∀ v : ZMod L × Fin 2 → ℂ, spinY *ᵥ (spinY *ᵥ v) = v)
    ∧ (∀ v : ZMod L × Fin 2 → ℂ,
        spinY *ᵥ (diracHam (L := L) J μ *ᵥ v) = -(diracHam J μ *ᵥ (spinY *ᵥ v)))
    ∧ (∀ (v : ZMod L × Fin 2 → ℂ) (k : ZMod L), siteWeight (spinY *ᵥ v) k = siteWeight v k)
    ∧ ∀ (W : Finset ℤ) (a : ℤ → ℂ) (t : ℝ),
        chainProp (L := L) J μ t *ᵥ (spinY *ᵥ packet (L := L) J μ W a 0)
          = spinY *ᵥ packet (L := L) J μ W a (-t) :=
  ⟨spinY_isHermitian, spinY_mulVec_spinY, spinY_mulVec_diracHam_mulVec J μ, siteWeight_spinY,
    chainProp_spinY_packet J μ⟩

end Dirac

end CSD.RecordLayer
