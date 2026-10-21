/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.AdiabaticPropagators

/-!
# Kato's comparison: `‖U_T − U_A‖ ≤ C / T`

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #162 (out of ~~#88~~, the core of Kato's adiabatic theorem).

Along a gapped `C²` path `Γ` with eigenprojector `P`, adiabatic generator `K = [Ṗ, P]`, physical
propagator `U_T` (`U' = −iT·H U`) and adiabatic propagator `U_A` (`U' = (−iT·H + K) U`) on
`[0, 1]`, **the two propagators differ by `O(1/T)` uniformly**:

  `∃ C, ∀ T > 0, ∀ s ∈ [0, 1], ‖U_T(s) − U_A(s)‖ ≤ C / T`.

The proof is Kato's. `W = U_T† U_A` has `W' = U_T† K U_A`, and the oscillation of the integrand is
what produces the `1/T`: write `K = Y H − H Y` for a `C¹` family `Y` (the **reduced resolvent**
`X = (λ − H)⁻¹ (1 − P)`, and `Y = X Ṗ P + P Ṗ X`); then `(U_T† Y U_A)' = −iT · U_T† K U_A + U_T† (Ẏ + Y K) U_A`,
so `W + (iT)⁻¹ U_T† Y U_A` has derivative `(iT)⁻¹ U_T† (Ẏ + Y K) U_A`, of size `O(1/T)`; the
boundary terms are `O(1/T)` because `Y` is bounded and the propagators are unitary.

* `circleIntegral_sub_inv_mul_self`, `circleIntegral_sub_inv_mul_sub_inv`,
  `circleIntegral_sub_inv_mul_sub_inv_eq` — the Cauchy evaluations of `∮ (z−λ)⁻¹ (z−μ)⁻¹ dz`
  (`0` for a double pole, `2πi (λ − μ)⁻¹` for `μ` outside);
* `Matrix.redResIntegral`, ★ `IsHermitian.redResIntegral_eq_conjD` — **the reduced resolvent as a
  contour integral** `(2πi)⁻¹ ∮ (z − λ)⁻¹ (z − H)⁻¹ dz` is `U diag(0 on the branch, (λ−μⱼ)⁻¹ off
  it) U†`;
* `GappedPath.redRes`, `redRes_eq_conjD`, `redRes_eq_near`, ★★ `contDiff_redRes` — **the reduced
  resolvent along the path is as smooth as the path** (the contour freezes locally, exactly as for
  `P` in #159; `contDiffOn_circleIntegral`);
* `smul_one_sub_H_mul_redRes`, `redRes_mul_smul_one_sub_H`, `redRes_mul_proj`, `proj_mul_redRes` —
  `(λ − H) X = X (λ − H) = 1 − P`, `X P = P X = 0`;
* `GappedPath.Y`, `contDiff_Y`, ★★ `Y_mul_H_sub` — **`Y H − H Y = K`**, pure algebra from the
  four identities above;
* `norm_one_le_one`, `norm_le_one_of_conjTranspose_mul_self`, `norm_conjTranspose_mul_mul_le` —
  unitaries have operator norm `≤ 1` (the C*-identity), so `‖U† X V‖ ≤ ‖X‖`;
* `norm_sub_le_of_hasDerivWithinAt_Icc` — the mean-value bound on `[0, T]`;
* ★★ `GappedPath.norm_sub_le_of_bounds` — the estimate with the two suprema as hypotheses;
* ★★★ `GappedPath.exists_norm_sub_le` — **Kato's comparison**.

## Honest scope

* `C` depends on the path only (through `sup ‖Y‖` and `sup ‖Ẏ + Y K‖` on `[0, 1]`, which exist by
  compactness here); `AdiabaticConstant.lean` (#166) makes it the formula
  `8 M₁/g² + 4 M₂/g² + 80 M₁²/g³` with `M₁ ≥ sup ‖Ḣ‖`, `M₂ ≥ sup ‖Ḧ‖`, through
  `norm_sub_le_of_bounds`.
* The path is `C²` (`2 ≤ n`) and the branch is an eigenvalue at every `s` (so `λ` is `C²` too,
  #159's `contDiff_lam`); the gap is uniform.
* Finite dimensions, `L2Operator` norm scope, one-sided derivatives at the ends.

References: T. Kato, "On the adiabatic theorem of quantum mechanics", J. Phys. Soc. Japan 5
(1950), §3; S. Teufel, *Adiabatic Perturbation Theory in Quantum Dynamics*, Thm 2.2 and its proof;
`AdiabaticPropagators.lean` (#161), `AdiabaticIntertwiner.lean` (#160), `RieszProjectorSmooth.lean`
(#159), `RieszProjector.lean` (#158); `specs/BACKLOG.md` #162, ~~#88~~.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Matrix ContDiff Topology
open Matrix Metric Set Complex Real Filter

noncomputable section

/-! ### Cauchy evaluations of `(z − λ)⁻¹ (z − μ)⁻¹` -/

/-- A double pole integrates to zero. -/
theorem circleIntegral_sub_inv_mul_self (c w : ℂ) (r : ℝ) :
    (∮ z in C(c, r), (z - w)⁻¹ * (z - w)⁻¹) = 0 := by
  have h : (fun z : ℂ => (z - w)⁻¹ * (z - w)⁻¹) = fun z => (z - w) ^ (-2 : ℤ) := by
    funext z
    rw [_root_.zpow_neg, zpow_two, mul_inv]
  show circleIntegral (fun z : ℂ => (z - w)⁻¹ * (z - w)⁻¹) c r = 0
  rw [h]
  exact circleIntegral.integral_sub_zpow_of_ne (by norm_num) c w r

/-- For `λ` inside and `μ` outside the circle, `∮ (z − λ)⁻¹ (z − μ)⁻¹ dz = 2πi (λ − μ)⁻¹`. -/
theorem circleIntegral_sub_inv_mul_sub_inv {c lamc μ : ℂ} {r : ℝ} (hlam : dist lamc c < r)
    (hμ : r < dist μ c) :
    (∮ z in C(c, r), (z - lamc)⁻¹ * (z - μ)⁻¹) = 2 * π * I * (lamc - μ)⁻¹ := by
  have hr : 0 ≤ r := dist_nonneg.trans hlam.le
  have hne : lamc - μ ≠ 0 := sub_ne_zero.2 fun h => by rw [h] at hlam; linarith
  have h1 : ∀ z ∈ sphere c r, z - lamc ≠ 0 := fun z hz => sub_ne_zero.2 fun h => by
    rw [mem_sphere] at hz; rw [← h] at hlam; linarith
  have h2 : ∀ z ∈ sphere c r, z - μ ≠ 0 := fun z hz => sub_ne_zero.2 fun h => by
    rw [mem_sphere] at hz; rw [← h] at hμ; linarith
  have hid : ∀ z ∈ sphere c r,
      (z - lamc)⁻¹ * (z - μ)⁻¹ = (lamc - μ)⁻¹ * ((z - lamc)⁻¹ - (z - μ)⁻¹) := by
    intro z hz
    have := h1 z hz
    have := h2 z hz
    field_simp
    ring
  rw [circleIntegral.integral_congr hr hid, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub (circleIntegrable_sub_inv_iff.2 (Or.inr fun h => by
      rw [mem_sphere, abs_of_nonneg hr] at h; linarith)) (circleIntegrable_sub_inv_iff.2 (Or.inr fun h => by
      rw [mem_sphere, abs_of_nonneg hr] at h; linarith)),
    circleIntegral_sub_inv_eq_ite hr hlam.ne, circleIntegral_sub_inv_eq_ite hr hμ.ne']
  simp only [hlam, ↓reduceIte, not_lt.2 hμ.le, sub_zero]
  ring

/-- The two cases together, for `μ` either on the branch or outside. -/
theorem circleIntegral_sub_inv_mul_sub_inv_eq {c lamc μ : ℂ} {r : ℝ} (hlam : dist lamc c < r)
    (hμ : μ = lamc ∨ r < dist μ c) :
    (∮ z in C(c, r), (z - lamc)⁻¹ * (z - μ)⁻¹)
      = if μ = lamc then 0 else 2 * π * I * (lamc - μ)⁻¹ := by
  rcases hμ with h | h
  · subst h
    simp only [↓reduceIte]
    exact circleIntegral_sub_inv_mul_self _ _ _
  · have hne : μ ≠ lamc := fun h' => by rw [h'] at h; linarith
    simp only [hne, ↓reduceIte]
    exact circleIntegral_sub_inv_mul_sub_inv hlam h

/-- The distance of two reals, in `ℂ`. -/
theorem dist_ofReal_ofReal (a b : ℝ) : dist (a : ℂ) (b : ℂ) = |a - b| := by
  rw [Complex.dist_of_im_eq (by simp)]
  simp [Real.dist_eq]

namespace Matrix

variable {N : ℕ}

/-! ### The reduced resolvent as a contour integral -/

/-- The **reduced resolvent integral** `(2πi)⁻¹ ∮_{C(c, r)} (z − λ)⁻¹ (z·1 − H)⁻¹ dz`. -/
def redResIntegral (H : Matrix (Fin N) (Fin N) ℂ) (c lamc : ℂ) (r : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (2 * π * I)⁻¹ • ∮ z in C(c, r), (z - lamc)⁻¹ • (z • (1 : Matrix (Fin N) (Fin N) ℂ) - H)⁻¹

/-- ★ **The reduced resolvent integral in the eigenbasis**: with `λ` inside the circle and every
eigenvalue either equal to `λ` or outside, it is `U diag(0 on the branch, (λ − μⱼ)⁻¹ off it) U†`. -/
theorem IsHermitian.redResIntegral_eq_conjD {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    {c lamc : ℂ} {r : ℝ} (hlam : dist lamc c < r)
    (hout : ∀ j, hH.eigC j = lamc ∨ r < dist (hH.eigC j) c) :
    redResIntegral H c lamc r
      = hH.conjD fun j => if hH.eigC j = lamc then 0 else (lamc - hH.eigC j)⁻¹ := by
  have hr : 0 ≤ r := dist_nonneg.trans hlam.le
  have hcirc : ∀ j, dist (hH.eigC j) c ≠ r := fun j => by
    rcases hout j with h | h
    · rw [h]; exact hlam.ne
    · exact h.ne'
  have hlamne : ∀ z ∈ sphere c r, z - lamc ≠ 0 := fun z hz => sub_ne_zero.2 fun h => by
    rw [mem_sphere] at hz; rw [← h] at hlam; linarith
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin N)), CircleIntegrable
      (fun z : ℂ => ((z - lamc)⁻¹ * (z - hH.eigC j)⁻¹) • hH.eigenProj j) c r := by
    intro j _
    refine ContinuousOn.circleIntegrable hr ?_
    have h1 : ContinuousOn (fun z : ℂ => (z - lamc)⁻¹ * (z - hH.eigC j)⁻¹) (sphere c r) :=
      ((continuousOn_id.sub continuousOn_const).inv₀ hlamne).mul
        ((continuousOn_id.sub continuousOn_const).inv₀ fun z hz =>
          sub_ne_zero.2 (hH.ne_eigC_of_mem_sphere hcirc hz j))
    exact h1.smul continuousOn_const
  unfold redResIntegral
  have hcongr : (∮ z in C(c, r), (z - lamc)⁻¹ • (z • (1 : Matrix (Fin N) (Fin N) ℂ) - H)⁻¹)
      = ∮ z in C(c, r), ∑ j, ((z - lamc)⁻¹ * (z - hH.eigC j)⁻¹) • hH.eigenProj j := by
    refine circleIntegral.integral_congr hr fun z hz => ?_
    rw [hH.inv_smul_one_sub_eq_sum (hH.ne_eigC_of_mem_sphere hcirc hz), Finset.smul_sum]
    simp only [smul_smul]
  rw [hcongr, circleIntegral.integral_fun_sum hint, Finset.smul_sum, IsHermitian.conjD_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [circleIntegral.integral_smul_const, smul_smul,
    circleIntegral_sub_inv_mul_sub_inv_eq hlam (hout j)]
  by_cases h : hH.eigC j = lamc
  · simp [h]
  · simp only [h, ↓reduceIte]
    rw [← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]

/-! ### Norms of unitaries -/

theorem norm_one_le_one : ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖ ≤ 1 := by
  have h : ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖ = ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖
      * ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖ := by
    have := CStarRing.norm_star_mul_self (x := (1 : Matrix (Fin N) (Fin N) ℂ))
    rwa [star_one, one_mul] at this
  nlinarith [norm_nonneg (1 : Matrix (Fin N) (Fin N) ℂ)]

/-- A matrix with `Uᴴ U = 1` has operator norm at most `1`. -/
theorem norm_le_one_of_conjTranspose_mul_self {U : Matrix (Fin N) (Fin N) ℂ} (hU : Uᴴ * U = 1) :
    ‖U‖ ≤ 1 := by
  have h : ‖U‖ * ‖U‖ = ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖ := by
    rw [← CStarRing.norm_star_mul_self]
    exact congrArg norm hU
  nlinarith [norm_nonneg U, norm_one_le_one (N := N)]

/-- Sandwiching between matrices of norm `≤ 1` does not increase the norm. -/
theorem norm_conjTranspose_mul_mul_le {U V : Matrix (Fin N) (Fin N) ℂ} (hU : ‖U‖ ≤ 1)
    (hV : ‖V‖ ≤ 1) (X : Matrix (Fin N) (Fin N) ℂ) : ‖Uᴴ * X * V‖ ≤ ‖X‖ := by
  have h1 : ‖Uᴴ * X‖ ≤ ‖X‖ := by
    calc ‖Uᴴ * X‖ ≤ ‖Uᴴ‖ * ‖X‖ := norm_mul_le _ _
      _ ≤ 1 * ‖X‖ := by
          have : ‖Uᴴ‖ = ‖U‖ := norm_star U
          rw [this]
          gcongr
      _ = ‖X‖ := one_mul _
  calc ‖Uᴴ * X * V‖ ≤ ‖Uᴴ * X‖ * ‖V‖ := norm_mul_le _ _
    _ ≤ ‖X‖ * 1 := by gcongr
    _ = ‖X‖ := mul_one _

end Matrix

/-! ### The mean-value bound on `[0, T]` -/

section MeanValue

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A function whose (one-sided) derivative within `[0, T]` is bounded by `C` moves by at most
`C · s`. -/
theorem norm_sub_le_of_hasDerivWithinAt_Icc {f f' : ℝ → F} {T C : ℝ}
    (hf : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt f (f' s) (Icc 0 T) s)
    (hb : ∀ s ∈ Icc (0 : ℝ) T, ‖f' s‖ ≤ C) : ∀ s ∈ Icc (0 : ℝ) T, ‖f s - f 0‖ ≤ C * s := by
  intro s hs
  have h := norm_image_sub_le_of_norm_deriv_right_le_segment (f := f) (f' := f') (a := 0) (b := T)
    (C := C) (fun s hs => (hf s hs).continuousWithinAt)
    (fun x hx => (hf x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hx.2) (Icc_subset_Icc_left hx.1)))
    (fun x hx => hb x (Ico_subset_Icc_self hx)) s hs
  simpa using h

end MeanValue

namespace Matrix.GappedPath

variable {N : ℕ} (Γ : GappedPath N)

/-! ### The reduced resolvent along the path -/

theorem eigC_eq_iff (s : ℝ) (j : Fin N) (x : ℝ) :
    (Γ.isHermitian s).eigC j = (x : ℂ) ↔ (Γ.isHermitian s).eigenvalues j = x := by
  change (((Γ.isHermitian s).eigenvalues j : ℝ) : ℂ) = (x : ℂ) ↔ _
  exact Complex.ofReal_inj

theorem proj_eq_conjD (s : ℝ) :
    Γ.proj s = (Γ.isHermitian s).conjD ((Γ.isHermitian s).discInd (Γ.lam s) (Γ.g / 2)) :=
  (Γ.isHermitian s).rieszProj_eq_conjD (half_pos Γ.g_pos).le (Γ.hcirc_self s)

/-- The **reduced resolvent** `X s = (λ s − H s)⁻¹ (1 − P s)`, as the contour integral
`(2πi)⁻¹ ∮_{C(λ s, g/2)} (z − λ s)⁻¹ (z − H s)⁻¹ dz`. -/
def redRes (s : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  redResIntegral (Γ.H s) (Γ.lam s) (Γ.lam s) (Γ.g / 2)

/-- The diagonal of the reduced resolvent: `0` on the branch, `(λ − μⱼ)⁻¹` off it. -/
def rr (s : ℝ) (j : Fin N) : ℂ :=
  if (Γ.isHermitian s).eigC j = (Γ.lam s : ℂ) then 0 else ((Γ.lam s : ℂ) - (Γ.isHermitian s).eigC j)⁻¹

/-- Off the branch, every eigenvalue is outside the disc of radius `g/2` about a point within `g/4`
of the branch. -/
theorem hout_near {s s₀ : ℝ} (h : |Γ.lam s - Γ.lam s₀| < Γ.g / 4) (j : Fin N) :
    (Γ.isHermitian s).eigC j = (Γ.lam s : ℂ) ∨ Γ.g / 2 < dist ((Γ.isHermitian s).eigC j) (Γ.lam s₀ : ℂ) := by
  rcases Γ.gap s j with h1 | h1
  · exact Or.inl ((Γ.eigC_eq_iff s j _).2 h1)
  · right
    rw [Γ.dist_eigC]
    have h3 := abs_sub_le ((Γ.isHermitian s).eigenvalues j) (Γ.lam s₀) (Γ.lam s)
    rw [abs_sub_comm (Γ.lam s₀) (Γ.lam s)] at h3
    linarith [Γ.g_pos]

theorem redRes_eq_conjD (s : ℝ) : Γ.redRes s = (Γ.isHermitian s).conjD (Γ.rr s) := by
  unfold redRes
  refine (Γ.isHermitian s).redResIntegral_eq_conjD ?_ ?_
  · rw [dist_self]; exact half_pos Γ.g_pos
  · exact Γ.hout_near (s₀ := s) (by rw [sub_self, abs_zero]; exact div_pos Γ.g_pos (by norm_num))

/-- **The contour freezes locally**: for `|λ s − λ s₀| < g/4`, the reduced resolvent at `s` is the
integral over the fixed circle about `λ s₀`. -/
theorem redRes_eq_near {s s₀ : ℝ} (h : |Γ.lam s - Γ.lam s₀| < Γ.g / 4) :
    Γ.redRes s = redResIntegral (Γ.H s) (Γ.lam s₀) (Γ.lam s) (Γ.g / 2) := by
  rw [Γ.redRes_eq_conjD]
  refine ((Γ.isHermitian s).redResIntegral_eq_conjD ?_ (Γ.hout_near h)).symm
  rw [dist_ofReal_ofReal]
  linarith [Γ.g_pos]

/-- ★★ **The reduced resolvent is as smooth as the path.** -/
theorem contDiff_redRes {n : ℕ∞} (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) : ContDiff ℝ n Γ.redRes := by
  have hlam : ContDiff ℝ n Γ.lam := Γ.contDiff_lam hH hex
  rw [contDiff_iff_contDiffAt]
  intro s₀
  set V : Set ℝ := {s | |Γ.lam s - Γ.lam s₀| < Γ.g / 4} with hV
  have hVo : IsOpen V :=
    isOpen_lt (continuous_abs.comp (Γ.continuous_lam.sub continuous_const)) continuous_const
  have hs₀ : s₀ ∈ V := by
    show |Γ.lam s₀ - Γ.lam s₀| < Γ.g / 4
    rw [sub_self, abs_zero]
    exact div_pos Γ.g_pos (by norm_num)
  set c : ℂ := (Γ.lam s₀ : ℂ) with hc
  set r : ℝ := Γ.g / 2 with hr
  have hr0 : 0 ≤ r := (half_pos Γ.g_pos).le
  set Φ : ℝ × ℝ → Matrix (Fin N) (Fin N) ℂ :=
    fun p => circleMap c r (2 * π * p.2) • (1 : Matrix (Fin N) (Fin N) ℂ) - Γ.H p.1 with hΦ
  have hΦc : ContDiff ℝ n Φ :=
    (contDiff_smul_of_contDiff ((contDiff_circleMap c r).comp (contDiff_const.mul contDiff_snd))
      contDiff_const).sub (hH.comp contDiff_fst)
  set ψ : ℝ × ℝ → ℂ := fun p => circleMap c r (2 * π * p.2) - (Γ.lam p.1 : ℂ) with hψ
  have hψc : ContDiff ℝ n ψ :=
    ((contDiff_circleMap c r).comp (contDiff_const.mul contDiff_snd)).sub
      (Complex.ofRealCLM.contDiff.comp (hlam.comp contDiff_fst))
  set W : Set (ℝ × ℝ) := Φ ⁻¹' {x | IsUnit x} ∩ ψ ⁻¹' {z | z ≠ 0} with hW
  have hWo : IsOpen W :=
    (Units.isOpen.preimage hΦc.continuous).inter (isOpen_ne.preimage hψc.continuous)
  have hVW : ∀ s ∈ V, ∀ u ∈ Icc (0 : ℝ) 1, (s, u) ∈ W := by
    intro s hs u _
    have hz : circleMap c r (2 * π * u) ∈ sphere c r := circleMap_mem_sphere c hr0 _
    refine ⟨Γ.isUnit_smul_one_sub ((Γ.isHermitian s).ne_eigC_of_mem_sphere (Γ.hcirc_near hs) hz),
      ?_⟩
    show circleMap c r (2 * π * u) - (Γ.lam s : ℂ) ≠ 0
    refine sub_ne_zero.2 fun h => ?_
    rw [mem_sphere] at hz
    rw [h, hc, dist_ofReal_ofReal] at hz
    have hs' : |Γ.lam s - Γ.lam s₀| < Γ.g / 4 := hs
    linarith [Γ.g_pos]
  have hsm : ContDiffOn ℝ n (fun s => redResIntegral (Γ.H s) c (Γ.lam s) r) V := by
    unfold redResIntegral
    refine ContDiffOn.const_smul _ ?_
    refine contDiffOn_circleIntegral hVo c r hWo hVW ?_
    exact contDiffOn_smul_of_contDiffOn (hψc.contDiffOn.inv fun p hp => hp.2)
      (contDiffOn_inv_comp hΦc fun p hp => hp.1)
  refine (hsm.contDiffAt (hVo.mem_nhds hs₀)).congr_of_eventuallyEq ?_
  filter_upwards [hVo.mem_nhds hs₀] with s hs
  exact Γ.redRes_eq_near hs

/-! ### The algebra of the reduced resolvent -/

theorem redRes_mul_proj (s : ℝ) : Γ.redRes s * Γ.proj s = 0 := by
  rw [Γ.redRes_eq_conjD, Γ.proj_eq_conjD, IsHermitian.conjD_mul_conjD]
  have : Γ.rr s * (Γ.isHermitian s).discInd (Γ.lam s) (Γ.g / 2) = 0 := by
    funext j
    simp only [Pi.mul_apply, Pi.zero_apply, rr, Γ.discInd_eq, Γ.eigC_eq_iff]
    by_cases h : (Γ.isHermitian s).eigenvalues j = Γ.lam s <;> simp [h]
  rw [this]
  unfold IsHermitian.conjD
  simp

theorem proj_mul_redRes (s : ℝ) : Γ.proj s * Γ.redRes s = 0 := by
  rw [Γ.redRes_eq_conjD, Γ.proj_eq_conjD, IsHermitian.conjD_mul_conjD, mul_comm]
  have : Γ.rr s * (Γ.isHermitian s).discInd (Γ.lam s) (Γ.g / 2) = 0 := by
    funext j
    simp only [Pi.mul_apply, Pi.zero_apply, rr, Γ.discInd_eq, Γ.eigC_eq_iff]
    by_cases h : (Γ.isHermitian s).eigenvalues j = Γ.lam s <;> simp [h]
  rw [this]
  unfold IsHermitian.conjD
  simp

/-- The diagonal identity `(λ − μⱼ) · rrⱼ = 1 − 𝟙_branch`. -/
theorem conjD_lam_sub_mul_rr (s : ℝ) :
    (Γ.isHermitian s).conjD ((fun j => (Γ.lam s : ℂ) - (Γ.isHermitian s).eigC j) * Γ.rr s)
      = 1 - Γ.proj s := by
  rw [Γ.proj_eq_conjD, ← IsHermitian.conjD_one (Γ.isHermitian s), ← IsHermitian.conjD_sub]
  congr 1
  funext j
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply, rr, Γ.discInd_eq]
  by_cases h : (Γ.isHermitian s).eigenvalues j = Γ.lam s
  · simp [h, Γ.eigC_eq_iff]
  · have h' : (Γ.isHermitian s).eigC j ≠ (Γ.lam s : ℂ) := fun h'' => h ((Γ.eigC_eq_iff s j _).1 h'')
    simp only [h', h, ↓reduceIte, sub_zero]
    exact mul_inv_cancel₀ (sub_ne_zero.2 (Ne.symm h'))

/-- `(λ − H) X = 1 − P`. -/
theorem smul_one_sub_H_mul_redRes (s : ℝ) :
    ((Γ.lam s : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - Γ.H s) * Γ.redRes s = 1 - Γ.proj s := by
  rw [(Γ.isHermitian s).smul_one_sub_eq_conjD, Γ.redRes_eq_conjD, IsHermitian.conjD_mul_conjD]
  exact Γ.conjD_lam_sub_mul_rr s

/-- `X (λ − H) = 1 − P`. -/
theorem redRes_mul_smul_one_sub_H (s : ℝ) :
    Γ.redRes s * ((Γ.lam s : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - Γ.H s) = 1 - Γ.proj s := by
  rw [(Γ.isHermitian s).smul_one_sub_eq_conjD, Γ.redRes_eq_conjD, IsHermitian.conjD_mul_conjD,
    mul_comm]
  exact Γ.conjD_lam_sub_mul_rr s

/-! ### The family `Y` with `Y H − H Y = K` -/

/-- Kato's `Y = X Ṗ P + P Ṗ X`. -/
def Y (s : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Γ.redRes s * deriv Γ.proj s * Γ.proj s + Γ.proj s * deriv Γ.proj s * Γ.redRes s

/-- ★★ **`Y H − H Y = K`**: pure algebra from `(λ − H) X = X (λ − H) = 1 − P` and `(λ − H) P = 0`. -/
theorem Y_mul_H_sub (s : ℝ) : Γ.Y s * Γ.H s - Γ.H s * Γ.Y s = Γ.K s := by
  set B : Matrix (Fin N) (Fin N) ℂ := (Γ.lam s : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - Γ.H s
    with hB
  set R := Γ.redRes s
  set P := Γ.proj s
  set P' := deriv Γ.proj s
  have hBR : B * R = 1 - P := Γ.smul_one_sub_H_mul_redRes s
  have hRB : R * B = 1 - P := Γ.redRes_mul_smul_one_sub_H s
  have hBP : B * P = 0 := by
    rw [hB, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Γ.H_mul_proj, sub_self]
  have hPB : P * B = 0 := by
    rw [hB, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Γ.proj_mul_H, sub_self]
  have hH' : Γ.H s = (Γ.lam s : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - B := by
    rw [hB, sub_sub_cancel]
  have e1 : Γ.Y s * Γ.H s - Γ.H s * Γ.Y s = B * Γ.Y s - Γ.Y s * B := by
    rw [hH', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
    abel
  have e2 : B * (R * P' * P) = (1 - P) * P' * P := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hBR]
  have e3 : B * (P * P' * R) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hBP, Matrix.zero_mul, Matrix.zero_mul]
  have e4 : R * P' * P * B = 0 := by
    rw [Matrix.mul_assoc, hPB, Matrix.mul_zero]
  have e5 : P * P' * R * B = P * P' * (1 - P) := by
    rw [Matrix.mul_assoc, hRB]
  rw [e1]
  show B * (R * P' * P + P * P' * R) - (R * P' * P + P * P' * R) * B = P' * P - P * P'
  rw [Matrix.mul_add, Matrix.add_mul, e2, e3, e4, e5]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
  abel

/-- `Y` is `C¹` along a gapped `C²` path. -/
theorem contDiff_Y {n : ℕ∞} (hn : 2 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) : ContDiff ℝ 1 Γ.Y := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast le_trans (by norm_num : (1 : ℕ∞) ≤ 2) hn
  have hR : ContDiff ℝ 1 Γ.redRes := (Γ.contDiff_redRes hH hex).of_le hn1
  have hP : ContDiff ℝ 1 Γ.proj := (Γ.contDiff_proj hH).of_le hn1
  have hP2 : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) Γ.proj := by
    rw [one_add_one_eq_two]
    have h2 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ n := WithTop.coe_le_coe.2 hn
    exact (Γ.contDiff_proj hH).of_le (by simpa using h2)
  have hP' : ContDiff ℝ 1 (deriv Γ.proj) := (contDiff_succ_iff_deriv.1 hP2).2.2
  exact ((hR.mul hP').mul hP).add ((hP.mul hP').mul hR)

/-! ### Kato's comparison -/

/-- ★★ **The estimate behind Kato's comparison**, with the two suprema as explicit hypotheses:
if `‖Y‖ ≤ MY` and `‖Ẏ + Y K‖ ≤ ME` on `[0, 1]`, then `‖U_T(s) − U_A(s)‖ ≤ (2 MY + ME) / T`. -/
theorem norm_sub_le_of_bounds {n : ℕ∞} (hn : 2 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) {MY ME : ℝ}
    (hMY : ∀ s ∈ Icc (0 : ℝ) 1, ‖Γ.Y s‖ ≤ MY)
    (hME : ∀ s ∈ Icc (0 : ℝ) 1, ‖deriv Γ.Y s + Γ.Y s * Γ.K s‖ ≤ ME) {T : ℝ} (hT : 0 < T)
    {UT UA : ℝ → Matrix (Fin N) (Fin N) ℂ} (hUT : Γ.IsPhysPropagator T UT)
    (hUA : Γ.IsAdPropagator T UA) : ∀ s ∈ Icc (0 : ℝ) 1, ‖UT s - UA s‖ ≤ (2 * MY + ME) / T := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hY : ContDiff ℝ 1 Γ.Y := Γ.contDiff_Y hn hH hex
  set E : ℝ → Matrix (Fin N) (Fin N) ℂ := fun s => deriv Γ.Y s + Γ.Y s * Γ.K s with hE
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  intro s hs
  -- unitarity
  have hUTn : ∀ s ∈ Icc (0 : ℝ) 1, ‖UT s‖ ≤ 1 := fun s hs =>
    norm_le_one_of_conjTranspose_mul_self (hUT.conjTranspose_mul_self s hs)
  have hUAn : ∀ s ∈ Icc (0 : ℝ) 1, ‖UA s‖ ≤ 1 := fun s hs =>
    norm_le_one_of_conjTranspose_mul_self (hUA.conjTranspose_mul_self hn1 hH s hs)
  have hsand : ∀ s ∈ Icc (0 : ℝ) 1, ∀ X : Matrix (Fin N) (Fin N) ℂ,
      ‖(UT s)ᴴ * X * UA s‖ ≤ ‖X‖ := fun s hs X =>
    norm_conjTranspose_mul_mul_le (hUTn s hs) (hUAn s hs) X
  set iT : ℂ := I * (T : ℂ) with hiT
  have hiT0 : iT ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hT.ne')
  have hiTn : ‖iT⁻¹‖ = T⁻¹ := by
    rw [norm_inv, hiT, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hT]
  have hM : ∀ s, Γ.physGen T s = (-iT) • Γ.H s := fun s => by
    simp only [physGen, hiT, neg_mul]
  -- the three families
  set W : ℝ → Matrix (Fin N) (Fin N) ℂ := fun s => (UT s)ᴴ * UA s with hWdef
  set G : ℝ → Matrix (Fin N) (Fin N) ℂ := fun s => (UT s)ᴴ * Γ.Y s * UA s with hGdef
  set F : ℝ → Matrix (Fin N) (Fin N) ℂ := fun s => W s + iT⁻¹ • G s with hFdef
  have hF : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt F (iT⁻¹ • ((UT s)ᴴ * E s * UA s)) (Icc 0 1) s := by
    intro s hs
    have hUTd := hUT.hasDerivWithinAt s hs
    have hUAd := hUA.hasDerivWithinAt s hs
    have hYd : HasDerivWithinAt Γ.Y (deriv Γ.Y s) (Icc 0 1) s :=
      (hY.differentiable one_ne_zero s).hasDerivAt.hasDerivWithinAt
    have hKY := Γ.Y_mul_H_sub s
    have hW' : HasDerivWithinAt W ((UT s)ᴴ * Γ.K s * UA s) (Icc 0 1) s := by
      refine (hUTd.matrixConjTranspose.mul hUAd).congr_deriv ?_
      rw [conjTranspose_mul, Γ.conjTranspose_physGen, adGen]
      noncomm_ring
    have hG' : HasDerivWithinAt G
        ((-iT) • ((UT s)ᴴ * Γ.K s * UA s) + (UT s)ᴴ * E s * UA s) (Icc 0 1) s := by
      refine ((hUTd.matrixConjTranspose.mul hYd).mul hUAd).congr_deriv ?_
      simp only [Pi.mul_apply]
      rw [conjTranspose_mul, Γ.conjTranspose_physGen, adGen, hM]
      have hYM : Γ.Y s * ((-iT) • Γ.H s) - ((-iT) • Γ.H s) * Γ.Y s = (-iT) • Γ.K s := by
        rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, hKY]
      rw [show (-iT) • ((UT s)ᴴ * Γ.K s * UA s) = (UT s)ᴴ * ((-iT) • Γ.K s) * UA s by
        rw [Matrix.mul_smul, Matrix.smul_mul], ← hYM]
      simp only [hE]
      noncomm_ring
    refine (hW'.add (hG'.const_smul iT⁻¹)).congr_deriv ?_
    rw [smul_add, smul_smul, mul_neg, inv_mul_cancel₀ hiT0, neg_one_smul, add_neg_cancel_left]
  have hFb : ∀ s ∈ Icc (0 : ℝ) 1, ‖iT⁻¹ • ((UT s)ᴴ * E s * UA s)‖ ≤ T⁻¹ * ME := by
    intro s hs
    rw [norm_smul, hiTn]
    exact mul_le_mul_of_nonneg_left ((hsand s hs _).trans (hME s hs)) (inv_nonneg.2 hT.le)
  have hFs := norm_sub_le_of_hasDerivWithinAt_Icc hF hFb s hs
  have hF0 : F 0 = 1 + iT⁻¹ • Γ.Y 0 := by
    simp only [hFdef, hWdef, hGdef, hUT.init, hUA.init, conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one]
  have hW1 : W s - 1 = (F s - F 0) - iT⁻¹ • (G s - Γ.Y 0) := by
    rw [hF0]
    simp only [hFdef, smul_sub]
    abel
  have hGn : ‖G s‖ ≤ MY := (hsand s hs _).trans (hMY s hs)
  have hWn : ‖W s - 1‖ ≤ (2 * MY + ME) / T := by
    calc ‖W s - 1‖ ≤ ‖F s - F 0‖ + ‖iT⁻¹ • (G s - Γ.Y 0)‖ := by rw [hW1]; exact norm_sub_le _ _
      _ ≤ T⁻¹ * ME * s + T⁻¹ * (‖G s‖ + ‖Γ.Y 0‖) := by
          rw [norm_smul, hiTn]
          gcongr
          exact norm_sub_le _ _
      _ ≤ T⁻¹ * ME * 1 + T⁻¹ * (MY + MY) := by
          have hME0 : 0 ≤ ME := (norm_nonneg _).trans (hME 0 h01)
          exact add_le_add (mul_le_mul_of_nonneg_left hs.2 (mul_nonneg (inv_nonneg.2 hT.le) hME0))
            (mul_le_mul_of_nonneg_left (add_le_add hGn (hMY 0 h01)) (inv_nonneg.2 hT.le))
      _ = (2 * MY + ME) / T := by ring
  have hdiff : UA s - UT s = UT s * (W s - 1) := by
    rw [Matrix.mul_sub, Matrix.mul_one, hWdef, ← Matrix.mul_assoc, hUT.mul_conjTranspose s hs,
      Matrix.one_mul]
  calc ‖UT s - UA s‖ = ‖UA s - UT s‖ := norm_sub_rev _ _
    _ = ‖UT s * (W s - 1)‖ := by rw [hdiff]
    _ ≤ ‖UT s‖ * ‖W s - 1‖ := norm_mul_le _ _
    _ ≤ 1 * ((2 * MY + ME) / T) := by gcongr; exact hUTn s hs
    _ = (2 * MY + ME) / T := one_mul _

/-- ★★★ **Kato's comparison.** Along a gapped `C²` path whose branch is an eigenvalue, there is a
constant `C` such that, for every speed `T > 0`, the physical and the adiabatic propagators satisfy
`‖U_T(s) − U_A(s)‖ ≤ C / T` for all `s ∈ [0, 1]`. (`AdiabaticConstant.lean` makes `C` explicit.) -/
theorem exists_norm_sub_le {n : ℕ∞} (hn : 2 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T → ∀ UT UA : ℝ → Matrix (Fin N) (Fin N) ℂ,
      Γ.IsPhysPropagator T UT → Γ.IsAdPropagator T UA →
      ∀ s ∈ Icc (0 : ℝ) 1, ‖UT s - UA s‖ ≤ C / T := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hY : ContDiff ℝ 1 Γ.Y := Γ.contDiff_Y hn hH hex
  have hYc : Continuous Γ.Y := hY.continuous
  have hY' : Continuous (deriv Γ.Y) := hY.continuous_deriv le_rfl
  have hK : Continuous Γ.K := Γ.continuous_K hn1 hH
  have hEc : Continuous fun s => deriv Γ.Y s + Γ.Y s * Γ.K s := hY'.add (hYc.mul hK)
  obtain ⟨MY, hMY⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hYc.continuousOn (s := Icc (0 : ℝ) 1))
  obtain ⟨ME, hME⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hEc.continuousOn (s := Icc (0 : ℝ) 1))
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hMY0 : 0 ≤ MY := (norm_nonneg _).trans (hMY 0 h01)
  have hME0 : 0 ≤ ME := (norm_nonneg _).trans (hME 0 h01)
  exact ⟨2 * MY + ME, by positivity, fun T hT UT UA hUT hUA =>
    Γ.norm_sub_le_of_bounds hn hH hex hMY hME hT hUT hUA⟩

end Matrix.GappedPath

end

end
