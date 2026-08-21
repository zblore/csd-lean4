/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF6.LindbladSemigroup
public import CsdLean4.Mathlib.Analysis.NormedSpace.TrotterGeneral
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Positivity of the Lindblad semigroup — the exponentiated CP tier (Q16's gate)

**Category:** 4-LF (open-system dynamics — the half `LF6/LindbladSemigroup.lean`
declared out of reach). That module's scope block deferred positivity of
`e^{tℒ}` as needing "a Lie–Trotter/Euler-approximant limit theorem or resolvent
positivity, neither of which Mathlib has". The 2026-08-20 gate re-check found
the label stale, and this module closes the gap in-corpus. Scoped first in
`specs/cp-semigroup-plan.md`.

The route:

* **The drift needs no Trotter at all.** For Hermitian `H` the generator
  splits as `ℒ = drift + jump` (`lindbladGeneratorCLM_split`) with
  `drift ρ = Gρ + ρG†`, `G = −iH − ½ΣL†L` (`gkslG`). Left- and
  right-multiplication commute, so
  `e^{t·drift} ρ = e^{tG} ρ e^{tG†}` (`exp_smul_driftCLM_apply`) —
  conjugation, positive at every `t` (`exp_smul_driftCLM_posSemidef`).
* **The jump exponential is a positive series.** `jump ρ = ΣLρL†` preserves
  PSD (the generator-tier Choi–Kraus witness), every series term of
  `e^{t·jump}` is PSD for `t ≥ 0`, and PSD passes to limits
  (`posSemidef_of_tendsto`, via the `dotProduct_mulVec` characterisation) —
  `exp_smul_jumpCLM_posSemidef`.
* **Assemble by the Banach-algebra Lie–Trotter formula**
  (`NormedSpace.trotter_product`, the de-skewed staging brick): `e^{tℒ}` is a
  limit of products of the two positive flows, products of PSD-preserving
  maps preserve PSD (`step_pow_posSemidef`), and the limit is PSD.
* ★★ `lindbladSemigroup_posSemidef` — **the flow of every GKSL generator
  with Hermitian `H` is a positive map at every `t ≥ 0`.**
* ★ `lindbladSemigroup_amplified_posSemidef` — **the complete-positivity
  shape**: the amplified generator `(1 ⊗ H, 1 ⊗ Lₖ)` is itself GKSL, so
  positivity survives every ancilla amplification of the generator — a
  literal instantiation.
* ★★ `idTensor_lindbladSemigroup` + ★★ `lindbladSemigroup_completelyPositive`
  — **the `id ⊗ Φ` identification (Q23, 2026-08-20)**: the amplified
  generator's flow IS `id ⊗ Φₜ` (blockwise action, exponential-series
  transport of the blockwise generator through `expCLM_apply_hasSum`), so the
  amplified positivity is **complete positivity of `Φₜ` in so many words**.
  *Supersession record*: this was the module's declared boundary at the Q16
  CP-brick landing (the missing block-structure lemma); Q23 delivered it the
  same week and the boundary retired — see `specs/BACKLOG.md` (Q23).

## References

`specs/cp-semigroup-plan.md` (scoping); `specs/BACKLOG.md` (Q16 gate
re-check, triage 2026-08-20); `LF6/LindbladSemigroup.lean` (the flow);
`LF6/LindbladGenerator.lean` (`lindblad_dissipation_posSemidef`);
`Mathlib/Analysis/NormedSpace/TrotterGeneral.lean` (`trotter_product`);
`specs/future-work.md` (LF6-9).
-/

@[expose] public section

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker

namespace CSD.LF6

variable {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [Fintype ι]

/-! ### PSD is closed under nonnegative scaling and under limits -/

omit [DecidableEq n] in
/-- Nonnegative real scaling preserves positive semidefiniteness
(instance-free form). -/
lemma posSemidef_real_smul {M : Matrix n n ℂ} (hM : M.PosSemidef) {t : ℝ}
    (ht : 0 ≤ t) : (t • M).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · show (t • M)ᴴ = t • M
    rw [Matrix.conjTranspose_smul, star_trivial, hM.1.eq]
  · have hq := hM.dotProduct_mulVec_nonneg x
    have harg : star x ⬝ᵥ ((t • M) *ᵥ x) = (t : ℂ) * (star x ⬝ᵥ (M *ᵥ x)) := by
      rw [Matrix.smul_mulVec, dotProduct_smul, Complex.real_smul]
    rw [harg]
    obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hq
    refine Complex.nonneg_iff.mpr ⟨?_, ?_⟩
    · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero]
      exact mul_nonneg ht hre
    · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        add_zero, ← him, mul_zero]

omit [DecidableEq n] in
/-- The quadratic form of a matrix at a fixed vector, as a linear
functional. -/
noncomputable def quadFormL (x : n → ℂ) : Matrix n n ℂ →ₗ[ℂ] ℂ where
  toFun M := star x ⬝ᵥ (M *ᵥ x)
  map_add' M N := by rw [Matrix.add_mulVec, dotProduct_add]
  map_smul' c M := by
    rw [RingHom.id_apply, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul]

omit [DecidableEq n] in
/-- **PSD is closed under limits**: the limit of a sequence of positive
semidefinite matrices is positive semidefinite. Hermiticity passes to the
limit by continuity of `star`; the quadratic form's real part stays
nonnegative by `ge_of_tendsto`, and its imaginary part stays zero. -/
lemma posSemidef_of_tendsto {g : ℕ → Matrix n n ℂ} {S : Matrix n n ℂ}
    (hg : Filter.Tendsto g Filter.atTop (nhds S))
    (h : ∀ i, (g i).PosSemidef) : S.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · have hstar : Filter.Tendsto (fun i => star (g i)) Filter.atTop
        (nhds (star S)) := (continuous_star.tendsto S).comp hg
    have heq : (fun i => star (g i)) = g := by
      funext i
      rw [Matrix.star_eq_conjTranspose, (h i).1.eq]
    rw [heq] at hstar
    have hSS := tendsto_nhds_unique hstar hg
    rw [Matrix.IsHermitian, ← Matrix.star_eq_conjTranspose, hSS]
  · have hq : Filter.Tendsto (fun i => quadFormL x (g i)) Filter.atTop
        (nhds (quadFormL x S)) :=
      ((LinearMap.toContinuousLinearMap (quadFormL x)).continuous.tendsto
        S).comp hg
    have hterm : ∀ i, 0 ≤ quadFormL x (g i) := fun i =>
      (h i).dotProduct_mulVec_nonneg x
    have hre : Filter.Tendsto (fun i => (quadFormL x (g i)).re) Filter.atTop
        (nhds ((quadFormL x S).re)) :=
      (Complex.continuous_re.tendsto _).comp hq
    have him : Filter.Tendsto (fun i => (quadFormL x (g i)).im) Filter.atTop
        (nhds ((quadFormL x S).im)) :=
      (Complex.continuous_im.tendsto _).comp hq
    have hre0 : 0 ≤ (quadFormL x S).re :=
      ge_of_tendsto' hre fun i => (Complex.nonneg_iff.mp (hterm i)).1
    have him0 : (fun i => (quadFormL x (g i)).im) = fun _ => (0 : ℝ) := by
      funext i
      exact ((Complex.nonneg_iff.mp (hterm i)).2).symm
    rw [him0] at him
    have himS : (quadFormL x S).im = 0 :=
      tendsto_nhds_unique him tendsto_const_nhds
    exact Complex.nonneg_iff.mpr ⟨hre0, himS.symm⟩

/-! ### Left and right multiplication as continuous endomorphisms -/

/-- Left multiplication as a continuous `ℝ`-endomorphism of matrix space. -/
noncomputable def mulLeftCLM (A : Matrix n n ℂ) :
    Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ A)).restrictScalars ℝ

/-- Right multiplication as a continuous `ℝ`-endomorphism of matrix space. -/
noncomputable def mulRightCLM (B : Matrix n n ℂ) :
    Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℂ B)).restrictScalars ℝ

@[simp] lemma mulLeftCLM_apply (A ρ : Matrix n n ℂ) :
    mulLeftCLM A ρ = A * ρ := rfl

@[simp] lemma mulRightCLM_apply (B ρ : Matrix n n ℂ) :
    mulRightCLM B ρ = ρ * B := rfl

/-- The exponential of any endomorphism, applied: the series form (the
`lindbladSemigroup_apply_hasSum` idiom, for an arbitrary endomorphism). -/
lemma expCLM_apply_hasSum (T : Matrix n n ℂ →L[ℝ] Matrix n n ℂ)
    (ρ : Matrix n n ℂ) :
    HasSum (fun m : ℕ => (((m.factorial : ℝ))⁻¹ • T ^ m) ρ) (exp T ρ) := by
  have hexp : exp T = ∑' m : ℕ, ((m.factorial : ℝ))⁻¹ • T ^ m := by
    rw [exp_eq_tsum (𝕂 := ℝ)]
  have h1 := (expSeries_summable' (𝕂 := ℝ) T).hasSum
  rw [← hexp] at h1
  exact h1.mapL (ContinuousLinearMap.apply ℝ (Matrix n n ℂ) ρ)

/-- Powers of a scaled left multiplication, applied. -/
lemma smul_mulLeftCLM_pow_apply (t : ℝ) (A : Matrix n n ℂ) (m : ℕ)
    (ρ : Matrix n n ℂ) :
    ((t • mulLeftCLM A) ^ m) ρ = (t • A) ^ m * ρ := by
  induction m generalizing ρ with
  | zero => simp
  | succ m ih =>
    have hstep : (t • mulLeftCLM A) ρ = t • (A * ρ) := by
      rw [_root_.smul_apply, mulLeftCLM_apply]
    calc ((t • mulLeftCLM A) ^ (m + 1)) ρ
        = ((t • mulLeftCLM A) ^ m) ((t • mulLeftCLM A) ρ) := by
          rw [pow_succ]; rfl
      _ = (t • A) ^ m * (t • (A * ρ)) := by rw [hstep, ih]
      _ = (t • A) ^ (m + 1) * ρ := by
          rw [pow_succ, Matrix.mul_assoc, smul_mul_assoc]

/-- Powers of a scaled right multiplication, applied. -/
lemma smul_mulRightCLM_pow_apply (t : ℝ) (B : Matrix n n ℂ) (m : ℕ)
    (ρ : Matrix n n ℂ) :
    ((t • mulRightCLM B) ^ m) ρ = ρ * (t • B) ^ m := by
  induction m generalizing ρ with
  | zero => simp
  | succ m ih =>
    have hstep : (t • mulRightCLM B) ρ = t • (ρ * B) := by
      rw [_root_.smul_apply, mulRightCLM_apply]
    calc ((t • mulRightCLM B) ^ (m + 1)) ρ
        = ((t • mulRightCLM B) ^ m) ((t • mulRightCLM B) ρ) := by
          rw [pow_succ]; rfl
      _ = (t • (ρ * B)) * (t • B) ^ m := by rw [hstep, ih]
      _ = ρ * (t • B) ^ (m + 1) := by
          rw [pow_succ', ← Matrix.mul_assoc, mul_smul_comm]

/-- The exponential of a scaled left multiplication is left multiplication by
the matrix exponential. -/
theorem exp_smul_mulLeftCLM_apply (t : ℝ) (A ρ : Matrix n n ℂ) :
    exp (t • mulLeftCLM A) ρ = exp (t • A) * ρ := by
  have hL := expCLM_apply_hasSum (t • mulLeftCLM A) ρ
  have hmat : HasSum (fun m : ℕ => ((m.factorial : ℝ))⁻¹ • (t • A) ^ m)
      (exp (t • A)) := exp_series_hasSum_exp' (𝕂 := ℝ) _
  have hR := hmat.mapL (mulRightCLM ρ)
  have hLterms : (fun m : ℕ =>
      (((m.factorial : ℝ))⁻¹ • (t • mulLeftCLM A) ^ m) ρ)
      = fun m : ℕ => ((m.factorial : ℝ))⁻¹ • ((t • A) ^ m * ρ) := by
    funext m
    rw [_root_.smul_apply, smul_mulLeftCLM_pow_apply]
  have hRterms : (fun m : ℕ =>
      mulRightCLM ρ (((m.factorial : ℝ))⁻¹ • (t • A) ^ m))
      = fun m : ℕ => ((m.factorial : ℝ))⁻¹ • ((t • A) ^ m * ρ) := by
    funext m
    rw [map_smul, mulRightCLM_apply]
  rw [hLterms] at hL
  rw [hRterms] at hR
  have hEq := hL.unique hR
  rw [hEq, mulRightCLM_apply]

/-- The exponential of a scaled right multiplication is right multiplication
by the matrix exponential. -/
theorem exp_smul_mulRightCLM_apply (t : ℝ) (B ρ : Matrix n n ℂ) :
    exp (t • mulRightCLM B) ρ = ρ * exp (t • B) := by
  have hL := expCLM_apply_hasSum (t • mulRightCLM B) ρ
  have hmat : HasSum (fun m : ℕ => ((m.factorial : ℝ))⁻¹ • (t • B) ^ m)
      (exp (t • B)) := exp_series_hasSum_exp' (𝕂 := ℝ) _
  have hR := hmat.mapL (mulLeftCLM ρ)
  have hLterms : (fun m : ℕ =>
      (((m.factorial : ℝ))⁻¹ • (t • mulRightCLM B) ^ m) ρ)
      = fun m : ℕ => ((m.factorial : ℝ))⁻¹ • (ρ * (t • B) ^ m) := by
    funext m
    rw [_root_.smul_apply, smul_mulRightCLM_pow_apply]
  have hRterms : (fun m : ℕ =>
      mulLeftCLM ρ (((m.factorial : ℝ))⁻¹ • (t • B) ^ m))
      = fun m : ℕ => ((m.factorial : ℝ))⁻¹ • (ρ * (t • B) ^ m) := by
    funext m
    rw [map_smul, mulLeftCLM_apply]
  rw [hLterms] at hL
  rw [hRterms] at hR
  have hEq := hL.unique hR
  rw [hEq, mulLeftCLM_apply]

/-! ### The drift/jump split of the GKSL generator -/

/-- The GKSL **drift matrix** `G = −iH − ½ΣL†L`: the non-Hermitian effective
Hamiltonian whose conjugation action is the drift half of the generator. -/
noncomputable def gkslG (H : Matrix n n ℂ) (L : ι → Matrix n n ℂ) :
    Matrix n n ℂ :=
  (-Complex.I) • H - (1 / 2 : ℂ) • ∑ k, (L k)ᴴ * L k

/-- The drift half of the generator: `ρ ↦ Gρ + ρG†`. -/
noncomputable def driftCLM (H : Matrix n n ℂ) (L : ι → Matrix n n ℂ) :
    Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  mulLeftCLM (gkslG H L) + mulRightCLM ((gkslG H L)ᴴ)

/-- The jump half of the generator: `ρ ↦ ΣLρL†`. -/
noncomputable def jumpCLM (L : ι → Matrix n n ℂ) :
    Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  ∑ k, mulLeftCLM (L k) * mulRightCLM ((L k)ᴴ)

lemma driftCLM_apply (H : Matrix n n ℂ) (L : ι → Matrix n n ℂ)
    (ρ : Matrix n n ℂ) :
    driftCLM H L ρ = gkslG H L * ρ + ρ * (gkslG H L)ᴴ := by
  rw [driftCLM, _root_.add_apply, mulLeftCLM_apply,
    mulRightCLM_apply]

lemma jumpCLM_apply (L : ι → Matrix n n ℂ) (ρ : Matrix n n ℂ) :
    jumpCLM L ρ = ∑ k, L k * ρ * (L k)ᴴ := by
  rw [jumpCLM, _root_.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (mulLeftCLM (L k) * mulRightCLM ((L k)ᴴ)) ρ
      = mulLeftCLM (L k) (mulRightCLM ((L k)ᴴ) ρ) from rfl,
    mulRightCLM_apply, mulLeftCLM_apply, Matrix.mul_assoc]

/-- **The drift/jump split** (Hermitian `H`): the GKSL generator is the drift
conjugation plus the Kraus jump part. -/
theorem lindbladGeneratorCLM_split {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (L : ι → Matrix n n ℂ) :
    lindbladGeneratorCLM H L = driftCLM H L + jumpCLM L := by
  refine ContinuousLinearMap.ext fun ρ => ?_
  rw [_root_.add_apply, lindbladGeneratorCLM_apply,
    driftCLM_apply, jumpCLM_apply, lindbladGenerator]
  have hGH : (gkslG H L)ᴴ
      = Complex.I • H - (1 / 2 : ℂ) • ∑ k, (L k)ᴴ * L k := by
    rw [gkslG, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_smul, hH.eq]
    congr 1
    · rw [show star (-Complex.I) = Complex.I from by simp]
    · rw [show star (1 / 2 : ℂ) = 1 / 2 from by norm_num,
        Matrix.conjTranspose_sum]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [hGH, gkslG]
  simp only [lindbladDissipator]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]
  simp only [Matrix.sub_mul, Matrix.mul_sub, smul_mul_assoc, mul_smul_comm]
  module

/-! ### The two flows are positive -/

/-- **The drift flow is conjugation**: `e^{t·drift} ρ = e^{tG} ρ e^{tG†}`. -/
theorem exp_smul_driftCLM_apply (H : Matrix n n ℂ) (L : ι → Matrix n n ℂ)
    (t : ℝ) (ρ : Matrix n n ℂ) :
    exp (t • driftCLM H L) ρ
      = exp (t • gkslG H L) * ρ * exp (t • (gkslG H L)ᴴ) := by
  have hsplit : t • driftCLM H L
      = t • mulLeftCLM (gkslG H L) + t • mulRightCLM ((gkslG H L)ᴴ) := by
    rw [driftCLM, smul_add]
  have hcomm : Commute (t • mulLeftCLM (gkslG H L))
      (t • mulRightCLM ((gkslG H L)ᴴ)) := by
    refine ContinuousLinearMap.ext fun σ => ?_
    show (t • mulLeftCLM (gkslG H L))
        ((t • mulRightCLM ((gkslG H L)ᴴ)) σ)
      = (t • mulRightCLM ((gkslG H L)ᴴ))
        ((t • mulLeftCLM (gkslG H L)) σ)
    simp only [_root_.smul_apply, map_smul, mulLeftCLM_apply,
      mulRightCLM_apply]
    rw [Matrix.mul_assoc]
  have hfact : exp (t • driftCLM H L)
      = exp (t • mulLeftCLM (gkslG H L))
        * exp (t • mulRightCLM ((gkslG H L)ᴴ)) := by
    rw [hsplit]
    exact exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hcomm
      ((expSeries_radius_eq_top ℝ
        (Matrix n n ℂ →L[ℝ] Matrix n n ℂ)).symm ▸ edist_lt_top _ _)
      ((expSeries_radius_eq_top ℝ
        (Matrix n n ℂ →L[ℝ] Matrix n n ℂ)).symm ▸ edist_lt_top _ _)
  rw [hfact,
    show (exp (t • mulLeftCLM (gkslG H L))
        * exp (t • mulRightCLM ((gkslG H L)ᴴ))) ρ
      = exp (t • mulLeftCLM (gkslG H L))
          (exp (t • mulRightCLM ((gkslG H L)ᴴ)) ρ) from rfl,
    exp_smul_mulRightCLM_apply, exp_smul_mulLeftCLM_apply, Matrix.mul_assoc]

/-- **The drift flow is positive at every time** — it is conjugation by
`e^{tG}`. -/
theorem exp_smul_driftCLM_posSemidef (H : Matrix n n ℂ)
    (L : ι → Matrix n n ℂ) (t : ℝ) {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    (exp (t • driftCLM H L) ρ).PosSemidef := by
  rw [exp_smul_driftCLM_apply]
  have hsm : t • (gkslG H L)ᴴ = (t • gkslG H L)ᴴ := by
    rw [Matrix.conjTranspose_smul, star_trivial]
  rw [hsm, Matrix.exp_conjTranspose]
  exact hρ.mul_mul_conjTranspose_same _

/-- The jump part preserves positive semidefiniteness (the generator-tier
Choi–Kraus witness, at the endomorphism level). -/
lemma jumpCLM_posSemidef_apply (L : ι → Matrix n n ℂ) {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) : (jumpCLM L ρ).PosSemidef := by
  rw [jumpCLM_apply]
  exact lindblad_dissipation_posSemidef L hρ

/-- Powers of the scaled jump part preserve positive semidefiniteness. -/
lemma smul_jumpCLM_pow_posSemidef (L : ι → Matrix n n ℂ) {t : ℝ}
    (ht : 0 ≤ t) (m : ℕ) {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    (((t • jumpCLM L) ^ m) ρ).PosSemidef := by
  induction m generalizing ρ with
  | zero => simpa using hρ
  | succ m ih =>
    rw [pow_succ,
      show ((t • jumpCLM L) ^ m * (t • jumpCLM L)) ρ
        = ((t • jumpCLM L) ^ m) ((t • jumpCLM L) ρ) from rfl]
    refine ih ?_
    rw [_root_.smul_apply]
    exact posSemidef_real_smul (jumpCLM_posSemidef_apply L hρ) ht

/-- **The jump flow is positive** for `t ≥ 0`: every term of the exponential
series is PSD, and PSD passes to the limit. -/
theorem exp_smul_jumpCLM_posSemidef (L : ι → Matrix n n ℂ) {t : ℝ}
    (ht : 0 ≤ t) {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    (exp (t • jumpCLM L) ρ).PosSemidef := by
  have hsum := expCLM_apply_hasSum (t • jumpCLM L) ρ
  refine posSemidef_of_tendsto hsum.tendsto_sum_nat fun N => ?_
  refine Matrix.posSemidef_sum _ fun m _ => ?_
  rw [_root_.smul_apply]
  exact posSemidef_real_smul (smul_jumpCLM_pow_posSemidef L ht m hρ)
    (by positivity)

/-! ### Assembly: the semigroup is positive -/

/-- Powers of one Trotter step preserve positive semidefiniteness. -/
lemma step_pow_posSemidef (H : Matrix n n ℂ) (L : ι → Matrix n n ℂ)
    {u : ℝ} (hu : 0 ≤ u) (k : ℕ) {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    (((exp (u • driftCLM H L) * exp (u • jumpCLM L)) ^ k) ρ).PosSemidef := by
  induction k generalizing ρ with
  | zero => simpa using hρ
  | succ k ih =>
    rw [pow_succ,
      show ((exp (u • driftCLM H L) * exp (u • jumpCLM L)) ^ k
            * (exp (u • driftCLM H L) * exp (u • jumpCLM L))) ρ
        = ((exp (u • driftCLM H L) * exp (u • jumpCLM L)) ^ k)
            ((exp (u • driftCLM H L) * exp (u • jumpCLM L)) ρ) from rfl]
    refine ih ?_
    rw [show (exp (u • driftCLM H L) * exp (u • jumpCLM L)) ρ
        = exp (u • driftCLM H L) (exp (u • jumpCLM L) ρ) from rfl]
    exact exp_smul_driftCLM_posSemidef H L u
      (exp_smul_jumpCLM_posSemidef L hu hρ)

omit [Fintype n] in
/-- Matrix space over a nonempty index is nontrivial. -/
lemma matrix_nontrivial [Nonempty n] :
    Nontrivial (Matrix n n ℂ) := by
  obtain ⟨c⟩ := (inferInstance : Nonempty n)
  refine ⟨0, 1, fun h => ?_⟩
  have hcc := congrFun (congrFun h c) c
  rw [Matrix.zero_apply, Matrix.one_apply_eq] at hcc
  exact zero_ne_one hcc

/-- ★★ **The Lindblad semigroup is a positive map**: for every GKSL generator
with Hermitian `H` and every `t ≥ 0`, `Φₜ = e^{tℒ}` maps positive
semidefinite matrices to positive semidefinite matrices. The half
`LF6/LindbladSemigroup.lean` deferred as out of Mathlib's reach, closed by
the Banach-algebra Trotter formula over the two positive flows. -/
theorem lindbladSemigroup_posSemidef [Nonempty n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (L : ι → Matrix n n ℂ) {t : ℝ} (ht : 0 ≤ t)
    {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    (lindbladSemigroup H L t ρ).PosSemidef := by
  have : Nontrivial (Matrix n n ℂ) := matrix_nontrivial
  have : NormOneClass (Matrix n n ℂ →L[ℝ] Matrix n n ℂ) :=
    ⟨by rw [ContinuousLinearMap.one_def]; exact ContinuousLinearMap.norm_id⟩
  have hsplit : t • lindbladGeneratorCLM H L
      = t • driftCLM H L + t • jumpCLM L := by
    rw [lindbladGeneratorCLM_split hH, smul_add]
  have htrot := NormedSpace.trotter_product
    (t • driftCLM H L) (t • jumpCLM L)
  rw [← hsplit] at htrot
  have happ := ((ContinuousLinearMap.apply ℝ (Matrix n n ℂ)
    ρ).continuous.tendsto _).comp htrot
  rw [lindbladSemigroup]
  refine posSemidef_of_tendsto happ fun m => ?_
  show (((exp ((m : ℝ)⁻¹ • (t • driftCLM H L))
      * exp ((m : ℝ)⁻¹ • (t • jumpCLM L))) ^ m) ρ).PosSemidef
  rw [smul_smul, smul_smul]
  exact step_pow_posSemidef H L
    (mul_nonneg (by positivity) ht) m hρ

/-- ★ **The complete-positivity shape**: the amplified generator
`(1 ⊗ H, 1 ⊗ Lₖ)` is itself GKSL with Hermitian Hamiltonian, so positivity
survives every ancilla amplification of the generator — a literal
instantiation of `lindbladSemigroup_posSemidef` on the product index. -/
theorem lindbladSemigroup_amplified_posSemidef
    {m' : Type*} [Fintype m'] [DecidableEq m'] [Nonempty m'] [Nonempty n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (L : ι → Matrix n n ℂ)
    {t : ℝ} (ht : 0 ≤ t)
    {ρ : Matrix (m' × n) (m' × n) ℂ} (hρ : ρ.PosSemidef) :
    (lindbladSemigroup ((1 : Matrix m' m' ℂ) ⊗ₖ H)
      (fun k => (1 : Matrix m' m' ℂ) ⊗ₖ L k) t ρ).PosSemidef := by
  have h1H : ((1 : Matrix m' m' ℂ) ⊗ₖ H).IsHermitian := by
    show ((1 : Matrix m' m' ℂ) ⊗ₖ H)ᴴ = (1 : Matrix m' m' ℂ) ⊗ₖ H
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hH.eq]
  exact lindbladSemigroup_posSemidef h1H _ ht hρ

/-! ### The `id ⊗ Φ` identification (Q23)

The amplified generator's flow IS `id ⊗ Φₜ`: the flow of `(1 ⊗ H, 1 ⊗ Lₖ)`
acts on each ancilla block of the composite matrix by `Φₜ` separately. With
this, `lindbladSemigroup_amplified_posSemidef` is complete positivity of `Φₜ`
in so many words (`lindbladSemigroup_completelyPositive`). -/

section IdTensor

variable {m' : Type*} [Fintype m'] [DecidableEq m']

/-- The `(i,j)` ancilla block of a composite matrix, as a continuous
`ℝ`-linear map: `blockAtCLM i j M k l = M (i,k) (j,l)`. -/
noncomputable def blockAtCLM (i j : m') :
    Matrix (m' × n) (m' × n) ℂ →L[ℝ] Matrix n n ℂ :=
  (LinearMap.toContinuousLinearMap
    ({ toFun := fun M => Matrix.of fun k l => M (i, k) (j, l)
       map_add' := fun M N => by
         ext k l
         simp only [Matrix.of_apply, Matrix.add_apply]
       map_smul' := fun c M => by
         ext k l
         simp only [Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply] } :
      Matrix (m' × n) (m' × n) ℂ →ₗ[ℂ] Matrix n n ℂ)).restrictScalars ℝ

omit [DecidableEq n] [DecidableEq m'] in
@[simp] lemma blockAtCLM_apply_entry (i j : m')
    (M : Matrix (m' × n) (m' × n) ℂ) (k l : n) :
    blockAtCLM i j M k l = M (i, k) (j, l) := rfl

omit [DecidableEq n] [DecidableEq m'] in
/-- `blockAtCLM` commutes with complex scaling (it is `ℝ`-bundled but
`ℂ`-linear as a function). -/
lemma blockAtCLM_csmul (i j : m') (c : ℂ)
    (M : Matrix (m' × n) (m' × n) ℂ) :
    blockAtCLM i j (c • M) = c • blockAtCLM i j M := by
  ext k l
  rw [blockAtCLM_apply_entry, Matrix.smul_apply, Matrix.smul_apply,
    blockAtCLM_apply_entry]

omit [DecidableEq n] in
/-- **Left Kronecker collapse**: multiplying by `1 ⊗ A` on the left acts on
each ancilla block by left multiplication by `A`. -/
lemma blockAtCLM_one_kronecker_mul (i j : m') (A : Matrix n n ℂ)
    (M : Matrix (m' × n) (m' × n) ℂ) :
    blockAtCLM i j (((1 : Matrix m' m' ℂ) ⊗ₖ A) * M)
      = A * blockAtCLM i j M := by
  ext k l
  rw [blockAtCLM_apply_entry, Matrix.mul_apply, Matrix.mul_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · refine Finset.sum_congr rfl fun k' _ => ?_
    rw [Matrix.kronecker_apply, Matrix.one_apply_eq, one_mul,
      blockAtCLM_apply_entry]
  · intro i' _ hi'
    refine Finset.sum_eq_zero fun k' _ => ?_
    rw [Matrix.kronecker_apply, Matrix.one_apply,
      if_neg (fun h => hi' h.symm), zero_mul, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

omit [DecidableEq n] in
/-- **Right Kronecker collapse**: multiplying by `1 ⊗ B` on the right acts on
each ancilla block by right multiplication by `B`. -/
lemma blockAtCLM_mul_one_kronecker (i j : m') (B : Matrix n n ℂ)
    (M : Matrix (m' × n) (m' × n) ℂ) :
    blockAtCLM i j (M * ((1 : Matrix m' m' ℂ) ⊗ₖ B))
      = blockAtCLM i j M * B := by
  ext k l
  rw [blockAtCLM_apply_entry, Matrix.mul_apply, Matrix.mul_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single j]
  · refine Finset.sum_congr rfl fun l' _ => ?_
    rw [Matrix.kronecker_apply, Matrix.one_apply_eq, one_mul,
      blockAtCLM_apply_entry]
  · intro j' _ hj'
    refine Finset.sum_eq_zero fun l' _ => ?_
    rw [Matrix.kronecker_apply, Matrix.one_apply, if_neg hj', zero_mul,
      mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

omit [DecidableEq n] in
/-- The amplified dissipator acts blockwise. -/
lemma blockAtCLM_ampDissipator (i j : m') (L : Matrix n n ℂ)
    (M : Matrix (m' × n) (m' × n) ℂ) :
    blockAtCLM i j (lindbladDissipator ((1 : Matrix m' m' ℂ) ⊗ₖ L) M)
      = lindbladDissipator L (blockAtCLM i j M) := by
  have hconj : ((1 : Matrix m' m' ℂ) ⊗ₖ L)ᴴ
      = (1 : Matrix m' m' ℂ) ⊗ₖ Lᴴ := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  have hLL : ((1 : Matrix m' m' ℂ) ⊗ₖ Lᴴ) * ((1 : Matrix m' m' ℂ) ⊗ₖ L)
      = (1 : Matrix m' m' ℂ) ⊗ₖ (Lᴴ * L) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  rw [lindbladDissipator, lindbladDissipator, hconj, hLL, map_sub,
    blockAtCLM_csmul, map_add, Matrix.mul_assoc,
    blockAtCLM_one_kronecker_mul, blockAtCLM_mul_one_kronecker,
    blockAtCLM_one_kronecker_mul, blockAtCLM_mul_one_kronecker,
    ← Matrix.mul_assoc]

/-- ★ **The amplified generator acts blockwise**: the GKSL generator of
`(1 ⊗ H, 1 ⊗ Lₖ)` applied to a composite matrix is the GKSL generator of
`(H, Lₖ)` applied to each ancilla block. No Hermiticity is needed — this is
pure Kronecker algebra. -/
theorem blockAtCLM_ampGenerator (i j : m') (H : Matrix n n ℂ)
    (L : ι → Matrix n n ℂ) (M : Matrix (m' × n) (m' × n) ℂ) :
    blockAtCLM i j (lindbladGeneratorCLM ((1 : Matrix m' m' ℂ) ⊗ₖ H)
        (fun k => (1 : Matrix m' m' ℂ) ⊗ₖ L k) M)
      = lindbladGeneratorCLM H L (blockAtCLM i j M) := by
  rw [lindbladGeneratorCLM_apply, lindbladGeneratorCLM_apply,
    lindbladGenerator, lindbladGenerator, map_add, blockAtCLM_csmul,
    map_sub, blockAtCLM_one_kronecker_mul, blockAtCLM_mul_one_kronecker,
    map_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => blockAtCLM_ampDissipator i j (L k) M

/-- Powers of the scaled amplified generator act blockwise. -/
lemma blockAtCLM_smul_ampGen_pow (i j : m') (H : Matrix n n ℂ)
    (L : ι → Matrix n n ℂ) (t : ℝ) (p : ℕ)
    (M : Matrix (m' × n) (m' × n) ℂ) :
    blockAtCLM i j (((t • lindbladGeneratorCLM ((1 : Matrix m' m' ℂ) ⊗ₖ H)
        (fun k => (1 : Matrix m' m' ℂ) ⊗ₖ L k)) ^ p) M)
      = ((t • lindbladGeneratorCLM H L) ^ p) (blockAtCLM i j M) := by
  induction p generalizing M with
  | zero => simp
  | succ p ih =>
    rw [pow_succ,
      show ((t • lindbladGeneratorCLM ((1 : Matrix m' m' ℂ) ⊗ₖ H)
            (fun k => (1 : Matrix m' m' ℂ) ⊗ₖ L k)) ^ p
          * (t • lindbladGeneratorCLM ((1 : Matrix m' m' ℂ) ⊗ₖ H)
            (fun k => (1 : Matrix m' m' ℂ) ⊗ₖ L k))) M
        = ((t • lindbladGeneratorCLM ((1 : Matrix m' m' ℂ) ⊗ₖ H)
            (fun k => (1 : Matrix m' m' ℂ) ⊗ₖ L k)) ^ p)
          ((t • lindbladGeneratorCLM ((1 : Matrix m' m' ℂ) ⊗ₖ H)
            (fun k => (1 : Matrix m' m' ℂ) ⊗ₖ L k)) M) from rfl,
      ih, _root_.smul_apply, map_smul, blockAtCLM_ampGenerator, pow_succ]
    rfl

/-- ★★ **The amplified flow acts blockwise** — the block form of
`id ⊗ Φₜ`: the Lindblad semigroup of `(1 ⊗ H, 1 ⊗ Lₖ)` applied to a
composite matrix is `Φₜ` applied to each ancilla block. Exponential-series
transport of `blockAtCLM_ampGenerator` through `expCLM_apply_hasSum`. -/
theorem blockAtCLM_lindbladSemigroup_amplified (i j : m')
    (H : Matrix n n ℂ) (L : ι → Matrix n n ℂ) (t : ℝ)
    (M : Matrix (m' × n) (m' × n) ℂ) :
    blockAtCLM i j (lindbladSemigroup ((1 : Matrix m' m' ℂ) ⊗ₖ H)
        (fun k => (1 : Matrix m' m' ℂ) ⊗ₖ L k) t M)
      = lindbladSemigroup H L t (blockAtCLM i j M) := by
  have hamp := expCLM_apply_hasSum
    (t • lindbladGeneratorCLM ((1 : Matrix m' m' ℂ) ⊗ₖ H)
      (fun k => (1 : Matrix m' m' ℂ) ⊗ₖ L k)) M
  have hblk := hamp.mapL (blockAtCLM i j)
  have hbase := expCLM_apply_hasSum (t • lindbladGeneratorCLM H L)
    (blockAtCLM i j M)
  have hterms : (fun p : ℕ => blockAtCLM i j
      ((((p.factorial : ℝ))⁻¹ • (t • lindbladGeneratorCLM
          ((1 : Matrix m' m' ℂ) ⊗ₖ H)
          (fun k => (1 : Matrix m' m' ℂ) ⊗ₖ L k)) ^ p) M))
      = fun p : ℕ => ((((p.factorial : ℝ))⁻¹
          • (t • lindbladGeneratorCLM H L) ^ p) (blockAtCLM i j M)) := by
    funext p
    rw [_root_.smul_apply, map_smul, blockAtCLM_smul_ampGen_pow,
      ← _root_.smul_apply]
  rw [hterms] at hblk
  rw [lindbladSemigroup, lindbladSemigroup]
  exact hblk.unique hbase

/-- **`id ⊗ Φ`**: the ancilla amplification of a superoperator, acting on
each ancilla block of the composite matrix by `Φ` separately —
`(idTensorCLM m' Φ) M (i,k) (j,l) = Φ (blockAtCLM i j M) k l`. -/
noncomputable def idTensorCLM (m' : Type*) [Fintype m'] [DecidableEq m']
    (Φ : Matrix n n ℂ →L[ℝ] Matrix n n ℂ) :
    Matrix (m' × n) (m' × n) ℂ →L[ℝ] Matrix (m' × n) (m' × n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => Matrix.of fun p q => Φ (blockAtCLM p.1 q.1 M) p.2 q.2
      map_add' := fun M N => by
        ext p q
        simp only [Matrix.of_apply, Matrix.add_apply, map_add]
      map_smul' := fun c M => by
        ext p q
        simp only [Matrix.of_apply, Matrix.smul_apply, map_smul,
          RingHom.id_apply] }

omit [DecidableEq n] in
@[simp] lemma idTensorCLM_apply_entry (Φ : Matrix n n ℂ →L[ℝ] Matrix n n ℂ)
    (M : Matrix (m' × n) (m' × n) ℂ) (p q : m' × n) :
    idTensorCLM m' Φ M p q = Φ (blockAtCLM p.1 q.1 M) p.2 q.2 := rfl

omit [DecidableEq n] in
/-- Amplifying the identity gives the identity: the blocks reassemble. -/
lemma idTensorCLM_one :
    idTensorCLM m' (1 : Matrix n n ℂ →L[ℝ] Matrix n n ℂ) = 1 := by
  refine ContinuousLinearMap.ext fun M => ?_
  ext p q
  rw [idTensorCLM_apply_entry, one_apply_eq_self, one_apply_eq_self,
    blockAtCLM_apply_entry]

/-- ★★ **The identification**: `id ⊗ Φₜ` IS the flow of the amplified
generator `(1 ⊗ H, 1 ⊗ Lₖ)` — as an equality of superoperators on the
composite matrix space. This is the lemma that lets
`lindbladSemigroup_amplified_posSemidef` be cited as complete positivity of
`Φₜ` in so many words. -/
theorem idTensor_lindbladSemigroup (H : Matrix n n ℂ)
    (L : ι → Matrix n n ℂ) (t : ℝ) :
    idTensorCLM m' (lindbladSemigroup H L t)
      = lindbladSemigroup ((1 : Matrix m' m' ℂ) ⊗ₖ H)
        (fun k => (1 : Matrix m' m' ℂ) ⊗ₖ L k) t := by
  refine ContinuousLinearMap.ext fun M => ?_
  ext p q
  obtain ⟨i, k⟩ := p
  obtain ⟨j, l⟩ := q
  rw [idTensorCLM_apply_entry, ← blockAtCLM_lindbladSemigroup_amplified,
    blockAtCLM_apply_entry]

/-- ★★ **The Lindblad semigroup is completely positive** — in so many words:
for every GKSL generator with Hermitian `H`, every `t ≥ 0`, and every finite
ancilla, `id ⊗ Φₜ` maps positive semidefinite composite matrices to positive
semidefinite composite matrices. The identification rewrites the claim onto
`lindbladSemigroup_amplified_posSemidef`. -/
theorem lindbladSemigroup_completelyPositive [Nonempty m'] [Nonempty n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (L : ι → Matrix n n ℂ)
    {t : ℝ} (ht : 0 ≤ t)
    {ρ : Matrix (m' × n) (m' × n) ℂ} (hρ : ρ.PosSemidef) :
    (idTensorCLM m' (lindbladSemigroup H L t) ρ).PosSemidef := by
  rw [idTensor_lindbladSemigroup]
  exact lindbladSemigroup_amplified_posSemidef hH L ht hρ

end IdTensor

end CSD.LF6
