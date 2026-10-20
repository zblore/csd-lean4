/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Matrix.AdiabaticBornFock
public import CsdLean4.Mathlib.Analysis.InnerProductSpace.GeometricPhase

/-!
# The phase: Berry's geometric phase survives the adiabatic limit

**Category:** 1-Mathlib (CSD-free; staged for upstream).
BACKLOG #164 (out of ~~#88~~; closes the loop ~~#56~~ opened — the general theorem behind
Berry's model).

Along a gapped `C²` path `Γ` with a **nondegenerate** branch (`mult = 1`, so `rank P = 1`), the
orbit `s ↦ A s ψ₀` of the adiabatic intertwiner `A` (#160, `A' = K A`, `K = [Ṗ, P]`) is a unit
section of the eigenline whose connection form vanishes — it is **BP-1's horizontal lift**
(`GeometricPhase.horizontalLift`). Consequently, for a **closed** eigenvector loop
`ψ 1 = e^{iφ} ψ 0`, `A 1 ψ₀ = e^{iβ} ψ₀` with `β = geometricPhase ψ 1 φ` the geometric phase of
the loop, and the physical propagator at speed `T` satisfies

  `U_T 1 ψ₀ = e^{−iT∫₀¹ lam} e^{iβ} ψ₀ + O(1/T)`:

**dynamical phase times Berry's phase, with the error of #162.**

The identification is a uniqueness-of-ODE step. For a `C¹` unit section `ψ` of the eigenline
(`P ψ = ψ`, `‖ψ‖ = 1`), `K ψ = (1 − P) ψ̇` (differentiate `P ψ = ψ`), and for a rank-one `P`,
`P ψ̇ = ⟪ψ, ψ̇⟫ ψ = i Im⟪ψ, ψ̇⟫ ψ` (`Re⟪ψ, ψ̇⟫ = 0` by unit norm), so `K ψ = ψ̇ − i A ψ` with
`A = Im⟪ψ, ψ̇⟫` the connection form. The horizontal lift `e^{−i∫A} ψ` therefore solves `χ' = K χ`,
`χ 0 = ψ 0`, and so does `A s ψ 0`; the vector-level uniqueness for propagators (Heisenberg
constancy of `A† χ`) identifies them.

* `Matrix.toEuclideanCLMᵣ`, `HasDerivWithinAt.toEuclideanCLM_apply`, `HasDerivAt.toEuclideanCLM_apply`
  — the derivative of `s ↦ M s (v s)`;
* ★ `IsPropagator.conjTranspose_apply_eq`, `IsPropagator.eq_apply_init` — **vector-level
  uniqueness**: every solution of `v' = G v` is `U v 0` (anti-Hermitian `G`);
* `Matrix.toEuclideanCLM_apply_eq_inner_smul`, `eq_inner_smul_of_toEuclideanCLM_apply_eq` — a
  rank-one Hermitian projector with `P ψ = ψ`, `‖ψ‖ = 1` is `P v = ⟪ψ, v⟫ ψ`;
* `inner_deriv_eq_im_mul_I` — `⟪ψ, ψ̇⟫ = i Im⟪ψ, ψ̇⟫` along a unit curve;
* `exists_eq_exp_smul_of_norm_eq`, `GeometricPhase.horizontalLift_zero` — small general facts;
* `GappedPath.rank_proj`, `rank_proj_eq_one`, `proj_one_eq_of_closed`, `exists_cyclic_of_proj_one_eq`
  — `rank P s = mult s`; a closed path has `P 1 = P 0`; a unit section of a rank-one eigenline
  with `P 1 = P 0` closes up to a phase;
* ★ `GappedPath.K_apply_section`, ★★ `K_apply_unit_section` — **`K ψ = (1 − P) ψ̇`, and
  `K ψ = ψ̇ − i A ψ` for a nondegenerate branch**;
* ★★ `GappedPath.hasDerivAt_horizontalLift_K` — **the horizontal lift solves `χ' = K χ`**;
* ★★★ `GappedPath.IsIntertwiner.toEuclideanCLM_apply_eq_horizontalLift` — **the intertwiner's
  orbit is the horizontal lift**: `A s ψ₀ = horizontalLift ψ s` on `[0, 1]` for every `C¹` unit
  section `ψ` of the eigenline with `ψ 0 = ψ₀`;
* ★★ `IsIntertwiner.toEuclideanCLM_apply_one_eq` — `A 1 ψ₀ = e^{iβ} ψ₀`, `β = geometricPhase ψ 1 φ`;
  `IsIntertwiner.exists_apply_one_eq` — the holonomy exists (`∃ β`) without choosing a section;
* ★★ `GappedPath.IsAdPropagator.toEuclideanCLM_apply_eq`, `exists_norm_sub_dynPhase_smul_le` —
  `U_A s ψ₀ = e^{−iT∫₀ˢ lam} A s ψ₀`, and `‖U_T s ψ₀ − e^{−iT∫₀ˢ lam} A s ψ₀‖ ≤ (C/T)‖ψ₀‖` (the
  adiabatic approximation with the parallel-transported eigenvector, any multiplicity);
* ★★★ `GappedPath.exists_norm_sub_phase_smul_le` — **the phase theorem**:
  `‖U_T 1 ψ₀ − e^{−iT∫₀¹ lam} e^{iβ} ψ₀‖ ≤ C / T`.

## Honest scope

* The eigenvector section `ψ` is a `C¹` map `ℝ → EuclideanSpace ℂ (Fin N)`, unit everywhere and
  in the eigenline `range (P t)` for every real `t` (the path `Γ` is defined on all of `ℝ`); only
  `[0, 1]` is used for the propagators. Any two such sections differ by a rephasing, and
  `GeometricPhase.geometricPhase_rephase` says `β` does not depend on the choice.
* Nondegeneracy is `Γ.mult 0 = 1` (constant along the path, `mult_eq`); the closed-loop
  hypothesis is `ψ 1 = e^{iφ} ψ 0`, which for rank one is equivalent to `P 1 = P 0`
  (`exists_cyclic_of_proj_one_eq`); `H 1 = H 0 ∧ lam 1 = lam 0` gives it (`proj_one_eq_of_closed`).
* `C` is #162's constant; the `C²` and eigenvalue hypotheses are #162's.

References: M. V. Berry, Proc. R. Soc. A 392 (1984) 45; B. Simon, PRL 51 (1983) 2167;
T. Kato, J. Phys. Soc. Japan 5 (1950) §3; `GeometricPhase.lean` (BP-1, #10), `AdiabaticBornFock.lean`
(#163), `AdiabaticPropagators.lean` (#161), `AdiabaticIntertwiner.lean` (#160);
`specs/berry-phase-scoping.md` BP-1, BP-5; `specs/BACKLOG.md` #164, ~~#88~~, ~~#56~~.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Matrix ContDiff Topology ComplexConjugate
open Matrix Metric Set Complex Filter GeometricPhase

namespace Matrix

variable {N : ℕ}

/-! ### The derivative of `s ↦ M s (v s)` -/

/-- `toEuclideanCLM`, with scalars restricted to `ℝ`, as a real continuous linear map on
matrices. -/
noncomputable def toEuclideanCLMᵣ :
    Matrix (Fin N) (Fin N) ℂ →L[ℝ] (EuclideanSpace ℂ (Fin N) →L[ℝ] EuclideanSpace ℂ (Fin N)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => (toEuclideanCLM (𝕜 := ℂ) A).restrictScalars ℝ
      map_add' := fun A B => ContinuousLinearMap.ext fun x => by simp [map_add]
      map_smul' := fun r A => ContinuousLinearMap.ext fun x => by
        simp only [RingHom.id_apply, ContinuousLinearMap.coe_restrictScalars', _root_.smul_apply]
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (E := Matrix (Fin N) (Fin N) ℂ) r A, map_smul,
          _root_.smul_apply]
        exact (RCLike.real_smul_eq_coe_smul (K := ℂ) (E := EuclideanSpace ℂ (Fin N)) r _).symm }

@[simp] theorem toEuclideanCLMᵣ_apply (A : Matrix (Fin N) (Fin N) ℂ) (x : EuclideanSpace ℂ (Fin N)) :
    toEuclideanCLMᵣ A x = toEuclideanCLM (𝕜 := ℂ) A x := rfl

theorem _root_.HasDerivWithinAt.toEuclideanCLM_apply {M : ℝ → Matrix (Fin N) (Fin N) ℂ}
    {M' : Matrix (Fin N) (Fin N) ℂ} {v : ℝ → EuclideanSpace ℂ (Fin N)} {v' : EuclideanSpace ℂ (Fin N)}
    {s : Set ℝ} {t : ℝ} (hM : HasDerivWithinAt M M' s t) (hv : HasDerivWithinAt v v' s t) :
    HasDerivWithinAt (fun u => toEuclideanCLM (𝕜 := ℂ) (M u) (v u))
      (toEuclideanCLM (𝕜 := ℂ) M' (v t) + toEuclideanCLM (𝕜 := ℂ) (M t) v') s t := by
  have h := (toEuclideanCLMᵣ.hasFDerivAt.comp_hasDerivWithinAt t hM).clm_apply hv
  simpa only [Function.comp_apply, toEuclideanCLMᵣ_apply] using h

theorem _root_.HasDerivAt.toEuclideanCLM_apply {M : ℝ → Matrix (Fin N) (Fin N) ℂ}
    {M' : Matrix (Fin N) (Fin N) ℂ} {v : ℝ → EuclideanSpace ℂ (Fin N)} {v' : EuclideanSpace ℂ (Fin N)}
    {t : ℝ} (hM : HasDerivAt M M' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun u => toEuclideanCLM (𝕜 := ℂ) (M u) (v u))
      (toEuclideanCLM (𝕜 := ℂ) M' (v t) + toEuclideanCLM (𝕜 := ℂ) (M t) v') t := by
  have h := (toEuclideanCLMᵣ.hasFDerivAt.comp_hasDerivAt t hM).clm_apply hv
  simpa only [Function.comp_apply, toEuclideanCLMᵣ_apply] using h

/-! ### Vector-level uniqueness for propagators -/

namespace IsPropagator

variable {G U : ℝ → Matrix (Fin N) (Fin N) ℂ} {T : ℝ}

/-- ★ **Heisenberg constancy on vectors**: for an anti-Hermitian generator, `U† v ≡ v 0` along
every solution `v' = G v`. -/
theorem conjTranspose_apply_eq (hU : IsPropagator G T U)
    (hG : ∀ s ∈ Icc (0 : ℝ) T, (G s)ᴴ = -G s) {v : ℝ → EuclideanSpace ℂ (Fin N)}
    (hv : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt v (toEuclideanCLM (𝕜 := ℂ) (G s) (v s)) (Icc 0 T) s) :
    ∀ s ∈ Icc (0 : ℝ) T, toEuclideanCLM (𝕜 := ℂ) (U s)ᴴ (v s) = v 0 := by
  have h0 : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun u => toEuclideanCLM (𝕜 := ℂ) (U u)ᴴ (v u)) 0 (Icc 0 T) s := by
    intro s hs
    refine ((hU.hasDerivWithinAt s hs).matrixConjTranspose.toEuclideanCLM_apply
      (hv s hs)).congr_deriv ?_
    rw [conjTranspose_mul, hG s hs, Matrix.mul_neg, map_neg, map_mul, _root_.neg_apply,
      mul_apply_eq_comp, neg_add_cancel]
  intro s hs
  rw [eq_of_hasDerivWithinAt_zero_Icc h0 s hs, hU.init, conjTranspose_one, map_one,
    one_apply_eq_self]

/-- ★ **Uniqueness on vectors**: every solution of `v' = G v` is `U v 0`. -/
theorem eq_apply_init (hU : IsPropagator G T U) (hG : ∀ s ∈ Icc (0 : ℝ) T, (G s)ᴴ = -G s)
    {v : ℝ → EuclideanSpace ℂ (Fin N)}
    (hv : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt v (toEuclideanCLM (𝕜 := ℂ) (G s) (v s)) (Icc 0 T) s) :
    ∀ s ∈ Icc (0 : ℝ) T, v s = toEuclideanCLM (𝕜 := ℂ) (U s) (v 0) := by
  intro s hs
  rw [← hU.conjTranspose_apply_eq hG hv s hs, ← mul_apply_eq_comp, ← map_mul,
    hU.mul_conjTranspose hG s hs, map_one, one_apply_eq_self]

end IsPropagator

/-! ### Rank-one projectors -/

/-- A rank-one Hermitian projector with a unit vector `ψ` in its range is `v ↦ ⟪ψ, v⟫ ψ`. -/
theorem toEuclideanCLM_apply_eq_inner_smul {P : Matrix (Fin N) (Fin N) ℂ} (hP : P.IsHermitian)
    (hrank : P.rank = 1) {ψ : EuclideanSpace ℂ (Fin N)}
    (hψ : toEuclideanCLM (𝕜 := ℂ) P ψ = ψ) (hunit : ‖ψ‖ = 1) (v : EuclideanSpace ℂ (Fin N)) :
    toEuclideanCLM (𝕜 := ℂ) P v = inner ℂ ψ v • ψ := by
  have hψ0 : ψ ≠ 0 := by
    rintro rfl
    simp at hunit
  have hmem : ψ.ofLp ∈ LinearMap.range P.mulVecLin :=
    ⟨ψ.ofLp, by rw [mulVecLin_apply, ← ofLp_toEuclideanCLM, hψ]⟩
  have hne : (⟨ψ.ofLp, hmem⟩ : LinearMap.range P.mulVecLin) ≠ 0 := by
    intro h
    exact hψ0 ((WithLp.ofLp_eq_zero 2).1 (congrArg Subtype.val h))
  have hmem' : (toEuclideanCLM (𝕜 := ℂ) P v).ofLp ∈ LinearMap.range P.mulVecLin :=
    ⟨v.ofLp, by rw [mulVecLin_apply, ofLp_toEuclideanCLM]⟩
  unfold Matrix.rank at hrank
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).1 hrank ⟨_, hmem'⟩
  have hc' : c • ψ = toEuclideanCLM (𝕜 := ℂ) P v := by
    apply WithLp.ofLp_injective
    rw [WithLp.ofLp_smul]
    exact congrArg Subtype.val hc
  have h1 : inner ℂ ψ (toEuclideanCLM (𝕜 := ℂ) P v) = c := by
    rw [← hc', inner_smul_right, inner_self_eq_norm_sq_to_K, hunit]
    simp
  have h2 : inner ℂ ψ (toEuclideanCLM (𝕜 := ℂ) P v) = inner ℂ ψ v := by
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      ← map_star, star_eq_conjTranspose, hP.eq, hψ]
  rw [← h2, h1, hc']

/-- Every vector of the range of a rank-one Hermitian projector is a multiple of a unit vector
in it: `P y = y → y = ⟪ψ, y⟫ ψ`. -/
theorem eq_inner_smul_of_toEuclideanCLM_apply_eq {P : Matrix (Fin N) (Fin N) ℂ}
    (hP : P.IsHermitian) (hrank : P.rank = 1) {ψ y : EuclideanSpace ℂ (Fin N)}
    (hψ : toEuclideanCLM (𝕜 := ℂ) P ψ = ψ) (hunit : ‖ψ‖ = 1)
    (hy : toEuclideanCLM (𝕜 := ℂ) P y = y) : y = inner ℂ ψ y • ψ := by
  rw [← toEuclideanCLM_apply_eq_inner_smul hP hrank hψ hunit y, hy]

end Matrix

/-! ### Two small general facts -/

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Along a unit curve, `⟪ψ, ψ̇⟫` is purely imaginary: `⟪ψ, ψ̇⟫ = i Im⟪ψ, ψ̇⟫`. -/
theorem inner_deriv_eq_im_mul_I {ψ : ℝ → E} {ψ' : E} {t : ℝ} (hψ : HasDerivAt ψ ψ' t)
    (hunit : ∀ t, ‖ψ t‖ = 1) :
    inner ℂ (ψ t) ψ' = ((inner ℂ (ψ t) ψ').im : ℂ) * I := by
  have h1 : HasDerivAt (fun t => inner ℂ (ψ t) (ψ t))
      (inner ℂ (ψ t) ψ' + inner ℂ ψ' (ψ t)) t := hψ.inner ℂ hψ
  have h2 : HasDerivAt (fun t => inner ℂ (ψ t) (ψ t)) 0 t := by
    have : (fun t => inner ℂ (ψ t) (ψ t)) = fun _ => (1 : ℂ) :=
      funext fun t => inner_self_eq_one (hunit t)
    rw [this]
    exact hasDerivAt_const _ _
  have h3 := h1.unique h2
  rw [← inner_conj_symm ψ' (ψ t)] at h3
  have hre : (inner ℂ (ψ t) ψ').re = 0 := by
    have := congrArg Complex.re h3
    simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at this
    linarith
  apply Complex.ext <;> simp [hre]

/-- Two unit vectors, one a multiple of the other, differ by a phase. -/
theorem exists_eq_exp_smul_of_norm_eq {x y : E} {c : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (h : y = c • x) : ∃ β : ℝ, y = Complex.exp ((β : ℂ) * I) • x := by
  have hc : ‖c‖ = 1 := by
    have := congrArg norm h
    rw [norm_smul, hx, hy, mul_one] at this
    exact this.symm
  obtain ⟨β, hβ⟩ := (Complex.norm_eq_one_iff c).1 hc
  exact ⟨β, by rw [hβ, h]⟩

/-- The horizontal lift starts where the curve does. -/
theorem GeometricPhase.horizontalLift_zero (ψ : ℝ → E) : horizontalLift ψ 0 = ψ 0 := by
  rw [horizontalLift, rephase, dynamicalPhase, intervalIntegral.integral_same, neg_zero,
    Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]

end General

namespace Matrix.GappedPath

variable {N : ℕ} (Γ : GappedPath N)

/-! ### Rank one and closed paths -/

/-- `rank (P s) = mult s`. -/
theorem rank_proj (s : ℝ) : (Γ.proj s).rank = Γ.mult s := by
  classical
  unfold proj mult
  rw [(Γ.isHermitian s).rank_rieszProj (half_pos Γ.g_pos).le (Γ.hcirc_self s)]
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun j => ?_)
  rw [Γ.dist_eigC]
  constructor
  · intro h
    rcases Γ.gap s j with h' | h'
    · exact h'
    · exfalso
      linarith [Γ.g_pos]
  · intro h
    rw [h, sub_self, abs_zero]
    exact half_pos Γ.g_pos

/-- A nondegenerate branch (`mult 0 = 1`) has rank-one projectors everywhere. -/
theorem rank_proj_eq_one {n : ℕ∞} (hH : ContDiff ℝ n Γ.H) (hmult : Γ.mult 0 = 1) (s : ℝ) :
    (Γ.proj s).rank = 1 := by
  rw [Γ.rank_proj, Γ.mult_eq hH s 0, hmult]

/-- A closed path (`H 1 = H 0`, `lam 1 = lam 0`) has `P 1 = P 0`. -/
theorem proj_one_eq_of_closed (hH : Γ.H 1 = Γ.H 0) (hlam : Γ.lam 1 = Γ.lam 0) :
    Γ.proj 1 = Γ.proj 0 := by
  unfold proj
  rw [hH, hlam]

/-- A unit section of a rank-one eigenline with `P 1 = P 0` closes up to a phase. -/
theorem exists_cyclic_of_proj_one_eq {n : ℕ∞} (hH : ContDiff ℝ n Γ.H) (hmult : Γ.mult 0 = 1)
    (hP : Γ.proj 1 = Γ.proj 0) {ψ : ℝ → EuclideanSpace ℂ (Fin N)} (hunit : ∀ t, ‖ψ t‖ = 1)
    (hsec : ∀ t, toEuclideanCLM (𝕜 := ℂ) (Γ.proj t) (ψ t) = ψ t) :
    ∃ φ : ℝ, ψ 1 = Complex.exp ((φ : ℂ) * I) • ψ 0 :=
  exists_eq_exp_smul_of_norm_eq (hunit 0) (hunit 1)
    (eq_inner_smul_of_toEuclideanCLM_apply_eq (Γ.proj_isHermitian 0) (Γ.rank_proj_eq_one hH hmult 0)
      (hsec 0) (hunit 0) (by rw [← hP, hsec 1]))

/-! ### `K` on a unit section of the eigenline -/

/-- ★ **`K ψ = (1 − P) ψ̇`** for a differentiable section `ψ` of the eigenline. -/
theorem K_apply_section {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H)
    {ψ : ℝ → EuclideanSpace ℂ (Fin N)} {ψ' : EuclideanSpace ℂ (Fin N)} {s : ℝ}
    (hψ : HasDerivAt ψ ψ' s) (hsec : ∀ t, toEuclideanCLM (𝕜 := ℂ) (Γ.proj t) (ψ t) = ψ t) :
    toEuclideanCLM (𝕜 := ℂ) (Γ.K s) (ψ s) = ψ' - toEuclideanCLM (𝕜 := ℂ) (Γ.proj s) ψ' := by
  have hd : HasDerivAt (fun t => toEuclideanCLM (𝕜 := ℂ) (Γ.proj t) (ψ t))
      (toEuclideanCLM (𝕜 := ℂ) (deriv Γ.proj s) (ψ s) + toEuclideanCLM (𝕜 := ℂ) (Γ.proj s) ψ') s :=
    (Γ.hasDerivAt_proj hn hH s).toEuclideanCLM_apply hψ
  have hfun : (fun t => toEuclideanCLM (𝕜 := ℂ) (Γ.proj t) (ψ t)) = ψ := funext hsec
  rw [hfun] at hd
  have hP : toEuclideanCLM (𝕜 := ℂ) (deriv Γ.proj s) (ψ s)
      = ψ' - toEuclideanCLM (𝕜 := ℂ) (Γ.proj s) ψ' :=
    eq_sub_of_add_eq (hd.unique hψ)
  rw [K, map_sub, map_mul, map_mul, _root_.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
    hsec s, hP, (toEuclideanCLM (𝕜 := ℂ) (Γ.proj s)).map_sub, ← mul_apply_eq_comp, ← map_mul,
    Γ.proj_mul_self]
  abel

/-- ★★ **`K ψ = ψ̇ − i A ψ`** for a `C¹` unit section `ψ` of a nondegenerate eigenline, `A` the
connection form `Im⟪ψ, ψ̇⟫`: Kato's generator acts on the section as covariant differentiation. -/
theorem K_apply_unit_section {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H) (hmult : Γ.mult 0 = 1)
    {ψ : ℝ → EuclideanSpace ℂ (Fin N)} (hψ : ContDiff ℝ 1 ψ) (hunit : ∀ t, ‖ψ t‖ = 1)
    (hsec : ∀ t, toEuclideanCLM (𝕜 := ℂ) (Γ.proj t) (ψ t) = ψ t) (s : ℝ) :
    toEuclideanCLM (𝕜 := ℂ) (Γ.K s) (ψ s)
      = deriv ψ s - (((connectionForm ψ s : ℝ) : ℂ) * I) • ψ s := by
  have hd := (hψ.differentiable one_ne_zero s).hasDerivAt
  rw [Γ.K_apply_section hn hH hd hsec,
    toEuclideanCLM_apply_eq_inner_smul (Γ.proj_isHermitian s) (Γ.rank_proj_eq_one hH hmult s)
      (hsec s) (hunit s), inner_deriv_eq_im_mul_I hd hunit, connectionForm]

/-- ★★ **The horizontal lift of a unit section solves Kato's equation `χ' = K χ`.** -/
theorem hasDerivAt_horizontalLift_K {n : ℕ∞} (hn : 1 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hmult : Γ.mult 0 = 1) {ψ : ℝ → EuclideanSpace ℂ (Fin N)} (hψ : ContDiff ℝ 1 ψ)
    (hunit : ∀ t, ‖ψ t‖ = 1) (hsec : ∀ t, toEuclideanCLM (𝕜 := ℂ) (Γ.proj t) (ψ t) = ψ t) (s : ℝ) :
    HasDerivAt (horizontalLift ψ)
      (toEuclideanCLM (𝕜 := ℂ) (Γ.K s) (horizontalLift ψ s)) s := by
  have hθ : HasDerivAt (fun t => -dynamicalPhase ψ t) (-connectionForm ψ s) s :=
    (hasDerivAt_dynamicalPhase hψ s).neg
  have hd := (hψ.differentiable one_ne_zero s).hasDerivAt
  refine (hasDerivAt_rephase hθ hd).congr_deriv ?_
  rw [horizontalLift, rephase, map_smul, Γ.K_apply_unit_section hn hH hmult hψ hunit hsec s,
    smul_sub, smul_smul, sub_eq_add_neg, ← neg_smul]
  congr 2
  push_cast
  ring

/-! ### The intertwiner's orbit is the horizontal lift -/

namespace IsIntertwiner

variable {Γ} {A : ℝ → Matrix (Fin N) (Fin N) ℂ}

/-- ★★★ **The adiabatic intertwiner parallel-transports the eigenvector**: for a nondegenerate
branch and any `C¹` unit section `ψ` of the eigenline, `A s (ψ 0) = horizontalLift ψ s` on
`[0, 1]` — the orbit of the intertwiner is BP-1's horizontal lift. -/
theorem toEuclideanCLM_apply_eq_horizontalLift (hA : Γ.IsIntertwiner 1 A) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) (hmult : Γ.mult 0 = 1) {ψ : ℝ → EuclideanSpace ℂ (Fin N)}
    (hψ : ContDiff ℝ 1 ψ) (hunit : ∀ t, ‖ψ t‖ = 1)
    (hsec : ∀ t, toEuclideanCLM (𝕜 := ℂ) (Γ.proj t) (ψ t) = ψ t) :
    ∀ s ∈ Icc (0 : ℝ) 1, toEuclideanCLM (𝕜 := ℂ) (A s) (ψ 0) = horizontalLift ψ s := by
  intro s hs
  rw [IsPropagator.eq_apply_init hA (fun s _ => Γ.conjTranspose_K hn hH s)
    (fun s _ => (Γ.hasDerivAt_horizontalLift_K hn hH hmult hψ hunit hsec s).hasDerivWithinAt)
    s hs, horizontalLift_zero]

/-- ★★ **The holonomy is Berry's phase**: for a closed eigenvector loop `ψ 1 = e^{iφ} ψ 0`,
`A 1 (ψ 0) = e^{iβ} ψ 0` with `β = geometricPhase ψ 1 φ`. -/
theorem toEuclideanCLM_apply_one_eq (hA : Γ.IsIntertwiner 1 A) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) (hmult : Γ.mult 0 = 1) {ψ : ℝ → EuclideanSpace ℂ (Fin N)}
    (hψ : ContDiff ℝ 1 ψ) (hunit : ∀ t, ‖ψ t‖ = 1)
    (hsec : ∀ t, toEuclideanCLM (𝕜 := ℂ) (Γ.proj t) (ψ t) = ψ t) {φ : ℝ}
    (hcyc : ψ 1 = Complex.exp ((φ : ℂ) * I) • ψ 0) :
    toEuclideanCLM (𝕜 := ℂ) (A 1) (ψ 0)
      = Complex.exp ((geometricPhase ψ 1 φ : ℂ) * I) • ψ 0 := by
  rw [hA.toEuclideanCLM_apply_eq_horizontalLift hn hH hmult hψ hunit hsec 1 ⟨zero_le_one, le_rfl⟩,
    horizontalLift_cyclic hcyc, horizontalLift_zero]

/-- The holonomy exists without choosing a section: for a nondegenerate branch with `P 1 = P 0`
and a unit `ψ₀ ∈ range (P 0)`, `A 1 ψ₀ = e^{iβ} ψ₀` for some `β`. -/
theorem exists_apply_one_eq (hA : Γ.IsIntertwiner 1 A) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) (hmult : Γ.mult 0 = 1) (hP : Γ.proj 1 = Γ.proj 0)
    {x : EuclideanSpace ℂ (Fin N)} (hx : toEuclideanCLM (𝕜 := ℂ) (Γ.proj 0) x = x)
    (hunit : ‖x‖ = 1) :
    ∃ β : ℝ, toEuclideanCLM (𝕜 := ℂ) (A 1) x = Complex.exp ((β : ℂ) * I) • x := by
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hy : toEuclideanCLM (𝕜 := ℂ) (Γ.proj 0) (toEuclideanCLM (𝕜 := ℂ) (A 1) x)
      = toEuclideanCLM (𝕜 := ℂ) (A 1) x := by
    rw [← mul_apply_eq_comp, ← map_mul, ← hP, ← hA.mul_proj_zero hn hH 1 h1, map_mul,
      mul_apply_eq_comp, hx]
  exact exists_eq_exp_smul_of_norm_eq hunit
    ((norm_toEuclideanCLM_apply_of_conjTranspose_mul_self (hA.conjTranspose_mul_self hn hH 1 h1)
      x).trans hunit)
    (eq_inner_smul_of_toEuclideanCLM_apply_eq (Γ.proj_isHermitian 0)
      (Γ.rank_proj_eq_one hH hmult 0) hx hunit hy)

end IsIntertwiner

/-! ### The phase theorem -/

namespace IsAdPropagator

variable {Γ} {T : ℝ} {U A : ℝ → Matrix (Fin N) (Fin N) ℂ}

/-- ★★ `U_A s ψ₀ = e^{−iT∫₀ˢ lam} · A s ψ₀` for `P 0 ψ₀ = ψ₀` (#161 on vectors). -/
theorem toEuclideanCLM_apply_eq (hU : Γ.IsAdPropagator T U) (hA : Γ.IsIntertwiner 1 A) {n : ℕ∞} (hn : 1 ≤ n)
    (hH : ContDiff ℝ n Γ.H) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {x : EuclideanSpace ℂ (Fin N)}
    (hx : toEuclideanCLM (𝕜 := ℂ) (Γ.proj 0) x = x) :
    toEuclideanCLM (𝕜 := ℂ) (U s) x = Γ.dynPhase T s • toEuclideanCLM (𝕜 := ℂ) (A s) x := by
  have h := congrArg (fun M => toEuclideanCLM (𝕜 := ℂ) M x) (hU.mul_proj_zero_eq hA hn hH s hs)
  simp only [map_mul, mul_apply_eq_comp, map_smul, _root_.smul_apply, hx] at h
  exact h

end IsAdPropagator

/-- ★★ **The adiabatic approximation with the parallel-transported eigenvector**:
`‖U_T s ψ₀ − e^{−iT∫₀ˢ lam} A s ψ₀‖ ≤ (C / T) ‖ψ₀‖` for `P 0 ψ₀ = ψ₀`, uniformly on `[0, 1]`
(any multiplicity). -/
theorem exists_norm_sub_dynPhase_smul_le {n : ℕ∞} (hn : 2 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T → ∀ UT A : ℝ → Matrix (Fin N) (Fin N) ℂ,
      Γ.IsPhysPropagator T UT → Γ.IsIntertwiner 1 A →
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ x : EuclideanSpace ℂ (Fin N),
        toEuclideanCLM (𝕜 := ℂ) (Γ.proj 0) x = x →
        ‖toEuclideanCLM (𝕜 := ℂ) (UT s) x - Γ.dynPhase T s • toEuclideanCLM (𝕜 := ℂ) (A s) x‖
          ≤ C / T * ‖x‖ := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  obtain ⟨C, hC0, hC⟩ := Γ.exists_norm_toEuclideanCLM_sub_le hn hH hex
  refine ⟨C, hC0, fun T hT UT A hUT hA s hs x hx => ?_⟩
  obtain ⟨UA, hUA⟩ := Γ.exists_isAdPropagator hn1 hH T
  rw [← hUA.toEuclideanCLM_apply_eq hA hn1 hH hs hx]
  exact hC T hT UT UA hUT hUA s hs x

/-- ★★★ **The phase theorem (Berry's phase from Kato's theorem).** Along a gapped `C²` path with
a nondegenerate branch and a closed `C¹` unit eigenvector loop `ψ` (`ψ 1 = e^{iφ} ψ 0`), there is
a constant `C` such that for every speed `T > 0` and physical propagator `U_T`,

  `‖U_T 1 (ψ 0) − e^{−iT∫₀¹ lam} e^{iβ} (ψ 0)‖ ≤ C / T`,  `β = geometricPhase ψ 1 φ`:

**the state returns with the dynamical phase times Berry's geometric phase, up to `O(1/T)`.** -/
theorem exists_norm_sub_phase_smul_le {n : ℕ∞} (hn : 2 ≤ n) (hH : ContDiff ℝ n Γ.H)
    (hex : ∀ s, ∃ j, (Γ.isHermitian s).eigenvalues j = Γ.lam s) (hmult : Γ.mult 0 = 1)
    {ψ : ℝ → EuclideanSpace ℂ (Fin N)} (hψ : ContDiff ℝ 1 ψ) (hunit : ∀ t, ‖ψ t‖ = 1)
    (hsec : ∀ t, toEuclideanCLM (𝕜 := ℂ) (Γ.proj t) (ψ t) = ψ t) {φ : ℝ}
    (hcyc : ψ 1 = Complex.exp ((φ : ℂ) * I) • ψ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T → ∀ UT : ℝ → Matrix (Fin N) (Fin N) ℂ,
      Γ.IsPhysPropagator T UT →
      ‖toEuclideanCLM (𝕜 := ℂ) (UT 1) (ψ 0)
          - (Γ.dynPhase T 1 * Complex.exp ((geometricPhase ψ 1 φ : ℂ) * I)) • ψ 0‖ ≤ C / T := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  obtain ⟨C, hC0, hC⟩ := Γ.exists_norm_sub_dynPhase_smul_le hn hH hex
  refine ⟨C, hC0, fun T hT UT hUT => ?_⟩
  obtain ⟨A, hA⟩ := Γ.exists_isIntertwiner hn1 hH one_pos
  have h := hC T hT UT A hUT hA 1 ⟨zero_le_one, le_rfl⟩ (ψ 0) (hsec 0)
  rw [hA.toEuclideanCLM_apply_one_eq hn1 hH hmult hψ hunit hsec hcyc, smul_smul, hunit 0,
    mul_one] at h
  exact h

end Matrix.GappedPath

end
