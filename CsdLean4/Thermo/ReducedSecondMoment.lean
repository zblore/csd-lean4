/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Thermo.CanonicalTypicality

/-!
# E1: the Fubini–Study second moment of the reduced state

**Category:** conceptually 1-Mathlib (CSD-free quantum statistical mechanics), kept under
`CSD.Thermo` beside TH-1.

The equilibration arc's first item (`specs/equilibration-arc-plan.md` E1) — in the Q24 scoping
note's vocabulary, its gated bricks B4/B5. TH-1 proved the *first* moment (the mean reduced
state is `I_A/d_A`); Q24 proved the Fubini–Study *second* moments of the moment map by twirl
algebra. This module spends both on the reduced state itself.

## ⚠️ H-TENSOR — the bipartition is a hypothesis, never an inference

Every statement carries the bipartition as an **explicit argument**

  `e : Fin N ≃ Fin dA × Fin dB`

exactly as `canonical_typicality_expectation` does. It is deliberately *not* obtained from a
tensor-product API (`QuantumInfo.regTensorEquiv` would make that easy, and is the temptation
this note exists to block). Rationale: a silently-chosen factorisation is a structural posit
doing load-bearing work — a second `D1`. Which factorisation is meant is physics input, so it
belongs in the signature where a reader and a referee can see it.
*(TODO(author): confirm the intended `D4`/`G6` referent — in this repo those IDs name an audit
record and a root-repair item, so they are presumably paper-side.)*

## What is proved

With `x_i = momentMap p i` and `r_{ij} = rayDensity p i j`:

* `blockPop` — the subsystem populations `(ρ_A)_{aa} = Σ_b x_{e⁻¹(a,b)}`, a **linear** statistic
  in the moment map, so Q24's linear moments apply verbatim (`blockPop_eq_linear`);
* ★ `fs_blockPop_mean` — `E[(ρ_A)_{aa}] = d_B/N` (`= 1/d_A`), the first moment in moment-map
  form;
* ★ `fs_blockPop_sq` — `E[(ρ_A)_{aa}²] = (d_B² + d_B)/(N(N+1))`;
* `signFlip_smul_rayDensity_ne` — a sign flip leaves a density entry alone when it touches
  neither index (companion to `signFlip_smul_offdiag`);
* ★ `fs_redOff_cross_vanish` — the genuinely four-index expectations vanish: a coordinate
  occurring an odd number of times is killed by the sign flip. This is the novel ingredient;
  everything else here is Q24 specialised.

## ⚠️ Honest scope — what is NOT yet proved

* **The off-diagonal second moment and the Hilbert–Schmidt assembly are NOT formalised here.**
  The two ingredients above determine them (see the closing section for the exact statement and
  route), and the arithmetic has been checked on paper — `E‖ρ_A − I_A/d_A‖₂² =
  (d_A+d_B)/(N+1) − 1/d_A`, the Lubkin–Page purity average — but arithmetic checked on paper is
  not a theorem, so it is recorded as a named remainder and not asserted.
* The **trace-norm** form the brief asks for would follow by `‖·‖₁ ≤ √d_A ‖·‖₂`, which needs the
  matrix-norm API rather than these moment computations.
* The reduced state is written **entrywise in the ray-density vocabulary**, which is what makes
  Q24's twirl results apply directly. Identifying these entries with `Matrix.traceRight` of the
  projector (the `canonical_typicality_expectation` spelling) is index bookkeeping, not done
  here.
* Moments only. Concentration is `fs_chebyshev_concentration` applied to these functionals.
-/

@[expose] public section

open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization BigOperators ComplexConjugate

namespace CSD.Thermo

open CSD.LF4

variable {N dA dB : ℕ} [NeZero N]

/-! ### The reduced state's entries, in moment-map / ray-density vocabulary -/

/-- The block indicator: `1` on the wires of subsystem level `a`. -/
noncomputable def blockIndicator (e : Fin N ≃ Fin dA × Fin dB) (a : Fin dA) (k : Fin N) : ℝ :=
  if (e k).1 = a then 1 else 0

/-- **The subsystem population** `(ρ_A)_{aa}`: the total moment-map weight of the `a`-block. -/
noncomputable def blockPop (e : Fin N ≃ Fin dA × Fin dB) (p : CPN N) (a : Fin dA) : ℝ :=
  ∑ b : Fin dB, momentMap p (e.symm (a, b))

/-- **The off-diagonal entry** `(ρ_A)_{aa'}` of the reduced state. -/
noncomputable def redOff (e : Fin N ≃ Fin dA × Fin dB) (p : CPN N) (a a' : Fin dA) : ℂ :=
  ∑ b : Fin dB, rayDensity p (e.symm (a, b)) (e.symm (a', b))

omit [NeZero N] in
/-- The population is the linear statistic of the block indicator — the bridge that lets Q24's
linear moment theorems apply unchanged. -/
lemma blockPop_eq_linear (e : Fin N ≃ Fin dA × Fin dB) (p : CPN N) (a : Fin dA) :
    blockPop e p a = ∑ k : Fin N, blockIndicator e a k * momentMap p k := by
  classical
  rw [blockPop, ← Equiv.sum_comp e.symm (fun k => blockIndicator e a k * momentMap p k),
    Fintype.sum_prod_type]
  symm
  calc (∑ a' : Fin dA, ∑ b : Fin dB,
          blockIndicator e a (e.symm (a', b)) * momentMap p (e.symm (a', b)))
      = ∑ b : Fin dB, blockIndicator e a (e.symm (a, b)) * momentMap p (e.symm (a, b)) :=
        Finset.sum_eq_single a
          (fun a' _ ha' => Finset.sum_eq_zero (fun b _ => by
            simp only [blockIndicator, Equiv.apply_symm_apply, if_neg ha', zero_mul]))
          (fun h => absurd (Finset.mem_univ a) h)
    _ = ∑ b : Fin dB, momentMap p (e.symm (a, b)) :=
        Finset.sum_congr rfl (fun b _ => by
          simp only [blockIndicator, Equiv.apply_symm_apply, if_pos, one_mul])

/-! ### The block indicator's own sums -/

omit [NeZero N] in
lemma sum_blockIndicator (e : Fin N ≃ Fin dA × Fin dB) (a : Fin dA) :
    ∑ k : Fin N, blockIndicator e a k = (dB : ℝ) := by
  classical
  rw [← Equiv.sum_comp e.symm (fun k => blockIndicator e a k), Fintype.sum_prod_type]
  calc (∑ a' : Fin dA, ∑ b : Fin dB, blockIndicator e a (e.symm (a', b)))
      = ∑ b : Fin dB, blockIndicator e a (e.symm (a, b)) :=
        Finset.sum_eq_single a
          (fun a' _ ha' => Finset.sum_eq_zero (fun b _ => by
            simp only [blockIndicator, Equiv.apply_symm_apply, if_neg ha']))
          (fun h => absurd (Finset.mem_univ a) h)
    _ = ∑ _b : Fin dB, (1 : ℝ) :=
        Finset.sum_congr rfl (fun b _ => by
          simp only [blockIndicator, Equiv.apply_symm_apply, if_pos])
    _ = (dB : ℝ) := by simp

omit [NeZero N] in
lemma sum_blockIndicator_sq (e : Fin N ≃ Fin dA × Fin dB) (a : Fin dA) :
    ∑ k : Fin N, blockIndicator e a k ^ 2 = (dB : ℝ) := by
  rw [← sum_blockIndicator e a]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [blockIndicator]
  split_ifs <;> norm_num

/-! ### ★ The population's first and second moments (Q24's linear moments, specialised) -/

/-- ★ **The mean subsystem population is `d_B/N`** (that is, `1/d_A`) — the first moment. -/
theorem fs_blockPop_mean (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB) (a : Fin dA) :
    ∫ p, blockPop e p a ∂(fubiniStudyMeasure p₀) = (dB : ℝ) / N := by
  have h : (fun p : CPN N => blockPop e p a)
      = fun p => ∑ k : Fin N, blockIndicator e a k * momentMap p k :=
    funext (fun p => blockPop_eq_linear e p a)
  rw [h, fs_linear_expectation p₀ (blockIndicator e a), sum_blockIndicator]

/-- ★ **The population's second moment**: `(d_B² + d_B)/(N(N+1))`. -/
theorem fs_blockPop_sq (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB) (a : Fin dA) :
    ∫ p, (blockPop e p a) ^ 2 ∂(fubiniStudyMeasure p₀)
      = ((dB : ℝ) ^ 2 + (dB : ℝ)) / ((N : ℝ) * ((N : ℝ) + 1)) := by
  have h : (fun p : CPN N => (blockPop e p a) ^ 2)
      = fun p => (∑ k : Fin N, blockIndicator e a k * momentMap p k) ^ 2 :=
    funext (fun p => by rw [blockPop_eq_linear e p a])
  rw [h, fs_linear_sq_moment p₀ (blockIndicator e a), sum_blockIndicator,
    sum_blockIndicator_sq]

/-! ### The sign flip away from both indices -/

/-- **A sign flip that touches neither index leaves the density entry alone.** The companion of
`signFlip_smul_offdiag` (which handles the case where the flipped coordinate *is* one of the
indices), and the engine behind the four-index vanishing below. -/
lemma signFlip_smul_rayDensity_ne (k i j : Fin N) (hik : i ≠ k) (hjk : j ≠ k) (p : CPN N) :
    rayDensity ((signFlip k) • p) i j = rayDensity p i j := by
  rw [smul_eq_mk, rayDensity_mk, signFlip_val, toEuclideanLin_signFlip_coord,
    toEuclideanLin_signFlip_coord, if_neg hik, if_neg hjk, one_mul, one_mul]
  have hden : (‖(Matrix.toEuclideanLin (signFlipMat k) p.rep)‖ : ℂ) ^ 2
      = (‖p.rep‖ : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, signFlip_normSq, Complex.ofReal_pow]
  rw [hden]
  rfl

/-! ### ★★ The off-diagonal second moment -/

/-- ★ **The four-index expectations vanish.** For `a ≠ a'` and `b ≠ b'`, the coordinate
`e⁻¹(a,b)` occurs an odd number of times in the product, so the sign flip there negates the
integrand and the integral is its own negative. -/
theorem fs_redOff_cross_vanish (p₀ : CPN N) (e : Fin N ≃ Fin dA × Fin dB)
    {a a' : Fin dA} (haa : a ≠ a') {b b' : Fin dB} (hbb : b ≠ b') :
    ∫ p, ((rayDensity p (e.symm (a, b)) (e.symm (a', b))).re
            * (rayDensity p (e.symm (a, b')) (e.symm (a', b'))).re
          + (rayDensity p (e.symm (a, b)) (e.symm (a', b))).im
            * (rayDensity p (e.symm (a, b')) (e.symm (a', b'))).im)
      ∂(fubiniStudyMeasure p₀) = 0 := by
  have hjk : e.symm (a', b) ≠ e.symm (a, b) :=
    fun h => haa (congrArg Prod.fst (e.symm.injective h)).symm
  have hi'k : e.symm (a, b') ≠ e.symm (a, b) :=
    fun h => hbb (congrArg Prod.snd (e.symm.injective h)).symm
  have hj'k : e.symm (a', b') ≠ e.symm (a, b) :=
    fun h => haa (congrArg Prod.fst (e.symm.injective h)).symm
  have hmeas : Measurable (fun p : CPN N =>
      (rayDensity p (e.symm (a, b)) (e.symm (a', b))).re
          * (rayDensity p (e.symm (a, b')) (e.symm (a', b'))).re
        + (rayDensity p (e.symm (a, b)) (e.symm (a', b))).im
          * (rayDensity p (e.symm (a, b')) (e.symm (a', b'))).im) := by
    refine Measurable.add ?_ ?_
    · exact ((Complex.measurable_re.comp (rayDensity_measurable _ _)).mul
        (Complex.measurable_re.comp (rayDensity_measurable _ _)))
    · exact ((Complex.measurable_im.comp (rayDensity_measurable _ _)).mul
        (Complex.measurable_im.comp (rayDensity_measurable _ _)))
  have h := fs_integral_unitary p₀ (signFlip (e.symm (a, b))) hmeas
  rw [integral_congr_ae (ae_of_all _ (fun p : CPN N => by
      rw [signFlip_smul_offdiag _ _ hjk,
        signFlip_smul_rayDensity_ne _ _ _ hi'k hj'k,
        Complex.neg_re, Complex.neg_im]
      ring :
    ∀ p : CPN N,
      (rayDensity ((signFlip (e.symm (a, b))) • p) (e.symm (a, b)) (e.symm (a', b))).re
          * (rayDensity ((signFlip (e.symm (a, b))) • p) (e.symm (a, b')) (e.symm (a', b'))).re
        + (rayDensity ((signFlip (e.symm (a, b))) • p) (e.symm (a, b)) (e.symm (a', b))).im
          * (rayDensity ((signFlip (e.symm (a, b))) • p) (e.symm (a, b')) (e.symm (a', b'))).im
      = -((rayDensity p (e.symm (a, b)) (e.symm (a', b))).re
            * (rayDensity p (e.symm (a, b')) (e.symm (a', b'))).re
          + (rayDensity p (e.symm (a, b)) (e.symm (a', b))).im
            * (rayDensity p (e.symm (a, b')) (e.symm (a', b'))).im))),
    integral_neg] at h
  linarith

/-! ### Remaining: the off-diagonal second moment and the Hilbert-Schmidt assembly

The two ingredients above (`fs_redOff_cross_vanish` and Q24's `fs_x_cross_moment`, applied
through `rayDensity_re_sq_add_im_sq`) determine

  `E|(rho_A)_{a a'}|^2 = d_B / (N (N+1))`   for `a != a'`,

because expanding `normSq (sum_b r_b)` into real and imaginary parts gives `d_B` diagonal terms
`E[x_i x_j] = 1/(N(N+1))` and `d_B (d_B - 1)` off-diagonal terms killed by
`fs_redOff_cross_vanish`. Combining with `fs_blockPop_mean` and `fs_blockPop_sq` yields the
Lubkin-Page purity average and the Hilbert-Schmidt deviation

  `E||rho_A - I_A/d_A||_2^2 = (d_A + d_B)/(N + 1) - 1/d_A`      (using `N = d_A d_B`),

which is the arc's E1 headline. That assembly is *arithmetic on the moments proved here* plus
the `normSq`-of-a-sum expansion; it is NOT yet formalised, and is recorded as the named
remainder rather than asserted. See `specs/equilibration-arc-plan.md` (E1).
-/

end CSD.Thermo
