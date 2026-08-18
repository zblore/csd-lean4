/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.DataProcessing
public import CsdLean4.Mathlib.Analysis.Matrix.L2OpNormEntry
public import CsdLean4.Mathlib.Analysis.Matrix.L2OpNormDiagonal

/-!
# CR-1: perturbing a unitary moves states by at most twice the operator-norm defect

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The **bridge between the two norms** a perturbative quantum argument uses: drives are
estimated in the **L2 operator norm** (the C*-norm, where Duhamel and Trotter bounds live),
while states are compared in the **trace distance** (the operational metric, where the
data-processing inequality lives). This file connects them:

  ★★ `traceDist_conj_sub_le` — `D(UρU†, VρV†) ≤ 2‖U − V‖`

for unitaries `U, V` and any density operator `ρ`. Nothing about the two unitaries is
assumed beyond unitarity: the bound is uniform in `ρ` and free of dimension factors.

## Route

The difference `D = UρU† − VρV†` is Hermitian and **traceless**, so the variational
collapse applies (`traceDist_eq_re_trace_posPart`) and `D₊ = D·P₊`
(`mul_posProj_eq_posPart`) turns the distance into a single trace `Re Tr(D·P₊)`. Splitting

  `UρU† − VρV† = (U−V)ρU† + Vρ(U−V)†`

and cycling the trace reduces the bound to two instances of the **Hölder-lite**

  `|Re Tr(ρ·M)| ≤ ‖M‖ · Re Tr ρ`     (`abs_re_trace_mul_le`, for `ρ` PSD),

proved by diagonalising `ρ` (`IsHermitian.spectral_theorem`), reading the trace as the
eigenvalue-weighted diagonal of the unitarily rotated `M`, and bounding each diagonal entry
by the operator norm (`norm_entry_le_l2_opNorm`). The projector's norm bound comes from
`norm_cfc_le`, the general statement that a Hermitian functional calculus is bounded by the
sup of the applied function over the spectrum.

⚠️ Scope: finite dimensions, `IsHermitian.cfc` (not the general continuous functional
calculus). `abs_re_trace_mul_le` is stated for the real part because that is what the
variational characterisation consumes; the modulus version would need `|Tr(ρM)| ≤ ‖M‖ Tr ρ`
through the same spectral route and is not needed here.

## Provenance

Named **CR-1** and feasibility-checked in `specs/channel-rg-scoping.md` §6 (CV-25); the
first brick of the CV-26 arc. Intended upstream location: beside
`Mathlib/Analysis/CStarAlgebra/Matrix.lean`'s unitary bounds, or with the trace-distance
material once that is upstreamed.

## Tags

trace distance, operator norm, unitary perturbation, functional calculus
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.L2Operator
open scoped ComplexOrder

namespace QuantumInfo

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-! ### Norm bounds from the functional calculus -/

set_option maxHeartbeats 800000 in
/-- **The functional calculus is bounded by the function on the spectrum**:
`‖cfc f‖ ≤ C` whenever `|f(λᵢ)| ≤ C` at every eigenvalue. The conjugating factors are
unitary, so the bound is the diagonal one. -/
theorem norm_cfc_le {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ i, |f (hA.eigenvalues i)| ≤ C) : ‖hA.cfc f‖ ≤ C := by
  set Vu : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hVu
  set D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) with hD
  have hdiag : ‖D‖ ≤ C := by
    rw [hD]
    refine Matrix.l2_opNorm_diagonal_le _ hC fun i => ?_
    show ‖((f (hA.eigenvalues i) : ℝ) : ℂ)‖ ≤ C
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hf i
  have hUn : ‖Vu‖ = 1 :=
    CStarRing.norm_of_mem_unitary hA.eigenvectorUnitary.property
  have hUsn : ‖star Vu‖ = 1 := by rw [norm_star]; exact hUn
  have hcfc : hA.cfc f = Vu * D * star Vu := by
    rw [hVu, hD]
    unfold Matrix.IsHermitian.cfc
    rw [Unitary.conjStarAlgAut_apply]
  have hleft : ‖Vu * D‖ ≤ ‖D‖ := by
    refine le_trans (norm_mul_le _ _) ?_
    rw [hUn, one_mul]
  rw [hcfc]
  calc ‖Vu * D * star Vu‖ ≤ ‖Vu * D‖ * ‖star Vu‖ := norm_mul_le _ _
    _ ≤ ‖D‖ * 1 :=
        mul_le_mul hleft (le_of_eq hUsn) (norm_nonneg _) (norm_nonneg _)
    _ = ‖D‖ := mul_one _
    _ ≤ C := hdiag

/-- **The positive-eigenspace projector has norm at most one** — its spectrum is `{0, 1}`. -/
theorem norm_posProj_le_one {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ‖posProj hA‖ ≤ 1 := by
  refine norm_cfc_le hA _ zero_le_one fun i => ?_
  by_cases h : 0 < hA.eigenvalues i <;> norm_num [h]

/-! ### The Hölder-lite bound -/

set_option maxHeartbeats 800000 in
/-- ★ **Hölder-lite**: `|Re Tr(ρ·M)| ≤ ‖M‖ · Re Tr ρ` for positive semidefinite `ρ`.
Diagonalising `ρ` reads the trace as the eigenvalue-weighted diagonal of the rotated `M`,
and every diagonal entry is bounded by the operator norm. -/
theorem abs_re_trace_mul_le {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (M : Matrix n n ℂ) :
    |RCLike.re (ρ * M).trace| ≤ ‖M‖ * RCLike.re ρ.trace := by
  classical
  set V : Matrix n n ℂ := (hρ.1.eigenvectorUnitary : Matrix n n ℂ) with hV
  set d : n → ℂ := RCLike.ofReal ∘ hρ.1.eigenvalues with hd
  set Nm : Matrix n n ℂ := star V * M * V with hNm
  have hspec : ρ = V * Matrix.diagonal d * star V := by
    conv_lhs => rw [hρ.1.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
  -- the trace, cycled onto the diagonal
  have hkey : (ρ * M).trace = (Matrix.diagonal d * Nm).trace := by
    rw [hspec, hNm]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hsum : (Matrix.diagonal d * Nm).trace
      = ∑ i, ((hρ.1.eigenvalues i : ℝ) : ℂ) * Nm i i := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.diagonal_mul]
    rfl
  -- the norm of the rotated observable
  have hVnorm : ‖V‖ = 1 := CStarRing.norm_of_mem_unitary hρ.1.eigenvectorUnitary.property
  have hVsnorm : ‖star V‖ = 1 := by rw [norm_star]; exact hVnorm
  have hNnorm : ‖Nm‖ ≤ ‖M‖ := by
    have hleft : ‖star V * M‖ ≤ ‖M‖ := by
      refine le_trans (norm_mul_le _ _) ?_
      rw [hVsnorm, one_mul]
    calc ‖Nm‖ ≤ ‖star V * M‖ * ‖V‖ := norm_mul_le _ _
      _ ≤ ‖M‖ * 1 :=
          mul_le_mul hleft (le_of_eq hVnorm) (norm_nonneg _) (norm_nonneg _)
      _ = ‖M‖ := mul_one _
  -- the eigenvalue sum is the trace
  have htrace : RCLike.re ρ.trace = ∑ i, hρ.1.eigenvalues i := by
    rw [hρ.1.trace_eq_sum_eigenvalues, map_sum]
    exact Finset.sum_congr rfl fun i _ => Complex.ofReal_re _
  rw [hkey, hsum, map_sum, htrace, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
  have hnn : 0 ≤ hρ.1.eigenvalues i := hρ.eigenvalues_nonneg i
  have hre : RCLike.re (((hρ.1.eigenvalues i : ℝ) : ℂ) * Nm i i)
      = hρ.1.eigenvalues i * RCLike.re (Nm i i) := by
    show ((((hρ.1.eigenvalues i : ℝ) : ℂ)) * Nm i i).re = _
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rfl
  rw [hre, abs_mul, abs_of_nonneg hnn, mul_comm ‖M‖ (hρ.1.eigenvalues i)]
  refine mul_le_mul_of_nonneg_left ?_ hnn
  calc |RCLike.re (Nm i i)| ≤ ‖Nm i i‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖Nm‖ := Matrix.norm_entry_le_l2_opNorm _ _ _
    _ ≤ ‖M‖ := hNnorm

/-! ### The bridge -/

set_option maxHeartbeats 800000 in
/-- ★★ **CR-1: the unitary-perturbation bridge.** Conjugating a state by two nearby
unitaries moves it by at most twice their operator-norm distance:

  `D(UρU†, VρV†) ≤ 2‖U − V‖`.

Uniform in the state and free of dimension factors — the interface that turns a Duhamel or
Trotter estimate on drives into a statement about distinguishability of the states they
produce. -/
theorem traceDist_conj_sub_le {U V ρ : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (hV : V ∈ Matrix.unitaryGroup n ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (h : (U * ρ * Uᴴ - V * ρ * Vᴴ).IsHermitian) :
    traceDist h ≤ 2 * ‖U - V‖ := by
  classical
  have hUU : Uᴴ * U = 1 := by
    have := hU
    rw [Matrix.mem_unitaryGroup_iff'] at this
    exact this
  have hVV : Vᴴ * V = 1 := by
    have := hV
    rw [Matrix.mem_unitaryGroup_iff'] at this
    exact this
  -- both conjugates are unit-trace, so the difference is traceless
  have hconjtr : ∀ {W : Matrix n n ℂ}, Wᴴ * W = 1 → (W * ρ * Wᴴ).trace = 1 := by
    intro W hW
    rw [Matrix.trace_mul_cycle, hW, Matrix.one_mul, htr]
  have htr0 : (U * ρ * Uᴴ - V * ρ * Vᴴ).trace = 0 := by
    rw [Matrix.trace_sub, hconjtr hUU, hconjtr hVV, sub_self]
  -- the variational collapse
  rw [traceDist_eq_re_trace_posPart h htr0, ← mul_posProj_eq_posPart h]
  set P : Matrix n n ℂ := posProj h with hP
  set W : Matrix n n ℂ := U - V with hW
  -- the two-term split
  have hsplit : (U * ρ * Uᴴ - V * ρ * Vᴴ) * P
      = ρ * (Uᴴ * P * W) + ρ * (Wᴴ * P * V)
        - (ρ * (Uᴴ * P * W) + ρ * (Wᴴ * P * V))
        + ((W * ρ * Uᴴ) * P + (V * ρ * Wᴴ) * P) := by
    rw [hW]
    simp only [Matrix.conjTranspose_sub]
    noncomm_ring
  have hsplit' : (U * ρ * Uᴴ - V * ρ * Vᴴ) * P
      = (W * ρ * Uᴴ) * P + (V * ρ * Wᴴ) * P := by
    rw [hsplit]
    abel
  -- cycle each term onto `ρ`
  have hcyc1 : ((W * ρ * Uᴴ) * P).trace = (ρ * (Uᴴ * P * W)).trace := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hcyc2 : ((V * ρ * Wᴴ) * P).trace = (ρ * (Wᴴ * P * V)).trace := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  -- norm bounds on the two rotated observables
  have hPnorm : ‖P‖ ≤ 1 := norm_posProj_le_one h
  have hUnorm : ‖Uᴴ‖ = 1 := by
    rw [← Matrix.star_eq_conjTranspose, norm_star]
    exact CStarRing.norm_of_mem_unitary hU
  have hVnorm : ‖V‖ = 1 := CStarRing.norm_of_mem_unitary hV
  have hWnorm : ‖Wᴴ‖ = ‖W‖ := by
    rw [← Matrix.star_eq_conjTranspose, norm_star]
  have hM1 : ‖Uᴴ * P * W‖ ≤ ‖W‖ := by
    have hleft : ‖Uᴴ * P‖ ≤ 1 := by
      refine le_trans (norm_mul_le _ _) ?_
      rw [hUnorm, one_mul]
      exact hPnorm
    calc ‖Uᴴ * P * W‖ ≤ ‖Uᴴ * P‖ * ‖W‖ := norm_mul_le _ _
      _ ≤ 1 * ‖W‖ := mul_le_mul_of_nonneg_right hleft (norm_nonneg _)
      _ = ‖W‖ := one_mul _
  have hM2 : ‖Wᴴ * P * V‖ ≤ ‖W‖ := by
    have hleft : ‖Wᴴ * P‖ ≤ ‖W‖ := by
      refine le_trans (norm_mul_le _ _) ?_
      rw [hWnorm]
      calc ‖W‖ * ‖P‖ ≤ ‖W‖ * 1 := mul_le_mul_of_nonneg_left hPnorm (norm_nonneg _)
        _ = ‖W‖ := mul_one _
    calc ‖Wᴴ * P * V‖ ≤ ‖Wᴴ * P‖ * ‖V‖ := norm_mul_le _ _
      _ ≤ ‖W‖ * 1 :=
          mul_le_mul hleft (le_of_eq hVnorm) (norm_nonneg _) (norm_nonneg _)
      _ = ‖W‖ := mul_one _
  -- assemble
  have htrρ : RCLike.re ρ.trace = 1 := by rw [htr]; simp
  have hb1 : |RCLike.re (ρ * (Uᴴ * P * W)).trace| ≤ ‖W‖ := by
    refine le_trans (abs_re_trace_mul_le hρ _) ?_
    rw [htrρ, mul_one]
    exact hM1
  have hb2 : |RCLike.re (ρ * (Wᴴ * P * V)).trace| ≤ ‖W‖ := by
    refine le_trans (abs_re_trace_mul_le hρ _) ?_
    rw [htrρ, mul_one]
    exact hM2
  rw [hsplit', Matrix.trace_add, map_add, hcyc1, hcyc2]
  calc RCLike.re (ρ * (Uᴴ * P * W)).trace + RCLike.re (ρ * (Wᴴ * P * V)).trace
      ≤ |RCLike.re (ρ * (Uᴴ * P * W)).trace| + |RCLike.re (ρ * (Wᴴ * P * V)).trace| :=
        add_le_add (le_abs_self _) (le_abs_self _)
    _ ≤ ‖W‖ + ‖W‖ := add_le_add hb1 hb2
    _ = 2 * ‖W‖ := by ring

end QuantumInfo
