/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Subadditivity

/-!
# Concavity of the von Neumann entropy, and the Holevo quantity

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

* ★ `vonNeumannEntropy_mixture_ge_of_posDef` — **concavity**: for a finite mixture
  `σ = ∑ᵢ pᵢ ρᵢ` of density matrices with weights `pᵢ ≥ 0` summing to one, `∑ᵢ pᵢ S(ρᵢ) ≤ S(σ)`,
  under Klein's full-support condition on `σ`. The condition is removed in
  `ConcavityFull.lean` (`vonNeumannEntropy_mixture_ge`), by mixing with the maximally mixed
  state and passing to the limit. The proof is the identity
  `S(σ) − ∑ᵢ pᵢ S(ρᵢ) = ∑ᵢ pᵢ D(ρᵢ ‖ σ)`: the cross term `Re Tr(σ log σ)` is the `p`-average of
  `Re Tr(ρᵢ log σ)` (`re_trace_finset_sum_smul_mul`), and Klein's inequality
  (`klein_inequality`, `Subadditivity.lean`) bounds each by `Re Tr(ρᵢ log ρᵢ) = −S(ρᵢ)`
  (`re_trace_self_log_eq_neg_vonNeumannEntropy`);
* `holevoChi` — the Holevo quantity `χ = S(∑ᵢ pᵢ ρᵢ) − ∑ᵢ pᵢ S(ρᵢ)` of an ensemble, and
  ★ `holevoChi_nonneg_of_posDef`.

The full-support hypothesis is the same discipline as `relEntropy_nonneg` and
`vonNeumannEntropy_le_pinching`: without it the junk value of `log` at `0` enters the cross term.
`ConcavityFull.lean` removes it for concavity (and hence for `holevoChi_nonneg`) by continuity.

Consumers: `CsdLean4/LF2/PreparationCoarseGraining.lean` (coarse-graining a preparation on `Σ`
does not decrease its entropy).
-/

@[expose] public section

open Matrix
open scoped ComplexOrder

/-! ### Concavity of the von Neumann entropy -/

namespace QuantumInfo

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Von Neumann entropy depends only on the matrix (transport along an equality of matrices). -/
theorem vonNeumannEntropy_congr_of_eq {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : A = B) : vonNeumannEntropy hA = vonNeumannEntropy hB := by
  subst hAB; rfl

/-- `Re Tr(ρ log ρ) = −S(ρ)`. -/
theorem re_trace_self_log_eq_neg_vonNeumannEntropy {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    RCLike.re ((ρ * hρ.cfc Real.log).trace) = -vonNeumannEntropy hρ := by
  rw [re_trace_self_log hρ, vonNeumannEntropy, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp only [Real.negMulLog]; ring

omit [DecidableEq n] in
/-- The cross term is affine in the first argument: for `σ = ∑ᵢ pᵢ ρᵢ`,
`Re Tr(σ L) = ∑ᵢ pᵢ Re Tr(ρᵢ L)`. -/
theorem re_trace_finset_sum_smul_mul {ι : Type*} (s : Finset ι) (p : ι → ℝ) (ρ : ι → Matrix n n ℂ)
    (L : Matrix n n ℂ) :
    RCLike.re (((∑ i ∈ s, ((p i : ℝ) : ℂ) • ρ i) * L).trace)
      = ∑ i ∈ s, p i * RCLike.re ((ρ i * L).trace) := by
  rw [Matrix.sum_mul, Matrix.trace_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  exact Complex.re_ofReal_mul _ _

/-- ★ **Concavity of the von Neumann entropy.** For a finite mixture `σ = ∑ᵢ pᵢ ρᵢ` of density
matrices with weights `pᵢ ≥ 0` summing to one, and `σ` of full support (Klein's condition),
`∑ᵢ pᵢ S(ρᵢ) ≤ S(σ)`. Proof: `S(σ) − ∑ᵢ pᵢ S(ρᵢ) = ∑ᵢ pᵢ D(ρᵢ ‖ σ) ≥ 0` — the cross term
`Re Tr(σ log σ)` is the `p`-average of `Re Tr(ρᵢ log σ)`, and Klein's inequality bounds each by
`Re Tr(ρᵢ log ρᵢ) = −S(ρᵢ)`. -/
theorem vonNeumannEntropy_mixture_ge_of_posDef {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (ρ : ι → Matrix n n ℂ) (hρ : ∀ i, (ρ i).PosSemidef)
    (htr : ∀ i, (ρ i).trace = 1) (hpd : (∑ i, ((p i : ℝ) : ℂ) • ρ i).PosDef) :
    ∑ i, p i * vonNeumannEntropy (hρ i).1 ≤ vonNeumannEntropy hpd.1 := by
  set σ := ∑ i, ((p i : ℝ) : ℂ) • ρ i with hσ
  have hσtr : σ.trace = 1 := by
    rw [hσ, Matrix.trace_sum]
    simp only [Matrix.trace_smul, htr, smul_eq_mul, mul_one]
    exact_mod_cast hp1
  -- Klein for each component against the mixture
  have hklein : ∀ i, RCLike.re ((ρ i * hpd.1.cfc Real.log).trace)
      ≤ RCLike.re ((ρ i * (hρ i).1.cfc Real.log).trace) :=
    fun i => klein_inequality (hρ i) hpd (htr i) hσtr
  -- the self term of the mixture is the average of the cross terms
  have hcross : RCLike.re ((σ * hpd.1.cfc Real.log).trace)
      = ∑ i, p i * RCLike.re ((ρ i * hpd.1.cfc Real.log).trace) :=
    re_trace_finset_sum_smul_mul Finset.univ p ρ _
  have hself := re_trace_self_log_eq_neg_vonNeumannEntropy hpd.1
  have hselfi : ∀ i, RCLike.re ((ρ i * (hρ i).1.cfc Real.log).trace) = -vonNeumannEntropy (hρ i).1 :=
    fun i => re_trace_self_log_eq_neg_vonNeumannEntropy (hρ i).1
  have hsum : ∑ i, p i * RCLike.re ((ρ i * hpd.1.cfc Real.log).trace)
      ≤ ∑ i, p i * RCLike.re ((ρ i * (hρ i).1.cfc Real.log).trace) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hklein i) (hp i)
  simp only [hselfi] at hsum
  rw [← hcross, hself] at hsum
  have : ∑ i, p i * -vonNeumannEntropy (hρ i).1 = -∑ i, p i * vonNeumannEntropy (hρ i).1 := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [this] at hsum
  linarith

/-- **The Holevo quantity** `χ = S(∑ᵢ pᵢ ρᵢ) − ∑ᵢ pᵢ S(ρᵢ)` of an ensemble. -/
noncomputable def holevoChi {ι : Type*} [Fintype ι] (p : ι → ℝ) {ρ : ι → Matrix n n ℂ}
    (hρ : ∀ i, (ρ i).IsHermitian) (hσ : (∑ i, ((p i : ℝ) : ℂ) • ρ i).IsHermitian) : ℝ :=
  vonNeumannEntropy hσ - ∑ i, p i * vonNeumannEntropy (hρ i)

/-- ★ **The Holevo quantity is non-negative** (concavity restated). -/
theorem holevoChi_nonneg_of_posDef {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (ρ : ι → Matrix n n ℂ) (hρ : ∀ i, (ρ i).PosSemidef)
    (htr : ∀ i, (ρ i).trace = 1) (hpd : (∑ i, ((p i : ℝ) : ℂ) • ρ i).PosDef) :
    0 ≤ holevoChi p (fun i => (hρ i).1) hpd.1 :=
  sub_nonneg.mpr (vonNeumannEntropy_mixture_ge_of_posDef p hp hp1 ρ hρ htr hpd)

end QuantumInfo
