/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Concavity
public import CsdLean4.Mathlib.QuantumInfo.Channel

/-!
# The Holevo bound and the single-letter Holevo range of a channel

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

* `isHermitian_finset_sum_smul`, `posSemidef_finset_sum_smul`, `trace_finset_sum_smul_eq_one` —
  a mixture of density matrices is a density matrix;
* `holevoChi_le_vonNeumannEntropy`, ★ `holevoChi_le_log_card` — **the Holevo bound**
  `χ ≤ S(∑ᵢ pᵢ ρᵢ) ≤ log (dim)`, with no support hypothesis (only the non-negativity of the
  components' entropies is used);
* `holevoRange Φ` — the set of single-letter Holevo quantities of the outputs of a channel over
  all finite ensembles of density matrices, and ★ `holevoRange_le_log_card`: every one is at
  most `log` of the output dimension. The greatest element of `holevoRange Φ`, when it exists, is
  the single-letter Holevo capacity of `Φ`; `CsdLean4/LF6/DeisolationCapacity.lean` exhibits it for
  the de-isolation channel. The regularised classical capacity (many channel uses) is not defined
  here.
-/

@[expose] public section

open Matrix
open scoped ComplexOrder

/-! ### The Holevo bound (Cat-1) -/

namespace QuantumInfo

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- A real mixture of Hermitian matrices is Hermitian. -/
theorem isHermitian_finset_sum_smul {ι : Type*} (s : Finset ι) (p : ι → ℝ) {ρ : ι → Matrix n n ℂ}
    (hρ : ∀ i, (ρ i).IsHermitian) : (∑ i ∈ s, ((p i : ℝ) : ℂ) • ρ i).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_smul, (hρ i).eq, Complex.star_def, Complex.conj_ofReal]

omit [Fintype n] [DecidableEq n] in
/-- A mixture of positive semidefinite matrices with non-negative weights is positive semidefinite. -/
theorem posSemidef_finset_sum_smul {ι : Type*} (s : Finset ι) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    {ρ : ι → Matrix n n ℂ} (hρ : ∀ i, (ρ i).PosSemidef) :
    (∑ i ∈ s, ((p i : ℝ) : ℂ) • ρ i).PosSemidef :=
  Matrix.posSemidef_sum _ fun i _ => (hρ i).smul (Complex.zero_le_real.mpr (hp i))

omit [DecidableEq n] in
/-- The trace of a mixture of trace-one matrices with weights summing to one is one. -/
theorem trace_finset_sum_smul_eq_one {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp1 : ∑ i, p i = 1)
    {ρ : ι → Matrix n n ℂ} (htr : ∀ i, (ρ i).trace = 1) :
    (∑ i, ((p i : ℝ) : ℂ) • ρ i).trace = 1 := by
  rw [Matrix.trace_sum]
  simp only [Matrix.trace_smul, htr, smul_eq_mul, mul_one]
  exact_mod_cast hp1

/-- The Holevo quantity is at most the entropy of the average state. -/
theorem holevoChi_le_vonNeumannEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    {ρ : ι → Matrix n n ℂ} (hρ : ∀ i, (ρ i).PosSemidef) (htr : ∀ i, (ρ i).trace = 1)
    (hσ : (∑ i, ((p i : ℝ) : ℂ) • ρ i).IsHermitian) :
    holevoChi p (fun i => (hρ i).1) hσ ≤ vonNeumannEntropy hσ := by
  unfold holevoChi
  have : 0 ≤ ∑ i, p i * vonNeumannEntropy (hρ i).1 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (vonNeumannEntropy_nonneg (hρ i) (htr i))
  linarith

/-- ★ **The Holevo bound**: `χ ≤ log (dim)`. -/
theorem holevoChi_le_log_card {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) {ρ : ι → Matrix n n ℂ} (hρ : ∀ i, (ρ i).PosSemidef)
    (htr : ∀ i, (ρ i).trace = 1) (hσ : (∑ i, ((p i : ℝ) : ℂ) • ρ i).IsHermitian) :
    holevoChi p (fun i => (hρ i).1) hσ ≤ Real.log (Fintype.card n) :=
  (holevoChi_le_vonNeumannEntropy p hp hρ htr hσ).trans
    (vonNeumannEntropy_le_log_card (posSemidef_finset_sum_smul Finset.univ p hp hρ)
      (trace_finset_sum_smul_eq_one p hp1 htr))

/-- **The single-letter Holevo range of a channel**: the Holevo quantities of the channel outputs
of all finite ensembles of density matrices. Its greatest element, when it exists, is the
single-letter Holevo capacity. -/
def holevoRange {m ι' : Type*} [Fintype m] [Fintype ι'] [DecidableEq m] (Φ : Channel n m ι') :
    Set ℝ :=
  {x | ∃ (k : ℕ) (p : Fin k → ℝ) (ρ : Fin k → Matrix n n ℂ) (_ : ∀ i, 0 ≤ p i)
    (_ : ∑ i, p i = 1) (hρ : ∀ i, (ρ i).PosSemidef) (_ : ∀ i, (ρ i).trace = 1),
    x = holevoChi p (fun i => Φ.apply_isHermitian (hρ i).1)
      (isHermitian_finset_sum_smul Finset.univ p fun i => Φ.apply_isHermitian (hρ i).1)}

/-- ★ **Every single-letter Holevo quantity of a channel is at most `log (dim)` of the output.** -/
theorem holevoRange_le_log_card {m ι' : Type*} [Fintype m] [Fintype ι'] [DecidableEq m]
    (Φ : Channel n m ι') {x : ℝ} (hx : x ∈ holevoRange Φ) : x ≤ Real.log (Fintype.card m) := by
  obtain ⟨k, p, ρ, hp, hp1, hρ, htr, rfl⟩ := hx
  exact holevoChi_le_log_card p hp hp1 (fun i => Φ.apply_posSemidef (hρ i))
    (fun i => (Φ.apply_trace (ρ i)).trans (htr i)) _

end QuantumInfo
