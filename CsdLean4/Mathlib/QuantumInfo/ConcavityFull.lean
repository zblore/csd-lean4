/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.HolevoBound

/-!
# Concavity of the von Neumann entropy without the support hypothesis

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

`Concavity.lean` proves `∑ᵢ pᵢ S(ρᵢ) ≤ S(∑ᵢ pᵢ ρᵢ)` under Klein's full-support condition on the
mixture. This file removes it:

* `mixOne A ε = (1 − ε) A + (ε / N) I` — mixing with the maximally mixed state keeps density
  matrices density matrices (`mixOne_posSemidef`, `mixOne_trace`), makes them positive definite
  for `ε > 0` (`mixOne_posDef`), commutes with mixtures (`sum_smul_mixOne`), and acts on the
  spectrum affinely, so its entropy is explicit: ★ `vonNeumannEntropy_mixOne`,
  `S(mixOne A ε) = ∑ᵢ negMulLog ((1 − ε) λᵢ + ε / N)` (via `cfc_eq_conj_diagonal` in the
  eigenbasis of `A`);
* ★ `vonNeumannEntropy_mixture_ge` — **concavity with no support hypothesis**: the supported
  inequality holds for the `mixOne`s at every `ε ∈ (0, 1)`, both sides are continuous in `ε`,
  and the set where a continuous inequality holds is closed, so it holds at `ε = 0`;
* ★ `holevoChi_nonneg` — the Holevo quantity of any ensemble of density matrices is
  non-negative.

Consumers: `CsdLean4/LF2/PreparationCoarseGraining.lean` (mixing preparations on `Σ`),
`CsdLean4/Empirical/CSD/ChannelCapacity.lean` (`holevoChi2_nonneg`).
-/

@[expose] public section

open Matrix
open scoped ComplexOrder


namespace QuantumInfo

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Mixing with the maximally mixed state: explicit spectrum -/

/-- `A` mixed with the maximally mixed state: `(1 − ε) A + (ε / N) I`. -/
noncomputable def mixOne (A : Matrix n n ℂ) (ε : ℝ) : Matrix n n ℂ :=
  ((1 - ε : ℝ) : ℂ) • A + ((ε / Fintype.card n : ℝ) : ℂ) • (1 : Matrix n n ℂ)

theorem mixOne_zero (A : Matrix n n ℂ) : mixOne A 0 = A := by
  simp [mixOne]

theorem mixOne_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) (ε : ℝ) :
    (mixOne A ε).IsHermitian := by
  unfold Matrix.IsHermitian mixOne
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hA.eq, Matrix.conjTranspose_one,
    Complex.star_def, Complex.conj_ofReal]

theorem mixOne_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef) {ε : ℝ} (h0 : 0 ≤ ε)
    (h1 : ε ≤ 1) : (mixOne A ε).PosSemidef :=
  (hA.smul (Complex.zero_le_real.mpr (by linarith))).add
    (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by positivity)))

theorem mixOne_posDef {A : Matrix n n ℂ} (hA : A.PosSemidef) {ε : ℝ} (h0 : 0 < ε)
    (h1 : ε ≤ 1) [Nonempty n] : (mixOne A ε).PosDef := by
  unfold mixOne
  rw [add_comm]
  refine Matrix.PosDef.add_posSemidef (Matrix.PosDef.one.smul ?_)
    (hA.smul (Complex.zero_le_real.mpr (by linarith)))
  rw [Complex.zero_lt_real]
  have : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  positivity

theorem mixOne_trace {A : Matrix n n ℂ} (htr : A.trace = 1) (ε : ℝ) [Nonempty n] :
    (mixOne A ε).trace = 1 := by
  have hc : (Fintype.card n : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [mixOne, Matrix.trace_add, Matrix.trace_smul, htr, Matrix.trace_one, smul_eq_mul, mul_one]
  push_cast
  field_simp
  ring

/-- The mixture of the `mixOne`s is the `mixOne` of the mixture. -/
theorem sum_smul_mixOne {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp1 : ∑ i, p i = 1)
    (ρ : ι → Matrix n n ℂ) (ε : ℝ) :
    ∑ i, ((p i : ℝ) : ℂ) • mixOne (ρ i) ε = mixOne (∑ i, ((p i : ℝ) : ℂ) • ρ i) ε := by
  simp only [mixOne, smul_add, Finset.sum_add_distrib, smul_smul, Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  · rw [← Finset.sum_smul]
    congr 1
    have : ∑ i, ((p i : ℝ) : ℂ) = 1 := by exact_mod_cast hp1
    rw [← Finset.sum_mul, this, one_mul]

/-- **The entropy of `mixOne A ε` is explicit**: `∑ᵢ negMulLog ((1 − ε) λᵢ + ε / N)` in the
eigenvalues of `A`, since `mixOne` acts on the spectrum affinely (same eigenvectors). -/
theorem vonNeumannEntropy_mixOne {A : Matrix n n ℂ} (hA : A.IsHermitian) (ε : ℝ) :
    vonNeumannEntropy (mixOne_isHermitian hA ε)
      = ∑ i, Real.negMulLog ((1 - ε) * hA.eigenvalues i + ε / Fintype.card n) := by
  set W : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hW
  have hWW : star W * W = 1 := Matrix.UnitaryGroup.star_mul_self _
  have hWW' : W * star W = 1 := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  have hspec : A = W * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * star W := by
    conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  set d : n → ℝ := fun i => (1 - ε) * hA.eigenvalues i + ε / Fintype.card n with hd
  have hMeq : mixOne A ε = W * diagonal (fun i => ((d i : ℝ) : ℂ)) * star W := by
    have hD : diagonal (fun i => ((d i : ℝ) : ℂ))
        = ((1 - ε : ℝ) : ℂ) • diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ))
          + ((ε / Fintype.card n : ℝ) : ℂ) • (1 : Matrix n n ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [hd]
      · simp [hij]
    rw [hD, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hWW', ← hspec]
    rfl
  rw [vonNeumannEntropy_eq_re_trace_cfc, cfc_eq_conj_diagonal (mixOne_isHermitian hA ε) hWW d hMeq,
    Matrix.trace_mul_cycle, hWW, Matrix.one_mul, Matrix.trace_diagonal, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Complex.ofReal_re _

/-! ### Concavity without the support hypothesis -/

/-- ★ **Concavity of the von Neumann entropy, no support hypothesis.** For any finite mixture
`σ = ∑ᵢ pᵢ ρᵢ` of density matrices with weights `pᵢ ≥ 0` summing to one,
`∑ᵢ pᵢ S(ρᵢ) ≤ S(σ)`. Proof: mix everything with the maximally mixed state,
`ρᵢ ↦ (1−ε) ρᵢ + (ε/N) I`; the mixture is then positive definite and the supported version
applies; both sides are explicit continuous functions of `ε` (`vonNeumannEntropy_mixOne`), so
the inequality on `(0, 1)` passes to `ε = 0` by closedness. -/
theorem vonNeumannEntropy_mixture_ge {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (ρ : ι → Matrix n n ℂ) (hρ : ∀ i, (ρ i).PosSemidef)
    (htr : ∀ i, (ρ i).trace = 1) :
    ∑ i, p i * vonNeumannEntropy (hρ i).1
      ≤ vonNeumannEntropy (posSemidef_finset_sum_smul Finset.univ p hp hρ).1 := by
  -- `ι` is nonempty (the weights sum to one) and hence `n` is nonempty (a trace is one)
  obtain ⟨i₀⟩ : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hp1
  have : Nonempty n := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := htr i₀
    simp [Matrix.trace] at this
  set σ := ∑ i, ((p i : ℝ) : ℂ) • ρ i with hσ
  have hσpsd : σ.PosSemidef := posSemidef_finset_sum_smul Finset.univ p hp hρ
  -- the two sides as explicit functions of ε
  set F : ℝ → ℝ := fun ε => ∑ i, p i * ∑ k, Real.negMulLog
    ((1 - ε) * (hρ i).1.eigenvalues k + ε / Fintype.card n) with hF
  set G : ℝ → ℝ := fun ε => ∑ k, Real.negMulLog
    ((1 - ε) * hσpsd.1.eigenvalues k + ε / Fintype.card n) with hG
  have hFc : Continuous F := by
    refine continuous_finsetSum _ fun i _ => Continuous.mul continuous_const ?_
    exact continuous_finsetSum _ fun k _ => Real.continuous_negMulLog.comp (by fun_prop)
  have hGc : Continuous G := by
    exact continuous_finsetSum _ fun k _ => Real.continuous_negMulLog.comp (by fun_prop)
  -- the supported inequality on (0, 1)
  have hIoo : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, F ε ≤ G ε := by
    intro ε hε
    have hmix := sum_smul_mixOne p hp1 ρ ε
    have hpd : (∑ i, ((p i : ℝ) : ℂ) • mixOne (ρ i) ε).PosDef := by
      rw [hmix]; exact mixOne_posDef hσpsd hε.1 hε.2.le
    have h := vonNeumannEntropy_mixture_ge_of_posDef p hp hp1 (fun i => mixOne (ρ i) ε)
      (fun i => mixOne_posSemidef (hρ i) hε.1.le hε.2.le)
      (fun i => mixOne_trace (htr i) ε) hpd
    have hL : ∑ i, p i * vonNeumannEntropy (mixOne_posSemidef (hρ i) hε.1.le hε.2.le).1 = F ε := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [vonNeumannEntropy_congr _ (mixOne_isHermitian (hρ i).1 ε), vonNeumannEntropy_mixOne]
    have hR : vonNeumannEntropy hpd.1 = G ε := by
      rw [vonNeumannEntropy_congr_of_eq hpd.1 (mixOne_isHermitian hσpsd.1 ε) hmix,
        vonNeumannEntropy_mixOne]
    rw [hL, hR] at h
    exact h
  -- pass to ε = 0 by closedness
  have hclosed : IsClosed {ε : ℝ | F ε ≤ G ε} := isClosed_le hFc hGc
  have h0 : (0 : ℝ) ∈ {ε : ℝ | F ε ≤ G ε} := by
    have hsub : Set.Ioo (0 : ℝ) 1 ⊆ {ε : ℝ | F ε ≤ G ε} := fun ε hε => hIoo ε hε
    have := hclosed.closure_subset_iff.mpr hsub
    rw [closure_Ioo zero_ne_one] at this
    exact this (Set.left_mem_Icc.mpr zero_le_one)
  have hF0 : F 0 = ∑ i, p i * vonNeumannEntropy (hρ i).1 := by
    simp [hF, vonNeumannEntropy]
  have hG0 : G 0 = vonNeumannEntropy hσpsd.1 := by
    simp [hG, vonNeumannEntropy]
  simp only [Set.mem_ofPred_eq] at h0
  rw [hF0, hG0] at h0
  exact h0

/-- ★ **The Holevo quantity is non-negative, no support hypothesis.** -/
theorem holevoChi_nonneg {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (ρ : ι → Matrix n n ℂ) (hρ : ∀ i, (ρ i).PosSemidef)
    (htr : ∀ i, (ρ i).trace = 1) :
    0 ≤ holevoChi p (fun i => (hρ i).1) (posSemidef_finset_sum_smul Finset.univ p hp hρ).1 :=
  sub_nonneg.mpr (vonNeumannEntropy_mixture_ge p hp hp1 ρ hρ htr)

end QuantumInfo
