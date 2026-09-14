/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Thermo.Jarzynski
public import CsdLean4.LF4.ProjectedDynamics
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Dynamics.BirkhoffSum.Average

/-!
# TH5c: the eigenstate thermalisation hypothesis as a hypothesis field, and what follows from it

**Category:** 3-Local (conceptually 1-Mathlib; CSD-free finite-dimensional quantum
statistical mechanics) with a CSD reading; kept in the `CSD.Thermo` tree alongside TH1–TH5d
(`specs/thermo-plan.md` TH5; `specs/BACKLOG.md` ▶ OPEN QUEUE #3).

## What ETH is, and what this module does and doesn't claim

The eigenstate thermalisation hypothesis (Deutsch 1991, Srednicki 1994) says that for a
generic many-body Hamiltonian the diagonal matrix elements `⟨eₙ, A eₙ⟩` of a physical
observable vary smoothly with the energy, so `⟨eₙ, A eₙ⟩ ≈ f(Eₙ)` for a smooth `f`. It's a
statement about which Hamiltonians are generic and belongs to random-matrix theory, and the
corpus doesn't prove it (BACKLOG #21, research). This module does the other half. It states ETH
as a **hypothesis field** `SatisfiesETH` and proves what a system that satisfies it does.

1. **dephasing.** Sample the Heisenberg expectation `⟨A⟩ₜ = ⟨ψₜ, A ψₜ⟩` along the Schrödinger
   orbit `ψₜ = exp(−itτH) ψ` at a timestep `τ`. Its Birkhoff (time) average converges, and the
   limit is the **diagonal ensemble** value `∑ₙ |cₙ|² ⟨eₙ, A eₙ⟩`, as long as the sampled phases
   `e^{iτ(Eₙ − Eₘ)}` are never `1` for `n ≠ m` (`Nonresonant`). Every off-diagonal term is a
   geometric sequence on the unit circle with ratio `≠ 1`, and those average to zero.
2. **ETH turns the diagonal ensemble into a function of the energy.** If `SatisfiesETH` holds
   with tolerance `ε`, the diagonal ensemble is within `ε` of `∑ₙ |cₙ|² f(Eₙ)`. If moreover the
   state lives in an energy window of half-width `δ` around `E` on which `f` moves by at most `η`,
   both the time average and the **microcanonical** average of `⟨eₙ, A eₙ⟩` over that window are
   within `ε + η` of `f(E)`, so the time average is within `2(ε + η)` of the microcanonical
   value. That's thermalisation, as the long-time value of `A` then depends on the initial
   state only through its energy.

## Main results

* `energyPhase hH τ n = e^{−iτEₙ}`; `schrodingerUnitary_eq_conj` (the Schrödinger unitary in
  the eigenbasis is the diagonal of phases), `schrodingerUnitary_pow_mulVec` (its powers act on
  the eigencoordinates by powers of the phases);
* `heisenbergObs A v = re ⟨v, A v⟩`, `eigenCoord hH ψ n = ⟨eₙ, ψ⟩`, `diagonalEnsemble hH A ψ`;
* `tendsto_cesaro_geom` — the Cesàro average of a unit-modulus geometric sequence with ratio
  `≠ 1` tends to `0`; `tendsto_cesaro_trigPoly` — a finite sum of such sequences averages to the
  sum of its ratio-one coefficients;
* ★★ `tendsto_birkhoffAverage_heisenbergObs` (**dephasing**): under `Nonresonant hH τ`, the
  Birkhoff average of `heisenbergObs A` along `v ↦ U v` converges to the diagonal ensemble;
  `nonresonant_of_nondegenerate` — a non-degenerate spectrum sampled with a timestep smaller
  than `2π / max|Eₙ − Eₘ|` is nonresonant;
* `SatisfiesETH hH A f ε`, `microcanonicalDiag hH A E δ`;
* ★ `abs_diagonalEnsemble_sub_le_of_eth` (the diagonal ensemble tracks `f` to within `ε`),
  ★ `abs_diagonalEnsemble_sub_le_of_window` (within `ε + η` of `f(E)` on a window),
  ★ `abs_microcanonicalDiag_sub_le` (the microcanonical average too);
* ★★ `eth_time_average` (**TH5c**): under nonresonance, ETH, and an energy window, the
  time average converges to a value within `2(ε + η)` of the microcanonical value.

## CSD reading

Records read `⟨A⟩ₜ` at the sampled times, and the Birkhoff average is the record frequency the
long run delivers (`Thermo/Equilibration.lean` sets this up for the same `birkhoffAverage`).
Nothing here needs mixing, which `Equilibration.lean` proves unitary dynamics can't supply. The
mechanism is dephasing of the off-diagonal terms, and it holds for every finite-dimensional
unitary orbit once the sampling is nonresonant. What ETH adds is that the value the records
settle to depends on the preparation only through its energy, so an apparatus can't tell
thermal preparations apart by their long-time averages. Whether the de-isolation dynamics of
`Σ` produces Hamiltonians that satisfy ETH is BACKLOG #21.

## Honest scope

* **Discrete sampling.** The time average is Mathlib's `birkhoffAverage` along the one-step
  map `v ↦ exp(−iτH) v`, as in `Equilibration.lean`. The continuous-time average `(1/T)∫₀ᵀ` is
  not stated; it's the same dephasing with `∫e^{iωt}` in place of the geometric sum.
* **Nonresonance is a hypothesis about the timestep**, not only about the spectrum. A
  non-degenerate spectrum makes every sufficiently small timestep nonresonant
  (`nonresonant_of_nondegenerate`), and a resonant timestep genuinely fails to dephase.
* ETH is stated for the **diagonal** elements only, which is all the time average sees, so the
  off-diagonal part of ETH (the `e^{−S/2}` suppression that governs fluctuations) isn't stated.
* Finite dimension, one observable, one state; no bath.

## Provenance

Foundational-triple only; no `sorry`, no new axioms. Consumes TH3/TH5a's eigenbasis lemmas,
`LF4/ProjectedDynamics.lean`'s `schrodingerUnitary`, and Mathlib's matrix exponential,
`geom_sum_eq`, `birkhoffAverage` and `Complex.exp_eq_one_iff`.

## References

`specs/thermo-plan.md` TH5; `specs/BACKLOG.md` (▶ OPEN QUEUE #3; #21 for ETH itself);
`Thermo/Equilibration.lean` (E4, the same `birkhoffAverage`; `not_hasCorrelationDecay_blockPop_of_unitary`);
`Thermo/Jarzynski.lean` (`star_dotProduct_eigenvectorBasis_self`);
`Thermo/FreeEnergy.lean` (`eigenvectorUnitary_isUnit`, `smul_conj`);
`LF4/ProjectedDynamics.lean` (`schrodingerUnitary`, `schrodingerGen`); `specs/future-work.md`.
-/

@[expose] public section

open scoped BigOperators ComplexOrder
open Matrix Filter Topology

namespace CSD
namespace Thermo

variable {N : ℕ} {H : Matrix (Fin N) (Fin N) ℂ}

/-! ## The Schrödinger unitary in the eigenbasis -/

/-- The phase `e^{−iτEₙ}` the `n`-th eigenvector picks up in one timestep. -/
noncomputable def energyPhase (hH : H.IsHermitian) (τ : ℝ) (n : Fin N) : ℂ :=
  Complex.exp (-(τ : ℂ) * Complex.I * (hH.eigenvalues n : ℂ))

lemma norm_energyPhase (hH : H.IsHermitian) (τ : ℝ) (n : Fin N) :
    ‖energyPhase hH τ n‖ = 1 := by
  rw [energyPhase, Complex.norm_exp]
  have : (-(τ : ℂ) * Complex.I * (hH.eigenvalues n : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero]

lemma star_energyPhase (hH : H.IsHermitian) (τ : ℝ) (n : Fin N) :
    star (energyPhase hH τ n) = Complex.exp ((τ : ℂ) * Complex.I * (hH.eigenvalues n : ℂ)) := by
  rw [energyPhase, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- **The Schrödinger unitary in the eigenbasis**: `exp(−iτH) = V · diag(e^{−iτEₙ}) · Vᴴ`. -/
theorem schrodingerUnitary_eq_conj (hH : H.IsHermitian) (τ : ℝ) :
    (LF4.schrodingerUnitary hH τ : Matrix (Fin N) (Fin N) ℂ)
      = (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
        * diagonal (energyPhase hH τ) * star (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) := by
  have hspec : H = (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * diagonal (RCLike.ofReal ∘ hH.eigenvalues)
      * star (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hinv : (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)⁻¹
      = star (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) :=
    Matrix.inv_eq_left_inv (Unitary.coe_star_mul_self _)
  have hgen : LF4.schrodingerGen H τ
      = (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
        * diagonal ((-(τ : ℂ) * Complex.I) • (RCLike.ofReal ∘ hH.eigenvalues))
        * star (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) := by
    rw [LF4.schrodingerGen, ← smul_conj]
    congr 1
  have hd : NormedSpace.exp ((-(τ : ℂ) * Complex.I) • (RCLike.ofReal ∘ hH.eigenvalues))
      = energyPhase hH τ := by
    funext n
    rw [Pi.exp_def]
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    rw [energyPhase, ← Complex.exp_eq_exp_ℂ]
    rfl
  show NormedSpace.exp (LF4.schrodingerGen H τ) = _
  rw [hgen, ← hinv, Matrix.exp_conj _ _ (eigenvectorUnitary_isUnit H hH), Matrix.exp_diagonal,
    hinv, hd]

/-- The eigencoordinates of `ψ`: `cₙ = ⟨eₙ, ψ⟩`. -/
noncomputable def eigenCoord (hH : H.IsHermitian) (ψ : Fin N → ℂ) (n : Fin N) : ℂ :=
  star ⇑(hH.eigenvectorBasis n) ⬝ᵥ ψ

lemma eigenCoord_eq_star_mulVec (hH : H.IsHermitian) (ψ : Fin N → ℂ) :
    eigenCoord hH ψ = star (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) *ᵥ ψ := by
  funext n
  rw [eigenCoord, ← hH.eigenvectorUnitary_col_eq]
  rfl

/-- **The powers of the Schrödinger unitary act on the eigencoordinates by powers of the
phases**: `Uᵗ ψ = V · (e^{−iτEₙ t} cₙ)ₙ`. -/
theorem schrodingerUnitary_pow_mulVec (hH : H.IsHermitian) (τ : ℝ) (t : ℕ) (ψ : Fin N → ℂ) :
    ((LF4.schrodingerUnitary hH τ : Matrix (Fin N) (Fin N) ℂ) ^ t) *ᵥ ψ
      = (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
          *ᵥ (fun n => energyPhase hH τ n ^ t * eigenCoord hH ψ n) := by
  have hconj : ∀ k : ℕ,
      ((hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) * diagonal (energyPhase hH τ)
        * star (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)) ^ k
      = (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) * diagonal (energyPhase hH τ) ^ k
        * star (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, pow_zero, Matrix.mul_one]
      exact (Unitary.coe_mul_star_self _).symm
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ))
        (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ), Unitary.coe_star_mul_self,
        Matrix.one_mul]
  rw [schrodingerUnitary_eq_conj, hconj, diagonal_pow, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← eigenCoord_eq_star_mulVec]
  congr 1
  funext n
  rw [Matrix.mulVec_diagonal, Pi.pow_apply]

/-! ## The Heisenberg time series -/

/-- The expectation `re ⟨v, A v⟩` of `A` in the (unnormalised) vector `v`. -/
noncomputable def heisenbergObs (A : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) : ℝ :=
  RCLike.re (star v ⬝ᵥ (A *ᵥ v))

/-- `A` read in the eigenbasis of `H`: `Ã = Vᴴ A V`, with `Ãₙₘ = ⟨eₙ, A eₘ⟩`. -/
noncomputable def eigenMatrix (hH : H.IsHermitian) (A : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  star (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) * A * hH.eigenvectorUnitary

lemma eigenMatrix_apply (hH : H.IsHermitian) (A : Matrix (Fin N) (Fin N) ℂ) (n m : Fin N) :
    eigenMatrix hH A n m
      = star ⇑(hH.eigenvectorBasis n) ⬝ᵥ (A *ᵥ ⇑(hH.eigenvectorBasis m)) := by
  rw [eigenMatrix, Matrix.mul_assoc, ← hH.eigenvectorUnitary_col_eq,
    ← hH.eigenvectorUnitary_col_eq]
  rfl

/-- The quadratic form of `A` in a vector `V w` is the quadratic form of `Ã` in `w`. -/
lemma star_mulVec_dotProduct (hH : H.IsHermitian) (A : Matrix (Fin N) (Fin N) ℂ)
    (w : Fin N → ℂ) :
    star ((hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) *ᵥ w)
        ⬝ᵥ (A *ᵥ ((hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) *ᵥ w))
      = star w ⬝ᵥ (eigenMatrix hH A *ᵥ w) := by
  have hL : star ((hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) *ᵥ w)
        ⬝ᵥ (A *ᵥ ((hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) *ᵥ w))
      = (star w ᵥ* ((hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)ᴴ
          * (A * (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)))) ⬝ᵥ w := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, Matrix.vecMul_vecMul]
  have hR : star w ⬝ᵥ (eigenMatrix hH A *ᵥ w)
      = (star w ᵥ* ((hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)ᴴ
          * (A * (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)))) ⬝ᵥ w := by
    rw [Matrix.dotProduct_mulVec, eigenMatrix, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  rw [hL, hR]

/-- The quadratic form as a double sum over the eigenbasis. -/
lemma star_dotProduct_mulVec_eq_sum (M : Matrix (Fin N) (Fin N) ℂ) (w : Fin N → ℂ) :
    star w ⬝ᵥ (M *ᵥ w) = ∑ n, ∑ m, star (w n) * M n m * w m := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring

/-- **The Heisenberg time series is a trigonometric polynomial**: sampled at timestep `τ`,
`⟨A⟩ₜ = re ∑ₙₘ (c̄ₙ Ãₙₘ cₘ) · (e^{iτ(Eₙ − Eₘ)})ᵗ`. -/
theorem heisenbergObs_pow (hH : H.IsHermitian) (τ : ℝ) (A : Matrix (Fin N) (Fin N) ℂ)
    (ψ : Fin N → ℂ) (t : ℕ) :
    heisenbergObs A (((LF4.schrodingerUnitary hH τ : Matrix (Fin N) (Fin N) ℂ) ^ t) *ᵥ ψ)
      = RCLike.re (∑ n, ∑ m,
          (star (eigenCoord hH ψ n) * eigenMatrix hH A n m * eigenCoord hH ψ m)
            * (star (energyPhase hH τ n) * energyPhase hH τ m) ^ t) := by
  rw [heisenbergObs, schrodingerUnitary_pow_mulVec, star_mulVec_dotProduct,
    star_dotProduct_mulVec_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  rw [star_mul', star_pow, mul_pow]
  ring

/-! ## Cesàro averages of geometric sequences on the unit circle -/

/-- **A unit-modulus geometric sequence with ratio `≠ 1` has Cesàro average tending to `0`.** -/
theorem tendsto_cesaro_geom {l : ℂ} (hl : ‖l‖ = 1) (h1 : l ≠ 1) :
    Tendsto (fun T : ℕ => (T : ℂ)⁻¹ * ∑ t ∈ Finset.range T, l ^ t) atTop (𝓝 0) := by
  have hne : ‖l - 1‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h1)
  refine squeeze_zero_norm (fun T => ?_) (tendsto_const_div_atTop_nhds_zero_nat (2 / ‖l - 1‖))
  rw [geom_sum_eq h1, norm_mul, norm_inv, Complex.norm_natCast, norm_div,
    div_eq_mul_inv (2 / ‖l - 1‖), mul_comm (2 / ‖l - 1‖), div_eq_mul_inv 2]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Nat.cast_nonneg T))
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (norm_nonneg _))
  calc ‖l ^ T - 1‖ ≤ ‖l ^ T‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hl, one_pow, norm_one]; norm_num

/-- The Cesàro average of the constant sequence `1` tends to `1`. -/
theorem tendsto_cesaro_one :
    Tendsto (fun T : ℕ => (T : ℂ)⁻¹ * ∑ t ∈ Finset.range T, (1 : ℂ) ^ t) atTop (𝓝 1) := by
  have h : ∀ T : ℕ, 1 ≤ T → (T : ℂ)⁻¹ * ∑ t ∈ Finset.range T, (1 : ℂ) ^ t = 1 := by
    intro T hT
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (by omega))
  exact tendsto_const_nhds.congr' (Filter.eventually_atTop.mpr ⟨1, fun T hT => (h T hT).symm⟩)

/-- **A finite sum of unit-modulus geometric sequences averages to the sum of its ratio-one
coefficients.** -/
theorem tendsto_cesaro_trigPoly {ι : Type*} [Fintype ι]
    (α l : ι → ℂ) (hl : ∀ q, ‖l q‖ = 1) :
    Tendsto (fun T : ℕ => (T : ℂ)⁻¹ * ∑ t ∈ Finset.range T, ∑ q, α q * l q ^ t) atTop
      (𝓝 (∑ q, if l q = 1 then α q else 0)) := by
  have hrw : ∀ T : ℕ, (T : ℂ)⁻¹ * ∑ t ∈ Finset.range T, ∑ q, α q * l q ^ t
      = ∑ q, α q * ((T : ℂ)⁻¹ * ∑ t ∈ Finset.range T, l q ^ t) := by
    intro T
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Finset.mul_sum, mul_left_comm]
  simp_rw [hrw]
  refine tendsto_finsetSum _ fun q _ => ?_
  by_cases hq : l q = 1
  · rw [if_pos hq, hq]
    simpa using tendsto_cesaro_one.const_mul (α q)
  · rw [if_neg hq]
    simpa using (tendsto_cesaro_geom (hl q) hq).const_mul (α q)

/-! ## ★★ Dephasing: the time average is the diagonal ensemble -/

/-- **Nonresonant sampling**: no two distinct eigenvectors have the same sampled phase,
`e^{iτ(Eₙ − Eₘ)} ≠ 1` for `n ≠ m`. -/
def Nonresonant (hH : H.IsHermitian) (τ : ℝ) : Prop :=
  ∀ n m, n ≠ m → star (energyPhase hH τ n) * energyPhase hH τ m ≠ 1

/-- **The diagonal ensemble**: `∑ₙ |cₙ|² ⟨eₙ, A eₙ⟩`, the value the time average settles to. -/
noncomputable def diagonalEnsemble (hH : H.IsHermitian) (A : Matrix (Fin N) (Fin N) ℂ)
    (ψ : Fin N → ℂ) : ℝ :=
  ∑ n, ‖eigenCoord hH ψ n‖ ^ 2 * RCLike.re (eigenMatrix hH A n n)

/-- The iterates of `v ↦ U v` are the powers of `U`. -/
lemma mulVec_iterate (U : Matrix (Fin N) (Fin N) ℂ) (t : ℕ) (v : Fin N → ℂ) :
    (fun w : Fin N → ℂ => U *ᵥ w)^[t] v = (U ^ t) *ᵥ v := by
  induction t with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, Matrix.mulVec_mulVec, ← pow_succ']

/-- ★★ **Dephasing.** Under nonresonant sampling, the Birkhoff average of the Heisenberg
expectation of `A` along the Schrödinger orbit of `ψ` converges to the diagonal ensemble
value. The off-diagonal terms of the trigonometric polynomial `⟨A⟩ₜ` are unit-modulus
geometric sequences with ratio `≠ 1`, and their Cesàro averages vanish. -/
theorem tendsto_birkhoffAverage_heisenbergObs (hH : H.IsHermitian) {τ : ℝ}
    (hres : Nonresonant hH τ) (A : Matrix (Fin N) (Fin N) ℂ) (ψ : Fin N → ℂ) :
    Tendsto (fun T : ℕ => birkhoffAverage ℝ
        (fun v : Fin N → ℂ => (LF4.schrodingerUnitary hH τ : Matrix (Fin N) (Fin N) ℂ) *ᵥ v)
        (heisenbergObs A) T ψ)
      atTop (𝓝 (diagonalEnsemble hH A ψ)) := by
  classical
  set α : Fin N × Fin N → ℂ := fun q =>
    star (eigenCoord hH ψ q.1) * eigenMatrix hH A q.1 q.2 * eigenCoord hH ψ q.2 with hα
  set l : Fin N × Fin N → ℂ := fun q => star (energyPhase hH τ q.1) * energyPhase hH τ q.2
    with hl
  have hl1 : ∀ q, ‖l q‖ = 1 := fun q => by
    rw [hl]; simp only [norm_mul, norm_star, norm_energyPhase, mul_one]
  have hseries : ∀ T : ℕ, birkhoffAverage ℝ
        (fun v : Fin N → ℂ => (LF4.schrodingerUnitary hH τ : Matrix (Fin N) (Fin N) ℂ) *ᵥ v)
        (heisenbergObs A) T ψ
      = RCLike.re ((T : ℂ)⁻¹ * ∑ t ∈ Finset.range T, ∑ q, α q * l q ^ t) := by
    intro T
    rw [birkhoffAverage, birkhoffSum, smul_eq_mul]
    simp only [mulVec_iterate, heisenbergObs_pow, ← Fintype.sum_prod_type', RCLike.re_to_complex]
    rw [← Complex.re_sum, ← Complex.re_ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
  have hlim : (∑ q, if l q = 1 then α q else 0)
      = ∑ n, ((‖eigenCoord hH ψ n‖ ^ 2 : ℝ) : ℂ) * eigenMatrix hH A n n := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_eq_single n]
    · have hnn : l (n, n) = 1 := by
        rw [hl]
        show star (energyPhase hH τ n) * energyPhase hH τ n = 1
        rw [Complex.star_def, Complex.conj_mul', norm_energyPhase]
        norm_num
      rw [if_pos hnn, hα]
      show star (eigenCoord hH ψ n) * eigenMatrix hH A n n * eigenCoord hH ψ n = _
      rw [mul_comm (star _), mul_assoc, Complex.star_def, Complex.conj_mul', mul_comm,
        ← Complex.ofReal_pow]
    · intro m _ hm
      rw [if_neg (hres n m (Ne.symm hm))]
    · intro h
      exact absurd (Finset.mem_univ n) h
  have hmain := tendsto_cesaro_trigPoly α l hl1
  rw [hlim] at hmain
  have hre := (Complex.continuous_re.tendsto _).comp hmain
  have hval : (∑ n, ((‖eigenCoord hH ψ n‖ ^ 2 : ℝ) : ℂ) * eigenMatrix hH A n n).re
      = diagonalEnsemble hH A ψ := by
    rw [Complex.re_sum, diagonalEnsemble]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.re_ofReal_mul, RCLike.re_to_complex]
  rw [hval] at hre
  refine hre.congr' (Filter.Eventually.of_forall fun T => ?_)
  simp only [Function.comp_apply]
  rw [hseries T, RCLike.re_to_complex]

/-- **A non-degenerate spectrum sampled with a small enough timestep is nonresonant**: if
`0 < |τ(Eₙ − Eₘ)| < 2π` for all `n ≠ m`, no sampled phase ratio is `1`. -/
theorem nonresonant_of_nondegenerate (hH : H.IsHermitian) {τ : ℝ}
    (hsmall : ∀ n m, n ≠ m → 0 < |τ * (hH.eigenvalues n - hH.eigenvalues m)|
      ∧ |τ * (hH.eigenvalues n - hH.eigenvalues m)| < 2 * Real.pi) :
    Nonresonant hH τ := by
  intro n m hnm h1
  obtain ⟨hpos, hlt⟩ := hsmall n m hnm
  rw [star_energyPhase, energyPhase, ← Complex.exp_add] at h1
  have harg : (τ : ℂ) * Complex.I * (hH.eigenvalues n : ℂ)
      + -(τ : ℂ) * Complex.I * (hH.eigenvalues m : ℂ)
      = ((τ * (hH.eigenvalues n - hH.eigenvalues m) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg, Complex.exp_eq_one_iff] at h1
  obtain ⟨k, hk⟩ := h1
  have hkI : ((τ * (hH.eigenvalues n - hH.eigenvalues m) : ℝ) : ℂ) * Complex.I
      = (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
    rw [hk]; push_cast; ring
  have hk' : τ * (hH.eigenvalues n - hH.eigenvalues m) = (k : ℝ) * (2 * Real.pi) :=
    Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero hkI)
  rw [hk', abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hpos hlt
  have hk0 : (k : ℝ) ≠ 0 := fun h => by rw [h, abs_zero, zero_mul] at hpos; exact lt_irrefl _ hpos
  have hk1 : 1 ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (Int.cast_ne_zero.mp hk0)
  have : 2 * Real.pi ≤ |(k : ℝ)| * (2 * Real.pi) :=
    le_mul_of_one_le_left (by positivity) hk1
  exact absurd hlt (not_lt.mpr this)

/-! ## ETH as a hypothesis field, and what it buys -/

/-- **The eigenstate thermalisation hypothesis, diagonal form, as a hypothesis field**: the
diagonal matrix elements `⟨eₙ, A eₙ⟩` are within `ε` of a function `f` of the energy `Eₙ`. -/
def SatisfiesETH (hH : H.IsHermitian) (A : Matrix (Fin N) (Fin N) ℂ) (f : ℝ → ℝ) (ε : ℝ) :
    Prop :=
  ∀ n, |RCLike.re (eigenMatrix hH A n n) - f (hH.eigenvalues n)| ≤ ε

/-- The eigencoordinates of a unit vector carry unit total weight. -/
lemma sum_normSq_eigenCoord (hH : H.IsHermitian) (ψ : Fin N → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    ∑ n, ‖eigenCoord hH ψ n‖ ^ 2 = 1 := by
  have hVV : (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
      * star (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Unitary.coe_mul_star_self _
  have h : star (eigenCoord hH ψ) ⬝ᵥ eigenCoord hH ψ = 1 := by
    rw [eigenCoord_eq_star_mulVec, Matrix.star_mulVec, ← Matrix.star_eq_conjTranspose, star_star,
      Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hVV, Matrix.vecMul_one, hψ]
  have h' : (∑ n, ((‖eigenCoord hH ψ n‖ ^ 2 : ℝ) : ℂ)) = 1 := by
    rw [← h]
    simp only [dotProduct, Pi.star_apply]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  exact_mod_cast h'

/-- A weighted average of numbers within `ε` of their targets is within `ε` of the weighted
average of the targets. -/
lemma abs_sum_weighted_sub_le {ι : Type*} (s : Finset ι) (w a b : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1) {ε : ℝ}
    (hab : ∀ i ∈ s, w i ≠ 0 → |a i - b i| ≤ ε) :
    |∑ i ∈ s, w i * a i - ∑ i ∈ s, w i * b i| ≤ ε := by
  rw [← Finset.sum_sub_distrib]
  calc |∑ i ∈ s, (w i * a i - w i * b i)|
      ≤ ∑ i ∈ s, |w i * a i - w i * b i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, w i * |a i - b i| := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg (hw i hi)]
    _ ≤ ∑ i ∈ s, w i * ε := by
        refine Finset.sum_le_sum fun i hi => ?_
        by_cases hw0 : w i = 0
        · rw [hw0, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (hab i hi hw0) (hw i hi)
    _ = ε := by rw [← Finset.sum_mul, hsum, one_mul]

/-- ★ **ETH makes the diagonal ensemble a function of the energy distribution**: for a unit
state, `|∑ₙ |cₙ|² ⟨eₙ, A eₙ⟩ − ∑ₙ |cₙ|² f(Eₙ)| ≤ ε`. -/
theorem abs_diagonalEnsemble_sub_le_of_eth (hH : H.IsHermitian)
    {A : Matrix (Fin N) (Fin N) ℂ} {f : ℝ → ℝ} {ε : ℝ} (heth : SatisfiesETH hH A f ε)
    (ψ : Fin N → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    |diagonalEnsemble hH A ψ - ∑ n, ‖eigenCoord hH ψ n‖ ^ 2 * f (hH.eigenvalues n)| ≤ ε :=
  abs_sum_weighted_sub_le Finset.univ (fun n => ‖eigenCoord hH ψ n‖ ^ 2) _ _
    (fun n _ => by positivity) (sum_normSq_eigenCoord hH ψ hψ) (fun n _ _ => heth n)

/-- **An energy window for a state**: every eigencomponent it carries has energy within `δ`
of `E`. -/
def InEnergyWindow (hH : H.IsHermitian) (ψ : Fin N → ℂ) (E δ : ℝ) : Prop :=
  ∀ n, eigenCoord hH ψ n ≠ 0 → |hH.eigenvalues n - E| ≤ δ

/-- ★ **On an energy window where `f` is `η`-flat, the diagonal ensemble is within `ε + η` of
`f(E)`.** -/
theorem abs_diagonalEnsemble_sub_le_of_window (hH : H.IsHermitian)
    {A : Matrix (Fin N) (Fin N) ℂ} {f : ℝ → ℝ} {ε : ℝ} (heth : SatisfiesETH hH A f ε)
    {E δ η : ℝ} (hflat : ∀ x, |x - E| ≤ δ → |f x - f E| ≤ η)
    (ψ : Fin N → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) (hwin : InEnergyWindow hH ψ E δ) :
    |diagonalEnsemble hH A ψ - f E| ≤ ε + η := by
  have h1 := abs_diagonalEnsemble_sub_le_of_eth hH heth ψ hψ
  have h2 : |∑ n, ‖eigenCoord hH ψ n‖ ^ 2 * f (hH.eigenvalues n) - f E| ≤ η := by
    have hfE : f E = ∑ n, ‖eigenCoord hH ψ n‖ ^ 2 * f E := by
      rw [← Finset.sum_mul, sum_normSq_eigenCoord hH ψ hψ, one_mul]
    rw [hfE]
    refine abs_sum_weighted_sub_le Finset.univ (fun n => ‖eigenCoord hH ψ n‖ ^ 2) _ _
      (fun n _ => by positivity) (sum_normSq_eigenCoord hH ψ hψ) fun n _ hn => ?_
    refine hflat _ (hwin n fun hc => hn ?_)
    rw [hc, norm_zero, zero_pow two_ne_zero]
  calc |diagonalEnsemble hH A ψ - f E|
      = |(diagonalEnsemble hH A ψ - ∑ n, ‖eigenCoord hH ψ n‖ ^ 2 * f (hH.eigenvalues n))
          + (∑ n, ‖eigenCoord hH ψ n‖ ^ 2 * f (hH.eigenvalues n) - f E)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ ε + η := add_le_add h1 h2

/-! ## The microcanonical value, and TH5c -/

/-- **The microcanonical average of `A`** over the energy window `|Eₙ − E| ≤ δ`: the plain
average of the diagonal elements `⟨eₙ, A eₙ⟩` over the eigenstates in the window. -/
noncomputable def microcanonicalDiag (hH : H.IsHermitian) (A : Matrix (Fin N) (Fin N) ℂ)
    (E δ : ℝ) : ℝ :=
  (∑ n ∈ Finset.univ.filter (fun n => |hH.eigenvalues n - E| ≤ δ),
      RCLike.re (eigenMatrix hH A n n))
    / (Finset.univ.filter (fun n => |hH.eigenvalues n - E| ≤ δ)).card

/-- ★ **Under ETH the microcanonical average is within `ε + η` of `f(E)`**, whenever the window
contains at least one eigenstate. -/
theorem abs_microcanonicalDiag_sub_le (hH : H.IsHermitian)
    {A : Matrix (Fin N) (Fin N) ℂ} {f : ℝ → ℝ} {ε : ℝ} (heth : SatisfiesETH hH A f ε)
    {E δ η : ℝ} (hflat : ∀ x, |x - E| ≤ δ → |f x - f E| ≤ η)
    (hne : (Finset.univ.filter (fun n => |hH.eigenvalues n - E| ≤ δ)).Nonempty) :
    |microcanonicalDiag hH A E δ - f E| ≤ ε + η := by
  set W := Finset.univ.filter (fun n => |hH.eigenvalues n - E| ≤ δ) with hW
  have hcard : (0 : ℝ) < W.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hw : ∀ n ∈ W, (0 : ℝ) ≤ (W.card : ℝ)⁻¹ := fun _ _ => inv_nonneg.mpr hcard.le
  have hsum : ∑ n ∈ W, (W.card : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hcard.ne']
  have hmicro : microcanonicalDiag hH A E δ
      = ∑ n ∈ W, (W.card : ℝ)⁻¹ * RCLike.re (eigenMatrix hH A n n) := by
    rw [microcanonicalDiag, div_eq_inv_mul, Finset.mul_sum]
  have hfE : f E = ∑ n ∈ W, (W.card : ℝ)⁻¹ * f E := by
    rw [← Finset.sum_mul, hsum, one_mul]
  rw [hmicro, hfE]
  refine abs_sum_weighted_sub_le W _ _ _ hw hsum fun n hn _ => ?_
  have hnE : |hH.eigenvalues n - E| ≤ δ := (Finset.mem_filter.mp hn).2
  calc |RCLike.re (eigenMatrix hH A n n) - f E|
      = |(RCLike.re (eigenMatrix hH A n n) - f (hH.eigenvalues n))
          + (f (hH.eigenvalues n) - f E)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ ε + η := add_le_add (heth n) (hflat _ hnE)

/-- A state in an energy window that carries any weight at all puts an eigenstate in it. -/
lemma window_nonempty_of_inEnergyWindow (hH : H.IsHermitian) {ψ : Fin N → ℂ} {E δ : ℝ}
    (hwin : InEnergyWindow hH ψ E δ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    (Finset.univ.filter (fun n => |hH.eigenvalues n - E| ≤ δ)).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hall : ∀ n, eigenCoord hH ψ n = 0 := by
    intro n
    by_contra hc
    have := hwin n hc
    have hmem : n ∈ Finset.univ.filter (fun n => |hH.eigenvalues n - E| ≤ δ) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ n, this⟩
    rw [hempty] at hmem
    exact Finset.notMem_empty n hmem
  have h1 := sum_normSq_eigenCoord hH ψ hψ
  simp only [hall, norm_zero, zero_pow two_ne_zero, Finset.sum_const_zero] at h1
  exact zero_ne_one h1

/-- ★★ **TH5c — ETH implies thermalisation of the time average.** Take a Hamiltonian `H`, an
observable `A` satisfying ETH with tolerance `ε` for a function `f` of the energy, a unit state
`ψ` in an energy window of half-width `δ` around `E` on which `f` moves by at most `η`, and a
nonresonant sampling timestep `τ`. Then the time average of `⟨A⟩ₜ` along the Schrödinger orbit
converges, and its limit is within `2(ε + η)` of the microcanonical average of `A` over the
window. The long-time value of `A` depends on the preparation only through its energy. -/
theorem eth_time_average (hH : H.IsHermitian) {τ : ℝ} (hres : Nonresonant hH τ)
    {A : Matrix (Fin N) (Fin N) ℂ} {f : ℝ → ℝ} {ε : ℝ} (heth : SatisfiesETH hH A f ε)
    {E δ η : ℝ} (hflat : ∀ x, |x - E| ≤ δ → |f x - f E| ≤ η)
    (ψ : Fin N → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) (hwin : InEnergyWindow hH ψ E δ) :
    Tendsto (fun T : ℕ => birkhoffAverage ℝ
        (fun v : Fin N → ℂ => (LF4.schrodingerUnitary hH τ : Matrix (Fin N) (Fin N) ℂ) *ᵥ v)
        (heisenbergObs A) T ψ)
      atTop (𝓝 (diagonalEnsemble hH A ψ))
    ∧ |diagonalEnsemble hH A ψ - microcanonicalDiag hH A E δ| ≤ 2 * (ε + η) := by
  refine ⟨tendsto_birkhoffAverage_heisenbergObs hH hres A ψ, ?_⟩
  have h1 := abs_diagonalEnsemble_sub_le_of_window hH heth hflat ψ hψ hwin
  have h2 := abs_microcanonicalDiag_sub_le hH heth hflat
    (window_nonempty_of_inEnergyWindow hH hwin hψ)
  calc |diagonalEnsemble hH A ψ - microcanonicalDiag hH A E δ|
      = |(diagonalEnsemble hH A ψ - f E) - (microcanonicalDiag hH A E δ - f E)| := by ring_nf
    _ ≤ |diagonalEnsemble hH A ψ - f E| + |microcanonicalDiag hH A E δ - f E| :=
        abs_sub _ _
    _ ≤ (ε + η) + (ε + η) := add_le_add h1 h2
    _ = 2 * (ε + η) := by ring

end Thermo
end CSD
