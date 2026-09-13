/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Thermo.FreeEnergy
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# TH5a: the Jarzynski equality, two-point-measurement form

**Category:** 3-Local (conceptually 1-Mathlib; CSD-free finite-dimensional quantum
statistical mechanics) with a CSD reading; kept in the `CSD.Thermo` tree alongside
TH1–TH4 (`specs/thermo-plan.md` TH5; `specs/BACKLOG.md` ▶ OPEN QUEUE #1).

**Glossary:** https://glossary.constraintsurfacedynamics.com/jarzynski-equality/

A finite quantum system with Hamiltonian `H₀` starts in the Gibbs state `ρ_β = e^{−βH₀}/Z₀`
(TH3, `gibbsState`). The **two-point-measurement protocol**: measure the energy — outcome
`i`, the eigenvalue `E₀ i` of `H₀`, with Born probability the Gibbs weight `e^{−βE₀ i}/Z₀`;
drive the system by a unitary `U` while its Hamiltonian becomes `H₁`; measure the energy
again — outcome `j`, the eigenvalue `E₁ j` of `H₁`, with Born probability
`‖⟨e₁ j, U e₀ i⟩‖²`. The **work** done on the system in that run is `W = E₁ j − E₀ i`. The
**Jarzynski equality** (1997) says that the exponential average of the work over the
protocol is a state function of the two endpoints,

  `⟨e^{−βW}⟩ = Z₁/Z₀ = e^{−βΔF}`,  `ΔF = F₁ − F₀ = −β⁻¹ (log Z₁ − log Z₀)`,

an *equality* valid arbitrarily far from equilibrium, whose Jensen consequence `⟨W⟩ ≥ ΔF`
is the second law for the process (TH2 is its entropy-facing twin). The proof is bookkeeping
once the transition matrix is seen to be **doubly stochastic**: the Gibbs factor `e^{−βE₀ i}`
cancels against the `e^{+βE₀ i}` inside `e^{−βW}`, and the sums of `‖⟨e₁ j, U e₀ i⟩‖²` over
`i` are `1` by unitarity, leaving `∑ⱼ e^{−βE₁ j}/Z₀`.

## Main results

* `tpmUnitary hH₀ hH₁ U` — the process read between the two eigenbases, `V₁ᴴ U V₀` (again a
  unitary); `tpmUnitary_apply` — its `(j, i)` entry is the amplitude `⟨e₁ j, U e₀ i⟩`;
* `tpmTransition hH₀ hH₁ U i j := ‖(V₁ᴴ U V₀) j i‖²`, the Born transition probability
  (`tpmTransition_eq`), **doubly stochastic**: `sum_tpmTransition_left` (over the final
  outcome) and `sum_tpmTransition_right` (over the initial outcome), both by unitarity;
* `tpmLaw hH₀ hH₁ U β i j := gibbsWeight (E₀ i) · tpmTransition i j` — the joint law of the
  two outcomes, a probability law (`tpmLaw_nonneg`, `sum_tpmLaw`);
  `tpmWork hH₀ hH₁ i j := E₁ j − E₀ i`;
* `gibbsState_mulVec_eigenvectorBasis` and `gibbsWeight_eq_re_born` — the Gibbs weight IS the
  Born probability `⟨e₀ i, ρ_β e₀ i⟩` of the energy outcome `i` in the Gibbs state, so the
  joint law is the *statistics of the protocol*, not a definition;
* ★★ `jarzynski` (**TH5a**): `∑ᵢⱼ tpmLaw i j · e^{−β W i j} = Z₁/Z₀`;
* ★★ `jarzynski_freeEnergy`: the same with right-hand side `e^{−β(F₁ − F₀)}` in the TH3 free
  energies of the two Gibbs states (`gibbs_free_energy_eq`), for `β > 0`;
* ★ `mean_work_ge_freeEnergy_sub` — Jensen (`convexOn_exp`): `ΔF ≤ ⟨W⟩`, the second law of
  the driven process.

## CSD reading

The protocol's two readouts are records; the Gibbs weights are the Born weights of the first
readout in the equilibrium preparation, and the transition probabilities the Born weights of
the second after a unitary de-isolation. On the sector the same statement is the two-time
record law of `RecordLayer/TwoTimeLuders.lean` under a Gibbs preparation measure and the
Schrödinger flow (the Hamiltonian flow of `⟨H⟩`, Q29(e)); that instantiation is the priced
row TH5d (`specs/BACKLOG.md` ▶ OPEN QUEUE #4). This file is the bare-matrix theorem it
consumes.

## Honest scope

Finite-dimensional, projective energy measurements with the eigenbases chosen by
`Matrix.IsHermitian.eigenvectorBasis` (degenerate spectra are allowed: the equality sums
over eigenvectors, not over distinct eigenvalues, and the transition weights are those of the
chosen bases). The work is the two-point-measurement work `E₁ j − E₀ i`, the standard
definition for closed driven systems; `ΔF` is the difference of the equilibrium free energies
of `H₁` and `H₀` at the same `β`. No bath, no heat: the driven system is closed, so
`W = ΔE`. Requires `[Nonempty n]` where a Gibbs state is involved (TH3's hypothesis).

## Provenance

Foundational-triple only (`propext, Classical.choice, Quot.sound`); no `sorry`, no new
axioms. Consumes TH3 (`gibbsState`, `partitionFn`, `gibbs_free_energy_eq`) and Mathlib's
spectral theorem and `convexOn_exp`; nothing is re-proved.
-/

@[expose] public section

open scoped BigOperators ComplexOrder
open Matrix

namespace CSD
namespace Thermo

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Unitaries are doubly stochastic in modulus squared -/

/-- Entry `(i, i)` of `Mᴴ M = 1`: the squared moduli down a column of a unitary sum to `1`. -/
lemma sum_norm_sq_col_eq_one (M : Matrix.unitaryGroup n ℂ) (i : n) :
    ∑ j, ‖(M : Matrix n n ℂ) j i‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (Unitary.coe_star_mul_self M) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  simp only [Matrix.star_apply, Complex.star_def, Complex.conj_mul'] at h
  exact_mod_cast h

/-- Entry `(j, j)` of `M Mᴴ = 1`: the squared moduli along a row of a unitary sum to `1`. -/
lemma sum_norm_sq_row_eq_one (M : Matrix.unitaryGroup n ℂ) (j : n) :
    ∑ i, ‖(M : Matrix n n ℂ) j i‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (Unitary.coe_mul_star_self M) j) j
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  simp only [Unitary.coe_star, Matrix.star_apply, Complex.star_def, Complex.mul_conj'] at h
  exact_mod_cast h

/-! ## The transition matrix of the protocol -/

variable {H₀ H₁ : Matrix n n ℂ}

/-- The process `U` read between the eigenbases of `H₀` and `H₁`: `V₁ᴴ U V₀`, with `V_k` the
eigenvector unitary of `H_k`. Its `(j, i)` entry is the amplitude `⟨e₁ j, U e₀ i⟩`
(`tpmUnitary_apply`). -/
noncomputable def tpmUnitary (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) : Matrix.unitaryGroup n ℂ :=
  star hH₁.eigenvectorUnitary * U * hH₀.eigenvectorUnitary

lemma tpmUnitary_coe (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) :
    (tpmUnitary hH₀ hH₁ U : Matrix n n ℂ)
      = star (hH₁.eigenvectorUnitary : Matrix n n ℂ) * U * hH₀.eigenvectorUnitary :=
  rfl

/-- The `(j, i)` entry of `V₁ᴴ U V₀` is the transition amplitude `⟨e₁ j, U e₀ i⟩` from the
`i`-th eigenvector of `H₀` to the `j`-th eigenvector of `H₁`. -/
lemma tpmUnitary_apply (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) (i j : n) :
    (tpmUnitary hH₀ hH₁ U : Matrix n n ℂ) j i
      = star ⇑(hH₁.eigenvectorBasis j) ⬝ᵥ ((U : Matrix n n ℂ) *ᵥ ⇑(hH₀.eigenvectorBasis i)) := by
  rw [tpmUnitary_coe, Matrix.mul_assoc, Matrix.mul_apply']
  rfl

/-- The **transition probability** of the protocol from energy outcome `i` of `H₀` to energy
outcome `j` of `H₁`: `‖⟨e₁ j, U e₀ i⟩‖²`, the Born weight of the second readout in the
post-first-readout state `U e₀ i`. -/
noncomputable def tpmTransition (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) (i j : n) : ℝ :=
  ‖(tpmUnitary hH₀ hH₁ U : Matrix n n ℂ) j i‖ ^ 2

lemma tpmTransition_eq (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) (i j : n) :
    tpmTransition hH₀ hH₁ U i j
      = ‖star ⇑(hH₁.eigenvectorBasis j)
          ⬝ᵥ ((U : Matrix n n ℂ) *ᵥ ⇑(hH₀.eigenvectorBasis i))‖ ^ 2 := by
  rw [tpmTransition, tpmUnitary_apply]

lemma tpmTransition_nonneg (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) (i j : n) : 0 ≤ tpmTransition hH₀ hH₁ U i j :=
  sq_nonneg _

/-- **Stochastic in the final outcome**: for each initial outcome `i`, the transition
probabilities over `j` sum to `1`. -/
lemma sum_tpmTransition_left (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) (i : n) : ∑ j, tpmTransition hH₀ hH₁ U i j = 1 :=
  sum_norm_sq_col_eq_one (tpmUnitary hH₀ hH₁ U) i

/-- **Doubly stochastic**: for each final outcome `j`, the transition probabilities over the
initial outcome `i` also sum to `1` — unitarity in the other order. This is the identity
that makes the Jarzynski average a state function. -/
lemma sum_tpmTransition_right (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) (j : n) : ∑ i, tpmTransition hH₀ hH₁ U i j = 1 :=
  sum_norm_sq_row_eq_one (tpmUnitary hH₀ hH₁ U) j

/-! ## The Gibbs weights are the Born weights of the first readout -/

/-- The Gibbs weights over the spectrum sum to `1`. -/
lemma sum_gibbsWeight_eigenvalues [Nonempty n] (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (β : ℝ) : ∑ i, gibbsWeight H hH β (hH.eigenvalues i) = 1 := by
  have hZ : partitionFn H hH β = ∑ i, Real.exp (-β * hH.eigenvalues i) := rfl
  simp only [gibbsWeight]
  rw [← Finset.sum_div, ← hZ]
  exact div_self (partitionFn_pos H hH β).ne'

/-- The eigenvectors of `H` are eigenvectors of the Gibbs state, with eigenvalue the Gibbs
weight of the energy: `ρ_β e_i = (e^{−βE_i}/Z) e_i`. -/
lemma gibbsState_mulVec_eigenvectorBasis (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ)
    (i : n) :
    gibbsState H hH β *ᵥ ⇑(hH.eigenvectorBasis i)
      = ((gibbsWeight H hH β (hH.eigenvalues i) : ℝ) : ℂ) • ⇑(hH.eigenvectorBasis i) := by
  rw [gibbsState_eq_conj, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hH.star_eigenvectorUnitary_mulVec, Matrix.diagonal_mulVec_single, mul_one,
    Matrix.mulVec_single, op_smul_eq_smul, hH.eigenvectorUnitary_col_eq]

/-- The eigenvectors are unit vectors: entry `(i, i)` of `V₀ᴴ V₀ = 1`. -/
lemma star_dotProduct_eigenvectorBasis_self (hH : H₀.IsHermitian) (i : n) :
    star ⇑(hH.eigenvectorBasis i) ⬝ᵥ ⇑(hH.eigenvectorBasis i) = 1 := by
  have h := congrFun (congrFun (Unitary.coe_star_mul_self hH.eigenvectorUnitary) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  simpa [dotProduct, Matrix.star_apply] using h

/-- **The Gibbs weight is a Born probability**: `e^{−βE_i}/Z = Re ⟨e_i, ρ_β e_i⟩`, the
probability of the energy outcome `i` when the Gibbs state is measured in the eigenbasis of
`H`. -/
lemma gibbsWeight_eq_re_born (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) (i : n) :
    gibbsWeight H hH β (hH.eigenvalues i)
      = RCLike.re (star ⇑(hH.eigenvectorBasis i)
          ⬝ᵥ (gibbsState H hH β *ᵥ ⇑(hH.eigenvectorBasis i))) := by
  rw [gibbsState_mulVec_eigenvectorBasis, dotProduct_smul,
    star_dotProduct_eigenvectorBasis_self, smul_eq_mul, mul_one]
  simp

/-! ## The joint law and the work -/

/-- The **joint law** of the two readouts: the Gibbs weight of the first outcome times the
transition probability to the second. -/
noncomputable def tpmLaw (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) (β : ℝ) (i j : n) : ℝ :=
  gibbsWeight H₀ hH₀ β (hH₀.eigenvalues i) * tpmTransition hH₀ hH₁ U i j

lemma tpmLaw_nonneg [Nonempty n] (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) (β : ℝ) (i j : n) : 0 ≤ tpmLaw hH₀ hH₁ U β i j :=
  mul_nonneg (gibbsWeight_pos H₀ hH₀ β _).le (tpmTransition_nonneg hH₀ hH₁ U i j)

/-- The joint law is a probability law on the outcome pairs. -/
lemma sum_tpmLaw [Nonempty n] (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) (β : ℝ) : ∑ i, ∑ j, tpmLaw hH₀ hH₁ U β i j = 1 := by
  simp only [tpmLaw, ← Finset.mul_sum, sum_tpmTransition_left, mul_one]
  exact sum_gibbsWeight_eigenvalues H₀ hH₀ β

/-- The **two-point-measurement work** on the outcome pair `(i, j)`: `E₁ j − E₀ i`, the energy
difference between the two readouts (the system is closed, so this is the work done on it). -/
noncomputable def tpmWork (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian) (i j : n) : ℝ :=
  hH₁.eigenvalues j - hH₀.eigenvalues i

/-! ## The Jarzynski equality -/

/-- **TH5a — the Jarzynski equality.** The exponential average of the two-point-measurement
work over the protocol is the ratio of the partition functions of the final and initial
Hamiltonians, `⟨e^{−βW}⟩ = Z₁/Z₀`, whatever the driving unitary `U`. The Gibbs factor of
the first readout cancels the `e^{+βE₀ i}` in `e^{−βW}`, and the transition matrix is doubly
stochastic (`sum_tpmTransition_right`). -/
theorem jarzynski [Nonempty n] (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) (β : ℝ) :
    ∑ i, ∑ j, tpmLaw hH₀ hH₁ U β i j * Real.exp (-β * tpmWork hH₀ hH₁ i j)
      = partitionFn H₁ hH₁ β / partitionFn H₀ hH₀ β := by
  have hZ := (partitionFn_pos H₀ hH₀ β).ne'
  have hterm : ∀ i j, tpmLaw hH₀ hH₁ U β i j * Real.exp (-β * tpmWork hH₀ hH₁ i j)
      = Real.exp (-β * hH₁.eigenvalues j) / partitionFn H₀ hH₀ β
          * tpmTransition hH₀ hH₁ U i j := by
    intro i j
    have hE := Real.exp_ne_zero (-β * hH₀.eigenvalues i)
    simp only [tpmLaw, gibbsWeight, tpmWork]
    rw [show -β * (hH₁.eigenvalues j - hH₀.eigenvalues i)
        = -β * hH₁.eigenvalues j - -β * hH₀.eigenvalues i by ring, Real.exp_sub]
    field_simp
  simp_rw [hterm]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_tpmTransition_right, mul_one]
  rw [← Finset.sum_div]
  rfl

/-- **The Jarzynski equality in free-energy form**: `⟨e^{−βW}⟩ = e^{−β(F₁ − F₀)}`, with `F_k`
the TH3 equilibrium free energy `−β⁻¹ log Z_k` of the Gibbs state of `H_k` at temperature
`β⁻¹` (`gibbs_free_energy_eq`). -/
theorem jarzynski_freeEnergy [Nonempty n] (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) {β : ℝ} (hβ : 0 < β) :
    ∑ i, ∑ j, tpmLaw hH₀ hH₁ U β i j * Real.exp (-β * tpmWork hH₀ hH₁ i j)
      = Real.exp (-β * (freeEnergy H₁ β⁻¹ (gibbsState_isHermitian H₁ hH₁ β)
          - freeEnergy H₀ β⁻¹ (gibbsState_isHermitian H₀ hH₀ β))) := by
  rw [jarzynski, gibbs_free_energy_eq H₁ hH₁ hβ, gibbs_free_energy_eq H₀ hH₀ hβ]
  have h0 := partitionFn_pos H₀ hH₀ β
  have h1 := partitionFn_pos H₁ hH₁ β
  have hβ' := hβ.ne'
  rw [show -β * (-β⁻¹ * Real.log (partitionFn H₁ hH₁ β)
        - -β⁻¹ * Real.log (partitionFn H₀ hH₀ β))
      = Real.log (partitionFn H₁ hH₁ β) - Real.log (partitionFn H₀ hH₀ β) by
        field_simp; ring]
  rw [Real.exp_sub, Real.exp_log h1, Real.exp_log h0]

/-- **The second law of the driven process** (Jensen on the Jarzynski equality): the mean
two-point-measurement work is at least the free-energy difference, `ΔF ≤ ⟨W⟩`. Convexity of
`exp` gives `e^{−β⟨W⟩} ≤ ⟨e^{−βW}⟩ = e^{−βΔF}`. -/
theorem mean_work_ge_freeEnergy_sub [Nonempty n] (hH₀ : H₀.IsHermitian)
    (hH₁ : H₁.IsHermitian) (U : Matrix.unitaryGroup n ℂ) {β : ℝ} (hβ : 0 < β) :
    freeEnergy H₁ β⁻¹ (gibbsState_isHermitian H₁ hH₁ β)
        - freeEnergy H₀ β⁻¹ (gibbsState_isHermitian H₀ hH₀ β)
      ≤ ∑ i, ∑ j, tpmLaw hH₀ hH₁ U β i j * tpmWork hH₀ hH₁ i j := by
  set ΔF := freeEnergy H₁ β⁻¹ (gibbsState_isHermitian H₁ hH₁ β)
    - freeEnergy H₀ β⁻¹ (gibbsState_isHermitian H₀ hH₀ β) with hΔF
  set p : n × n → ℝ := fun q => tpmLaw hH₀ hH₁ U β q.1 q.2 with hp
  set w : n × n → ℝ := fun q => -β * tpmWork hH₀ hH₁ q.1 q.2 with hw
  have hp0 : ∀ q ∈ (Finset.univ : Finset (n × n)), 0 ≤ p q :=
    fun q _ => tpmLaw_nonneg hH₀ hH₁ U β q.1 q.2
  have hp1 : ∑ q, p q = 1 := by
    rw [Fintype.sum_prod_type]
    exact sum_tpmLaw hH₀ hH₁ U β
  have hJ := convexOn_exp.map_sum_le hp0 hp1 (fun q _ => Set.mem_univ (w q))
  have hR : ∑ q, p q • Real.exp (w q) = Real.exp (-β * ΔF) := by
    simp only [smul_eq_mul, hp, hw]
    rw [Fintype.sum_prod_type]
    exact jarzynski_freeEnergy hH₀ hH₁ U hβ
  have hL : ∑ q, p q • w q = -β * ∑ i, ∑ j, tpmLaw hH₀ hH₁ U β i j * tpmWork hH₀ hH₁ i j := by
    simp only [smul_eq_mul, hp, hw]
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hL, hR, Real.exp_le_exp, neg_mul, neg_mul, neg_le_neg_iff] at hJ
  exact le_of_mul_le_mul_left hJ hβ

end Thermo
end CSD
