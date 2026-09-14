/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Thermo.Jarzynski

/-!
# TH5b: the Crooks fluctuation theorem, two-point-measurement form

**Category:** 3-Local (conceptually 1-Mathlib; CSD-free finite-dimensional quantum
statistical mechanics) with a CSD reading; kept in the `CSD.Thermo` tree alongside
TH1–TH5a (`specs/thermo-plan.md` TH5; `specs/BACKLOG.md` ▶ OPEN QUEUE #2).

**Glossary:** https://glossary.constraintsurfacedynamics.com/crooks-fluctuation-theorem/

The Jarzynski equality (TH5a, `Thermo/Jarzynski.lean`) averages the two-point-measurement
work of the **forward protocol** — Gibbs state of `H₀`, read, drive by `U`, read in the
eigenbasis of `H₁`. The **reverse protocol** starts in the Gibbs state of `H₁` at the same
temperature, drives by `U⁻¹ = Uᴴ`, and reads in the eigenbasis of `H₀`. Crooks' theorem (1999)
is the pointwise relation between the two work distributions,

  `P_F(W) = P_R(−W) · e^{β(W − ΔF)}`,

so the forward and reverse histograms cross exactly at `W = ΔF`, which is how single-molecule
experiments read a free energy off two irreversible data sets. Jarzynski is its corollary
(multiply by `e^{−βW}` and sum: the reverse law sums to one).

The whole content is one symmetry and one cancellation. The reverse protocol's transition
matrix is the **transpose** of the forward one — `V₀ᴴ Uᴴ V₁ = (V₁ᴴ U V₀)ᴴ`, so
`‖⟨e₀ i, Uᴴ e₁ j⟩‖² = ‖⟨e₁ j, U e₀ i⟩‖²` (`tpmTransition_star`, microscopic reversibility) —
and the two Gibbs weights differ by exactly `e^{βW}` times `Z₁/Z₀`.

## Main results

* `tpmUnitary_star`, `tpmTransition_star` — the reverse protocol's transition matrix is the
  transpose of the forward one (`Uᴴ` between the swapped eigenbases); `tpmWork_symm` — its
  work is minus the forward work;
* ★★ `crooks_pairwise` (**TH5b, the pairwise form**): on every outcome pair,
  `P_F(i, j) · Z₀ = P_R(j, i) · Z₁ · e^{βW(i, j)}`; `crooks_pairwise_freeEnergy` — the same as
  `P_F(i, j) = P_R(j, i) · e^{β(W − ΔF)}` in the TH3 free energies; `crooks_ratio` — the ratio
  form on pairs of positive transition probability;
* `workDist hH₀ hH₁ U β w` — the **work distribution**, `P(W = w) = ∑_{W(i,j) = w} P(i, j)`;
  `workDist_nonneg`, `sum_workDist` (a probability law on the finite set of work values);
* ★★ `crooks` (**TH5b, the histogram form**): `P_F(w) = P_R(−w) · e^{β(w − ΔF)}` for every
  real `w`, by reindexing the reverse pairs along `Prod.swap`;
* `jarzynski_workDist` — Jarzynski read on the histogram: `∑_w P_F(w) e^{−βw} = e^{−βΔF}`.

## CSD reading

The forward and reverse protocols are two runs of the same de-isolation with the flow
reversed; on the sector the reverse protocol is the time-reversed Schrödinger flow, which is
again a Hamiltonian flow (of `−⟨H⟩`), so both protocols live under Liouville. The theorem
says the two records' work statistics are related pointwise, not only on average: the
irreversibility of a single run is priced by `e^{β(W − ΔF)}`. The sector-level instantiation
is TH5d (`specs/BACKLOG.md` ▶ OPEN QUEUE #4).

## Honest scope

As TH5a: finite dimension, projective readouts in the spectral-theorem eigenbases, a closed
driven system, the same `β` at both ends; the reverse protocol is defined with the same
eigenbases (its transition matrix is the transpose, `tpmTransition_star`, so no choice is
hidden). The ratio form `P_F/P_R = e^{β(W − ΔF)}` needs `P_R(j, i) ≠ 0`, i.e. a positive
transition probability; the product form `crooks_pairwise_freeEnergy` needs nothing and is
the theorem. Requires `[Nonempty n]` (TH3's hypothesis).

## Provenance

Foundational-triple only (`propext, Classical.choice, Quot.sound`); no `sorry`, no new
axioms. Consumes TH5a and TH3; nothing is re-proved.
-/

@[expose] public section

open scoped BigOperators ComplexOrder
open Matrix

namespace CSD
namespace Thermo

variable {n : Type*} [Fintype n] [DecidableEq n] {H₀ H₁ : Matrix n n ℂ}

/-! ## The reverse protocol -/

/-- The reverse protocol's unitary between the swapped eigenbases is the adjoint of the
forward one: `V₀ᴴ Uᴴ V₁ = (V₁ᴴ U V₀)ᴴ`. -/
lemma tpmUnitary_star (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) :
    tpmUnitary hH₁ hH₀ (star U) = star (tpmUnitary hH₀ hH₁ U) := by
  simp only [tpmUnitary, star_mul, star_star, mul_assoc]

/-- **Microscopic reversibility**: the reverse protocol's transition matrix is the transpose
of the forward one, `‖⟨e₀ i, Uᴴ e₁ j⟩‖² = ‖⟨e₁ j, U e₀ i⟩‖²`. -/
lemma tpmTransition_star (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) (i j : n) :
    tpmTransition hH₁ hH₀ (star U) j i = tpmTransition hH₀ hH₁ U i j := by
  simp only [tpmTransition, tpmUnitary_star, Unitary.coe_star, Matrix.star_apply, norm_star]

/-- The reverse protocol's work on the pair `(j, i)` is minus the forward work on `(i, j)`. -/
lemma tpmWork_symm (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian) (i j : n) :
    tpmWork hH₁ hH₀ j i = -tpmWork hH₀ hH₁ i j := by
  simp only [tpmWork, neg_sub]

/-! ## The pairwise Crooks relation -/

/-- **TH5b — the Crooks relation on outcome pairs**, partition-function form: the forward
probability of the pair `(i, j)` and the reverse probability of the pair `(j, i)` satisfy
`P_F(i, j) · Z₀ = P_R(j, i) · Z₁ · e^{βW(i, j)}`. The transition probabilities agree
(`tpmTransition_star`); the Gibbs weights differ by `e^{βW}` up to the normalisations. -/
theorem crooks_pairwise [Nonempty n] (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) (β : ℝ) (i j : n) :
    tpmLaw hH₀ hH₁ U β i j * partitionFn H₀ hH₀ β
      = tpmLaw hH₁ hH₀ (star U) β j i * partitionFn H₁ hH₁ β
          * Real.exp (β * tpmWork hH₀ hH₁ i j) := by
  simp only [tpmLaw, gibbsWeight, tpmTransition_star, tpmWork]
  rw [show β * (hH₁.eigenvalues j - hH₀.eigenvalues i)
      = -β * hH₀.eigenvalues i - -β * hH₁.eigenvalues j by ring, Real.exp_sub]
  have h0 := Real.exp_ne_zero (-β * hH₀.eigenvalues i)
  have h1 := Real.exp_ne_zero (-β * hH₁.eigenvalues j)
  have hZ0 := (partitionFn_pos H₀ hH₀ β).ne'
  have hZ1 := (partitionFn_pos H₁ hH₁ β).ne'
  field_simp

/-- **The Crooks relation in free-energy form**: `P_F(i, j) = P_R(j, i) · e^{β(W − ΔF)}` with
`ΔF = F₁ − F₀` the TH3 free energies of the two Gibbs states (`gibbs_free_energy_eq`). -/
theorem crooks_pairwise_freeEnergy [Nonempty n] (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) {β : ℝ} (hβ : 0 < β) (i j : n) :
    tpmLaw hH₀ hH₁ U β i j
      = tpmLaw hH₁ hH₀ (star U) β j i
          * Real.exp (β * (tpmWork hH₀ hH₁ i j
              - (freeEnergy H₁ β⁻¹ (gibbsState_isHermitian H₁ hH₁ β)
                  - freeEnergy H₀ β⁻¹ (gibbsState_isHermitian H₀ hH₀ β)))) := by
  have h := crooks_pairwise hH₀ hH₁ U β i j
  have h0 := partitionFn_pos H₀ hH₀ β
  have h1 := partitionFn_pos H₁ hH₁ β
  have hβ' := hβ.ne'
  rw [gibbs_free_energy_eq H₁ hH₁ hβ, gibbs_free_energy_eq H₀ hH₀ hβ]
  rw [show β * (tpmWork hH₀ hH₁ i j - (-β⁻¹ * Real.log (partitionFn H₁ hH₁ β)
        - -β⁻¹ * Real.log (partitionFn H₀ hH₀ β)))
      = β * tpmWork hH₀ hH₁ i j
          + (Real.log (partitionFn H₁ hH₁ β) - Real.log (partitionFn H₀ hH₀ β)) by
        field_simp; ring,
    Real.exp_add, Real.exp_sub, Real.exp_log h1, Real.exp_log h0]
  rw [← mul_left_inj' h0.ne', h]
  field_simp

/-- **The Crooks ratio**: on a pair of positive transition probability,
`P_F(i, j) / P_R(j, i) = e^{β(W − ΔF)}`. -/
theorem crooks_ratio [Nonempty n] (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) {β : ℝ} (hβ : 0 < β) {i j : n}
    (hT : 0 < tpmTransition hH₀ hH₁ U i j) :
    tpmLaw hH₀ hH₁ U β i j / tpmLaw hH₁ hH₀ (star U) β j i
      = Real.exp (β * (tpmWork hH₀ hH₁ i j
          - (freeEnergy H₁ β⁻¹ (gibbsState_isHermitian H₁ hH₁ β)
              - freeEnergy H₀ β⁻¹ (gibbsState_isHermitian H₀ hH₀ β)))) := by
  have hR : tpmLaw hH₁ hH₀ (star U) β j i ≠ 0 := by
    rw [tpmLaw, tpmTransition_star]
    exact (mul_pos (gibbsWeight_pos H₁ hH₁ β _) hT).ne'
  rw [crooks_pairwise_freeEnergy hH₀ hH₁ U hβ i j]
  exact mul_div_cancel_left₀ _ hR

/-! ## The work distribution and the histogram form -/

/-- The **work distribution** of the protocol: the probability that the two-point-measurement
work equals `w`, `P(W = w) = ∑_{W(i, j) = w} P(i, j)`. -/
noncomputable def workDist (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) (β : ℝ) (w : ℝ) : ℝ :=
  ∑ q : n × n, if tpmWork hH₀ hH₁ q.1 q.2 = w then tpmLaw hH₀ hH₁ U β q.1 q.2 else 0

lemma workDist_nonneg [Nonempty n] (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) (β : ℝ) (w : ℝ) : 0 ≤ workDist hH₀ hH₁ U β w :=
  Finset.sum_nonneg fun q _ => by
    split_ifs
    · exact tpmLaw_nonneg hH₀ hH₁ U β q.1 q.2
    · exact le_rfl

/-- The **set of work values** of the protocol: the finite set `{E₁ j − E₀ i}`. -/
noncomputable def workValues (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian) : Finset ℝ :=
  Finset.univ.image fun q : n × n => tpmWork hH₀ hH₁ q.1 q.2

/-- Summing a function of the work against the work distribution over the work values is
summing it against the joint law over the outcome pairs. -/
lemma sum_workValues_workDist_mul (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) (β : ℝ) (g : ℝ → ℝ) :
    ∑ w ∈ workValues hH₀ hH₁, workDist hH₀ hH₁ U β w * g w
      = ∑ q : n × n, tpmLaw hH₀ hH₁ U β q.1 q.2 * g (tpmWork hH₀ hH₁ q.1 q.2) := by
  simp only [workDist, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [workValues, Finset.mem_image, Finset.mem_univ, true_and, exists_apply_eq_apply,
    if_true]

/-- The work distribution is a probability law on the work values. -/
lemma sum_workDist [Nonempty n] (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) (β : ℝ) :
    ∑ w ∈ workValues hH₀ hH₁, workDist hH₀ hH₁ U β w = 1 := by
  have h := sum_workValues_workDist_mul hH₀ hH₁ U β (fun _ => 1)
  simp only [mul_one] at h
  rw [h, Fintype.sum_prod_type]
  exact sum_tpmLaw hH₀ hH₁ U β

/-- **TH5b — the Crooks fluctuation theorem, histogram form**: for every real `w`,
`P_F(w) = P_R(−w) · e^{β(w − ΔF)}`, where `P_R` is the work distribution of the reverse
protocol (Gibbs state of `H₁`, drive by `Uᴴ`, read in the eigenbasis of `H₀`). The forward
pairs `(i, j)` of work `w` are the reverse pairs `(j, i)` of work `−w`, and on each the
pairwise relation holds. -/
theorem crooks [Nonempty n] (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) {β : ℝ} (hβ : 0 < β) (w : ℝ) :
    workDist hH₀ hH₁ U β w
      = workDist hH₁ hH₀ (star U) β (-w)
          * Real.exp (β * (w - (freeEnergy H₁ β⁻¹ (gibbsState_isHermitian H₁ hH₁ β)
              - freeEnergy H₀ β⁻¹ (gibbsState_isHermitian H₀ hH₀ β)))) := by
  unfold workDist
  rw [Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.prodComm n n) _ _ fun q => ?_
  show (if tpmWork hH₀ hH₁ q.1 q.2 = w then tpmLaw hH₀ hH₁ U β q.1 q.2 else 0)
      = (if tpmWork hH₁ hH₀ q.2 q.1 = -w then tpmLaw hH₁ hH₀ (star U) β q.2 q.1 else 0)
          * Real.exp (β * (w - (freeEnergy H₁ β⁻¹ (gibbsState_isHermitian H₁ hH₁ β)
              - freeEnergy H₀ β⁻¹ (gibbsState_isHermitian H₀ hH₀ β))))
  simp only [tpmWork_symm hH₀ hH₁, neg_inj, ite_mul, zero_mul]
  split_ifs with hq
  · rw [← hq]
    exact crooks_pairwise_freeEnergy hH₀ hH₁ U hβ q.1 q.2
  · rfl

/-- **Jarzynski on the histogram**: `∑_w P_F(w) e^{−βw} = e^{−βΔF}`, TH5a read on the work
distribution. -/
theorem jarzynski_workDist [Nonempty n] (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (U : Matrix.unitaryGroup n ℂ) {β : ℝ} (hβ : 0 < β) :
    ∑ w ∈ workValues hH₀ hH₁, workDist hH₀ hH₁ U β w * Real.exp (-β * w)
      = Real.exp (-β * (freeEnergy H₁ β⁻¹ (gibbsState_isHermitian H₁ hH₁ β)
          - freeEnergy H₀ β⁻¹ (gibbsState_isHermitian H₀ hH₀ β))) := by
  rw [sum_workValues_workDist_mul hH₀ hH₁ U β (fun w => Real.exp (-β * w)),
    Fintype.sum_prod_type]
  exact jarzynski_freeEnergy hH₀ hH₁ U hβ

end Thermo
end CSD
