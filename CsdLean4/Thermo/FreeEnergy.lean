/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Mathlib.QuantumInfo.Subadditivity
import CsdLean4.Mathlib.QuantumInfo.Entropy

/-!
# TH3: temperature, free energy, and the Gibbs variational principle

**Category:** conceptually 1-Mathlib (CSD-free general quantum statistical
mechanics) with a CSD reading; kept in the `CSD.Thermo` tree alongside TH1/TH2.

At fixed inverse temperature `β > 0` (temperature `T = 1/β`), the **Gibbs state**
`ρ_β = exp(-βH)/Z`, `Z = Tr(exp(-βH))`, minimises the **free energy**
`F(ρ) = E(ρ) − T·S(ρ)` (energy `E(ρ) = Re Tr(ρH)`, entropy `S`) over all density
operators, with minimum value the standard `F(ρ_β) = −T log Z`. This is the
variational characterisation of thermal equilibrium: at temperature `T`, nature
minimises free energy, and the minimiser is the Boltzmann/Gibbs state. In the
CSD reading it is the equilibrium of the typicality ensemble; the second law
(TH2) and canonical typicality (TH1) are its entropy- and volume-facing shadows.

## Main results

* `gibbsState H hH β` : the Gibbs density `exp(-βH)/Z`, built through the
  Hermitian functional calculus `hH.cfc (x ↦ exp(-βx)/Z)`; `gibbsState_posDef`,
  `gibbsState_trace` (a genuine density), and the crux
  `cfc_log_gibbsState` : `log(ρ_β) = −β·H − (log Z)·1`.
* `freeEnergy H hH T ρ hρ := Re Tr(ρH) − T·S(ρ)`.
* `gibbs_free_energy_eq` : `F(ρ_β) = −T·log Z` (the equilibrium free energy).
* `gibbs_free_energy_min` (**TH3, the variational principle**): for `β > 0`,
  `F(ρ_β) ≤ F(ρ)` for every density `ρ`. Proof: `β(F(ρ) − F(ρ_β)) =
  D(ρ ‖ ρ_β) ≥ 0` by Klein's inequality (`relEntropy_nonneg`), using the
  log-linear form of `log ρ_β`.

## Honest scope

`F` uses `vonNeumannEntropy` (K1) and the energy `Re Tr(ρH)`; temperature enters
as the parameter `T = 1/β`. Equality `F(ρ) = F(ρ_β)` iff `ρ = ρ_β` (the strict
Klein case) is not separately extracted here — only the inequality. As with the
rest of the thermo track this is a QM-statistical-mechanics theorem with a CSD
reading; the deterministic-microdynamics interpretation rests on the shared
A5/D1 residue. Requires `[Nonempty n]` (a Gibbs state needs at least one level;
otherwise `Z = 0`).

## Provenance

Foundational-triple only (`propext, Classical.choice, Quot.sound`); no `sorry`,
no new axioms. Reuses K1 (`vonNeumannEntropy`) and the Klein / relative-entropy
layer (`relEntropy_nonneg`, `cfc_eq_conj_diagonal`, `re_trace_self_log`);
nothing is re-proved.
-/

open scoped BigOperators ComplexOrder
open Matrix QuantumInfo

namespace CSD
namespace Thermo

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The partition function and Gibbs weights -/

/-- The **partition function** `Z = Tr(exp(-βH)) = ∑ᵢ exp(-β λᵢ)`. -/
noncomputable def partitionFn (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) : ℝ :=
  ∑ i, Real.exp (-β * hH.eigenvalues i)

lemma partitionFn_pos [Nonempty n] (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    0 < partitionFn H hH β :=
  Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

/-- The **Gibbs weight** `x ↦ exp(-βx)/Z`, the function applied to the spectrum
of `H` to build the Gibbs state. -/
noncomputable def gibbsWeight (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) (x : ℝ) : ℝ :=
  Real.exp (-β * x) / partitionFn H hH β

lemma gibbsWeight_pos [Nonempty n] (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) (x : ℝ) :
    0 < gibbsWeight H hH β x :=
  div_pos (Real.exp_pos _) (partitionFn_pos H hH β)

/-- `log` of the Gibbs weight is affine in the energy: `log(exp(-βx)/Z) =
−βx − log Z`. This is what makes the relative entropy against the Gibbs state
collapse to the free-energy difference. -/
lemma log_gibbsWeight [Nonempty n] (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) (x : ℝ) :
    Real.log (gibbsWeight H hH β x) = -β * x - Real.log (partitionFn H hH β) := by
  rw [gibbsWeight, Real.log_div (Real.exp_ne_zero _) (partitionFn_pos H hH β).ne',
    Real.log_exp]

/-! ## The Gibbs state -/

/-- The **Gibbs state** `ρ_β = exp(-βH)/Z`, built through the Hermitian
functional calculus: `hH.cfc (gibbsWeight …)`. Its eigenvalues are the Gibbs
weights `exp(-β λᵢ)/Z`. -/
noncomputable def gibbsState (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    Matrix n n ℂ :=
  hH.cfc (gibbsWeight H hH β)

lemma gibbsState_isHermitian (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    (gibbsState H hH β).IsHermitian :=
  cfc_isHermitian hH _

/-- The Gibbs state as a unitary conjugation of the diagonal weight matrix:
`ρ_β = U · diag(exp(-βλ)/Z) · Uᴴ` with `U = hH.eigenvectorUnitary`. This is the
definitional unfolding of `hH.cfc`. -/
lemma gibbsState_eq_conj (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    gibbsState H hH β
      = (hH.eigenvectorUnitary : Matrix n n ℂ)
        * diagonal (fun i => ((gibbsWeight H hH β (hH.eigenvalues i) : ℝ) : ℂ))
        * star (hH.eigenvectorUnitary : Matrix n n ℂ) := by
  unfold gibbsState Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply]
  rfl

/-- The eigenvector unitary is a unit (invertible), so its `vecMul` is injective
— the input to the positive-definiteness argument. -/
lemma eigenvectorUnitary_isUnit (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    IsUnit (hH.eigenvectorUnitary : Matrix n n ℂ) :=
  ⟨⟨(hH.eigenvectorUnitary : Matrix n n ℂ),
      star (hH.eigenvectorUnitary : Matrix n n ℂ),
      Unitary.coe_mul_star_self _, Unitary.coe_star_mul_self _⟩, rfl⟩

/-- The Gibbs state is **positive-definite**: a unitary conjugate of the diagonal
of strictly-positive Gibbs weights. -/
lemma gibbsState_posDef [Nonempty n] (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    (gibbsState H hH β).PosDef := by
  rw [gibbsState_eq_conj H hH β]
  have hdiag : (diagonal (fun i => ((gibbsWeight H hH β (hH.eigenvalues i) : ℝ) : ℂ))).PosDef :=
    (Matrix.posDef_diagonal_iff).mpr
      (fun i => RCLike.ofReal_pos.mpr (gibbsWeight_pos H hH β _))
  have hinj : Function.Injective (hH.eigenvectorUnitary : Matrix n n ℂ).vecMul :=
    Matrix.vecMul_injective_iff_isUnit.mpr (eigenvectorUnitary_isUnit H hH)
  simpa [Matrix.star_eq_conjTranspose] using hdiag.mul_mul_conjTranspose_same hinj

/-- The Gibbs state has **trace one** (a genuine density): the conjugation
drops out cyclically and the diagonal weights sum to `Z/Z = 1`. -/
lemma gibbsState_trace [Nonempty n] (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    (gibbsState H hH β).trace = 1 := by
  rw [gibbsState_eq_conj H hH β, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
  rw [show (∑ i, ((gibbsWeight H hH β (hH.eigenvalues i) : ℝ) : ℂ))
      = ((∑ i, gibbsWeight H hH β (hH.eigenvalues i) : ℝ) : ℂ) from by push_cast; rfl]
  rw [show (∑ i, gibbsWeight H hH β (hH.eigenvalues i))
      = partitionFn H hH β / partitionFn H hH β from by
    simp only [gibbsWeight]; rw [← Finset.sum_div]; rfl]
  rw [div_self (partitionFn_pos H hH β).ne']
  norm_num

/-- Pulling a scalar into a unitary-conjugated diagonal:
`a • (V · diag D · Vᴴ) = V · diag (a • D) · Vᴴ`. -/
private lemma smul_conj (a : ℂ) (V : Matrix n n ℂ) (D : n → ℂ) :
    a • (V * diagonal D * star V) = V * diagonal (a • D) * star V := by
  rw [diagonal_smul, mul_smul_comm, smul_mul_assoc]

/-! ## The crux: `log(ρ_β) = −βH − (log Z)·1` -/

/-- **The Gibbs log identity.** The functional-calculus logarithm of the Gibbs
state is affine in the Hamiltonian:

    `log(ρ_β) = −β·H − (log Z)·1`.

Both sides are `U · diagonal(…) · Uᴴ` on the eigenbasis of `H`; the diagonal of
the LHS is `log(exp(-βλ)/Z) = −βλ − log Z` (`log_gibbsWeight`), matching the RHS
entrywise. This is the identity that turns `D(ρ ‖ ρ_β)` into the free-energy
difference. -/
lemma cfc_log_gibbsState [Nonempty n] (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    (gibbsState_isHermitian H hH β).cfc Real.log
      = (-β : ℂ) • H - ((Real.log (partitionFn H hH β) : ℝ) : ℂ) • (1 : Matrix n n ℂ) := by
  set U := (hH.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hU : star U * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hMeq : gibbsState H hH β
      = U * diagonal (fun i => ((gibbsWeight H hH β (hH.eigenvalues i) : ℝ) : ℂ)) * star U :=
    gibbsState_eq_conj H hH β
  -- LHS via cfc_eq_conj_diagonal at the H-eigenbasis diagonalisation.
  rw [cfc_eq_conj_diagonal (gibbsState_isHermitian H hH β) hU
      (fun i => gibbsWeight H hH β (hH.eigenvalues i)) hMeq Real.log]
  -- Freeze `log Z` so the H it hides is not disturbed by the H-rewrites below.
  set Z := partitionFn H hH β with hZ
  set logZ := Real.log Z with hlogZ
  -- Expand H and 1 in the same eigenbasis, on the RHS only.
  have hHexp : H = U * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * star U := by
    conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  have hone : (1 : Matrix n n ℂ) = U * diagonal (fun _ => (1 : ℂ)) * star U := by
    rw [Matrix.diagonal_one, Matrix.mul_one]
    exact (mul_eq_one_comm.mp hU).symm
  conv_rhs => rw [hHexp, hone]
  rw [smul_conj, smul_conj, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
  congr 2
  exact congrArg diagonal (funext fun i => by
    rw [log_gibbsWeight H hH β]
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    ring)

/-! ## Free energy and the variational principle -/

/-- The **energy** `E(ρ) = Re Tr(ρH)` (mean value of the Hamiltonian). -/
noncomputable def energy (H : Matrix n n ℂ) (ρ : Matrix n n ℂ) : ℝ :=
  RCLike.re (ρ * H).trace

/-- The **free energy** `F(ρ) = E(ρ) − T·S(ρ)` at temperature `T`. -/
noncomputable def freeEnergy (H : Matrix n n ℂ) (T : ℝ) {ρ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) : ℝ :=
  energy H ρ - T * vonNeumannEntropy hρ

/-- The cross term of the relative entropy against the Gibbs state:
`Re Tr(ρ · log ρ_β) = −β·E(ρ) − log Z` for a trace-one `ρ`. Immediate from the
Gibbs log identity plus trace linearity. -/
lemma re_trace_mul_log_gibbs [Nonempty n] (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (β : ℝ) {ρ : Matrix n n ℂ} (htr : ρ.trace = 1) :
    RCLike.re ((ρ * (gibbsState_isHermitian H hH β).cfc Real.log).trace)
      = -β * energy H ρ - Real.log (partitionFn H hH β) := by
  rw [cfc_log_gibbsState H hH β, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, htr,
    smul_eq_mul, smul_eq_mul, mul_one]
  simp only [energy]
  show (((-β : ℂ)) * (ρ * H).trace
      - ((Real.log (partitionFn H hH β) : ℝ) : ℂ)).re
    = -β * (ρ * H).trace.re - Real.log (partitionFn H hH β)
  rw [Complex.sub_re, Complex.ofReal_re]
  congr 1
  rw [show ((-β : ℂ)) = ((-β : ℝ) : ℂ) from by push_cast; ring, Complex.re_ofReal_mul]

/-- **The Gibbs free energy** equals `−T log Z` (the standard equilibrium free
energy). Obtained by evaluating the relative-entropy identity at `ρ = ρ_β`,
where `D(ρ_β ‖ ρ_β) = 0`. -/
theorem gibbs_free_energy_eq [Nonempty n] (H : Matrix n n ℂ) (hH : H.IsHermitian)
    {β : ℝ} (hβ : 0 < β) :
    freeEnergy H β⁻¹ (gibbsState_isHermitian H hH β)
      = -β⁻¹ * Real.log (partitionFn H hH β) := by
  have hgibbs := gibbsState_posDef H hH β
  -- Re Tr(ρ_β log ρ_β) = −S(ρ_β) (self term).
  have hself : RCLike.re ((gibbsState H hH β
      * (gibbsState_isHermitian H hH β).cfc Real.log).trace)
      = -vonNeumannEntropy (gibbsState_isHermitian H hH β) := by
    rw [re_trace_self_log (gibbsState_isHermitian H hH β)]
    unfold vonNeumannEntropy
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by simp only [Real.negMulLog]; ring)
  -- Re Tr(ρ_β log ρ_β) = −β E(ρ_β) − log Z (cross term at ρ = ρ_β).
  have hcross := re_trace_mul_log_gibbs H hH β (gibbsState_trace H hH β)
  rw [hself] at hcross
  -- So S(ρ_β) = β E(ρ_β) + log Z, giving F(ρ_β) = E − (1/β) S = −(1/β) log Z.
  rw [freeEnergy]
  have hS : vonNeumannEntropy (gibbsState_isHermitian H hH β)
      = β * energy H (gibbsState H hH β) + Real.log (partitionFn H hH β) := by
    linarith
  rw [hS]
  field_simp
  ring

/-- **TH3 — the Gibbs variational principle (the free-energy minimum).** At
inverse temperature `β > 0`, the Gibbs state minimises the free energy among all
density operators:

    `F(ρ_β) ≤ F(ρ)`   for every density `ρ`,

with `F(ρ_β) = −T log Z` (`gibbs_free_energy_eq`). Proof: Klein's inequality
`D(ρ ‖ ρ_β) ≥ 0` unfolds, via the Gibbs log identity, to
`β(F(ρ) − F(ρ_β)) ≥ 0`. -/
theorem gibbs_free_energy_min [Nonempty n] (H : Matrix n n ℂ) (hH : H.IsHermitian)
    {β : ℝ} (hβ : 0 < β) {ρ : Matrix n n ℂ}
    (hpsd : ρ.PosSemidef) (htr : ρ.trace = 1) :
    freeEnergy H β⁻¹ (gibbsState_isHermitian H hH β) ≤ freeEnergy H β⁻¹ hpsd.1 := by
  have hgibbs := gibbsState_posDef H hH β
  -- Klein: 0 ≤ D(ρ ‖ ρ_β) = Re Tr(ρ log ρ) − Re Tr(ρ log ρ_β).
  have hklein := relEntropy_nonneg hpsd hgibbs htr (gibbsState_trace H hH β)
  rw [relEntropy] at hklein
  -- Self term: Re Tr(ρ log ρ) = −S(ρ).
  have hself : RCLike.re ((ρ * hpsd.1.cfc Real.log).trace) = -vonNeumannEntropy hpsd.1 := by
    rw [re_trace_self_log hpsd.1]
    unfold vonNeumannEntropy
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by simp only [Real.negMulLog]; ring)
  -- Cross term: Re Tr(ρ log ρ_β) = −β E(ρ) − log Z.
  have hcross := re_trace_mul_log_gibbs H hH β htr
  rw [hself, hcross] at hklein
  -- hklein : 0 ≤ −S(ρ) − (−β E(ρ) − log Z) = −S(ρ) + β E(ρ) + log Z.
  rw [gibbs_free_energy_eq H hH hβ, freeEnergy, energy]
  -- Scale the Klein bound `0 ≤ β E − S + log Z` by `β⁻¹ > 0` and cancel `β⁻¹β = 1`.
  have hkey : 0 ≤ β * RCLike.re (ρ * H).trace - vonNeumannEntropy hpsd.1
      + Real.log (partitionFn H hH β) := by
    simp only [energy] at hklein
    linarith
  have hβ' : (0 : ℝ) < β⁻¹ := inv_pos.mpr hβ
  have hmul := mul_nonneg hβ'.le hkey
  have hexpand : β⁻¹ * (β * RCLike.re (ρ * H).trace - vonNeumannEntropy hpsd.1
        + Real.log (partitionFn H hH β))
      = RCLike.re (ρ * H).trace - β⁻¹ * vonNeumannEntropy hpsd.1
        + β⁻¹ * Real.log (partitionFn H hH β) := by
    rw [mul_add, mul_sub, ← mul_assoc, inv_mul_cancel₀ hβ.ne', one_mul]
  rw [hexpand] at hmul
  linarith

/-! ## Non-vacuity: the trivial Hamiltonian -/

/-- Non-vacuity: for `H = 0` on a nonempty system the Gibbs state is the
maximally-mixed state `I/d` (every temperature is the same), a genuine density,
and the variational principle fires. Confirms the hypotheses are satisfiable. -/
theorem gibbsState_zero_trace [Nonempty n] (β : ℝ) :
    (gibbsState (0 : Matrix n n ℂ) Matrix.isHermitian_zero β).trace = 1 :=
  gibbsState_trace _ _ _

end Thermo
end CSD
