/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Mathlib.QuantumInfo.Subadditivity
import CsdLean4.Mathlib.QuantumInfo.Entropy

/-!
# TH2: the second law as coarse-grained entropy monotonicity

**Category:** conceptually 1-Mathlib (CSD-free general quantum statistical
mechanics) with a CSD reading; kept in the `CSD.Thermo` tree alongside TH1
because its physical content is the CSD H-theorem.

The CSD thermodynamic picture (`specs/thermo-plan.md`): the fine-grained
de-isolation flow is unitary, hence **entropy-conserving** (Liouville /
reversibility); irreversibility enters through **coarse-graining** — passing
to the pointer-basis diagonal (dephasing). This module proves the
H-theorem form of the second law for that coarse-graining:

    `S(ρ) ≤ S(pinch ρ)`,

pinching (dephasing to the pointer-basis diagonal) never decreases the von
Neumann entropy. The fine-grained step conserves entropy
(`vonNeumannEntropy_conj_unitary`, K1); the coarse-graining step increases
it. Together: reversible microdynamics, entropy increase from
coarse-graining — the Boltzmann/Gibbs picture, native to the CSD substrate.

## Main results

* `pinch` : the pointer-basis dephasing / coarse-graining map
  `ρ ↦ diagonal (fun i => (ρ i i).re)`. Hermitian; trace-preserving on
  densities; positive-definite when the pointer weights are all positive.
* `vonNeumannEntropy_le_pinching` (**TH2, the H-theorem**): for a density `ρ`
  with strictly positive pointer weights, `S(ρ) ≤ S(pinch ρ)`. Via Klein's
  inequality `D(ρ ‖ pinch ρ) ≥ 0` and the diagonal identity
  `Tr(ρ · log(pinch ρ)) = Tr(pinch ρ · log(pinch ρ)) = −S(pinch ρ)`.
* `entropy_reversible_then_coarsegrain` (**the second-law statement**): a
  fine-grained unitary step conserves entropy and the following
  coarse-graining does not decrease it, so `S(ρ) ≤ S(pinch (U ρ Uᴴ))`.
* `entropy_production_nonneg` (**the sign of the second law**): the entropy
  gained by pinching, `S(pinch ρ) − S(ρ) ≥ 0`. Its pure-state instance
  (`S(ρ)=0`, Born weights on the diagonal) is the entropy-production witness of
  the decoherence tier (LF6-B.3, `decohere_vonNeumann_entropy_nonneg`),
  recovered here as an instance of the general monotonicity.

## Honest scope

The strict-positivity hypothesis on the pointer weights (`pinch ρ`
positive-definite) is Klein's support condition; without it the finite
`negMulLog`-junk expression can misbehave (the same discipline as
`relEntropy_nonneg`). For a pure state with a vanishing Born weight the
inequality still holds by continuity, but the clean Klein route needs full
support; the pure-state corollary is stated under it. This is the
H-theorem for a SPECIFIC coarse-graining (the pointer-basis pinch), not a
universal second law, and it is a statement about the coarse-graining map,
not a proof that a given state thermalises dynamically (that needs
mixing / ETH; the CSD-microdynamics reading rests on the shared A5/D1
residue, as across the thermo track).

## Provenance

Foundational-triple only (`propext, Classical.choice, Quot.sound`); no
`sorry`, no new axioms. Reuses K1 (`vonNeumannEntropy`,
`vonNeumannEntropy_diagonal`, `vonNeumannEntropy_conj_unitary`) and the
Klein / relative-entropy layer (`klein_inequality`, `cfc_eq_conj_diagonal`,
`re_trace_self_log`); nothing is re-proved.
-/

open scoped BigOperators ComplexOrder
open Matrix QuantumInfo

namespace CSD
namespace Thermo

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The pointer-basis pinching (dephasing) map -/

/-- The **pointer-basis pinching** (dephasing) map: replace `ρ` by the diagonal
matrix of its (real) diagonal entries. This is the coarse-graining that
discards the off-diagonal coherences in the pointer basis — the irreversible
step of a de-isolation measurement. -/
noncomputable def pinch (ρ : Matrix n n ℂ) : Matrix n n ℂ :=
  diagonal (fun i => ((ρ i i).re : ℂ))

@[simp] lemma pinch_apply (ρ : Matrix n n ℂ) (i j : n) :
    pinch ρ i j = if i = j then ((ρ i i).re : ℂ) else 0 := by
  simp [pinch, diagonal_apply]

omit [Fintype n] in
/-- `pinch ρ` is Hermitian (a real-diagonal matrix). -/
lemma pinch_isHermitian (ρ : Matrix n n ℂ) : (pinch ρ).IsHermitian :=
  isHermitian_diagonal_of_self_adjoint _
    (funext fun i => (RCLike.conj_ofReal ((ρ i i).re)))

/-- On a Hermitian `ρ`, the pinched diagonal entry IS the original diagonal
entry: `ρ i i = (ρ i i).re`, since Hermitian forces real diagonal. -/
lemma diag_ofReal_re_of_isHermitian {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (i : n) : ((ρ i i).re : ℂ) = ρ i i := by
  have h : (starRingEnd ℂ) (ρ i i) = ρ i i := by
    have hh := congrFun (congrFun hρ i) i
    rw [Matrix.conjTranspose_apply, Complex.star_def] at hh
    exact hh
  exact Complex.conj_eq_iff_re.mp h

/-- Pinching preserves the trace of a Hermitian matrix (real diagonal): the
diagonal is untouched. -/
lemma pinch_trace_of_isHermitian {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    (pinch ρ).trace = ρ.trace := by
  rw [pinch, trace_diagonal, Matrix.trace]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [diag_apply]
  exact diag_ofReal_re_of_isHermitian hρ i

/-- Pinching a trace-one density gives a trace-one density. -/
lemma pinch_trace_one {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (htr : ρ.trace = 1) :
    (pinch ρ).trace = 1 := by
  rw [pinch_trace_of_isHermitian hρ, htr]

/-- When all pointer weights `(ρ i i).re` are strictly positive, `pinch ρ` is
positive-definite (Klein's support condition). -/
lemma pinch_posDef {ρ : Matrix n n ℂ} (hpos : ∀ i, 0 < (ρ i i).re) :
    (pinch ρ).PosDef := by
  unfold pinch
  exact (Matrix.posDef_diagonal_iff).mpr (fun i => RCLike.ofReal_pos.mpr (hpos i))

/-! ## The `cfc log` of a pinched (diagonal) state -/

/-- The continuous functional calculus of a real function on the pinched
(diagonal) state is diagonal: `cfc f (pinch ρ) = diagonal (f ∘ pointer-weights)`.
Instance of `cfc_eq_conj_diagonal` at the trivial diagonalisation `U = 1`. -/
lemma pinch_cfc (ρ : Matrix n n ℂ) (f : ℝ → ℝ) :
    (pinch_isHermitian ρ).cfc f
      = diagonal (fun i => ((f ((ρ i i).re) : ℝ) : ℂ)) := by
  have hU : (star (1 : Matrix n n ℂ)) * 1 = 1 := by simp
  have hMeq : pinch ρ
      = (1 : Matrix n n ℂ) * diagonal (fun i => (((ρ i i).re : ℝ) : ℂ)) * star 1 := by
    simp [pinch]
  rw [cfc_eq_conj_diagonal (pinch_isHermitian ρ) hU (fun i => (ρ i i).re) hMeq f]
  simp

/-! ## The cross term `Tr(ρ · log(pinch ρ))` -/

/-- **The diagonal cross-term identity.** `Re Tr(ρ · cfc log (pinch ρ))` sees
only the diagonal of `ρ`, so it collapses to the pointer-weight sum
`∑ᵢ (ρ i i).re · log((ρ i i).re) = −S(pinch ρ)`. This is the crux of the
H-theorem: the relative-entropy cross term is the pinched self-entropy. -/
lemma re_trace_mul_pinch_cfc_log (ρ : Matrix n n ℂ) :
    RCLike.re ((ρ * (pinch_isHermitian ρ).cfc Real.log).trace)
      = ∑ i, (ρ i i).re * Real.log ((ρ i i).re) := by
  rw [pinch_cfc ρ Real.log]
  have htr : (ρ * diagonal (fun i => ((Real.log ((ρ i i).re) : ℝ) : ℂ))).trace
      = ∑ i, ρ i i * ((Real.log ((ρ i i).re) : ℝ) : ℂ) := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [diag_apply, Matrix.mul_diagonal]
  rw [htr, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  show (ρ i i * ((Real.log ((ρ i i).re) : ℝ) : ℂ)).re
    = (ρ i i).re * Real.log ((ρ i i).re)
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-! ## The H-theorem -/

/-- **TH2 — the second law (H-theorem for pointer-basis coarse-graining).**
For a density `ρ` with strictly positive pointer weights, pinching does not
decrease the von Neumann entropy:

    `S(ρ) ≤ S(pinch ρ)`.

Proof: Klein's inequality gives `Tr(ρ log ρ) ≥ Tr(ρ log(pinch ρ))`; the RHS is
`−S(pinch ρ)` by the diagonal cross-term identity, the LHS is `−S(ρ)` by
`re_trace_self_log`. -/
theorem vonNeumannEntropy_le_pinching {ρ : Matrix n n ℂ}
    (hpsd : ρ.PosSemidef) (htr : ρ.trace = 1) (hpos : ∀ i, 0 < (ρ i i).re) :
    vonNeumannEntropy hpsd.1 ≤ vonNeumannEntropy (pinch_isHermitian ρ) := by
  have hpd : (pinch ρ).PosDef := pinch_posDef hpos
  have htrσ : (pinch ρ).trace = 1 := pinch_trace_one hpsd.1 htr
  -- Klein: Re Tr(ρ · cfc log (pinch ρ)) ≤ Re Tr(ρ · cfc log ρ).
  have hklein := klein_inequality hpsd hpd htr htrσ
  -- RHS: Re Tr(ρ · cfc log ρ) = ∑ eig · log eig = −S(ρ).
  have hself := re_trace_self_log hpsd.1
  have hSρ : RCLike.re ((ρ * hpsd.1.cfc Real.log).trace) = -vonNeumannEntropy hpsd.1 := by
    rw [hself]
    unfold vonNeumannEntropy
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by simp only [Real.negMulLog]; ring)
  -- LHS: Re Tr(ρ · cfc log (pinch ρ)) = ∑ pointer-weight · log = −S(pinch ρ).
  have hcross := re_trace_mul_pinch_cfc_log ρ
  have hSσ : RCLike.re ((ρ * (pinch_isHermitian ρ).cfc Real.log).trace)
      = -vonNeumannEntropy (pinch_isHermitian ρ) := by
    rw [hcross]
    have hd : vonNeumannEntropy (pinch_isHermitian ρ)
        = ∑ i, Real.negMulLog ((ρ i i).re) := vonNeumannEntropy_diagonal (pinch_isHermitian ρ)
    rw [hd, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by simp only [Real.negMulLog]; ring)
  rw [hSσ, hSρ] at hklein
  linarith

/-! ## The second-law statement: reversible step + coarse-graining -/

/-- **The second-law statement.** A fine-grained **unitary** step (the
reversible de-isolation microdynamics) conserves entropy, and the subsequent
**coarse-graining** (pinching to the pointer basis) does not decrease it:

    `S(ρ) = S(U ρ Uᴴ) ≤ S(pinch (U ρ Uᴴ))`.

The entropy of the isolated (unitarily-evolved) system is unchanged; all
entropy production is in the coarse-graining. -/
theorem entropy_reversible_then_coarsegrain {ρ U : Matrix n n ℂ}
    (hpsd : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hU : star U * U = 1)
    (hUρU : (U * ρ * star U).IsHermitian)
    (hpsdU : (U * ρ * star U).PosSemidef)
    (htrU : (U * ρ * star U).trace = 1)
    (hpos : ∀ i, 0 < ((U * ρ * star U) i i).re) :
    vonNeumannEntropy hpsd.1
      ≤ vonNeumannEntropy (pinch_isHermitian (U * ρ * star U)) := by
  have hconserve : vonNeumannEntropy hUρU = vonNeumannEntropy hpsd.1 :=
    vonNeumannEntropy_conj_unitary hpsd.1 hU hUρU
  have hincrease := vonNeumannEntropy_le_pinching hpsdU htrU hpos
  rw [hconserve] at hincrease
  exact hincrease

/-- **Entropy production is non-negative** (restatement of TH2): the entropy
gained by pinching, `S(pinch ρ) − S(ρ)`, is `≥ 0`. This is the sign of the
second law — coarse-graining produces entropy, never destroys it. The pure-state
instance (`S(ρ) = 0`, so `S(pinch ρ) ≥ 0` with the Born weights on the
diagonal) is the entropy-production witness already recorded at LF6-B.3
(`decohere_vonNeumann_entropy_nonneg`); here it is the general monotonicity. -/
theorem entropy_production_nonneg {ρ : Matrix n n ℂ}
    (hpsd : ρ.PosSemidef) (htr : ρ.trace = 1) (hpos : ∀ i, 0 < (ρ i i).re) :
    0 ≤ vonNeumannEntropy (pinch_isHermitian ρ) - vonNeumannEntropy hpsd.1 :=
  sub_nonneg.mpr (vonNeumannEntropy_le_pinching hpsd htr hpos)

end Thermo
end CSD
