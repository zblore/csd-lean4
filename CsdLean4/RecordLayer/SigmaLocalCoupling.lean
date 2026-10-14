/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.CellLawForced
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Hermitian

/-!
# RecordLayer/SigmaLocalCoupling: the cell law from a Σ-local coupling

**Category:** 7-SigmaLayer (the record layer — the premise conversion for Posit 1, BACKLOG #152).
**TERM-SCOPE(Hamiltonian)** — the vector-field sense, at the *linear* level; `specs/TERMS.md`.

`CellLawForced.lean` characterises the cell law by **generation**: a rate field whose rates are
the normalised Hamiltonians of the coordinate phase rotations is the moment map. That premise is
about the rates. This module moves the premise onto the **measurement coupling**, which is where
a Σ-local account must put it, and proves the cell law from there.

## The coupling

A Σ-local measurement couples the base (the calculation space `ℂℙ^{N−1}`, the state QM calculates
with) to the fibre register through a product Hamiltonian `H = Q_A(x) · p_R`: a base observable
times the register momentum. Hamilton's equations say the register drifts at speed `Q_A(x)` while
the base is moved by the Hamiltonian flow of `Q_A` — the back-reaction `BackReactionNecessity.lean`
shows a Σ-local measurement must have. Only the base operator `A` enters here:
`SigmaLocalCoupling N` is a Hermitian `A` that is **einselected** in the context's basis, i.e.
commutes with every coordinate projector `|eᵢ⟩⟨eᵢ|` (`pointer_invariant_iff_commute`: the pointer
observables of an interaction are exactly the ones commuting with it).

## What is proved

* `A_eq_diagonal`: einselection makes `A` diagonal, with real spectrum `eig` (Hermitian).
* ★★ `baseGen_eq_sum`: the base generator `Q_A = ½ re⟪x, Ax⟫` is `∑ λᵢ · coordEnergy i` — a
  torus Hamiltonian; and ★★ `fundamentalForm_torusField`: **its Hamiltonian vector field is the
  torus field `∑ λᵢ • phaseGen i`**. Einselection makes the back-reaction *generate the context's
  torus action*, at the eigenvalue speeds. This is Posit 1's "the dynamics generates the torus
  action", as a theorem given einselection.
* ★ `drift_eq_sum_momentMap`: the degree-0 drift of the register is the eigenvalue average under
  the moment map, `⟨A⟩ = ∑ λᵢ Φᵢ`.
* ★★★ `isCalibrated_forall_iff`: a rate field is **calibrated** against a coupling when the
  rate-weighted average of the outcome labels (the eigenvalues) equals the register's drift. A
  rate field calibrated against *every* einselected coupling **is the moment map**, and
  conversely. The forward direction needs only the `N` projector couplings.
* ★★★ `isTorusGenerated_of_calibrated` / `rate_eq_momentMap_of_calibrated`: the context field so
  calibrated is torus-generated and its rates are the moment map — the premise conversion:

  **Posit 1 ⟸ (Σ-local product coupling) ∧ (einselected in the context's basis) ∧ (readout
  calibrated to the drift for every such coupling).**

## ⚠️ What "the rates read off the coupling" had to mean, and why

The row's phrasing asked for `IsGeneratedRateField` "for the rates read off the coupling". The
obvious reading — divide the `i`-th summand `λᵢ · coordEnergy i` by its speed `λᵢ` and normalise
— is **vacuous**: the unit-speed outcome generator is `coordEnergy i` whatever the coupling is,
so no coupling is consulted and the conclusion is `isTorusGenerated_momentContext` again. That is
recorded here as a finding. The non-vacuous reading is **calibration**: the labelled readout
(outcome `i` labelled by the eigenvalue `λᵢ`, the pointer displacement when the system is the
eigenstate) averages, over the ontic fibre, to what the coupling actually does to the register.
It says nothing about any single outcome's weight; it constrains the *mean* for each coupling in
the context's commutant, and that is enough. The principle is the author's to accept or reword;
the Lean content is the equivalence.

## Honest scope

* **The fibre half is prose.** `H = Q_A · p_R` and `q̇_R = Q_A` are Hamilton's equations on the
  arena, whose manifold flow is `R-016`'s business; this module uses only the base operator.
* **Which coupling an apparatus realises** is `R-015`, a boundary; the class is named, not
  derived.
* **Linear level**, as `CellLawForced.lean`: `fundamentalForm`, `phaseGen` and `quadraticEnergy`
  on `ℂᴺ`, with the ray-level statements through `momentMap`.

References: `specs/BACKLOG.md` #152, #151, #19; `specs/POSITS.md` Posit 1; `RecordLayer/CellLawForced.lean`
(`IsPhaseHamiltonian`, `coordEnergy`, `phaseGen`, `generatedRateField_eq_momentMap`);
`RecordLayer/BackReactionNecessity.lean`; `Empirical/CSD/PointerCommutation.lean`
(`pointer_invariant_iff_commute`); `Mathlib/Analysis/InnerProductSpace/HamiltonianVectorField.lean`
(`quadraticEnergy_hamiltonian_duality`); `specs/way-theorem-scoping.md` (brick 2, the
premise-conversion precedent).
-/

@[expose] public section

open Kahler Matrix
open scoped ComplexConjugate

namespace CSD
namespace RecordLayer

open LF4

variable {N : ℕ}

/-! ### The coupling, by its base operator -/

/-- A **Σ-local product coupling** `H = Q_A(x) · p_R`, recorded by its base operator: a Hermitian
matrix on the context's Hilbert space, **einselected** in the context's basis — it commutes with
every coordinate projector `|eᵢ⟩⟨eᵢ| = Matrix.single i i 1`. -/
structure SigmaLocalCoupling (N : ℕ) where
  /-- The base operator. -/
  A : Matrix (Fin N) (Fin N) ℂ
  /-- The base operator is Hermitian. -/
  hermitian : A.IsHermitian
  /-- The context's basis is the pointer basis: every coordinate projector commutes with `A`. -/
  einselected : ∀ i : Fin N, Commute (Matrix.single i i (1 : ℂ)) A

/-- A matrix commuting with every coordinate projector has no off-diagonal entries. -/
lemma apply_of_ne_of_commute_single {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : ∀ i : Fin N, Commute (Matrix.single i i (1 : ℂ)) A) {i j : Fin N} (h : i ≠ j) :
    A i j = 0 := by
  have hc : (Matrix.single i i (1 : ℂ) * A) i j = (A * Matrix.single i i (1 : ℂ)) i j := by
    rw [(hA i).eq]
  rw [Matrix.single_mul_apply_same, one_mul] at hc
  rw [hc]
  simp [Matrix.mul_apply, h]

namespace SigmaLocalCoupling

variable (S : SigmaLocalCoupling N)

/-- Einselection kills the off-diagonal entries. -/
lemma apply_of_ne {i j : Fin N} (h : i ≠ j) : S.A i j = 0 :=
  apply_of_ne_of_commute_single S.einselected h

/-- The spectrum: the diagonal, real because `A` is Hermitian. -/
noncomputable def eig (i : Fin N) : ℝ := RCLike.re (S.A i i)

lemma A_apply_self (i : Fin N) : S.A i i = (S.eig i : ℂ) :=
  (S.hermitian.coe_re_apply_self i).symm

/-- **Einselection makes the base operator diagonal**, with spectrum `eig`. -/
theorem A_eq_diagonal : S.A = Matrix.diagonal fun i => (S.eig i : ℂ) := by
  ext i j
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, A_apply_self]
  · rw [Matrix.diagonal_apply_ne _ h, S.apply_of_ne h]

/-- The base operator as an operator on the context's Hilbert space. -/
noncomputable def op : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N) S.A

lemma op_symm (u v : EuclideanSpace ℂ (Fin N)) : inner ℂ (S.op u) v = inner ℂ u (S.op v) :=
  (Matrix.isSymmetric_toEuclideanLin_iff.2 S.hermitian) u v

/-- The operator acts coordinatewise by the spectrum. -/
lemma op_apply (x : EuclideanSpace ℂ (Fin N)) (i : Fin N) : S.op x i = (S.eig i : ℂ) * x i := by
  have h : S.op x = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N)
      (Matrix.diagonal fun j => (S.eig j : ℂ)) x := by
    rw [op, ← A_eq_diagonal]
  rw [h]
  show ((Matrix.diagonal fun j => (S.eig j : ℂ)) *ᵥ (WithLp.ofLp x)) i = _
  rw [Matrix.mulVec_diagonal]

/-! ### The base generator is a torus Hamiltonian -/

/-- The **base generator** `Q_A(x) = ½ re⟪x, A x⟫`: the base observable of the coupling, whose
Hamiltonian flow is the back-reaction and whose value is the register's drift. -/
noncomputable def baseGen : EuclideanSpace ℂ (Fin N) → ℝ := quadraticEnergy S.op

/-- ★★ **Einselection ⇒ the base generator is a torus Hamiltonian**: `Q_A = ∑ λᵢ · coordEnergy i`. -/
theorem baseGen_eq_sum (x : EuclideanSpace ℂ (Fin N)) :
    S.baseGen x = ∑ i, S.eig i * coordEnergy i x := by
  have hterm : ∀ i : Fin N, (inner ℂ (x i) (S.op x i)).re = S.eig i * ‖x i‖ ^ 2 := fun i => by
    rw [op_apply, RCLike.inner_apply, mul_assoc, Complex.mul_conj', ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  unfold baseGen quadraticEnergy metric
  rw [PiLp.inner_apply, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hterm, coordEnergy]
  ring

/-- ★★ **Einselection ⇒ the back-reaction is the torus flow at the eigenvalue speeds**: the
Hamiltonian vector field of the base generator is `∑ λᵢ • phaseGen i`, i.e.
`ι_{∑ λᵢ X_i} ω = dQ_A`. -/
theorem fundamentalForm_torusField (x v : EuclideanSpace ℂ (Fin N)) :
    fundamentalForm (∑ i, S.eig i • phaseGen i x) v = fderiv ℝ S.baseGen x v := by
  have hdual := quadraticEnergy_hamiltonian_duality S.op S.op_symm x v
  rw [baseGen, ← hdual]
  congr 1
  ext j
  simp [hamiltonianVectorFieldOf, complexStructure, phaseGen, coordProj_apply, op_apply]
  simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-! ### Drift and calibration -/

/-- The **drift**: the base generator normalised to degree `0`, the register's speed per unit
momentum as a function of the ray — `⟨A⟩` at a unit representative. -/
noncomputable def drift (p : CPN N) : ℝ := S.baseGen p.rep / (‖p.rep‖ ^ 2 / 2)

/-- ★ **The drift is the eigenvalue average under the moment map**: `⟨A⟩ = ∑ λᵢ Φᵢ`. -/
theorem drift_eq_sum_momentMap (p : CPN N) : S.drift p = ∑ i, S.eig i * momentMap p i := by
  have hn : ‖p.rep‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr p.rep_nonzero)
  unfold drift
  rw [baseGen_eq_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coordEnergy, momentMap]
  field_simp

/-- A rate field is **calibrated** against the coupling `S` when the rate-weighted average of the
outcome labels (the eigenvalues) is the register's drift, at every preparation. -/
def IsCalibrated (rate : CPN N → Fin N → ℝ) (S : SigmaLocalCoupling N) : Prop :=
  ∀ p : CPN N, ∑ i, rate p i * S.eig i = S.drift p

end SigmaLocalCoupling

/-- The diagonal coupling with real spectrum `d` — in particular the projector couplings
`d = Pi.single j 1`. -/
noncomputable def SigmaLocalCoupling.ofDiagonal (d : Fin N → ℝ) : SigmaLocalCoupling N where
  A := Matrix.diagonal fun i => (d i : ℂ)
  hermitian := Matrix.isHermitian_diagonal_of_self_adjoint _ (by
    rw [isSelfAdjoint_iff]
    funext i
    simp)
  einselected := fun i => by
    show Matrix.single i i (1 : ℂ) * Matrix.diagonal (fun j => (d j : ℂ))
        = Matrix.diagonal (fun j => (d j : ℂ)) * Matrix.single i i 1
    ext a b
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
    split_ifs with hab
    · obtain ⟨rfl, rfl⟩ := hab
      ring
    · ring

lemma SigmaLocalCoupling.eig_ofDiagonal (d : Fin N → ℝ) (i : Fin N) :
    (SigmaLocalCoupling.ofDiagonal d).eig i = d i := by
  simp [SigmaLocalCoupling.eig, SigmaLocalCoupling.ofDiagonal, Matrix.diagonal_apply_eq]

open SigmaLocalCoupling in
/-- ★★★ **The cell law is forced by calibration.** A rate field calibrated against every
einselected coupling is the moment map, and the moment map is calibrated against every such
coupling. The forward direction uses only the `N` projector couplings. -/
theorem isCalibrated_forall_iff (rate : CPN N → Fin N → ℝ) :
    (∀ S : SigmaLocalCoupling N, IsCalibrated rate S) ↔ rate = momentMap := by
  constructor
  · intro h
    funext p j
    have hj := h (ofDiagonal (Pi.single j 1)) p
    rw [drift_eq_sum_momentMap] at hj
    simp only [eig_ofDiagonal, Pi.single_apply, mul_ite, ite_mul, mul_one, mul_zero, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hj
    exact hj
  · rintro rfl S p
    rw [drift_eq_sum_momentMap]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

open SigmaLocalCoupling in
/-- ★★★ **The premise conversion for Posit 1**: a context field calibrated against every
einselected Σ-local coupling has the moment map for its rates. -/
theorem rate_eq_momentMap_of_calibrated (c : ContextField N)
    (h : ∀ S : SigmaLocalCoupling N, IsCalibrated c.rate S) (p : CPN N) (i : Fin N) :
    c.rate p i = momentMap p i := by
  rw [(isCalibrated_forall_iff c.rate).1 h]

open SigmaLocalCoupling in
/-- ★★★ A context field calibrated against every einselected Σ-local coupling is
**torus-generated**: calibration implies generation. -/
theorem isTorusGenerated_of_calibrated (c : ContextField N)
    (h : ∀ S : SigmaLocalCoupling N, IsCalibrated c.rate S) : IsTorusGenerated c := by
  show IsGeneratedRateField c.rate
  rw [(isCalibrated_forall_iff c.rate).1 h]
  exact isTorusGenerated_momentContext

end RecordLayer
end CSD

end
