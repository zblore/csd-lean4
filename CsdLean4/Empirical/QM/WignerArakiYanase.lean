/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.Contextuality.MerminPeres
public import CsdLean4.Empirical.QM.Algorithms.HadamardTest
public import CsdLean4.LF5.VonNeumannUnitary
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.TransitionProbability

/-!
# Empirical/QM: the Wigner–Araki–Yanase theorem

**Category:** 3-Local (promotion-ready to 2-Framework on demand, exactly as
`no_cloning_two_state` is). QM-generic: no CSD ontology, pure inner-product
geometry, plus `Fin 2 × Fin 2` matrix computations for the witnesses.

The Wigner–Araki–Yanase (WAY) theorem: an observable `A` of a system `S` that
fails to commute with the system part `L_S` of an *additively conserved*
quantity `L = L_S ⊗ 1 + 1 ⊗ L_A` admits no exact measurement by an isometric
interaction `U` on `HS ⊗ HA` conserving `L` — *provided* the pointer states are
insensitive to `L_A` (the Yanase condition `⟨ξ_i, L_A ξ_j⟩ = 0`, Yanase 1961)
or the measurement is repeatable (`⟨φ_i, φ_j⟩ = 0`). Contrapositively: exact,
Yanase-compliant (or repeatable) conserving measurements exist only for
observables commuting with `L_S`.

## The master identity

Everything follows from one line. For exact records `U (a ⊗ ξ) = φ ⊗ ξ₁`,
`U (a' ⊗ ξ) = φ' ⊗ ξ₂` of orthogonal system vectors `a ⊥ a'` from a unit ready
state `ξ`, conservation `L ∘ U = U ∘ L` and inner-product preservation give
(`arakiYanase_identity`)

  `⟨a, L_S a'⟩ = ⟨φ, L_S φ'⟩ · ⟨ξ₁, ξ₂⟩ + ⟨φ, φ'⟩ · ⟨ξ₁, L_A ξ₂⟩`.

Distinct pointer states `ξ₁ ⊥ ξ₂` kill the first term; the Yanase condition
*or* repeatability kills the second (`arakiYanase_offDiag_eq_zero`). Summing
over an eigenbasis of `A` then makes `L_S` block-diagonal in the eigenspaces of
`A`, i.e. `Commute A L_S` (`wigner_araki_yanase`); the no-go form
`no_exact_record_of_not_commute` is its contrapositive. Neither `a` nor `a'`
need be normalised, so the `σ_x` instance below runs on the raw vectors
`(1, 1)`, `(1, −1)`.

## Abstraction over the tensor structure

As in `no_cloning_two_state`, the tensor product enters only through a map
`tensor : HS → HA → HT` with the inner-product factorisation
`⟨tensor a b, tensor c d⟩ = ⟨a, c⟩ · ⟨b, d⟩`, and additivity of `L` only on
product vectors, `L (tensor a b) = tensor (L_S a) b + tensor a (L_A b)`. `U`
enters as an inner-product-preserving map commuting with `L`; no linearity of
`U`, no `Matrix.exp`, no unitary group, no `Star` synthesis. The witnesses
instantiate the idiom on `EuclideanSpace ℂ (Fin 2 × Fin 2)` with
`tensorEuc`/`swapMap` from `Empirical/QM/Algorithms/HadamardTest.lean` (both
factors are `Fin 2`, so the same-index product is the right one), `sigmaX`/`sigmaZ`
from `Empirical/QM/Contextuality/MerminPeres.lean`, the isometry of a unitary
matrix from `Projectivization.inner_toEuclideanLin_unitary`, and the measurement
unitary `LF5.vnUnitary 2`, which *is* CNOT (`(j, k) ↦ (j, j + k)` mod 2).

## Witnesses

* **The side condition is load-bearing** (`swap_exact_record_not_commute`):
  SWAP conserves `σ_z ⊗ 1 + 1 ⊗ σ_z` (`chargeZZ_swapMap`), records `σ_x`
  exactly from the ready state `|0⟩` with orthogonal pointers `(1, ±1)`, yet
  `⟨(1, 1), σ_z (1, −1)⟩ = 2 ≠ 0` (`inner_xPlus_sigmaZ_xMinus`). Both escape
  routes are closed there — the pointer fails Yanase *and* the record is not
  repeatable (`φ_± = |0⟩`) — so the theorem fails once both extra hypotheses
  are dropped. A reader cannot believe the side condition removable.
* **Non-vacuity** (`way_hypotheses_satisfiable`): CNOT conserves
  `σ_z ⊗ 1 + 1 ⊗ σ_x` (`chargeZX_mul_cnot`), records `σ_z` exactly and
  repeatably (`cnot_record`) with orthogonal pointers (`inner_ket`) — every
  hypothesis of `wigner_araki_yanase` is met, through the *repeatability*
  disjunct: the pointer fails Yanase against `L_A = σ_x`
  (`cnot_pointer_not_yanase`).
* **The no-go in use** (`sigmaX_no_exact_conserving_record`): no isometry
  conserving `σ_z ⊗ 1 + 1 ⊗ L_A`, for any `L_A`, records `σ_x` exactly with
  orthogonal pointers unless the pointer fails Yanase *and* the record is
  non-repeatable. `σ_x` has the eigenvectors of the corpus's `rotatedProj`
  (`Empirical/CSD/PointerCommutation.lean`, `rotatedProj_not_commute`), which
  this module does not import (layer hygiene: Empirical/QM sits below
  Empirical/CSD).

## Neighbours in the corpus

`pointer_basis_of_commuting` / `pointer_invariant_iff_commute`
(`Empirical/CSD/PointerCommutation.lean`) are the einselection direction: a
pointer `P` commuting with `H_int` on *one* space. WAY is about an additive
conserved quantity on a *tensor product* and the exactly recorded observable —
neighbours, not the same theorem; nothing is re-proved here.
`csd_robertson_uncertainty` (`Empirical/CSD/Uncertainty.lean`) is the other
uncertainty-type theorem of the Empirical layer. Quantitative WAY (Ozawa 2002:
the measurement error is bounded below by the inverse apparatus variance of
`L_A`) is not formalised.

## Where this sits relative to CSD

WAY constrains nothing in CSD, for different reasons at the two measurement
tiers. In the LF5 von Neumann tier its hypotheses *can* be met — `vnUnitary`
(`LF5/VonNeumannUnitary.lean`) is a tensor-product isometry, and the CNOT witness
below exhibits an additive `L` it conserves — and its conclusion then holds
trivially: the recorded computational basis is `L_S = σ_z`-diagonal. In the
record layer (`RecordLayer/`), the stroke `pointerEvolve` / `jointLift` is a skew
product on the arena `ℂℙ^{N−1} × T² × ℂℙ^N`, not a linear isometry on
`HS ⊗ HA`, and no additive `L_S ⊗ 1 + 1 ⊗ L_A` is modelled, so the hypotheses
are not met at all. In neither tier is a physical apparatus charge modelled —
a consequence of the `R-015` boundary in `specs/residues.tsv` (the coupling is
an engineered witness; which physical `H_int`, hence which conserved `L_A`, an
apparatus realises is a modelling input). This module is a QM-side theorem, not
a CSD result; the record-layer scope statement is its twin
`Empirical/CSD/WignerArakiYanase.lean` (`no_joint_hilbert_map`: no map on a joint
Hilbert space reproduces any joint lift's pointer image — the fibre register
selects the outcome; brick 1 of `specs/way-theorem-scoping.md` §3), and §2 W5–W7
there record what WAY does *not* say about the record layer.
`specs/qm-empirical-tests.md` (ER1, the twins board) and `specs/future-work.md`
(MT-1, the measurement-theoretic pillar row) index it.

## Experimental verification

WAY is a structural theorem, not a measured inequality. Its laboratory face is
Ozawa's conservative-quantum-computing bound (Ozawa 2002b): under an additive
conservation law a gate that fails to commute with the conserved charge — a
`σ_x` rotation under `σ_z` conservation — cannot be realised with unit fidelity
by a finite control system; the infidelity floor scales inversely with the
control's charge variance, which is the quantitative WAY theorem in gate form.

## Source

Wigner 1952, *Z. Phys.* **133**, 101; Araki–Yanase 1960, *Phys. Rev.* **120**,
622; Yanase 1961, *Phys. Rev.* **123**, 666; Ozawa 2002, *Phys. Rev. Lett.*
**88**, 050402 (quantitative form) and *Phys. Rev. Lett.* **89**, 057902
(conservative quantum computing); neither quantitative form is formalised here.
-/

@[expose] public section

open scoped Kronecker
open Matrix

namespace CSD
namespace Empirical
namespace QM
namespace WignerArakiYanase

/-! ## The abstract theorem -/

section Abstract

variable {HS HA HT : Type*}
  [NormedAddCommGroup HS] [InnerProductSpace ℂ HS]
  [NormedAddCommGroup HA] [InnerProductSpace ℂ HA]
  [NormedAddCommGroup HT] [InnerProductSpace ℂ HT]

/-- **The Araki–Yanase master identity.** For an inner-product-preserving `U` commuting
with an additive `L` (`L (a ⊗ b) = L_S a ⊗ b + a ⊗ L_A b`), a unit ready state `ξ`, orthogonal
system vectors `a ⊥ a'`, and exact records `U (a ⊗ ξ) = φ ⊗ ξ₁`, `U (a' ⊗ ξ) = φ' ⊗ ξ₂`,

  `⟨a, L_S a'⟩ = ⟨φ, L_S φ'⟩ · ⟨ξ₁, ξ₂⟩ + ⟨φ, φ'⟩ · ⟨ξ₁, L_A ξ₂⟩`.

Only `inner_add_right`, the factorisation, isometry and pointwise conservation are used:
no linearity of `U`, no additivity of `tensor`, and `a`, `a'` need not be normalised. -/
theorem arakiYanase_identity (tensor : HS → HA → HT)
    (h_tensor_inner : ∀ (a c : HS) (b d : HA),
      inner ℂ (tensor a b) (tensor c d) = inner ℂ a c * inner ℂ b d)
    (L : HT → HT) (LS : HS → HS) (LA : HA → HA)
    (h_add : ∀ (a : HS) (b : HA), L (tensor a b) = tensor (LS a) b + tensor a (LA b))
    (U : HT → HT) (hU : ∀ x y : HT, inner ℂ (U x) (U y) = inner ℂ x y)
    (hUL : ∀ x : HT, L (U x) = U (L x))
    (ξ : HA) (hξ : ‖ξ‖ = 1) {a a' : HS} (haa' : inner ℂ a a' = 0)
    {φ φ' : HS} {ξ₁ ξ₂ : HA}
    (hrec : U (tensor a ξ) = tensor φ ξ₁) (hrec' : U (tensor a' ξ) = tensor φ' ξ₂) :
    inner ℂ a (LS a')
      = inner ℂ φ (LS φ') * inner ℂ ξ₁ ξ₂ + inner ℂ φ φ' * inner ℂ ξ₁ (LA ξ₂) := by
  have hξξ : inner ℂ ξ ξ = 1 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hξ]; simp
  calc inner ℂ a (LS a')
      = inner ℂ a (LS a') * inner ℂ ξ ξ + inner ℂ a a' * inner ℂ ξ (LA ξ) := by
        rw [hξξ, haa']; ring
    _ = inner ℂ (tensor a ξ) (L (tensor a' ξ)) := by
        rw [h_add, inner_add_right, h_tensor_inner, h_tensor_inner]
    _ = inner ℂ (U (tensor a ξ)) (U (L (tensor a' ξ))) := (hU _ _).symm
    _ = inner ℂ (U (tensor a ξ)) (L (U (tensor a' ξ))) := by rw [hUL]
    _ = inner ℂ (tensor φ ξ₁) (L (tensor φ' ξ₂)) := by rw [hrec, hrec']
    _ = inner ℂ φ (LS φ') * inner ℂ ξ₁ ξ₂ + inner ℂ φ φ' * inner ℂ ξ₁ (LA ξ₂) := by
        rw [h_add, inner_add_right, h_tensor_inner, h_tensor_inner]

/-- **Off-diagonal vanishing.** With distinct (orthogonal) pointer states and *either* the
Yanase condition `⟨ξ₁, L_A ξ₂⟩ = 0` *or* repeatability `⟨φ, φ'⟩ = 0`, the master identity
forces `⟨a, L_S a'⟩ = 0`. The disjunction is the whole theorem: `swap_exact_record_not_commute`
shows the conclusion fails when both disjuncts fail. -/
theorem arakiYanase_offDiag_eq_zero (tensor : HS → HA → HT)
    (h_tensor_inner : ∀ (a c : HS) (b d : HA),
      inner ℂ (tensor a b) (tensor c d) = inner ℂ a c * inner ℂ b d)
    (L : HT → HT) (LS : HS → HS) (LA : HA → HA)
    (h_add : ∀ (a : HS) (b : HA), L (tensor a b) = tensor (LS a) b + tensor a (LA b))
    (U : HT → HT) (hU : ∀ x y : HT, inner ℂ (U x) (U y) = inner ℂ x y)
    (hUL : ∀ x : HT, L (U x) = U (L x))
    (ξ : HA) (hξ : ‖ξ‖ = 1) {a a' : HS} (haa' : inner ℂ a a' = 0)
    {φ φ' : HS} {ξ₁ ξ₂ : HA}
    (hrec : U (tensor a ξ) = tensor φ ξ₁) (hrec' : U (tensor a' ξ) = tensor φ' ξ₂)
    (hξ₁₂ : inner ℂ ξ₁ ξ₂ = 0)
    (hside : inner ℂ ξ₁ (LA ξ₂) = 0 ∨ inner ℂ φ φ' = 0) :
    inner ℂ a (LS a') = 0 := by
  rw [arakiYanase_identity tensor h_tensor_inner L LS LA h_add U hU hUL ξ hξ haa' hrec hrec',
    hξ₁₂, mul_zero, zero_add]
  rcases hside with h | h <;> simp [h]

/-- ★★ **Wigner–Araki–Yanase.** Let `A` be diagonal in an orthonormal basis `b` with
eigenvalues `α`, and let `U` be an inner-product-preserving interaction conserving the
additive `L = L_S ⊗ 1 + 1 ⊗ L_A` that records every `b i` exactly from the unit ready state
`ξ` (`U (b i ⊗ ξ) = φ i ⊗ ξ' i`) with pointers orthogonal across distinct eigenvalues. If, across
distinct eigenvalues, the pointers satisfy the Yanase condition or the record is repeatable,
then `Commute A L_S`. The hypotheses on the record are asked only across *distinct
eigenvalues*, so a degenerate `A` is covered. -/
theorem wigner_araki_yanase {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ HS)
    (A LS : Module.End ℂ HS) (α : ι → ℂ) (hA : ∀ i, A (b i) = α i • b i)
    (tensor : HS → HA → HT)
    (h_tensor_inner : ∀ (a c : HS) (b d : HA),
      inner ℂ (tensor a b) (tensor c d) = inner ℂ a c * inner ℂ b d)
    (L : HT → HT) (LA : HA → HA)
    (h_add : ∀ (a : HS) (c : HA), L (tensor a c) = tensor (LS a) c + tensor a (LA c))
    (U : HT → HT) (hU : ∀ x y : HT, inner ℂ (U x) (U y) = inner ℂ x y)
    (hUL : ∀ x : HT, L (U x) = U (L x))
    (ξ : HA) (hξ : ‖ξ‖ = 1) (φ : ι → HS) (ξ' : ι → HA)
    (hrec : ∀ i, U (tensor (b i) ξ) = tensor (φ i) (ξ' i))
    (hdistinct : ∀ i j, α i ≠ α j → inner ℂ (ξ' i) (ξ' j) = 0)
    (hside : ∀ i j, α i ≠ α j → inner ℂ (ξ' i) (LA (ξ' j)) = 0 ∨ inner ℂ (φ i) (φ j) = 0) :
    Commute A LS := by
  -- matrix elements of `L_S` between distinct eigenvalues of `A` vanish
  have hoff : ∀ i j, α i ≠ α j → inner ℂ (b i) (LS (b j)) = 0 := by
    intro i j hij
    have hne : i ≠ j := fun h => hij (congrArg α h)
    exact arakiYanase_offDiag_eq_zero tensor h_tensor_inner L LS LA h_add U hU hUL ξ hξ
      (b.orthonormal.inner_eq_zero hne) (hrec i) (hrec j) (hdistinct i j hij) (hside i j hij)
  show A * LS = LS * A
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp]
  refine b.toBasis.ext fun j => ?_
  simp only [LinearMap.comp_apply, OrthonormalBasis.coe_toBasis]
  have hexp := b.sum_repr' (LS (b j))
  calc A (LS (b j))
      = A (∑ i, inner ℂ (b i) (LS (b j)) • b i) := by rw [hexp]
    _ = ∑ i, inner ℂ (b i) (LS (b j)) • (α i • b i) := by simp only [map_sum, map_smul, hA]
    _ = ∑ i, inner ℂ (b i) (LS (b j)) • (α j • b i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : α i = α j
        · rw [h]
        · rw [hoff i j h]; simp
    _ = α j • ∑ i, inner ℂ (b i) (LS (b j)) • b i := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
    _ = α j • LS (b j) := by rw [hexp]
    _ = LS (α j • b j) := by rw [map_smul]
    _ = LS (A (b j)) := by rw [hA]

/-- ★ **The no-go form**, which is how the theorem is used: if `A` does not commute with
`L_S`, no ready state and no exact record with pointers orthogonal across distinct eigenvalues
and Yanase-compliant (or repeatable) across distinct eigenvalues exists for any conserving
isometry `U`. Contrapositive of `wigner_araki_yanase`. -/
theorem no_exact_record_of_not_commute {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ HS)
    (A LS : Module.End ℂ HS) (α : ι → ℂ) (hA : ∀ i, A (b i) = α i • b i)
    (hAL : ¬ Commute A LS)
    (tensor : HS → HA → HT)
    (h_tensor_inner : ∀ (a c : HS) (b d : HA),
      inner ℂ (tensor a b) (tensor c d) = inner ℂ a c * inner ℂ b d)
    (L : HT → HT) (LA : HA → HA)
    (h_add : ∀ (a : HS) (c : HA), L (tensor a c) = tensor (LS a) c + tensor a (LA c))
    (U : HT → HT) (hU : ∀ x y : HT, inner ℂ (U x) (U y) = inner ℂ x y)
    (hUL : ∀ x : HT, L (U x) = U (L x)) :
    ¬ ∃ (ξ : HA) (φ : ι → HS) (ξ' : ι → HA), ‖ξ‖ = 1 ∧
      (∀ i, U (tensor (b i) ξ) = tensor (φ i) (ξ' i)) ∧
      (∀ i j, α i ≠ α j → inner ℂ (ξ' i) (ξ' j) = 0) ∧
      (∀ i j, α i ≠ α j → inner ℂ (ξ' i) (LA (ξ' j)) = 0 ∨ inner ℂ (φ i) (φ j) = 0) := by
  rintro ⟨ξ, φ, ξ', hξ, hrec, hdistinct, hside⟩
  exact hAL (wigner_araki_yanase b A LS α hA tensor h_tensor_inner L LA h_add U hU hUL ξ hξ
    φ ξ' hrec hdistinct hside)

end Abstract

/-! ## Two-qubit infrastructure

Kronecker matrices act factorwise on `tensorEuc`; the computational kets and the unnormalised
`σ_x` eigenvectors, with their `σ_z`/`σ_x` actions and inner products. -/

section TwoQubit

open CSD.Empirical.MerminPeres (sigmaX sigmaZ)
open CSD.Empirical.QM.HadamardTest (tensorEuc tensorEuc_apply inner_tensorEuc swapMap
  swapMap_apply swapMap_tensorEuc inner_swapMap inner_eq_sum)
open CSD.LF5 (vnUnitary vnPerm)

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A Kronecker product acts factorwise on a product vector:
`(A ⊗ₖ B) (a ⊗ c) = (A a) ⊗ (B c)`. This is the additivity input for `L = L_S ⊗ₖ 1 + 1 ⊗ₖ L_A`.
Placed here rather than beside `tensorEuc` to keep `Kronecker` out of the Hadamard-test
import chain (`SigmaLayer/Interference.lean` sits downstream of it). -/
lemma toEuclideanLin_kronecker_tensorEuc (A B : Matrix κ κ ℂ) (a c : EuclideanSpace ℂ κ) :
    toEuclideanLin (A ⊗ₖ B) (tensorEuc a c)
      = tensorEuc (toEuclideanLin A a) (toEuclideanLin B c) := by
  ext ⟨i, j⟩
  simp only [toLpLin_apply, WithLp.ofLp_toLp, tensorEuc_apply, mulVec, dotProduct,
    kroneckerMap_apply, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- The computational ket `|j⟩ = EuclideanSpace.single j 1`. -/
noncomputable def ket (j : Fin 2) : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single j 1

/-- `‖|j⟩‖ = 1`. -/
lemma norm_ket (j : Fin 2) : ‖ket j‖ = 1 := by
  rw [ket, PiLp.norm_single, norm_one]

/-- `⟨i|j⟩ = δ_ij`. -/
lemma inner_ket (i j : Fin 2) : inner ℂ (ket i) (ket j) = if i = j then 1 else 0 := by
  simp [ket, EuclideanSpace.inner_single_left, PiLp.single_apply]

/-- `σ_z |j⟩ = (−1)^j |j⟩`: the computational basis is the `σ_z` eigenbasis. -/
lemma sigmaZ_ket (j : Fin 2) : toEuclideanLin sigmaZ (ket j) = (![1, -1] j : ℂ) • ket j := by
  ext i
  fin_cases i <;> fin_cases j <;> simp [ket, sigmaZ, toLpLin_apply]

/-- The computational basis as the orthonormal basis `EuclideanSpace.basisFun`, in `ket` form. -/
lemma basisFun_eq_ket (j : Fin 2) : EuclideanSpace.basisFun (Fin 2) ℂ j = ket j :=
  EuclideanSpace.basisFun_apply (ι := Fin 2) (𝕜 := ℂ) j

/-- `|j⟩ ⊗ |k⟩` is the standard basis vector at `(j, k)`. -/
lemma tensorEuc_ket (j k : Fin 2) :
    tensorEuc (ket j) (ket k) = WithLp.toLp 2 (Pi.single (j, k) (1 : ℂ)) := by
  ext ⟨p, q⟩
  simp only [tensorEuc_apply, ket, PiLp.single_apply, Pi.single_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- The unnormalised `σ_x` eigenvector `(1, 1)`. -/
noncomputable def xPlus : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![1, 1]

/-- `xPlus ≠ 0` (its `0`-th coordinate is `1`); the hypothesis `Projectivization.mk` needs to
form the ray `[xPlus]` in the CSD twin. -/
lemma xPlus_ne_zero : xPlus ≠ 0 := by
  intro h
  have := congrFun (congrArg WithLp.ofLp h) 0
  simp [xPlus] at this

/-- The unnormalised `σ_x` eigenvector `(1, −1)`. -/
noncomputable def xMinus : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![1, -1]

/-- `σ_x (1, 1) = (1, 1)`. -/
lemma sigmaX_xPlus : toEuclideanLin sigmaX xPlus = xPlus := by
  ext i
  fin_cases i <;> simp [xPlus, sigmaX, toLpLin_apply]

/-- `σ_x (1, −1) = −(1, −1)`. -/
lemma sigmaX_xMinus : toEuclideanLin sigmaX xMinus = -xMinus := by
  ext i
  fin_cases i <;> simp [xMinus, sigmaX, toLpLin_apply]

/-- The two `σ_x` eigenvectors are orthogonal. -/
lemma inner_xPlus_xMinus : inner ℂ xPlus xMinus = 0 := by
  simp [xPlus, xMinus, inner_eq_sum, Fin.sum_univ_two]

/-- `⟨(1, 1), σ_z (1, −1)⟩ = 2`: the `σ_x` eigenvectors are coupled by `σ_z`. This is the
`⟨a, L_S a'⟩ ≠ 0` that WAY forbids for an exact conserving record. -/
lemma inner_xPlus_sigmaZ_xMinus : inner ℂ xPlus (toEuclideanLin sigmaZ xMinus) = 2 := by
  norm_num [xPlus, xMinus, sigmaZ, toLpLin_apply, mulVec, dotProduct, Fin.sum_univ_two,
    inner_eq_sum]

/-- `(1, ±1) = σ_x|0⟩ ± |1⟩`-type identity in the form the SWAP witness needs: `⟨0|0⟩ = 1`,
i.e. the SWAP record `φ_± = |0⟩` is *not* repeatable (`⟨φ_+, φ_-⟩ ≠ 0`). -/
lemma inner_ket_zero_self : inner ℂ (ket 0) (ket 0) = 1 := by
  rw [inner_ket]; simp

end TwoQubit

/-! ## Witnesses: CNOT (non-vacuity) and SWAP (sharpness) -/

section Witnesses

open CSD.Empirical.MerminPeres (sigmaX sigmaZ)
open CSD.Empirical.QM.HadamardTest (tensorEuc tensorEuc_apply inner_tensorEuc swapMap
  swapMap_apply swapMap_tensorEuc inner_swapMap inner_eq_sum)
open CSD.LF5 (vnUnitary vnPerm)

/-- The additive charge `σ_z ⊗ 1 + 1 ⊗ σ_x` conserved by CNOT (`L_S = σ_z`, `L_A = σ_x`). -/
noncomputable def chargeZX : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  sigmaZ ⊗ₖ 1 + 1 ⊗ₖ sigmaX

/-- The additive charge `σ_z ⊗ 1 + 1 ⊗ σ_z` conserved by SWAP (`L_S = L_A = σ_z`). -/
noncomputable def chargeZZ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  sigmaZ ⊗ₖ 1 + 1 ⊗ₖ sigmaZ

/-- `chargeZX` is additive on product vectors: `L (a ⊗ c) = σ_z a ⊗ c + a ⊗ σ_x c`. -/
lemma chargeZX_tensorEuc (a c : EuclideanSpace ℂ (Fin 2)) :
    toEuclideanLin chargeZX (tensorEuc a c)
      = tensorEuc (toEuclideanLin sigmaZ a) c + tensorEuc a (toEuclideanLin sigmaX c) := by
  rw [chargeZX, map_add, LinearMap.add_apply, toEuclideanLin_kronecker_tensorEuc,
    toEuclideanLin_kronecker_tensorEuc, toLpLin_one, LinearMap.id_apply, LinearMap.id_apply]

/-- `chargeZZ` is additive on product vectors: `L (a ⊗ c) = σ_z a ⊗ c + a ⊗ σ_z c`. -/
lemma chargeZZ_tensorEuc (a c : EuclideanSpace ℂ (Fin 2)) :
    toEuclideanLin chargeZZ (tensorEuc a c)
      = tensorEuc (toEuclideanLin sigmaZ a) c + tensorEuc a (toEuclideanLin sigmaZ c) := by
  rw [chargeZZ, map_add, LinearMap.add_apply, toEuclideanLin_kronecker_tensorEuc,
    toEuclideanLin_kronecker_tensorEuc, toLpLin_one, LinearMap.id_apply, LinearMap.id_apply]

/-- `(0 : Fin 2) - 1 = 1`, in the form `simp` leaves behind (`-1 = 1` in `Fin 2`). -/
lemma neg_one_fin_two : (-1 : Fin 2) = 1 := by decide

/-- CNOT (`vnUnitary 2`) commutes with `σ_z ⊗ 1 + 1 ⊗ σ_x`: entrywise on `Fin 2 × Fin 2`. -/
lemma chargeZX_mul_cnot : chargeZX * vnUnitary 2 = vnUnitary 2 * chargeZX := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [chargeZX, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, vnUnitary,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, vnPerm,
      kroneckerMap_apply, sigmaZ, sigmaX, Matrix.one_apply, neg_one_fin_two]

/-- CNOT conserves `chargeZX` pointwise: `L (U x) = U (L x)`. -/
lemma chargeZX_cnot (x : EuclideanSpace ℂ (Fin 2 × Fin 2)) :
    toEuclideanLin chargeZX (toEuclideanLin (vnUnitary 2) x)
      = toEuclideanLin (vnUnitary 2) (toEuclideanLin chargeZX x) := by
  simp only [toLpLin_apply, mulVec_mulVec, chargeZX_mul_cnot]

/-- CNOT is an isometry of `EuclideanSpace ℂ (Fin 2 × Fin 2)`. -/
lemma inner_cnot (x y : EuclideanSpace ℂ (Fin 2 × Fin 2)) :
    inner ℂ (toEuclideanLin (vnUnitary 2) x) (toEuclideanLin (vnUnitary 2) y) = inner ℂ x y :=
  Projectivization.inner_toEuclideanLin_unitary ⟨vnUnitary 2, CSD.LF5.vnUnitary_mem_unitaryGroup⟩
    x y

/-- **CNOT records `σ_z` exactly and repeatably**: `U (|j⟩ ⊗ |0⟩) = |j⟩ ⊗ |j⟩`
(`φ j = ξ' j = |j⟩`; `vnUnitary_mulVec_ground`). -/
lemma cnot_record (j : Fin 2) :
    toEuclideanLin (vnUnitary 2) (tensorEuc (ket j) (ket 0)) = tensorEuc (ket j) (ket j) := by
  rw [tensorEuc_ket, tensorEuc_ket, toLpLin_apply, WithLp.ofLp_toLp,
    CSD.LF5.vnUnitary_mulVec_ground]

/-- **The CNOT pointer fails the Yanase condition** against `L_A = σ_x`: `⟨0| σ_x |1⟩ = 1 ≠ 0`.
CNOT therefore satisfies `wigner_araki_yanase` through the repeatability disjunct only. -/
lemma cnot_pointer_not_yanase : inner ℂ (ket 0) (toEuclideanLin sigmaX (ket 1)) = 1 := by
  simp [ket, sigmaX, toLpLin_apply, EuclideanSpace.inner_single_left]

/-- **Non-vacuity of `wigner_araki_yanase`.** With `A = L_S = σ_z` on the computational basis
(`α = (1, −1)`), there are a tensor map, an additive conserved `L` with apparatus part `L_A`, an
isometry `U` conserving `L`, a unit ready state and exact records satisfying every hypothesis of
`wigner_araki_yanase` — and the pointers *fail* the Yanase condition, so it is the repeatability
disjunct that carries the instance. Witness: `tensorEuc`, `chargeZX`, `σ_x`, CNOT, `|0⟩`,
`φ j = ξ' j = |j⟩`. -/
theorem way_hypotheses_satisfiable :
    ∃ (tensor : EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2) →
        EuclideanSpace ℂ (Fin 2 × Fin 2))
      (L : EuclideanSpace ℂ (Fin 2 × Fin 2) → EuclideanSpace ℂ (Fin 2 × Fin 2))
      (LA : EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2))
      (U : EuclideanSpace ℂ (Fin 2 × Fin 2) → EuclideanSpace ℂ (Fin 2 × Fin 2))
      (ξ : EuclideanSpace ℂ (Fin 2)) (φ ξ' : Fin 2 → EuclideanSpace ℂ (Fin 2)),
      (∀ i, toEuclideanLin sigmaZ (EuclideanSpace.basisFun (Fin 2) ℂ i)
        = (![1, -1] i : ℂ) • EuclideanSpace.basisFun (Fin 2) ℂ i) ∧
      (∀ (a c : EuclideanSpace ℂ (Fin 2)) (b d : EuclideanSpace ℂ (Fin 2)),
        inner ℂ (tensor a b) (tensor c d) = inner ℂ a c * inner ℂ b d) ∧
      (∀ a c, L (tensor a c) = tensor (toEuclideanLin sigmaZ a) c + tensor a (LA c)) ∧
      (∀ x y, inner ℂ (U x) (U y) = inner ℂ x y) ∧
      (∀ x, L (U x) = U (L x)) ∧
      ‖ξ‖ = 1 ∧
      (∀ i, U (tensor (EuclideanSpace.basisFun (Fin 2) ℂ i) ξ) = tensor (φ i) (ξ' i)) ∧
      (∀ i j, (![1, -1] i : ℂ) ≠ ![1, -1] j → inner ℂ (ξ' i) (ξ' j) = 0) ∧
      (∀ i j, (![1, -1] i : ℂ) ≠ ![1, -1] j →
        inner ℂ (ξ' i) (LA (ξ' j)) = 0 ∨ inner ℂ (φ i) (φ j) = 0) ∧
      inner ℂ (ξ' 0) (LA (ξ' 1)) ≠ 0 := by
  have hne : ∀ i j : Fin 2, (![1, -1] i : ℂ) ≠ ![1, -1] j → i ≠ j :=
    fun i j h hij => h (by rw [hij])
  refine ⟨tensorEuc, toEuclideanLin chargeZX, toEuclideanLin sigmaX, toEuclideanLin (vnUnitary 2),
    ket 0, ket, ket, ?_, fun a c b d => inner_tensorEuc a b c d, chargeZX_tensorEuc, inner_cnot,
    chargeZX_cnot,
    norm_ket 0, ?_, ?_, ?_, ?_⟩
  · intro i; rw [basisFun_eq_ket]; exact sigmaZ_ket i
  · intro i; rw [basisFun_eq_ket]; exact cnot_record i
  · intro i j h; rw [inner_ket, if_neg (hne i j h)]
  · intro i j h; exact Or.inr (by rw [inner_ket, if_neg (hne i j h)])
  · rw [cnot_pointer_not_yanase]; exact one_ne_zero

/-- SWAP conserves `chargeZZ` pointwise: `L (swap x) = swap (L x)`. -/
lemma chargeZZ_swapMap (x : EuclideanSpace ℂ (Fin 2 × Fin 2)) :
    toEuclideanLin chargeZZ (swapMap x) = swapMap (toEuclideanLin chargeZZ x) := by
  ext ⟨i, j⟩
  simp only [chargeZZ, toLpLin_apply, WithLp.ofLp_toLp, swapMap_apply, mulVec, dotProduct,
    Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.add_apply, kroneckerMap_apply]
  fin_cases i <;> fin_cases j <;> simp [sigmaZ, Matrix.one_apply]

/-- **Sharpness: the side condition cannot be dropped.** There are data satisfying every
hypothesis of `arakiYanase_offDiag_eq_zero` *except* `hside` — an isometry conserving an additive
`σ_z ⊗ 1 + 1 ⊗ L_A`, a unit ready state, orthogonal system vectors recorded exactly with
orthogonal pointers — for which `⟨a, L_S a'⟩ ≠ 0`; and there both disjuncts of `hside` fail
(the pointer violates Yanase and the record is not repeatable). Witness: SWAP with
`L_A = σ_z`, ready state `|0⟩`, `a = (1, 1)`, `a' = (1, −1)`, records `|0⟩ ⊗ (1, ±1)`
(`swapMap_tensorEuc`), so `φ_± = |0⟩` and `ξ_± = (1, ±1)`. -/
theorem swap_exact_record_not_commute :
    ∃ (U L : EuclideanSpace ℂ (Fin 2 × Fin 2) → EuclideanSpace ℂ (Fin 2 × Fin 2))
      (LA : EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2))
      (ξ a a' φ φ' ξ₁ ξ₂ : EuclideanSpace ℂ (Fin 2)),
      (∀ x y, inner ℂ (U x) (U y) = inner ℂ x y) ∧
      (∀ x, L (U x) = U (L x)) ∧
      (∀ b c, L (tensorEuc b c) = tensorEuc (toEuclideanLin sigmaZ b) c + tensorEuc b (LA c)) ∧
      ‖ξ‖ = 1 ∧ inner ℂ a a' = 0 ∧
      U (tensorEuc a ξ) = tensorEuc φ ξ₁ ∧ U (tensorEuc a' ξ) = tensorEuc φ' ξ₂ ∧
      inner ℂ ξ₁ ξ₂ = 0 ∧
      inner ℂ a (toEuclideanLin sigmaZ a') ≠ 0 ∧
      inner ℂ ξ₁ (LA ξ₂) ≠ 0 ∧ inner ℂ φ φ' ≠ 0 := by
  refine ⟨swapMap, toEuclideanLin chargeZZ, toEuclideanLin sigmaZ, ket 0, xPlus, xMinus,
    ket 0, ket 0, xPlus, xMinus, inner_swapMap, chargeZZ_swapMap, chargeZZ_tensorEuc, norm_ket 0,
    inner_xPlus_xMinus, swapMap_tensorEuc _ _, swapMap_tensorEuc _ _, inner_xPlus_xMinus, ?_, ?_,
    ?_⟩
  · rw [inner_xPlus_sigmaZ_xMinus]; exact two_ne_zero
  · rw [inner_xPlus_sigmaZ_xMinus]; exact two_ne_zero
  · rw [inner_ket_zero_self]; exact one_ne_zero

/-- **The no-go in use: no exact conserving record of `σ_x` with a well-behaved pointer.**
For *any* apparatus part `L_A`, any isometry `U` conserving the additive `σ_z ⊗ 1 + 1 ⊗ L_A`
that records the `σ_x` eigenvectors `(1, ±1)` exactly from a unit ready state with orthogonal
pointers must have a pointer violating the Yanase condition *and* a non-repeatable record.
(`σ_x` has the eigenvectors of `rotatedProj`, `Empirical/CSD/PointerCommutation.lean`;
`sigmaX_xPlus`, `sigmaX_xMinus`.) The `2 ≠ 0` of `inner_xPlus_sigmaZ_xMinus` against
`arakiYanase_offDiag_eq_zero`. -/
theorem sigmaX_no_exact_conserving_record
    (L : EuclideanSpace ℂ (Fin 2 × Fin 2) → EuclideanSpace ℂ (Fin 2 × Fin 2))
    (LA : EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2))
    (h_add : ∀ b c, L (tensorEuc b c) = tensorEuc (toEuclideanLin sigmaZ b) c + tensorEuc b (LA c))
    (U : EuclideanSpace ℂ (Fin 2 × Fin 2) → EuclideanSpace ℂ (Fin 2 × Fin 2))
    (hU : ∀ x y, inner ℂ (U x) (U y) = inner ℂ x y) (hUL : ∀ x, L (U x) = U (L x))
    (ξ : EuclideanSpace ℂ (Fin 2)) (hξ : ‖ξ‖ = 1) {φ φ' ξ₁ ξ₂ : EuclideanSpace ℂ (Fin 2)}
    (hrec : U (tensorEuc xPlus ξ) = tensorEuc φ ξ₁)
    (hrec' : U (tensorEuc xMinus ξ) = tensorEuc φ' ξ₂)
    (hξ₁₂ : inner ℂ ξ₁ ξ₂ = 0) :
    inner ℂ ξ₁ (LA ξ₂) ≠ 0 ∧ inner ℂ φ φ' ≠ 0 := by
  have key : ¬ (inner ℂ ξ₁ (LA ξ₂) = 0 ∨ inner ℂ φ φ' = 0) := fun hside => by
    have h := arakiYanase_offDiag_eq_zero tensorEuc (fun a c b d => inner_tensorEuc a b c d) L
      (toEuclideanLin sigmaZ) LA h_add U hU hUL ξ hξ inner_xPlus_xMinus hrec hrec' hξ₁₂ hside
    rw [inner_xPlus_sigmaZ_xMinus] at h
    exact two_ne_zero h
  exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩

end Witnesses

end WignerArakiYanase
end QM
end Empirical
end CSD
