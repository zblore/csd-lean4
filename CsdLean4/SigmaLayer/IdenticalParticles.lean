/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.Symmetrization
public import CsdLean4.SigmaLayer.TensorSolved
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Trace

/-!
# SigmaLayer/IdenticalParticles: the boson and fermion sectors of two identical particles

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)) — the identical-particle pillar.
BACKLOG #206, the first brick of `future-work.md` IP-1.

`SigmaLayer/Symmetrization.lean` (SL-T8) built the exchange operator `swap` on
`TwoParticle N = EuclideanSpace ℂ (Fin N × Fin N)`, the projectors `½(1 ± swap)` and the `±1`
dichotomy. This file turns that into the two-particle sectors and proves what identical particles
do in them: the sectors' sizes are occupation counts, fermions exclude, bosons bunch, and the
sector of a pair of identical particles is a superselection label that no exchange-symmetric
dynamics or observable can change or see.

## What is proved

* `bosonSector N` and `fermionSector N` — the `+1` and `−1` eigenspaces of exchange
  (`mem_bosonSector_iff_apply`: `x (j, i) = x (i, j)`; `mem_fermionSector_iff_apply`:
  `x (j, i) = -x (i, j)`); ★ `isCompl_bosonSector_fermionSector` and ★
  `fermionSector_eq_orthogonal` (the fermions are exactly the orthogonal complement of the bosons);
* ★ `trace_swap` (the trace of exchange is `N`), ★★ `finrank_bosonSector` (`(N + 1).choose 2`) and
  ★★ `finrank_fermionSector` (`N.choose 2`), by the trace of the projectors; ★★
  `finrank_bosonSector_eq_card` and ★★ `finrank_fermionSector_eq_card` — **one dimension per
  occupation configuration**: two bosons are counted by occupations `P : Fin N → ℕ` with
  `∑ P = 2`, two fermions by the set of two occupied modes;
* ★★ `apply_diag_eq_zero_of_mem_fermionSector` (**Pauli exclusion**, every fermionic state, not
  only a product: the amplitude for both particles in one mode is `0`), `wedge` (the
  antisymmetrised product `v ⊗ w − w ⊗ v`) and ★★ `wedge_eq_zero_iff` (**the antisymmetrised
  product vanishes exactly when the two single-particle states are linearly dependent** — two
  fermions cannot share a state, in any basis), ★ `norm_sq_wedge` and ★ `norm_sq_symState`
  (`2 (‖v‖²‖w‖² ∓ |⟨v, w⟩|²)`, the Cauchy–Schwarz gap);
* ★★ `bosonic_enhancement` — for orthonormal `v`, `w` the probability that both bosons are found in
  mode `i` is **twice** that for distinguishable particles, and for fermions it is `0`
  (`fermionic_same_mode`);
* on the composite arena of `SigmaLayer/TensorSolved.lean`: `exchangeMatrix N`, the permutation
  matrix of `Equiv.prodComm` (`toEuclideanLin_exchangeMatrix`), with ★
  `exchangeMatrix_mul_kronecker` (`P (A ⊗ B) = (B ⊗ A) P`) and ★ `exchangeMatrix_mul_aliceOp`
  (exchange carries Alice's local algebra onto Bob's); `IsExchangeSymmetric` (the operators of
  two *identical* particles), with ★ `isExchangeSymmetric_kronecker_self`,
  ★ `isExchangeSymmetric_oneBody` and ★ `IsExchangeSymmetric.exp_smul`;
* ★★ `IsExchangeSymmetric.mem_bosonSector` / `mem_fermionSector` (**the sectors are invariant**:
  every exchange-symmetric operator, so every evolution `exp (t • H)` with `H` exchange-symmetric,
  maps each sector into itself), ★★ `IsExchangeSymmetric.inner_eq_zero` (**superselection**: no
  exchange-symmetric operator connects a boson to a fermion) and ★★
  `IsExchangeSymmetric.inner_add_add` (no interference between the sectors);
* ★★★ `identical_particles` — the capstone.

## Honest scope

⚠️ **The symmetrisation postulate is shown consistent, not derived.** What is proved is that the
sector of two identical particles is conserved by every exchange-symmetric dynamics and invisible to
every exchange-symmetric observable — so restricting to one sector is a superselection rule the
theory can carry. That nature uses only the two one-dimensional representations of the exchange,
and which one for which particle (spin–statistics), is not proved here; at finite dimension without
relativity it cannot be, and it stays the posit it is in textbook QM.

⚠️ **Two particles only.** The `n`-particle sectors (the symmetric and alternating powers of
`ℂᴺ`, with dimensions `(N + n − 1).choose n` and `N.choose n`), second quantisation on the
occupation lattice and the CCR/CAR algebras are the pillar's remainder: BACKLOG ~~#214~~
(`SigmaLayer/ManyIdenticalParticles.lean`), ~~#215~~ (`SigmaLayer/FermionFock.lean`,
`SigmaLayer/BosonFock.lean`), ~~#216~~ (`SigmaLayer/ExchangeStatistics.lean`).

The Hong–Ou–Mandel dip, the experiment that bosonic enhancement predicts, is already in the corpus
for two modes (`Empirical/QM/HongOuMandel.lean`, `hom_exchange_trichotomy`).

References: [`future-work.md`](../../specs/future-work.md) IP-1, SL-T8;
`SigmaLayer/Symmetrization.lean` (`swap`, `symProj`, `antisymProj`, `tprod`);
`SigmaLayer/TensorSolved.lean` (`composite_is_tensor_product`); `Empirical/QM/NoCommunication.lean`
(`aliceOp`, `bobOp`); `Empirical/QM/HongOuMandel.lean`; Mathlib `Sym.equivNatSumOfFintype`,
`Sym.card_sym_eq_choose`, `Fintype.card_finset_len`, `LinearMap.IsProj.trace`;
`specs/BACKLOG.md` #206.
-/

@[expose] public section

open Module Matrix NormedSpace
open scoped InnerProductSpace Kronecker
open CSD.Empirical.QM

namespace CSD.SigmaLayer

variable {N : ℕ}

/-! ### The two sectors -/

/-- **The bosonic sector**: the two-particle states that exchange leaves fixed. -/
noncomputable def bosonSector (N : ℕ) : Submodule ℂ (TwoParticle N) :=
  Module.End.eigenspace (swap N) 1

/-- **The fermionic sector**: the two-particle states that exchange negates. -/
noncomputable def fermionSector (N : ℕ) : Submodule ℂ (TwoParticle N) :=
  Module.End.eigenspace (swap N) (-1)

theorem mem_bosonSector {x : TwoParticle N} : x ∈ bosonSector N ↔ swap N x = x := by
  rw [bosonSector, Module.End.mem_eigenspace_iff, one_smul]

theorem mem_fermionSector {x : TwoParticle N} : x ∈ fermionSector N ↔ swap N x = -x := by
  rw [fermionSector, Module.End.mem_eigenspace_iff, neg_one_smul]

theorem mem_bosonSector_iff_apply {x : TwoParticle N} :
    x ∈ bosonSector N ↔ ∀ i j, x (j, i) = x (i, j) := by
  rw [mem_bosonSector]
  constructor
  · intro h i j
    have := congrArg (fun y : TwoParticle N => y (i, j)) h
    simpa [swap_apply] using this
  · intro h
    ext p
    rw [swap_apply]
    exact h p.1 p.2

theorem mem_fermionSector_iff_apply {x : TwoParticle N} :
    x ∈ fermionSector N ↔ ∀ i j, x (j, i) = -x (i, j) := by
  rw [mem_fermionSector]
  constructor
  · intro h i j
    have := congrArg (fun y : TwoParticle N => y (i, j)) h
    simpa [swap_apply] using this
  · intro h
    ext p
    rw [swap_apply, PiLp.neg_apply]
    exact h p.1 p.2

theorem symProj_mem_bosonSector (x : TwoParticle N) : symProj N x ∈ bosonSector N := by
  rw [mem_bosonSector, swap_eq_self_iff, symProj_idem]

theorem antisymProj_mem_fermionSector (x : TwoParticle N) :
    antisymProj N x ∈ fermionSector N := by
  rw [mem_fermionSector, swap_eq_neg_iff, antisymProj_idem]

/-- `½(1 + swap)` is the projection onto the bosonic sector. -/
theorem isProj_symProj : LinearMap.IsProj (bosonSector N) (symProj N) :=
  ⟨symProj_mem_bosonSector, fun x hx => (swap_eq_self_iff x).1 (mem_bosonSector.1 hx)⟩

/-- `½(1 − swap)` is the projection onto the fermionic sector. -/
theorem isProj_antisymProj : LinearMap.IsProj (fermionSector N) (antisymProj N) :=
  ⟨antisymProj_mem_fermionSector, fun x hx => (swap_eq_neg_iff x).1 (mem_fermionSector.1 hx)⟩

/-- A boson and a fermion are orthogonal. -/
theorem inner_eq_zero_of_mem_bosonSector_of_mem_fermionSector {x y : TwoParticle N}
    (hx : x ∈ bosonSector N) (hy : y ∈ fermionSector N) : ⟪x, y⟫_ℂ = 0 := by
  have h := swap_isSymmetric (N := N) x y
  rw [mem_bosonSector.1 hx, mem_fermionSector.1 hy, inner_neg_right] at h
  have h2 : (2 : ℂ) * ⟪x, y⟫_ℂ = 0 := by linear_combination h
  simpa using h2

/-- **The two sectors are complementary**: every two-particle state is a boson plus a fermion, in one
way only. -/
theorem isCompl_bosonSector_fermionSector : IsCompl (bosonSector N) (fermionSector N) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hy
    exact eq_zero_of_swap_self_and_neg x (mem_bosonSector.1 hx) (mem_fermionSector.1 hy)
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    rw [← symProj_add_antisymProj x]
    exact Submodule.add_mem_sup (symProj_mem_bosonSector x) (antisymProj_mem_fermionSector x)

/-- **The fermions are exactly the orthogonal complement of the bosons.** -/
theorem fermionSector_eq_orthogonal : fermionSector N = (bosonSector N)ᗮ := by
  apply le_antisymm
  · intro y hy
    exact (Submodule.mem_orthogonal _ _).2 fun x hx =>
      inner_eq_zero_of_mem_bosonSector_of_mem_fermionSector hx hy
  · intro y hy
    have hs := (Submodule.mem_orthogonal _ _).1 hy _ (symProj_mem_bosonSector y)
    have h1 : ⟪symProj N y, symProj N y⟫_ℂ = 0 := by
      rw [← symProj_isSymmetric (symProj N y) y, symProj_idem]
      exact hs
    have h2 := symProj_add_antisymProj y
    rw [inner_self_eq_zero.1 h1, zero_add] at h2
    rw [← h2]
    exact antisymProj_mem_fermionSector y

/-! ### The sizes of the sectors are occupation counts -/

/-- **The trace of exchange is `N`**: exchange fixes exactly the `N` basis states with both particles
in one mode. -/
theorem trace_swap : LinearMap.trace ℂ (TwoParticle N) (swap N) = N := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (Fin N × Fin N) ℂ).toBasis,
    Matrix.trace]
  simp [LinearMap.toMatrix_apply, swap_apply, Prod.ext_iff]
  refine (congrArg Finset.card ?_).trans
    ((Finset.diag_card (Finset.univ : Finset (Fin N))).trans (Finset.card_fin N))
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_diag]
  exact ⟨fun h => h.2, fun h => ⟨h.symm, h⟩⟩

theorem two_mul_finrank_bosonSector : 2 * finrank ℂ (bosonSector N) = N * (N + 1) := by
  have h := (isProj_symProj (N := N)).trace
  rw [symProj, map_smul, map_add, LinearMap.trace_id, trace_swap, finrank_euclideanSpace,
    Fintype.card_prod, Fintype.card_fin, smul_eq_mul] at h
  have h2 : ((2 * finrank ℂ (bosonSector N) : ℕ) : ℂ) = ((N * (N + 1) : ℕ) : ℂ) := by
    push_cast at h ⊢
    rw [← h]
    ring
  exact_mod_cast h2

theorem two_mul_finrank_fermionSector : 2 * finrank ℂ (fermionSector N) + N = N * N := by
  have h := (isProj_antisymProj (N := N)).trace
  rw [antisymProj, map_smul, map_sub, LinearMap.trace_id, trace_swap, finrank_euclideanSpace,
    Fintype.card_prod, Fintype.card_fin, smul_eq_mul] at h
  have h2 : ((2 * finrank ℂ (fermionSector N) + N : ℕ) : ℂ) = ((N * N : ℕ) : ℂ) := by
    push_cast at h ⊢
    rw [← h]
    ring
  exact_mod_cast h2

/-- **Two bosons in `N` modes span `(N + 1).choose 2 = N(N + 1)/2` dimensions.** -/
theorem finrank_bosonSector : finrank ℂ (bosonSector N) = (N + 1).choose 2 := by
  have h := two_mul_finrank_bosonSector (N := N)
  rw [Nat.choose_two_right, Nat.add_sub_cancel]
  ring_nf
  ring_nf at h
  omega

/-- **Two fermions in `N` modes span `N.choose 2 = N(N − 1)/2` dimensions.** -/
theorem finrank_fermionSector : finrank ℂ (fermionSector N) = N.choose 2 := by
  have h := two_mul_finrank_fermionSector (N := N)
  rw [Nat.choose_two_right, Nat.mul_sub_one]
  omega

/-- **One bosonic dimension per occupation configuration.** The bosonic sector has exactly as many
dimensions as there are ways to put two quanta into `N` modes, `P : Fin N → ℕ` with `∑ P = 2`. -/
theorem finrank_bosonSector_eq_card :
    finrank ℂ (bosonSector N) = Nat.card {P : Fin N → ℕ // ∑ i, P i = 2} := by
  rw [finrank_bosonSector, ← Nat.card_congr (Sym.equivNatSumOfFintype (Fin N) 2),
    Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, Fintype.card_fin,
    show N + 2 - 1 = N + 1 by omega]

/-- **One fermionic dimension per pair of occupied modes.** The fermionic sector has exactly as many
dimensions as there are sets of two occupied modes (occupations `0` or `1`, total `2`). -/
theorem finrank_fermionSector_eq_card :
    finrank ℂ (fermionSector N) = Fintype.card {s : Finset (Fin N) // s.card = 2} := by
  rw [finrank_fermionSector, Fintype.card_finset_len, Fintype.card_fin]

/-! ### Pauli exclusion -/

/-- **Pauli exclusion.** In every fermionic state, the amplitude for both particles in the same mode
is zero. -/
theorem apply_diag_eq_zero_of_mem_fermionSector {x : TwoParticle N} (hx : x ∈ fermionSector N)
    (i : Fin N) : x (i, i) = 0 := by
  have h := mem_fermionSector_iff_apply.1 hx i i
  have h2 : (2 : ℂ) * x (i, i) = 0 := by linear_combination h
  simpa using h2

/-- **The antisymmetrised product** `v ⊗ w − w ⊗ v` of two single-particle states. -/
noncomputable def wedge (v w : EuclideanSpace ℂ (Fin N)) : TwoParticle N :=
  tprod v w - tprod w v

/-- **The symmetrised product** `v ⊗ w + w ⊗ v` of two single-particle states. -/
noncomputable def symState (v w : EuclideanSpace ℂ (Fin N)) : TwoParticle N :=
  tprod v w + tprod w v

theorem wedge_apply (v w : EuclideanSpace ℂ (Fin N)) (p : Fin N × Fin N) :
    wedge v w p = v p.1 * w p.2 - w p.1 * v p.2 := by
  simp [wedge]

theorem symState_apply (v w : EuclideanSpace ℂ (Fin N)) (p : Fin N × Fin N) :
    symState v w p = v p.1 * w p.2 + w p.1 * v p.2 := by
  simp [symState]

theorem wedge_mem_fermionSector (v w : EuclideanSpace ℂ (Fin N)) :
    wedge v w ∈ fermionSector N := by
  rw [mem_fermionSector, wedge, map_sub, swap_tprod, swap_tprod, neg_sub]

theorem symState_mem_bosonSector (v w : EuclideanSpace ℂ (Fin N)) :
    symState v w ∈ bosonSector N := by
  rw [mem_bosonSector, symState, map_add, swap_tprod, swap_tprod, add_comm]

/-- **Two fermions cannot share a state, in any basis.** The antisymmetrised product of two
single-particle states vanishes exactly when they are linearly dependent. -/
theorem wedge_eq_zero_iff (v w : EuclideanSpace ℂ (Fin N)) :
    wedge v w = 0 ↔ ¬ LinearIndependent ℂ ![v, w] := by
  rw [LinearIndependent.pair_iff]
  constructor
  · intro h hli
    have hvw : ∀ i j, v i * w j = w i * v j := fun i j => by
      have := congrArg (fun y : TwoParticle N => y (i, j)) h
      simpa [wedge_apply, sub_eq_zero] using this
    by_cases hv : v = 0
    · have := hli 1 0 (by simp [hv])
      exact one_ne_zero this.1
    · obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra hc
        refine hv ?_
        ext j
        by_contra hj
        exact hc ⟨j, hj⟩
      have := hli (w i) (-(v i)) (by
        ext j
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply]
        linear_combination -(hvw i j))
      exact hi (neg_eq_zero.1 this.2)
  · intro h
    simp only [not_forall] at h
    obtain ⟨s, t, hst, hne⟩ := h
    have hk : ∀ k, s * v k + t * w k = 0 := fun k => by
      have := congrArg (fun y : EuclideanSpace ℂ (Fin N) => y k) hst
      simpa using this
    ext p
    rw [wedge_apply, PiLp.zero_apply]
    have h1 := hk p.1
    have h2 := hk p.2
    rcases not_and_or.1 hne with hs | ht
    · refine mul_left_cancel₀ hs ?_
      rw [mul_zero]
      linear_combination w p.2 * h1 - w p.1 * h2
    · refine mul_left_cancel₀ ht ?_
      rw [mul_zero]
      linear_combination v p.1 * h2 - v p.2 * h1

theorem wedge_self (v : EuclideanSpace ℂ (Fin N)) : wedge v v = 0 :=
  sub_self _

/-! ### Bosonic enhancement -/

theorem inner_tprod (a b c d : EuclideanSpace ℂ (Fin N)) :
    ⟪tprod a b, tprod c d⟫_ℂ = ⟪a, c⟫_ℂ * ⟪b, d⟫_ℂ := by
  simp only [PiLp.inner_apply, tprod_apply, RCLike.inner_apply, Fintype.sum_prod_type, map_mul,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem norm_tprod (v w : EuclideanSpace ℂ (Fin N)) : ‖tprod v w‖ = ‖v‖ * ‖w‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    ← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _), Finset.sum_mul_sum,
    Fintype.sum_prod_type]
  simp_rw [tprod_apply, norm_mul, mul_pow]

/-- The squared norm of a sum of two product states, through `⟨v, w⟩⟨w, v⟩ = |⟨v, w⟩|²`. -/
theorem re_inner_tprod_swap (v w : EuclideanSpace ℂ (Fin N)) :
    RCLike.re ⟪tprod v w, tprod w v⟫_ℂ = ‖⟪v, w⟫_ℂ‖ ^ 2 := by
  rw [inner_tprod, ← inner_conj_symm w v, ← inner_conj_symm v w, RCLike.conj_conj,
    mul_comm, RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_re, RCLike.norm_conj]

/-- `‖v ⊗ w + w ⊗ v‖² = 2 (‖v‖²‖w‖² + |⟨v, w⟩|²)`. -/
theorem norm_sq_symState (v w : EuclideanSpace ℂ (Fin N)) :
    ‖symState v w‖ ^ 2 = 2 * (‖v‖ ^ 2 * ‖w‖ ^ 2 + ‖⟪v, w⟫_ℂ‖ ^ 2) := by
  rw [symState, @norm_add_sq ℂ, re_inner_tprod_swap, norm_tprod, norm_tprod]
  ring

/-- `‖v ⊗ w − w ⊗ v‖² = 2 (‖v‖²‖w‖² − |⟨v, w⟩|²)` — twice the Cauchy–Schwarz gap. -/
theorem norm_sq_wedge (v w : EuclideanSpace ℂ (Fin N)) :
    ‖wedge v w‖ ^ 2 = 2 * (‖v‖ ^ 2 * ‖w‖ ^ 2 - ‖⟪v, w⟫_ℂ‖ ^ 2) := by
  rw [wedge, @norm_sub_sq ℂ, re_inner_tprod_swap, norm_tprod, norm_tprod]
  ring

/-- **Bosonic enhancement.** For orthonormal single-particle states, the probability that two bosons
in the symmetrised state are both found in mode `i` is twice the probability for two
distinguishable particles in `v ⊗ w`. -/
theorem bosonic_enhancement {v w : EuclideanSpace ℂ (Fin N)} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hvw : ⟪v, w⟫_ℂ = 0) (i : Fin N) :
    ‖symState v w (i, i)‖ ^ 2 / ‖symState v w‖ ^ 2
      = 2 * (‖tprod v w (i, i)‖ ^ 2 / ‖tprod v w‖ ^ 2) := by
  rw [norm_sq_symState, norm_tprod, hv, hw, hvw, symState_apply, tprod_apply]
  simp only [norm_zero]
  rw [show v (i, i).1 * w (i, i).2 + w (i, i).1 * v (i, i).2 = 2 * (v i * w i) by
    simp only; ring, norm_mul, Complex.norm_two]
  ring

/-- **Fermions never share a mode**: the same-mode probability of an antisymmetrised pair is `0`. -/
theorem fermionic_same_mode (v w : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    ‖wedge v w (i, i)‖ ^ 2 = 0 := by
  rw [apply_diag_eq_zero_of_mem_fermionSector (wedge_mem_fermionSector v w), norm_zero]
  norm_num

/-! ### The sectors on the composite arena -/

/-- **Exchange as a matrix** on the composite arena `Fin N × Fin N` of
`SigmaLayer/TensorSolved.lean`: the permutation matrix of `Equiv.prodComm`. -/
noncomputable def exchangeMatrix (N : ℕ) : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ :=
  (Equiv.prodComm (Fin N) (Fin N)).toPEquiv.toMatrix

theorem toEuclideanLin_exchangeMatrix : toEuclideanLin (exchangeMatrix N) = swap N := by
  ext x p
  simp [exchangeMatrix, Matrix.toLpLin_apply, PEquiv.toMatrix_toPEquiv_mulVec, swap_apply]
  rfl

/-- **Exchange intertwines the two factors**: `P (A ⊗ B) = (B ⊗ A) P`. -/
theorem exchangeMatrix_mul_kronecker (A B : Matrix (Fin N) (Fin N) ℂ) :
    exchangeMatrix N * (A ⊗ₖ B) = (B ⊗ₖ A) * exchangeMatrix N := by
  rw [exchangeMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext p q
  simp [Matrix.kroneckerMap_apply, mul_comm]

/-- **Exchange carries Alice's local algebra onto Bob's.** -/
theorem exchangeMatrix_mul_aliceOp (A : Matrix (Fin N) (Fin N) ℂ) :
    exchangeMatrix N * NoCommunication.aliceOp A = NoCommunication.bobOp A * exchangeMatrix N :=
  exchangeMatrix_mul_kronecker A 1

/-- **An operator of two identical particles**: one that commutes with exchange. -/
def IsExchangeSymmetric (M : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) : Prop :=
  Commute (exchangeMatrix N) M

/-- The same operation applied to both particles is exchange-symmetric. -/
theorem isExchangeSymmetric_kronecker_self (U : Matrix (Fin N) (Fin N) ℂ) :
    IsExchangeSymmetric (U ⊗ₖ U) :=
  exchangeMatrix_mul_kronecker U U

/-- A one-body operator `h ⊗ 1 + 1 ⊗ h` is exchange-symmetric. -/
theorem isExchangeSymmetric_oneBody (h : Matrix (Fin N) (Fin N) ℂ) :
    IsExchangeSymmetric (NoCommunication.aliceOp h + NoCommunication.bobOp h) := by
  have hb : exchangeMatrix N * NoCommunication.bobOp h
      = NoCommunication.aliceOp h * exchangeMatrix N :=
    exchangeMatrix_mul_kronecker 1 h
  show exchangeMatrix N * _ = _ * exchangeMatrix N
  rw [mul_add, add_mul, exchangeMatrix_mul_aliceOp, hb, add_comm]

/-- The evolution generated by an exchange-symmetric operator is exchange-symmetric. -/
theorem IsExchangeSymmetric.exp_smul {H : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ}
    (hH : IsExchangeSymmetric H) (t : ℂ) : IsExchangeSymmetric (exp (t • H)) :=
  (Commute.smul_right hH t).exp_right

theorem IsExchangeSymmetric.swap_toEuclideanLin {M : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ}
    (hM : IsExchangeSymmetric M) (x : TwoParticle N) :
    swap N (toEuclideanLin M x) = toEuclideanLin M (swap N x) := by
  have := congrArg (fun A => toEuclideanLin A x) hM.eq
  simpa [Matrix.toLpLin_mul_same, toEuclideanLin_exchangeMatrix] using this

/-- **The bosonic sector is invariant** under every exchange-symmetric operator. -/
theorem IsExchangeSymmetric.mem_bosonSector {M : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ}
    (hM : IsExchangeSymmetric M) {x : TwoParticle N} (hx : x ∈ bosonSector N) :
    toEuclideanLin M x ∈ bosonSector N := by
  rw [SigmaLayer.mem_bosonSector] at hx ⊢
  rw [hM.swap_toEuclideanLin, hx]

/-- **The fermionic sector is invariant** under every exchange-symmetric operator. -/
theorem IsExchangeSymmetric.mem_fermionSector {M : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ}
    (hM : IsExchangeSymmetric M) {x : TwoParticle N} (hx : x ∈ fermionSector N) :
    toEuclideanLin M x ∈ fermionSector N := by
  rw [SigmaLayer.mem_fermionSector] at hx ⊢
  rw [hM.swap_toEuclideanLin, hx, map_neg]

/-- **Superselection.** No exchange-symmetric operator connects a boson to a fermion. -/
theorem IsExchangeSymmetric.inner_eq_zero {M : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ}
    (hM : IsExchangeSymmetric M) {x y : TwoParticle N} (hx : x ∈ bosonSector N)
    (hy : y ∈ fermionSector N) : ⟪x, toEuclideanLin M y⟫_ℂ = 0 :=
  inner_eq_zero_of_mem_bosonSector_of_mem_fermionSector hx (hM.mem_fermionSector hy)

/-- The same, with the fermion on the left. -/
theorem IsExchangeSymmetric.inner_eq_zero' {M : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ}
    (hM : IsExchangeSymmetric M) {x y : TwoParticle N} (hx : x ∈ bosonSector N)
    (hy : y ∈ fermionSector N) : ⟪y, toEuclideanLin M x⟫_ℂ = 0 := by
  rw [← inner_conj_symm, inner_eq_zero_of_mem_bosonSector_of_mem_fermionSector
    (hM.mem_bosonSector hx) hy, map_zero]

/-- **No interference between the sectors.** For an exchange-symmetric observable, a superposition
of a boson and a fermion has the expectation of the mixture. -/
theorem IsExchangeSymmetric.inner_add_add {M : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ}
    (hM : IsExchangeSymmetric M) {x y : TwoParticle N} (hx : x ∈ bosonSector N)
    (hy : y ∈ fermionSector N) :
    ⟪x + y, toEuclideanLin M (x + y)⟫_ℂ
      = ⟪x, toEuclideanLin M x⟫_ℂ + ⟪y, toEuclideanLin M y⟫_ℂ := by
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, hM.inner_eq_zero hx hy,
    hM.inner_eq_zero' hx hy]
  ring

/-! ### The capstone -/

/-- **Identical particles at `n = 2`.**

1. the bosonic and fermionic sectors are complementary, the fermions the orthogonal complement of
   the bosons;
2. their dimensions are the occupation counts: two quanta in `N` modes for bosons, two occupied
   modes for fermions;
3. Pauli exclusion: every fermionic state has zero amplitude for both particles in one mode;
4. the antisymmetrised product of two states vanishes exactly when they are linearly dependent;
5. bosonic enhancement: for orthonormal states the same-mode probability is twice the
   distinguishable one;
6. every evolution generated by an exchange-symmetric operator keeps each sector;
7. superselection: no exchange-symmetric operator connects a boson to a fermion. -/
theorem identical_particles :
    (IsCompl (bosonSector N) (fermionSector N) ∧ fermionSector N = (bosonSector N)ᗮ)
    ∧ (finrank ℂ (bosonSector N) = Nat.card {P : Fin N → ℕ // ∑ i, P i = 2}
        ∧ finrank ℂ (fermionSector N) = Fintype.card {s : Finset (Fin N) // s.card = 2})
    ∧ (∀ x ∈ fermionSector N, ∀ i, x (i, i) = 0)
    ∧ (∀ v w : EuclideanSpace ℂ (Fin N), wedge v w = 0 ↔ ¬ LinearIndependent ℂ ![v, w])
    ∧ (∀ v w : EuclideanSpace ℂ (Fin N), ‖v‖ = 1 → ‖w‖ = 1 → ⟪v, w⟫_ℂ = 0 → ∀ i,
        ‖symState v w (i, i)‖ ^ 2 / ‖symState v w‖ ^ 2
          = 2 * (‖tprod v w (i, i)‖ ^ 2 / ‖tprod v w‖ ^ 2))
    ∧ (∀ H : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ, IsExchangeSymmetric H → ∀ t : ℂ,
        (∀ x ∈ bosonSector N, toEuclideanLin (exp (t • H)) x ∈ bosonSector N)
        ∧ ∀ x ∈ fermionSector N, toEuclideanLin (exp (t • H)) x ∈ fermionSector N)
    ∧ (∀ M : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ, IsExchangeSymmetric M →
        ∀ x ∈ bosonSector N, ∀ y ∈ fermionSector N, ⟪x, toEuclideanLin M y⟫_ℂ = 0) :=
  ⟨⟨isCompl_bosonSector_fermionSector, fermionSector_eq_orthogonal⟩,
    ⟨finrank_bosonSector_eq_card, finrank_fermionSector_eq_card⟩,
    fun _ hx i => apply_diag_eq_zero_of_mem_fermionSector hx i,
    wedge_eq_zero_iff,
    fun _ _ hv hw hvw i => bosonic_enhancement hv hw hvw i,
    fun _ hH t => ⟨fun _ hx => (hH.exp_smul t).mem_bosonSector hx,
      fun _ hx => (hH.exp_smul t).mem_fermionSector hx⟩,
    fun _ hM _ hx _ hy => hM.inner_eq_zero hx hy⟩

end CSD.SigmaLayer
