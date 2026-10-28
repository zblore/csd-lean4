/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.CV.Oscillator
public import CsdLean4.CV.ApproxCCR
public import CsdLean4.SigmaLayer.FermionFock

/-!
# SigmaLayer/BosonFock: second quantisation for bosons, and the capstone

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)) — the identical-particle pillar.
BACKLOG #215 (boson half and capstone), after ~~#214~~ (`SigmaLayer/ManyIdenticalParticles.lean`)
and `SigmaLayer/FermionFock.lean` (the fermion half).

The bosonic Fock space of `K` modes, each truncated to `L` levels, is the CV track's occupation
lattice `FieldSpace K L` (`CV/FieldModes.lean`). Its ladder operators are the truncated oscillator's
(`CV/Oscillator.lean`) acting on one mode.

## What is proved

* `modeOp A k` — a single-mode matrix `A` acting on mode `k`: ★ `modeOp_mul`, `modeOp_one`,
  `modeOp_sub`, `modeOp_smul` (a representation of the single-mode matrix algebra), ★
  `modeOp_mul_comm` (**operators on different modes commute**), ★ `inner_modeOp_conjTranspose`
  (`Aᴴ` acts as the adjoint);
* `bAnnihilate k`, `bCreate k` — the truncated ladder operators of mode `k`, with `inner_bCreate`
  (creation is the adjoint of annihilation);
* ★★ `bAnnihilate_mul_bCreate_sub` — **`[b_k, b_k†] = 1 − L · |top⟩⟨top|_k`**, the CV track's
  `truncated_ccr` on mode `k`; ★★ `bAnnihilate_mul_bCreate_sub_of_ne` and
  `bAnnihilate_mul_bAnnihilate_sub` — **the CCR between different modes hold exactly**;
* `bNumber k = b_k† b_k` (the occupation of mode `k`), `bTotalNumber`; `bosonFockSector K L n`, the
  `n`-particle sector (`mem_bosonFockSector_iff`: the eigenspace of the total number), and ★★
  `isInternal_bosonFockSector` (**the Fock space is the direct sum of the `n`-particle sectors**);
* ★★★ `ccr_exact_on_bosonFockSector` — **on the `n`-particle sector with `n + 1 < L`, the CCR hold
  exactly**: the cutoff defect never acts there. Over the whole truncated space they cannot
  (`no_exact_finite_ccr`);
* ★★★ `bosonFockEquiv` — **for `n < L`, the `n`-particle sector of the Fock space is the `n`-boson
  sector of first quantisation** (`nBosonSector n K` of ~~#214~~), by the canonical map: the
  first-quantised amplitude on a sorted configuration is the Fock amplitude on its occupation
  numbers (`bosonFockEquiv_apply`, `monoOcc`, injective by sorting and onto by counting);
* ★★★ `second_quantisation` — the capstone, both halves.

## Honest scope

⚠️ **The identification is by the canonical map on amplitudes, not yet as operators.** That `b_k†`
and `a_j†` correspond to symmetrised and antisymmetrised tensoring with the orbital `e_k`, the
normalisation factors (`√(n!/∏ P_m!)` for bosons, `√n!` for fermions) that make the maps
isometric, and the correspondence of one-body operators `dΓ(h) = ∑ h_ij a_i† a_j` with `∑_k h^{(k)}`
are the operator dictionary: the fermion half is ~~#220~~ (`SigmaLayer/FermionDictionary.lean`), the
boson half BACKLOG #221, the one-body operators #222.

⚠️ **The bosonic CCR are exact only below the cutoff.** On the whole truncated space the defect is
unavoidable (`no_exact_finite_ccr`); the fermionic CAR need no cutoff (`SigmaLayer/FermionFock.lean`).

References: [`future-work.md`](../../specs/future-work.md) IP-1; `SigmaLayer/FermionFock.lean`
(`supportedOn`, `isInternal_supportedOn_fiber`, the CAR, Jordan–Wigner);
`SigmaLayer/ManyIdenticalParticles.lean` (`nBosonSector`, `nBosonEquiv`, `MonoConfig`);
`CV/Oscillator.lean` (`annihilation`, `creation`, `truncated_ccr`); `CV/ApproxCCR.lean`
(`no_exact_finite_ccr`); Mathlib `List.Perm.eq_of_sortedLE`, `Sym.equivNatSumOfFintype`;
`specs/BACKLOG.md` #215.
-/

@[expose] public section

open Module
open scoped InnerProductSpace Matrix

namespace CSD.SigmaLayer

open CSD.CV

variable {K L : ℕ}

/-! ### Single-mode operators on the multi-mode lattice -/

/-- **A single-mode matrix acting on mode `k`.** -/
noncomputable def modeOp (A : Matrix (Fin L) (Fin L) ℂ) (k : Fin K) :
    Module.End ℂ (FieldSpace K L) where
  toFun x := WithLp.toLp 2 fun c => ∑ m, A (c k) m * x (Function.update c k m)
  map_add' x y := by
    ext c
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    ext c
    simp [Finset.mul_sum, mul_left_comm]

theorem modeOp_apply (A : Matrix (Fin L) (Fin L) ℂ) (k : Fin K) (x : FieldSpace K L)
    (c : FieldConfig K L) :
    modeOp A k x c = ∑ m, A (c k) m * x (Function.update c k m) := rfl

theorem modeOp_mul (A B : Matrix (Fin L) (Fin L) ℂ) (k : Fin K) :
    modeOp (A * B) k = modeOp A k * modeOp B k := by
  apply LinearMap.ext
  intro x
  ext c
  simp only [Module.End.mul_apply, modeOp_apply, Matrix.mul_apply, Function.update_self,
    Function.update_idem, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem modeOp_one (k : Fin K) : modeOp (1 : Matrix (Fin L) (Fin L) ℂ) k = 1 := by
  apply LinearMap.ext
  intro x
  ext c
  simp [modeOp_apply, Matrix.one_apply, Function.update_eq_self]

theorem modeOp_sub (A B : Matrix (Fin L) (Fin L) ℂ) (k : Fin K) :
    modeOp (A - B) k = modeOp A k - modeOp B k := by
  apply LinearMap.ext
  intro x
  ext c
  simp [modeOp_apply, sub_mul, Finset.sum_sub_distrib]

theorem modeOp_smul (a : ℂ) (A : Matrix (Fin L) (Fin L) ℂ) (k : Fin K) :
    modeOp (a • A) k = a • modeOp A k := by
  apply LinearMap.ext
  intro x
  ext c
  simp [modeOp_apply, Finset.mul_sum, mul_assoc]

/-- **Operators on different modes commute.** -/
theorem modeOp_mul_comm {k k' : Fin K} (h : k ≠ k') (A B : Matrix (Fin L) (Fin L) ℂ) :
    modeOp A k * modeOp B k' = modeOp B k' * modeOp A k := by
  apply LinearMap.ext
  intro x
  ext c
  simp only [Module.End.mul_apply, modeOp_apply, Function.update_of_ne h.symm,
    Function.update_of_ne h, Finset.mul_sum, Function.update_comm h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The involution `(c, m) ↦ (c[k ↦ m], c k)` of configuration–level pairs. -/
def modeSwap (k : Fin K) : FieldConfig K L × Fin L ≃ FieldConfig K L × Fin L where
  toFun p := (Function.update p.1 k p.2, p.1 k)
  invFun p := (Function.update p.1 k p.2, p.1 k)
  left_inv p := by simp [Function.update_eq_self]
  right_inv p := by simp [Function.update_eq_self]

/-- **`Aᴴ` acts as the adjoint of `A`.** -/
theorem inner_modeOp_conjTranspose (A : Matrix (Fin L) (Fin L) ℂ) (k : Fin K)
    (x y : FieldSpace K L) :
    ⟪modeOp Aᴴ k x, y⟫_ℂ = ⟪x, modeOp A k y⟫_ℂ := by
  have hL : ⟪modeOp Aᴴ k x, y⟫_ℂ = ∑ p : FieldConfig K L × Fin L,
      y p.1 * (A p.2 (p.1 k) * (starRingEnd ℂ) (x (Function.update p.1 k p.2))) := by
    rw [PiLp.inner_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [RCLike.inner_apply, modeOp_apply, Matrix.conjTranspose_apply, Finset.mul_sum]
  have hR : ⟪x, modeOp A k y⟫_ℂ = ∑ p : FieldConfig K L × Fin L,
      A (p.1 k) p.2 * y (Function.update p.1 k p.2) * (starRingEnd ℂ) (x p.1) := by
    rw [PiLp.inner_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [RCLike.inner_apply, modeOp_apply, Finset.sum_mul]
  rw [hL, hR]
  refine Fintype.sum_equiv (modeSwap k) _ _ fun p => ?_
  simp only [modeSwap, Equiv.coe_fn_mk, Function.update_self, Function.update_idem,
    Function.update_eq_self]
  ring

/-! ### The truncated ladder operators -/

/-- **The bosonic annihilation operator** of mode `k`: the truncated oscillator's on that mode. -/
noncomputable def bAnnihilate (k : Fin K) : Module.End ℂ (FieldSpace K L) :=
  modeOp (annihilation L) k

/-- **The bosonic creation operator** of mode `k`. -/
noncomputable def bCreate (k : Fin K) : Module.End ℂ (FieldSpace K L) := modeOp (creation L) k

/-- Creation is the adjoint of annihilation. -/
theorem inner_bCreate (k : Fin K) (x y : FieldSpace K L) :
    ⟪bCreate k x, y⟫_ℂ = ⟪x, bAnnihilate k y⟫_ℂ :=
  inner_modeOp_conjTranspose (annihilation L) k x y

/-- **`[b_k, b_k†] = 1 − L · |top⟩⟨top|_k`**: the truncated CCR on mode `k`. -/
theorem bAnnihilate_mul_bCreate_sub (k : Fin K) :
    bAnnihilate k * bCreate k - bCreate k * bAnnihilate k
      = 1 - (L : ℂ) • modeOp (topProj L) k := by
  rw [bAnnihilate, bCreate, ← modeOp_mul, ← modeOp_mul, ← modeOp_sub, truncated_ccr, modeOp_sub,
    modeOp_one, modeOp_smul]

/-- **Different modes: `[b_k, b_{k'}†] = 0`**, exactly. -/
theorem bAnnihilate_mul_bCreate_sub_of_ne {k k' : Fin K} (h : k ≠ k') :
    bAnnihilate k * bCreate k' - bCreate k' * bAnnihilate k = (0 : Module.End ℂ (FieldSpace K L)) := by
  rw [bAnnihilate, bCreate, modeOp_mul_comm h, sub_self]

/-- **`[b_k, b_{k'}] = 0`**, exactly. -/
theorem bAnnihilate_mul_bAnnihilate_sub (k k' : Fin K) :
    bAnnihilate k * bAnnihilate k' - bAnnihilate k' * bAnnihilate k
      = (0 : Module.End ℂ (FieldSpace K L)) := by
  by_cases h : k = k'
  · subst h
    exact sub_self _
  · rw [bAnnihilate, bAnnihilate, modeOp_mul_comm h, sub_self]

theorem modeOp_topProj_apply (k : Fin K) (x : FieldSpace K L) (c : FieldConfig K L) :
    modeOp (topProj L) k x c = (if ((c k : Fin L) : ℕ) = L - 1 then 1 else 0) * x c := by
  rw [modeOp_apply, topProj, Finset.sum_eq_single (c k)]
  · rw [Matrix.diagonal_apply_eq, Function.update_eq_self]
  · intro m _ hm
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hm), zero_mul]
  · exact fun h => absurd (Finset.mem_univ _) h

/-! ### Number operators and the `n`-particle sectors -/

/-- The occupation of mode `k`, `b_k† b_k`. -/
noncomputable def bNumber (k : Fin K) : Module.End ℂ (FieldSpace K L) := bCreate k * bAnnihilate k

theorem bNumber_apply (k : Fin K) (x : FieldSpace K L) (c : FieldConfig K L) :
    bNumber k x c = (((c k : Fin L) : ℕ) : ℂ) * x c := by
  rw [bNumber, bCreate, bAnnihilate, ← modeOp_mul, creation_mul_annihilation, modeOp_apply,
    numberOp, Finset.sum_eq_single (c k)]
  · rw [Matrix.diagonal_apply_eq, Function.update_eq_self]
  · intro m _ hm
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hm), zero_mul]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- The total number of quanta in a configuration. -/
def bOccTotal (c : FieldConfig K L) : ℕ := ∑ k, (c k : ℕ)

/-- The total number operator `∑ b_k† b_k`. -/
noncomputable def bTotalNumber (K L : ℕ) : Module.End ℂ (FieldSpace K L) := ∑ k, bNumber k

theorem bTotalNumber_apply (x : FieldSpace K L) (c : FieldConfig K L) :
    bTotalNumber K L x c = (bOccTotal c : ℂ) * x c := by
  rw [bTotalNumber, LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  simp only [bNumber_apply, bOccTotal, Nat.cast_sum, Finset.sum_mul]

/-- **The `n`-particle sector of the bosonic Fock space.** -/
abbrev bosonFockSector (K L n : ℕ) : Submodule ℂ (FieldSpace K L) :=
  supportedOn fun c : FieldConfig K L => bOccTotal c = n

/-- The `n`-particle sector is the eigenspace of the total number with eigenvalue `n`. -/
theorem mem_bosonFockSector_iff {n : ℕ} {x : FieldSpace K L} :
    x ∈ bosonFockSector K L n ↔ bTotalNumber K L x = (n : ℂ) • x := by
  constructor
  · intro hx
    ext c
    rw [bTotalNumber_apply, PiLp.smul_apply, smul_eq_mul]
    by_cases h : bOccTotal c = n
    · rw [h]
    · rw [hx c h, mul_zero, mul_zero]
  · intro hx c hc
    have := congrArg (fun y : FieldSpace K L => y c) hx
    simp only [bTotalNumber_apply, PiLp.smul_apply, smul_eq_mul] at this
    have hne : (bOccTotal c : ℂ) - n ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hc)
    have h0 : ((bOccTotal c : ℂ) - n) * x c = 0 := by linear_combination this
    exact (mul_eq_zero.1 h0).resolve_left hne

/-- **The bosonic Fock space is the direct sum of the `n`-particle sectors.** -/
theorem isInternal_bosonFockSector : DirectSum.IsInternal (bosonFockSector K L) :=
  isInternal_supportedOn_fiber bOccTotal

theorem le_bOccTotal (c : FieldConfig K L) (k : Fin K) : (c k : ℕ) ≤ bOccTotal c :=
  Finset.single_le_sum (f := fun k => (c k : ℕ)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

/-- **Below the cutoff the CCR hold exactly**: on the `n`-particle sector with `n + 1 < L`,
`[b_k, b_k†] = 1`. -/
theorem ccr_exact_on_bosonFockSector {n : ℕ} (hn : n + 1 < L) {x : FieldSpace K L}
    (hx : x ∈ bosonFockSector K L n) (k : Fin K) :
    (bAnnihilate k * bCreate k - bCreate k * bAnnihilate k : Module.End ℂ (FieldSpace K L)) x = x := by
  rw [bAnnihilate_mul_bCreate_sub]
  ext c
  rw [LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply, PiLp.sub_apply,
    PiLp.smul_apply, modeOp_topProj_apply, smul_eq_mul]
  by_cases h : bOccTotal c = n
  · have hk := le_bOccTotal c k
    rw [ite_eq_right (by omega), zero_mul, mul_zero, sub_zero]
  · rw [hx c h, mul_zero, mul_zero, sub_zero]

/-! ### The identification with first quantisation -/

/-- The occupation-number configurations with `n` quanta. -/
abbrev BosonOcc (K L n : ℕ) : Type := {d : FieldConfig K L // bOccTotal d = n}

theorem count_ofFn_lt {n : ℕ} (hL : n < L) (c : Fin n → Fin K) (m : Fin K) :
    (List.ofFn c).count m < L :=
  lt_of_le_of_lt ((List.count_le_length).trans (by rw [List.length_ofFn])) hL

/-- **The occupation numbers of a sorted configuration.** -/
def monoOcc {n : ℕ} (hL : n < L) (c : MonoConfig n K) : BosonOcc K L n :=
  ⟨fun m => ⟨(List.ofFn c.1).count m, count_ofFn_lt hL c.1 m⟩, by
    simp only [bOccTotal]
    have := Multiset.sum_count_eq_card (s := Finset.univ)
      (m := (List.ofFn c.1 : Multiset (Fin K))) (fun a _ => Finset.mem_univ a)
    simpa using this⟩

theorem monoOcc_injective {n : ℕ} (hL : n < L) : Function.Injective (monoOcc (K := K) hL) := by
  intro c c' h
  have hcount : ∀ m, (List.ofFn c.1).count m = (List.ofFn c'.1).count m := fun m =>
    congrArg Fin.val (congrFun (congrArg Subtype.val h) m)
  have hperm : List.Perm (List.ofFn c.1) (List.ofFn c'.1) := List.perm_iff_count.2 hcount
  exact Subtype.ext (List.ofFn_injective
    (hperm.eq_of_sortedLE c.2.sortedLE_ofFn c'.2.sortedLE_ofFn))

/-- Below the cutoff, occupation configurations are the occupation-number vectors. -/
def bosonOccEquivNat {n : ℕ} (hL : n < L) :
    BosonOcc K L n ≃ {P : Fin K → ℕ // ∑ i, P i = n} where
  toFun d := ⟨fun m => d.1 m, d.2⟩
  invFun P := ⟨fun m => ⟨P.1 m, lt_of_le_of_lt
      ((Finset.single_le_sum (f := P.1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)).trans_eq
        P.2) hL⟩, P.2⟩
  left_inv d := by
    apply Subtype.ext
    funext m
    rfl
  right_inv P := by
    apply Subtype.ext
    funext m
    rfl

theorem card_bosonOcc {n : ℕ} (hL : n < L) :
    Fintype.card (BosonOcc K L n) = (K + n - 1).choose n := by
  rw [Fintype.card_congr ((bosonOccEquivNat hL).trans (Sym.equivNatSumOfFintype (Fin K) n).symm),
    Sym.card_sym_eq_choose, Fintype.card_fin]

theorem card_monoConfig (n K : ℕ) : Fintype.card (MonoConfig n K) = (K + n - 1).choose n := by
  rw [Fintype.card_congr (monoStrictEquiv n K), Fintype.card_congr (strictConfigEquivFinset n _),
    Fintype.card_finset_len, Fintype.card_fin]

/-- **Sorted configurations are occupation-number configurations**, below the cutoff. -/
noncomputable def monoOccEquiv {n : ℕ} (hL : n < L) : MonoConfig n K ≃ BosonOcc K L n :=
  Equiv.ofBijective (monoOcc hL) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨monoOcc_injective hL, by rw [card_monoConfig, card_bosonOcc hL]⟩)

/-- **The `n`-particle Fock sector is the `n`-boson sector of first quantisation**, for `n < L`:
the first-quantised amplitude on a sorted configuration is the Fock amplitude on its occupation
numbers. -/
noncomputable def bosonFockEquiv {n : ℕ} (hL : n < L) :
    bosonFockSector K L n ≃ₗ[ℂ] nBosonSector n K :=
  (supportedOnEquiv _).trans ((LinearEquiv.funCongrLeft ℂ ℂ (monoOccEquiv hL)).trans
    nBosonEquiv.symm)

theorem bosonFockEquiv_apply {n : ℕ} (hL : n < L) (y : bosonFockSector K L n)
    (c : MonoConfig n K) :
    (bosonFockEquiv hL y : ManyParticle n K) c.1 = (y : FieldSpace K L) (monoOcc hL c).1 := by
  rw [show (bosonFockEquiv hL y : ManyParticle n K) c.1 = nBosonEquiv (bosonFockEquiv hL y) c
    from rfl]
  unfold bosonFockEquiv
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- **`n` bosons in the Fock space span `(K + n − 1).choose n` dimensions**, below the cutoff. -/
theorem finrank_bosonFockSector {n : ℕ} (hL : n < L) :
    finrank ℂ (bosonFockSector K L n) = (K + n - 1).choose n := by
  rw [LinearEquiv.finrank_eq (bosonFockEquiv hL), finrank_nBosonSector]

/-! ### The capstone -/

/-- **Second quantisation at finite dimension.**

1. fermions: the CAR hold exactly — `{a_i, a_j†} = δ_ij`, `{a_i, a_j} = 0`, `{a_i†, a_j†} = 0` —
   creation is the adjoint of annihilation, and `a_j = Z_0 ⋯ Z_{j−1} σ⁻_j` (Jordan–Wigner);
2. the fermionic Fock space has dimension `2^N`, is the direct sum of its `n`-particle sectors, and
   each is the `n`-fermion sector of first quantisation (`nFermionSector n N`);
3. bosons: `[b_k, b_k†] = 1 − L · |top⟩⟨top|_k` and the CCR between different modes hold exactly;
4. on the `n`-particle sector with `n + 1 < L` the CCR hold exactly, while on the whole truncated
   space no pair of matrices satisfies them;
5. the bosonic Fock space is the direct sum of its `n`-particle sectors, and for `n < L` each is the
   `n`-boson sector of first quantisation (`nBosonSector n K`). -/
theorem second_quantisation (N : ℕ) :
    ((∀ i j : Fin N, fAnnihilate i * fCreate j + fCreate j * fAnnihilate i
          = if i = j then 1 else 0)
        ∧ (∀ i j : Fin N, fAnnihilate i * fAnnihilate j + fAnnihilate j * fAnnihilate i = 0)
        ∧ (∀ i j : Fin N, fCreate i * fCreate j + fCreate j * fCreate i = 0)
        ∧ (∀ (j : Fin N) (x y : FieldSpace N 2), ⟪fCreate j x, y⟫_ℂ = ⟪x, fAnnihilate j y⟫_ℂ)
        ∧ ∀ j : Fin N, fAnnihilate j = jwString j * qubitLower j)
    ∧ (finrank ℂ (FieldSpace N 2) = 2 ^ N
        ∧ DirectSum.IsInternal (fockSector N)
        ∧ ∀ n, Nonempty (fockSector N n ≃ₗ[ℂ] nFermionSector n N))
    ∧ ((∀ k : Fin K, bAnnihilate k * bCreate k - bCreate k * bAnnihilate k
          = 1 - (L : ℂ) • modeOp (topProj L) k)
        ∧ (∀ k k' : Fin K, k ≠ k' →
          bAnnihilate k * bCreate k' - bCreate k' * bAnnihilate k
            = (0 : Module.End ℂ (FieldSpace K L)))
        ∧ ∀ k k' : Fin K, bAnnihilate k * bAnnihilate k' - bAnnihilate k' * bAnnihilate k
            = (0 : Module.End ℂ (FieldSpace K L)))
    ∧ ((∀ n, n + 1 < L → ∀ x ∈ bosonFockSector K L n, ∀ k : Fin K,
          (bAnnihilate k * bCreate k - bCreate k * bAnnihilate k : Module.End ℂ (FieldSpace K L)) x
            = x)
        ∧ ∀ (Q P : Matrix (Fin L) (Fin L) ℂ) (c : ℂ), c ≠ 0 → 0 < L → Q * P - P * Q ≠ c • 1)
    ∧ (DirectSum.IsInternal (bosonFockSector K L)
        ∧ ∀ n, n < L → Nonempty (bosonFockSector K L n ≃ₗ[ℂ] nBosonSector n K)) :=
  ⟨⟨fAnnihilate_mul_fCreate_add, fAnnihilate_mul_fAnnihilate_add, fCreate_mul_fCreate_add,
      inner_fCreate, fAnnihilate_eq_jwString_mul_qubitLower⟩,
    ⟨finrank_fermionFock, isInternal_fockSector, fun n => ⟨fockFermionEquiv n N⟩⟩,
    ⟨bAnnihilate_mul_bCreate_sub, fun _ _ h => bAnnihilate_mul_bCreate_sub_of_ne h,
      bAnnihilate_mul_bAnnihilate_sub⟩,
    ⟨fun _ hn _ hx k => ccr_exact_on_bosonFockSector hn hx k,
      fun Q P _ hc hL => no_exact_finite_ccr Q P (mul_ne_zero hc (by
        rw [Fintype.card_fin]
        exact_mod_cast hL.ne'))⟩,
    ⟨isInternal_bosonFockSector, fun _ hL => ⟨bosonFockEquiv hL⟩⟩⟩

end CSD.SigmaLayer
