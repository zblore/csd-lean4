/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.SigmaLayer.OneBody

/-!
# SigmaLayer/TwoBody: two-body interactions in the two pictures

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)) — the identical-particle pillar.
BACKLOG #223, after ~~#222~~ (`SigmaLayer/OneBody.lean`).

A two-particle matrix `V`, with `V (i, j) (k, l) = ⟨ij|V|kl⟩`, acts on `n` identical particles as
`½ ∑_{p ≠ q} V^{(pq)}`, the same `V` on every pair (`twoBody V`). In second quantisation it is
`½ ∑ V_{(ij)(kl)} a_i† a_j† a_l a_k` (`dGamma2F`, `dGamma2B`). This module proves the two are the
same operator under the first-quantisation maps of ~~#220~~ and ~~#221~~.

The route avoids a second round of slot-sign bookkeeping. Normal ordering rewrites
`a_i† a_j† a_l a_k` as `a_i† a_k · a_j† a_l − δ_jk a_i† a_l`, a polynomial in one-body hops, which
~~#222~~ already carries across. In first quantisation the same polynomial in the hops
`oneBody (single i k 1)` is `½ ∑_{p ≠ q} V^{(pq)}`: the `p = q` terms of the double hop are exactly
the `δ_jk` correction. This identity holds on every state, symmetric or not.

## What is proved

* `twoBody V` — `(½ ∑_{p≠q} V^{(pq)} x)(c)
  = ½ ∑_{p≠q} ∑_{(m,m')} V (c_p, c_q) (m, m') · x (c[p ↦ m][q ↦ m'])`;
* ★★ `oneBody_single_oneBody_single_apply` / ★★ `twoBody_eq_sum_oneBody` — **the pair operator as
  a polynomial in one-body hops**, `½ ∑ V_{ab} (E_{a₁b₁} E_{a₂b₂} − δ_{a₂b₁} E_{a₁b₂})`, on every
  state;
* `twoBody_one` — the unit interaction counts pairs, `n(n−1)/2`;
* ★★ `fCreate_mul_fCreate_mul_fAnnihilate_mul_fAnnihilate` — **normal ordering for fermions**, from
  the exact CAR; ★★ `bCreate_mul_bCreate_mul_bAnnihilate_mul_bAnnihilate` — **the same for truncated
  bosons**, where `δ_jk` carries the top-level correction `1 − L P_k` of the truncated CCR;
* `dGamma2F_one` — the unit fermion interaction is `½ N̂(N̂ − 1)`;
* `bosonFirst_bCreate_topProj` — the top-level correction is invisible below the cutoff;
* ★★★ `fermionFirst_dGamma2F` — **`Φ_n (W y) = (½ ∑_{p≠q} V^{(pq)}) (Φ_n y)` for fermions**, every
  `n`;
* ★★★ `bosonFirst_dGamma2B` — **the same for bosons**, below the cutoff;
* ★★★ `two_body` — the capstone.

## Honest scope

⚠️ **Bosons below the cutoff** (`n < L`), as in ~~#221~~ and ~~#222~~. On the truncated space the
boson normal ordering carries the top-level projector; it drops out only because `Φ_n` reads no
amplitude with a mode at the top level.

⚠️ **No symmetry is imposed on `V`.** The identities hold for every two-particle matrix; Hermiticity
and exchange symmetry `V_{(ij)(kl)} = V_{(ji)(lk)}` are what make `W` a physical interaction, and
are not needed for the dictionary.

References: [`future-work.md`](../../specs/future-work.md) IP-1; `SigmaLayer/OneBody.lean`
(`fermionFirst_dGammaF`, `bosonFirst_dGammaB`, `oneBody`); `SigmaLayer/FermionFock.lean`
(`fAnnihilate_mul_fCreate_add`, `fAnnihilate_mul_fAnnihilate_add`); `SigmaLayer/BosonFock.lean`
(`bAnnihilate_mul_bCreate_sub`, `modeOp_topProj_apply`); `specs/BACKLOG.md` #223.
-/

@[expose] public section

open Module
open scoped InnerProductSpace

namespace CSD.SigmaLayer

open CSD.CV

variable {n N K L : ℕ}

/-! ### Two-body operators in first quantisation -/

/-- **A one-body hop** `E_{ab}`: move one particle from mode `b` into mode `a`, in every slot. -/
theorem oneBody_single_apply (a b : Fin N) (x : ManyParticle n N) (c : ManyConfig n N) :
    oneBody (Matrix.single a b 1) x c = ∑ p, if c p = a then x (Function.update c p b) else 0 := by
  rw [oneBody_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : c p = a
  · simp [h, Matrix.single_apply, Finset.sum_ite_eq]
  · simp [h, Ne.symm h]

/-- **Two hops are a pair hop plus a one-body correction**:
`(E_{ik} E_{jl} x)(c) − δ_jk (E_{il} x)(c) = ∑_{p ≠ q} [c_p = i, c_q = j] x(c[p ↦ k][q ↦ l])`; the
`p = q` terms of the double hop are the correction. -/
theorem oneBody_single_oneBody_single_apply (i j k l : Fin N) (x : ManyParticle n N)
    (c : ManyConfig n N) :
    oneBody (Matrix.single i k 1) (oneBody (Matrix.single j l 1) x) c
        - (if j = k then oneBody (Matrix.single i l 1) x c else 0)
      = ∑ p, ∑ q ∈ Finset.univ.erase p,
          if c p = i ∧ c q = j then x (Function.update (Function.update c p k) q l) else 0 := by
  have hsplit : ∀ p, (∑ q, if Function.update c p k q = j
        then x (Function.update (Function.update c p k) q l) else 0)
      = (if k = j then x (Function.update c p l) else 0)
        + ∑ q ∈ Finset.univ.erase p,
          if c q = j then x (Function.update (Function.update c p k) q l) else 0 := fun p => by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), Function.update_self,
      Function.update_idem]
    congr 1
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hq)]
  simp only [oneBody_single_apply, hsplit, ite_and]
  by_cases hjk : j = k
  · subst hjk
    simp only [↓reduceIte]
    rw [sub_eq_iff_eq_add', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : c p = i <;> simp [h]
  · simp only [hjk, Ne.symm hjk, ↓reduceIte, zero_add, sub_zero]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : c p = i <;> simp [h]

/-- **A two-particle matrix acting on every pair of particles**, `½ ∑_{p ≠ q} V^{(pq)}`, with
`V (i, j) (k, l) = ⟨ij|V|kl⟩`. -/
noncomputable def twoBody (V : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) :
    ManyParticle n N →ₗ[ℂ] ManyParticle n N where
  toFun x := WithLp.toLp 2 fun c => (1 / 2 : ℂ) * ∑ p, ∑ q ∈ Finset.univ.erase p, ∑ b,
      V (c p, c q) b * x (Function.update (Function.update c p b.1) q b.2)
  map_add' x y := by
    ext c
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    ext c
    simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun b _ => by ring

theorem twoBody_apply (V : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) (x : ManyParticle n N)
    (c : ManyConfig n N) :
    twoBody V x c = (1 / 2 : ℂ) * ∑ p, ∑ q ∈ Finset.univ.erase p, ∑ b,
      V (c p, c q) b * x (Function.update (Function.update c p b.1) q b.2) := rfl

/-- **The pair operator as a polynomial in one-body hops**,
`½ ∑_{p≠q} V^{(pq)} = ½ ∑_{ab} V_{ab} (E_{a₁b₁} E_{a₂b₂} − δ_{a₂b₁} E_{a₁b₂})`, on every state. -/
theorem twoBody_eq_sum_oneBody (V : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ)
    (x : ManyParticle n N) :
    twoBody V x = (1 / 2 : ℂ) • ∑ a, ∑ b, V a b •
      (oneBody (Matrix.single a.1 b.1 1) (oneBody (Matrix.single a.2 b.2 1) x)
        - if a.2 = b.1 then oneBody (Matrix.single a.1 b.2 1) x else 0) := by
  ext c
  have hc : ∀ a b : Fin N × Fin N,
      (oneBody (Matrix.single a.1 b.1 1) (oneBody (Matrix.single a.2 b.2 1) x)
        - if a.2 = b.1 then oneBody (Matrix.single a.1 b.2 1) x else 0) c
      = ∑ p, ∑ q ∈ Finset.univ.erase p, if c p = a.1 ∧ c q = a.2
          then x (Function.update (Function.update c p b.1) q b.2) else 0 := fun a b => by
    rw [← oneBody_single_oneBody_single_apply]
    split_ifs <;> simp
  simp only [twoBody_apply, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul, hc]
  congr 1
  symm
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  calc _ = ∑ a : Fin N × Fin N, ∑ p, ∑ b : Fin N × Fin N, ∑ q ∈ Finset.univ.erase p,
        if c p = a.1 ∧ c q = a.2 then
          V a b * x (Function.update (Function.update c p b.1) q b.2) else 0 :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ p, ∑ q ∈ Finset.univ.erase p, ∑ b : Fin N × Fin N, ∑ a : Fin N × Fin N,
        if c p = a.1 ∧ c q = a.2 then
          V a b * x (Function.update (Function.update c p b.1) q b.2) else 0 := by
        refine Finset.sum_comm.trans (Finset.sum_congr rfl fun p _ => ?_)
        exact (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans
          (Finset.sum_comm.trans (Finset.sum_congr rfl fun q _ => Finset.sum_comm))
    _ = _ := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
          Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_eq_single (c p, c q)]
        · simp
        · intro a _ ha
          refine ite_eq_right_iff.2 fun h => absurd h ?_
          rintro ⟨h1, h2⟩
          exact ha (Prod.ext h1.symm h2.symm)
        · exact fun h => absurd (Finset.mem_univ _) h

/-- **The unit interaction counts pairs**: `½ ∑_{p ≠ q} 1 = n(n−1)/2`. -/
theorem twoBody_one (x : ManyParticle n N) :
    twoBody (1 : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) x = ((n.choose 2 : ℕ) : ℂ) • x := by
  ext c
  have hb : ∀ p q, ∑ b : Fin N × Fin N, (1 : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) (c p, c q) b
      * x (Function.update (Function.update c p b.1) q b.2) = x c := fun p q => by
    rw [Finset.sum_eq_single (c p, c q)]
    · simp
    · intro b _ hb
      rw [Matrix.one_apply_ne (Ne.symm hb), zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h
  rw [twoBody_apply, PiLp.smul_apply, smul_eq_mul]
  simp only [hb, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_choose_two]
  cases n with
  | zero => simp
  | succ n =>
    push_cast
    ring

/-! ### Two-body operators in second quantisation -/

/-- `dΓ` of a matrix unit is a single hop `a_a† a_b`. -/
theorem dGammaF_single (a b : Fin N) :
    dGammaF (Matrix.single a b 1) = fCreate a * fAnnihilate b := by
  simp [dGammaF, Matrix.single_apply, ite_smul, ite_and, Finset.sum_ite_eq]

/-- `dΓ` of a matrix unit is a single hop `b_a† b_b`. -/
theorem dGammaB_single (a b : Fin K) :
    dGammaB (L := L) (Matrix.single a b 1) = bCreate a * bAnnihilate b := by
  simp [dGammaB, Matrix.single_apply, ite_smul, ite_and, Finset.sum_ite_eq]

/-- **Normal ordering for fermions**: `a_i† a_j† a_l a_k = a_i† a_k a_j† a_l − δ_jk a_i† a_l`. -/
theorem fCreate_mul_fCreate_mul_fAnnihilate_mul_fAnnihilate (i j k l : Fin N) :
    fCreate i * fCreate j * fAnnihilate l * fAnnihilate k
      = fCreate i * fAnnihilate k * (fCreate j * fAnnihilate l)
        - if j = k then fCreate i * fAnnihilate l else 0 := by
  have h1 : fAnnihilate l * fAnnihilate k = -(fAnnihilate k * fAnnihilate l) :=
    eq_neg_of_add_eq_zero_left (fAnnihilate_mul_fAnnihilate_add l k)
  have hL : fCreate i * fCreate j * fAnnihilate l * fAnnihilate k
      = -(fCreate i * (fCreate j * fAnnihilate k) * fAnnihilate l) := by
    rw [mul_assoc _ (fAnnihilate l), h1]
    simp only [mul_neg, mul_assoc]
  have hR : fCreate i * fAnnihilate k * (fCreate j * fAnnihilate l)
      = fCreate i * (fAnnihilate k * fCreate j) * fAnnihilate l := by
    simp only [mul_assoc]
  rw [hL, hR]
  by_cases hjk : j = k
  · subst hjk
    rw [eq_sub_of_add_eq (fAnnihilate_mul_fCreate_add_self j), ite_eq_left (rfl : j = j)]
    simp only [mul_sub, sub_mul, mul_one]
    abel
  · rw [eq_neg_of_add_eq_zero_left (fAnnihilate_mul_fCreate_add_of_ne (Ne.symm hjk)),
      ite_eq_right hjk]
    simp only [mul_neg, neg_mul, sub_zero]

/-- **Normal ordering for truncated bosons**:
`b_i† b_j† b_l b_k = b_i† b_k b_j† b_l − δ_jk b_i† (1 − L P_k) b_l`, where `P_k` projects on the
top level of mode `k`. -/
theorem bCreate_mul_bCreate_mul_bAnnihilate_mul_bAnnihilate (i j k l : Fin K) :
    bCreate i * bCreate j * bAnnihilate l * bAnnihilate k
      = bCreate i * bAnnihilate k * (bCreate j * bAnnihilate l)
        - if j = k then bCreate i * (1 - (L : ℂ) • modeOp (topProj L) k) * bAnnihilate l
          else 0 := by
  have h1 : bAnnihilate l * bAnnihilate k = bAnnihilate k * bAnnihilate l :=
    sub_eq_zero.1 (bAnnihilate_mul_bAnnihilate_sub (L := L) l k)
  calc bCreate i * bCreate j * bAnnihilate l * bAnnihilate k
      = bCreate i * bCreate j * bAnnihilate k * bAnnihilate l := by
        rw [mul_assoc _ (bAnnihilate l), h1, ← mul_assoc]
    _ = bCreate i * bAnnihilate k * (bCreate j * bAnnihilate l)
        - bCreate i * (bAnnihilate k * bCreate j - bCreate j * bAnnihilate k) * bAnnihilate l := by
        noncomm_ring
    _ = _ := by
        by_cases hjk : j = k
        · subst hjk
          rw [bAnnihilate_mul_bCreate_sub, ite_eq_left (rfl : j = j)]
        · rw [bAnnihilate_mul_bCreate_sub_of_ne (Ne.symm hjk), ite_eq_right hjk, mul_zero, zero_mul]

/-- **The two-body interaction** `½ ∑ V_{(ij)(kl)} a_i† a_j† a_l a_k` on the fermionic Fock
space. -/
noncomputable def dGamma2F (V : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) :
    Module.End ℂ (FieldSpace N 2) :=
  (1 / 2 : ℂ) • ∑ a, ∑ b, V a b • (fCreate a.1 * fCreate a.2 * fAnnihilate b.2 * fAnnihilate b.1)

/-- **The two-body interaction** `½ ∑ V_{(ij)(kl)} b_i† b_j† b_l b_k` on the bosonic Fock space. -/
noncomputable def dGamma2B (V : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ) :
    Module.End ℂ (FieldSpace K L) :=
  (1 / 2 : ℂ) • ∑ a, ∑ b, V a b • (bCreate a.1 * bCreate a.2 * bAnnihilate b.2 * bAnnihilate b.1)

/-- **Two-body operators in the two pictures, for fermions**:
`Φ_n (W y) = (½ ∑_{p≠q} V^{(pq)}) Φ_n y`, every `n`. -/
theorem fermionFirst_dGamma2F (V : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ)
    (y : FieldSpace N 2) :
    fermionFirst n N (dGamma2F V y) = twoBody V (fermionFirst n N y) := by
  have hE : ∀ (a b : Fin N) (w : FieldSpace N 2), fermionFirst n N (fCreate a (fAnnihilate b w))
      = oneBody (Matrix.single a b 1) (fermionFirst n N w) := fun a b w => by
    rw [← fermionFirst_dGammaF, dGammaF_single]
    rfl
  have hterm : ∀ a b : Fin N × Fin N,
      fermionFirst n N ((fCreate a.1 * fCreate a.2 * fAnnihilate b.2 * fAnnihilate b.1) y)
        = oneBody (Matrix.single a.1 b.1 1) (oneBody (Matrix.single a.2 b.2 1) (fermionFirst n N y))
          - if a.2 = b.1 then oneBody (Matrix.single a.1 b.2 1) (fermionFirst n N y) else 0 :=
      fun a b => by
    rw [fCreate_mul_fCreate_mul_fAnnihilate_mul_fAnnihilate, LinearMap.sub_apply, map_sub]
    simp only [Module.End.mul_apply, hE]
    split_ifs <;> simp [hE]
  rw [twoBody_eq_sum_oneBody]
  simp only [dGamma2F, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, hterm]

/-- **The unit fermion interaction is `½ N̂(N̂ − 1)`**, with `N̂` the total number. -/
theorem dGamma2F_one :
    dGamma2F (1 : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ)
      = (1 / 2 : ℂ) • (fTotalNumber N * (fTotalNumber N - 1)) := by
  simp only [dGamma2F, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, Fintype.sum_prod_type,
    fCreate_mul_fCreate_mul_fAnnihilate_mul_fAnnihilate, Finset.sum_sub_distrib]
  congr 1
  rw [fTotalNumber, mul_sub, mul_one, Finset.sum_mul_sum]
  simp only [fNumber, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- Below the cutoff, the first-quantisation map does not see the top level of a mode. -/
theorem bosonFirst_modeOp_topProj (hL : n + 1 < L) (k : Fin K) (z : FieldSpace K L) :
    bosonFirst (Nat.lt_of_succ_lt hL) (modeOp (topProj L) k z) = 0 := by
  ext c
  have hne : ((occOf (Nat.lt_of_succ_lt hL) c k : Fin L) : ℕ) ≠ L - 1 := by
    have := occNat_le c k
    simp only [occOf]
    omega
  rw [bosonFirst_apply, modeOp_topProj_apply, ite_eq_right hne, zero_mul, mul_zero, PiLp.zero_apply]

/-- The vacuum component of a created state vanishes. -/
theorem bosonFirst_bCreate_zero (hL : 0 < L) (i : Fin K) (w : FieldSpace K L) :
    bosonFirst hL (bCreate i w) = 0 := by
  ext c
  rw [bosonFirst_apply, PiLp.zero_apply, bCreate_apply_of_eq_zero i w _ (by
    simp [occOf, occNat]), mul_zero]

/-- The top-level correction of the truncated commutator is invisible below the cutoff. -/
theorem bosonFirst_bCreate_topProj (hL : n < L) (i k : Fin K) (z : FieldSpace K L) :
    bosonFirst hL (bCreate i (modeOp (topProj L) k z)) = 0 := by
  cases n with
  | zero => exact bosonFirst_bCreate_zero hL i _
  | succ n => rw [bosonFirst_bCreate hL, bosonFirst_modeOp_topProj hL, map_zero]

/-- **Two-body operators in the two pictures, for bosons**: `Φ_n (W y) = (½ ∑_{p≠q} V^{(pq)}) Φ_n y`
below the cutoff. -/
theorem bosonFirst_dGamma2B (hL : n < L) (V : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ)
    (y : FieldSpace K L) :
    bosonFirst hL (dGamma2B V y) = twoBody V (bosonFirst hL y) := by
  have hE : ∀ (a b : Fin K) (w : FieldSpace K L), bosonFirst hL (bCreate a (bAnnihilate b w))
      = oneBody (Matrix.single a b 1) (bosonFirst hL w) := fun a b w => by
    rw [← bosonFirst_dGammaB, dGammaB_single]
    rfl
  have hterm : ∀ a b : Fin K × Fin K,
      bosonFirst hL ((bCreate a.1 * bCreate a.2 * bAnnihilate b.2 * bAnnihilate b.1 :
          Module.End ℂ (FieldSpace K L)) y)
        = oneBody (Matrix.single a.1 b.1 1) (oneBody (Matrix.single a.2 b.2 1) (bosonFirst hL y))
          - if a.2 = b.1 then oneBody (Matrix.single a.1 b.2 1) (bosonFirst hL y) else 0 :=
      fun a b => by
    rw [bCreate_mul_bCreate_mul_bAnnihilate_mul_bAnnihilate, LinearMap.sub_apply, map_sub]
    simp only [Module.End.mul_apply, hE]
    split_ifs
    · simp only [mul_sub, sub_mul, mul_one, LinearMap.sub_apply, Module.End.mul_apply,
        map_sub, hE, LinearMap.smul_apply, map_smul, bosonFirst_bCreate_topProj, smul_zero,
        sub_zero]
    · simp
  rw [twoBody_eq_sum_oneBody]
  simp only [dGamma2B, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, hterm]

/-! ### The capstone -/

/-- **Two-body interactions in the two pictures.**

1. in first quantisation, `½ ∑_{p≠q} V^{(pq)}` is the hop polynomial
   `½ ∑ V_{ab} (E_{a₁b₁} E_{a₂b₂} − δ_{a₂b₁} E_{a₁b₂})`, on every state;
2. `½ ∑ V_{(ij)(kl)} a_i† a_j† a_l a_k` on the fermionic Fock space is `½ ∑_{p≠q} V^{(pq)}` on every
   `n`-fermion sector;
3. `½ ∑ V_{(ij)(kl)} b_i† b_j† b_l b_k` on the bosonic Fock space is `½ ∑_{p≠q} V^{(pq)}` on every
   `n`-boson sector below the cutoff;
4. the unit interaction counts pairs: `n(n−1)/2` in first quantisation, `½ N̂(N̂ − 1)` for
   fermions. -/
theorem two_body :
    (∀ (V : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) (x : ManyParticle n N),
        twoBody V x = (1 / 2 : ℂ) • ∑ a, ∑ b, V a b •
          (oneBody (Matrix.single a.1 b.1 1) (oneBody (Matrix.single a.2 b.2 1) x)
            - if a.2 = b.1 then oneBody (Matrix.single a.1 b.2 1) x else 0))
    ∧ (∀ (V : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) (y : FieldSpace N 2),
        fermionFirst n N (dGamma2F V y) = twoBody V (fermionFirst n N y))
    ∧ (∀ (hL : n < L) (V : Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ) (y : FieldSpace K L),
        bosonFirst hL (dGamma2B V y) = twoBody V (bosonFirst hL y))
    ∧ ((∀ x : ManyParticle n N,
          twoBody (1 : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) x = ((n.choose 2 : ℕ) : ℂ) • x)
        ∧ dGamma2F (1 : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ)
          = (1 / 2 : ℂ) • (fTotalNumber N * (fTotalNumber N - 1))) :=
  ⟨twoBody_eq_sum_oneBody, fermionFirst_dGamma2F, bosonFirst_dGamma2B, ⟨twoBody_one, dGamma2F_one⟩⟩

end CSD.SigmaLayer
