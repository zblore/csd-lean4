/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.QEC.SteaneFaultyRecovery

/-!
# The fault model of Steane's method, completed

**Category:** 3-Local (Empirical, QM twin). BACKLOG #235 (residue of ~~#232~~).

`SteaneFaultyRecovery.lean` (~~#232~~) proved `deviatesBy_faultyMethod` for one kind of extraction
fault: a **unitary** on data qubit `q` and ancilla qubit `q`, **after** the transversal `CNOT`. This
module adds the other two cases — a fault before the `CNOT`, and a fault that is a channel — so that
any single-location fault model at an extraction location is a CSS deviation.

## Operators on one pair

* `PairOp`; `OnPair.of_sum`, `OnPair.zero`, `onPair_one`, `OnPair.add`, `OnPair.smul`,
  ★ `OnPair.mul`, `OnPair.list_prod` — the operators on data qubit `q` and ancilla qubit `q` form a
  subalgebra;
* `cnotData`, `cnotAnc`, ★★ `tCNOT_conj_kron` — **the transversal `CNOT` conjugates a product on the
  pair `q` into four such products** (`CNOT (A ⊗ B) CNOT = Σ_{a,b} PₐAP_b ⊗ XᵃBXᵇ`; the other pairs'
  `CNOT`s cancel); ★★ `OnPair.conj_tCNOT` — so it keeps every operator on the pair on the pair.

## A fault before the `CNOT`

`readAround`, ★★ `readAround_eq` — **Steane's extraction with `Fb` before the `CNOT` and `Fa` after
it is the extraction with the single fault `Fa · CNOT Fb CNOT` after it**: a fault before the `CNOT`
is the conjugated fault after it.

## A fault that is a channel

* `sum_faultReadOp_conjTranspose_mul_eq`, ★ `sum_faultReadOp_family`, `sum_bitFaultOp_family`,
  `sum_phaseFaultOp_family` — **the readout under a Kraus family of faults is a complete
  measurement** whenever the family is trace preserving;
* `channelKraus`, ★★ `channelMethod` — **Steane's method with a channel fault at one extraction
  location, as a channel**; ★ `channelMethod_unit` — with a one-operator family it is ~~#232~~'s
  `faultyMethod`;
* `aroundFam`, `aroundFam_tp`, ★ `onPair_aroundFam` — **a channel before the `CNOT` and a channel
  after it are one channel after it**, still on the pair;
* ★★★ `deviatesBy_channelMethod` — **Steane's method with any channel fault on the pair at one
  extraction location is a CSS deviation of the identity**; ★★★ `deviatesBy_channelMethod_around` —
  **with faults on both sides of the `CNOT`**; ★★ `methodRecovery_channelMethod` — the next recovery
  removes it.

## Faults under a pattern

* `sum_prod_ofFn_conjTranspose_mul` — **any number of channels in sequence is a channel**;
  `prod_ofFn_eq_one`;
* `locFam`, `locFam_tp`, `onPair_locFam`, `onPair_locFam_false` — **one location under a pattern as a
  Kraus family**: the fault's channel if it is faulty, the identity if not;
* `roundKraus`, `roundKraus_tp`, `roundKraus_none`, `roundKraus_none_of_ne`,
  `onPair_roundKraus_single` — **seven locations under a pattern**, branch by branch;
  `faultReadOp_zero`, `bitFaultOp_zero`, `phaseFaultOp_zero`.

`SteaneOverlapMachine.lean` (~~#233~~) runs the machine with this fault model at every extraction
location.

## Honest scope

⚠️ **The pair, not the block.** A fault at extraction location `q` acts on data qubit `q` and ancilla
qubit `q`; a fault spreading to a second pair is two locations, as in every location count.

⚠️ **Ancilla preparation is ideal** (#234): a fault inside the encoding circuit of `|+̄⟩` can act on
several ancilla qubits at once and is not a fault on one pair. ▸ The verified preparation is
`SteaneVerifiedAncilla.lean` (BACKLOG ~~#234~~).

⚠️ **One round per basis**, as in ~~#228~~ and ~~#229~~.

References: A. Steane, PRL 78 (1997) 2252; P. Aliferis, D. Gottesman, J. Preskill, Quantum Inf.
Comput. 6 (2006) 97; `specs/BACKLOG.md` #235, #232, #233, #234, #231;
`Empirical/QM/QEC/SteaneFaultyRecovery.lean`,
`Empirical/QM/QEC/SteaneMethod.lean`, `Empirical/QM/QEC/SteaneOverlapMachine.lean`,
`Mathlib/QuantumInfo/SyndromeExtraction.lean`; `docs/FROM-POSTULATES-TO-QUANTUM-COMPUTERS.md` link 12;
`specs/future-work.md`.
-/

@[expose] public section

open Matrix QuantumInfo
open QuantumInfo.CliffordT Controlled QuantumInfo.Controlled
open scoped Kronecker

noncomputable section

namespace QuantumInfo

/-- **Any number of channels in sequence**: the ordered products of one Kraus operator from each of
`m` trace-preserving families form a trace-preserving family. -/
theorem sum_prod_ofFn_conjTranspose_mul {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] :
    ∀ {m : ℕ} (X : Fin m → ι → Matrix n n ℂ), (∀ i, ∑ a, (X i a)ᴴ * X i a = 1) →
      ∑ s : Fin m → ι, ((List.ofFn fun i => X i (s i)).prod)ᴴ * (List.ofFn fun i => X i (s i)).prod
        = 1
  | 0, X, _ => by simp
  | m + 1, X, hX => by
    have ih := sum_prod_ofFn_conjTranspose_mul (fun i => X i.succ) fun i => hX i.succ
    rw [← (Fin.consEquiv fun _ : Fin (m + 1) => ι).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons]
    rw [Finset.sum_comm]
    calc ∑ t : Fin m → ι, ∑ a, (X 0 a * (List.ofFn fun i => X i.succ (t i)).prod)ᴴ
          * (X 0 a * (List.ofFn fun i => X i.succ (t i)).prod)
        = ∑ t : Fin m → ι, ((List.ofFn fun i => X i.succ (t i)).prod)ᴴ * (∑ a, (X 0 a)ᴴ * X 0 a)
          * (List.ofFn fun i => X i.succ (t i)).prod := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by simp only [hX 0, Matrix.mul_one]; exact ih

end QuantumInfo

namespace CSD
namespace Empirical
namespace QM
namespace QEC
namespace Steane

/-- Operators on the data block and the ancilla block together. -/
abbrev PairOp : Type :=
  Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ

/-! ### Operators on one pair -/

/-- A sum over any finite index of products on the pair `q` is an operator on the pair. -/
theorem OnPair.of_sum {q : Fin 7} {ι : Type*} [Fintype ι] (A B : ι → Matrix (Fin 2) (Fin 2) ℂ) :
    OnPair q (∑ i, gateOf q (A i) ⊗ₖ gateOf q (B i)) := by
  classical
  let e := Fintype.equivFin ι
  exact ⟨Fintype.card ι, fun k => A (e.symm k), fun k => B (e.symm k),
    (e.symm.sum_comp fun i => gateOf q (A i) ⊗ₖ gateOf q (B i)).symm⟩

theorem OnPair.zero (q : Fin 7) : OnPair q 0 :=
  ⟨0, Fin.elim0, Fin.elim0, by simp⟩

/-- The fault model is inhabited: the identity on the pair is an operator on the pair. -/
theorem onPair_one (q : Fin 7) : OnPair q 1 :=
  ⟨1, fun _ => 1, fun _ => 1, by simp [gateOf_one]⟩

theorem OnPair.add {q : Fin 7} {F G : PairOp} (hF : OnPair q F) (hG : OnPair q G) :
    OnPair q (F + G) := by
  obtain ⟨r, A, B, rfl⟩ := hF
  obtain ⟨r', A', B', rfl⟩ := hG
  have h := OnPair.of_sum (q := q) (Sum.elim A A') (Sum.elim B B')
  simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] using h

theorem OnPair.smul {q : Fin 7} {F : PairOp} (hF : OnPair q F) (c : ℂ) : OnPair q (c • F) := by
  obtain ⟨r, A, B, rfl⟩ := hF
  have h := OnPair.of_sum (q := q) (fun k => c • A k) B
  simpa only [gateOf_smul, Matrix.smul_kronecker, Finset.smul_sum] using h

/-- ★ **A product of operators on the pair is an operator on the pair.** -/
theorem OnPair.mul {q : Fin 7} {F G : PairOp} (hF : OnPair q F) (hG : OnPair q G) :
    OnPair q (F * G) := by
  obtain ⟨r, A, B, rfl⟩ := hF
  obtain ⟨r', A', B', rfl⟩ := hG
  have h := OnPair.of_sum (q := q) (fun p : Fin r × Fin r' => A p.1 * A' p.2)
    (fun p => B p.1 * B' p.2)
  simp only [gateOf_mul, Matrix.mul_kronecker_mul, Fintype.sum_prod_type] at h
  rw [Finset.sum_mul_sum]
  exact h

theorem OnPair.list_prod {q : Fin 7} : ∀ l : List PairOp, (∀ F ∈ l, OnPair q F) → OnPair q l.prod
  | [], _ => by rw [List.prod_nil]; exact onPair_one q
  | F :: l, h => by
    rw [List.prod_cons]
    exact (h F List.mem_cons_self).mul (OnPair.list_prod l fun G hG => h G (List.mem_cons_of_mem _ hG))

/-! ### The transversal `CNOT` keeps a fault on its pair -/

/-- The data half of a `CNOT`-conjugate: the entries of `A` in control row `a` and column `b`,
`Pₐ A P_b`. -/
def cnotData (a b : Fin 2) (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => if i = a ∧ j = b then A i j else 0

/-- The ancilla half: `B` with its rows shifted by `a` and its columns by `b`, `Xᵃ B Xᵇ`. -/
def cnotAnc (a b : Fin 2) (B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => B (i + a) (j + b)

/-- Conjugating by the transversal `CNOT` relabels rows and columns. -/
theorem tCNOT_conj_apply (M : PairOp) (p p' : (Fin 7 → Fin 2) × (Fin 7 → Fin 2)) :
    (tCNOT * M * tCNOT) p p' = M (extractPerm id p) (extractPerm id p') := by
  have hσ := extractPerm_involutive (H := (id : (Fin 7 → Fin 2) → (Fin 7 → Fin 2))) id_add_self
  rw [show tCNOT = permMat (extractPerm (id : (Fin 7 → Fin 2) → (Fin 7 → Fin 2))) from rfl,
    mul_permMat_apply, permMat_mul_apply hσ]

/-- ★★ **The transversal `CNOT` conjugates a product on the pair `q` into four products on the
pair**: `CNOT (A ⊗ B) CNOT = Σ_{a,b} PₐAP_b ⊗ XᵃBXᵇ` at `q`, the other six `CNOT`s cancelling. -/
theorem tCNOT_conj_kron (q : Fin 7) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    tCNOT * (gateOf q A ⊗ₖ gateOf q B) * tCNOT
      = ∑ p : Fin 2 × Fin 2, gateOf q (cnotData p.1 p.2 A) ⊗ₖ gateOf q (cnotAnc p.1 p.2 B) := by
  ext ⟨x, y⟩ ⟨x', y'⟩
  rw [tCNOT_conj_apply, Matrix.sum_apply]
  simp only [extractPerm, id_eq, Matrix.kroneckerMap_apply]
  by_cases hx : ∀ i, i ≠ q → x i = x' i
  · by_cases hy : ∀ i, i ≠ q → y i = y' i
    · have hyx : ∀ i, i ≠ q → (y + x) i = (y' + x') i := fun i hi => by
        simp only [Pi.add_apply, hx i hi, hy i hi]
      simp only [gateOf_apply_of_agree hx, gateOf_apply_of_agree hy, gateOf_apply_of_agree hyx]
      rw [Finset.sum_eq_single (x q, x' q)]
      · simp [cnotData, cnotAnc]
      · rintro ⟨a, b⟩ _ hab
        simp only [cnotData, Matrix.of_apply]
        rw [ite_eq_right fun h => hab (by rw [h.1, h.2]), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have hyx : ¬∀ i, i ≠ q → (y + x) i = (y' + x') i := fun h => hy fun i hi => by
        have h' := h i hi
        simp only [Pi.add_apply, hx i hi] at h'
        exact add_right_cancel h'
      simp [gateOf_apply_of_not_agree hy, gateOf_apply_of_not_agree hyx]
  · simp [gateOf_apply_of_not_agree hx]

/-- ★★ **The transversal `CNOT` keeps an operator on the pair `q` on the pair `q`.** -/
theorem OnPair.conj_tCNOT {q : Fin 7} {F : PairOp} (hF : OnPair q F) :
    OnPair q (tCNOT * F * tCNOT) := by
  obtain ⟨r, A, B, rfl⟩ := hF
  have h := OnPair.of_sum (q := q) (fun p : Fin r × (Fin 2 × Fin 2) => cnotData p.2.1 p.2.2 (A p.1))
    (fun p => cnotAnc p.2.1 p.2.2 (B p.1))
  rw [Fintype.sum_prod_type] at h
  rw [Matrix.mul_sum, Matrix.sum_mul]
  simp only [tCNOT_conj_kron]
  exact h

/-! ### A fault before the `CNOT` -/

/-- **Steane's extraction with `Fb` before the transversal `CNOT` and `Fa` after it**, read as `m`. -/
def readAround (Fb Fa : PairOp) (m : Fin 7 → Fin 2) : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  (ancRead m : Matrix (Fin 7 → Fin 2) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ) * Fa * tCNOT * Fb
    * (ancPrep plusAnc : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) (Fin 7 → Fin 2) ℂ)

/-- ★★ **A fault before the `CNOT` is the conjugated fault after it**: the extraction with `Fb`
before and `Fa` after is `faultReadOp` of `Fa · CNOT Fb CNOT`. -/
theorem readAround_eq (Fb Fa : PairOp) (m : Fin 7 → Fin 2) :
    readAround Fb Fa m = faultReadOp (Fa * (tCNOT * Fb * tCNOT)) m := by
  have hT : tCNOT * tCNOT = 1 := extractMat_mul_self id_add_self
  rw [readAround, faultReadOp]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc tCNOT tCNOT, hT, Matrix.one_mul]

/-! ### The readout under a Kraus family of faults -/

theorem sum_faultReadOp_conjTranspose_mul_eq (F : PairOp) :
    ∑ m, (faultReadOp F m)ᴴ * faultReadOp F m
      = (F * tCNOT
          * (ancPrep plusAnc : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) (Fin 7 → Fin 2) ℂ))ᴴ
        * (F * tCNOT
          * (ancPrep plusAnc : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) (Fin 7 → Fin 2) ℂ)) := by
  set W : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) (Fin 7 → Fin 2) ℂ := F * tCNOT * ancPrep plusAnc
  have hW : ∀ m, faultReadOp F m
      = (ancRead m : Matrix (Fin 7 → Fin 2) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ) * W := by
    intro m
    simp only [faultReadOp, W, Matrix.mul_assoc]
  have h2 : ∀ m : Fin 7 → Fin 2,
      ((ancRead m : Matrix (Fin 7 → Fin 2) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ) * W)ᴴ
        * ((ancRead m : Matrix (Fin 7 → Fin 2) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ) * W)
      = Wᴴ * ((ancRead m : Matrix (Fin 7 → Fin 2) ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) ℂ)ᴴ * ancRead m)
        * W := by
    intro m
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  simp only [hW]
  rw [Finset.sum_congr rfl fun m _ => h2 m, ← Matrix.sum_mul, ← Matrix.mul_sum,
    sum_ancRead_conjTranspose_mul, Matrix.mul_one]

/-- ★ **The readout under a trace-preserving Kraus family of faults is a complete measurement.** -/
theorem sum_faultReadOp_family {κ : Type*} [Fintype κ] {K : κ → PairOp}
    (hK : ∑ k, (K k)ᴴ * K k = 1) :
    ∑ p : κ × (Fin 7 → Fin 2), (faultReadOp (K p.1) p.2)ᴴ * faultReadOp (K p.1) p.2 = 1 := by
  set V : Matrix ((Fin 7 → Fin 2) × (Fin 7 → Fin 2)) (Fin 7 → Fin 2) ℂ := ancPrep plusAnc
  have hT : tCNOTᴴ * tCNOT = 1 := by
    rw [extractMat_conjTranspose id_add_self, extractMat_mul_self id_add_self]
  have hterm : ∀ k, (K k * tCNOT * V)ᴴ * (K k * tCNOT * V)
      = Vᴴ * (tCNOTᴴ * ((K k)ᴴ * K k) * tCNOT) * V := by
    intro k
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [Fintype.sum_prod_type]
  simp only [sum_faultReadOp_conjTranspose_mul_eq]
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Matrix.sum_mul, ← Matrix.mul_sum, ← Matrix.sum_mul,
    ← Matrix.mul_sum, hK, Matrix.mul_one, hT, Matrix.mul_one, ancPrep_conjTranspose_mul,
    sum_plusAnc_sq, one_smul]

theorem bitFaultOp_conjTranspose_mul (F : PairOp) (m : Fin 7 → Fin 2) :
    (bitFaultOp F m)ᴴ * bitFaultOp F m = (faultReadOp F m)ᴴ * faultReadOp F m := by
  rw [bitFaultOp, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (pauliMat _ _),
    pauliMat_conjTranspose_mul_self, Matrix.one_mul]

theorem phaseFaultOp_conjTranspose_mul (F : PairOp) (m : Fin 7 → Fin 2) :
    (phaseFaultOp F m)ᴴ * phaseFaultOp F m
      = hadTransversal 7 * ((faultReadOp F m)ᴴ * faultReadOp F m) * hadTransversal 7 := by
  rw [phaseFaultOp, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (pauliMat _ _),
    pauliMat_conjTranspose_mul_self, Matrix.one_mul, conjTranspose_mul, conjTranspose_mul,
    hadTransversal_conjTranspose]
  calc hadTransversal 7 * ((faultReadOp F m)ᴴ * hadTransversal 7)
        * (hadTransversal 7 * faultReadOp F m * hadTransversal 7)
      = hadTransversal 7 * (faultReadOp F m)ᴴ * (hadTransversal 7 * hadTransversal 7)
        * faultReadOp F m * hadTransversal 7 := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hadTransversal_mul_self, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem sum_bitFaultOp_family {κ : Type*} [Fintype κ] {K : κ → PairOp}
    (hK : ∑ k, (K k)ᴴ * K k = 1) :
    ∑ p : κ × (Fin 7 → Fin 2), (bitFaultOp (K p.1) p.2)ᴴ * bitFaultOp (K p.1) p.2 = 1 := by
  simp only [bitFaultOp_conjTranspose_mul]
  exact sum_faultReadOp_family hK

theorem sum_phaseFaultOp_family {κ : Type*} [Fintype κ] {K : κ → PairOp}
    (hK : ∑ k, (K k)ᴴ * K k = 1) :
    ∑ p : κ × (Fin 7 → Fin 2), (phaseFaultOp (K p.1) p.2)ᴴ * phaseFaultOp (K p.1) p.2 = 1 := by
  simp only [phaseFaultOp_conjTranspose_mul]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, sum_faultReadOp_family hK, Matrix.mul_one,
    hadTransversal_mul_self]

/-! ### Steane's method with a channel fault -/

/-- A branch of Steane's method with the fault's Kraus operator `K p.1` at an extraction location of
round `r`. -/
def channelKraus {κ : Type*} (K : κ → PairOp) (r : MethodRound) (p : κ × OutPair) :
    Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ :=
  faultyKraus (K p.1) r p.2

theorem channelKraus_tp {κ : Type*} [Fintype κ] {K : κ → PairOp} (hK : ∑ k, (K k)ᴴ * K k = 1)
    (r : MethodRound) : ∑ p, (channelKraus K r p)ᴴ * channelKraus K r p = 1 := by
  have h1 : (1 : PairOp)ᴴ * 1 = 1 := by rw [conjTranspose_one, Matrix.one_mul]
  cases r with
  | bit =>
    have hY := sum_phaseFaultOp_conjTranspose_mul h1
    simp only [phaseFaultOp_one] at hY
    have h := sum_mul_conjTranspose_mul_of_tp (sum_bitFaultOp_family hK) hY
    rw [← (Equiv.prodAssoc κ (Fin 7 → Fin 2) (Fin 7 → Fin 2)).sum_comp]
    simp only [Equiv.prodAssoc_apply, channelKraus, faultyKraus]
    exact h
  | phase =>
    have hX := sum_bitFaultOp_conjTranspose_mul h1
    simp only [bitFaultOp_one] at hX
    let e : (Fin 7 → Fin 2) × (κ × (Fin 7 → Fin 2)) ≃ κ × OutPair :=
      { toFun := fun p => (p.2.1, (p.1, p.2.2)), invFun := fun p => (p.2.1, (p.1, p.2.2)),
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    have h := sum_mul_conjTranspose_mul_of_tp hX (sum_phaseFaultOp_family hK)
    rw [← e.sum_comp]
    simp only [e, Equiv.coe_fn_mk, channelKraus, faultyKraus]
    exact h

/-- ★★ **Steane's method with a channel fault at one extraction location of round `r`**: the fault is
the Kraus family `K`, trace preserving, on data qubit `q` and ancilla qubit `q` after the transversal
`CNOT`. -/
def channelMethod {κ : Type*} [Fintype κ] (K : κ → PairOp) (hK : ∑ k, (K k)ᴴ * K k = 1)
    (r : MethodRound) : Channel (Fin 7 → Fin 2) (Fin 7 → Fin 2) (κ × OutPair) where
  kraus := channelKraus K r
  tp := channelKraus_tp hK r

/-- ★ **A one-operator family is ~~#232~~'s unitary fault.** -/
theorem channelMethod_unit {F : PairOp} (hF : Fᴴ * F = 1) (r : MethodRound) :
    (channelMethod (fun _ : Unit => F) (by rw [Fintype.sum_unique]; exact hF) r).apply
      = (faultyMethod F hF r).apply := by
  funext ρ
  rw [Channel.apply_def, Channel.apply_def, Fintype.sum_prod_type, Fintype.sum_unique]
  rfl

/-- **A channel `Kb` before the `CNOT` and a channel `Ka` after it, as one family after it**:
`(i, k) ↦ Ka k · CNOT (Kb i) CNOT`. By `readAround_eq`, its readout is the circuit with both. -/
def aroundFam {κ₁ κ₂ : Type*} (Kb : κ₁ → PairOp) (Ka : κ₂ → PairOp) (p : κ₁ × κ₂) : PairOp :=
  Ka p.2 * (tCNOT * Kb p.1 * tCNOT)

theorem aroundFam_tp {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂] {Kb : κ₁ → PairOp} {Ka : κ₂ → PairOp}
    (hb : ∑ i, (Kb i)ᴴ * Kb i = 1) (ha : ∑ k, (Ka k)ᴴ * Ka k = 1) :
    ∑ p, (aroundFam Kb Ka p)ᴴ * aroundFam Kb Ka p = 1 := by
  have hT : tCNOTᴴ = tCNOT := extractMat_conjTranspose id_add_self
  have hTT : tCNOT * tCNOT = 1 := extractMat_mul_self id_add_self
  have hX : ∑ i, (tCNOT * Kb i * tCNOT)ᴴ * (tCNOT * Kb i * tCNOT) = 1 := by
    have hterm : ∀ i, (tCNOT * Kb i * tCNOT)ᴴ * (tCNOT * Kb i * tCNOT)
        = tCNOT * ((Kb i)ᴴ * Kb i) * tCNOT := by
      intro i
      rw [conjTranspose_mul, conjTranspose_mul, hT]
      calc tCNOT * ((Kb i)ᴴ * tCNOT) * (tCNOT * Kb i * tCNOT)
          = tCNOT * (Kb i)ᴴ * (tCNOT * tCNOT) * Kb i * tCNOT := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hTT, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_mul, ← Finset.mul_sum, hb,
      Matrix.mul_one, hTT]
  have h := sum_mul_conjTranspose_mul_of_tp hX ha
  simp only [aroundFam]
  exact h

/-- ★ **Faults on the pair on both sides of the `CNOT` give a fault on the pair after it.** -/
theorem onPair_aroundFam {q : Fin 7} {κ₁ κ₂ : Type*} {Kb : κ₁ → PairOp} {Ka : κ₂ → PairOp}
    (hb : ∀ i, OnPair q (Kb i)) (ha : ∀ k, OnPair q (Ka k)) (p : κ₁ × κ₂) :
    OnPair q (aroundFam Kb Ka p) :=
  (ha p.2).mul (hb p.1).conj_tCNOT

/-! ### The faulty method is a correctable deviation -/

/-- ★★★ **Steane's method with any channel fault on the pair `q` at one extraction location is a CSS
deviation of the identity** — ~~#232~~'s `deviatesBy_faultyMethod` for channels. -/
theorem deviatesBy_channelMethod {q : Fin 7} {κ : Type} [Fintype κ] {K : κ → PairOp}
    (hK : ∑ k, (K k)ᴴ * K k = 1) (hOn : ∀ k, OnPair q (K k)) (r : MethodRound) :
    DeviatesBy steaneProj cssMix id (channelMethod K hK r).apply :=
  deviatesBy_cssMix_of_atQubit _ fun p => atQubit_faultyKraus (hOn p.1) r p.2

/-- ★★★ **And with faults on both sides of the `CNOT`**: a channel `Kb` on the pair before it and a
channel `Ka` on the pair after it. -/
theorem deviatesBy_channelMethod_around {q : Fin 7} {κ₁ κ₂ : Type} [Fintype κ₁] [Fintype κ₂]
    {Kb : κ₁ → PairOp} {Ka : κ₂ → PairOp} (hb : ∑ i, (Kb i)ᴴ * Kb i = 1)
    (ha : ∑ k, (Ka k)ᴴ * Ka k = 1) (hOnb : ∀ i, OnPair q (Kb i)) (hOna : ∀ k, OnPair q (Ka k))
    (r : MethodRound) :
    DeviatesBy steaneProj cssMix id (channelMethod (aroundFam Kb Ka) (aroundFam_tp hb ha) r).apply :=
  deviatesBy_channelMethod _ (onPair_aroundFam hOnb hOna) r

/-- ★★ **The next recovery removes a channel fault.** -/
theorem methodRecovery_channelMethod {q : Fin 7} {κ : Type} [Fintype κ] {K : κ → PairOp}
    (hK : ∑ k, (K k)ᴴ * K k = 1) (hOn : ∀ k, OnPair q (K k)) (r : MethodRound)
    {ρ : Matrix (Fin 7 → Fin 2) (Fin 7 → Fin 2) ℂ} (hρ : IsCodeState steaneProj ρ) :
    methodRecovery.apply ((channelMethod K hK r).apply ρ) = ρ := by
  obtain ⟨E, hE, h⟩ := deviatesBy_channelMethod hK hOn r ρ hρ
  rw [h, id, isRecovery_methodRecovery_cssMix E hE ρ hρ]

/-! ### Faults under a pattern -/

/-- An ordered product whose factors are all `1` is `1`. -/
theorem prod_ofFn_eq_one {M : Type*} [Monoid M] {m : ℕ} (f : Fin m → M) (h : ∀ j, f j = 1) :
    (List.ofFn f).prod = 1 := by
  rw [show f = fun _ => 1 from funext h, List.ofFn_const, List.prod_replicate, one_pow]

/-- **One extraction location under the pattern, as a Kraus family on `Option κ`**: the fault's
operators `K k` at `some k` if the location is faulty, the identity at `none` if it is not. -/
def locFam {α κ : Type*} [MonoidWithZero α] (K : κ → α) (b : Bool) : Option κ → α
  | none => if b then 0 else 1
  | some k => if b then K k else 0

theorem locFam_tp {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ] {K : κ → Matrix n n ℂ}
    (hK : ∑ k, (K k)ᴴ * K k = 1)
    (b : Bool) : ∑ o, (locFam K b o)ᴴ * locFam K b o = 1 := by
  rw [Fintype.sum_option]
  cases b <;> simp [locFam, hK]

theorem onPair_locFam {q : Fin 7} {κ : Type*} {K : κ → PairOp} (hOn : ∀ k, OnPair q (K k))
    (b : Bool) : ∀ o, OnPair q (locFam K b o)
  | none => by cases b <;> simp [locFam, OnPair.zero, onPair_one]
  | some k => by cases b <;> simp [locFam, OnPair.zero, hOn k]

/-- A location without a fault is on every pair. -/
theorem onPair_locFam_false (q : Fin 7) {κ : Type*} (K : κ → PairOp) :
    ∀ o, OnPair q (locFam K false o)
  | none => by simp [locFam, onPair_one]
  | some _ => by simp [locFam, OnPair.zero]

/-- **The faults of one round under a pattern**, in branch `s`: the ordered product over the seven
pairs of their locations' Kraus operators. -/
def roundKraus {α κ : Type*} [MonoidWithZero α] (K : Fin 7 → κ → α) (b : Fin 7 → Bool)
    (s : Fin 7 → Option κ) : α :=
  (List.ofFn fun q => locFam (K q) (b q) (s q)).prod

theorem roundKraus_tp {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]
    {K : Fin 7 → κ → Matrix n n ℂ}
    (hK : ∀ q, ∑ k, (K q k)ᴴ * K q k = 1) (b : Fin 7 → Bool) :
    ∑ s, (roundKraus K b s)ᴴ * roundKraus K b s = 1 :=
  sum_prod_ofFn_conjTranspose_mul (fun q => locFam (K q) (b q)) fun q => locFam_tp (hK q) (b q)

/-- With no faulty pair the round is the identity in the branch `none` everywhere… -/
theorem roundKraus_none {α κ : Type*} [MonoidWithZero α] (K : Fin 7 → κ → α) :
    roundKraus K (fun _ => false) (fun _ => none) = 1 := by
  unfold roundKraus
  exact prod_ofFn_eq_one _ fun q => by simp [locFam]

/-- …and zero in every other branch. -/
theorem roundKraus_none_of_ne {α κ : Type*} [MonoidWithZero α] (K : Fin 7 → κ → α)
    {s : Fin 7 → Option κ}
    (h : s ≠ fun _ => none) : roundKraus K (fun _ => false) s = 0 := by
  obtain ⟨q, hq⟩ := Function.ne_iff.1 h
  obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 hq
  have h0 : locFam (K q) ((fun _ => false) q) (s q) = 0 := by simp [locFam, hk]
  unfold roundKraus
  exact List.prod_eq_zero (List.mem_ofFn.2 ⟨q, h0⟩)

/-- With one faulty pair `q`, every branch of the round is an operator on the pair `q`. -/
theorem onPair_roundKraus_single {κ : Type*} {K : Fin 7 → κ → PairOp} {q : Fin 7}
    (hOn : ∀ k, OnPair q (K q k)) (s : Fin 7 → Option κ) :
    OnPair q (roundKraus K (fun q' => decide (q' = q)) s) := by
  refine OnPair.list_prod _ fun F hF => ?_
  obtain ⟨q', rfl⟩ := List.mem_ofFn.1 hF
  by_cases h : q' = q
  · subst h
    simpa only [decide_true] using onPair_locFam hOn true (s q')
  · simpa only [decide_eq_false h] using onPair_locFam_false q (K q') (s q')

theorem faultReadOp_zero (m : Fin 7 → Fin 2) : faultReadOp 0 m = 0 := by
  simp [faultReadOp]

theorem bitFaultOp_zero (m : Fin 7 → Fin 2) : bitFaultOp 0 m = 0 := by
  rw [bitFaultOp, faultReadOp_zero, Matrix.mul_zero]

theorem phaseFaultOp_zero (m : Fin 7 → Fin 2) : phaseFaultOp 0 m = 0 := by
  rw [phaseFaultOp, faultReadOp_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_zero]

end Steane
end QEC
end QM
end Empirical
end CSD

end

end
