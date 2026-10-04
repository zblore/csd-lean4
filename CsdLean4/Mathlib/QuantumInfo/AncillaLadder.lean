/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Clifford

/-!
# The ancilla ladder: how a single fault propagates, and why the cat state is needed

**Category:** 1-Mathlib (CSD-free). BACKLOG #95, split out of #62 (c2).

[`SyndromeExtraction.lean`](SyndromeExtraction.lean) (#94) built syndrome extraction as a circuit and
left one thing open in its header: the ancilla is **one unverified block**, so nothing bounds how far a
single ancilla fault spreads into the data. This file proves what that costs, and what the cat state
buys, in the Heisenberg picture `Clifford.lean` already supports.

## The mechanism, and the two architectures

A `CNOT` ladder that measures a weight-`w` check can be wired two ways:

* **shared target** — all `w` data qubits are controls onto **one** ancilla qubit. Cheap, and it is
  what #94's gadget does;
* **cat state** — `w` ancilla qubits, each the target of **one** `CNOT`, prepared in
  `|0…0⟩ + |1…1⟩` so the parity of their measurements is the check value. Expensive, and it is what
  fault-tolerant syndrome extraction actually uses.

`cnotGate_conj_pauliOp` says a `CNOT` propagates `X` from control to target and `Z` from **target to
control**. So the dangerous direction for a data→ancilla ladder is a `Z` fault on the *ancilla*, and
the two architectures differ exactly there — which is the content below.

## What is proved

* `laddGate anc L` — the ladder with controls `L` and shared target `anc`, built from `cnotGate`, with
  ★ `cnotGate_laddGate_comm` (the `CNOT`s commute: same target, controls off the target) and
  ★ `laddGate_involutive`;
* ★★★ `laddGate_conj_pauliOp` — **the ladder's Heisenberg action**: it conjugates every Pauli to a
  Pauli with no phase, with the `X` and `Z` label maps `xLadd`, `zLadd` given as explicit folds of
  `cnotFlip`. This is `Clifford.lean`'s one-gate theorem telescoped along the ladder, by induction;
* ★ `zLadd_apply_target` — the invariant that makes the computation work: the ladder never changes the
  target's own `Z` bit;
* ★★★ `zLadd_bitAt_target_apply` — **the shared-target cost**: a single `Z` fault on the shared ancilla
  comes out as a `Z` on the ancilla **and on every control in the ladder**. With
  ★★★ `dataSupport_zLadd_bitAt_target` and ★★ `card_dataSupport_zLadd_bitAt_target`, the data-side
  support is exactly the control list, of size `L.length`: **one fault, `w` data errors**;
* ★★ `zLadd_singleton_apply` and ★★ `card_dataSupport_zLadd_singleton` — **the cat-state cost**: with
  one control per ancilla qubit the same fault reaches exactly **one** data qubit. The contrast is the
  whole justification for the cat state;
* `IsCat`, `catVerify` — the cat labels (the constant strings) and the pairwise-agreement
  verification, with ★ `catVerify_eq_zero_iff` (verification passes exactly on cat labels) and
  ★★ `not_isCat_add_bitAt` / ★★ `catVerify_ne_zero_of_single_flip` — **a single bit-flip during
  preparation is flagged**, for every register of at least two qubits.

Together: a single ancilla fault either lands on one data qubit (cat architecture) or is caught by
verification — and with the shared ancilla of #94 it lands on `w` of them, which for a weight-4 check
is past what a distance-3 code can correct.

## Honest scope

⚠️ **No fault model, no probabilities, no threshold.** "One fault" here means one Pauli inserted at one
place, and the conclusions are **support** statements about where it comes out. Nothing here counts
fault locations, assigns them probabilities, or proves any threshold; that is #96 and #97.

⚠️ **The cat state is not prepared here.** `IsCat` describes the labels a cat state is supported on and
`catVerify` is the parity check on them; no preparation circuit is built, no superposition is
constructed, and the `X`-basis measurement whose parity gives the check value is **not** assembled. So
this file proves the *propagation* and *flagging* content of "verified ancilla", not a verified-ancilla
gadget.

⚠️ **`Z` faults on the ancilla only.** That is the dangerous direction for a data→ancilla ladder, and
it is the one the architectures differ on; `X` faults on the ancilla propagate *away* from the data
(`xLadd` moves control bits into the target) and faults on the data are not the ancilla's business.
No claim is made about a general fault at a general location.

⚠️ **Weight is not correctability.** `card_dataSupport_zLadd_bitAt_target` says the induced data error
has weight `L.length`; that a weight-4 error is *not corrected* by a distance-3 code is not proved
here — what follows is only that the distance-3 guarantee does not apply to it. The weight-1 case is
the one the corpus's recovery theorems cover.

⚠️ **One register, one check.** The data and the ancilla live in the same `Fin n` register and one
ladder is analysed; nothing composes rounds, interleaves gates, or tracks a second check.

⚠️ **No Steane instance is built here.** The theorems are stated for an arbitrary control list, so a
Hamming row's weight-4 support is one of their instances, but the embedding of seven data qubits and
an ancilla block into a single register is **not** written down and no Steane-specific number is
proved in this file.

## References

`Mathlib/QuantumInfo/Clifford.lean` (`cnotGate_conj_pauliOp`, `cnotFlip`);
`Mathlib/QuantumInfo/SyndromeExtraction.lean` (#94, whose unverified ancilla this prices);
`specs/BACKLOG.md` #95, #94, #96, #97, #62; `specs/future-work.md`.
-/

@[expose] public section

namespace QuantumInfo

variable {n : ℕ}

/-! ### Single-bit labels -/

/-- The label with a single bit set — one Pauli on one qubit. -/
def bitAt (j : Fin n) : Fin n → Fin 2 := fun i => if i = j then 1 else 0

@[simp] theorem bitAt_self (j : Fin n) : bitAt j j = 1 := by simp [bitAt]

theorem bitAt_of_ne {i j : Fin n} (h : i ≠ j) : bitAt j i = 0 := by simp [bitAt, h]

/-! ### The ladder -/

/-- **The ancilla ladder**: a `CNOT` from each control in `L` into the shared target `anc`. -/
noncomputable def laddGate (anc : Fin n) : List (Fin n) → QReg n → QReg n
  | [], ψ => ψ
  | d :: L, ψ => cnotGate d anc (laddGate anc L ψ)

@[simp] theorem laddGate_nil (anc : Fin n) (ψ : QReg n) : laddGate anc [] ψ = ψ := rfl

@[simp] theorem laddGate_cons (anc d : Fin n) (L : List (Fin n)) (ψ : QReg n) :
    laddGate anc (d :: L) ψ = cnotGate d anc (laddGate anc L ψ) := rfl

/-- The `X` label map of the ladder: each control's bit is added into the target. -/
def xLadd (anc : Fin n) : List (Fin n) → (Fin n → Fin 2) → (Fin n → Fin 2)
  | [], a => a
  | d :: L, a => cnotFlip d anc (xLadd anc L a)

/-- The `Z` label map of the ladder: the target's bit is added into each control. **This** is the
direction that costs. -/
def zLadd (anc : Fin n) : List (Fin n) → (Fin n → Fin 2) → (Fin n → Fin 2)
  | [], b => b
  | d :: L, b => cnotFlip anc d (zLadd anc L b)

@[simp] theorem zLadd_nil (anc : Fin n) (b : Fin n → Fin 2) : zLadd anc [] b = b := rfl

@[simp] theorem zLadd_cons (anc d : Fin n) (L : List (Fin n)) (b : Fin n → Fin 2) :
    zLadd anc (d :: L) b = cnotFlip anc d (zLadd anc L b) := rfl

/-! ### The ladder's `CNOT`s commute -/

/-- Two `CNOT`s with the same target and controls off it commute, at the label level. -/
theorem cnotFlip_comm_of_target {d₁ d₂ anc : Fin n} (h₁ : d₁ ≠ anc) (h₂ : d₂ ≠ anc)
    (z : Fin n → Fin 2) :
    cnotFlip d₂ anc (cnotFlip d₁ anc z) = cnotFlip d₁ anc (cnotFlip d₂ anc z) := by
  funext i
  by_cases hi : i = anc
  · subst hi
    rw [cnotFlip_apply_k, cnotFlip_apply_k, cnotFlip_apply_k, cnotFlip_apply_k,
      cnotFlip_apply_ne _ _ _ h₁, cnotFlip_apply_ne _ _ _ h₂]
    exact add_right_comm _ _ _
  · rw [cnotFlip_apply_ne _ _ _ hi, cnotFlip_apply_ne _ _ _ hi,
      cnotFlip_apply_ne _ _ _ hi, cnotFlip_apply_ne _ _ _ hi]

/-- ★ **A single `CNOT` of the ladder commutes with the rest of it.** -/
theorem cnotGate_laddGate_comm (anc : Fin n) (L : List (Fin n)) (hL : ∀ d ∈ L, d ≠ anc)
    {d : Fin n} (hd : d ≠ anc) (ψ : QReg n) :
    cnotGate d anc (laddGate anc L ψ) = laddGate anc L (cnotGate d anc ψ) := by
  induction L with
  | nil => rfl
  | cons e L ih =>
      have he : e ≠ anc := hL e (List.mem_cons_self ..)
      have hL' : ∀ c ∈ L, c ≠ anc := fun c hc => hL c (List.mem_cons_of_mem e hc)
      rw [laddGate_cons, laddGate_cons, ← ih hL']
      ext z
      rw [cnotGate_apply, cnotGate_apply, cnotGate_apply, cnotGate_apply,
        cnotFlip_comm_of_target hd he]

/-- ★ The ladder is self-inverse. -/
theorem laddGate_involutive (anc : Fin n) (L : List (Fin n)) (hL : ∀ d ∈ L, d ≠ anc) (ψ : QReg n) :
    laddGate anc L (laddGate anc L ψ) = ψ := by
  induction L with
  | nil => rfl
  | cons d L ih =>
      have hd : d ≠ anc := hL d (List.mem_cons_self ..)
      have hL' : ∀ c ∈ L, c ≠ anc := fun c hc => hL c (List.mem_cons_of_mem d hc)
      rw [laddGate_cons, laddGate_cons, cnotGate_laddGate_comm anc L hL' hd,
        ← laddGate_cons, laddGate_cons, cnotGate_cnotGate d anc hd, ih hL']

/-! ### The ladder's Heisenberg action -/

/-- ★★★ **The ladder conjugates every Pauli to a Pauli, with no phase**, and the label maps are the
folds `xLadd`, `zLadd`. `Clifford.lean`'s one-gate theorem, telescoped along the ladder. -/
theorem laddGate_conj_pauliOp (anc : Fin n) :
    ∀ (L : List (Fin n)), (∀ d ∈ L, d ≠ anc) → ∀ (a b : Fin n → Fin 2) (ψ : QReg n),
      laddGate anc L (pauliOp a b (laddGate anc L ψ))
        = pauliOp (xLadd anc L a) (zLadd anc L b) ψ
  | [], _, _, _, _ => rfl
  | d :: L, hL, a, b, ψ => by
      have hd : d ≠ anc := hL d (List.mem_cons_self ..)
      have hL' : ∀ c ∈ L, c ≠ anc := fun c hc => hL c (List.mem_cons_of_mem d hc)
      rw [laddGate_cons, laddGate_cons, cnotGate_laddGate_comm anc L hL' hd ψ,
        laddGate_conj_pauliOp anc L hL' a b (cnotGate d anc ψ),
        cnotGate_conj_pauliOp d anc hd]
      rfl

/-! ### What one `Z` fault on the shared ancilla costs -/

/-- ★ **The ladder never changes the target's own `Z` bit.** The invariant behind every computation
below. -/
theorem zLadd_apply_target (anc : Fin n) (L : List (Fin n)) (hL : ∀ d ∈ L, d ≠ anc)
    (b : Fin n → Fin 2) : zLadd anc L b anc = b anc := by
  induction L with
  | nil => rfl
  | cons d L ih =>
      have hd : d ≠ anc := hL d (List.mem_cons_self ..)
      have hL' : ∀ c ∈ L, c ≠ anc := fun c hc => hL c (List.mem_cons_of_mem d hc)
      rw [zLadd_cons, cnotFlip_apply_ne _ _ _ (Ne.symm hd), ih hL']

/-- ★★★ **The shared-target cost.** A single `Z` fault on the shared ancilla comes out of the ladder
as a `Z` on the ancilla *and on every control*: with `w` controls, one fault becomes `w` data
errors. -/
theorem zLadd_bitAt_target_apply (anc : Fin n) (L : List (Fin n)) (hL : ∀ d ∈ L, d ≠ anc)
    (hnd : L.Nodup) (i : Fin n) :
    zLadd anc L (bitAt anc) i = if i = anc then 1 else if i ∈ L then 1 else 0 := by
  induction L with
  | nil =>
      by_cases hi : i = anc
      · subst hi; simp
      · simp [bitAt_of_ne hi, hi]
  | cons d L ih =>
      have hd : d ≠ anc := hL d (List.mem_cons_self ..)
      have hL' : ∀ c ∈ L, c ≠ anc := fun c hc => hL c (List.mem_cons_of_mem d hc)
      have hnd' : L.Nodup := (List.nodup_cons.1 hnd).2
      have hdL : d ∉ L := (List.nodup_cons.1 hnd).1
      rw [zLadd_cons]
      by_cases hid : i = d
      · subst hid
        rw [cnotFlip_apply_k, zLadd_apply_target anc L hL', ih hL' hnd',
          if_neg hd, if_neg hdL]
        simp [hd]
      · rw [cnotFlip_apply_ne _ _ _ hid, ih hL' hnd']
        by_cases hi : i = anc
        · subst hi; simp
        · rw [if_neg hi, if_neg hi]
          by_cases hiL : i ∈ L
          · rw [if_pos hiL, if_pos (List.mem_cons_of_mem d hiL)]
          · rw [if_neg hiL, if_neg]
            simpa [hid] using hiL

/-- The data-side support of the propagated fault: the qubits other than the ancilla that carry a
`Z`. -/
def dataSupport (anc : Fin n) (b : Fin n → Fin 2) : Finset (Fin n) :=
  Finset.univ.filter fun i => i ≠ anc ∧ b i = 1

/-- ★★★ **The data-side support is exactly the control list.** -/
theorem dataSupport_zLadd_bitAt_target (anc : Fin n) (L : List (Fin n)) (hL : ∀ d ∈ L, d ≠ anc)
    (hnd : L.Nodup) : dataSupport anc (zLadd anc L (bitAt anc)) = L.toFinset := by
  ext i
  rw [dataSupport, Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨-, hne, hval⟩
    rw [zLadd_bitAt_target_apply anc L hL hnd i, if_neg hne] at hval
    by_cases hiL : i ∈ L
    · exact hiL
    · rw [if_neg hiL] at hval
      exact absurd hval (by decide)
  · intro hiL
    refine ⟨Finset.mem_univ i, hL i hiL, ?_⟩
    rw [zLadd_bitAt_target_apply anc L hL hnd i, if_neg (hL i hiL), if_pos hiL]

/-- ★★ **One fault, `w` data errors**, where `w` is the weight of the check the ladder measures. -/
theorem card_dataSupport_zLadd_bitAt_target (anc : Fin n) (L : List (Fin n))
    (hL : ∀ d ∈ L, d ≠ anc) (hnd : L.Nodup) :
    (dataSupport anc (zLadd anc L (bitAt anc))).card = L.length := by
  rw [dataSupport_zLadd_bitAt_target anc L hL hnd, List.toFinset_card_of_nodup hnd]

/-! ### What the cat architecture costs instead -/

/-- ★★ **The cat-state cost.** With one control per ancilla qubit the same fault reaches the ancilla
and exactly one data qubit. -/
theorem zLadd_singleton_apply {anc d : Fin n} (h : d ≠ anc) (i : Fin n) :
    zLadd anc [d] (bitAt anc) i = if i = anc then 1 else if i = d then 1 else 0 := by
  rw [zLadd_bitAt_target_apply anc [d] (by simpa using h) (by simp) i]
  by_cases hi : i = anc
  · simp [hi]
  · simp [hi]

/-- ★★ **One fault, one data error** — the contrast that justifies the cat state. -/
theorem card_dataSupport_zLadd_singleton {anc d : Fin n} (h : d ≠ anc) :
    (dataSupport anc (zLadd anc [d] (bitAt anc))).card = 1 := by
  rw [card_dataSupport_zLadd_bitAt_target anc [d] (by simpa using h) (by simp)]
  rfl

/-! ### The cat labels and their verification -/

/-- The labels a cat state is supported on: the constant strings. -/
def IsCat (z : Fin n → Fin 2) : Prop := ∀ i j, z i = z j

theorem isCat_const (v : Fin 2) : IsCat (fun _ : Fin n => v) := fun _ _ => rfl

/-- **The verification measurement**: the pairwise agreement of the ancilla bits, as a label. It
vanishes exactly on the cat labels. -/
def catVerify [NeZero n] (z : Fin n → Fin 2) : Fin n → Fin 2 := fun i => z i + z 0

/-- ★ **Verification passes exactly on the cat labels.** -/
theorem catVerify_eq_zero_iff [NeZero n] (z : Fin n → Fin 2) :
    catVerify z = 0 ↔ IsCat z := by
  constructor
  · intro h i j
    have hi : z i + z 0 = 0 := by simpa [catVerify] using congrFun h i
    have hj : z j + z 0 = 0 := by simpa [catVerify] using congrFun h j
    revert hi hj
    generalize z i = x
    generalize z j = y
    generalize z 0 = w
    revert x y w
    decide
  · intro h
    funext i
    rw [catVerify, h i 0]
    exact (by decide : ∀ x : Fin 2, x + x = 0) (z 0)

/-- ★★ **A single bit-flip takes a cat label off the cat set** — on any register of at least two
qubits. -/
theorem not_isCat_add_bitAt {z : Fin n → Fin 2} (hz : IsCat z) {j i : Fin n} (hij : i ≠ j) :
    ¬ IsCat (z + bitAt j) := by
  intro h
  have h1 : (z + bitAt j) i = z i := by
    simp only [Pi.add_apply, bitAt_of_ne hij, add_zero]
  have h2 : (z + bitAt j) j = z j + 1 := by
    simp only [Pi.add_apply, bitAt_self]
  have h3 : z i = z j + 1 := by rw [← h1, ← h2]; exact h i j
  rw [hz i j] at h3
  revert h3
  generalize z j = x
  revert x
  decide

/-- ★★ **So a single preparation bit-flip is flagged.** The verification measurement is nonzero on
it, which is the content of "verified ancilla": one fault inside the preparation either lands on one
data qubit or is caught. -/
theorem catVerify_ne_zero_of_single_flip [NeZero n] {z : Fin n → Fin 2} (hz : IsCat z) {j i : Fin n}
    (hij : i ≠ j) : catVerify (z + bitAt j) ≠ 0 := by
  intro h
  exact not_isCat_add_bitAt hz hij ((catVerify_eq_zero_iff _).1 h)

end QuantumInfo

end
