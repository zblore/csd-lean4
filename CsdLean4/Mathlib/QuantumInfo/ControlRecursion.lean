/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.ControlledSingle

/-!
# `C^k(U)` from `CNOT`s and single-qubit gates: the control-count recursion

**Category:** 1-Mathlib (CSD-free; staged for upstream). BACKLOG #85, part (e3) of `R-005`
(`specs/magic-plan.md`, "The split"); it closes the original row #72, whose other pieces are
`ControlledGate.lean` (#83) and `EulerDecomposition.lean` with `ControlledSingle.lean` (#84).

★★ `ctrlSetOf_mem_closure`: **a gate with any number of controls, on any control pattern, is a
product of `CNOT`s and single-qubit gates.** Nielsen–Chuang Figure 4.10, with no work qubits: the
ancilla-free route is forced, because the work-qubit ladder is not a matrix identity (it reproduces
`C^k(U)` only on the sector where the work qubits are `0`, and #73 consumes an exact product).

Two ingredients, and both are new algebra rather than bookkeeping.

**The pattern costs nothing.** Conjugating by one `X` on a control qubit flips that control value
(★ `xGate_conj_ctrlSet`), so only the *number* of controls matters. The mechanism is that `X` on
qubit `a` is a permutation matrix, and multiplying by it relabels (`xGate_mul_apply`,
`mul_xGate_apply`).

**The recursion needs two target qubits at once.** `C(V)` on the target and `C^{k-1}(X)` on the last
control act on different qubits, so #84's one-control algebra does not reach it. `pairSet` is the
family of gates that act by a `4 × 4` block on a *pair* of qubits — by one block on the labels
matching the pattern on the control set, by another on the rest — and it is closed under products,
blockwise in each branch (★★ `pairSet_mul`, through a four-element collapse). Every gate of the
recursion is one of them, so ★★ `ctrlSetOf_insert` reduces to two `4 × 4` identities, which
`diagBlock` and `flipBlock` settle in three rewrites: conjugating a block-diagonal gate by the flip
swaps its two blocks, and

`diag(1, V) · X · diag(1, V*) · X · diag(V, V) = diag(V* V, V V) = diag(1, U)` when `V² = U`,

while on the labels where the controls do not match the same product is `diag(1, V) · diag(1, V*)`,
the identity. The square root `V` comes from `Euler.exists_sqrt`.

* `flipBit`, `flipAt`, `xGate_apply`, `xGate_mul_apply`, `mul_xGate_apply`,
  ★ `xGate_conj_ctrlSet`;
* `diagBlock`, `flipBlock`, `diagBlock_apply_of_fst_eq`, `diagBlock_apply_of_fst_ne`,
  `flipBlock_apply_of_snd_eq`, `flipBlock_apply_of_snd_ne`, `diagBlock_mul`, `diagBlock_one`,
  ★ `flipBlock_conj_diagBlock`, ★ `diagBlock_five`;
* `pairSet`, `sum_collapse_pair`, ★★ `pairSet_mul`;
* `ctrlSetOf`, `pairSet_eq_ctrlOf`, `pairSet_eq_ctrlSetOf_fst`, `pairSet_eq_ctrlSetOf_snd`,
  `pairSet_eq_ctrlSetOf_insert`, ★★ `ctrlSetOf_insert`;
* `elementary`, `xGate_mem_elementary`, `ctrlOf_mem_closure`, ★★ `ctrlSetOf_mem_closure`,
  ★★ `ctrlGateOf_mem_closure`.

## Honest scope

⚠️ This is an exact product identity, not a gate count: the recursion is proved, and the number of
elementary gates it produces is not claimed (that is BACKLOG #74, deliberately not claimed).
⚠️ Nothing here *approximates* a gate; the single-qubit gates in the product are exact. Approximating
them by Clifford+T words is BACKLOG #81.

References: M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information* §4.3,
Figures 4.8 and 4.10; `specs/magic-plan.md`; `specs/BACKLOG.md` #85, #72, #73;
`specs/future-work.md`.
-/

@[expose] public section

open Matrix

namespace QuantumInfo

namespace Controlled

open TwoLevel MultiControlled Euler

variable {m : ℕ}

/-! ### The bit flip as a relabelling -/

/-- The other bit. -/
def flipBit (b : Fin 2) : Fin 2 := if b = 0 then 1 else 0

@[simp] theorem flipBit_flipBit (b : Fin 2) : flipBit (flipBit b) = b := by
  revert b
  decide

theorem flipBit_ne (b : Fin 2) : flipBit b ≠ b := by
  revert b
  decide

theorem eq_flipBit_of_ne {b c : Fin 2} (h : b ≠ c) : c = flipBit b := by
  revert b c
  decide

/-- The label with the `a`-th bit flipped. -/
def flipAt (a : Fin m) (k : Fin m → Fin 2) : Fin m → Fin 2 :=
  Function.update k a (flipBit (k a))

@[simp] theorem flipAt_apply_self (a : Fin m) (k : Fin m → Fin 2) :
    flipAt a k a = flipBit (k a) := by
  rw [flipAt, Function.update_self]

theorem flipAt_apply_of_ne {a i : Fin m} (h : i ≠ a) (k : Fin m → Fin 2) :
    flipAt a k i = k i := by
  rw [flipAt, Function.update_of_ne h]

@[simp] theorem flipAt_flipAt (a : Fin m) (k : Fin m → Fin 2) : flipAt a (flipAt a k) = k := by
  funext i
  by_cases hi : i = a
  · subst hi
    rw [flipAt_apply_self, flipAt_apply_self, flipBit_flipBit]
  · rw [flipAt_apply_of_ne hi, flipAt_apply_of_ne hi]

theorem flipAt_agree_iff {a j : Fin m} {k l : Fin m → Fin 2} :
    (∀ i, i ≠ j → flipAt a k i = flipAt a l i) ↔ ∀ i, i ≠ j → k i = l i := by
  constructor
  · intro h i hi
    by_cases hia : i = a
    · subst hia
      have h1 := h i hi
      rw [flipAt_apply_self, flipAt_apply_self] at h1
      have h2 := congrArg flipBit h1
      rwa [flipBit_flipBit, flipBit_flipBit] at h2
    · rw [← flipAt_apply_of_ne hia k, ← flipAt_apply_of_ne hia l]
      exact h i hi
  · intro h i hi
    by_cases hia : i = a
    · subst hia
      rw [flipAt_apply_self, flipAt_apply_self, h i hi]
    · rw [flipAt_apply_of_ne hia, flipAt_apply_of_ne hia]
      exact h i hi

theorem eq_flipAt_iff {a : Fin m} {k l : Fin m → Fin 2} :
    l = flipAt a k ↔ (∀ i, i ≠ a → k i = l i) ∧ k a ≠ l a := by
  constructor
  · intro h
    refine ⟨fun i hi => by rw [h, flipAt_apply_of_ne hi], ?_⟩
    rw [h, flipAt_apply_self]
    exact fun hc => flipBit_ne (k a) hc.symm
  · intro ⟨hag, hne⟩
    funext i
    by_cases hi : i = a
    · subst hi
      rw [flipAt_apply_self, eq_flipBit_of_ne hne]
    · rw [flipAt_apply_of_ne hi]
      exact (hag i hi).symm

/-- **The bit flip is a permutation matrix.** -/
theorem xGate_apply (a : Fin m) (k l : Fin m → Fin 2) :
    xGate a k l = if l = flipAt a k then 1 else 0 := by
  by_cases hag : ∀ i, i ≠ a → k i = l i
  · rw [xGate, singleGate, ctrlSet_apply_of_ctrl hag (by simp), blockEntry]
    by_cases hka : k a = l a
    · rw [if_neg (fun h => (eq_flipAt_iff.mp h).2 hka)]
      rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (k a) with h | h <;>
        rw [h] at hka ⊢ <;> rw [← hka] <;> simp
    · rw [if_pos (eq_flipAt_iff.mpr ⟨hag, hka⟩)]
      rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (k a) with h | h <;>
        rw [h] at hka ⊢ <;> rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (l a) with h' | h' <;>
        rw [h'] at hka ⊢ <;> simp_all
  · rw [xGate, singleGate, ctrlSet_apply_of_not_agree hag, if_neg]
    intro h
    exact hag (eq_flipAt_iff.mp h).1

theorem xGate_mul_apply (a : Fin m) (G : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ)
    (k l : Fin m → Fin 2) : (xGate a * G) k l = G (flipAt a k) l := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (flipAt a k)]
  · rw [xGate_apply, if_pos rfl, one_mul]
  · intro p _ hp
    rw [xGate_apply, if_neg hp, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mul_xGate_apply (a : Fin m) (G : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ)
    (k l : Fin m → Fin 2) : (G * xGate a) k l = G k (flipAt a l) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (flipAt a l)]
  · rw [xGate_apply, flipAt_flipAt, if_pos rfl, mul_one]
  · intro p _ hp
    rw [xGate_apply, if_neg, mul_zero]
    intro hl
    exact hp (by rw [hl, flipAt_flipAt])
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- ★ **Conjugating by one `X` on a control qubit flips that control value**, so only the number of
controls matters, never the pattern. -/
theorem xGate_conj_ctrlSet {S : Finset (Fin m)} {j u : Fin m} (hju : j ≠ u)
    (pat : Fin m → Fin 2) (a b c d : ℂ) :
    xGate u * ctrlSet S j pat a b c d * xGate u
      = ctrlSet S j (Function.update pat u (flipBit (pat u))) a b c d := by
  ext k l
  rw [mul_xGate_apply, xGate_mul_apply]
  have hpat : (∀ i ∈ S, flipAt u k i = pat i)
      ↔ ∀ i ∈ S, k i = Function.update pat u (flipBit (pat u)) i := by
    constructor
    · intro h i hi
      by_cases hiu : i = u
      · subst hiu
        rw [Function.update_self]
        have h1 := h i hi
        rw [flipAt_apply_self] at h1
        have h2 := congrArg flipBit h1
        rwa [flipBit_flipBit] at h2
      · rw [Function.update_of_ne hiu, ← flipAt_apply_of_ne hiu k]
        exact h i hi
    · intro h i hi
      by_cases hiu : i = u
      · subst hiu
        rw [flipAt_apply_self]
        have h1 := h i hi
        rw [Function.update_self] at h1
        rw [h1, flipBit_flipBit]
      · rw [flipAt_apply_of_ne hiu]
        have h1 := h i hi
        rwa [Function.update_of_ne hiu] at h1
  by_cases hag : ∀ i, i ≠ j → k i = l i
  · have hag' : ∀ i, i ≠ j → flipAt u k i = flipAt u l i := flipAt_agree_iff.mpr hag
    by_cases hc : ∀ i ∈ S, flipAt u k i = pat i
    · rw [ctrlSet_apply_of_ctrl hag' hc, ctrlSet_apply_of_ctrl hag (hpat.mp hc),
        flipAt_apply_of_ne hju, flipAt_apply_of_ne hju]
    · rw [ctrlSet_apply_of_not_ctrl hag' hc,
        ctrlSet_apply_of_not_ctrl hag (fun h => hc (hpat.mpr h)),
        flipAt_apply_of_ne hju, flipAt_apply_of_ne hju]
  · rw [ctrlSet_apply_of_not_agree (fun h => hag (flipAt_agree_iff.mp h)),
      ctrlSet_apply_of_not_agree hag]

/-! ### The `4 × 4` blocks -/

/-- The block acting on the second qubit by `A` when the first carries `0` and by `B` when it
carries `1`, never changing the first. -/
def diagBlock (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => if p.1 = q.1 then (if p.1 = 0 then A else B) p.2 q.2 else 0

/-- The block that flips the first qubit and leaves the second. -/
def flipBlock : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => if p.2 = q.2 then xMat p.1 q.1 else 0

theorem diagBlock_apply_of_fst_ne {A B : Matrix (Fin 2) (Fin 2) ℂ} {p q : Fin 2 × Fin 2}
    (h : p.1 ≠ q.1) : diagBlock A B p q = 0 := by
  rw [diagBlock, if_neg h]

theorem diagBlock_apply_of_fst_eq {A B : Matrix (Fin 2) (Fin 2) ℂ} {p q : Fin 2 × Fin 2}
    (h : p.1 = q.1) : diagBlock A B p q = (if p.1 = 0 then A else B) p.2 q.2 := by
  rw [diagBlock, if_pos h]

theorem flipBlock_apply_of_snd_ne {p q : Fin 2 × Fin 2} (h : p.2 ≠ q.2) : flipBlock p q = 0 := by
  rw [flipBlock, if_neg h]

theorem flipBlock_apply_of_snd_eq {p q : Fin 2 × Fin 2} (h : p.2 = q.2) :
    flipBlock p q = xMat p.1 q.1 := by
  rw [flipBlock, if_pos h]

theorem diagBlock_mul (A B C D : Matrix (Fin 2) (Fin 2) ℂ) :
    diagBlock A B * diagBlock C D = diagBlock (A * C) (B * D) := by
  ext ⟨p1, p2⟩ ⟨q1, q2⟩
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;>
    simp [diagBlock, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

@[simp] theorem diagBlock_one : diagBlock 1 1 = 1 := by
  ext ⟨p1, p2⟩ ⟨q1, q2⟩
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;>
    simp [diagBlock]

/-- ★ Conjugating by the flip swaps the two blocks. -/
theorem flipBlock_conj_diagBlock (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    flipBlock * diagBlock A B * flipBlock = diagBlock B A := by
  ext ⟨p1, p2⟩ ⟨q1, q2⟩
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;>
    simp [diagBlock, flipBlock, xMat, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- ★ **The block identity behind the recursion.** With `V² = U`, inserting the two flips turns
three controlled gates into one controlled `U`. -/
theorem diagBlock_five {U V : Matrix (Fin 2) (Fin 2) ℂ} (hV : star V * V = 1) (hVV : V * V = U) :
    diagBlock 1 V * flipBlock * diagBlock 1 (star V) * flipBlock * diagBlock V V
      = diagBlock 1 U := by
  have hassoc : ∀ M N P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      M * flipBlock * N * flipBlock * P = M * (flipBlock * N * flipBlock) * P := by
    intro M N P
    simp only [mul_assoc]
  rw [hassoc, flipBlock_conj_diagBlock, diagBlock_mul, diagBlock_mul, one_mul, mul_one, hV, hVV]

/-! ### Gates on a pair of qubits -/

/-- The gate acting by the `4 × 4` block `M` on the pair `(u, t)` of the labels that match `pat` on
the control set `S`, and by `N` on all the others. -/
def pairSet (S : Finset (Fin m)) (u t : Fin m) (pat : Fin m → Fin 2)
    (M N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ := fun k l =>
  if (∀ i, i ≠ u → i ≠ t → k i = l i) then
    (if ∀ i ∈ S, k i = pat i then M else N) (k u, k t) (l u, l t)
  else 0

variable {S : Finset (Fin m)} {u t : Fin m} {pat : Fin m → Fin 2}

theorem pairSet_apply_of_agree {M N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    {k l : Fin m → Fin 2} (hag : ∀ i, i ≠ u → i ≠ t → k i = l i) :
    pairSet S u t pat M N k l =
      (if ∀ i ∈ S, k i = pat i then M else N) (k u, k t) (l u, l t) := by
  rw [pairSet, if_pos hag]

theorem pairSet_apply_of_not_agree {M N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    {k l : Fin m → Fin 2} (h : ¬(∀ i, i ≠ u → i ≠ t → k i = l i)) :
    pairSet S u t pat M N k l = 0 := by
  rw [pairSet, if_neg h]

/-- Every sum here collapses to the four labels that agree with `k` away from the pair. -/
theorem sum_collapse_pair (hut : u ≠ t) (k : Fin m → Fin 2) (f : (Fin m → Fin 2) → ℂ)
    (hf : ∀ p, ¬(∀ i, i ≠ u → i ≠ t → p i = k i) → f p = 0) :
    ∑ p, f p = ∑ bb : Fin 2 × Fin 2,
      f (Function.update (Function.update k u bb.1) t bb.2) := by
  classical
  have hval : ∀ bb : Fin 2 × Fin 2,
      (Function.update (Function.update k u bb.1) t bb.2) u = bb.1 ∧
      (Function.update (Function.update k u bb.1) t bb.2) t = bb.2 := by
    intro bb
    exact ⟨by rw [Function.update_of_ne hut, Function.update_self], by rw [Function.update_self]⟩
  have hinj : ∀ p ∈ (Finset.univ : Finset (Fin 2 × Fin 2)),
      ∀ q ∈ (Finset.univ : Finset (Fin 2 × Fin 2)),
      (Function.update (Function.update k u p.1) t p.2)
        = (Function.update (Function.update k u q.1) t q.2) → p = q := by
    intro p _ q _ h
    have h1 := congrFun h u
    have h2 := congrFun h t
    rw [(hval p).1, (hval q).1] at h1
    rw [(hval p).2, (hval q).2] at h2
    exact Prod.ext h1 h2
  rw [← Finset.sum_image hinj]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro p _ hp
  refine hf p fun hag => hp ?_
  refine Finset.mem_image.mpr ⟨(p u, p t), Finset.mem_univ _, ?_⟩
  funext i
  by_cases hiu : i = u
  · subst hiu
    rw [Function.update_of_ne hut, Function.update_self]
  · by_cases hit : i = t
    · subst hit
      rw [Function.update_self]
    · rw [Function.update_of_ne hit, Function.update_of_ne hiu]
      exact (hag i hiu hit).symm

/-- ★★ **Pair gates multiply blockwise, in each branch separately.** -/
theorem pairSet_mul (hut : u ≠ t) (huS : u ∉ S) (htS : t ∉ S)
    (M N M' N' : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    pairSet S u t pat M N * pairSet S u t pat M' N'
      = pairSet S u t pat (M * M') (N * N') := by
  have hneu : ∀ i ∈ S, i ≠ u := fun i hi hiu => huS (by rw [← hiu]; exact hi)
  have hnet : ∀ i ∈ S, i ≠ t := fun i hi hit => htS (by rw [← hit]; exact hi)
  ext k l
  by_cases hag : ∀ i, i ≠ u → i ≠ t → k i = l i
  · have key : ∀ bb : Fin 2 × Fin 2,
        ((∀ i ∈ S, (Function.update (Function.update k u bb.1) t bb.2) i = pat i)
          ↔ ∀ i ∈ S, k i = pat i) := by
      intro bb
      constructor
      · intro h i hi
        rw [← Function.update_of_ne (hneu i hi) bb.1 k,
          ← Function.update_of_ne (hnet i hi) bb.2 (Function.update k u bb.1)]
        exact h i hi
      · intro h i hi
        rw [Function.update_of_ne (hnet i hi), Function.update_of_ne (hneu i hi)]
        exact h i hi
    have hagp : ∀ bb : Fin 2 × Fin 2, ∀ i, i ≠ u → i ≠ t →
        k i = (Function.update (Function.update k u bb.1) t bb.2) i := by
      intro bb i hiu hit
      rw [Function.update_of_ne hit, Function.update_of_ne hiu]
    have hagl : ∀ bb : Fin 2 × Fin 2, ∀ i, i ≠ u → i ≠ t →
        (Function.update (Function.update k u bb.1) t bb.2) i = l i := by
      intro bb i hiu hit
      rw [Function.update_of_ne hit, Function.update_of_ne hiu]
      exact hag i hiu hit
    have hvu : ∀ bb : Fin 2 × Fin 2,
        (Function.update (Function.update k u bb.1) t bb.2) u = bb.1 := fun bb => by
      rw [Function.update_of_ne hut, Function.update_self]
    have hvt : ∀ bb : Fin 2 × Fin 2,
        (Function.update (Function.update k u bb.1) t bb.2) t = bb.2 := fun bb => by
      rw [Function.update_self]
    rw [Matrix.mul_apply]
    have hcol : ∑ p, pairSet S u t pat M N k p * pairSet S u t pat M' N' p l
        = ∑ bb : Fin 2 × Fin 2,
            pairSet S u t pat M N k (Function.update (Function.update k u bb.1) t bb.2) *
              pairSet S u t pat M' N' (Function.update (Function.update k u bb.1) t bb.2) l := by
      refine sum_collapse_pair hut k _ fun p hp => ?_
      rw [pairSet_apply_of_not_agree (fun hc => hp fun i hiu hit => (hc i hiu hit).symm), zero_mul]
    rw [hcol, pairSet_apply_of_agree hag, Fintype.sum_prod_type]
    by_cases hc : ∀ i ∈ S, k i = pat i
    · rw [if_pos hc, Matrix.mul_apply, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
      rw [pairSet_apply_of_agree (hagp (b, b')), pairSet_apply_of_agree (hagl (b, b')),
        if_pos hc, if_pos ((key (b, b')).mpr hc), hvu (b, b'), hvt (b, b')]
    · rw [if_neg hc, Matrix.mul_apply, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
      rw [pairSet_apply_of_agree (hagp (b, b')), pairSet_apply_of_agree (hagl (b, b')),
        if_neg hc, if_neg (fun h => hc ((key (b, b')).mp h)), hvu (b, b'), hvt (b, b')]
  · rw [pairSet_apply_of_not_agree hag, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases hp : ∀ i, i ≠ u → i ≠ t → k i = p i
    · rw [pairSet_apply_of_not_agree
        (fun hc => hag fun i hiu hit => (hp i hiu hit).trans (hc i hiu hit)), mul_zero]
    · rw [pairSet_apply_of_not_agree hp, zero_mul]

/-! ### The gates of the recursion are pair gates -/

/-- The gate `U` on qubit `j`, controlled by the set `S` on the pattern `pat`. -/
def ctrlSetOf (S : Finset (Fin m)) (j : Fin m) (pat : Fin m → Fin 2)
    (U : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ :=
  ctrlSet S j pat (U 0 0) (U 0 1) (U 1 0) (U 1 1)

theorem ctrlSetOf_apply_block {j : Fin m} {U : Matrix (Fin 2) (Fin 2) ℂ}
    {k l : Fin m → Fin 2} (hag : ∀ i, i ≠ j → k i = l i) (hc : ∀ i ∈ S, k i = pat i) :
    ctrlSetOf S j pat U k l = U (k j) (l j) := by
  rw [ctrlSetOf, ctrlSet_apply_of_ctrl hag hc, blockEntry_eq_apply, ← Matrix.eta_fin_two U]

theorem ctrlSetOf_apply_id {j : Fin m} {U : Matrix (Fin 2) (Fin 2) ℂ}
    {k l : Fin m → Fin 2} (hag : ∀ i, i ≠ j → k i = l i) (hc : ¬∀ i ∈ S, k i = pat i) :
    ctrlSetOf S j pat U k l = (1 : Matrix (Fin 2) (Fin 2) ℂ) (k j) (l j) := by
  rw [ctrlSetOf, ctrlSet_apply_of_not_ctrl hag hc, Matrix.one_apply]

theorem ctrlSetOf_apply_of_not_agree {j : Fin m} {U : Matrix (Fin 2) (Fin 2) ℂ}
    {k l : Fin m → Fin 2} (h : ¬∀ i, i ≠ j → k i = l i) : ctrlSetOf S j pat U k l = 0 := by
  rw [ctrlSetOf, ctrlSet_apply_of_not_agree h]

theorem ctrlOf_eq_ctrlSetOf (a j : Fin m) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    ctrlOf a j U = ctrlSetOf {a} j (fun _ => 1) U := rfl

theorem one_pair_apply (p q : Fin 2 × Fin 2) :
    (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) p q = if p = q then 1 else 0 :=
  Matrix.one_apply

/-- The one-control gate on the pair: the control set plays no part in it. -/
theorem pairSet_eq_ctrlOf (hut : u ≠ t) (V : Matrix (Fin 2) (Fin 2) ℂ) :
    pairSet S u t pat (diagBlock 1 V) (diagBlock 1 V) = ctrlOf u t V := by
  ext k l
  by_cases hu : k u = l u
  · by_cases hagt : ∀ i, i ≠ t → k i = l i
    · have hag : ∀ i, i ≠ u → i ≠ t → k i = l i := fun i _ hit => hagt i hit
      have hblock : (if ∀ i ∈ S, k i = pat i then diagBlock (1 : Matrix (Fin 2) (Fin 2) ℂ) V
          else diagBlock (1 : Matrix (Fin 2) (Fin 2) ℂ) V)
          = diagBlock (1 : Matrix (Fin 2) (Fin 2) ℂ) V := by
        split <;> rfl
      rw [pairSet_apply_of_agree hag, hblock, ctrlOf_eq_ctrlSetOf,
        diagBlock_apply_of_fst_eq (show ((k u, k t) : Fin 2 × Fin 2).1 = (l u, l t).1 from hu)]
      by_cases hk1 : k u = 1
      · rw [ctrlSetOf_apply_block hagt (by simpa using hk1), hk1]
        rw [if_neg (by decide : ¬((1 : Fin 2) = 0))]
      · have hk0 : k u = 0 := by
          rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (k u) with h | h
          · exact h
          · exact absurd h hk1
        rw [ctrlSetOf_apply_id hagt (by simpa using hk1), hk0, if_pos rfl]
    · rw [pairSet_apply_of_not_agree, ctrlOf_eq_ctrlSetOf, ctrlSetOf_apply_of_not_agree hagt]
      intro hag
      exact hagt fun i hit => by
        by_cases hiu : i = u
        · rw [hiu]; exact hu
        · exact hag i hiu hit
  · have hagt : ¬∀ i, i ≠ t → k i = l i := fun h => hu (h u hut)
    rw [ctrlOf_eq_ctrlSetOf, ctrlSetOf_apply_of_not_agree hagt]
    by_cases hag : ∀ i, i ≠ u → i ≠ t → k i = l i
    · rw [pairSet_apply_of_agree hag]
      split <;> exact diagBlock_apply_of_fst_ne hu
    · rw [pairSet_apply_of_not_agree hag]

/-- The multiply-controlled gate on the first qubit of the pair. -/
theorem pairSet_eq_ctrlSetOf_fst (hut : u ≠ t) :
    pairSet S u t pat flipBlock 1 = ctrlSetOf S u pat xMat := by
  ext k l
  by_cases ht : k t = l t
  · by_cases hagu : ∀ i, i ≠ u → k i = l i
    · have hag : ∀ i, i ≠ u → i ≠ t → k i = l i := fun i hiu _ => hagu i hiu
      rw [pairSet_apply_of_agree hag]
      by_cases hc : ∀ i ∈ S, k i = pat i
      · rw [if_pos hc, ctrlSetOf_apply_block hagu hc,
          flipBlock_apply_of_snd_eq (show ((k u, k t) : Fin 2 × Fin 2).2 = (l u, l t).2 from ht)]
      · rw [if_neg hc, ctrlSetOf_apply_id hagu hc, one_pair_apply, Matrix.one_apply]
        by_cases h : k u = l u
        · rw [if_pos (Prod.ext h ht), if_pos h]
        · rw [if_neg (fun hc' => h (congrArg Prod.fst hc')), if_neg h]
    · rw [pairSet_apply_of_not_agree, ctrlSetOf_apply_of_not_agree hagu]
      intro hag
      exact hagu fun i hiu => by
        by_cases hit : i = t
        · rw [hit]; exact ht
        · exact hag i hiu hit
  · have hagu : ¬∀ i, i ≠ u → k i = l i := fun h => ht (h t (Ne.symm hut))
    rw [ctrlSetOf_apply_of_not_agree hagu]
    by_cases hag : ∀ i, i ≠ u → i ≠ t → k i = l i
    · rw [pairSet_apply_of_agree hag]
      split
      · exact flipBlock_apply_of_snd_ne ht
      · rw [one_pair_apply, if_neg (fun hc => ht (congrArg Prod.snd hc))]
    · rw [pairSet_apply_of_not_agree hag]

/-- The multiply-controlled gate on the second qubit of the pair. -/
theorem pairSet_eq_ctrlSetOf_snd (hut : u ≠ t) (V : Matrix (Fin 2) (Fin 2) ℂ) :
    pairSet S u t pat (diagBlock V V) 1 = ctrlSetOf S t pat V := by
  ext k l
  by_cases hu : k u = l u
  · by_cases hagt : ∀ i, i ≠ t → k i = l i
    · have hag : ∀ i, i ≠ u → i ≠ t → k i = l i := fun i _ hit => hagt i hit
      rw [pairSet_apply_of_agree hag]
      by_cases hc : ∀ i ∈ S, k i = pat i
      · rw [if_pos hc, ctrlSetOf_apply_block hagt hc,
          diagBlock_apply_of_fst_eq (show ((k u, k t) : Fin 2 × Fin 2).1 = (l u, l t).1 from hu)]
        split <;> rfl
      · rw [if_neg hc, ctrlSetOf_apply_id hagt hc, one_pair_apply, Matrix.one_apply]
        by_cases h : k t = l t
        · rw [if_pos (Prod.ext hu h), if_pos h]
        · rw [if_neg (fun hc' => h (congrArg Prod.snd hc')), if_neg h]
    · rw [pairSet_apply_of_not_agree, ctrlSetOf_apply_of_not_agree hagt]
      intro hag
      exact hagt fun i hit => by
        by_cases hiu : i = u
        · rw [hiu]; exact hu
        · exact hag i hiu hit
  · have hagt : ¬∀ i, i ≠ t → k i = l i := fun h => hu (h u hut)
    rw [ctrlSetOf_apply_of_not_agree hagt]
    by_cases hag : ∀ i, i ≠ u → i ≠ t → k i = l i
    · rw [pairSet_apply_of_agree hag]
      split
      · exact diagBlock_apply_of_fst_ne hu
      · rw [one_pair_apply, if_neg (fun hc => hu (congrArg Prod.fst hc))]
    · rw [pairSet_apply_of_not_agree hag]

/-- The gate with one more control: the first qubit of the pair joins the control set. -/
theorem pairSet_eq_ctrlSetOf_insert (hut : u ≠ t) (hpu : pat u = 1)
    (U : Matrix (Fin 2) (Fin 2) ℂ) :
    pairSet S u t pat (diagBlock 1 U) 1 = ctrlSetOf (insert u S) t pat U := by
  have hins : ∀ k : Fin m → Fin 2,
      ((∀ i ∈ insert u S, k i = pat i) ↔ (k u = 1 ∧ ∀ i ∈ S, k i = pat i)) := by
    intro k
    rw [Finset.forall_mem_insert, hpu]
  ext k l
  by_cases hu : k u = l u
  · by_cases hagt : ∀ i, i ≠ t → k i = l i
    · have hag : ∀ i, i ≠ u → i ≠ t → k i = l i := fun i _ hit => hagt i hit
      rw [pairSet_apply_of_agree hag]
      by_cases hc : ∀ i ∈ S, k i = pat i
      · rw [if_pos hc,
          diagBlock_apply_of_fst_eq (show ((k u, k t) : Fin 2 × Fin 2).1 = (l u, l t).1 from hu)]
        by_cases hk1 : k u = 1
        · rw [ctrlSetOf_apply_block hagt ((hins k).mpr ⟨hk1, hc⟩), hk1,
            if_neg (by decide : ¬((1 : Fin 2) = 0))]
        · have hk0 : k u = 0 := by
            rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (k u) with h | h
            · exact h
            · exact absurd h hk1
          rw [ctrlSetOf_apply_id hagt (fun h => hk1 ((hins k).mp h).1), hk0, if_pos rfl]
      · rw [if_neg hc, ctrlSetOf_apply_id hagt (fun h => hc ((hins k).mp h).2), one_pair_apply,
          Matrix.one_apply]
        by_cases h : k t = l t
        · rw [if_pos (Prod.ext hu h), if_pos h]
        · rw [if_neg (fun hc' => h (congrArg Prod.snd hc')), if_neg h]
    · rw [pairSet_apply_of_not_agree, ctrlSetOf_apply_of_not_agree hagt]
      intro hag
      exact hagt fun i hit => by
        by_cases hiu : i = u
        · rw [hiu]; exact hu
        · exact hag i hiu hit
  · have hagt : ¬∀ i, i ≠ t → k i = l i := fun h => hu (h u hut)
    rw [ctrlSetOf_apply_of_not_agree hagt]
    by_cases hag : ∀ i, i ≠ u → i ≠ t → k i = l i
    · rw [pairSet_apply_of_agree hag]
      split
      · exact diagBlock_apply_of_fst_ne hu
      · rw [one_pair_apply, if_neg (fun hc => hu (congrArg Prod.fst hc))]
    · rw [pairSet_apply_of_not_agree hag]

/-- ★★ **The control-count recursion** (Nielsen–Chuang Figure 4.10, ancilla-free): one more control
costs two one-control gates, two gates with the old control set on the new control qubit, and one
gate with the old control set on the target, with `V` a square root of `U`. -/
theorem ctrlSetOf_insert (hut : u ≠ t) (huS : u ∉ S) (htS : t ∉ S) (hpu : pat u = 1)
    {U V : Matrix (Fin 2) (Fin 2) ℂ} (hV : V ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hVV : V * V = U) :
    ctrlSetOf (insert u S) t pat U
      = ctrlOf u t V * ctrlSetOf S u pat xMat * ctrlOf u t (star V) * ctrlSetOf S u pat xMat
          * ctrlSetOf S t pat V := by
  have hstar : star V * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  have hstar' : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp hV
  rw [← pairSet_eq_ctrlOf (S := S) (pat := pat) hut V,
    ← pairSet_eq_ctrlSetOf_fst (S := S) (pat := pat) hut,
    ← pairSet_eq_ctrlOf (S := S) (pat := pat) hut (star V),
    ← pairSet_eq_ctrlSetOf_snd (S := S) (pat := pat) hut V,
    pairSet_mul hut huS htS, pairSet_mul hut huS htS, pairSet_mul hut huS htS,
    pairSet_mul hut huS htS, ← pairSet_eq_ctrlSetOf_insert hut hpu U,
    diagBlock_five hstar hVV,
    show diagBlock (1 : Matrix (Fin 2) (Fin 2) ℂ) V * 1 * diagBlock 1 (star V) * 1 * 1
        = 1 by rw [mul_one, mul_one, mul_one, diagBlock_mul, one_mul, hstar', diagBlock_one]]

/-! ### Every controlled gate is a product of `CNOT`s and single-qubit gates -/

/-- The universal gate set: single-qubit gates and `CNOT`s. -/
def elementary (m : ℕ) : Set (Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ) :=
  {g | (∃ (j : Fin m) (M : Matrix (Fin 2) (Fin 2) ℂ),
        M ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ g = gateOf j M) ∨
      (∃ a b : Fin m, a ≠ b ∧ g = cnotGate' a b)}

theorem gateOf_mem_elementary (j : Fin m) {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Fin 2) ℂ) : gateOf j M ∈ elementary m :=
  Or.inl ⟨j, M, hM, rfl⟩

theorem cnotGate'_mem_elementary {a b : Fin m} (hab : a ≠ b) : cnotGate' a b ∈ elementary m :=
  Or.inr ⟨a, b, hab, rfl⟩

theorem xGate_eq_gateOf (j : Fin m) : xGate j = gateOf j xMat := by
  rw [xGate, gateOf, xMat]
  norm_num

theorem xGate_mem_elementary (j : Fin m) : xGate j ∈ elementary m := by
  rw [xGate_eq_gateOf]
  exact gateOf_mem_elementary j xMat_mem_unitaryGroup

theorem phaseMat_eq (α : ℝ) :
    !![(1 : ℂ), 0; 0, expI α] = expI (α / 2) • rzMat α := by
  rw [rzMat_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [← expI_add, show α / 2 + -(α / 2) = 0 by ring, show α / 2 + α / 2 = α by ring]

theorem phaseMat_mem_unitaryGroup (α : ℝ) :
    !![(1 : ℂ), 0; 0, expI α] ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [phaseMat_eq]
  exact expI_smul_mem_unitaryGroup _ (rzMat_mem_unitaryGroup α)

theorem singleGate_phase_eq_gateOf (a : Fin m) (α : ℝ) :
    singleGate a 1 0 0 (expI α) = gateOf a !![(1 : ℂ), 0; 0, expI α] := by
  rw [gateOf]
  norm_num

/-- A one-control gate is a product of elementary gates: #84's circuit. -/
theorem ctrlOf_mem_closure {a j : Fin m} (haj : a ≠ j) {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ctrlOf a j U ∈ Submonoid.closure (elementary m) := by
  obtain ⟨α, A, B, C, hA, hB, hC, -, heq⟩ := ctrlOf_eq_circuit haj hU
  rw [heq, singleGate_phase_eq_gateOf]
  refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_) ?_
  · exact Submonoid.subset_closure (gateOf_mem_elementary a (phaseMat_mem_unitaryGroup α))
  · exact Submonoid.subset_closure (gateOf_mem_elementary j hA)
  · exact Submonoid.subset_closure (cnotGate'_mem_elementary haj)
  · exact Submonoid.subset_closure (gateOf_mem_elementary j hB)
  · exact Submonoid.subset_closure (cnotGate'_mem_elementary haj)
  · exact Submonoid.subset_closure (gateOf_mem_elementary j hC)

theorem ctrlSetOf_empty (j : Fin m) (pat : Fin m → Fin 2) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    ctrlSetOf ∅ j pat U = gateOf j U := by
  ext k l
  by_cases hag : ∀ i, i ≠ j → k i = l i
  · rw [ctrlSetOf, gateOf, singleGate, ctrlSet_apply_of_ctrl hag (by simp),
      ctrlSet_apply_of_ctrl hag (by simp)]
  · rw [ctrlSetOf, gateOf, singleGate, ctrlSet_apply_of_not_agree hag,
      ctrlSet_apply_of_not_agree hag]

/-- The induction behind `ctrlSetOf_mem_closure`, on the number of controls. -/
theorem ctrlSetOf_mem_closure_aux (n : ℕ) : ∀ (S : Finset (Fin m)) (j : Fin m) (pat : Fin m → Fin 2)
    (U : Matrix (Fin 2) (Fin 2) ℂ), S.card = n → j ∉ S →
    U ∈ Matrix.unitaryGroup (Fin 2) ℂ →
    ctrlSetOf S j pat U ∈ Submonoid.closure (elementary m) := by
  induction n with
  | zero =>
    intro S j pat U hcard _ hU
    rw [Finset.card_eq_zero.mp hcard, ctrlSetOf_empty]
    exact Submonoid.subset_closure (gateOf_mem_elementary j hU)
  | succ n ih =>
    intro S j pat U hcard hjS hU
    obtain ⟨u, huS⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    have hcard' : (S.erase u).card = n := by
      rw [Finset.card_erase_of_mem huS, hcard]
      omega
    have huS' : u ∉ S.erase u := Finset.notMem_erase u S
    have hjS' : j ∉ S.erase u := fun h => hjS (Finset.mem_of_mem_erase h)
    have huj : u ≠ j := fun h => hjS (h ▸ huS)
    have main : ∀ p : Fin m → Fin 2, p u = 1 →
        ctrlSetOf S j p U ∈ Submonoid.closure (elementary m) := by
      intro p hpu
      obtain ⟨V, hV, hVV⟩ := exists_sqrt hU
      rw [← Finset.insert_erase huS,
        ctrlSetOf_insert huj huS' hjS' hpu hV hVV]
      refine mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_
      · exact ctrlOf_mem_closure huj hV
      · exact ih (S.erase u) u p xMat hcard' huS' xMat_mem_unitaryGroup
      · exact ctrlOf_mem_closure huj (Unitary.star_mem hV)
      · exact ih (S.erase u) u p xMat hcard' huS' xMat_mem_unitaryGroup
      · exact ih (S.erase u) j p V hcard' hjS' hV
    by_cases hpu : pat u = 1
    · exact main pat hpu
    · have hpu0 : pat u = 0 := by
        rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) (pat u) with h | h
        · exact h
        · exact absurd h hpu
      have hupd : Function.update pat u 1 u = 1 := Function.update_self _ _ _
      have key : ctrlSetOf S j pat U
          = xGate u * ctrlSetOf S j (Function.update pat u 1) U * xGate u := by
        rw [ctrlSetOf, ctrlSetOf, xGate_conj_ctrlSet (Ne.symm huj) (Function.update pat u 1),
          hupd, show flipBit 1 = 0 from rfl, Function.update_idem, ← hpu0,
          Function.update_eq_self]
      rw [key]
      exact mul_mem (mul_mem (Submonoid.subset_closure (xGate_mem_elementary u))
        (main _ hupd)) (Submonoid.subset_closure (xGate_mem_elementary u))

/-- ★★ **A gate with any number of controls, on any control pattern, is a product of `CNOT`s and
single-qubit gates.** -/
theorem ctrlSetOf_mem_closure (S : Finset (Fin m)) (j : Fin m) (pat : Fin m → Fin 2)
    {U : Matrix (Fin 2) (Fin 2) ℂ} (hjS : j ∉ S) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ctrlSetOf S j pat U ∈ Submonoid.closure (elementary m) :=
  ctrlSetOf_mem_closure_aux S.card S j pat U rfl hjS hU

/-- ★★ **#71's multiply-controlled gate is a product of `CNOT`s and single-qubit gates** — the form
#73 consumes, since the two-level theory of #70 and #71 produces exactly these. -/
theorem ctrlGateOf_mem_closure (j : Fin m) (pat : Fin m → Fin 2)
    {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ctrlGate j pat (U 0 0) (U 0 1) (U 1 0) (U 1 1) ∈ Submonoid.closure (elementary m) := by
  rw [← ctrlSet_erase_eq_ctrlGate]
  exact ctrlSetOf_mem_closure (Finset.univ.erase j) j pat (Finset.notMem_erase j Finset.univ) hU

end Controlled

end QuantumInfo
