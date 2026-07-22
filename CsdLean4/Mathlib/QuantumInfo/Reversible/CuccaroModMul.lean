/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Reversible.CuccaroModAdd
meta import CsdLean4.Mathlib.QuantumInfo.Reversible.CuccaroModAdd
public import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularMulLoop
public import CsdLean4.Mathlib.QuantumInfo.Reversible.Eval
meta import CsdLean4.Mathlib.QuantumInfo.Reversible.Eval
meta import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularMulLoop

/-!
# The carry-clean (Θ(n)-qubit) MODULAR MULTIPLY `X·Y mod N`  (ECDLP Phase 2, Stage 2b)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

Stage 2 (`CuccaroModAdd.lean`) delivered the carry-clean modular ADDER `cuccaroModAdd`
(`Acc ← (a + b) mod N`, every scratch wire restored). This module folds it into the carry-clean
modular **MULTIPLY** `X · Y mod N` with **ONE reused scratch bank** (Θ(n) qubits), versus the dirty
`ModularMulLoop.mulLoop`'s Θ(n²) fresh-ancilla model.

```
Acc = 0; for each bit i of X MSB-first: Acc ← (2·Acc) mod N; Acc ← (Acc + X_i·Y) mod N.
```

## The two clean sub-gadgets (each reuses the SAME scratch bank, re-cleaned per step)

1. **`cuccaroModDouble` — clean `Acc ← (2·Acc) mod N`.** Realised as an **in-place shift +
   conditional subtract** (Beauregard), NOT copy-add-uncopy. The copy-add-uncopy route is *not*
   clean: the copy register holds `a`, which cannot be uncomputed once `Acc` becomes `2a mod N`
   (no register then holds `a`, and `a = halve(2a mod N)` needs a halver). The shift `rotChain`
   doubles by an information-preserving wire rotation (`new[i] = old[i-1]`, `new[0] = old[n] = 0`),
   so there is *no* scratch to clean from the doubling itself; the `mod N` reduce reuses the Stage-2
   pieces (`cuccaroSub`, `maskCopy`, `cuccaroAdd`). The comparison flag is uncomputed **by parity**:
   for **odd `N`** (the ECDLP prime case), `[2a < N] = ¬(2a mod N) mod 2`, so a `CX (Acc 0) flag ; X`
   clears it. **Load-bearing hypothesis: `N` odd.**
2. **`cuccaroCModAdd` — clean bit-gated `Acc ← (Acc + X_i·Y) mod N`.** The masked-operand trick:
   `Mask2 ^= X_i·Y` (`maskCopyCtrl`, `n` `CCX`s), run `cuccaroModAdd` with addend `Mask2`, then
   uncompute `Mask2 ^= X_i·Y`. Because `X_i` and `Y` are preserved by the modular add, the mask
   uncomputes cleanly. This avoids a controlled adder.

## What is proved (`sorry`-free, foundational-triple-only)

* `cuccaroModDouble_correct` / `_clean` / `_preserves_Nreg` / `_toffoli` (= `6n + 4`).
* `cuccaroCModAdd_correct` / `_clean` / `_preserves_operand` / `_toffoli` (= `14n + 10`).
* `cuccaroModMul_correct` — general `n`: `Acc ← (X · Yval) mod N`.
* `cuccaroModMul_clean` — the **shared** scratch bank restored (so the Θ(n) reuse is real).
* `cuccaroModMul_preserves_XY` — `X`, `Y` intact.
* `cuccaroModMul_toffoli` — `(20n + 14)·n = 20n² + 14n` (the headline; per-step `20n + 14`).

## Honest cost / scope

Per-multiply Toffoli `20n² + 14n` (NOT the `~2n²` of a non-modular multiply: the `mod N` reduce per
step is irreducible in this measurement-free `CCX`-only DSL). The prize is **Θ(n) reusable qubits**
(ONE shared scratch bank `mod`) vs the dirty `mulLoop`'s Θ(n²) fresh ancilla; the per-multiply
Toffoli is also ~`1.5×` better than the dirty `30n²`. This is the verified modular field-multiply
atom; the elliptic-curve point op is a later stage. **Load-bearing hypothesis: `N` odd** (the parity
flag-uncompute in the doubler), which holds for the ECDLP prime field.
-/

@[expose] public section

namespace Reversible

variable {m n : ℕ}

/-! ### The in-place left-shift (doubling) rotation `rotChain`

`rotChain f k` is the top-down adjacent-swap chain `swap(f k, f(k-1)) :: ... :: swap(f 1, f 0)`. It
realises the cyclic up-rotation of the block `[0, k]`: `new[i] = old[i-1]` for `1 ≤ i ≤ k`,
`new[0] = old[k]`. With `old[k] = false` this is multiplication by `2` of the low `k` bits. -/

/-- Top-down adjacent-swap chain on register `f` (length `k`). -/
def rotChain (f : ℕ → Fin m) : ℕ → Circuit m
  | 0 => []
  | k + 1 => Gate.swap (f (k + 1)) (f k) :: rotChain f k

/-- A wire distinct from every `f j` (`j ≤ k`) survives `rotChain f k`. -/
theorem rotChain_external (f : ℕ → Fin m) (k : ℕ) (s : State m) (w : Fin m)
    (hw : ∀ j, j ≤ k → w ≠ f j) : denote (rotChain f k) s w = s w := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [rotChain, denote_cons, ih _ (fun j hj => hw j (Nat.le_succ_of_le hj))]
    show denoteGate (Gate.swap (f (k + 1)) (f k)) s w = s w
    simp only [denoteGate, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (hw (k + 1) (le_refl _)) (hw k (Nat.le_succ k))]

/-- **The rotation action.** With `f` injective on `[0, k]`: after `rotChain f k`, wire `f 0` holds
`s (f k)` and wire `f i` (for `1 ≤ i ≤ k`) holds `s (f (i-1))`. -/
theorem rotChain_apply (f : ℕ → Fin m) :
    ∀ (k : ℕ) (s : State m), (∀ i j, i ≤ k → j ≤ k → f i = f j → i = j) →
      denote (rotChain f k) s (f 0) = s (f k)
      ∧ ∀ i, 1 ≤ i → i ≤ k → denote (rotChain f k) s (f i) = s (f (i - 1)) := by
  intro k
  induction k with
  | zero => intro s _; exact ⟨rfl, fun i h1 h2 => by omega⟩
  | succ k ih =>
    intro s hinj
    set t := denoteGate (Gate.swap (f (k + 1)) (f k)) s with ht
    have hinj' : ∀ i j, i ≤ k → j ≤ k → f i = f j → i = j :=
      fun i j hi hj h => hinj i j (by omega) (by omega) h
    obtain ⟨ih1, ih2⟩ := ih t hinj'
    have htop : denote (rotChain f (k + 1)) s = denote (rotChain f k) t := by
      rw [rotChain, denote_cons, ← ht]
    have htk1 : t (f (k + 1)) = s (f k) := by
      rw [ht]; show denoteGate (Gate.swap (f (k + 1)) (f k)) s (f (k + 1)) = s (f k)
      simp only [denoteGate, Function.comp_apply, Equiv.swap_apply_left]
    have htne : ∀ i, i < k → t (f i) = s (f i) := by
      intro i hik
      rw [ht]; show denoteGate (Gate.swap (f (k + 1)) (f k)) s (f i) = s (f i)
      simp only [denoteGate, Function.comp_apply]
      rw [Equiv.swap_apply_of_ne_of_ne]
      · intro h; exact absurd (hinj i (k + 1) (by omega) (le_refl _) h) (by omega)
      · intro h; exact absurd (hinj i k (by omega) (by omega) h) (by omega)
    refine ⟨?_, ?_⟩
    · rw [htop, ih1]
      show t (f k) = s (f (k + 1))
      rw [ht]; simp only [denoteGate, Function.comp_apply, Equiv.swap_apply_right]
    · intro i h1 h2
      rw [htop]
      rcases Nat.lt_or_ge i (k + 1) with hik | hik
      · rw [ih2 i h1 (by omega), htne (i - 1) (by omega)]
      · have hi : i = k + 1 := by omega
        subst hi
        rw [rotChain_external f k t (f (k + 1))
            (fun j hj h => absurd (hinj (k + 1) j (le_refl _) (by omega) h) (by omega)),
          htk1, Nat.add_sub_cancel]

/-- **The rotation doubles.** With `f` injective on `[0, k]` and `s (f k) = false`:
`regValRange f (denote (rotChain f k) s) (k+1) = 2 * regValRange f s k`. -/
theorem rotChain_value (f : ℕ → Fin m) (s : State m) (k : ℕ)
    (hinj : ∀ i j, i ≤ k → j ≤ k → f i = f j → i = j) (htop : s (f k) = false) :
    regValRange f (denote (rotChain f k) s) (k + 1) = 2 * regValRange f s k := by
  obtain ⟨h0, hi⟩ := rotChain_apply f k s hinj
  rw [regValRange, Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  rw [h0, htop, Bool.toNat_false, add_zero, regValRange, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hmem
  rw [Finset.mem_range] at hmem
  rw [hi (i + 1) (by omega) (by omega), Nat.add_sub_cancel, pow_succ]
  ring

/-- Cost of the rotation: zero Toffoli (it is `k` `swap`s, each `3` CNOTs). -/
theorem rotChain_toffoli (f : ℕ → Fin m) (k : ℕ) :
    (circuitCost (rotChain f k)).toffoli = 0 := by
  induction k with
  | zero => simp [rotChain, circuitCost]
  | succ k ih =>
    rw [rotChain, show (Gate.swap (f (k + 1)) (f k) :: rotChain f k)
        = [Gate.swap (f (k + 1)) (f k)] ++ rotChain f k from rfl,
      cost_comp_toffoli_count, ih]
    simp [circuitCost, gateCost]

/-! ### The clean modular doubler `cuccaroModDouble`

Reuses the Stage-2 layout `CuccaroModLayout` (register `B` is unused by the doubler). The reduce
pieces (`cuccaroSub L.layN`, `maskCopy L`, `cuccaroAdd L.layM`) are exactly those of `cuccaroModAdd`.
The flag uncompute is `CX (Acc 0) flag ; X flag` (parity, **odd `N`**). -/

/-- **The carry-clean modular doubler** `Acc ← (2·Acc) mod N`. Seven stages: rotate (×2),
subtract `N`, copy sign to flag, mask `N`, add back, unmask, parity-uncompute the flag. -/
def cuccaroModDouble (L : CuccaroModLayout m n) : Circuit m :=
  rotChain L.Acc n
    ++ cuccaroSub L.layN
    ++ [Gate.CX (L.Acc n) L.flag]
    ++ maskCopy L
    ++ cuccaroAdd L.layM
    ++ maskCopy L
    ++ [Gate.CX (L.Acc 0) L.flag, Gate.X L.flag]

/-- The full doubler spec (value + every scratch wire clean + `Nreg` preserved). -/
theorem cuccaroModDouble_spec (L : CuccaroModLayout m n) (s : State m)
    (hAccTop : s (L.Acc n) = false) (hNtop : s (L.Nreg n) = false)
    (hMask0 : ∀ j, j < n + 1 → s (L.Mask j) = false)
    (hflag : s L.flag = false) (hZ : s L.Z = false)
    {N a : ℕ} (h2N : 2 * N ≤ 2 ^ n) (hNodd : N % 2 = 1)
    (hAcc : regValRange L.Acc s n = a)
    (hN : regValRange L.Nreg s n = N) (haN : a < N) :
    regValRange L.Acc (denote (cuccaroModDouble L) s) n = (2 * a) % N
      ∧ denote (cuccaroModDouble L) s L.flag = false
      ∧ (∀ j, j < n + 1 → denote (cuccaroModDouble L) s (L.Mask j) = false)
      ∧ denote (cuccaroModDouble L) s L.Z = false
      ∧ denote (cuccaroModDouble L) s (L.Acc n) = false
      ∧ regValRange L.Nreg (denote (cuccaroModDouble L) s) n = N
      ∧ denote (cuccaroModDouble L) s (L.Nreg n) = s (L.Nreg n) := by
  -- numeric prelims
  have hQpos : 0 < 2 ^ n := Nat.two_pow_pos n
  have hP : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le a) haN
  have haHalf : a < 2 ^ n := lt_of_lt_of_le haN (by omega)
  -- width-(n+1) initial readouts
  have hvN0 : regValRange L.Nreg s (n + 1) = N := by rw [regValRange_succ, hN, hNtop]; simp
  -- Acc injective on [0, n]
  have hAccinj' : ∀ i j, i ≤ n → j ≤ n → L.Acc i = L.Acc j → i = j :=
    fun i j hi hj h => L.hAccinj i j (by omega) (by omega) h
  -- decompose the circuit
  set s1 := denote (rotChain L.Acc n) s with hs1
  set s2 := denote (cuccaroSub L.layN) s1 with hs2
  set s3 := denoteGate (Gate.CX (L.Acc n) L.flag) s2 with hs3
  set s4 := denote (maskCopy L) s3 with hs4
  set s5 := denote (cuccaroAdd L.layM) s4 with hs5
  set s6 := denote (maskCopy L) s5 with hs6
  set s7 := denoteGate (Gate.X L.flag) (denoteGate (Gate.CX (L.Acc 0) L.flag) s6) with hs7
  have hsf : denote (cuccaroModDouble L) s = s7 := by
    rw [hs7, hs6, hs5, hs4, hs3, hs2, hs1]
    simp only [cuccaroModDouble, denote_append, denote_cons, denote_nil]
  -- ===== Z clean throughout =====
  have hZ1 : s1 L.Z = false := by
    rw [hs1, rotChain_external L.Acc n s L.Z (fun j _ => (L.hAccZ j).symm)]; exact hZ
  have hZ2 : s2 L.Z = false := by
    have h : denote (cuccaroSub L.layN) s1 L.Z = s1 L.Z := cuccaroSub_preserves_Z L.layN s1
    rw [hs2, h]; exact hZ1
  have hZ3 : s3 L.Z = false := by rw [hs3, denoteGate_cx_ne L.hflagZ.symm]; exact hZ2
  have hZ4 : s4 L.Z = false := by
    rw [hs4, maskCopy_external L s3 L.Z (fun j _ => (L.hMZ j).symm)]; exact hZ3
  have hZ5 : s5 L.Z = false := by
    have h : denote (cuccaroAdd L.layM) s4 L.Z = s4 L.Z := cuccaroAdd_preserves_Z L.layM s4
    rw [hs5, h]; exact hZ4
  have hZ6 : s6 L.Z = false := by
    rw [hs6, maskCopy_external L s5 L.Z (fun j _ => (L.hMZ j).symm)]; exact hZ5
  have hZ7 : s7 L.Z = false := by
    rw [hs7, denoteGate_x_ne L.hflagZ.symm, denoteGate_cx_ne L.hflagZ.symm]; exact hZ6
  -- ===== STAGE 1: rotate ⇒ Acc = 2a (width n+1) =====
  have hAcc1 : regValRange L.Acc s1 (n + 1) = 2 * a := by
    rw [hs1, rotChain_value L.Acc s n hAccinj' hAccTop, hAcc]
  have hN1 : ∀ j, j < n + 1 → s1 (L.Nreg j) = s (L.Nreg j) := fun j _ => by
    rw [hs1]; exact rotChain_external L.Acc n s (L.Nreg j) (fun i _ => (L.hAccN i j).symm)
  have hMa1 : ∀ j, j < n + 1 → s1 (L.Mask j) = s (L.Mask j) := fun j _ => by
    rw [hs1]; exact rotChain_external L.Acc n s (L.Mask j) (fun i _ => (L.hAccM i j).symm)
  have hflag1 : s1 L.flag = false := by
    rw [hs1, rotChain_external L.Acc n s L.flag (fun i _ => (L.hAccflag i).symm)]; exact hflag
  have hvN1 : regValRange L.Nreg s1 (n + 1) = N := by
    rw [show regValRange L.Nreg s1 (n + 1) = regValRange L.Nreg s (n + 1) from
      Finset.sum_congr rfl (fun j hj => by rw [hN1 j (Finset.mem_range.mp hj)]), hvN0]
  -- ===== STAGE 2: Acc -= Nreg =====
  have hAcc2 : regValRange L.Acc s2 (n + 1) = (2 * a + 2 ^ (n + 1) - N) % 2 ^ (n + 1) := by
    have h := cuccaroSub_correct L.layN s1 hZ1
    rw [← hs2] at h
    rw [show regValRange L.Acc s2 (n + 1)
          = (regValRange L.Acc s1 (n + 1) + 2 ^ (n + 1) - regValRange L.Nreg s1 (n + 1))
            % 2 ^ (n + 1) from h, hAcc1, hvN1]
  have hN2 : ∀ j, j < n + 1 → s2 (L.Nreg j) = s1 (L.Nreg j) := fun j hj => by
    rw [hs2]; exact cuccaroSub_preserves_B L.layN s1 hZ1 j hj
  have hMa2 : ∀ j, j < n + 1 → s2 (L.Mask j) = s1 (L.Mask j) := fun j _ => by
    rw [hs2]
    exact cuccaroSub_preserves_external L.layN s1 (L.Mask j) (L.hMZ j)
      (fun i _ => (L.hAccM i j).symm) (fun i _ => (L.hNM i j).symm)
  have hflag2 : s2 L.flag = false := by
    rw [hs2, cuccaroSub_preserves_external L.layN s1 L.flag L.hflagZ
      (fun i _ => (L.hAccflag i).symm) (fun i _ => (L.hNflag i).symm)]; exact hflag1
  -- ===== flag = [2a < N] =====
  have hFeq : s2 (L.Acc n) = decide (2 * a < N) := by
    rw [regValRange_top_bit L.Acc s2 n, hAcc2]
    rcases lt_or_ge (2 * a) N with hlt | hge
    · rw [Nat.mod_eq_of_lt (show 2 * a + 2 ^ (n + 1) - N < 2 ^ (n + 1) by omega),
        show decide (2 * a < N) = true from by rw [decide_eq_true_eq]; exact hlt,
        decide_eq_true_eq]
      omega
    · rw [show (2 * a + 2 ^ (n + 1) - N) % 2 ^ (n + 1) = 2 * a - N from by
          rw [show 2 * a + 2 ^ (n + 1) - N = (2 * a - N) + 2 ^ (n + 1) by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)],
        show decide (2 * a < N) = false from by rw [decide_eq_false_iff_not]; omega,
        decide_eq_false_iff_not]
      omega
  -- ===== STAGE 3: flag ^= Acc[n] =====
  have hs3flag : s3 L.flag = s2 (L.Acc n) := by
    rw [hs3, denoteGate_cx_target (L.hAccflag n) s2, hflag2, Bool.xor_false]
  have hAcc3 : regValRange L.Acc s3 (n + 1) = regValRange L.Acc s2 (n + 1) := by
    apply Finset.sum_congr rfl; intro j _
    show (s3 (L.Acc j)).toNat * 2 ^ j = (s2 (L.Acc j)).toNat * 2 ^ j
    rw [hs3, denoteGate_cx_ne (L.hAccflag j) s2]
  have hN3 : ∀ j, j < n + 1 → s3 (L.Nreg j) = s2 (L.Nreg j) := fun j _ => by
    rw [hs3]; exact denoteGate_cx_ne (L.hNflag j) s2
  have hMa3 : ∀ j, j < n + 1 → s3 (L.Mask j) = s2 (L.Mask j) := fun j _ => by
    rw [hs3]; exact denoteGate_cx_ne (L.hMflag j) s2
  have hMask3 : ∀ j, j < n + 1 → s3 (L.Mask j) = false := fun j hj => by
    rw [hMa3 j hj, hMa2 j hj, hMa1 j hj, hMask0 j hj]
  have hNs3 : regValRange L.Nreg s3 n = N := by
    rw [show regValRange L.Nreg s3 n = regValRange L.Nreg s n from
      Finset.sum_congr rfl (fun j hj => by
        have hjn : j < n := Finset.mem_range.mp hj
        rw [hN3 j (by omega), hN2 j (by omega), hN1 j (by omega)]), hN]
  -- ===== STAGE 4: Mask ^= flag·Nreg =====
  have hAcc4 : regValRange L.Acc s4 (n + 1) = regValRange L.Acc s3 (n + 1) := by
    apply Finset.sum_congr rfl; intro j _
    show (s4 (L.Acc j)).toNat * 2 ^ j = (s3 (L.Acc j)).toNat * 2 ^ j
    rw [hs4, maskCopy_external L s3 (L.Acc j) (fun i _ => L.hAccM j i)]
  have hM4_lo : ∀ j, j < n → s4 (L.Mask j) = (s3 L.flag && s3 (L.Nreg j)) := fun j hj => by
    rw [hs4, maskCopy_Mask L s3 j hj, hMask3 j (by omega)]; simp
  have hM4_top : s4 (L.Mask n) = false := by
    rw [hs4, maskCopy_Mask_top L s3, hMask3 n (by omega)]
  have hvM4 : regValRange L.Mask s4 (n + 1) = (s3 L.flag).toNat * regValRange L.Nreg s3 n := by
    rw [regValRange_succ, hM4_top]
    simp only [Bool.toNat_false, zero_mul, add_zero]
    rw [regValRange, regValRange, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj; rw [Finset.mem_range] at hj
    rw [hM4_lo j hj]
    cases s3 L.flag <;> simp [Nat.mul_comm]
  have hflag4 : s4 L.flag = s3 L.flag := by
    rw [hs4]; exact maskCopy_external L s3 L.flag (fun j _ => (L.hMflag j).symm)
  have hN5 : ∀ j, j < n + 1 → s5 (L.Nreg j) = s4 (L.Nreg j) := fun j _ => by
    rw [hs5]; exact cuccaroAdd_preserves_external L.layM s4 (L.Nreg j) (L.hNZ j)
      (fun i _ => (L.hAccN i j).symm) (fun i _ => L.hNM j i)
  have hN4 : ∀ j, j < n + 1 → s4 (L.Nreg j) = s3 (L.Nreg j) := fun j _ => by
    rw [hs4]; exact maskCopy_external L s3 (L.Nreg j) (fun i _ => L.hNM j i)
  -- ===== STAGE 5: Acc += Mask;  Acc = (2a) mod N =====
  have hr5 : regValRange L.Acc s5 (n + 1) = (2 * a) % N := by
    have h := cuccaroAdd_correct L.layM s4 hZ4
    rw [← hs5] at h
    rw [show regValRange L.Acc s5 (n + 1)
          = (regValRange L.Acc s4 (n + 1) + regValRange L.Mask s4 (n + 1)) % 2 ^ (n + 1) from h,
        hAcc4, hAcc3, hAcc2, hvM4, hNs3, hs3flag, hFeq]
    rcases lt_or_ge (2 * a) N with hlt | hge
    · rw [show decide (2 * a < N) = true from by rw [decide_eq_true_eq]; exact hlt,
        Bool.toNat_true, one_mul,
        Nat.mod_eq_of_lt (show 2 * a + 2 ^ (n + 1) - N < 2 ^ (n + 1) by omega),
        show 2 * a + 2 ^ (n + 1) - N + N = 2 * a + 2 ^ (n + 1) by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (show 2 * a < 2 ^ (n + 1) by omega)]
      exact (Nat.mod_eq_of_lt hlt).symm
    · have hD : (2 * a + 2 ^ (n + 1) - N) % 2 ^ (n + 1) = 2 * a - N := by
        rw [show 2 * a + 2 ^ (n + 1) - N = (2 * a - N) + 2 ^ (n + 1) by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
      rw [show decide (2 * a < N) = false from by rw [decide_eq_false_iff_not]; omega,
        Bool.toNat_false, zero_mul, add_zero, hD,
        Nat.mod_eq_of_lt (show 2 * a - N < 2 ^ (n + 1) by omega)]
      exact (mod_eq_sub_of_le_of_lt_two_mul hge (by omega)).symm
  -- ===== STAGE 6: uncompute Mask =====
  have hAcc6 : regValRange L.Acc s6 (n + 1) = regValRange L.Acc s5 (n + 1) := by
    apply Finset.sum_congr rfl; intro j _
    show (s6 (L.Acc j)).toNat * 2 ^ j = (s5 (L.Acc j)).toNat * 2 ^ j
    rw [hs6, maskCopy_external L s5 (L.Acc j) (fun i _ => L.hAccM j i)]
  have hM5eq : ∀ j, j < n + 1 → s5 (L.Mask j) = s4 (L.Mask j) := fun j hj => by
    rw [hs5]; exact cuccaroAdd_preserves_B L.layM s4 hZ4 j hj
  have hflag5 : s5 L.flag = s4 L.flag := by
    rw [hs5]; exact cuccaroAdd_preserves_external L.layM s4 L.flag L.hflagZ
      (fun i _ => (L.hAccflag i).symm) (fun i _ => (L.hMflag i).symm)
  have hMask6 : ∀ j, j < n + 1 → s6 (L.Mask j) = false := fun j hj => by
    rcases lt_or_ge j n with hjn | hjn
    · rw [hs6, maskCopy_Mask L s5 j hjn, hM5eq j hj, hM4_lo j hjn]
      have e2 : s5 L.flag = s3 L.flag := by rw [hflag5, hflag4]
      have e3 : s5 (L.Nreg j) = s3 (L.Nreg j) := by rw [hN5 j hj, hN4 j hj]
      rw [e2, e3]; simp
    · have hjeq : j = n := by omega
      rw [hjeq, hs6, maskCopy_Mask_top L s5, hM5eq n (by omega), hM4_top]
  have hflag6 : s6 L.flag = s3 L.flag := by
    rw [hs6, maskCopy_external L s5 L.flag (fun j _ => (L.hMflag j).symm), hflag5, hflag4]
  have hvAcc6 : regValRange L.Acc s6 (n + 1) = (2 * a) % N := by rw [hAcc6, hr5]
  -- the residue is < N ≤ 2ⁿ, so the low-n readout equals the (n+1)-readout and Acc[n] = false
  have hrlt : (2 * a) % N < 2 ^ n := lt_of_lt_of_le (Nat.mod_lt _ hNpos) (by omega)
  have hAcctop6 : s6 (L.Acc n) = false := by
    rw [regValRange_top_bit L.Acc s6 n, hvAcc6, decide_eq_false_iff_not]; omega
  have hval6 : regValRange L.Acc s6 n = (2 * a) % N := by
    have hsucc := regValRange_succ L.Acc s6 n
    rw [hAcctop6] at hsucc; simp only [Bool.toNat_false, zero_mul, add_zero] at hsucc
    rw [← hsucc, hvAcc6]
  -- bit 0 of the residue = its parity
  have hAcc0bit : (s6 (L.Acc 0)).toNat = ((2 * a) % N) % 2 := by
    have hsplit := regValRange_succ' L.Acc s6 n
    rw [hvAcc6] at hsplit
    have hb : (s6 (L.Acc 0)).toNat < 2 := by cases s6 (L.Acc 0) <;> simp
    omega
  -- ===== STAGE 7: parity flag uncompute =====
  -- flag at s6 = [2a < N]; bit0 of r = ¬[2a<N] (N odd) ⟹ flag ^^ bit0 = true ⟹ X clears.
  have hflagPar : (s6 L.flag ^^ s6 (L.Acc 0)) = true := by
    rw [hflag6, hs3flag, hFeq]
    have hr0 : ((2 * a) % N) % 2 = (if 2 * a < N then 0 else 1) := by
      rcases lt_or_ge (2 * a) N with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt, if_pos hlt]; omega
      · rw [mod_eq_sub_of_le_of_lt_two_mul hge (by omega), if_neg (by omega)]; omega
    rcases lt_or_ge (2 * a) N with hlt | hge
    · have hb0 : s6 (L.Acc 0) = false :=
        Bool.toNat_eq_zero.mp (by rw [hAcc0bit, hr0, if_pos hlt])
      rw [hb0, show decide (2 * a < N) = true from by rw [decide_eq_true_eq]; exact hlt]; rfl
    · have hb0 : s6 (L.Acc 0) = true :=
        Bool.toNat_eq_one.mp (by rw [hAcc0bit, hr0, if_neg (by omega)])
      rw [hb0, show decide (2 * a < N) = false from by rw [decide_eq_false_iff_not]; omega]; rfl
  have hf7 : s7 L.flag = false := by
    rw [hs7, denoteGate_x_target, denoteGate_cx_target (L.hAccflag 0) s6]
    rw [show (s6 (L.Acc 0) ^^ s6 L.flag) = true from by rw [Bool.xor_comm]; exact hflagPar]
    rfl
  -- Acc, Nreg, Mask unchanged across stage 7 (it only touches flag)
  have hAcc7 : ∀ j, j < n + 1 → s7 (L.Acc j) = s6 (L.Acc j) := fun j _ => by
    rw [hs7, denoteGate_x_ne (L.hAccflag j), denoteGate_cx_ne (L.hAccflag j)]
  have hAcctop7 : s7 (L.Acc n) = false := by rw [hAcc7 n (by omega), hAcctop6]
  have hval7 : regValRange L.Acc s7 n = (2 * a) % N := by
    rw [show regValRange L.Acc s7 n = regValRange L.Acc s6 n from
      Finset.sum_congr rfl (fun j hj => by
        rw [hAcc7 j (Nat.lt_succ_of_lt (Finset.mem_range.mp hj))]), hval6]
  have hMask7 : ∀ j, j < n + 1 → s7 (L.Mask j) = false := fun j hj => by
    rw [hs7, denoteGate_x_ne (L.hMflag j), denoteGate_cx_ne (L.hMflag j)]; exact hMask6 j hj
  -- Nreg preserved across 5,6,7
  have hN6 : ∀ j, j < n + 1 → s6 (L.Nreg j) = s5 (L.Nreg j) := fun j _ => by
    rw [hs6]; exact maskCopy_external L s5 (L.Nreg j) (fun i _ => L.hNM j i)
  have hN7 : ∀ j, j < n + 1 → s7 (L.Nreg j) = s6 (L.Nreg j) := fun j _ => by
    rw [hs7, denoteGate_x_ne (L.hNflag j), denoteGate_cx_ne (L.hNflag j)]
  have hNfinal : regValRange L.Nreg s7 n = N := by
    rw [show regValRange L.Nreg s7 n = regValRange L.Nreg s n from
      Finset.sum_congr rfl (fun j hj => by
        have hjn : j < n := Finset.mem_range.mp hj
        rw [hN7 j (by omega), hN6 j (by omega), hN5 j (by omega), hN4 j (by omega),
          hN3 j (by omega), hN2 j (by omega), hN1 j (by omega)]), hN]
  have hNtop7 : s7 (L.Nreg n) = s (L.Nreg n) := by
    rw [hN7 n (by omega), hN6 n (by omega), hN5 n (by omega), hN4 n (by omega), hN3 n (by omega),
      hN2 n (by omega), hN1 n (by omega)]
  -- assemble
  rw [hsf]
  exact ⟨hval7, hf7, hMask7, hZ7, hAcctop7, hNfinal, hNtop7⟩

/-- **Correctness.** `cuccaroModDouble` leaves `Acc = (2·a) mod N`. -/
theorem cuccaroModDouble_correct (L : CuccaroModLayout m n) (s : State m)
    (hAccTop : s (L.Acc n) = false) (hNtop : s (L.Nreg n) = false)
    (hMask0 : ∀ j, j < n + 1 → s (L.Mask j) = false)
    (hflag : s L.flag = false) (hZ : s L.Z = false)
    {N a : ℕ} (h2N : 2 * N ≤ 2 ^ n) (hNodd : N % 2 = 1)
    (hAcc : regValRange L.Acc s n = a)
    (hN : regValRange L.Nreg s n = N) (haN : a < N) :
    regValRange L.Acc (denote (cuccaroModDouble L) s) n = (2 * a) % N :=
  (cuccaroModDouble_spec L s hAccTop hNtop hMask0 hflag hZ h2N hNodd hAcc hN haN).1

/-- **The doubler is carry-clean.** Flag, carry-out `Acc[n]`, every `Mask`, and `Z` restored. -/
theorem cuccaroModDouble_clean (L : CuccaroModLayout m n) (s : State m)
    (hAccTop : s (L.Acc n) = false) (hNtop : s (L.Nreg n) = false)
    (hMask0 : ∀ j, j < n + 1 → s (L.Mask j) = false)
    (hflag : s L.flag = false) (hZ : s L.Z = false)
    {N a : ℕ} (h2N : 2 * N ≤ 2 ^ n) (hNodd : N % 2 = 1)
    (hAcc : regValRange L.Acc s n = a)
    (hN : regValRange L.Nreg s n = N) (haN : a < N) :
    denote (cuccaroModDouble L) s L.flag = false
      ∧ denote (cuccaroModDouble L) s (L.Acc n) = false
      ∧ (∀ j, j < n + 1 → denote (cuccaroModDouble L) s (L.Mask j) = false)
      ∧ denote (cuccaroModDouble L) s L.Z = false := by
  obtain ⟨-, hflag9, hMask9, hZ9, hAcctop9, -, -⟩ :=
    cuccaroModDouble_spec L s hAccTop hNtop hMask0 hflag hZ h2N hNodd hAcc hN haN
  exact ⟨hflag9, hAcctop9, hMask9, hZ9⟩

/-- **`Nreg` is preserved** (low value and top padding wire). -/
theorem cuccaroModDouble_preserves_Nreg (L : CuccaroModLayout m n) (s : State m)
    (hAccTop : s (L.Acc n) = false) (hNtop : s (L.Nreg n) = false)
    (hMask0 : ∀ j, j < n + 1 → s (L.Mask j) = false)
    (hflag : s L.flag = false) (hZ : s L.Z = false)
    {N a : ℕ} (h2N : 2 * N ≤ 2 ^ n) (hNodd : N % 2 = 1)
    (hAcc : regValRange L.Acc s n = a)
    (hN : regValRange L.Nreg s n = N) (haN : a < N) :
    regValRange L.Nreg (denote (cuccaroModDouble L) s) n = N
      ∧ denote (cuccaroModDouble L) s (L.Nreg n) = s (L.Nreg n) := by
  obtain ⟨-, -, -, -, -, hNfin, hNtop9⟩ :=
    cuccaroModDouble_spec L s hAccTop hNtop hMask0 hflag hZ h2N hNodd hAcc hN haN
  exact ⟨hNfin, hNtop9⟩

/-- **Derived Toffoli cost: `6n + 4`.** Rotation `0` (`swap`s, no Toffoli), subtract `2(n+1)`,
mask `n`, add `2(n+1)`, mask `n`, single gates `0`: `2(n+1) + n + 2(n+1) + n = 6n + 4`. -/
theorem cuccaroModDouble_toffoli (L : CuccaroModLayout m n) :
    (circuitCost (cuccaroModDouble L)).toffoli = 6 * n + 4 := by
  rw [cuccaroModDouble]
  simp only [cost_comp_toffoli_count, rotChain_toffoli, cuccaroAdd_toffoli, cuccaroSub_toffoli,
    maskCopy_toffoli]
  have hCX : (circuitCost ([Gate.CX (L.Acc n) L.flag] : Circuit m)).toffoli = 0 := by
    simp [circuitCost, gateCost]
  have hCXX : (circuitCost ([Gate.CX (L.Acc 0) L.flag, Gate.X L.flag] : Circuit m)).toffoli = 0 := by
    simp [circuitCost, gateCost]
  rw [hCX, hCXX]
  ring

/-! ### Two `cuccaroModAdd` frame lemmas (external wires + per-wire `B`)

`cuccaroModAdd` exports only `regValRange`-level operand preservation; the bit-gated adder needs
(a) preservation of wires *entirely outside* the modular adder (for the read-only `Y` / `ctrl`),
and (b) **per-wire** restoration of the addend register `B` (for the masked-operand uncompute).
Both compose the per-stage frame lemmas; the ancilla `Z` stays clean throughout (the per-stage
`_preserves_Z` lemmas are unconditional). -/

/-- A wire disjoint from every modular-adder family (`Acc, B, Nreg, Mask, flag, Z`) survives
`cuccaroModAdd`. -/
theorem cuccaroModAdd_preserves_external (L : CuccaroModLayout m n) (s : State m) (w : Fin m)
    (hAcc : ∀ j, w ≠ L.Acc j) (hB : ∀ j, w ≠ L.B j) (hNg : ∀ j, w ≠ L.Nreg j)
    (hM : ∀ j, w ≠ L.Mask j) (hflag : w ≠ L.flag) (hZ : w ≠ L.Z) :
    denote (cuccaroModAdd L) s w = s w := by
  simp only [cuccaroModAdd, denote_append, denote_cons, denote_nil]
  rw [cuccaroAdd_preserves_external L.layB _ w hZ (fun i _ => hAcc i) (fun i _ => hB i),
    denoteGate_x_ne hflag,
    denoteGate_cx_ne hflag,
    cuccaroSub_preserves_external L.layB _ w hZ (fun i _ => hAcc i) (fun i _ => hB i),
    maskCopy_external L _ w (fun j _ => hM j),
    cuccaroAdd_preserves_external L.layM _ w hZ (fun i _ => hAcc i) (fun i _ => hM i),
    maskCopy_external L _ w (fun j _ => hM j),
    denoteGate_cx_ne hflag,
    cuccaroSub_preserves_external L.layN _ w hZ (fun i _ => hAcc i) (fun i _ => hNg i),
    cuccaroAdd_preserves_external L.layB _ w hZ (fun i _ => hAcc i) (fun i _ => hB i)]

/-- **Per-wire restoration of the addend `B`.** Each `B k` (`k < n + 1`) is returned to its input
value (the carries threaded through it during the three `cuccaroAdd L.layB` / two `cuccaroSub L.layB`
passes are restored). Needs only `s Z = false`. -/
theorem cuccaroModAdd_preserves_B_wire (L : CuccaroModLayout m n) (s : State m) (hZ : s L.Z = false)
    (k : ℕ) (hk : k < n + 1) :
    denote (cuccaroModAdd L) s (L.B k) = s (L.B k) := by
  simp only [cuccaroModAdd, denote_append, denote_cons, denote_nil]
  -- the 9 stage states
  set s1 := denote (cuccaroAdd L.layB) s with hs1
  set s2 := denote (cuccaroSub L.layN) s1 with hs2
  set s3 := denoteGate (Gate.CX (L.Acc n) L.flag) s2 with hs3
  set s4 := denote (maskCopy L) s3 with hs4
  set s5 := denote (cuccaroAdd L.layM) s4 with hs5
  set s6 := denote (maskCopy L) s5 with hs6
  set s7 := denote (cuccaroSub L.layB) s6 with hs7
  set s8 := denoteGate (Gate.X L.flag) (denoteGate (Gate.CX (L.Acc n) L.flag) s7) with hs8
  -- Z clean at every stage (each stage maps Z ↦ Z)
  have hZ1 : s1 L.Z = false := by
    have h : denote (cuccaroAdd L.layB) s L.Z = s L.Z := cuccaroAdd_preserves_Z L.layB s
    rw [hs1, h]; exact hZ
  have hZ2 : s2 L.Z = false := by
    have h : denote (cuccaroSub L.layN) s1 L.Z = s1 L.Z := cuccaroSub_preserves_Z L.layN s1
    rw [hs2, h]; exact hZ1
  have hZ3 : s3 L.Z = false := by rw [hs3, denoteGate_cx_ne L.hflagZ.symm]; exact hZ2
  have hZ4 : s4 L.Z = false := by
    rw [hs4, maskCopy_external L s3 L.Z (fun j _ => (L.hMZ j).symm)]; exact hZ3
  have hZ5 : s5 L.Z = false := by
    have h : denote (cuccaroAdd L.layM) s4 L.Z = s4 L.Z := cuccaroAdd_preserves_Z L.layM s4
    rw [hs5, h]; exact hZ4
  have hZ6 : s6 L.Z = false := by
    rw [hs6, maskCopy_external L s5 L.Z (fun j _ => (L.hMZ j).symm)]; exact hZ5
  have hZ7 : s7 L.Z = false := by
    have h : denote (cuccaroSub L.layB) s6 L.Z = s6 L.Z := cuccaroSub_preserves_Z L.layB s6
    rw [hs7, h]; exact hZ6
  have hZ8 : s8 L.Z = false := by
    rw [hs8, denoteGate_x_ne L.hflagZ.symm, denoteGate_cx_ne L.hflagZ.symm]; exact hZ7
  -- B k preserved at every stage
  have hB1 : s1 (L.B k) = s (L.B k) := by rw [hs1]; exact cuccaroAdd_preserves_B L.layB s hZ k hk
  have hB2 : s2 (L.B k) = s1 (L.B k) := by
    rw [hs2]; exact cuccaroSub_preserves_external L.layN s1 (L.B k) (L.hBZ k)
      (fun i _ => (L.hAccB i k).symm) (fun i _ => L.hBN k i)
  have hB3 : s3 (L.B k) = s2 (L.B k) := by rw [hs3]; exact denoteGate_cx_ne (L.hBflag k) s2
  have hB4 : s4 (L.B k) = s3 (L.B k) := by
    rw [hs4]; exact maskCopy_external L s3 (L.B k) (fun i _ => L.hBM k i)
  have hB5 : s5 (L.B k) = s4 (L.B k) := by
    rw [hs5]; exact cuccaroAdd_preserves_external L.layM s4 (L.B k) (L.hBZ k)
      (fun i _ => (L.hAccB i k).symm) (fun i _ => L.hBM k i)
  have hB6 : s6 (L.B k) = s5 (L.B k) := by
    rw [hs6]; exact maskCopy_external L s5 (L.B k) (fun i _ => L.hBM k i)
  have hB7 : s7 (L.B k) = s6 (L.B k) := by rw [hs7]; exact cuccaroSub_preserves_B L.layB s6 hZ6 k hk
  have hB8 : s8 (L.B k) = s7 (L.B k) := by
    rw [hs8, denoteGate_x_ne (L.hBflag k), denoteGate_cx_ne (L.hBflag k)]
  have hB9 : denote (cuccaroAdd L.layB) s8 (L.B k) = s8 (L.B k) :=
    cuccaroAdd_preserves_B L.layB s8 hZ8 k hk
  show denote (cuccaroAdd L.layB) s8 (L.B k) = s (L.B k)
  rw [hB9, hB8, hB7, hB6, hB5, hB4, hB3, hB2, hB1]

/-! ### The control-masked copy `maskCopyCtrl`

`Mask2 ^= ctrl · Y` via `n` Toffolis `CCX ctrl (Y i) (B i)` (the addend register `B` plays the role
of `Mask2`). Mirrors `maskCopy` with `(flag, Nreg, Mask) ↦ (ctrl, Y, B)`. -/

/-- First `k` masked-copy gates `CCX ctrl (Y i) (B i)`. -/
def maskCopyCtrlPrefix (L : CuccaroModLayout m n) (Y : ℕ → Fin m) (ctrl : Fin m) (k : ℕ) :
    Circuit m :=
  (List.range k).map (fun i => Gate.CCX ctrl (Y i) (L.B i))

/-- The full control-masked copy: `Mask2 = B ^= ctrl · Y` on all `n` low wires. Self-inverse. -/
def maskCopyCtrl (L : CuccaroModLayout m n) (Y : ℕ → Fin m) (ctrl : Fin m) : Circuit m :=
  maskCopyCtrlPrefix L Y ctrl n

theorem maskCopyCtrlPrefix_succ (L : CuccaroModLayout m n) (Y : ℕ → Fin m) (ctrl : Fin m) (k : ℕ)
    (s : State m) :
    denote (maskCopyCtrlPrefix L Y ctrl (k + 1)) s
      = denoteGate (Gate.CCX ctrl (Y k) (L.B k)) (denote (maskCopyCtrlPrefix L Y ctrl k) s) := by
  simp only [maskCopyCtrlPrefix, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    denote_append, denote_cons, denote_nil]

/-- **The control-masked-copy invariant.** After `k` gates: `B j` (`j < k`) holds
`B j ^^ (ctrl ∧ Y j)`; `B j` (`k ≤ j ≤ n`) is untouched; every non-`B` wire is preserved. -/
theorem maskCopyCtrlPrefix_spec (L : CuccaroModLayout m n) (Y : ℕ → Fin m) (ctrl : Fin m)
    (s : State m) (hctrlB : ∀ j, ctrl ≠ L.B j) (hYB : ∀ i j, Y i ≠ L.B j) :
    ∀ k, k ≤ n →
      (∀ j, j < k → denote (maskCopyCtrlPrefix L Y ctrl k) s (L.B j)
          = (s (L.B j) ^^ (s ctrl && s (Y j))))
      ∧ (∀ j, k ≤ j → j < n + 1 → denote (maskCopyCtrlPrefix L Y ctrl k) s (L.B j) = s (L.B j))
      ∧ (∀ w, (∀ j, j < n → w ≠ L.B j) → denote (maskCopyCtrlPrefix L Y ctrl k) s w = s w) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun j hj => by omega, fun j _ _ => by simp [maskCopyCtrlPrefix],
      fun w _ => by simp [maskCopyCtrlPrefix]⟩
  | succ k ih =>
    intro hk
    have hkn : k ≤ n := by omega
    have hkltn : k < n := hk
    obtain ⟨ih1, ih2, ih3⟩ := ih hkn
    set sk := denote (maskCopyCtrlPrefix L Y ctrl k) s with hskdef
    have hctrlk : sk ctrl = s ctrl := ih3 ctrl (fun j _ => hctrlB j)
    have hYk : sk (Y k) = s (Y k) := ih3 (Y k) (fun j _ => hYB k j)
    have hBkk : sk (L.B k) = s (L.B k) := ih2 k (le_refl k) (by omega)
    have hstep := maskCopyCtrlPrefix_succ L Y ctrl k s
    rw [← hskdef] at hstep
    have hBne : ∀ j, j ≠ k → j < n + 1 → L.B j ≠ L.B k := by
      intro j hj hjn h; exact hj (L.hBinj j k hjn (by omega) h)
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      rw [hstep]
      rcases eq_or_ne j k with rfl | hjk
      · have key : denoteGate (Gate.CCX ctrl (Y j) (L.B j)) sk (L.B j)
              = (sk (L.B j) ^^ (sk ctrl && sk (Y j))) := by
          simp only [denoteGate]
          rw [if_neg (by
            rintro (h | h)
            · exact (hctrlB j) h.symm
            · exact (hYB j j) h.symm)]
          rw [Function.update_self]
        rw [key, hBkk, hctrlk, hYk]
      · rw [denoteGate_ccx_ne (hBne j hjk (by omega))]
        exact ih1 j (by omega)
    · intro j hjk hjn
      rw [hstep, denoteGate_ccx_ne (hBne j (by omega) hjn)]
      exact ih2 j (by omega) hjn
    · intro w hw
      rw [hstep, denoteGate_ccx_ne (hw k hkltn)]
      exact ih3 w hw

/-- `maskCopyCtrl` computed clause (`j < n`). -/
theorem maskCopyCtrl_B (L : CuccaroModLayout m n) (Y : ℕ → Fin m) (ctrl : Fin m) (s : State m)
    (hctrlB : ∀ j, ctrl ≠ L.B j) (hYB : ∀ i j, Y i ≠ L.B j) (j : ℕ) (hj : j < n) :
    denote (maskCopyCtrl L Y ctrl) s (L.B j) = (s (L.B j) ^^ (s ctrl && s (Y j))) :=
  ((maskCopyCtrlPrefix_spec L Y ctrl s hctrlB hYB n (le_refl n)).1) j hj

/-- `maskCopyCtrl` top wire `B n` untouched. -/
theorem maskCopyCtrl_B_top (L : CuccaroModLayout m n) (Y : ℕ → Fin m) (ctrl : Fin m) (s : State m)
    (hctrlB : ∀ j, ctrl ≠ L.B j) (hYB : ∀ i j, Y i ≠ L.B j) :
    denote (maskCopyCtrl L Y ctrl) s (L.B n) = s (L.B n) :=
  ((maskCopyCtrlPrefix_spec L Y ctrl s hctrlB hYB n (le_refl n)).2.1) n (le_refl n) (by omega)

/-- `maskCopyCtrl` preserves every non-`B` wire. -/
theorem maskCopyCtrl_external (L : CuccaroModLayout m n) (Y : ℕ → Fin m) (ctrl : Fin m) (s : State m)
    (hctrlB : ∀ j, ctrl ≠ L.B j) (hYB : ∀ i j, Y i ≠ L.B j) (w : Fin m)
    (hw : ∀ j, j < n → w ≠ L.B j) :
    denote (maskCopyCtrl L Y ctrl) s w = s w :=
  ((maskCopyCtrlPrefix_spec L Y ctrl s hctrlB hYB n (le_refl n)).2.2) w hw

theorem maskCopyCtrlPrefix_toffoli (L : CuccaroModLayout m n) (Y : ℕ → Fin m) (ctrl : Fin m)
    (k : ℕ) : (circuitCost (maskCopyCtrlPrefix L Y ctrl k)).toffoli = k := by
  induction k with
  | zero => simp [maskCopyCtrlPrefix, circuitCost]
  | succ k ih =>
    have hsplit : maskCopyCtrlPrefix L Y ctrl (k + 1)
        = maskCopyCtrlPrefix L Y ctrl k ++ [Gate.CCX ctrl (Y k) (L.B k)] := by
      simp [maskCopyCtrlPrefix, List.range_succ, List.map_append]
    rw [hsplit, cost_comp_toffoli_count, ih]
    simp [circuitCost, gateCost]

theorem maskCopyCtrl_toffoli (L : CuccaroModLayout m n) (Y : ℕ → Fin m) (ctrl : Fin m) :
    (circuitCost (maskCopyCtrl L Y ctrl)).toffoli = n :=
  maskCopyCtrlPrefix_toffoli L Y ctrl n

/-- **`maskCopyCtrl` value:** with `B` initially `0`, `Mask2 = B` ends holding `if ctrl then y else 0`
where `y = regValRange Y s n`. -/
theorem maskCopyCtrl_value (L : CuccaroModLayout m n) (Y : ℕ → Fin m) (ctrl : Fin m) (s : State m)
    (hctrlB : ∀ j, ctrl ≠ L.B j) (hYB : ∀ i j, Y i ≠ L.B j)
    (hB0 : ∀ j, j < n → s (L.B j) = false) :
    regValRange L.B (denote (maskCopyCtrl L Y ctrl) s) n
      = if s ctrl then regValRange Y s n else 0 := by
  rw [regValRange]
  have hcongr : ∀ j ∈ Finset.range n,
      (denote (maskCopyCtrl L Y ctrl) s (L.B j)).toNat * 2 ^ j
        = (if s ctrl then (s (Y j)).toNat else 0) * 2 ^ j := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [maskCopyCtrl_B L Y ctrl s hctrlB hYB j hj, hB0 j hj]
    cases s ctrl <;> simp
  rw [Finset.sum_congr rfl hcongr]
  cases s ctrl <;> simp [regValRange]

/-! ### The clean bit-gated modular adder `cuccaroCModAdd` -/

/-- Bundled layout for the clean conditional modular add: the Stage-2 modular-adder layout `mod`
(its addend register `mod.B` is the masked operand `Mask2`), plus the read-only multiplicand `Y`
and the gating bit `ctrl`, disjoint from everything `mod` touches. -/
structure CuccaroCModLayout (m n : ℕ) where
  /-- The carry-clean modular-adder layout (`mod.B` = the masked operand `Mask2`). -/
  mod : CuccaroModLayout m n
  /-- The read-only multiplicand register (`n` bits). -/
  Y : ℕ → Fin m
  /-- The gating bit. -/
  ctrl : Fin m
  hYAcc : ∀ i j, Y i ≠ mod.Acc j
  hYB : ∀ i j, Y i ≠ mod.B j
  hYN : ∀ i j, Y i ≠ mod.Nreg j
  hYM : ∀ i j, Y i ≠ mod.Mask j
  hYflag : ∀ i, Y i ≠ mod.flag
  hYZ : ∀ i, Y i ≠ mod.Z
  hctrlAcc : ∀ j, ctrl ≠ mod.Acc j
  hctrlB : ∀ j, ctrl ≠ mod.B j
  hctrlN : ∀ j, ctrl ≠ mod.Nreg j
  hctrlM : ∀ j, ctrl ≠ mod.Mask j
  hctrlflag : ctrl ≠ mod.flag
  hctrlZ : ctrl ≠ mod.Z

/-- **The carry-clean bit-gated modular adder** `Acc ← (Acc + (if ctrl then Y else 0)) mod N`. Mask
the operand into `Mask2 = mod.B`, run `cuccaroModAdd`, uncompute the mask. -/
def cuccaroCModAdd (K : CuccaroCModLayout m n) : Circuit m :=
  maskCopyCtrl K.mod K.Y K.ctrl ++ cuccaroModAdd K.mod ++ maskCopyCtrl K.mod K.Y K.ctrl

/-- The full bit-gated-adder spec (value + all scratch incl. `Mask2` clean + `Y` / `ctrl` / `Nreg`
preserved). -/
theorem cuccaroCModAdd_spec (K : CuccaroCModLayout m n) (s : State m)
    (hAccTop : s (K.mod.Acc n) = false) (hBtop : ∀ j, j < n + 1 → s (K.mod.B j) = false)
    (hNtop : s (K.mod.Nreg n) = false) (hMask0 : ∀ j, j < n + 1 → s (K.mod.Mask j) = false)
    (hflag : s K.mod.flag = false) (hZ : s K.mod.Z = false)
    {N a y : ℕ} (h2N : 2 * N ≤ 2 ^ n)
    (hAcc : regValRange K.mod.Acc s n = a) (hN : regValRange K.mod.Nreg s n = N)
    (haN : a < N) (hYval : regValRange K.Y s n = y) (hyN : y < N) :
    regValRange K.mod.Acc (denote (cuccaroCModAdd K) s) n
        = (a + (if s K.ctrl then y else 0)) % N
      ∧ denote (cuccaroCModAdd K) s K.mod.flag = false
      ∧ denote (cuccaroCModAdd K) s (K.mod.Acc n) = false
      ∧ (∀ j, j < n + 1 → denote (cuccaroCModAdd K) s (K.mod.Mask j) = false)
      ∧ (∀ j, j < n + 1 → denote (cuccaroCModAdd K) s (K.mod.B j) = false)
      ∧ denote (cuccaroCModAdd K) s K.mod.Z = false
      ∧ regValRange K.Y (denote (cuccaroCModAdd K) s) n = y
      ∧ denote (cuccaroCModAdd K) s K.ctrl = s K.ctrl
      ∧ regValRange K.mod.Nreg (denote (cuccaroCModAdd K) s) n = N
      ∧ denote (cuccaroCModAdd K) s (K.mod.Nreg n) = s (K.mod.Nreg n) := by
  set L := K.mod with hLdef
  set Y := K.Y with hYdef
  set ctrl := K.ctrl with hctrldef
  -- disjointness shortcuts
  have hctrlB : ∀ j, ctrl ≠ L.B j := K.hctrlB
  have hYB : ∀ i j, Y i ≠ L.B j := K.hYB
  -- decompose
  set s1 := denote (maskCopyCtrl L Y ctrl) s with hs1
  set s2 := denote (cuccaroModAdd L) s1 with hs2
  have hsf : denote (cuccaroCModAdd K) s = denote (maskCopyCtrl L Y ctrl) s2 := by
    rw [hs2, hs1]; simp only [cuccaroCModAdd, denote_append]; rfl
  -- ===== STAGE 1: mask the operand into B =====
  -- Acc, Nreg, Mask, flag, Z, Y, ctrl preserved (all non-B)
  have hAcc1 : ∀ j, s1 (L.Acc j) = s (L.Acc j) := fun j => by
    rw [hs1]; exact maskCopyCtrl_external L Y ctrl s hctrlB hYB (L.Acc j) (fun i _ => (L.hAccB j i))
  have hN1 : ∀ j, s1 (L.Nreg j) = s (L.Nreg j) := fun j => by
    rw [hs1]; exact maskCopyCtrl_external L Y ctrl s hctrlB hYB (L.Nreg j) (fun i _ => (L.hBN i j).symm)
  have hM1 : ∀ j, s1 (L.Mask j) = s (L.Mask j) := fun j => by
    rw [hs1]; exact maskCopyCtrl_external L Y ctrl s hctrlB hYB (L.Mask j) (fun i _ => (L.hBM i j).symm)
  have hflag1 : s1 L.flag = false := by
    rw [hs1, maskCopyCtrl_external L Y ctrl s hctrlB hYB L.flag (fun i _ => (L.hBflag i).symm)]
    exact hflag
  have hZ1 : s1 L.Z = false := by
    rw [hs1, maskCopyCtrl_external L Y ctrl s hctrlB hYB L.Z (fun i _ => (L.hBZ i).symm)]; exact hZ
  have hctrl1 : s1 ctrl = s ctrl := by
    rw [hs1, maskCopyCtrl_external L Y ctrl s hctrlB hYB ctrl (fun j _ => (hctrlB j))]
  have hY1 : ∀ j, s1 (Y j) = s (Y j) := fun j => by
    rw [hs1]; exact maskCopyCtrl_external L Y ctrl s hctrlB hYB (Y j) (fun i _ => (hYB j i))
  -- B value at s1 = if ctrl then y else 0
  have hbdef : regValRange L.B s1 n = (if s ctrl then y else 0) := by
    rw [hs1, maskCopyCtrl_value L Y ctrl s hctrlB hYB (fun j hj => hBtop j (by omega)), hYval]
  set b := (if s ctrl then y else 0) with hbb
  have hbN : b < N := by
    rw [hbb]; split
    · exact hyN
    · exact Nat.lt_of_le_of_lt (Nat.zero_le a) haN
  -- B top wire still false; B is clean except low computed bits (needed for cuccaroModAdd hyps)
  have hBtop1 : s1 (L.B n) = false := by
    rw [hs1, maskCopyCtrl_B_top L Y ctrl s hctrlB hYB]; exact hBtop n (by omega)
  -- width-n readouts at s1
  have hAccv1 : regValRange L.Acc s1 n = a := by
    rw [show regValRange L.Acc s1 n = regValRange L.Acc s n from
      Finset.sum_congr rfl (fun j _ => by rw [hAcc1 j]), hAcc]
  have hNv1 : regValRange L.Nreg s1 n = N := by
    rw [show regValRange L.Nreg s1 n = regValRange L.Nreg s n from
      Finset.sum_congr rfl (fun j _ => by rw [hN1 j]), hN]
  have hAcctop1 : s1 (L.Acc n) = false := by rw [hAcc1 n]; exact hAccTop
  have hNtop1 : s1 (L.Nreg n) = false := by rw [hN1 n]; exact hNtop
  have hMask01 : ∀ j, j < n + 1 → s1 (L.Mask j) = false := fun j hj => by rw [hM1 j]; exact hMask0 j hj
  -- ===== STAGE 2: cuccaroModAdd =====
  have hAdd := cuccaroModAdd_spec L s1 hAcctop1 hBtop1 hNtop1 hMask01 hflag1 hZ1 h2N hAccv1 hbdef hNv1
    haN hbN
  obtain ⟨hr2, hflag2, hMask2, hZ2, hAcctop2, hBfin2, hNfin2, hBtop2, hNtop2⟩ := hAdd
  rw [← hs2] at hr2 hflag2 hMask2 hZ2 hAcctop2 hBfin2 hNfin2 hBtop2 hNtop2
  -- Acc value at s2 = (a + b) mod N
  have hr2' : regValRange L.Acc s2 n = (a + b) % N := hr2
  -- ctrl, Y preserved across the modular add (external)
  have hctrl2 : s2 ctrl = s1 ctrl := by
    rw [hs2]; exact cuccaroModAdd_preserves_external L s1 ctrl (fun j => K.hctrlAcc j) hctrlB
      (fun j => K.hctrlN j) (fun j => K.hctrlM j) K.hctrlflag K.hctrlZ
  have hY2 : ∀ j, s2 (Y j) = s1 (Y j) := fun j => by
    rw [hs2]; exact cuccaroModAdd_preserves_external L s1 (Y j) (fun i => K.hYAcc j i)
      (fun i => K.hYB j i) (fun i => K.hYN j i) (fun i => K.hYM j i) (K.hYflag j) (K.hYZ j)
  -- B per-wire preserved across the modular add
  have hBwire2 : ∀ j, j < n + 1 → s2 (L.B j) = s1 (L.B j) := fun j hj => by
    rw [hs2]; exact cuccaroModAdd_preserves_B_wire L s1 hZ1 j hj
  -- ===== STAGE 3: uncompute the mask ⇒ B clean =====
  set s3 := denote (maskCopyCtrl L Y ctrl) s2 with hs3
  -- the second maskCopyCtrl on s2: Acc/Nreg/Mask/flag/Z/Y/ctrl preserved (non-B)
  have hAcc3 : ∀ j, s3 (L.Acc j) = s2 (L.Acc j) := fun j => by
    rw [hs3]; exact maskCopyCtrl_external L Y ctrl s2 hctrlB hYB (L.Acc j) (fun i _ => (L.hAccB j i))
  have hflag3 : s3 L.flag = false := by
    rw [hs3, maskCopyCtrl_external L Y ctrl s2 hctrlB hYB L.flag (fun i _ => (L.hBflag i).symm), hflag2]
  have hAcctop3 : s3 (L.Acc n) = false := by rw [hAcc3 n, hAcctop2]
  have hMask3 : ∀ j, j < n + 1 → s3 (L.Mask j) = false := fun j hj => by
    rw [hs3, maskCopyCtrl_external L Y ctrl s2 hctrlB hYB (L.Mask j) (fun i _ => (L.hBM i j).symm)]
    exact hMask2 j hj
  have hZ3 : s3 L.Z = false := by
    rw [hs3, maskCopyCtrl_external L Y ctrl s2 hctrlB hYB L.Z (fun i _ => (L.hBZ i).symm), hZ2]
  have hN3 : ∀ j, s3 (L.Nreg j) = s2 (L.Nreg j) := fun j => by
    rw [hs3]; exact maskCopyCtrl_external L Y ctrl s2 hctrlB hYB (L.Nreg j) (fun i _ => (L.hBN i j).symm)
  have hctrl3 : s3 ctrl = s2 ctrl := by
    rw [hs3, maskCopyCtrl_external L Y ctrl s2 hctrlB hYB ctrl (fun j _ => (hctrlB j))]
  have hY3 : ∀ j, s3 (Y j) = s2 (Y j) := fun j => by
    rw [hs3]; exact maskCopyCtrl_external L Y ctrl s2 hctrlB hYB (Y j) (fun i _ => (hYB j i))
  -- B clean after the uncompute: low bits cancel, top untouched
  have hBclean : ∀ j, j < n + 1 → s3 (L.B j) = false := fun j hj => by
    rcases lt_or_ge j n with hjn | hjn
    · rw [hs3, maskCopyCtrl_B L Y ctrl s2 hctrlB hYB j hjn]
      -- s2 (B j) = s1 (B j) = s (B j) ^^ (s ctrl && s (Y j)); s (B j) = false
      have hbj : s2 (L.B j) = (s ctrl && s (Y j)) := by
        rw [hBwire2 j hj, hs1, maskCopyCtrl_B L Y ctrl s hctrlB hYB j hjn, hBtop j (by omega)]; simp
      have hcj : (s2 ctrl && s2 (Y j)) = (s ctrl && s (Y j)) := by
        rw [hctrl2, hctrl1, hY2 j, hY1 j]
      rw [hbj, hcj, Bool.xor_self]
    · have hjeq : j = n := by omega
      rw [hjeq, hs3, maskCopyCtrl_B_top L Y ctrl s2 hctrlB hYB, hBwire2 n (by omega), hs1,
        maskCopyCtrl_B_top L Y ctrl s hctrlB hYB]
      exact hBtop n (by omega)
  -- assemble the final readouts
  rw [hsf]
  refine ⟨?_, hflag3, hAcctop3, hMask3, hBclean, hZ3, ?_, ?_, ?_, ?_⟩
  · -- value: ((a+b) mod N) carried through the clean uncompute (Acc preserved in stage 3)
    rw [show regValRange L.Acc s3 n = regValRange L.Acc s2 n from
      Finset.sum_congr rfl (fun j _ => by rw [hAcc3 j]), hr2', hbb]
  · -- Y preserved
    rw [show regValRange Y s3 n = regValRange Y s n from
      Finset.sum_congr rfl (fun j _ => by rw [hY3 j, hY2 j, hY1 j]), hYval]
  · -- ctrl preserved
    rw [hctrl3, hctrl2, hctrl1]
  · -- Nreg preserved (low value)
    rw [show regValRange L.Nreg s3 n = regValRange L.Nreg s2 n from
      Finset.sum_congr rfl (fun j _ => by rw [hN3 j])]
    exact hNfin2
  · -- Nreg top wire preserved
    rw [hN3 n, hNtop2, hN1 n]

/-- **Correctness.** The bit-gated modular adder leaves `Acc = (a + (if ctrl then y else 0)) mod N`. -/
theorem cuccaroCModAdd_correct (K : CuccaroCModLayout m n) (s : State m)
    (hAccTop : s (K.mod.Acc n) = false) (hBtop : ∀ j, j < n + 1 → s (K.mod.B j) = false)
    (hNtop : s (K.mod.Nreg n) = false) (hMask0 : ∀ j, j < n + 1 → s (K.mod.Mask j) = false)
    (hflag : s K.mod.flag = false) (hZ : s K.mod.Z = false)
    {N a y : ℕ} (h2N : 2 * N ≤ 2 ^ n)
    (hAcc : regValRange K.mod.Acc s n = a) (hN : regValRange K.mod.Nreg s n = N)
    (haN : a < N) (hYval : regValRange K.Y s n = y) (hyN : y < N) :
    regValRange K.mod.Acc (denote (cuccaroCModAdd K) s) n = (a + (if s K.ctrl then y else 0)) % N :=
  (cuccaroCModAdd_spec K s hAccTop hBtop hNtop hMask0 hflag hZ h2N hAcc hN haN hYval hyN).1

/-- **The bit-gated adder is carry-clean**, including the masked operand `Mask2 = mod.B`. -/
theorem cuccaroCModAdd_clean (K : CuccaroCModLayout m n) (s : State m)
    (hAccTop : s (K.mod.Acc n) = false) (hBtop : ∀ j, j < n + 1 → s (K.mod.B j) = false)
    (hNtop : s (K.mod.Nreg n) = false) (hMask0 : ∀ j, j < n + 1 → s (K.mod.Mask j) = false)
    (hflag : s K.mod.flag = false) (hZ : s K.mod.Z = false)
    {N a y : ℕ} (h2N : 2 * N ≤ 2 ^ n)
    (hAcc : regValRange K.mod.Acc s n = a) (hN : regValRange K.mod.Nreg s n = N)
    (haN : a < N) (hYval : regValRange K.Y s n = y) (hyN : y < N) :
    denote (cuccaroCModAdd K) s K.mod.flag = false
      ∧ denote (cuccaroCModAdd K) s (K.mod.Acc n) = false
      ∧ (∀ j, j < n + 1 → denote (cuccaroCModAdd K) s (K.mod.Mask j) = false)
      ∧ (∀ j, j < n + 1 → denote (cuccaroCModAdd K) s (K.mod.B j) = false)
      ∧ denote (cuccaroCModAdd K) s K.mod.Z = false := by
  obtain ⟨-, hflag', hAcctop', hMask', hB', hZ', -, -, -, -⟩ :=
    cuccaroCModAdd_spec K s hAccTop hBtop hNtop hMask0 hflag hZ h2N hAcc hN haN hYval hyN
  exact ⟨hflag', hAcctop', hMask', hB', hZ'⟩

/-- **The operand is preserved:** `Y`, `ctrl`, and `Nreg` survive. -/
theorem cuccaroCModAdd_preserves_operand (K : CuccaroCModLayout m n) (s : State m)
    (hAccTop : s (K.mod.Acc n) = false) (hBtop : ∀ j, j < n + 1 → s (K.mod.B j) = false)
    (hNtop : s (K.mod.Nreg n) = false) (hMask0 : ∀ j, j < n + 1 → s (K.mod.Mask j) = false)
    (hflag : s K.mod.flag = false) (hZ : s K.mod.Z = false)
    {N a y : ℕ} (h2N : 2 * N ≤ 2 ^ n)
    (hAcc : regValRange K.mod.Acc s n = a) (hN : regValRange K.mod.Nreg s n = N)
    (haN : a < N) (hYval : regValRange K.Y s n = y) (hyN : y < N) :
    regValRange K.Y (denote (cuccaroCModAdd K) s) n = y
      ∧ denote (cuccaroCModAdd K) s K.ctrl = s K.ctrl
      ∧ regValRange K.mod.Nreg (denote (cuccaroCModAdd K) s) n = N := by
  obtain ⟨-, -, -, -, -, -, hY', hctrl', hN', -⟩ :=
    cuccaroCModAdd_spec K s hAccTop hBtop hNtop hMask0 hflag hZ h2N hAcc hN haN hYval hyN
  exact ⟨hY', hctrl', hN'⟩

/-- **Derived Toffoli cost: `14n + 10`.** Two control-masks (`n` `CCX` each) + the modular adder
(`12n + 10`): `n + (12n + 10) + n = 14n + 10`. -/
theorem cuccaroCModAdd_toffoli (K : CuccaroCModLayout m n) :
    (circuitCost (cuccaroCModAdd K)).toffoli = 14 * n + 10 := by
  rw [cuccaroCModAdd]
  simp only [cost_comp_toffoli_count, maskCopyCtrl_toffoli, cuccaroModAdd_toffoli]
  ring

/-- A wire disjoint from `Acc, Nreg, Mask, flag, Z` survives `cuccaroModDouble` (it touches no other
families; the addend register `B` is *not* used by the doubler). -/
theorem cuccaroModDouble_preserves_external (L : CuccaroModLayout m n) (s : State m) (w : Fin m)
    (hAcc : ∀ j, w ≠ L.Acc j) (hNg : ∀ j, w ≠ L.Nreg j) (hM : ∀ j, w ≠ L.Mask j)
    (hflag : w ≠ L.flag) (hZ : w ≠ L.Z) :
    denote (cuccaroModDouble L) s w = s w := by
  simp only [cuccaroModDouble, denote_append, denote_cons, denote_nil]
  rw [denoteGate_x_ne hflag,
    denoteGate_cx_ne hflag,
    maskCopy_external L _ w (fun j _ => hM j),
    cuccaroAdd_preserves_external L.layM _ w hZ (fun i _ => hAcc i) (fun i _ => hM i),
    maskCopy_external L _ w (fun j _ => hM j),
    denoteGate_cx_ne hflag,
    cuccaroSub_preserves_external L.layN _ w hZ (fun i _ => hAcc i) (fun i _ => hNg i),
    rotChain_external L.Acc n _ w (fun j _ => hAcc j)]

/-- A wire disjoint from `Acc, B, Nreg, Mask, flag, Z` survives `cuccaroCModAdd` (the read-only `Y`
and `ctrl` are never written). -/
theorem cuccaroCModAdd_preserves_external (K : CuccaroCModLayout m n) (s : State m) (w : Fin m)
    (hAcc : ∀ j, w ≠ K.mod.Acc j) (hB : ∀ j, w ≠ K.mod.B j) (hNg : ∀ j, w ≠ K.mod.Nreg j)
    (hM : ∀ j, w ≠ K.mod.Mask j) (hflag : w ≠ K.mod.flag) (hZ : w ≠ K.mod.Z) :
    denote (cuccaroCModAdd K) s w = s w := by
  simp only [cuccaroCModAdd, denote_append]
  rw [maskCopyCtrl_external K.mod K.Y K.ctrl _ K.hctrlB K.hYB w (fun j _ => hB j),
    cuccaroModAdd_preserves_external K.mod _ w hAcc hB hNg hM hflag hZ,
    maskCopyCtrl_external K.mod K.Y K.ctrl _ K.hctrlB K.hYB w (fun j _ => hB j)]

/-! ### The carry-clean modular multiply: the Horner fold with ONE reused scratch bank -/

/-- An `n`-bit carry-clean modular-multiply layout on `Fin m`: a single Stage-2 modular-adder layout
`mod` (its addend register `mod.B` is the shared masked-operand scratch `Mask2`), a multiplicand
register `Y`, and a multiplier register `X`. Both `Y` and `X` are disjoint from everything `mod`
touches; `X` is injective on `[0, n)`. **This is ONE shared scratch bank** — `mod` (with its
`Acc, B, Nreg, Mask, flag, Z`) is reused across all `n` Horner steps (`Θ(n)` qubits, not `Θ(n²)`). -/
structure CuccaroMulLayout (m n : ℕ) where
  /-- The shared carry-clean modular-adder layout (`mod.B` = the reused masked-operand scratch). -/
  mod : CuccaroModLayout m n
  /-- The multiplicand register `Y` (read-only, `n` bits). -/
  Y : ℕ → Fin m
  /-- The multiplier register `X` (read-only control bits; bit `n-1-j` gates step `j`). -/
  X : ℕ → Fin m
  hYAcc : ∀ i j, Y i ≠ mod.Acc j
  hYB : ∀ i j, Y i ≠ mod.B j
  hYN : ∀ i j, Y i ≠ mod.Nreg j
  hYM : ∀ i j, Y i ≠ mod.Mask j
  hYflag : ∀ i, Y i ≠ mod.flag
  hYZ : ∀ i, Y i ≠ mod.Z
  hXAcc : ∀ i j, X i ≠ mod.Acc j
  hXB : ∀ i j, X i ≠ mod.B j
  hXN : ∀ i j, X i ≠ mod.Nreg j
  hXM : ∀ i j, X i ≠ mod.Mask j
  hXflag : ∀ i, X i ≠ mod.flag
  hXZ : ∀ i, X i ≠ mod.Z

/-- The bit-gated-adder layout for step `j` (its gate is bit `X (n-1-j)`, MSB-first). -/
def CuccaroMulLayout.cmod (L : CuccaroMulLayout m n) (j : ℕ) : CuccaroCModLayout m n where
  mod := L.mod
  Y := L.Y
  ctrl := L.X (n - 1 - j)
  hYAcc := L.hYAcc; hYB := L.hYB; hYN := L.hYN; hYM := L.hYM; hYflag := L.hYflag; hYZ := L.hYZ
  hctrlAcc := fun k => L.hXAcc (n - 1 - j) k
  hctrlB := fun k => L.hXB (n - 1 - j) k
  hctrlN := fun k => L.hXN (n - 1 - j) k
  hctrlM := fun k => L.hXM (n - 1 - j) k
  hctrlflag := L.hXflag (n - 1 - j)
  hctrlZ := L.hXZ (n - 1 - j)

/-- One Horner step on the shared bank: double the accumulator, then bit-gated-add `X_{n-1-j}·Y`. -/
def cuccaroModMulStep (L : CuccaroMulLayout m n) (j : ℕ) : Circuit m :=
  cuccaroModDouble L.mod ++ cuccaroCModAdd (L.cmod j)

/-- The general-`n` carry-clean modular multiply: fold the Horner step over the `n` multiplier bits
MSB-first, reusing the single scratch bank `mod`. -/
def cuccaroModMul (L : CuccaroMulLayout m n) : Circuit m :=
  ((List.range n).map (fun j => cuccaroModMulStep L j)).flatMap id

/-- The first `k` Horner steps (the induction handle). -/
def cuccaroModMulUpto (L : CuccaroMulLayout m n) (k : ℕ) : Circuit m :=
  ((List.range k).map (fun j => cuccaroModMulStep L j)).flatMap id

theorem cuccaroModMul_eq_upto (L : CuccaroMulLayout m n) : cuccaroModMul L = cuccaroModMulUpto L n :=
  rfl

theorem cuccaroModMulUpto_succ (L : CuccaroMulLayout m n) (k : ℕ) :
    cuccaroModMulUpto L (k + 1) = cuccaroModMulUpto L k ++ cuccaroModMulStep L k := by
  simp [cuccaroModMulUpto, List.range_succ, List.map_append, List.flatMap_append]

/-- **The multiply-loop invariant.** After the first `k` Horner steps from a clean bank
(`Acc = 0`), the accumulator holds `(hornerVal bits n k · y) mod N` (`bits i = [X i]`), the whole
scratch bank is restored clean, and `Nreg`, `Y`, every `X` bit are intact. By induction on `k`. -/
theorem cuccaroModMul_invariant (L : CuccaroMulLayout m n) (s : State m)
    (hAccTop : s (L.mod.Acc n) = false) (hNtop : s (L.mod.Nreg n) = false)
    (hMask0 : ∀ j, j < n + 1 → s (L.mod.Mask j) = false)
    (hB0 : ∀ j, j < n + 1 → s (L.mod.B j) = false)
    (hflag : s L.mod.flag = false) (hZ : s L.mod.Z = false)
    {N y : ℕ} (h2N : 2 * N ≤ 2 ^ n) (hNodd : N % 2 = 1) (hNpos : 0 < N) (hyN : y < N)
    (hAcc0 : regValRange L.mod.Acc s n = 0) (hNval : regValRange L.mod.Nreg s n = N)
    (hYval : regValRange L.Y s n = y) :
    ∀ k, k ≤ n →
      regValRange L.mod.Acc (denote (cuccaroModMulUpto L k) s) n
          = (hornerVal (fun i => if s (L.X i) then 1 else 0) n k * y) % N
      ∧ denote (cuccaroModMulUpto L k) s (L.mod.Acc n) = false
      ∧ denote (cuccaroModMulUpto L k) s L.mod.flag = false
      ∧ (∀ j, j < n + 1 → denote (cuccaroModMulUpto L k) s (L.mod.Mask j) = false)
      ∧ (∀ j, j < n + 1 → denote (cuccaroModMulUpto L k) s (L.mod.B j) = false)
      ∧ denote (cuccaroModMulUpto L k) s L.mod.Z = false
      ∧ regValRange L.mod.Nreg (denote (cuccaroModMulUpto L k) s) n = N
      ∧ denote (cuccaroModMulUpto L k) s (L.mod.Nreg n) = false
      ∧ regValRange L.Y (denote (cuccaroModMulUpto L k) s) n = y
      ∧ ∀ i, denote (cuccaroModMulUpto L k) s (L.X i) = s (L.X i) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, hAccTop, hflag, hMask0, hB0, hZ, ?_, hNtop, hYval, fun i => rfl⟩
    · simp [cuccaroModMulUpto, hAcc0, hornerVal_zero]
    · simpa [cuccaroModMulUpto] using hNval
  | succ k ih =>
    intro hk1
    have hk : k < n := by omega
    obtain ⟨ihAcc, ihAccTop, ihflag, ihMask, ihB, ihZ, ihNval, ihNtop, ihYval, ihX⟩ := ih (by omega)
    set bits := fun i => if s (L.X i) then 1 else 0 with hbits
    set sk := denote (cuccaroModMulUpto L k) s with hskdef
    rw [cuccaroModMulUpto_succ, denote_append, ← hskdef]
    -- the running residue c at sk
    set c := (hornerVal bits n k * y) % N with hcdef
    have hcN : c < N := by rw [hcdef]; exact Nat.mod_lt _ hNpos
    have hAcck : regValRange L.mod.Acc sk n = c := ihAcc
    -- ===== DOUBLE on the shared bank =====
    set sd := denote (cuccaroModDouble L.mod) sk with hsddef
    have hdbl := cuccaroModDouble_spec L.mod sk ihAccTop ihNtop ihMask ihflag ihZ h2N hNodd hAcck
      ihNval hcN
    obtain ⟨hdAcc, hdflag, hdMask, hdZ, hdAcctop, hdNval, hdNtop⟩ := hdbl
    rw [← hsddef] at hdAcc hdflag hdMask hdZ hdAcctop hdNval hdNtop
    -- B clean / Y / X survive the double (external to Acc,Nreg,Mask,flag,Z)
    have hdB : ∀ j, j < n + 1 → sd (L.mod.B j) = false := fun j hj => by
      rw [hsddef, cuccaroModDouble_preserves_external L.mod sk (L.mod.B j)
        (fun i => (L.mod.hAccB i j).symm) (fun i => (L.mod.hBN j i)) (fun i => (L.mod.hBM j i))
        (L.mod.hBflag j) (L.mod.hBZ j)]
      exact ihB j hj
    have hdY : regValRange L.Y sd n = y := by
      rw [show regValRange L.Y sd n = regValRange L.Y sk n from
        Finset.sum_congr rfl (fun j _ => by
          rw [hsddef, cuccaroModDouble_preserves_external L.mod sk (L.Y j)
            (fun i => L.hYAcc j i) (fun i => L.hYN j i) (fun i => L.hYM j i)
            (L.hYflag j) (L.hYZ j)]), ihYval]
    have hdX : ∀ i, sd (L.X i) = sk (L.X i) := fun i => by
      rw [hsddef, cuccaroModDouble_preserves_external L.mod sk (L.X i)
        (fun j => L.hXAcc i j) (fun j => L.hXN i j) (fun j => L.hXM i j) (L.hXflag i) (L.hXZ i)]
    -- d := (2c) mod N < N
    set d := (2 * c) % N with hddef
    have hdN : d < N := by rw [hddef]; exact Nat.mod_lt _ hNpos
    have hAccd : regValRange L.mod.Acc sd n = d := hdAcc
    -- ===== bit-gated ADD on the shared bank =====
    set K := L.cmod k with hKdef
    have hKmod : K.mod = L.mod := rfl
    have hKY : K.Y = L.Y := rfl
    have hKctrl : K.ctrl = L.X (n - 1 - k) := rfl
    have hcm := cuccaroCModAdd_spec K sd
      (by rw [hKmod]; exact hdAcctop) (by rw [hKmod]; exact hdB)
      (by rw [hKmod]; exact hdNtop.trans ihNtop)
      (by rw [hKmod]; exact hdMask) (by rw [hKmod]; exact hdflag) (by rw [hKmod]; exact hdZ)
      h2N (by rw [hKmod]; exact hAccd) (by rw [hKmod]; exact hdNval) hdN
      (by rw [hKY]; exact hdY) hyN
    obtain ⟨hcmAcc, hcmflag, hcmAcctop, hcmMask, hcmB, hcmZ, hcmY, hcmctrl, hcmNval, hcmNtop⟩ := hcm
    -- ctrl bit value at sd = original X bit
    have hctrlval : sd K.ctrl = s (L.X (n - 1 - k)) := by
      rw [hKctrl, hdX (n - 1 - k), ihX (n - 1 - k)]
    -- X bits survive the bit-gated add (external)
    have hcmX : ∀ i, denote (cuccaroCModAdd K) sd (L.X i) = sd (L.X i) := fun i => by
      rw [cuccaroCModAdd_preserves_external K sd (L.X i)
        (by rw [hKmod]; exact fun j => L.hXAcc i j) (by rw [hKmod]; exact fun j => L.hXB i j)
        (by rw [hKmod]; exact fun j => L.hXN i j) (by rw [hKmod]; exact fun j => L.hXM i j)
        (by rw [hKmod]; exact L.hXflag i) (by rw [hKmod]; exact L.hXZ i)]
    -- unfold the step into double then bit-gated add
    have hstep : denote (cuccaroModMulStep L k) sk = denote (cuccaroCModAdd K) sd := by
      rw [hKdef, hsddef, cuccaroModMulStep, denote_append]
    rw [hstep]
    -- assemble the 10 conjuncts at step k+1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- VALUE: (hornerVal (k+1) · y) mod N
      rw [show L.mod.Acc = K.mod.Acc from rfl, hcmAcc, hctrlval, hddef, Nat.mod_add_mod, hcdef,
        horner_mod_step (hornerVal bits n k) y N (s (L.X (n - 1 - k))), hornerVal_succ]
    · rw [show L.mod.Acc = K.mod.Acc from rfl]; exact hcmAcctop
    · rw [show L.mod.flag = K.mod.flag from rfl]; exact hcmflag
    · intro j hj; rw [show L.mod.Mask = K.mod.Mask from rfl]; exact hcmMask j hj
    · intro j hj; rw [show L.mod.B = K.mod.B from rfl]; exact hcmB j hj
    · rw [show L.mod.Z = K.mod.Z from rfl]; exact hcmZ
    · rw [show L.mod.Nreg = K.mod.Nreg from rfl]; exact hcmNval
    · -- Nreg top preserved
      have h8 : denote (cuccaroCModAdd K) sd (K.mod.Nreg n) = false := by
        rw [hcmNtop]; exact hdNtop.trans ihNtop
      exact h8
    · rw [show L.Y = K.Y from rfl]; exact hcmY
    · intro i; rw [hcmX i, hdX i, ihX i]

/-- **The verified general-`n` carry-clean modular multiply.** From a clean shared bank
(`Acc = 0`, all scratch `false`, `Nreg = N`, `Y = Yval < N`, `2N ≤ 2ⁿ`, `N` odd), the loop leaves the
accumulator holding `(X · Yval) mod N`, with the multiplier `X` arbitrary. -/
theorem cuccaroModMul_correct (L : CuccaroMulLayout m n) (s : State m)
    (hAccTop : s (L.mod.Acc n) = false) (hNtop : s (L.mod.Nreg n) = false)
    (hMask0 : ∀ j, j < n + 1 → s (L.mod.Mask j) = false)
    (hB0 : ∀ j, j < n + 1 → s (L.mod.B j) = false)
    (hflag : s L.mod.flag = false) (hZ : s L.mod.Z = false)
    {N Yval : ℕ} (h2N : 2 * N ≤ 2 ^ n) (hNodd : N % 2 = 1) (hNpos : 0 < N) (hyN : Yval < N)
    (hAcc0 : regValRange L.mod.Acc s n = 0) (hNval : regValRange L.mod.Nreg s n = N)
    (hYval : regValRange L.Y s n = Yval) :
    regValRange L.mod.Acc (denote (cuccaroModMul L) s) n = (regValRange L.X s n * Yval) % N := by
  rw [cuccaroModMul_eq_upto]
  have h := (cuccaroModMul_invariant L s hAccTop hNtop hMask0 hB0 hflag hZ h2N hNodd hNpos hyN
    hAcc0 hNval hYval n (le_refl n)).1
  rw [h, ← regValRange_eq_hornerVal_bits]

/-- **The shared scratch bank is restored clean** (so the `Θ(n)` reuse is real): the carry-out
`Acc[n]`, `flag`, every `Mask`, every `Mask2 = mod.B`, and `Z` all return to `false`. -/
theorem cuccaroModMul_clean (L : CuccaroMulLayout m n) (s : State m)
    (hAccTop : s (L.mod.Acc n) = false) (hNtop : s (L.mod.Nreg n) = false)
    (hMask0 : ∀ j, j < n + 1 → s (L.mod.Mask j) = false)
    (hB0 : ∀ j, j < n + 1 → s (L.mod.B j) = false)
    (hflag : s L.mod.flag = false) (hZ : s L.mod.Z = false)
    {N Yval : ℕ} (h2N : 2 * N ≤ 2 ^ n) (hNodd : N % 2 = 1) (hNpos : 0 < N) (hyN : Yval < N)
    (hAcc0 : regValRange L.mod.Acc s n = 0) (hNval : regValRange L.mod.Nreg s n = N)
    (hYval : regValRange L.Y s n = Yval) :
    denote (cuccaroModMul L) s (L.mod.Acc n) = false
      ∧ denote (cuccaroModMul L) s L.mod.flag = false
      ∧ (∀ j, j < n + 1 → denote (cuccaroModMul L) s (L.mod.Mask j) = false)
      ∧ (∀ j, j < n + 1 → denote (cuccaroModMul L) s (L.mod.B j) = false)
      ∧ denote (cuccaroModMul L) s L.mod.Z = false := by
  rw [cuccaroModMul_eq_upto]
  obtain ⟨-, hAt, hf, hMa, hB, hZ', -, -, -, -⟩ :=
    cuccaroModMul_invariant L s hAccTop hNtop hMask0 hB0 hflag hZ h2N hNodd hNpos hyN
      hAcc0 hNval hYval n (le_refl n)
  exact ⟨hAt, hf, hMa, hB, hZ'⟩

/-- **`X` and `Y` are intact** (and `Nreg = N`): the multiplier / multiplicand survive the multiply. -/
theorem cuccaroModMul_preserves_XY (L : CuccaroMulLayout m n) (s : State m)
    (hAccTop : s (L.mod.Acc n) = false) (hNtop : s (L.mod.Nreg n) = false)
    (hMask0 : ∀ j, j < n + 1 → s (L.mod.Mask j) = false)
    (hB0 : ∀ j, j < n + 1 → s (L.mod.B j) = false)
    (hflag : s L.mod.flag = false) (hZ : s L.mod.Z = false)
    {N Yval : ℕ} (h2N : 2 * N ≤ 2 ^ n) (hNodd : N % 2 = 1) (hNpos : 0 < N) (hyN : Yval < N)
    (hAcc0 : regValRange L.mod.Acc s n = 0) (hNval : regValRange L.mod.Nreg s n = N)
    (hYval : regValRange L.Y s n = Yval) :
    (∀ i, denote (cuccaroModMul L) s (L.X i) = s (L.X i))
      ∧ regValRange L.Y (denote (cuccaroModMul L) s) n = Yval
      ∧ regValRange L.mod.Nreg (denote (cuccaroModMul L) s) n = N := by
  rw [cuccaroModMul_eq_upto]
  obtain ⟨-, -, -, -, -, -, hNv, -, hY, hX⟩ :=
    cuccaroModMul_invariant L s hAccTop hNtop hMask0 hB0 hflag hZ h2N hNodd hNpos hyN
      hAcc0 hNval hYval n (le_refl n)
  exact ⟨hX, hY, hNv⟩

/-! ### Derived cost: `(20n + 14)·n = 20n² + 14n` Toffolis -/

theorem cuccaroModMulStep_toffoli (L : CuccaroMulLayout m n) (j : ℕ) :
    (circuitCost (cuccaroModMulStep L j)).toffoli = 20 * n + 14 := by
  rw [cuccaroModMulStep, cost_comp_toffoli_count, cuccaroModDouble_toffoli, cuccaroCModAdd_toffoli]
  ring

theorem cuccaroModMulUpto_toffoli (L : CuccaroMulLayout m n) (k : ℕ) :
    (circuitCost (cuccaroModMulUpto L k)).toffoli = (20 * n + 14) * k := by
  induction k with
  | zero => simp [cuccaroModMulUpto, circuitCost]
  | succ k ih =>
    rw [cuccaroModMulUpto_succ, cost_comp_toffoli_count, ih, cuccaroModMulStep_toffoli]
    ring

/-- **Derived Toffoli cost: `(20n + 14)·n = 20n² + 14n`.** `n` Horner steps, each `20n + 14`
(doubler `6n + 4` + bit-gated adder `14n + 10`). The prize is the `Θ(n)` reusable qubit count
(one shared scratch bank), not the Toffoli constant (modular reduction per step is irreducible in
this measurement-free `CCX`-only DSL); still ~`1.5×` better than the dirty `mulLoop`'s `30n²`. -/
theorem cuccaroModMul_toffoli (L : CuccaroMulLayout m n) :
    (circuitCost (cuccaroModMul L)).toffoli = (20 * n + 14) * n := by
  rw [cuccaroModMul_eq_upto, cuccaroModMulUpto_toffoli]

/-! ### Non-vacuity witness + `#eval` / `runArr` cross-check (`n = 3`, `N = 3`)

A concrete `CuccaroMulLayout 24 3`: `Acc → {0,1,2,3}`, the shared masked-operand scratch
`Mask2 = mod.B → {4,5,6,7}`, `Nreg → {8,9,10,11}` (preset `N = 3` on wires `8,9`),
`Mask → {12,13,14,15}`, `flag → 16`, `Z → 17`, multiplicand `Y → {18,19,20}` (preset `2` on wire
`19`), multiplier `X → {21,22,23}`. `n = 3` is forced by `2N ≤ 2ⁿ` (`N = 3` needs `2ⁿ ≥ 6`). The
witnesses realise `X · 2 mod 3`: `X = 3 ↦ 0`, `X = 2 ↦ 1`, `X = 1 ↦ 2`, read off the strict `Array`
evaluator (`runArr`, via `regValRangeArr_eq`), with the **shared scratch reading clean afterward**. -/

/-- A concrete `n = 3` carry-clean modular-adder layout on `Fin 24` (the shared bank). -/
def cuccaroMulModLayout3 : CuccaroModLayout 24 3 where
  Acc i := if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else 3
  B i := if i = 0 then 4 else if i = 1 then 5 else if i = 2 then 6 else 7
  Nreg i := if i = 0 then 8 else if i = 1 then 9 else if i = 2 then 10 else 11
  Mask i := if i = 0 then 12 else if i = 1 then 13 else if i = 2 then 14 else 15
  flag := 16
  Z := 17
  hAccB i j := by split_ifs <;> decide
  hAccN i j := by split_ifs <;> decide
  hAccM i j := by split_ifs <;> decide
  hBN i j := by split_ifs <;> decide
  hBM i j := by split_ifs <;> decide
  hNM i j := by split_ifs <;> decide
  hAccflag i := by split_ifs <;> decide
  hBflag i := by split_ifs <;> decide
  hNflag i := by split_ifs <;> decide
  hMflag i := by split_ifs <;> decide
  hAccZ i := by split_ifs <;> decide
  hBZ i := by split_ifs <;> decide
  hNZ i := by split_ifs <;> decide
  hMZ i := by split_ifs <;> decide
  hflagZ := by decide
  hAccinj i j hi hj h := by split_ifs at h <;> omega
  hBinj i j hi hj h := by split_ifs at h <;> omega
  hNinj i j hi hj h := by split_ifs at h <;> omega
  hMinj i j hi hj h := by split_ifs at h <;> omega

/-- A concrete `n = 3` carry-clean modular-multiply layout on `Fin 24`. -/
def cuccaroMulLayout3 : CuccaroMulLayout 24 3 where
  mod := cuccaroMulModLayout3
  Y i := if i = 0 then 18 else if i = 1 then 19 else 20
  X i := if i = 0 then 21 else if i = 1 then 22 else 23
  hYAcc i j := by simp only [cuccaroMulModLayout3]; split_ifs <;> decide
  hYB i j := by simp only [cuccaroMulModLayout3]; split_ifs <;> decide
  hYN i j := by simp only [cuccaroMulModLayout3]; split_ifs <;> decide
  hYM i j := by simp only [cuccaroMulModLayout3]; split_ifs <;> decide
  hYflag i := by simp only [cuccaroMulModLayout3]; split_ifs <;> decide
  hYZ i := by simp only [cuccaroMulModLayout3]; split_ifs <;> decide
  hXAcc i j := by simp only [cuccaroMulModLayout3]; split_ifs <;> decide
  hXB i j := by simp only [cuccaroMulModLayout3]; split_ifs <;> decide
  hXN i j := by simp only [cuccaroMulModLayout3]; split_ifs <;> decide
  hXM i j := by simp only [cuccaroMulModLayout3]; split_ifs <;> decide
  hXflag i := by simp only [cuccaroMulModLayout3]; split_ifs <;> decide
  hXZ i := by simp only [cuccaroMulModLayout3]; split_ifs <;> decide

/-- Input state for `n = 3, N = 3, Y = 2`: `Nreg = 3` (wires `8,9`), `Y = 2` (wire `19`), multiplier
`X` bits `x0,x1,x2` (wires `21,22,23`), all of `Acc / Mask2 / Mask / flag / Z` clean. -/
def cuccaroMulState3 (x0 x1 x2 : Bool) : State 24 := fun w =>
  if w = 8 then true else if w = 9 then true        -- Nreg = 3
  else if w = 19 then true                           -- Y = 2
  else if w = 21 then x0 else if w = 22 then x1 else if w = 23 then x2
  else false

/-- The structural preconditions of `cuccaroModMul_correct` hold at `cuccaroMulState3`. -/
theorem cuccaroMulState3_pre (x0 x1 x2 : Bool) :
    cuccaroMulState3 x0 x1 x2 (cuccaroMulLayout3.mod.Acc 3) = false
      ∧ cuccaroMulState3 x0 x1 x2 (cuccaroMulLayout3.mod.Nreg 3) = false
      ∧ (∀ j, j < 3 + 1 → cuccaroMulState3 x0 x1 x2 (cuccaroMulLayout3.mod.Mask j) = false)
      ∧ (∀ j, j < 3 + 1 → cuccaroMulState3 x0 x1 x2 (cuccaroMulLayout3.mod.B j) = false)
      ∧ cuccaroMulState3 x0 x1 x2 cuccaroMulLayout3.mod.flag = false
      ∧ cuccaroMulState3 x0 x1 x2 cuccaroMulLayout3.mod.Z = false
      ∧ regValRange cuccaroMulLayout3.mod.Acc (cuccaroMulState3 x0 x1 x2) 3 = 0
      ∧ regValRange cuccaroMulLayout3.mod.Nreg (cuccaroMulState3 x0 x1 x2) 3 = 3
      ∧ regValRange cuccaroMulLayout3.Y (cuccaroMulState3 x0 x1 x2) 3 = 2 := by
  refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · intro j _; simp only [cuccaroMulLayout3, cuccaroMulModLayout3]; split_ifs <;> rfl
  · intro j _; simp only [cuccaroMulLayout3, cuccaroMulModLayout3]; split_ifs <;> rfl
  · simp [regValRange, Finset.sum_range_succ, cuccaroMulLayout3, cuccaroMulModLayout3,
      cuccaroMulState3]
  · simp [regValRange, Finset.sum_range_succ, cuccaroMulLayout3, cuccaroMulModLayout3,
      cuccaroMulState3]
  · simp [regValRange, Finset.sum_range_succ, cuccaroMulLayout3, cuccaroMulState3]

/-- The headline is non-vacuous: `cuccaroModMul_correct` applies to `cuccaroMulLayout3` with
`X = 3, Y = 2, N = 3`, giving `(3 * 2) mod 3 = 0`. -/
example : regValRange cuccaroMulLayout3.mod.Acc
    (denote (cuccaroModMul cuccaroMulLayout3) (cuccaroMulState3 true true false)) 3
      = (regValRange cuccaroMulLayout3.X (cuccaroMulState3 true true false) 3 * 2) % 3 := by
  obtain ⟨hAt, hNt, hMa, hB, hf, hZ, hA0, hNv, hYv⟩ := cuccaroMulState3_pre true true false
  exact cuccaroModMul_correct cuccaroMulLayout3 _ hAt hNt hMa hB hf hZ (by decide) (by decide)
    (by decide) (by decide) hA0 hNv hYv

-- `X = 3, Y = 2, N = 3 ↦ (3*2) mod 3 = 0`. Prints `0`, instantly (strict `Array` evaluator).
#eval regValRangeArr cuccaroMulLayout3.mod.Acc
  (runArr (cuccaroModMul cuccaroMulLayout3) (ofState (cuccaroMulState3 true true false))) 3
-- 0

-- `X = 2, Y = 2, N = 3 ↦ (2*2) mod 3 = 1`. Prints `1`.
#eval regValRangeArr cuccaroMulLayout3.mod.Acc
  (runArr (cuccaroModMul cuccaroMulLayout3) (ofState (cuccaroMulState3 false true false))) 3
-- 1

-- `X = 1, Y = 2, N = 3 ↦ (1*2) mod 3 = 2`. Prints `2`.
#eval regValRangeArr cuccaroMulLayout3.mod.Acc
  (runArr (cuccaroModMul cuccaroMulLayout3) (ofState (cuccaroMulState3 true false false))) 3
-- 2

-- The shared scratch reads CLEAN afterward (Θ(n) reuse is real): Mask2 = mod.B (wires 4..7) = 0,
-- Mask (12..15) = 0, flag (16) = false, Z (17) = false, carry-out Acc[3] (wire 3) = false.
#eval regValRangeArr cuccaroMulLayout3.mod.B
  (runArr (cuccaroModMul cuccaroMulLayout3) (ofState (cuccaroMulState3 true true false))) 4
-- 0
#eval regValRangeArr cuccaroMulLayout3.mod.Mask
  (runArr (cuccaroModMul cuccaroMulLayout3) (ofState (cuccaroMulState3 true true false))) 4
-- 0
#eval (runArr (cuccaroModMul cuccaroMulLayout3) (ofState (cuccaroMulState3 true true false)))[16]!
-- false
#eval (runArr (cuccaroModMul cuccaroMulLayout3) (ofState (cuccaroMulState3 true true false)))[17]!
-- false
#eval (runArr (cuccaroModMul cuccaroMulLayout3) (ofState (cuccaroMulState3 true true false)))[3]!
-- false

-- X, Y intact afterward: X reads `3`, Y reads `2`.
#eval regValRangeArr cuccaroMulLayout3.X
  (runArr (cuccaroModMul cuccaroMulLayout3) (ofState (cuccaroMulState3 true true false))) 3
-- 3
#eval regValRangeArr cuccaroMulLayout3.Y
  (runArr (cuccaroModMul cuccaroMulLayout3) (ofState (cuccaroMulState3 true true false))) 3
-- 2

/-- The cross-check is faithful to the `denote`-based theorem: by `regValRangeArr_eq`, the fast
`Array` value (`0`) *is* the `regValRange (denote …)` quantity `cuccaroModMul_correct` constrains. -/
example : regValRangeArr cuccaroMulLayout3.mod.Acc
    (runArr (cuccaroModMul cuccaroMulLayout3) (ofState (cuccaroMulState3 true true false))) 3
      = regValRange cuccaroMulLayout3.mod.Acc
        (denote (cuccaroModMul cuccaroMulLayout3) (cuccaroMulState3 true true false)) 3 :=
  regValRangeArr_eq cuccaroMulLayout3.mod.Acc (cuccaroModMul cuccaroMulLayout3)
    (cuccaroMulState3 true true false) 3

end Reversible
