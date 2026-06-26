import CsdLean4.Mathlib.QuantumInfo.Reversible.CuccaroAdd

/-!
# The carry-clean (ancilla-restoring) MODULAR adder  (ECDLP Phase 2, Stage 2)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

Stage 1 (`CuccaroAdd.lean`) delivered the in-place, ancilla-restoring ripple-carry adder
`cuccaroAdd : A ← (A + B) mod 2ⁿ` (`B` preserved, the single ancilla `Z` returned `false`). This
module builds, on top of it, the **carry-clean MODULAR adder** `cuccaroModAdd`:

```
Acc ← (a + b) mod N      (a, b < N, 2N ≤ 2ⁿ)
```

that leaves **every** flag / scratch / carry wire restored to its input value, so it is reusable in
place inside a multiply loop with **Θ(n)** qubits (versus the Θ(n²) fresh-ancilla penalty the dirty
`ModularAdd.modAdd` carries). This is the qubit collapse that turns the per-multiply Toffoli budget
from the fresh-ancilla `~30n²` toward `~12n²` (an `n`-fold reuse of a `12n+10`-Toffoli clean add).

## The construction (clean Beauregard, controlled-add-free)

All arithmetic runs on **`n+1`-bit** registers (the extra high wire is the sign / carry-out, which a
plain Cuccaro adder does not expose, so it is materialised as register bit `n`). With `2N ≤ 2ⁿ`, all
operands have bit `n` clear and `a + b < 2N ≤ 2ⁿ < 2ⁿ⁺¹`, so the adds never overflow `n+1` bits.

1. `Acc += B`               — `cuccaroAdd`; `Acc = a + b`.
2. `Acc -= Nreg`            — `cuccaroSub` (the `inverse` adder); `Acc = a + b − N (mod 2ⁿ⁺¹)`.
3. `flag ^= Acc[n]`         — copy the sign bit: `flag = [a + b < N]`.
4. `Mask ^= flag·Nreg`      — `n` Toffolis: `Mask = flag ? N : 0` (the masked constant — this
                              replaces a controlled adder, which the CCX-only gate set cannot build
                              without C³X).
5. `Acc += Mask`            — `cuccaroAdd`; `Acc = (a + b) mod N =: r`.
6. `Mask ^= flag·Nreg`      — uncompute the mask: `Mask = 0`.
7. `Acc -= B`               — `cuccaroSub`; sign bit `Acc[n] = [r < b] = ¬flag`.
8. `flag ^= Acc[n]; X flag` — uncompute the flag: `flag = ¬(flag ^^ ¬flag) = 0`. THE clean step.
9. `Acc += B`               — `cuccaroAdd`; restore `Acc = r`.

The flag uncompute (step 8) is the Beauregard trick: for `a, b < N`,
`(a + b mod N) < b  ⟺  a + b ≥ N  ⟺  ¬flag`, so re-deriving the comparison against the **preserved**
addend `b` recomputes the flag and a CNOT+X clears it. This is what most formalisations stop short
of; it is what makes the adder ancilla-restoring.

## What is proved (all `sorry`-free, foundational-triple-only)

* `cuccaroSub_correct` / `_preserves_B` / `_preserves_Z` / `_preserves_external` — the clean
  subtractor as the `inverse` Cuccaro adder, characterised via the bijection
  (`reversible_inverse_correct'`) and the unconditional `cuccaroAdd_preserves_Z` / `_external`.
* `cuccaroModAdd_correct`  — `regValRange Acc (denote (cuccaroModAdd L) s) n = (a + b) % N`.
* `cuccaroModAdd_clean`    — **the point**: the flag wire, the carry-out wire `Acc[n]`, every `Mask`
  scratch wire, and the ancilla `Z` are **all** restored to `false`. The adder is reusable.
* `cuccaroModAdd_preserves_operand` — the addend `B` is intact (and `Nreg = N`).
* `cuccaroModAdd_toffoli`  — derived `12n + 10` Toffolis (5 carry-out passes at `2(n+1)` + two masks
  at `n`).

## Scope (honest)

This is the carry-clean **modular adder** (Stage 2): it makes the modular ADD reusable in Θ(n)
qubits. The carry-clean modular MULTIPLY (folding this over the multiplicand bits) and the secp256k1
figure re-cost are Stage 2b / Stage 3, not built here.
-/

namespace Reversible

variable {m n : ℕ}

/-! ### Small gate-action helpers (single-wire reads of `CX` / `X` / `CCX`) -/

/-- A wire distinct from the target of a `CX` is unchanged. -/
theorem denoteGate_cx_ne {c t w : Fin m} (h : w ≠ t) (s : State m) :
    denoteGate (Gate.CX c t) s w = s w := by
  simp only [denoteGate]
  split
  · rfl
  · exact Function.update_of_ne h _ _

/-- The target of a non-degenerate `CX` reads `s c ^^ s t`. -/
theorem denoteGate_cx_target {c t : Fin m} (h : c ≠ t) (s : State m) :
    denoteGate (Gate.CX c t) s t = (s c ^^ s t) := by
  simp only [denoteGate, if_neg h]
  rw [Function.update_self]

/-- A wire distinct from the target of an `X` is unchanged. -/
theorem denoteGate_x_ne {i w : Fin m} (h : w ≠ i) (s : State m) :
    denoteGate (Gate.X i) s w = s w := by
  simp only [denoteGate]
  exact Function.update_of_ne h _ _

/-- The target of an `X` is flipped. -/
theorem denoteGate_x_target (i : Fin m) (s : State m) :
    denoteGate (Gate.X i) s i = !(s i) := by
  simp only [denoteGate]
  rw [Function.update_self]

/-- A wire distinct from the target of a `CCX` is unchanged. -/
theorem denoteGate_ccx_ne {c₁ c₂ t w : Fin m} (h : w ≠ t) (s : State m) :
    denoteGate (Gate.CCX c₁ c₂ t) s w = s w := by
  simp only [denoteGate]
  split
  · rfl
  · exact Function.update_of_ne h _ _

/-! ### The top (sign) bit of a register as a comparison -/

/-- **Register bit `k` is the `≥ 2ᵏ` comparison of the low `k+1` bits.** Reads off
`regValRange_succ` (`= low + bit·2ᵏ`, `low < 2ᵏ`): the bit is set iff the `k+1`-bit value is `≥ 2ᵏ`.
This materialises the sign / carry-out bit that the carry-clean Cuccaro adder does not expose. -/
theorem regValRange_top_bit (f : ℕ → Fin m) (s : State m) (k : ℕ) :
    s (f k) = decide (2 ^ k ≤ regValRange f s (k + 1)) := by
  have hlo : regValRange f s k < 2 ^ k := regValRange_lt f s k
  rw [regValRange_succ]
  cases h : s (f k) with
  | false =>
    simp only [Bool.toNat_false, zero_mul, add_zero]
    rw [eq_comm, decide_eq_false_iff_not]; omega
  | true =>
    simp only [Bool.toNat_true, one_mul]
    rw [eq_comm, decide_eq_true_eq]; omega

/-- A `regValRange`-congruence shortcut: equal on the low `k` wires ⇒ equal readouts. -/
private theorem rvc {f : ℕ → Fin m} {x y : State m} {k : ℕ}
    (h : ∀ j, j < k → x (f j) = y (f j)) : regValRange f x k = regValRange f y k :=
  Finset.sum_congr rfl (fun j hj => by rw [h j (Finset.mem_range.mp hj)])

/-! ### The clean subtractor: `cuccaroSub = inverse cuccaroAdd`

`cuccaroAdd` is a bijection, so its gate-reverse `inverse` is the exact inverse permutation
`Acc ← Acc − B (mod 2ⁿ)`. All four facts are characterised through the bijection identity
`denote (cuccaroAdd L) (denote (cuccaroSub L) s) = s` (`reversible_inverse_correct'`) plus the
**unconditional** forward lemmas `cuccaroAdd_preserves_Z` / `cuccaroAdd_preserves_external`. -/

/-- The clean ripple-carry **subtractor**: the gate-reverse of the Cuccaro adder. -/
def cuccaroSub (L : CuccaroLayout m n) : Circuit m := inverse (cuccaroAdd L)

/-- The subtractor restores the ancilla `Z` to its input value, unconditionally. -/
theorem cuccaroSub_preserves_Z (L : CuccaroLayout m n) (s : State m) :
    denote (cuccaroSub L) s L.Z = s L.Z := by
  have hfwd : denote (cuccaroAdd L) (denote (cuccaroSub L) s) = s :=
    reversible_inverse_correct' (cuccaroAdd L) s
  have hz := cuccaroAdd_preserves_Z L (denote (cuccaroSub L) s)
  rw [hfwd] at hz
  exact hz.symm

/-- The subtractor preserves external wires (distinct from `Z` and the used `A` / `B` wires). -/
theorem cuccaroSub_preserves_external (L : CuccaroLayout m n) (s : State m) (w : Fin m)
    (hwZ : w ≠ L.Z) (hwA : ∀ i, i < n → w ≠ L.A i) (hwB : ∀ i, i < n → w ≠ L.B i) :
    denote (cuccaroSub L) s w = s w := by
  have hfwd : denote (cuccaroAdd L) (denote (cuccaroSub L) s) = s :=
    reversible_inverse_correct' (cuccaroAdd L) s
  have hext := cuccaroAdd_preserves_external L (denote (cuccaroSub L) s) w hwZ hwA hwB
  rw [hfwd] at hext
  exact hext.symm

/-- The subtractor preserves the subtrahend register `B`. -/
theorem cuccaroSub_preserves_B (L : CuccaroLayout m n) (s : State m) (hZ : s L.Z = false)
    (k : ℕ) (hk : k < n) :
    denote (cuccaroSub L) s (L.B k) = s (L.B k) := by
  have hfwd : denote (cuccaroAdd L) (denote (cuccaroSub L) s) = s :=
    reversible_inverse_correct' (cuccaroAdd L) s
  have hrZ : denote (cuccaroSub L) s L.Z = false := by
    rw [cuccaroSub_preserves_Z L s]; exact hZ
  have hb := cuccaroAdd_preserves_B L (denote (cuccaroSub L) s) hrZ k hk
  rw [hfwd] at hb
  exact hb.symm

/-- **The clean subtractor is value-correct.** For `s Z = false`, register `A` ends holding
`(A − B) mod 2ⁿ` (in ℕ-truncation-safe form `(A + 2ⁿ − B) mod 2ⁿ`), in place, with `Z` restored. -/
theorem cuccaroSub_correct (L : CuccaroLayout m n) (s : State m) (hZ : s L.Z = false) :
    regValRange L.A (denote (cuccaroSub L) s) n
      = (regValRange L.A s n + 2 ^ n - regValRange L.B s n) % 2 ^ n := by
  have hfwd : denote (cuccaroAdd L) (denote (cuccaroSub L) s) = s :=
    reversible_inverse_correct' (cuccaroAdd L) s
  have hrZ : denote (cuccaroSub L) s L.Z = false := by
    rw [cuccaroSub_preserves_Z L s]; exact hZ
  set r := denote (cuccaroSub L) s with hr
  have hc := cuccaroAdd_correct L r hrZ
  rw [hfwd] at hc
  have hBeq : regValRange L.B s n = regValRange L.B r n := by
    apply Finset.sum_congr rfl
    intro k hk; rw [Finset.mem_range] at hk
    show (s (L.B k)).toNat * 2 ^ k = (r (L.B k)).toNat * 2 ^ k
    rw [← hfwd, cuccaroAdd_preserves_B L r hrZ k hk]
  set vAr := regValRange L.A r n with hvAr
  set vAs := regValRange L.A s n with hvAs
  set vB := regValRange L.B s n with hvB
  rw [← hBeq] at hc
  have hvArlt : vAr < 2 ^ n := regValRange_lt _ _ _
  have hvBlt : vB < 2 ^ n := regValRange_lt _ _ _
  show vAr = (vAs + 2 ^ n - vB) % 2 ^ n
  rcases lt_or_ge (vAr + vB) (2 ^ n) with hlt | hge
  · have hvAs : vAs = vAr + vB := by rw [hc, Nat.mod_eq_of_lt hlt]
    rw [hvAs, show vAr + vB + 2 ^ n - vB = vAr + 2 ^ n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hvArlt]
  · have hvAs : vAs = vAr + vB - 2 ^ n := by
      rw [hc, mod_eq_sub_of_le_of_lt_two_mul hge (by omega)]
    rw [show vAs + 2 ^ n - vB = vAr by omega, Nat.mod_eq_of_lt hvArlt]

/-- Cost of the subtractor: `2n` Toffolis (the gate-reverse of `cuccaroAdd`). -/
theorem cuccaroSub_toffoli (L : CuccaroLayout m n) :
    (circuitCost (cuccaroSub L)).toffoli = 2 * n := by
  rw [cuccaroSub, cost_inverse_toffoli, cuccaroAdd_toffoli]

/-! ### The modular-adder layout -/

/-- A carry-clean modular-adder layout on `m` wires for `n`-bit operands. -/
structure CuccaroModLayout (m n : ℕ) where
  /-- Accumulator / result register (`n+1` wires; bit `n` is the sign / carry-out, kept clean). -/
  Acc : ℕ → Fin m
  /-- Addend register (holds `b`, preserved). -/
  B : ℕ → Fin m
  /-- Constant register (preset to `N`, preserved). -/
  Nreg : ℕ → Fin m
  /-- Work register for the masked constant (init/returned `0`). -/
  Mask : ℕ → Fin m
  /-- Comparison flag (init/returned `false`). -/
  flag : Fin m
  /-- Cuccaro ancilla (init/returned `false`). -/
  Z : Fin m
  hAccB : ∀ i j, Acc i ≠ B j
  hAccN : ∀ i j, Acc i ≠ Nreg j
  hAccM : ∀ i j, Acc i ≠ Mask j
  hBN : ∀ i j, B i ≠ Nreg j
  hBM : ∀ i j, B i ≠ Mask j
  hNM : ∀ i j, Nreg i ≠ Mask j
  hAccflag : ∀ i, Acc i ≠ flag
  hBflag : ∀ i, B i ≠ flag
  hNflag : ∀ i, Nreg i ≠ flag
  hMflag : ∀ i, Mask i ≠ flag
  hAccZ : ∀ i, Acc i ≠ Z
  hBZ : ∀ i, B i ≠ Z
  hNZ : ∀ i, Nreg i ≠ Z
  hMZ : ∀ i, Mask i ≠ Z
  hflagZ : flag ≠ Z
  hAccinj : ∀ i j, i < n + 1 → j < n + 1 → Acc i = Acc j → i = j
  hBinj : ∀ i j, i < n + 1 → j < n + 1 → B i = B j → i = j
  hNinj : ∀ i j, i < n + 1 → j < n + 1 → Nreg i = Nreg j → i = j
  hMinj : ∀ i j, i < n + 1 → j < n + 1 → Mask i = Mask j → i = j

variable {L : CuccaroModLayout m n}

/-- `Acc += B` Cuccaro layout (width `n+1`). -/
def CuccaroModLayout.layB (L : CuccaroModLayout m n) : CuccaroLayout m (n + 1) where
  A := L.Acc; B := L.B; Z := L.Z
  hAB := L.hAccB; hAZ := L.hAccZ; hBZ := L.hBZ; hAinj := L.hAccinj; hBinj := L.hBinj

/-- `Acc -= Nreg` Cuccaro layout (width `n+1`). -/
def CuccaroModLayout.layN (L : CuccaroModLayout m n) : CuccaroLayout m (n + 1) where
  A := L.Acc; B := L.Nreg; Z := L.Z
  hAB := L.hAccN; hAZ := L.hAccZ; hBZ := L.hNZ; hAinj := L.hAccinj; hBinj := L.hNinj

/-- `Acc += Mask` Cuccaro layout (width `n+1`). -/
def CuccaroModLayout.layM (L : CuccaroModLayout m n) : CuccaroLayout m (n + 1) where
  A := L.Acc; B := L.Mask; Z := L.Z
  hAB := L.hAccM; hAZ := L.hAccZ; hBZ := L.hMZ; hAinj := L.hAccinj; hBinj := L.hMinj

/-! ### The mask gadget: `Mask ^= flag · Nreg` -/

/-- The first `k` masked-copy gates: `CCX flag Nreg[i] Mask[i]` for `i < k`. -/
def maskCopyPrefix (L : CuccaroModLayout m n) (k : ℕ) : Circuit m :=
  (List.range k).map (fun i => Gate.CCX L.flag (L.Nreg i) (L.Mask i))

/-- The masked copy: all `n` gates `CCX flag Nreg[i] Mask[i]`. Self-inverse (applied twice it clears
`Mask`); it realises the conditional reduction without a controlled adder. -/
def maskCopy (L : CuccaroModLayout m n) : Circuit m := maskCopyPrefix L n

theorem maskCopyPrefix_succ (L : CuccaroModLayout m n) (k : ℕ) (s : State m) :
    denote (maskCopyPrefix L (k + 1)) s
      = denoteGate (Gate.CCX L.flag (L.Nreg k) (L.Mask k)) (denote (maskCopyPrefix L k) s) := by
  simp only [maskCopyPrefix, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    denote_append, denote_cons, denote_nil]

/-- **The mask gadget invariant.** After `k` gates: `Mask j` (for `j < k`) holds
`Mask j ^^ (flag ∧ Nreg j)`; `Mask j` for `k ≤ j ≤ n` is untouched; every non-`Mask` wire (in
particular `flag`, `Nreg`, `Acc`, `B`, `Z`) is preserved. -/
theorem maskCopyPrefix_spec (L : CuccaroModLayout m n) (s : State m) :
    ∀ k, k ≤ n →
      (∀ j, j < k → denote (maskCopyPrefix L k) s (L.Mask j)
          = (s (L.Mask j) ^^ (s L.flag && s (L.Nreg j))))
      ∧ (∀ j, k ≤ j → j < n + 1 → denote (maskCopyPrefix L k) s (L.Mask j) = s (L.Mask j))
      ∧ (∀ w, (∀ j, j < n → w ≠ L.Mask j) → denote (maskCopyPrefix L k) s w = s w) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_⟩
    · intro j hj; omega
    · intro j _ _; simp [maskCopyPrefix]
    · intro w _; simp [maskCopyPrefix]
  | succ k ih =>
    intro hk
    have hkn : k ≤ n := by omega
    have hkltn : k < n := hk
    obtain ⟨ih1, ih2, ih3⟩ := ih hkn
    set sk := denote (maskCopyPrefix L k) s with hskdef
    have hflagk : sk L.flag = s L.flag := ih3 L.flag (fun j _ => (L.hMflag j).symm)
    have hNregk : sk (L.Nreg k) = s (L.Nreg k) := ih3 (L.Nreg k) (fun j _ => L.hNM k j)
    have hMaskk : sk (L.Mask k) = s (L.Mask k) := ih2 k (le_refl k) (by omega)
    have hstep := maskCopyPrefix_succ L k s
    rw [← hskdef] at hstep
    have hMaskne : ∀ j, j ≠ k → j < n + 1 → L.Mask j ≠ L.Mask k := by
      intro j hj hjn h
      exact hj (L.hMinj j k hjn (by omega) h)
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      rw [hstep]
      rcases eq_or_ne j k with rfl | hjk
      · have key : denoteGate (Gate.CCX L.flag (L.Nreg j) (L.Mask j)) sk (L.Mask j)
              = (sk (L.Mask j) ^^ (sk L.flag && sk (L.Nreg j))) := by
          simp only [denoteGate]
          rw [if_neg (by
            rintro (h | h)
            · exact (L.hMflag j) h
            · exact (L.hNM j j) h.symm)]
          rw [Function.update_self]
        rw [key, hMaskk, hflagk, hNregk]
      · rw [denoteGate_ccx_ne (hMaskne j hjk (by omega))]
        exact ih1 j (by omega)
    · intro j hjk hjn
      rw [hstep, denoteGate_ccx_ne (hMaskne j (by omega) hjn)]
      exact ih2 j (by omega) hjn
    · intro w hw
      rw [hstep, denoteGate_ccx_ne (hw k hkltn)]
      exact ih3 w hw

/-- Masked copy, computed clause (`j < n`). -/
theorem maskCopy_Mask (L : CuccaroModLayout m n) (s : State m) (j : ℕ) (hj : j < n) :
    denote (maskCopy L) s (L.Mask j) = (s (L.Mask j) ^^ (s L.flag && s (L.Nreg j))) :=
  ((maskCopyPrefix_spec L s n (le_refl n)).1) j hj

/-- Masked copy, top wire `Mask n` is untouched. -/
theorem maskCopy_Mask_top (L : CuccaroModLayout m n) (s : State m) :
    denote (maskCopy L) s (L.Mask n) = s (L.Mask n) :=
  ((maskCopyPrefix_spec L s n (le_refl n)).2.1) n (le_refl n) (by omega)

/-- Masked copy preserves every non-`Mask` wire. -/
theorem maskCopy_external (L : CuccaroModLayout m n) (s : State m) (w : Fin m)
    (hw : ∀ j, j < n → w ≠ L.Mask j) :
    denote (maskCopy L) s w = s w :=
  ((maskCopyPrefix_spec L s n (le_refl n)).2.2) w hw

theorem maskCopyPrefix_toffoli (L : CuccaroModLayout m n) (k : ℕ) :
    (circuitCost (maskCopyPrefix L k)).toffoli = k := by
  induction k with
  | zero => simp [maskCopyPrefix, circuitCost]
  | succ k ih =>
    have hsplit : maskCopyPrefix L (k + 1)
        = maskCopyPrefix L k ++ [Gate.CCX L.flag (L.Nreg k) (L.Mask k)] := by
      simp [maskCopyPrefix, List.range_succ, List.map_append]
    rw [hsplit, cost_comp_toffoli_count, ih]
    simp [circuitCost, gateCost]

theorem maskCopy_toffoli (L : CuccaroModLayout m n) :
    (circuitCost (maskCopy L)).toffoli = n :=
  maskCopyPrefix_toffoli L n

/-! ### The modular adder -/

/-- **The carry-clean modular adder.** Nine stages (5 Cuccaro passes + 2 masks + 3 single gates);
see the module header for the schematic. -/
def cuccaroModAdd (L : CuccaroModLayout m n) : Circuit m :=
  cuccaroAdd L.layB
    ++ cuccaroSub L.layN
    ++ [Gate.CX (L.Acc n) L.flag]
    ++ maskCopy L
    ++ cuccaroAdd L.layM
    ++ maskCopy L
    ++ cuccaroSub L.layB
    ++ [Gate.CX (L.Acc n) L.flag, Gate.X L.flag]
    ++ cuccaroAdd L.layB

/-- Placeholder spec; proven below. -/
theorem cuccaroModAdd_spec (L : CuccaroModLayout m n) (s : State m)
    (hAccTop : s (L.Acc n) = false) (hBtop : s (L.B n) = false) (hNtop : s (L.Nreg n) = false)
    (hMask0 : ∀ j, j < n + 1 → s (L.Mask j) = false)
    (hflag : s L.flag = false) (hZ : s L.Z = false)
    {N a b : ℕ} (h2N : 2 * N ≤ 2 ^ n)
    (hAcc : regValRange L.Acc s n = a) (hB : regValRange L.B s n = b)
    (hN : regValRange L.Nreg s n = N) (haN : a < N) (hbN : b < N) :
    regValRange L.Acc (denote (cuccaroModAdd L) s) n = (a + b) % N
      ∧ denote (cuccaroModAdd L) s L.flag = false
      ∧ (∀ j, j < n + 1 → denote (cuccaroModAdd L) s (L.Mask j) = false)
      ∧ denote (cuccaroModAdd L) s L.Z = false
      ∧ denote (cuccaroModAdd L) s (L.Acc n) = false
      ∧ regValRange L.B (denote (cuccaroModAdd L) s) n = b
      ∧ regValRange L.Nreg (denote (cuccaroModAdd L) s) n = N
      ∧ denote (cuccaroModAdd L) s (L.B n) = s (L.B n)
      ∧ denote (cuccaroModAdd L) s (L.Nreg n) = s (L.Nreg n) := by
  -- numeric prelims
  have hQpos : 0 < 2 ^ n := Nat.two_pow_pos n
  have hP : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le a) haN
  -- width-(n+1) initial readouts
  have hvAcc0 : regValRange L.Acc s (n + 1) = a := by rw [regValRange_succ, hAcc, hAccTop]; simp
  have hvB0 : regValRange L.B s (n + 1) = b := by rw [regValRange_succ, hB, hBtop]; simp
  have hvN0 : regValRange L.Nreg s (n + 1) = N := by rw [regValRange_succ, hN, hNtop]; simp
  -- decompose the circuit into 9 stages
  set s1 := denote (cuccaroAdd L.layB) s with hs1
  set s2 := denote (cuccaroSub L.layN) s1 with hs2
  set s3 := denoteGate (Gate.CX (L.Acc n) L.flag) s2 with hs3
  set s4 := denote (maskCopy L) s3 with hs4
  set s5 := denote (cuccaroAdd L.layM) s4 with hs5
  set s6 := denote (maskCopy L) s5 with hs6
  set s7 := denote (cuccaroSub L.layB) s6 with hs7
  set s8 := denoteGate (Gate.X L.flag) (denoteGate (Gate.CX (L.Acc n) L.flag) s7) with hs8
  set s9 := denote (cuccaroAdd L.layB) s8 with hs9
  have hsf : denote (cuccaroModAdd L) s = s9 := by
    rw [hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]
    simp only [cuccaroModAdd, denote_append, denote_cons, denote_nil]
  -- ===== ancilla Z clean throughout =====
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
  have hZ9 : s9 L.Z = false := by
    have h : denote (cuccaroAdd L.layB) s8 L.Z = s8 L.Z := cuccaroAdd_preserves_Z L.layB s8
    rw [hs9, h]; exact hZ8
  -- ===== STAGE 1: Acc += B =====
  have hAcc1 : regValRange L.Acc s1 (n + 1) = a + b := by
    have h := cuccaroAdd_correct L.layB s hZ
    rw [← hs1] at h
    rw [show regValRange L.Acc s1 (n + 1)
          = (regValRange L.Acc s (n + 1) + regValRange L.B s (n + 1)) % 2 ^ (n + 1) from h,
        hvAcc0, hvB0, Nat.mod_eq_of_lt (by omega)]
  have hB1 : ∀ j, j < n + 1 → s1 (L.B j) = s (L.B j) := fun j hj => by
    rw [hs1]; exact cuccaroAdd_preserves_B L.layB s hZ j hj
  have hN1 : ∀ j, j < n + 1 → s1 (L.Nreg j) = s (L.Nreg j) := fun j _ => by
    rw [hs1]
    exact cuccaroAdd_preserves_external L.layB s (L.Nreg j) (L.hNZ j)
      (fun i _ => (L.hAccN i j).symm) (fun i _ => (L.hBN i j).symm)
  have hMa1 : ∀ j, j < n + 1 → s1 (L.Mask j) = s (L.Mask j) := fun j _ => by
    rw [hs1]
    exact cuccaroAdd_preserves_external L.layB s (L.Mask j) (L.hMZ j)
      (fun i _ => (L.hAccM i j).symm) (fun i _ => (L.hBM i j).symm)
  have hflag1 : s1 L.flag = false := by
    rw [hs1, cuccaroAdd_preserves_external L.layB s L.flag L.hflagZ
      (fun i _ => (L.hAccflag i).symm) (fun i _ => (L.hBflag i).symm)]; exact hflag
  have hvN1 : regValRange L.Nreg s1 (n + 1) = N := by rw [rvc hN1, hvN0]
  -- ===== STAGE 2: Acc -= Nreg =====
  have hAcc2 : regValRange L.Acc s2 (n + 1) = (a + b + 2 ^ (n + 1) - N) % 2 ^ (n + 1) := by
    have h := cuccaroSub_correct L.layN s1 hZ1
    rw [← hs2] at h
    rw [show regValRange L.Acc s2 (n + 1)
          = (regValRange L.Acc s1 (n + 1) + 2 ^ (n + 1) - regValRange L.Nreg s1 (n + 1))
            % 2 ^ (n + 1) from h, hAcc1, hvN1]
  have hN2 : ∀ j, j < n + 1 → s2 (L.Nreg j) = s1 (L.Nreg j) := fun j hj => by
    rw [hs2]; exact cuccaroSub_preserves_B L.layN s1 hZ1 j hj
  have hB2 : ∀ j, j < n + 1 → s2 (L.B j) = s1 (L.B j) := fun j _ => by
    rw [hs2]
    exact cuccaroSub_preserves_external L.layN s1 (L.B j) (L.hBZ j)
      (fun i _ => (L.hAccB i j).symm) (fun i _ => L.hBN j i)
  have hMa2 : ∀ j, j < n + 1 → s2 (L.Mask j) = s1 (L.Mask j) := fun j _ => by
    rw [hs2]
    exact cuccaroSub_preserves_external L.layN s1 (L.Mask j) (L.hMZ j)
      (fun i _ => (L.hAccM i j).symm) (fun i _ => (L.hNM i j).symm)
  have hflag2 : s2 L.flag = false := by
    rw [hs2, cuccaroSub_preserves_external L.layN s1 L.flag L.hflagZ
      (fun i _ => (L.hAccflag i).symm) (fun i _ => (L.hNflag i).symm)]; exact hflag1
  -- ===== flag = [a+b < N] =====
  have hFeq : s2 (L.Acc n) = decide (a + b < N) := by
    rw [regValRange_top_bit L.Acc s2 n, hAcc2]
    rcases lt_or_ge (a + b) N with hlt | hge
    · rw [Nat.mod_eq_of_lt (show a + b + 2 ^ (n + 1) - N < 2 ^ (n + 1) by omega),
        show decide (a + b < N) = true from by rw [decide_eq_true_eq]; exact hlt,
        decide_eq_true_eq]
      omega
    · rw [show (a + b + 2 ^ (n + 1) - N) % 2 ^ (n + 1) = a + b - N from by
          rw [show a + b + 2 ^ (n + 1) - N = (a + b - N) + 2 ^ (n + 1) by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)],
        show decide (a + b < N) = false from by rw [decide_eq_false_iff_not]; omega,
        decide_eq_false_iff_not]
      omega
  -- ===== STAGE 3: flag ^= Acc[n] =====
  have hs3flag : s3 L.flag = s2 (L.Acc n) := by
    rw [hs3, denoteGate_cx_target (L.hAccflag n) s2, hflag2, Bool.xor_false]
  have hAcc3 : regValRange L.Acc s3 (n + 1) = regValRange L.Acc s2 (n + 1) :=
    rvc (fun j _ => by rw [hs3]; exact denoteGate_cx_ne (L.hAccflag j) s2)
  have hN3 : ∀ j, j < n + 1 → s3 (L.Nreg j) = s2 (L.Nreg j) := fun j _ => by
    rw [hs3]; exact denoteGate_cx_ne (L.hNflag j) s2
  have hMa3 : ∀ j, j < n + 1 → s3 (L.Mask j) = s2 (L.Mask j) := fun j _ => by
    rw [hs3]; exact denoteGate_cx_ne (L.hMflag j) s2
  have hMask3 : ∀ j, j < n + 1 → s3 (L.Mask j) = false := fun j hj => by
    rw [hMa3 j hj, hMa2 j hj, hMa1 j hj, hMask0 j hj]
  have hNs3 : regValRange L.Nreg s3 n = N := by
    rw [rvc (k := n) (fun j hj => by rw [hN3 j (by omega), hN2 j (by omega), hN1 j (by omega)]), hN]
  -- ===== STAGE 4: Mask ^= flag·Nreg =====
  have hAcc4 : regValRange L.Acc s4 (n + 1) = regValRange L.Acc s3 (n + 1) :=
    rvc (fun j _ => by rw [hs4]; exact maskCopy_external L s3 (L.Acc j) (fun i _ => L.hAccM j i))
  have hN4 : ∀ j, j < n + 1 → s4 (L.Nreg j) = s3 (L.Nreg j) := fun j _ => by
    rw [hs4]; exact maskCopy_external L s3 (L.Nreg j) (fun i _ => L.hNM j i)
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
  -- flag preserved through stages 4..7
  have hflag4 : s4 L.flag = s3 L.flag := by
    rw [hs4]; exact maskCopy_external L s3 L.flag (fun j _ => (L.hMflag j).symm)
  have hflag5 : s5 L.flag = s4 L.flag := by
    rw [hs5]; exact cuccaroAdd_preserves_external L.layM s4 L.flag L.hflagZ
      (fun i _ => (L.hAccflag i).symm) (fun i _ => (L.hMflag i).symm)
  have hflag6 : s6 L.flag = s5 L.flag := by
    rw [hs6]; exact maskCopy_external L s5 L.flag (fun j _ => (L.hMflag j).symm)
  have hflag7 : s7 L.flag = s6 L.flag := by
    rw [hs7]; exact cuccaroSub_preserves_external L.layB s6 L.flag L.hflagZ
      (fun i _ => (L.hAccflag i).symm) (fun i _ => (L.hBflag i).symm)
  have hN5 : ∀ j, j < n + 1 → s5 (L.Nreg j) = s4 (L.Nreg j) := fun j _ => by
    rw [hs5]; exact cuccaroAdd_preserves_external L.layM s4 (L.Nreg j) (L.hNZ j)
      (fun i _ => (L.hAccN i j).symm) (fun i _ => L.hNM j i)
  -- ===== STAGE 5: Acc += Mask;  Acc = (a+b) mod N =====
  have hr5 : regValRange L.Acc s5 (n + 1) = (a + b) % N := by
    have h := cuccaroAdd_correct L.layM s4 hZ4
    rw [← hs5] at h
    rw [show regValRange L.Acc s5 (n + 1)
          = (regValRange L.Acc s4 (n + 1) + regValRange L.Mask s4 (n + 1)) % 2 ^ (n + 1) from h,
        hAcc4, hAcc3, hAcc2, hvM4, hNs3, hs3flag, hFeq]
    rcases lt_or_ge (a + b) N with hlt | hge
    · rw [show decide (a + b < N) = true from by rw [decide_eq_true_eq]; exact hlt,
        Bool.toNat_true, one_mul,
        Nat.mod_eq_of_lt (show a + b + 2 ^ (n + 1) - N < 2 ^ (n + 1) by omega),
        show a + b + 2 ^ (n + 1) - N + N = a + b + 2 ^ (n + 1) by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (show a + b < 2 ^ (n + 1) by omega)]
      exact (Nat.mod_eq_of_lt hlt).symm
    · have hD : (a + b + 2 ^ (n + 1) - N) % 2 ^ (n + 1) = a + b - N := by
        rw [show a + b + 2 ^ (n + 1) - N = (a + b - N) + 2 ^ (n + 1) by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
      rw [show decide (a + b < N) = false from by rw [decide_eq_false_iff_not]; omega,
        Bool.toNat_false, zero_mul, add_zero, hD, Nat.mod_eq_of_lt (show a + b - N < 2 ^ (n + 1) by omega)]
      exact (mod_eq_sub_of_le_of_lt_two_mul hge (by omega)).symm
  -- ===== STAGE 6: uncompute Mask =====
  have hAcc6 : regValRange L.Acc s6 (n + 1) = regValRange L.Acc s5 (n + 1) :=
    rvc (fun j _ => by rw [hs6]; exact maskCopy_external L s5 (L.Acc j) (fun i _ => L.hAccM j i))
  have hN6 : ∀ j, j < n + 1 → s6 (L.Nreg j) = s5 (L.Nreg j) := fun j _ => by
    rw [hs6]; exact maskCopy_external L s5 (L.Nreg j) (fun i _ => L.hNM j i)
  have hM5eq : ∀ j, j < n + 1 → s5 (L.Mask j) = s4 (L.Mask j) := fun j hj => by
    rw [hs5]; exact cuccaroAdd_preserves_B L.layM s4 hZ4 j hj
  have hMask6 : ∀ j, j < n + 1 → s6 (L.Mask j) = false := fun j hj => by
    rcases lt_or_ge j n with hjn | hjn
    · rw [hs6, maskCopy_Mask L s5 j hjn, hM5eq j hj, hM4_lo j hjn]
      have e2 : s5 L.flag = s3 L.flag := by rw [hflag5, hflag4]
      have e3 : s5 (L.Nreg j) = s3 (L.Nreg j) := by rw [hN5 j hj, hN4 j hj]
      rw [e2, e3]; simp
    · have hjeq : j = n := by omega
      rw [hjeq, hs6, maskCopy_Mask_top L s5, hM5eq n (by omega), hM4_top]
  have hvAcc6 : regValRange L.Acc s6 (n + 1) = (a + b) % N := by rw [hAcc6, hr5]
  -- ===== B preserved across all stages (for steps 7,9 + operand) =====
  have hB3 : ∀ j, j < n + 1 → s3 (L.B j) = s2 (L.B j) := fun j _ => by
    rw [hs3]; exact denoteGate_cx_ne (L.hBflag j) s2
  have hB4 : ∀ j, j < n + 1 → s4 (L.B j) = s3 (L.B j) := fun j _ => by
    rw [hs4]; exact maskCopy_external L s3 (L.B j) (fun i _ => L.hBM j i)
  have hB5 : ∀ j, j < n + 1 → s5 (L.B j) = s4 (L.B j) := fun j _ => by
    rw [hs5]; exact cuccaroAdd_preserves_external L.layM s4 (L.B j) (L.hBZ j)
      (fun i _ => (L.hAccB i j).symm) (fun i _ => L.hBM j i)
  have hB6 : ∀ j, j < n + 1 → s6 (L.B j) = s5 (L.B j) := fun j _ => by
    rw [hs6]; exact maskCopy_external L s5 (L.B j) (fun i _ => L.hBM j i)
  have hvB6 : regValRange L.B s6 (n + 1) = b := by
    rw [rvc (k := n + 1) (fun j hj => by
      rw [hB6 j hj, hB5 j hj, hB4 j hj, hB3 j hj, hB2 j hj, hB1 j hj]), hvB0]
  -- ===== STAGE 7: Acc -= B; sign bit = [r < b] =====
  have hvAcc7 : regValRange L.Acc s7 (n + 1) = ((a + b) % N + 2 ^ (n + 1) - b) % 2 ^ (n + 1) := by
    have h := cuccaroSub_correct L.layB s6 hZ6
    rw [← hs7] at h
    rw [show regValRange L.Acc s7 (n + 1)
          = (regValRange L.Acc s6 (n + 1) + 2 ^ (n + 1) - regValRange L.B s6 (n + 1))
            % 2 ^ (n + 1) from h, hvAcc6, hvB6]
  have hB7 : ∀ j, j < n + 1 → s7 (L.B j) = s6 (L.B j) := fun j hj => by
    rw [hs7]; exact cuccaroSub_preserves_B L.layB s6 hZ6 j hj
  -- flag-complementarity
  have hcomp : (s7 (L.Acc n) ^^ s3 L.flag) = true := by
    rw [regValRange_top_bit L.Acc s7 n, hvAcc7, hs3flag, hFeq]
    have hrltN : (a + b) % N < N := Nat.mod_lt _ hNpos
    rcases lt_or_ge (a + b) N with hlt | hge
    · have hr : (a + b) % N = a + b := Nat.mod_eq_of_lt hlt
      rw [show ((a + b) % N + 2 ^ (n + 1) - b) % 2 ^ (n + 1) = (a + b) % N - b from by
          rw [show (a + b) % N + 2 ^ (n + 1) - b = ((a + b) % N - b) + 2 ^ (n + 1) by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)],
        show decide (a + b < N) = true from by rw [decide_eq_true_eq]; exact hlt,
        show decide (2 ^ n ≤ (a + b) % N - b) = false from by rw [decide_eq_false_iff_not]; omega]
      rfl
    · have hr : (a + b) % N = a + b - N := mod_eq_sub_of_le_of_lt_two_mul hge (by omega)
      rw [Nat.mod_eq_of_lt (show (a + b) % N + 2 ^ (n + 1) - b < 2 ^ (n + 1) by omega),
        show decide (a + b < N) = false from by rw [decide_eq_false_iff_not]; omega,
        show decide (2 ^ n ≤ (a + b) % N + 2 ^ (n + 1) - b) = true from by
          rw [decide_eq_true_eq]; omega]
      rfl
  -- ===== STAGE 8: flag uncompute =====
  have hAcc8 : regValRange L.Acc s8 (n + 1) = regValRange L.Acc s7 (n + 1) :=
    rvc (fun j _ => by rw [hs8, denoteGate_x_ne (L.hAccflag j), denoteGate_cx_ne (L.hAccflag j)])
  have hB8 : ∀ j, j < n + 1 → s8 (L.B j) = s7 (L.B j) := fun j _ => by
    rw [hs8, denoteGate_x_ne (L.hBflag j), denoteGate_cx_ne (L.hBflag j)]
  have hvB8 : regValRange L.B s8 (n + 1) = b := by
    rw [rvc (k := n + 1) (fun j hj => by
      rw [hB8 j hj, hB7 j hj, hB6 j hj, hB5 j hj, hB4 j hj, hB3 j hj, hB2 j hj, hB1 j hj]), hvB0]
  have hf8 : s8 L.flag = false := by
    have h7f : s7 L.flag = s3 L.flag := by rw [hflag7, hflag6, hflag5, hflag4]
    rw [hs8, denoteGate_x_target, denoteGate_cx_target (L.hAccflag n), h7f]
    simp only [hcomp, Bool.not_true]
  -- ===== STAGE 9: Acc += B; restore Acc = r =====
  have hvAcc9 : regValRange L.Acc s9 (n + 1) = (a + b) % N := by
    have h := cuccaroAdd_correct L.layB s8 hZ8
    rw [← hs9] at h
    rw [show regValRange L.Acc s9 (n + 1)
          = (regValRange L.Acc s8 (n + 1) + regValRange L.B s8 (n + 1)) % 2 ^ (n + 1) from h,
        hAcc8, hvAcc7, hvB8]
    have hrlt : (a + b) % N < 2 ^ n := lt_of_lt_of_le (Nat.mod_lt _ hNpos) (by omega)
    rw [Nat.mod_add_mod,
      show (a + b) % N + 2 ^ (n + 1) - b + b = (a + b) % N + 2 ^ (n + 1) by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hAcctop9 : s9 (L.Acc n) = false := by
    rw [regValRange_top_bit L.Acc s9 n, hvAcc9]
    have hrlt : (a + b) % N < 2 ^ n := lt_of_lt_of_le (Nat.mod_lt _ hNpos) (by omega)
    rw [decide_eq_false_iff_not]; omega
  have hval : regValRange L.Acc s9 n = (a + b) % N := by
    have hsucc := regValRange_succ L.Acc s9 n
    rw [hAcctop9] at hsucc
    simp only [Bool.toNat_false, zero_mul, add_zero] at hsucc
    rw [← hsucc, hvAcc9]
  -- flag clean: s9 = s8 on flag (external)
  have hflag9 : s9 L.flag = false := by
    rw [hs9, cuccaroAdd_preserves_external L.layB s8 L.flag L.hflagZ
      (fun i _ => (L.hAccflag i).symm) (fun i _ => (L.hBflag i).symm)]
    exact hf8
  -- Mask clean: preserved s6 → s9
  have hMask7 : ∀ j, j < n + 1 → s7 (L.Mask j) = s6 (L.Mask j) := fun j _ => by
    rw [hs7]; exact cuccaroSub_preserves_external L.layB s6 (L.Mask j) (L.hMZ j)
      (fun i _ => (L.hAccM i j).symm) (fun i _ => (L.hBM i j).symm)
  have hMask8 : ∀ j, j < n + 1 → s8 (L.Mask j) = s7 (L.Mask j) := fun j _ => by
    rw [hs8, denoteGate_x_ne (L.hMflag j), denoteGate_cx_ne (L.hMflag j)]
  have hMask9 : ∀ j, j < n + 1 → s9 (L.Mask j) = false := fun j hj => by
    rw [hs9, cuccaroAdd_preserves_external L.layB s8 (L.Mask j) (L.hMZ j)
      (fun i _ => (L.hAccM i j).symm) (fun i _ => (L.hBM i j).symm),
      hMask8 j hj, hMask7 j hj, hMask6 j hj]
  -- B / Nreg preserved (operand)
  have hB9 : ∀ j, j < n + 1 → s9 (L.B j) = s8 (L.B j) := fun j hj => by
    rw [hs9]; exact cuccaroAdd_preserves_B L.layB s8 hZ8 j hj
  have hBfinal : regValRange L.B s9 n = b := by
    rw [rvc (k := n) (fun j hj => by
      rw [hB9 j (by omega), hB8 j (by omega), hB7 j (by omega), hB6 j (by omega), hB5 j (by omega),
        hB4 j (by omega), hB3 j (by omega), hB2 j (by omega), hB1 j (by omega)]), hB]
  have hN7 : ∀ j, j < n + 1 → s7 (L.Nreg j) = s6 (L.Nreg j) := fun j _ => by
    rw [hs7]; exact cuccaroSub_preserves_external L.layB s6 (L.Nreg j) (L.hNZ j)
      (fun i _ => (L.hAccN i j).symm) (fun i _ => (L.hBN i j).symm)
  have hN8 : ∀ j, j < n + 1 → s8 (L.Nreg j) = s7 (L.Nreg j) := fun j _ => by
    rw [hs8, denoteGate_x_ne (L.hNflag j), denoteGate_cx_ne (L.hNflag j)]
  have hN9 : ∀ j, j < n + 1 → s9 (L.Nreg j) = s8 (L.Nreg j) := fun j _ => by
    rw [hs9]; exact cuccaroAdd_preserves_external L.layB s8 (L.Nreg j) (L.hNZ j)
      (fun i _ => (L.hAccN i j).symm) (fun i _ => (L.hBN i j).symm)
  have hNfinal : regValRange L.Nreg s9 n = N := by
    rw [rvc (k := n) (fun j hj => by
      rw [hN9 j (by omega), hN8 j (by omega), hN7 j (by omega), hN6 j (by omega), hN5 j (by omega),
        hN4 j (by omega), hN3 j (by omega), hN2 j (by omega), hN1 j (by omega)]), hN]
  -- top padding wires `B[n]`, `Nreg[n]` are restored (F1: exported for the multiply-loop caller)
  have hBtop9 : s9 (L.B n) = s (L.B n) := by
    rw [hB9 n (by omega), hB8 n (by omega), hB7 n (by omega), hB6 n (by omega), hB5 n (by omega),
      hB4 n (by omega), hB3 n (by omega), hB2 n (by omega), hB1 n (by omega)]
  have hNtop9 : s9 (L.Nreg n) = s (L.Nreg n) := by
    rw [hN9 n (by omega), hN8 n (by omega), hN7 n (by omega), hN6 n (by omega), hN5 n (by omega),
      hN4 n (by omega), hN3 n (by omega), hN2 n (by omega), hN1 n (by omega)]
  -- assemble
  rw [hsf]
  exact ⟨hval, hflag9, hMask9, hZ9, hAcctop9, hBfinal, hNfinal, hBtop9, hNtop9⟩

/-- **Correctness.** The carry-clean modular adder leaves `Acc = (a + b) mod N`. -/
theorem cuccaroModAdd_correct (L : CuccaroModLayout m n) (s : State m)
    (hAccTop : s (L.Acc n) = false) (hBtop : s (L.B n) = false) (hNtop : s (L.Nreg n) = false)
    (hMask0 : ∀ j, j < n + 1 → s (L.Mask j) = false)
    (hflag : s L.flag = false) (hZ : s L.Z = false)
    {N a b : ℕ} (h2N : 2 * N ≤ 2 ^ n)
    (hAcc : regValRange L.Acc s n = a) (hB : regValRange L.B s n = b)
    (hN : regValRange L.Nreg s n = N) (haN : a < N) (hbN : b < N) :
    regValRange L.Acc (denote (cuccaroModAdd L) s) n = (a + b) % N :=
  (cuccaroModAdd_spec L s hAccTop hBtop hNtop hMask0 hflag hZ h2N hAcc hB hN haN hbN).1

/-- **The carry-clean property — THE point.** Every scratch wire is restored to `false`: the flag,
the carry-out / sign wire `Acc[n]`, every `Mask` wire, and the Cuccaro ancilla `Z`. So `cuccaroModAdd`
is ancilla-restoring and reusable in place inside a multiply loop with Θ(n) qubits. -/
theorem cuccaroModAdd_clean (L : CuccaroModLayout m n) (s : State m)
    (hAccTop : s (L.Acc n) = false) (hBtop : s (L.B n) = false) (hNtop : s (L.Nreg n) = false)
    (hMask0 : ∀ j, j < n + 1 → s (L.Mask j) = false)
    (hflag : s L.flag = false) (hZ : s L.Z = false)
    {N a b : ℕ} (h2N : 2 * N ≤ 2 ^ n)
    (hAcc : regValRange L.Acc s n = a) (hB : regValRange L.B s n = b)
    (hN : regValRange L.Nreg s n = N) (haN : a < N) (hbN : b < N) :
    denote (cuccaroModAdd L) s L.flag = false
      ∧ denote (cuccaroModAdd L) s (L.Acc n) = false
      ∧ (∀ j, j < n + 1 → denote (cuccaroModAdd L) s (L.Mask j) = false)
      ∧ denote (cuccaroModAdd L) s L.Z = false := by
  obtain ⟨-, hflag9, hMask9, hZ9, hAcctop9, -, -, -, -⟩ :=
    cuccaroModAdd_spec L s hAccTop hBtop hNtop hMask0 hflag hZ h2N hAcc hB hN haN hbN
  exact ⟨hflag9, hAcctop9, hMask9, hZ9⟩

/-- **The addend operand is intact — low value AND top padding wires.** `B = b` and `Nreg = N`
survive the whole circuit (needed for the flag uncompute), and the width-`(n+1)` top padding wires
`B[n]`, `Nreg[n]` are restored to their input values. The top-wire conclusions are what let a
Stage-2b multiply-loop caller re-establish the `hBtop : B n = false` / `hNtop : Nreg n = false`
preconditions of the next iteration through the public API (F1 repair). -/
theorem cuccaroModAdd_preserves_operand (L : CuccaroModLayout m n) (s : State m)
    (hAccTop : s (L.Acc n) = false) (hBtop : s (L.B n) = false) (hNtop : s (L.Nreg n) = false)
    (hMask0 : ∀ j, j < n + 1 → s (L.Mask j) = false)
    (hflag : s L.flag = false) (hZ : s L.Z = false)
    {N a b : ℕ} (h2N : 2 * N ≤ 2 ^ n)
    (hAcc : regValRange L.Acc s n = a) (hB : regValRange L.B s n = b)
    (hN : regValRange L.Nreg s n = N) (haN : a < N) (hbN : b < N) :
    regValRange L.B (denote (cuccaroModAdd L) s) n = b
      ∧ regValRange L.Nreg (denote (cuccaroModAdd L) s) n = N
      ∧ denote (cuccaroModAdd L) s (L.B n) = s (L.B n)
      ∧ denote (cuccaroModAdd L) s (L.Nreg n) = s (L.Nreg n) := by
  obtain ⟨-, -, -, -, -, hBfin, hNfin, hBtop9, hNtop9⟩ :=
    cuccaroModAdd_spec L s hAccTop hBtop hNtop hMask0 hflag hZ h2N hAcc hB hN haN hbN
  exact ⟨hBfin, hNfin, hBtop9, hNtop9⟩

/-! ### Derived cost: `12n + 10` Toffolis -/

/-- **Derived Toffoli cost: `12n + 10`.** Five carry-out Cuccaro passes at `2(n+1)` each (three adds
+ two subtractors) plus the two mask gadgets at `n` each; the three single gates `[CX]`, `[CX, X]` are
free. So `5·2(n+1) + 2n = 12n + 10`. The leading `12n` matches the dirty `ModularAdd.modAdd`; the win
is the **qubit count** (Θ(n) reusable, vs Θ(n²) fresh per add), not the Toffoli constant. -/
theorem cuccaroModAdd_toffoli (L : CuccaroModLayout m n) :
    (circuitCost (cuccaroModAdd L)).toffoli = 12 * n + 10 := by
  rw [cuccaroModAdd]
  simp only [cost_comp_toffoli_count, cuccaroAdd_toffoli, cuccaroSub_toffoli, maskCopy_toffoli]
  have hCX : (circuitCost ([Gate.CX (L.Acc n) L.flag] : Circuit m)).toffoli = 0 := by
    simp [circuitCost, gateCost]
  have hCXX : (circuitCost ([Gate.CX (L.Acc n) L.flag, Gate.X L.flag] : Circuit m)).toffoli = 0 := by
    simp [circuitCost, gateCost]
  rw [hCX, hCXX]
  ring

/-! ### Non-vacuity witness + `#eval` / `runArr` cross-check (both branches + flag-clean)

A concrete `n = 3` layout on `Fin 18`: `Acc → {0,1,2,3}` (bit 3 = carry-out), `B → {4,5,6,7}`,
`Nreg → {8,9,10,11}` (preset `N = 3` on wires `8,9`), `Mask → {12,13,14,15}`, `flag → 16`, `Z → 17`.
`n = 3` is forced by `2N ≤ 2ⁿ`: for `N = 3` that needs `2ⁿ ≥ 6`. The strict `Array` evaluator
`runArr` (with the proven bridge `regValRangeArr_eq` back to `denote`) witnesses both branches
(`1+1 mod 3 = 2`, the `a+b<N` add-back branch; `2+2 mod 3 = 1`, the `a+b≥N` no-add-back branch) and
that the flag, the carry-out wire, and the `Mask` scratch all read clean afterward. -/

/-- A concrete `n = 3` carry-clean modular-adder layout on `Fin 18`. -/
def cuccaroModLayout3 : CuccaroModLayout 18 3 where
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

/-- Concrete input state for `n = 3, N = 3`: `Acc = a` (wires `0,1,2`), `B = b` (wires `4,5,6`),
`Nreg = 3` (wires `8,9`), all scratch / carry-out / flag / ancilla `false`. -/
def cuccaroModState3 (a0 a1 a2 b0 b1 b2 : Bool) : State 18 := fun w =>
  if w = 0 then a0 else if w = 1 then a1 else if w = 2 then a2
  else if w = 4 then b0 else if w = 5 then b1 else if w = 6 then b2
  else if w = 8 then true else if w = 9 then true
  else false

/-- Structural hypotheses of `cuccaroModAdd_correct` hold at `cuccaroModState3` (clean scratch,
`Nreg = 3`), for any data bits. -/
private theorem cuccaroModState3_pre (a0 a1 a2 b0 b1 b2 : Bool) :
    cuccaroModState3 a0 a1 a2 b0 b1 b2 (cuccaroModLayout3.Acc 3) = false
      ∧ cuccaroModState3 a0 a1 a2 b0 b1 b2 (cuccaroModLayout3.B 3) = false
      ∧ cuccaroModState3 a0 a1 a2 b0 b1 b2 (cuccaroModLayout3.Nreg 3) = false
      ∧ (∀ j, j < 3 + 1 → cuccaroModState3 a0 a1 a2 b0 b1 b2 (cuccaroModLayout3.Mask j) = false)
      ∧ cuccaroModState3 a0 a1 a2 b0 b1 b2 cuccaroModLayout3.flag = false
      ∧ cuccaroModState3 a0 a1 a2 b0 b1 b2 cuccaroModLayout3.Z = false
      ∧ regValRange cuccaroModLayout3.Nreg (cuccaroModState3 a0 a1 a2 b0 b1 b2) 3 = 3 := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, ?_⟩
  · intro j _; simp only [cuccaroModLayout3]; split_ifs <;> rfl
  · simp [regValRange, Finset.sum_range_succ, cuccaroModLayout3, cuccaroModState3]

/-- The headline is non-vacuous: `cuccaroModAdd_correct` applies to `cuccaroModLayout3` with
`a = 1, b = 1, N = 3`, giving `(1 + 1) mod 3 = 2`. -/
example : regValRange cuccaroModLayout3.Acc
    (denote (cuccaroModAdd cuccaroModLayout3) (cuccaroModState3 true false false true false false)) 3
      = (1 + 1) % 3 := by
  obtain ⟨hAccTop, hBtop, hNtop, hMask0, hflag, hZ, hN⟩ :=
    cuccaroModState3_pre true false false true false false
  have hAcc : regValRange cuccaroModLayout3.Acc
      (cuccaroModState3 true false false true false false) 3 = 1 := by
    simp [regValRange, Finset.sum_range_succ, cuccaroModLayout3, cuccaroModState3]
  have hB : regValRange cuccaroModLayout3.B
      (cuccaroModState3 true false false true false false) 3 = 1 := by
    simp [regValRange, Finset.sum_range_succ, cuccaroModLayout3, cuccaroModState3]
  have h2N : 2 * 3 ≤ 2 ^ 3 := by decide
  exact cuccaroModAdd_correct cuccaroModLayout3 _ hAccTop hBtop hNtop hMask0 hflag hZ h2N
    hAcc hB hN (by decide) (by decide)

-- `a = 1, b = 1, N = 3 ↦ (1+1) mod 3 = 2` (the `a+b<N` add-back branch). Prints `2`.
#eval regValRangeArr cuccaroModLayout3.Acc
  (runArr (cuccaroModAdd cuccaroModLayout3) (ofState (cuccaroModState3 true false false true false false))) 3
-- 2

-- `a = 2, b = 2, N = 3 ↦ (2+2) mod 3 = 1` (the `a+b≥N` no-add-back branch). Prints `1`.
#eval regValRangeArr cuccaroModLayout3.Acc
  (runArr (cuccaroModAdd cuccaroModLayout3) (ofState (cuccaroModState3 false true false false true false))) 3
-- 1

-- flag wire (16) clean afterward (both branches): prints `false`.
#eval (runArr (cuccaroModAdd cuccaroModLayout3) (ofState (cuccaroModState3 true false false true false false)))[16]!
-- false
#eval (runArr (cuccaroModAdd cuccaroModLayout3) (ofState (cuccaroModState3 false true false false true false)))[16]!
-- false

-- carry-out wire (Acc bit 3 = wire 3) clean afterward: prints `false`.
#eval (runArr (cuccaroModAdd cuccaroModLayout3) (ofState (cuccaroModState3 false true false false true false)))[3]!
-- false

-- Mask scratch (wires 12..15) all clean afterward: prints `0`.
#eval regValRangeArr cuccaroModLayout3.Mask
  (runArr (cuccaroModAdd cuccaroModLayout3) (ofState (cuccaroModState3 false true false false true false))) 4
-- 0

-- ancilla Z (17) clean afterward: prints `false`.
#eval (runArr (cuccaroModAdd cuccaroModLayout3) (ofState (cuccaroModState3 true false false true false false)))[17]!
-- false

/-- The cross-check is faithful to the real `denote`-based theorem: by `regValRangeArr_eq`, the fast
`Array` value (`2`) *is* the `regValRange (denote …)` quantity `cuccaroModAdd_correct` constrains. -/
example : regValRangeArr cuccaroModLayout3.Acc
    (runArr (cuccaroModAdd cuccaroModLayout3) (ofState (cuccaroModState3 true false false true false false))) 3
      = regValRange cuccaroModLayout3.Acc
        (denote (cuccaroModAdd cuccaroModLayout3) (cuccaroModState3 true false false true false false)) 3 :=
  regValRangeArr_eq cuccaroModLayout3.Acc (cuccaroModAdd cuccaroModLayout3)
    (cuccaroModState3 true false false true false false) 3

end Reversible
