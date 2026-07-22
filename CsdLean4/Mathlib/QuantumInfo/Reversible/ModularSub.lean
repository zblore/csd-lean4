/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularAdd
import CsdLean4.Mathlib.QuantumInfo.Reversible.Eval

/-!
# Reversible modular subtraction — the verified value primitive `(a, b) ↦ (a − b mod N, b)`  (ECDLP Phase 2, Stage S6.3e-1)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

This module **verifies the modular-subtraction VALUE primitive** `a − b mod N` over bit registers,
the one genuinely-missing field-operation primitive the elliptic-curve point formulas need (both the
`a = 0` doubling `9X⁴ − 8XY²` and the addition use field subtraction). It mirrors the verified
`ModAdd` development (`fullAdder` → `rippleCirc` → `rippleCirc_correct`) step-for-step, with a
borrow chain in place of the carry chain, and reuses the S6.3a conditional-add-back-on-a-flag
structure (`cRippleCirc` controlled on the borrow flag) for the modular fix.

```
modSub L = rippleSub L.subStep ++ cRippleCirc L.fixStep
```

* **Subtract step** `rippleSub L.subStep` (minuend register `B` holds `a`, subtrahend `Sub` holds
  `b` read-only, fresh borrow chain `Bor`): `rippleSub_correct` writes `B ← (a − b) mod 2ⁿ` and the
  borrow-out wire `Bor n` becomes the comparison flag `decide (a < b)` (`rippleSub_borrowout`),
  preserving `Sub = b`.
* **Modular fix** `cRippleCirc L.fixStep` (`Nreg` preset to `N`, same `B`, fresh carry chain `C`,
  control = the borrow flag `Bor n`, fresh ancilla `anc`): conditional add-back of `N`, gated on the
  borrow `a < b` — exactly the S6.3a controlled-add structure. The borrow flag is **already** the
  `a < b` predicate (no `X`-flip needed, unlike `modReduce` where the carry-out is `N ≤ x` and must be
  flipped).

The two branches (verified in `modSub_correct`):
* `a ≥ b` (borrow clear): subtract step value `(a − b) mod 2ⁿ = a − b`, no add-back; `a − b < N`
  since `a < N`. So `B = a − b = (a + N − b) mod N`.
* `a < b` (borrow set): subtract step value `(a − b) mod 2ⁿ = a + 2ⁿ − b` (no underflow wrap into
  range, `a − b` is computed mod `2ⁿ`); then `+ N mod 2ⁿ = (a + 2ⁿ − b + N) mod 2ⁿ`. Since
  `a − b + N < N ≤ 2ⁿ` (as `a < b ⇒ a + N − b < N`), `a + 2ⁿ − b + N = 2ⁿ + (a + N − b)` wraps to
  `a + N − b = (a + N − b) mod N`.

The headline is stated as `(a + N − b) % N` to stay in ℕ-truncated-subtraction-safe form: for
`a, b < N` this is exactly the integer `(a − b) mod N` (both branches above land on it).

## The subtractor (route (i): `fullSub` borrow chain, mirroring `fullAdder`)

`fullSub mw sw bin bout := [X mw] ++ fullAdder sw mw bin bout ++ [X mw]`: borrow-subtract is
"invert minuend, add, invert result". The full adder on `(sw, mw, bin, bout)` after flipping `mw`
computes into `mw` the bit `sw ⊕ ¬mw ⊕ bin = ¬(mw ⊕ sw ⊕ bin)` and into `bout` the carry
`majority(sw, ¬mw, bin) = majority(¬mw, sw, bin) = bout` (the borrow-out), so a final `X mw` yields
`diff = mw ⊕ sw ⊕ bin`. Verified by `decide` over all inputs (`fullSub_correct`), exactly like
`fullAdder_correct`.

## Carve line (what this is, and is NOT)

This is the **value-correct modular-subtraction atom in the fresh-ancilla model**. ℕ / `mod N` bit
arithmetic; NO field / group semantics are in play here. It is a field-operation **PRIMITIVE**: the
full SLP → circuit assembly of the EC point operation (routing all field ops — add / sub / mul /
double / const-mult — and deriving `M` as an exhibited-circuit count) is the later S6.3e stages;
`nsmul` (const-mult) / `neg` compose from `{modAdd, modDouble, modSub}`. This module does NOT claim
the point operation.

**Named residue (same fresh-ancilla model as `modAdd`):** the borrow chain `Bor`, the comparison
flag `Bor n`, and the fix-step carry chain `C` are left **dirty** after `modSub`; correctness holds
because the layout supplies fresh wires per use (`modSub_correct` requires `Bor / C / anc`
initialised `false`). In-place reuse across many subtractions needs carry/borrow-clean adders —
which `rippleCirc` / `rippleSub` / `cRippleCirc` do NOT provide. That is the genuine remaining
cleanup work, NOT built here.

## Honest cost

`modSub_toffoli` derives `10n` Toffolis from the exhibited gate list: subtract step `2n` (`rippleSub`,
two Toffolis per `fullSub` slice — the two `X mw` framing gates are free) + fix step `8n`
(`cRippleCirc_toffoli`, the controlled add-back), composed through `cost_comp_toffoli_count`. Same
`10n` as the single-step `modReduce` (S6.3a): a verified compare-and-conditional-add.
-/

namespace Reversible

variable {n : ℕ}

/-! ### The full-subtractor gadget (the verified primitive) -/

/-- The six-gate full subtractor on wires `mw sw bin bout` (with `bout` initialised `false`):
`mw ← mw ⊕ sw ⊕ bin` (difference bit, in place into the minuend wire `mw`),
`bout ← majority(¬mw, sw, bin)` (borrow-out), `sw`/`bin` unchanged.

Borrow-subtract is "invert the minuend, add, invert the result": `fullSub` flips `mw`, runs
`fullAdder sw mw bin bout` (which writes the sum `sw ⊕ ¬mw ⊕ bin` into `mw` and the carry
`majority(sw, ¬mw, bin)` into `bout`), then flips `mw` back. Correctness on the concrete layout is
`fullSub_correct`. -/
def fullSub (mw sw bin bout : Fin n) : Circuit n :=
  [Gate.X mw] ++ fullAdder sw mw bin bout ++ [Gate.X mw]

/-- **Full-subtractor correctness — genuine all-inputs coverage.** On the concrete `State 4` layout
(wires `0,1,2,3 = mw, sw, bin, bout`), with `bout` initialised `false`, the gadget computes the
difference bit on `mw` (wire `0`), the borrow-out on `bout` (wire `3`), and preserves `sw` (wire `1`)
and `bin` (wire `2`). Proved by `decide` over the finite `State 4` (16 inputs, each with
`s 3 = false`). -/
theorem fullSub_correct :
    ∀ s : State 4, s 3 = false →
      (denote (fullSub 0 1 2 3) s 0 = (s 0 ^^ s 1 ^^ s 2))
        ∧ (denote (fullSub 0 1 2 3) s 3 = majority (! s 0) (s 1) (s 2))
        ∧ (denote (fullSub 0 1 2 3) s 1 = s 1)
        ∧ (denote (fullSub 0 1 2 3) s 2 = s 2) := by
  decide

/-- **Frame lemma for the gadget.** A wire distinct from all four of `mw, sw, bin, bout` is untouched
by `fullSub` (every gate's wires lie in `{mw, sw, bin, bout}`). Lets the borrow chain lift the slice
over a register. -/
theorem fullSub_apply_of_ne {mw sw bin bout w : Fin n}
    (hmw : w ≠ mw) (hsw : w ≠ sw) (hbin : w ≠ bin) (hbout : w ≠ bout) (s : State n) :
    denote (fullSub mw sw bin bout) s w = s w := by
  apply denote_apply_of_forall_not_mem
  intro g hg
  simp only [fullSub, fullAdder, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [gateWires]

/-- **Full-subtractor correctness, general `Fin n` wires.** For pairwise-distinct wires
`mw, sw, bin, bout` with `bout` initialised `false`, the gadget writes the difference bit to `mw`,
the borrow-out to `bout`, and preserves `sw` and `bin` — over arbitrary `Fin n` (not just the concrete
`State 4` of `fullSub_correct`). This is the slice the borrow chain iterates. -/
theorem fullSub_correct_general {mw sw bin bout : Fin n}
    (hmwsw : mw ≠ sw) (hmwbin : mw ≠ bin) (hboutmw : bout ≠ mw) (hboutsw : bout ≠ sw)
    (hboutbin : bout ≠ bin) (hswbin : sw ≠ bin) {s : State n} (hb0 : s bout = false) :
    denote (fullSub mw sw bin bout) s mw = (s mw ^^ s sw ^^ s bin)
      ∧ denote (fullSub mw sw bin bout) s bout = majority (! s mw) (s sw) (s bin)
      ∧ denote (fullSub mw sw bin bout) s sw = s sw
      ∧ denote (fullSub mw sw bin bout) s bin = s bin := by
  have hswmw : sw ≠ mw := hmwsw.symm
  have hbinmw : bin ≠ mw := hmwbin.symm
  have hmwbout : mw ≠ bout := hboutmw.symm
  have hswbout : sw ≠ bout := hboutsw.symm
  have hbinbout : bin ≠ bout := hboutbin.symm
  have hbinsw : bin ≠ sw := hswbin.symm
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [fullSub, fullAdder, List.cons_append, List.nil_append, denote_cons, denote_nil] <;>
    simp_all [denoteGate, majority] <;>
    cases s mw <;> cases s sw <;> cases s bin <;> decide

/-! ### Derived cost of the gadget -/

/-- **Derived cost of the full subtractor** (from the gate list, via `circuitCost`): two Toffolis,
two CNOTs — the same as `fullAdder` (the two `X` framing gates are free). Read off
`[X, CCX, CX, CCX, CX, X]`. -/
theorem fullSub_toffoli (mw sw bin bout : Fin n) :
    (circuitCost (fullSub mw sw bin bout)).toffoli = 2 := by
  simp [circuitCost, fullSub, fullAdder, gateCost]

/-! ### The full-subtractor arithmetic identity on ℕ -/

/-- **The full-subtractor arithmetic identity on ℕ.** The minuend bit plus twice the borrow-out
equals the difference bit plus the subtrahend bit plus the borrow-in — the per-slice borrow fact the
chain accumulates (the subtraction analogue of `fulladder_nat`). -/
theorem fullsub_nat (a b c : Bool) :
    a.toNat + 2 * (majority (! a) b c).toNat = (a ^^ b ^^ c).toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

/-! ### The borrow chain (general `n`): `B ← (a − b) mod 2ⁿ`, borrow flag = `a < b`

A `SubLayout` lays out the minuend register `B` (overwritten with `(a − b) mod 2ⁿ`), the subtrahend
register `Sub` (read-only `b`), and a borrow chain `Bor` (`Bor 0` the input borrow, `Bor n` the
output borrow = the comparison flag). Pairwise disjoint, bounded-injective — exactly the
`RippleLayout` discipline. -/

/-- A borrow-chain subtractor layout on `m` wires for `n`-bit registers: minuend register `B`
(overwritten with the difference), subtrahend `Sub` (read-only), and a borrow chain `Bor`. The three
images are pairwise disjoint and each is injective on its used index range. The injectivity fields are
**bounded** (`< n` for registers, `< n + 1` for the borrow chain) — an unbounded `ℕ → Fin m`
injectivity field is uninhabitable and would make the theorem vacuous. -/
structure SubLayout (m n : ℕ) where
  /-- Minuend register (holds `a`, overwritten with `(a − b) mod 2ⁿ`). -/
  B : ℕ → Fin m
  /-- Subtrahend register (holds `b`, read-only). -/
  Sub : ℕ → Fin m
  /-- Borrow chain (`Bor i` = borrow into bit `i`; `Bor n` = the `a < b` flag). -/
  Bor : ℕ → Fin m
  hBSub : ∀ i j, B i ≠ Sub j
  hBBor : ∀ i j, B i ≠ Bor j
  hSubBor : ∀ i j, Sub i ≠ Bor j
  hBinj : ∀ i j, i < n → j < n → B i = B j → i = j
  hSubinj : ∀ i j, i < n → j < n → Sub i = Sub j → i = j
  hBorinj : ∀ i j, i < n + 1 → j < n + 1 → Bor i = Bor j → i = j

variable {m : ℕ}

/-- One borrow slice: a full subtractor on `(B i, Sub i, Bor i, Bor (i+1))`. -/
def subSlice (L : SubLayout m n) (i : ℕ) : Circuit m :=
  fullSub (L.B i) (L.Sub i) (L.Bor i) (L.Bor (i + 1))

/-- The circuit of the first `k` borrow slices (bits `0 .. k-1`). -/
def subPrefix (L : SubLayout m n) (k : ℕ) : Circuit m :=
  (List.range k).flatMap (subSlice L)

/-- The full borrow-chain subtractor: all `n` slices. -/
def rippleSub (L : SubLayout m n) : Circuit m := subPrefix L n

theorem denote_subPrefix_succ (L : SubLayout m n) (k : ℕ) (s : State m) :
    denote (subPrefix L (k + 1)) s = denote (subSlice L k) (denote (subPrefix L k) s) := by
  simp only [subPrefix, List.range_succ, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, denote_append]

/-- **The borrow-chain invariant.** After the first `k` slices: register `B`'s low `k` bits plus the
borrow into bit `k` scaled by `2^k` equal the low-`k` minuend value plus the low-`k` subtrahend value
(P1, the borrow recurrence `B + 2^k·borrow = a + Sub` over the low `k` bits); the subtrahend `Sub` is
untouched (P2); the unprocessed high bits of `B` (P4) and the unset high borrows (P5) are preserved.
By induction on `k`, lifting `fullSub_correct_general` through the frame lemma `fullSub_apply_of_ne`. -/
theorem rippleSub_invariant (L : SubLayout m n) (s : State m) (hBor0 : ∀ j, s (L.Bor j) = false) :
    ∀ k, k ≤ n →
      (regValRange L.B s k + (denote (subPrefix L k) s (L.Bor k)).toNat * 2 ^ k
        = regValRange L.B (denote (subPrefix L k) s) k + regValRange L.Sub s k)
      ∧ (∀ j, j < n → denote (subPrefix L k) s (L.Sub j) = s (L.Sub j))
      ∧ (∀ j, k ≤ j → j < n → denote (subPrefix L k) s (L.B j) = s (L.B j))
      ∧ (∀ j, k < j → j < n + 1 → denote (subPrefix L k) s (L.Bor j) = s (L.Bor j)) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [subPrefix, regValRange, hBor0]
    · intro j _; simp [subPrefix]
    · intro j _ _; simp [subPrefix]
    · intro j _ _; simp [subPrefix]
  | succ k ih =>
    intro hk
    have hkn : k ≤ n := Nat.le_of_succ_le hk
    have hkltn : k < n := hk
    obtain ⟨hP1, hP2, hP4, hP5⟩ := ih hkn
    have hmwsw : L.B k ≠ L.Sub k := L.hBSub k k
    have hmwbin : L.B k ≠ L.Bor k := L.hBBor k k
    have hboutmw : L.Bor (k + 1) ≠ L.B k := (L.hBBor k (k + 1)).symm
    have hboutsw : L.Bor (k + 1) ≠ L.Sub k := (L.hSubBor k (k + 1)).symm
    have hboutbin : L.Bor (k + 1) ≠ L.Bor k := by
      intro h; exact (Nat.succ_ne_self k) (L.hBorinj (k + 1) k (by omega) (by omega) h)
    have hswbin : L.Sub k ≠ L.Bor k := L.hSubBor k k
    have hb0' : denote (subPrefix L k) s (L.Bor (k + 1)) = false := by
      rw [hP5 (k + 1) (by omega) (by omega)]; exact hBor0 (k + 1)
    obtain ⟨hdiff, hborrow, hSubk, _hBork⟩ :=
      fullSub_correct_general hmwsw hmwbin hboutmw hboutsw hboutbin hswbin hb0'
    simp only [denote_subPrefix_succ, subSlice]
    set sk := denote (subPrefix L k) s with hskdef
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- P1: the borrow-chain arithmetic
      have hBklow : regValRange L.B (denote (fullSub (L.B k) (L.Sub k) (L.Bor k) (L.Bor (k + 1))) sk) k
          = regValRange L.B sk k := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        rw [fullSub_apply_of_ne
          (fun h => (show j ≠ k by omega) (L.hBinj j k (by omega) hkltn h))
          (L.hBSub j k) (L.hBBor j k) (L.hBBor j (k + 1)) sk]
      -- expand both sides at index k; the minuend bit at k is the original (B's low/high
      -- bits are preserved up to slice k via hP4)
      rw [regValRange_succ L.B s, regValRange_succ L.B _ (k := k), regValRange_succ L.Sub s,
          hBklow, hdiff, hborrow, hP2 k hkltn, hP4 k (Nat.le_refl k) hkltn, pow_succ]
      have hfn := fullsub_nat (s (L.B k)) (s (L.Sub k)) (sk (L.Bor k))
      cases h1 : s (L.B k) <;> cases h2 : s (L.Sub k) <;> cases h3 : sk (L.Bor k) <;>
        simp only [h1, h2, h3, majority, Bool.not_true, Bool.not_false, Bool.xor_false,
          Bool.xor_true, Bool.and_self, Bool.and_true, Bool.and_false, Bool.or_true,
          Bool.or_false, Bool.or_self, Bool.toNat_true, Bool.toNat_false, zero_mul, one_mul,
          mul_zero, add_zero, zero_add] at hP1 hfn ⊢ <;>
        omega
    · -- P2: Sub untouched
      intro j hj
      by_cases hjk : j = k
      · subst hjk; rw [hSubk]; exact hP2 j hj
      · rw [fullSub_apply_of_ne (L.hBSub k j).symm
          (fun h => hjk (L.hSubinj j k hj hkltn h)) (L.hSubBor j k) (L.hSubBor j (k + 1)) sk]
        exact hP2 j hj
    · -- P4: high bits of B preserved
      intro j hjk hjn
      rw [fullSub_apply_of_ne
        (fun h => (show j ≠ k by omega) (L.hBinj j k hjn hkltn h))
        (L.hBSub j k) (L.hBBor j k) (L.hBBor j (k + 1)) sk]
      exact hP4 j (by omega) hjn
    · -- P5: high borrows preserved
      intro j hjk hjn
      rw [fullSub_apply_of_ne ((L.hBBor k j).symm) ((L.hSubBor k j).symm)
        (fun h => (show j ≠ k by omega) (L.hBorinj j k hjn (by omega) h))
        (fun h => (show j ≠ k + 1 by omega) (L.hBorinj j (k + 1) hjn (by omega) h)) sk]
      exact hP5 j (by omega) hjn

/-- **Borrow-chain subtractor correctness.** For a disjoint-wire layout with all borrows initialised
`false`, the ripple subtractor leaves the minuend register `B` holding `(a − b) mod 2ⁿ`, where
`a = B`, `b = Sub`. The borrow recurrence, derived from the exhibited circuit `rippleSub`. -/
theorem rippleSub_correct (L : SubLayout m n) (s : State m) (hBor0 : ∀ j, s (L.Bor j) = false) :
    regValRange L.B (denote (rippleSub L) s) n
      = (regValRange L.B s n + 2 ^ n - regValRange L.Sub s n) % 2 ^ n := by
  obtain ⟨hP1, -, -, -⟩ := rippleSub_invariant L s hBor0 n (Nat.le_refl n)
  rw [rippleSub]
  set a := regValRange L.B s n with ha
  set bsub := regValRange L.Sub s n with hbsub
  have hblt : regValRange L.B (denote (subPrefix L n) s) n < 2 ^ n := regValRange_lt _ _ _
  have hsublt : bsub < 2 ^ n := regValRange_lt _ _ _
  set B' := regValRange L.B (denote (subPrefix L n) s) n with hB'
  -- invariant at n: a + borrow_n·2ⁿ = B' + bsub
  cases h : denote (subPrefix L n) s (L.Bor n)
  · -- borrow clear: a = B' + bsub, so a ≥ bsub and B' = a − bsub
    simp only [h, Bool.toNat_false, zero_mul, add_zero] at hP1
    have hsum : a + 2 ^ n - bsub = 2 ^ n + B' := by omega
    rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt hblt]
  · -- borrow set: a + 2ⁿ = B' + bsub, so a < bsub and B' = a + 2ⁿ − bsub < 2ⁿ
    simp only [h, Bool.toNat_true, one_mul] at hP1
    have hsum : a + 2 ^ n - bsub = B' := by omega
    rw [hsum, Nat.mod_eq_of_lt hblt]

/-- **The borrow-out is the comparison flag.** For a disjoint-wire layout with all borrows
initialised `false`, the ripple subtractor's output borrow wire `Bor n` holds `decide (a < b)` — it
is set exactly when the subtraction underflows, i.e. when the minuend `a` is below the subtrahend
`b`. Read off `rippleSub_invariant` (clause P1) together with `regValRange_lt`. This is the
comparison primitive for the modular fix: add `N` back iff the borrow is set. -/
theorem rippleSub_borrowout (L : SubLayout m n) (s : State m) (hBor0 : ∀ j, s (L.Bor j) = false) :
    denote (rippleSub L) s (L.Bor n)
      = decide (regValRange L.B s n < regValRange L.Sub s n) := by
  obtain ⟨hP1, -, -, -⟩ := rippleSub_invariant L s hBor0 n (Nat.le_refl n)
  rw [rippleSub]
  have hblt : regValRange L.B (denote (subPrefix L n) s) n < 2 ^ n := regValRange_lt _ _ _
  cases h : denote (subPrefix L n) s (L.Bor n)
  · simp only [h, Bool.toNat_false, zero_mul, add_zero] at hP1
    rw [eq_comm, decide_eq_false_iff_not]
    omega
  · simp only [h, Bool.toNat_true, one_mul] at hP1
    rw [eq_comm, decide_eq_true_eq]
    omega

/-! ### Modular subtraction: the borrow chain + conditional add-back of `N`

A `ModSubLayout` bundles the subtract step's `SubLayout` (minuend `B`, subtrahend `Sub`, borrow chain
`Bor`) and the fix step's controlled-add sub-data (constant register `Nreg` preset to `N`, fix carry
chain `C`, shared ancilla `anc`), with the control being the borrow flag `Bor n` (= `a < b`). The fix
step is the S6.3a conditional-add-back structure (`cRippleCirc`), gated directly on the borrow (no
`X`-flip, since the borrow is already the `a < b` predicate that triggers the add-back). -/

/-- A single-step modular-subtraction layout on `Fin m` for `n`-bit registers. Bundles:
* `B` — the minuend (holds `a`, overwritten with `a − b mod N`);
* `Sub` — the subtrahend (holds `b`, read-only, preserved);
* `Bor` — the borrow chain; `Bor n` is the comparison flag (= `a < b`), the control of the fix;
* `Nreg` — the fix constant register (preset to `N`), with a fresh carry chain `C`;
* `anc` — the shared clean ancilla for the controlled add-back.

The fields are pure wire geometry (pairwise disjointness + per-range bounded injectivity), mirroring
the `SubLayout` / `ModReduceLayout` discipline. The injectivity fields are **bounded** (`< n` for
registers, `< n + 1` for chains) — an unbounded `ℕ → Fin m` injectivity field is uninhabitable and
would make the theorem vacuous. -/
structure ModSubLayout (m n : ℕ) where
  /-- Minuend register: holds `a`, overwritten with `a − b mod N`. -/
  B : ℕ → Fin m
  /-- Subtrahend register: holds `b`, read-only (preserved). -/
  Sub : ℕ → Fin m
  /-- Borrow chain; `Bor n` is the comparison flag (= `a < b`). -/
  Bor : ℕ → Fin m
  /-- Fix-step constant register (preset to `N`). -/
  Nreg : ℕ → Fin m
  /-- Fix-step carry chain (distinct from the borrow chain). -/
  C : ℕ → Fin m
  /-- Shared clean ancilla for the controlled add-back. -/
  anc : Fin m
  -- subtract-step register geometry (B, Sub, Bor pairwise disjoint + bounded injective)
  hBSub : ∀ i j, B i ≠ Sub j
  hBBor : ∀ i j, B i ≠ Bor j
  hSubBor : ∀ i j, Sub i ≠ Bor j
  hBinj : ∀ i j, i < n → j < n → B i = B j → i = j
  hSubinj : ∀ i j, i < n → j < n → Sub i = Sub j → i = j
  hBorinj : ∀ i j, i < n + 1 → j < n + 1 → Bor i = Bor j → i = j
  -- fix-step register geometry (Nreg, B, C pairwise disjoint + injective)
  hBNreg : ∀ i j, B i ≠ Nreg j
  hBC : ∀ i j, B i ≠ C j
  hNregC : ∀ i j, Nreg i ≠ C j
  hNreginj : ∀ i j, i < n → j < n → Nreg i = Nreg j → i = j
  hCinj : ∀ i j, i < n + 1 → j < n + 1 → C i = C j → i = j
  -- the flag (= Bor n) controls the fix step; disjoint from fix-step registers
  hflagNreg : ∀ j, Bor n ≠ Nreg j
  hflagB : ∀ j, Bor n ≠ B j
  hflagC : ∀ j, Bor n ≠ C j
  hflaganc : Bor n ≠ anc
  -- the ancilla is disjoint from fix-step registers
  hancNreg : ∀ j, anc ≠ Nreg j
  hancB : ∀ j, anc ≠ B j
  hancC : ∀ j, anc ≠ C j
  -- cross-step disjointness: fix-step wires (Nreg, C, anc) are untouched by the subtract step
  -- (B is shared between the steps by design; Bor n is the control).
  hNregSub : ∀ i j, Nreg i ≠ Sub j
  hNregBor : ∀ i j, Nreg i ≠ Bor j
  hCSub : ∀ i j, C i ≠ Sub j
  hCBor : ∀ i j, C i ≠ Bor j
  hancSub : ∀ j, anc ≠ Sub j
  hancBor : ∀ j, anc ≠ Bor j
  -- the subtrahend `Sub` is disjoint from every fix-step wire (so it survives the fix step)
  hSubNreg : ∀ i j, Sub i ≠ Nreg j
  hSubC : ∀ i j, Sub i ≠ C j
  hSubanc : ∀ j, Sub j ≠ anc

variable {L : ModSubLayout m n}

/-- The subtract step as a `SubLayout`: minuend `B` + subtrahend `Sub` + borrow chain `Bor`. -/
def ModSubLayout.subStep (L : ModSubLayout m n) : SubLayout m n where
  B := L.B
  Sub := L.Sub
  Bor := L.Bor
  hBSub := L.hBSub
  hBBor := L.hBBor
  hSubBor := L.hSubBor
  hBinj := L.hBinj
  hSubinj := L.hSubinj
  hBorinj := L.hBorinj

/-- The fix step as a `CRippleLayout`: constant `Nreg` + data `B` + carry chain `C`, controlled on
the borrow flag `Bor n`, with the shared ancilla. -/
def ModSubLayout.fixStep (L : ModSubLayout m n) : CRippleLayout m n where
  A := L.Nreg
  B := L.B
  C := L.C
  ctrl := L.Bor n
  anc := L.anc
  hAB i j := (L.hBNreg j i).symm
  hAC := L.hNregC
  hBC := L.hBC
  hAinj := L.hNreginj
  hBinj := L.hBinj
  hCinj := L.hCinj
  hctrlA := L.hflagNreg
  hctrlB := L.hflagB
  hctrlC := L.hflagC
  hctrlanc := L.hflaganc
  hancA := L.hancNreg
  hancB := L.hancB
  hancC := L.hancC

/-- **The modular-subtraction circuit.** Borrow-chain subtractor (`rippleSub`, producing the `a < b`
borrow flag) followed by the S6.3a controlled add-back of `N` gated on the flag (`cRippleCirc`). -/
def modSub (L : ModSubLayout m n) : Circuit m :=
  rippleSub L.subStep ++ cRippleCirc L.fixStep

/-! ### Frame: fix-step inputs survive the subtract step

`rippleSub L.subStep` touches only the wires `{B k, Sub k, Bor k}` (the slices are
`fullSub (B k) (Sub k) (Bor k) (Bor (k+1))`). The fix step's `Nreg`, `C`, and `anc` are disjoint from
those, so their values pass through the subtract step unchanged. -/

/-- **Generic subtract-step frame.** A wire `w` with `w ≠ B k`, `w ≠ Sub k`, `w ≠ Bor k` for all `k`
is left unchanged by `rippleSub L.subStep`. -/
theorem rippleSub_subStep_preserves (s : State m) (w : Fin m)
    (hB : ∀ k, w ≠ L.B k) (hS : ∀ k, w ≠ L.Sub k) (hBor : ∀ k, w ≠ L.Bor k) :
    denote (rippleSub L.subStep) s w = s w := by
  apply denote_apply_of_forall_not_mem
  intro g hg
  rw [rippleSub, subPrefix, List.mem_flatMap] at hg
  obtain ⟨k, _hk, hgk⟩ := hg
  simp only [subSlice, fullSub, fullAdder, ModSubLayout.subStep, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hgk
  rcases hgk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [gateWires, hB k, hS k, hBor k, hBor (k + 1)]

/-- After the subtract step, `Nreg` is unchanged on every wire. -/
theorem modSub_subStep_preserves_Nreg (s : State m) (j : ℕ) :
    denote (rippleSub L.subStep) s (L.Nreg j) = s (L.Nreg j) :=
  rippleSub_subStep_preserves s (L.Nreg j)
    (fun k => (L.hBNreg k j).symm) (fun k => L.hNregSub j k) (fun k => L.hNregBor j k)

/-- After the subtract step, the fix carry chain `C` is unchanged on every wire. -/
theorem modSub_subStep_preserves_C (s : State m) (j : ℕ) :
    denote (rippleSub L.subStep) s (L.C j) = s (L.C j) :=
  rippleSub_subStep_preserves s (L.C j)
    (fun k => (L.hBC k j).symm) (fun k => L.hCSub j k) (fun k => L.hCBor j k)

/-- After the subtract step, the shared ancilla `anc` is unchanged. -/
theorem modSub_subStep_preserves_anc (s : State m) :
    denote (rippleSub L.subStep) s L.anc = s L.anc :=
  rippleSub_subStep_preserves s L.anc
    (fun k => L.hancB k) (fun k => L.hancSub k) (fun k => L.hancBor k)

/-! ### Frame: the subtrahend `Sub` survives the fix step

`cRippleCirc L.fixStep` touches only `{Nreg, B, C, anc, Bor n}`. Since `Sub` is disjoint from all of
these, the subtrahend passes through the fix step unchanged. -/

/-- **Subtrahend frame through the fix step.** `Sub j` is untouched by `cRippleCirc L.fixStep`. -/
theorem cRippleCirc_fixStep_preserves_Sub (s : State m) (j : ℕ) :
    denote (cRippleCirc L.fixStep) s (L.Sub j) = s (L.Sub j) := by
  apply cRippleCirc_preserves_external
  · exact fun h => L.hSubBor j n h
  · exact L.hSubanc j
  · exact fun k _ => L.hSubNreg j k
  · exact fun k _ => (L.hBSub k j).symm
  · exact fun k _ => L.hSubC j k

/-! ### Value correctness, both branches -/

/-- **The complete single-step modular subtraction — both branches, verified from the exhibited
circuit.** For a disjoint-wire `ModSubLayout` with the borrow chain `Bor`, the fix carry chain `C`,
and the ancilla `anc` all initialised `false`, the constant register `Nreg` preset to `N`, minuend
`B` holding `a`, subtrahend `Sub` holding `b`, with `a < N`, `b < N`, `N ≤ 2ⁿ`: the circuit
`modSub L` leaves `B` holding `(a + N − b) mod N` (= `a − b mod N`).

Proof. The subtract step (`rippleSub_correct`) writes `(a + 2ⁿ − b) mod 2ⁿ` to `B` and sets the
borrow flag `Bor n = decide (a < b)` (`rippleSub_borrowout`), preserving `Sub = b` and — via the
frame lemmas — `Nreg = N`, `C = false`, `anc = false`. The fix step (`cRippleCirc_correct`) adds `N`
back iff the flag is set. The two branches:
* `a ≥ b` (flag clear): subtract value `(a + 2ⁿ − b) mod 2ⁿ = a − b` (`b ≤ a < 2ⁿ`); no add-back, and
  `a − b < N` (`a < N`), so `B = a − b = (a + N − b) mod N`.
* `a < b` (flag set): subtract value `(a + 2ⁿ − b) mod 2ⁿ = a + 2ⁿ − b` (no wrap, `a + 2ⁿ − b < 2ⁿ`),
  then `+ N mod 2ⁿ = (a + 2ⁿ + N − b) mod 2ⁿ = a + N − b` (`a + N − b < N ≤ 2ⁿ`), which is
  `(a + N − b) mod N`. -/
theorem modSub_correct (L : ModSubLayout m n) (s : State m)
    (hBor : ∀ j, s (L.Bor j) = false) (hC : ∀ j, s (L.C j) = false) (hanc : s L.anc = false)
    {N a b : ℕ} (hN : N ≤ 2 ^ n) (hNreg : regValRange L.Nreg s n = N)
    (hB : regValRange L.B s n = a) (hSub : regValRange L.Sub s n = b)
    (haN : a < N) (hbN : b < N) :
    regValRange L.B (denote (modSub L) s) n = (a + N - b) % N := by
  have hNpos : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le a) haN
  have halt : a < 2 ^ n := by omega
  have hblt : b < 2 ^ n := by omega
  -- decompose the circuit at the subtract step
  set ssub := denote (rippleSub L.subStep) s with hssubdef
  have hdenote : denote (modSub L) s = denote (cRippleCirc L.fixStep) ssub := by
    rw [modSub, denote_append, ← hssubdef]
  rw [hdenote]
  -- SUBTRACT STEP value of B: (a + 2ⁿ − b) mod 2ⁿ
  have hBsub : regValRange L.B ssub n = (a + 2 ^ n - b) % 2 ^ n := by
    have := rippleSub_correct L.subStep s (by intro j; exact hBor j)
    simp only [ModSubLayout.subStep, hB, hSub, hssubdef] at this ⊢
    rw [this]
  -- SUBTRACT STEP flag: Bor n = decide (a < b)
  have hflag : ssub (L.Bor n) = decide (a < b) := by
    have hbo := rippleSub_borrowout L.subStep s (by intro j; exact hBor j)
    simp only [ModSubLayout.subStep, hB, hSub, hssubdef] at hbo ⊢
    rw [hbo]
  -- SUBTRACT STEP frame: fix-step presets / clean carries survive
  have hNregsub : regValRange L.fixStep.A ssub n = N := by
    rw [← hNreg]
    apply Finset.sum_congr rfl
    intro j _
    show (ssub (L.Nreg j)).toNat * 2 ^ j = (s (L.Nreg j)).toNat * 2 ^ j
    rw [hssubdef, modSub_subStep_preserves_Nreg]
  have hCsub : ∀ j, ssub (L.fixStep.C j) = false := by
    intro j; show ssub (L.C j) = false
    rw [hssubdef, modSub_subStep_preserves_C]; exact hC j
  have hancsub : ssub L.fixStep.anc = false := by
    show ssub L.anc = false
    rw [hssubdef, modSub_subStep_preserves_anc]; exact hanc
  -- FIX STEP: controlled add-back of N, conditional on the flag
  have hfix := cRippleCirc_correct L.fixStep ssub hCsub hancsub
  show regValRange L.fixStep.B (denote (cRippleCirc L.fixStep) ssub) n = (a + N - b) % N
  rw [hfix]
  show (if ssub (L.fixStep.ctrl) then (regValRange L.fixStep.A ssub n + regValRange L.fixStep.B ssub n) % 2 ^ n
      else regValRange L.fixStep.B ssub n) = (a + N - b) % N
  show (if ssub (L.Bor n) then (regValRange L.fixStep.A ssub n + regValRange L.B ssub n) % 2 ^ n
      else regValRange L.B ssub n) = (a + N - b) % N
  rw [hflag, hNregsub, hBsub]
  by_cases hlt : a < b
  · -- a < b: flag set, add N back; subtract value is a + 2ⁿ − b (no wrap)
    simp only [hlt, decide_true, if_true]
    have hnowrap : (a + 2 ^ n - b) % 2 ^ n = a + 2 ^ n - b := Nat.mod_eq_of_lt (by omega)
    rw [hnowrap]
    -- N + (a + 2ⁿ − b) = 2ⁿ + (a + N − b), and a + N − b < N ≤ 2ⁿ
    have hsum : N + (a + 2 ^ n - b) = 2 ^ n + (a + N - b) := by omega
    rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · -- a ≥ b: flag clear, no add-back; subtract value is a − b
    have hge : b ≤ a := by omega
    simp only [hlt, decide_false, Bool.false_eq_true, if_false]
    have hsubval : (a + 2 ^ n - b) % 2 ^ n = a - b := by
      have hsum : a + 2 ^ n - b = 2 ^ n + (a - b) := by omega
      rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hsubval]
    -- a − b = (a + N − b) mod N, since a − b < N
    have heq : a + N - b = (a - b) + N := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- **The subtrahend register is intact.** `modSub L` leaves `Sub` holding `b` (read-only). The
subtract step preserves `Sub` (P2 of the borrow invariant) and the fix step is disjoint from `Sub`. -/
theorem modSub_preserves_subtrahend (L : ModSubLayout m n) (s : State m)
    (hBor : ∀ j, s (L.Bor j) = false) {b : ℕ} (hSub : regValRange L.Sub s n = b) :
    regValRange L.Sub (denote (modSub L) s) n = b := by
  rw [← hSub]
  set ssub := denote (rippleSub L.subStep) s with hssubdef
  have hdenote : denote (modSub L) s = denote (cRippleCirc L.fixStep) ssub := by
    rw [modSub, denote_append, ← hssubdef]
  rw [hdenote]
  -- subtract step preserves Sub (borrow invariant P2)
  obtain ⟨-, hP2, -, -⟩ := rippleSub_invariant L.subStep s (by intro j; exact hBor j) n (le_refl n)
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  show (denote (cRippleCirc L.fixStep) ssub (L.Sub j)).toNat * 2 ^ j = (s (L.Sub j)).toNat * 2 ^ j
  rw [cRippleCirc_fixStep_preserves_Sub]
  have hSubk : ssub (L.Sub j) = s (L.Sub j) := by
    rw [hssubdef, rippleSub]
    exact hP2 j hj
  rw [hSubk]

/-- **The modular-subtraction output is a genuine residue in `[0, N)`.** Corollary of
`modSub_correct` and `Nat.mod_lt`. -/
theorem modSub_in_range (L : ModSubLayout m n) (s : State m)
    (hBor : ∀ j, s (L.Bor j) = false) (hC : ∀ j, s (L.C j) = false) (hanc : s L.anc = false)
    {N a b : ℕ} (hN : N ≤ 2 ^ n) (hNreg : regValRange L.Nreg s n = N)
    (hB : regValRange L.B s n = a) (hSub : regValRange L.Sub s n = b)
    (haN : a < N) (hbN : b < N) :
    regValRange L.B (denote (modSub L) s) n < N := by
  rw [modSub_correct L s hBor hC hanc hN hNreg hB hSub haN hbN]
  exact Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le a) haN)

/-! ### Derived cost -/

/-- **Derived Toffoli cost of the modular subtractor**: `10n` Toffolis, from the exhibited gate list.
Subtract step `2n` (`rippleSub`, two Toffolis per `fullSub` slice — the framing `X`s are free) + fix
step `8n` (`cRippleCirc_toffoli`, the controlled add-back), composed through `cost_comp_toffoli_count`.
Same `10n` as the single-step `modReduce` (S6.3a): a verified compare-and-conditional-add. -/
theorem modSub_toffoli (L : ModSubLayout m n) :
    (circuitCost (modSub L)).toffoli = 10 * n := by
  rw [modSub, cost_comp_toffoli_count, cRippleCirc_toffoli]
  -- subtract step ripple: 2n (two Toffolis per fullSub slice)
  have hsub : (circuitCost (rippleSub L.subStep)).toffoli = 2 * n := by
    rw [rippleSub, subPrefix]
    suffices h : ∀ k, (circuitCost ((List.range k).flatMap (subSlice L.subStep))).toffoli = 2 * k
      from h n
    intro k
    induction k with
    | zero => simp [circuitCost]
    | succ k ih =>
      have hsplit : (List.range (k + 1)).flatMap (subSlice L.subStep)
          = (List.range k).flatMap (subSlice L.subStep) ++ subSlice L.subStep k := by
        rw [List.range_succ, List.flatMap_append]; simp
      rw [hsplit, cost_comp_toffoli_count, ih, subSlice, fullSub_toffoli]
      omega
  rw [hsub]
  omega

/-! ### Non-vacuity witness

A concrete 3-bit modular-subtraction layout on `Fin 25`:
* minuend `B → {0,1,2}`, subtrahend `Sub → {3,4,5}`, borrow chain `Bor → {6,7,8,9}`,
* fix constant `Nreg → {10,11,12}`, fix carry chain `C → {13,14,15,16}`, ancilla `17`.

(`n = 3` is taken to share the `modAdd` witness scale; `N = 5` needs `N ≤ 2³ = 8`.) This exhibits
that `ModSubLayout` is inhabited (the bounded-injectivity bundle is satisfiable), so the headlines
are not vacuously quantified. The concrete runs below subtract modulo `N = 5` at fully-specified
input states, covering **both branches**: `a = 3, b = 1 ↦ (3 − 1) mod 5 = 2` (the `a ≥ b`
no-wrap branch), `a = 1, b = 3 ↦ (1 − 3) mod 5 = 3` (the `a < b` WRAP branch, the load-bearing
case), and `a = b = 2 ↦ 0`. -/

/-- A concrete 3-bit modular-subtraction layout on `Fin 25`. -/
def modSubLayout2 : ModSubLayout 25 3 where
  B i := if i = 0 then 0 else if i = 1 then 1 else 2
  Sub i := if i = 0 then 3 else if i = 1 then 4 else 5
  Bor i := if i = 0 then 6 else if i = 1 then 7 else if i = 2 then 8 else 9
  Nreg i := if i = 0 then 10 else if i = 1 then 11 else 12
  C i := if i = 0 then 13 else if i = 1 then 14 else if i = 2 then 15 else 16
  anc := 17
  hBSub i j := by split_ifs <;> decide
  hBBor i j := by split_ifs <;> decide
  hSubBor i j := by split_ifs <;> decide
  hBinj i j hi hj h := by split_ifs at h <;> omega
  hSubinj i j hi hj h := by split_ifs at h <;> omega
  hBorinj i j hi hj h := by split_ifs at h <;> omega
  hBNreg i j := by split_ifs <;> decide
  hBC i j := by split_ifs <;> decide
  hNregC i j := by split_ifs <;> decide
  hNreginj i j hi hj h := by split_ifs at h <;> omega
  hCinj i j hi hj h := by split_ifs at h <;> omega
  hflagNreg j := by split_ifs <;> decide
  hflagB j := by split_ifs <;> decide
  hflagC j := by split_ifs <;> decide
  hflaganc := by decide
  hancNreg j := by split_ifs <;> decide
  hancB j := by split_ifs <;> decide
  hancC j := by split_ifs <;> decide
  hNregSub i j := by split_ifs <;> decide
  hNregBor i j := by split_ifs <;> decide
  hCSub i j := by split_ifs <;> decide
  hCBor i j := by split_ifs <;> decide
  hancSub j := by split_ifs <;> decide
  hancBor j := by split_ifs <;> decide
  hSubNreg i j := by split_ifs <;> decide
  hSubC i j := by split_ifs <;> decide
  hSubanc j := by split_ifs <;> decide

/-- The headline is non-vacuous: it applies to the concrete `modSubLayout2`. -/
example (s : State 25)
    (hBor : ∀ j, s (modSubLayout2.Bor j) = false) (hC : ∀ j, s (modSubLayout2.C j) = false)
    (hanc : s modSubLayout2.anc = false) (hNreg : regValRange modSubLayout2.Nreg s 3 = 5)
    (hB : regValRange modSubLayout2.B s 3 = 3) (hSub : regValRange modSubLayout2.Sub s 3 = 1) :
    regValRange modSubLayout2.B (denote (modSub modSubLayout2) s) 3 = (3 + 5 - 1) % 5 := by
  have hN : (5 : ℕ) ≤ 2 ^ 3 := by decide
  exact modSub_correct modSubLayout2 s hBor hC hanc hN hNreg hB hSub (by decide) (by decide)

/-- Concrete input state for `n = 3, N = 5`: minuend `B = a` (wires `0,1,2`), subtrahend `Sub = b`
(wires `3,4,5`), `Nreg = 5` (wires `10,12`, bits `0` and `2`), all borrows / fix carries / ancilla
`false`. Parameterised by the data bits of `a` and `b`. -/
def modSubState2 (a0 a1 a2 b0 b1 b2 : Bool) : State 25 := fun w =>
  if w = 0 then a0 else if w = 1 then a1 else if w = 2 then a2
  else if w = 3 then b0 else if w = 4 then b1 else if w = 5 then b2
  else if w = 10 then true else if w = 12 then true   -- Nreg = 5 (bits 0, 2)
  else false

/-- The hypotheses of `modSub_correct` hold at `modSubState2` (borrows / carries / ancilla clear,
`Nreg = 5`), for any data bits. The `regValRange` register-value preconditions are concrete sums,
discharged by `decide`. -/
private theorem modSubState2_pre (a0 a1 a2 b0 b1 b2 : Bool) :
    (∀ j, modSubState2 a0 a1 a2 b0 b1 b2 (modSubLayout2.Bor j) = false)
      ∧ (∀ j, modSubState2 a0 a1 a2 b0 b1 b2 (modSubLayout2.C j) = false)
      ∧ modSubState2 a0 a1 a2 b0 b1 b2 modSubLayout2.anc = false
      ∧ regValRange modSubLayout2.Nreg (modSubState2 a0 a1 a2 b0 b1 b2) 3 = 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j; show modSubState2 a0 a1 a2 b0 b1 b2 (modSubLayout2.Bor j) = false
    simp only [modSubLayout2]; split_ifs <;> rfl
  · intro j; show modSubState2 a0 a1 a2 b0 b1 b2 (modSubLayout2.C j) = false
    simp only [modSubLayout2]; split_ifs <;> rfl
  · rfl
  · simp [regValRange, Finset.sum_range_succ, modSubLayout2, modSubState2]

/-- **Concrete run, the `a ≥ b` no-wrap branch:** `a = 3, b = 1, N = 5 ↦ (3 − 1) mod 5 = 2`. -/
example : regValRange modSubLayout2.B
    (denote (modSub modSubLayout2) (modSubState2 true true false true false false)) 3 = 2 := by
  obtain ⟨hBor, hC, hanc, hNreg⟩ := modSubState2_pre true true false true false false
  have hB : regValRange modSubLayout2.B
      (modSubState2 true true false true false false) 3 = 3 := by
    simp [regValRange, Finset.sum_range_succ, modSubLayout2, modSubState2]
  have hSub : regValRange modSubLayout2.Sub
      (modSubState2 true true false true false false) 3 = 1 := by
    simp [regValRange, Finset.sum_range_succ, modSubLayout2, modSubState2]
  have hN : (5 : ℕ) ≤ 2 ^ 3 := by decide
  rw [modSub_correct modSubLayout2 (modSubState2 true true false true false false) hBor hC hanc
    hN hNreg hB hSub (by decide) (by decide)]

/-- **Concrete run, the `a < b` WRAP branch (the load-bearing case):** `a = 1, b = 3, N = 5 ↦
(1 − 3) mod 5 = 3`. The borrow flag triggers the add-back of `N`, giving `1 − 3 + 5 = 3`, not a
truncated `0`. -/
example : regValRange modSubLayout2.B
    (denote (modSub modSubLayout2) (modSubState2 true false false true true false)) 3 = 3 := by
  obtain ⟨hBor, hC, hanc, hNreg⟩ := modSubState2_pre true false false true true false
  have hB : regValRange modSubLayout2.B
      (modSubState2 true false false true true false) 3 = 1 := by
    simp [regValRange, Finset.sum_range_succ, modSubLayout2, modSubState2]
  have hSub : regValRange modSubLayout2.Sub
      (modSubState2 true false false true true false) 3 = 3 := by
    simp [regValRange, Finset.sum_range_succ, modSubLayout2, modSubState2]
  have hN : (5 : ℕ) ≤ 2 ^ 3 := by decide
  rw [modSub_correct modSubLayout2 (modSubState2 true false false true true false) hBor hC hanc
    hN hNreg hB hSub (by decide) (by decide)]

/-- **Concrete run, the `a = b` zero branch:** `a = 2, b = 2, N = 5 ↦ 0`. -/
example : regValRange modSubLayout2.B
    (denote (modSub modSubLayout2) (modSubState2 false true false false true false)) 3 = 0 := by
  obtain ⟨hBor, hC, hanc, hNreg⟩ := modSubState2_pre false true false false true false
  have hB : regValRange modSubLayout2.B
      (modSubState2 false true false false true false) 3 = 2 := by
    simp [regValRange, Finset.sum_range_succ, modSubLayout2, modSubState2]
  have hSub : regValRange modSubLayout2.Sub
      (modSubState2 false true false false true false) 3 = 2 := by
    simp [regValRange, Finset.sum_range_succ, modSubLayout2, modSubState2]
  have hN : (5 : ℕ) ≤ 2 ^ 3 := by decide
  rw [modSub_correct modSubLayout2 (modSubState2 false true false false true false) hBor hC hanc
    hN hNreg hB hSub (by decide) (by decide)]

/-! ### Harness cross-check (`runArr` / `regValRangeArr`, audited SOUND)

Fast `Array Bool`-backed runs of the full `modSub` circuit (the `Fin 25` `denote` blows up under
`#eval` via lazy `Function.update` re-reads; `runArr` is O(gates)). Each printed number is certified
equal to the `regValRange (denote …)` of `modSub_correct` by `regValRangeArr_eq`. Both branches are
covered: `a ≥ b` (no wrap) and `a < b` (the load-bearing WRAP, where the borrow flag must fire the
add-back). -/

-- `a = 3, b = 1, N = 5 ↦ (3 − 1) mod 5 = 2` (the `a ≥ b` no-wrap branch). Prints `2`.
#eval regValRangeArr modSubLayout2.B
  (runArr (modSub modSubLayout2) (ofState (modSubState2 true true false true false false))) 3
-- 2

-- `a = 1, b = 3, N = 5 ↦ (1 − 3) mod 5 = 3` (the `a < b` WRAP branch). Prints `3`, NOT a truncated 0.
#eval regValRangeArr modSubLayout2.B
  (runArr (modSub modSubLayout2) (ofState (modSubState2 true false false true true false))) 3
-- 3

-- `a = 2, b = 2, N = 5 ↦ 0` (the `a = b` zero branch). Prints `0`.
#eval regValRangeArr modSubLayout2.B
  (runArr (modSub modSubLayout2) (ofState (modSubState2 false true false false true false))) 3
-- 0

-- The subtrahend is preserved across the whole circuit: `Sub` stays `1`, `3`, `2` respectively.
#eval regValRangeArr modSubLayout2.Sub
  (runArr (modSub modSubLayout2) (ofState (modSubState2 true false false true true false))) 3
-- 3

/-- The cross-check is faithful to the real `denote`-based theorem: by `regValRangeArr_eq`, the fast
`Array` value (`3`, the wrap branch above) *is* the `regValRange (denote …)` quantity that
`modSub_correct` constrains. -/
example : regValRangeArr modSubLayout2.B
    (runArr (modSub modSubLayout2) (ofState (modSubState2 true false false true true false))) 3
      = regValRange modSubLayout2.B (denote (modSub modSubLayout2)
        (modSubState2 true false false true true false)) 3 :=
  regValRangeArr_eq modSubLayout2.B (modSub modSubLayout2)
    (modSubState2 true false false true true false) 3

end Reversible
