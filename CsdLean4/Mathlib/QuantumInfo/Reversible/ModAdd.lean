/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Reversible.Circuit
public import CsdLean4.Mathlib.QuantumInfo.Reversible.Cost
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi

/-!
# Reversible modular addition — register encoding, verified full adder, ripple cost  (ECDLP Tranche 2, Pass 1)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The addition layer of the reversible-circuit substrate
(`Circuit.lean` / `Cost.lean`, `specs/ecdlp-resource-plan.md`). Pass 1 delivers a **sorry-free
semantic + derived-cost scaffold**: the register readout `regVal`, the **fully verified** four-gate
full-adder gadget, its derived cost, and the **linear** Toffoli / CNOT count of an `k`-slice ripple
adder (composed through the Tranche-1 `cost_comp_*` lemmas, not re-derived).

The locked design decision is respected throughout: every cost claim is about an *exhibited*
`Circuit` and is discharged through `circuitCost`. The full-adder correctness is genuine
all-inputs coverage (`decide` over `Fintype (Fin 4 → Bool)`), not a single example.

## What is proved here

**Pass 1 (cost + gadget):**
* `regVal` little-endian readout, `regVal_lt_two_pow`, and an `X`-flip round-trip lemma.
* `fullAdder` (four gates) with **full all-inputs correctness** on the concrete `State 4` layout:
  sum bit `b ← a ⊕ b ⊕ cin`, carry-out `cout ← majority(a, b, cin)` (with `cout` init `false`),
  `a` and `cin` preserved.
* `fullAdder_cost`: derived `toffoli = 2`, `cnot = 2` (and the full `Cost` record).
* `rippleAdder` (an `k`-slice concatenation of `fullAdder` gadgets) with **linear cost**:
  `(circuitCost (rippleAdder ...)).toffoli = 2 * k` and `.cnot = 2 * k`, composed through the
  Tranche-1 composition lemmas.

**Pass 2 Stage A (general gadget):** `fullAdder_correct_general` lifts the full-adder correctness
off the concrete `State 4` to arbitrary distinct `Fin n` wires, via the Circuit-level frame lemma
`denote_apply_of_forall_not_mem` / `fullAdder_apply_of_ne`.

**Pass 2 Stage B (carry-chain arithmetic — the modular-addition correctness):** `rippleCirc`, the
in-place ripple adder over a disjoint-wire `RippleLayout`, computes `(A + B) mod 2 ^ n` into register
`B`: `rippleCirc_correct`. Proved by induction on the slices (`rippleCirc_invariant`, the 4-clause
carry invariant) lifting `fullAdder_correct_general` through the frame lemma and the per-slice
arithmetic `fulladder_nat`. Non-vacuity witnessed by `rippleLayout2` (a concrete 2-bit layout on
`Fin 7`). This is the genuine *computational* correctness, not just the cost.
-/

@[expose] public section

namespace Reversible

variable {n : ℕ}

/-! ### Register encoding (little-endian) -/

/-- Little-endian binary readout of a wire state: wire `i` carries place value `2 ^ i`. -/
def regVal (s : State n) : ℕ := ∑ i : Fin n, if s i then 2 ^ (i : ℕ) else 0

@[simp] theorem regVal_zero (s : State 0) : regVal s = 0 := by
  simp [regVal]

/-- The register value is bounded by `2 ^ n` (an `n`-wire register holds an `n`-bit number). -/
theorem regVal_lt_two_pow (s : State n) : regVal s < 2 ^ n := by
  induction n with
  | zero => simp [regVal]
  | succ m ih =>
    -- Split the top wire off the sum.
    have hsplit : regVal s
        = (∑ i : Fin m, if s (i.castSucc) then 2 ^ (i : ℕ) else 0)
          + (if s (Fin.last m) then 2 ^ m else 0) := by
      simp only [regVal, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    -- The lower-`m` part is `< 2 ^ m` (it is `regVal` of the restricted state).
    have hlow : (∑ i : Fin m, if s (i.castSucc) then 2 ^ (i : ℕ) else 0) < 2 ^ m :=
      ih (fun i => s i.castSucc)
    rw [hsplit, pow_succ]
    have htop : (if s (Fin.last m) then 2 ^ m else 0) ≤ 2 ^ m := by
      split <;> simp
    omega

/-- The general place-value update law for `Function.update s i b`: replacing wire `i`'s bit by `b`
(for ANY prior bit `s i` and ANY new bit `b`) removes `i`'s old place-value contribution and adds the
new one. The reusable round-trip helper consumed by ModMul / ScalarMul. -/
theorem regVal_update_eq (s : State n) (i : Fin n) (b : Bool) :
    regVal (Function.update s i b)
      = (regVal s - (if s i then 2 ^ (i : ℕ) else 0)) + (if b then 2 ^ (i : ℕ) else 0) := by
  classical
  have hmem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  -- Peel index `i` out of both sums.
  have hupd : regVal (Function.update s i b)
      = (if b then 2 ^ (i : ℕ) else 0)
        + ∑ j ∈ Finset.univ.erase i, if Function.update s i b j then 2 ^ (j : ℕ) else 0 := by
    rw [regVal, ← Finset.add_sum_erase _ _ hmem, Function.update_self]
  have horig : regVal s
      = (if s i then 2 ^ (i : ℕ) else 0)
        + ∑ j ∈ Finset.univ.erase i, if s j then 2 ^ (j : ℕ) else 0 := by
    rw [regVal, ← Finset.add_sum_erase _ _ hmem]
  -- Off-index terms agree.
  have hcongr : (∑ j ∈ Finset.univ.erase i, if Function.update s i b j then 2 ^ (j : ℕ) else 0)
      = ∑ j ∈ Finset.univ.erase i, if s j then 2 ^ (j : ℕ) else 0 := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hupd, horig, hcongr]
  omega

/-! ### The full-adder gadget (the verified primitive) -/

/-- Boolean majority of three bits: at least two are set. -/
def majority (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-- The four-gate full adder on wires `a b cin cout` (with `cout` initialised `false`):
`b ← a ⊕ b ⊕ cin` (sum bit), `cout ← majority(a, b, cin)` (carry-out), `a`/`cin` unchanged.

The gate order realises the standard in-place adder: write the partial carry into `cout` from
`(a,b)`, fold `a` into `b`, fold `(cin,b)` into `cout`, fold `cin` into `b`. Correctness on the
concrete layout is `fullAdder_correct`. -/
def fullAdder (a b cin cout : Fin n) : Circuit n :=
  [.CCX a b cout, .CX a b, .CCX cin b cout, .CX cin b]

/-- **Full-adder correctness — genuine all-inputs coverage.** On the concrete `State 4` layout
(wires `0,1,2,3 = a,b,cin,cout`), with `cout` initialised `false`, the gadget computes the sum bit
on wire `1`, the carry-out on wire `3`, and preserves `a` (wire `0`) and `cin` (wire `2`). Proved by
`decide` over the finite `State 4 = Fin 4 → Bool` (16 inputs, each input fixed `s 3 = false`). -/
theorem fullAdder_correct :
    ∀ s : State 4, s 3 = false →
      (denote (fullAdder 0 1 2 3) s 1 = (s 0 ^^ s 1 ^^ s 2))
        ∧ (denote (fullAdder 0 1 2 3) s 3 = majority (s 0) (s 1) (s 2))
        ∧ (denote (fullAdder 0 1 2 3) s 0 = s 0)
        ∧ (denote (fullAdder 0 1 2 3) s 2 = s 2) := by
  decide

/-- **Frame lemma for the gadget.** A wire distinct from all four of `a, b, cin, cout` is untouched
by `fullAdder` (every gate's wires lie in `{a, b, cin, cout}`). The payoff of the Circuit-level
`denote_apply_of_forall_not_mem`; lets the carry-chain (Pass 2) lift this slice over a register. -/
theorem fullAdder_apply_of_ne {a b cin cout w : Fin n}
    (ha : w ≠ a) (hb : w ≠ b) (hcin : w ≠ cin) (hcout : w ≠ cout) (s : State n) :
    denote (fullAdder a b cin cout) s w = s w := by
  apply denote_apply_of_forall_not_mem
  intro g hg
  simp only [fullAdder, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;>
    simp_all [gateWires]

/-- **Full-adder correctness, general `Fin n` wires.** For pairwise-distinct wires `a, b, cin, cout`
with `cout` initialised `false`, the gadget writes the sum bit to `b`, the carry-out to `cout`, and
preserves `a` and `cin` — over arbitrary `Fin n` (not just the concrete `State 4` of
`fullAdder_correct`). This is the slice the ripple carry-chain (Pass 2) iterates. -/
theorem fullAdder_correct_general {a b cin cout : Fin n}
    (hba : b ≠ a) (hbcin : b ≠ cin) (hcouta : cout ≠ a) (hcoutb : cout ≠ b)
    (hcoutcin : cout ≠ cin) (hacin : a ≠ cin) {s : State n} (hc0 : s cout = false) :
    denote (fullAdder a b cin cout) s b = (s a ^^ s b ^^ s cin)
      ∧ denote (fullAdder a b cin cout) s cout = majority (s a) (s b) (s cin)
      ∧ denote (fullAdder a b cin cout) s a = s a
      ∧ denote (fullAdder a b cin cout) s cin = s cin := by
  have hab : a ≠ b := hba.symm
  have hcinb : cin ≠ b := hbcin.symm
  have haco : a ≠ cout := hcouta.symm
  have hbco : b ≠ cout := hcoutb.symm
  have hcinco : cin ≠ cout := hcoutcin.symm
  have hcina : cin ≠ a := hacin.symm
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [fullAdder, denote_cons, denote_nil] <;>
    simp_all [denoteGate] <;>
    cases s a <;> cases s b <;> cases s cin <;> decide

/-! ### Derived cost of the gadget -/

/-- **Derived cost of the full adder** (from the gate list, via `circuitCost`): two Toffolis, two
CNOTs, Toffoli depth two, everything else zero. Not asserted — read off `[CCX, CX, CCX, CX]`. -/
theorem fullAdder_cost (a b cin cout : Fin n) :
    circuitCost (fullAdder a b cin cout)
      = { qubits := n, ancilla := 0, toffoli := 2, toffoliDepth := 2,
          cnot := 2, tCount := 0, meas := 0 } := by
  simp [circuitCost, fullAdder, gateCost]

@[simp] theorem fullAdder_toffoli (a b cin cout : Fin n) :
    (circuitCost (fullAdder a b cin cout)).toffoli = 2 := by
  rw [fullAdder_cost]

@[simp] theorem fullAdder_cnot (a b cin cout : Fin n) :
    (circuitCost (fullAdder a b cin cout)).cnot = 2 := by
  rw [fullAdder_cost]

/-! ### Ripple adder (general `n`): linear cost -/

/-- An `k`-slice ripple adder: the concatenation of `fullAdder` gadgets, one per quadruple of wires
in `slices`. A quadruple is `(a, b, cin, cout)`. The wire layout (which carries feed which sums) is a
Pass-2 concern; Pass 1 fixes only the *gate list* (hence the cost). -/
def rippleAdder (slices : List (Fin n × Fin n × Fin n × Fin n)) : Circuit n :=
  slices.flatMap (fun q => fullAdder q.1 q.2.1 q.2.2.1 q.2.2.2)

@[simp] theorem rippleAdder_nil : rippleAdder ([] : List (Fin n × Fin n × Fin n × Fin n)) = [] := rfl

/-- **Ripple-adder Toffoli count is linear in the number of slices.** Each slice contributes exactly
two Toffolis (`fullAdder_toffoli`); the count adds over the concatenation
(`cost_comp_toffoli_count`). Proved by induction over the slice list, composing the Tranche-1
lemma — not by re-deriving the sum. -/
theorem rippleAdder_toffoli (slices : List (Fin n × Fin n × Fin n × Fin n)) :
    (circuitCost (rippleAdder slices)).toffoli = 2 * slices.length := by
  induction slices with
  | nil => simp
  | cons q rest ih =>
    have hsplit : rippleAdder (q :: rest)
        = fullAdder q.1 q.2.1 q.2.2.1 q.2.2.2 ++ rippleAdder rest := by
      simp [rippleAdder, List.flatMap_cons]
    rw [hsplit, cost_comp_toffoli_count, fullAdder_toffoli, ih, List.length_cons]
    omega

/-- **Ripple-adder CNOT count is linear in the number of slices.** Same route via
`cost_comp_cnot_count` + `fullAdder_cnot`. -/
theorem rippleAdder_cnot (slices : List (Fin n × Fin n × Fin n × Fin n)) :
    (circuitCost (rippleAdder slices)).cnot = 2 * slices.length := by
  induction slices with
  | nil => simp
  | cons q rest ih =>
    have hsplit : rippleAdder (q :: rest)
        = fullAdder q.1 q.2.1 q.2.2.1 q.2.2.2 ++ rippleAdder rest := by
      simp [rippleAdder, List.flatMap_cons]
    rw [hsplit, cost_comp_cnot_count, fullAdder_cnot, ih, List.length_cons]
    omega

/-! ### Pass 2: ripple carry-chain arithmetic correctness

The Pass-1 ripple cost says nothing about what `rippleAdder` *computes*. Here we exhibit a concrete
in-place ripple layout (input registers `A`, `B` and a carry chain `C`, as injective pairwise-disjoint
wire families) and prove the register `B` ends up holding `(A + B) mod 2 ^ n`, by induction on the
slices, lifting `fullAdder_correct_general` through the frame lemma `fullAdder_apply_of_ne`. -/

/-- Place-value readout of the low `k` bits of a register laid out on wires `f i` (place value
`2 ^ i` at index `i`). Indices are `ℕ` to keep the layout arithmetic coercion-free. -/
def regValRange {m : ℕ} (f : ℕ → Fin m) (s : State m) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, (s (f i)).toNat * 2 ^ i

theorem regValRange_succ {m : ℕ} (f : ℕ → Fin m) (s : State m) (k : ℕ) :
    regValRange f s (k + 1) = regValRange f s k + (s (f k)).toNat * 2 ^ k := by
  simp [regValRange, Finset.sum_range_succ]

theorem regValRange_lt {m : ℕ} (f : ℕ → Fin m) (s : State m) (k : ℕ) :
    regValRange f s k < 2 ^ k := by
  induction k with
  | zero => simp [regValRange]
  | succ k ih =>
    rw [regValRange_succ, pow_succ]
    have : (s (f k)).toNat ≤ 1 := by cases s (f k) <;> simp
    have h2 : (s (f k)).toNat * 2 ^ k ≤ 2 ^ k := by
      calc (s (f k)).toNat * 2 ^ k ≤ 1 * 2 ^ k := by exact Nat.mul_le_mul_right _ this
        _ = 2 ^ k := one_mul _
    omega

/-- **The full-adder arithmetic identity on ℕ.** The sum bit plus twice the carry equals the
arithmetic sum of the three input bits — the per-slice fact the carry chain accumulates. -/
theorem fulladder_nat (a b c : Bool) :
    (a ^^ b ^^ c).toNat + 2 * (majority a b c).toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

/-- A ripple-carry adder layout on `m` wires for `n`-bit registers: input registers `A`, `B` and a
carry chain `C` (with `C 0` the input carry and `C n` the output carry), as `ℕ`-indexed wire families.
The three images are pairwise disjoint and each is injective on its used index range — exactly the
geometry hypotheses any real layout satisfies (they are about *wires*, not about the computation). -/
structure RippleLayout (m n : ℕ) where
  /-- Wires of register `A` (the first addend). -/
  A : ℕ → Fin m
  /-- Wires of register `B` (the second addend; overwritten with the sum). -/
  B : ℕ → Fin m
  /-- Wires of the carry chain (`C i` = carry into bit `i`). -/
  C : ℕ → Fin m
  hAB : ∀ i j, A i ≠ B j
  hAC : ∀ i j, A i ≠ C j
  hBC : ∀ i j, B i ≠ C j
  hAinj : ∀ i j, i < n → j < n → A i = A j → i = j
  hBinj : ∀ i j, i < n → j < n → B i = B j → i = j
  hCinj : ∀ i j, i < n + 1 → j < n + 1 → C i = C j → i = j

variable {m : ℕ}

/-- One ripple slice: a full adder on `(A i, B i, C i, C (i+1))`. -/
def rippleSlice (L : RippleLayout m n) (i : ℕ) : Circuit m :=
  fullAdder (L.A i) (L.B i) (L.C i) (L.C (i + 1))

/-- The circuit of the first `k` slices (bits `0 .. k-1`). -/
def ripplePrefix (L : RippleLayout m n) (k : ℕ) : Circuit m :=
  (List.range k).flatMap (rippleSlice L)

/-- The full ripple adder: all `n` slices. -/
def rippleCirc (L : RippleLayout m n) : Circuit m := ripplePrefix L n

theorem denote_ripplePrefix_succ (L : RippleLayout m n) (k : ℕ) (s : State m) :
    denote (ripplePrefix L (k + 1)) s = denote (rippleSlice L k) (denote (ripplePrefix L k) s) := by
  simp only [ripplePrefix, List.range_succ, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, denote_append]

/-- **The carry-chain invariant.** After the first `k` slices: register `B`'s low `k` bits plus the
carry into bit `k` equal the low-`k` sum of `A` and `B` (P1); register `A` is untouched (P2); the
unprocessed high bits of `B` (P4) and the unset high carries (P5) are preserved. By induction on `k`,
each step lifting `fullAdder_correct_general` through the frame lemma `fullAdder_apply_of_ne`. -/
theorem rippleCirc_invariant (L : RippleLayout m n) (s : State m) (hC0 : ∀ j, s (L.C j) = false) :
    ∀ k, k ≤ n →
      (regValRange L.B (denote (ripplePrefix L k) s) k
          + (denote (ripplePrefix L k) s (L.C k)).toNat * 2 ^ k
        = regValRange L.A s k + regValRange L.B s k)
      ∧ (∀ j, j < n → denote (ripplePrefix L k) s (L.A j) = s (L.A j))
      ∧ (∀ j, k ≤ j → j < n → denote (ripplePrefix L k) s (L.B j) = s (L.B j))
      ∧ (∀ j, k < j → j < n + 1 → denote (ripplePrefix L k) s (L.C j) = s (L.C j)) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [ripplePrefix, regValRange, hC0]
    · intro j _; simp [ripplePrefix]
    · intro j _ _; simp [ripplePrefix]
    · intro j _ _; simp [ripplePrefix]
  | succ k ih =>
    intro hk
    have hkn : k ≤ n := Nat.le_of_succ_le hk
    have hkltn : k < n := hk
    obtain ⟨hP1, hP2, hP4, hP5⟩ := ih hkn
    have hba : L.B k ≠ L.A k := (L.hAB k k).symm
    have hbcin : L.B k ≠ L.C k := L.hBC k k
    have hcouta : L.C (k + 1) ≠ L.A k := (L.hAC k (k + 1)).symm
    have hcoutb : L.C (k + 1) ≠ L.B k := (L.hBC k (k + 1)).symm
    have hcoutcin : L.C (k + 1) ≠ L.C k := by
      intro h; exact (Nat.succ_ne_self k) (L.hCinj (k + 1) k (by omega) (by omega) h)
    have hacin : L.A k ≠ L.C k := L.hAC k k
    have hc0' : denote (ripplePrefix L k) s (L.C (k + 1)) = false := by
      rw [hP5 (k + 1) (by omega) (by omega)]; exact hC0 (k + 1)
    obtain ⟨hsum, hcarry, hAk, _hCk⟩ :=
      fullAdder_correct_general hba hbcin hcouta hcoutb hcoutcin hacin hc0'
    simp only [denote_ripplePrefix_succ, rippleSlice]
    set sk := denote (ripplePrefix L k) s with hskdef
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- P1: the carry-chain arithmetic
      have hBklow : regValRange L.B (denote (fullAdder (L.A k) (L.B k) (L.C k) (L.C (k + 1))) sk) k
          = regValRange L.B sk k := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        rw [fullAdder_apply_of_ne ((L.hAB k j).symm)
          (fun h => (show j ≠ k by omega) (L.hBinj j k (by omega) hkltn h))
          (L.hBC j k) (L.hBC j (k + 1)) sk]
      rw [regValRange_succ, hBklow, hsum, hcarry, regValRange_succ, regValRange_succ,
          hP2 k hkltn, hP4 k (Nat.le_refl k) hkltn, pow_succ]
      have hfn := fulladder_nat (s (L.A k)) (s (L.B k)) (sk (L.C k))
      cases h1 : s (L.A k) <;> cases h2 : s (L.B k) <;> cases h3 : sk (L.C k) <;>
        simp only [h1, h2, h3, majority, Bool.xor_false, Bool.xor_true, Bool.not_true,
          Bool.not_false, Bool.and_self, Bool.and_true, Bool.and_false, Bool.or_true,
          Bool.or_false, Bool.or_self, Bool.toNat_true, Bool.toNat_false, zero_mul, one_mul,
          mul_zero, add_zero, zero_add] at hP1 hfn ⊢ <;>
        omega
    · -- P2: A untouched
      intro j hj
      by_cases hjk : j = k
      · subst hjk; rw [hAk]; exact hP2 j hj
      · rw [fullAdder_apply_of_ne (fun h => hjk (L.hAinj j k hj hkltn h))
          (L.hAB j k) (L.hAC j k) (L.hAC j (k + 1)) sk]
        exact hP2 j hj
    · -- P4: high bits of B preserved
      intro j hjk hjn
      rw [fullAdder_apply_of_ne ((L.hAB k j).symm)
        (fun h => (show j ≠ k by omega) (L.hBinj j k hjn hkltn h))
        (L.hBC j k) (L.hBC j (k + 1)) sk]
      exact hP4 j (by omega) hjn
    · -- P5: high carries preserved
      intro j hjk hjn
      rw [fullAdder_apply_of_ne ((L.hAC k j).symm) ((L.hBC k j).symm)
        (fun h => (show j ≠ k by omega) (L.hCinj j k hjn (by omega) h))
        (fun h => (show j ≠ k + 1 by omega) (L.hCinj j (k + 1) hjn (by omega) h)) sk]
      exact hP5 j (by omega) hjn

/-- **Ripple-carry adder correctness (Pass 2 headline).** For a disjoint-wire layout with all carries
initialised `false`, the ripple adder leaves register `B` holding `(A + B) mod 2 ^ n`. The carry-chain
identity, derived from the exhibited circuit `rippleCirc` — not postulated. -/
theorem rippleCirc_correct (L : RippleLayout m n) (s : State m) (hC0 : ∀ j, s (L.C j) = false) :
    regValRange L.B (denote (rippleCirc L) s) n
      = (regValRange L.A s n + regValRange L.B s n) % 2 ^ n := by
  obtain ⟨hP1, -, -, -⟩ := rippleCirc_invariant L s hC0 n (Nat.le_refl n)
  rw [rippleCirc]
  have hlt : regValRange L.B (denote (ripplePrefix L n) s) n < 2 ^ n := regValRange_lt _ _ _
  cases h : denote (ripplePrefix L n) s (L.C n)
  · simp only [h, Bool.toNat_false, zero_mul, add_zero] at hP1
    rw [← hP1, Nat.mod_eq_of_lt hlt]
  · simp only [h, Bool.toNat_true, one_mul] at hP1
    rw [hP1.symm, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]

/-! ### Non-vacuity witness

A concrete `2`-bit ripple layout on `Fin 7` (register `A` on wires `0,1`, `B` on `2,3`, carry chain
`C` on `4,5,6`), exhibiting that `RippleLayout` is inhabited and `rippleCirc_correct` applies — the
headline is not vacuously quantified over an unsatisfiable hypothesis bundle. -/

/-- A concrete 2-bit adder layout: `A → {0,1}`, `B → {2,3}`, carry chain `C → {4,5,6}` on `Fin 7`. -/
def rippleLayout2 : RippleLayout 7 2 where
  A i := if i = 0 then 0 else 1
  B i := if i = 0 then 2 else 3
  C i := if i = 0 then 4 else if i = 1 then 5 else 6
  hAB i j := by split_ifs <;> decide
  hAC i j := by split_ifs <;> decide
  hBC i j := by split_ifs <;> decide
  hAinj i j hi hj h := by split_ifs at h with h1 h2 h2 <;> omega
  hBinj i j hi hj h := by split_ifs at h with h1 h2 h2 <;> omega
  hCinj i j hi hj h := by split_ifs at h <;> omega

/-- The Pass-2 headline is non-vacuous: it applies to the concrete `rippleLayout2`. -/
example (s : State 7) (hC0 : ∀ j, s (rippleLayout2.C j) = false) :
    regValRange rippleLayout2.B (denote (rippleCirc rippleLayout2) s) 2
      = (regValRange rippleLayout2.A s 2 + regValRange rippleLayout2.B s 2) % 2 ^ 2 :=
  rippleCirc_correct rippleLayout2 s hC0

end Reversible
