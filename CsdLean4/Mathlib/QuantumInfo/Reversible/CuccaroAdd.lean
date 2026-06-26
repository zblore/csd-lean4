import CsdLean4.Mathlib.QuantumInfo.Reversible.Eval
import Mathlib.Tactic.Ring

/-!
# The carry-clean (Cuccaro) ripple-carry adder — in-place, ancilla-restoring  (ECDLP Phase 2, Stage 1)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The single highest-leverage reversible gadget the corpus lacked: an **in-place, ancilla-restoring**
ripple-carry adder (Cuccaro, Draper, Kutin, Moulton 2004). Unlike `rippleCirc` / `cRippleCirc`
(which thread an explicit Θ(n)-wire carry chain `C` and leave its top carry dirty), the Cuccaro adder
stores the carries *inside the preserved addend register* during the computation and **restores them**,
needing only **one** clean ancilla `Z` (the low carry, init `false`, returned `false`). This collapses
the fresh-ancilla penalty that every prior ECDLP adder (`ModularAdd`, `ModularAddCtrl`,
`DoublingAssembly`) carried as a named residue, and brings the per-multiply Toffoli cost from ~30n²
toward ~2n².

## The construction (standard Cuccaro, mod 2ⁿ, no output carry, one ancilla)

Two three-gate blocks on `(c, b, a)` (carry-in, sum register, addend register):

* `maj c b a := [CX a b, CX a c, CCX c b a]` — folds the carry-out into `a`:
  `a ← majority(a, b, c)`, `b ← b ⊕ a`, `c ← c ⊕ a` (the `(b,c)` side effects are undone by `uma`).
* `uma c b a := [CCX c b a, CX a c, CX c b]` — writes the sum bit and restores: applied to a
  post-`maj` state it gives `b ← a ⊕ b ⊕ c` (the sum), `a ← a` (restored), `c ← c` (restored).

The circuit is a forward `maj` chain then a backward `uma` chain, with the carry threading through the
addend register's wires. Equivalently — and this is the formulation proved here — it is the **recursive**
`maj c b₀ a₀ ++ (adder on the high bits with carry-in a₀) ++ uma c b₀ a₀`, which makes the
compute / uncompute correctness a clean induction on the bit count (`cuccaroRec_correct`).

## What is proved here

* `maj` / `uma` with per-block all-inputs `decide` correctness (`maj_correct` / `uma_correct` on the
  concrete `State 3`) and the general `Fin m` lifts (`maj_correct_general` / `uma_correct_general`).
* `cuccaroAdd_correct` — **general `n`, in-place sum**: register `A` ends holding `(A + B) mod 2ⁿ`.
* `cuccaroAdd_preserves_B` — register `B` (the addend) is returned untouched.
* `cuccaroAdd_ancilla_clean` — **the carry-clean property**: the ancilla `Z` returns to `false`, so the
  adder is reusable in place with no fresh ancilla. This is what distinguishes it from
  `rippleCirc` / `cRippleCirc`.
* `cuccaroAdd_toffoli` — derived `2n` Toffolis (`n` `maj` + `n` `uma`, each one `CCX`).

**Scope (honest):** this is the value-correct, in-place, ancilla-restoring adder modulo `2ⁿ`. It does
**no** modular (`mod N`) reduction — a *carry-clean modular* adder / multiply is Stage 2. The `n=3`
witness (`cuccaroLayout3`, `5 + 6 mod 8 = 3`) is `#eval`/`decide`-cross-checked through the strict
`Array` evaluator `runArr`.
-/

namespace Reversible

variable {m n : ℕ}

/-! ### Arithmetic helpers -/

/-- Bottom-bit split of a place-value readout: peel index `0` off `regValRange` and factor `2` out of
the remaining (shifted) register. The recursion's per-step accounting primitive. -/
theorem regValRange_succ' (f : ℕ → Fin m) (s : State m) (k : ℕ) :
    regValRange f s (k + 1)
      = (s (f 0)).toNat + 2 * regValRange (fun i => f (i + 1)) s k := by
  rw [regValRange, Finset.sum_range_succ', regValRange, Finset.mul_sum]
  simp only [pow_zero, mul_one]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The carry-propagation modular identity: a low bit plus twice a value, reduced mod `2P`, is the low
bit plus twice the value reduced mod `P`. The arithmetic core of the per-slice carry step. -/
theorem nat_lowbit_carry (lowbit X P : ℕ) (hlb : lowbit < 2) (hP : 0 < P) :
    (lowbit + 2 * X) % (2 * P) = lowbit + 2 * (X % P) := by
  conv_lhs => rw [← Nat.div_add_mod X P]
  rw [Nat.mul_add, ← Nat.mul_assoc]
  rw [show lowbit + (2 * P * (X / P) + 2 * (X % P))
        = (lowbit + 2 * (X % P)) + 2 * P * (X / P) by ring]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by have := Nat.mod_lt X hP; omega)

/-! ### The MAJ / UMA blocks -/

/-- The `maj` (majority) block on wires `c b a` (carry-in, sum register, addend register):
`[CX a b, CX a c, CCX c b a]`. Folds the carry-out into `a`. -/
def maj (c b a : Fin m) : Circuit m := [.CX a b, .CX a c, .CCX c b a]

/-- The `uma` (un-majority-and-add) block on wires `c b a`: `[CCX c b a, CX a c, CX c b]`. Applied to a
post-`maj` state, writes the sum into `b` and restores `a`, `c`. -/
def uma (c b a : Fin m) : Circuit m := [.CCX c b a, .CX a c, .CX c b]

/-- **`maj` correctness — all-inputs `decide`.** On `State 3` (wires `0,1,2 = c,b,a`): `a ← majority`,
`b ← b ⊕ a`, `c ← c ⊕ a`. -/
theorem maj_correct :
    ∀ s : State 3,
      (denote (maj 0 1 2) s 2 = majority (s 2) (s 1) (s 0))
        ∧ (denote (maj 0 1 2) s 1 = (s 1 ^^ s 2))
        ∧ (denote (maj 0 1 2) s 0 = (s 0 ^^ s 2)) := by
  decide

/-- **`uma` correctness — all-inputs `decide`.** On `State 3` (wires `0,1,2 = c,b,a`), the raw gate
action: `a ← a ⊕ (c ∧ b)`, then `c ← c ⊕ a'`, then `b ← b ⊕ c'`. -/
theorem uma_correct :
    ∀ s : State 3,
      (denote (uma 0 1 2) s 2 = (s 2 ^^ (s 0 && s 1)))
        ∧ (denote (uma 0 1 2) s 0 = (s 0 ^^ (s 2 ^^ (s 0 && s 1))))
        ∧ (denote (uma 0 1 2) s 1 = (s 1 ^^ (s 0 ^^ (s 2 ^^ (s 0 && s 1))))) := by
  decide

/-- **Frame lemma for `maj`.** A wire distinct from `c, b, a` is untouched. -/
theorem maj_apply_of_ne {c b a w : Fin m} (hc : w ≠ c) (hb : w ≠ b) (ha : w ≠ a) (s : State m) :
    denote (maj c b a) s w = s w := by
  apply denote_apply_of_forall_not_mem
  intro g hg
  simp only [maj, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp_all [gateWires]

/-- **Frame lemma for `uma`.** A wire distinct from `c, b, a` is untouched. -/
theorem uma_apply_of_ne {c b a w : Fin m} (hc : w ≠ c) (hb : w ≠ b) (ha : w ≠ a) (s : State m) :
    denote (uma c b a) s w = s w := by
  apply denote_apply_of_forall_not_mem
  intro g hg
  simp only [uma, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp_all [gateWires]

/-- **`maj` correctness, general `Fin m` wires.** For pairwise-distinct `c, b, a`:
`a ← majority(a,b,c)`, `b ← b ⊕ a`, `c ← c ⊕ a`. -/
theorem maj_correct_general {c b a : Fin m} (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a)
    (s : State m) :
    denote (maj c b a) s a = majority (s a) (s b) (s c)
      ∧ denote (maj c b a) s b = (s b ^^ s a)
      ∧ denote (maj c b a) s c = (s c ^^ s a) := by
  have hbc := hcb.symm; have hac := hca.symm; have hab := hba.symm
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [maj, denote_cons, denote_nil, denoteGate] <;>
    simp_all <;>
    cases s a <;> cases s b <;> cases s c <;> simp_all [majority]

/-- **`uma` correctness, general `Fin m` wires.** For pairwise-distinct `c, b, a`, the raw gate action
(in terms of the input bits). Composed with the post-`maj` relation it yields the sum / restoration. -/
theorem uma_correct_general {c b a : Fin m} (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a)
    (s : State m) :
    denote (uma c b a) s a = (s a ^^ (s c && s b))
      ∧ denote (uma c b a) s c = (s c ^^ (s a ^^ (s c && s b)))
      ∧ denote (uma c b a) s b = (s b ^^ (s c ^^ (s a ^^ (s c && s b)))) := by
  have hbc := hcb.symm; have hac := hca.symm; have hab := hba.symm
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [uma, denote_cons, denote_nil, denoteGate] <;>
    simp_all <;>
    cases s a <;> cases s b <;> cases s c <;> simp_all

/-! ### Derived block costs -/

@[simp] theorem maj_toffoli (c b a : Fin m) : (circuitCost (maj c b a)).toffoli = 1 := by
  simp [circuitCost, maj, gateCost]

@[simp] theorem uma_toffoli (c b a : Fin m) : (circuitCost (uma c b a)).toffoli = 1 := by
  simp [circuitCost, uma, gateCost]

/-! ### The Cuccaro layout and recursive circuit -/

/-- A Cuccaro-adder layout on `m` wires for `n`-bit registers: the sum register `A` (overwritten with
the sum), the addend register `B` (preserved; also holds the carry chain internally during the run),
and a single clean ancilla `Z` (the low carry, init/returned `false`). The two register images are
pairwise disjoint, disjoint from `Z`, and each injective on its used index range. -/
structure CuccaroLayout (m n : ℕ) where
  /-- Wires of the sum register `A` (overwritten with `(A + B) mod 2ⁿ`). -/
  A : ℕ → Fin m
  /-- Wires of the addend register `B` (preserved; carries threaded through and restored). -/
  B : ℕ → Fin m
  /-- The single clean ancilla (low carry; init/returned `false`). -/
  Z : Fin m
  hAB : ∀ i j, A i ≠ B j
  hAZ : ∀ i, A i ≠ Z
  hBZ : ∀ i, B i ≠ Z
  hAinj : ∀ i j, i < n → j < n → A i = A j → i = j
  hBinj : ∀ i j, i < n → j < n → B i = B j → i = j

/-- The recursive Cuccaro adder on the `len` bits `start .. start + len - 1` with carry-in wire
`carry`: `maj carry A_start B_start ++ (recurse on the high bits, carry-in B_start) ++
uma carry A_start B_start`. The carry-out of the low slice (`majority`, stored in `B start`) is the
carry-in of the recursive remainder; the outer `uma` writes the low sum bit and restores. -/
def cuccaroRec (L : CuccaroLayout m n) : Fin m → ℕ → ℕ → Circuit m
  | _, _, 0 => []
  | carry, start, len + 1 =>
      maj carry (L.A start) (L.B start)
        ++ cuccaroRec L (L.B start) (start + 1) len
        ++ uma carry (L.A start) (L.B start)

/-- The full Cuccaro adder: all `n` bits, carry-in the ancilla `Z`. -/
def cuccaroAdd (L : CuccaroLayout m n) : Circuit m := cuccaroRec L L.Z 0 n

theorem denote_cuccaroRec_succ (L : CuccaroLayout m n) (carry : Fin m) (start len : ℕ)
    (s : State m) :
    denote (cuccaroRec L carry start (len + 1)) s
      = denote (uma carry (L.A start) (L.B start))
          (denote (cuccaroRec L (L.B start) (start + 1) len)
            (denote (maj carry (L.A start) (L.B start)) s)) := by
  show denote (maj carry (L.A start) (L.B start)
        ++ cuccaroRec L (L.B start) (start + 1) len
        ++ uma carry (L.A start) (L.B start)) s = _
  rw [denote_append, denote_append]

/-! ### Recursive correctness invariant -/

/-- **The Cuccaro carry-chain invariant.** For the `len`-bit recursive adder with carry-in `carry`
(disjoint from the register range): register `A` ends holding `(carry + A + B) mod 2^len` (P1);
register `B` is restored (P2); the carry-in wire is restored (P3); any external wire is preserved (P4).
By induction on `len`, peeling one `maj`/`uma` pair per step. -/
theorem cuccaroRec_correct (L : CuccaroLayout m n) :
    ∀ (len start : ℕ) (carry : Fin m) (s : State m),
      start + len ≤ n →
      (∀ i, i < len → carry ≠ L.A (start + i)) →
      (∀ i, i < len → carry ≠ L.B (start + i)) →
      (regValRange (fun i => L.A (start + i)) (denote (cuccaroRec L carry start len) s) len
        = ((s carry).toNat
            + regValRange (fun i => L.A (start + i)) s len
            + regValRange (fun i => L.B (start + i)) s len) % 2 ^ len)
      ∧ (∀ i, i < len →
          denote (cuccaroRec L carry start len) s (L.B (start + i)) = s (L.B (start + i)))
      ∧ (denote (cuccaroRec L carry start len) s carry = s carry)
      ∧ (∀ w, w ≠ carry → (∀ i, i < len → w ≠ L.A (start + i))
            → (∀ i, i < len → w ≠ L.B (start + i))
            → denote (cuccaroRec L carry start len) s w = s w) := by
  intro len
  induction len with
  | zero =>
    intro start carry s _ _ _
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [cuccaroRec, regValRange, Nat.mod_one]
    · intro i hi; omega
    · simp [cuccaroRec]
    · intro w _ _ _; simp [cuccaroRec]
  | succ len ih =>
    intro start carry s hbound hcA hcB
    -- The three slice wires.
    have hcAst : carry ≠ L.A start := by have := hcA 0 (by omega); simpa using this
    have hcBst : carry ≠ L.B start := by have := hcB 0 (by omega); simpa using this
    have hAstBst : L.A start ≠ L.B start := L.hAB start start
    have hstart_lt : start < n := by omega
    -- carry distinct from the inner (high-bit) range.
    have hcAhi : ∀ i, i < len → carry ≠ L.A (start + 1 + i) := fun i _ => by
      have := hcA (1 + i) (by omega); rwa [show start + (1 + i) = start + 1 + i from by omega] at this
    have hcBhi : ∀ i, i < len → carry ≠ L.B (start + 1 + i) := fun i _ => by
      have := hcB (1 + i) (by omega); rwa [show start + (1 + i) = start + 1 + i from by omega] at this
    -- maj step values.
    obtain ⟨hmajA, hmajB, hmajC⟩ := maj_correct_general hcAst hcBst hAstBst s
    set s1 := denote (maj carry (L.A start) (L.B start)) s with hs1
    have hsBst : s1 (L.B start) = majority (s (L.B start)) (s (L.A start)) (s carry) := hmajA
    have hsAst : s1 (L.A start) = (s (L.A start) ^^ s (L.B start)) := hmajB
    have hsC : s1 carry = (s carry ^^ s (L.B start)) := hmajC
    -- inner carry-in wire is B start; its disjointness from the inner range.
    have hBst_neq_Ahi : ∀ i, i < len → L.B start ≠ L.A (start + 1 + i) := by
      intro i _; exact (L.hAB (start + 1 + i) start).symm
    have hBst_neq_Bhi : ∀ i, i < len → L.B start ≠ L.B (start + 1 + i) := by
      intro i hi h
      have := L.hBinj start (start + 1 + i) (by omega) (by omega) h; omega
    -- s1 = s on the inner range.
    have hs1_Ahi : ∀ i, i < len → s1 (L.A (start + 1 + i)) = s (L.A (start + 1 + i)) := by
      intro i hi
      exact maj_apply_of_ne (hcAhi i hi).symm
        (fun h => absurd (L.hAinj (start + 1 + i) start (by omega) hstart_lt h) (by omega))
        (L.hAB (start + 1 + i) start) s
    have hs1_Bhi : ∀ i, i < len → s1 (L.B (start + 1 + i)) = s (L.B (start + 1 + i)) := by
      intro i hi
      exact maj_apply_of_ne (hcBhi i hi).symm (L.hAB start (start + 1 + i)).symm
        (fun h => absurd (L.hBinj (start + 1 + i) start (by omega) hstart_lt h) (by omega)) s
    -- inner IH on s1.
    obtain ⟨hP1, hP2, hP3, hP4⟩ :=
      ih (start + 1) (L.B start) s1 (by omega) hBst_neq_Ahi hBst_neq_Bhi
    set s2 := denote (cuccaroRec L (L.B start) (start + 1) len) s1 with hs2
    -- s2 values on the slice wires (inner frame + carry restoration).
    have hs2_C : s2 carry = s1 carry :=
      hP4 carry hcBst (fun i hi => hcAhi i hi) (fun i hi => hcBhi i hi)
    have hs2_Ast : s2 (L.A start) = s1 (L.A start) :=
      hP4 (L.A start) hAstBst
        (fun i _ h => absurd (L.hAinj start (start + 1 + i) hstart_lt (by omega) h) (by omega))
        (fun i _ => L.hAB start (start + 1 + i))
    have hs2_Bst : s2 (L.B start) = s1 (L.B start) := hP3
    -- final state.
    set t := denote (cuccaroRec L carry start (len + 1)) s with ht
    have htdef : t = denote (uma carry (L.A start) (L.B start)) s2 := by
      rw [ht, denote_cuccaroRec_succ]
    obtain ⟨humaA, humaC, humaB⟩ := uma_correct_general hcAst hcBst hAstBst s2
    -- Resolve the three slice wires after uma, in terms of original bits.
    have ht_Bst : t (L.B start) = s (L.B start) := by
      rw [htdef, humaA, hs2_Bst, hs2_C, hs2_Ast, hsBst, hsC, hsAst]
      cases s (L.A start) <;> cases s (L.B start) <;> cases s carry <;> simp [majority]
    have ht_C : t carry = s carry := by
      rw [htdef, humaC, hs2_Bst, hs2_C, hs2_Ast, hsBst, hsC, hsAst]
      cases s (L.A start) <;> cases s (L.B start) <;> cases s carry <;> simp [majority]
    have ht_Ast : t (L.A start) = (s (L.A start) ^^ s (L.B start) ^^ s carry) := by
      rw [htdef, humaB, hs2_Bst, hs2_C, hs2_Ast, hsBst, hsC, hsAst]
      cases s (L.A start) <;> cases s (L.B start) <;> cases s carry <;> simp [majority]
    -- t = s2 on the inner range (uma frame).
    have ht_Ahi : ∀ i, i < len → t (L.A (start + 1 + i)) = s2 (L.A (start + 1 + i)) := by
      intro i hi
      rw [htdef]
      exact uma_apply_of_ne (hcAhi i hi).symm
        (fun h => absurd (L.hAinj (start + 1 + i) start (by omega) hstart_lt h) (by omega))
        (L.hAB (start + 1 + i) start) s2
    have ht_Bhi : ∀ i, i < len → t (L.B (start + 1 + i)) = s2 (L.B (start + 1 + i)) := by
      intro i hi
      rw [htdef]
      exact uma_apply_of_ne (hcBhi i hi).symm (L.hAB start (start + 1 + i)).symm
        (fun h => absurd (L.hBinj (start + 1 + i) start (by omega) hstart_lt h) (by omega)) s2
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- P1: the carry-chain arithmetic.
      set P := 2 ^ len with hPdef
      have hP : 0 < P := Nat.two_pow_pos len
      have hpow : 2 ^ (len + 1) = 2 * P := by rw [hPdef, pow_succ]; ring
      have hRAt : regValRange (fun i => L.A (start + 1 + i)) t len
          = regValRange (fun i => L.A (start + 1 + i)) s2 len := by
        apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi; rw [ht_Ahi i hi]
      have hRA1 : regValRange (fun i => L.A (start + 1 + i)) s1 len
          = regValRange (fun i => L.A (start + 1 + i)) s len := by
        apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi; rw [hs1_Ahi i hi]
      have hRB1 : regValRange (fun i => L.B (start + 1 + i)) s1 len
          = regValRange (fun i => L.B (start + 1 + i)) s len := by
        apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi; rw [hs1_Bhi i hi]
      rw [regValRange_succ' (fun i => L.A (start + i)) t,
          regValRange_succ' (fun i => L.A (start + i)) s,
          regValRange_succ' (fun i => L.B (start + i)) s]
      simp only [Nat.add_zero]
      have hnorm : (fun i => L.A (start + (i + 1))) = (fun i => L.A (start + 1 + i)) := by
        funext i; congr 1; omega
      have hnormB : (fun i => L.B (start + (i + 1))) = (fun i => L.B (start + 1 + i)) := by
        funext i; congr 1; omega
      rw [hnorm, hnormB, hRAt, hP1, hRA1, hRB1, hsBst, ht_Ast]
      have hL0lt : ((s (L.A start) ^^ s (L.B start) ^^ s carry)).toNat < 2 := by
        cases (s (L.A start) ^^ s (L.B start) ^^ s carry) <;> simp
      have hfa : (s carry).toNat + (s (L.A start)).toNat + (s (L.B start)).toNat
          = ((s (L.A start) ^^ s (L.B start) ^^ s carry)).toNat
            + 2 * (majority (s (L.B start)) (s (L.A start)) (s carry)).toNat := by
        cases s (L.A start) <;> cases s (L.B start) <;> cases s carry <;> decide
      set RA := regValRange (fun i => L.A (start + 1 + i)) s len with hRAd
      set RB := regValRange (fun i => L.B (start + 1 + i)) s len with hRBd
      set L0 := ((s (L.A start) ^^ s (L.B start) ^^ s carry)).toNat with hL0d
      set G := (majority (s (L.B start)) (s (L.A start)) (s carry)).toNat with hGd
      rw [hpow]
      have hregroup : (s carry).toNat
          + ((s (L.A start)).toNat + 2 * RA) + ((s (L.B start)).toNat + 2 * RB)
            = L0 + 2 * (G + RA + RB) := by omega
      rw [hregroup, nat_lowbit_carry L0 (G + RA + RB) P hL0lt hP]
    · -- P2: B restored.
      intro i hi
      rcases i with _ | j
      · simpa [Nat.add_zero] using ht_Bst
      · have hj : j < len := by omega
        rw [show start + (j + 1) = start + 1 + j from by omega, ht_Bhi j hj, hP2 j hj, hs1_Bhi j hj]
    · -- P3: carry restored.
      exact ht_C
    · -- P4: external wires preserved.
      intro w hwc hwA hwB
      have hwAst : w ≠ L.A start := by simpa [Nat.add_zero] using hwA 0 (by omega)
      have hwBst : w ≠ L.B start := by simpa [Nat.add_zero] using hwB 0 (by omega)
      rw [htdef, uma_apply_of_ne hwc hwAst hwBst s2,
          hP4 w hwBst
            (fun i hi => by
              have := hwA (1 + i) (by omega)
              rwa [show start + (1 + i) = start + 1 + i from by omega] at this)
            (fun i hi => by
              have := hwB (1 + i) (by omega)
              rwa [show start + (1 + i) = start + 1 + i from by omega] at this),
          hs1, maj_apply_of_ne hwc hwAst hwBst s]

/-! ### Headline theorems -/

/-- **Cuccaro adder correctness (in-place sum).** For a disjoint-wire layout with the ancilla `Z`
initialised `false`, the Cuccaro adder leaves register `A` holding `(A + B) mod 2ⁿ` — in place, with no
carry chain, one ancilla. -/
theorem cuccaroAdd_correct (L : CuccaroLayout m n) (s : State m) (hZ : s L.Z = false) :
    regValRange L.A (denote (cuccaroAdd L) s) n
      = (regValRange L.A s n + regValRange L.B s n) % 2 ^ n := by
  obtain ⟨hP1, -, -, -⟩ :=
    cuccaroRec_correct L n 0 L.Z s (by omega)
      (fun i _ => by simpa using (L.hAZ i).symm)
      (fun i _ => by simpa using (L.hBZ i).symm)
  rw [cuccaroAdd]
  have hA : (fun i => L.A (0 + i)) = L.A := by funext i; congr 1; omega
  have hB : (fun i => L.B (0 + i)) = L.B := by funext i; congr 1; omega
  rw [hA] at hP1
  rw [hB] at hP1
  rw [hP1, hZ]
  simp

set_option linter.unusedVariables false in
/-- **Register `B` is preserved.** The addend register is returned untouched (carries threaded through
it during the run are restored). The ancilla hypothesis `hZ` is taken for API uniformity with the other
headlines; `B`-preservation does not actually consume it. -/
theorem cuccaroAdd_preserves_B (L : CuccaroLayout m n) (s : State m) (hZ : s L.Z = false) :
    ∀ k, k < n → denote (cuccaroAdd L) s (L.B k) = s (L.B k) := by
  obtain ⟨-, hP2, -, -⟩ :=
    cuccaroRec_correct L n 0 L.Z s (by omega)
      (fun i _ => by simpa using (L.hAZ i).symm)
      (fun i _ => by simpa using (L.hBZ i).symm)
  intro k hk
  have := hP2 k hk
  simpa using this

/-- **The carry-clean property.** The ancilla `Z` returns to `false`: the Cuccaro adder borrows the
low-carry wire clean and returns it clean, so it is reusable in place with no fresh ancilla. This is
what distinguishes it from `rippleCirc` / `cRippleCirc` (which leave the top carry dirty). -/
theorem cuccaroAdd_ancilla_clean (L : CuccaroLayout m n) (s : State m) (hZ : s L.Z = false) :
    denote (cuccaroAdd L) s L.Z = false := by
  obtain ⟨-, -, hP3, -⟩ :=
    cuccaroRec_correct L n 0 L.Z s (by omega)
      (fun i _ => by simpa using (L.hAZ i).symm)
      (fun i _ => by simpa using (L.hBZ i).symm)
  rw [cuccaroAdd, hP3, hZ]

/-! ### Derived cost: 2n Toffolis -/

theorem cuccaroRec_toffoli (L : CuccaroLayout m n) (carry : Fin m) (start len : ℕ) :
    (circuitCost (cuccaroRec L carry start len)).toffoli = 2 * len := by
  induction len generalizing start carry with
  | zero => simp [cuccaroRec, circuitCost]
  | succ len ih =>
    have hsplit : cuccaroRec L carry start (len + 1)
        = maj carry (L.A start) (L.B start)
          ++ cuccaroRec L (L.B start) (start + 1) len
          ++ uma carry (L.A start) (L.B start) := rfl
    rw [hsplit, cost_comp_toffoli_count, cost_comp_toffoli_count, maj_toffoli, uma_toffoli,
      ih (L.B start) (start + 1)]
    omega

/-- **Derived Toffoli cost: `2n`.** `n` `maj` blocks + `n` `uma` blocks, each exactly one `CCX`; the
`CX`s are CNOTs (zero Toffoli). The honest in-place carry-clean overhead — half the `~30n²`-per-multiply
fresh-ancilla cost the corpus adders carried. -/
theorem cuccaroAdd_toffoli (L : CuccaroLayout m n) :
    (circuitCost (cuccaroAdd L)).toffoli = 2 * n := by
  rw [cuccaroAdd, cuccaroRec_toffoli]

/-! ### Non-vacuity witness + `#eval` / `decide` cross-check

A concrete 3-bit layout on `Fin 7` (`A → {0,1,2}`, `B → {3,4,5}`, `Z → 6`). The headline applies, and
the strict `Array` evaluator `runArr` (with the proven bridge `regValRangeArr_eq` back to `denote`)
witnesses `5 + 6 mod 8 = 3`, the ancilla returning `false`, and `B` intact. -/

/-- A concrete 3-bit Cuccaro layout on `Fin 7`. -/
def cuccaroLayout3 : CuccaroLayout 7 3 where
  A i := if i = 0 then 0 else if i = 1 then 1 else 2
  B i := if i = 0 then 3 else if i = 1 then 4 else 5
  Z := 6
  hAB i j := by split_ifs <;> decide
  hAZ i := by split_ifs <;> decide
  hBZ i := by split_ifs <;> decide
  hAinj i j hi hj h := by split_ifs at h <;> omega
  hBinj i j hi hj h := by split_ifs at h <;> omega

/-- The headline is non-vacuous: it applies to `cuccaroLayout3`. -/
example (s : State 7) (hZ : s cuccaroLayout3.Z = false) :
    regValRange cuccaroLayout3.A (denote (cuccaroAdd cuccaroLayout3) s) 3
      = (regValRange cuccaroLayout3.A s 3 + regValRange cuccaroLayout3.B s 3) % 2 ^ 3 :=
  cuccaroAdd_correct cuccaroLayout3 s hZ

/-- Witness state: `A = 5` (wires `0,1,2 = 1,0,1`), `B = 6` (wires `3,4,5 = 0,1,1`), `Z = 6 = false`. -/
def cuccaroWitness3 : State 7 := ![true, false, true, false, true, true, false]

-- `A ← 5 + 6 mod 8 = 3`. Fast `Array`-backed run, read off register `A` (low 3 bits). Prints `3`.
#eval regValRangeArr cuccaroLayout3.A
  (runArr (cuccaroAdd cuccaroLayout3) (ofState cuccaroWitness3)) 3
-- 3

-- `B` intact: reads `6`.
#eval regValRangeArr cuccaroLayout3.B
  (runArr (cuccaroAdd cuccaroLayout3) (ofState cuccaroWitness3)) 3
-- 6

-- ancilla clean: reads `false`.
#eval (runArr (cuccaroAdd cuccaroLayout3) (ofState cuccaroWitness3))[cuccaroLayout3.Z.val]!
-- false

-- Green, fast, theorem-independent value check: the `Array`-backed register read is `3`, by `decide`
-- (kernel-reduced; the strict `Array` evaluator avoids the lazy `Function.update` blowup of `denote`).
set_option maxRecDepth 4000 in
example : regValRangeArr cuccaroLayout3.A
    (runArr (cuccaroAdd cuccaroLayout3) (ofState cuccaroWitness3)) 3 = 3 := by
  decide

-- The cross-check is faithful to the real `denote`-based theorem: by `regValRangeArr_eq`, the fast
-- `Array` value (`3`) *is* the `regValRange (denote …)` quantity `cuccaroAdd_correct` constrains.
example : regValRangeArr cuccaroLayout3.A
    (runArr (cuccaroAdd cuccaroLayout3) (ofState cuccaroWitness3)) 3
      = regValRange cuccaroLayout3.A (denote (cuccaroAdd cuccaroLayout3) cuccaroWitness3) 3 :=
  regValRangeArr_eq cuccaroLayout3.A (cuccaroAdd cuccaroLayout3) cuccaroWitness3 3

end Reversible
