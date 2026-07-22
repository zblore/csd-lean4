/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModAdd

/-!
# Reversible controlled addition — the quantum×quantum primitive  (ECDLP Phase 2, Stage S2)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The Tranche-3 multiplier (`ModMul.lean`) is **quantum×classical**: it multiplies a *classical constant*
`a = ∑ 2^sh` (fixed shifts) by the quantum register `Y`. Squaring `Y²` and, more importantly, the field
multiplications inside an elliptic-curve point operation are **quantum×quantum** (both factors are
registers): bit `i` of one factor must *control* whether the other, shifted, is added. That needs a
**controlled adder**, the primitive built here.

The obstacle: a control-wire-`ctrl`ed full adder needs `ctrl` ANDed with the adder's two inputs — i.e.
3-control gates — while the DSL tops out at `CCX` (2 controls). We use the standard clean-ancilla
decomposition `CCCX ctrl x y z = [CCX ctrl x anc, CCX anc y z, CCX ctrl x anc]` (`anc` init `false`,
restored to `false`), so one shared ancilla suffices and the controlled full adder stays inside the
2-control DSL.

## What is proved here (Stage S2.1 — the gadget)

* `cfullAdder` — the controlled full adder on `(ctrl, a, b, cin, cout, anc)` (with `cout`, `anc`
  initialised `false`), eight `CCX` gates: each gate of `fullAdder` controlled on `ctrl` via the
  ancilla decomposition.
* `cfullAdder_correct` — **full all-inputs correctness** (`decide` over `State 6`): when `ctrl` is set
  it computes the full-adder sum/carry (`b ← a⊕b⊕cin`, `cout ← majority`, `a`/`cin` preserved); when
  `ctrl` is clear it is the **identity**; either way `anc` is restored to `false`.
* `cfullAdder_cost` — derived `toffoli = 8`, everything else `0`: a controlled add is `4×` the
  uncontrolled full adder's two Toffolis, plus one ancilla. The honest quantum×quantum overhead.
-/

namespace Reversible

variable {n : ℕ}

/-- The controlled full adder on wires `ctrl a b cin cout anc` (with `cout`, `anc` initialised `false`):
when `ctrl` is set it acts as `fullAdder a b cin cout`; when `ctrl` is clear it is the identity. Each
of `fullAdder`'s four gates is controlled on `ctrl`: the two `CCX`s become 3-control gates realised by
the clean-ancilla decomposition `CCX ctrl · anc ; CCX anc · cout ; CCX ctrl · anc`, and the two `CX`s
become `CCX ctrl · ·`. Eight `CCX`s; `anc` is borrowed clean and returned clean. -/
def cfullAdder (ctrl a b cin cout anc : Fin n) : Circuit n :=
  [ .CCX ctrl a anc, .CCX anc b cout, .CCX ctrl a anc,   -- CCCX ctrl a b cout
    .CCX ctrl a b,                                        -- controlled (CX a b)
    .CCX ctrl cin anc, .CCX anc b cout, .CCX ctrl cin anc, -- CCCX ctrl cin b cout
    .CCX ctrl cin b ]                                     -- controlled (CX cin b)

/-- **Controlled-full-adder correctness — genuine all-inputs coverage.** On the concrete `State 6`
layout (wires `0..5 = ctrl, a, b, cin, cout, anc`), with `cout` and `anc` initialised `false`: if
`ctrl` (wire `0`) is set the gadget computes the sum bit on `b` (wire `2`), the carry-out on `cout`
(wire `4`), and preserves `a`, `cin`; if `ctrl` is clear it preserves `b` and leaves `cout` `false`;
the ancilla (wire `5`) is restored to `false` in both cases. Proved by `decide` over `State 6` (the
`2^6` inputs with `cout`, `anc` fixed `false`). -/
theorem cfullAdder_correct :
    ∀ s : State 6, s 4 = false → s 5 = false →
      (denote (cfullAdder 0 1 2 3 4 5) s 2 = if s 0 then (s 1 ^^ s 2 ^^ s 3) else s 2)
        ∧ (denote (cfullAdder 0 1 2 3 4 5) s 4 = if s 0 then majority (s 1) (s 2) (s 3) else false)
        ∧ (denote (cfullAdder 0 1 2 3 4 5) s 5 = false)
        ∧ (denote (cfullAdder 0 1 2 3 4 5) s 0 = s 0)
        ∧ (denote (cfullAdder 0 1 2 3 4 5) s 1 = s 1)
        ∧ (denote (cfullAdder 0 1 2 3 4 5) s 3 = s 3) := by
  decide

/-- **Derived Toffoli cost of the controlled full adder** (from the gate list, via `circuitCost`):
eight Toffolis. Read off the eight `CCX`s. The uncontrolled `fullAdder` is `2` Toffolis `+ 2` CNOTs; the
controlled gadget is `8` Toffolis `+ 0` CNOTs (`cfullAdder_cnot`) — the two `CX`s are promoted to
`CCX ctrl · ·` (absorbing the CNOTs into Toffolis) and the two `CCX`s expand to ancilla-mediated `CCCX`.
Plus one designated clean ancilla wire (not billed by `gateCost`). The honest quantum×quantum overhead. -/
theorem cfullAdder_cost (ctrl a b cin cout anc : Fin n) :
    (circuitCost (cfullAdder ctrl a b cin cout anc)).toffoli = 8 := by
  simp [circuitCost, cfullAdder, gateCost]

/-- The controlled full adder uses **no CNOTs** (`cnot = 0`): every gate is a `CCX`, the two `CX`s of
the uncontrolled `fullAdder` having been promoted to controlled `CCX`s. Derived from the gate list. -/
theorem cfullAdder_cnot (ctrl a b cin cout anc : Fin n) :
    (circuitCost (cfullAdder ctrl a b cin cout anc)).cnot = 0 := by
  simp [circuitCost, cfullAdder, gateCost]

/-- **Frame lemma for the controlled gadget.** A wire distinct from all six of `ctrl, a, b, cin, cout,
anc` is untouched by `cfullAdder` (every gate's wires lie in that set). Lets the controlled carry-chain
lift the gadget over a register. -/
theorem cfullAdder_apply_of_ne {ctrl a b cin cout anc w : Fin n}
    (hctrl : w ≠ ctrl) (ha : w ≠ a) (hb : w ≠ b) (hcin : w ≠ cin) (hcout : w ≠ cout)
    (hanc : w ≠ anc) (s : State n) :
    denote (cfullAdder ctrl a b cin cout anc) s w = s w := by
  apply denote_apply_of_forall_not_mem
  intro g hg
  simp only [cfullAdder, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [gateWires]

-- Budget note: under the Lean v4.33 toolchain the pre-upgrade proof (one `simp only` chain building
-- the full `Function.update` gate-read term, then a 4-wire `cases` generalising over that large term)
-- hit a `(deterministic) timeout at isDefEq` even at 2000000 heartbeats — 4.33's `isDefEq`/`simp` is
-- far slower for this shape. Restructured: the four Boolean wire values are cased FIRST (recording
-- `s ctrl = …` etc.), so each of the 16 branches unfolds `denote` on concrete Booleans and the
-- intermediate term never grows; the read-out `Function.update` chain then resolves per-branch via
-- `update_apply` + the distinctness hyps, and each leaf closes by Boolean computation. The proof now
-- fits within the *default* 200000 heartbeats; the modest explicit budget below is kept only as
-- CI-machine-variance headroom.
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
/-- **Controlled-full-adder correctness, general `Fin n` wires.** For pairwise-distinct wires
`ctrl, a, b, cin, cout, anc` with `cout` and `anc` initialised `false`: when `ctrl` is set the gadget
writes the sum bit to `b`, the carry-out to `cout`, and preserves `a`, `cin`; when `ctrl` is clear it
preserves `b` and leaves `cout` `false`; the ancilla `anc` is restored to `false` in both cases. This
is the slice the controlled ripple carry-chain iterates. -/
theorem cfullAdder_correct_general {ctrl a b cin cout anc : Fin n}
    (hctrla : ctrl ≠ a) (hctrlb : ctrl ≠ b) (hctrlcin : ctrl ≠ cin) (hctrlcout : ctrl ≠ cout)
    (hctrlanc : ctrl ≠ anc) (hab : a ≠ b) (hacin : a ≠ cin) (hacout : a ≠ cout) (haanc : a ≠ anc)
    (hbcin : b ≠ cin) (hbcout : b ≠ cout) (hbanc : b ≠ anc) (hcincout : cin ≠ cout)
    (hcinanc : cin ≠ anc) (hcoutanc : cout ≠ anc) {s : State n}
    (hcout : s cout = false) (hanc : s anc = false) :
    (denote (cfullAdder ctrl a b cin cout anc) s b
        = if s ctrl then (s a ^^ s b ^^ s cin) else s b)
      ∧ (denote (cfullAdder ctrl a b cin cout anc) s cout
        = if s ctrl then majority (s a) (s b) (s cin) else false)
      ∧ (denote (cfullAdder ctrl a b cin cout anc) s anc = false)
      ∧ (denote (cfullAdder ctrl a b cin cout anc) s a = s a)
      ∧ (denote (cfullAdder ctrl a b cin cout anc) s cin = s cin)
      ∧ (denote (cfullAdder ctrl a b cin cout anc) s ctrl = s ctrl) := by
  cases hsctrl : s ctrl <;> cases hsa : s a <;> cases hsb : s b <;> cases hscin : s cin <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [cfullAdder, denote_cons, denote_nil, denoteGate,
      Function.update_apply, hcout, hanc, hsctrl, hsa, hsb, hscin,
      hctrla, hctrlb, hctrlcin, hctrlcout, hctrlanc, hab, hacin, hacout, haanc, hbcin, hbcout,
      hbanc, hcincout, hcinanc, hcoutanc, hctrla.symm, hctrlb.symm, hctrlcin.symm, hctrlcout.symm,
      hctrlanc.symm, hab.symm, hacin.symm, hacout.symm, haanc.symm, hbcin.symm, hbcout.symm,
      hbanc.symm, hcincout.symm, hcinanc.symm, hcoutanc.symm, majority,
      eq_self_iff_true, or_self, or_false, false_or, if_true, if_false,
      Bool.xor_false, Bool.xor_true, Bool.and_false, Bool.and_true, Bool.or_false, Bool.or_true,
      Bool.not_true, Bool.not_false, Bool.false_eq_true]

/-! ### The controlled ripple adder (general `n`): correctness

A `CRippleLayout` is a `RippleLayout` (registers `A`, `B`, carry chain `C`) plus a control wire `ctrl`
and a shared clean ancilla `anc`, both disjoint from the registers. The controlled ripple adder is one
`cfullAdder` per slice, all sharing `ctrl` and `anc`. The headline: it leaves register `B` holding
`(A + B) mod 2^n` when `ctrl` is set, and `B` unchanged when `ctrl` is clear. -/

/-- A controlled ripple-adder layout: a `RippleLayout` plus a control wire and a shared ancilla,
both disjoint from registers `A`, `B` and the carry chain `C`. -/
structure CRippleLayout (m n : ℕ) extends RippleLayout m n where
  /-- The control wire (set ⇒ add, clear ⇒ identity). -/
  ctrl : Fin m
  /-- The shared clean ancilla for the `CCCX` decomposition (borrowed and returned `false`). -/
  anc : Fin m
  hctrlA : ∀ i, ctrl ≠ A i
  hctrlB : ∀ i, ctrl ≠ B i
  hctrlC : ∀ i, ctrl ≠ C i
  hctrlanc : ctrl ≠ anc
  hancA : ∀ i, anc ≠ A i
  hancB : ∀ i, anc ≠ B i
  hancC : ∀ i, anc ≠ C i

variable {m : ℕ}

/-- One controlled ripple slice: a controlled full adder on `(A i, B i, C i, C (i+1))` with the shared
control and ancilla. -/
def cRippleSlice (L : CRippleLayout m n) (i : ℕ) : Circuit m :=
  cfullAdder L.ctrl (L.A i) (L.B i) (L.C i) (L.C (i + 1)) L.anc

/-- The circuit of the first `k` controlled slices. -/
def cRipplePrefix (L : CRippleLayout m n) (k : ℕ) : Circuit m :=
  (List.range k).flatMap (cRippleSlice L)

/-- The full controlled ripple adder: all `n` slices. -/
def cRippleCirc (L : CRippleLayout m n) : Circuit m := cRipplePrefix L n

theorem denote_cRipplePrefix_succ (L : CRippleLayout m n) (k : ℕ) (s : State m) :
    denote (cRipplePrefix L (k + 1)) s
      = denote (cRippleSlice L k) (denote (cRipplePrefix L k) s) := by
  simp only [cRipplePrefix, List.range_succ, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, denote_append]

/-- **The controlled carry-chain invariant.** After the first `k` slices: `B`'s low `k` bits plus the
carry into bit `k` equal `(if ctrl then A else 0) + B` over the low `k` bits (P1 — unified: `ctrl` clear
⇒ added value `0`, carry stays `false`, `B` unchanged; `ctrl` set ⇒ the ripple sum); `A` untouched (P2);
high `B` (P4) and high carries (P5) preserved; ancilla restored to `false` (P6); the control bit
preserved (P0c); and — the clause that closes the `ctrl`-clear case — the working carry stays `false`
when `ctrl` is clear (P7). By induction on `k`, lifting `cfullAdder_correct_general` through
`cfullAdder_apply_of_ne`. -/
theorem cRippleCirc_invariant (L : CRippleLayout m n) (s : State m)
    (hC0 : ∀ j, s (L.C j) = false) (hanc0 : s L.anc = false) :
    ∀ k, k ≤ n →
      (regValRange L.B (denote (cRipplePrefix L k) s) k
          + (denote (cRipplePrefix L k) s (L.C k)).toNat * 2 ^ k
        = (if s L.ctrl then regValRange L.A s k else 0) + regValRange L.B s k)
      ∧ (∀ j, j < n → denote (cRipplePrefix L k) s (L.A j) = s (L.A j))
      ∧ (∀ j, k ≤ j → j < n → denote (cRipplePrefix L k) s (L.B j) = s (L.B j))
      ∧ (∀ j, k < j → j < n + 1 → denote (cRipplePrefix L k) s (L.C j) = s (L.C j))
      ∧ (denote (cRipplePrefix L k) s L.anc = false)
      ∧ (denote (cRipplePrefix L k) s L.ctrl = s L.ctrl)
      ∧ (s L.ctrl = false → denote (cRipplePrefix L k) s (L.C k) = false) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [cRipplePrefix, regValRange, hC0]
    · intro j _; simp [cRipplePrefix]
    · intro j _ _; simp [cRipplePrefix]
    · intro j _ _; simp [cRipplePrefix]
    · simp [cRipplePrefix, hanc0]
    · simp [cRipplePrefix]
    · intro _; simp [cRipplePrefix, hC0]
  | succ k ih =>
    intro hk
    have hkn : k ≤ n := Nat.le_of_succ_le hk
    have hkltn : k < n := hk
    obtain ⟨hP1, hP2, hP4, hP5, hP6, hP0, hP7⟩ := ih hkn
    -- distinctness for this slice's wires (ctrl, A k, B k, C k, C (k+1), anc)
    have hctrlAk : L.ctrl ≠ L.A k := L.hctrlA k
    have hctrlBk : L.ctrl ≠ L.B k := L.hctrlB k
    have hctrlCk : L.ctrl ≠ L.C k := L.hctrlC k
    have hctrlCk1 : L.ctrl ≠ L.C (k + 1) := L.hctrlC (k + 1)
    have hAkBk : L.A k ≠ L.B k := L.hAB k k
    have hAkCk : L.A k ≠ L.C k := L.hAC k k
    have hAkCk1 : L.A k ≠ L.C (k + 1) := L.hAC k (k + 1)
    have hAkanc : L.A k ≠ L.anc := (L.hancA k).symm
    have hBkCk : L.B k ≠ L.C k := L.hBC k k
    have hBkCk1 : L.B k ≠ L.C (k + 1) := L.hBC k (k + 1)
    have hBkanc : L.B k ≠ L.anc := (L.hancB k).symm
    have hCkCk1 : L.C k ≠ L.C (k + 1) := by
      intro h; exact (Nat.succ_ne_self k) (L.hCinj (k + 1) k (by omega) (by omega) h.symm)
    have hCkanc : L.C k ≠ L.anc := (L.hancC k).symm
    have hCk1anc : L.C (k + 1) ≠ L.anc := (L.hancC (k + 1)).symm
    have hc0' : denote (cRipplePrefix L k) s (L.C (k + 1)) = false := by
      rw [hP5 (k + 1) (by omega) (by omega)]; exact hC0 (k + 1)
    obtain ⟨hsum, hcarry, hancres, hAk, hCk, hctrlk⟩ :=
      cfullAdder_correct_general hctrlAk hctrlBk hctrlCk hctrlCk1 L.hctrlanc hAkBk hAkCk hAkCk1
        hAkanc hBkCk hBkCk1 hBkanc hCkCk1 hCkanc hCk1anc hc0' hP6
    simp only [denote_cRipplePrefix_succ, cRippleSlice]
    set sk := denote (cRipplePrefix L k) s with hskdef
    -- ctrl is constant across slices: sk ctrl = s ctrl
    rw [hP0] at hsum hcarry
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- P1: the controlled carry-chain arithmetic
      have hBklow : regValRange L.B (denote (cfullAdder L.ctrl (L.A k) (L.B k) (L.C k)
            (L.C (k + 1)) L.anc) sk) k = regValRange L.B sk k := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        rw [cfullAdder_apply_of_ne (L.hctrlB j).symm ((L.hAB k j).symm)
          (fun h => (show j ≠ k by omega) (L.hBinj j k (by omega) hkltn h))
          (L.hBC j k) (L.hBC j (k + 1)) (L.hancB j).symm sk]
      rw [regValRange_succ, hBklow, hsum, hcarry, regValRange_succ, regValRange_succ,
          hP2 k hkltn, hP4 k (Nat.le_refl k) hkltn, pow_succ]
      cases hc : s L.ctrl with
      | true =>
        -- ctrl set: the standard ripple-sum step
        simp only [hc, if_true] at hP1 ⊢
        have hfn := fulladder_nat (s (L.A k)) (s (L.B k)) (sk (L.C k))
        cases h1 : s (L.A k) <;> cases h2 : s (L.B k) <;> cases h3 : sk (L.C k) <;>
          simp only [h1, h2, h3, majority, Bool.xor_false, Bool.xor_true, Bool.not_true,
            Bool.not_false, Bool.and_self, Bool.and_true, Bool.and_false, Bool.or_true,
            Bool.or_false, Bool.or_self, Bool.toNat_true, Bool.toNat_false, zero_mul, one_mul,
            mul_zero, add_zero, zero_add] at hP1 hfn ⊢ <;>
          omega
      | false =>
        -- ctrl clear: the added value is 0 and the carry was false, so B is unchanged
        have hckf : sk (L.C k) = false := hP7 hc
        simp only [hc, Bool.false_eq_true, if_false, hckf, Bool.toNat_false, zero_mul,
          add_zero] at hP1 ⊢
        omega
    · -- P2: A untouched
      intro j hj
      by_cases hjk : j = k
      · subst hjk; rw [hAk]; exact hP2 j hj
      · rw [cfullAdder_apply_of_ne (L.hctrlA j).symm
          (fun h => hjk (L.hAinj j k hj hkltn h)) (L.hAB j k) (L.hAC j k) (L.hAC j (k + 1))
          (L.hancA j).symm sk]
        exact hP2 j hj
    · -- P4: high bits of B preserved
      intro j hjk hjn
      rw [cfullAdder_apply_of_ne (L.hctrlB j).symm ((L.hAB k j).symm)
        (fun h => (show j ≠ k by omega) (L.hBinj j k hjn hkltn h))
        (L.hBC j k) (L.hBC j (k + 1)) (L.hancB j).symm sk]
      exact hP4 j (by omega) hjn
    · -- P5: high carries preserved
      intro j hjk hjn
      rw [cfullAdder_apply_of_ne (L.hctrlC j).symm ((L.hAC k j).symm) ((L.hBC k j).symm)
        (fun h => (show j ≠ k by omega) (L.hCinj j k hjn (by omega) h))
        (fun h => (show j ≠ k + 1 by omega) (L.hCinj j (k + 1) hjn (by omega) h))
        (L.hancC j).symm sk]
      exact hP5 j (by omega) hjn
    · -- P6: ancilla restored
      exact hancres
    · -- P0: control preserved
      rw [hctrlk]; exact hP0
    · -- P7: carry stays false when ctrl clear
      intro hcf
      rw [hcarry, hcf]; simp

/-- **Controlled ripple-adder correctness (the S2 headline).** For a disjoint-wire layout with all
carries and the ancilla initialised `false`, the controlled ripple adder leaves register `B` holding
`(A + B) mod 2^n` when the control wire `ctrl` is set, and `B` **unchanged** when `ctrl` is clear. The
quantum×quantum-ready conditional add, derived from the exhibited circuit `cRippleCirc`. -/
theorem cRippleCirc_correct (L : CRippleLayout m n) (s : State m)
    (hC0 : ∀ j, s (L.C j) = false) (hanc0 : s L.anc = false) :
    regValRange L.B (denote (cRippleCirc L) s) n
      = if s L.ctrl then (regValRange L.A s n + regValRange L.B s n) % 2 ^ n
        else regValRange L.B s n := by
  obtain ⟨hP1, -, -, -, -, -, hP7⟩ := cRippleCirc_invariant L s hC0 hanc0 n (Nat.le_refl n)
  rw [cRippleCirc]
  have hlt : regValRange L.B (denote (cRipplePrefix L n) s) n < 2 ^ n := regValRange_lt _ _ _
  cases hc : s L.ctrl with
  | true =>
    simp only [hc, if_true] at hP1 ⊢
    cases h : denote (cRipplePrefix L n) s (L.C n)
    · simp only [h, Bool.toNat_false, zero_mul, add_zero] at hP1
      rw [← hP1, Nat.mod_eq_of_lt hlt]
    · simp only [h, Bool.toNat_true, one_mul] at hP1
      rw [hP1.symm, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
  | false =>
    have hcnf : denote (cRipplePrefix L n) s (L.C n) = false := hP7 hc
    simp only [hc, Bool.false_eq_true, if_false, hcnf, Bool.toNat_false, zero_mul,
      add_zero, zero_add] at hP1 ⊢
    exact hP1

/-- **Derived cost of the controlled ripple adder**: `8n` Toffolis (eight per slice, `cfullAdder_cost`),
composed through the Tranche-1 `cost_comp_toffoli_count` — `4×` the uncontrolled ripple adder's `2n`,
the honest quantum×quantum overhead. -/
theorem cRippleCirc_toffoli (L : CRippleLayout m n) :
    (circuitCost (cRippleCirc L)).toffoli = 8 * n := by
  rw [cRippleCirc, cRipplePrefix]
  suffices h : ∀ k, (circuitCost ((List.range k).flatMap (cRippleSlice L))).toffoli = 8 * k from h n
  intro k
  induction k with
  | zero => simp [circuitCost]
  | succ k ih =>
    have hsplit : (List.range (k + 1)).flatMap (cRippleSlice L)
        = (List.range k).flatMap (cRippleSlice L) ++ cRippleSlice L k := by
      rw [List.range_succ, List.flatMap_append]; simp
    rw [hsplit, cost_comp_toffoli_count, ih, cRippleSlice, cfullAdder_cost]
    omega

/-- **The shared ancilla is returned clean.** After the whole controlled ripple adder the ancilla is
`false` again (it is borrowed and restored within each slice). The hygiene fact a multi-step consumer
needs to reuse the ancilla between successive controlled adds. -/
theorem cRippleCirc_anc_restored (L : CRippleLayout m n) (s : State m)
    (hC0 : ∀ j, s (L.C j) = false) (hanc0 : s L.anc = false) :
    denote (cRippleCirc L) s L.anc = false := by
  obtain ⟨-, -, -, -, h, -, -⟩ := cRippleCirc_invariant L s hC0 hanc0 n (Nat.le_refl n)
  rw [cRippleCirc]; exact h

/-- **The control wire is preserved** by the controlled ripple adder (it is read, never written). The
consumer needs this to keep each partial-product's control bit equal to the original register bit across
the accumulation loop. -/
theorem cRippleCirc_ctrl_preserved (L : CRippleLayout m n) (s : State m)
    (hC0 : ∀ j, s (L.C j) = false) (hanc0 : s L.anc = false) :
    denote (cRippleCirc L) s L.ctrl = s L.ctrl := by
  obtain ⟨-, -, -, -, -, h, -⟩ := cRippleCirc_invariant L s hC0 hanc0 n (Nat.le_refl n)
  rw [cRippleCirc]; exact h

/-- **The controlled ripple adder preserves any external wire** (distinct from `ctrl`, `anc`, and every
register/carry wire `A k`, `B k`, `C k`). The frame lemma at circuit granularity: every gate of
`cRippleCirc L` has wires among `{ctrl, anc} ∪ {A k, B k, C k}`. -/
theorem cRippleCirc_preserves_external (L : CRippleLayout m n) (s : State m) (x : Fin m)
    (hctrl : x ≠ L.ctrl) (hanc : x ≠ L.anc) (hA : ∀ k, k < n → x ≠ L.A k)
    (hB : ∀ k, k < n → x ≠ L.B k) (hC : ∀ k, k < n + 1 → x ≠ L.C k) :
    denote (cRippleCirc L) s x = s x := by
  apply denote_apply_of_forall_not_mem
  intro g hg
  rw [cRippleCirc, cRipplePrefix, List.mem_flatMap] at hg
  obtain ⟨k, hk, hgk⟩ := hg
  rw [List.mem_range] at hk
  simp only [cRippleSlice, cfullAdder, List.mem_cons, List.not_mem_nil, or_false] at hgk
  rcases hgk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [gateWires, hctrl, hanc, hA k hk, hB k hk, hC k (by omega), hC (k + 1) (by omega)]

/-! ### Non-vacuity witness

A concrete 2-bit controlled ripple layout on `Fin 9` (registers `A → {0,1}`, `B → {2,3}`, carry chain
`C → {4,5,6}`, control `7`, ancilla `8`), exhibiting that `CRippleLayout` is inhabited and the headline
applies. -/

/-- A concrete 2-bit controlled adder layout on `Fin 9`. -/
def cRippleLayout2 : CRippleLayout 9 2 where
  A i := if i = 0 then 0 else 1
  B i := if i = 0 then 2 else 3
  C i := if i = 0 then 4 else if i = 1 then 5 else 6
  ctrl := 7
  anc := 8
  hAB i j := by split_ifs <;> decide
  hAC i j := by split_ifs <;> decide
  hBC i j := by split_ifs <;> decide
  hAinj i j hi hj h := by split_ifs at h with h1 h2 h2 <;> omega
  hBinj i j hi hj h := by split_ifs at h with h1 h2 h2 <;> omega
  hCinj i j hi hj h := by split_ifs at h <;> omega
  hctrlA i := by split_ifs <;> decide
  hctrlB i := by split_ifs <;> decide
  hctrlC i := by split_ifs <;> decide
  hctrlanc := by decide
  hancA i := by split_ifs <;> decide
  hancB i := by split_ifs <;> decide
  hancC i := by split_ifs <;> decide

/-- The S2 headline is non-vacuous: it applies to the concrete `cRippleLayout2`. -/
example (s : State 9) (hC0 : ∀ j, s (cRippleLayout2.C j) = false)
    (hanc0 : s cRippleLayout2.anc = false) :
    regValRange cRippleLayout2.B (denote (cRippleCirc cRippleLayout2) s) 2
      = if s cRippleLayout2.ctrl then
          (regValRange cRippleLayout2.A s 2 + regValRange cRippleLayout2.B s 2) % 2 ^ 2
        else regValRange cRippleLayout2.B s 2 :=
  cRippleCirc_correct cRippleLayout2 s hC0 hanc0

end Reversible
