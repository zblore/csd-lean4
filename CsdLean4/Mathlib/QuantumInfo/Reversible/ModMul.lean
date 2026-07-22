/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModAdd
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Reversible modular multiplication — semantic target + shift-and-add multiplier cost  (ECDLP Tranche 3, Stage A)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The multiplication layer of the reversible-circuit substrate
(`Circuit.lean` / `Cost.lean` / `ModAdd.lean`, `specs/ecdlp-resource-plan.md`). The semantic target is
**Shor's modular-multiplication oracle** `mulOracle : |y⟩ ↦ |a·y⟩` on `ZMod N` (a permutation when `a`
is a unit), which the corpus's `Empirical/QM/Algorithms/ShorCore.lean` carries with no gate-level
content. This tranche builds the missing reversible circuit + *derived* cost.

## What is proved here (Stage A)

* `mulConst` — the semantic target: the `ZMod N` map `y ↦ a · y`, with `mulConst_bijective` (a unit
  acts as a permutation — the reversibility that lets a circuit realise it).
* `multiplier` — the shift-and-add multiplier as the concatenation of a list of partial-product adder
  circuits, with **derived cost** `multiplier_toffoli` / `_cnot` (the total count is the list-sum of the
  block counts, composed through the Tranche-1 `cost_comp_*` lemmas — not annotated).
* `rippleCirc_toffoli` / `_cnot` — a ripple adder block costs `2 * n` Toffolis / CNOTs (derived), so a
  multiplier built from `m` width-`n` adders costs `2 * n * m` (`multiplier_ripple_toffoli`).
* The per-partial-product correctness is `ModAdd.rippleCirc_correct` (one shifted add); the building
  block is in hand.

## Stage B.1 — the per-step accumulation correctness (landed below)

* `regValRange_split` — split a register readout at an offset (`low + 2^i · window`), the tool relating
  a windowed add to the full accumulator value with no division.
* `rippleCirc_preserves_external` — a ripple circuit preserves any wire disjoint from its layout (the
  frame lemma at circuit granularity).
* `accStep` — **THE per-step heart**: one full-remaining-width ripple add of the multiplicand (value
  `Yv`) into the accumulator window `Acc[i, W)` increases the full accumulator value by exactly
  `2^i · Yv` (carry propagating through the whole upper accumulator; low `i` bits preserved; no overflow).

## Stage B.2 — the fold to `Acc = a · Y` (landed below)

* `MulLayout` — the multi-register wire geometry (accumulator, multiplicand with high bits held zero,
  per-shift carry chains; bounded injectivity/disjointness, so it is inhabitable — see `mulLayout1`).
* `mulCircuit` — the shift-and-add multiplier: one partial-product ripple add per shift in `shifts`.
* `mulCircuit_correct` — **THE headline**: the multiplier leaves the accumulator holding
  `Acc + (∑ sh ∈ shifts, 2^sh) · Y`, by folding `accStep` over the shifts (an induction threading
  `Y`-preservation via `stepLayout_preserves_Y` and carry-freshness via `stepLayout_preserves_carry`;
  each step at its own width `W - sh`, applied individually so there is no dependent-width fold). With
  `Acc` initialised `0` and `∑ 2^sh = a` (the set bits of the classical constant), this is `Acc = a · Y`.
* `mulLayout1` + the closing `example` — a concrete `Fin 6` witness, so the headline is non-vacuous.

## Stage B.3 — the modular (`ZMod N`) capstone (landed below)

* `mulCircuit_correct_zmod` — connects the exact integer product to the semantic target: the output
  register, read in `ZMod N`, is `mulConst N (∑ 2^sh) Y` (Shor's `mulOracle` action `y ↦ a·y mod N`).
  The `ZMod N` cast performs the reduction (no `N = 2^W` assumption); the no-overflow hypothesis keeps
  the register exact. Honest residue: the register holds the exact integer `a·Y` — reducing it in place
  to a `bitlen N`-bit representative is a reversible conditional-subtract circuit (qubit optimisation),
  not built here.
-/

namespace Reversible

variable {m : ℕ}

/-! ### Semantic target: the `ZMod N` multiplication oracle -/

/-- The modular-multiplication oracle action: `y ↦ a · y` on `ZMod N`. This is the permutation Shor's
`mulOracle` realises (for `a` a unit); the circuit below is its reversible implementation. -/
def mulConst (N : ℕ) (a : ZMod N) : ZMod N → ZMod N := fun y => a * y

/-- For a unit `a`, `mulConst` is a bijection (the reversibility that admits a reversible circuit):
its inverse is multiplication by `a⁻¹`. -/
theorem mulConst_bijective {N : ℕ} {a : ZMod N} (ha : IsUnit a) :
    Function.Bijective (mulConst N a) := by
  obtain ⟨u, rfl⟩ := ha
  constructor
  · intro x y h
    simp only [mulConst] at h
    calc x = (↑u⁻¹ * ↑u) * x := by rw [Units.inv_mul, one_mul]
      _ = ↑u⁻¹ * (↑u * x) := by rw [mul_assoc]
      _ = ↑u⁻¹ * (↑u * y) := by rw [h]
      _ = (↑u⁻¹ * ↑u) * y := by rw [mul_assoc]
      _ = y := by rw [Units.inv_mul, one_mul]
  · intro y
    refine ⟨↑u⁻¹ * y, ?_⟩
    simp only [mulConst]
    rw [← mul_assoc, Units.mul_inv, one_mul]

/-! ### The shift-and-add multiplier circuit and its derived cost -/

/-- The shift-and-add multiplier: the concatenation of a list of partial-product adder circuits. Each
entry is the circuit that adds one shifted copy of the multiplicand into the accumulator; the multiplier
is their composition. (Which adders appear is fixed by the classical constant `a` — its set bits — so no
quantum control is needed; the gate list, hence the cost, is determined.) -/
def multiplier (adders : List (Circuit m)) : Circuit m := adders.flatMap id

@[simp] theorem multiplier_nil : multiplier ([] : List (Circuit m)) = [] := rfl

/-- **Multiplier Toffoli count is the sum of the block counts** (derived, composed through the
Tranche-1 `cost_comp_toffoli_count`). Not annotated — read off the concatenated gate list. -/
theorem multiplier_toffoli (adders : List (Circuit m)) :
    (circuitCost (multiplier adders)).toffoli
      = (adders.map (fun c => (circuitCost c).toffoli)).sum := by
  induction adders with
  | nil => simp
  | cons c rest ih =>
    have hsplit : multiplier (c :: rest) = c ++ multiplier rest := by
      simp [multiplier, List.flatMap_cons]
    rw [hsplit, cost_comp_toffoli_count, ih, List.map_cons, List.sum_cons]

/-- **Multiplier CNOT count is the sum of the block counts** (derived). -/
theorem multiplier_cnot (adders : List (Circuit m)) :
    (circuitCost (multiplier adders)).cnot
      = (adders.map (fun c => (circuitCost c).cnot)).sum := by
  induction adders with
  | nil => simp
  | cons c rest ih =>
    have hsplit : multiplier (c :: rest) = c ++ multiplier rest := by
      simp [multiplier, List.flatMap_cons]
    rw [hsplit, cost_comp_cnot_count, ih, List.map_cons, List.sum_cons]

/-- The first `k` slices of a ripple adder cost `2 * k` Toffolis (derived, induction on `k` composing
`cost_comp_toffoli_count` + `fullAdder_toffoli`). -/
theorem ripplePrefix_toffoli (L : RippleLayout m n) (k : ℕ) :
    (circuitCost (ripplePrefix L k)).toffoli = 2 * k := by
  induction k with
  | zero => simp [ripplePrefix]
  | succ k ih =>
    have hsplit : ripplePrefix L (k + 1) = ripplePrefix L k ++ rippleSlice L k := by
      simp [ripplePrefix, List.range_succ, List.flatMap_append]
    rw [hsplit, cost_comp_toffoli_count, ih]
    simp only [rippleSlice, fullAdder_toffoli]
    omega

/-- A ripple adder block (`n` slices) costs `2 * n` Toffolis (derived). -/
theorem rippleCirc_toffoli (L : RippleLayout m n) :
    (circuitCost (rippleCirc L)).toffoli = 2 * n := ripplePrefix_toffoli L n

/-- A multiplier built from `m'` width-`n` ripple-adder blocks costs `2 * n * m'` Toffolis (derived).
The count is independent of whether the layouts are *valid* (disjoint-wire) — cost is syntactic, so this
is a cost statement, not a correctness one; the multiplier's correctness is Stage B. -/
theorem multiplier_ripple_toffoli {n : ℕ} (Ls : List (RippleLayout m n)) :
    (circuitCost (multiplier (Ls.map rippleCirc))).toffoli = 2 * n * Ls.length := by
  rw [multiplier_toffoli, List.map_map]
  have hconst : Ls.map ((fun c => (circuitCost c).toffoli) ∘ rippleCirc)
      = Ls.map (fun _ => 2 * n) := by
    apply List.map_congr_left
    intro L _; simp [Function.comp, rippleCirc_toffoli]
  rw [hconst, List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_comm]

/-! ### Stage B: multiplication correctness — arithmetic tools -/

/-- **Split a register readout at an offset.** The low-`i` value plus `2^i` times the value of the
window starting at `i`. The key tool relating a windowed add to the full accumulator value (no
division). -/
theorem regValRange_split {m : ℕ} (f : ℕ → Fin m) (s : State m) (i k : ℕ) (h : i ≤ k) :
    regValRange f s k
      = regValRange f s i + 2 ^ i * regValRange (fun j => f (i + j)) s (k - i) := by
  simp only [regValRange]
  rw [← Finset.sum_range_add_sum_Ico (fun j => (s (f j)).toNat * 2 ^ j) h]
  congr 1
  rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [pow_add]
  exact mul_left_comm _ _ _

/-- **A ripple circuit preserves any wire external to its layout** (disjoint from all of `A`, `B`, `C`).
The frame lemma at circuit granularity, lifting `denote_apply_of_forall_not_mem`: every gate of
`rippleCirc L` has wires among `L.A`, `L.B`, `L.C`, so a wire avoiding all three is untouched. -/
theorem rippleCirc_preserves_external {w : ℕ} (L : RippleLayout m w) (s : State m) (x : Fin m)
    (hA : ∀ k, k < w → x ≠ L.A k) (hB : ∀ k, k < w → x ≠ L.B k)
    (hC : ∀ k, k < w + 1 → x ≠ L.C k) :
    denote (rippleCirc L) s x = s x := by
  apply denote_apply_of_forall_not_mem
  intro g hg
  rw [rippleCirc, ripplePrefix, List.mem_flatMap] at hg
  obtain ⟨k, hk, hgk⟩ := hg
  rw [List.mem_range] at hk
  simp only [rippleSlice, fullAdder, List.mem_cons, List.not_mem_nil, or_false] at hgk
  rcases hgk with rfl | rfl | rfl | rfl <;>
    simp [gateWires, hA k hk, hB k hk, hC k (by omega), hC (k + 1) (by omega)]

/-- **Single accumulation step.** One full-remaining-width ripple add of the multiplicand (value `Yv`,
read by `L.A`) into the accumulator window `Acc[i, W)` increases the full accumulator value by
`2^i · Yv` — provided the add does not overflow the window. The carry propagates through the whole
upper accumulator (width `w = W - i`), so nothing is dropped; the low `i` bits are preserved. -/
theorem accStep {w : ℕ} (L : RippleLayout m w) (Acc : ℕ → Fin m) (s : State m)
    (i W : ℕ) (hw : w = W - i) (hiW : i ≤ W)
    (hB : ∀ k, L.B k = Acc (i + k))
    (hAccinj : ∀ j k, j < W → k < W → Acc j = Acc k → j = k)
    (hAccA : ∀ j, j < i → ∀ k, Acc j ≠ L.A k)
    (hAccC : ∀ j, j < i → ∀ k, Acc j ≠ L.C k)
    (hcarry : ∀ j, s (L.C j) = false)
    (Yv : ℕ) (hYv : regValRange L.A s w = Yv)
    (hno : Yv + regValRange (fun k => Acc (i + k)) s w < 2 ^ w) :
    regValRange Acc (denote (rippleCirc L) s) W
      = regValRange Acc s W + 2 ^ i * Yv := by
  have hWi : W - i = w := hw.symm
  have hcorr := rippleCirc_correct L s hcarry
  have hBwin : L.B = fun k => Acc (i + k) := funext hB
  rw [hBwin, hYv, Nat.mod_eq_of_lt hno] at hcorr
  have hlow : regValRange Acc (denote (rippleCirc L) s) i = regValRange Acc s i := by
    simp only [regValRange]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [rippleCirc_preserves_external L s (Acc j) (fun k _ => hAccA j hj k) ?_
        (fun k _ => hAccC j hj k)]
    intro k hk
    rw [hB]
    exact fun h => absurd (hAccinj j (i + k) (by omega) (by omega) h) (by omega)
  rw [regValRange_split Acc (denote (rippleCirc L) s) i W hiW,
      regValRange_split Acc s i W hiW, hlow, hWi, hcorr]
  ring

/-! ### Stage B.2: the fold to `Acc = a · Y`

A `MulLayout` lays out, on `Fin M`, the accumulator `Acc` (W wires), the multiplicand `Y` (a W-wire
register whose high bits `[n, W)` are held zero, so no separate addend-pad wires are needed), and a
per-shift carry chain `Carry sh`. The multiplier is the concatenation, over a list of shifts (the set
bits of the classical constant `a`), of one full-window ripple add of `Y` into `Acc[sh, W)` per shift.
Folding `accStep` over the shifts gives `Acc ← Acc + (∑ 2^sh) · Y`. Each step has its own width
`W - sh`, but the steps are applied individually (the circuits are all `Circuit M`), so there is no
dependent-width fold. -/

/-- A multiplier layout on `Fin M`: accumulator `Acc`, multiplicand `Y` (high bits held zero), and a
per-shift carry chain `Carry`. The fields are pure wire geometry (disjointness + injectivity). -/
structure MulLayout (M n W : ℕ) where
  /-- Accumulator wires (indices `[0, W)`). -/
  Acc : ℕ → Fin M
  /-- Multiplicand wires (a `W`-wire register; values live in `[0, n)`, high bits held zero). -/
  Y : ℕ → Fin M
  /-- Carry chain for the partial-product add at shift `sh`. -/
  Carry : ℕ → ℕ → Fin M
  hYAcc : ∀ i j, Y i ≠ Acc j
  hYCarry : ∀ i sh j, Y i ≠ Carry sh j
  hAccCarry : ∀ i sh j, Acc i ≠ Carry sh j
  hCarryCross : ∀ sh sh' i j, sh ≤ W → sh' ≤ W → sh ≠ sh' → Carry sh i ≠ Carry sh' j
  hAccInj : ∀ i j, i < W → j < W → Acc i = Acc j → i = j
  hYInj : ∀ i j, i < W → j < W → Y i = Y j → i = j
  hCarryInj : ∀ sh i j, i ≤ W → j ≤ W → Carry sh i = Carry sh j → i = j

variable {n W : ℕ}

/-- The ripple-adder layout for the partial product at shift `sh`: add the multiplicand `Y` (the low
window) into the accumulator window `Acc[sh, W)` (width `W - sh`), with carry chain `Carry sh`. -/
def stepLayout (L : MulLayout m n W) (sh : ℕ) : RippleLayout m (W - sh) where
  A := L.Y
  B := fun k => L.Acc (sh + k)
  C := L.Carry sh
  hAB i j := L.hYAcc i (sh + j)
  hAC i j := L.hYCarry i sh j
  hBC i j := L.hAccCarry (sh + i) sh j
  hAinj i j hi hj h := L.hYInj i j (by omega) (by omega) h
  hBinj i j hi hj h := by have := L.hAccInj (sh + i) (sh + j) (by omega) (by omega) h; omega
  hCinj i j hi hj h := L.hCarryInj sh i j (by omega) (by omega) h

/-- The shift-and-add multiplier circuit: one partial-product ripple add per shift in `shifts`. -/
def mulCircuit (L : MulLayout m n W) (shifts : List ℕ) : Circuit m :=
  multiplier (shifts.map (fun sh => rippleCirc (stepLayout L sh)))

/-- A register readout over `[0, k)` equals its readout over `[0, n)` when bits `[n, k)` are zero. -/
theorem regValRange_eq_of_high_zero {m : ℕ} (f : ℕ → Fin m) (s : State m) (n k : ℕ) (hnk : n ≤ k)
    (hz : ∀ j, n ≤ j → j < k → s (f j) = false) :
    regValRange f s k = regValRange f s n := by
  rw [regValRange_split f s n k hnk]
  have : regValRange (fun j => f (n + j)) s (k - n) = 0 := by
    simp only [regValRange]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_range] at hj
    rw [hz (n + j) (by omega) (by omega)]
    simp
  rw [this, mul_zero, add_zero]

/-- A partial-product step preserves the multiplicand `Y` (the addend wires are read-only; the wires
beyond the window are external). -/
theorem stepLayout_preserves_Y (L : MulLayout m n W) (sh : ℕ) (s : State m)
    (hcarry : ∀ k, s (L.Carry sh k) = false) (j : ℕ) (hj : j < W) :
    denote (rippleCirc (stepLayout L sh)) s (L.Y j) = s (L.Y j) := by
  by_cases hjw : j < W - sh
  · exact (rippleCirc_invariant (stepLayout L sh) s hcarry (W - sh) (le_refl _)).2.1 j hjw
  · apply rippleCirc_preserves_external
    · exact fun k _ => fun h => absurd (L.hYInj j k hj (by omega) h) (by omega)
    · exact fun k _ => L.hYAcc j (sh + k)
    · exact fun k _ => L.hYCarry j sh k

/-- A partial-product step at shift `sh` preserves the carry chain of any other shift `sh' ≠ sh`. -/
theorem stepLayout_preserves_carry (L : MulLayout m n W) (sh sh' : ℕ)
    (hshW : sh ≤ W) (hsh'W : sh' ≤ W) (hne : sh' ≠ sh) (s : State m) (k : ℕ) :
    denote (rippleCirc (stepLayout L sh)) s (L.Carry sh' k) = s (L.Carry sh' k) := by
  apply rippleCirc_preserves_external
  · exact fun p _ => (L.hYCarry p sh' k).symm
  · exact fun p _ => (L.hAccCarry (sh + p) sh' k).symm
  · exact fun p _ => L.hCarryCross sh' sh k p hsh'W hshW hne

/-- **Multiplier correctness (Stage B.2 headline).** The shift-and-add multiplier over `shifts` (the
set bits of the classical constant `a`) leaves the accumulator holding `Acc + (∑ 2^sh) · Y`, provided
the carries start `false`, `Y`'s high bits are zero, and the result does not overflow `2^W`. With
`Acc` initialised to `0` and `∑ 2^sh = a`, this is `Acc = a · Y`. -/
theorem mulCircuit_correct (L : MulLayout m n W) :
    ∀ (shifts : List ℕ), shifts.Nodup → (∀ sh ∈ shifts, sh + n ≤ W) →
    ∀ (s : State m) (Yv : ℕ),
      (∀ sh ∈ shifts, ∀ k, s (L.Carry sh k) = false) →
      (∀ j, n ≤ j → j < W → s (L.Y j) = false) →
      regValRange L.Y s n = Yv →
      regValRange L.Acc s W + (shifts.map (2 ^ ·)).sum * Yv < 2 ^ W →
      regValRange L.Acc (denote (mulCircuit L shifts) s) W
        = regValRange L.Acc s W + (shifts.map (2 ^ ·)).sum * Yv := by
  intro shifts
  induction shifts with
  | nil => intro _ _ s Yv _ _ _ _; simp [mulCircuit, multiplier]
  | cons sh rest ih =>
    intro hnd hsh s Yv hcarry hYhigh hYv hbound
    have hshmem : sh ∈ sh :: rest := List.mem_cons_self
    have hshW : sh ≤ W := by have := hsh sh hshmem; omega
    have hnsh : n ≤ W - sh := by have := hsh sh hshmem; omega
    -- circuit splits as the step then the rest
    have hcirc : mulCircuit L (sh :: rest) = rippleCirc (stepLayout L sh) ++ mulCircuit L rest := by
      simp [mulCircuit, multiplier, List.map_cons, List.flatMap_cons]
    set s1 := denote (rippleCirc (stepLayout L sh)) s with hs1
    -- the addend value (Y over the window) is Yv
    have hYvw : regValRange (stepLayout L sh).A s (W - sh) = Yv := by
      show regValRange L.Y s (W - sh) = Yv
      rw [regValRange_eq_of_high_zero L.Y s n (W - sh) hnsh (fun j hj hj2 => hYhigh j hj (by omega)),
        hYv]
    -- no overflow on the window
    have hsplit := regValRange_split L.Acc s sh W hshW
    have hno : Yv + regValRange (fun k => L.Acc (sh + k)) s (W - sh) < 2 ^ (W - sh) := by
      have hbexp : regValRange L.Acc s W + ((2 ^ sh) * Yv + (rest.map (2 ^ ·)).sum * Yv) < 2 ^ W := by
        have := hbound; simp only [List.map_cons, List.sum_cons, Nat.add_mul] at this; exact this
      have e : 2 ^ sh * regValRange (fun k => L.Acc (sh + k)) s (W - sh)
          = regValRange L.Acc s W - regValRange L.Acc s sh := by omega
      have key : 2 ^ sh * (Yv + regValRange (fun k => L.Acc (sh + k)) s (W - sh)) < 2 ^ W := by
        rw [Nat.mul_add, e]; omega
      have hpow : (2 : ℕ) ^ W = 2 ^ sh * 2 ^ (W - sh) := by rw [← pow_add]; congr 1; omega
      rw [hpow] at key
      exact Nat.lt_of_mul_lt_mul_left key
    -- the step accumulates 2^sh * Yv
    have hstep : regValRange L.Acc s1 W = regValRange L.Acc s W + 2 ^ sh * Yv :=
      accStep (stepLayout L sh) L.Acc s sh W rfl hshW (fun _ => rfl) L.hAccInj
        (fun j _ k => (L.hYAcc k j).symm) (fun j _ k => L.hAccCarry j sh k)
        (hcarry sh hshmem) Yv hYvw hno
    -- Y preserved ⇒ its readout and high-zero carry to s1
    have hYpres : ∀ j, j < W → s1 (L.Y j) = s (L.Y j) := fun j hj =>
      stepLayout_preserves_Y L sh s (hcarry sh hshmem) j hj
    have hYv1 : regValRange L.Y s1 n = Yv := by
      rw [← hYv]; apply Finset.sum_congr rfl
      intro j hj; rw [Finset.mem_range] at hj; rw [hYpres j (by omega)]
    have hYhigh1 : ∀ j, n ≤ j → j < W → s1 (L.Y j) = false := fun j hj hj2 => by
      rw [hYpres j hj2]; exact hYhigh j hj hj2
    -- other carries stay false at s1
    have hcarry1 : ∀ sh' ∈ rest, ∀ k, s1 (L.Carry sh' k) = false := by
      intro sh' hsh' k
      have hne : sh' ≠ sh := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hsh')
      have hsh'W : sh' ≤ W := by have := hsh sh' (List.mem_cons_of_mem _ hsh'); omega
      rw [hs1, stepLayout_preserves_carry L sh sh' hshW hsh'W hne s k]
      exact hcarry sh' (List.mem_cons_of_mem _ hsh') k
    -- bound carries to the rest
    have hbound1 : regValRange L.Acc s1 W + (rest.map (2 ^ ·)).sum * Yv < 2 ^ W := by
      rw [hstep]
      have := hbound; simp only [List.map_cons, List.sum_cons, Nat.add_mul] at this; omega
    -- assemble
    rw [hcirc, denote_append, ← hs1,
      ih (List.nodup_cons.mp hnd).2 (fun sh' h => hsh sh' (List.mem_cons_of_mem _ h)) s1 Yv
        hcarry1 hYhigh1 hYv1 hbound1, hstep]
    simp only [List.map_cons, List.sum_cons, Nat.add_mul]
    ring

/-! ### Non-vacuity witness

A concrete `MulLayout` showing the structure is inhabited (the bounded injectivity/disjointness fields
are jointly satisfiable in finitely many wires) and `mulCircuit_correct` applies. Accumulator on wire
`0`, multiplicand on wire `1`, and two disjoint carry banks (`{2,3}` for shift `0`, `{4,5}` for shift
`1`) so the cross-shift disjointness `hCarryCross` is non-vacuous. -/

/-- A concrete 1-bit multiplier layout on `Fin 6` (`n = W = 1`): accumulator wire `0`, multiplicand
wire `1`, carry banks `{2,3}` (shift `0`) and `{4,5}` (shift `1`), via the arithmetic encoding
`Carry sh k = 2 + 2·min sh 1 + min k 1` (no case split — every field proof is `omega`). -/
def mulLayout1 : MulLayout 6 1 1 where
  Acc _ := 0
  Y _ := 1
  Carry sh k := ⟨2 + 2 * min sh 1 + min k 1, by omega⟩
  hYAcc _ _ := by decide
  hYCarry i sh j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hAccCarry i sh j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hCarryCross sh sh' i j hsh hsh' hne := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hAccInj i j _ _ _ := by omega
  hYInj i j _ _ _ := by omega
  hCarryInj sh i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega

/-- The Pass-2 headline is non-vacuous: it applies to `mulLayout1`. For the 1-bit multiply by `a = 1`
(`shifts = [0]`), with accumulator initialised `0`, it yields `Acc = 1 · Y = Y`. -/
example (s : State 6) (hcarry : ∀ sh ∈ [0], ∀ k, s (mulLayout1.Carry sh k) = false)
    (hacc0 : regValRange mulLayout1.Acc s 1 = 0) (Yv : ℕ) (hYv : regValRange mulLayout1.Y s 1 = Yv)
    (hbnd : regValRange mulLayout1.Acc s 1 + ([0].map (2 ^ ·)).sum * Yv < 2 ^ 1) :
    regValRange mulLayout1.Acc (denote (mulCircuit mulLayout1 [0]) s) 1 = Yv := by
  rw [mulCircuit_correct mulLayout1 [0] (by decide) (by decide) s Yv hcarry
    (by intro j hj hj2; omega) hYv hbnd, hacc0]
  simp

/-! ### Stage B.3: the modular (`ZMod N`) connection — the multiplier realises `mulConst`

`mulCircuit_correct` gives the *exact* integer product `a · Y` in the `W`-bit accumulator (no
overflow). The Shor `mulOracle` action is `y ↦ a · y` on `ZMod N` (`mulConst`), and that is precisely
the accumulator's value cast into `ZMod N` — the cast performs the `mod N` reduction, with no
`N = 2^W` assumption and no truncation hypothesised away (the no-overflow hypothesis guarantees the
register holds the exact integer; the `ZMod N` cast then reduces it honestly).

Honest scope: the accumulator physically holds the exact integer `a · Y` (`W` bits, `W` chosen large
enough — for Shor `W ≥ 2·bitlen N`, since `a, y < N ⇒ a·y < N²`); its `ZMod N` interpretation is the
oracle action. Reducing the register in place to a `bitlen N`-bit representative of `a·y mod N` is a
reversible modular-reduction circuit (conditional-subtract), a qubit-count optimisation not built here. -/

/-- **Modular-multiplication correctness (Tranche 3 capstone).** With the accumulator initialised `0`
and no overflow, the shift-and-add multiplier's output register, read in `ZMod N`, is the `mulConst`
(modular-multiplication) action `(∑ 2^sh) · Y`. For `∑ 2^sh = a` this is Shor's `mulOracle` action
`y ↦ a · y mod N`. -/
theorem mulCircuit_correct_zmod (N : ℕ) (L : MulLayout m n W) (shifts : List ℕ) (s : State m)
    (Yv : ℕ) (hnd : shifts.Nodup) (hsh : ∀ sh ∈ shifts, sh + n ≤ W)
    (hcarry : ∀ sh ∈ shifts, ∀ k, s (L.Carry sh k) = false)
    (hYhigh : ∀ j, n ≤ j → j < W → s (L.Y j) = false)
    (hYv : regValRange L.Y s n = Yv)
    (hAcc0 : regValRange L.Acc s W = 0)
    (hbound : (shifts.map (2 ^ ·)).sum * Yv < 2 ^ W) :
    ((regValRange L.Acc (denote (mulCircuit L shifts) s) W : ℕ) : ZMod N)
      = mulConst N (((shifts.map (2 ^ ·)).sum : ℕ) : ZMod N) ((Yv : ℕ) : ZMod N) := by
  have hb : regValRange L.Acc s W + (shifts.map (2 ^ ·)).sum * Yv < 2 ^ W := by
    rw [hAcc0, zero_add]; exact hbound
  rw [mulCircuit_correct L shifts hnd hsh s Yv hcarry hYhigh hYv hb, hAcc0, zero_add, mulConst,
    Nat.cast_mul]

/-- Non-vacuity of the modular capstone: applied to `mulLayout1` it computes `mulConst N 1 Y` in
`ZMod N` (multiply by `a = 1`). -/
example (N : ℕ) (s : State 6) (hcarry : ∀ sh ∈ [0], ∀ k, s (mulLayout1.Carry sh k) = false)
    (hacc0 : regValRange mulLayout1.Acc s 1 = 0) (Yv : ℕ) (hYv : regValRange mulLayout1.Y s 1 = Yv)
    (hbnd : ([0].map (2 ^ ·)).sum * Yv < 2 ^ 1) :
    ((regValRange mulLayout1.Acc (denote (mulCircuit mulLayout1 [0]) s) 1 : ℕ) : ZMod N)
      = mulConst N (1 : ZMod N) ((Yv : ℕ) : ZMod N) := by
  rw [mulCircuit_correct_zmod N mulLayout1 [0] s Yv (by decide) (by decide) hcarry
    (by intro j hj hj2; omega) hYv hacc0 hbnd]
  norm_num [mulConst]

end Reversible
