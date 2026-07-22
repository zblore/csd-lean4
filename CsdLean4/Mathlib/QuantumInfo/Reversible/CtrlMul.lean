/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Mathlib.QuantumInfo.Reversible.CtrlAdd
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModMul

/-!
# Reversible quantum×quantum multiplication — controlled shift-and-add  (ECDLP Phase 2, Stage S2.3)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The Tranche-3 multiplier (`ModMul.lean`) is quantum×classical (`a·Y`, `a` a *classical* constant fixing
which shifts appear). A genuine **quantum×quantum** multiply `X·Y` (both factors registers — what
squaring and elliptic-curve field multiplication need) controls each partial-product add on a *register
bit* `X_i`. This module folds the controlled ripple adder (`CtrlAdd.lean`, `cRippleCirc_correct`) over
the bits of `X`, with the per-bit control wire bound to `X_i` and a shared ancilla re-cleaned between
steps (`cRippleCirc_anc_restored`).

## What is proved here

* `cAccStep` — **the controlled accumulation step**: one controlled full-window ripple add of the
  multiplicand `Y` (value `Yv`) into the accumulator window `Acc[i, W)`, controlled on `ctrl`, increases
  the accumulator by `if ctrl then 2^i · Yv else 0`. The controlled analogue of `ModMul.accStep`,
  routed through `cRippleCirc_correct` (so the `ctrl`-clear case adds nothing) — the heart of the
  quantum×quantum multiply.
-/

namespace Reversible

variable {m : ℕ}

/-- **Controlled accumulation step.** One controlled full-remaining-width ripple add of the multiplicand
(value `Yv`, read by `L.A`) into the accumulator window `Acc[i, W)`, controlled on `L.ctrl`: it
increases the full accumulator value by `2^i · Yv` when the control is set and leaves it unchanged when
clear — `+ (if ctrl then 2^i · Yv else 0)`. The carry propagates through the whole upper accumulator
(width `w = W - i`); the low `i` bits are preserved (they are external to the slice); the add must not
overflow the window. The controlled analogue of `ModMul.accStep`. -/
theorem cAccStep {w : ℕ} (L : CRippleLayout m w) (Acc : ℕ → Fin m) (s : State m)
    (i W : ℕ) (hw : w = W - i) (hiW : i ≤ W)
    (hB : ∀ k, L.B k = Acc (i + k))
    (hAccinj : ∀ j k, j < W → k < W → Acc j = Acc k → j = k)
    (hAccA : ∀ j, j < i → ∀ k, Acc j ≠ L.A k)
    (hAccC : ∀ j, j < i → ∀ k, Acc j ≠ L.C k)
    (hAccctrl : ∀ j, j < i → Acc j ≠ L.ctrl)
    (hAccanc : ∀ j, j < i → Acc j ≠ L.anc)
    (hcarry : ∀ j, s (L.C j) = false) (hanc0 : s L.anc = false)
    (Yv : ℕ) (hYv : regValRange L.A s w = Yv)
    (hno : Yv + regValRange (fun k => Acc (i + k)) s w < 2 ^ w) :
    regValRange Acc (denote (cRippleCirc L) s) W
      = regValRange Acc s W + (if s L.ctrl then 2 ^ i * Yv else 0) := by
  have hWi : W - i = w := hw.symm
  have hcorr := cRippleCirc_correct L s hcarry hanc0
  have hBwin : L.B = fun k => Acc (i + k) := funext hB
  rw [hBwin, hYv] at hcorr
  have hlow : regValRange Acc (denote (cRippleCirc L) s) i = regValRange Acc s i := by
    simp only [regValRange]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [cRippleCirc_preserves_external L s (Acc j) (hAccctrl j hj) (hAccanc j hj)
        (fun k _ => hAccA j hj k) ?_ (fun k _ => hAccC j hj k)]
    intro k hk
    rw [hB]
    exact fun h => absurd (hAccinj j (i + k) (by omega) (by omega) h) (by omega)
  rw [regValRange_split Acc (denote (cRippleCirc L) s) i W hiW,
      regValRange_split Acc s i W hiW, hlow, hWi]
  cases hc : s L.ctrl with
  | true =>
    simp only [hc, if_true] at hcorr ⊢
    rw [Nat.mod_eq_of_lt hno] at hcorr
    rw [hcorr]; ring
  | false =>
    simp only [hc, Bool.false_eq_true, if_false] at hcorr ⊢
    rw [hcorr]; ring

/-! ### The quantum×quantum multiplier and its correctness

A `CMulLayout` lays out, on `Fin M`: the accumulator `Acc` (W wires), the **control register** `X` (the
first factor, whose bit `sh` controls partial product `sh`), the multiplicand `Y` (W wires, high bits
held zero), a per-shift carry chain `Carry`, and the shared ancilla `anc`. The multiplier is the
concatenation, over the shift list, of one controlled full-window ripple add of `Y` into `Acc[sh, W)`
controlled on `X sh`. Folding `cAccStep` gives `Acc ← Acc + (∑ sh, [X_sh] · 2^sh) · Y = Acc + X·Y`. -/

/-- A quantum×quantum multiplier layout on `Fin M`: accumulator `Acc`, control register `X`,
multiplicand `Y` (high bits zero), per-shift carry chain `Carry`, shared ancilla `anc`. The fields are
pure wire geometry (disjointness + injectivity). -/
structure CMulLayout (M n W : ℕ) where
  /-- Accumulator wires (indices `[0, W)`). -/
  Acc : ℕ → Fin M
  /-- Control-register wires (the first factor `X`; bit `sh` controls partial product `sh`). -/
  X : ℕ → Fin M
  /-- Multiplicand wires (`W`-wire register; values in `[0, n)`, high bits held zero). -/
  Y : ℕ → Fin M
  /-- Carry chain for the partial-product add at shift `sh`. -/
  Carry : ℕ → ℕ → Fin M
  /-- The shared clean ancilla. -/
  anc : Fin M
  hYAcc : ∀ i j, Y i ≠ Acc j
  hYCarry : ∀ i sh j, Y i ≠ Carry sh j
  hAccCarry : ∀ i sh j, Acc i ≠ Carry sh j
  hCarryCross : ∀ sh sh' i j, sh ≤ W → sh' ≤ W → sh ≠ sh' → Carry sh i ≠ Carry sh' j
  hAccInj : ∀ i j, i < W → j < W → Acc i = Acc j → i = j
  hYInj : ∀ i j, i < W → j < W → Y i = Y j → i = j
  hCarryInj : ∀ sh i j, i ≤ W → j ≤ W → Carry sh i = Carry sh j → i = j
  hXAcc : ∀ i j, X i ≠ Acc j
  hXY : ∀ i j, X i ≠ Y j
  hXCarry : ∀ i sh j, X i ≠ Carry sh j
  hXanc : ∀ i, X i ≠ anc
  hXInj : ∀ i j, i < W → j < W → X i = X j → i = j
  hAncAcc : ∀ j, anc ≠ Acc j
  hAncY : ∀ j, anc ≠ Y j
  hAncCarry : ∀ sh j, anc ≠ Carry sh j

variable {n W : ℕ}

/-- The controlled-ripple layout for the partial product at shift `sh`: controlled on `X sh`, add the
multiplicand `Y` into the accumulator window `Acc[sh, W)` (width `W - sh`), carry chain `Carry sh`,
shared ancilla `anc`. -/
def cStepLayout (L : CMulLayout m n W) (sh : ℕ) : CRippleLayout m (W - sh) where
  A := L.Y
  B := fun k => L.Acc (sh + k)
  C := L.Carry sh
  ctrl := L.X sh
  anc := L.anc
  hAB i j := L.hYAcc i (sh + j)
  hAC i j := L.hYCarry i sh j
  hBC i j := L.hAccCarry (sh + i) sh j
  hAinj i j hi hj h := L.hYInj i j (by omega) (by omega) h
  hBinj i j hi hj h := by have := L.hAccInj (sh + i) (sh + j) (by omega) (by omega) h; omega
  hCinj i j hi hj h := L.hCarryInj sh i j (by omega) (by omega) h
  hctrlA i := L.hXY sh i
  hctrlB i := L.hXAcc sh (sh + i)
  hctrlC i := L.hXCarry sh sh i
  hctrlanc := L.hXanc sh
  hancA i := L.hAncY i
  hancB i := L.hAncAcc (sh + i)
  hancC i := L.hAncCarry sh i

/-- The quantum×quantum multiplier circuit: one controlled partial-product ripple add per shift. -/
def cMulCircuit (L : CMulLayout m n W) (shifts : List ℕ) : Circuit m :=
  multiplier (shifts.map (fun sh => cRippleCirc (cStepLayout L sh)))

/-- A partial-product step preserves the multiplicand `Y` (addend wires are read-only). -/
theorem cStepLayout_preserves_Y (L : CMulLayout m n W) (sh : ℕ) (s : State m)
    (hcarry : ∀ k, s (L.Carry sh k) = false) (hanc : s L.anc = false) (j : ℕ) (hj : j < W) :
    denote (cRippleCirc (cStepLayout L sh)) s (L.Y j) = s (L.Y j) := by
  by_cases hjw : j < W - sh
  · exact (cRippleCirc_invariant (cStepLayout L sh) s hcarry hanc (W - sh) (le_refl _)).2.1 j hjw
  · apply cRippleCirc_preserves_external
    · exact L.hXY sh j |>.symm
    · exact (L.hAncY j).symm
    · exact fun k _ => fun h => absurd (L.hYInj j k hj (by omega) h) (by omega)
    · exact fun k _ => L.hYAcc j (sh + k)
    · exact fun k _ => L.hYCarry j sh k

/-- A partial-product step at shift `sh` preserves the carry chain of any other shift `sh' ≠ sh`. -/
theorem cStepLayout_preserves_carry (L : CMulLayout m n W) (sh sh' : ℕ)
    (hshW : sh ≤ W) (hsh'W : sh' ≤ W) (hne : sh' ≠ sh) (s : State m) (k : ℕ) :
    denote (cRippleCirc (cStepLayout L sh)) s (L.Carry sh' k) = s (L.Carry sh' k) := by
  apply cRippleCirc_preserves_external
  · exact (L.hXCarry sh sh' k).symm
  · exact (L.hAncCarry sh' k).symm
  · exact fun p _ => (L.hYCarry p sh' k).symm
  · exact fun p _ => (L.hAccCarry (sh + p) sh' k).symm
  · exact fun p _ => L.hCarryCross sh' sh k p hsh'W hshW hne

/-- A partial-product step preserves every control bit `X j` (the control register is read-only). -/
theorem cStepLayout_preserves_X (L : CMulLayout m n W) (sh : ℕ) (s : State m)
    (hcarry : ∀ k, s (L.Carry sh k) = false) (hanc : s L.anc = false) (j : ℕ) (hjW : j < W)
    (hshW : sh < W) :
    denote (cRippleCirc (cStepLayout L sh)) s (L.X j) = s (L.X j) := by
  by_cases hjsh : j = sh
  · rw [hjsh]
    exact cRippleCirc_ctrl_preserved (cStepLayout L sh) s hcarry hanc
  · apply cRippleCirc_preserves_external
    · exact fun h => hjsh (L.hXInj j sh hjW hshW h)
    · exact L.hXanc j
    · exact fun k _ => L.hXY j k
    · exact fun k _ => L.hXAcc j (sh + k)
    · exact fun k _ => L.hXCarry j sh k

/-- **Quantum×quantum multiplier correctness (the S2.3 headline).** The controlled shift-and-add
multiplier over `shifts` leaves the accumulator holding `Acc + (∑ sh ∈ shifts, [X_sh] · 2^sh) · Y`,
where `[X_sh]` is `0/1` for the control bit — provided the carries and ancilla start `false`, `Y`'s high
bits are zero, and no step overflows. With `shifts = [0, …, n-1]` and `Acc` initialised `0` this is
`Acc = X · Y` (both factors quantum). -/
theorem cMulCircuit_correct (L : CMulLayout m n W) :
    ∀ (shifts : List ℕ), shifts.Nodup → (∀ sh ∈ shifts, sh + n ≤ W) → (∀ sh ∈ shifts, sh < W) →
    ∀ (s : State m) (Yv : ℕ),
      (∀ sh ∈ shifts, ∀ k, s (L.Carry sh k) = false) → s L.anc = false →
      (∀ j, n ≤ j → j < W → s (L.Y j) = false) →
      regValRange L.Y s n = Yv →
      regValRange L.Acc s W + (shifts.map (fun sh => 2 ^ sh * Yv)).sum < 2 ^ W →
      regValRange L.Acc (denote (cMulCircuit L shifts) s) W
        = regValRange L.Acc s W
          + (shifts.map (fun sh => if s (L.X sh) then 2 ^ sh * Yv else 0)).sum := by
  intro shifts
  induction shifts with
  | nil => intro _ _ _ s Yv _ _ _ _; simp [cMulCircuit, multiplier]
  | cons sh rest ih =>
    intro hnd hshn hshW s Yv hcarry hanc hYhigh hYv hbound
    have hshmem : sh ∈ sh :: rest := List.mem_cons_self
    have hshWlt : sh < W := hshW sh hshmem
    have hshWle : sh ≤ W := le_of_lt hshWlt
    have hnsh : n ≤ W - sh := by have := hshn sh hshmem; omega
    have hcirc : cMulCircuit L (sh :: rest)
        = cRippleCirc (cStepLayout L sh) ++ cMulCircuit L rest := by
      simp [cMulCircuit, multiplier, List.map_cons, List.flatMap_cons]
    set s1 := denote (cRippleCirc (cStepLayout L sh)) s with hs1
    -- the addend value over the window is Yv
    have hYvw : regValRange (cStepLayout L sh).A s (W - sh) = Yv := by
      show regValRange L.Y s (W - sh) = Yv
      rw [regValRange_eq_of_high_zero L.Y s n (W - sh) hnsh (fun j hj hj2 => hYhigh j hj (by omega)),
        hYv]
    -- no overflow on the window (from the worst-case bound, control-independent)
    have hno : Yv + regValRange (fun k => L.Acc (sh + k)) s (W - sh) < 2 ^ (W - sh) := by
      have hbexp : regValRange L.Acc s W
          + (2 ^ sh * Yv + (rest.map (fun sh' => 2 ^ sh' * Yv)).sum) < 2 ^ W := by
        have := hbound; simp only [List.map_cons, List.sum_cons] at this; exact this
      have hsplit := regValRange_split L.Acc s sh W hshWle
      have e : 2 ^ sh * regValRange (fun k => L.Acc (sh + k)) s (W - sh)
          = regValRange L.Acc s W - regValRange L.Acc s sh := by omega
      have key : 2 ^ sh * (Yv + regValRange (fun k => L.Acc (sh + k)) s (W - sh)) < 2 ^ W := by
        rw [Nat.mul_add, e]; omega
      have hpow : (2 : ℕ) ^ W = 2 ^ sh * 2 ^ (W - sh) := by rw [← pow_add]; congr 1; omega
      rw [hpow] at key
      exact Nat.lt_of_mul_lt_mul_left key
    -- the step accumulates (if X_sh then 2^sh * Yv else 0)
    have hstep : regValRange L.Acc s1 W
        = regValRange L.Acc s W + (if s (L.X sh) then 2 ^ sh * Yv else 0) :=
      cAccStep (cStepLayout L sh) L.Acc s sh W rfl hshWle (fun _ => rfl) L.hAccInj
        (fun j _ k => (L.hYAcc k j).symm) (fun j _ k => L.hAccCarry j sh k)
        (fun j _ => (L.hXAcc sh j).symm) (fun j _ => (L.hAncAcc j).symm)
        (hcarry sh hshmem) hanc Yv hYvw hno
    -- Y preserved ⇒ readout and high-zero carry to s1
    have hYpres : ∀ j, j < W → s1 (L.Y j) = s (L.Y j) := fun j hj =>
      cStepLayout_preserves_Y L sh s (hcarry sh hshmem) hanc j hj
    have hYv1 : regValRange L.Y s1 n = Yv := by
      rw [← hYv]; apply Finset.sum_congr rfl
      intro j hj; rw [Finset.mem_range] at hj; rw [hYpres j (by omega)]
    have hYhigh1 : ∀ j, n ≤ j → j < W → s1 (L.Y j) = false := fun j hj hj2 => by
      rw [hYpres j hj2]; exact hYhigh j hj hj2
    -- X preserved ⇒ each remaining control bit is the original
    have hXpres : ∀ j, j < W → s1 (L.X j) = s (L.X j) := fun j hj =>
      cStepLayout_preserves_X L sh s (hcarry sh hshmem) hanc j hj hshWlt
    -- carries of the rest stay false, ancilla re-cleaned
    have hcarry1 : ∀ sh' ∈ rest, ∀ k, s1 (L.Carry sh' k) = false := by
      intro sh' hsh' k
      have hne : sh' ≠ sh := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hsh')
      have hsh'W : sh' ≤ W := le_of_lt (hshW sh' (List.mem_cons_of_mem _ hsh'))
      rw [hs1, cStepLayout_preserves_carry L sh sh' hshWle hsh'W hne s k]
      exact hcarry sh' (List.mem_cons_of_mem _ hsh') k
    have hanc1 : s1 L.anc = false := by
      rw [hs1]; exact cRippleCirc_anc_restored (cStepLayout L sh) s (hcarry sh hshmem) hanc
    -- the rest's added value uses s1's control bits = s's (X preserved)
    have hrestcong : (rest.map (fun sh' => if s1 (L.X sh') then 2 ^ sh' * Yv else 0)).sum
        = (rest.map (fun sh' => if s (L.X sh') then 2 ^ sh' * Yv else 0)).sum := by
      congr 1
      apply List.map_congr_left
      intro sh' hsh'
      rw [hXpres sh' (hshW sh' (List.mem_cons_of_mem _ hsh'))]
    -- bound for the rest (worst-case, control-independent)
    have hbound1 : regValRange L.Acc s1 W + (rest.map (fun sh' => 2 ^ sh' * Yv)).sum < 2 ^ W := by
      rw [hstep]
      have := hbound; simp only [List.map_cons, List.sum_cons] at this
      split <;> omega
    rw [hcirc, denote_append, ← hs1,
      ih (List.nodup_cons.mp hnd).2 (fun sh' h => hshn sh' (List.mem_cons_of_mem _ h))
        (fun sh' h => hshW sh' (List.mem_cons_of_mem _ h)) s1 Yv hcarry1 hanc1 hYhigh1 hYv1 hbound1,
      hstep, hrestcong]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- The sum of controlled partial products over `[0, n)` is exactly `X · Y`: each set control bit
`X_sh` contributes `2^sh · Yv`, so the total is `(∑ 2^sh·[X_sh]) · Yv = regValRange X · Yv`. -/
theorem ctrlSum_eq (s : State m) (X : ℕ → Fin m) (Yv n : ℕ) :
    ((List.range n).map (fun sh => if s (X sh) then 2 ^ sh * Yv else 0)).sum
      = regValRange X s n * Yv := by
  induction n with
  | zero => simp [regValRange]
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, regValRange_succ, Nat.add_mul]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    cases s (X k) <;> simp

/-- **Quantum×quantum multiply, `X · Y` form.** Over the full shift list `[0, n)`, the controlled
shift-and-add multiplier leaves the accumulator holding `Acc + (regValRange X) · Y`. With `Acc`
initialised `0` this is `Acc = X · Y` (both factors quantum); with `X` preset to a copy of `Y` it is
`Acc = Y²` (squaring). The `ctrlSum_eq` rewrite collapses the per-bit controlled sum to the product.

The overflow hypothesis `hbound` is the **worst-case-over-`X`** condition
`Acc + (∑ 2^sh)·Yv < 2^W = Acc + (2ⁿ−1)·Yv < 2^W`, with no `if`: because `X` is a *quantum* register,
a sound circuit must not overflow on *any* branch of a superposition, so the design-time bound must hold
for the maximal `X`. (For squaring, the copy gadget `X := Y` is a precondition supplied by the caller as
`regValRange X s n = regValRange Y s n`; the copy CNOT fan-out is not built here.) -/
theorem cMulCircuit_eq_mul (L : CMulLayout m n W) (s : State m) (Yv : ℕ)
    (hshn : ∀ sh ∈ List.range n, sh + n ≤ W) (hshW : ∀ sh ∈ List.range n, sh < W)
    (hcarry : ∀ sh ∈ List.range n, ∀ k, s (L.Carry sh k) = false) (hanc : s L.anc = false)
    (hYhigh : ∀ j, n ≤ j → j < W → s (L.Y j) = false) (hYv : regValRange L.Y s n = Yv)
    (hbound : regValRange L.Acc s W + ((List.range n).map (fun sh => 2 ^ sh * Yv)).sum < 2 ^ W) :
    regValRange L.Acc (denote (cMulCircuit L (List.range n)) s) W
      = regValRange L.Acc s W + regValRange L.X s n * Yv := by
  rw [cMulCircuit_correct L (List.range n) List.nodup_range hshn hshW s Yv hcarry hanc hYhigh
    hYv hbound, ctrlSum_eq]

/-! ### Non-vacuity witness

A concrete 1-bit quantum×quantum multiplier layout on `Fin 8`: accumulator `0`, control register `X`
on `1`, multiplicand `Y` on `2`, carry banks `{3,4}` (shift `0`) / `{5,6}` (shift `1`), shared ancilla
`7` — exhibiting that `CMulLayout` is inhabited and `cMulCircuit_eq_mul` applies. -/

/-- A concrete 1-bit (`n = W = 1`) quantum×quantum multiplier layout on `Fin 8`. -/
def cMulLayout1 : CMulLayout 8 1 1 where
  Acc _ := 0
  X _ := 1
  Y _ := 2
  Carry sh k := ⟨3 + 2 * min sh 1 + min k 1, by omega⟩
  anc := 7
  hYAcc _ _ := by decide
  hYCarry i sh j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hAccCarry i sh j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hCarryCross sh sh' i j hsh hsh' hne := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hAccInj i j _ _ _ := by omega
  hYInj i j _ _ _ := by omega
  hCarryInj sh i j hi hj h := by rw [Fin.ext_iff] at h; dsimp only at h; omega
  hXAcc _ _ := by decide
  hXY _ _ := by decide
  hXCarry i sh j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega
  hXanc _ := by decide
  hXInj i j _ _ _ := by omega
  hAncAcc _ := by decide
  hAncY _ := by decide
  hAncCarry sh j := by rw [ne_eq, Fin.ext_iff]; dsimp only; omega

/-- The S2.3 headline is non-vacuous: it applies to `cMulLayout1`. For the 1-bit multiply with `Acc`
initialised `0`, it yields `Acc = X · Y`. -/
example (s : State 8) (hcarry : ∀ sh ∈ List.range 1, ∀ k, s (cMulLayout1.Carry sh k) = false)
    (hanc : s cMulLayout1.anc = false) (hacc0 : regValRange cMulLayout1.Acc s 1 = 0)
    (Yv : ℕ) (hYv : regValRange cMulLayout1.Y s 1 = Yv)
    (hbnd : regValRange cMulLayout1.Acc s 1 + ((List.range 1).map (fun sh => 2 ^ sh * Yv)).sum < 2 ^ 1) :
    regValRange cMulLayout1.Acc (denote (cMulCircuit cMulLayout1 (List.range 1)) s) 1
      = regValRange cMulLayout1.X s 1 * Yv := by
  rw [cMulCircuit_eq_mul cMulLayout1 s Yv (by decide) (by decide) hcarry hanc
    (by intro j hj hj2; omega) hYv hbnd, hacc0, zero_add]

end Reversible
