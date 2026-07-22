/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Reversible.Cost

/-!
# A VALUE-EXACT constant-propagation pass on reversible circuits  (ECDLP, the frontier's key lever)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The ecdsa.fail frontier's dominant Toffoli lever is `constprop` (`ecdsafail-toffoli-reduction`): a forward
abstract interpretation over the op-stream that tracks each wire as `Zero / One / Unknown` (seeded from
the classical init — ancillas are `|0⟩`) and FOLDS provably-determined Toffolis:

* a `CCX` with a control known `0` never fires → **drop** it;
* a `CCX` with a control known `1` acts as a `CX` on the other control → **fold to `CX`**.

Both are VALUE-EXACT — they change the gate list but not the function computed — so they cost NO hard
inputs (`no new λ`), the property the harness names as required and hard to certify. This module builds
that pass and MACHINE-CHECKS its value-exactness (`cprop_denote`): the frontier optimises informally; here
it is a proved circuit-to-circuit transform. The abstract state is deliberately conservative (any written
wire becomes `Unknown`; only `swap` moves knowledge), which is sound and already captures the main
benefit — a fresh `|0⟩` ancilla stays known-`0` until it is written, so every Toffoli reading it as a
control while it is still `0` is dropped.
-/

@[expose] public section

namespace Reversible

variable {m : ℕ}

/-- Abstract wire values: `none = Unknown`, `some b = provably `b``. -/
abbrev Abs (m : ℕ) := Fin m → Option Bool

/-- The abstract state `α` soundly describes concrete state `s`: every wire `α` claims to know has that
value in `s`. -/
def absAgree (α : Abs m) (s : State m) : Prop := ∀ i b, α i = some b → s i = b

/-! ### Folding one gate against the abstract state -/

/-- **Fold a gate given known-constant wires.** Only `CCX` folds: a degenerate `CCX` (target is a control)
is the identity → drop; a control known `0` → drop; a control known `1` → collapse to a `CX` on the other
control. Every other gate is kept. VALUE-EXACT (`foldGate_denote`). -/
def foldGate (α : Abs m) : Gate m → Circuit m
  | .CCX c₁ c₂ t =>
      if t = c₁ ∨ t = c₂ then []
      else if α c₁ = some false ∨ α c₂ = some false then []
      else if α c₁ = some true then [.CX c₂ t]
      else if α c₂ = some true then [.CX c₁ t]
      else [.CCX c₁ c₂ t]
  | g => [g]

/-- **`foldGate` is value-exact.** On any state the abstract `α` correctly describes, the folded gate list
computes exactly what the original gate does. -/
theorem foldGate_denote {α : Abs m} {s : State m} (h : absAgree α s) (g : Gate m) :
    denote (foldGate α g) s = denoteGate g s := by
  cases g with
  | X i => rfl
  | CX c t => rfl
  | swap i j => rfl
  | CCX c₁ c₂ t =>
    by_cases hdeg : t = c₁ ∨ t = c₂
    · have hf : foldGate α (.CCX c₁ c₂ t) = [] := by simp only [foldGate, if_pos hdeg]
      rw [hf, denote_nil, denoteGate, if_pos hdeg]
    · by_cases h0 : α c₁ = some false ∨ α c₂ = some false
      · have hf : foldGate α (.CCX c₁ c₂ t) = [] := by simp only [foldGate, if_neg hdeg, if_pos h0]
        rw [hf, denote_nil, denoteGate, if_neg hdeg]
        have hff : (s c₁ && s c₂) = false := by
          rcases h0 with hc | hc
          · rw [h c₁ false hc]; rfl
          · rw [h c₂ false hc]; exact Bool.and_false _
        rw [hff, Bool.xor_false, Function.update_eq_self]
      · by_cases h1 : α c₁ = some true
        · have hf : foldGate α (.CCX c₁ c₂ t) = [.CX c₂ t] := by
            simp only [foldGate, if_neg hdeg, if_neg h0, if_pos h1]
          have hc₁ : s c₁ = true := h c₁ true h1
          have hne2 : ¬ (c₂ = t) := fun e => hdeg (Or.inr e.symm)
          rw [hf]
          simp only [denote_cons, denote_nil, denoteGate, if_neg hne2, if_neg hdeg, hc₁,
            Bool.true_and, Bool.xor_comm]
        · by_cases h2 : α c₂ = some true
          · have hf : foldGate α (.CCX c₁ c₂ t) = [.CX c₁ t] := by
              simp only [foldGate, if_neg hdeg, if_neg h0, if_neg h1, if_pos h2]
            have hc₂ : s c₂ = true := h c₂ true h2
            have hne1 : ¬ (c₁ = t) := fun e => hdeg (Or.inl e.symm)
            rw [hf]
            simp only [denote_cons, denote_nil, denoteGate, if_neg hne1, if_neg hdeg, hc₂,
              Bool.and_true, Bool.xor_comm]
          · have hf : foldGate α (.CCX c₁ c₂ t) = [.CCX c₁ c₂ t] := by
              simp only [foldGate, if_neg hdeg, if_neg h0, if_neg h1, if_neg h2]
            rw [hf]; rfl

/-! ### Forward-updating the abstract state -/

/-- **Conservative forward abstract-state update.** `X` flips a known bit; `swap` exchanges; a `CX`/`CCX`
write makes the target `Unknown` (sound over-approximation). Wires not written keep their knowledge — so a
fresh `|0⟩` ancilla stays known-`0` until something writes it. -/
def stepAbs (α : Abs m) : Gate m → Abs m
  | .X i => Function.update α i none
  | .CX _ t => Function.update α t none
  | .CCX _ _ t => Function.update α t none
  | .swap i j => fun k => if k = i then α j else if k = j then α i else α k

/-- **`stepAbs` is sound.** If `α` describes `s`, the updated abstract state describes the gate's output
state. Every write-target becomes `Unknown` (vacuously sound); `swap` exchanges knowledge; untouched
wires keep it. -/
theorem stepAbs_agree {α : Abs m} {s : State m} (h : absAgree α s) (g : Gate m) :
    absAgree (stepAbs α g) (denoteGate g s) := by
  intro i b hib
  cases g with
  | X j =>
    simp only [stepAbs] at hib
    by_cases hij : i = j
    · rw [hij, Function.update_self] at hib; simp at hib
    · rw [Function.update_of_ne hij] at hib
      simp only [denoteGate, Function.update_of_ne hij]; exact h i b hib
  | CX c t =>
    simp only [stepAbs] at hib
    by_cases hit : i = t
    · rw [hit, Function.update_self] at hib; simp at hib
    · rw [Function.update_of_ne hit] at hib
      have hi : denoteGate (.CX c t) s i = s i := by
        by_cases hct : c = t
        · rw [denoteGate, if_pos hct]
        · rw [denoteGate, if_neg hct, Function.update_of_ne hit]
      rw [hi]; exact h i b hib
  | CCX c₁ c₂ t =>
    simp only [stepAbs] at hib
    by_cases hit : i = t
    · rw [hit, Function.update_self] at hib; simp at hib
    · rw [Function.update_of_ne hit] at hib
      have hi : denoteGate (.CCX c₁ c₂ t) s i = s i := by
        by_cases hdeg : t = c₁ ∨ t = c₂
        · rw [denoteGate, if_pos hdeg]
        · rw [denoteGate, if_neg hdeg, Function.update_of_ne hit]
      rw [hi]; exact h i b hib
  | swap p q =>
    simp only [stepAbs] at hib
    by_cases hip : i = p
    · simp only [if_pos hip] at hib
      rw [denoteGate, Function.comp_apply, hip, Equiv.swap_apply_left]; exact h q b hib
    · by_cases hiq : i = q
      · simp only [if_neg hip, if_pos hiq] at hib
        rw [denoteGate, Function.comp_apply, hiq, Equiv.swap_apply_right]; exact h p b hib
      · simp only [if_neg hip, if_neg hiq] at hib
        rw [denoteGate, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hip hiq]; exact h i b hib

/-! ### The pass and its value-exactness -/

/-- **The constant-propagation pass.** Fold each gate against the running abstract state, threading the
forward update. Seeded with `α` describing the input (e.g. ancillas `some false`). -/
def cprop (α : Abs m) : Circuit m → Circuit m
  | [] => []
  | g :: gs => foldGate α g ++ cprop (stepAbs α g) gs

/-- **THE HEADLINE — `cprop` is VALUE-EXACT.** For any input `s` the seed `α` correctly describes, the
propagated circuit computes exactly the same function: `denote (cprop α c) s = denote c s`. So folding
provably-determined Toffolis changes the gate list (fewer/cheaper gates) but NOT the computed value — the
frontier's key lever, machine-checked. -/
theorem cprop_denote {α : Abs m} (c : Circuit m) {s : State m} (h : absAgree α s) :
    denote (cprop α c) s = denote c s := by
  induction c generalizing α s with
  | nil => rfl
  | cons g gs ih =>
    show denote (foldGate α g ++ cprop (stepAbs α g) gs) s = denote (g :: gs) s
    rw [denote_append, foldGate_denote h g, denote_cons]
    exact ih (stepAbs_agree h g)

/-! ### A concrete win: a known-`0` ancilla control drops its Toffoli -/

/-- Layout: wire `0` is a known-`0` ancilla; `1, 2` are data. -/
def demoAbs : Abs 3 := fun i => if i = 0 then some false else none

/-- On a state where wire `0` is `false`, `demoAbs` is sound. -/
theorem demoAbs_agree (s : State 3) (h0 : s 0 = false) : absAgree demoAbs s := by
  intro i b hib
  by_cases hi : i = 0
  · subst hi
    cases b <;> simp_all [demoAbs]
  · simp only [demoAbs, if_neg hi] at hib
    simp at hib

/-- `cprop` DROPS the Toffoli in `[CCX 0 1 2]` (control wire `0` known `0`): the emitted Toffoli count
falls `1 → 0`, value-exactly (`cprop_denote` + `demoAbs_agree`). The single measured instance of the
frontier's `constprop` lever, machine-checked. -/
example : (circuitCost (cprop demoAbs [Gate.CCX 0 1 2])).toffoli = 0 := by decide

/-- ...and the original had one Toffoli — so the fold is a real `−1`. -/
example : (circuitCost [Gate.CCX (0 : Fin 3) 1 2]).toffoli = 1 := by decide

/-! ### `cprop` is a sound REDUCING optimization (cost side)

`cprop_denote` shows the pass preserves the computed VALUE. These show it never increases — and, on a
known-constant control, strictly decreases — the emitted Toffoli count. Together: `cprop` is a certified
value-exact Toffoli-reducing pass, exactly the frontier's key lever, proved both correct and beneficial. -/

/-- **Folding never increases a gate's Toffoli count.** A `CCX` folds to `[]`, `[CX]`, or `[CCX]` — Toffoli
count `0`, `0`, or `1`, all `≤ 1`; every other gate is unchanged. -/
theorem foldGate_toffoli_le (α : Abs m) (g : Gate m) :
    (circuitCost (foldGate α g)).toffoli ≤ (gateCost g).toffoli := by
  cases g with
  | X i => simp [foldGate, circuitCost, gateCost]
  | CX c t => simp [foldGate, circuitCost, gateCost]
  | swap i j => simp [foldGate, circuitCost, gateCost]
  | CCX c₁ c₂ t => simp only [foldGate]; split_ifs <;> simp [circuitCost, gateCost]

/-- **`cprop` never increases the Toffoli count.** So constant-propagation is a valid optimization: it
computes the same value (`cprop_denote`) with no more Toffolis. -/
theorem cprop_toffoli_le (α : Abs m) (c : Circuit m) :
    (circuitCost (cprop α c)).toffoli ≤ (circuitCost c).toffoli := by
  induction c generalizing α with
  | nil => simp [cprop]
  | cons g gs ih =>
    rw [cprop, cost_comp_toffoli_count]
    have hcons : (circuitCost (g :: gs)).toffoli
        = (gateCost g).toffoli + (circuitCost gs).toffoli := by simp [circuitCost]
    rw [hcons]
    have h1 := foldGate_toffoli_le α g
    have h2 := ih (stepAbs α g)
    omega

/-- **The reduction mechanism.** A non-degenerate `CCX` with a control known to be `false` folds AWAY (to
`[]`): its Toffoli is dropped entirely. This is where constant propagation buys Toffolis. -/
theorem foldGate_ccx_known_false (α : Abs m) (c₁ c₂ t : Fin m)
    (hdeg : ¬ (t = c₁ ∨ t = c₂)) (h0 : α c₁ = some false ∨ α c₂ = some false) :
    foldGate α (Gate.CCX c₁ c₂ t) = [] := by
  simp only [foldGate, if_neg hdeg, if_pos h0]

/-- **A real multi-Toffoli win on the AND-adder's carry cell.** The three-`CCX` carry cell
`[CCX a b g, CCX a c g, CCX b c g]` with the carry-in `c` a known-`0` ancilla constant-propagates to a
SINGLE Toffoli — a value-exact `3 → 1` (67%) Toffoli reduction, exactly the structure constant folding
exploits in a ripple/AND adder whose low carry-in is `|0⟩`. -/
theorem andCell_constprop_reduces :
    (circuitCost (cprop (fun i : Fin 4 => if i = 2 then some false else none)
        [Gate.CCX 0 1 3, Gate.CCX 0 2 3, Gate.CCX 1 2 3])).toffoli = 1
      ∧ (circuitCost [Gate.CCX (0 : Fin 4) 1 3, Gate.CCX 0 2 3, Gate.CCX 1 2 3]).toffoli = 3 := by
  decide

end Reversible
