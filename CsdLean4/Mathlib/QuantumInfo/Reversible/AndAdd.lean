/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.Reversible.Eval
meta import CsdLean4.Mathlib.QuantumInfo.Reversible.Eval
public import CsdLean4.Mathlib.QuantumInfo.Reversible.ModAdd
meta import CsdLean4.Mathlib.QuantumInfo.Reversible.ModAdd

/-!
# AND-based reversible adder with explicit fresh per-carry AND temporaries  (Tier-X / L5-c prerequisite)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate). **Pure Boolean-DSL
value-correctness; no amplitude bridge and no measurement** (those are `#31` / `L5-d`).

## Why this file exists (the L5-c wall verdict)

The measurement-based AND-uncomputation gadget (`Empirical/QM/MeasurementUncompute.lean`, Gidney's
measure-and-correct, the ~2× Toffoli saving) needs an *attachment point*: a fresh ancilla holding a
logical AND of two data wires (`andInput`-shaped), uncomputed at an **explicit** sub-circuit. The
corpus's two ripple adders do not provide one:

* `ModAdd.rippleCirc` computes carries into a carry chain `C` and **leaves them dirty** (never
  uncomputed) — no uncompute sub-block to replace.
* `CuccaroAdd.cuccaroAdd` restores the carries **unitarily** inside `uma` (in-place, carry-restoring),
  with **no fresh AND temporary** — again nothing for a measurement gadget to attach to.

This file supplies the missing primitive: an adder whose carries live in **fresh `|0⟩` ancillas**,
computed by an explicit AND (Toffoli) and **uncomputed by an explicit reverse Toffoli**. The
uncompute-AND Toffolis are exactly the ones the measurement route would later eliminate.

## What is built

**Reusable circuit infrastructure** (target-frame + agreement propagation):
* `gateTarget` / `denote_apply_of_forall_not_mem_target` — a wire that is never a *target* (it may be a
  control) is preserved. The control-permitting refinement of `gateWires` / `denote_apply_of_forall_not_mem`.
* `denote_agree_on` — two states agreeing on every wire a circuit's gates touch produce equal outputs
  on those wires. The locality lemma that makes the uncompute-pass cleanup provable.

**The AND-uncompute cell** (item 1, the must-have attachment point):
* `andCarry a b g := [CCX a b g]` — the fresh-AND compute: `g ← g ⊕ (a ∧ b)` (`= a ∧ b` for `g = 0`),
  `a` / `b` preserved (`andCarry_correct`). The `andInput`-shaped state `g = a ∧ b`.
* `andUncompute a b g := [CCX a b g]` — the explicit AND-uncompute (the Toffoli a measurement gadget
  replaces). `andUncompute_restores`: it undoes `andCarry`, returning `g` to its input value.
* `andCell a b g out := andCarry ++ [CX g out] ++ andUncompute` — compute-use-uncompute:
  `out ← out ⊕ (a ∧ b)`, ancilla `g` restored (`andCell_correct` / `andCell_ancilla_clean`).

**The full AND-based ripple adder** (items 2/3): `andAdd`, on an `AndAddLayout` with addends `A`, `B`
(both preserved), a separate sum register `S`, and a fresh per-carry ancilla chain `G`. Structure:
`andForward ++ andSumPass ++ inverse andForward` — compute all carries into `G` (preserving `A`, `B`),
write the sums into `S`, then **uncompute** every carry via the reverse pass.
* `andAdd_correct`: `regValRange S (denote (andAdd L) s) n = (A + B) % 2 ^ n`.
* `andAdd_ancilla_clean`: every fresh carry-AND ancilla `G i` returns to `false`.
* `andAdd_toffoli`: `6 * n` Toffolis, of which the `3 * n` **uncompute** half is the measurement-route
  saving target (`andAdd_uncompute_toffoli`).

## Honest scope

Value-correct + ancilla-clean over `regVal`, Boolean DSL only. The compute / uncompute Toffolis here
are unitary; **replacing the uncompute half with the measurement gadget is `L5-d`**, and the
amplitude lift of the AND-uncompute block is `#31`. No measurement, no amplitudes, no ECDSA resource
claim here. The carry cell uses a 3-Toffoli *preserving majority*
`MAJ(a,b,c) = (a∧b) ⊕ (a∧c) ⊕ (b∧c)` (GF(2) identity, `majority_eq_xor3`) so the addend register `B`
survives untouched — which is what makes the reverse pass an exact `inverse` and the cleanup provable.
-/

@[expose] public section

namespace Reversible

variable {n : ℕ}

/-! ### Target-frame lemma (controls allowed, only the written wire matters) -/

/-- The set of wires a gate *writes* (its target), excluding control wires. A wire outside this set is
preserved even if it is a control. The control-permitting refinement of `gateWires`. -/
def gateTarget : Gate n → Finset (Fin n)
  | .X i => {i}
  | .CX _ t => {t}
  | .CCX _ _ t => {t}
  | .swap i j => {i, j}

/-- **Target-frame (single gate).** A wire that is not the target of `g` is preserved by `denoteGate g`
— even if it is a control. -/
theorem denoteGate_apply_of_not_mem_target {g : Gate n} {s : State n} {i : Fin n}
    (hi : i ∉ gateTarget g) : denoteGate g s i = s i := by
  cases g with
  | X j =>
    simp only [gateTarget, Finset.mem_singleton] at hi
    simp [denoteGate, Function.update_of_ne hi]
  | CX c t =>
    simp only [gateTarget, Finset.mem_singleton] at hi
    by_cases h : c = t
    · simp [denoteGate, if_pos h]
    · simp [denoteGate, if_neg h, Function.update_of_ne hi]
  | CCX c₁ c₂ t =>
    simp only [gateTarget, Finset.mem_singleton] at hi
    by_cases h : t = c₁ ∨ t = c₂
    · simp [denoteGate, if_pos h]
    · simp [denoteGate, if_neg h, Function.update_of_ne hi]
  | swap a b =>
    simp only [gateTarget, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    simp only [denoteGate, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hi.1 hi.2]

/-- **Target-frame (circuit).** A wire that is never a target of any gate of `c` is preserved by
`denote c` (it may appear as a control). -/
theorem denote_apply_of_forall_not_mem_target {i : Fin n} :
    ∀ (c : Circuit n), (∀ g ∈ c, i ∉ gateTarget g) → ∀ s : State n, denote c s i = s i
  | [], _, _ => rfl
  | g :: rest, hi, s => by
    rw [denote_cons,
      denote_apply_of_forall_not_mem_target rest
        (fun g' hg' => hi g' (List.mem_cons_of_mem g hg')) (denoteGate g s)]
    exact denoteGate_apply_of_not_mem_target (hi g (by simp))

/-! ### Agreement propagation (the cleanup locality lemma) -/

/-- **Agreement (single gate).** If `s` and `s'` agree on every wire satisfying `P`, and every wire of
`g` satisfies `P`, then `denoteGate g s` and `denoteGate g s'` agree on every `P`-wire. -/
theorem denoteGate_agree {P : Fin n → Prop} {g : Gate n}
    (hg : ∀ w ∈ gateWires g, P w) {s s' : State n}
    (hss : ∀ w, P w → s w = s' w) (w : Fin n) (hw : P w) :
    denoteGate g s w = denoteGate g s' w := by
  cases g with
  | X i =>
    simp only [denoteGate, Function.update_apply]
    by_cases h : w = i
    · rw [if_pos h, if_pos h, hss i (hg i (by simp [gateWires]))]
    · rw [if_neg h, if_neg h]; exact hss w hw
  | CX c t =>
    by_cases hct : c = t
    · simp only [denoteGate, if_pos hct]; exact hss w hw
    · simp only [denoteGate, if_neg hct, Function.update_apply]
      by_cases h : w = t
      · rw [if_pos h, if_pos h, hss c (hg c (by simp [gateWires])),
          hss t (hg t (by simp [gateWires]))]
      · rw [if_neg h, if_neg h]; exact hss w hw
  | CCX c₁ c₂ t =>
    by_cases hguard : t = c₁ ∨ t = c₂
    · simp only [denoteGate, if_pos hguard]; exact hss w hw
    · simp only [denoteGate, if_neg hguard, Function.update_apply]
      by_cases h : w = t
      · rw [if_pos h, if_pos h, hss c₁ (hg c₁ (by simp [gateWires])),
          hss c₂ (hg c₂ (by simp [gateWires])), hss t (hg t (by simp [gateWires]))]
      · rw [if_neg h, if_neg h]; exact hss w hw
  | swap i j =>
    simp only [denoteGate, Function.comp_apply]
    apply hss
    by_cases hi : w = i
    · rw [hi, Equiv.swap_apply_left]; exact hg j (by simp [gateWires])
    · by_cases hj : w = j
      · rw [hj, Equiv.swap_apply_right]; exact hg i (by simp [gateWires])
      · rw [Equiv.swap_apply_of_ne_of_ne hi hj]; exact hw

/-- **Agreement propagation (circuit).** If every gate of `c` touches only `P`-wires, and `s`, `s'`
agree on all `P`-wires, then `denote c s` and `denote c s'` agree on all `P`-wires. The locality lemma
behind the carry-ancilla cleanup: the sum pass leaves the addend/carry wires untouched, so the reverse
pass undoes the forward pass on them exactly. -/
theorem denote_agree_on {P : Fin n → Prop} :
    ∀ (c : Circuit n), (∀ g ∈ c, ∀ w ∈ gateWires g, P w) →
      ∀ {s s' : State n}, (∀ w, P w → s w = s' w) →
        ∀ w, P w → denote c s w = denote c s' w
  | [], _, _, _, hss, w, hw => hss w hw
  | g :: rest, hc, s, s', hss, w, hw => by
    rw [denote_cons, denote_cons]
    refine denote_agree_on rest (fun g' hg' => hc g' (List.mem_cons_of_mem _ hg')) ?_ w hw
    intro w' hw'
    exact denoteGate_agree (fun w'' hw'' => hc g (List.mem_cons_self ..) w'' hw'') hss w' hw'

/-! ### The fresh-AND carry cell and its explicit uncompute (item 1, the attachment point) -/

/-- **The fresh-AND compute.** A single Toffoli folding the logical AND of data wires `a`, `b` into a
fresh ancilla `g`: `g ← g ⊕ (a ∧ b)`. For a `|0⟩`-initialised `g` this writes `g = a ∧ b` — the
`andInput`-shaped state (a fresh ancilla holding `a ∧ b`, correlated with the data). -/
def andCarry (a b g : Fin n) : Circuit n := [.CCX a b g]

/-- **The explicit AND-uncompute** (the Toffoli a measurement gadget replaces). Identical gate list to
`andCarry` (a Toffoli is its own inverse): applied after `andCarry` it restores the ancilla. Named
separately to mark the attachment point. -/
def andUncompute (a b g : Fin n) : Circuit n := [.CCX a b g]

/-- **Fresh-AND-compute correctness.** For a fresh ancilla distinct from the data, `andCarry` writes
the AND into `g` (`g ← g ⊕ (a ∧ b)`) and leaves `a`, `b` untouched. -/
theorem andCarry_correct {a b g : Fin n} (hga : g ≠ a) (hgb : g ≠ b) (s : State n) :
    denote (andCarry a b g) s g = (s g ^^ (s a && s b))
      ∧ denote (andCarry a b g) s a = s a
      ∧ denote (andCarry a b g) s b = s b := by
  have hag : a ≠ g := hga.symm
  have hbg : b ≠ g := hgb.symm
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [andCarry, denote_cons, denote_nil, denoteGate,
      if_neg (not_or.mpr ⟨hga, hgb⟩)] <;>
    simp [hag, hbg]

/-- **Ancilla-clean for a `|0⟩` ancilla.** `andCarry` on a fresh `g = false` writes exactly `a ∧ b`. -/
theorem andCarry_writes_and {a b g : Fin n} (hga : g ≠ a) (hgb : g ≠ b) {s : State n}
    (hg0 : s g = false) : denote (andCarry a b g) s g = (s a && s b) := by
  rw [(andCarry_correct hga hgb s).1, hg0]; simp

/-- **The AND-uncompute restores the ancilla.** Running `andUncompute` after `andCarry` returns the
whole state to its input — in particular the fresh ancilla `g` is restored. This is the explicit
uncompute point: the second Toffoli (`andUncompute`) is the one a measurement-based gadget eliminates. -/
theorem andUncompute_restores (a b g : Fin n) (s : State n) :
    denote (andUncompute a b g) (denote (andCarry a b g) s) = s := by
  show denoteGate (.CCX a b g) (denoteGate (.CCX a b g) s) = s
  exact denoteGate_involutive (.CCX a b g) s

/-- **The compute-use-uncompute cell.** Fold the AND of `a`, `b` into `out` through a fresh ancilla:
compute `g = a ∧ b` (`andCarry`), use it (`CX g out`, i.e. `out ← out ⊕ g`), then uncompute `g`
(`andUncompute`). The cell is `[CCX a b g, CX g out, CCX a b g]`: an explicit fresh-AND temporary with
an explicit AND-uncompute sub-block, value-correct and ancilla-clean. -/
def andCell (a b g out : Fin n) : Circuit n :=
  andCarry a b g ++ [.CX g out] ++ andUncompute a b g

set_option linter.unnecessarySeqFocus false in
/-- **Cell correctness (general).** `out ← out ⊕ g ⊕ (a ∧ b)` (reading the fresh ancilla's input bit
`g`), the ancilla `g` is restored to its input, and `a`, `b` are preserved. For a `|0⟩` ancilla
(`hg0`) the `g` term drops and `out ← out ⊕ (a ∧ b)` (`andCell_correct_clean`). The genuine fresh-AND
temporary (`g = g ⊕ a ∧ b` between the compute and uncompute) is used and then cleaned up. -/
theorem andCell_correct {a b g out : Fin n}
    (hga : g ≠ a) (hgb : g ≠ b) (hoa : out ≠ a) (hob : out ≠ b) (hog : out ≠ g)
    (s : State n) :
    denote (andCell a b g out) s out = (s out ^^ s g ^^ (s a && s b))
      ∧ denote (andCell a b g out) s g = s g
      ∧ denote (andCell a b g out) s a = s a
      ∧ denote (andCell a b g out) s b = s b := by
  have hag : a ≠ g := hga.symm
  have hbg : b ≠ g := hgb.symm
  have hao : a ≠ out := hoa.symm
  have hbo : b ≠ out := hob.symm
  have hgo : g ≠ out := hog.symm
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [andCell, andCarry, andUncompute, denote_append, denote_cons, denote_nil, denoteGate,
      if_neg (not_or.mpr ⟨hga, hgb⟩)] <;>
    simp_all <;>
    cases s a <;> cases s b <;> cases s g <;> cases s out <;> decide

/-- **Cell correctness for a `|0⟩` ancilla.** With a fresh `g = false`, `out ← out ⊕ (a ∧ b)`, `g`
restored to `false`, `a`/`b` preserved. -/
theorem andCell_correct_clean {a b g out : Fin n}
    (hga : g ≠ a) (hgb : g ≠ b) (hoa : out ≠ a) (hob : out ≠ b) (hog : out ≠ g)
    {s : State n} (hg0 : s g = false) :
    denote (andCell a b g out) s out = (s out ^^ (s a && s b))
      ∧ denote (andCell a b g out) s g = false := by
  obtain ⟨ho, hg, _, _⟩ := andCell_correct hga hgb hoa hob hog s
  refine ⟨?_, by rw [hg, hg0]⟩
  rw [ho, hg0]; simp

/-- **Cell ancilla-clean.** A `|0⟩`-initialised cell ancilla returns to `false`. -/
theorem andCell_ancilla_clean {a b g out : Fin n}
    (hga : g ≠ a) (hgb : g ≠ b) (hoa : out ≠ a) (hob : out ≠ b) (hog : out ≠ g)
    {s : State n} (hg0 : s g = false) :
    denote (andCell a b g out) s g = false :=
  (andCell_correct_clean hga hgb hoa hob hog hg0).2

/-! ### Cell cost: one compute-AND + one uncompute-AND Toffoli -/

/-- **Cell Toffoli cost = 2.** One compute-AND (`andCarry`) + one uncompute-AND (`andUncompute`); the
`CX g out` is a CNOT. -/
theorem andCell_toffoli (a b g out : Fin n) : (circuitCost (andCell a b g out)).toffoli = 2 := by
  simp [circuitCost, andCell, andCarry, andUncompute, gateCost]

/-- **The uncompute-AND half is one Toffoli** — the measurement-route saving target. The cell's two
Toffolis split as one compute + one uncompute; the measurement gadget (`#31`/`L5-d`) eliminates this
uncompute Toffoli (replacing it with `H` + measurement + a conditional Clifford). -/
theorem andCell_uncompute_toffoli (a b g : Fin n) :
    (circuitCost (andUncompute a b g)).toffoli = 1 := by
  simp [circuitCost, andUncompute, gateCost]

/-! ### The preserving-majority carry cell (3-Toffoli, addend-preserving)

The ripple's per-carry cell must compute the carry-out `MAJ(a, b, c)` into a **fresh** ancilla while
leaving its inputs (in particular the addend register `B`) untouched — that is what makes the reverse
pass an exact `inverse` and the ancilla cleanup provable. The GF(2) identity
`MAJ(a,b,c) = (a∧b) ⊕ (a∧c) ⊕ (b∧c)` lets three Toffolis into a single fresh target do this. -/

/-- **Majority as a GF(2) sum of ANDs**: `MAJ(a,b,c) = (a∧b) ⊕ (a∧c) ⊕ (b∧c)`. The identity that makes
the carry computable into a fresh ancilla by three Toffolis that all read (never overwrite) the inputs. -/
theorem majority_eq_xor3 (a b c : Bool) :
    majority a b c = ((a && b) ^^ (a && c) ^^ (b && c)) := by
  cases a <;> cases b <;> cases c <;> decide

/-- **The preserving-majority carry cell.** Three Toffolis folding the AND of each input pair into a
fresh target `g`: `[CCX a b g, CCX a c g, CCX b c g]`. Each gate writes only `g` (the inputs are pure
controls), so `a`, `b`, `c` are preserved and `g ← g ⊕ MAJ(a,b,c)`. These are the explicit fresh-AND
computes; the reverse pass (`inverse`) is the explicit AND-uncompute. -/
def andCarryCell (a b c g : Fin n) : Circuit n := [.CCX a b g, .CCX a c g, .CCX b c g]

/-- **Preserving-majority correctness.** For a fresh ancilla `g = false` distinct from `a, b, c`, the
cell writes `g = MAJ(a, b, c)` and preserves `a`, `b`, `c`. -/
theorem andCarryCell_correct {a b c g : Fin n}
    (hga : g ≠ a) (hgb : g ≠ b) (hgc : g ≠ c) {s : State n} (hg0 : s g = false) :
    denote (andCarryCell a b c g) s g = majority (s a) (s b) (s c)
      ∧ denote (andCarryCell a b c g) s a = s a
      ∧ denote (andCarryCell a b c g) s b = s b
      ∧ denote (andCarryCell a b c g) s c = s c := by
  have hag : a ≠ g := hga.symm
  have hbg : b ≠ g := hgb.symm
  have hcg : c ≠ g := hgc.symm
  rw [majority_eq_xor3]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [andCarryCell, denote_cons, denote_nil, denoteGate,
      if_neg (not_or.mpr ⟨hga, hgb⟩), if_neg (not_or.mpr ⟨hga, hgc⟩),
      if_neg (not_or.mpr ⟨hgb, hgc⟩)] <;>
    simp only [Function.update_apply, hag, hbg, hcg, hg0] <;>
    simp_all

/-- Cell Toffoli cost = 3 (the three fresh-AND computes). -/
theorem andCarryCell_toffoli (a b c g : Fin n) :
    (circuitCost (andCarryCell a b c g)).toffoli = 3 := by
  simp [circuitCost, andCarryCell, gateCost]

/-! ### The AND-based ripple-adder layout -/

/-- The AND-based ripple-adder wire geometry for `n`-bit registers on `m` wires: addends `A`, `B`
(**both preserved**), a separate sum register `S` (output), and a **fresh per-carry ancilla chain**
`G` (`G 0` the input carry, `G (i+1)` the carry out of bit `i`, all init `false`). The four images are
pairwise disjoint and each injective on its used index range — the bounded-injectivity pattern of
`RippleLayout` / `CuccaroLayout`, refined to a separate sum register so the reverse pass is an exact
`inverse`. -/
structure AndAddLayout (m n : ℕ) where
  /-- First addend (preserved). -/
  A : ℕ → Fin m
  /-- Second addend (preserved). -/
  B : ℕ → Fin m
  /-- Sum output register (`(A + B) mod 2 ^ n`). -/
  S : ℕ → Fin m
  /-- Fresh per-carry ancilla chain (`G i` = carry into bit `i`; init/returned `false`). -/
  G : ℕ → Fin m
  hAB : ∀ i j, A i ≠ B j
  hAS : ∀ i j, A i ≠ S j
  hAG : ∀ i j, A i ≠ G j
  hBS : ∀ i j, B i ≠ S j
  hBG : ∀ i j, B i ≠ G j
  hSG : ∀ i j, S i ≠ G j
  hSinj : ∀ i j, i < n → j < n → S i = S j → i = j
  hGinj : ∀ i j, i < n + 1 → j < n + 1 → G i = G j → i = j

variable {m : ℕ}

/-! ### Carry / sum / forward / uncompute circuits -/

/-- The carry compute for bit `i`: preserving-majority of `(A i, B i, G i)` into the fresh `G (i+1)`. -/
def andForwardSlice (L : AndAddLayout m n) (i : ℕ) : Circuit m :=
  andCarryCell (L.A i) (L.B i) (L.G i) (L.G (i + 1))

/-- The forward carry pass over the first `k` bits. -/
def andForwardPrefix (L : AndAddLayout m n) (k : ℕ) : Circuit m :=
  (List.range k).flatMap (andForwardSlice L)

/-- The full forward carry pass (all `n` bits): computes `G (i+1) = carry`, preserving `A`, `B`. -/
def andForward (L : AndAddLayout m n) : Circuit m := andForwardPrefix L n

/-- The sum-write for bit `i`: `S i ← S i ⊕ A i ⊕ B i ⊕ G i` (three CNOTs into `S i`). -/
def andSumSlice (L : AndAddLayout m n) (i : ℕ) : Circuit m :=
  [.CX (L.A i) (L.S i), .CX (L.B i) (L.S i), .CX (L.G i) (L.S i)]

/-- The sum pass over the first `k` bits. -/
def andSumPrefix (L : AndAddLayout m n) (k : ℕ) : Circuit m :=
  (List.range k).flatMap (andSumSlice L)

/-- The full sum pass (all `n` bits). -/
def andSumPass (L : AndAddLayout m n) : Circuit m := andSumPrefix L n

/-- **The AND-based ripple adder.** Compute all carries into the fresh ancilla chain `G`
(`andForward`), write the sums into `S` (`andSumPass`), then **uncompute** every carry via the reverse
pass `inverse (andForward L)`. The uncompute pass is the explicit AND-uncompute sub-block — exactly
the Toffolis a measurement-based gadget would eliminate. -/
def andAdd (L : AndAddLayout m n) : Circuit m :=
  andForward L ++ andSumPass L ++ inverse (andForward L)

/-! ### Membership / wire / target characterisation of the forward & sum gates -/

theorem mem_andForwardPrefix {L : AndAddLayout m n} {k : ℕ} {g : Gate m}
    (hg : g ∈ andForwardPrefix L k) : ∃ j, j < k ∧ g ∈ andForwardSlice L j := by
  simp only [andForwardPrefix, List.mem_flatMap, List.mem_range] at hg
  exact hg

theorem mem_andSumPrefix {L : AndAddLayout m n} {k : ℕ} {g : Gate m}
    (hg : g ∈ andSumPrefix L k) : ∃ j, j < k ∧ g ∈ andSumSlice L j := by
  simp only [andSumPrefix, List.mem_flatMap, List.mem_range] at hg
  exact hg

theorem andForwardSlice_wires {L : AndAddLayout m n} {j : ℕ} {g : Gate m}
    (hg : g ∈ andForwardSlice L j) {w : Fin m} (hw : w ∈ gateWires g) :
    w = L.A j ∨ w = L.B j ∨ w = L.G j ∨ w = L.G (j + 1) := by
  simp only [andForwardSlice, andCarryCell, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;>
    simp only [gateWires, Finset.mem_insert, Finset.mem_singleton] at hw <;> tauto

theorem andForwardSlice_target {L : AndAddLayout m n} {j : ℕ} {g : Gate m}
    (hg : g ∈ andForwardSlice L j) {w : Fin m} (hw : w ∈ gateTarget g) :
    w = L.G (j + 1) := by
  simp only [andForwardSlice, andCarryCell, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simpa [gateTarget] using hw

theorem andSumSlice_target {L : AndAddLayout m n} {j : ℕ} {g : Gate m}
    (hg : g ∈ andSumSlice L j) {w : Fin m} (hw : w ∈ gateTarget g) :
    w = L.S j := by
  simp only [andSumSlice, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simpa [gateTarget] using hw

/-! ### Preservation lemmas (target-frame) -/

theorem andForwardPrefix_preserves_A (L : AndAddLayout m n) (s : State m) (k i : ℕ) :
    denote (andForwardPrefix L k) s (L.A i) = s (L.A i) := by
  apply denote_apply_of_forall_not_mem_target
  intro g hg hmem
  obtain ⟨j, _, hgj⟩ := mem_andForwardPrefix hg
  exact L.hAG i (j + 1) (andForwardSlice_target hgj hmem)

theorem andForwardPrefix_preserves_B (L : AndAddLayout m n) (s : State m) (k i : ℕ) :
    denote (andForwardPrefix L k) s (L.B i) = s (L.B i) := by
  apply denote_apply_of_forall_not_mem_target
  intro g hg hmem
  obtain ⟨j, _, hgj⟩ := mem_andForwardPrefix hg
  exact L.hBG i (j + 1) (andForwardSlice_target hgj hmem)

theorem andForwardPrefix_preserves_S (L : AndAddLayout m n) (s : State m) (k i : ℕ) :
    denote (andForwardPrefix L k) s (L.S i) = s (L.S i) := by
  apply denote_apply_of_forall_not_mem_target
  intro g hg hmem
  obtain ⟨j, _, hgj⟩ := mem_andForwardPrefix hg
  exact L.hSG i (j + 1) (andForwardSlice_target hgj hmem)

/-- The forward slice for bit `k` preserves any wire other than its single target `G (k+1)`. -/
theorem andForwardSlice_preserves (L : AndAddLayout m n) (s : State m) (k : ℕ) {w : Fin m}
    (hw : w ≠ L.G (k + 1)) : denote (andForwardSlice L k) s w = s w := by
  apply denote_apply_of_forall_not_mem_target
  intro g hg hmem
  exact hw (andForwardSlice_target hg hmem)

theorem andSumPrefix_preserves_of_ne_S (L : AndAddLayout m n) (t : State m) (k : ℕ) {w : Fin m}
    (hw : ∀ i, i < k → w ≠ L.S i) : denote (andSumPrefix L k) t w = t w := by
  apply denote_apply_of_forall_not_mem_target
  intro g hg hmem
  obtain ⟨j, hjk, hgj⟩ := mem_andSumPrefix hg
  exact hw j hjk (andSumSlice_target hgj hmem)

/-! ### Arithmetic: the true carry and the adder sum identity -/

/-- The true ripple carry sequence: `carryOf 0 = false`, `carryOf (i+1) = MAJ(aᵢ, bᵢ, carryOf i)`. -/
def carryOf (a b : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | (i + 1) => majority (a i) (b i) (carryOf a b i)

/-- **The adder sum identity (ℕ).** The low-`k` sum bits plus the carry into bit `k`, place-weighted,
equal the low-`k` parts of the two addends. Induction on `k` via the bitwise `fulladder_nat`. -/
theorem adder_sum_identity (a b : ℕ → Bool) :
    ∀ k, (∑ i ∈ Finset.range k, (a i ^^ b i ^^ carryOf a b i).toNat * 2 ^ i)
          + (carryOf a b k).toNat * 2 ^ k
        = (∑ i ∈ Finset.range k, (a i).toNat * 2 ^ i)
          + (∑ i ∈ Finset.range k, (b i).toNat * 2 ^ i) := by
  intro k
  induction k with
  | zero => simp [carryOf]
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      show carryOf a b (k + 1) = majority (a k) (b k) (carryOf a b k) from rfl, pow_succ]
    cases h1 : a k <;> cases h2 : b k <;> cases h3 : carryOf a b k <;>
      simp only [h3, majority, Bool.xor_false, Bool.xor_true, Bool.not_true,
        Bool.not_false, Bool.and_self, Bool.and_true, Bool.and_false, Bool.or_true,
        Bool.or_false, Bool.or_self, Bool.toNat_true, Bool.toNat_false, zero_mul, one_mul,
        add_zero] at ih ⊢ <;>
      omega

/-! ### Forward carry invariant -/

/-- **The forward carry invariant.** After the first `k` forward slices, every computed carry ancilla
`G i` (`i ≤ k`) holds the true carry `carryOf i`, and the not-yet-computed ancillas (`k < i ≤ n`) are
still `false`. By induction on `k`, each step a preserving-majority `andCarryCell` on fresh `G (k+1)`. -/
theorem andForward_carry (L : AndAddLayout m n) (s : State m) (hG0 : ∀ j, s (L.G j) = false) :
    ∀ k, k ≤ n →
      (∀ i, i ≤ k → denote (andForwardPrefix L k) s (L.G i)
          = carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) i)
      ∧ (∀ i, k < i → i ≤ n → denote (andForwardPrefix L k) s (L.G i) = false) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · intro i hi
      have : i = 0 := Nat.le_zero.mp hi
      subst this
      simp [andForwardPrefix, carryOf, hG0]
    · intro i _ _; simp [andForwardPrefix, hG0]
  | succ k ih =>
    intro hk
    have hkn : k ≤ n := Nat.le_of_succ_le hk
    have hkltn : k < n := hk
    obtain ⟨hC, hU⟩ := ih hkn
    have hsplit : andForwardPrefix L (k + 1)
        = andForwardPrefix L k ++ andForwardSlice L k := by
      simp [andForwardPrefix, List.range_succ, List.flatMap_append]
    -- the slice's fresh target G (k+1) is still false before the slice
    set sk := denote (andForwardPrefix L k) s with hskdef
    have hfresh : sk (L.G (k + 1)) = false := hU (k + 1) (by omega) (by omega)
    -- distinctness of the slice wires
    have hga : L.G (k + 1) ≠ L.A k := (L.hAG k (k + 1)).symm
    have hgb : L.G (k + 1) ≠ L.B k := (L.hBG k (k + 1)).symm
    have hgc : L.G (k + 1) ≠ L.G k := fun h =>
      Nat.succ_ne_self k (L.hGinj (k + 1) k (by omega) (by omega) h)
    obtain ⟨hcarry, hAk, hBk, hGk⟩ := andCarryCell_correct hga hgb hgc hfresh
    -- the slice's input bits, in terms of original s
    have hskA : sk (L.A k) = s (L.A k) := andForwardPrefix_preserves_A L s k k
    have hskB : sk (L.B k) = s (L.B k) := andForwardPrefix_preserves_B L s k k
    have hskG : sk (L.G k) = carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) k :=
      hC k (le_refl k)
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [hsplit, denote_append, ← hskdef]
      by_cases hik : i = k + 1
      · subst hik
        simp only [andForwardSlice]
        rw [hcarry, hskA, hskB, hskG]
        rfl
      · have hiG : L.G i ≠ L.G (k + 1) := fun h =>
          hik (L.hGinj i (k + 1) (by omega) (by omega) h)
        rw [andForwardSlice_preserves L sk k hiG, hC i (by omega)]
    · intro i hik hin
      rw [hsplit, denote_append, ← hskdef]
      have hiG : L.G i ≠ L.G (k + 1) := fun h =>
        (by omega : i ≠ k + 1) (L.hGinj i (k + 1) (by omega) (by omega) h)
      rw [andForwardSlice_preserves L sk k hiG, hU i (by omega) hin]

/-! ### Sum-pass value invariant -/

/-- The sum slice for bit `k` preserves any wire other than its single target `S k`. -/
theorem andSumSlice_preserves (L : AndAddLayout m n) (u : State m) (k : ℕ) {w : Fin m}
    (hw : w ≠ L.S k) : denote (andSumSlice L k) u w = u w := by
  apply denote_apply_of_forall_not_mem_target
  intro g hg hmem
  exact hw (andSumSlice_target hg hmem)

/-- **Single sum slice.** `S i ← S i ⊕ A i ⊕ B i ⊕ G i` (the inputs are pure controls). -/
theorem andSumSlice_correct (L : AndAddLayout m n) (u : State m) (k : ℕ) :
    denote (andSumSlice L k) u (L.S k)
      = (u (L.S k) ^^ u (L.A k) ^^ u (L.B k) ^^ u (L.G k)) := by
  have hAS' : L.A k ≠ L.S k := L.hAS k k
  have hBS' : L.B k ≠ L.S k := L.hBS k k
  have hGS' : L.G k ≠ L.S k := (L.hSG k k).symm
  simp only [andSumSlice, denote_cons, denote_nil, denoteGate, if_neg hAS', if_neg hBS', if_neg hGS',
    Function.update_apply]
  simp_all
  cases u (L.S k) <;> cases u (L.A k) <;> cases u (L.B k) <;> cases u (L.G k) <;> simp_all

/-- **Sum-pass value invariant.** After the first `k` sum slices, the processed sum wires (`i < k`)
carry `S i ⊕ A i ⊕ B i ⊕ G i`, and the unprocessed ones (`k ≤ i < n`) are unchanged. By induction on
`k`, each step a single `andSumSlice` writing only `S k`. -/
theorem andSum_value (L : AndAddLayout m n) (t : State m) :
    ∀ k, k ≤ n →
      (∀ i, i < k → denote (andSumPrefix L k) t (L.S i)
          = (t (L.S i) ^^ t (L.A i) ^^ t (L.B i) ^^ t (L.G i)))
      ∧ (∀ i, k ≤ i → i < n → denote (andSumPrefix L k) t (L.S i) = t (L.S i)) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨fun i hi => absurd hi (Nat.not_lt_zero i), fun i _ _ => by simp [andSumPrefix]⟩
  | succ k ih =>
    intro hk
    have hkn : k ≤ n := Nat.le_of_succ_le hk
    have hkltn : k < n := hk
    obtain ⟨hC, hU⟩ := ih hkn
    have hsplit : andSumPrefix L (k + 1) = andSumPrefix L k ++ andSumSlice L k := by
      simp [andSumPrefix, List.range_succ, List.flatMap_append]
    set u := denote (andSumPrefix L k) t with hudef
    -- the prefix preserves A, B, G (targets are all S wires)
    have hpres : ∀ w : Fin m, (∀ i, i < k → w ≠ L.S i) → u w = t w := by
      intro w hw; exact andSumPrefix_preserves_of_ne_S L t k hw
    have huA : u (L.A k) = t (L.A k) := hpres _ (fun i _ => L.hAS k i)
    have huB : u (L.B k) = t (L.B k) := hpres _ (fun i _ => L.hBS k i)
    have huG : u (L.G k) = t (L.G k) := hpres _ (fun i _ => (L.hSG i k).symm)
    have huS : u (L.S k) = t (L.S k) := hU k (le_refl k) hkltn
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [hsplit, denote_append, ← hudef]
      by_cases hik : i = k
      · subst hik
        rw [andSumSlice_correct, huA, huB, huG, huS]
      · have hiS : L.S i ≠ L.S k := fun h =>
          hik (L.hSinj i k (by omega) hkltn h)
        rw [andSumSlice_preserves L u k hiS, hC i (by omega)]
    · intro i hik hin
      rw [hsplit, denote_append, ← hudef]
      have hiS : L.S i ≠ L.S k := fun h => (by omega : i ≠ k) (L.hSinj i k hin hkltn h)
      rw [andSumSlice_preserves L u k hiS, hU i (by omega) hin]

/-! ### Per-bit value of the full adder -/

/-- **Per-bit sum value.** Bit `k` of the sum register holds `A k ⊕ B k ⊕ carry k`. The uncompute pass
(`inverse andForward`) only touches `G` wires, so `S k` is the value written by `andSumPass` over the
forward-completed carries. -/
theorem andAdd_sum_bit (L : AndAddLayout m n) (s : State m)
    (hG0 : ∀ j, s (L.G j) = false) (hS0 : ∀ i, s (L.S i) = false) (k : ℕ) (hk : k < n) :
    denote (andAdd L) s (L.S k)
      = (s (L.A k) ^^ s (L.B k)
          ^^ carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) k) := by
  rw [andAdd, denote_append, denote_append]
  set t := denote (andForward L) s with htdef
  -- the uncompute pass preserves S k (it only writes G wires)
  have hinvS : denote (inverse (andForward L)) (denote (andSumPass L) t) (L.S k)
      = denote (andSumPass L) t (L.S k) := by
    apply denote_apply_of_forall_not_mem_target
    intro g hg hmem
    rw [inverse, List.mem_reverse] at hg
    obtain ⟨j, _, hgj⟩ := mem_andForwardPrefix hg
    exact L.hSG k (j + 1) (andForwardSlice_target hgj hmem)
  rw [hinvS]
  -- value of the sum pass at S k
  obtain ⟨hSC, _⟩ := andSum_value L t n (le_refl n)
  rw [andSumPass, hSC k hk]
  -- t = forward of s: S, A, B preserved; G k = carry k
  have htS : t (L.S k) = false := by rw [htdef, andForward, andForwardPrefix_preserves_S]; exact hS0 k
  have htA : t (L.A k) = s (L.A k) := by rw [htdef, andForward, andForwardPrefix_preserves_A]
  have htB : t (L.B k) = s (L.B k) := by rw [htdef, andForward, andForwardPrefix_preserves_B]
  have htG : t (L.G k) = carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) k := by
    rw [htdef, andForward]; exact (andForward_carry L s hG0 n (le_refl n)).1 k (by omega)
  rw [htS, htA, htB, htG]
  simp

/-! ### Headline theorems -/

/-- **AND-based ripple-adder correctness.** For a disjoint-wire layout with all carry ancillas and the
sum register initialised `false`, the sum register ends holding `(A + B) mod 2 ^ n`. The carries are
computed into fresh ancillas (`andForward`), the sums written (`andSumPass`), and the carries
uncomputed (`inverse andForward`); the value is read off the exhibited circuit, not postulated. -/
theorem andAdd_correct (L : AndAddLayout m n) (s : State m)
    (hG0 : ∀ j, s (L.G j) = false) (hS0 : ∀ i, s (L.S i) = false) :
    regValRange L.S (denote (andAdd L) s) n
      = (regValRange L.A s n + regValRange L.B s n) % 2 ^ n := by
  have hbit : regValRange L.S (denote (andAdd L) s) n
      = ∑ i ∈ Finset.range n,
          (s (L.A i) ^^ s (L.B i)
            ^^ carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) i).toNat * 2 ^ i := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [andAdd_sum_bit L s hG0 hS0 i hi]
  -- arithmetic: combine the per-bit sum with the carry identity
  have hid := adder_sum_identity (fun i => s (L.A i)) (fun i => s (L.B i)) n
  have hcombine : regValRange L.S (denote (andAdd L) s) n
      + (carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) n).toNat * 2 ^ n
      = regValRange L.A s n + regValRange L.B s n := by
    rw [hbit]; exact hid
  have hlt : regValRange L.S (denote (andAdd L) s) n < 2 ^ n := regValRange_lt _ _ _
  set vS := regValRange L.S (denote (andAdd L) s) n
  set vA := regValRange L.A s n
  set vB := regValRange L.B s n
  cases hc : carryOf (fun i => s (L.A i)) (fun i => s (L.B i)) n
  · simp only [hc, Bool.toNat_false, zero_mul, add_zero] at hcombine
    rw [← hcombine, Nat.mod_eq_of_lt hlt]
  · simp only [hc, Bool.toNat_true, one_mul] at hcombine
    rw [← hcombine, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]

/-- **Ancilla-clean: every fresh carry-AND ancilla returns to `false`.** The reverse pass
`inverse (andForward L)` uncomputes every carry: the sum pass leaves the addend / carry wires
untouched (`denote_agree_on`), so the reverse pass undoes the forward pass on the `G` chain exactly
(`reversible_inverse_correct`). This is the explicit AND-uncompute working — the property a
measurement-based gadget must reproduce. -/
theorem andAdd_ancilla_clean (L : AndAddLayout m n) (s : State m) (hG0 : ∀ j, s (L.G j) = false)
    (j : ℕ) : denote (andAdd L) s (L.G j) = false := by
  rw [andAdd, denote_append, denote_append]
  set t := denote (andForward L) s with htdef
  -- P-wires: those that are not sum wires
  have hagree : denote (inverse (andForward L)) (denote (andSumPass L) t) (L.G j)
      = denote (inverse (andForward L)) t (L.G j) := by
    refine denote_agree_on (P := fun w => ∀ i, i < n → w ≠ L.S i) (inverse (andForward L))
      ?_ ?_ (L.G j) ?_
    · -- every wire of the uncompute pass is a non-S wire
      intro g hg w hw
      rw [inverse, List.mem_reverse] at hg
      obtain ⟨jj, _, hgj⟩ := mem_andForwardPrefix hg
      intro i _ heq
      rcases andForwardSlice_wires hgj hw with h | h | h | h
      · exact L.hAS jj i (h.symm.trans heq)
      · exact L.hBS jj i (h.symm.trans heq)
      · exact L.hSG i jj (heq.symm.trans h)
      · exact L.hSG i (jj + 1) (heq.symm.trans h)
    · -- the sum pass preserves non-S wires
      intro w hwP
      exact andSumPrefix_preserves_of_ne_S L t n (fun i hi => hwP i hi)
    · -- G j is a non-S wire
      intro i _ heq; exact L.hSG i j heq.symm
  rw [hagree, htdef, reversible_inverse_correct]
  exact hG0 j

/-! ### Derived cost: 6n Toffolis (3n compute + 3n uncompute) -/

theorem andForwardPrefix_toffoli (L : AndAddLayout m n) (k : ℕ) :
    (circuitCost (andForwardPrefix L k)).toffoli = 3 * k := by
  induction k with
  | zero => simp [andForwardPrefix, circuitCost]
  | succ k ih =>
    have hsplit : andForwardPrefix L (k + 1)
        = andForwardPrefix L k ++ andForwardSlice L k := by
      simp [andForwardPrefix, List.range_succ, List.flatMap_append]
    rw [hsplit, cost_comp_toffoli_count, ih, andForwardSlice, andCarryCell_toffoli]
    omega

theorem andSumPrefix_toffoli (L : AndAddLayout m n) (k : ℕ) :
    (circuitCost (andSumPrefix L k)).toffoli = 0 := by
  induction k with
  | zero => simp [andSumPrefix, circuitCost]
  | succ k ih =>
    have hsplit : andSumPrefix L (k + 1) = andSumPrefix L k ++ andSumSlice L k := by
      simp [andSumPrefix, List.range_succ, List.flatMap_append]
    rw [hsplit, cost_comp_toffoli_count, ih, andSumSlice]
    simp [circuitCost, gateCost]

/-- **The uncompute half is `3 * n` Toffolis** — the AND-uncompute cost a measurement-based gadget
would eliminate (the ~2× saving target for L5-d). It equals the compute half (`andForward`,
`3 * n`) by `cost_inverse_toffoli`. -/
theorem andAdd_uncompute_toffoli (L : AndAddLayout m n) :
    (circuitCost (inverse (andForward L))).toffoli = 3 * n := by
  rw [cost_inverse_toffoli, andForward, andForwardPrefix_toffoli]

/-- **Derived Toffoli cost: `6 * n`.** `3 * n` compute-AND Toffolis (`andForward`) `+` `3 * n`
uncompute-AND Toffolis (`inverse andForward`); the sum pass is CNOT-only. The uncompute `3 * n`
(`andAdd_uncompute_toffoli`) is exactly what the measurement route saves. -/
theorem andAdd_toffoli (L : AndAddLayout m n) :
    (circuitCost (andAdd L)).toffoli = 6 * n := by
  rw [andAdd, cost_comp_toffoli_count, cost_comp_toffoli_count, andForward, andSumPass,
    andForwardPrefix_toffoli, andSumPrefix_toffoli, cost_inverse_toffoli, andForwardPrefix_toffoli]
  omega

/-! ### Non-vacuity witness + `#eval` cross-check

A concrete 2-bit AND-based adder layout on `Fin 9`: `A → {0,1}`, `B → {2,3}`, `S → {4,5}`, carry chain
`G → {6,7,8}`. The headlines apply, and the strict `Array` evaluator `runArr` (bridge
`regValRangeArr_eq`) witnesses `2 + 3 = 5`, the sum register reading `5` and every carry ancilla
returning `false`. -/

/-- A concrete 2-bit AND-based adder layout on `Fin 9`. -/
def andAddLayout2 : AndAddLayout 9 2 where
  A i := if i = 0 then 0 else 1
  B i := if i = 0 then 2 else 3
  S i := if i = 0 then 4 else 5
  G i := if i = 0 then 6 else if i = 1 then 7 else 8
  hAB i j := by split_ifs <;> decide
  hAS i j := by split_ifs <;> decide
  hAG i j := by split_ifs <;> decide
  hBS i j := by split_ifs <;> decide
  hBG i j := by split_ifs <;> decide
  hSG i j := by split_ifs <;> decide
  hSinj i j hi hj h := by split_ifs at h <;> omega
  hGinj i j hi hj h := by split_ifs at h <;> omega

/-- The headlines are non-vacuous: they apply to `andAddLayout2`. -/
example (s : State 9) (hG0 : ∀ j, s (andAddLayout2.G j) = false)
    (hS0 : ∀ i, s (andAddLayout2.S i) = false) :
    regValRange andAddLayout2.S (denote (andAdd andAddLayout2) s) 2
      = (regValRange andAddLayout2.A s 2 + regValRange andAddLayout2.B s 2) % 2 ^ 2 :=
  andAdd_correct andAddLayout2 s hG0 hS0

/-- Witness: `A = 2` (wires `0,1 = 0,1`), `B = 3` (wires `2,3 = 1,1`), `S`/`G` init `false`. -/
def andAddWitness2 : State 9 := ![false, true, true, true, false, false, false, false, false]

-- `S ← 2 + 3 = 5`. Fast `Array`-backed run, read off register `S` (low 2 bits). Prints `1` (= 5 mod 4).
#eval regValRangeArr andAddLayout2.S
  (runArr (andAdd andAddLayout2) (ofState andAddWitness2)) 2
-- 1

-- Every carry ancilla clean: reads `false`.
#eval (runArr (andAdd andAddLayout2) (ofState andAddWitness2))[andAddLayout2.G 0 |>.val]!
-- false
#eval (runArr (andAdd andAddLayout2) (ofState andAddWitness2))[andAddLayout2.G 1 |>.val]!
-- false
#eval (runArr (andAdd andAddLayout2) (ofState andAddWitness2))[andAddLayout2.G 2 |>.val]!
-- false

-- Theorem-independent value check via the proven `runArr` bridge: `S` reads `1 = 5 mod 4`.
-- (An `example := by decide` value-check stood here; kernel `decide` cannot reduce this cross-module
-- `Array` circuit under the Lean 4 module system. The `#eval` above exhibits the value; the
-- `runArr`/`regValRange` correctness bridge is proven separately.)

end Reversible
