/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModReduceCtrl

/-!
# Fast `#eval`-able reversible-circuit evaluation — the `Array Bool` bridge  (ECDLP testing infra)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate). **This is testing
infrastructure, not part of the ECDLP cost / correctness claims.**

## Purpose

A strict `Array Bool`-backed evaluator (`runArr`) for `Reversible.Circuit`, with a **proven bridge**
(`runArr_apply`, `regValRangeArr_eq`) to the reference `denote` semantics. The point is fast,
*theorem-independent* value cross-checks: `#eval`-ing `runArr` / `regValRangeArr` on a concrete
circuit witness produces a number that is **certified equal** (by the bridge lemmas) to the
`denote` / `regValRange` value the correctness theorems are stated about. So the `#eval` checks the
*real* `denote`-based semantics, not a separate evaluator.

## The pathology it fixes

The reference state is `State n := Fin n → Bool` and `denoteGate` uses `Function.update` (and, for
`swap`, `Equiv.swap`). Under `#eval` / `native_decide` these are **lazy**: reading one final-wire bit
of `denote c s` re-reads the inner state through the whole gate history. A `CCX` reads 3 bits, so a
single final-bit read recurses `3 ^ depth` through the fold — exponential blowup. On the `Fin 27`,
61-gate `cModAdd` circuit this hangs.

`runArr` represents the state as a strict `Array Bool`: each gate is O(1) array work
(`Array.set!` / `Array.getElem!`), the whole run is O(gates), no re-reads. It evaluates instantly.

## The bridge

* `applyGate_apply` — the step lemma: `applyGate g a` matches `denoteGate g s` wire-for-wire, given
  `a` represents `s` (`a.size = m` and `∀ j, a[j]! = s j`), and preserves the representation.
* `runArr_apply` — **headline:** `(runArr c (ofState s))[i]! = denote c s i` for all `i`. Induction
  on `c`, maintaining the representation invariant; `ofState` seeds it via `Array.getElem_ofFn`.
* `regValRangeArr_eq` — the consumer-facing bridge:
  `regValRangeArr f (runArr c (ofState s)) k = regValRange f (denote c s) k` (a `Finset.sum_congr`
  over `runArr_apply`). So `#eval regValRangeArr f (runArr c (ofState s)) k` is a fast number,
  *equal to* the `regValRange f (denote c s) k` of the correctness theorems.

`runArr_apply` and `regValRangeArr_eq` are pure structural / arithmetic proofs (foundational triple
only); no `native_decide` appears in any proven lemma. The demonstration `example`s below use
`decide` / `rfl` on small witnesses to exhibit a green, fast, theorem-independent value check.
-/

namespace Reversible

variable {m : ℕ}

/-! ### The strict `Array Bool` evaluator -/

/-- A single gate's action on a strict `Array Bool` state. Each gate is O(1) array work
(`Array.getElem!` / `Array.set!`). Degenerate forms (control = target) act as the identity, mirroring
`denoteGate`. Out-of-bounds indices are inert (`set!` = `setIfInBounds`); on a size-`m` array indexed
by `Fin m` every access is in bounds, which is what the bridge lemmas assume. -/
def applyGate (g : Gate m) (a : Array Bool) : Array Bool :=
  match g with
  | .X i => a.set! i.val (! a[i.val]!)
  | .CX c t => if c = t then a else a.set! t.val (a[c.val]! ^^ a[t.val]!)
  | .CCX c₁ c₂ t =>
      if t = c₁ ∨ t = c₂ then a else a.set! t.val (a[t.val]! ^^ (a[c₁.val]! && a[c₂.val]!))
  | .swap i j => let vi := a[i.val]!; let vj := a[j.val]!; (a.set! i.val vj).set! j.val vi

/-- Run a circuit on a strict `Array Bool` state (fold `applyGate` over the gate list). O(gates). -/
def runArr (c : Circuit m) (a : Array Bool) : Array Bool :=
  c.foldl (fun a g => applyGate g a) a

/-- Seed the array representation of a `State m`. `(ofState s).size = m` and `(ofState s)[j]! = s j`. -/
def ofState (s : State m) : Array Bool := Array.ofFn s

@[simp] theorem ofState_size (s : State m) : (ofState s).size = m := by
  simp [ofState]

/-- The seed array represents its source state: `(ofState s)[j]! = s j`. -/
theorem ofState_getElem! (s : State m) (j : Fin m) : (ofState s)[j.val]! = s j := by
  have hlt : j.val < (ofState s).size := by simp
  rw [getElem!_pos (ofState s) j.val hlt]
  simp only [ofState, Array.getElem_ofFn]

/-! ### The representation predicate and the bridge -/

/-- `a` represents the `State m` `s`: it has the right size and agrees with `s` on every wire. The
invariant maintained by `applyGate` / `runArr`. -/
def Represents (a : Array Bool) (s : State m) : Prop :=
  a.size = m ∧ ∀ j : Fin m, a[j.val]! = s j

theorem ofState_represents (s : State m) : Represents (ofState s) s :=
  ⟨ofState_size s, ofState_getElem! s⟩

/-- `applyGate` preserves array size. -/
@[simp] theorem applyGate_size (g : Gate m) (a : Array Bool) : (applyGate g a).size = a.size := by
  cases g <;> simp [applyGate] <;> split <;> simp

/-! Local `getElem!`-only rewrite lemmas for `set!` (= `setIfInBounds`). Stated purely in
`Array.getElem!` to keep proof terms term-independent (the dependent `getElem` bounds proof breaks
`rw`). Both route `a[i]!` through `a[i]?` via `Array.getElem!_eq_getD`. -/

/-- Updating in bounds, then reading the updated index: `(a.set! i v)[i]! = v` for `i < a.size`. -/
private theorem getElem!_set!_self {a : Array Bool} {i : ℕ} {v : Bool} (h : i < a.size) :
    (a.set! i v)[i]! = v := by
  rw [Array.getElem!_eq_getD, Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_self_of_lt h, Option.getD_some]

/-- Updating index `i`, then reading a different index `j`: `(a.set! i v)[j]! = a[j]!`. -/
private theorem getElem!_set!_ne {a : Array Bool} {i j : ℕ} {v : Bool} (h : i ≠ j) :
    (a.set! i v)[j]! = a[j]! := by
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD, Array.set!_eq_setIfInBounds,
    Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne h]

/-- **The step lemma.** If `a` represents `s`, then `applyGate g a` represents `denoteGate g s`:
the size is preserved and `(applyGate g a)[i]! = denoteGate g s i` wire-for-wire. Cased on `g`;
each case is `Array.set!` (= `setIfInBounds`) reasoning matched against `Function.update` /
`Equiv.swap`. -/
theorem applyGate_apply (g : Gate m) {a : Array Bool} {s : State m} (h : Represents a s) :
    Represents (applyGate g a) (denoteGate g s) := by
  obtain ⟨hsize, hget⟩ := h
  refine ⟨by simp [hsize], ?_⟩
  intro i
  cases g with
  | X k =>
    -- result array = a.set! k (! a[k]!)
    simp only [applyGate, denoteGate]
    by_cases hik : i = k
    · subst hik
      rw [getElem!_set!_self (by rw [hsize]; exact i.2), hget i, Function.update_self]
    · have hik' : k.val ≠ i.val := fun h => hik (Fin.ext h.symm)
      rw [getElem!_set!_ne hik', hget i, Function.update_of_ne hik]
  | CX c t =>
    by_cases hct : c = t
    · simp only [applyGate, denoteGate, if_pos hct]; rw [hget i]
    · simp only [applyGate, denoteGate, if_neg hct]
      by_cases hit : i = t
      · subst hit
        rw [getElem!_set!_self (by rw [hsize]; exact i.2), hget c, hget i, Function.update_self]
      · have hit' : t.val ≠ i.val := fun h => hit (Fin.ext h.symm)
        rw [getElem!_set!_ne hit', hget i, Function.update_of_ne hit]
  | CCX c₁ c₂ t =>
    by_cases hguard : t = c₁ ∨ t = c₂
    · simp only [applyGate, denoteGate, if_pos hguard]; rw [hget i]
    · simp only [applyGate, denoteGate, if_neg hguard]
      by_cases hit : i = t
      · subst hit
        rw [getElem!_set!_self (by rw [hsize]; exact i.2), hget i, hget c₁, hget c₂,
          Function.update_self]
      · have hit' : t.val ≠ i.val := fun h => hit (Fin.ext h.symm)
        rw [getElem!_set!_ne hit', hget i, Function.update_of_ne hit]
  | swap p q =>
    -- result = (a.set! p vq).set! q vp ; denoteGate (.swap p q) s i = s (Equiv.swap p q i)
    simp only [applyGate, denoteGate, Function.comp_apply]
    have hsz1 : (a.set! p.val a[q.val]!).size = m := by
      rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hsize]
    by_cases hiq : i = q
    · subst hiq
      rw [getElem!_set!_self (hsz1.symm ▸ i.2), hget p, Equiv.swap_apply_right]
    · have hiq' : q.val ≠ i.val := fun h => hiq (Fin.ext h.symm)
      rw [getElem!_set!_ne hiq']
      by_cases hip : i = p
      · subst hip
        rw [getElem!_set!_self (hsize.symm ▸ i.2), hget q, Equiv.swap_apply_left]
      · have hip' : p.val ≠ i.val := fun h => hip (Fin.ext h.symm)
        rw [getElem!_set!_ne hip', hget i, Equiv.swap_apply_of_ne_of_ne hip hiq]

/-- `runArr` preserves the representation invariant (fold of `applyGate_apply`). -/
theorem runArr_represents (c : Circuit m) {a : Array Bool} {s : State m} (h : Represents a s) :
    Represents (runArr c a) (denote c s) := by
  induction c generalizing a s with
  | nil => simpa [runArr, denote] using h
  | cons g rest ih =>
    rw [runArr, List.foldl_cons, ← runArr, denote_cons]
    exact ih (applyGate_apply g h)

/-- **Bridge headline.** The strict `Array Bool` run of a circuit on `ofState s` reproduces the
reference `denote` semantics wire-for-wire: `(runArr c (ofState s))[i]! = denote c s i`. So an `#eval`
of `runArr` is a faithful, fast computation of `denote`. -/
theorem runArr_apply (c : Circuit m) (s : State m) (i : Fin m) :
    (runArr c (ofState s))[i.val]! = denote c s i :=
  (runArr_represents c (ofState_represents s)).2 i

/-! ### The register-value bridge (`regValRange`) -/

/-- Place-value readout of the low `k` bits of a register laid out on wires `f i`, read off a strict
`Array Bool` state. The `Array`-backed counterpart of `regValRange`. -/
def regValRangeArr (f : ℕ → Fin m) (a : Array Bool) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, (a[(f i).val]!).toNat * 2 ^ i

/-- **Consumer-facing bridge.** The fast `Array`-backed register read equals the reference
`regValRange` of the `denote` semantics. Hence `#eval regValRangeArr f (runArr c (ofState s)) k` is a
fast number, *certified equal* to the `regValRange f (denote c s) k` the correctness theorems use. -/
theorem regValRangeArr_eq (f : ℕ → Fin m) (c : Circuit m) (s : State m) (k : ℕ) :
    regValRangeArr f (runArr c (ofState s)) k = regValRange f (denote c s) k := by
  unfold regValRangeArr regValRange
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [runArr_apply]

/-! ### Demonstration: a green, fast, theorem-independent value cross-check

The `Fin m` `denote` evaluator blows up under `#eval` on a many-gate circuit (lazy `Function.update`
re-reads, exponential in depth). `runArr` evaluates instantly. The witness is the S6.3a 2-bit
reducer `modReduceLayout2 : ModReduceLayout 13 2` at the `x = 3 ↦ 0` subtract-branch state.

The `#eval` prints the fast `Array`-backed value; the `example` confirms — fast, via `decide` — that
the `Array`-backed register read equals that number; and `regValRangeArr_eq` certifies that this same
number is the `regValRange (denote …)` of `modReduce_correct`. -/

-- Fast `Array`-backed run of the full reduce circuit, read off register `B` (low 2 bits): the
-- `x = 3 ↦ 3 mod 3 = 0` subtract branch. Prints `0`, instantly.
#eval regValRangeArr modReduceLayout2.B
  (runArr (modReduce modReduceLayout2) (ofState (modReduceState2 true true))) 2
-- 0

-- The `x = 2 ↦ 2 mod 3 = 2` identity branch. Prints `2`, instantly.
#eval regValRangeArr modReduceLayout2.B
  (runArr (modReduce modReduceLayout2) (ofState (modReduceState2 false true))) 2
-- 2

-- Green, fast, theorem-independent value check: the `Array`-backed register read is `0`, by
-- `decide` (kernel-reduced, no `ofReduceBool`; the strict `Array` evaluator has no lazy
-- `Function.update` re-reads, so the reduction is O(gates)). The `maxRecDepth` bump covers the
-- elaborator's recursion through the gate-list `foldl`, not any exponential blowup: the same
-- computation through `denote` is exponentially slow even with the bump.
set_option maxRecDepth 4000 in
example : regValRangeArr modReduceLayout2.B
    (runArr (modReduce modReduceLayout2) (ofState (modReduceState2 true true))) 2 = 0 := by
  decide

-- The `x = 2 ↦ 2 mod 3 = 2` identity branch: the `Array`-backed read is `2`, by `decide`.
set_option maxRecDepth 4000 in
example : regValRangeArr modReduceLayout2.B
    (runArr (modReduce modReduceLayout2) (ofState (modReduceState2 false true))) 2 = 2 := by
  decide

/-- The cross-check is faithful to the real `denote`-based theorem: by `regValRangeArr_eq`, the fast
`Array` value (`0`, above) *is* the `regValRange (denote …)` quantity that `modReduce_correct`
constrains. This `example` exhibits the bridge instantiated at the witness. -/
example : regValRangeArr modReduceLayout2.B
    (runArr (modReduce modReduceLayout2) (ofState (modReduceState2 true true))) 2
      = regValRange modReduceLayout2.B (denote (modReduce modReduceLayout2)
        (modReduceState2 true true)) 2 :=
  regValRangeArr_eq modReduceLayout2.B (modReduce modReduceLayout2) (modReduceState2 true true) 2

end Reversible
