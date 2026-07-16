import CsdLean4.Mathlib.QuantumInfo.Reversible.CuccaroAdd
import CsdLean4.Mathlib.QuantumInfo.ECDLP.SafegcdDivstep

/-!
# The value-faithful safegcd divstep circuit — TRANCHE 1: the exact-halving gadget  (ECDLP L6, #36c-2)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

This module opens the deferred residue named in `SafegcdInversion.lean` and `SafegcdDivstep.lean`:
the **reversible BIT-CIRCUIT whose denotation equals `ECDLP.Safegcd.divstep`**. The existing
`ResourceBounds.divstepProxyGadget` is a COST proxy — its `denote` computes *modular* arithmetic, not
the integer divstep — so `divstepToffoli` is cost-backed but the value is not circuit-backed. Building
the value-faithful circuit is a multi-tranche task (there is no signed-integer register layer yet); this
module is **tranche 1**.

## The divstep's three register updates, and which one this tranche builds

One `divstep (δ,f,g) ↦ (δ',f',g')` (with `f` kept ODD) does, on the `(f,g)` registers:

* a **branch-conditional swap** `f ↔ g` (the `δ>0 ∧ g` odd branch sets `f' = g`);
* an **integer combination** `g ± f` (forming the even numerator `g-f` or `g+f`);
* an **exact halving** `↦ /2` of that even numerator (or of `g` itself when `g` is even).

**This tranche builds the exact halving** — the divstep-specific primitive, and the one provable on the
EXISTING natural-number register decoder (`Reversible.regValRange`): every divstep halving is of an
*even* register (the numerator is even in each branch, `divstep_gcd`'s per-branch `Odd.sub_odd` /
`Odd.add_odd` / `Even`), so its magnitude alone determines the result and no signed decoding is needed
here. Signed subtraction (tranche 2) and conditional swap + branch routing (tranche 3), then the
assembly `denote = divstepRev` (tranche 4), are the remaining tranches.

## What tranche 1 proves (genuine, `denote`-level, general `n`)

* `shiftDown` — a concrete `Circuit` of `n` `swap` gates that bubbles the bottom bit to the top, i.e.
  moves every bit down one place (`shiftDown_apply_lt` / `shiftDown_apply_top`).
* `halve_correct` — **the value identity**: for an EVEN register (bottom bit `false`), the shifted
  register decodes to `regValRange F s (n+1) / 2`. So `denote (shiftDown F n)` genuinely computes `÷2`.
* `shiftDown_toffoli` — the halving is **Toffoli-free** (`0` Toffolis; pure wire permutation, `3n`
  CNOTs). This REFINES the `divstepToffoli` cost model: its `cuccaroModDouble` proxy charged `6n+4`
  Toffolis for the halving, an OVERCOUNT — the real halving carries no Toffoli cost. The divstep's
  Toffoli cost lives entirely in the subtraction / cofactor track, not the shift.

The halving is exact and reversible on the even-register domain because the discarded bottom bit is
known `false`; the general (parity-carrying) halving keeps that bit as the divstep's history garbage —
the reversibility already isolated by `SafegcdDivstep.divstepRev_injective`.

References: `specs/active-todo.md` (#36c option 2), `SafegcdInversion.lean`
(`divstepProxyGadget`, the cost proxy this value-completes), `SafegcdDivstep.lean` (`divstep`,
`divstepRev`, `divstepRev_injective`), `Reversible/CuccaroAdd.lean` (`regValRange`, `regValRange_succ'`).
-/

namespace ECDLP.Safegcd.Circuit

open Reversible

variable {m : ℕ}

/-! ### The shift-down (halving) circuit -/

/-- **The shift-down swap chain** on the register laid out at wires `F 0, …, F n`. It is the forward
chain `swap (F 0)(F 1) ; swap (F 1)(F 2) ; … ; swap (F (n-1))(F n)` (here indexed by the number of
swaps `n`, for an `(n+1)`-bit register). Applied left to right it bubbles the bottom bit up to the top
wire and moves every other bit DOWN one place — an arithmetic right shift (`halve_correct`). -/
def shiftDown (F : ℕ → Fin m) : ℕ → Circuit m
  | 0 => []
  | k + 1 => shiftDown F k ++ [.swap (F k) (F (k + 1))]

/-- The shift-down circuit is Toffoli-free (all `swap` gates). -/
theorem shiftDown_toffoli (F : ℕ → Fin m) (n : ℕ) :
    (circuitCost (shiftDown F n)).toffoli = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [shiftDown, cost_comp_toffoli_count, ih]
    rfl

/-- **Wire action of the shift chain (the induction core).** For an injective layout `F`, after the
`k`-swap chain: every position `i < k` holds the old bit `i+1` (shifted down), position `k` holds the
old bottom bit `0` (bubbled up), and every position `i > k` is untouched. Proved by induction on `k`;
each step is one `swap` composed on top, resolved by injectivity of `F`. -/
theorem shiftDown_wire (F : ℕ → Fin m) (hF : Function.Injective F) (s : State m) (k : ℕ) :
    (∀ i, i < k → denote (shiftDown F k) s (F i) = s (F (i + 1)))
      ∧ denote (shiftDown F k) s (F k) = s (F 0)
      ∧ (∀ i, k < i → denote (shiftDown F k) s (F i) = s (F i)) := by
  induction k with
  | zero =>
    refine ⟨by omega, rfl, ?_⟩
    intro i _; rfl
  | succ k ih =>
    obtain ⟨ihA, ihB, ihC⟩ := ih
    -- One more swap on top of the k-chain (stated pointwise so rewrites land cleanly).
    have hstep : ∀ w, denote (shiftDown F (k + 1)) s w
        = denote (shiftDown F k) s (Equiv.swap (F k) (F (k + 1)) w) := by
      intro w
      rw [shiftDown, denote_append]
      rfl
    have hne : F k ≠ F (k + 1) := fun h => by have := hF h; omega
    refine ⟨?_, ?_, ?_⟩
    · -- positions i < k+1
      intro i hi
      rw [hstep]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · -- i < k : untouched by the top swap, then IH (A)
        have h1 : F i ≠ F k := fun h => by have := hF h; omega
        have h2 : F i ≠ F (k + 1) := fun h => by have := hF h; omega
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
        exact ihA i hlt
      · -- i = k : the swap sends F k ↦ F (k+1), which IH (C) leaves at s (F (k+1))
        subst heq
        rw [Equiv.swap_apply_left]
        exact ihC (i + 1) (by omega)
    · -- position k+1 : the swap sends F (k+1) ↦ F k, which IH (B) sends to s (F 0)
      rw [hstep, Equiv.swap_apply_right]
      exact ihB
    · -- positions i > k+1 : untouched by the top swap, then IH (C)
      intro i hi
      rw [hstep]
      have h1 : F i ≠ F k := fun h => by have := hF h; omega
      have h2 : F i ≠ F (k + 1) := fun h => by have := hF h; omega
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      exact ihC i (by omega)

/-- Every position `i < n` of the shifted register holds the old bit `i + 1` (shifted down one place). -/
theorem shiftDown_apply_lt (F : ℕ → Fin m) (hF : Function.Injective F) (s : State m)
    {n i : ℕ} (hi : i < n) : denote (shiftDown F n) s (F i) = s (F (i + 1)) :=
  (shiftDown_wire F hF s n).1 i hi

/-- The top position `n` of the shifted register holds the old bottom bit (`0`). -/
theorem shiftDown_apply_top (F : ℕ → Fin m) (hF : Function.Injective F) (s : State m) (n : ℕ) :
    denote (shiftDown F n) s (F n) = s (F 0) :=
  (shiftDown_wire F hF s n).2.1

/-! ### The halving value identity -/

/-- **Exact halving of an EVEN register.** If the bottom bit is `false` (the value is even), the
shift-down circuit computes exactly `÷2`: the `(n+1)`-bit register decodes to `regValRange F s (n+1) / 2`.

This is the divstep's third register update on a value-faithful circuit (general `n`, `denote`-level):
each divstep halving is of an even numerator, so this discharges the halving primitive. Proof: the
shifted register's low `n` bits are the old bits `1..n` (`shiftDown_apply_lt`), i.e.
`regValRange (F ∘ (·+1)) s n`, and the top bit is the old bottom bit `= 0`; `regValRange_succ'` gives
`regValRange F s (n+1) = 0 + 2 · regValRange (F ∘ (·+1)) s n`, so the shifted value is exactly the half. -/
theorem halve_correct (F : ℕ → Fin m) (hF : Function.Injective F) (s : State m) (n : ℕ)
    (hbot : s (F 0) = false) :
    regValRange F (denote (shiftDown F n) s) (n + 1) = regValRange F s (n + 1) / 2 := by
  set t := denote (shiftDown F n) s with ht
  -- The shifted low-n block equals the old shifted-by-one register.
  have hlow : regValRange F t n = regValRange (fun i => F (i + 1)) s n := by
    unfold regValRange
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [ht, shiftDown_apply_lt F hF s hi]
  -- The top bit is the old bottom bit, which is false.
  have htop : t (F n) = false := by rw [ht, shiftDown_apply_top F hF s n, hbot]
  -- Assemble the shifted value: only the low-n block survives.
  have hval : regValRange F t (n + 1) = regValRange (fun i => F (i + 1)) s n := by
    rw [regValRange_succ, htop, hlow]; simp
  -- The source value is twice its shifted-by-one register (bottom bit false).
  have hsrc : regValRange F s (n + 1) = 2 * regValRange (fun i => F (i + 1)) s n := by
    rw [regValRange_succ' F s n, hbot]; simp
  rw [hval, hsrc, Nat.mul_div_cancel_left _ (by norm_num)]

/-! ### A concrete `decide`-checked witness (anti-hollow) -/

/-- Layout on `4` wires: register `F i = i` (bits `0,1,2,3`). -/
def F4 : ℕ → Fin 4 := fun i => ⟨i % 4, Nat.mod_lt _ (by norm_num)⟩

theorem F4_injOn : Function.Injective (fun i : Fin 4 => F4 i) := by decide

/-- `10 = 0b1010` (even) halves to `5 = 0b0101`: the shift-down circuit on the `4`-bit register holding
`10` decodes to `5`. Machine-checked through the real `denote` semantics on the concrete state. -/
example :
    regValRange F4 (denote (shiftDown F4 3)
      (fun w => [false, true, false, true].getD w.val false)) 4 = 5 := by decide

end ECDLP.Safegcd.Circuit
