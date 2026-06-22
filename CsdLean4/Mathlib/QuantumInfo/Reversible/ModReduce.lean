import CsdLean4.Mathlib.QuantumInfo.Reversible.ModAdd

/-!
# Reversible modular reduction — comparison via carry-out, single-step reduce  (ECDLP Phase 2, Stage S4)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The resource figures so far (`ResourceBounds.lean`) cost *multiply-and-accumulate* but **omit the
modular reduction** that keeps the accumulator bounded — a real completeness gap in the Toffoli count
(`mulCircuit_correct_zmod` discharges the reduction *semantically*, by reading the register in `ZMod N`,
but exhibits no reduction *circuit*, so its cost is unaccounted). This module closes the gap on the
verified side as far as a measurement-free, control-light gate DSL honestly allows, and names the
documented residue.

Modular reduction of `x` (with `x < 2N`) is **compare-and-conditional-subtract**: if `x ≥ N` return
`x − N`, else return `x`. Two facts make this cheap to *verify* by reusing the Tranche-2 ripple adder:

* **The comparison is the carry-out.** Adding the complement constant `2ⁿ − N` to `x` overflows
  (`carry-out = 1`) **iff** `x ≥ N`. The carry-out wire `C n` of `rippleCirc` already carries this bit;
  `rippleCirc_carryout` reads it off the existing `rippleCirc_invariant` — no new circuit.
* **The subtract is that same add.** When `x ≥ N` (and `x < 2N`), `rippleCirc` with register `A` preset
  to `2ⁿ − N` leaves register `B` holding `(2ⁿ − N + x) mod 2ⁿ = x − N = x mod N`
  (`rippleCirc_modReduce_ge`), a corollary of `rippleCirc_correct`.

## What is proved here (verified)

* `rippleCirc_carryout` — the ripple adder's carry-out wire is the comparison flag
  `decide (2ⁿ ≤ A + B)`. The verified core of modular reduction.
* `rippleCirc_modReduce_ge` — for `N ≤ x < 2N` and register `A` preset to `2ⁿ − N`, the ripple adder
  computes `x mod N` into register `B`. A verified single-step modular reduction (the `x ≥ N` branch).
* `mod_eq_sub_of_le_of_lt_two_mul` — the ℕ spec the circuit realises: `N ≤ x < 2N ⇒ x mod N = x − N`.

## Documented residue (named, not built)

Making the subtract **conditional on the flag** in one reversible pass needs a flag-*controlled* adder
(every `CX`→`CCX`, every `CCX`→ a 3-control gate), which inflates gate count and is control-heavier than
this DSL is meant to carry; and the `x < N` branch is the identity (no subtract). The *cost* of the
conditional subtract is therefore documented in `ResourceBounds.lean` (`modReduceToffoli`/`modMultToffoli`),
composed over this verified comparison core, not exhibited as a circuit. So: comparison VERIFIED, reduce
value VERIFIED for `x ≥ N`, the conditional-control wrapper DOCUMENTED.
-/

namespace Reversible

variable {m n : ℕ}

/-- **ℕ spec of single-step reduction.** For `N ≤ x < 2N`, the modulus is one subtraction:
`x mod N = x − N`. The arithmetic fact the comparison-and-subtract circuit realises. -/
theorem mod_eq_sub_of_le_of_lt_two_mul {x N : ℕ} (hle : N ≤ x) (hlt : x < 2 * N) :
    x % N = x - N := by
  have hN : 0 < N := by omega
  rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)]

/-- **The carry-out is the comparison flag.** For a disjoint-wire layout with all carries initialised
`false`, the ripple adder's output carry wire `C n` holds `decide (2ⁿ ≤ A + B)` — it is set exactly when
the addition overflows `n` bits, i.e. when `A + B ≥ 2ⁿ`. Read off `rippleCirc_invariant` (clause P1)
together with `regValRange_lt`; no new circuit. This is the comparison primitive of modular reduction:
preset `A := 2ⁿ − N` and the carry-out becomes `decide (N ≤ x)`. -/
theorem rippleCirc_carryout (L : RippleLayout m n) (s : State m) (hC0 : ∀ j, s (L.C j) = false) :
    denote (rippleCirc L) s (L.C n)
      = decide (2 ^ n ≤ regValRange L.A s n + regValRange L.B s n) := by
  obtain ⟨hP1, -, -, -⟩ := rippleCirc_invariant L s hC0 n (Nat.le_refl n)
  rw [rippleCirc]
  have hlt : regValRange L.B (denote (ripplePrefix L n) s) n < 2 ^ n := regValRange_lt _ _ _
  cases h : denote (ripplePrefix L n) s (L.C n)
  · simp only [h, Bool.toNat_false, zero_mul, add_zero] at hP1
    rw [eq_comm, decide_eq_false_iff_not]
    omega
  · simp only [h, Bool.toNat_true, one_mul] at hP1
    rw [eq_comm, decide_eq_true_eq]
    omega

/-- **Verified single-step modular reduction (the `x ≥ N` branch).** With register `A` preset to the
complement constant `2ⁿ − N` and register `B` holding `x` with `N ≤ x < 2N`, the ripple adder leaves
`B` holding `x mod N`. Proof: `rippleCirc_correct` gives `B ← (2ⁿ − N + x) mod 2ⁿ`; since `N ≤ x < 2ⁿ`
the sum is `2ⁿ + (x − N)` with `x − N < 2ⁿ`, so the mod yields `x − N`, which equals `x mod N` by
`Nat.mod_eq_sub_of_le_of_lt_two_mul`. The reduction *value* is therefore verified for the case that
actually needs reducing; the flag-controlled wrapper (so the `x < N` case is left untouched) is the
documented residue (`ResourceBounds.modReduceToffoli`). -/
theorem rippleCirc_modReduce_ge (L : RippleLayout m n) (s : State m) (hC0 : ∀ j, s (L.C j) = false)
    {N : ℕ} (hN : N ≤ 2 ^ n) (hA : regValRange L.A s n = 2 ^ n - N)
    (hge : N ≤ regValRange L.B s n) (hx2N : regValRange L.B s n < 2 * N) :
    regValRange L.B (denote (rippleCirc L) s) n = regValRange L.B s n % N := by
  have hxlt : regValRange L.B s n < 2 ^ n := regValRange_lt _ _ _
  have hcorr := rippleCirc_correct L s hC0
  rw [hcorr, hA]
  set x := regValRange L.B s n with hx
  -- 2ⁿ − N + x = 2ⁿ + (x − N), with x − N < 2ⁿ, so the mod drops the 2ⁿ.
  have hsum : 2 ^ n - N + x = 2 ^ n + (x - N) := by omega
  rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  exact (mod_eq_sub_of_le_of_lt_two_mul hge hx2N).symm

/-! ### Non-vacuity

`rippleCirc_carryout` and `rippleCirc_modReduce_ge` inherit inhabitation of `RippleLayout` from
`rippleLayout2` (Tranche 2). The example below pins the comparison primitive at the concrete 2-bit
layout, confirming the headlines are not vacuously quantified. -/

/-- The comparison primitive is non-vacuous: it applies to the concrete `rippleLayout2`. -/
example (s : State 7) (hC0 : ∀ j, s (rippleLayout2.C j) = false) :
    denote (rippleCirc rippleLayout2) s (rippleLayout2.C 2)
      = decide (2 ^ 2 ≤ regValRange rippleLayout2.A s 2 + regValRange rippleLayout2.B s 2) :=
  rippleCirc_carryout rippleLayout2 s hC0

end Reversible
