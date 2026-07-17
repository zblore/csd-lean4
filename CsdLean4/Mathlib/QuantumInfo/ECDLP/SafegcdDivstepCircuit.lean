import CsdLean4.Mathlib.QuantumInfo.Reversible.CuccaroAdd
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularSub
import CsdLean4.Mathlib.QuantumInfo.ECDLP.SafegcdDivstep

/-!
# The value-faithful safegcd divstep circuit — TRANCHES 1–4b  (ECDLP L6, #36c-2)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

This module opens the deferred residue named in `SafegcdInversion.lean` and `SafegcdDivstep.lean`:
the **reversible BIT-CIRCUIT whose denotation equals `ECDLP.Safegcd.divstep`**. The existing
`ResourceBounds.divstepProxyGadget` is a COST proxy — its `denote` computes *modular* arithmetic, not
the integer divstep — so `divstepToffoli` is cost-backed but the value is not circuit-backed. Building
the value-faithful circuit is a multi-tranche task (there was no signed-integer register layer). Tranches
so far: **1** exact (unsigned) halving; **2** signed integer `±` (the `g ∓ f` numerators); **3** the
branch-conditional register swap `f ↔ g` + the `Odd g` test; **4a** the SIGNED (sign-extending) halving;
**4b** the g-register update `g ↦ (g ∓ f)/2` composing T2 + T4a; **4c** the `0 < δ` control read (the
branch discriminant, `regValZ_pos_iff`/`regValZ_nonneg_iff`); **4d** the `δ`-counter update `δ ↦ 1 ± δ`
(a T2 corollary — signed `±` against the constant `1`); **4e** the reversible nonzero/OR gadget
(`orAccum` — the "low bits ≠ 0" half of the `0<δ` read); **4f** the branch-A f-recovery `f ← f + 2·g`
(`addTwice`, resolving the in-place `f' = g` without a swap) + the composition identity `branchA_recovers`.
**4g** the lane-0 cswap elision (`cswap_lane0_noop` — the frontier's `divstep 0..n → 1..n` Toffoli lever,
here a proved value-exact identity: when the swap fires, `f, g` are both odd so wire-0 swap is a no-op).
So every divstep sub-operation AND branch A's in-place `(f,g)` transformation are circuit-backed; **4h** the
branch-control-bit synthesis (`and3_correct`: `bA = sign_clear ∧ nonzero_δ ∧ odd_g` into a clean ancilla).
Remaining: the controlled (branch-gated) gadget variants + wiring the control bits, then the end-to-end
`denote = divstepRev`.

## The divstep's three register updates, and which one this tranche builds

One `divstep (δ,f,g) ↦ (δ',f',g')` (with `f` kept ODD) does, on the `(f,g)` registers:

* a **branch-conditional swap** `f ↔ g` (the `δ>0 ∧ g` odd branch sets `f' = g`);
* an **integer combination** `g ± f` (forming the even numerator `g-f` or `g+f`);
* an **exact halving** `↦ /2` of that even numerator (or of `g` itself when `g` is even).

**Tranche 1 builds the exact halving** — the divstep-specific primitive, provable on the EXISTING
natural-number register decoder (`Reversible.regValRange`): every divstep halving is of an *even*
register (the numerator is even in each branch, `divstep_gcd`'s per-branch `Odd.sub_odd` / `Odd.add_odd`
/ `Even`), so its magnitude alone determines the result and no signed decoding is needed there.

**Tranche 2 builds the signed integer arithmetic** — the `g + f` and `g - f` numerator computations.
`f`, `g` range over ℤ (they go negative), so this needs a SIGNED register decoder. The clean device is
`signedRep` — the **balanced two's-complement representative**, depending only on the unsigned readout
(no bit indexing): `signedRep n u = u` for `u < 2^{n-1}` and `u - 2^n` otherwise. Then `regValZ` is the
signed value of a register, and the verified mod-`2^n` gadgets (`cuccaroAdd`, `rippleSub`) realise signed
ℤ addition / subtraction under a NO-OVERFLOW bound (`signedAdd_correct`, `signedSub_correct`) — because
two's-complement `+`/`−` IS mod-`2^n` arithmetic reinterpreted, exact whenever the true result fits the
signed range. Conditional swap + branch routing (tranche 3), then the assembly `denote = divstepRev`
(tranche 4), remain.

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

/-! ## Tranche 2: the signed integer arithmetic (`g ± f`)

The divstep numerators `g - f` (branch A) and `g + f` (branch B) are ℤ operations (`f, g` go negative).
`signedRep` is the two's-complement **balanced representative** of an `n`-bit unsigned readout, and
`regValZ` the signed value of a register. The verified mod-`2^n` gadgets then realise signed ℤ
arithmetic under a no-overflow hypothesis. -/

/-- **The two's-complement (balanced) signed value** of an `n`-bit readout `z`. `signedRep n u = u` for
`u` in the low half `[0, 2^{n-1})` and `u - 2^n` in the high half `[2^{n-1}, 2^n)` — the faithful
`n`-bit two's-complement decoding, written uniformly as `(z + 2^{n-1}) mod 2^n - 2^{n-1}` so it depends
only on `z mod 2^n` (`signedRep_congr`) and needs no bit indexing. -/
def signedRep (n : ℕ) (z : ℤ) : ℤ := (z + 2 ^ (n - 1)) % 2 ^ n - 2 ^ (n - 1)

/-- `signedRep n z ≡ z [ZMOD 2^n]`: the signed value is congruent to the raw readout mod `2^n`. -/
theorem signedRep_modEq (n : ℕ) (z : ℤ) : signedRep n z ≡ z [ZMOD 2 ^ n] := by
  unfold signedRep
  calc (z + 2 ^ (n - 1)) % 2 ^ n - 2 ^ (n - 1)
      ≡ (z + 2 ^ (n - 1)) - 2 ^ (n - 1) [ZMOD 2 ^ n] := (Int.mod_modEq _ _).sub_right _
    _ = z := by ring

/-- **`signedRep` depends only on the value mod `2^n`.** Congruent readouts have the same signed value —
the reason mod-`2^n` register arithmetic is faithful to two's complement. -/
theorem signedRep_congr (n : ℕ) {z w : ℤ} (h : z ≡ w [ZMOD 2 ^ n]) :
    signedRep n z = signedRep n w := by
  unfold signedRep
  have hshift : (z + 2 ^ (n - 1)) % 2 ^ n = (w + 2 ^ (n - 1)) % 2 ^ n := h.add_right _
  rw [hshift]

/-- **`signedRep` fixes in-range values.** If `z` already lies in the signed range `[-2^{n-1}, 2^{n-1})`,
it is its own two's-complement representative. This is the no-overflow fixpoint the arithmetic theorems
land on. -/
theorem signedRep_of_mem (n : ℕ) (hn : 1 ≤ n) {z : ℤ}
    (hlo : -2 ^ (n - 1) ≤ z) (hhi : z < 2 ^ (n - 1)) : signedRep n z = z := by
  unfold signedRep
  have hpow : (2 : ℤ) ^ n = 2 ^ (n - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  have h0 : 0 ≤ z + 2 ^ (n - 1) := by linarith
  have h1 : z + 2 ^ (n - 1) < 2 ^ n := by rw [hpow]; linarith
  rw [Int.emod_eq_of_lt h0 h1]; ring

/-- **The signed (two's-complement) value of a register**: the balanced representative of its unsigned
`n`-bit readout. `regValZ` is to signed arithmetic what `regValRange` is to unsigned. -/
def regValZ (f : ℕ → Fin m) (s : State m) (n : ℕ) : ℤ := signedRep n (regValRange f s n : ℤ)

/-- Casting a natural readout mod `2^n` into ℤ is congruent to the raw ℤ value mod `2^n`. The bridge
that lets `signedRep_congr` consume the `% 2^n` in the verified gadget correctness statements. -/
theorem natCast_mod_modEq (a : ℕ) (n : ℕ) : (((a % 2 ^ n : ℕ) : ℤ)) ≡ (a : ℤ) [ZMOD 2 ^ n] := by
  refine Int.modEq_iff_dvd.mpr ⟨(a / 2 ^ n : ℕ), ?_⟩
  have h : 2 ^ n * (a / 2 ^ n) + a % 2 ^ n = a := Nat.div_add_mod a (2 ^ n)
  push_cast at h ⊢
  linarith [h]

/-- **Value-faithful signed ADDITION (the `g + f` numerator).** Under a no-overflow bound on the signed
sum, the verified carry-clean adder `cuccaroAdd` computes `regValZ` addition: register `A` ends holding
`regValZ A + regValZ B` at the SIGNED (two's-complement) level, not merely mod `2^n`. This is the
divstep branch-B numerator `g + f` on a value-faithful circuit. Proof: `cuccaroAdd_correct` gives the
unsigned `(uA+uB) mod 2^n`; `signedRep` collapses the mod (it depends only on the value mod `2^n`,
`signedRep_congr` + `signedRep_modEq`), and the range hypothesis pins the result via `signedRep_of_mem`. -/
theorem signedAdd_correct {n : ℕ} (L : CuccaroLayout m n) (s : State m) (hn : 1 ≤ n)
    (hZ : s L.Z = false)
    (hlo : -2 ^ (n - 1) ≤ regValZ L.A s n + regValZ L.B s n)
    (hhi : regValZ L.A s n + regValZ L.B s n < 2 ^ (n - 1)) :
    regValZ L.A (denote (cuccaroAdd L) s) n = regValZ L.A s n + regValZ L.B s n := by
  set uA := regValRange L.A s n with huA
  set uB := regValRange L.B s n with huB
  have hres : regValRange L.A (denote (cuccaroAdd L) s) n = (uA + uB) % 2 ^ n :=
    cuccaroAdd_correct L s hZ
  -- congruences: the mod-2^n readout is congruent to the signed sum a + b
  have hcong : (((uA + uB) % 2 ^ n : ℕ) : ℤ)
      ≡ regValZ L.A s n + regValZ L.B s n [ZMOD 2 ^ n] := by
    refine (natCast_mod_modEq (uA + uB) n).trans ?_
    push_cast
    exact ((signedRep_modEq n (uA : ℤ)).add (signedRep_modEq n (uB : ℤ))).symm
  calc regValZ L.A (denote (cuccaroAdd L) s) n
      = signedRep n (((uA + uB) % 2 ^ n : ℕ) : ℤ) := by unfold regValZ; rw [hres]
    _ = signedRep n (regValZ L.A s n + regValZ L.B s n) := signedRep_congr n hcong
    _ = regValZ L.A s n + regValZ L.B s n := signedRep_of_mem n hn hlo hhi

/-- **Value-faithful signed SUBTRACTION (the `g - f` numerator).** Under a no-overflow bound on the
signed difference, the verified borrow-chain subtractor `rippleSub` computes `regValZ` subtraction:
the minuend register `B` ends holding `regValZ B - regValZ Sub` at the SIGNED level. This is the divstep
branch-A numerator `g - f` on a value-faithful circuit. Proof mirrors `signedAdd_correct`, absorbing the
`+ 2^n` guard of `rippleSub_correct` into the mod-`2^n` congruence. -/
theorem signedSub_correct {n : ℕ} (L : SubLayout m n) (s : State m) (hn : 1 ≤ n)
    (hBor0 : ∀ j, s (L.Bor j) = false)
    (hlo : -2 ^ (n - 1) ≤ regValZ L.B s n - regValZ L.Sub s n)
    (hhi : regValZ L.B s n - regValZ L.Sub s n < 2 ^ (n - 1)) :
    regValZ L.B (denote (rippleSub L) s) n = regValZ L.B s n - regValZ L.Sub s n := by
  set uB := regValRange L.B s n with huB
  set uS := regValRange L.Sub s n with huS
  have hres : regValRange L.B (denote (rippleSub L) s) n = (uB + 2 ^ n - uS) % 2 ^ n :=
    rippleSub_correct L s hBor0
  have hSlt : uS < 2 ^ n := huS ▸ regValRange_lt _ _ _
  -- the modded nat readout, cast to ℤ, is congruent to the signed difference b - c
  have hcong : (((uB + 2 ^ n - uS) % 2 ^ n : ℕ) : ℤ)
      ≡ regValZ L.B s n - regValZ L.Sub s n [ZMOD 2 ^ n] := by
    refine (natCast_mod_modEq (uB + 2 ^ n - uS) n).trans ?_
    have hcast : ((uB + 2 ^ n - uS : ℕ) : ℤ) = (uB : ℤ) + 2 ^ n - uS := by
      have hle : uS ≤ uB + 2 ^ n := by omega
      push_cast [Nat.cast_sub hle]
      ring
    rw [hcast]
    -- (uB + 2^n - uS) ≡ (uB - uS) ≡ (a - b) [ZMOD 2^n]
    have h1 : (uB : ℤ) + 2 ^ n - uS ≡ (uB : ℤ) - uS [ZMOD 2 ^ n] :=
      Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩
    refine h1.trans ?_
    exact ((signedRep_modEq n (uB : ℤ)).sub (signedRep_modEq n (uS : ℤ))).symm
  calc regValZ L.B (denote (rippleSub L) s) n
      = signedRep n (((uB + 2 ^ n - uS) % 2 ^ n : ℕ) : ℤ) := by unfold regValZ; rw [hres]
    _ = signedRep n (regValZ L.B s n - regValZ L.Sub s n) := signedRep_congr n hcong
    _ = regValZ L.B s n - regValZ L.Sub s n := signedRep_of_mem n hn hlo hhi

/-! ### Signed-decoder `decide` witnesses (anti-hollow) -/

/-- `0b1110 = 14` as a 4-bit two's-complement number is `-2`. -/
example : signedRep 4 14 = -2 := by decide

/-- `0b0011 = 3` (low half) decodes to `+3`. -/
example : signedRep 4 3 = 3 := by decide

/-- `0b1000 = 8` is the most-negative 4-bit value `-8`. -/
example : signedRep 4 8 = -8 := by decide

/-! ## Tranche 3: the branch control — conditional swap `f ↔ g` and the parity test

The divstep's branch A (`0 < δ ∧ Odd g`) sets `f' = g` — a conditional swap of the `f` and `g`
registers, controlled by a branch bit. This tranche builds that controlled swap value-faithfully, plus
the `Odd g` branch test as a bit read (`regValRange_odd_iff` / `regValZ_odd_iff`). The remaining control
input `0 < δ` is a sign read on the `δ` register; combined with `Odd g` it forms the branch-A control
bit, whose ancilla synthesis + the full conditional assembly is tranche 4. -/

/-- **The Fredkin (controlled-swap) gate** on target wires `x, y` with control `c`:
`[CX x y, CCX c y x, CX x y]`. When `c` is set it exchanges `x` and `y`; when clear it is the identity
(`cswap_correct_general`). One Toffoli. -/
def cswap (c x y : Fin m) : Circuit m := [.CX x y, .CCX c y x, .CX x y]

/-- **`cswap` correctness (general `Fin m`).** For pairwise-distinct `c, x, y`: the targets `x, y` are
exchanged exactly when the control `c` is set, and `c` itself is preserved. -/
theorem cswap_correct_general {c x y : Fin m} (hcx : c ≠ x) (hcy : c ≠ y) (hxy : x ≠ y)
    (s : State m) :
    denote (cswap c x y) s x = (if s c then s y else s x)
      ∧ denote (cswap c x y) s y = (if s c then s x else s y)
      ∧ denote (cswap c x y) s c = s c := by
  have hxc := hcx.symm; have hyc := hcy.symm; have hyx := hxy.symm
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [cswap, denote_cons, denote_nil, denoteGate] <;>
    simp_all <;>
    cases s c <;> cases s x <;> cases s y <;> simp_all

/-- **Frame lemma for `cswap`.** A wire distinct from `c, x, y` is untouched. -/
theorem cswap_apply_of_ne {c x y w : Fin m} (hc : w ≠ c) (hx : w ≠ x) (hy : w ≠ y) (s : State m) :
    denote (cswap c x y) s w = s w := by
  apply denote_apply_of_forall_not_mem
  intro g hg
  simp only [cswap, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp_all [gateWires]

/-- **The controlled register swap** of the `n`-bit registers `F` and `G`, controlled by wire `c`: one
Fredkin gate per bit. When `c` is set it exchanges the two registers; when clear it is the identity
(`condSwapReg_swaps`). This is the divstep branch-A move `f ↔ g`. -/
def condSwapReg (c : Fin m) (F G : ℕ → Fin m) : ℕ → Circuit m
  | 0 => []
  | k + 1 => condSwapReg c F G k ++ cswap c (F k) (G k)

/-- The controlled register swap costs `n` Toffolis (one CCX per bit). -/
theorem condSwapReg_toffoli (c : Fin m) (F G : ℕ → Fin m) (n : ℕ) :
    (circuitCost (condSwapReg c F G n)).toffoli = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [condSwapReg, cost_comp_toffoli_count, ih]
    rfl

/-- **Wire action of the controlled register swap (induction core).** For a disjoint, injective layout,
after the `k`-bit controlled swap: positions `i < k` of `F` and `G` are exchanged iff the control `c` is
set (and unchanged otherwise), the control `c` is preserved, and positions `i ≥ k` are untouched. -/
theorem condSwapReg_wire {c : Fin m} {F G : ℕ → Fin m}
    (hcF : ∀ i, c ≠ F i) (hcG : ∀ i, c ≠ G i) (hFG : ∀ i j, F i ≠ G j)
    (hF : Function.Injective F) (hG : Function.Injective G) (s : State m) (k : ℕ) :
    (∀ i, i < k → denote (condSwapReg c F G k) s (F i) = if s c then s (G i) else s (F i))
      ∧ (∀ i, i < k → denote (condSwapReg c F G k) s (G i) = if s c then s (F i) else s (G i))
      ∧ denote (condSwapReg c F G k) s c = s c
      ∧ (∀ i, k ≤ i → denote (condSwapReg c F G k) s (F i) = s (F i)
          ∧ denote (condSwapReg c F G k) s (G i) = s (G i)) := by
  induction k with
  | zero =>
    refine ⟨by omega, by omega, rfl, ?_⟩
    intro i _; exact ⟨rfl, rfl⟩
  | succ k ih =>
    obtain ⟨ihA, ihB, ihC, ihD⟩ := ih
    have hstep : ∀ w, denote (condSwapReg c F G (k + 1)) s w
        = denote (cswap c (F k) (G k)) (denote (condSwapReg c F G k) s) w := by
      intro w; rw [condSwapReg, denote_append]
    set t := denote (condSwapReg c F G k) s with ht
    obtain ⟨htFk, htGk⟩ := ihD k (le_refl k)
    -- cswap on the top bit, over the k-chain result t
    have hsw := cswap_correct_general (hcF k) (hcG k) (hFG k k) t
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- F positions i < k+1
      intro i hi
      rw [hstep]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · rw [cswap_apply_of_ne (hcF i).symm (fun h => by exact absurd (hF h) (by omega))
          (fun h => hFG i k h)]
        exact ihA i hlt
      · rw [hsw.1, ihC, htFk, htGk]
    · -- G positions i < k+1
      intro i hi
      rw [hstep]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · rw [cswap_apply_of_ne (hcG i).symm (fun h => (hFG k i) h.symm)
          (fun h => by exact absurd (hG h) (by omega))]
        exact ihB i hlt
      · rw [hsw.2.1, ihC, htFk, htGk]
    · -- control preserved
      rw [hstep, hsw.2.2]; exact ihC
    · -- untouched high positions i ≥ k+1
      intro i hi
      constructor
      · rw [hstep, cswap_apply_of_ne (hcF i).symm (fun h => by exact absurd (hF h) (by omega))
          (fun h => hFG i k h)]
        exact (ihD i (by omega)).1
      · rw [hstep, cswap_apply_of_ne (hcG i).symm (fun h => (hFG k i) h.symm)
          (fun h => by exact absurd (hG h) (by omega))]
        exact (ihD i (by omega)).2

/-- **The controlled register swap exchanges the registers when the control is set.** For a set control
`c`, `F` and `G` swap bitwise, hence their `regValRange` (and `regValZ`) readouts swap. This is the
divstep branch-A `f ↔ g` on a value-faithful circuit. -/
theorem condSwapReg_swaps {c : Fin m} {F G : ℕ → Fin m}
    (hcF : ∀ i, c ≠ F i) (hcG : ∀ i, c ≠ G i) (hFG : ∀ i j, F i ≠ G j)
    (hF : Function.Injective F) (hG : Function.Injective G) (s : State m) (hc : s c = true)
    (n : ℕ) :
    (∀ i, i < n → denote (condSwapReg c F G n) s (F i) = s (G i))
      ∧ (∀ i, i < n → denote (condSwapReg c F G n) s (G i) = s (F i)) := by
  obtain ⟨hA, hB, _, _⟩ := condSwapReg_wire hcF hcG hFG hF hG s n
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [hA i hi, if_pos hc]
  · rw [hB i hi, if_pos hc]

/-- **Lane-0 cswap elision (a real frontier Toffoli lever).** A controlled swap of two wires holding
EQUAL values is the identity — swapping equal bits does nothing, whatever the control. -/
theorem cswap_noop_of_eq {c x y : Fin m} (hxy : x ≠ y) (hcx : c ≠ x) (hcy : c ≠ y) (s : State m)
    (heq : s x = s y) : denote (cswap c x y) s = s := by
  obtain ⟨hx, hy, hc⟩ := cswap_correct_general hcx hcy hxy s
  funext w
  by_cases hwx : w = x
  · subst hwx; rw [hx, ← heq]; split <;> rfl
  by_cases hwy : w = y
  · subst hwy; rw [hy, heq]; split <;> rfl
  by_cases hwc : w = c
  · subst hwc; exact hc
  · exact cswap_apply_of_ne hwc hwx hwy s

/-- **The divstep lane-0 cswap is a no-op** (the frontier's `divstep 0..n → 1..n` elision). When the
branch-A `f ↔ g` swap fires, `f` and `g` are BOTH odd, so wire `0` is `true` for both; swapping equal
bits does nothing. So the lane-0 controlled swap is eliminable — a per-divstep Toffoli saving the field
ships (`ecdsafail-toffoli-reduction`), here a proved value-exact identity. -/
theorem cswap_lane0_noop {c : Fin m} {F G : ℕ → Fin m} (hcF : c ≠ F 0) (hcG : c ≠ G 0)
    (hFG : F 0 ≠ G 0) (s : State m) (hf : s (F 0) = true) (hg : s (G 0) = true) :
    denote (cswap c (F 0) (G 0)) s = s :=
  cswap_noop_of_eq hFG hcF hcG s (hf.trans hg.symm)

/-! ### The `Odd g` branch test as a bit read -/

/-- **Parity is the bottom bit.** For a nonempty register, `regValRange` is odd iff wire `0` is set —
the divstep's `Odd g` branch test is exactly a read of the register's low bit. Parity is
interpretation-independent, so this holds for the signed value too (`regValZ_odd_iff`). -/
theorem regValRange_odd_iff (f : ℕ → Fin m) (s : State m) {n : ℕ} (hn : 1 ≤ n) :
    Odd (regValRange f s n) ↔ s (f 0) = true := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [regValRange_succ' f s k, Nat.odd_add]
  have heven : Even (2 * regValRange (fun i => f (i + 1)) s k) := ⟨_, two_mul _⟩
  simp only [heven, iff_true]
  cases s (f 0) <;> simp

/-- **The signed `Odd g` test.** The signed register value `regValZ` is odd iff wire `0` is set — the
divstep condition `Odd g` (on the signed `g`) is the same low-bit read, since `regValZ ≡ regValRange`
mod `2^n` and `2 ∣ 2^n` for `n ≥ 1`. -/
theorem regValZ_odd_iff (f : ℕ → Fin m) (s : State m) {n : ℕ} (hn : 1 ≤ n) :
    Odd (regValZ f s n) ↔ s (f 0) = true := by
  have hmod := signedRep_modEq n (regValRange f s n : ℤ)
  have hdvd2 : (2 : ℤ) ∣ ((regValRange f s n : ℤ) - signedRep n (regValRange f s n)) :=
    dvd_trans (dvd_pow_self 2 (by omega : n ≠ 0)) (Int.modEq_iff_dvd.mp hmod)
  have h2' : signedRep n (regValRange f s n) % 2 = (regValRange f s n : ℤ) % 2 :=
    Int.modEq_iff_dvd.mpr hdvd2
  rw [regValZ, Int.odd_iff, h2', ← Int.odd_iff, Int.odd_coe_nat]
  exact regValRange_odd_iff f s hn

/-- Controlled swap of `F i = 2i`, `G i = 2i+1` on control wire `6`, `n = 3` bits, control SET: the two
`3`-bit registers holding `5` and `2` are exchanged (readouts swap). Machine-checked through `denote`. -/
example :
    let s : State 7 := fun w => [true, false, false, true, false, true, true].getD w.val false
    let F : ℕ → Fin 7 := fun i => ⟨(2 * i) % 7, Nat.mod_lt _ (by norm_num)⟩
    let G : ℕ → Fin 7 := fun i => ⟨(2 * i + 1) % 7, Nat.mod_lt _ (by norm_num)⟩
    regValRange F (denote (condSwapReg 6 F G 3) s) 3 = regValRange G s 3
      ∧ regValRange G (denote (condSwapReg 6 F G 3) s) 3 = regValRange F s 3 := by decide

/-! ## Tranche 4a: the SIGNED halving (sign-extending shift)

Tranche 1's `shiftDown` halves the UNSIGNED magnitude (it fills the vacated top bit with `0`). The
divstep halves SIGNED numerators `(g ± f)/2` where `g, f` go negative, so it needs an ARITHMETIC
(sign-extending) right shift — one that keeps the sign bit. This section builds it.

First, two two's-complement facts: `signedRep_high` evaluates `signedRep` on the high half, and
`regValZ_signBit` decomposes the signed value as `low bits − sign·2^n` — the workhorse for reasoning
about signs (and the eventual `0 < δ` read). -/

/-- **`signedRep` on the high half.** For `v ∈ [2^{W-1}, 2^W)` (top bit set), the two's-complement value
is `v - 2^W` (negative). Complements `signedRep_of_mem` (the low half, where it is `v`). -/
theorem signedRep_high (W : ℕ) (hW : 1 ≤ W) {v : ℤ} (hlo : 2 ^ (W - 1) ≤ v) (hhi : v < 2 ^ W) :
    signedRep W v = v - 2 ^ W := by
  have hpow : (2 : ℤ) ^ W = 2 ^ (W - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  have hcong : v ≡ v - 2 ^ W [ZMOD 2 ^ W] := Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩
  rw [signedRep_congr W hcong]
  apply signedRep_of_mem W hW <;> rw [hpow] <;> linarith

/-- **The two's-complement sign decomposition.** The signed register value is its low `n` bits minus
its sign bit weighted `2^n`: `regValZ f s (n+1) = regValRange f s n - (bit n)·2^n`. Proof: split the top
bit; the low half (`bit n = 0`) uses `signedRep_of_mem`, the high half (`bit n = 1`) uses
`signedRep_high`. -/
theorem regValZ_signBit (f : ℕ → Fin m) (s : State m) (n : ℕ) :
    regValZ f s (n + 1) = (regValRange f s n : ℤ) - (s (f n)).toNat * 2 ^ n := by
  have hLlt : regValRange f s n < 2 ^ n := regValRange_lt _ _ _
  rw [regValZ, regValRange_succ]
  push_cast
  set L : ℤ := (regValRange f s n : ℤ) with hL
  have hLlt' : L < 2 ^ n := by rw [hL]; exact_mod_cast hLlt
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  cases s (f n) with
  | false =>
    simp only [Bool.toNat_false, Nat.cast_zero, zero_mul, add_zero, sub_zero]
    exact signedRep_of_mem (n + 1) (by omega) (by simp only [Nat.add_sub_cancel]; linarith)
      (by simpa using hLlt')
  | true =>
    simp only [Bool.toNat_true, Nat.cast_one, one_mul]
    rw [signedRep_high (n + 1) (by omega) (by simpa using (by linarith : (2:ℤ)^n ≤ L + 2 ^ n))
      (by rw [pow_succ]; linarith)]
    ring

/-- **The signed (sign-extending) halving gadget** on an `(n+1)`-bit register: the tranche-1 shift
`shiftDown` followed by one CNOT copying the sign bit up (`CX (F (n-1)) (F n)`). Where `shiftDown` alone
fills the vacated top with `0` (unsigned `÷2`), this restores the sign, giving a two's-complement
arithmetic right shift. One extra CNOT, still Toffoli-free. -/
def signedHalve (F : ℕ → Fin m) (n : ℕ) : Circuit m := shiftDown F n ++ [.CX (F (n - 1)) (F n)]

/-- The signed halving is Toffoli-free (`shiftDown` is, and a CNOT adds none). -/
theorem signedHalve_toffoli (F : ℕ → Fin m) (n : ℕ) :
    (circuitCost (signedHalve F n)).toffoli = 0 := by
  rw [signedHalve, cost_comp_toffoli_count, shiftDown_toffoli]; rfl

/-- **Exact signed halving of an EVEN register.** For an even register (bottom bit `false`), the
sign-extending shift computes signed `÷2` at the two's-complement level: `regValZ` is halved. This is
the divstep's halving on the SIGNED numerators `(g ± f)/2` (which go negative) — the piece tranche 1's
unsigned `halve_correct` did not cover. Proof: the shift moves bits `1..n` down and the CNOT restores
the sign bit (the vacated bit is `0`, even); `regValZ_signBit` then reduces both sides to the sign
decomposition, and `regValRange_succ'/_succ` give `regValZ s = 2 · regValZ s'`. -/
theorem signedHalve_correct (F : ℕ → Fin m) (hF : Function.Injective F) (s : State m) {n : ℕ}
    (hn : 1 ≤ n) (hbot : s (F 0) = false) :
    regValZ F (denote (signedHalve F n) s) (n + 1) = regValZ F s (n + 1) / 2 := by
  -- sign bit is restored: s' (F n) = s (F n)
  have hsFn : denote (signedHalve F n) s (F n) = s (F n) := by
    rw [signedHalve, denote_append]
    have hne : F (n - 1) ≠ F n := fun h => by have := hF h; omega
    simp only [denote_cons, denote_nil, denoteGate, if_neg hne, Function.update_self]
    have h1 : denote (shiftDown F n) s (F (n - 1)) = s (F n) := by
      have := shiftDown_apply_lt F hF s (i := n - 1) (by omega : n - 1 < n)
      rwa [Nat.sub_add_cancel hn] at this
    rw [h1, shiftDown_apply_top F hF s n, hbot]
    simp
  -- low n bits: shifted down, so they equal the shifted register
  have hR' : regValRange F (denote (signedHalve F n) s) n = regValRange (fun i => F (i + 1)) s n := by
    unfold regValRange
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hsi : denote (signedHalve F n) s (F i) = s (F (i + 1)) := by
      rw [signedHalve, denote_append]
      have hne : F i ≠ F n := fun h => by have := hF h; omega
      have hne2 : F (n - 1) ≠ F n := fun h => by have := hF h; omega
      simp only [denote_cons, denote_nil, denoteGate, if_neg hne2, Function.update_of_ne hne]
      exact shiftDown_apply_lt F hF s hi
    rw [hsi]
  -- the arithmetic key: regValRange F s n + sign·2^n = 2 · (low shifted register)
  have e2 : regValRange F s (n + 1) = 2 * regValRange (fun i => F (i + 1)) s n := by
    rw [regValRange_succ' F s n, hbot]; simp
  have hkey : (regValRange F s n : ℤ) + (s (F n)).toNat * 2 ^ n
      = 2 * (regValRange (fun i => F (i + 1)) s n : ℤ) := by
    have := (regValRange_succ F s n).symm.trans e2
    exact_mod_cast this
  -- assemble via the sign decomposition of both states
  have hlhs : regValZ F (denote (signedHalve F n) s) (n + 1)
      = (regValRange (fun i => F (i + 1)) s n : ℤ) - (s (F n)).toNat * 2 ^ n := by
    rw [regValZ_signBit F (denote (signedHalve F n) s) n, hR', hsFn]
  rw [hlhs, regValZ_signBit F s n]
  have hstep : (regValRange F s n : ℤ) - (s (F n)).toNat * 2 ^ n
      = 2 * ((regValRange (fun i => F (i + 1)) s n : ℤ) - (s (F n)).toNat * 2 ^ n) := by
    linarith [hkey]
  rw [hstep, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]

/-- `-6 = 0b1010` as a 4-bit two's-complement value halves (signed) to `-3 = 0b1101`: the
sign-extending shift on the register holding `-6` decodes to `-3`. Machine-checked through `denote`. -/
example :
    regValZ F4 (denote (signedHalve F4 3)
      (fun w => [false, true, false, true].getD w.val false)) 4 = -3 := by decide

/-! ## Tranche 4b: the g-register update — composing signed `±` (T2) with signed halve (T4a)

The divstep's `g`-register update is `g ↦ (g - f)/2` (branch A) or `g ↦ (g + f)/2` (branch B). Each is
the composition of a signed integer combination (tranche 2) and a signed halving (tranche 4a). This
section assembles the two verified stages into one circuit whose `denote` computes the divstep numerator
directly at the signed-ℤ (`regValZ`) level — no new infrastructure, just composition.

The load-bearing observation: since `f` is kept ODD throughout the divstep and `g` is odd in these
branches, the numerator `g ∓ f` is EVEN — so the intermediate register has bottom bit `false`, exactly
the hypothesis `signedHalve_correct` consumes. -/

/-- **The g-update, subtract branch (branch A numerator): `g ↦ (g - f)/2`.** The composite circuit
`rippleSub ; signedHalve` on the minuend register `B` computes `(regValZ B - regValZ Sub)/2` at the
signed level. `B = g`, `Sub = f`. Requires `g, f` odd (so `g - f` is even and the halving is exact) and
the signed difference in range. Composes `signedSub_correct` (T2) with `signedHalve_correct` (T4a); the
evenness of `g - f` (`Odd.sub_odd`) discharges the halving's bottom-bit hypothesis. -/
theorem gUpdateSub_correct {n : ℕ} (L : SubLayout m (n + 1)) (s : State m) (hn : 1 ≤ n)
    (hBinj : Function.Injective L.B) (hBor0 : ∀ j, s (L.Bor j) = false)
    (hgodd : Odd (regValZ L.B s (n + 1))) (hfodd : Odd (regValZ L.Sub s (n + 1)))
    (hlo : -2 ^ n ≤ regValZ L.B s (n + 1) - regValZ L.Sub s (n + 1))
    (hhi : regValZ L.B s (n + 1) - regValZ L.Sub s (n + 1) < 2 ^ n) :
    regValZ L.B (denote (rippleSub L ++ signedHalve L.B n) s) (n + 1)
      = (regValZ L.B s (n + 1) - regValZ L.Sub s (n + 1)) / 2 := by
  rw [denote_append]
  set s' := denote (rippleSub L) s with hs'
  -- the subtraction stage: B holds g - f
  have hsub : regValZ L.B s' (n + 1) = regValZ L.B s (n + 1) - regValZ L.Sub s (n + 1) :=
    signedSub_correct L s (by omega) hBor0 (by simpa using hlo) (by simpa using hhi)
  -- g - f is even, so the intermediate bottom bit is false
  have heven : s' (L.B 0) = false := by
    cases hb : s' (L.B 0) with
    | false => rfl
    | true =>
      exact absurd (hsub ▸ (regValZ_odd_iff L.B s' (by omega)).mpr hb)
        (Int.not_odd_iff_even.mpr (hgodd.sub_odd hfodd))
  -- the halving stage
  rw [signedHalve_correct L.B hBinj s' hn heven, hsub]

/-- **The g-update, add branch (branch B numerator): `g ↦ (g + f)/2`.** The composite circuit
`cuccaroAdd ; signedHalve` on the sum register `A` computes `(regValZ A + regValZ B)/2` at the signed
level. `A = g`, `B = f`. Requires `g, f` odd (so `g + f` is even) and the signed sum in range. Composes
`signedAdd_correct` (T2) with `signedHalve_correct` (T4a); evenness of `g + f` (`Odd.add_odd`) discharges
the halving's bottom-bit hypothesis. -/
theorem gUpdateAdd_correct {n : ℕ} (L : CuccaroLayout m (n + 1)) (s : State m) (hn : 1 ≤ n)
    (hAinj : Function.Injective L.A) (hZ : s L.Z = false)
    (hgodd : Odd (regValZ L.A s (n + 1))) (hfodd : Odd (regValZ L.B s (n + 1)))
    (hlo : -2 ^ n ≤ regValZ L.A s (n + 1) + regValZ L.B s (n + 1))
    (hhi : regValZ L.A s (n + 1) + regValZ L.B s (n + 1) < 2 ^ n) :
    regValZ L.A (denote (cuccaroAdd L ++ signedHalve L.A n) s) (n + 1)
      = (regValZ L.A s (n + 1) + regValZ L.B s (n + 1)) / 2 := by
  rw [denote_append]
  set s' := denote (cuccaroAdd L) s with hs'
  have hadd : regValZ L.A s' (n + 1) = regValZ L.A s (n + 1) + regValZ L.B s (n + 1) :=
    signedAdd_correct L s (by omega) hZ (by simpa using hlo) (by simpa using hhi)
  have heven : s' (L.A 0) = false := by
    cases hb : s' (L.A 0) with
    | false => rfl
    | true =>
      exact absurd (hadd ▸ (regValZ_odd_iff L.A s' (by omega)).mpr hb)
        (Int.not_odd_iff_even.mpr (hgodd.add_odd hfodd))
  rw [signedHalve_correct L.A hAinj s' hn heven, hadd]

/-! ## Tranche 4c: the `0 < δ` control read — the branch discriminant

The divstep's branch A is taken when `0 < δ ∧ Odd g`. The `Odd g` half is a wire-0 read
(`regValZ_odd_iff`, T3); this section supplies the other half, the SIGN read `0 < δ` (and `0 ≤ δ`),
characterised in bits via the two's-complement decomposition `regValZ_signBit`. These are the value
primitives a branch-bit synthesis circuit computes into its control ancilla. The `δ`-counter *arithmetic*
`δ ↦ 1 ± δ` (updating `δ` across the step) remains — it needs a small signed constant-add/negate layer. -/

/-- **The sign read `0 ≤ δ`.** A signed register is non-negative iff its sign bit (wire `n`) is clear.
Immediate from `regValZ_signBit`. -/
theorem regValZ_nonneg_iff (f : ℕ → Fin m) (s : State m) (n : ℕ) :
    0 ≤ regValZ f s (n + 1) ↔ s (f n) = false := by
  have hLlt : (regValRange f s n : ℤ) < 2 ^ n := by exact_mod_cast regValRange_lt f s n
  have hL0 : 0 ≤ (regValRange f s n : ℤ) := by positivity
  rw [regValZ_signBit]
  cases hb : s (f n) with
  | false =>
    simp only [Bool.toNat_false, Nat.cast_zero, zero_mul, sub_zero]
    exact iff_of_true hL0 trivial
  | true =>
    simp only [Bool.toNat_true, Nat.cast_one, one_mul]
    exact iff_of_false (by linarith) (by decide)

/-- **The `0 < δ` branch read.** A signed register is strictly positive iff its sign bit (wire `n`) is
clear AND its low `n` bits are not all zero: `0 < regValZ f s (n+1) ↔ s (f n) = false ∧ regValRange f s n
≠ 0`. This is the divstep's `0 < δ` discriminant as a bit read (a sign test plus a nonzero test). -/
theorem regValZ_pos_iff (f : ℕ → Fin m) (s : State m) (n : ℕ) :
    0 < regValZ f s (n + 1) ↔ s (f n) = false ∧ regValRange f s n ≠ 0 := by
  have hLlt : (regValRange f s n : ℤ) < 2 ^ n := by exact_mod_cast regValRange_lt f s n
  rw [regValZ_signBit]
  cases hb : s (f n) with
  | false =>
    simp only [Bool.toNat_false, Nat.cast_zero, zero_mul, sub_zero]
    rw [Int.natCast_pos, Nat.pos_iff_ne_zero]
    simp
  | true =>
    simp only [Bool.toNat_true, Nat.cast_one, one_mul]
    exact iff_of_false (by linarith) (by rintro ⟨h, _⟩; exact absurd h (by decide))

/-! ## Tranche 4d: the δ-counter update `δ ↦ 1 ± δ` — a tranche-2 corollary

The divstep's `δ` update is `δ ↦ 1 - δ` (branch A) or `δ ↦ 1 + δ` (branches B, C). Each is signed
arithmetic against the constant `1`, so it needs NO new circuit: with a register initialised to the
value `1`, `cuccaroAdd` gives `1 + δ` and `rippleSub` gives `1 - δ` at the signed level. These are
immediate instances of tranche 2, recorded here to close the δ-arithmetic item. -/

/-- **δ ↦ 1 + δ** (branches B, C). If register `B` holds the constant `1`, `cuccaroAdd` leaves the
`A`-register holding `regValZ A + 1` — the divstep's `δ` increment. Instance of `signedAdd_correct`. -/
theorem deltaInc_correct {n : ℕ} (L : CuccaroLayout m (n + 1)) (s : State m) (hZ : s L.Z = false)
    (hone : regValZ L.B s (n + 1) = 1)
    (hlo : -2 ^ n ≤ regValZ L.A s (n + 1) + 1) (hhi : regValZ L.A s (n + 1) + 1 < 2 ^ n) :
    regValZ L.A (denote (cuccaroAdd L) s) (n + 1) = regValZ L.A s (n + 1) + 1 := by
  rw [signedAdd_correct L s (by omega) hZ (by rw [hone]; simpa using hlo)
    (by rw [hone]; simpa using hhi), hone]

/-- **δ ↦ 1 - δ** (branch A). If register `B` (the minuend) holds the constant `1`, `rippleSub` leaves
`B` holding `1 - regValZ Sub` — the divstep's `δ ↦ 1 - δ`. Instance of `signedSub_correct`. -/
theorem deltaDec_correct {n : ℕ} (L : SubLayout m (n + 1)) (s : State m)
    (hBor0 : ∀ j, s (L.Bor j) = false) (hone : regValZ L.B s (n + 1) = 1)
    (hlo : -2 ^ n ≤ 1 - regValZ L.Sub s (n + 1)) (hhi : 1 - regValZ L.Sub s (n + 1) < 2 ^ n) :
    regValZ L.B (denote (rippleSub L) s) (n + 1) = 1 - regValZ L.Sub s (n + 1) := by
  rw [signedSub_correct L s (by omega) hBor0 (by rw [hone]; simpa using hlo)
    (by rw [hone]; simpa using hhi), hone]

/-! ## Tranche 4e: the reversible nonzero / OR gadget (branch-synthesis prerequisite)

The `0 < δ` control read (`regValZ_pos_iff`, T4c) is `sign bit clear ∧ low bits NOT all zero`. A branch
circuit must turn the "low bits not all zero" half into a single control bit — a reversible OR of the
low wires into a fresh ancilla. This section builds it.

The primitive is a De Morgan OR block `a ← a ∨ (c ∨ w)`... concretely, for a fresh `a` (init `false`),
`orBlock c w a` sets `a = c ∨ w` while restoring `c, w`, via `¬(¬c ∧ ¬w)` (X's + one Toffoli). Chaining
it along an ancilla ladder (`orAccum`) ORs a whole register: `A k` ends `true` iff some low wire is set. -/

/-- **The De Morgan OR block.** With target `a` init `false`, sets `a = s c ∨ s w` and restores `c, w`:
`[X c, X w, CCX c w a, X a, X c, X w]` computes `a ← ¬(¬c ∧ ¬w) = c ∨ w`. One Toffoli. -/
def orBlock (c w a : Fin m) : Circuit m := [.X c, .X w, .CCX c w a, .X a, .X c, .X w]

/-- **`orBlock` correctness.** For distinct wires and `a` init `false`: `a` ends `s c || s w`, and `c, w`
are restored. -/
theorem orBlock_correct {c w a : Fin m} (hca : c ≠ a) (hwa : w ≠ a) (hcw : c ≠ w) (s : State m)
    (ha : s a = false) :
    denote (orBlock c w a) s a = (s c || s w)
      ∧ denote (orBlock c w a) s c = s c ∧ denote (orBlock c w a) s w = s w := by
  have hac := hca.symm; have haw := hwa.symm; have hwc := hcw.symm
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [orBlock, denote_cons, denote_nil, denoteGate] <;>
    simp_all

/-- **Frame lemma for `orBlock`.** A wire distinct from `c, w, a` is untouched. -/
theorem orBlock_apply_of_ne {c w a x : Fin m} (hc : x ≠ c) (hw : x ≠ w) (haa : x ≠ a) (s : State m) :
    denote (orBlock c w a) s x = s x := by
  apply denote_apply_of_forall_not_mem
  intro g hg
  simp only [orBlock, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [gateWires]

/-- **The OR accumulator.** An ancilla ladder `A 0, …, A k` (all init `false`) ORs the low wires
`W 0, …, W (k-1)`: `A (i+1) ← A i ∨ W i`. After `k` blocks, `A k` holds the OR of `W 0 … W (k-1)`. -/
def orAccum (A W : ℕ → Fin m) : ℕ → Circuit m
  | 0 => []
  | k + 1 => orAccum A W k ++ orBlock (A k) (W k) (A (k + 1))

/-- **Frame lemma for `orAccum`.** A wire distinct from every ladder ancilla `A 0..A k` and every input
`W 0..W (k-1)` the `k`-block accumulator touches is left unchanged. -/
theorem orAccum_apply_of_ne {A W : ℕ → Fin m} (x : Fin m) (s : State m) (k : ℕ)
    (hxA : ∀ i, i ≤ k → x ≠ A i) (hxW : ∀ i, i < k → x ≠ W i) :
    denote (orAccum A W k) s x = s x := by
  induction k with
  | zero => rfl
  | succ j ihj =>
    rw [orAccum, denote_append,
      orBlock_apply_of_ne (hxA j (by omega)) (hxW j (by omega)) (hxA (j + 1) (by omega))]
    exact ihj (fun i hi => hxA i (by omega)) (fun i hi => hxW i (by omega))

/-- **The nonzero test (`orAccum` correctness).** For a disjoint, injective ancilla ladder `A` and input
family `W` (ancillas all init `false`), the top ancilla `A k` ends `true` iff SOME input wire `W i`
(`i < k`) is set — a reversible nonzero test — and every input wire is preserved. Proved by induction:
each block ORs the running accumulator with the next wire (`orBlock_correct`), the frame lemma isolating
the untouched wires. -/
theorem orAccum_correct {A W : ℕ → Fin m} (hAinj : Function.Injective A)
    (hWinj : Function.Injective W) (hAW : ∀ i j, A i ≠ W j)
    (s : State m) (hA0 : ∀ i, s (A i) = false) (k : ℕ) :
    (denote (orAccum A W k) s (A k) = true ↔ ∃ i, i < k ∧ s (W i) = true)
      ∧ (∀ j, denote (orAccum A W k) s (W j) = s (W j)) := by
  induction k with
  | zero =>
    refine ⟨?_, fun j => rfl⟩
    rw [orAccum, denote_nil, hA0 0]
    simp
  | succ k ih =>
    obtain ⟨ihOr, ihW⟩ := ih
    have hstep : ∀ w, denote (orAccum A W (k + 1)) s w
        = denote (orBlock (A k) (W k) (A (k + 1))) (denote (orAccum A W k) s) w := by
      intro w; rw [orAccum, denote_append]
    set t := denote (orAccum A W k) s with ht
    -- A (k+1) was untouched by the first k blocks, so still false
    have htA1 : t (A (k + 1)) = false := by
      rw [ht, orAccum_apply_of_ne (A (k + 1)) s k
        (fun i hi h => by have := hAinj h; omega) (fun i _ => hAW (k + 1) i), hA0]
    have hne_cw : A k ≠ W k := hAW k k
    have hne_ca : A k ≠ A (k + 1) := fun h => by have := hAinj h; omega
    have hne_wa : W k ≠ A (k + 1) := fun h => (hAW (k + 1) k h.symm)
    have hblk := orBlock_correct hne_ca hne_wa hne_cw t htA1
    refine ⟨?_, ?_⟩
    · rw [hstep, hblk.1]
      -- t (A k) = OR over i<k ; t (W k) = s (W k)
      rw [ihW k]
      constructor
      · intro h
        rcases Bool.or_eq_true_iff.mp h with hAk | hWk
        · obtain ⟨i, hi, hwi⟩ := ihOr.mp hAk
          exact ⟨i, by omega, hwi⟩
        · exact ⟨k, by omega, hWk⟩
      · rintro ⟨i, hi, hwi⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact Bool.or_eq_true_iff.mpr (Or.inl (ihOr.mpr ⟨i, hlt, hwi⟩))
        · exact Bool.or_eq_true_iff.mpr (Or.inr hwi)
    · intro j
      rw [hstep]
      by_cases hjk : j = k
      · subst hjk
        rw [hblk.2.2, ihW]
      · rw [orBlock_apply_of_ne (fun h => (hAW k j h.symm))
          (fun h => hjk (hWinj h)) (fun h => (hAW (k + 1) j h.symm)), ihW]

/-! ### The branch-control-bit synthesis (`bA = (0<δ) ∧ Odd g`)

Once the three control bits are on wires — `sign_clear` (`¬` δ's sign bit), `nonzero_δ` (`orAccum`'s
output), `odd_g` (`g`'s wire 0) — the branch-A control `bA = sign_clear ∧ nonzero_δ ∧ odd_g` is one clean
3-way AND into a fresh ancilla, with a scratch ancilla uncomputed. -/

/-- **3-way AND into a fresh ancilla.** `[CCX a b u, CCX u c t, CCX a b u]`: with scratch `u` and target
`t` both `false`, sets `t = a ∧ b ∧ c` and restores `u` to `false` (compute–copy–uncompute). Two
Toffolis (the third restores the scratch). -/
def and3 (a b c u t : Fin m) : Circuit m := [.CCX a b u, .CCX u c t, .CCX a b u]

/-- **`and3` correctness.** For pairwise-distinct wires with scratch `u` and target `t` init `false`,
`t` ends `s a && s b && s c` and `u` is restored to `false`. This synthesises the branch-A control bit
`(0<δ) ∧ Odd g` (its three inputs being `sign_clear`, `nonzero_δ`, `odd_g`). -/
theorem and3_correct {a b c u t : Fin m}
    (hau : a ≠ u) (hbu : b ≠ u) (hcu : c ≠ u) (hat : a ≠ t) (hbt : b ≠ t) (hct : c ≠ t)
    (hut : u ≠ t) (s : State m) (hu : s u = false) (ht : s t = false) :
    denote (and3 a b c u t) s t = (s a && s b && s c)
      ∧ denote (and3 a b c u t) s u = false := by
  have hua := hau.symm; have hub := hbu.symm; have huc := hcu.symm
  have hta := hat.symm; have htb := hbt.symm; have htc := hct.symm; have htu := hut.symm
  refine ⟨?_, ?_⟩ <;>
    simp only [and3, denote_cons, denote_nil, denoteGate] <;>
    simp_all

/-! ## Tranche 4f: the f-recovery `f ← f + 2·g` and the branch-A transformation

The divstep branch A is `(f, g) ↦ (g, (g - f)/2)`. Its `g`-update `g ↦ (g - f)/2` is `gUpdateSub_correct`
(T4b). The `f`-update `f ↦ g` (the old `g`) is the subtle in-place step — naively swapping would destroy
the `g` the g-update needs. The resolution: run the g-update FIRST (so `g` now holds `(g_old - f_old)/2`),
then recover `f' = g_old` by `f ← f + 2·g`, since `f_old + 2·(g_old - f_old)/2 = g_old`. The `+2·g` is
two `cuccaroAdd`s of `g` into `f` (`addTwice_correct`). So branch A = `gUpdateSub ; addTwice` — both
verified stages; no swap, no lost value. -/

/-- **`f ← f + 2·g` via two adders.** Two `cuccaroAdd`s of register `B` into register `A` add `2·B` at
the signed level (the second add reuses the carry-clean ancilla and the preserved `B`). Under a
no-overflow bound on the true `regValZ A + 2·regValZ B`, `A` ends holding exactly that. This is the
divstep branch-A `f`-recovery: with `B = g = (g_old - f_old)/2`, it drives `f` from `f_old` to `g_old`. -/
theorem addTwice_correct {n : ℕ} (L : CuccaroLayout m (n + 1)) (s : State m) (hZ : s L.Z = false)
    (hlo : -2 ^ n ≤ regValZ L.A s (n + 1) + 2 * regValZ L.B s (n + 1))
    (hhi : regValZ L.A s (n + 1) + 2 * regValZ L.B s (n + 1) < 2 ^ n) :
    regValZ L.A (denote (cuccaroAdd L ++ cuccaroAdd L) s) (n + 1)
      = regValZ L.A s (n + 1) + 2 * regValZ L.B s (n + 1) := by
  rw [denote_append]
  set s3 := denote (cuccaroAdd L) s with hs3
  set uA := regValRange L.A s (n + 1) with huA
  set uB := regValRange L.B s (n + 1) with huB
  have h3A : regValRange L.A s3 (n + 1) = (uA + uB) % 2 ^ (n + 1) := cuccaroAdd_correct L s hZ
  have h3B : regValRange L.B s3 (n + 1) = uB := by
    rw [huB]; unfold regValRange; apply Finset.sum_congr rfl
    intro k hk; rw [Finset.mem_range] at hk
    rw [hs3, cuccaroAdd_preserves_B L s hZ k hk]
  have h3Z : s3 L.Z = false := by rw [hs3]; exact cuccaroAdd_ancilla_clean L s hZ
  have h4A : regValRange L.A (denote (cuccaroAdd L) s3) (n + 1) = (uA + 2 * uB) % 2 ^ (n + 1) := by
    rw [cuccaroAdd_correct L s3 h3Z, h3A, h3B, Nat.mod_add_mod]
    congr 1; ring
  calc regValZ L.A (denote (cuccaroAdd L) s3) (n + 1)
      = signedRep (n + 1) (((uA + 2 * uB) % 2 ^ (n + 1) : ℕ) : ℤ) := by
        unfold regValZ; rw [h4A]
    _ = signedRep (n + 1) (regValZ L.A s (n + 1) + 2 * regValZ L.B s (n + 1)) := by
        apply signedRep_congr
        refine (natCast_mod_modEq (uA + 2 * uB) (n + 1)).trans ?_
        push_cast
        have hA := (signedRep_modEq (n + 1) (uA : ℤ)).symm
        have hB := (signedRep_modEq (n + 1) (uB : ℤ)).symm
        exact hA.add ((hB.mul_left 2))
    _ = regValZ L.A s (n + 1) + 2 * regValZ L.B s (n + 1) :=
        signedRep_of_mem (n + 1) (by omega) hlo hhi

/-- **Branch-A recovery identity.** For `f, g` odd, the `sub ; halve ; add-2g` sequence yields the
divstep branch-A pair `(g, (g-f)/2)`: after the g-update the g-register holds `(g-f)/2`, and
`f + 2·((g-f)/2) = g` recovers `f' = g`. This is the arithmetic that makes `gUpdateSub` (the g-update)
and `addTwice` (the f-recovery, with `B = g` now holding `(g-f)/2`) compose to `divstep`'s branch A
`(f, g) ↦ (g, (g-f)/2)` — in place, with no swap and no value destroyed. -/
theorem branchA_recovers {f g : ℤ} (hf : Odd f) (hg : Odd g) :
    f + 2 * ((g - f) / 2) = g := by
  rw [Int.mul_ediv_cancel' (even_iff_two_dvd.mp (hg.sub_odd hf))]; ring

end ECDLP.Safegcd.Circuit
