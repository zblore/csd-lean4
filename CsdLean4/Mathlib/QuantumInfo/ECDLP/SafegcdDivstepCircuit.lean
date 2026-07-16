import CsdLean4.Mathlib.QuantumInfo.Reversible.CuccaroAdd
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularSub
import CsdLean4.Mathlib.QuantumInfo.ECDLP.SafegcdDivstep

/-!
# The value-faithful safegcd divstep circuit — TRANCHES 1–2  (ECDLP L6, #36c-2)

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

end ECDLP.Safegcd.Circuit
