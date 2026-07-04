import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic

/-!
# The Bernstein-Yang safegcd divstep: an exhibited function with a VERIFIED GCD invariant

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

This file promotes the corpus's safegcd modular inversion from TRUSTED toward VERIFIED. The prior
state (`SafegcdInversion.lean`) had the value ride on `binGcdInv = ZMod.inv` (a definitional
unfolding, NOT an algorithm-correctness proof) and the `2n` divstep count as a documented op-count
model with no exhibited divstep. Here the divstep transition is exhibited as a concrete function and
its central algebraic invariant is a genuine theorem.

## The divstep (Bernstein-Yang, CHES 2019)

The transition `(δ, f, g) ↦ (δ', f', g')` with `f` kept odd throughout:

* if `δ > 0` and `g` odd:    `(δ', f', g') = (1 - δ, g, (g - f) / 2)`;
* else if `g` odd:           `(δ', f', g') = (1 + δ, f, (g + f) / 2)`;
* else (`g` even):           `(δ', f', g') = (1 + δ, f, g / 2)`.

The `(g & 1)·f` term of the reference is split into the two `Odd g` branches. Each halving is EXACT
(the numerator is even in its branch), so the divstep is a genuine `ℤ³ → ℤ³` function, not a partial
one.

## What is VERIFIED here (genuine theorems, not `ZMod.inv` unfoldings)

* **Layer 1 (the function).** `divstep` is exhibited; `divstep_fst_odd` proves `f` stays odd; small
  instances are machine-checked (`#eval` + `decide`).
* **Layer 2 (the GCD invariant, the algebraic core).** `divstep_gcd : Odd f → Int.gcd f' g' =
  Int.gcd f g`. This is the single most valuable target: the divstep genuinely PRESERVES the gcd, a
  real theorem proved from parity + coprimality-with-2, NOT an unfolding of `Nat.gcd` / `ZMod.inv`.
* **Iterated invariant.** `divstepIter_gcd`: any number of divsteps preserves the gcd.
* **Layer 3a (correctness modulo termination).** `divstepIter_natAbs_of_g_zero`: WHEN the running `g`
  reaches `0` after `k` divsteps, the running `|f|` EQUALS `Int.gcd f₀ g₀`. So the divstep loop, once
  it terminates, computes the gcd. (This is conditional on `g = 0`; TERMINATION -- that `g` reaches
  `0` within the Bernstein-Yang `2·bits` bound -- is the named residual, requiring the potential /
  transition-matrix argument, not attempted here.)
* **Layer 3b (Bezout cofactor tracking, up to the `2^k` scale).** `divstepIter_bezout`: at every step
  `2^k · f_k` and `2^k · g_k` are integer linear combinations of `f₀, g₀`. This is the honest form of
  the cofactor invariant: the divstep's exact halvings force the `2^k` denominator that Bernstein-Yang
  removes with a final `2^{-k}` (Montgomery) correction.

## What remains TRUSTED / DOCUMENTED (the named residual)

* **TERMINATION**: the `g → 0` within `2·bits` divstep bound (`safegcdDivsteps = 2n`). Not proved;
  requires the Bernstein-Yang potential-function / transition-matrix analysis.
* **The reversible bit-circuit**: a divstep gadget in the Reversible DSL whose `denote`/`evalProgram`
  equals `divstep`, composing the verified `ModularSub` / halving gadgets. The op-count model
  `divstepToffoli` in `SafegcdInversion.lean` is over this NOT-yet-exhibited circuit.
* **The final `2^{-k}` correction** tying `divstepIter_bezout` at `g = 0` to `a⁻¹ mod N`.

So the promotion is precise: the divstep transition is now a proved-correct gcd-preserving function
(value side genuinely upgraded, no longer a `ZMod.inv` unfolding), while termination and the bit-level
reversible circuit remain the documented residue.
-/

namespace ECDLP.Safegcd

/-! ### Generic gcd helpers (parity / coprimality with 2) -/

/-- Two integers have equal `Int.gcd` when they have the same common divisors. The workhorse for the
per-branch invariants: it reduces a gcd equality to a divisibility bi-implication, avoiding any
reasoning about `Nat.gcd`'s recursion. -/
theorem gcd_eq_of_dvd_iff {A B C D : ℤ}
    (h : ∀ d : ℤ, (d ∣ A ∧ d ∣ B) ↔ (d ∣ C ∧ d ∣ D)) :
    Int.gcd A B = Int.gcd C D := by
  apply Nat.dvd_antisymm
  · have h1 := (h ((Int.gcd A B : ℤ))).mp ⟨Int.gcd_dvd_left A B, Int.gcd_dvd_right A B⟩
    exact Int.dvd_gcd h1.1 h1.2
  · have h2 := (h ((Int.gcd C D : ℤ))).mpr ⟨Int.gcd_dvd_left C D, Int.gcd_dvd_right C D⟩
    exact Int.dvd_gcd h2.1 h2.2

/-- A divisor of an odd integer is odd. -/
theorem odd_of_dvd_odd {d g : ℤ} (hdg : d ∣ g) (hg : Odd g) : Odd d := by
  rcases Int.even_or_odd d with he | ho
  · exfalso
    obtain ⟨r, hr⟩ := he
    obtain ⟨e, he'⟩ := hdg
    obtain ⟨m, hm⟩ := hg
    have : 2 * m + 1 = 2 * (r * e) := by rw [← hm, he', hr]; ring
    omega
  · exact ho

/-- An odd integer is coprime to `2` (explicit Bezout witness, no name-guessing). -/
theorem isCoprime_two_of_odd {d : ℤ} (ho : Odd d) : IsCoprime d 2 := by
  obtain ⟨k, hk⟩ := ho
  exact ⟨1, -k, by rw [hk]; ring⟩

/-- `Int.gcd a (-b) = Int.gcd a b` (via `natAbs`). -/
theorem gcd_neg_right (a b : ℤ) : Int.gcd a (-b) = Int.gcd a b := by
  simp [Int.gcd, Int.natAbs_neg]

/-- **Halving a gcd against an odd argument.** For `m` odd, `Int.gcd m (2·k) = Int.gcd m k`: the
factor of `2` is coprime to the odd `m`, so it cannot be a common divisor. Genuine (not a `Nat.gcd`
unfolding): proved through `gcd_eq_of_dvd_iff` + `odd_of_dvd_odd` + coprimality with `2`. -/
theorem gcd_two_mul_right_of_odd {m k : ℤ} (hm : Odd m) :
    Int.gcd m (2 * k) = Int.gcd m k := by
  apply gcd_eq_of_dvd_iff
  intro d
  constructor
  · rintro ⟨hdm, hd2k⟩
    exact ⟨hdm, (isCoprime_two_of_odd (odd_of_dvd_odd hdm hm)).dvd_of_dvd_mul_left hd2k⟩
  · rintro ⟨hdm, hdk⟩
    exact ⟨hdm, hdk.mul_left 2⟩

/-! ### Layer 1: the divstep as an exhibited function -/

/-- **The Bernstein-Yang divstep** `(δ, f, g) ↦ (δ', f', g')`. The `(g & 1)·f` term of the reference is
split into the two `Odd g` branches; each `/2` is exact in its branch (`divstep_fst_odd` +
`divstep_gcd` depend on this). Returns the full triple `(δ', f', g')`. -/
def divstep (d f g : ℤ) : ℤ × ℤ × ℤ :=
  if 0 < d ∧ Odd g then (1 - d, g, (g - f) / 2)
  else if Odd g then (1 + d, f, (g + f) / 2)
  else (1 + d, f, g / 2)

/-- **`f` stays odd.** Every branch sets `f'` to either the (odd, by branch condition) `g` or the
old (odd, by hypothesis) `f`, so oddness of the `f`-register is a divstep invariant. -/
theorem divstep_fst_odd {d f g : ℤ} (hf : Odd f) : Odd (divstep d f g).2.1 := by
  unfold divstep
  split_ifs with h1 h2
  · exact h1.2
  · exact hf
  · exact hf

/-! ### Layer 2: the GCD invariant (the algebraic core) -/

/-- **THE GCD INVARIANT (the algebraic core -- a genuine theorem).** One divstep preserves the gcd of
the `(f, g)` pair: `Int.gcd f' g' = Int.gcd f g`, for `f` odd. This is the load-bearing correctness
fact that makes the divstep recurrence genuinely COMPUTE the gcd (and hence, at termination, the
Bezout cofactor / modular inverse). It is proved from parity and coprimality-with-`2`, NOT by
unfolding `Nat.gcd` or `ZMod.inv`.

Per branch (with `h := ` the halved register):
* `δ>0, g` odd: `(f', g') = (g, (g-f)/2)`, and `gcd g h = gcd f g` since `f = g - 2h`;
* `g` odd:      `(f', g') = (f, (g+f)/2)`, and `gcd f h = gcd f g` since `g = 2h - f`;
* `g` even:     `(f', g') = (f, g/2)`,     and `gcd f h = gcd f g` since `g = 2h`.
Each step uses translation invariance (`Int.gcd_add_mul_right_right`) and odd-halving
(`gcd_two_mul_right_of_odd`). -/
theorem divstep_gcd {d f g : ℤ} (hf : Odd f) :
    Int.gcd (divstep d f g).2.1 (divstep d f g).2.2 = Int.gcd f g := by
  unfold divstep
  split_ifs with h1 h2
  · -- (f', g') = (g, (g - f)/2), with g odd
    obtain ⟨_, hg⟩ := h1
    have hdvd : (2 : ℤ) ∣ (g - f) := even_iff_two_dvd.mp (Odd.sub_odd hg hf)
    have h2h : 2 * ((g - f) / 2) = g - f := Int.mul_ediv_cancel' hdvd
    show Int.gcd g ((g - f) / 2) = Int.gcd f g
    set h := (g - f) / 2 with hh
    have hfeq : f = g - 2 * h := by linarith [h2h]
    rw [Int.gcd_comm f g, hfeq,
      show g - 2 * h = (-(2 * h)) + 1 * g by ring,
      Int.gcd_add_mul_right_right, gcd_neg_right, gcd_two_mul_right_of_odd hg]
  · -- (f', g') = (f, (g + f)/2), with g odd
    have hg : Odd g := h2
    have hdvd : (2 : ℤ) ∣ (g + f) := even_iff_two_dvd.mp (Odd.add_odd hg hf)
    have h2h : 2 * ((g + f) / 2) = g + f := Int.mul_ediv_cancel' hdvd
    show Int.gcd f ((g + f) / 2) = Int.gcd f g
    set h := (g + f) / 2 with hh
    have hgeq : g = 2 * h - f := by linarith [h2h]
    rw [hgeq, show 2 * h - f = (2 * h) + (-1) * f by ring,
      Int.gcd_add_mul_right_right, gcd_two_mul_right_of_odd hf]
  · -- (f', g') = (f, g/2), with g even
    have hg : Even g := (Int.even_or_odd g).resolve_right h2
    have hdvd : (2 : ℤ) ∣ g := even_iff_two_dvd.mp hg
    have h2h : 2 * (g / 2) = g := Int.mul_ediv_cancel' hdvd
    show Int.gcd f (g / 2) = Int.gcd f g
    set h := g / 2 with hh
    have hgeq : g = 2 * h := h2h.symm
    rw [hgeq, gcd_two_mul_right_of_odd hf]

/-! ### The iterated divstep and its invariants -/

/-- Iterate the divstep `n` times on a full `(δ, f, g)` state. -/
def divstepIter (n : ℕ) (s : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (fun t : ℤ × ℤ × ℤ => divstep t.1 t.2.1 t.2.2)^[n] s

@[simp] theorem divstepIter_zero (s : ℤ × ℤ × ℤ) : divstepIter 0 s = s := rfl

theorem divstepIter_succ (n : ℕ) (s : ℤ × ℤ × ℤ) :
    divstepIter (n + 1) s
      = (fun t : ℤ × ℤ × ℤ => divstep t.1 t.2.1 t.2.2) (divstepIter n s) := by
  simp only [divstepIter, Function.iterate_succ']
  rfl

/-- The `f`-register stays odd under any number of divsteps. -/
theorem divstepIter_fst_odd {s : ℤ × ℤ × ℤ} (hf : Odd s.2.1) (n : ℕ) :
    Odd (divstepIter n s).2.1 := by
  induction n with
  | zero => simpa using hf
  | succ k ih =>
    rw [divstepIter_succ]
    exact divstep_fst_odd ih

/-- **Iterated GCD invariant.** Any number of divsteps preserves the gcd of the `(f, g)` pair:
`Int.gcd (divstepIter n s).f (divstepIter n s).g = Int.gcd s.f s.g`, for `s.f` odd. Genuine theorem,
by induction over `divstep_gcd` (each step needs, and re-establishes, oddness of `f`). -/
theorem divstepIter_gcd {s : ℤ × ℤ × ℤ} (hf : Odd s.2.1) (n : ℕ) :
    Int.gcd (divstepIter n s).2.1 (divstepIter n s).2.2 = Int.gcd s.2.1 s.2.2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [divstepIter_succ]
    have hodd : Odd (divstepIter k s).2.1 := divstepIter_fst_odd hf k
    calc
      Int.gcd (divstep (divstepIter k s).1 (divstepIter k s).2.1 (divstepIter k s).2.2).2.1
          (divstep (divstepIter k s).1 (divstepIter k s).2.1 (divstepIter k s).2.2).2.2
          = Int.gcd (divstepIter k s).2.1 (divstepIter k s).2.2 := divstep_gcd hodd
      _ = Int.gcd s.2.1 s.2.2 := ih

/-! ### Layer 3a: correctness modulo termination -/

/-- **Correctness modulo termination.** WHEN the running `g` reaches `0` after `k` divsteps, the
running `|f|` EQUALS `Int.gcd f₀ g₀`. So once the divstep loop terminates (`g = 0`), the surviving
`f`-register carries `±gcd(f₀, g₀)` -- the divstep genuinely computes the gcd. Conditional on the
`g = 0` hypothesis; TERMINATION (that `g` reaches `0` within the `2·bits` bound) is the named
residual. Proof: `gcd f 0 = |f|` (`Int.gcd_zero_right`) combined with the iterated invariant. -/
theorem divstepIter_natAbs_of_g_zero {s : ℤ × ℤ × ℤ} (hf : Odd s.2.1) {n : ℕ}
    (hg : (divstepIter n s).2.2 = 0) :
    (divstepIter n s).2.1.natAbs = Int.gcd s.2.1 s.2.2 := by
  have hinv := divstepIter_gcd hf n
  rw [hg, Int.gcd_zero_right] at hinv
  exact hinv

/-- **Coprime specialisation.** For coprime `(f₀, g₀)`, at termination the `f`-register is `±1`
(`|f| = 1`). This is the shape the modular inversion consumes: with `f₀ = N` (odd modulus), `g₀ = a`
coprime to `N`, the loop drives `f` to a unit, and the paired Bezout cofactor (tracked up to the
`2^k` scale by `divstepIter_bezout`) is `a⁻¹ mod N` after the final `2^{-k}` correction. -/
theorem divstepIter_natAbs_one_of_coprime {s : ℤ × ℤ × ℤ} (hf : Odd s.2.1) {n : ℕ}
    (hcop : Int.gcd s.2.1 s.2.2 = 1) (hg : (divstepIter n s).2.2 = 0) :
    (divstepIter n s).2.1.natAbs = 1 := by
  rw [divstepIter_natAbs_of_g_zero hf hg, hcop]

/-! ### Layer 3b: Bezout cofactor tracking (up to the `2^k` scale) -/

/-- `x` is an integer linear combination of `f₀` and `g₀`. -/
def IsBezout (f0 g0 x : ℤ) : Prop := ∃ a b : ℤ, x = a * f0 + b * g0

theorem IsBezout.left (f0 g0 : ℤ) : IsBezout f0 g0 f0 := ⟨1, 0, by ring⟩
theorem IsBezout.right (f0 g0 : ℤ) : IsBezout f0 g0 g0 := ⟨0, 1, by ring⟩

theorem IsBezout.add {f0 g0 x y : ℤ} (hx : IsBezout f0 g0 x) (hy : IsBezout f0 g0 y) :
    IsBezout f0 g0 (x + y) := by
  obtain ⟨a, b, rfl⟩ := hx; obtain ⟨c, d, rfl⟩ := hy
  exact ⟨a + c, b + d, by ring⟩

theorem IsBezout.sub {f0 g0 x y : ℤ} (hx : IsBezout f0 g0 x) (hy : IsBezout f0 g0 y) :
    IsBezout f0 g0 (x - y) := by
  obtain ⟨a, b, rfl⟩ := hx; obtain ⟨c, d, rfl⟩ := hy
  exact ⟨a - c, b - d, by ring⟩

theorem IsBezout.smul (c : ℤ) {f0 g0 x : ℤ} (hx : IsBezout f0 g0 x) :
    IsBezout f0 g0 (c * x) := by
  obtain ⟨a, b, rfl⟩ := hx
  exact ⟨c * a, c * b, by ring⟩

/-- **Bezout cofactor tracking (up to the `2^k` scale).** At every step, `2^k · f_k` and `2^k · g_k`
are integer linear combinations of the initial `f₀, g₀`. This is the HONEST form of the cofactor
invariant: the divstep's exact halvings force the `2^k` denominator, which Bernstein-Yang removes with
a single final `2^{-k}` (Montgomery-style) correction. Proved by induction; each branch expresses
`2^{k+1}·f_{k+1}` and `2^{k+1}·g_{k+1}` as `±`-combinations / doublings of `2^k·f_k, 2^k·g_k` using
the exact-halving identity. Termination + the `2^{-k}` correction (tying this to `a⁻¹ mod N` at
`g = 0`) are the named residual. -/
theorem divstepIter_bezout (s : ℤ × ℤ × ℤ) (hf : Odd s.2.1) (n : ℕ) :
    IsBezout s.2.1 s.2.2 (2 ^ n * (divstepIter n s).2.1)
      ∧ IsBezout s.2.1 s.2.2 (2 ^ n * (divstepIter n s).2.2) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simpa using IsBezout.left s.2.1 s.2.2
    · simpa using IsBezout.right s.2.1 s.2.2
  | succ k ih =>
    obtain ⟨ihf, ihg⟩ := ih
    have hoddk : Odd (divstepIter k s).2.1 := divstepIter_fst_odd hf k
    rw [divstepIter_succ]
    set t := divstepIter k s with ht
    -- Abbreviations for the running registers at step k.
    set f := t.2.1 with hfdef
    set g := t.2.2 with hgdef
    set d := t.1 with hddef
    -- ihf : IsBezout .. (2^k * f), ihg : IsBezout .. (2^k * g)
    show IsBezout s.2.1 s.2.2 (2 ^ (k + 1) * (divstep d f g).2.1)
      ∧ IsBezout s.2.1 s.2.2 (2 ^ (k + 1) * (divstep d f g).2.2)
    have hpow : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by ring
    unfold divstep
    split_ifs with h1 h2
    · -- (f', g') = (g, (g-f)/2), g odd
      obtain ⟨_, hg⟩ := h1
      have hdvd : (2 : ℤ) ∣ (g - f) := even_iff_two_dvd.mp (Odd.sub_odd hg hoddk)
      have h2h : 2 * ((g - f) / 2) = g - f := Int.mul_ediv_cancel' hdvd
      refine ⟨?_, ?_⟩
      · -- 2^{k+1} * g = 2 * (2^k * g)
        have : (2 : ℤ) ^ (k + 1) * g = 2 * (2 ^ k * g) := by rw [hpow]; ring
        rw [this]; exact ihg.smul 2
      · -- 2^{k+1} * ((g-f)/2) = 2^k * (g - f) = 2^k*g - 2^k*f
        have : (2 : ℤ) ^ (k + 1) * ((g - f) / 2) = 2 ^ k * g - 2 ^ k * f := by
          have e1 : (2 : ℤ) ^ (k + 1) * ((g - f) / 2) = 2 ^ k * (2 * ((g - f) / 2)) := by
            rw [hpow]; ring
          rw [e1, h2h]; ring
        rw [this]; exact ihg.sub ihf
    · -- (f', g') = (f, (g+f)/2), g odd
      have hg : Odd g := h2
      have hdvd : (2 : ℤ) ∣ (g + f) := even_iff_two_dvd.mp (Odd.add_odd hg hoddk)
      have h2h : 2 * ((g + f) / 2) = g + f := Int.mul_ediv_cancel' hdvd
      refine ⟨?_, ?_⟩
      · have : (2 : ℤ) ^ (k + 1) * f = 2 * (2 ^ k * f) := by rw [hpow]; ring
        rw [this]; exact ihf.smul 2
      · have : (2 : ℤ) ^ (k + 1) * ((g + f) / 2) = 2 ^ k * g + 2 ^ k * f := by
          have e1 : (2 : ℤ) ^ (k + 1) * ((g + f) / 2) = 2 ^ k * (2 * ((g + f) / 2)) := by
            rw [hpow]; ring
          rw [e1, h2h]; ring
        rw [this]; exact ihg.add ihf
    · -- (f', g') = (f, g/2), g even
      have hg : Even g := (Int.even_or_odd g).resolve_right h2
      have hdvd : (2 : ℤ) ∣ g := even_iff_two_dvd.mp hg
      have h2h : 2 * (g / 2) = g := Int.mul_ediv_cancel' hdvd
      refine ⟨?_, ?_⟩
      · have : (2 : ℤ) ^ (k + 1) * f = 2 * (2 ^ k * f) := by rw [hpow]; ring
        rw [this]; exact ihf.smul 2
      · have : (2 : ℤ) ^ (k + 1) * (g / 2) = 2 ^ k * g := by
          have e1 : (2 : ℤ) ^ (k + 1) * (g / 2) = 2 ^ k * (2 * (g / 2)) := by
            rw [hpow]; ring
          rw [e1, h2h]
        rw [this]; exact ihg

/-! ### Layer 1 machine-checks (small instances) -/

/-- `divstep 1 5 3 = (0, 3, -1)` (the `δ>0 ∧ g` odd branch): `(1-1, 3, (3-5)/2)`. -/
example : divstep 1 5 3 = (0, 3, -1) := by decide

/-- gcd preserved on a concrete instance: `gcd 3 (-1) = 1 = gcd 5 3`. -/
example : Int.gcd (divstep 1 5 3).2.1 (divstep 1 5 3).2.2 = Int.gcd 5 3 := by decide

/-- `divstep (-1) 5 4 = (0, 5, 2)` (the `g` even branch): `(1+(-1), 5, 4/2)`. -/
example : divstep (-1) 5 4 = (0, 5, 2) := by decide

end ECDLP.Safegcd
