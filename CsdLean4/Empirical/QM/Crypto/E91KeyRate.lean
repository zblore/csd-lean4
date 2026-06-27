import CsdLean4.Empirical.QM.Crypto.E91
import CsdLean4.Empirical.QM.Protocols.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Empirical/QM: E91 device-independent asymptotic secret-key rate

**Category:** 3-Local (QM-validity content, no CSD ontology).

Builds the **key-rate layer** on top of the E91 certification
(`Crypto/E91.lean`): from a certified CHSH value `S ∈ (2, 2√2]` it produces the
standard device-independent one-way **asymptotic** secret-key rate and ties it
to the reusable `Protocols` interface.

## The bound

The collective-attack DIQKD key rate (Acín–Brunner–Gisin–Massar–Pironio–Scarani
2007; Pironio et al. 2009) is

```
r(S) = 1 − h₂( (1 + √((S/2)² − 1)) / 2 ),
```

with `h₂` the **base-2** binary entropy. Mathlib's `Real.binEntropy` is the
**nat-based** entropy (`binEntropy 2⁻¹ = log 2`, not `1`), so the base-2 form
used here is `Real.binEntropy · / Real.log 2` — this is the only deviation from
the spec's literal `1 − Real.binEntropy …` formula and is forced by the unit
convention (`r(2) = 0` requires `h₂(1/2) = 1`, a base-2 fact).

## What this delivers

- `e91KeyRate` — the rate `r(S)` (base-2 normalised).
- `e91_key_rate_pos_of_chsh` — **the headline**: any CHSH violation
  `2 < S ≤ 2√2` (above the LHV ceiling of `lhvCHSH_abs_le_two`) gives a strictly
  positive secret-key rate, hence an extractable key. **Unconditional** (no
  binEntropy-monotonicity hypothesis): the positivity reduces to
  `Real.binEntropy_lt_log_two` at the argument `≠ 1/2`.
- `e91_key_rate_zero_at_classical` / `e91_key_rate_one_at_tsirelson` — the
  boundary values `r(2) = 0` (classical bound, no key) and `r(2√2) = 1`
  (Tsirelson, a full secret bit).
- `e91Protocol`, `e91_protocol_secure`, `e91_chsh_certifies_secure_key` —
  the `Protocols.RealProtocol` instantiation tying the rate to the reusable
  security interface and to the LHV ceiling `e91_eavesdropper_chsh_le_two`
  (= `lhvCHSH_abs_le_two`).
- `e91_eavesdropper_advantage` — the LHV/eavesdropper CHSH advantage (normalised
  by Tsirelson `2√2`) is bounded by the protocol's `SecurityBound.ε = 1/√2`,
  grounded in `lhvCHSH_abs_le_two`. This is what makes `SecurityBound`
  load-bearing rather than decorative.

## Honest scope

This is the **asymptotic** (collective-attack, i.i.d.) DI key rate. The
finite-key correction (smoothing / concentration, min-entropy accounting) is a
**separate later tranche** and is *not* proved here. The device-independence
rests on `lhvCHSH_abs_le_two` (the LHV/eavesdropper CHSH bound proved in
`Crypto/E91.lean`); the rate formula itself is the standard DIQKD bound, imported
as a definition, not re-derived from a finite-key security analysis.

## Source

Acín, Brunner, Gisin, Massar, Pironio, Scarani 2007, *Phys. Rev. Lett.* **98**,
230501; Pironio et al. 2009, *New J. Phys.* **11**, 045021; Ekert 1991,
*Phys. Rev. Lett.* **67**, 661.
-/

open MeasureTheory

namespace CSD
namespace Empirical
namespace QM
namespace E91

variable {S : ℝ}

/-- The E91 device-independent asymptotic secret-key rate at CHSH value `S`:
`r(S) = 1 − h₂((1 + √((S/2)² − 1))/2)`, with `h₂` the base-2 binary entropy
(`Real.binEntropy · / Real.log 2`). See the module docstring for the
nat-vs-bit normalisation. -/
noncomputable def e91KeyRate (S : ℝ) : ℝ :=
  1 - Real.binEntropy ((1 + Real.sqrt ((S / 2) ^ 2 - 1)) / 2) / Real.log 2

/-- **The classical bound gives no key.** At the local-realistic ceiling
`S = 2` the rate vanishes: `r(2) = 0`. (Argument `= 1/2`, `h₂(1/2) = 1`.) -/
theorem e91_key_rate_zero_at_classical : e91KeyRate 2 = 0 := by
  have h0 : ((2 : ℝ) / 2) ^ 2 - 1 = 0 := by norm_num
  have harg : (1 + Real.sqrt (((2 : ℝ) / 2) ^ 2 - 1)) / 2 = 2⁻¹ := by
    rw [h0, Real.sqrt_zero]; norm_num
  unfold e91KeyRate
  rw [harg, Real.binEntropy_two_inv,
    div_self (ne_of_gt (Real.log_pos (by norm_num)))]
  norm_num

/-- **Tsirelson gives a full secret bit.** At the quantum maximum `S = 2√2` the
rate is `r(2√2) = 1`. (Argument `= 1`, `h₂(1) = 0`.) -/
theorem e91_key_rate_one_at_tsirelson : e91KeyRate (2 * Real.sqrt 2) = 1 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hbase : 2 * Real.sqrt 2 / 2 = Real.sqrt 2 := by ring
  have h1 : (2 * Real.sqrt 2 / 2) ^ 2 - 1 = 1 := by rw [hbase, hs2]; norm_num
  have harg : (1 + Real.sqrt ((2 * Real.sqrt 2 / 2) ^ 2 - 1)) / 2 = 1 := by
    rw [h1, Real.sqrt_one]; norm_num
  unfold e91KeyRate
  rw [harg, Real.binEntropy_one]
  norm_num

/-- **Headline: a CHSH violation yields a positive secret-key rate.** For any
certified CHSH value `2 < S ≤ 2√2` — strictly above the local-hidden-variable
ceiling `2` of `lhvCHSH_abs_le_two` — the asymptotic DI key rate is strictly
positive, so a genuine secret key is extractable.

**Positivity uses only `2 < S`; `hS'` is the physical Tsirelson fence, not
load-bearing for positivity.** The argument `(1 + √((S/2)² − 1))/2` is `> 1/2`
(since `S > 2 ⟹ (S/2)² > 1 ⟹ √(…) > 0`), so `Real.binEntropy_lt_log_two` gives
`h < log 2` at the argument `≠ 1/2`, hence `h / log 2 < 1` and
`r = 1 − h/log 2 > 0`. No binEntropy-monotonicity fact is assumed. The
hypothesis `hS'` (`S ≤ 2√2`) records the physical constraint that CHSH cannot
exceed the Tsirelson bound; it is exactly the domain on which the argument is a
valid probability `≤ 1` (`harg_le` below). It is kept for physical faithfulness;
the strictly stronger statement `(2 < S) → 0 < e91KeyRate S` also holds. -/
theorem e91_key_rate_pos_of_chsh (hS : 2 < S) (hS' : S ≤ 2 * Real.sqrt 2) :
    0 < e91KeyRate S := by
  have h1 : (1 : ℝ) < S / 2 := by linarith
  have hp := mul_pos (sub_pos.2 h1) (show (0 : ℝ) < S / 2 + 1 by linarith)
  have hx : 0 < (S / 2) ^ 2 - 1 := by nlinarith [hp]
  have hsqrt_pos : 0 < Real.sqrt ((S / 2) ^ 2 - 1) := Real.sqrt_pos.2 hx
  -- argument is strictly above 1/2
  have hgt : (2 : ℝ)⁻¹ < (1 + Real.sqrt ((S / 2) ^ 2 - 1)) / 2 := by
    rw [lt_div_iff₀ (show (0 : ℝ) < 2 by norm_num)]
    nlinarith [hsqrt_pos]
  have hne : (1 + Real.sqrt ((S / 2) ^ 2 - 1)) / 2 ≠ 2⁻¹ := ne_of_gt hgt
  -- Physical Tsirelson fence (`hS'`): the argument is a valid probability `≤ 1`
  -- exactly on `S ≤ 2√2`. NOT used for positivity (which needs only `2 < S`);
  -- recorded here for physical faithfulness.
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos2 : (0 : ℝ) ≤ 2 * Real.sqrt 2 + S := by nlinarith [Real.sqrt_nonneg 2, hS]
  have hxle : (S / 2) ^ 2 - 1 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hS') hpos2, hs2]
  have harg_le : (1 + Real.sqrt ((S / 2) ^ 2 - 1)) / 2 ≤ 1 := by
    rw [div_le_one (show (0 : ℝ) < 2 by norm_num)]
    have hle : Real.sqrt ((S / 2) ^ 2 - 1) ≤ 1 := by
      have := Real.sqrt_le_sqrt hxle
      rwa [Real.sqrt_one] at this
    linarith
  -- positivity: h < log 2 ⟹ h/log 2 < 1 ⟹ r > 0
  have hlt : Real.binEntropy ((1 + Real.sqrt ((S / 2) ^ 2 - 1)) / 2) < Real.log 2 :=
    Real.binEntropy_lt_log_two.2 hne
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hfrac :
      Real.binEntropy ((1 + Real.sqrt ((S / 2) ^ 2 - 1)) / 2) / Real.log 2 < 1 :=
    (div_lt_one hlog).2 hlt
  unfold e91KeyRate
  linarith [hfrac, harg_le]

/-! ### The reusable `Protocols` instantiation -/

/-- The eavesdropper's security bound for the E91 protocol: the classical (LHV)
CHSH ceiling `2` normalised by the Tsirelson value `2√2` to a `[0,1]` advantage,
`ε = 1/√2`. The honest reading is "no local eavesdropper reproduces a CHSH
fraction above `1/√2`"; the quantum protocol exceeds it. A minimal stand-in, not
a min-entropy accounting. -/
noncomputable def e91Security : Protocols.SecurityBound where
  ε := 1 / Real.sqrt 2
  ε_nonneg := by positivity
  ε_le_one := by
    rw [div_le_one (Real.sqrt_pos.2 (by norm_num))]
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by norm_num)

/-- The E91 device-independent protocol at observed CHSH value `S`, packaged as
a `Protocols.RealProtocol`: asymptotic key rate `e91KeyRate S` with the LHV
security bound `e91Security`. -/
noncomputable def e91Protocol (S : ℝ) : Protocols.RealProtocol where
  keyRate := e91KeyRate S
  security := e91Security

/-- The LHV/eavesdropper CHSH ceiling, re-exported as the E91 certification
premise: any local-hidden-variable eavesdropper has `|S| ≤ 2`, so an observed
`S > 2` certifies the channel. Direct theorem-level reuse of
`lhvCHSH_abs_le_two`. -/
theorem e91_eavesdropper_chsh_le_two
    {Λ : Type*} [MeasurableSpace Λ] {SettingA SettingB : Type*}
    (μ : Measure Λ) [IsProbabilityMeasure μ]
    (A : SettingA → Λ → ℝ) (B : SettingB → Λ → ℝ)
    (hA : ∀ a, Measurable (A a)) (hB : ∀ b, Measurable (B b))
    (hApm : ∀ a l, A a l = 1 ∨ A a l = -1) (hBpm : ∀ b l, B b l = 1 ∨ B b l = -1)
    (a a' : SettingA) (b b' : SettingB) :
    |lhvCHSH μ A B a a' b b'| ≤ 2 :=
  lhvCHSH_abs_le_two μ A B hA hB hApm hBpm a a' b b'

/-- **The eavesdropper's advantage is bounded by the protocol's `SecurityBound`.**
Any local-hidden-variable eavesdropper's CHSH value, normalised by the Tsirelson
maximum `2√2` to a `[0,1]` advantage fraction, is bounded by the protocol's
declared security bound `(e91Protocol S).security.ε = 1/√2`. This is the genuine
consumer that makes `SecurityBound`/`RealProtocol.security` load-bearing: the
field is not decoration, it is a *proved* upper bound on the LHV/eavesdropper
advantage, **grounded in `lhvCHSH_abs_le_two`** (`lhvCHSH ≤ |lhvCHSH| ≤ 2`,
divided by the positive `2√2`, with `2/(2√2) = 1/√2`), not asserted. -/
theorem e91_eavesdropper_advantage
    {Λ : Type*} [MeasurableSpace Λ] {SettingA SettingB : Type*}
    (μ : Measure Λ) [IsProbabilityMeasure μ]
    (A : SettingA → Λ → ℝ) (B : SettingB → Λ → ℝ)
    (hA : ∀ a, Measurable (A a)) (hB : ∀ b, Measurable (B b))
    (hApm : ∀ a l, A a l = 1 ∨ A a l = -1) (hBpm : ∀ b l, B b l = 1 ∨ B b l = -1)
    (a a' : SettingA) (b b' : SettingB) :
    lhvCHSH μ A B a a' b b' / (2 * Real.sqrt 2) ≤ (e91Protocol S).security.ε := by
  have hbound : lhvCHSH μ A B a a' b b' ≤ 2 :=
    le_trans (le_abs_self _) (lhvCHSH_abs_le_two μ A B hA hB hApm hBpm a a' b b')
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have h2s : (2 : ℝ) * Real.sqrt 2 ≠ 0 := by positivity
  have key : (2 : ℝ) / (2 * Real.sqrt 2) = 1 / Real.sqrt 2 := by
    rw [div_eq_div_iff h2s hs]; ring
  show lhvCHSH μ A B a a' b b' / (2 * Real.sqrt 2) ≤ 1 / Real.sqrt 2
  rw [← key]
  gcongr

/-- **The E91 protocol at a certified CHSH violation is secure.** For
`2 < S ≤ 2√2`, the `RealProtocol` `e91Protocol S` has a positive key rate, i.e.
`RealProtocol.secure`. Immediate from `e91_key_rate_pos_of_chsh`. -/
theorem e91_protocol_secure (hS : 2 < S) (hS' : S ≤ 2 * Real.sqrt 2) :
    (e91Protocol S).secure := by
  show 0 < e91KeyRate S
  exact e91_key_rate_pos_of_chsh hS hS'

/-- **CHSH-to-key-rate capstone (assembled DI tie).** A certified CHSH violation
`2 < S ≤ 2√2` simultaneously: (1) certifies the channel against every
local-hidden-variable eavesdropper — the **proved** ceiling `|S| ≤ 2`
(`lhvCHSH_abs_le_two`), which `S > 2` exceeds — and (2) yields a secure E91
`RealProtocol` (positive key rate) that emulates any ideal key length over enough
signals. The LHV bound is a theorem-level conjunct here (not a prose remark): the
certification and the positive key rate are one assembled statement. Ties the
key-rate layer to the reusable `Protocols` interface (`secure`, `emulates`,
`secure_emulates`). -/
theorem e91_chsh_certifies_secure_key (hS : 2 < S) (hS' : S ≤ 2 * Real.sqrt 2) :
    (∀ {Λ : Type*} [MeasurableSpace Λ] {SettingA SettingB : Type*}
        (μ : Measure Λ) [IsProbabilityMeasure μ]
        (A : SettingA → Λ → ℝ) (B : SettingB → Λ → ℝ),
        (∀ a, Measurable (A a)) → (∀ b, Measurable (B b)) →
        (∀ a l, A a l = 1 ∨ A a l = -1) → (∀ b l, B b l = 1 ∨ B b l = -1) →
        ∀ (xa xa' : SettingA) (xb xb' : SettingB),
          |lhvCHSH μ A B xa xa' xb xb'| ≤ 2)
      ∧ (e91Protocol S).secure
      ∧ (∀ I : Protocols.IdealQKD, ∃ n : ℕ, (e91Protocol S).emulates I n) := by
  have hsec : (e91Protocol S).secure := e91_protocol_secure hS hS'
  refine ⟨?_, hsec, fun I => Protocols.secure_emulates _ hsec I⟩
  intro Λ _ SettingA SettingB μ _ A B hA hB hApm hBpm xa xa' xb xb'
  exact lhvCHSH_abs_le_two μ A B hA hB hApm hBpm xa xa' xb xb'

end E91
end QM
end Empirical
end CSD
