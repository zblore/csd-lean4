/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.Bell
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Empirical: E91 device-independent certification — the local-hidden-variable CHSH bound

**Category:** 3-Local. The LHV CHSH `≤ 2` bound is QM-generic (a theorem about a
hidden-variable probability space, no CSD ontology) and promotion-ready to
2-Framework; the QM tie-in re-uses `Bell.lean`'s Tsirelson saturation.

**Scope (honest).** What is proved is the **correlation-level certification**: the
singlet attains `2√2` while every LHV model is `≤ 2`, so no local-realistic
description reproduces the quantum correlations (the basis of E91's
eavesdropper-detection). This is *not* a full cryptographic security proof — there
is no key-rate, finite-key, or general-adversary analysis here. "Device-independent"
refers to the certification being LHV-model-agnostic, not to a security theorem.

## What this closes

`Empirical/QM/Bell.lean` carries `bellClassicalBoundValue : ℝ := 2` as a *named
constant*, explicitly **not** a theorem that any local-hidden-variable (LHV) model
satisfies `|S| ≤ 2` (see its docstring). This file supplies that missing theorem,
turning the Bell-1964 classical bound into genuine Lean content and giving the
device-independent (Ekert 1991) security witness real teeth:

- `lhvCHSH_abs_le_two` — **the Bell/CHSH inequality.** For *any* hidden-variable
  probability space `(Λ, μ)` and any `±1`-valued local response functions
  `A : SettingA → Λ → ℝ`, `B : SettingB → Λ → ℝ`, the CHSH combination of the
  factorisable correlations `E(a,b) = ∫ A(a,·)·B(b,·) dμ` obeys `|S| ≤ 2`.
- `lhvCHSH_lt_tsirelson` — every LHV CHSH value is `< 2√2`.
- `e91_no_lhv_reproduces_singlet` — the **device-independent security witness**:
  the singlet at canonical angles realises `|S| = 2√2` (Bell A1), while *every*
  LHV model is capped at `2 < 2√2`. So an observed CHSH value at the Tsirelson
  bound certifies that no local-hidden-variable description — in particular no
  local eavesdropper strategy — can have produced the correlations.

## The mathematics

The LHV model is the standard one: a probability space `(Λ, μ)` of hidden
variables and deterministic `±1` response functions, with `factorisable`
correlations `E(a,b) = ∫ A(a,λ) B(b,λ) dμ(λ)`. The bound is the pointwise
Bell–CHSH algebra

```
S(λ) = A(a,λ)B(b,λ) − A(a,λ)B(b',λ) + A(a',λ)B(b,λ) + A(a',λ)B(b',λ) ∈ {−2, +2},
```

so `|S(λ)| ≤ 2` for every `λ` (a 16-way `±1` case split), followed by integral
monotonicity `|∫ S dμ| ≤ ∫ |S| dμ ≤ ∫ 2 dμ = 2` on the probability measure `μ`.
This is Bell's 1964 inequality in the CHSH (Clauser–Horne–Shimony–Holt 1969) form;
the integrand bound is the whole content, the rest is monotonicity of the Bochner
integral.

## Experimental verification

- Ekert 1991: *Phys. Rev. Lett.* **67**, 661 (E91 protocol).
- Clauser, Horne, Shimony, Holt 1969: *Phys. Rev. Lett.* **23**, 880 (CHSH form).
- Loophole-free Bell violations underwriting device-independent QKD: Hensen et al.
  2015, *Nature* **526**, 682; Giustina et al. 2015 and Shalm et al. 2015,
  *Phys. Rev. Lett.* **115**, 250401 / 250402.
-/

@[expose] public section

open MeasureTheory Real
open scoped BigOperators

namespace CSD
namespace Empirical
namespace QM
namespace E91

variable {Λ : Type*} [MeasurableSpace Λ] {SettingA SettingB : Type*}

/-! ### The factorisable LHV correlation -/

/-- The local-hidden-variable correlation `E(a,b) = ∫ A(a,λ)·B(b,λ) dμ(λ)`: the
expectation of the product of the two sides' local `±1` responses, the only
correlation a local-hidden-variable model can produce. -/
noncomputable def lhvCorrelation (μ : Measure Λ)
    (A : SettingA → Λ → ℝ) (B : SettingB → Λ → ℝ) (a : SettingA) (b : SettingB) : ℝ :=
  ∫ l, A a l * B b l ∂μ

/-- The CHSH combination of four LHV correlations,
`S = E(a,b) − E(a,b') + E(a',b) + E(a',b')`. -/
noncomputable def lhvCHSH (μ : Measure Λ)
    (A : SettingA → Λ → ℝ) (B : SettingB → Λ → ℝ)
    (a a' : SettingA) (b b' : SettingB) : ℝ :=
  lhvCorrelation μ A B a b - lhvCorrelation μ A B a b'
    + lhvCorrelation μ A B a' b + lhvCorrelation μ A B a' b'

/-! ### The Bell/CHSH inequality `|S| ≤ 2` -/

/-- **The Bell–CHSH inequality for any local-hidden-variable model.** For a
hidden-variable probability space `(Λ, μ)` and `±1`-valued, measurable local
response functions `A, B`, the CHSH combination of the factorisable correlations
satisfies `|S| ≤ 2`.

Bell 1964 (*Physics* **1**, 195) in the CHSH 1969 form. The proof is the pointwise
`±1` identity `S(λ) ∈ {−2, +2}` plus monotonicity of the Bochner integral on the
probability measure `μ`. -/
theorem lhvCHSH_abs_le_two (μ : Measure Λ) [IsProbabilityMeasure μ]
    (A : SettingA → Λ → ℝ) (B : SettingB → Λ → ℝ)
    (hA : ∀ a, Measurable (A a)) (hB : ∀ b, Measurable (B b))
    (hApm : ∀ a l, A a l = 1 ∨ A a l = -1) (hBpm : ∀ b l, B b l = 1 ∨ B b l = -1)
    (a a' : SettingA) (b b' : SettingB) :
    |lhvCHSH μ A B a a' b b'| ≤ 2 := by
  -- Each product `A x · B y` is bounded by `1`, hence integrable on `μ`.
  have hbound : ∀ (x : SettingA) (y : SettingB) (l : Λ), |A x l * B y l| ≤ 1 := by
    intro x y l
    rcases hApm x l with h | h <;> rcases hBpm y l with h' | h' <;>
      rw [h, h'] <;> norm_num
  have hint : ∀ (x : SettingA) (y : SettingB), Integrable (fun l => A x l * B y l) μ := by
    intro x y
    refine (integrable_const (1 : ℝ)).mono'
      ((hA x).mul (hB y)).aestronglyMeasurable (ae_of_all _ (fun l => ?_))
    rw [Real.norm_eq_abs]; exact hbound x y l
  -- Pointwise: the CHSH integrand is `±2`, so its absolute value is `≤ 2`.
  have hpt : ∀ l : Λ,
      |A a l * B b l - A a l * B b' l + A a' l * B b l + A a' l * B b' l| ≤ 2 := by
    intro l
    rcases hApm a l with ha | ha <;> rcases hApm a' l with ha' | ha' <;>
      rcases hBpm b l with hb | hb <;> rcases hBpm b' l with hb' | hb' <;>
      rw [ha, ha', hb, hb'] <;> norm_num
  -- Assemble the four correlation integrals into one integral of the CHSH integrand.
  -- Combined-integrability facts, stated with explicit *lambda* types so the
  -- `integral_add`/`integral_sub` rewrites match the pointwise integrand form.
  have h12 : Integrable (fun l => A a l * B b l - A a l * B b' l) μ :=
    (hint a b).sub (hint a b')
  have h123 : Integrable (fun l => A a l * B b l - A a l * B b' l + A a' l * B b l) μ :=
    h12.add (hint a' b)
  have hSint : Integrable
      (fun l => A a l * B b l - A a l * B b' l + A a' l * B b l + A a' l * B b' l) μ :=
    h123.add (hint a' b')
  have hSeq : lhvCHSH μ A B a a' b b'
      = ∫ l, (A a l * B b l - A a l * B b' l + A a' l * B b l + A a' l * B b' l) ∂μ := by
    unfold lhvCHSH lhvCorrelation
    rw [← integral_sub (hint a b) (hint a b'), ← integral_add h12 (hint a' b),
      ← integral_add h123 (hint a' b')]
  rw [hSeq]
  calc
    |∫ l, (A a l * B b l - A a l * B b' l + A a' l * B b l + A a' l * B b' l) ∂μ|
        = ‖∫ l, (A a l * B b l - A a l * B b' l + A a' l * B b l + A a' l * B b' l) ∂μ‖ :=
          (Real.norm_eq_abs _).symm
    _ ≤ ∫ l, ‖A a l * B b l - A a l * B b' l + A a' l * B b l + A a' l * B b' l‖ ∂μ :=
          norm_integral_le_integral_norm _
    _ ≤ ∫ _l : Λ, (2 : ℝ) ∂μ :=
          integral_mono hSint.norm (integrable_const 2) (fun l => by
            rw [Real.norm_eq_abs]; exact hpt l)
    _ = 2 := by simp

/-! ### Strict separation from the quantum Tsirelson value -/

/-- Every LHV CHSH value is strictly below the quantum Tsirelson bound `2√2`. -/
theorem lhvCHSH_lt_tsirelson (μ : Measure Λ) [IsProbabilityMeasure μ]
    (A : SettingA → Λ → ℝ) (B : SettingB → Λ → ℝ)
    (hA : ∀ a, Measurable (A a)) (hB : ∀ b, Measurable (B b))
    (hApm : ∀ a l, A a l = 1 ∨ A a l = -1) (hBpm : ∀ b l, B b l = 1 ∨ B b l = -1)
    (a a' : SettingA) (b b' : SettingB) :
    lhvCHSH μ A B a a' b b' < 2 * Real.sqrt 2 := by
  have hle : lhvCHSH μ A B a a' b b' ≤ 2 :=
    le_trans (le_abs_self _) (lhvCHSH_abs_le_two μ A B hA hB hApm hBpm a a' b b')
  have h2 : (2 : ℝ) < 2 * Real.sqrt 2 := by
    have h1 : (1 : ℝ) < Real.sqrt 2 := by
      have : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      rwa [Real.sqrt_one] at this
    linarith
  linarith

/-! ### E91 device-independent security witness -/

/-- **E91 device-independent security witness.** The singlet at canonical angles
realises a CHSH magnitude of `2√2` (Bell A1, `chsh_singlet_tsirelson_bound`), while
**every** local-hidden-variable model — any hidden-variable probability space with
`±1` local responses — is capped at `|S| ≤ 2`. Since `2 < 2√2`, an observed CHSH
value at the Tsirelson bound is unreproducible by any LHV model, hence certifies
the absence of any local-realistic (eavesdropper) description of the source. This
is the device-independent security guarantee underlying the Ekert 1991 protocol.

**Experimental verification:** Ekert 1991, *Phys. Rev. Lett.* **67**, 661;
loophole-free Bell tests: Hensen 2015, Giustina 2015, Shalm 2015. -/
theorem e91_no_lhv_reproduces_singlet :
    (∃ a a' b b' : CSD.LF3.DetectorSetting,
      |Bell.chshOperator a a' b b'| = 2 * Real.sqrt 2)
    ∧ (∀ {Λ : Type*} [MeasurableSpace Λ] {SettingA SettingB : Type*}
        (μ : Measure Λ) [IsProbabilityMeasure μ]
        (A : SettingA → Λ → ℝ) (B : SettingB → Λ → ℝ),
        (∀ a, Measurable (A a)) → (∀ b, Measurable (B b)) →
        (∀ a l, A a l = 1 ∨ A a l = -1) → (∀ b l, B b l = 1 ∨ B b l = -1) →
        ∀ (xa xa' : SettingA) (xb xb' : SettingB),
          |lhvCHSH μ A B xa xa' xb xb'| ≤ 2) := by
  refine ⟨Bell.chsh_singlet_tsirelson_bound, ?_⟩
  intro Λ instMS SettingA SettingB μ instPb A B hA hB hApm hBpm xa xa' xb xb'
  exact lhvCHSH_abs_le_two μ A B hA hB hApm hBpm xa xa' xb xb'

end E91
end QM
end Empirical
end CSD
