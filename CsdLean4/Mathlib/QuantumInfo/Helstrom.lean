/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.QuantumInfo.TraceDistance

/-!
# The Helstrom bound — minimum-error state discrimination (K3)

**Category:** 1-Mathlib (CSD-free; staged as a Mathlib-upstream candidate).

The **operational meaning of the trace distance**: it is exactly the advantage, over blind
guessing, of the best possible measurement at telling two states apart.

One of two states is prepared, `ρ₀` with prior `p₀` and `ρ₁` with prior `p₁`, and we must
guess which. The most general strategy is a **two-outcome test** — an effect `E` with
`0 ≤ E ≤ 1` (`IsTest`) — where outcome `E` means "guess `ρ₀`" and outcome `1 − E` means
"guess `ρ₁`". Helstrom's theorem says the optimal success probability is

  `P_success = ½ (1 + ‖p₀ρ₀ − p₁ρ₁‖₁)`,   equivalently   `P_error = ½ (1 − ‖p₀ρ₀ − p₁ρ₁‖₁)`,

and — the sharper half — that the optimum is **attained**, by the projector onto the positive
eigenspace of the *Helstrom operator* `A = p₀ρ₀ − p₁ρ₁` (`helstromTest`).

At **equal priors** this reads `P_error = ½ (1 − D(ρ₀, ρ₁))` with `D` the trace distance of
[`TraceDistance.lean`](TraceDistance.lean): indistinguishable states (`D = 0`) force a coin
flip, perfectly distinguishable ones (`D = 1`) allow an error-free test. This is the operational
content that makes `traceDist` *the* metric of statistical distinguishability, and it is the
converse companion to the data-processing inequality `channel_traceDist_le`
([`DataProcessing.lean`](DataProcessing.lean)): channels cannot increase distinguishability,
and distinguishability is exactly what a measurement can extract.

## What this file proves

* `re_trace_posPart_eq` — `Re Tr(A₊) = ½(‖A‖₁ + Re Tr A)`, the Jordan-decomposition identity
  that converts the variational optimum into a trace norm.
* `re_trace_mul_le_helstrom` — **optimality**: no test beats `helstromTest`,
  `Re Tr(A·E) ≤ Re Tr(A·helstromTest)` for every `E` with `0 ≤ E ≤ 1`.
* `re_trace_mul_helstrom` — **attainment**: `Re Tr(A·helstromTest) = ½(‖A‖₁ + Re Tr A)`.
* `successProb_le` / `successProb_helstromTest` — the equal-prior Helstrom bound
  `P_success ≤ ½(1 + D(ρ₀,ρ₁))`, **with equality** at `helstromTest`.
* `errorProb_ge` / `errorProb_helstromTest` — the same in error form,
  `P_error ≥ ½(1 − D(ρ₀,ρ₁))`, attained.
* `helstrom_indistinguishable` / `helstrom_perfect` — the two extremes: `D = 0` forces
  `P_error = ½` (a coin flip), `D = 1` permits `P_error = 0`.
* `successProbPrior_le` / `successProbPrior_helstromTest` — the general-prior statement
  `P_success ≤ ½(1 + ‖p₀ρ₀ − p₁ρ₁‖₁)`, attained.

Both halves rest on the Jordan-decomposition machinery already in `TraceDistance.lean`:
the upper bound is `re_trace_mul_le_re_trace_posPart` (the variational half `Re Tr(A·P) ≤
Re Tr(A₊)` for `0 ≤ P ≤ 1`) and the attainment is `mul_posProj_eq_posPart`
(`A · P₊ = A₊`) — the positive-eigenspace projector is exactly where that bound is tight.

## Relation to unambiguous discrimination

`Empirical/QM/USD.lean` solves the *complementary* problem: zero error at the cost of a third,
inconclusive outcome. Helstrom is the two-outcome optimum — always conclusive, minimum error.
The two are the endpoints of the discrimination trade-off, and both are POVM statements.

## References

`specs/qi-qec-roadmap.md` (K3, the trace-distance metric core); `specs/future-work.md`;
`specs/BACKLOG.md`. Helstrom, *Quantum Detection and Estimation Theory* (1976);
Holevo (1973); Nielsen & Chuang §9.2.1. Companion results: `QuantumInfo.traceDist`
(`TraceDistance.lean`), `QuantumInfo.channel_traceDist_le` (`DataProcessing.lean`),
`CSD.Empirical.QM.USD.usd_success` (`Empirical/QM/USD.lean`).
-/

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace QuantumInfo

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Two-outcome tests -/

/-- A **two-outcome test** (binary POVM): an effect `E` with `0 ≤ E ≤ 1`. Outcome `E` is read
as "guess the first state", outcome `1 − E` as "guess the second". -/
structure IsTest (E : Matrix n n ℂ) : Prop where
  /-- `0 ≤ E`. -/
  nonneg : E.PosSemidef
  /-- `E ≤ 1`. -/
  le_one : ((1 : Matrix n n ℂ) - E).PosSemidef

/-- The **Helstrom test** for a Hermitian operator `A`: the projector onto the positive
eigenspace of `A`. This is the optimal discriminator for the Helstrom operator
`A = p₀ρ₀ − p₁ρ₁` (`re_trace_mul_le_helstrom`, `re_trace_mul_helstrom`). -/
noncomputable def helstromTest {A : Matrix n n ℂ} (hA : A.IsHermitian) : Matrix n n ℂ :=
  posProj hA

/-- The Helstrom test is a genuine two-outcome test. -/
lemma helstromTest_isTest {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    IsTest (helstromTest hA) :=
  ⟨posProj_posSemidef hA, one_sub_posProj_posSemidef hA⟩

/-! ### The variational optimum -/

/-- **`Re Tr(A₊) = ½(‖A‖₁ + Re Tr A)`.** Adding the Jordan decomposition
`Tr A = Tr A₊ − Tr A₋` to the trace-norm identity `‖A‖₁ = Tr A₊ + Tr A₋` eliminates `A₋`.
This is what turns the variational optimum below into a trace norm. -/
lemma re_trace_posPart_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    RCLike.re (posPart hA).trace = (traceNorm hA + RCLike.re A.trace) / 2 := by
  have hjordan : A.trace = (posPart hA).trace - (negPart hA).trace := by
    rw [← Matrix.trace_sub, posPart_sub_negPart]
  have hre : RCLike.re A.trace
      = RCLike.re (posPart hA).trace - RCLike.re (negPart hA).trace := by
    rw [hjordan, map_sub]
  have hnorm := traceNorm_eq_re_trace_posPart_add_negPart hA
  linarith

/-- **Optimality of the Helstrom test.** For every two-outcome test `E`,
`Re Tr(A·E) ≤ Re Tr(A·helstromTest)` — no measurement extracts more of `A` than the
projector onto its positive eigenspace. -/
theorem re_trace_mul_le_helstrom {A E : Matrix n n ℂ} (hA : A.IsHermitian) (hE : IsTest E) :
    RCLike.re (A * E).trace ≤ RCLike.re (A * helstromTest hA).trace := by
  rw [helstromTest, mul_posProj_eq_posPart]
  exact re_trace_mul_le_re_trace_posPart hA hE.nonneg hE.le_one

/-- **Attainment.** The Helstrom test achieves the bound in closed form:
`Re Tr(A·helstromTest) = ½(‖A‖₁ + Re Tr A)`. -/
theorem re_trace_mul_helstrom {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    RCLike.re (A * helstromTest hA).trace = (traceNorm hA + RCLike.re A.trace) / 2 := by
  rw [helstromTest, mul_posProj_eq_posPart, re_trace_posPart_eq]

/-! ### Equal priors: the operational meaning of the trace distance -/

/-- The **success probability** of the test `E` at discriminating `ρ₀` from `ρ₁`, each
prepared with prior `½`: guess "0" on outcome `E`, "1" on outcome `1 − E`. -/
noncomputable def successProb (ρ₀ ρ₁ E : Matrix n n ℂ) : ℝ :=
  (RCLike.re (ρ₀ * E).trace + RCLike.re (ρ₁ * ((1 : Matrix n n ℂ) - E)).trace) / 2

/-- The **error probability** of the test `E`. -/
noncomputable def errorProb (ρ₀ ρ₁ E : Matrix n n ℂ) : ℝ :=
  1 - successProb ρ₀ ρ₁ E

/-- Success rewritten around the **Helstrom operator** `ρ₀ − ρ₁`: blind guessing (`½`) plus
half of what the test extracts from the difference. -/
lemma successProb_eq {ρ₀ ρ₁ E : Matrix n n ℂ} (hρ₁ : ρ₁.trace = 1) :
    successProb ρ₀ ρ₁ E = (1 + RCLike.re ((ρ₀ - ρ₁) * E).trace) / 2 := by
  have hmul : ρ₁ * ((1 : Matrix n n ℂ) - E) = ρ₁ - ρ₁ * E := by
    rw [Matrix.mul_sub, Matrix.mul_one]
  have hsub : (ρ₀ - ρ₁) * E = ρ₀ * E - ρ₁ * E := Matrix.sub_mul ρ₀ ρ₁ E
  rw [successProb, hmul, hsub, Matrix.trace_sub, Matrix.trace_sub, map_sub, map_sub, hρ₁]
  simp only [RCLike.one_re]
  ring

omit [DecidableEq n] in
/-- The Helstrom operator of two states is traceless. -/
lemma re_trace_sub_eq_zero {ρ₀ ρ₁ : Matrix n n ℂ} (h₀ : ρ₀.trace = 1) (h₁ : ρ₁.trace = 1) :
    RCLike.re (ρ₀ - ρ₁).trace = 0 := by
  rw [Matrix.trace_sub, h₀, h₁, sub_self, map_zero]

/-- **The Helstrom bound (equal priors).** No two-outcome test discriminates `ρ₀` from `ρ₁`
better than `½(1 + D(ρ₀,ρ₁))`, where `D` is the trace distance. -/
theorem successProb_le {ρ₀ ρ₁ E : Matrix n n ℂ} (h : (ρ₀ - ρ₁).IsHermitian)
    (h₀ : ρ₀.trace = 1) (h₁ : ρ₁.trace = 1) (hE : IsTest E) :
    successProb ρ₀ ρ₁ E ≤ (1 + traceDist h) / 2 := by
  have hopt := re_trace_mul_le_helstrom h hE
  have hval := re_trace_mul_helstrom h
  rw [re_trace_sub_eq_zero h₀ h₁] at hval
  rw [successProb_eq h₁, traceDist]
  linarith

/-- **Attainment (equal priors).** The Helstrom test meets the bound exactly, so
`½(1 + D(ρ₀,ρ₁))` is the optimal success probability, not merely an upper bound. -/
theorem successProb_helstromTest {ρ₀ ρ₁ : Matrix n n ℂ} (h : (ρ₀ - ρ₁).IsHermitian)
    (h₀ : ρ₀.trace = 1) (h₁ : ρ₁.trace = 1) :
    successProb ρ₀ ρ₁ (helstromTest h) = (1 + traceDist h) / 2 := by
  have hval := re_trace_mul_helstrom h
  rw [re_trace_sub_eq_zero h₀ h₁] at hval
  rw [successProb_eq h₁, hval, traceDist]
  ring

/-- **The Helstrom bound in error form:** `P_error ≥ ½(1 − D(ρ₀,ρ₁))`. -/
theorem errorProb_ge {ρ₀ ρ₁ E : Matrix n n ℂ} (h : (ρ₀ - ρ₁).IsHermitian)
    (h₀ : ρ₀.trace = 1) (h₁ : ρ₁.trace = 1) (hE : IsTest E) :
    (1 - traceDist h) / 2 ≤ errorProb ρ₀ ρ₁ E := by
  have := successProb_le h h₀ h₁ hE
  rw [errorProb]
  linarith

/-- **The minimum error probability is `½(1 − D(ρ₀,ρ₁))`** — attained by the Helstrom test.
This is the operational meaning of the trace distance. -/
theorem errorProb_helstromTest {ρ₀ ρ₁ : Matrix n n ℂ} (h : (ρ₀ - ρ₁).IsHermitian)
    (h₀ : ρ₀.trace = 1) (h₁ : ρ₁.trace = 1) :
    errorProb ρ₀ ρ₁ (helstromTest h) = (1 - traceDist h) / 2 := by
  rw [errorProb, successProb_helstromTest h h₀ h₁]
  ring

/-! ### The two extremes -/

/-- **Indistinguishable states force a coin flip.** If `D(ρ₀,ρ₁) = 0` — equivalently
`ρ₀ = ρ₁`, by `traceDist_eq_zero_iff` — then the error probability is exactly `½` for
*every* `E` whatsoever (not merely every test): no measurement does better than guessing. -/
theorem helstrom_indistinguishable {ρ₀ ρ₁ E : Matrix n n ℂ} (h : (ρ₀ - ρ₁).IsHermitian)
    (h₁ : ρ₁.trace = 1) (hD : traceDist h = 0) :
    errorProb ρ₀ ρ₁ E = 1 / 2 := by
  have heq : ρ₀ = ρ₁ := (traceDist_eq_zero_iff h).mp hD
  have hmul : ρ₁ * ((1 : Matrix n n ℂ) - E) = ρ₁ - ρ₁ * E := by
    rw [Matrix.mul_sub, Matrix.mul_one]
  rw [errorProb, heq, successProb, hmul, Matrix.trace_sub, map_sub, h₁]
  simp only [RCLike.one_re]
  ring

/-- **Perfectly distinguishable states admit an error-free test.** If `D(ρ₀,ρ₁) = 1` then the
Helstrom test has error probability `0`. -/
theorem helstrom_perfect {ρ₀ ρ₁ : Matrix n n ℂ} (h : (ρ₀ - ρ₁).IsHermitian)
    (h₀ : ρ₀.trace = 1) (h₁ : ρ₁.trace = 1) (hD : traceDist h = 1) :
    errorProb ρ₀ ρ₁ (helstromTest h) = 0 := by
  rw [errorProb_helstromTest h h₀ h₁, hD]
  norm_num

/-! ### General priors -/

/-- The **success probability at general priors** `p₀, p₁`: guess "0" on `E`, "1" on `1 − E`. -/
noncomputable def successProbPrior (p₀ p₁ : ℝ) (ρ₀ ρ₁ E : Matrix n n ℂ) : ℝ :=
  p₀ * RCLike.re (ρ₀ * E).trace + p₁ * RCLike.re (ρ₁ * ((1 : Matrix n n ℂ) - E)).trace

/-- Success at general priors, rewritten around the **Helstrom operator**
`A = p₀ρ₀ − p₁ρ₁`: the blind-guess baseline `p₁` plus what the test extracts from `A`. -/
lemma successProbPrior_eq {p₀ p₁ : ℝ} {ρ₀ ρ₁ E : Matrix n n ℂ} (h₁ : ρ₁.trace = 1) :
    successProbPrior p₀ p₁ ρ₀ ρ₁ E
      = p₁ + RCLike.re (((p₀ : ℂ) • ρ₀ - (p₁ : ℂ) • ρ₁) * E).trace := by
  have hA : RCLike.re (((p₀ : ℂ) • ρ₀ - (p₁ : ℂ) • ρ₁) * E).trace
      = p₀ * RCLike.re (ρ₀ * E).trace - p₁ * RCLike.re (ρ₁ * E).trace := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_sub, map_sub,
      Matrix.trace_smul, Matrix.trace_smul]
    simp
  have hB : RCLike.re (ρ₁ * ((1 : Matrix n n ℂ) - E)).trace
      = 1 - RCLike.re (ρ₁ * E).trace := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, map_sub, h₁]
    simp only [RCLike.one_re]
  rw [successProbPrior, hA, hB]
  ring

omit [DecidableEq n] in
/-- The Helstrom operator at general priors has trace `p₀ − p₁`. -/
lemma re_trace_helstromOp {p₀ p₁ : ℝ} {ρ₀ ρ₁ : Matrix n n ℂ}
    (h₀ : ρ₀.trace = 1) (h₁ : ρ₁.trace = 1) :
    RCLike.re ((p₀ : ℂ) • ρ₀ - (p₁ : ℂ) • ρ₁).trace = p₀ - p₁ := by
  rw [Matrix.trace_sub, map_sub, Matrix.trace_smul, Matrix.trace_smul, h₀, h₁]
  simp

/-- **The Helstrom bound (general priors).** With priors summing to `1`, no two-outcome test
succeeds with probability better than `½(1 + ‖p₀ρ₀ − p₁ρ₁‖₁)`. -/
theorem successProbPrior_le {p₀ p₁ : ℝ} {ρ₀ ρ₁ E : Matrix n n ℂ}
    (hA : ((p₀ : ℂ) • ρ₀ - (p₁ : ℂ) • ρ₁).IsHermitian)
    (hp : p₀ + p₁ = 1) (h₀ : ρ₀.trace = 1) (h₁ : ρ₁.trace = 1) (hE : IsTest E) :
    successProbPrior p₀ p₁ ρ₀ ρ₁ E ≤ (1 + traceNorm hA) / 2 := by
  have hopt := re_trace_mul_le_helstrom hA hE
  have hval := re_trace_mul_helstrom hA
  rw [re_trace_helstromOp h₀ h₁] at hval
  rw [successProbPrior_eq h₁]
  linarith

/-- **Attainment (general priors).** The Helstrom test meets the general-prior bound. -/
theorem successProbPrior_helstromTest {p₀ p₁ : ℝ} {ρ₀ ρ₁ : Matrix n n ℂ}
    (hA : ((p₀ : ℂ) • ρ₀ - (p₁ : ℂ) • ρ₁).IsHermitian)
    (hp : p₀ + p₁ = 1) (h₀ : ρ₀.trace = 1) (h₁ : ρ₁.trace = 1) :
    successProbPrior p₀ p₁ ρ₀ ρ₁ (helstromTest hA) = (1 + traceNorm hA) / 2 := by
  have hval := re_trace_mul_helstrom hA
  rw [re_trace_helstromOp h₀ h₁] at hval
  rw [successProbPrior_eq h₁, hval]
  linarith

end QuantumInfo
