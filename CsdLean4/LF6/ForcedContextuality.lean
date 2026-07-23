/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.QM.Crypto.E91

/-!
# LF6-A.1: Forced contextuality of the entangled de-isolation tier

**Category:** 6-Local (first concrete attack on CSD's D1 entangled frontier; the
conceptual crux of the entangled-singlet de-isolation tier).

## The idea

In CSD a measurement is **de-isolation** (LF5): the deterministic
FS-measure-preserving flow carves the ontic space `Σ` into pointer-outcome
volumes. A *product* (factorising, non-contextual) outcome-partition of `Σ` —
one where Alice's outcome is a function of her setting and the shared microstate
alone, `RA : SettingA → Λ → Sign`, and Bob's of his setting alone,
`RB : SettingB → Λ → Sign`, on **one shared probability space** `(Λ, μ)` — is
*precisely* a deterministic local-hidden-variable model. The setting-locality on
a shared `Λ` (`RA a` depends on `a` only, `RB b` on `b` only) **is** the
factorisation / non-contextuality being ruled out.

By Bell/CHSH (already in the corpus, `E91.lhvCHSH_abs_le_two`) no such product
partition reproduces the singlet correlations: any product partition obeys
`|CHSH| ≤ 2`, while the singlet at canonical settings reaches `2√2`
(`Bell.chsh_singlet_at_optimal_angles`). So any partition that DOES realise the
singlet must be **jointly contextual**. The non-factorisation is *forced*, not
posited; it lives in the `Σ`-volume engine's reading of the entangled state.

## Conceptual ledger (honest)

- **(a) Derived, not posited.** The non-factorisation is a property of the
  `Σ`-volume engine's reading of the entangled state (the singlet kernel
  `P_st`), not a partition put in by hand. `engine_joint_nonfactorises` is a
  `P_st`-arithmetic fact; the correlations are the *derived* source.
- **(b) Contextuality is FORCED (Bell).** By
  `no_product_partition_realises_singlet`, no setting-local `Σ`-partition on a
  shared `(Λ, μ)` reproduces the singlet correlations. Hence any de-isolation
  carve realising the singlet is contextual. This is `e91_no_lhv_reproduces_singlet`'s
  content re-expressed for setting-local `Σ`-partitions; it REUSES
  `lhvCHSH_abs_le_two` and the singlet `2√2`, it does not re-prove Bell.
- **(c) Factorisation = measurement.** A product outcome-partition would be a
  setting-local assignment of definite values, i.e. a *completed* measurement.
  So factorisation IS the measurement and cannot pre-exist de-isolation. The
  outcomes are not setting-local definite values waiting to be read; they are
  produced by the carve.
- **(d) Nudge ≠ carve.** Pre-measurement *nudging* (a unitary `Φ_U` reshaping of
  the `Σ`-volumes, e.g. an axis rotation) IS available and is distinct from the
  *carve* (the de-isolation flow that fixes the pointer blocks). Nudging is a
  symmetry of the engine; carving is the irreversible context selection.
- **(e) One engine, two outputs.** Born weights (LF4/LF5 moment-map /
  Duistermaat-Heckman volume) and non-locality (this file) are two outputs of
  the SAME `Σ`-volume engine. The marginals factorise (no-signalling,
  `engine_marginal_factorises`) even though the joint does not.
- **(f) Residue: A5.** This realises the singlet correlations MODULO **A5** — the
  entangled sector / the singlet's preparation region `Ω₀` is *posited*, not
  derived from deterministic dynamics (SO-1: the sector origin, distinct from Paper C Axiom A5). The forced-contextuality
  no-go is unconditional Bell content; the *engine reading* of the singlet rests
  on the posited entangled sector.
- **(g) Scope: LF6-A.1 only.** THIS file is the conceptual crux (LF6-A.1). The
  full de-isolation flow on `ℂℙ¹⁵` (pointer-block volumes `= P_st`, local flow
  factorisation `Φ = Φ_A ⊗ Φ_B`, a.s. frequencies → `P_st`, composing LF5
  `vnDilation_pointer_volume` + LF3 `born_eq_P_st`) is **LF6-A.2, deferred**.

## What is reused (no Bell re-proof)

- `CSD.Empirical.QM.E91.lhvCorrelation` / `lhvCHSH` / `lhvCHSH_abs_le_two`
  (the LHV CHSH `≤ 2` bound on any shared probability space with `±1` local
  responses).
- `CSD.Empirical.Bell.correlation` / `chshOperator` /
  `chsh_singlet_at_optimal_angles` (the singlet's `−a·b` correlation and the
  canonical `−2√2` CHSH value).
- `CSD.LF3.P_st` / `marginal_a_eq_half` / `marginal_b_eq_half` /
  `no_signalling_strong_readout_a` / `no_signalling_strong_readout_b`.

All exports are foundational-triple-only (the machinery is measure-theoretic, no
Busch).
-/

@[expose] public section

open MeasureTheory Real
open scoped BigOperators

namespace CSD
namespace LF6

open CSD.LF3 CSD.Empirical CSD.Empirical.QM.E91

/-! ### The singlet correlation target -/

/-- The singlet correlation function, taken verbatim from the corpus
(`Bell.correlation a b = −(a·b)`, `Bell.correlation_eq_neg_dot`). This is the
target a `Σ`-partition must reproduce; it is the singlet's `−a·b`, not a
reinvention. -/
noncomputable def singletCorrelation (a b : DetectorSetting) : ℝ :=
  Empirical.Bell.correlation a b

/-- `singletCorrelation a b = −(a·b)`, re-stating `LF3.correlation_eq_neg_dot`. -/
theorem singletCorrelation_eq_neg_dot (a b : DetectorSetting) :
    singletCorrelation a b = -(dotR a b) :=
  Empirical.Bell.correlation_eq_neg_dot a b

/-! ### The product-partition predicate

A **product partition** of the shared ontic space `(Λ, μ)` is a pair of
setting-local `±1` measurable response functions. `RA a` depends only on
Alice's setting `a`, `RB b` only on Bob's setting `b`: that setting-locality on
a *shared* `Λ` is exactly the factorisation / non-contextuality assumption — it
is a deterministic local-hidden-variable model. -/

/-- `RA, RB` form a **product (non-contextual) partition** of the shared ontic
space `(Λ, μ)`: setting-local, measurable, `±1`-valued responses. The
load-bearing structural point is the *setting-locality* — `RA a` is a function of
Alice's setting `a` and the shared microstate alone, `RB b` of Bob's setting `b`
alone. -/
def IsProductPartition {Λ : Type*} [MeasurableSpace Λ]
    (RA RB : DetectorSetting → Λ → ℝ) : Prop :=
  (∀ a, Measurable (RA a)) ∧ (∀ b, Measurable (RB b)) ∧
    (∀ a l, RA a l = 1 ∨ RA a l = -1) ∧ (∀ b l, RB b l = 1 ∨ RB b l = -1)

/-- A product partition **reproduces the singlet correlations** if its
factorisable LHV correlation `∫ RA(a,·)·RB(b,·) dμ` matches the singlet's
`−a·b` at every pair of settings. -/
def ReproducesSinglet {Λ : Type*} [MeasurableSpace Λ] (μ : Measure Λ)
    (RA RB : DetectorSetting → Λ → ℝ) : Prop :=
  ∀ a b, lhvCorrelation μ RA RB a b = singletCorrelation a b

/-- A reproducing product partition's CHSH combination is *literally* the singlet
CHSH operator: rewrite each LHV correlation by the reproduction hypothesis. -/
theorem lhvCHSH_eq_chshOperator {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure Λ) (RA RB : DetectorSetting → Λ → ℝ)
    (hRep : ReproducesSinglet μ RA RB) (a a' b b' : DetectorSetting) :
    lhvCHSH μ RA RB a a' b b' = Empirical.Bell.chshOperator a a' b b' := by
  -- `singletCorrelation = Bell.correlation` definitionally, so `hRep` rewrites
  -- each LHV correlation straight to `Bell.correlation`.
  have e : ∀ x y, lhvCorrelation μ RA RB x y = Empirical.Bell.correlation x y :=
    fun x y => hRep x y
  unfold lhvCHSH Empirical.Bell.chshOperator
  rw [e a b, e a b', e a' b, e a' b']

/-! ### The forced-contextuality no-go -/

/-- **`no_product_partition_realises_singlet` (LF6-A.1, load-bearing).** There is
NO product (setting-local, non-contextual) partition of any shared probability
space `(Λ, μ)` whose factorisable correlations reproduce the singlet
correlations.

Proof: such a partition gives `lhvCHSH = chshOperator = −2√2` at the canonical
settings (`lhvCHSH_eq_chshOperator` + `Bell.chsh_singlet_at_optimal_angles`),
hence `|lhvCHSH| = 2√2`; but `lhvCHSH_abs_le_two` caps it at `2`, and `2 < 2√2`.

This is `e91_no_lhv_reproduces_singlet`'s content re-expressed for setting-local
`Σ`-partitions: it reuses `lhvCHSH_abs_le_two` and the singlet `2√2` directly and
does NOT re-prove Bell. The forced contextuality: any `Σ`-partition realising the
singlet must be jointly contextual. -/
theorem no_product_partition_realises_singlet {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure Λ) [IsProbabilityMeasure μ] (RA RB : DetectorSetting → Λ → ℝ)
    (hPP : IsProductPartition RA RB) (hRep : ReproducesSinglet μ RA RB) :
    False := by
  obtain ⟨hA, hB, hApm, hBpm⟩ := hPP
  -- The LHV cap: |lhvCHSH| ≤ 2 at the canonical settings.
  have hbound :=
    lhvCHSH_abs_le_two μ RA RB hA hB hApm hBpm
      Empirical.Bell.chshA Empirical.Bell.chshA'
      Empirical.Bell.chshB Empirical.Bell.chshB'
  -- The singlet value: lhvCHSH = chshOperator = −2√2.
  rw [lhvCHSH_eq_chshOperator μ RA RB hRep,
      Empirical.Bell.chsh_singlet_at_optimal_angles] at hbound
  -- So 2√2 ≤ 2, contradicting 2 < 2√2.
  have hpos : (0 : ℝ) < 2 * Real.sqrt 2 := by positivity
  rw [abs_neg, abs_of_pos hpos] at hbound
  have hgt : (2 : ℝ) < 2 * Real.sqrt 2 := by
    have h1 : (1 : ℝ) < Real.sqrt 2 := by
      have h := Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (1 : ℝ) < 2)
      rwa [Real.sqrt_one] at h
    linarith
  linarith

/-- **Non-vacuity of the no-go.** Product partitions exist (the predicate is
inhabitable) and reproduce *some* correlation — just not the singlet's. The
all-`+1` responses form a product partition whose correlation is the constant
`1`; since the singlet correlation is non-constant (`−a·b`), this partition does
not reproduce the singlet, so `no_product_partition_realises_singlet` is a
genuine separation, not a vacuous predicate. -/
theorem productPartition_nonvacuous {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure Λ) [IsProbabilityMeasure μ] :
    IsProductPartition (Λ := Λ) (fun (_ : DetectorSetting) (_ : Λ) => (1 : ℝ))
        (fun (_ : DetectorSetting) (_ : Λ) => (1 : ℝ)) ∧
      (∀ a b : DetectorSetting,
        lhvCorrelation μ (fun (_ : DetectorSetting) (_ : Λ) => (1 : ℝ))
          (fun (_ : DetectorSetting) (_ : Λ) => (1 : ℝ)) a b = 1) := by
  refine ⟨⟨fun _ => measurable_const, fun _ => measurable_const,
      fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl⟩, ?_⟩
  intro a b
  unfold lhvCorrelation
  rw [show (fun l : Λ => (1 : ℝ) * 1) = fun _ : Λ => (1 : ℝ) from by funext l; ring,
      integral_const]
  simp

/-! ### The engine's non-factorising joint / factorising marginal pair -/

/-- **`engine_joint_nonfactorises`.** The singlet kernel does NOT factor: there
is a concrete setting and sign pair where the joint `P_st(s,t)` differs from the
product of marginals `P_A(s)·P_B(t) = (1/2)·(1/2) = 1/4`.

Witness: aligned axes `a = b = ẑ̂_x` (so `a·b = 1`) with `s = t = +`, where
`P_st = (1 − 1)/4 = 0 ≠ 1/4`. A `P_st`-arithmetic fact; the *derived* source of
the singlet correlations. -/
theorem engine_joint_nonfactorises :
    ∃ (a b : DetectorSetting) (s t : Sign),
      P_st a b s t ≠ (∑ t' : Sign, P_st a b s t') * (∑ s' : Sign, P_st a b s' t) := by
  refine ⟨Empirical.Bell.chshA, Empirical.Bell.chshA, Sign.plus, Sign.plus, ?_⟩
  have hdot : dotR Empirical.Bell.chshA Empirical.Bell.chshA = 1 := by
    unfold dotR
    simp only [Empirical.Bell.chshA_vec_ofLp_0, Empirical.Bell.chshA_vec_ofLp_1,
      Empirical.Bell.chshA_vec_ofLp_2]
    norm_num
  have hP : P_st Empirical.Bell.chshA Empirical.Bell.chshA Sign.plus Sign.plus = 0 := by
    unfold P_st; rw [hdot]; simp only [Sign.val_plus]; norm_num
  rw [hP, marginal_a_eq_half, marginal_b_eq_half]
  norm_num

/-- **`engine_marginal_factorises` (no-signalling).** Each marginal of the
singlet kernel is `1/2`, independent of the other side's setting. The marginal
factorises even though the joint does not — the operational signature of
no-signalling. Reuses `LF3.marginal_a_eq_half` / `marginal_b_eq_half` /
`no_signalling_strong_readout_a` / `_b`. -/
theorem engine_marginal_factorises :
    (∀ (a b : DetectorSetting) (s : Sign), ∑ t : Sign, P_st a b s t = 1 / 2) ∧
      (∀ (a b : DetectorSetting) (t : Sign), ∑ s : Sign, P_st a b s t = 1 / 2) ∧
      (∀ (a b b' : DetectorSetting) (s : Sign),
        (∑ t : Sign, P_st a b s t) = ∑ t : Sign, P_st a b' s t) ∧
      (∀ (a a' b : DetectorSetting) (t : Sign),
        (∑ s : Sign, P_st a b s t) = ∑ s : Sign, P_st a' b s t) :=
  ⟨marginal_a_eq_half, marginal_b_eq_half,
    no_signalling_strong_readout_a, no_signalling_strong_readout_b⟩

end LF6
end CSD
