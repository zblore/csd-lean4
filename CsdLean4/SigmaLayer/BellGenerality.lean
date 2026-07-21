import CsdLean4.SigmaLayer.CompositeInterface
import CsdLean4.Empirical.QM.Bell
import CsdLean4.Empirical.QM.Crypto.E91
import CsdLean4.Empirical.QM.Contextuality.KS18
import CsdLean4.Mathlib.Probability.CGLMP

/-!
# SigmaLayer/BellGenerality: the universal Bell/contextuality bounds

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)).

Where `SigmaLayer/CompositeAdapters.lean` inhabits the T13/T14 predicates with SPECIFIC violation witnesses
(the singlet, the maximally-entangled qudit, Cabello-18, Mermin-Peres, GHZ), this module exposes the
UNIVERSAL bounds behind them — the general form of Bell's theorem and Kochen-Specker, quantified over ALL
local-hidden-variable models, ALL quantum states, and ALL parity-`(18,9)` configurations:

* **Classical CHSH bound** (`lhv_chsh_le_two`): every local-hidden-variable model has `|S| ≤ 2` (the
  Bell-CHSH inequality, for all `±1` response functions on any hidden-variable space).
* **Quantum Tsirelson bound** (`qm_chsh_le_tsirelson`): every quantum state has `|S| ≤ 2√2` (for all
  detector settings) — the universal quantum ceiling.
* **Classical CGLMP bound** (`cglmp_lhv_le_two`): every local-hidden-variable table has `cglmp ≤ 2`, for
  every dimension `d ≥ 2`.
* **General Bell separation** (`bell_general_separation`): the classical ceiling `2` is strictly below the
  quantum ceiling `2√2`, and the gap is ATTAINED (the singlet reaches `2√2`) — so quantum correlations
  universally and provably exceed every local-hidden-variable model.
* **General Kochen-Specker** (`general_ks_noNonContextualValuation`): NO `{0,1}` valuation selects exactly
  one vector per basis, for ANY `9`-basis / `18`-vector configuration in which each vector lies in exactly
  two bases (not just the Cabello-18 instance).

These are the general theorems the corpus already proves (`E91.lhvCHSH_abs_le_two`,
`Bell.chsh_qm_tsirelson_bound`, `CGLMP.cglmp_lhv_bound`, `KochenSpecker.no_value_assignment_18_9`), lifted
into the SigmaLayer ledger as universal statements rather than per-instance witnesses.
-/

open Matrix
open scoped BigOperators

namespace CSD.SigmaLayer

open CSD.LF3 CSD.Empirical.Bell CSD.Empirical.QM.E91 CSD.Empirical.KochenSpecker

/-- **Universal classical CHSH bound (T14, classical side).** Every local-hidden-variable model — any
`±1`-valued measurable response functions `A, B` on any hidden-variable probability space — satisfies the
Bell-CHSH inequality `|S| ≤ 2`. The general Bell 1964 / CHSH 1969 bound. -/
theorem lhv_chsh_le_two {Λ : Type*} [MeasurableSpace Λ] {SA SB : Type*}
    (μ : MeasureTheory.Measure Λ) [MeasureTheory.IsProbabilityMeasure μ]
    (A : SA → Λ → ℝ) (B : SB → Λ → ℝ)
    (hA : ∀ a, Measurable (A a)) (hB : ∀ b, Measurable (B b))
    (hApm : ∀ a l, A a l = 1 ∨ A a l = -1) (hBpm : ∀ b l, B b l = 1 ∨ B b l = -1)
    (a a' : SA) (b b' : SB) :
    |lhvCHSH μ A B a a' b b'| ≤ 2 :=
  lhvCHSH_abs_le_two μ A B hA hB hApm hBpm a a' b b'

/-- **Universal classical CGLMP bound (T14, qudit classical side).** Every local-hidden-variable table
(two `Bool` settings per party, `ZMod d` outcomes) has CGLMP value `≤ 2`, for every dimension `d ≥ 2`. -/
theorem cglmp_lhv_le_two {d : ℕ} {Λ : Type*} [MeasurableSpace Λ]
    (μ : MeasureTheory.Measure Λ) [MeasureTheory.IsProbabilityMeasure μ] (hd : 2 ≤ d)
    (A B : Bool → Λ → ZMod d) (hA : ∀ x, Measurable (A x)) (hB : ∀ y, Measurable (B y)) :
    ProbabilityTheory.CGLMP.cglmpLHV μ A B ≤ 2 :=
  ProbabilityTheory.CGLMP.cglmp_lhv_bound μ hd A B hA hB

/-- The quantum CHSH value of a bipartite state for four detector settings (the `σ·a ⊗ σ·b`
correlation combination). -/
noncomputable def qmChsh (a a' b b' : DetectorSetting) (ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)) : ℝ :=
  Complex.re (inner ℂ ψ (toEuclideanLin (sigmaDotJoint a b) ψ))
    - Complex.re (inner ℂ ψ (toEuclideanLin (sigmaDotJoint a b') ψ))
    + Complex.re (inner ℂ ψ (toEuclideanLin (sigmaDotJoint a' b) ψ))
    + Complex.re (inner ℂ ψ (toEuclideanLin (sigmaDotJoint a' b') ψ))

/-- **Universal quantum Tsirelson bound (T14, quantum side).** Every unit bipartite quantum state, for
all detector settings, has `|S| ≤ 2√2` — the general Tsirelson ceiling (Khalfin-Tsirelson). -/
theorem qm_chsh_le_tsirelson (a a' b b' : DetectorSetting)
    (ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)) (hψ : ‖ψ‖ = 1) :
    |qmChsh a a' b b' ψ| ≤ 2 * Real.sqrt 2 :=
  chsh_qm_tsirelson_bound a a' b b' ψ hψ

/-- **General Bell separation (T14).** The universal quantum-classical gap: every quantum state obeys the
Tsirelson bound `2√2`, the classical local bound is `2 < 2√2`, and the gap is ATTAINED (the singlet
reaches `2√2`). Together with `lhv_chsh_le_two` (classical `≤ 2` for every hidden-variable model), this is
the general statement that quantum correlations provably and universally exceed every local model. -/
theorem bell_general_separation :
    (∀ (a a' b b' : DetectorSetting) (ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)), ‖ψ‖ = 1 →
        |qmChsh a a' b b' ψ| ≤ 2 * Real.sqrt 2)
    ∧ bellClassicalBoundValue < 2 * Real.sqrt 2
    ∧ (∃ a a' b b' : DetectorSetting, |chshOperator a a' b b'| = 2 * Real.sqrt 2) :=
  ⟨fun a a' b b' ψ hψ => qm_chsh_le_tsirelson a a' b b' ψ hψ,
    chsh_classical_bound_violated,
    chsh_singlet_tsirelson_bound⟩

/-- **General Kochen-Specker (T13).** For ANY assignment of `9` bases among `18` vectors in which every
vector lies in exactly two bases, no `{0,1}` valuation selects exactly one vector per basis: a parity
obstruction to non-contextual value assignments, general over the configuration (the Cabello-18 instance
`cabello18_noNonContextualValuation` is one such). -/
theorem general_ks_noNonContextualValuation (bases : Fin 9 → Finset (Fin 18))
    (h_appears : ∀ v : Fin 18,
      ((Finset.univ : Finset (Fin 9)).filter (fun B => v ∈ bases B)).card = 2) :
    NoNonContextualValuation
      (fun lambda : Fin 18 → Bool =>
        ∀ B : Fin 9, ((bases B).filter (fun v => lambda v = true)).card = 1) :=
  no_value_assignment_18_9 bases h_appears

end CSD.SigmaLayer
