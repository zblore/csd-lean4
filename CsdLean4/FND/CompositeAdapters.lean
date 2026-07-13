import CsdLean4.FND.CompositeInterface
import CsdLean4.Empirical.QM.Bell
import CsdLean4.Empirical.QM.Multipartite.GHZ
import CsdLean4.Empirical.QM.Contextuality.KS18
import CsdLean4.Empirical.QM.Contextuality.MerminPeres
import CsdLean4.LF6.CGLMPQudit

/-!
# FND/CompositeAdapters: inhabiting the composition targets from the existing capstones

**Category:** 7-FND (the Choice A ontological layer).

Tranche 3 adapters. Each theorem here inhabits one of the `FND/CompositeInterface.lean` target predicates
by wiring an existing LF6/Empirical capstone through the interface. No new mathematics is proved: the
content is the demonstration that the FND-layer targets are exactly the reconstruction results already in
the corpus.

* **T15 no-signalling:** `singlet_hasNoSignalling` (from `Bell.no_signalling_alice/bob`).
* **T14 Bell (CGLMP):** `maxEntangled_noLocalHiddenVariable` (from `no_lhv_realises_maxEntangled_cglmp_d`).
* **T14 Bell (CHSH/Tsirelson):** `singlet_hasTsirelsonSeparation` (from `chsh_classical_bound_violated`
  and `chsh_singlet_tsirelson_bound`).
* **T13 contextuality:** `cabello18_noNonContextualValuation` (Kochen-Specker),
  `merminPeres_noNonContextualValuation`, `ghz_noNonContextualValuation`.
* **T10 POVM:** `povm_weightsProbability` (from `POVM.weights_sum_eq_one`). The full T10 content, the POVM
  Born weights realised as Fubini-Study pointer-block frequencies through a Naimark dilation, IS the
  existing `CSD.LF4.povm_born_frequency_volume_canonical`; it is not restated here.

## T9 (mixed states): no inhabitant, by the reported gap

We give NO inhabitant of a mixed-state Born or ensemble target. The `DensityOperatorIx.IsPure` purity
predicate is defined (`FND/CompositeInterface.lean`), but the convex-ensemble representation and the Born
rule on mixtures are the reported Mathlib density-matrix gap: Mathlib has no mixed-state type, and the
repository's `CSD.LF2.DensityOperatorIx` carries no purity/ensemble/Born API. This is left out honestly
rather than stated vacuously.
-/

open scoped BigOperators
open CSD.LF3 CSD.Empirical.Bell

namespace CSD.FND

/-! ### T15: no-signalling from the singlet -/

/-- **T15 inhabited by the singlet.** The singlet joint outcome law `P_st` satisfies operational
no-signalling: both marginals are independent of the far party's setting. From `no_signalling_alice`
and `no_signalling_bob`. -/
theorem singlet_hasNoSignalling : HasNoSignalling P_st :=
  ⟨fun a b b' s => no_signalling_alice a b b' s,
    fun a a' b t => no_signalling_bob a a' b t⟩

/-! ### T14: Bell nonlocality -/

/-- **T14 (CGLMP) inhabited by the maximally-entangled qudit.** No measurable local-hidden-variable
table reproduces the maximally-entangled QM CGLMP table `pQM d`, for every `d ≥ 2`. From
`no_lhv_realises_maxEntangled_cglmp_d` (the `d`-intrinsic CGLMP violation). -/
theorem maxEntangled_noLocalHiddenVariable (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    NoLocalHiddenVariableTable (CSD.LF6.CGLMPQudit.pQM d) :=
  fun _Λ _ μ _ A B hA hB hRep =>
    CSD.LF6.CGLMPQudit.no_lhv_realises_maxEntangled_cglmp_d d hd μ A B hA hB hRep

/-- **T14 (CHSH/Tsirelson) inhabited by the singlet.** The classical local bound `2` is strictly below
the Tsirelson value `2√2`, and the singlet at the optimal angles attains `|CHSH| = 2√2`. From
`chsh_classical_bound_violated` and `chsh_singlet_tsirelson_bound`. -/
theorem singlet_hasTsirelsonSeparation :
    HasTsirelsonSeparation
      (fun q : DetectorSetting × DetectorSetting × DetectorSetting × DetectorSetting =>
        chshOperator q.1 q.2.1 q.2.2.1 q.2.2.2)
      bellClassicalBoundValue := by
  refine ⟨chsh_classical_bound_violated, ?_⟩
  obtain ⟨a, a', b, b', h⟩ := chsh_singlet_tsirelson_bound
  exact ⟨(a, a', b, b'), h⟩

/-! ### T13: contextuality -/

/-- **T13 inhabited by Kochen-Specker (Cabello-18).** No `{true, false}` valuation of the 18 Cabello
vectors selects exactly one vector per basis. From `ks_no_value_assignment_cabello18`. -/
theorem cabello18_noNonContextualValuation :
    NoNonContextualValuation
      (fun lambda : Fin 18 → Bool =>
        ∀ B : Fin 9, ((CSD.Empirical.KochenSpecker.cabelloBasis B).filter
          (fun v => lambda v = true)).card = 1) :=
  CSD.Empirical.KochenSpecker.ks_no_value_assignment_cabello18

/-- **T13 inhabited by Mermin-Peres.** No `±1` valuation of the 3×3 Mermin-Peres square reproduces the
six operator-product parities. From `no_lhv_mermin_peres`. -/
theorem merminPeres_noNonContextualValuation :
    NoNonContextualValuation
      (fun lambda : Fin 3 → Fin 3 → ℤ =>
        (∀ i j, lambda i j = 1 ∨ lambda i j = -1) ∧
        (lambda 0 0 * lambda 0 1 * lambda 0 2 = 1) ∧
        (lambda 1 0 * lambda 1 1 * lambda 1 2 = 1) ∧
        (lambda 2 0 * lambda 2 1 * lambda 2 2 = 1) ∧
        (lambda 0 0 * lambda 1 0 * lambda 2 0 = 1) ∧
        (lambda 0 1 * lambda 1 1 * lambda 2 1 = 1) ∧
        (lambda 0 2 * lambda 1 2 * lambda 2 2 = -1)) :=
  CSD.Empirical.MerminPeres.no_lhv_mermin_peres

/-- **T13 inhabited by GHZ (Mermin).** No `±1` valuation of the three parties' `x, y` axes reproduces the
four GHZ/Mermin product parities. From `no_lhv_assignment_for_ghz`. -/
theorem ghz_noNonContextualValuation :
    NoNonContextualValuation
      (fun lambda : Fin 3 → CSD.Empirical.GHZ.PauliAxis → ℤ =>
        (∀ i ax, lambda i ax = 1 ∨ lambda i ax = -1) ∧
        lambda 0 CSD.Empirical.GHZ.PauliAxis.x * lambda 1 CSD.Empirical.GHZ.PauliAxis.x
            * lambda 2 CSD.Empirical.GHZ.PauliAxis.x = 1 ∧
        lambda 0 CSD.Empirical.GHZ.PauliAxis.x * lambda 1 CSD.Empirical.GHZ.PauliAxis.y
            * lambda 2 CSD.Empirical.GHZ.PauliAxis.y = -1 ∧
        lambda 0 CSD.Empirical.GHZ.PauliAxis.y * lambda 1 CSD.Empirical.GHZ.PauliAxis.x
            * lambda 2 CSD.Empirical.GHZ.PauliAxis.y = -1 ∧
        lambda 0 CSD.Empirical.GHZ.PauliAxis.y * lambda 1 CSD.Empirical.GHZ.PauliAxis.y
            * lambda 2 CSD.Empirical.GHZ.PauliAxis.x = -1) :=
  CSD.Empirical.GHZ.no_lhv_assignment_for_ghz

/-! ### T10: POVM normalisation -/

/-- **T10 (normalisation) inhabited.** On a unit state a POVM's Born weights sum to one, so they are a
probability distribution over outcomes. From `POVM.weights_sum_eq_one`. -/
theorem povm_weightsProbability {N : ℕ} {ι : Type*} [Fintype ι] (P : CSD.LF2.POVM N ι)
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1) :
    POVMWeightsProbability P ψ :=
  P.weights_sum_eq_one ψ hψ

end CSD.FND
