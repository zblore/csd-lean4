/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
import CsdLean4.SigmaLayer.ProjectiveSector
import CsdLean4.Mathlib.Probability.CGLMP
import CsdLean4.LF2.POVM
import CsdLean4.LF2.ReducedDensity

/-!
# SigmaLayer/CompositeInterface: composite, mixed-state, POVM, contextuality and Bell targets

**Category:** 7-SigmaLayer (the projective-sector layer (Paper C)).

Tranche 3. The composition- and measurement-dependent reconstruction targets (ledger T9-T15 of
`SigmaLayer/Adapters.lean`) as bridge interfaces and uninhabited `Prop` predicates. As with
`SigmaLayer/TheoremTargets.lean`, a target predicate is NOT a postulate: it is a statement whose inhabitants
are theorems, proved for concrete models in `SigmaLayer/CompositeAdapters.lean` by wiring the existing
LF6/Empirical CGLMP, CHSH, GHZ, Kochen-Specker and no-signalling capstones through these interfaces.

Every predicate here is stated GENERICALLY (over the table, valuation, POVM or density operator), so this
module depends only on the type-providing files, and the concrete instances are supplied by the adapter
module. We deliberately provide NO inhabitants here.

## Parked and reported targets

* **B6 (composite tensor structure).** `CompositeSector` carries the tensor dimension as a NAMED field,
  not a theorem: the P3 tensor-product derivation is parked by standing instruction, so composite
  structure is posited per instance.
* **T11 (composite joint probabilities), T12 (entangled predictions).** Not given separate predicates
  here. T11 is realised as the joint Born frequencies of the existing entangled capstones (the
  `bell_singlet_frequency_convergence_joint` family); T12 (entangled predictions inconsistent with any
  local model) is exactly `NoLocalHiddenVariableTable` (T14). Both are recorded as awaiting the parked
  P3 derivation for a sector-intrinsic statement.
* **Mixed-state / density-matrix gap.** Mathlib has NO density-matrix or mixed-state type (no
  `Mathlib/QuantumInfo`, no trace-one-state structure). The repository's own `CSD.LF2.DensityOperatorIx`
  (trace-one positive semidefinite Hermitian, with `reduced`/`reducedLeft` partial traces) is the only
  primitive available. It has no purity predicate, no convex-ensemble API, and no Born rule stated on it
  (the POVM/Born surface is on pure states). `DensityOperatorIx.IsPure` below adds the purity predicate;
  the ensemble/mixture and mixed-Born content remains a genuine gap.
-/

open MeasureTheory
open scoped BigOperators LinearAlgebra.Projectivization

namespace CSD.SigmaLayer

universe u

/-! ### B6: the composite sector bridge interface -/

/-- **The composite projective sector (bridge B6).** A joint projective sector for a composite system,
together with the tensor-dimension relation `NA * NB = Njoint` as a `tensor_dimension` field. The field
can be filled by ASSUMPTION (a bare bridge instance) OR DERIVED: `CSD.SigmaLayer.CompositeSector.ofReconstruction`
(`SigmaLayer/TensorReconstruction.lean`) constructs a `CompositeSector` in which `tensor_dimension` is PROVED by
`composite_dim_eq` from commuting, generating local observable embeddings — so B6 is no longer necessarily
a posit. The by-hand entangled tier still supplies the field directly per instance; the reconstruction
route is available whenever the local-algebra data is on hand. -/
structure CompositeSector (NA NB Njoint : ℕ) {Sigma : Type u} [MeasurableSpace Sigma]
    (D : ConstraintDynamics Sigma) where
  /-- The joint projective sector on the composite dilation. -/
  jointSector : ProjectiveSector Njoint D
  /-- B6 (parked): the composite dimension realises the tensor product of the two parties. -/
  tensor_dimension : NA * NB = Njoint

/-! ### T15: operational no-signalling -/

/-- **T15: operational no-signalling.** For a joint outcome law `P` over party settings `SA, SB` and
outcomes `OA, OB`, each party's marginal is independent of the other party's setting: Alice's marginal is
the same for any Bob setting, and vice versa. Generic over the setting/outcome types. -/
def HasNoSignalling {SA SB OA OB : Type*} [Fintype OA] [Fintype OB]
    (P : SA → SB → OA → OB → ℝ) : Prop :=
  (∀ (a : SA) (b b' : SB) (s : OA), (∑ t : OB, P a b s t) = (∑ t : OB, P a b' s t)) ∧
  (∀ (a a' : SA) (b : SB) (t : OB), (∑ s : OA, P a b s t) = (∑ s : OA, P a' b s t))

/-! ### T14: Bell nonlocality -/

/-- **T14 (CGLMP form): no local-hidden-variable table.** No measurable local-hidden-variable model
(two `Bool` settings per party, `ZMod d` outcomes) reproduces the quantum CGLMP table `qmTable`. Generic
over the target table; the maximally-entangled qudit table `pQM d` inhabits it in the adapter module. -/
def NoLocalHiddenVariableTable {d : ℕ} (qmTable : Bool → Bool → ZMod d → ℝ) : Prop :=
  ∀ (Λ : Type) [MeasurableSpace Λ] (μ : Measure Λ) [IsProbabilityMeasure μ]
    (A B : Bool → Λ → ZMod d), (∀ x, Measurable (A x)) → (∀ y, Measurable (B y)) →
    ProbabilityTheory.CGLMP.lhvTable μ A B = qmTable → False

/-- **T14 (CHSH/Tsirelson form): a Tsirelson separation.** The classical local bound is strictly below
the Tsirelson value `2√2`, and some measurement configuration attains `|CHSH| = 2√2`. Generic over the
configuration type and the CHSH functional. -/
def HasTsirelsonSeparation {S : Type*} (chsh : S → ℝ) (classicalBound : ℝ) : Prop :=
  classicalBound < 2 * Real.sqrt 2 ∧ ∃ s : S, |chsh s| = 2 * Real.sqrt 2

/-! ### T13: contextuality -/

/-- **T13: no non-contextual valuation.** The set of value assignments satisfying the given constraints
is empty: no non-contextual (assignment-based) model reproduces the quantum constraints. Generic over
the valuation type and the constraint predicate; the Kochen-Specker (Cabello-18), Mermin-Peres and GHZ
obstructions each inhabit it in the adapter module. -/
def NoNonContextualValuation {Val : Type*} (constraints : Val → Prop) : Prop :=
  ¬ ∃ v : Val, constraints v

/-! ### T10: POVM measurement -/

/-- **T10 (normalisation): a POVM's Born weights form a probability distribution.** On a unit state the
weights sum to one. Generic over the POVM; inhabited via `POVM.weights_sum_eq_one`. The full T10 content
(the weights realised as Fubini-Study pointer-block frequencies through a Naimark dilation) is the
existing `povm_born_frequency_volume_canonical`, re-exposed in the adapter module. -/
def POVMWeightsProbability {N : ℕ} {ι : Type*} [Fintype ι] (P : CSD.LF2.POVM N ι)
    (ψ : EuclideanSpace ℂ (Fin N)) : Prop :=
  ∑ i, P.weight ψ i = 1

/-! ### T9: mixed states -/

/-- **T9 (purity): a density operator is pure iff idempotent.** A trace-one positive semidefinite
Hermitian operator represents a projective sector pure state exactly when it is a projector (`ρ² = ρ`, hence
rank one given trace one); otherwise it is a genuine mixture. This is the purity primitive Mathlib
lacks. The convex-ensemble representation and the Born rule on mixtures remain a gap (see the module
header). -/
def DensityOperatorIx.IsPure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : CSD.LF2.DensityOperatorIx ι) : Prop :=
  ρ.M * ρ.M = ρ.M

end CSD.SigmaLayer
