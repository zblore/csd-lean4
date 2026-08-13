/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.BasisMeasurement
public import CsdLean4.LF4.BargmannSelection
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudyUnique

/-!
# RecordLayer/StatisticsRigidity: transition probabilities are record observables (Q18)

**Category:** 7-SigmaLayer (the record layer — the operational statistics kernel).

The Q11 scoping session ([`specs/unitary-tpp-scoping.md`](../../specs/unitary-tpp-scoping.md))
reduced the necessity audit's two systematic conditioners — the `hTPP` FS-isometry posit of
`LF4/UnitarySelection.lean` (W3) and the `U(N)`-invariance datum of every measure-forcing
result — to ONE record-level premise. This module is the named first brick: it proves the
**kernel identification** and lands the two conversions.

## The kernel identification

`recordKernel p q` is the **operational pairwise statistic**: the Born rate that a context
containing `q` as an outcome assigns to the unit preparation representative of `p`. It is
defined *through the record machinery* (`bornRateBasis`, a chosen extending context) — the
definition never mentions the inner product. The headline

* ★★ `recordKernel_eq_transProb` — `recordKernel p q = transProb p q`

identifies it with the Fubini–Study transition probability, and
`recordKernel_well_defined` shows ANY context containing `q` assigns the same rate (the
operational independence that makes the kernel a statistic of the pair, not of the chosen
apparatus). Consequently

* ★ `recordStatisticsPreserving_iff_transProbPreserving` — *"preserves the record layer's
  observable statistics"* and *"preserves the FS metric"* are the SAME predicate.

## The two conversions (premise conversion, NOT elimination)

* ★ `projectedFlow_unitary_of_record_statistics` — W3 + the Bargmann selection consumed
  with the record-level premise `∀ t, RecordStatisticsPreserving (d.projectedFlow t)` in
  place of `hTPP`. A thin wrapper over `projectedFlow_unitary_of_bargmann_continuous`, and
  honestly labelled as such: the mathematics is the existing Wigner chain; what changes is
  the *status* of the hypothesis — operational (preserves observed record statistics)
  rather than geometric (is an FS-isometry).
* ★★ `measure_eq_fubiniStudy_of_record_statistics_invariant` — any probability measure on
  the sector invariant under EVERY record-statistics-preserving symmetry is the
  Fubini–Study measure. `U(N)` appears in the proof (via `transProbPreserving_unitary` +
  `fubiniStudyMeasure_unique`), **never in the statement** — the conversion the necessity
  audit asked for, in the `fubiniStudy_forced_by_symmetry` template: the group is no
  longer named in the premise.
* `recordStatisticsPreserving_realisation` — the operational symmetry group is
  semi-unitary: every record-statistics-preserving self-map is realised by a unitary or an
  antiunitary (`wigner_rigidity_unitaryGroup` through the iff). With the realisability
  inclusions `recordStatisticsPreserving_unitary` / `recordStatisticsPreserving_conjProj`
  this identifies the operationally-defined symmetry group with the semi-unitary group in
  the forward-and-realisability directions.

## Honest scope (read before citing)

* **Premise conversion, not elimination.** The operational premises survive as posits:
  *why the projected flow preserves record statistics* (for the dynamics) and the
  indifference principle *the sampling law cannot weight configurations no record
  statistics distinguish* (for the measure). Both are better-motivated than the named
  structures they replace — that is the entire claim; their physical motivation is owed by
  the papers, not by this file.
* **NOT the §13.2 trap.** Nothing here derives transition-probability preservation from
  `flow_preserves_volume`. Statistics preservation is logically independent of Liouville
  (a measure-preserving map need not preserve any context's rates); the `measure ≠ metric`
  guard in `LF4/UnitarySelection.lean` stands unchanged.
* **D1 (`G`-from-dynamics) untouched.** `obsFlow_not_uniquely_ergodic` still shows a
  single ontic flow cannot force the measure; the operational route *sidesteps* the
  dynamics route rather than repairing it.
* **The FS-invariance converse is not stated.** "μ_FS is invariant under every
  record-statistics-preserving map" would need FS-invariance of the antiunitary branch
  (`conjProj` pushforward), which the corpus does not have; the discharge direction
  (statements above) does not need it.

## Non-vacuity

`recordStatisticsPreserving_unitary` inhabits the predicate at every unitary — genuinely
moving maps, not the identity — and `recordStatisticsPreserving_conjProj` inhabits the
antiunitary class, so the realisation disjunction is non-vacuous on both branches.

## Provenance

Foundational-triple only (`propext, Classical.choice, Quot.sound`); no `sorry`, no new
axioms. Wigner (`wigner_rigidity_unitaryGroup`) and the measure uniqueness
(`fubiniStudyMeasure_unique`) are consumed as-is, not rebuilt here.

## References

`specs/unitary-tpp-scoping.md` §4–§5 (the scoping this executes); `specs/BACKLOG.md` row
Q18; `specs/necessity-audit.md` (the two conditioners); `specs/future-work.md` (W-3, the
§13.2 caveat on SL-3, D1c); `RecordLayer/BasisMeasurement.lean` (`bornRateBasis`,
`bornRateBasis_eq_inner_sq`); `Mathlib/LinearAlgebra/Projectivization/
TransitionProbability.lean` (`transProb`, `transProb_mk`); `WignerRigidity.lean`
(`TransProbPreserving`, `wigner_rigidity_unitaryGroup`, `conjProj`);
`FubiniStudyUnique.lean` (`fubiniStudyMeasure_unique`); `LF4/BargmannSelection.lean`
(`projectedFlow_unitary_of_bargmann_continuous`).
-/

@[expose] public section

open MeasureTheory
open scoped LinearAlgebra.Projectivization
open Projectivization

namespace CSD
namespace RecordLayer

variable {N : ℕ}

/-! ## The unit preparation representative -/

/-- The unit-norm canonical representative of a ray: the preparation vector the record
machinery samples. -/
noncomputable def unitRep (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) : EuclideanSpace ℂ (Fin N) :=
  (‖p.rep‖⁻¹ : ℂ) • p.rep

/-- The unit representative is a unit vector. -/
theorem norm_unitRep (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) : ‖unitRep p‖ = 1 := by
  show ‖(‖p.rep‖⁻¹ : ℂ) • p.rep‖ = 1
  exact norm_smul_inv_norm p.rep_nonzero

/-- The unit representative is nonzero. -/
theorem unitRep_ne_zero (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) : unitRep p ≠ 0 := by
  intro h
  have h1 := norm_unitRep p
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

/-- The unit representative represents its ray. -/
theorem mk_unitRep (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    Projectivization.mk ℂ (unitRep p) (unitRep_ne_zero p) = p := by
  conv_rhs => rw [← p.mk_rep]
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ (unitRep_ne_zero p) p.rep_nonzero).mpr
    ⟨(‖p.rep‖⁻¹ : ℂ), rfl⟩

/-! ## Transition probabilities are record observables: the pointwise identification -/

/-- **The pointwise identification** (general inner-product space form). For a unit
preparation `ψ` and a context `b` containing the outcome vector `b i`, the projective
transition probability between the rays IS the record layer's Born rate of outcome `i`:
`transProb [ψ] [b i] = bornRateBasis b ψ i`. Route: `transProb_mk` reduces to the
vector-level form on the given representatives; unit norms kill the denominator;
conjugate symmetry aligns the inner-product orientation with `bornRateBasis_eq_inner_sq`. -/
theorem transProb_mk_eq_bornRateBasis {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (b : OrthonormalBasis (Fin n) ℂ E)
    {ψ : E} (hne : ψ ≠ 0) (hψ : ‖ψ‖ = 1) (i : Fin n) :
    transProb (Projectivization.mk ℂ ψ hne)
        (Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i))
      = bornRateBasis b ψ i := by
  rw [transProb_mk hne (b.orthonormal.ne_zero i), bornRateBasis_eq_inner_sq]
  unfold transProbVec
  rw [hψ, b.orthonormal.1 i, ← norm_inner_symm ψ (b i)]
  norm_num

/-! ## The operational kernel -/

/-- **Every ray is an outcome of some context**: a chosen orthonormal basis carries a
representative of `q` at a chosen index. The tool is the Gram–Schmidt extension
`Orthonormal.exists_orthonormalBasis_extension_of_card_eq` applied to the singleton
family `{unitRep q}`. -/
theorem exists_context_extending_ray (q : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    ∃ (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N),
      Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i) = q := by
  -- the sector is inhabited, so `N` is positive and an index exists
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exfalso
      apply q.rep_nonzero
      subst h
      exact Subsingleton.elim _ _
    · exact h
  let i₀ : Fin N := ⟨0, hN⟩
  have hun : ‖unitRep q‖ = 1 := norm_unitRep q
  -- the singleton family at `i₀` is orthonormal
  have hs : Orthonormal ℂ (({i₀} : Set (Fin N)).domRestrict fun _ : Fin N => unitRep q) := by
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · rw [Set.domRestrict_apply]
      exact hun
    · exact absurd (Subtype.ext ((Set.mem_singleton_iff.mp i.2).trans
        (Set.mem_singleton_iff.mp j.2).symm)) hij
  obtain ⟨b, hb⟩ := hs.exists_orthonormalBasis_extension_of_card_eq
    (by rw [finrank_euclideanSpace_fin, Fintype.card_fin])
  refine ⟨b, i₀, ?_⟩
  have hbi : b i₀ = unitRep q := hb i₀ (Set.mem_singleton i₀)
  simp only [hbi]
  exact mk_unitRep q

/-- **The operational pairwise statistic.** The Born rate that a (chosen) context
containing `q` as an outcome assigns to the unit preparation representative of `p` —
defined through the record machinery (`bornRateBasis`), never through the inner product.
`recordKernel_well_defined` shows the chosen context is immaterial;
`recordKernel_eq_transProb` identifies the statistic with the transition probability. -/
noncomputable def recordKernel (p q : ℙ ℂ (EuclideanSpace ℂ (Fin N))) : ℝ :=
  bornRateBasis (exists_context_extending_ray q).choose (unitRep p)
    (exists_context_extending_ray q).choose_spec.choose

/-- ★★ **The kernel identification (the brick's headline).** The record layer's
operational pairwise statistic IS the Fubini–Study transition probability:
`recordKernel p q = transProb p q`. Transition probabilities — the hypothesis
`TransProbPreserving` quantifies over — are thereby OBSERVABLES of the record layer, so a
geometric premise about the FS metric and an operational premise about observed record
statistics are statements about the same quantity. This is what converts the `hTPP` and
`U(N)` conditioners (`specs/unitary-tpp-scoping.md` §4). -/
theorem recordKernel_eq_transProb (p q : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    recordKernel p q = transProb p q := by
  show bornRateBasis (exists_context_extending_ray q).choose (unitRep p)
      (exists_context_extending_ray q).choose_spec.choose = transProb p q
  rw [← transProb_mk_eq_bornRateBasis _ (unitRep_ne_zero p) (norm_unitRep p) _,
      mk_unitRep, (exists_context_extending_ray q).choose_spec.choose_spec]

/-- **Context independence.** ANY context carrying `q` at ANY index assigns the
preparation `p` the same rate — the kernel is a statistic of the pair, not of the chosen
apparatus. Immediate from the identification applied on both sides. -/
theorem recordKernel_well_defined
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) (i : Fin N)
    {ψ : EuclideanSpace ℂ (Fin N)} (hne : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    {p q : ℙ ℂ (EuclideanSpace ℂ (Fin N))}
    (hp : Projectivization.mk ℂ ψ hne = p)
    (hq : Projectivization.mk ℂ (b i) (b.orthonormal.ne_zero i) = q) :
    bornRateBasis b ψ i = recordKernel p q := by
  rw [recordKernel_eq_transProb, ← hp, ← hq, transProb_mk_eq_bornRateBasis b hne hψ i]

/-! ## The operational symmetry predicate -/

/-- A self-map of the sector **preserves record statistics** when it preserves the
operational pairwise kernel — every preparation/outcome pair keeps its observed rate.
This is the record-level premise the Q11 conversions consume in place of the geometric
`TransProbPreserving`. -/
def RecordStatisticsPreserving
    (f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))) : Prop :=
  ∀ p q, recordKernel (f p) (f q) = recordKernel p q

/-- ★ **The predicates coincide.** Preserving the record layer's observable statistics IS
preserving the Fubini–Study transition probabilities — stated as an iff so the
operationally-defined symmetry group is *identified with*, not merely included in, the
transition-probability preservers. Immediate from the kernel identification, which is
where the content lives. -/
theorem recordStatisticsPreserving_iff_transProbPreserving
    (f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    RecordStatisticsPreserving f ↔ TransProbPreserving f := by
  constructor
  · intro h p q
    have h1 := h p q
    rwa [recordKernel_eq_transProb, recordKernel_eq_transProb] at h1
  · intro h p q
    rw [recordKernel_eq_transProb, recordKernel_eq_transProb]
    exact h p q

/-- **Realisability (unitary branch).** Every unitary action preserves record statistics
— non-vacuity of the predicate at genuinely moving maps. -/
theorem recordStatisticsPreserving_unitary (U : Matrix.unitaryGroup (Fin N) ℂ) :
    RecordStatisticsPreserving (fun p : ℙ ℂ (EuclideanSpace ℂ (Fin N)) => U • p) :=
  (recordStatisticsPreserving_iff_transProbPreserving _).mpr (transProbPreserving_unitary U)

/-- **Realisability (antiunitary branch).** Complex conjugation of the representative
preserves record statistics, so the realisation disjunction below is non-vacuous on the
antiunitary side too. -/
theorem recordStatisticsPreserving_conjProj :
    RecordStatisticsPreserving (conjProj (N := N)) :=
  (recordStatisticsPreserving_iff_transProbPreserving _).mpr conjProj_transProbPreserving

/-- **The operational symmetry group is semi-unitary.** Every record-statistics-preserving
self-map of the sector is realised by a unitary or an antiunitary — Wigner rigidity
consumed through the kernel identification. Together with the two realisability
inclusions, the group of operational symmetries is identified with the semi-unitary group
with no linearity, continuity, or dimension hypothesis. -/
theorem recordStatisticsPreserving_realisation
    {f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N))}
    (hf : RecordStatisticsPreserving f) :
    (∃ U : Matrix.unitaryGroup (Fin N) ℂ, ∀ p, f p = U • p)
    ∨ (∃ U : Matrix.unitaryGroup (Fin N) ℂ, ∀ p, f p = U • conjProj p) :=
  wigner_rigidity_unitaryGroup
    ((recordStatisticsPreserving_iff_transProbPreserving _).mp hf)

/-! ## The two conversions -/

/-- ★ **W3/Bargmann with the record-level premise.** The unitary-branch selection of
`LF4/BargmannSelection.lean`, consumed with "the projected flow preserves record
statistics" in place of the FS-isometry posit `hTPP`. A thin wrapper by design — the
mathematics is the existing Wigner→Bargmann chain; the conversion is in the *status* of
the hypothesis: operational (record statistics) rather than geometric (FS isometry).
NOT the §13.2 trap: nothing is derived from `flow_preserves_volume`. -/
theorem projectedFlow_unitary_of_record_statistics
    (d : LF4.KahlerOnticSetup N)
    (hStats : ∀ t, RecordStatisticsPreserving (d.projectedFlow t))
    (h0 : LF4.ProjUnitary d 0)
    {p q r : ℙ ℂ (EuclideanSpace ℂ (Fin N))} (him : (bargmann p q r).im ≠ 0)
    (hcont : Continuous (LF4.bargmannObservable d p q r)) :
    ∀ t, LF4.ProjUnitary d t :=
  LF4.projectedFlow_unitary_of_bargmann_continuous d
    (fun t => (recordStatisticsPreserving_iff_transProbPreserving _).mp (hStats t))
    h0 him hcont

/-- ★★ **The `U(N)`-free measure statement.** Any probability measure on the sector
invariant under EVERY record-statistics-preserving symmetry is the Fubini–Study measure.
`U(N)` appears in the proof (`transProbPreserving_unitary` feeds
`fubiniStudyMeasure_unique`), **never in the statement**: the premise names no group —
it is the epistemic indifference "the sampling law cannot weight sector configurations
that no record statistics distinguish", and the group over which it quantifies is itself
pinned by `recordStatisticsPreserving_realisation`. This is the conversion the necessity
audit requested, in the same template as `fubiniStudy_forced_by_symmetry`. -/
theorem measure_eq_fubiniStudy_of_record_statistics_invariant [NeZero N]
    (p₀ : ℙ ℂ (EuclideanSpace ℂ (Fin N)))
    (μ : Measure (ℙ ℂ (EuclideanSpace ℂ (Fin N)))) [IsProbabilityMeasure μ]
    (hinv : ∀ f : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (EuclideanSpace ℂ (Fin N)),
      RecordStatisticsPreserving f → μ.map f = μ) :
    μ = Matrix.UnitaryGroup.fubiniStudyMeasure p₀ :=
  Matrix.UnitaryGroup.fubiniStudyMeasure_unique p₀ μ
    (fun U => hinv _ (recordStatisticsPreserving_unitary U))

end RecordLayer
end CSD
