/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF6.ForcedContextuality
public import CsdLean4.LF6.GHZContextuality
public import CsdLean4.LF4.SingletKahler

/-!
# WS-I witness: composite nonfactorisation on the concrete arena

**Category:** Special (validation-hardening witness suite,
`specs/validation-hardening-plan.md` WS-I).

**Where CSD's composite nonfactorisation lives.** In this corpus the claim is
*partition-level*, not state-level: no setting-local product partition of the
ontic space `Σ` (responses `RA a`, `RB b` each depending on one wing's setting
and the shared microstate alone) reproduces the singlet correlations — the
Bell-forced content of `no_product_partition_realises_singlet` (LF6-A, riding
E91's `lhvCHSH_abs_le_two`). The subsystem structure is explicit in
production: wings `ℂ²`, composite `HAB = EuclideanSpace ℂ (Fin 2 × Fin 2)`
with the unit `singlet` state (`LF3/Singlet/State.lean`), realised on the
concrete ontic arena `KSigma 4 = ℂℙ³ × T²` with fibre law `kMuPsi`
(`LF4/SingletKahler.lean`); the dynamical tie is
`singletDeisolation_carve_not_product` (LF6). A Hilbert-space-level
"`singlet ≠ u ⊗ v`" lemma is deliberately **not** added here: it would be new
QM-side mathematics beside the corpus's Σ-partition formulation, exactly what
the anti-duplication rule forbids.

This module instantiates the obstruction chain on the concrete witness arena:

* `kMuPsi_no_product_partition` — no product partition of `(KSigma 4, kMuPsi)`
  reproduces the singlet: the composite ontic structure over the concrete
  arena is **not** the excluded Cartesian/product ontology;
* `kMuPsi_productPartition_nonvacuous` — product partitions of the arena
  *exist* (constant correlation `1`), so the obstruction is a genuine
  separation there, not an unsatisfiable predicate;
* `fs_no_product_partition_ghz` — the tripartite (GHZ, deterministic
  all-or-nothing) analogue on the concrete `(ℂℙ⁷, μ_FS)` arena.
-/

@[expose] public section

open MeasureTheory Matrix Matrix.UnitaryGroup
open CSD.LF3 CSD.LF4 CSD.LF6 CSD.Empirical.QM.E91

namespace CSD
namespace Tests
namespace Witnesses

/-- **WS-I headline: composite nonfactorisation on the concrete arena.** No
setting-local product partition of the concrete singlet arena
`(KSigma 4, kMuPsi)` reproduces the singlet correlations. Instantiates
`no_product_partition_realises_singlet` (Bell-forced; rides
`lhvCHSH_abs_le_two`) at the witness space — the composite ontic structure
over the concrete arena is not the excluded product ontology. -/
theorem kMuPsi_no_product_partition :
    ∀ RA RB : DetectorSetting → KSigma 4 → ℝ,
      IsProductPartition RA RB → ReproducesSinglet kMuPsi RA RB → False :=
  fun RA RB hPP hRep =>
    no_product_partition_realises_singlet kMuPsi RA RB hPP hRep

/-- **Non-vacuity on the concrete arena.** Product partitions of
`(KSigma 4, kMuPsi)` exist (the all-`+1` responses, constant correlation `1`),
so `kMuPsi_no_product_partition` is a genuine separation, not an artefact of
an unsatisfiable predicate. Instantiates `productPartition_nonvacuous`. -/
theorem kMuPsi_productPartition_nonvacuous :
    IsProductPartition (Λ := KSigma 4)
        (fun (_ : DetectorSetting) (_ : KSigma 4) => (1 : ℝ))
        (fun (_ : DetectorSetting) (_ : KSigma 4) => (1 : ℝ)) ∧
      (∀ a b : DetectorSetting,
        lhvCorrelation kMuPsi
          (fun (_ : DetectorSetting) (_ : KSigma 4) => (1 : ℝ))
          (fun (_ : DetectorSetting) (_ : KSigma 4) => (1 : ℝ)) a b = 1) :=
  productPartition_nonvacuous kMuPsi

/-- **The tripartite analogue on a concrete arena.** No party-local product
partition of `(ℂℙ⁷, μ_FS)` reproduces the GHZ perfect correlations — the
deterministic all-or-nothing composite obstruction, at every base point.
Instantiates `no_product_partition_realises_ghz` (which routes through
`no_lhv_assignment_for_ghz`; the contradiction is pointwise, not a
statistical inequality). -/
theorem fs_no_product_partition_ghz (p₀ : CPN 8) :
    ∀ R : Fin 3 → Empirical.GHZ.PauliAxis → CPN 8 → ℝ,
      IsProductPartitionGHZ R → ReproducesGHZ (fubiniStudyMeasure p₀) R → False :=
  fun R hPP hRep =>
    no_product_partition_realises_ghz (fubiniStudyMeasure p₀) R hPP hRep

end Witnesses
end Tests
end CSD
