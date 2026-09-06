/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.ObservableCorrespondenceN
public import CsdLean4.SigmaLayer.MixedEnsemble
public import CsdLean4.RecordLayer.BasinFrequency

/-!
# LF4 §14 states obligation: mixed states / density operators as ontic eigen-mixtures

**Category:** 3-Local (LF4 §14 discharge — the density-operator / mixed-state case of the states
obligation).

This module discharges the **mixed-state** part of the §14 *states* obligation, completing the
states-side realisation begun for pure states / rank-one projectors in
`LF4/ObservableCorrespondenceN.lean` (`pure_state_born_prob_eq_volume`).

A density operator `ρ` is realised as an **ontic eigen-mixture**: its Born probability
`Tr(ρ · |φ⟩⟨φ|)` of a projective outcome `|φ⟩` is the `ρ`-eigenvalue-weighted sum of the ontic
typicality measures of `ρ`'s pure eigenstates, on the fibred arena `Σ = ℂℙ^M × T²`
(`mixed_state_born_eq_ensemble_volume`). This composes three existing pieces:

* the spectral ensemble `Tr(ρ · E) = ∑ᵢ λᵢ · Tr(|eᵢ⟩⟨eᵢ| · E)` (`SigmaLayer.mixedEnsemble_capstone`);
* the pure Born rule `Tr(|eᵢ⟩⟨eᵢ| · |φ⟩⟨φ|) = ‖⟨eᵢ, φ⟩‖²` (`LF2.born_quadratic`);
* the pure-state ontic realisation `‖⟨φ, eᵢ⟩‖² = μ(globalBasin (momentContext _) 0)` at the
  transported ray `[Wᴴ eᵢ]` (`pure_state_born_prob_eq_basin`, the fibred twin of
  `LF4.pure_state_born_prob_eq_volume`), with `W` a unitary sending `e₀ ↦ φ`.

⚠️ **No genericity hypothesis.** The base-side route carried `hpos` on each transported
eigenvector `Wᴴ eᵢ` (the outcome `φ` had to overlap every eigenvector of `ρ`). The fibred route
goes through the unconditional `globalBasin_born`, so the migration *removed* that restriction:
every density operator and every pure outcome is now covered. This realises the density operator
(mixed state) as an ontic object — the
state-side content underlying the resource bundle `NoBroadcasting` (a bipartite `ρ` confined to a
pure marginal). Foundational triple; carving-free, Gleason-free.

References: `LF4/ObservableCorrespondenceN.lean` (`pure_state_born_prob_eq_volume`, the base-side
twin, and `unitary_transport_norm`); `RecordLayer/GlobalBasin.lean` (`globalBasin_born`);
`SigmaLayer/MixedEnsemble.lean` (`mixedEnsemble_capstone`, `eigenvectorBasis_norm_one`);
`LF2/BornWrapper.lean` (`born_quadratic`, `rankOneEffect`, `traceForm`); `specs/LF4-todo.md §14`;
`BRIDGE-OBLIGATIONS.md` (the §14 states bundle fields).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Matrix Matrix.UnitaryGroup Unitary
open scoped ENNReal LinearAlgebra.Projectivization

namespace CSD
namespace LF4

open CSD.LF2 CSD.SigmaLayer

variable {M : ℕ}

/-- ★ **The pure-state realisation on the fibred arena** — the fibred twin of
`pure_state_born_prob_eq_volume` (CR-4).

The Born probability `‖⟨Φ, ψ⟩‖²` is the epistemic typicality measure of the global basin of
index `0` at the transported ray `[Wᴴ ψ]`, on `Σ = ℂℙ^M × T²`.

⚠️ **The genericity hypothesis is gone.** The base-side theorem carries `hpos` (the outcome must
overlap every basis direction) because it goes through `fsMeasure_bornRegionN`. The fibred route
goes through `CSD.RecordLayer.globalBasin_born`, which is unconditional, so migrating this
statement *drops* a hypothesis rather than moving one.

**Placement.** This lives here rather than beside the other CR-4 engine twins in
`RecordLayer/BasinFrequency.lean` because it has exactly one consumer, the capstone below
(CONVENTIONS.md §9, rule of two). If a second consumer appears, move it there. -/
theorem pure_state_born_prob_eq_basin
    (Φ ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ : ‖ψ‖ = 1)
    (W : Matrix.unitaryGroup (Fin (M + 1)) ℂ)
    (hW : Matrix.toEuclideanLin W.val (EuclideanSpace.single 0 (1 : ℂ)) = Φ)
    (φ : EuclideanSpace ℂ (Fin (M + 1)))
    (hφ : φ = Matrix.toEuclideanLin (star W.val) ψ) (hφ0 : φ ≠ 0) :
    ‖inner ℂ Φ ψ‖ ^ 2
      = (CSD.RecordLayer.epistemicMeasure (Projectivization.mk ℂ φ hφ0)
          (CSD.RecordLayer.globalBasin (CSD.RecordLayer.momentContext (M + 1)) 0)).toReal := by
  have hφnorm : ‖φ‖ = 1 := by rw [hφ]; exact unitary_transport_norm W ψ hψ
  rw [CSD.RecordLayer.globalBasin_born φ hφ0 hφnorm 0, ENNReal.toReal_ofReal (by positivity)]
  congr 1
  rw [← hW, inner_toEuclideanLin_adjoint W (EuclideanSpace.single 0 (1 : ℂ)) ψ, ← hφ]

/-- **§14 states obligation — the mixed-state / density-operator case.** A density operator `ρ` is
realised as an **ontic eigen-mixture**: the Born probability `Tr(ρ · |φ⟩⟨φ|)` of a projective
outcome `|φ⟩` is the `ρ`-eigenvalue-weighted sum of the ontic typicality measures of `ρ`'s pure
eigenstates on the fibred arena. Composes the spectral ensemble (`mixedEnsemble_capstone`), the
pure Born rule (`born_quadratic`), and the pure-state realisation
(`pure_state_born_prob_eq_basin`). No genericity hypothesis. Foundational triple.

⚠️ `hφ0` is **not** a residual restriction: `Wᴴ eᵢ` has norm one (`unitary_transport_norm`), so
its nonzero-ness is derivable. The binder is there because `Projectivization.mk` takes the proof
as data, not because the theorem needs an assumption.

This realises the density operator (mixed state) as an ontic object — the state-side content
underlying `NoBroadcasting` (a bipartite `ρ` confined to a pure marginal). -/
theorem mixed_state_born_eq_ensemble_volume (ρ : DensityOperator (M + 1))
    (φ : EuclideanSpace ℂ (Fin (M + 1))) (hφ : ‖φ‖ = 1)
    (W : Matrix.unitaryGroup (Fin (M + 1)) ℂ)
    (hW : Matrix.toEuclideanLin W.val (EuclideanSpace.single 0 (1 : ℂ)) = φ)
    (hφ0 : ∀ i, Matrix.toEuclideanLin (star W.val) (ρ.isHermitian.eigenvectorBasis i) ≠ 0) :
    traceForm ρ (rankOneEffect φ hφ)
      = ∑ i, ρ.isHermitian.eigenvalues i
          * (CSD.RecordLayer.epistemicMeasure
              (Projectivization.mk ℂ (Matrix.toEuclideanLin (star W.val)
                (ρ.isHermitian.eigenvectorBasis i)) (hφ0 i))
              (CSD.RecordLayer.globalBasin
                (CSD.RecordLayer.momentContext (M + 1)) 0)).toReal := by
  rw [mixedEnsemble_capstone ρ (rankOneEffect φ hφ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [born_quadratic (ρ.isHermitian.eigenvectorBasis i) φ (eigenvectorBasis_norm_one ρ i) hφ,
      show ‖inner ℂ (ρ.isHermitian.eigenvectorBasis i) φ‖ ^ 2
          = ‖inner ℂ φ (ρ.isHermitian.eigenvectorBasis i)‖ ^ 2 from by
        rw [← inner_conj_symm, RCLike.norm_conj]]
  exact pure_state_born_prob_eq_basin φ (ρ.isHermitian.eigenvectorBasis i)
    (eigenvectorBasis_norm_one ρ i) W hW _ rfl (hφ0 i)

end LF4
end CSD
