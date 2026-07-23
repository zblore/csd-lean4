/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.ObservableCorrespondenceN
public import CsdLean4.SigmaLayer.MixedEnsemble

/-!
# LF4 §14 states obligation: mixed states / density operators as ontic eigen-mixtures

**Category:** 3-Local (LF4 §14 discharge — the density-operator / mixed-state case of the states
obligation).

This module discharges the **mixed-state** part of the §14 *states* obligation, completing the
states-side realisation begun for pure states / rank-one projectors in
`LF4/ObservableCorrespondenceN.lean` (`pure_state_born_prob_eq_volume`).

A density operator `ρ` is realised as an **ontic eigen-mixture**: its Born probability
`Tr(ρ · |φ⟩⟨φ|)` of a projective outcome `|φ⟩` is the `ρ`-eigenvalue-weighted sum of the ontic
Fubini–Study volumes of `ρ`'s pure eigenstates (`mixed_state_born_eq_ensemble_volume`). This
composes three existing pieces:

* the spectral ensemble `Tr(ρ · E) = ∑ᵢ λᵢ · Tr(|eᵢ⟩⟨eᵢ| · E)` (`SigmaLayer.mixedEnsemble_capstone`);
* the pure Born rule `Tr(|eᵢ⟩⟨eᵢ| · |φ⟩⟨φ|) = ‖⟨eᵢ, φ⟩‖²` (`LF2.born_quadratic`);
* the pure-state ontic realisation `‖⟨φ, eᵢ⟩‖² = vol(bornRegionN (Wᴴ eᵢ) 0)`
  (`LF4.pure_state_born_prob_eq_volume`), with `W` a unitary sending `e₀ ↦ φ`.

Genericity `hpos` is on each transported eigenvector `Wᴴ eᵢ` (i.e. the outcome `φ` overlaps every
eigenvector of `ρ`). This realises the density operator (mixed state) as an ontic object — the
state-side content underlying the resource bundle `NoBroadcasting` (a bipartite `ρ` confined to a
pure marginal). Foundational triple; carving-free, Gleason-free.

References: `LF4/ObservableCorrespondenceN.lean` (`pure_state_born_prob_eq_volume`, `bornRegionN`);
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

/-- **§14 states obligation — the mixed-state / density-operator case.** A density operator `ρ` is
realised as an **ontic eigen-mixture**: the Born probability `Tr(ρ · |φ⟩⟨φ|)` of a projective
outcome `|φ⟩` is the `ρ`-eigenvalue-weighted sum of the ontic Fubini–Study volumes of `ρ`'s pure
eigenstates. Composes the spectral ensemble (`mixedEnsemble_capstone`), the pure Born rule
(`born_quadratic`), and the pure-state realisation (`pure_state_born_prob_eq_volume`). Genericity
`hpos` is on each transported eigenvector `Wᴴ eᵢ`. Foundational triple.

This realises the density operator (mixed state) as an ontic object — the state-side content
underlying `NoBroadcasting` (a bipartite `ρ` confined to a pure marginal). -/
theorem mixed_state_born_eq_ensemble_volume (p₀ : CPN (M + 1)) (ρ : DensityOperator (M + 1))
    (φ : EuclideanSpace ℂ (Fin (M + 1))) (hφ : ‖φ‖ = 1)
    (W : Matrix.unitaryGroup (Fin (M + 1)) ℂ)
    (hW : Matrix.toEuclideanLin W.val (EuclideanSpace.single 0 (1 : ℂ)) = φ)
    (hφ0 : ∀ i, Matrix.toEuclideanLin (star W.val) (ρ.isHermitian.eigenvectorBasis i) ≠ 0)
    (hpos : ∀ i j, 0 < ‖inner ℂ (EuclideanSpace.single j (1 : ℂ))
        (Matrix.toEuclideanLin (star W.val) (ρ.isHermitian.eigenvectorBasis i))‖ ^ 2) :
    traceForm ρ (rankOneEffect φ hφ)
      = ∑ i, ρ.isHermitian.eigenvalues i
          * (fubiniStudyMeasure p₀
              (bornRegionN (Matrix.toEuclideanLin (star W.val)
                (ρ.isHermitian.eigenvectorBasis i)) (hφ0 i) 0)).toReal := by
  rw [mixedEnsemble_capstone ρ (rankOneEffect φ hφ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [born_quadratic (ρ.isHermitian.eigenvectorBasis i) φ (eigenvectorBasis_norm_one ρ i) hφ,
      show ‖inner ℂ (ρ.isHermitian.eigenvectorBasis i) φ‖ ^ 2
          = ‖inner ℂ φ (ρ.isHermitian.eigenvectorBasis i)‖ ^ 2 from by
        rw [← inner_conj_symm, RCLike.norm_conj]]
  exact pure_state_born_prob_eq_volume p₀ φ (ρ.isHermitian.eigenvectorBasis i)
    (eigenvectorBasis_norm_one ρ i) W hW _ rfl (hφ0 i) (hpos i)

end LF4
end CSD
