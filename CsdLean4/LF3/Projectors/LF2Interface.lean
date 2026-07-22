/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF3.Projectors.SectorVolume
public import CsdLean4.LF2.BornWrapper

/-!
# LF3 Projectors / LF2 interface: sector volume ↔ LF2 Born form

**Category:** 3-Local (LF3 → LF2 bridge: sector volume equals LF2 trace-form Born weight on rank-1 effects).

Paper §5.14 / §9.7. (Renamed from branch-weight terminology in Phase 11,
2026-05-18, to align with the volume-ratios reading.)

Bridges the abstract `H_SA`-level sector volume to LF2's concrete matrix-based
Born form. The basis isomorphism `H_SA ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N)` and the
matrix representation of `mHat P s t` under that iso enter as **explicit
hypotheses** of the bridge theorem, matching Mathlib's idiom for cross-API
bridge lemmas (supply the bridging iso at the call site rather than hiding it
as a field of `SystemApparatusSetup`).

The trace-inner identity `Tr(|φ⟩⟨φ| · M) = ⟨φ, Mφ⟩` is the core algebraic
content; it generalises LF2's `born_quadratic` to arbitrary effects via
`Matrix.dotProduct_mulVec` and `dotProduct_comm` (paper §5.14, spec §9.7).
-/

@[expose] public section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix

namespace CSD
namespace LF3

variable {K_A K_B H_SA : Type*}
  [NormedAddCommGroup K_A] [InnerProductSpace ℂ K_A] [FiniteDimensional ℂ K_A]
  [NormedAddCommGroup K_B] [InnerProductSpace ℂ K_B] [FiniteDimensional ℂ K_B]
  [NormedAddCommGroup H_SA] [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA]
  {S : SystemApparatusSetup K_A K_B H_SA}

/-- Basis isomorphism from the abstract `H_SA` to a concrete finite-dim
    Euclidean space, used to translate operators on `H_SA` into matrices for
    the LF2 Born-form interface. -/
abbrev BasisIso (H_SA : Type*) [NormedAddCommGroup H_SA]
    [InnerProductSpace ℂ H_SA] [FiniteDimensional ℂ H_SA] (N : ℕ) : Type _ :=
  H_SA ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N)

/-- Interpret a unit vector `Ψ : EuclideanSpace ℂ (Fin N)` as an LF2
    `DensityOperator N` via its rank-1 outer product `|Ψ⟩⟨Ψ|`. -/
noncomputable def rankOneStateOfΨ {N : ℕ}
    (Ψ : EuclideanSpace ℂ (Fin N)) (hΨ : ‖Ψ‖ = 1) :
    CSD.LF2.DensityOperator N :=
  CSD.LF2.rankOneDensity Ψ hΨ

/-- Interpret an `N × N` matrix `M` satisfying the effect axioms as an LF2
    `Effect N`. -/
noncomputable def effectOfM {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ)
    (h1 : M.IsHermitian) (h2 : M.PosSemidef) (h3 : (1 - M).PosSemidef) :
    CSD.LF2.Effect N :=
  ⟨M, h1, h2, h3⟩

/-! ### Trace-inner core identity (paper §5.14) -/

/-- `Tr(|φ⟩⟨φ| · M) = ⟨φ, Mφ⟩`. The generalised Born trace identity for an
    arbitrary effect matrix `M` and a vector `φ`. Composes `vecMulVec_mul`,
    `trace_vecMulVec`, the EuclideanSpace inner-product formula, and
    `dotProduct_mulVec` plus `dotProduct_comm`. -/
lemma trace_outerProduct_mul_eq_inner {N : ℕ}
    (φ : EuclideanSpace ℂ (Fin N)) (M : Matrix (Fin N) (Fin N) ℂ) :
    ((CSD.LF2.outerProduct φ) * M).trace
      = inner ℂ φ ((Matrix.toEuclideanLin M) φ) := by
  unfold CSD.LF2.outerProduct
  rw [Matrix.vecMulVec_mul, Matrix.trace_vecMulVec]
  -- LHS: (fun i => φ i) ⬝ᵥ ((fun i => star (φ i)) ᵥ* M)
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin]
  -- RHS: M *ᵥ ofLp φ ⬝ᵥ star (ofLp φ)
  -- (ofLp φ) i = φ i  (η-definitional on EuclideanSpace = WithLp 2 (Fin N → ℂ))
  show (φ.ofLp) ⬝ᵥ ((fun i => star (φ.ofLp i)) ᵥ* M)
      = (M *ᵥ φ.ofLp) ⬝ᵥ star (φ.ofLp)
  rw [dotProduct_comm φ.ofLp]
  rw [← dotProduct_mulVec]
  rw [dotProduct_comm]
  rfl

/-! ### Bridge theorem (paper §5.14 / spec §9.7) -/

/-- LF3 ↔ LF2 bridge. Given a basis isomorphism `basisIso` and a matrix `M`
    representing `mHat P s t` under that iso (i.e. `M` is the matrix of the
    pointer-sector projector in the chosen basis, plus standard effect
    properties), the operator-form sector volume equals the LF2 Born-form
    trace pairing of the rank-1 density `|basisIso Ψ⟩⟨basisIso Ψ|` with the
    effect `M`. -/
theorem sectorVolume_eq_LF2_Born
    {N : ℕ} (P : ProjectorAlgebra S) (s t : Sign)
    (basisIso : BasisIso H_SA N)
    (Ψ : H_SA) (hΨ : ‖Ψ‖ = 1)
    (M : Matrix (Fin N) (Fin N) ℂ)
    (hM_eq : ∀ x : H_SA,
      basisIso (mHat P s t x) = (Matrix.toEuclideanLin M) (basisIso x))
    (hM1 : M.IsHermitian) (hM2 : M.PosSemidef)
    (hM3 : (1 - M).PosSemidef) :
    sectorVolume P Ψ s t
      = CSD.LF2.traceForm
          (rankOneStateOfΨ (basisIso Ψ)
            (by rw [LinearIsometryEquiv.norm_map]; exact hΨ))
          (effectOfM M hM1 hM2 hM3) := by
  unfold sectorVolume CSD.LF2.traceForm rankOneStateOfΨ effectOfM
  -- LHS: re ⟨Ψ, mHat P s t Ψ⟩
  -- RHS: re ((rankOneDensity (basisIso Ψ) _).M * M).trace
  --    = re (outerProduct (basisIso Ψ) * M).trace
  rw [show inner ℂ Ψ (mHat P s t Ψ)
        = inner ℂ (basisIso Ψ) (basisIso (mHat P s t Ψ))
       from (LinearIsometryEquiv.inner_map_map basisIso Ψ (mHat P s t Ψ)).symm]
  rw [hM_eq Ψ]
  -- LHS: re ⟨basisIso Ψ, (toEuclideanLin M) (basisIso Ψ)⟩
  congr 1
  show inner ℂ (basisIso Ψ) ((Matrix.toEuclideanLin M) (basisIso Ψ))
       = ((CSD.LF2.rankOneDensity (basisIso Ψ) _).M * M).trace
  unfold CSD.LF2.rankOneDensity
  exact (trace_outerProduct_mul_eq_inner (basisIso Ψ) M).symm

end LF3
end CSD
