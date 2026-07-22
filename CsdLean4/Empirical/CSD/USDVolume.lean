/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF4.POVMNaimark
public import CsdLean4.LF4.BornRegionUncond
public import CsdLean4.LF2.EffectAux
public import CsdLean4.Empirical.QM.USD

/-!
# Empirical/CSD: the USD (unambiguous-discrimination) POVM and its Born weights as Kähler volumes

**Category:** 3-Local (CSD-ontic layer; the second *non-projective* (POVM) entry in
the volume-frequency series, after the trine).

The **unambiguous state discrimination** POVM (Ivanovic–Dieks–Peres) is the canonical
"why POVMs are needed" measurement: it distinguishes two non-orthogonal pure states
`ψ₁, ψ₂` (overlap `s = ⟨ψ₁,ψ₂⟩ ∈ [0,1)`) with **zero error** at the cost of an
inconclusive outcome. The three effects are
`E₁ = a|ψ₂^⊥⟩⟨ψ₂^⊥|`, `E₂ = a|ψ₁^⊥⟩⟨ψ₁^⊥|`, `E? = |χ?⟩⟨χ?|` with `a = 1/(1+s)`;
the full `usdPOVM : POVM 2 (Fin 3)` (states + unambiguity + success + completeness)
is built in `Empirical/QM/USD.lean`.

This file:
- gives the closed-form conclusive Born weights
  `p₁(ψ) = a‖⟨ψ, ψ₂^⊥⟩‖²`, `p₂(ψ) = a‖⟨ψ, ψ₁^⊥⟩‖²`;
- runs the POVM through the tranche: `canonicalNaimark (usdPOVM …)` is the dilation,
  and `usd_born_frequency_volume` lands the three USD outcome frequencies as
  **Fubini–Study volumes** on the dilated ontic `Σ' = ℂℙ⁵` — carving-free, Gleason-free.

Like the trine, the volume reading is the general POVM capstone instantiated at a
concrete non-projective measurement; it routes through the hpos-free engine
(`povm_born_frequency_volume_uncond`, `LF4/BornRegionUncond.lean`), so no genericity
hypothesis on the dilated state is carried (2026-06-11 migration).
-/

@[expose] public section

open Matrix MeasureTheory Matrix.UnitaryGroup ProbabilityTheory Filter
open scoped Kronecker MatrixOrder ComplexOrder LinearAlgebra.Projectivization

namespace CSD
namespace Empirical
namespace CSDBridge
namespace USDVolume

open CSD.LF2 CSD.LF4 CSD.Empirical.QM.USD

variable (s : ℝ)

/-! ### The conclusive Born weights -/

/-- **Closed-form conclusive weight (outcome 1):** `p₁(ψ) = a‖⟨ψ, ψ₂^⊥⟩‖²`. -/
theorem usd_weight_e1 (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : ‖ψ‖ = 1) :
    (usdPOVM s hs0 hs1).weight ψ 0 = usdA s * ‖inner ℂ ψ (psi2perp s)‖ ^ 2 := by
  show RCLike.re (inner ℂ ψ (Matrix.toEuclideanLin ((usdPOVM s hs0 hs1).E 0).M ψ)) = _
  rw [show (usdPOVM s hs0 hs1).E 0 = E1 s hs0 hs1 from rfl, E1, scaledRankOneEffect_M]
  exact scaledRankOne_quadratic (usdA s) (psi2perp s) ψ (psi2perp_norm s hs1 (by linarith)) hψ

/-- **Closed-form conclusive weight (outcome 2):** `p₂(ψ) = a‖⟨ψ, ψ₁^⊥⟩‖²`. -/
theorem usd_weight_e2 (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ψ : EuclideanSpace ℂ (Fin 2)) (hψ : ‖ψ‖ = 1) :
    (usdPOVM s hs0 hs1).weight ψ 1 = usdA s * ‖inner ℂ ψ psi1perp‖ ^ 2 := by
  show RCLike.re (inner ℂ ψ (Matrix.toEuclideanLin ((usdPOVM s hs0 hs1).E 1).M ψ)) = _
  rw [show (usdPOVM s hs0 hs1).E 1 = E2 s hs0 from rfl, E2, scaledRankOneEffect_M]
  exact scaledRankOne_quadratic (usdA s) psi1perp ψ psi1perp_norm hψ

/-! ### The USD POVM Born weights as Kähler volumes -/

/-- The canonical Naimark dilation of the USD POVM (it exists, like every POVM's). -/
noncomputable def usdNaimark (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    NaimarkDilation (usdPOVM s hs0 hs1) := canonicalNaimark (usdPOVM s hs0 hs1)

/-- **The USD POVM Born weights as Kähler volumes (the capstone).** Instantiating
`povm_born_frequency_volume_uncond` at the unambiguous-discrimination POVM: i.i.d.
Fubini–Study trials on the dilated ontic `Σ' = ℂℙ⁵` have the `k`-th USD outcome's
empirical frequency converge, on a single almost-sure event, to the USD Born weight
`pₖ(ψ) = ⟨ψ, Eₖ ψ⟩` (the two conclusive weights `a‖⟨ψₖ^⊥, ψ⟩‖²` and the inconclusive
weight) — realised as a sum of Fubini–Study volumes of the dilated barycentric cells.
The **second non-projective (POVM) entry in the volume-frequency series**, after the
trine; carving-free, Gleason-free, and (since the 2026-06-11 hpos migration) with no
genericity hypothesis on the dilated state — notably, `ψ = ψ₁` or `ψ₂` (a conclusive
weight exactly zero, the unambiguity case itself) is covered. -/
theorem usd_born_frequency_volume (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ψ : EuclideanSpace ℂ (Fin 2)) (e : (Fin 2 × Fin 3) ≃ Fin 6)
    (ψ' : EuclideanSpace ℂ (Fin 6))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
      (Matrix.toEuclideanLin (usdNaimark s hs0 hs1).V ψ))
    (hψ'0 : ψ' ≠ 0) (hnorm : ‖ψ'‖ = 1)
    (p₀ : CPN 6) {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN 6) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ j : Fin 6,
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ' hψ'0 j) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ k : Fin 3,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin 2,
            (∑ l ∈ Finset.range m,
                Set.indicator ((X l) ⁻¹' bornRegion ψ' hψ'0 (e (n, k))) (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds ((usdPOVM s hs0 hs1).weight ψ k)) :=
  povm_born_frequency_volume_uncond (usdPOVM s hs0 hs1) (usdNaimark s hs0 hs1) ψ e ψ'
    hψ'eq hψ'0 hnorm p₀ X hX hlaw hindep

end USDVolume
end CSDBridge
end Empirical
end CSD
