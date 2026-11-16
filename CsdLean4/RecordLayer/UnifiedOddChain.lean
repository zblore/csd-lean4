/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.RecordLayer.DiracSegment
public import CsdLean4.RecordLayer.UnifiedOddWall

/-!
# The mirror-odd sector is a chain with hard ends

**Category:** 7-SigmaLayer (the record layer). BACKLOG #416 — milestone **M6** of the author's
programme "From `Σ` to physical spacetime", obligation UO-16; Task 3 of the research delivery
plan of 2026-11-16: the wall as a property of the energy. No new assumption; it verifies the
boundary condition that UA-18 (a) chose.

UA-18 (a) takes the walled chain to be the mirror-odd sector of the ring and says that the
upper component vanishes at each wall and that the end hop is `√2` times the bulk hop.
#407 to #415 work in that sector without showing that it is a chain. #275
(`RecordLayer/DiracSegment.lean`) wrote the mirror-*even* sector out as a segment with an
explicit energy `segHam`. Exchanging the two spinor components turns the odd sector at rest
energy `μ` into the even sector at rest energy `−μ`. This module makes that exchange and so
carries #275's results to the odd sector.

* `compSwap`, `compSwap_compSwap`, `compSwapₗ`, `compSwap_neg`,
  ★ `chainParity_compSwap` — the exchange turns mirror-odd into mirror-even;
* ★ `diracHam_mulVec_compSwap`, `compSwap_pow_mulVec`, ★ `compSwap_chainProp_mulVec` — it
  carries the energy and the evolution at `μ` to those at `−μ`;
* `chainInner_compSwap`, `regionWeight_compSwap`;
* `IsOddState`, `IsOddState.isEvenState_compSwap`, `IsOddState.diracHam_mulVec`,
  `isOddState_oddWall`;
* `oddSegOf` — the map of the odd sector onto the segment `{0, …, M} × Fin 2`;
* ★★ `chainInner_eq_segInner_oddSegOf` — it is an isometry on the odd sector;
* ★★ `oddSegOf_end` — the image has no second component at the two ends (in the ring's
  labelling: no upper component at the walls);
* ★★★ `oddSegOf_diracHam_mulVec` — it intertwines the ring's energy with the segment's:
  `S H(μ) φ = H_seg(−μ) S φ`;
* ★★★ `odd_sector_chain_flow_equiv` — and the evolutions:
  `S e^{−itH(μ)} φ = e^{−itH_seg(−μ)} S φ`;
* `chainInner_mulVec_hermitian`, ★★ `oddSeg_generator_symm` — the segment's energy is
  symmetric on the image of the odd sector;
* ★★ `regionWeight_eq_segRegionWeight_oddSegOf` — a mirror-symmetric region's weight is the
  weight of its trace on the segment;
* ★★ `oddSegOf_oddWall_flow` — the wall state of #407 at the packet time `s` is the
  segment's evolution of the wall state at `0`.

## Exact scope

* **The segment's energy is #275's `segHam`, at rest energy `−μ`, in exchanged components.**
  It is the lattice hop times `σ_x` and the rest energy times `σ_z` on `{0, …, M}`, with one
  component absent at both ends and the two end edges carrying `√2`. Exchanging the
  components back gives the same chain with rest energy `+μ` and the *upper* component
  absent at the ends. That last sentence is a relabelling; the theorems are stated in the
  exchanged labelling.
* **UA-18 (a)'s boundary condition is confirmed**: the upper component vanishes at the walls
  (`odd_apply_eq_zero` of #407, `oddSegOf_end` here) and the end hop is `√2` (`segHop` of
  #275). Nothing downstream needs correcting.
* **A ring of `2M` sites, `M ≥ 2`**, as #275. The modules #407 to #415 are stated for a ring
  of `M + 1` sites; they apply here when that number is even.
* **One Dirac carrier.** The two-level clock (`deviceHam`, a block per level) is not
  restated on the segment; each of its blocks is covered by these theorems.
* **Symmetric on the image, not Hermitian as a matrix.** `oddSeg_generator_symm` is the
  statement on the states the chain has. That `segHam` is a Hermitian matrix is not proved
  here or in #275.
* **Uncoupled.** The gates and pointers are not carried to the segment.

## References

`specs/future-work.md` (records to spacetime); `specs/unified-record-spacetime-plan.md`
(UA-8, UA-18, UO-16, UD-173, UD-186); `specs/unified-m6-feasibility.md` (§6, item 6);
`RecordLayer/DiracSegment.lean` (#275: `segOf`, `segHam`, `segProp`, `IsEvenState`,
`chainInner_eq_segInner`, `segOf_diracHam_mulVec`, `segOf_chainProp_mulVec`,
`regionWeight_eq_segRegionWeight`, `IsEvenState.end_one`); `RecordLayer/UnifiedOddWall.lean`
(#407: `oddWall`, `chainParity_oddWall`, `chainProp_oddWall`, `odd_apply_eq_zero`);
`RecordLayer/DiracReturn.lean` (#270: `chainParity`, `diracHam_mulVec_chainParity`);
`RecordLayer/DiracTiming.lean` (`diracHam_mulVec_apply`); `RecordLayer/DiracArrival.lean`
(`chainProp`, `regionWeight`).
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Complex CSD.CV CSD.SigmaLayer
open scoped Matrix NNReal

namespace CSD.RecordLayer

/-! ### Exchanging the two components -/

section Swap

variable {L : ℕ}

/-- **The exchange of the two spinor components.** -/
def compSwap (φ : ZMod L × Fin 2 → ℂ) : ZMod L × Fin 2 → ℂ := fun p => φ (p.1, 1 - p.2)

theorem compSwap_compSwap (φ : ZMod L × Fin 2 → ℂ) : compSwap (compSwap φ) = φ := by
  funext ⟨j, a⟩
  simp only [compSwap, sub_sub_cancel]

/-- The exchange, as a linear map. -/
def compSwapₗ : (ZMod L × Fin 2 → ℂ) →ₗ[ℂ] (ZMod L × Fin 2 → ℂ) where
  toFun := compSwap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem compSwapₗ_apply (φ : ZMod L × Fin 2 → ℂ) : compSwapₗ φ = compSwap φ := rfl

theorem compSwap_neg (φ : ZMod L × Fin 2 → ℂ) : compSwap (-φ) = -compSwap φ := rfl

/-- ★ **The exchange turns the mirror into minus the mirror.** -/
theorem chainParity_compSwap (φ : ZMod L × Fin 2 → ℂ) :
    chainParity (compSwap φ) = -compSwap (chainParity φ) := by
  funext ⟨j, a⟩
  fin_cases a <;> simp [chainParity, compSwap]

theorem regionWeight_compSwap (φ : ZMod L × Fin 2 → ℂ) (A : Finset (ZMod L)) :
    regionWeight (compSwap φ) A = regionWeight φ A := by
  simp only [regionWeight, siteWeight, compSwap, Fin.sum_univ_two]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [sub_zero, sub_self]
  ring

variable [NeZero L]

theorem chainInner_compSwap (φ ψ : ZMod L × Fin 2 → ℂ) :
    chainInner (compSwap φ) (compSwap ψ) = chainInner φ ψ := by
  simp only [chainInner, compSwap, Fintype.sum_prod_type, Fin.sum_univ_two]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [sub_zero, sub_self]
  ring

/-- ★ **The exchange carries the energy at `μ` to the energy at `−μ`.** -/
theorem diracHam_mulVec_compSwap (J μ : ℝ) (φ : ZMod L × Fin 2 → ℂ) :
    diracHam J (-μ) *ᵥ compSwap φ = compSwap (diracHam J μ *ᵥ φ) := by
  funext ⟨j, a⟩
  rw [diracHam_mulVec_apply]
  simp only [compSwap]
  rw [diracHam_mulVec_apply]
  fin_cases a <;> simp

theorem compSwap_pow_mulVec (J μ : ℝ) (φ : ZMod L × Fin 2 → ℂ) (n : ℕ) :
    compSwap (diracHam J μ ^ n *ᵥ φ) = diracHam J (-μ) ^ n *ᵥ compSwap φ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ← diracHam_mulVec_compSwap, ih, pow_succ',
      Matrix.mulVec_mulVec]

open scoped Matrix.Norms.L2Operator in
/-- ★ **The exchange carries the evolution at `μ` to the evolution at `−μ`.** -/
theorem compSwap_chainProp_mulVec (J μ t : ℝ) (φ : ZMod L × Fin 2 → ℂ) :
    compSwap (chainProp (L := L) J μ t *ᵥ φ) = chainProp J (-μ) t *ᵥ compSwap φ := by
  set c : ℂ := -(I * t)
  have hA := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c • diracHam (L := L) J μ)
  have hB := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c • diracHam (L := L) J (-μ))
  let LA : Matrix (ZMod L × Fin 2) (ZMod L × Fin 2) ℂ →ₗ[ℂ] (ZMod L × Fin 2 → ℂ) :=
    { toFun := fun A => compSwap (A *ᵥ φ)
      map_add' := fun A B => by rw [Matrix.add_mulVec]; rfl
      map_smul' := fun a A => by rw [Matrix.smul_mulVec]; rfl }
  let LB : Matrix (ZMod L × Fin 2) (ZMod L × Fin 2) ℂ →ₗ[ℂ] (ZMod L × Fin 2 → ℂ) :=
    { toFun := fun A => A *ᵥ compSwap φ
      map_add' := fun A B => Matrix.add_mulVec A B _
      map_smul' := fun a A => Matrix.smul_mulVec a A _ }
  have h1 := hA.mapL (LinearMap.toContinuousLinearMap LA)
  have h2 := hB.mapL (LinearMap.toContinuousLinearMap LB)
  have heq : (fun n => LinearMap.toContinuousLinearMap LA
        (((n.factorial : ℂ)⁻¹) • (c • diracHam (L := L) J μ) ^ n))
      = fun n => LinearMap.toContinuousLinearMap LB
        (((n.factorial : ℂ)⁻¹) • (c • diracHam (L := L) J (-μ)) ^ n) := by
    funext n
    simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk, LA, LB,
      smul_pow, Matrix.smul_mulVec]
    rw [← compSwapₗ_apply, map_smul, map_smul, compSwapₗ_apply, compSwap_pow_mulVec]
  rw [heq] at h1
  exact h1.unique h2

/-- The inner product of a state with a Hermitian matrix applied to another. -/
theorem chainInner_mulVec_hermitian {A : Matrix (ZMod L × Fin 2) (ZMod L × Fin 2) ℂ}
    (hA : A.IsHermitian) (u v : ZMod L × Fin 2 → ℂ) :
    chainInner u (A *ᵥ v) = chainInner (A *ᵥ u) v := by
  simp only [chainInner, Matrix.mulVec, dotProduct, Finset.mul_sum, star_sum, star_mul',
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
  have h : star (A q p) = A p q := by
    have := congrFun (congrFun hA.eq p) q
    rwa [Matrix.conjTranspose_apply] at this
  rw [h]
  ring

/-- **The odd sector**: the states the mirror sends to their negative. -/
def IsOddState (φ : ZMod L × Fin 2 → ℂ) : Prop := chainParity φ = -φ

theorem IsOddState.diracHam_mulVec {φ : ZMod L × Fin 2 → ℂ} (hφ : IsOddState φ) (J μ : ℝ) :
    IsOddState (diracHam J μ *ᵥ φ) := by
  rw [IsOddState, ← diracHam_mulVec_chainParity, hφ, Matrix.mulVec_neg]

/-- The wall state of #407 is in the odd sector. -/
theorem isOddState_oddWall (c μ ℓ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (t : ℝ) :
    IsOddState (oddWall (L := L) c μ ℓ W β t) :=
  chainParity_oddWall c μ ℓ W β t

end Swap

/-! ### The odd sector on the segment -/

section Segment

variable {M : ℕ} [NeZero M]

omit [NeZero M] in
theorem IsOddState.isEvenState_compSwap {φ : ZMod (2 * M) × Fin 2 → ℂ} (hφ : IsOddState φ) :
    IsEvenState (compSwap φ) := by
  rw [IsEvenState, chainParity_compSwap, hφ, compSwap_neg, neg_neg]

/-- **The map of the odd sector onto the segment**: exchange the components, then #275's
map. -/
def oddSegOf (φ : ZMod (2 * M) × Fin 2 → ℂ) : Fin (M + 1) × Fin 2 → ℂ := segOf (compSwap φ)

/-- ★★ **The map is an isometry on the odd sector.** -/
theorem chainInner_eq_segInner_oddSegOf {φ ψ : ZMod (2 * M) × Fin 2 → ℂ} (hφ : IsOddState φ)
    (hψ : IsOddState ψ) : chainInner φ ψ = segInner (oddSegOf φ) (oddSegOf ψ) := by
  rw [oddSegOf, oddSegOf, ← chainInner_eq_segInner hφ.isEvenState_compSwap
    hψ.isEvenState_compSwap, chainInner_compSwap]

omit [NeZero M] in
/-- ★★ **The image has no second component at the two ends.** In the ring's labelling that
is the upper component, at the walls. -/
theorem oddSegOf_end {φ : ZMod (2 * M) × Fin 2 → ℂ} (hφ : IsOddState φ) {j : Fin (M + 1)}
    (hj : IsSegEnd j) : oddSegOf φ (j, 1) = 0 := by
  rw [oddSegOf, segOf, hφ.isEvenState_compSwap.end_one hj, mul_zero]

/-- ★★★ **The ring's energy on the odd sector is the segment's energy**:
`S H(μ) φ = H_seg(−μ) S φ`. -/
theorem oddSegOf_diracHam_mulVec (hM : 2 ≤ M) {φ : ZMod (2 * M) × Fin 2 → ℂ}
    (hφ : IsOddState φ) (J μ : ℝ) :
    oddSegOf (diracHam J μ *ᵥ φ) = segHam J (-μ) *ᵥ oddSegOf φ := by
  rw [oddSegOf, oddSegOf, ← diracHam_mulVec_compSwap,
    segOf_diracHam_mulVec hM hφ.isEvenState_compSwap]

/-- ★★★ **The mirror-odd sector of the ring is the chain with hard ends, as a flow**:
`S e^{−itH(μ)} φ = e^{−itH_seg(−μ)} S φ` for every mirror-odd `φ`. -/
theorem odd_sector_chain_flow_equiv (hM : 2 ≤ M) {φ : ZMod (2 * M) × Fin 2 → ℂ}
    (hφ : IsOddState φ) (J μ t : ℝ) :
    oddSegOf (chainProp (L := 2 * M) J μ t *ᵥ φ) = segProp J (-μ) t *ᵥ oddSegOf φ := by
  rw [oddSegOf, oddSegOf, compSwap_chainProp_mulVec,
    segOf_chainProp_mulVec hM hφ.isEvenState_compSwap]

/-- ★★ **The segment's energy is symmetric on the image of the odd sector.** -/
theorem oddSeg_generator_symm (hM : 2 ≤ M) {φ ψ : ZMod (2 * M) × Fin 2 → ℂ}
    (hφ : IsOddState φ) (hψ : IsOddState ψ) (J μ : ℝ) :
    segInner (oddSegOf φ) (segHam J (-μ) *ᵥ oddSegOf ψ)
      = segInner (segHam J (-μ) *ᵥ oddSegOf φ) (oddSegOf ψ) := by
  rw [← oddSegOf_diracHam_mulVec hM hψ, ← oddSegOf_diracHam_mulVec hM hφ,
    ← chainInner_eq_segInner_oddSegOf hφ (hψ.diracHam_mulVec J μ),
    ← chainInner_eq_segInner_oddSegOf (hφ.diracHam_mulVec J μ) hψ]
  exact chainInner_mulVec_hermitian (diracHam_isHermitian J μ) φ ψ

/-- ★★ **A mirror-symmetric region's weight is the weight of its trace on the segment.** -/
theorem regionWeight_eq_segRegionWeight_oddSegOf {φ : ZMod (2 * M) × Fin 2 → ℂ}
    (hφ : IsOddState φ) {A : Finset (ZMod (2 * M))} (hA : ∀ k, -k ∈ A ↔ k ∈ A) :
    regionWeight φ A
      = segRegionWeight (oddSegOf φ) (Finset.univ.filter fun j => segSite j ∈ A) := by
  rw [oddSegOf, ← regionWeight_eq_segRegionWeight hφ.isEvenState_compSwap hA,
    regionWeight_compSwap]

/-- ★★ **The wall state on the segment.** The wall state of #407 at the packet time `s` is
the segment's evolution, through the flow time `s`, of the wall state at `0`. -/
theorem oddSegOf_oddWall_flow (hM : 2 ≤ M) (c μ ℓ : ℝ) (W : Finset ℤ) (β : ℤ → ℂ) (s : ℝ) :
    oddSegOf (oddWall (L := 2 * M) c μ ℓ W β s)
      = segProp (scaledHop c (ℓ / (2 * M : ℕ))) (-μ) s
        *ᵥ oddSegOf (oddWall (L := 2 * M) c μ ℓ W β 0) := by
  rw [← odd_sector_chain_flow_equiv hM (isOddState_oddWall c μ ℓ W β 0), chainProp_oddWall]

end Segment

end CSD.RecordLayer

end
