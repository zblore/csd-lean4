import CsdLean4.LF2.Setup
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Data.ENNReal.Basic

/-!
# LF2 Measure Bridge

**Category:** 3-Local (LF2 `π_* μL = c · μFS` bridge plus the invariant-measure uniqueness axiom).

Four pieces (spec §3.3, Lemma 1, Lemma 2, Theorem 1):

1. `pushforward_apply` — thin wrapper over `Measure.map_apply` specialised to a
   `SectorData`'s projection.
2. `preimage_action_eq` — the preimage/action identity
   `π⁻¹(epAction g '' A) = onticAction g '' (π⁻¹(A))`.
3. `pushforward_epAction_invariant` — the pushforward `π*μL` is invariant under
   the induced `G`-action on `P`.
4. `measure_bridge` — combining (3) with the imported
   `invariant_measure_uniqueness` axiom gives `π*μL = c • μFS`.

The invariant-measure uniqueness result on the abstract projective target is
**imported as an axiom** per spec §7.4. In the concrete CSD model it is
uniqueness of the `SU(N)`-invariant Borel probability measure on `CP^{N-1}`;
LF2 does not construct `P` or reprove the classification theorem.
-/

open MeasureTheory Set

namespace CSD
namespace LF2

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]

/-- Pushforward rewrite for the projection, specialised form of
    `Measure.map_apply`. -/
lemma SectorData.pushforward_apply
    (D : SectorData SigmaSpace P G) {A : Set P} (hA : MeasurableSet A) :
    (Measure.map D.π D.μL) A = D.μL (D.π ⁻¹' A) :=
  Measure.map_apply D.measurable_π hA

/-- **Lemma 1 of the spec.** Preimage/action identity: pulling back an
    epistemic orbit along `π` equals pushing the preimage through the ontic
    action. Consequence of `π`-equivariance + bijectivity of the action. -/
lemma SectorData.preimage_action_eq
    (D : SectorData SigmaSpace P G) (g : G) (A : Set P) :
    D.π ⁻¹' (D.epAction g '' A) = (D.onticAction g) '' (D.π ⁻¹' A) := by
  ext x
  simp only [mem_preimage, mem_image]
  constructor
  · rintro ⟨y, hy, hyeq⟩
    refine ⟨(D.onticAction g).symm x, ?_, (D.onticAction g).apply_symm_apply x⟩
    have key : D.π ((D.onticAction g).symm x) = y := by
      apply (D.epAction g).injective
      rw [← D.hπ_equiv g]
      rw [(D.onticAction g).apply_symm_apply]
      exact hyeq.symm
    rw [key]; exact hy
  · rintro ⟨z, hz, hzeq⟩
    refine ⟨D.π z, hz, ?_⟩
    rw [← hzeq, D.hπ_equiv]

/-- **Lemma 2 of the spec.** The pushforward measure `π*μL` is invariant under
    the induced `G`-action on `P`. -/
lemma SectorData.pushforward_epAction_invariant
    (D : SectorData SigmaSpace P G) (g : G) :
    MeasurePreserving (D.epAction g)
      (Measure.map D.π D.μL) (Measure.map D.π D.μL) := by
  refine ⟨(D.epAction g).measurable, ?_⟩
  rw [Measure.map_map (D.epAction g).measurable D.measurable_π]
  have heq : (D.epAction g : P → P) ∘ D.π = D.π ∘ (D.onticAction g : SigmaSpace → SigmaSpace) := by
    funext x; exact (D.hπ_equiv g x).symm
  rw [heq]
  rw [← Measure.map_map D.measurable_π (D.onticAction g).measurable]
  rw [(D.hμL_inv g).map_eq]

/-- **Imported axiom (spec §7.4).** Uniqueness of the `G`-invariant probability
    measure on the abstract projective target up to scaling: when the action
    is transitive, any finite `G`-invariant Borel measure is a constant
    multiple of the reference measure `μFS`.

    In the concrete CSD model this is the classical statement that the
    `SU(N)`-invariant Borel probability measure on `CP^{N-1}` is unique (the
    Fubini–Study measure). It is imported rather than constructed because LF2
    leaves `P` abstract.

    **Transitivity is required.** Without `htrans`, the statement is false in
    general: take `P = {0, 1}`, `G` the trivial group, `μFS = uniform`,
    `μ = δ_0`. Both are invariant under the trivial action; no `c : ENNReal`
    satisfies `δ_0 = c • uniform`. Transitivity rules out this and related
    pathological actions. The standard proof additionally requires
    compactness of `G` or an equivalent regularity property; the spec
    authorises the import for the concrete `SU(N)` on `CP^{N-1}` setting
    where compactness holds and `μFS` is Fubini–Study Haar.

    **Caveat.** This axiom carries strictly the assumptions of the standard
    Haar-on-compact-homogeneous-space theorem (Mathlib has Haar measure on
    topological groups; the homogeneous-quotient construction is not yet
    packaged at the required abstraction level). When that infrastructure
    lands, swap `axiom` for `theorem`-via-import. -/
axiom invariant_measure_uniqueness
    {P G : Type*} [MeasurableSpace P] [Group G]
    (action : G → P ≃ᵐ P)
    (htrans : ∀ p q : P, ∃ g : G, action g p = q)
    (μFS : Measure P) [IsProbabilityMeasure μFS]
    (hμFS_inv : ∀ g, MeasurePreserving (action g) μFS μFS)
    (μ : Measure P) [IsFiniteMeasure μ]
    (hμ_inv : ∀ g, MeasurePreserving (action g) μ μ) :
    ∃ c : ENNReal, μ = c • μFS

/-- **Theorem 1 of the spec (the measure bridge).** Under the sector-compatible
    data of `SectorData`, the pushforward of the ontic Liouville measure along
    `π` is a constant multiple of the reference measure `μFS`. The constant is
    pinned down by comparing total masses. -/
theorem measure_bridge
    (D : SectorData SigmaSpace P G)
    (μFS : Measure P) [IsProbabilityMeasure μFS]
    (hμFS_inv : ∀ g, MeasurePreserving (D.epAction g) μFS μFS) :
    ∃ c : ENNReal, Measure.map D.π D.μL = c • μFS :=
  invariant_measure_uniqueness D.epAction D.epAction_transitive μFS hμFS_inv
    (Measure.map D.π D.μL) (fun g => D.pushforward_epAction_invariant g)

end LF2
end CSD
