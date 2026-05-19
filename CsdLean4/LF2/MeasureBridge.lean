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
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

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
    D.π ⁻¹' ((g • ·) '' A) = ((g • ·) : SigmaSpace → SigmaSpace) '' (D.π ⁻¹' A) := by
  ext x
  simp only [mem_preimage, mem_image]
  constructor
  · rintro ⟨y, hy, hyeq⟩
    -- π x = g • y. So g⁻¹ • π x = y. By equivariance, π (g⁻¹ • x) = g⁻¹ • π x = y.
    refine ⟨g⁻¹ • x, ?_, smul_inv_smul g x⟩
    rw [D.hπ_equiv, hyeq.symm, inv_smul_smul]; exact hy
  · rintro ⟨z, hz, hzeq⟩
    -- z ∈ π⁻¹ A, x = g • z. Then π x = π (g • z) = g • π z by equivariance.
    refine ⟨D.π z, hz, ?_⟩
    rw [← hzeq, D.hπ_equiv]

/-- **Lemma 2 of the spec.** The pushforward measure `π*μL` is invariant under
    the induced `G`-action on `P`. -/
lemma SectorData.pushforward_epAction_invariant
    (D : SectorData SigmaSpace P G) (g : G) :
    MeasurePreserving ((g • ·) : P → P)
      (Measure.map D.π D.μL) (Measure.map D.π D.μL) := by
  refine ⟨D.measurable_smul_P g, ?_⟩
  rw [Measure.map_map (D.measurable_smul_P g) D.measurable_π]
  have heq : ((g • ·) : P → P) ∘ D.π = D.π ∘ ((g • ·) : SigmaSpace → SigmaSpace) := by
    funext x; exact (D.hπ_equiv g x).symm
  rw [heq]
  rw [← Measure.map_map D.measurable_π (D.measurable_smul_σ g)]
  rw [(D.hμL_inv g).map_eq]

/-- **Imported axiom (spec §7.4).** Uniqueness of the `G`-invariant probability
    measure on the abstract projective target up to scaling: when the action
    is transitive, any finite `G`-invariant Borel measure is a constant
    multiple of the reference measure `μFS`.

    In the concrete CSD model this is the classical statement that the
    `SU(N)`-invariant Borel probability measure on `CP^{N-1}` is unique (the
    Fubini–Study measure). It is imported rather than constructed because LF2
    leaves `P` abstract.

    ## Hypotheses the axiom *should* carry but currently does not

    The intended theorem is the standard Haar-on-compact-homogeneous-space
    classification, which additionally requires:

    - `G` is a topological group, with a compatible measurable structure;
    - `G` is **compact** (the source of measure uniqueness — without
      compactness, non-compact unimodular cases need a different proof);
    - The action `G × P → P` is **continuous** (or at least Borel
      measurable jointly);
    - `μFS` is an **inner-regular Borel probability measure** on a
      Hausdorff `P` (or, equivalently, a Radon measure);
    - `μ` is similarly Borel regular and inner regular.

    None of these hypotheses are encoded in the axiom signature below.
    The axiom as stated is therefore **stronger than the classical
    theorem it is meant to import**: a hostile interpretation in an
    abstract `(P, G)` setting without the above structure could in
    principle render the statement inconsistent.

    ## Transitivity is required

    Without `IsPretransitive`, the statement is false even in the
    intended (compact group + Haar) setting: take `P = {0, 1}`, `G` the
    trivial group, `μFS = uniform`, `μ = δ_0`. Both are invariant under
    the trivial action; no `c : ENNReal` satisfies `δ_0 = c • uniform`.
    Transitivity rules out this and related pathological actions.

    ## LF4 discharge plan

    LF4 instantiates `SectorData` with concrete `P := ℙ ℂ (Fin N → ℂ)`
    (or a Kähler manifold variant), `G := SU(N)`, both with their
    natural topology, and `μFS := Fubini–Study`. At that point:

    - `[CompactSpace G]`, `[TopologicalSpace P]`, `[ContinuousSMul G P]`,
      `[BorelSpace P]`, `[IsHaarMeasure μFS]` all become available.
    - The classical theorem applies (Mathlib has Haar measure on
      topological groups; the homogeneous-quotient construction is
      partially available via `Mathlib.MeasureTheory.Measure.Haar.*`).
    - Swap `axiom` for `theorem`-via-import; thread the new typeclass
      instances through `SectorData` so `MeasureBridgeData.ofSectorData`
      callers acquire them by signature.

    Until then, this axiom is **a documented spec-level import** rather
    than a Mathlib-derived theorem. The honest reading: the LF2 chain
    is conditional on the LF4 instantiation supplying the hypotheses
    needed to make this a theorem. -/
axiom invariant_measure_uniqueness
    {P G : Type*} [MeasurableSpace P] [Group G]
    [MulAction G P] [MulAction.IsPretransitive G P]
    (μFS : Measure P) [IsProbabilityMeasure μFS]
    (hμFS_inv : ∀ g : G, MeasurePreserving ((g • ·) : P → P) μFS μFS)
    (μ : Measure P) [IsFiniteMeasure μ]
    (hμ_inv : ∀ g : G, MeasurePreserving ((g • ·) : P → P) μ μ) :
    ∃ c : ENNReal, μ = c • μFS

/-- **Theorem 1 of the spec (the measure bridge).** Under the sector-compatible
    data of `SectorData`, the pushforward of the ontic Liouville measure along
    `π` is a constant multiple of the reference measure `μFS`. The theorem
    only asserts existence of the scaling constant `c`; computing or pinning
    down `c = D.μL Set.univ` (the obvious comparison of total masses) is a
    separate step not in scope of v1.00 and not required by LF3 consumers. -/
theorem measure_bridge
    (D : SectorData SigmaSpace P G)
    (μFS : Measure P) [IsProbabilityMeasure μFS]
    (hμFS_inv : ∀ g : G, MeasurePreserving ((g • ·) : P → P) μFS μFS) :
    ∃ c : ENNReal, Measure.map D.π D.μL = c • μFS :=
  invariant_measure_uniqueness μFS hμFS_inv
    (Measure.map D.π D.μL) (fun g => D.pushforward_epAction_invariant g)

end LF2
end CSD
