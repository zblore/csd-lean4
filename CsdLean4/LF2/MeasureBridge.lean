import CsdLean4.LF2.Setup
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Data.ENNReal.Basic

/-!
# LF2 Measure Bridge

**Category:** 3-Local (LF2 `π_* μL = c · μFS` bridge ingredients).

Three pieces (spec §3.3, Lemma 1, Lemma 2):

1. `pushforward_apply` — thin wrapper over `Measure.map_apply` specialised to a
   `SectorData`'s projection.
2. `preimage_action_eq` — the preimage/action identity
   `π⁻¹((g • ·) '' A) = (g • ·) '' (π⁻¹(A))` (the `MulAction` form; the earlier
   `epAction`/`onticAction` named maps were removed in the `MulAction` migration).
3. `pushforward_epAction_invariant` — the pushforward `π*μL` is invariant under
   the induced `G`-action on `P`.

The measure bridge `π*μL = c • μFS` (spec Theorem 1) follows from (3) plus
uniqueness of the `G`-invariant measure. On the concrete instances the bridge
holds **axiom-free** (`CSD.LF4.cp_measure_bridge`, `k_measure_bridge` — `c = 1`,
trivial / product-marginal fibres). The earlier abstract over-general statement
`measure_bridge` and the imported `invariant_measure_uniqueness` axiom it required
were **removed (2026-06-04)**: nothing downstream used the abstract version, and
the concrete `CP^{N-1}` uniqueness it would have needed is itself a proved,
axiom-free theorem in the tree (`Matrix.UnitaryGroup.invariant_measure_uniqueness_cpn`).
The corpus's only remaining imported axiom is `busch_effect_gleason`.
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


end LF2
end CSD
