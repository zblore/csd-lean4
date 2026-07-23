/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF5.FlowBornFrequency
public import CsdLean4.LF6.GHZContextuality

/-!
# LF6-C.2: the GHZ de-isolation flow

**Category:** 6-Local (the dynamical realisation of the multipartite entangled
de-isolation tier; the D1 entangled frontier at the three-party GHZ).

This is **LF6-C.2** of `specs/lf6-plan.md`: an actual deterministic,
Fubini-Study-measure-preserving de-isolation flow `Phi != id` on the dilated
three-qubit projective ontic space whose context-fixed pointer-block volumes are
the GHZ Born weights, with a.s. pointer-block frequencies converging to them. It
is the dynamical counterpart of the deterministic forced-contextuality no-go
LF6-C.1 (`GHZContextuality.lean`), mirroring the singlet's LF6-A.2
(`SingletDeisolationFlow.lean`) at three parties.

## The construction (reusing LF5 @ N = 8)

The three-qubit register `ℂ⁸ ≅ ℂ² ⊗ ℂ² ⊗ ℂ²` is measured by the LF5 von Neumann
de-isolation flow `measurementFlow 8 e` on the dilated projective ontic space
`Σ' = ℂℙ^{63} = ℙ(EuclideanSpace ℂ (Fin 64))` (`64 = 8·8 = 63 + 1`). The flow is
inherited wholesale from LF5-B at `N = 8`; it is genuinely `Phi != id`
(`1 < 8`) and Fubini-Study measure-preserving.

The prepared state is the GHZ state itself, reindexed to the computational
`Fin 8` basis (`nudgedGHZ = ghzState ∘ ghzIdx.symm`). Then the headline:

```
pointer-block w FS volume  =  ‖⟨e_{ghzIdx w}, nudgedGHZ⟩‖²   -- LF5 vnDilation_pointer_volume @ N=8
                           =  ‖ghzState w‖²                    -- reindex coordinate identity
                           =  ghzWeight w                      -- computed GHZ Born weight (1/2 or 0)
```

so the reproduction is LF5@N=8 + a coordinate (reindex-isometry) step + the
computed GHZ Born weights. The Born = FS-volume identity is **imported** through
`vnDilation_pointer_volume` (derived one layer down by the moment-map /
Duistermaat-Heckman cluster, `fs_born_volume_ratio_N`, Gleason-free, no Born put
in); this file does not re-derive it. What is exercised is the measurement
**dynamics** (`Phi != id`).

## Which carve this builds (honest)

This is the **minimal computational-basis carve**: the pointer blocks are the
eight computational outcomes, and the GHZ Born weights are the diagonal
`(1/2, 0, 0, 0, 0, 0, 0, 1/2)` (the `(0,0,0)` and `(1,1,1)` support). This carve
genuinely reuses the LF5 engine at `N = 8` and lands on the real GHZ diagonal
weights (not stubs), but it is a **diagonal** carve: the computational-basis
measurement is not a Mermin context, so its block-volume statistics do **not**
reproduce the four `<XXX> = +1`, `<XYY> = <YXY> = <YYX> = -1` Mermin
correlations that carry GHZ's contextuality.

The contextuality tie is therefore the **honest weaker** one:
`ghzDeisolation_contextuality_anchor` re-exports LF6-C.1
`no_product_partition_realises_ghz` (no product partition reproduces the four
GHZ perfect correlations, deterministic all-or-nothing), which is the no-go the
**Mermin-context** carve would route through. The Mermin-context carve itself —
the GHZ state in the X/Y measurement basis, whose block correlations reproduce
the perfect GHZ correlations and tie *dynamically* to C.1, mirroring the
singlet's `singletDeisolation_blockVolume_correlation` — is the deferred
increment (it needs the GHZ joint X/Y eigenstructure, the three-party analogue
of LF3's `singletJointEig`, which the corpus does not yet carry). We do **not**
claim the diagonal carve is the contextual one.

## Honest scope (the C.2 ledger)

- **Exhibited.** A genuine deterministic FS-measure-preserving de-isolation flow
  `Phi != id` (`ghzDeisolation_*`, inherited from LF5-B @ N=8), whose
  context-fixed `BornRegion` pointer-block volumes equal the GHZ Born weights
  (`ghzDeisolation_pointer_volume`) and whose a.s. block frequencies converge to
  them (`ghzDeisolation_frequency`).
- **Imported, not re-derived.** Born = FS-volume is the DH/moment-map cluster's,
  imported through `vnDilation_pointer_volume`. The GHZ state, its Born weights,
  and the contextuality no-go are `Empirical.GHZ` / LF6-C.1.
- **Realisation, not derivation.** The flow **realises** the GHZ measurement
  dynamically; it does not derive the weights from independent dynamics. The
  carve is the joint moment subdivision, never a setting-local product region.
- **Deferred (the genuine increment).** The Mermin-context carve whose block
  correlations reproduce the four GHZ perfect correlations and tie dynamically
  to C.1 (the three-party analogue of A.2's contextual block-correlation), and
  the local product flow `V = V_0 ⊗ V_1 ⊗ V_2` (A.3's analogue).
- **Residue: A5.** The GHZ entangled sector / preparation region is posited, not
  derived (SO-1: the sector origin, distinct from Paper C Axiom A5); the typicality law on `Σ'` is the Fubini-Study
  measure (A5).

All exports are foundational-triple-only (Gleason-free; the LF5 pointer engine
is off Busch, C.1 is measure-theoretic Mermin content).

Reference: `specs/lf6-plan.md` (LF6-C.2).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization

namespace CSD
namespace LF6

open CSD.LF5 CSD.LF4 CSD.LF2 CSD.Empirical.GHZ

/-! ### Index identification `Fin 2 × Fin 2 × Fin 2 ≃ Fin 8` -/

/-- The pointer-index identification `(i, j, k) ↦ Fin 8` tying the LF5 pointer
outcome at `N = 8` to the three-qubit computational basis. Only `ghzIdx.symm`
composed with `ghzIdx` (an identity) is consumed downstream, so its numeric
values are irrelevant. -/
def ghzIdx : Fin 2 × Fin 2 × Fin 2 ≃ Fin 8 :=
  ((Equiv.refl (Fin 2)).prodCongr finProdFinEquiv).trans finProdFinEquiv

/-! ### The GHZ Born weights -/

/-- **The computed GHZ Born weights.** The three-qubit GHZ state has support
exactly on the two all-equal computational indices `(0,0,0)` and `(1,1,1)`, each
with weight `1/2`; every off-support outcome has weight `0`. The predicate
`w.1 = w.2.1 ∧ w.2.1 = w.2.2` (all three indices equal) picks out precisely the
diagonal support. This is not a stub: `ghz_normSq_eq_weight` proves it equals
`‖ghzState w‖²`. -/
noncomputable def ghzWeight (w : Fin 2 × Fin 2 × Fin 2) : ℝ :=
  if w.1 = w.2.1 ∧ w.2.1 = w.2.2 then (2 : ℝ)⁻¹ else 0

/-- **The GHZ Born weights are the squared computational amplitudes.** For every
computational outcome `w`, `‖ghzState w‖² = ghzWeight w` — genuinely computed
from the eight basis evaluations of the GHZ state (`1/2` on `(0,0,0)`/`(1,1,1)`,
`0` elsewhere). -/
lemma ghz_normSq_eq_weight (w : Fin 2 × Fin 2 × Fin 2) :
    ‖ghzState w‖ ^ 2 = ghzWeight w := by
  obtain ⟨i, j, k⟩ := w
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [ghzWeight] <;>
    simp [ghzState, EuclideanSpace.single]

/-- The GHZ Born weights sum to `1` (the two support cells each `1/2`). -/
lemma sum_ghzWeight : ∑ w : Fin 2 × Fin 2 × Fin 2, ghzWeight w = 1 := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, ghzWeight]
  norm_num

/-! ### The nudged GHZ state (the prepared state) -/

/-- **The prepared state.** The GHZ state reindexed to the computational `Fin 8`
basis, `nudgedGHZ k = ghzState (ghzIdx.symm k)`. For the minimal
computational-basis carve there is no basis rotation (the "nudge" is the identity
context); the name mirrors A.2's `nudgedSinglet`. -/
noncomputable def nudgedGHZ : EuclideanSpace ℂ (Fin 8) :=
  WithLp.toLp 2 (fun k : Fin 8 => ghzState (ghzIdx.symm k))

/-- The pointer-cell coordinate of the nudged GHZ state is the GHZ amplitude. -/
lemma nudgedGHZ_coord (w : Fin 2 × Fin 2 × Fin 2) :
    (nudgedGHZ) (ghzIdx w) = ghzState w := by
  have h : ghzIdx.symm (ghzIdx w) = w := Equiv.symm_apply_apply ghzIdx w
  show ghzState (ghzIdx.symm (ghzIdx w)) = ghzState w
  rw [h]

/-- **The nudge coordinate-Born identity.** The squared computational amplitude
of the nudged GHZ state at the pointer cell `w` equals the GHZ Born weight
`ghzWeight w` — composing the coordinate identity with the computed weights
`ghz_normSq_eq_weight`. -/
lemma nudgedGHZ_born (w : Fin 2 × Fin 2 × Fin 2) :
    ‖inner ℂ (EuclideanSpace.single (ghzIdx w) (1 : ℂ)) (nudgedGHZ)‖ ^ 2
      = ghzWeight w := by
  rw [EuclideanSpace.inner_single_left, map_one, one_mul, nudgedGHZ_coord]
  exact ghz_normSq_eq_weight w

/-- The pointer-cell squared coordinate as a function of the outcome triple. -/
lemma nudgedGHZ_coord_normSq (w : Fin 2 × Fin 2 × Fin 2) :
    ‖(nudgedGHZ) (ghzIdx w)‖ ^ 2 = ghzWeight w := by
  rw [nudgedGHZ_coord]; exact ghz_normSq_eq_weight w

/-- **The nudged GHZ state is a unit preparation.** `‖φ‖² = ∑_w ghzWeight w = 1`.
Discharges the `hψ` hypothesis of the LF5 pointer-volume / frequency theorems. -/
theorem nudgedGHZ_norm : ‖nudgedGHZ‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ k : Fin 8, ‖(nudgedGHZ) k‖ ^ 2 = 1 := by
    calc ∑ k : Fin 8, ‖(nudgedGHZ) k‖ ^ 2
        = ∑ w : Fin 2 × Fin 2 × Fin 2, ‖(nudgedGHZ) (ghzIdx w)‖ ^ 2 :=
          (Equiv.sum_comp ghzIdx (fun k => ‖(nudgedGHZ) k‖ ^ 2)).symm
      _ = ∑ w : Fin 2 × Fin 2 × Fin 2, ghzWeight w :=
          Finset.sum_congr rfl (fun w _ => nudgedGHZ_coord_normSq w)
      _ = 1 := sum_ghzWeight
  rw [hsum, Real.sqrt_one]

/-- The nudged GHZ state is nonzero. -/
theorem nudgedGHZ_ne_zero : nudgedGHZ ≠ 0 := by
  intro h
  have := nudgedGHZ_norm
  rw [h, norm_zero] at this
  exact one_ne_zero this.symm

/-! ### Deliverable 1: the flow -/

/-- **The GHZ de-isolation flow** `Phi = measurementFlow 8 finProdFinEquiv` on the
dilated projective ontic space `Σ' = ℂℙ^{63} = ℙ(EuclideanSpace ℂ (Fin 64))`
(`64 = 8·8`). This is the LF5-B von Neumann de-isolation flow instantiated at the
joint three-qubit system `N = 8`. -/
noncomputable def ghzDeisolationFlow :
    ℙ ℂ (EuclideanSpace ℂ (Fin (8 * 8))) → ℙ ℂ (EuclideanSpace ℂ (Fin (8 * 8))) :=
  measurementFlow 8 finProdFinEquiv

/-- The GHZ de-isolation flow is Fubini-Study measure-preserving (the Liouville /
`hΦ_pres` content), inherited from `measurementFlow_measurePreserving`. -/
theorem ghzDeisolation_measurePreserving (p₀ : CPN (8 * 8)) :
    MeasurePreserving ghzDeisolationFlow (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀) :=
  measurementFlow_measurePreserving finProdFinEquiv p₀

/-- The GHZ de-isolation flow is genuinely not the identity (`N = 8 > 1`),
inherited from `measurementFlow_ne_id`. -/
theorem ghzDeisolation_ne_id : ghzDeisolationFlow ≠ id :=
  measurementFlow_ne_id (by norm_num) finProdFinEquiv

/-! ### Deliverable 2: pointer-block FS volume = GHZ Born weight (the headline) -/

/-- **The reproduction (the C.2 headline).** The context-fixed `BornRegion`
pointer-block `w` Fubini-Study volume of the GHZ de-isolation flow equals the GHZ
Born weight `ghzWeight w`, for the prepared state `φ = nudgedGHZ`.

The proof **composes** LF5 `vnDilation_pointer_volume` at `N = 8` (pointer-block
volume = `‖⟨e_i, φ⟩‖²`, Gleason-free, Born = FS-volume imported from the DH engine)
with the nudge coordinate-Born identity `nudgedGHZ_born` (the reindex-isometry
step + the computed GHZ Born weights). Minimal computational-basis carve; the
weights are the real GHZ diagonal `(1/2, 0, …, 0, 1/2)`. -/
theorem ghzDeisolation_pointer_volume {M : ℕ}
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV 8) (nudgedGHZ)))
    (hψ'0 : ψ' ≠ 0) (w : Fin 2 × Fin 2 × Fin 2) :
    ∑ n : Fin 8,
        (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, ghzIdx w)))).toReal
      = ghzWeight w := by
  rw [← vnDilation_pointer_volume (nudgedGHZ) nudgedGHZ_norm e p₀ ψ' hψ'eq hψ'0 (ghzIdx w)]
  exact nudgedGHZ_born w

/-! ### Deliverable 3: a.s. pointer-block frequencies → GHZ Born weight -/

/-- **The empirical capstone.** For i.i.d. Fubini-Study-typical trials on the
dilated `Σ' = ℂℙ^{63}` (the sector-typicality posit (SO-1) on the enlarged entangled
sector), almost surely every pointer-block `w` empirical frequency converges to
the GHZ Born weight `ghzWeight w`. Instantiates LF5
`vnDilation_pointer_frequency` at `N = 8`, `φ = nudgedGHZ`, and lands the limit on
`ghzWeight` via `nudgedGHZ_born`. -/
theorem ghzDeisolation_frequency {M : ℕ}
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV 8) (nudgedGHZ)))
    (hψ'0 : ψ' ≠ 0)
    (p₀ : CPN (M + 1))
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ j : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ' hψ'0 j) (fun _ => (1 : ℝ))))) :
    ∀ᵐ ω ∂ Pr, ∀ w : Fin 2 × Fin 2 × Fin 2,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin 8,
            (∑ k ∈ Finset.range m,
                Set.indicator ((X k) ⁻¹' bornRegion ψ' hψ'0 (e (n, ghzIdx w)))
                  (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds (ghzWeight w)) := by
  filter_upwards [vnDilation_pointer_frequency (nudgedGHZ) nudgedGHZ_norm e ψ'
      hψ'eq hψ'0 p₀ X hX hlaw hindep] with ω hω w
  have h := hω (ghzIdx w)
  rwa [nudgedGHZ_born w] at h

/-! ### Deliverable 4: the contextuality tie (via C.1, honest weaker form) -/

/-- **The contextuality anchor (routed through C.1).** No product (setting-local,
non-contextual) `plus/minus 1` partition of any shared probability space
`(Λ, μ)` reproduces the four GHZ perfect correlations `<XXX> = +1`,
`<XYY> = <YXY> = <YYX> = -1` (deterministic all-or-nothing, LF6-C.1).

**Honest scope.** This is the no-go the **Mermin-context** carve would route
through. The carve *built in this file* is the **minimal computational-basis**
carve, whose diagonal block weights `(1/2, 0, …, 0, 1/2)` do **not** reproduce
the Mermin X/Y correlations; so this anchor is the deferred Mermin-context
carve's contextuality tie, not a property of the diagonal carve exhibited above.
The diagonal carve realises the GHZ *diagonal weights*; it is not itself the
contextual carve. The dynamical Mermin-context carve (the three-party analogue of
A.2's `singletDeisolation_blockVolume_correlation`) is the deferred increment. -/
theorem ghzDeisolation_contextuality_anchor {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure Λ) [IsProbabilityMeasure μ] (R : Fin 3 → PauliAxis → Λ → ℝ)
    (hPP : IsProductPartitionGHZ R) (hRep : ReproducesGHZ μ R) : False :=
  no_product_partition_realises_ghz μ R hPP hRep

/-! ### Deliverable 5: the capstone -/

/-- **The LF6-C.2 capstone: the GHZ de-isolation flow.** A deterministic,
Fubini-Study-measure-preserving de-isolation flow `Phi != id` on the dilated
`Σ' = ℂℙ^{63}` whose context-fixed `BornRegion` pointer-block volumes are the GHZ
Born weights, with a.s. block frequencies → the weights and a contextuality
anchor routed through C.1. Conjuncts:

1. genuine dynamics, `Phi != id` (`measurementFlow_ne_id`, `1 < 8`);
2. physically admissible: FS measure-preserving (`measurementFlow_measurePreserving`);
3. pointer-block FS volume = the GHZ Born weight, every outcome
   (`ghzDeisolation_pointer_volume`);
4. a.s. block frequencies → the GHZ Born weight (`ghzDeisolation_frequency`);
5. the contextuality anchor: no setting-local `plus/minus 1` product partition
   reproduces the GHZ perfect correlations (`no_product_partition_realises_ghz`,
   C.1) — the tie for the deferred Mermin-context carve.

Minimal computational-basis carve (diagonal weights `(1/2, 0, …, 0, 1/2)`). Born
= FS-volume is imported from the DH/FS-volume engine, not re-derived; the flow
realises (not derives) the GHZ measurement. The Mermin-context carve and the
local product flow `V = V_0 ⊗ V_1 ⊗ V_2` are deferred. Residue: A5 (the GHZ
entangled sector posited). Honest ledger: module docstring. -/
theorem ghzDeisolation_flow_capstone {M : ℕ}
    (e : Fin 8 × Fin 8 ≃ Fin (M + 1)) (p₀ : CPN (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV 8) (nudgedGHZ)))
    (hψ'0 : ψ' ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → CPN (M + 1)) (hX : ∀ n, Measurable (X n))
    (hlaw : ∀ n, Measure.map (X n) Pr = fubiniStudyMeasure p₀)
    (hindep : ∀ j : Fin (M + 1),
      Pairwise (Function.onFun (fun f g : Ω → ℝ => IndepFun f g Pr)
        (fun n => Set.indicator ((X n) ⁻¹' bornRegion ψ' hψ'0 j) (fun _ => (1 : ℝ))))) :
    -- (1) genuine dynamics
    measurementFlow 8 e ≠ id
    -- (2) FS measure-preserving
    ∧ MeasurePreserving (measurementFlow 8 e)
        (fubiniStudyMeasure p₀) (fubiniStudyMeasure p₀)
    -- (3) pointer-block FS volume = the GHZ Born weight
    ∧ (∀ w : Fin 2 × Fin 2 × Fin 2,
        ∑ n : Fin 8,
            (fubiniStudyMeasure p₀ (bornRegion ψ' hψ'0 (e (n, ghzIdx w)))).toReal
          = ghzWeight w)
    -- (4) a.s. block frequencies → the GHZ Born weight
    ∧ (∀ᵐ ω ∂ Pr, ∀ w : Fin 2 × Fin 2 × Fin 2,
        Tendsto
          (fun m : ℕ =>
            ∑ n : Fin 8,
              (∑ k ∈ Finset.range m,
                  Set.indicator ((X k) ⁻¹' bornRegion ψ' hψ'0 (e (n, ghzIdx w)))
                    (fun _ => (1 : ℝ)) ω)
                / (m : ℝ))
          atTop
          (nhds (ghzWeight w)))
    -- (5) the contextuality anchor (routed through C.1)
    ∧ (∀ (Λ : Type) [MeasurableSpace Λ] (μ : Measure Λ) [IsProbabilityMeasure μ]
        (R : Fin 3 → PauliAxis → Λ → ℝ), IsProductPartitionGHZ R →
        ReproducesGHZ μ R → False) :=
  ⟨measurementFlow_ne_id (by norm_num) e,
   measurementFlow_measurePreserving e p₀,
   fun w => ghzDeisolation_pointer_volume e p₀ ψ' hψ'eq hψ'0 w,
   ghzDeisolation_frequency e ψ' hψ'eq hψ'0 p₀ X hX hlaw hindep,
   fun Λ _ μ _ R hPP hRep => no_product_partition_realises_ghz μ R hPP hRep⟩

end LF6
end CSD
