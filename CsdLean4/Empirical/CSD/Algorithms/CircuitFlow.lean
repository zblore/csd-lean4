/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF2.FlowChannel
public import CsdLean4.LF4.Instance
public import CsdLean4.LF5.MeasurementFlow
public import CsdLean4.LF6.DecoherenceChannel
public import CsdLean4.RecordLayer.GlobalBasin
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.TransitionProbability

/-!
# Empirical/CSD: a quantum circuit is a flow on `Σ`, and its readout is a record basin

**Category:** 3-Local (CSD-side companion to `Empirical/QM/Algorithms/`; the generic engine the
algorithm twins `GroverFlow.lean` and `ShorFlow.lean` instantiate).

A quantum circuit on a register indexed by `ι` is a unitary `U` on `EuclideanSpace ℂ ι`. On the
CSD side the register's state space is the sector `Σ = ℂℙ^{card ι − 1}` (`cpSectorData`), the
circuit is the **flow** `x ↦ U • x` on it, running the circuit `k` times is the flow iterated `k`
times, and the readout of the computational-basis measurement is the record basin of the
outcome (`RecordLayer/GlobalBasin.lean`) or, on the density-operator side, the de-isolation
channel (`LF6/DecoherenceChannel.lean`). Nothing here is specific to an algorithm: the pattern is
`Empirical/CSD/QEC/RegisterFlow.lean`'s, factored out.

* `Circuit ι` — a unitary on the register; `Circuit.toUnitaryGroup`, the enumerated unitary in
  `U(card ι)`; `Circuit.flow`, **the circuit as a `Σ`-flow**; `Circuit.flow_iterate`, `k` runs
  are the projective action of `U ^ k`;
* ★ `Circuit.isUnitaryLift_flow` — **the flow lifts the circuit's unitary** through the register
  representative, with no hypothesis (through the canonical measurable unit section);
* ★★ `Circuit.barycenter_flow_iterate` — **the density operator after `k` runs is
  `U^k ρ (U^k)ᴴ`**, for every preparation, derived from the ontic flow (`barycenter_flow`);
* `readout ρ i` — the weight the de-isolation channel assigns to outcome `i`;
  `readout_outerProduct`, `readout_conj_outerProduct` — on a pure input it is the Born weight
  `‖ψ i‖²`, and after a unitary it is `‖(U ψ) i‖²`; `barycenterMatrix_dirac` — the density
  operator of a preparation concentrated at one point is the projector of its representative;
* ★★ `Circuit.epistemicMeasure_globalBasin_flow_iterate` — **the readout on `Σ`**: at the point
  reached from the ray of a unit `ψ` by `k` runs of the circuit, the record basin of outcome `i`
  has Born weight `‖(U^k ψ) i‖²` (`globalBasin_born`).

Helpers, index-generic: `toEuclideanLin_pow_apply`, `toEuclideanLin_reindex_piLpCongrLeft`.

⚠️ **Honest scope.** A circuit is its unitary; no gate decomposition, timing, or Hamiltonian
generating `U` is modelled (the flow is the time-one map of the projective action, as in
`RegisterFlow.lean`, and `R-015` applies). The readout is the corpus's computational-basis record
basin, context-fixed and kinematic (`globalBasin_born`'s own scope note).

References: `Empirical/CSD/QEC/RegisterFlow.lean` (the pattern); `LF2/FlowChannel.lean`
(`IsUnitaryLift`, `barycenter_flow`); `RecordLayer/GlobalBasin.lean` (`globalBasin_born`);
`LF6/DecoherenceChannel.lean`; `specs/BACKLOG.md` #34; `specs/future-work.md`.
-/

@[expose] public section

open MeasureTheory Matrix QuantumInfo
open scoped LinearAlgebra.Projectivization

namespace CSD
namespace Empirical
namespace CSDBridge
namespace Algorithms

open CSD.LF2 CSD.LF4 CSD.LF6 CSD.RecordLayer

/-! ### Index-generic helpers -/

section Helpers

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- `toEuclideanLin` of a product is the composite. -/
theorem toEuclideanLin_mul_apply' (A B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanLin (A * B) v = Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) := by
  show WithLp.toLp 2 ((A * B) *ᵥ WithLp.ofLp v) = WithLp.toLp 2 (A *ᵥ (B *ᵥ WithLp.ofLp v))
  rw [Matrix.mulVec_mulVec]

/-- `toEuclideanLin` of a power is the iterate. -/
theorem toEuclideanLin_pow_apply (U : Matrix ι ι ℂ) (k : ℕ) (v : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanLin (U ^ k) v = (Matrix.toEuclideanLin U)^[k] v := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, toEuclideanLin_mul_apply', ih, Function.iterate_succ_apply]

/-- Reindexing a matrix and its argument together. -/
theorem toEuclideanLin_reindex_piLpCongrLeft (e : ι ≃ κ) (U : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanLin (Matrix.reindex e e U) (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e v)
      = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (Matrix.toEuclideanLin U v) := by
  ext j
  simp only [Matrix.toLpLin_apply, LinearIsometryEquiv.piLpCongrLeft_apply,
    Matrix.reindex_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, PiLp.toLp_apply,
    Equiv.piCongrLeft'_apply]
  exact Fintype.sum_equiv e.symm _ _ fun _ => rfl

omit [DecidableEq ι] [DecidableEq κ] in
/-- The coordinate of a reindexed vector at a reindexed index. -/
theorem piLpCongrLeft_apply_apply (e : ι ≃ κ) (v : EuclideanSpace ℂ ι) (i : ι) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e v (e i) = v i := by
  simp [LinearIsometryEquiv.piLpCongrLeft_apply]

end Helpers

/-! ### The register's sector and representative -/

/-- A circuit on the register indexed by `ι`: a unitary on `EuclideanSpace ℂ ι`. -/
structure Circuit (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The unitary of the circuit. -/
  U : Matrix ι ι ℂ
  /-- Unitarity, `Uᴴ U = 1`. -/
  conjTranspose_mul : Uᴴ * U = 1

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A nonempty register has a nonzero number of basis states. -/
instance instNeZeroCard : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩

/-- The enumeration of the register's index that places its sector at `ℂℙ^{card ι − 1}`. -/
noncomputable abbrev idx (ι : Type*) [Fintype ι] : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι

/-- The register's sector, `Σ = ℂℙ^{card ι − 1}`. -/
abbrev RegisterSector (ι : Type*) [Fintype ι] := CPN (Fintype.card ι)

/-- The register representative: the canonical measurable unit section of the sector, read in
the register's own index. -/
noncomputable def registerRep (ι : Type*) [Fintype ι] : RegisterSector ι → EuclideanSpace ℂ ι :=
  fun x => (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (idx ι)).symm (Projectivization.unitSection x)

omit [DecidableEq ι] [Nonempty ι] in
theorem registerRep_norm (x : RegisterSector ι) : ‖registerRep ι x‖ = 1 := by
  simp only [registerRep, LinearIsometryEquiv.norm_map, Projectivization.norm_unitSection]

omit [DecidableEq ι] [Nonempty ι] in
theorem measurable_registerRep : Measurable (registerRep ι) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (idx ι)).symm.continuous.measurable.comp
    Projectivization.measurable_unitSection

/-! ### The circuit as a flow -/

namespace Circuit

variable (C : Circuit ι)

/-- The circuit's unitary, enumerated, as an element of `U(card ι)`. -/
noncomputable def toUnitaryGroup : Matrix.unitaryGroup (Fin (Fintype.card ι)) ℂ :=
  ⟨Matrix.reindex (idx ι) (idx ι) C.U,
    CSD.LF5.reindex_mem_unitaryGroup (idx ι) (Matrix.mem_unitaryGroup_iff'.mpr (by
      rw [Matrix.star_eq_conjTranspose]; exact C.conjTranspose_mul))⟩

omit [Nonempty ι] in
theorem coe_toUnitaryGroup :
    (C.toUnitaryGroup : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ)
      = Matrix.reindex (idx ι) (idx ι) C.U :=
  rfl

omit [Nonempty ι] in
/-- The enumerated unitary of `k` runs is the reindexed `U ^ k`. -/
theorem coe_toUnitaryGroup_pow (k : ℕ) :
    ((C.toUnitaryGroup ^ k : Matrix.unitaryGroup (Fin (Fintype.card ι)) ℂ)
        : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ)
      = Matrix.reindex (idx ι) (idx ι) (C.U ^ k) := by
  rw [SubmonoidClass.coe_pow, coe_toUnitaryGroup, ← Matrix.coe_reindexAlgEquiv ℂ ℂ (idx ι),
    ← map_pow]

/-- **The circuit as a flow on `Σ`**: the projective action of its unitary on the register's
sector. A flow of the corpus's `cpSectorData` (`Σ = P = ℂℙ^{card ι − 1}`, `π = id`). -/
noncomputable def flow : RegisterSector ι → RegisterSector ι :=
  fun x => C.toUnitaryGroup • x

omit [Nonempty ι] in
theorem flow_def (x : RegisterSector ι) : C.flow x = C.toUnitaryGroup • x :=
  rfl

omit [Nonempty ι] in
theorem measurable_flow : Measurable C.flow :=
  (continuous_const_smul C.toUnitaryGroup).measurable

omit [Nonempty ι] in
/-- `k` runs of the circuit are the flow iterated `k` times: the projective action of `U ^ k`. -/
theorem flow_iterate (k : ℕ) (x : RegisterSector ι) :
    C.flow^[k] x = (C.toUnitaryGroup ^ k) • x := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, pow_succ', mul_smul]; rfl

/-- ★ **The flow lifts the enumerated unitary** through the canonical unit section, with no
hypothesis. -/
theorem isUnitaryLift_flow_unitSection (p₀ : RegisterSector ι) :
    IsUnitaryLift (cpSectorData p₀) C.flow Projectivization.unitSection
      (C.toUnitaryGroup : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) :=
  isUnitaryLift_of_smul (cpSectorData p₀) C.flow C.toUnitaryGroup (fun _ => rfl)
    Projectivization.unitSection Projectivization.norm_unitSection
    Projectivization.unitSection_ne_zero Projectivization.mk_unitSection

/-- ★ **The flow lifts the circuit's own unitary** through the register representative. -/
theorem isUnitaryLift_flow (p₀ : RegisterSector ι) :
    IsUnitaryLift (cpSectorData p₀) C.flow (registerRep ι) C.U :=
  isUnitaryLift_of_reindex (cpSectorData p₀) C.flow (idx ι) _ _ (by
    intro x
    have hx := C.isUnitaryLift_flow_unitSection p₀ x
    rw [coe_toUnitaryGroup] at hx
    simpa only [registerRep, LinearIsometryEquiv.apply_symm_apply] using hx)

/-- ★★ **The density operator after `k` runs is `U^k ρ (U^k)ᴴ`**, for every preparation on the
sector, derived from the ontic flow: the Schrödinger picture of the circuit. -/
theorem barycenter_flow_iterate (p₀ : RegisterSector ι) (μprep : Measure (RegisterSector ι))
    [IsProbabilityMeasure μprep] (k : ℕ) :
    barycenterMatrix (registerRep ι)
        (Measure.map (cpSectorData p₀).π (Measure.map C.flow^[k] μprep))
      = C.U ^ k * barycenterMatrix (registerRep ι) (Measure.map (cpSectorData p₀).π μprep)
          * (C.U ^ k)ᴴ :=
  barycenter_flow (cpSectorData p₀) μprep C.flow^[k] (C.measurable_flow.iterate k)
    (registerRep ι) registerRep_norm measurable_registerRep (C.U ^ k)
    ((C.isUnitaryLift_flow p₀).iterate k)

/-- The same in the enumerated index, the form the readout channel takes. -/
theorem barycenter_unitSection_flow_iterate (p₀ : RegisterSector ι)
    (μprep : Measure (RegisterSector ι)) [IsProbabilityMeasure μprep] (k : ℕ) :
    barycenterMatrix Projectivization.unitSection
        (Measure.map (cpSectorData p₀).π (Measure.map C.flow^[k] μprep))
      = (C.toUnitaryGroup ^ k).val
          * barycenterMatrix Projectivization.unitSection (Measure.map (cpSectorData p₀).π μprep)
          * (C.toUnitaryGroup ^ k).valᴴ := by
  rw [SubmonoidClass.coe_pow]
  exact barycenter_flow (cpSectorData p₀) μprep C.flow^[k] (C.measurable_flow.iterate k)
    Projectivization.unitSection Projectivization.norm_unitSection
    Projectivization.measurable_unitSection _ ((C.isUnitaryLift_flow_unitSection p₀).iterate k)

omit [Nonempty ι] in
/-- The point reached from the ray of `ψ` by `k` runs is the ray of `U^k ψ`. -/
theorem flow_iterate_mk (k : ℕ) (ψ : EuclideanSpace ℂ (Fin (Fintype.card ι))) (hψ0 : ψ ≠ 0) :
    C.flow^[k] (Projectivization.mk ℂ ψ hψ0)
      = Projectivization.mk ℂ
          (Matrix.toEuclideanLin (C.toUnitaryGroup ^ k).val ψ)
          (Matrix.UnitaryGroup.toEuclideanLin_unitary_ne_zero (C.toUnitaryGroup ^ k) hψ0) := by
  rw [C.flow_iterate]
  exact Matrix.UnitaryGroup.smul_mk_eq_mk (C.toUnitaryGroup ^ k) ψ hψ0

omit [Nonempty ι] in
/-- ★★ **The readout on `Σ`.** At the point reached from the ray of a unit vector `ψ` by `k` runs
of the circuit, the record basin of the computational-basis outcome `i` (the apparatus's
context-fixed basin, `globalBasin`) has Born weight `‖(U^k ψ) i‖²`. -/
theorem epistemicMeasure_globalBasin_flow_iterate (k : ℕ)
    (ψ : EuclideanSpace ℂ (Fin (Fintype.card ι))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1)
    (i : Fin (Fintype.card ι)) :
    epistemicMeasure (C.flow^[k] (Projectivization.mk ℂ ψ hψ0))
        (globalBasin (momentContext (Fintype.card ι)) i)
      = ENNReal.ofReal
          (‖Matrix.toEuclideanLin (C.toUnitaryGroup ^ k).val ψ i‖ ^ 2) := by
  rw [flow_iterate_mk, globalBasin_born _ _
    (by rw [Projectivization.norm_toEuclideanLin_unitary]; exact hψ),
    EuclideanSpace.inner_single_left, map_one, one_mul]

end Circuit

/-! ### The readout channel -/

/-- **The readout**: the weight the de-isolation channel assigns to the computational-basis
outcome `i` of a density operator `ρ`, the diagonal entry of the channel's output. -/
noncomputable def readout {M : ℕ} [NeZero M] (ρ : Matrix (Fin M) (Fin M) ℂ) (i : Fin M) : ℂ :=
  (deisolationChannel M).apply ρ i i

/-- On a pure input the readout is the Born weight. -/
theorem readout_outerProduct {M : ℕ} [NeZero M] (φ : EuclideanSpace ℂ (Fin M)) (i : Fin M) :
    readout (outerProduct φ) i = ((‖φ i‖ ^ 2 : ℝ) : ℂ) := by
  rw [readout, deisolationChannel_apply_outerProduct, decohereReduced_apply, if_pos rfl,
    Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- After a unitary, the readout of a pure input is the Born weight of the image. -/
theorem readout_conj_outerProduct {M : ℕ} [NeZero M] (V : Matrix (Fin M) (Fin M) ℂ)
    (φ : EuclideanSpace ℂ (Fin M)) (i : Fin M) :
    readout (V * outerProduct φ * Vᴴ) i = ((‖Matrix.toEuclideanLin V φ i‖ ^ 2 : ℝ) : ℂ) := by
  rw [← outerProduct_toEuclideanLin, readout_outerProduct]

/-- The density operator of a preparation concentrated at one point is the projector of that
point's representative. -/
theorem barycenterMatrix_dirac {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
    {κ : Type*} (rep : Q → EuclideanSpace ℂ κ) (q : Q) :
    barycenterMatrix rep (Measure.dirac q) = outerProduct (rep q) := by
  ext j k
  simp only [barycenterMatrix, Matrix.of_apply, entryFn, integral_dirac, outerProduct,
    Matrix.vecMulVec_apply]

end Algorithms
end CSDBridge
end Empirical
end CSD
