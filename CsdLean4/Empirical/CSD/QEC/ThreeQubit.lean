/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Empirical.CSD.Framework
public import CsdLean4.Empirical.QM.QEC.ThreeQubit
public import CsdLean4.Empirical.QM.QEC.BitFlipDilation
public import CsdLean4.Empirical.QM.QEC.SyndromeRecovery
public import CsdLean4.LF4.Instance
public import CsdLean4.LF5.MeasurementFlow
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitSection

/-!
# Empirical/CSD: the three-qubit bit-flip code (CSD-side reading)

**Category:** 3-Local (CSD-side companion to `Empirical/QM/QEC/ThreeQubit.lean`).

Pairs with the QM-validity bit-flip code (Shor 1995). The QM file proves error correction
as pure matrix algebra: stabilisers fix the codespace, the discretised Pauli errors give
distinct syndromes, and each `X` is self-inverse (recovery). This file states the **CSD
reading** and, since 2026-09-11, proves its two ontic halves (the error channel from a
`Σ`-flow; the code and error regions of `Σ`). The ontic content is subtler than "a flow off
the codespace", and getting it right is what makes QEC the corpus's sharpest pointer at the
dynamics layer.

- **The codespace is a sub-surface of `Σ`.** The `+1` joint eigenspace of the stabilisers
  is a 2-dimensional subspace of `ℂ⁸`, i.e. a `ℂℙ¹ ⊂ ℂℙ⁷` inside the ontic `Σ = ℂℙ⁷` of
  the three-qubit register — a *constraint surface within the constraint surface*.
- **The physical error is decoherence, which is volume flow — not a volume-preserving flow
  on the system alone.** A *coherent* (stray-unitary) error would be a symplectomorphism of
  `Σ_sys` (volume-preserving, no information lost). But the dominant error is the system
  **entangling with the environment**, `|ψ_L⟩|e₀⟩ ↦ Σ_E (E|ψ_L⟩)|e_E⟩`: the *joint* flow
  on `Σ_sys × Σ_env` is volume-preserving (Liouville — the `hΦ_pres` field), while the
  system **marginal** spreads as its coherence leaks into system–environment correlation.
  That is the "volume loss": lost *from the system to the environment*, conserved jointly.
  The Pauli errors `{I, X₁, X₂, X₃}` formalised on the QM side are the **discretised**
  representation of this channel (the QEC discretisation theorem), not coherent rotations.
- **The syndrome measurement is the entropy-extraction step** — the part that actually
  undoes decoherence. Measuring the stabilisers reads the environment's "which-error"
  record, *re-concentrating* the system's spread reduced state back to a pure state in one
  branch; the unitary recovery afterwards is the easy, volume-preserving return to the
  codespace. The four syndrome weights *are* the decoherence probabilities, and each is a
  sum of two computational-basis Fubini–Study volumes (a coarse-graining of the general-`N`
  Born-from-volume result at `N = 8`): "syndrome statistics as Kähler volumes."

So the honest ontic statement of QEC needs the environment `Σ_env`, the joint flow, and
partial trace. **Since 2026-09-11 (W6, W11) that is what this module has**, in two pieces:

* **The error channel is produced by a `Σ`-flow.** `bitFlipChannel_traceRight_barycenter_flow`:
  on a joint sector (system qubit ⊗ environment qubit), for a preparation that is a product with
  the environment ready and an ontic flow lifting the bit-flip joint unitary `U_p`
  (`QM/QEC/BitFlipDilation.lean`), the reduced density operator of the flowed preparation is
  the bit-flip channel applied to the system's density operator. The "volume loss" is the
  partial trace over the environment of a flow that is unitary on the joint space, exactly as
  described above. And `bitFlipFlow_traceRight_barycenter` is the **concrete instance**: on the
  corpus's own sector `cpSectorData` over `ℂℙ³` (`Σ = P = ℂℙ³`, `π = id`), the projective action
  `bitFlipFlow` of `U_p` is a `Φ ≠ id` flow, it lifts `U_p` with no hypothesis
  (`isUnitaryLift_bitFlipFlow`, via the canonical measurable unit section), and its environment
  marginal is the bit-flip channel.
* **The code space is a region of `Σ`, and the syndrome is a partition.** `codeRegion` is the
  set of rays of the codespace, the sub-surface `ℂℙ¹ ⊂ ℂℙ⁷`; `errorRegion k` is its image under
  the error `Eₖ`. ★★ `errorRegion_disjoint`: **the four error regions are pairwise disjoint**
  — two errored codewords on one ray would share their stabiliser eigenvalues, hence their
  syndromes, hence their error — so the syndrome measurement is the ontic selection of which of
  four disjoint regions the trajectory occupies. `recovery_mem_codeRegion`: re-applying the
  identified error returns every point of its error region to the code region.
* **The syndrome measurement is a projective measurement whose outcomes are the regions**
  (2026-09-12). `QM/QEC/SyndromeRecovery.lean` builds the syndrome projectors `Pₖ` (pairwise
  orthogonal, summing to `1`) and ★ `syndromeProj_fixes_errorRegion` here says every point of the
  `k`-th error region is fixed by `Pₖ` and annihilated by every other `Pⱼ`: the projectors *are*
  the indicator of the partition. The syndrome-conditioned recovery `R` (Kraus `Eₖ Pₖ`: "if in
  region `k`, apply `Eₖ`") is then **one channel** that returns every code state from the mixed
  post-error state — `Empirical/CSD/QECDecoherence.lean`, `syndrome_recovery_corrects_mixed`, the
  conjunct `csd_qec_decoherence_corrected` gained on 2026-09-12.

What is *not* here: the joint flow on the three-qubit register ⊗ environment (the flow theorem is
stated for one qubit's error channel; the register-level error is `singleFlipChannel`, the
correctable part of independent noise with free weights). The `LF5/SyndromeFlow.lean` tranche
carries the coherent-error syndrome flow.

## Source

Shor 1995, *Phys. Rev. A* **52**, R2493 (the bit-flip half of the 9-qubit code).
-/

@[expose] public section

open MeasureTheory Matrix QuantumInfo
open scoped ComplexOrder Kronecker LinearAlgebra.Projectivization

namespace CSD
namespace Empirical
namespace CSDBridge
namespace QEC

open CSD.LF2 CSD.Empirical.QM.QEC


open CSD.LF2 CSD.Empirical.QM.QEC

/-! ### The bit-flip channel produced by a `Σ`-flow -/

section Flow

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

/-- ★★ **The bit-flip channel is produced by a `Σ`-flow.** On a joint sector (system qubit ⊗
environment qubit), for a preparation that is a product with the environment ready and an ontic
flow lifting the bit-flip joint unitary `U_p`, the reduced density operator of the flowed
preparation is the bit-flip channel applied to the system's density operator. -/
theorem bitFlipChannel_traceRight_barycenter_flow (D : SectorData SigmaSpace P G)
    (μprep : Measure SigmaSpace) [IsProbabilityMeasure μprep]
    (Φ : SigmaSpace → SigmaSpace) (hΦ : Measurable Φ)
    (rep : P → EuclideanSpace ℂ (Fin 2 × Fin 2)) (hrep_unit : ∀ p, ‖rep p‖ = 1)
    (hrep_meas : Measurable rep)
    (repS : P → EuclideanSpace ℂ (Fin 2)) (hrepS_meas : Measurable repS)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hlift : IsUnitaryLift D Φ rep (bitFlipUnitary p))
    (hprod : ∀ᵐ x ∂μprep, outerProduct (rep (D.π x))
      = outerProduct (repS (D.π x)) ⊗ₖ outerProduct (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))) :
    Matrix.traceRight (barycenterMatrix rep (Measure.map D.π (Measure.map Φ μprep)))
      = (bitFlipChannel p hp0 hp1).apply (barycenterMatrix repS (Measure.map D.π μprep)) := by
  rw [← stinespringChannel_bitFlipUnitary p hp0 hp1]
  exact traceRight_barycenter_flow D μprep Φ hΦ rep hrep_unit hrep_meas repS hrepS_meas
    (bitFlipUnitary p) (bitFlipUnitary_conjTranspose_mul p hp0 hp1) _
    (by rw [PiLp.norm_single]; exact norm_one) hlift hprod

end Flow

/-! ### The concrete flow: the bit-flip unitary acting on `ℂℙ³` -/

section Concrete

/-- The joint index `Fin 2 × Fin 2` as `Fin 4`. -/
def jointEquiv : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv

/-- The bit-flip joint unitary as an element of `U(4)`, reindexed to `Fin 4`. -/
noncomputable def bitFlipU4 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Matrix.unitaryGroup (Fin 4) ℂ :=
  ⟨Matrix.reindex jointEquiv jointEquiv (bitFlipUnitary p),
    CSD.LF5.reindex_mem_unitaryGroup jointEquiv
      (Matrix.mem_unitaryGroup_iff'.mpr (by
        rw [Matrix.star_eq_conjTranspose]; exact bitFlipUnitary_conjTranspose_mul p hp0 hp1))⟩

theorem bitFlipU4_val (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ((bitFlipU4 p hp0 hp1 : Matrix.unitaryGroup (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ)
      = Matrix.reindex jointEquiv jointEquiv (bitFlipUnitary p) := rfl

/-- **The bit-flip de-isolation flow** on the joint projective space `ℂℙ³`: the projective action of
`U_p`. This is a flow of the corpus's `cpSectorData` (`Σ = P = ℂℙ³`, `π = id`). -/
noncomputable def bitFlipFlow (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    CSD.LF4.CPN 4 → CSD.LF4.CPN 4 :=
  fun q => bitFlipU4 p hp0 hp1 • q

theorem measurable_bitFlipFlow (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Measurable (bitFlipFlow p hp0 hp1) :=
  (continuous_const_smul (bitFlipU4 p hp0 hp1)).measurable

/-- The joint representative: the canonical unit section of `ℂℙ³`, transported to `Fin 2 × Fin 2`. -/
noncomputable def jointRep : CSD.LF4.CPN 4 → EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  fun q => (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ jointEquiv).symm (Projectivization.unitSection q)

theorem jointRep_norm (q : CSD.LF4.CPN 4) : ‖jointRep q‖ = 1 := by
  simp only [jointRep, LinearIsometryEquiv.norm_map, Projectivization.norm_unitSection]

theorem measurable_jointRep : Measurable jointRep :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ jointEquiv).symm.continuous.measurable.comp
    Projectivization.measurable_unitSection

/-- ★ **The bit-flip flow lifts `U_p`**, with no hypotheses: `cpSectorData`'s projection is the
identity and the flow is the projective action of the reindexed unitary. -/
theorem isUnitaryLift_bitFlipFlow (p₀ : CSD.LF4.CPN 4) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsUnitaryLift (CSD.LF4.cpSectorData p₀) (bitFlipFlow p hp0 hp1) jointRep (bitFlipUnitary p) :=
  isUnitaryLift_of_reindex (CSD.LF4.cpSectorData p₀) (bitFlipFlow p hp0 hp1) jointEquiv _ _
    (by
      have h := isUnitaryLift_of_smul (CSD.LF4.cpSectorData p₀) (bitFlipFlow p hp0 hp1)
        (bitFlipU4 p hp0 hp1) (fun _ => rfl) Projectivization.unitSection
        Projectivization.norm_unitSection Projectivization.unitSection_ne_zero
        Projectivization.mk_unitSection
      intro x
      have hx := h x
      rw [bitFlipU4_val] at hx
      simpa only [jointRep, LinearIsometryEquiv.apply_symm_apply] using hx)

/-- ★★ **On `ℂℙ³` the bit-flip channel is the environment marginal of `bitFlipFlow`, with no lift
hypothesis.** For any preparation on the joint projective space that is a product with the
environment ready (a.e., in the canonical representative), the reduced density operator of the
flowed preparation is the bit-flip channel applied to the system's density operator. -/
theorem bitFlipFlow_traceRight_barycenter (p₀ : CSD.LF4.CPN 4)
    (μprep : Measure (CSD.LF4.CPN 4)) [IsProbabilityMeasure μprep]
    (repS : CSD.LF4.CPN 4 → EuclideanSpace ℂ (Fin 2)) (hrepS_meas : Measurable repS)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hprod : ∀ᵐ x ∂μprep, outerProduct (jointRep x)
      = outerProduct (repS x) ⊗ₖ outerProduct (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))) :
    Matrix.traceRight (barycenterMatrix jointRep
        (Measure.map (CSD.LF4.cpSectorData p₀).π (Measure.map (bitFlipFlow p hp0 hp1) μprep)))
      = (bitFlipChannel p hp0 hp1).apply
          (barycenterMatrix repS (Measure.map (CSD.LF4.cpSectorData p₀).π μprep)) :=
  bitFlipChannel_traceRight_barycenter_flow (CSD.LF4.cpSectorData p₀) μprep (bitFlipFlow p hp0 hp1)
    (measurable_bitFlipFlow p hp0 hp1) jointRep jointRep_norm measurable_jointRep repS hrepS_meas
    p hp0 hp1 (isUnitaryLift_bitFlipFlow p₀ p hp0 hp1) hprod

end Concrete

/-! ### The code space as a region of `Σ`, and the error regions -/

section Region

/-- **The code region**: the rays of the codespace `{a|000⟩ + b|111⟩}` in the projective space of
the three-qubit register — the sub-surface `ℂℙ¹ ⊂ ℂℙ⁷` of `Σ`. -/
def codeRegion : Set (ℙ ℂ H3) :=
  {q | ∃ (a b : ℂ) (h : logical a b ≠ 0), q = Projectivization.mk ℂ (logical a b) h}

/-- **The error region of error `k`**: the image of the code region under the error `Eₖ`. -/
def errorRegion (k : Fin 4) : Set (ℙ ℂ H3) :=
  {q | ∃ (a b : ℂ) (h : Matrix.toEuclideanLin (errorOp k) (logical a b) ≠ 0),
    q = Projectivization.mk ℂ (Matrix.toEuclideanLin (errorOp k) (logical a b)) h}

/-- The errored codewords are stabiliser eigenvectors with eigenvalues the syndrome of the error. -/
theorem stab_eigen_errorOp (k : Fin 4) (a b : ℂ) :
    Matrix.toEuclideanLin Z1Z2 (Matrix.toEuclideanLin (errorOp k) (logical a b))
        = (errorSyndrome k).1 • Matrix.toEuclideanLin (errorOp k) (logical a b)
      ∧ Matrix.toEuclideanLin Z2Z3 (Matrix.toEuclideanLin (errorOp k) (logical a b))
        = (errorSyndrome k).2 • Matrix.toEuclideanLin (errorOp k) (logical a b) := by
  have h := three_qubit_syndrome_eigenstates a b
  fin_cases k
  · simpa [errorOp, Matrix.toLpLin_one] using h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

/-- ★★ **The four error regions are pairwise disjoint.** Two errored codewords on one ray would
share their stabiliser eigenvalues, hence their syndromes, hence their error index. This is the
identifiability of the syndrome read as a partition of `Σ`: the syndrome measurement is the ontic
selection of which of the four disjoint regions the trajectory occupies. -/
theorem errorRegion_disjoint {i j : Fin 4} (hij : i ≠ j) : Disjoint (errorRegion i) (errorRegion j) := by
  rw [Set.disjoint_left]
  rintro q ⟨a, b, ha, rfl⟩ ⟨a', b', ha', hq⟩
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ ha ha').mp hq
  set v := Matrix.toEuclideanLin (errorOp i) (logical a b) with hv
  set w := Matrix.toEuclideanLin (errorOp j) (logical a' b') with hw
  have hi := stab_eigen_errorOp i a b
  have hj := stab_eigen_errorOp j a' b'
  -- the errored codeword `v = c • w` carries both syndromes
  have key : ∀ (S : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) (si sj : ℂ),
      Matrix.toEuclideanLin S v = si • v → Matrix.toEuclideanLin S w = sj • w → si = sj := by
    intro S si sj hSi hSj
    have e : si • v = sj • v := by
      rw [← hSi, ← hc, map_smul, hSj, smul_comm]
    have := sub_eq_zero.mpr e
    rw [← sub_smul] at this
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h ha
  have h1 := key Z1Z2 _ _ hi.1 hj.1
  have h2 := key Z2Z3 _ _ hi.2 hj.2
  exact hij (three_qubit_syndromes_distinct (Prod.ext h1 h2))

/-- ★ **The syndrome projectors are the indicator of the error regions.** Every point of the
`k`-th error region has a representative fixed by the `k`-th syndrome projector and annihilated by
every other: the projective measurement `{Pₖ}` of `QM/QEC/SyndromeRecovery.lean` reads off which
of the four disjoint regions of `Σ` the trajectory occupies. -/
theorem syndromeProj_fixes_errorRegion (k : Fin 4) (q : ℙ ℂ H3) (hq : q ∈ errorRegion k) :
    ∃ (v : H3) (hv : v ≠ 0), q = Projectivization.mk ℂ v hv
      ∧ Matrix.toEuclideanLin (syndromeProj k) v = v
      ∧ ∀ j, j ≠ k → Matrix.toEuclideanLin (syndromeProj j) v = 0 := by
  obtain ⟨a, b, h, rfl⟩ := hq
  exact ⟨_, h, rfl, syndromeProj_errorOp_logical k a b,
    fun j hj => syndromeProj_errorOp_logical_of_ne hj a b⟩

/-- **Recovery returns to the code region**: re-applying the identified error sends every point of
its error region back into the code region (each `Xⱼ` is self-inverse). -/
theorem recovery_mem_codeRegion (k : Fin 4) (a b : ℂ)
    (h : Matrix.toEuclideanLin (errorOp k) (Matrix.toEuclideanLin (errorOp k) (logical a b)) ≠ 0) :
    Projectivization.mk ℂ
        (Matrix.toEuclideanLin (errorOp k) (Matrix.toEuclideanLin (errorOp k) (logical a b))) h
      ∈ codeRegion := by
  have hrec : Matrix.toEuclideanLin (errorOp k) (Matrix.toEuclideanLin (errorOp k) (logical a b))
      = logical a b := by
    have h3 := three_qubit_corrects_single_bitflip a b
    fin_cases k
    · simp [errorOp, Matrix.toLpLin_one]
    · exact h3.2.2.1
    · exact h3.2.2.2.1
    · exact h3.2.2.2.2
  refine ⟨a, b, hrec ▸ h, ?_⟩
  simp only [hrec]

end Region

/-- ★★ **The three-qubit bit-flip code corrects any single bit-flip, in the CSD reading.** The
QM-side correction theorem (stabilisers fix the codespace, the four syndromes are distinct, each
`Xⱼ` is self-inverse), **together with its `Σ`-reading**: the four error regions of `Σ` are
pairwise disjoint (the syndrome is a partition of `Σ`), and recovery returns each error region to
the code region. The error channel itself is produced by a `Σ`-flow
(`bitFlipFlow_traceRight_barycenter`). No bundle is carried: every conjunct is proved. -/
theorem csd_three_qubit_corrects_single_bitflip (a b : ℂ) :
    ((Matrix.toEuclideanLin Z1Z2 (logical a b) = logical a b
        ∧ Matrix.toEuclideanLin Z2Z3 (logical a b) = logical a b)
      ∧ Function.Injective errorSyndrome
      ∧ (Matrix.toEuclideanLin X1 (Matrix.toEuclideanLin X1 (logical a b)) = logical a b
        ∧ Matrix.toEuclideanLin X2 (Matrix.toEuclideanLin X2 (logical a b)) = logical a b
        ∧ Matrix.toEuclideanLin X3 (Matrix.toEuclideanLin X3 (logical a b)) = logical a b))
    ∧ (∀ i j : Fin 4, i ≠ j → Disjoint (errorRegion i) (errorRegion j))
    ∧ (∀ (k : Fin 4) (a b : ℂ)
        (h : Matrix.toEuclideanLin (errorOp k) (Matrix.toEuclideanLin (errorOp k) (logical a b)) ≠ 0),
        Projectivization.mk ℂ
          (Matrix.toEuclideanLin (errorOp k) (Matrix.toEuclideanLin (errorOp k) (logical a b))) h
          ∈ codeRegion) :=
  ⟨three_qubit_corrects_single_bitflip a b, fun _ _ hij => errorRegion_disjoint hij,
    fun k a b h => recovery_mem_codeRegion k a b h⟩

end QEC
end CSDBridge
end Empirical
end CSD
