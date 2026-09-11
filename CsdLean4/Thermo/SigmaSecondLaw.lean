/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.LF2.FlowChannel
public import CsdLean4.LF6.DecoherenceChannel
public import CsdLean4.Thermo.SecondLaw
public import CsdLean4.Thermo.Landauer

/-!
# The second law, data processing and Landauer on `Σ`

**Category:** 3-Local (W7 of `specs/qit-chain-scoping.md`; the thermodynamic and
information-theoretic theorems of the corpus instantiated on preparations under `Σ`-flows).

TH2 (`Thermo/SecondLaw.lean`), the data-processing inequality (`Mathlib/QuantumInfo/
DataProcessing.lean`) and TH4 (`Thermo/Landauer.lean`) are theorems about bare density matrices, a
unitary `U` and a coarse-graining map `pinch`. W3 made the density operator of a preparation on `Σ`
a definite matrix (the barycentre) and W6 made its evolution along an ontic flow lifting `U` a
theorem. This module instantiates the three on that evolution, so each becomes a statement about
`Σ`-regions under de-isolation:

* `deisolationChannel_apply_eq_pinch` — **the coarse-graining of the second law is the
  de-isolation channel**: on a Hermitian input, tracing the pointer out of the von Neumann
  coupling is exactly the pointer-basis pinching `pinch` of TH2. The `pinch` is not an extra
  postulated coarse-graining; it is the environment marginal of the de-isolation flow;
* ★ `vonNeumannEntropy_flow_eq` — **entropy is conserved along the ontic flow** (closed system);
* ★★ `vonNeumannEntropy_le_pinching_flow` — **the second law on `Σ`**: `S(ρ(μprep)) =
  S(ρ(Φ_* μprep)) ≤ S(pinch ρ(Φ_* μprep))`, reversible microdynamics on `Σ`, entropy production
  from coarse-graining;
* ★★ `vonNeumannEntropy_le_deisolation` — **the second law under de-isolation**: the entropy of the
  system's reduced density operator after a flow lifting the von Neumann coupling is at least its
  entropy before, because the reduced flowed state is the pinching;
* ★★ `traceDist_traceRight_flow_le` — **data processing on `Σ`**: de-isolation along a flow lifting
  any joint unitary cannot increase the trace distance of two preparations' reduced density
  operators;
* ★★ `landauer_flow` — **Landauer on `Σ`**: for a product preparation on a system-plus-bath sector
  whose bath preparation has the Gibbs state as its density operator, the entropy removed from the
  system preparation by an ontic flow lifting the joint unitary is at most `β` times the heat
  dumped into the bath (`barycenter_flow_prod` supplies the flowed joint state to `landauer_bound`).

## Honest scope

⚠️ **The hypotheses are TH2's and TH4's.** The pinching inequality needs full support (strictly
positive pointer weights), Landauer needs full-rank final marginals and a full-rank initial system
state. These are inherited, not added. The lift hypothesis `IsUnitaryLift` is W6's (a theorem for
the projective unitary actions, `isUnitaryLift_of_smul`; for LF5's reindexed measurement flow the
joint-index instance is W6′). The Gibbs hypothesis of `landauer_flow` says the bath *preparation*
is thermal; that a bath preparation on `Σ` has a Gibbs barycentre is not derived here (the
canonical-typicality route, `Thermo/CanonicalTypicality.lean`, is the corpus's approach).

⚠️ **Posits unchanged.** The sector is posited (`specs/POSITS.md`); what is proved is that, given
it and a flow lifting a unitary, the QIT thermodynamics of preparations holds as the QIT layer
states it.

References: `specs/qit-chain-scoping.md` (W7); `LF2/FlowChannel.lean` (W6);
`LF6/DecoherenceChannel.lean`; `Thermo/SecondLaw.lean` (`pinch`, `vonNeumannEntropy_le_pinching`);
`Thermo/Landauer.lean` (`landauer_bound`); `Mathlib/QuantumInfo/DataProcessing.lean`
(`channel_traceDist_le`).
-/

@[expose] public section

open MeasureTheory Matrix QuantumInfo
open scoped ComplexOrder Kronecker

namespace CSD
namespace Thermo

open CSD.LF2 CSD.LF5 CSD.LF6

/-! ### Bookkeeping -/

/-- Von Neumann entropy depends only on the matrix (transport along an equality of matrices). -/
theorem vonNeumannEntropy_congr_of_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : A = B) :
    vonNeumannEntropy hA = vonNeumannEntropy hB := by
  subst hAB; rfl

/-! ### The de-isolation channel is the pointer-basis pinching -/

section Deisolation

variable {N : ℕ} [NeZero N]

/-- **The coarse-graining of the second law is the de-isolation channel.** On a Hermitian input,
tracing the pointer out of the von Neumann coupling gives exactly the pointer-basis pinching:
`(deisolationChannel N).apply ρ = pinch ρ`. The `pinch` of TH2 is not an extra postulated
coarse-graining; it is the environment marginal of the de-isolation flow. -/
theorem deisolationChannel_apply_eq_pinch {ρ : Matrix (Fin N) (Fin N) ℂ} (hρ : ρ.IsHermitian) :
    (deisolationChannel N).apply ρ = pinch ρ := by
  rw [deisolationChannel_apply]
  ext a b
  rw [partialTraceRight_apply, pinch_apply]
  have hterm : ∀ k, (vnDilationV N * ρ * (vnDilationV N)ᴴ) (a, k) (b, k)
      = if k = a ∧ k = b then ρ a b else 0 := by
    intro k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, vnDilationV_apply, Prod.mk.injEq]
    by_cases hka : k = a
    · subst hka
      by_cases hkb : k = b
      · subst hkb
        simp
      · rw [if_neg (fun h => hkb h.2)]
        refine Finset.sum_eq_zero fun x _ => ?_
        rw [if_neg (fun h => hkb (h.2.trans h.1.symm))]
        simp
    · rw [if_neg (fun h => hka h.1)]
      refine Finset.sum_eq_zero fun x _ => ?_
      have hin : (∑ y, (if a = y ∧ k = y then (1 : ℂ) else 0) * ρ y x) = 0 :=
        Finset.sum_eq_zero fun y _ => by
          rw [if_neg (fun h => hka (h.2.trans h.1.symm)), zero_mul]
      rw [hin, zero_mul]
  simp_rw [hterm]
  by_cases hab : a = b
  · subst hab
    simp [diag_ofReal_re_of_isHermitian hρ a]
  · rw [if_neg hab]
    exact Finset.sum_eq_zero fun x _ => if_neg (fun h => hab (h.1.symm.trans h.2))

end Deisolation

/-! ### The second law on `Σ`, closed system -/

section Closed

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (D : SectorData SigmaSpace P G) (μprep : Measure SigmaSpace) [IsProbabilityMeasure μprep]
  (Φ : SigmaSpace → SigmaSpace) (rep : P → EuclideanSpace ℂ ι)

/-- The projective law of the flowed preparation is a probability measure. -/
theorem isProbabilityMeasure_projectiveLaw_flow (hΦ : Measurable Φ) :
    IsProbabilityMeasure (Measure.map D.π (Measure.map Φ μprep)) := by
  have : IsProbabilityMeasure (Measure.map Φ μprep) :=
    Measure.isProbabilityMeasure_map' hΦ.aemeasurable
  exact Measure.isProbabilityMeasure_map' D.measurable_π.aemeasurable

/-- ★ **Entropy is conserved along the ontic flow.** The density operator of the flowed
preparation is `U ρ Uᴴ` (`barycenter_flow`), and conjugation by a unitary preserves the
spectrum. -/
theorem vonNeumannEntropy_flow_eq (hΦ : Measurable Φ) (hrep_unit : ∀ p, ‖rep p‖ = 1)
    (hrep_meas : Measurable rep) (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1)
    (hlift : IsUnitaryLift D Φ rep U) :
    vonNeumannEntropy (barycenterMatrix_isHermitian rep (Measure.map D.π (Measure.map Φ μprep)))
      = vonNeumannEntropy (barycenterMatrix_isHermitian rep (Measure.map D.π μprep)) := by
  have h : barycenterMatrix rep (Measure.map D.π (Measure.map Φ μprep))
      = U * barycenterMatrix rep (Measure.map D.π μprep) * star U := by
    rw [Matrix.star_eq_conjTranspose]
    exact barycenter_flow D μprep Φ hΦ rep hrep_unit hrep_meas U hlift
  have hU' : star U * U = 1 := by rw [Matrix.star_eq_conjTranspose]; exact hU
  have hB := barycenterMatrix_isHermitian rep (Measure.map D.π μprep)
  have hUBU : (U * barycenterMatrix rep (Measure.map D.π μprep) * star U).IsHermitian :=
    h ▸ barycenterMatrix_isHermitian rep _
  rw [vonNeumannEntropy_congr_of_eq _ hUBU h]
  exact vonNeumannEntropy_conj_unitary hB hU' hUBU

/-- ★★ **The second law on `Σ`.** Along an ontic flow lifting a unitary, the entropy of a
preparation is conserved, and pinching the flowed density operator to the pointer basis does not
decrease it: `S(ρ(μprep)) = S(ρ(Φ_* μprep)) ≤ S(pinch ρ(Φ_* μprep))`, under the full-support
hypothesis TH2 needs (strictly positive pointer weights after the flow). Reversible
microdynamics on `Σ`, entropy production from coarse-graining. -/
theorem vonNeumannEntropy_le_pinching_flow (hΦ : Measurable Φ) (hrep_unit : ∀ p, ‖rep p‖ = 1)
    (hrep_meas : Measurable rep) (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1)
    (hlift : IsUnitaryLift D Φ rep U)
    (hpos : ∀ i, 0 < ((barycenterMatrix rep (Measure.map D.π (Measure.map Φ μprep))) i i).re) :
    vonNeumannEntropy (barycenterMatrix_isHermitian rep (Measure.map D.π μprep))
      ≤ vonNeumannEntropy
          (pinch_isHermitian (barycenterMatrix rep (Measure.map D.π (Measure.map Φ μprep)))) := by
  have := isProbabilityMeasure_projectiveLaw_flow D μprep Φ hΦ
  rw [← vonNeumannEntropy_flow_eq D μprep Φ rep hΦ hrep_unit hrep_meas U hU hlift]
  exact vonNeumannEntropy_le_pinching (barycenterMatrix_posSemidef rep hrep_unit hrep_meas _)
    (barycenterMatrix_trace rep hrep_unit hrep_meas _) hpos

end Closed

/-! ### The second law and data processing on `Σ`, open system -/

section Open

variable {SigmaSpace P G : Type*}
  [MeasurableSpace SigmaSpace] [Nonempty SigmaSpace]
  [MeasurableSpace P]
  [Group G]
  [MulAction G SigmaSpace] [MulAction G P]
  [MulAction.IsPretransitive G P]

variable (D : SectorData SigmaSpace P G)

/-- ★★ **Data processing on `Σ`: de-isolation cannot increase the distinguishability of two
preparations.** For two preparations on a joint sector, both products with the environment ready
in `e₀`, and an ontic flow lifting `U`, the trace distance of the reduced flowed density operators
is at most the trace distance of the system density operators before the flow
(`channel_traceDist_le` on the channel `traceRight_barycenter_flow` produces). -/
theorem traceDist_traceRight_flow_le {n e : Type*} [Fintype n] [Fintype e] [DecidableEq n]
    [DecidableEq e]
    (μprep μprep' : Measure SigmaSpace) [IsProbabilityMeasure μprep] [IsProbabilityMeasure μprep']
    (Φ : SigmaSpace → SigmaSpace) (hΦ : Measurable Φ)
    (rep : P → EuclideanSpace ℂ (n × e)) (hrep_unit : ∀ p, ‖rep p‖ = 1)
    (hrep_meas : Measurable rep)
    (repS : P → EuclideanSpace ℂ n) (hrepS_unit : ∀ p, ‖repS p‖ = 1) (hrepS_meas : Measurable repS)
    (U : Matrix (n × e) (n × e) ℂ) (hU : Uᴴ * U = 1) (e₀ : EuclideanSpace ℂ e) (he₀ : ‖e₀‖ = 1)
    (hlift : IsUnitaryLift D Φ rep U)
    (hprod : ∀ᵐ x ∂μprep,
      outerProduct (rep (D.π x)) = outerProduct (repS (D.π x)) ⊗ₖ outerProduct e₀)
    (hprod' : ∀ᵐ x ∂μprep',
      outerProduct (rep (D.π x)) = outerProduct (repS (D.π x)) ⊗ₖ outerProduct e₀) :
    traceDist
        ((barycenterMatrix_isHermitian rep (Measure.map D.π (Measure.map Φ μprep))).traceRight.sub
          (barycenterMatrix_isHermitian rep (Measure.map D.π (Measure.map Φ μprep'))).traceRight)
      ≤ traceDist ((barycenterMatrix_isHermitian repS (Measure.map D.π μprep)).sub
          (barycenterMatrix_isHermitian repS (Measure.map D.π μprep'))) := by
  have h1 := isProbabilityMeasure_projectiveLaw D μprep
  have h2 := isProbabilityMeasure_projectiveLaw D μprep'
  have hS := barycenterMatrix_isHermitian repS (Measure.map D.π μprep)
  have hS' := barycenterMatrix_isHermitian repS (Measure.map D.π μprep')
  have htr : (barycenterMatrix repS (Measure.map D.π μprep)).trace
      = (barycenterMatrix repS (Measure.map D.π μprep')).trace := by
    rw [barycenterMatrix_trace repS hrepS_unit hrepS_meas, barycenterMatrix_trace repS hrepS_unit hrepS_meas]
  have key := channel_traceDist_le (stinespringChannel U hU e₀ he₀) hS hS' htr
  refine le_of_eq_of_le (traceDist_congr _ _ ?_) key
  rw [traceRight_barycenter_flow D μprep Φ hΦ rep hrep_unit hrep_meas repS hrepS_meas U hU e₀ he₀
      hlift hprod,
    traceRight_barycenter_flow D μprep' Φ hΦ rep hrep_unit hrep_meas repS hrepS_meas U hU e₀ he₀
      hlift hprod']

variable {N : ℕ} [NeZero N]

/-- ★★ **The second law under de-isolation.** For a preparation on the system-plus-apparatus
sector, product with the apparatus ready in `a₀`, and an ontic flow lifting the von Neumann
coupling `vnUnitary N`, the entropy of the system's reduced density operator after the flow is at
least the entropy of the system's density operator before it. The reduced flowed state is the
de-isolation channel's output, which is the pointer-basis pinching
(`deisolationChannel_apply_eq_pinch`), and pinching does not decrease entropy (TH2). Full support
of the system state is TH2's hypothesis. -/
theorem vonNeumannEntropy_le_deisolation
    (μprep : Measure SigmaSpace) [IsProbabilityMeasure μprep]
    (Φ : SigmaSpace → SigmaSpace) (hΦ : Measurable Φ)
    (rep : P → EuclideanSpace ℂ (Fin N × Fin N)) (hrep_unit : ∀ p, ‖rep p‖ = 1)
    (hrep_meas : Measurable rep)
    (repS : P → EuclideanSpace ℂ (Fin N)) (hrepS_unit : ∀ p, ‖repS p‖ = 1)
    (hrepS_meas : Measurable repS)
    (hlift : IsUnitaryLift D Φ rep (vnUnitary N))
    (hprod : ∀ᵐ x ∂μprep, outerProduct (rep (D.π x))
      = outerProduct (repS (D.π x)) ⊗ₖ outerProduct (EuclideanSpace.single (0 : Fin N) (1 : ℂ)))
    (hpos : ∀ i, 0 < ((barycenterMatrix repS (Measure.map D.π μprep)) i i).re) :
    vonNeumannEntropy (barycenterMatrix_isHermitian repS (Measure.map D.π μprep))
      ≤ vonNeumannEntropy
          (barycenterMatrix_isHermitian rep (Measure.map D.π (Measure.map Φ μprep))).traceRight := by
  have h1 := isProbabilityMeasure_projectiveLaw D μprep
  have hred : Matrix.traceRight (barycenterMatrix rep (Measure.map D.π (Measure.map Φ μprep)))
      = pinch (barycenterMatrix repS (Measure.map D.π μprep)) := by
    rw [traceRight_barycenter_flow D μprep Φ hΦ rep hrep_unit hrep_meas repS hrepS_meas
      (vnUnitary N) vnUnitary_conjTranspose_mul _ (by rw [PiLp.norm_single]; exact norm_one) hlift hprod]
    exact deisolationChannel_apply_eq_pinch (barycenterMatrix_isHermitian repS _)
  rw [vonNeumannEntropy_congr_of_eq _ (pinch_isHermitian _) hred]
  exact vonNeumannEntropy_le_pinching (barycenterMatrix_posSemidef repS hrepS_unit hrepS_meas _)
    (barycenterMatrix_trace repS hrepS_unit hrepS_meas _) hpos

end Open

/-! ### Landauer on `Σ` -/

section LandauerSigma

variable {SigmaS SigmaE PS PE G : Type*}
  [MeasurableSpace SigmaS] [MeasurableSpace SigmaE] [Nonempty SigmaS] [Nonempty SigmaE]
  [MeasurableSpace PS] [MeasurableSpace PE]
  [Group G] [MulAction G (SigmaS × SigmaE)] [MulAction G (PS × PE)]
  [MulAction.IsPretransitive G (PS × PE)]
  {n e : Type*} [Fintype n] [Fintype e] [DecidableEq n] [DecidableEq e] [Nonempty e]

omit [DecidableEq n] [DecidableEq e] [Nonempty e] in
/-- The joint density operator of a flowed product preparation is `U (ρ_S ⊗ ρ_E) Uᴴ`. -/
theorem barycenter_flow_prod (D : SectorData (SigmaS × SigmaE) (PS × PE) G)
    (πS : SigmaS → PS) (πE : SigmaE → PE) (hπS : Measurable πS) (hπE : Measurable πE)
    (hπ : D.π = Prod.map πS πE)
    (μS : Measure SigmaS) [IsProbabilityMeasure μS] (μE : Measure SigmaE) [IsProbabilityMeasure μE]
    (Φ : SigmaS × SigmaE → SigmaS × SigmaE) (hΦ : Measurable Φ)
    (rep : PS × PE → EuclideanSpace ℂ (n × e)) (hrep_unit : ∀ p, ‖rep p‖ = 1)
    (hrep_meas : Measurable rep)
    (repS : PS → EuclideanSpace ℂ n) (repE : PE → EuclideanSpace ℂ e)
    (hprod : ∀ p q, outerProduct (rep (p, q)) = outerProduct (repS p) ⊗ₖ outerProduct (repE q))
    (U : Matrix (n × e) (n × e) ℂ) (hlift : IsUnitaryLift D Φ rep U) :
    barycenterMatrix rep (Measure.map D.π (Measure.map Φ (μS.prod μE)))
      = U * (barycenterMatrix repS (Measure.map πS μS) ⊗ₖ barycenterMatrix repE (Measure.map πE μE))
          * star U := by
  rw [Matrix.star_eq_conjTranspose, barycenter_flow D (μS.prod μE) Φ hΦ rep hrep_unit hrep_meas U hlift,
    hπ, ← Measure.map_prod_map μS μE hπS hπE, barycenterMatrix_prod rep repS repE hprod]

/-- ★★ **Landauer's principle on `Σ`.** A product preparation on a system-plus-bath sector whose
bath preparation has the Gibbs state at inverse temperature `β` as its density operator, evolved
by an ontic flow lifting the joint unitary `U`, obeys `S(ρ_S) − S(ρ_S') ≤ β · ΔQ`: the entropy
removed from the system preparation is bounded by `β` times the heat dumped into the bath
(`landauer_bound` with the flowed joint state supplied by `barycenter_flow_prod`). The full-rank
hypotheses are those of `landauer_bound`. -/
theorem landauer_flow (D : SectorData (SigmaS × SigmaE) (PS × PE) G)
    (πS : SigmaS → PS) (πE : SigmaE → PE) (hπS : Measurable πS) (hπE : Measurable πE)
    (hπ : D.π = Prod.map πS πE)
    (μS : Measure SigmaS) [IsProbabilityMeasure μS] (μE : Measure SigmaE) [IsProbabilityMeasure μE]
    (Φ : SigmaS × SigmaE → SigmaS × SigmaE) (hΦ : Measurable Φ)
    (rep : PS × PE → EuclideanSpace ℂ (n × e)) (hrep_unit : ∀ p, ‖rep p‖ = 1)
    (hrep_meas : Measurable rep)
    (repS : PS → EuclideanSpace ℂ n) (hrepS_unit : ∀ p, ‖repS p‖ = 1) (hrepS_meas : Measurable repS)
    (repE : PE → EuclideanSpace ℂ e)
    (hprod : ∀ p q, outerProduct (rep (p, q)) = outerProduct (repS p) ⊗ₖ outerProduct (repE q))
    (U : Matrix (n × e) (n × e) ℂ) (hU : Uᴴ * U = 1) (hlift : IsUnitaryLift D Φ rep U)
    (HB : Matrix e e ℂ) (hHB : HB.IsHermitian) {β : ℝ}
    (hgibbs : barycenterMatrix repE (Measure.map πE μE) = gibbsState HB hHB β)
    (hpdS : (barycenterMatrix repS (Measure.map πS μS)).PosDef)
    (hpdS' : (Matrix.traceRight
        (barycenterMatrix rep (Measure.map D.π (Measure.map Φ (μS.prod μE))))).PosDef)
    (hpdB' : (Matrix.traceLeft
        (barycenterMatrix rep (Measure.map D.π (Measure.map Φ (μS.prod μE))))).PosDef) :
    vonNeumannEntropy hpdS.1 - vonNeumannEntropy hpdS'.1
      ≤ β * (energy HB (Matrix.traceLeft
              (barycenterMatrix rep (Measure.map D.π (Measure.map Φ (μS.prod μE)))))
            - energy HB (gibbsState HB hHB β)) := by
  have hS : IsProbabilityMeasure (Measure.map πS μS) := Measure.isProbabilityMeasure_map' hπS.aemeasurable
  have hjoint := barycenter_flow_prod D πS πE hπS hπE hπ μS μE Φ hΦ rep hrep_unit hrep_meas repS repE
    hprod U hlift
  rw [hgibbs] at hjoint
  have hU' : star U * U = 1 := by rw [Matrix.star_eq_conjTranspose]; exact hU
  have htrS : (barycenterMatrix repS (Measure.map πS μS)).trace = 1 :=
    barycenterMatrix_trace repS hrepS_unit hrepS_meas _
  have hpdS'' : (partialTraceRight
      (U * (barycenterMatrix repS (Measure.map πS μS) ⊗ₖ gibbsState HB hHB β) * star U)).PosDef :=
    hjoint ▸ hpdS'
  have hpdB'' : (partialTraceLeft
      (U * (barycenterMatrix repS (Measure.map πS μS) ⊗ₖ gibbsState HB hHB β) * star U)).PosDef :=
    hjoint ▸ hpdB'
  have key := landauer_bound HB hHB hpdS htrS hU' hpdS'' hpdB''
  rw [vonNeumannEntropy_congr_of_eq hpdS'.1 hpdS''.1 (by rw [hjoint]; rfl), hjoint]
  exact key

end LandauerSigma

end Thermo
end CSD
