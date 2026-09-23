# Batch 008: evolving prepared trials and checking the measurement channel

Reviewer: Codex. Started: 2026-09-22. Completed: 2026-09-23. Baseline:
`7ba739232d72c8c27cee91d86e4001c415c310d7` plus the recorded local edits.
Batch 007 was committed and pushed to `origin/codex/corpus-review` at the user's request.
This batch remains local. `origin/main` has 40 commits absent from this review branch;
its integration is a separate validation task.

## Scope and result

| File under CsdLean4 | Review |
|---|---|
| LF5/MeasurementFlow.lean | Full code/comment review: finite-index reindexing, basis action, distinct projective basis rays, measurability, FS preservation and nonidentity for N > 1. Corrected the obsolete Fin-only rationale and stale entangled-consumer scope; Lean statements are unchanged. |
| LF5/FlowBornFrequency.lean | Full code/comment review: dilation normalization, pointer-block volume identities, base and fibred frequency statements, zero amplitudes, trial laws and independence. Existing proofs establish their statements. Added explicit initial-law transport and evolved-sample frequencies using the existing engine. |
| LF6/MeasurementFlowChannel.lean | Full code/comment review: joint-index lift, representative reindexing, reduced-channel identity, entropy assumptions and canonical-section instantiation. No invalid mathematical statement found. Corrected the section and entropy descriptions. |
| Thermo/SigmaSecondLaw.lean | Partial: inspected channel-as-pinching and the de-isolation entropy route and corrected three related support descriptions. Its other thermodynamic results are not counted as fully reviewed. |
| Tests/AxiomAudit/Dynamics.lean | Partial: added two axiom regression pins next to the existing fibred frequency pins. The rest of this audit file is not a full source review. |

Supporting inspections of DilationFromFlow, BasinFrequency, GlobalBasin,
Capstone, CapstoneCanonical, PointerOutcome, DecoherenceChannel, SecondLaw and the independent
coordinate-process API do not add full-review credit. Reading an imported theorem's interface
is not a fresh proof audit of its entire dependency cluster.

## CR-LF5-001: derive the law of explicitly evolved trials

The original frequency theorems sample either the ambient FS law with preparation-indexed
Born regions, or the post-preparation Dirac-times-Haar law with fixed global basins. Their
statements are valid. Naming the dilated vector in the latter did not itself say that each
trial was obtained by evolving an input sample. The inspected base capstones and pointer
outcome upgrade also assume their sampling law; they do not supply that fibred transport.

The new result is a specialization of the existing terminal frequency engine:

1. `epistemicMeasure_map_measurementFlow` proves
   `F_* (δ_p × Haar) = δ_(measurementFlow p) × Haar`, where
   `F(p, θ) = (measurementFlow p, θ)`.
2. `vnDilation_pointer_frequency_basin_after_flow` starts with trials having the law at
   the embedded input ray `[ψ ⊗ a₀]`. It proves the output law using the pushforward
   identity and `measurementFlow_realises_dilation`.
3. Pairwise independence of the input random variables implies pairwise independence
   of the evolved basin indicators, by measurable composition. The existing
   `vnDilation_pointer_frequency_basin` then supplies simultaneous pointer-block limits
   `|ψ_i|²` for the samples `F(X_k)`.

The new adapter assumes pairwise independence of the full input trials, which is stronger
than the old engine's per-cell indicator independence. The old engine and all its signatures
remain available. Neither independence of outcomes within one trial nor stationarity of the
prepared ray is assumed. The initial Dirac-times-Haar preparation law is still supplied;
ambient FS invariance alone would not identify that prepared law.

The construction includes zero amplitudes and works at N = 1, where no nonidentity claim is
made. Nonidentity is available for `1 < N`, as the existing measurement-flow theorem requires.
The auxiliary nonzero proofs are consistent with normalization; they witness the projective
constructors, rather than additional physical restrictions.

### What this closes, and what remains

This proves initial-to-output sampling transport for this concrete fibred lift. The basins
are fixed subsets of the joint arena; their rates depend on the base ray through momentContext.
The conclusion remains a sum of cell frequencies per pointer block. It does not yet connect
that event to a changed, persistent record register. Nor does it derive Haar preparation or
establish calibration for an arbitrary LF2 effect or arbitrary lifted flow.

CR-LF2-006 therefore remains open for record-event integration. The next inspection starts with existing
RecordLayer/Measurement and DrivenTwoTime interfaces and their concrete protocols. The latter
already defines `baseLift` as the same `Prod.map` and proves `basinIndex_pullback` and
`drivenJointRecordSector_eq`; use those interfaces before adding a new connection. The corpus already has record dynamics; this review does not claim
that such a connection is absent everywhere. General moving-singlet calibration remains
separate from this single-system basis measurement.

## CR-LF5-002: reindexing is an interface choice

The current staged FubiniStudy and UnitaryTransitive modules quantify over an arbitrary
finite index type. LF5 still reindexes to Fin m to match the downstream volume interfaces.
Corrected that distinction in MeasurementFlow and MeasurementFlowChannel, qualified the
nonidentity claim with N > 1, and replaced stale entangled-work deferral with the existing
SingletDeisolationFlow consumer. No wider index refactor is needed for these valid proofs.

## CR-LF6-001: exact channel and entropy scope

The LF6 reduced-state identity uses a measurable ontic flow whose projection is measurementFlow,
a measurable unit section of the joint ray map, and an almost-everywhere product projector
with the ready apparatus. The canonical-section version discharges only the representative
hypotheses. It still requires the flow projection and product preparation. Clarified that
scope and the distinction from abstract `fromPreparation`, which does not demand a section.

The entropy theorem's `hpos` says that every diagonal entry of the initial system barycentre
in the measurement basis is strictly positive. It does not assert full rank of that matrix.
For example, the matrix with all four entries equal to 1/2 has positive diagonal, trace one
and determinant zero. The proof passes hpos to positivity of the *pinched* state in TH2's
Klein-inequality argument. Corrected the LF6 wording and its SigmaSecondLaw source comments.
The SecondLaw source already describes positive pointer weights accurately. No entropy
hypothesis was removed and no stronger entropy result is claimed.

The channel-as-pinching identity also confirms why fixed computational-basis weights are
preserved by this channel. This is specific to the measurement basis and does not assert
that all fixed-effect probabilities are invariant under all unitaries.

## Next-file finding: CR-RECORD-003

A targeted inspection found that `Measurement.outcome` describes its missing-outcome set as
null for an arbitrary `FibreContext`. That structure requires nonnegative rates but does not
require their sum to be one; all-zero rates leave every outcome cell empty. Its normalized
Born specialization has a valid separate almost-everywhere coverage theorem. Follow this
through the real-fibre measurement API and its broader description of a selector as a
measurement interaction. This is queued for the next batch, not full-review credit here.

## Validation

- Passed final focused build: `lake build --wfail CsdLean4.LF5.PointerOutcome CsdLean4.LF6.MeasurementFlowChannel CsdLean4.LF6.SingletDeisolationFlow` (3336 jobs). This includes all three fully reviewed modules and SigmaSecondLaw.
- Passed eight relevant guards: doc-promises, category-tags, claims, semantic-mutations, references, import-hygiene, residues and mathlib-absence. The last reports one existing untagged availability claim elsewhere as an advisory warning.
- Passed all three examples below: a positive-diagonal singular matrix, N = 2 nonidentity, and the evolved frequency theorem with the entire sampling bundle supplied by independent coordinates.
- Passed both new guarded axiom pins and both LF6 axiom checks below: only propext, Classical.choice and Quot.sound. The new Dynamics pins were checked in isolation with the same text; the full umbrella audit target was not run.
- Review-register consistency and Git whitespace checked at completion.

Initial proof attempts needed the existing indicator-composition lemma. Standalone examples
needed explicit sampling-law types and matrix notation; one run timed out and one encountered
a missing object during rebuilding. The final run after the build passed. No new axiom or sorry
is added. Full `CsdLean4`, `CsdLeanTests`, the complete axiom audit and all blocking CI checks
remain required before integration with main.

## Coverage

35 of 691 tracked Lean files fully reviewed (5.07%), with two
partial entries in this batch. Supporting inspections are not counted. The targeted review
sample still does not justify a corpus-wide defect-rate or effort forecast; the stratified
30-file pilot remains pending.

## Reproducible checks

Run the following with `lake env lean --stdin` after building the reviewed modules. The two
new guarded axiom outputs are also checked into Tests/AxiomAudit/Dynamics.lean.

```lean
import CsdLean4.LF5.FlowBornFrequency
import CsdLean4.LF6.MeasurementFlowChannel
import CsdLean4.Mathlib.Probability.IIDCoordinateProcess
open CSD CSD.LF2 CSD.LF4 CSD.LF5 MeasureTheory ProbabilityTheory Filter Matrix
open scoped LinearAlgebra.Projectivization
variable {N : ℕ} [NeZero N]

-- Positive diagonal entries do not imply invertibility.
example :
    let ρ : Matrix (Fin 2) (Fin 2) ℂ := !![1/2, 1/2; 1/2, 1/2]
    (∀ i, 0 < (ρ i i).re) ∧ ρ.trace = 1 ∧ ρ.det = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  · norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  · norm_num [Matrix.det_fin_two]

-- Nontrivial dynamics is available at N = 2.
example : measurementFlow 2 finProdFinEquiv ≠ id :=
  measurementFlow_ne_id (by decide) finProdFinEquiv

-- Discharge the new theorem's entire trial bundle using independent input coordinates.
example {M : ℕ}
    (ψ : EuclideanSpace ℂ (Fin N)) (hψ : ‖ψ‖ = 1) (hψ0 : ψ ≠ 0)
    (e : (Fin N × Fin N) ≃ Fin (M + 1))
    (ψ' : EuclideanSpace ℂ (Fin (M + 1)))
    (hψ'eq : ψ' = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanLin (vnDilationV N) ψ))
    (hψ'0 : ψ' ≠ 0) :
    let μ := CSD.RecordLayer.epistemicMeasure (Projectivization.mk ℂ
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e)
        (Matrix.toEuclideanLin (embedGround N) ψ))
      (piLpCongrLeft_embedGround_ne_zero e ψ hψ0))
    ∀ᵐ ω ∂ (Measure.infinitePi fun _ : ℕ => μ), ∀ i : Fin N,
      Tendsto
        (fun m : ℕ =>
          ∑ n : Fin N,
            (∑ k ∈ Finset.range m,
                Set.indicator
                  ((Prod.map (measurementFlow N e) id ∘ (fun ω : ℕ → KSigma (M + 1) => ω k)) ⁻¹' CSD.RecordLayer.globalBasin
                    (CSD.RecordLayer.momentContext (M + 1)) (e (n, i)))
                  (fun _ => (1 : ℝ)) ω)
              / (m : ℝ))
        atTop
        (nhds (‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2)) := by
  let μ : Measure (KSigma (M + 1)) :=
    CSD.RecordLayer.epistemicMeasure (Projectivization.mk ℂ
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e)
        (Matrix.toEuclideanLin (embedGround N) ψ))
      (piLpCongrLeft_embedGround_ne_zero e ψ hψ0))
  change ∀ᵐ ω ∂ (Measure.infinitePi fun _ : ℕ => μ), _
  exact vnDilation_pointer_frequency_basin_after_flow ψ hψ hψ0 e ψ' hψ'eq hψ'0
    (Ω := ℕ → KSigma (M + 1)) (Pr := Measure.infinitePi fun _ : ℕ => μ)
    (fun n (ω : ℕ → KSigma (M + 1)) => ω n) (fun n => measurable_pi_apply n)
    (fun n => Measure.infinitePi_map_eval (fun _ : ℕ => μ) n)
    (fun _ _ hab => (iIndepFun_eval_infinitePi μ).indepFun hab)

/-- info: 'CSD.LF5.epistemicMeasure_map_measurementFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.epistemicMeasure_map_measurementFlow
/-- info: 'CSD.LF5.vnDilation_pointer_frequency_basin_after_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.vnDilation_pointer_frequency_basin_after_flow
#print axioms CSD.LF6.measurementFlow_traceRight_barycenter
#print axioms CSD.LF6.measurementFlow_vonNeumannEntropy_le
```
