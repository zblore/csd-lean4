import CsdLean4.LF1.MainTheorem
import CsdLean4.LF1.GeneralFrequency
import CsdLean4.Mathlib.Analysis.Matrix.OperatorConvex
import CsdLean4.Mathlib.Analysis.Matrix.OperatorConvexBridge
import CsdLean4.Mathlib.Analysis.Matrix.StoneC1
import CsdLean4.LF2.BornWrapper
import CsdLean4.LF2.ReducedDensity
import CsdLean4.Mathlib.MeasureTheory.LintegralFintypeProd
import CsdLean4.Mathlib.QuantumInfo.Channel
import CsdLean4.Mathlib.QuantumInfo.Stinespring
import CsdLean4.Mathlib.QuantumInfo.CanonicalChannels
import CsdLean4.Mathlib.QuantumInfo.TraceDistance
import CsdLean4.Mathlib.QuantumInfo.DataProcessing
import CsdLean4.Mathlib.QuantumInfo.Entropy
import CsdLean4.Mathlib.QuantumInfo.PartialTrace
import CsdLean4.Mathlib.QuantumInfo.Subadditivity
import CsdLean4.Mathlib.QuantumInfo.StrongSubadditivity
import CsdLean4.Mathlib.QuantumInfo.Register
import CsdLean4.Mathlib.QuantumInfo.Hadamard
import CsdLean4.Mathlib.QuantumInfo.Fourier
import CsdLean4.Mathlib.QuantumInfo.Reversible.Circuit
import CsdLean4.Mathlib.QuantumInfo.Reversible.Cost
import CsdLean4.Mathlib.QuantumInfo.Reversible.ConstProp
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModAdd
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModMul
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModInv
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModReduce
import CsdLean4.Mathlib.QuantumInfo.Reversible.CtrlAdd
import CsdLean4.Mathlib.QuantumInfo.Reversible.CtrlMul
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModReduceCtrl
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularAdd
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularAddCtrl
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularDouble
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularMul
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularMulLoop
import CsdLean4.Mathlib.QuantumInfo.Reversible.VerifiedAdder
import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularSub
import CsdLean4.Mathlib.QuantumInfo.Reversible.Eval
import CsdLean4.Mathlib.QuantumInfo.Reversible.Depth
import CsdLean4.Mathlib.QuantumInfo.Reversible.ProgramRouter
import CsdLean4.Mathlib.QuantumInfo.Reversible.ProgramRouterDoubling
import CsdLean4.Mathlib.QuantumInfo.Reversible.DoublingAssembly
import CsdLean4.Mathlib.QuantumInfo.Reversible.DoublingAssemblyOps
import CsdLean4.Mathlib.QuantumInfo.Reversible.CuccaroAdd
import CsdLean4.Mathlib.QuantumInfo.Reversible.CuccaroModAdd
import CsdLean4.Mathlib.QuantumInfo.Reversible.CuccaroModMul
import CsdLean4.Mathlib.QuantumInfo.Reversible.VerifiedAdderCarryClean
import CsdLean4.Mathlib.QuantumInfo.Reversible.AndAdd
import CsdLean4.Mathlib.QuantumInfo.Reversible.GidneyAdder
import CsdLean4.Mathlib.QuantumInfo.ECDLP.EllipticCurve
import CsdLean4.Mathlib.QuantumInfo.ECDLP.ScalarMul
import CsdLean4.Mathlib.QuantumInfo.ECDLP.Secp256k1
import CsdLean4.Mathlib.QuantumInfo.ECDLP.ResourceBounds
import CsdLean4.Mathlib.QuantumInfo.ECDLP.Inversion
import CsdLean4.Mathlib.QuantumInfo.ECDLP.PointDouble
import CsdLean4.Mathlib.QuantumInfo.ECDLP.PointAdd
import CsdLean4.Mathlib.QuantumInfo.ECDLP.PointAddBenchmark
import CsdLean4.Mathlib.QuantumInfo.ECDLP.SafegcdInversion
import CsdLean4.Mathlib.QuantumInfo.ECDLP.KaratsubaMul
import CsdLean4.Mathlib.QuantumInfo.ECDLP.HalfGcdInversion
import CsdLean4.Mathlib.QuantumInfo.ECDLP.TwoTrack
import CsdLean4.Mathlib.QuantumInfo.ECDLP.ThreeTrackScore
import CsdLean4.Mathlib.QuantumInfo.ECDLP.TrustedEstimate
import CsdLean4.Mathlib.QuantumInfo.ECDLP.SafegcdDivstep
import CsdLean4.Mathlib.QuantumInfo.ECDLP.SafegcdDivstepCircuit
import CsdLean4.Empirical.QM.MeasurementUncompute
import CsdLean4.Empirical.QM.MeasurementUncomputeLift
import CsdLean4.Empirical.QM.MeasurementAdder
import CsdLean4.Empirical.QM.MeasurementGidneyAdder
import CsdLean4.Empirical.QM.MeasurementAdderHierarchy
import CsdLean4.CV.ApproxCCR
import CsdLean4.CV.Position
import CsdLean4.CV.Oscillator
import CsdLean4.CV.OscillatorSpectrum
import CsdLean4.Thermo.CanonicalTypicality
import CsdLean4.Thermo.SecondLaw
import CsdLean4.Thermo.FreeEnergy
import CsdLean4.Thermo.Landauer
import CsdLean4.LF2.Interface
import CsdLean4.LF2.Preparation
import CsdLean4.LF3.Interface
import CsdLean4.LF3.PurePreparation
import CsdLean4.LF3.SingletProjective
import CsdLean4.LF3.Singlet.JointProjector
import CsdLean4.LF3.Singlet.JointEig
import CsdLean4.LF3.Projectors.TensorModel
import CsdLean4.LF4.Instance
import CsdLean4.LF4.KahlerInstance
import CsdLean4.LF4.KahlerFlow
import CsdLean4.LF4.KahlerOnticSetup
import CsdLean4.LF4.NonTrivialSetup
import CsdLean4.LF4.RotationSchrodinger
import CsdLean4.LF4.BothPillars
import CsdLean4.LF4.ManyToOnePillars
import CsdLean4.LF4.UnitarySelection
import CsdLean4.LF4.BargmannSelection
import CsdLean4.LF4.ProjectedDynamics
import CsdLean4.LF4.PhaseLift
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.PhaseRigidity
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Bargmann
import CsdLean4.LF4.MomentMap
import CsdLean4.LF4.ObservableFlow
import CsdLean4.LF4.TypicalityForcing
import CsdLean4.LF4.BornVolume
import CsdLean4.LF4.MomentPushforward
import CsdLean4.LF4.BornFS
import CsdLean4.LF4.QubitBornFrequency
import CsdLean4.LF4.BornFrequencyPartition
import CsdLean4.LF4.MomentMarginal
import CsdLean4.LF4.DuistermaatHeckman
import CsdLean4.LF4.GaussianFS
import CsdLean4.LF4.GaussianCP
import CsdLean4.LF4.GaussianCPN
import CsdLean4.LF4.MomentMarginalUniform
import CsdLean4.LF4.MomentRatioUniform
import CsdLean4.LF4.MomentRatioUniformN
import CsdLean4.LF4.MomentUniform
import CsdLean4.LF4.MomentBridgeN
import CsdLean4.LF4.MomentDirichletN
import CsdLean4.LF4.MomentBornN
import CsdLean4.LF4.BornFrequencyN
import CsdLean4.LF4.QubitConsistency
import CsdLean4.Mathlib.MeasureTheory.PiCurry
import CsdLean4.LF4.SingletKahler
import CsdLean4.LF4.SingletKahlerFlow
import CsdLean4.LF4.KahlerWignerLift
import CsdLean4.LF4.KahlerVolumeForced
import CsdLean4.LF4.SchrodingerKahlerInvariance
import CsdLean4.LF4.SingleQubitKahler
import CsdLean4.LF4.SingletObservables
import CsdLean4.LF4.HardyKahler
import CsdLean4.LF4.SpectralExpansion
import CsdLean4.LF4.SpectralCarving
import CsdLean4.LF4.SpectralVariance
import CsdLean4.LF4.UncertaintyKahler
import CsdLean4.LF4.PauliRobertson
import CsdLean4.LF4.PauliDotRobertson
import CsdLean4.LF4.OnticBorn
import CsdLean4.LF2.POVM
import CsdLean4.LF2.EffectAux
import CsdLean4.LF4.POVMDilation
import CsdLean4.LF4.POVMVolume
import CsdLean4.LF4.BornFlowLinkage
import CsdLean4.LF4.POVMNaimark
import CsdLean4.LF4.BornRegionUncond
import CsdLean4.LF4.TrialWitness
import CsdLean4.LF5.VonNeumannUnitary
import CsdLean4.LF5.MeasurementFlow
import CsdLean4.LF5.DilationFromFlow
import CsdLean4.LF5.FlowBornFrequency
import CsdLean4.LF5.Capstone
import CsdLean4.LF5.CapstoneCanonical
import CsdLean4.LF5.PointerOutcome
import CsdLean4.LF5.SyndromeFlow
import CsdLean4.LF5.SyndromeOutcome
import CsdLean4.LF6.ForcedContextuality
import CsdLean4.LF6.GHZContextuality
import CsdLean4.LF6.SingletDeisolationFlow
import CsdLean4.LF6.GHZDeisolationFlow
import CsdLean4.LF6.GHZMerminCarve
import CsdLean4.LF6.LocalDeisolationFlow
import CsdLean4.LF6.GHZLocalFlow
import CsdLean4.LF6.Decoherence
import CsdLean4.LF6.MaxEntangledDeisolationFlow
import CsdLean4.LF6.PartialSchmidtCorrelation
import CsdLean4.LF6.DephasingSemigroup
import CsdLean4.LF6.AmplitudeDamping
import CsdLean4.LF6.CGLMPQutrit
import CsdLean4.LF6.CGLMPQudit
import CsdLean4.LF6.MaxEntangledCGLMPCapstone
import CsdLean4.LF6.GHZnDeisolationFlow
import CsdLean4.Empirical.QM.Bell
import CsdLean4.Empirical.QM.NoCloning
import CsdLean4.Empirical.QM.NoDeleting
import CsdLean4.Empirical.QM.Resources.SuperdenseCoding
import CsdLean4.Empirical.QM.Resources.Teleportation
import CsdLean4.Empirical.QM.NoCommunication
import CsdLean4.Empirical.QM.NoBroadcasting
import CsdLean4.Empirical.QM.Protocols.Basic
import CsdLean4.Empirical.QM.Crypto.QuantumMoney
import CsdLean4.Empirical.QM.Crypto.E91
import CsdLean4.Empirical.QM.Crypto.E91KeyRate
import CsdLean4.Empirical.QM.Crypto.E91FiniteKey
import CsdLean4.Empirical.QM.Crypto.WiesnerProtocol
import CsdLean4.Empirical.QM.USD
import CsdLean4.Empirical.QM.QEC.ThreeQubit
import CsdLean4.Empirical.QM.QEC.PhaseFlip
import CsdLean4.Empirical.QM.QEC.BitFlipChannel
import CsdLean4.Empirical.QM.Uncertainty
import CsdLean4.Empirical.QM.Multipartite.GHZ
import CsdLean4.Empirical.QM.Contextuality.KS18
import CsdLean4.Empirical.QM.Contextuality.MerminPeres
import CsdLean4.Empirical.QM.Hardy
import CsdLean4.Empirical.QM.SternGerlach
import CsdLean4.Empirical.QM.Malus
import CsdLean4.Empirical.QM.Algorithms.DeutschJozsa
import CsdLean4.Empirical.QM.Algorithms.Simon
import CsdLean4.Empirical.QM.Algorithms.SwapTest
import CsdLean4.Empirical.QM.Algorithms.HadamardTest
import CsdLean4.Empirical.QM.Algorithms.BernsteinVazirani
import CsdLean4.Empirical.QM.Algorithms.Grover
import CsdLean4.Empirical.QM.Algorithms.ShorCore
import CsdLean4.Empirical.QM.Algorithms.ShorRecovery
import CsdLean4.Empirical.QM.Algorithms.ShorRandomA
import CsdLean4.Empirical.QM.Algorithms.ShorCapstone
import CsdLean4.Empirical.CSD.Framework
import CsdLean4.Empirical.CSD.Bell
import CsdLean4.Empirical.CSD.NoCloning
import CsdLean4.Empirical.CSD.NoDeleting
import CsdLean4.Empirical.CSD.NoBroadcasting
import CsdLean4.Empirical.CSD.NoCommunication
import CsdLean4.Empirical.CSD.Uncertainty
import CsdLean4.Empirical.CSD.SternGerlach
import CsdLean4.Empirical.CSD.SternGerlachVolume
import CsdLean4.Empirical.CSD.MalusVolume
import CsdLean4.Empirical.Metrology.Ramsey
import CsdLean4.Empirical.Metrology.QuantumFisher
import CsdLean4.Empirical.Metrology.Heisenberg
import CsdLean4.Empirical.CSD.BellVolume
import CsdLean4.Empirical.CSD.GHZVolume
import CsdLean4.Empirical.CSD.HardyVolume
import CsdLean4.Empirical.CSD.ContextVolume
import CsdLean4.Empirical.CSD.UncertaintyVolume
import CsdLean4.Empirical.CSD.TrineVolume
import CsdLean4.Empirical.CSD.USDVolume
import CsdLean4.Empirical.CSD.SICVolume
import CsdLean4.Empirical.CSD.WeakMeasurement
import CsdLean4.Empirical.CSD.QuantumZeno
import CsdLean4.Empirical.CSD.QutritPOVMVolume
import CsdLean4.Empirical.CSD.SIC3Volume
import CsdLean4.Empirical.CSD.MUB3Volume
import CsdLean4.Empirical.CSD.VolumeCanonical
import CsdLean4.Empirical.CSD.Resources.SuperdenseCoding
import CsdLean4.Empirical.CSD.Resources.Teleportation
import CsdLean4.Empirical.CSD.Crypto.QuantumMoney
import CsdLean4.Empirical.CSD.Crypto.E91
import CsdLean4.Empirical.CSD.QEC.ThreeQubit
import CsdLean4.Empirical.CSD.Contextuality.MerminPeres
import CsdLean4.Empirical.CSD.Hardy
import CsdLean4.Empirical.CSD.Contextuality.KS18
import CsdLean4.Empirical.CSD.Contextuality.KS18Volume
import CsdLean4.Empirical.CSD.Contextuality.MerminPeresVolume
import CsdLean4.Empirical.CSD.Multipartite.GHZ
import CsdLean4.Empirical.CSD.Einselection
import CsdLean4.Empirical.CSD.QECDecoherence
import CsdLean4.Empirical.CSD.ChannelCapacity
import CsdLean4.Empirical.QM.Gates.SingleQubit
import CsdLean4.Empirical.QM.Gates.TwoQubit
import CsdLean4.Empirical.QM.Gates.BellPrep
import CsdLean4.Empirical.QM.Gates.MultiQubit
import CsdLean4.Empirical.CSD.Gates.Framework
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Topology
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.MeasureSpace
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Unitary
import CsdLean4.Mathlib.LinearAlgebra.Matrix.UnitaryCompact
import CsdLean4.Mathlib.LinearAlgebra.Matrix.UnitaryHaar
import CsdLean4.Mathlib.Analysis.InnerProductSpace.KahlerForm
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudy
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitaryTransitive
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudyUnique
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.TransitionProbability
import CsdLean4.Mathlib.LinearAlgebra.Projectivization.WignerRigidity
import CsdLean4.Empirical.CSD.Gates.WignerDischarge
import CsdLean4.Mathlib.Probability.CGLMP
import CsdLean4.FND.Adapters
import CsdLean4.FND.ForwardCapstone
import CsdLean4.FND.LiftedMeasurement
import CsdLean4.FND.UnifiedMeasurement
import CsdLean4.FND.ConditioningLink
import CsdLean4.FND.PostMeasurement
import CsdLean4.FND.TimeIndexedRecord
import CsdLean4.FND.CompositeAdapters
import CsdLean4.FND.BellGenerality
import CsdLean4.FND.TensorGeneration
import CsdLean4.FND.TensorSolved
import CsdLean4.FND.TensorReconstruction
import CsdLean4.FND.LocalisedTypicality
import CsdLean4.FND.A5NoGo
import CsdLean4.FND.Interference
import CsdLean4.FND.TensorSector
import CsdLean4.FND.Luders
import CsdLean4.FND.ConditionalUpdate
import CsdLean4.FND.MixedState

/-!
# Axiom regression suite

**Category:** Special (cross-layer axiom-posture regression for all headline theorems).

`#guard_msgs` + `#print axioms` for every theorem in `AXIOMS.md §5`. Build
fails on regression: if any theorem acquires (or sheds) an axiom, the
expected `info:` string no longer matches `#print axioms`'s output, and
this module fails to compile.

The intent is **not** to forbid axiom changes; legitimate changes are
welcome and require updating both this module and `AXIOMS.md §5` in the
same commit. The intent is to make axiom drift impossible without an
explicit, visible diff.

## How to update

When discharging an axiom (e.g., LF4 proves `rankOneDensity_unique_of_certainty`)
or introducing a new one, update the `/-- info: ... -/` line above the
corresponding `#print axioms` to match the new output, in lockstep with
the corresponding `AXIOMS.md §5` row.
-/

namespace CSD.Tests.AxiomAudit

open CSD CSD.LF1 CSD.LF1.OnticSetup CSD.LF2 CSD.LF3

/-! ### LF1 -/

/-- info: 'CSD.LF1.OnticSetup.LF1_main_theorem_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF1_main_theorem_ae

/-- info: 'CSD.LF1.freq_tendsto_of_iid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF1.freq_tendsto_of_iid

/-! ### LF2 -/

/-- info: 'CSD.LF2.LF1_main_theorem_projective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF1_main_theorem_projective

/-- info: 'CSD.LF2.lf1_weight_eq_projective_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lf1_weight_eq_projective_weight

/-- info: 'CSD.LF2.SectorData.outcomeOfProjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SectorData.outcomeOfProjective

/-- info: 'CSD.LF2.SectorData.outcomeOfProjective_preEvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SectorData.outcomeOfProjective_preEvent

/--
info: 'CSD.LF2.SectorData.outcomeOfProjective_weight_eq_projectiveWeight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms SectorData.outcomeOfProjective_weight_eq_projectiveWeight

-- (The abstract `measure_bridge` + the `invariant_measure_uniqueness` axiom it carried
-- were removed 2026-06-04; the bridge holds axiom-free on the concrete instances —
-- `cp_measure_bridge` / `k_measure_bridge`, pinned below. Only `busch_effect_gleason`
-- remains as an imported axiom.)
/-- info: 'CSD.LF2.born_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms born_quadratic

-- Partial trace (Cat-1 Mathlib staging) + the reduced density operator (LF2).
-- traceRight/traceLeft trace out a tensor factor; the API (kronecker defining
-- property, trace-preservation, Hermitian/PSD preservation) sends a density
-- operator to its reduced density operator. Foundational triple. Unblocks E3b/E2.
/-- info: 'Matrix.traceRight_kronecker' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Matrix.traceRight_kronecker

/-- info: 'Matrix.trace_traceRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.trace_traceRight

/-- info: 'Matrix.PosSemidef.traceRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.PosSemidef.traceRight

/-- info: 'CSD.LF2.DensityOperatorIx.reduced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.LF2.DensityOperatorIx.reduced

-- Quantum channels in Kraus form (Cat-1 Mathlib staging; phase C1 of
-- specs/channels-plan.md). The action is trace-preserving (apply_trace),
-- PSD-preserving (apply_posSemidef), and Hermiticity-preserving — so a channel
-- sends density operators to density operators. Foundational triple. On-ramp to Φ≠id.
/-- info: 'QuantumInfo.Channel.apply_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.Channel.apply_trace

/-- info: 'QuantumInfo.Channel.apply_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.Channel.apply_posSemidef

/-- info: 'QuantumInfo.Channel.apply_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.Channel.apply_isHermitian

-- Stinespring dilation (Cat-1 staging; phase C2 of specs/channels-plan.md). The
-- Kraus ↔ Stinespring bridge: every channel's stacked-Kraus matrix is an isometry
-- (stinespringIsom_isom) whose dilate-then-trace action is the Kraus action
-- (apply_eq_traceRight_stinespring), and conversely the env-blocks of an isometry
-- form a channel (ofIsometry_apply). The on-ramp to Φ≠id. Foundational triple.
/-- info: 'QuantumInfo.Channel.stinespringIsom_isom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.Channel.stinespringIsom_isom

/-- info: 'QuantumInfo.Channel.apply_eq_traceRight_stinespring' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.Channel.apply_eq_traceRight_stinespring

/-- info: 'QuantumInfo.Channel.ofIsometry_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.Channel.ofIsometry_apply

-- Canonical channels (Cat-1 staging; phase C3 of specs/channels-plan.md). The
-- unitary channel (ρ ↦ UρUᴴ), the trace-out channel (ρ ↦ traceRight ρ, the literal
-- discard-the-environment from C2's ofIsometry 1), and the mixed-unitary channel
-- (ρ ↦ ∑ᵢ pᵢ • Uᵢ ρ Uᵢᴴ, the dephasing/depolarizing/bit-flip generaliser).
-- Foundational triple.
/-- info: 'QuantumInfo.Channel.unitaryChannel_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.Channel.unitaryChannel_apply

/-- info: 'QuantumInfo.Channel.traceOutChannel_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.Channel.traceOutChannel_apply

/-- info: 'QuantumInfo.Channel.mixedUnitaryChannel_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms QuantumInfo.Channel.mixedUnitaryChannel_apply

-- General-N DH Slice D.5a: Tonelli for a product over a finite index (lintegral).
-- ∫⁻ ∏ᵢ fᵢ(xᵢ) ∂(pi μ) = ∏ᵢ ∫⁻ fᵢ ∂μᵢ — the lintegral analogue of the Bochner
-- integral_fintype_prod_eq_prod (Mathlib has only the Bochner version). Cat-1
-- staging; needed for the pi-withDensity bridge (D.5b). Foundational triple.
/-- info: 'MeasureTheory.lintegral_fin_nat_prod_eq_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MeasureTheory.lintegral_fin_nat_prod_eq_prod

/-- info: 'MeasureTheory.lintegral_fintype_prod_eq_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MeasureTheory.lintegral_fintype_prod_eq_prod

-- General-N DH Slice D.5b: the pi-withDensity bridge. Measure.pi (μ.withDensity gᵢ)
-- = (Measure.pi μ).withDensity (∏ gᵢ) — the pi analogue of prod_withDensity (absent
-- from Mathlib), via Measure.pi_eq on rectangles + D.5a. Foundational triple.
/-- info: 'MeasureTheory.pi_withDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MeasureTheory.pi_withDensity

/-- info: 'CSD.LF2.pure_state_born_weights' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pure_state_born_weights

/--
info: 'CSD.LF2.pure_state_born_weights_of_certainty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 busch_effect_gleason]
-/
#guard_msgs in #print axioms pure_state_born_weights_of_certainty

/-- info: 'CSD.LF2.PurePreparation.OP_certain_at_ψ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PurePreparation.OP_certain_at_ψ

/-- info: 'CSD.LF2.PurePreparation.born_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, busch_effect_gleason] -/
#guard_msgs in #print axioms PurePreparation.born_rank_one

/-- info: 'CSD.LF2.PurePreparation.born_rank_one_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PurePreparation.born_rank_one_direct

/-! ### LF3 -/

/-- info: 'CSD.LF3.LF3_main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF3_main_theorem

/-- info: 'CSD.LF3.LF3_finite_leakage_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF3_finite_leakage_theorem

-- Re-routed off Busch (2026-06-02): the chain bridge now goes through the
-- foundational-triple `weight_eq_P_st` → `OP_p_at_jointEig_eq_P_st_direct` (the
-- ontic-stratum, volume-ratio Born step). All six capstones are now
-- foundational-triple-only; the Busch-mediated `OP_p_at_jointEig_eq_P_st` stays as
-- the operational-stratum statement. See AXIOMS.md §2.4.
/-- info: 'CSD.LF3.LF3_singlet_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF3_singlet_frequency_convergence

/-- info: 'CSD.LF3.LF3_singlet_frequency_convergence_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF3_singlet_frequency_convergence_born

/-- info: 'CSD.LF3.LF3_singlet_frequency_convergence_born_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF3_singlet_frequency_convergence_born_inner

/-- info: 'CSD.LF3.LF3_singlet_frequency_convergence_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF3_singlet_frequency_convergence_joint

/-- info: 'CSD.LF3.LF3_singlet_frequency_convergence_born_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF3_singlet_frequency_convergence_born_joint

/-- info: 'CSD.LF3.LF3_singlet_frequency_convergence_born_inner_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LF3_singlet_frequency_convergence_born_inner_joint

/-- info: 'CSD.LF3.PureSingletPreparation.ofHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PureSingletPreparation.ofHypothesis

-- The genuine joint-spin-projector Born identity (LF4 §3 groundwork):
-- ⟨ψ⁻ | Πˢ(a)⊗Πᵗ(b) | ψ⁻⟩ = P_st. Pure matrix algebra, foundational triple only.
/-- info: 'CSD.LF3.singlet_jointSpinProj_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms singlet_jointSpinProj_expectation

-- The Born identity for the GENUINE joint spin eigenstate (LF4-todo §3 discharged):
-- ‖⟨ψ⁻, singletJointEig s t⟩‖² = P_st, with singletJointEig the actual normalised
-- projection of the singlet onto the sector. Foundational triple only.
/-- info: 'CSD.LF3.singletJointEig_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms singletJointEig_born

/-- info: 'CSD.LF3.PureSingletPreparation.weight_eq_P_st' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PureSingletPreparation.weight_eq_P_st

/-- info: 'CSD.LF3.ProjectorAlgebra.ofTensorEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ProjectorAlgebra.ofTensorEmbedding

/--
info: 'CSD.LF3.MeasurementJointEig.singletProjectiveOutcome_measurable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms MeasurementJointEig.singletProjectiveOutcome_measurable

/--
info: 'CSD.LF3.MeasurementJointEig.singletProjectiveOutcome_disjoint_distinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms MeasurementJointEig.singletProjectiveOutcome_disjoint_distinct

/-- info: 'CSD.LF3.OP_p_at_jointEig_eq_P_st' depends on axioms: [propext, Classical.choice, Quot.sound, busch_effect_gleason] -/
#guard_msgs in #print axioms OP_p_at_jointEig_eq_P_st

/-- info: 'CSD.LF3.OP_p_at_jointEig_eq_P_st_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms OP_p_at_jointEig_eq_P_st_direct

/-- info: 'CSD.LF3.MeasurementUnitary.ofUnitaryTensorEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MeasurementUnitary.ofUnitaryTensorEmbedding

/-! ### Empirical predictions (Bell family, Phase A1-A5)

All Phase A1-A5 predictions cite only the foundational triple: the LF3
content they re-export does too (LF3 algebraic core in `Singlet/Kernel.lean`
is axiom-clean), and the new CHSH-at-Tsirelson computation is pure
arithmetic. -/

/-- info: 'CSD.Empirical.Bell.correlation_eq_neg_dot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.correlation_eq_neg_dot

/-- info: 'CSD.Empirical.Bell.no_signalling_alice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.no_signalling_alice

/-- info: 'CSD.Empirical.Bell.no_signalling_bob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.no_signalling_bob

/-- info: 'CSD.Empirical.Bell.singlet_marginal_alice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.singlet_marginal_alice

/-- info: 'CSD.Empirical.Bell.singlet_marginal_bob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.singlet_marginal_bob

/-- info: 'CSD.Empirical.Bell.chsh_classical_bound_violated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.chsh_classical_bound_violated

/-- info: 'CSD.Empirical.Bell.chsh_singlet_at_optimal_angles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.chsh_singlet_at_optimal_angles

/-- info: 'CSD.Empirical.Bell.chsh_singlet_tsirelson_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.chsh_singlet_tsirelson_bound

/-- info: 'CSD.Empirical.Bell.chsh_inner_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.chsh_inner_bound

/-- info: 'CSD.Empirical.Bell.chsh_qm_tsirelson_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Bell.chsh_qm_tsirelson_bound

/-! ### Empirical predictions (no-cloning, Phase B2) -/

/-- info: 'CSD.Empirical.NoCloning.no_cloning_two_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.NoCloning.no_cloning_two_state

/-- info: 'CSD.Empirical.NoCloning.no_universal_cloner_of_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.NoCloning.no_universal_cloner_of_witness

/-- info: 'CSD.Empirical.NoDeleting.no_deleting_two_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.NoDeleting.no_deleting_two_state

/-- info: 'CSD.Empirical.NoDeleting.no_universal_deleter_of_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.NoDeleting.no_universal_deleter_of_witness

/-- info: 'CSD.Empirical.QM.SuperdenseCoding.encode_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.SuperdenseCoding.encode_X

/-- info: 'CSD.Empirical.QM.SuperdenseCoding.encode_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.SuperdenseCoding.encode_Z

/-- info: 'CSD.Empirical.QM.SuperdenseCoding.encode_XZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.SuperdenseCoding.encode_XZ

/-- info: 'CSD.Empirical.QM.SuperdenseCoding.encode_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.SuperdenseCoding.encode_I

/-- info: 'CSD.Empirical.QM.SuperdenseCoding.bell_basis_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.SuperdenseCoding.bell_basis_orthonormal

-- E5: Quantum teleportation (branch-conditional form). teleState = |ψ⟩⊗|Φ⁺⟩
-- factorises; the Bell-basis expansion sends each branch to a Pauli image of ψ;
-- the four corrections {I,Z,X,ZX} recover ψ exactly. QM-validity; foundational triple.
/-- info: 'CSD.Empirical.QM.Teleportation.teleState_factorises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Teleportation.teleState_factorises

/-- info: 'CSD.Empirical.QM.Teleportation.teleportation_bell_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Teleportation.teleportation_bell_expansion

/-- info: 'CSD.Empirical.QM.Teleportation.teleportation_branch_recovers_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Teleportation.teleportation_branch_recovers_input

-- E3a: No-communication (marginal form). Alice's local unitary U⊗I cannot change
-- any Bob-side expectation ⟨φ,(I⊗Q)φ⟩; via the Kronecker mixed-product collapse
-- (U⊗I)ᴴ(I⊗Q)(U⊗I) = I⊗Q. No partial trace. QM-validity; foundational triple.
/-- info: 'CSD.Empirical.QM.NoCommunication.aliceOp_conjugate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.NoCommunication.aliceOp_conjugate

/-- info: 'CSD.Empirical.QM.NoCommunication.no_communication' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.NoCommunication.no_communication

/-- info: 'CSD.Empirical.QM.NoCommunication.bob_expectation_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.NoCommunication.bob_expectation_invariant

-- E3b: No-communication, reduced-density form. Alice's local unitary U⊗I leaves
-- Bob's reduced state (traceLeft ρ) invariant, via the partial-trace cyclicity
-- lemma. The structured form lands on the LF2 DensityOperatorIx.reducedLeft.
-- Foundational triple.
/-- info: 'Matrix.traceLeft_conjTranspose_kronecker_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.traceLeft_conjTranspose_kronecker_one

/-- info: 'CSD.Empirical.QM.NoCommunication.no_communication_reduced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.NoCommunication.no_communication_reduced

/-- info: 'CSD.Empirical.QM.NoCommunication.reducedLeft_aliceConj_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.NoCommunication.reducedLeft_aliceConj_eq

-- E3 CPTP form (channels phase C4): an arbitrary local channel Φ ⊗ id on Alice's
-- subsystem leaves Bob's reduced state traceLeft invariant (channel_no_communication),
-- via the Kraus-summed partial-trace lemma (traceLeft_sum_conjTranspose_kronecker_one)
-- and the local channel Φ ⊗ id (tensorRight). Retires the E3 CPTP gap. Foundational triple.
/-- info: 'CSD.Empirical.QM.NoCommunication.channel_no_communication' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.NoCommunication.channel_no_communication

/-- info: 'Matrix.traceLeft_sum_conjTranspose_kronecker_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.traceLeft_sum_conjTranspose_kronecker_one

/-- info: 'QuantumInfo.Channel.tensorRight_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Channel.tensorRight_apply

-- Trace distance foundation (Cat-1 staging; K3 of specs/qi-qec-roadmap.md). Trace norm
-- = ∑|λᵢ| and trace distance ½‖ρ-σ‖₁; the distinguishability headline traceDist = 0 ↔ ρ=σ,
-- and traceNorm of a PSD operator = its trace. Foundational triple. (K3 metric set + the
-- data-processing inequality are both closed — see channel_traceDist_le pinned below.)
/-- info: 'QuantumInfo.traceDist_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.traceDist_eq_zero_iff

/-- info: 'QuantumInfo.traceDist_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.traceDist_comm

-- Trace-norm subadditivity ‖A+B‖₁ ≤ ‖A‖₁ + ‖B‖₁ and the trace-distance triangle inequality
-- D(ρ,τ) ≤ D(ρ,σ) + D(σ,τ) (K3 metric core completed; specs/trace-distance-triangle-plan.md).
-- Jordan decomposition via Matrix.IsHermitian.cfc + the PSD-product trace bound. Foundational
-- triple, Gleason-free.
/-- info: 'QuantumInfo.tr_psd_mul_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.tr_psd_mul_nonneg

/-- info: 'QuantumInfo.traceNorm_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.traceNorm_add_le

/-- info: 'QuantumInfo.traceDist_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.traceDist_triangle

-- CPTP data-processing inequality traceDist (Φρ) (Φσ) ≤ traceDist ρ σ (K3; channels cannot
-- increase distinguishability). Channel adjoint Φ†(P) = ∑ Kᵢᴴ P Kᵢ (unital + positive ⟹
-- 0 ≤ Φ†P ≤ I), variational form D = Re Tr(D₊) for traceless Hermitian D, and the L6 key bound.
-- Foundational triple, Gleason-free.
/-- info: 'QuantumInfo.Channel.adjoint_unital' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Channel.adjoint_unital

/-- info: 'QuantumInfo.Channel.adjoint_trace_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Channel.adjoint_trace_mul

/-- info: 'QuantumInfo.channel_traceDist_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.channel_traceDist_le

/-- info: 'QuantumInfo.traceDist_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.traceDist_le_one

/-- info: 'QuantumInfo.traceDist_conj_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.traceDist_conj_unitary

-- Spectral von Neumann entropy S(ρ) = ∑ᵢ negMulLog(λᵢ) = −Tr(ρ log ρ) (K1-A of specs/k1-plan.md).
-- Cat-1 staging beside TraceDistance; the operator-form identity (via re_trace_cfc), S ≥ 0 for a
-- density operator (eigenvalues in [0,1]), pure-state vanishing (rank-1 projection), and unitary
-- invariance (charpoly conjugation-invariance). Foundational triple, Gleason-free. Additivity on
-- tensor products is stated under an explicit eigenvalue-product hypothesis (no Kronecker spectral
-- theorem in Mathlib); discharging it is the deferred K1-A.2 item.
/-- info: 'QuantumInfo.vonNeumannEntropy_eq_re_trace_cfc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_eq_re_trace_cfc

/-- info: 'QuantumInfo.vonNeumannEntropy_eq_neg_re_trace_mul_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_eq_neg_re_trace_mul_log

/-- info: 'QuantumInfo.cfc_id_mul_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.cfc_id_mul_log

/-- info: 'QuantumInfo.negMulLog_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.negMulLog_mul

/-- info: 'QuantumInfo.charpoly_conj_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.charpoly_conj_unitary

/-- info: 'QuantumInfo.vonNeumannEntropy_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_nonneg

/-- info: 'QuantumInfo.vonNeumannEntropy_eq_zero_of_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_eq_zero_of_pure

/-- info: 'QuantumInfo.vonNeumannEntropy_conj_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_conj_unitary

/-- info: 'QuantumInfo.vonNeumannEntropy_kronecker_of_eigenvalues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_kronecker_of_eigenvalues

-- K1-A.2 (specs/k1-plan.md): the Kronecker spectrum discharges the eigenvalue-product
-- hypothesis, making tensor additivity UNCONDITIONAL. spectral_sum_kronecker is the
-- load-bearing fact (eigenvalues of ρ⊗σ are the products λρ·λσ, in permutation-invariant
-- spectral-sum form); vonNeumannEntropy_kronecker is the headline S(ρ⊗σ) = S(ρ)+S(σ) for
-- density operators (PSD + unit trace), no spectral hypothesis. Foundational triple.
/-- info: 'QuantumInfo.spectral_sum_kronecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.spectral_sum_kronecker

/-- info: 'QuantumInfo.vonNeumannEntropy_kronecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_kronecker

-- General diagonal entropy (Cat-1, LF6-B.3 prerequisite): S(diagonal ↑d) = ∑ negMulLog(dᵢ),
-- via charpoly_diagonal + spectral_sum_eq_of_charpoly_prod (the const-smul-one route generalised).
-- Consumed by the LF6-B.3 Born-vector entropy witness (the decohered reduced state is diagonal).
/-- info: 'QuantumInfo.vonNeumannEntropy_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_diagonal

-- K1-B.1 (specs/k1-plan.md): matrix partial trace (Mathlib has none). Load-bearing results:
-- trace preservation (partialTraceRight_trace), tensor reduction with the trace of the
-- TRACED-OUT factor multiplying the surviving one (partialTraceRight_kronecker), PSD
-- preservation via the v⊗eₖ witness vectors (partialTraceRight_posSemidef /
-- partialTraceLeft_posSemidef), and the reduced-state-of-a-density-is-a-density corollaries
-- (partialTraceRight_density / partialTraceLeft_density). Foundational triple. Shared
-- prerequisite with the gated decoherence / entangled D1 tier and the Landauer touchpoint.
/-- info: 'QuantumInfo.partialTraceRight_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.partialTraceRight_trace

/-- info: 'QuantumInfo.partialTraceRight_kronecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.partialTraceRight_kronecker

/-- info: 'QuantumInfo.partialTraceLeft_kronecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.partialTraceLeft_kronecker

/-- info: 'QuantumInfo.partialTraceRight_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.partialTraceRight_posSemidef

/-- info: 'QuantumInfo.partialTraceLeft_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.partialTraceLeft_posSemidef

/-- info: 'QuantumInfo.partialTraceRight_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.partialTraceRight_density

/-- info: 'QuantumInfo.partialTraceLeft_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.partialTraceLeft_density

-- K1-B.2 (specs/k1-plan.md): quantum relative entropy + Klein's inequality. relEntropy_nonneg /
-- klein_inequality are Klein's inequality D(ρ‖σ) ≥ 0 for σ POSITIVE-DEFINITE (load-bearing: the
-- junk-log finite expression can be negative when supp ρ ⊄ supp σ). The technical core is the
-- DOUBLY-STOCHASTIC overlap matrix Dᵢⱼ = ‖Vᵢⱼ‖² (overlapV_row_sum / overlapV_col_sum) and the
-- cross-term spectral expansion Tr(ρ · cfc g σ) = ∑ᵢⱼ pᵢ g(qⱼ) ‖Vᵢⱼ‖² (trace_mul_cfc_eq), which
-- expresses a trace of a product of two operators in DIFFERENT eigenbases. The reduced-trace
-- identities (trace_mul_kronecker_one_right / _left, Tr(M(X⊗I)) = Tr(Tr_B M · X)) are the
-- subadditivity prerequisites. Foundational triple. The Kronecker-log split and the resulting
-- subadditivity headline are the remaining K1-B.2 wall (see specs/k1-plan.md).
/-- info: 'QuantumInfo.relEntropy_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.relEntropy_nonneg

/-- info: 'QuantumInfo.klein_inequality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.klein_inequality

/-- info: 'QuantumInfo.trace_mul_cfc_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.trace_mul_cfc_eq

/-- info: 'QuantumInfo.overlapV_row_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.overlapV_row_sum

/-- info: 'QuantumInfo.overlapV_col_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.overlapV_col_sum

/-- info: 'QuantumInfo.trace_mul_kronecker_one_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.trace_mul_kronecker_one_right

-- K1-B.2 wall closure: the Kronecker-log operator split (cfc_log_kronecker, via the
-- decomposition-independent cfc_eq_conj_diagonal / Lagrange-interpolation route) and the
-- von Neumann subadditivity headline S(ρ_AB) ≤ S(ρ_A) + S(ρ_B) (marginals positive-definite,
-- ρ_AB only PSD -- pure entangled states covered). Foundational triple, Gleason-free.
/-- info: 'QuantumInfo.cfc_eq_conj_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.cfc_eq_conj_diagonal

/-- info: 'QuantumInfo.cfc_log_kronecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.cfc_log_kronecker

/-- info: 'QuantumInfo.vonNeumannEntropy_subadditive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_subadditive

-- K1-A/B remainder (2026-06-17): the maximum-entropy bound S ≤ log d (concave Jensen),
-- Schmidt symmetry (pure-state marginals have equal entropy, via MMᴴ/MᴴM cospectrum),
-- purification existence, and Araki–Lieb |S(ρ_A) − S(ρ_B)| ≤ S(ρ_AB) (for ρ_AB
-- positive-definite; the pure-entangled saturating case is excluded, by design).
-- Foundational triple, Gleason-free.
/-- info: 'QuantumInfo.vonNeumannEntropy_le_log_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_le_log_card

/-- info: 'QuantumInfo.pure_marginal_entropy_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.pure_marginal_entropy_eq

/-- info: 'QuantumInfo.exists_purification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.exists_purification

/-- info: 'QuantumInfo.araki_lieb_one_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.araki_lieb_one_side

/-- info: 'QuantumInfo.vonNeumannEntropy_araki_lieb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_araki_lieb

-- K1-C strong subadditivity (specs/k1-plan.md §K1-C): the mutual-information identity
-- D(ρ ‖ ρ_X⊗ρ_Y) = S(ρ_X)+S(ρ_Y)−S(ρ) (relEntropy_kronecker_eq_entropy_sub, unconditional)
-- and the CONDITIONAL reduction strong_subadditivity_of_relEntropy_monotone: SSA derived from
-- the data-processing inequality (DPI) carried as an EXPLICIT hypothesis hDPI. The deep
-- operator-convexity input (Lieb concavity / joint convexity of relative entropy / DPI) is NOT
-- in Mathlib and is isolated as hDPI; no axiom is introduced. Foundational triple on what lands.
/-- info: 'QuantumInfo.relEntropy_kronecker_eq_entropy_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.relEntropy_kronecker_eq_entropy_sub

/-- info: 'QuantumInfo.strong_subadditivity_of_relEntropy_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.strong_subadditivity_of_relEntropy_monotone

-- n-qubit register (R1 of specs/nqubit-register-plan.md): QReg n = EuclideanSpace ℂ
-- (Fin n → Fin 2); Born prob as a squared inner product (prob_eq_inner_sq), normalisation
-- of a unit state (sum_prob_eq_one), basis state measured with certainty (prob_basisState).
-- Foundational triple. The enabling infra for the quantum-algorithm branch.
/-- info: 'QuantumInfo.prob_eq_inner_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.prob_eq_inner_sq

/-- info: 'QuantumInfo.sum_prob_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.sum_prob_eq_one

/-- info: 'QuantumInfo.prob_basisState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.prob_basisState

-- Hadamard transform (R2): Hn = H^⊗n with product entries; Hn|0ⁿ⟩ = uniform superposition
-- (Hn_apply_zero, every amplitude = (1/√2)ⁿ). First step of every Hadamard algorithm.
-- Foundational triple.
/-- info: 'QuantumInfo.Hn_apply_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Hn_apply_zero

-- Hadamard unitarity (R3): character orthogonality ⟹ Hnᴴ * Hn = 1 (Hn_unitary), factored
-- per-qubit through the single-qubit orthogonality; Hn is also an involution (Hn_mul_self,
-- Hn * Hn = 1). Makes any Hadamard circuit's full output a legitimate probability vector.
-- Foundational triple.
/-- info: 'QuantumInfo.Hn_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Hn_unitary

/-- info: 'QuantumInfo.Hn_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.Hn_mul_self

-- Quantum Fourier transform (R5): F j k = (1/√N) ω^{jk}, ω = exp(2πi/N) a primitive N-th
-- root of unity; unitary (qft_unitary, Fᴴ * F = 1) via roots-of-unity orthogonality
-- ∑ₖ ζᵏ = N·[ζ=1] (the ℂ-analogue of the Hadamard character sum). A finite N×N unitary.
-- Foundational triple.
/-- info: 'QuantumInfo.qft_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.qft_unitary

-- Deutsch-Jozsa (R4): the circuit H^⊗n ∘ U_f ∘ H^⊗n on |0ⁿ⟩ discriminates constant from
-- balanced f in one query — prob(measure 0ⁿ) = 1 if constant, 0 if balanced. Foundational
-- triple. First algorithm in the quantum-algorithm branch.
/-- info: 'CSD.Empirical.QM.DeutschJozsa.deutsch_jozsa_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.DeutschJozsa.deutsch_jozsa_constant

/-- info: 'CSD.Empirical.QM.DeutschJozsa.deutsch_jozsa_balanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.DeutschJozsa.deutsch_jozsa_balanced

-- Simon's algorithm (single-register reduced analysis): H^⊗n on the coset state
-- (1/√2)(|x₀⟩+|x₀⊕s⟩). The general Hadamard entry collects per-qubit signs into one parity
-- sign (Hn_apply_inner), giving amplitude (1/√2)^{n+1}·(-1)^⟨x₀,y⟩·(1+(-1)^⟨s,y⟩)
-- (simon_amplitude). Hence prob = 0 when ⟨s,y⟩ odd (simon_orthogonal, the Simon promise:
-- every outcome ⊥ s) and prob = 2/2ⁿ when ⟨s,y⟩ even (simon_uniform, uniform on s^⊥); the
-- coset state is normalised for s ≠ 0 (cosetState_normalized). Foundational triple.
/-- info: 'CSD.Empirical.QM.Simon.Hn_apply_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Simon.Hn_apply_inner

/-- info: 'CSD.Empirical.QM.Simon.simon_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Simon.simon_amplitude

/-- info: 'CSD.Empirical.QM.Simon.simon_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Simon.simon_orthogonal

/-- info: 'CSD.Empirical.QM.Simon.simon_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Simon.simon_uniform

/-- info: 'CSD.Empirical.QM.Simon.cosetState_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Simon.cosetState_normalized

-- Swap test (ancilla-interferometry overlap/fidelity estimator): the circuit
-- H_anc ∘ cSWAP ∘ H_anc on |0⟩⊗ψ⊗φ collapses (two-Hadamard ancilla orthogonality) to the
-- ancilla-0 amplitude (1/2)(ψ i φ j + φ i ψ j) (swapTest_apply); the ancilla-0 marginal is
-- P(0) = (1 + |⟨ψ,φ⟩|²)/2 (swap_test_prob) via the tensor identity ⟨ψ⊗φ,φ⊗ψ⟩ = |⟨ψ,φ⟩|².
-- Hence P(0) = 1 for equal states (swap_test_equal) and 1/2 for orthogonal (swap_test_orthogonal).
-- Foundational triple.
/-- info: 'CSD.Empirical.QM.SwapTest.swap_test_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.SwapTest.swap_test_prob

/-- info: 'CSD.Empirical.QM.SwapTest.swap_test_equal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.SwapTest.swap_test_equal

/-- info: 'CSD.Empirical.QM.SwapTest.swap_test_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.SwapTest.swap_test_orthogonal

-- Hadamard test (parent of the swap test; expectation-value estimator): the circuit
-- H_anc ∘ cU ∘ H_anc on |0⟩⊗ψ collapses (two-Hadamard ancilla orthogonality) to the
-- ancilla-0 amplitude (1/2)(ψ i + (Uψ) i) (hadTest_apply); the ancilla-0 marginal is
-- P(0) = (1 + Re⟨ψ,Uψ⟩)/2 (hadamard_test_prob), ancilla-1 P(1) = (1 - Re⟨ψ,Uψ⟩)/2
-- (hadamard_test_prob1), so P(0) - P(1) = Re⟨ψ,Uψ⟩ (hadamard_test_prob_diff); P(0) = 1 at
-- Uψ = ψ (hadamard_test_eq_one). The swap test is this at U = swapMap on the doubled
-- register: swapTestProb0 = hadTestProb0 swapMap (ψ⊗φ) (swap_test_via_hadamard), value
-- (1 + ‖⟨ψ,φ⟩‖²)/2 (hadamard_test_swap_closed) — derived NATIVELY through hadamard_test_prob
-- via the inner identity Re⟨ψ⊗φ,swap(ψ⊗φ)⟩ = ‖⟨ψ,φ⟩‖² (re_inner_tensorEuc_swap) and the
-- tensor unit norms, NOT through SwapTest.swap_test_prob. Foundational triple.
/-- info: 'CSD.Empirical.QM.HadamardTest.hadamard_test_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.HadamardTest.hadamard_test_prob

/-- info: 'CSD.Empirical.QM.HadamardTest.hadamard_test_prob1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.HadamardTest.hadamard_test_prob1

/-- info: 'CSD.Empirical.QM.HadamardTest.hadamard_test_prob_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.HadamardTest.hadamard_test_prob_diff

/-- info: 'CSD.Empirical.QM.HadamardTest.hadamard_test_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.HadamardTest.hadamard_test_eq_one

/-- info: 'CSD.Empirical.QM.HadamardTest.swap_test_via_hadamard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.HadamardTest.swap_test_via_hadamard

/-- info: 'CSD.Empirical.QM.HadamardTest.re_inner_tensorEuc_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.HadamardTest.re_inner_tensorEuc_swap

/-- info: 'CSD.Empirical.QM.HadamardTest.hadamard_test_swap_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.HadamardTest.hadamard_test_swap_closed

-- Bernstein-Vazirani: the FULL phase-oracle circuit H^⊗n ∘ U_f ∘ H^⊗n on |0ⁿ⟩ for the hidden
-- linear function f_a(x) = ⟨a,x⟩. The 𝔽₂ character sum ∑ₓ (-1)^⟨z,x⟩ = 2ⁿ·[z=0]
-- (bitInner_char_sum) collapses the output amplitude to the Kronecker delta δ_{y,a}
-- (bv_amplitude), so the hidden a is measured with certainty (bv_certain) and every other
-- outcome has probability 0 (bv_zero). One query. Foundational triple.
/-- info: 'CSD.Empirical.QM.BernsteinVazirani.bitInner_char_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.BernsteinVazirani.bitInner_char_sum

/-- info: 'CSD.Empirical.QM.BernsteinVazirani.bv_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.BernsteinVazirani.bv_amplitude

/-- info: 'CSD.Empirical.QM.BernsteinVazirani.bv_certain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.BernsteinVazirani.bv_certain

/-- info: 'CSD.Empirical.QM.BernsteinVazirani.bv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.BernsteinVazirani.bv_zero

-- Grover (R5+): amplitude amplification of a marked item w. The genuine reflection operators
-- oracle = I - 2|w⟩⟨w| and diffusion = 2|s⟩⟨s| - I keep the evolution in the 2D (|w⟩, rest)
-- plane, where one step is a rotation by 2θ (sin θ = 1/√N). The closed form for the success
-- probability after k steps is sin²((2k+1)θ) (grover_success). Foundational triple.
/-- info: 'CSD.Empirical.QM.Grover.grover_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Grover.grover_success

-- Grover optimal iteration: when the accumulated angle hits π/2 ((2k+1)θ = π/2) the marked
-- item is measured with certainty (grover_certain, prob = 1). Foundational triple.
/-- info: 'CSD.Empirical.QM.Grover.grover_certain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Grover.grover_certain

-- Shor's algorithm, quantum core (M1 = S1+S2+S3-core; specs/shor-plan.md). The genuine
-- multiply-by-a oracle |y⟩↦|a·y⟩ on EuclideanSpace ℂ (ZMod N) has eigenvectors u_s with
-- eigenvalues ω_r^s (mulOracle_eigU, r = orderOf a); the QFT inverse inverts the QFT exactly so
-- phase estimation reads a QFT column with certainty (phase_estimation_exact); and in the ideal
-- case r ∣ T the eigenphase ω_r^s is read off as the basis state s·(T/r) with prob 1
-- (shor_order_readout, the M1 headline). Foundational triple. The uniform-1/r joint marginal is
-- deferred (next tranche).
/-- info: 'CSD.Empirical.QM.Shor.mulOracle_eigU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.mulOracle_eigU

/-- info: 'CSD.Empirical.QM.Shor.phase_estimation_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.phase_estimation_exact

/-- info: 'CSD.Empirical.QM.Shor.shor_order_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_order_readout

-- Shor's algorithm, M1.5 (full ideal-case output distribution; specs/shor-plan.md). The genuine
-- two-register modexp state postModexpState = (1/√T) ∑_x |x⟩|a^x⟩ (jointModexp_initial), expanded
-- in the eigenbasis (basisState_apow_eq + postModexp_eq_eigenbasis), is read by the
-- counting-register inverse QFT (qftInvCount_postModexp) so that measuring the counting register
-- gives prob = 1/r on each multiple s·(T/r) (shor_order_distribution, the uniform-1/r marginal M1
-- deferred). Foundational triple. General r ∤ T (S4) remains the open quantum piece.
/-- info: 'CSD.Empirical.QM.Shor.shor_order_distribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_order_distribution

-- Shor's algorithm, S4 (phase estimation lower bound, general r ∤ T; specs/shor-plan.md §S4). The
-- single-eigenvector / generic-phase Dirichlet-kernel estimate: the inverse-QFT amplitude of the
-- phase state phaseStateR φ at index c is the Dirichlet sum (1/T) ∑_x e^{2πi(φ-c/T)x}
-- (applyQFTinv_phaseStateR_apply); when c is the closest index to φ·T (|φ-c/T| ≤ 1/(2T)) the readout
-- probability is ≥ 4/π² (phase_estimation_lower_bound), via geom_sum_eq +
-- Complex.norm_exp_I_mul_ofReal_sub_one + the Jordan inequality Real.mul_abs_le_abs_sin. The Shor
-- corollary instantiates φ = s/r. Foundational triple. The two-register r ∤ T marginal (cross-term
-- control across the r eigen-branches) is beyond S4 and deferred.
/-- info: 'CSD.Empirical.QM.Shor.phase_estimation_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.phase_estimation_lower_bound

/-- info: 'CSD.Empirical.QM.Shor.shor_phase_estimation_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_phase_estimation_lower_bound

-- Shor S5 (period recovery, uniqueness route): the measured count determines the order r.
-- Distinct lowest-terms fractions are ≥ 1/(b·d) apart (abs_sub_rat_ge), so a fraction within
-- 1/(2T) of c/T with denominator product < T is unique (approx_unique ⟹ shor_period_determined).
-- Foundational triple.
/-- info: 'CSD.Empirical.QM.Shor.abs_sub_rat_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.abs_sub_rat_ge

/-- info: 'CSD.Empirical.QM.Shor.approx_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.approx_unique

/-- info: 'CSD.Empirical.QM.Shor.shor_period_determined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_period_determined

-- Shor S6 (factoring from order): a nontrivial square root of unity mod N yields a proper
-- nontrivial divisor gcd(x-1, N) of N. The classical reduction order-finding ⟹ factoring.
-- Foundational triple.
/-- info: 'CSD.Empirical.QM.Shor.nontrivial_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.nontrivial_factor

/-- info: 'CSD.Empirical.QM.Shor.N_has_nontrivial_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.N_has_nontrivial_factor

--- S6 bridge: an even-order unit `a` with `a^(r/2) ≢ ±1` gives the nontrivial-square-root
--- hypotheses for the integer lift `x`. Foundational triple.
/-- info: 'CSD.Empirical.QM.Shor.even_order_sqrt_unity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.even_order_sqrt_unity

--- S6 composed: even order ⟹ proper nontrivial divisor gcd(x-1, N). The full classical
--- reduction order-finding ⟹ factoring. Foundational triple.
/-- info: 'CSD.Empirical.QM.Shor.shor_factor_of_even_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_factor_of_even_order

--- S7b: the per-cyclic-factor 2-adic-valuation distribution bound. In a finite cyclic group of
--- even order, no v₂(order) class exceeds half the group. Pure finite group theory; foundational
--- triple. The meaty, reusable core of the random-`a` ≥ 1/2 argument (specs/shor-plan.md §S7).
/-- info: 'CSD.Empirical.QM.Shor.card_v2_orderOf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.card_v2_orderOf_le

-- S7c: the `−1` characterisation (abstract cyclic core). In a finite cyclic group the unique
-- order-2 element `z` is hit by `a^(R/2)` iff v₂(orderOf a) = v₂(R). Per-cyclic-factor core of the
-- Shor `a^(r/2) = -1` success condition. Pure finite group theory; foundational triple.
/-- info: 'CSD.Empirical.QM.Shor.pow_half_eq_orderTwo_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.pow_half_eq_orderTwo_iff

-- S7a: two-factor CRT framing for units. The CRT iso `(ZMod (m*n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ`
-- transports `orderOf` to an `lcm` (`unitsCRT_orderOf`), splits the success witness `-1` to
-- `(-1, -1)` (`unitsCRT_neg_one`), and factors the cardinality (`card_units_mul`). Cyclicity-
-- agnostic assembly of standard Mathlib pieces; foundational triple.
/-- info: 'CSD.Empirical.QM.Shor.unitsCRT_orderOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.unitsCRT_orderOf

/-- info: 'CSD.Empirical.QM.Shor.unitsCRT_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.unitsCRT_neg_one

/-- info: 'CSD.Empirical.QM.Shor.card_units_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.card_units_mul

-- S7d-1: the diagonal count (abstract). Sums the per-factor v₂ bound `card_v2_orderOf_le` (S7b)
-- over the first coordinate of a product group to bound the matched-v₂ diagonal by half. Only the
-- second factor is cyclic / even; Finset sum-decomposition of standard Mathlib pieces; triple.
/-- info: 'CSD.Empirical.QM.Shor.two_mul_card_diag_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.two_mul_card_diag_le

-- S7d-2a: the BAD characterisation (abstract). For a pair of finite cyclic groups with order-2
-- elements z₁, z₂, the Shor "BAD" event ¬(Even r ∧ p^(r/2) ≠ (z₁,z₂)) holds iff the two component
-- orders share the same 2-adic valuation. Prod.orderOf (→ lcm) + Nat.factorization_lcm (→ max) +
-- pow_half_eq_orderTwo_iff (S7c) per factor + omega case split; triple.
/-- info: 'CSD.Empirical.QM.Shor.bad_iff_v2_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.bad_iff_v2_eq

-- S7d-2b-i (two_mul_card_good_ge): for a pair of finite cyclic groups G₁, G₂ with distinguished
-- order-2 elements z₁, z₂, the Shor "GOOD" event Even (orderOf p) ∧ p^(orderOf p/2) ≠ (z₁,z₂) covers
-- at least half: |G₁|·|G₂| ≤ 2·#GOOD. Complement of bad_iff_v2_eq (S7d-2a) against the diagonal count
-- two_mul_card_diag_le (S7d-1) via Finset.filter_congr + card_filter_add_card_filter_not + omega; triple.
/-- info: 'CSD.Empirical.QM.Shor.two_mul_card_good_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.two_mul_card_good_ge

-- S7d-2b-ii (shor_good_transport): the abstract GOOD lower bound transported onto the actual units
-- group of a coprime composite. For coprime m, n with cyclic unit groups each having orderOf(-1)=2,
-- |(ZMod (m·n))ˣ| ≤ 2·#GOOD. Transport two_mul_card_good_ge (S7d-2b-i) across unitsCRT (S7a) via a
-- Finset.card_bij filter bijection (predicate corresponds: MulEquiv.orderOf_eq + unitsCRT_neg_one)
-- + card_units_mul; triple.
/-- info: 'CSD.Empirical.QM.Shor.shor_good_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_good_transport

-- S7★ (shor_random_a_success): the prime-power headline. For distinct odd primes p ≠ q and
-- exponents α, β ≥ 1, the Shor GOOD event covers ≥ half of (ZMod (p^α·q^β))ˣ — random-a success ≥ 1/2.
-- Instantiates shor_good_transport (S7d-2b-ii) at m=p^α, n=q^β: coprimality (Nat.Coprime.pow),
-- cyclicity (ZMod.isCyclic_units_of_prime_pow), orderOf(-1)=2 (orderOf_neg_one, ringChar=p^α≠2); triple.
/-- info: 'CSD.Empirical.QM.Shor.shor_random_a_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_random_a_success

-- S7★ (shor_success_prob_ge): the probability reading of the headline. Restates the counting bound
-- as #GOOD/#units ≥ 1/2 under uniform sampling. Pure ℚ-arithmetic corollary of shor_random_a_success
-- (le_div_iff₀ + Fintype.card_pos + linarith on the cast bound); triple.
/-- info: 'CSD.Empirical.QM.Shor.shor_success_prob_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_success_prob_ge

-- gen-C (two_mul_card_pi_diag_le): the m-fold diagonal count (abstract). General-m analogue of
-- two_mul_card_diag_le: for a finite family of finite cyclic groups with the distinguished factor
-- i₀ of even order (and a free factor i₁ ≠ i₀), the fully-matched-v₂ diagonal is at most half the
-- product group. Route: fiberwise partition by the common valuation (card_eq_sum_card_fiberwise),
-- each fiber a piFinset product (Fintype.card_piFinset), factor out i₀ (mul_prod_erase) bounded by
-- card_v2_orderOf_le (S7b), erased sum bounded by a disjoint-biUnion count over {i // i ≠ i₀}; triple.
/-- info: 'CSD.Empirical.QM.Shor.two_mul_card_pi_diag_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.two_mul_card_pi_diag_le

-- gen-A (orderOf_pi): the order of a tuple in a finite indexed product is the lcm of component
-- orders (m-fold Prod.orderOf, re-exported from Mathlib's Pi.orderOf); triple.
/-- info: 'CSD.Empirical.QM.Shor.orderOf_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.orderOf_pi

-- gen-A (unitsPiCRT_neg_one): the indexed units-CRT iso (ZMod (∏ N i))ˣ ≃* Π i, (ZMod (N i))ˣ sends
-- the success witness -1 to the constant tuple fun _ => -1 (m-fold unitsCRT_neg_one); triple.
/-- info: 'CSD.Empirical.QM.Shor.unitsPiCRT_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.unitsPiCRT_neg_one

-- gen-B (bad_iff_v2_eq_pi): the m-fold BAD characterisation (Pi form). For a finite indexed family
-- of finite cyclic groups with distinguished order-2 elements, the Shor BAD event holds iff every
-- component order shares the 2-adic valuation of the distinguished index (m-fold bad_iff_v2_eq);
-- triple.
/-- info: 'CSD.Empirical.QM.Shor.bad_iff_v2_eq_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.bad_iff_v2_eq_pi

-- gen-B (two_mul_card_good_pi_ge): the abstract m-fold GOOD lower bound (Pi form). For a finite
-- indexed family of finite cyclic groups each with a distinguished order-2 element and a free index
-- i₁ ≠ i₀, the Shor GOOD event covers at least half the product group (m-fold two_mul_card_good_ge);
-- triple.
/-- info: 'CSD.Empirical.QM.Shor.two_mul_card_good_pi_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.two_mul_card_good_pi_ge

-- gen-D (shor_random_a_success_pi): the m-fold coprime transport (indexed S7d-2b-ii). For a
-- pairwise-coprime family N : ι → ℕ of nonzero moduli with cyclic unit groups each having
-- orderOf (-1) = 2 and a free index i₁ ≠ i₀, the Shor GOOD event covers at least half of
-- (ZMod (∏ i, N i))ˣ (m-fold shor_good_transport, transported across unitsPiCRT); triple.
/-- info: 'CSD.Empirical.QM.Shor.shor_random_a_success_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_random_a_success_pi

-- gen-E (shor_random_a_success_general): the general odd-composite headline (S7★-gen). For odd N
-- with ≥ 2 distinct prime factors, the Shor GOOD event covers at least half of (ZMod N)ˣ.
-- Instantiates gen-D at the prime-power factorisation ι := ↥N.primeFactors,
-- N' p := p^(N.factorization p) (∏ N' = N, pairwise coprime; per-factor odd-prime-power cyclicity +
-- orderOf(-1)=2; free index pair from one_lt_card), transported ∏N' → N via the units MulEquiv; triple.
/-- info: 'CSD.Empirical.QM.Shor.shor_random_a_success_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_random_a_success_general

-- gen-E (shor_success_prob_ge_general): the probability reading of the general headline. Restates
-- the counting bound as #GOOD/#units ≥ 1/2 under uniform sampling mod an odd composite N. Pure
-- ℚ-arithmetic corollary of shor_random_a_success_general; triple.
/-- info: 'CSD.Empirical.QM.Shor.shor_success_prob_ge_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_success_prob_ge_general

-- Shor factoring capstone (shor_random_a_yields_factor): pointwise, a GOOD unit a (Even (orderOf a)
-- ∧ a^(orderOf a/2) ≠ -1 in the units group) yields a proper nontrivial factor gcd(x-1, N) of N,
-- where x lifts a^(orderOf a/2). Bridges the units ≠ ±1 conditions to the ZMod-coercion hypotheses
-- of shor_factor_of_even_order (S6); foundational triple.
/-- info: 'CSD.Empirical.QM.Shor.shor_random_a_yields_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_random_a_yields_factor

-- Shor factoring capstone (shor_factor_prob_ge): the probability reading. For odd N with ≥ 2
-- distinct prime factors, a uniformly random unit yields a proper nontrivial factor of N with
-- probability ≥ 1/2 — the GOOD filter ⊆ the factor-yielding filter (shor_random_a_yields_factor),
-- so the ≥ 1/2 GOOD frequency (shor_success_prob_ge_general) transports by card + ℚ monotonicity.
-- Foundational triple.
/-- info: 'CSD.Empirical.QM.Shor.shor_factor_prob_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Shor.shor_factor_prob_ge

/-- info: 'QuantumInfo.traceNorm_of_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.traceNorm_of_posSemidef

-- E2: No-broadcasting, pure-marginal confinement core. A bipartite PSD operator
-- with a pure first-factor marginal |ψ⟩⟨ψ| is confined to that pure sector
-- ((P⊗I)·ρ·(P⊗I) = ρ) — the obstruction to broadcasting a pure state. Built on the
-- partial-trace module laws + PSD block-vanishing. Foundational triple. The full
-- BCFJS commuting-states theorem is fidelity-gated (deferred QI-infra tranche).
/-- info: 'CSD.Empirical.QM.NoBroadcasting.pure_marginal_confinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.NoBroadcasting.pure_marginal_confinement

/-- info: 'CSD.Empirical.QuantumMoney.wiesner_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumMoney.wiesner_inner

/-- info: 'CSD.Empirical.QuantumMoney.wiesner_nonorthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumMoney.wiesner_nonorthogonal

/-- info: 'CSD.Empirical.QuantumMoney.quantum_money_unforgeable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QuantumMoney.quantum_money_unforgeable

-- Wiesner single-slot mint/verify protocol on top of quantum_money_unforgeable:
-- honest money verifies with certainty (completeness), no isometry forges both
-- non-orthogonal notes (no perfect forgery, instantiating quantum_money_unforgeable),
-- and the per-slot acceptance advantage is bounded by the shared Protocols
-- SecurityBound (ε = 1, the trivial probability bound; quantitative cloning ε out
-- of scope). Foundational triple only.
/-- info: 'CSD.Empirical.QM.Wiesner.wiesner_verify_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Wiesner.wiesner_verify_honest

/-- info: 'CSD.Empirical.QM.Wiesner.wiesner_forge_impossible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Wiesner.wiesner_forge_impossible

/-- info: 'CSD.Empirical.QM.Wiesner.wiesner_forge_advantage_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.Wiesner.wiesner_forge_advantage_le

-- E91 device-independent security: the local-hidden-variable CHSH bound |S| ≤ 2
-- (Bell 1964 / CHSH 1969, the previously un-formalised premise behind
-- bellClassicalBoundValue), every LHV value strictly below the Tsirelson 2√2, and
-- the device-independent witness (singlet attains 2√2; every LHV capped at 2).
-- Foundational triple only.
/-- info: 'CSD.Empirical.QM.E91.lhvCHSH_abs_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.lhvCHSH_abs_le_two

/-- info: 'CSD.Empirical.QM.E91.lhvCHSH_lt_tsirelson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.lhvCHSH_lt_tsirelson

/-- info: 'CSD.Empirical.QM.E91.e91_no_lhv_reproduces_singlet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.e91_no_lhv_reproduces_singlet

-- E91 device-independent asymptotic secret-key rate (Crypto/E91KeyRate.lean):
-- a certified CHSH violation 2 < S ≤ 2√2 (above the LHV ceiling) gives a positive
-- DI secret-key rate (e91_key_rate_pos_of_chsh, UNCONDITIONAL), with boundary
-- values r(2) = 0 and r(2√2) = 1, instantiating the minimal reusable Protocols
-- interface (SecurityBound / RealProtocol.secure / IdealQKD via secure_emulates).
-- Reuses Real.binEntropy and lhvCHSH_abs_le_two. Foundational triple only.
/-- info: 'CSD.Empirical.QM.E91.e91_key_rate_pos_of_chsh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.e91_key_rate_pos_of_chsh

/-- info: 'CSD.Empirical.QM.E91.e91_key_rate_zero_at_classical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.e91_key_rate_zero_at_classical

/-- info: 'CSD.Empirical.QM.E91.e91_key_rate_one_at_tsirelson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.e91_key_rate_one_at_tsirelson

/-- info: 'CSD.Empirical.QM.E91.e91_eavesdropper_chsh_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.e91_eavesdropper_chsh_le_two

/-- info: 'CSD.Empirical.QM.E91.e91_eavesdropper_advantage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.e91_eavesdropper_advantage

/-- info: 'CSD.Empirical.QM.E91.e91_protocol_secure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.e91_protocol_secure

/-- info: 'CSD.Empirical.QM.E91.e91_chsh_certifies_secure_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.e91_chsh_certifies_secure_key

-- E91 finite-sample / finite-key concentration (Crypto/E91FiniteKey.lean):
-- the empirical CHSH estimator Sn = (sum of n bounded, unbiased, independent
-- per-round CHSH statistics)/n concentrates around the true S via Mathlib's
-- sub-Gaussian Hoeffding pipeline (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
-- per round + measure_sum_range_ge_le_of_iIndepFun Chernoff tail), giving the
-- finite-round confidence bridge to e91_key_rate_pos_of_chsh. Finite-SAMPLE
-- confidence, NOT composable finite-key security. Foundational triple only.
/-- info: 'CSD.Empirical.QM.E91.e91_chsh_concentration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.e91_chsh_concentration

/-- info: 'CSD.Empirical.QM.E91.e91_finite_key_confidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.E91.e91_finite_key_confidence

/-- info: 'CSD.Empirical.Protocols.secure_emulates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Protocols.secure_emulates

-- USD (unambiguous state discrimination), the POVM-essential QM-validity result:
-- the unambiguity zeros ⟨ψ₂,E₁ψ₂⟩ = ⟨ψ₁,E₂ψ₁⟩ = 0 (zero-error discrimination,
-- impossible projectively) and the IDP success probability 1 − s. Foundational
-- triple only.
/-- info: 'CSD.Empirical.QM.USD.usd_unambiguous_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.USD.usd_unambiguous_1

/-- info: 'CSD.Empirical.QM.USD.usd_unambiguous_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.USD.usd_unambiguous_2

/-- info: 'CSD.Empirical.QM.USD.usd_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.USD.usd_success

/-- info: 'CSD.Empirical.QM.USD.usd_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.USD.usd_complete

/-- info: 'CSD.Empirical.QM.USD.usdPOVM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.USD.usdPOVM

-- QEC: the three-qubit bit-flip code (first QEC theorem; foundational-triple only).
/--
info: 'CSD.Empirical.QM.QEC.three_qubit_corrects_single_bitflip' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.three_qubit_corrects_single_bitflip

/-- info: 'CSD.Empirical.QM.QEC.syndrome_X1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.syndrome_X1

/-- info: 'CSD.Empirical.QM.QEC.syndrome_X2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.syndrome_X2

/-- info: 'CSD.Empirical.QM.QEC.syndrome_X3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.syndrome_X3

-- Identifiability (the load-bearing QEC ingredient, now inside the bit-flip capstone): the
-- four error syndromes {I,X₁,X₂,X₃} → {(+,+),(−,+),(−,−),(+,−)} are pairwise distinct, so
-- measuring (Z₁Z₂, Z₂Z₃) pins down the error. Injectivity of errorSyndrome.
/-- info: 'CSD.Empirical.QM.QEC.three_qubit_syndromes_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.three_qubit_syndromes_distinct

/-- info: 'CSD.Empirical.QM.QEC.three_qubit_syndrome_eigenstates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.three_qubit_syndrome_eigenstates

/--
info: 'CSD.Empirical.QM.QEC.three_qubit_corrects_single_phaseflip' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.three_qubit_corrects_single_phaseflip

-- Phase-flip identifiability (Hadamard dual; now inside the phase-flip capstone).
/-- info: 'CSD.Empirical.QM.QEC.three_qubit_phaseflip_syndromes_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.three_qubit_phaseflip_syndromes_distinct

/-- info: 'CSD.Empirical.QM.QEC.three_qubit_phaseflip_syndrome_eigenstates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.three_qubit_phaseflip_syndrome_eigenstates

-- The bit-flip error channel (channels phase C4): the single-qubit error as a CPTP
-- mixedUnitaryChannel {I, X}, Φ(ρ) = (1-p)ρ + p XρX — the honest "error = decoherence"
-- model behind the bit-flip code. Foundational triple.
/-- info: 'CSD.Empirical.QM.QEC.bitFlipChannel_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.QEC.bitFlipChannel_apply

/-- info: 'CSD.Empirical.Uncertainty.robertson_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Uncertainty.robertson_core

/-- info: 'CSD.Empirical.Uncertainty.robertson_uncertainty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Uncertainty.robertson_uncertainty

/-! ### Empirical predictions (GHZ paradox, Phase D6 / Mermin all-or-nothing) -/

/-- info: 'CSD.Empirical.GHZ.ghz_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.GHZ.ghz_norm

/-- info: 'CSD.Empirical.GHZ.ghz_expectation_xxx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.GHZ.ghz_expectation_xxx

/-- info: 'CSD.Empirical.GHZ.ghz_expectation_xyy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.GHZ.ghz_expectation_xyy

/-- info: 'CSD.Empirical.GHZ.ghz_expectation_yxy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.GHZ.ghz_expectation_yxy

/-- info: 'CSD.Empirical.GHZ.ghz_expectation_yyx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.GHZ.ghz_expectation_yyx

/-- info: 'CSD.Empirical.GHZ.no_lhv_assignment_for_ghz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.GHZ.no_lhv_assignment_for_ghz

/-! ### Empirical predictions (Kochen-Specker, Phase D9 / Cabello 1996 18-vector form)

The abstract combinatorial impossibility and the concrete Cabello-18
instance. The abstract form is genuinely Cat-2 (CSD-free, Hilbert-
space-free); the instance is Cat-3 only because it lives under
`Empirical/`. Both pinned to the foundational triple. -/

/-- info: 'CSD.Empirical.KochenSpecker.no_value_assignment_18_9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.KochenSpecker.no_value_assignment_18_9

/-- info: 'CSD.Empirical.KochenSpecker.cabelloBasis_appears_twice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.KochenSpecker.cabelloBasis_appears_twice

/-- info: 'CSD.Empirical.MerminPeres.no_lhv_mermin_peres' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.no_lhv_mermin_peres

/-- info: 'CSD.Empirical.MerminPeres.sigmaX_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.sigmaX_sq

/-- info: 'CSD.Empirical.MerminPeres.sigmaY_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.sigmaY_sq

/-- info: 'CSD.Empirical.MerminPeres.sigmaZ_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.sigmaZ_sq

/-- info: 'CSD.Empirical.MerminPeres.sigmaX_mul_sigmaY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.sigmaX_mul_sigmaY

/-- info: 'CSD.Empirical.MerminPeres.sigmaY_mul_sigmaX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.sigmaY_mul_sigmaX

/-- info: 'CSD.Empirical.MerminPeres.mermin_peres_R0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.mermin_peres_R0

/-- info: 'CSD.Empirical.MerminPeres.mermin_peres_R1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.mermin_peres_R1

/-- info: 'CSD.Empirical.MerminPeres.mermin_peres_R2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.mermin_peres_R2

/-- info: 'CSD.Empirical.MerminPeres.mermin_peres_C0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.mermin_peres_C0

/-- info: 'CSD.Empirical.MerminPeres.mermin_peres_C1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.mermin_peres_C1

/-- info: 'CSD.Empirical.MerminPeres.mermin_peres_C2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.MerminPeres.mermin_peres_C2

/-- info: 'CSD.Empirical.Hardy.no_lhv_hardy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.no_lhv_hardy

/-- info: 'CSD.Empirical.Hardy.HardyQM.hardyAmp_AB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQM.hardyAmp_AB

/-- info: 'CSD.Empirical.Hardy.HardyQM.hardyAmp_A_B'minus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQM.hardyAmp_A_B'minus

/-- info: 'CSD.Empirical.Hardy.HardyQM.hardyAmp_A'minus_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQM.hardyAmp_A'minus_B

/-- info: 'CSD.Empirical.Hardy.HardyQM.hardyAmp_A'_B'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQM.hardyAmp_A'_B'

/-- info: 'CSD.Empirical.Hardy.HardyQM.exists_hardy_realisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQM.exists_hardy_realisation

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.phi_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.phi_sq

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.phi_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.phi_cube

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.sqrtPhi_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.sqrtPhi_sq

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_AB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_AB

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_A_B'minus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_A_B'minus

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_A'minus_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_A'minus_B

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_A'_B'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.hardyMaxAmp_A'_B'

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.exists_hardy_realisation_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.exists_hardy_realisation_max

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.normSq_hardyMaxVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.normSq_hardyMaxVec

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.hardyMax_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.hardyMax_value

/-- info: 'CSD.Empirical.Hardy.HardyQMMax.hardyMax_probability_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Hardy.HardyQMMax.hardyMax_probability_eq

/-- info: 'CSD.Empirical.SternGerlach.born_zPlus_zPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.SternGerlach.born_zPlus_zPlus

/-- info: 'CSD.Empirical.SternGerlach.born_zMinus_zPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.SternGerlach.born_zMinus_zPlus

/-- info: 'CSD.Empirical.SternGerlach.born_xPlus_zPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.SternGerlach.born_xPlus_zPlus

/-- info: 'CSD.Empirical.SternGerlach.born_xMinus_zPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.SternGerlach.born_xMinus_zPlus

/-- info: 'CSD.Empirical.SternGerlach.born_z_basis_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.SternGerlach.born_z_basis_complete

/-- info: 'CSD.Empirical.SternGerlach.born_x_basis_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.SternGerlach.born_x_basis_complete

/-- info: 'CSD.Empirical.Malus.malus_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Malus.malus_law

/-- info: 'CSD.Empirical.Malus.malus_basis_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Malus.malus_basis_complete

/-- info: 'CSD.Empirical.Malus.malus_pi_div_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.Malus.malus_pi_div_two

/--
info: 'CSD.Empirical.KochenSpecker.ks_no_value_assignment_cabello18' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms CSD.Empirical.KochenSpecker.ks_no_value_assignment_cabello18

/--
info: 'CSD.Empirical.KochenSpecker.cabello_pairwise_orthogonal_in_basis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms CSD.Empirical.KochenSpecker.cabello_pairwise_orthogonal_in_basis

/-! ### Empirical/CSD bridge readings

CSD-side companions to the Empirical/QM/ predictions. Each cites the
foundational triple and the LF4-discharge axioms threaded through the
shared `CSDBridge.Context` bundle.

The Bell-family CSD readings are re-exports of LF3 chain capstones;
their axiom citations match the corresponding LF3 capstones. -/

/-- info: 'CSD.Empirical.CSDBridge.Bell.bell_singlet_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.Empirical.CSDBridge.Bell.bell_singlet_frequency_convergence

/--
info: 'CSD.Empirical.CSDBridge.NoCloning.no_csd_cloning_bundle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CSD.Empirical.CSDBridge.NoCloning.no_csd_cloning_bundle

/--
info: 'CSD.Empirical.CSDBridge.NoDeleting.no_csd_deleting_bundle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms CSD.Empirical.CSDBridge.NoDeleting.no_csd_deleting_bundle

/--
info: 'CSD.Empirical.CSDBridge.Uncertainty.csd_robertson_uncertainty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Uncertainty.csd_robertson_uncertainty

-- Phase-E CSD bridges (transport readings; foundational-triple only).
/--
info: 'CSD.Empirical.CSDBridge.NoBroadcasting.csd_no_broadcasting' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.NoBroadcasting.csd_no_broadcasting

/--
info: 'CSD.Empirical.CSDBridge.NoCommunication.csd_no_communication' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.NoCommunication.csd_no_communication

/--
info: 'CSD.Empirical.CSDBridge.Teleportation.csd_teleportation_branch_recovers_input' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Teleportation.csd_teleportation_branch_recovers_input

/--
info: 'CSD.Empirical.CSDBridge.E91.csd_lhv_chsh_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.E91.csd_lhv_chsh_bound

/--
info: 'CSD.Empirical.CSDBridge.QEC.csd_three_qubit_corrects_single_bitflip' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QEC.csd_three_qubit_corrects_single_bitflip

-- Stern-Gerlach: representative pin (the iconic 1/2 split) + completeness.
-- All six transport theorems share the same foundational-triple axiom set.
/--
info: 'CSD.Empirical.CSDBridge.SternGerlach.csd_sg_born_xPlus_zPlus' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SternGerlach.csd_sg_born_xPlus_zPlus

/--
info: 'CSD.Empirical.CSDBridge.SternGerlach.csd_sg_born_x_basis_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SternGerlach.csd_sg_born_x_basis_complete

-- Stern-Gerlach Born values as DERIVED Kähler-volume frequencies (carving-free,
-- Gleason-free CSD-ontic layer): the moment-sublevel frequency → Born number
-- via fs_moment_pushforward_uniform (DH theorem). Strictly above both the
-- transport tag (csd_sg_*) and the carved LF4 capstone (sg_frequency_convergence).
-- Foundational triple only; NO busch_effect_gleason, NO invariant_measure_uniqueness.
/--
info: 'CSD.Empirical.CSDBridge.SternGerlachVolume.csd_sg_volume_certain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SternGerlachVolume.csd_sg_volume_certain

/--
info: 'CSD.Empirical.CSDBridge.SternGerlachVolume.csd_sg_volume_half' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SternGerlachVolume.csd_sg_volume_half

-- Malus's law (parametric generalisation of the two SG values) as a DERIVED
-- Kähler-volume frequency: freq → cos²(θ/2) via the same volume route.
-- Foundational triple only; NO busch_effect_gleason.
/--
info: 'CSD.Empirical.CSDBridge.MalusVolume.csd_malus_law' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MalusVolume.csd_malus_law

-- Metrology A1: Ramsey interferometry. The fringe cos²(φ/2) as a DERIVED
-- Kähler-volume frequency (the Malus reading with θ = φ the accumulated phase),
-- plus the first parameter-driven metrology flow Φ_φ = diag(1,e^{iφ}) on Σ = ℂℙ¹
-- (FS-measure-preserving, genuinely ≠ id, via the audited LF4.obsFlow).
-- Foundational triple only; NO busch_effect_gleason.
/--
info: 'CSD.Empirical.Metrology.ramsey_fringe_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramsey_fringe_volume

/--
info: 'CSD.Empirical.Metrology.ramseyPhaseFlow_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramseyPhaseFlow_measurePreserving

/--
info: 'CSD.Empirical.Metrology.ramseyPhaseFlow_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramseyPhaseFlow_ne_id

/--
info: 'CSD.Empirical.Metrology.ramsey_fringe_max' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramsey_fringe_max

/--
info: 'CSD.Empirical.Metrology.ramsey_fringe_min' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramsey_fringe_min

/--
info: 'CSD.Empirical.Metrology.ramsey_fringe_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramsey_fringe_hasDerivAt

-- The Ramsey output state IS the genuine interferometer circuit H·diag(1,e^{iφ})·H·|0⟩
-- (corpus Hadamard QM.Gates.qmH), machine-checked (not a hand-check).
/--
info: 'CSD.Empirical.Metrology.ramseyVec_eq_circuit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramseyVec_eq_circuit

-- Metrology A2: Quantum Fisher Information = Fubini-Study metric. The genuine
-- derivative of the Ramsey state (ramseyVec_hasDerivAt, proved via HasDerivAt, not
-- asserted), the FS line element g = 1/4 (ramsey_fs_metric), the QFI F_Q = 1
-- (ramsey_qfi), the classical Fisher info of the |0⟩ readout F_C = 1
-- (ramsey_classical_fisher, sin φ ≠ 0), and the QCRB saturation F_C = F_Q
-- (ramsey_qcrb_saturation): the computational-basis Ramsey measurement is
-- Fisher-optimal. Foundational triple only; NO busch_effect_gleason.
/--
info: 'CSD.Empirical.Metrology.ramseyVec_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramseyVec_hasDerivAt

/--
info: 'CSD.Empirical.Metrology.ramsey_fs_metric' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramsey_fs_metric

/--
info: 'CSD.Empirical.Metrology.ramsey_qfi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramsey_qfi

/--
info: 'CSD.Empirical.Metrology.ramsey_classical_fisher' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramsey_classical_fisher

/--
info: 'CSD.Empirical.Metrology.ramsey_qcrb_saturation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ramsey_qcrb_saturation

-- Metrology A3: the Heisenberg limit (1/N scaling) via the entangled GHZ probe.
-- The phase-accumulated GHZ state on the genuine N-qubit carrier Fin (2^N) is
-- normalized (ghzPhaseVec_norm) with a GENUINE derivative (ghzPhaseVec_hasDerivAt,
-- proved via HasDerivAt, not asserted), giving F_Q^GHZ = N² (ghz_qfi) — the
-- Heisenberg quadratic enhancement — versus F_Q^SQL = N for N separable probes, so
-- the entangled probe carries N× the information (heisenberg_advantage: N² = N·N).
-- Reuses A2's fsMetric/qfi/singleRL idiom; foundational triple only (no busch).

/--
info: 'CSD.Empirical.Metrology.ghzPhaseVec_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ghzPhaseVec_norm

/--
info: 'CSD.Empirical.Metrology.ghzPhaseVec_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ghzPhaseVec_hasDerivAt

/--
info: 'CSD.Empirical.Metrology.ghz_qfi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ghz_qfi

/--
info: 'CSD.Empirical.Metrology.heisenberg_advantage' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.heisenberg_advantage

/--
info: 'CSD.Empirical.Metrology.ghz_qfi_div_sql' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.Metrology.ghz_qfi_div_sql

-- Bell singlet joint frequencies as DERIVED Kähler-volume convergence (N=4
-- surfacing of born_frequency_convergence_N): carving-free, Gleason-free, and
-- UNCONDITIONAL (no PureSingletPreparation bundle). Plus the recovered singlet
-- correlation -cos θ. Foundational triple only; NO busch_effect_gleason.
/--
info: 'CSD.Empirical.CSDBridge.BellVolume.bell_singlet_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.BellVolume.bell_singlet_born_frequency_volume

/--
info: 'CSD.Empirical.CSDBridge.BellVolume.bell_singlet_volume_correlation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.BellVolume.bell_singlet_volume_correlation

-- GHZ three-qubit joint frequencies as DERIVED Kähler-volume convergence (N=8
-- surfacing of born_frequency_convergence_N, generic xy-plane basis): carving-free,
-- Gleason-free, unconditional. Plus the recovered three-point correlation cos Φ
-- (Mermin values are the excluded Φ=0,π boundary). Foundational triple only.
/--
info: 'CSD.Empirical.CSDBridge.GHZVolume.ghz_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.GHZVolume.ghz_born_frequency_volume

/--
info: 'CSD.Empirical.CSDBridge.GHZVolume.ghz_volume_correlation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.GHZVolume.ghz_volume_correlation

-- Hardy's maximal probability (5√5−11)/2 ≈ 9.017% as a DERIVED Kähler-volume
-- frequency (N=4 surfacing of born_frequency_convergence_N at the golden-ratio
-- Hardy state, an interior simplex point — no boundary obstruction): carving-free,
-- Gleason-free, unconditional. Foundational triple only.
/--
info: 'CSD.Empirical.CSDBridge.HardyVolume.hardy_max_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.HardyVolume.hardy_max_born_frequency_volume

/--
info: 'CSD.Empirical.CSDBridge.HardyVolume.hardy_max_volume_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.HardyVolume.hardy_max_volume_probability

-- Arbitrary rank-1 projective measurement context: outcome Born weights as
-- Fubini–Study typicality volumes. Carving-free, Gleason-free, the reusable
-- contextuality grounding. Foundational triple only.
/--
info: 'CSD.Empirical.CSDBridge.ContextVolume.context_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ContextVolume.context_born_frequency_volume

-- Degenerate-eigenspace context: the outcome-a Born weight as the block sum of
-- per-ray Born weights (rank-1-sum projector ⟨ψ, Pₐ ψ⟩). Closes the rank-1 scope
-- note. Foundational triple only.
/--
info: 'CSD.Empirical.CSDBridge.ContextVolume.block_born_eq_blockSum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ContextVolume.block_born_eq_blockSum

-- Degenerate-eigenspace context block frequency → block Born weight (sum of FS
-- typicality volumes). Covers Mermin–Peres rank-2 eigenspaces and any degenerate
-- projective context. Carving-free, Gleason-free, foundational triple only.
/--
info: 'CSD.Empirical.CSDBridge.ContextVolume.block_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ContextVolume.block_born_frequency_volume

-- Degenerate-eigenspace block frequency as the frequency of a SINGLE union event
-- (⋃_{blk i = a} bornRegion). The aeece86-owed union restatement, available now
-- that the per-ray cells are pairwise disjoint (CSD.LF4.bornRegion_pairwiseDisjoint,
-- LF5-F). Sum form untouched. Foundational triple only.
/--
info: 'CSD.Empirical.CSDBridge.ContextVolume.block_born_frequency_volume_event' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ContextVolume.block_born_frequency_volume_event

-- Concrete degenerate (rank-2) witness: the two-qubit parity Z⊗Z. The +1 parity
-- outcome Born weight realised as a block sum of two FS typicality volumes
-- (computational eigenbasis, blk = ![0,1,1,0]). The Mermin–Peres rank-2 observable
-- case made explicit. Carving-free, Gleason-free, foundational triple only.
/--
info: 'CSD.Empirical.CSDBridge.ContextVolume.zz_parity_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ContextVolume.zz_parity_born_frequency_volume

-- Qubit observable variance as a product of two Fubini–Study typicality volumes
-- (the CSD volume-ratio twin of robertson_uncertainty). Var = 4·vol₊·vol₋, the ±
-- Born weights derived as FS volumes via context_born_frequency_volume (M=1).
-- Carving-free, Gleason-free, foundational triple only. The Robertson INEQUALITY
-- itself stays at the QM-validity layer (Empirical/QM/Uncertainty.lean).
/--
info: 'CSD.Empirical.CSDBridge.UncertaintyVolume.born_variance_eq_vol_product' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.UncertaintyVolume.born_variance_eq_vol_product

-- The variance-as-volume-product frequency capstone: 4·freq₊(m)·freq₋(m) → the
-- volume-product variance, grounding observable spread in ontic typicality
-- volumes on Σ = ℂℙ¹. Foundational triple only.
/--
info: 'CSD.Empirical.CSDBridge.UncertaintyVolume.uncertainty_volume_frequency' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.UncertaintyVolume.uncertainty_volume_frequency

-- Trine POVM: the first non-projective (POVM) entry in the volume-frequency series.
-- A concrete qubit trine POVM (completeness ∑ Eₖ = I), its canonical Naimark
-- dilation, and the frequency-volume capstone — POVM outcome frequencies on the
-- dilated Σ' = ℂℙ⁵ → the trine Born weight as a sum of FS volumes. Foundational
-- triple only (carving-free, Gleason-free; POVM Born = Kähler volume).
/--
info: 'CSD.Empirical.CSDBridge.TrineVolume.trine_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.TrineVolume.trine_complete

/--
info: 'CSD.Empirical.CSDBridge.TrineVolume.trine_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.TrineVolume.trine_born_frequency_volume

/--
info: 'CSD.Empirical.CSDBridge.TrineVolume.trine_weight_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.TrineVolume.trine_weight_eq

-- USD volume capstone: the second non-projective (POVM) volume-frequency entry,
-- foundational-triple only (carving-free, Gleason-free).
/--
info: 'CSD.Empirical.CSDBridge.USDVolume.usd_weight_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.USDVolume.usd_weight_e1

/--
info: 'CSD.Empirical.CSDBridge.USDVolume.usd_weight_e2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.USDVolume.usd_weight_e2

/--
info: 'CSD.Empirical.CSDBridge.USDVolume.usd_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.USDVolume.usd_born_frequency_volume

-- SIC volume capstone: the third non-projective (POVM) volume-frequency entry,
-- foundational-triple only (carving-free, Gleason-free); includes the equiangular
-- SIC property and the tetrahedral tight-frame completeness.
/--
info: 'CSD.Empirical.CSDBridge.SICVolume.sic_outer_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SICVolume.sic_outer_sum

/--
info: 'CSD.Empirical.CSDBridge.SICVolume.sic_inner_normSq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SICVolume.sic_inner_normSq

/--
info: 'CSD.Empirical.CSDBridge.SICVolume.sic_weight_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SICVolume.sic_weight_eq

/--
info: 'CSD.Empirical.CSDBridge.SICVolume.sic_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SICVolume.sic_born_frequency_volume

-- Weak / unsharp measurement (Build 15c): the one-parameter unsharp POVM
-- interpolating no-measurement (η=0) and the sharp σ_z carve (η=1), its Born weights,
-- and the partial-volume-nudge reading on the dilated Σ' = ℂℙ³. Foundational-triple
-- only (carving-free, Gleason-free), static / operational (continuous dynamics D1-gated).
/--
info: 'CSD.Empirical.CSDBridge.WeakMeasurement.weak_effects_sum_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WeakMeasurement.weak_effects_sum_one

/--
info: 'CSD.Empirical.CSDBridge.WeakMeasurement.weak_effect_psd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WeakMeasurement.weak_effect_psd

/--
info: 'CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_weight_plus' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_weight_plus

/--
info: 'CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_weight_plus_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_weight_plus_unit

/--
info: 'CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_weight_minus' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_weight_minus

/--
info: 'CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_unsharp_interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_unsharp_interpolation

/--
info: 'CSD.Empirical.CSDBridge.WeakMeasurement.weak_partial_information_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WeakMeasurement.weak_partial_information_witness

/--
info: 'CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_frequency_volume

-- Quantum Zeno effect (Build 15d): frequent projective re-measurement freezes the state.
-- Part A (DERIVED, concrete σx/|0⟩ witness): variance (ΔH)²=1 from the matrices (varH_eq),
-- the quadratic short-time bound P(s) ≥ 1−(ΔH)²s² (zeno_survival_quadratic, from cos²=1−sin²
-- ≥ 1−s²), and the zero initial slope P'(0)=0 (zeno_survival_slope_zero). Part B: the Zeno
-- lower bound P_n ≥ 1−(ΔH)²t²/n (Bernoulli) and the freezing limit P_n → 1
-- (zeno_freezing, squeeze). Non-vacuity: (ΔH)²>0 with full free decay at π/2. The closed-form
-- exp(-isσx) is the standard qubit rotation (asserted closed form); everything else derived.
-- Foundational-triple only; static/operational, the dynamical Σ-flow realisation D1-gated.
/--
info: 'CSD.Empirical.CSDBridge.QuantumZeno.varH_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumZeno.varH_eq

/--
info: 'CSD.Empirical.CSDBridge.QuantumZeno.zeno_survival_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumZeno.zeno_survival_quadratic

/--
info: 'CSD.Empirical.CSDBridge.QuantumZeno.zeno_survival_slope_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumZeno.zeno_survival_slope_zero

/--
info: 'CSD.Empirical.CSDBridge.QuantumZeno.zeno_survival_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumZeno.zeno_survival_lower_bound

/--
info: 'CSD.Empirical.CSDBridge.QuantumZeno.zeno_freezing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumZeno.zeno_freezing

/--
info: 'CSD.Empirical.CSDBridge.QuantumZeno.zeno_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumZeno.zeno_nonvacuous

-- Qutrit POVM volume capstone: the first non-qubit (N=3) volume-frequency entry,
-- foundational-triple only (carving-free, Gleason-free); a genuine non-projective
-- qutrit POVM (the unsharp / white-noise measurement) via Naimark dilation to ℂℙ⁸.
/--
info: 'CSD.Empirical.CSDBridge.QutritPOVMVolume.noisy_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QutritPOVMVolume.noisy_complete

/--
info: 'CSD.Empirical.CSDBridge.QutritPOVMVolume.noisy_weight_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QutritPOVMVolume.noisy_weight_eq

/--
info: 'CSD.Empirical.CSDBridge.QutritPOVMVolume.noisy_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QutritPOVMVolume.noisy_born_frequency_volume

-- d=3 SIC (Hesse) volume capstone: the first SYMMETRIC non-qubit (N=3) volume entry,
-- foundational-triple only (carving-free, Gleason-free); the genuine dimension-3 SIC
-- (9 Weyl-Heisenberg states, equiangular |⟨ψⱼ,ψₖ⟩|²=1/4) via Naimark dilation to ℂℙ²⁶.
/--
info: 'CSD.Empirical.CSDBridge.SIC3Volume.sic3_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SIC3Volume.sic3_complete

/--
info: 'CSD.Empirical.CSDBridge.SIC3Volume.sic3_inner_normSq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SIC3Volume.sic3_inner_normSq

/--
info: 'CSD.Empirical.CSDBridge.SIC3Volume.sic3_weight_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SIC3Volume.sic3_weight_eq

/--
info: 'CSD.Empirical.CSDBridge.SIC3Volume.sic3_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SIC3Volume.sic3_born_frequency_volume

-- d=3 complete-MUB volume capstone: the 4 mutually unbiased bases in dimension 3
-- (|⟨v,w⟩|²=1/3 across distinct bases) as a 12-outcome POVM via Naimark dilation to ℂℙ³⁵;
-- foundational-triple only (carving-free, Gleason-free).
/--
info: 'CSD.Empirical.CSDBridge.MUB3Volume.mub3_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MUB3Volume.mub3_complete

/--
info: 'CSD.Empirical.CSDBridge.MUB3Volume.mub3_unbiased' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MUB3Volume.mub3_unbiased

/--
info: 'CSD.Empirical.CSDBridge.MUB3Volume.mub3_weight_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MUB3Volume.mub3_weight_eq

/--
info: 'CSD.Empirical.CSDBridge.MUB3Volume.mub3_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MUB3Volume.mub3_born_frequency_volume

-- Superdense coding: representative pins (one encoding + the orthonormality).
/--
info: 'CSD.Empirical.CSDBridge.SuperdenseCoding.csd_sdc_encode_X' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SuperdenseCoding.csd_sdc_encode_X

/--
info: 'CSD.Empirical.CSDBridge.SuperdenseCoding.csd_sdc_bell_basis_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SuperdenseCoding.csd_sdc_bell_basis_orthonormal

/--
info: 'CSD.Empirical.CSDBridge.QuantumMoney.no_csd_quantum_money_forger' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QuantumMoney.no_csd_quantum_money_forger

/--
info: 'CSD.Empirical.CSDBridge.MerminPeres.no_csd_mermin_peres_assignment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.no_csd_mermin_peres_assignment

/--
info: 'CSD.Empirical.CSDBridge.Hardy.no_csd_hardy_assignment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Hardy.no_csd_hardy_assignment

/--
info: 'CSD.Empirical.CSDBridge.KochenSpecker.no_csd_ks_assignment_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms CSD.Empirical.CSDBridge.KochenSpecker.no_csd_ks_assignment_bundle

/-- info: 'CSD.Empirical.CSDBridge.GHZ.no_csd_ghz_lhv_bundle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.CSDBridge.GHZ.no_csd_ghz_lhv_bundle

/-! ### Tranche 1 Tier A gates (added 2026-05-22)

Pure linear-algebra gate identities + CSD-side bundle framework.
The unitarity proofs cite only the foundational triple; the
`CSDUnitaryBundle` is a structure (no axioms). -/

/-- info: 'CSD.Empirical.QM.Gates.qmH_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmH_mul_self

/-- info: 'CSD.Empirical.QM.Gates.qmS_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmS_sq

/-- info: 'CSD.Empirical.QM.Gates.qmT_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmT_sq

/-- info: 'CSD.Empirical.QM.Gates.qmCNOT_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmCNOT_mul_self

/-- info: 'CSD.Empirical.QM.Gates.qmSWAP_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmSWAP_mul_self

/-- info: 'CSD.Empirical.QM.Gates.qmCZ_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmCZ_mul_self

-- Two-qubit gate UNITARITY (Gᴴ * G = 1) via Hermiticity (Gᴴ = G) + involutivity.
/-- info: 'CSD.Empirical.QM.Gates.qmCNOT_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmCNOT_unitary

/-- info: 'CSD.Empirical.QM.Gates.qmSWAP_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmSWAP_unitary

/-- info: 'CSD.Empirical.QM.Gates.qmCZ_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmCZ_unitary

/-- info: 'CSD.Empirical.QM.Gates.qmBellPrep_factorisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmBellPrep_factorisation

/-- info: 'CSD.Empirical.QM.Gates.qmBellPrep_yields_phiplus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmBellPrep_yields_phiplus

/-- info: 'CSD.Empirical.QM.Gates.qmToffoli_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmToffoli_mul_self

/-- info: 'CSD.Empirical.QM.Gates.qmFredkin_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmFredkin_mul_self

-- Multi-qubit gate UNITARITY (Gᴴ * G = 1) via Hermiticity + involutivity.
/-- info: 'CSD.Empirical.QM.Gates.qmToffoli_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmToffoli_unitary

/-- info: 'CSD.Empirical.QM.Gates.qmFredkin_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Empirical.QM.Gates.qmFredkin_unitary

/-! ### Mathlib upstream candidates (Projectivization, §12)

These are CSD-free Mathlib-track lemmas staged under
`CsdLean4/Mathlib/LinearAlgebra/Projectivization/`. They cite the
foundational triple only — any axiom acquisition would be an upstream
regression and a blocker for the eventual Mathlib PR. -/

/-- info: 'Projectivization.continuous_mk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.continuous_mk'

/-- info: 'Projectivization.isOpenMap_mk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.isOpenMap_mk'

/-- info: 'Projectivization.isOpenQuotientMap_mk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.isOpenQuotientMap_mk'

/-- info: 'Projectivization.instT2Space' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.instT2Space

/-- info: 'Projectivization.instCompactSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.instCompactSpace

/-- info: 'Projectivization.instMeasurableSingletonClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.instMeasurableSingletonClass

/-- info: 'Projectivization.borel_eq_map_mk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.borel_eq_map_mk'

/-- info: 'Projectivization.lift_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.lift_measurable

/-- info: 'Projectivization.measurable_iff_measurable_comp_mk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.measurable_iff_measurable_comp_mk'

/-- info: 'Projectivization.continuous_iff_continuous_comp_mk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.continuous_iff_continuous_comp_mk'

/-- info: 'Projectivization.continuous_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.continuous_lift

/-- info: 'Projectivization.mapOfInjective_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.mapOfInjective_continuous

/-- info: 'Projectivization.mapEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.mapEquiv

/-- info: 'Projectivization.mapEquiv_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.mapEquiv_continuous

/-- info: 'Projectivization.mapEquiv_continuous_of_finiteDim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.mapEquiv_continuous_of_finiteDim

/-- info: 'Projectivization.mapEquiv_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.mapEquiv_one

/-- info: 'Projectivization.mapEquiv_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.mapEquiv_mul

/-- info: 'Projectivization.instMulAction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.instMulAction

/-- info: 'Projectivization.instContinuousConstSMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Projectivization.instContinuousConstSMul

/-- info: 'Matrix.UnitaryGroup.toEuclideanLinearEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.toEuclideanLinearEquiv

/-- info: 'Matrix.UnitaryGroup.toEuclideanLinearEquivHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.toEuclideanLinearEquivHom

/-- info: 'Matrix.UnitaryGroup.instProjectivizationMulAction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instProjectivizationMulAction

/-- info: 'Matrix.UnitaryGroup.instProjectivizationContinuousConstSMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instProjectivizationContinuousConstSMul

/-- info: 'Matrix.UnitaryGroup.sum_norm_sq_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.sum_norm_sq_col

/-- info: 'Matrix.UnitaryGroup.val_norm_apply_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.val_norm_apply_le_one

/-- info: 'Matrix.UnitaryGroup.val_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.val_norm_le_one

/-- info: 'Matrix.UnitaryGroup.instCompactSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instCompactSpace

/-- info: 'Matrix.UnitaryGroup.instMeasurableSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instMeasurableSpace

/-- info: 'Matrix.UnitaryGroup.instBorelSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instBorelSpace

/-- info: 'Matrix.UnitaryGroup.unitaryHaar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.unitaryHaar

/-- info: 'Matrix.UnitaryGroup.unitaryHaar_isHaarMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.unitaryHaar_isHaarMeasure

/-- info: 'Matrix.UnitaryGroup.instIsFiniteMeasureUnitaryHaar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instIsFiniteMeasureUnitaryHaar

/-- info: 'Matrix.UnitaryGroup.unitaryHaar_univ_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.unitaryHaar_univ_ne_zero

/-- info: 'Matrix.UnitaryGroup.unitaryHaar_univ_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.unitaryHaar_univ_ne_top

/-- info: 'Matrix.UnitaryGroup.unitaryHaarProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.unitaryHaarProb

/-- info: 'Matrix.UnitaryGroup.instIsProbabilityMeasureUnitaryHaarProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instIsProbabilityMeasureUnitaryHaarProb

/-- info: 'Matrix.UnitaryGroup.unitaryHaarProb_isHaarMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.unitaryHaarProb_isHaarMeasure

/-- info: 'Matrix.UnitaryGroup.toEuclideanLin_apply_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.toEuclideanLin_apply_continuous

/-- info: 'Matrix.UnitaryGroup.toEuclideanLin_unitary_apply_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.toEuclideanLin_unitary_apply_ne_zero

/-- info: 'Matrix.UnitaryGroup.orbitMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.orbitMap

/-- info: 'Matrix.UnitaryGroup.orbit_map_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.orbit_map_continuous

/-- info: 'Matrix.UnitaryGroup.orbit_map_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.orbit_map_measurable

/-- info: 'Matrix.UnitaryGroup.fubiniStudyMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.fubiniStudyMeasure

/--
info: 'Matrix.UnitaryGroup.instIsProbabilityMeasureFubiniStudyMeasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instIsProbabilityMeasureFubiniStudyMeasure

/-- info: 'Matrix.UnitaryGroup.smul_comp_orbitMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.smul_comp_orbitMap

/-- info: 'Matrix.UnitaryGroup.fubiniStudyMeasure_smul_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.fubiniStudyMeasure_smul_invariant

/-- info: 'Matrix.UnitaryGroup.exists_unitary_e_zero_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.exists_unitary_e_zero_eq

/-- info: 'Matrix.UnitaryGroup.exists_unitary_map_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.exists_unitary_map_unit

/-- info: 'Matrix.UnitaryGroup.exists_unitary_mapping_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.exists_unitary_mapping_nonzero

/-- info: 'Matrix.UnitaryGroup.smul_mk_eq_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.smul_mk_eq_mk

/-- info: 'Matrix.UnitaryGroup.instIsPretransitive_projectivization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instIsPretransitive_projectivization

/-- info: 'Matrix.UnitaryGroup.instContinuousSMul_projectivization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instContinuousSMul_projectivization

/-- info: 'Matrix.UnitaryGroup.instIsMulRightInvariantUnitaryHaarProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.instIsMulRightInvariantUnitaryHaarProb

/-- info: 'Matrix.UnitaryGroup.haar_orbit_indicator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.haar_orbit_indicator_eq

/-- info: 'Matrix.UnitaryGroup.fubiniStudyMeasure_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Matrix.UnitaryGroup.fubiniStudyMeasure_unique

-- Pointwise Kähler fundamental form (2026-07-10): the form-level analogue of fubiniStudyMeasure. On a
-- complex inner-product space (the tangent model ψ^⊥ of ℂℙ^{N-1}) the flat Hermitian structure gives the
-- Kähler triple g = re⟪·,·⟫, ω = im⟪·,·⟫, J = i•·. Proved pointwise & axiom-free: J²=-1, ω alternating
-- ℝ-bilinear, J-compatibility ω u v = g(Ju) v, dual g u v = ω u (Jv), ω J-invariant (a (1,1)-form),
-- positivity ω u (Ju) = ‖u‖². This is the "compatible with J + positive" half of Kähler. Closedness dω=0
-- and the global ω^∧n/n! = μ_FS need manifold exterior calculus (absent from Mathlib) and stay blocked.
/-- info: 'Kahler.fubiniStudy_pointwise_kahler_compatibility' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Kahler.fubiniStudy_pointwise_kahler_compatibility

/-- info: 'Kahler.fundamentalForm_eq_metric_complexStructure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Kahler.fundamentalForm_eq_metric_complexStructure

/-- info: 'Kahler.fundamentalForm_complexStructure_self_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Kahler.fundamentalForm_complexStructure_self_pos

/-- info: 'Kahler.inner_complexStructure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Kahler.inner_complexStructure

/-- info: 'Kahler.fundamentalForm_antisymm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Kahler.fundamentalForm_antisymm

-- Tangent-space tie (2026-07-11): the projective tangent model ψ^⊥ = (span ℂ {ψ})ᗮ is J-invariant, so
-- it is a complex subspace on which the pointwise Kähler triple restricts — the flat form INDUCES the
-- Fubini–Study structure on each tangent space of ℂℙ^{N-1} (still pointwise; no manifold needed).
/-- info: 'Kahler.tangent_complexStructure_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Kahler.tangent_complexStructure_invariant

-- Schrödinger flow = Kähler symplectomorphism (2026-07-11): ties the pointwise Kähler form to the
-- Schrödinger pillar. Any ℂ-linear isometry preserves g = re⟪·,·⟫ and ω = im⟪·,·⟫
-- (kahler_structure_isometry_invariant), so exp(-itH) (schrodingerUnitary, unitary) preserves the FS
-- metric AND symplectic form — QM evolution is a symplectic isometry of the CP^{N-1} Kähler geometry
-- (Kibble/Ashtekar–Schilling picture, pointwise/linear level). The converse X_H = ω⁻¹dH (KG-2) stays
-- Mathlib-blocked (manifold symplectic-gradient API).
/-- info: 'Kahler.kahler_structure_isometry_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Kahler.kahler_structure_isometry_invariant

/-- info: 'CSD.LF4.schrodinger_flow_kahler_symplectomorphism' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.LF4.schrodinger_flow_kahler_symplectomorphism

-- `whitespace := lax` because the long theorem names push the axiom list
-- past the pretty-printer width, wrapping it across lines; lax collapses
-- the wrap so a single-line docstring matches.
/-- info: 'Matrix.UnitaryGroup.invariant_finiteMeasure_eq_smul_fubiniStudy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.UnitaryGroup.invariant_finiteMeasure_eq_smul_fubiniStudy

/-- info: 'Matrix.UnitaryGroup.invariant_measure_uniqueness_cpn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.UnitaryGroup.invariant_measure_uniqueness_cpn

/-! ### Transition probability on ℂℙ^{N-1} (Wigner / FS rigidity foundation)

The transition-probability API plus the forward (realisability) direction
`U(N) ⊆ transition-preservers`, and the coincidence / orthogonality
characterisations. All foundational-triple-only. The Wigner / FS converse is
now PROVED (`wigner_rigidity`, W6), pinned below. -/

/-- info: 'Projectivization.transProb_smul_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.transProb_smul_unitary

/-- info: 'Projectivization.transProb_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.transProb_eq_one_iff

/-- info: 'Projectivization.transProb_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.transProb_eq_zero_iff

/-! #### Step (1) of the Wigner / FS rigidity converse

The `TransProbPreserving` predicate (injectivity + orthogonality preservation)
and the `U(N) → TransProbPreserving` realisability inclusion. All
foundational-triple-only. The Wigner converse itself is now PROVED
(`wigner_rigidity`, W6, pinned below); ℂ-linearity is DERIVED (not assumed) and
the antiunitary branch is genuinely present, so no branch elimination is needed. -/

/-- info: 'Projectivization.TransProbPreserving.injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.TransProbPreserving.injective

/-- info: 'Projectivization.transProbPreserving_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.transProbPreserving_unitary

/-- info: 'Projectivization.TransProbPreserving.orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.TransProbPreserving.orthogonal

-- Wigner converse step (2a): the image ONB vector's ray is the image ray
-- (`mk (imageOrthonormalBasis i) = f (mk (b i))`).
/-- info: 'Projectivization.mk_imageOrthonormalBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.mk_imageOrthonormalBasis

-- Wigner converse step (2b) headline: the candidate unitary agrees with `f` on
-- the source basis points (`mk (candidateUnitary (b i)) = f (mk (b i))`).
/-- info: 'Projectivization.candidateUnitary_agrees_on_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.candidateUnitary_agrees_on_basis

-- Wigner converse step (2c) frame reduction: the frame-reduced map
-- `projMap (candidateUnitary hf b).symm ∘ f` is `TransProbPreserving` ...
/-- info: 'Projectivization.reducedMap_transProbPreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.reducedMap_transProbPreserving

-- ... and fixes every source basis ray (`reducedMap hf b (mk (b i)) = mk (b i)`),
-- reducing the open converse to the single Wigner normal-form lemma. Fixing the
-- basis rays does NOT make the map the identity (diagonal-phase freedom is genuine).
/-- info: 'Projectivization.reducedMap_fixes_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.reducedMap_fixes_basis

-- Wigner converse Stage 1 (moduli-preservation kernel): a preserving map fixing
-- a point `q` preserves the transition probability from every point to `q`.
/-- info: 'Projectivization.TransProbPreserving.transProb_of_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.TransProbPreserving.transProb_of_fixed

-- Wigner converse Stage 1: transition probability to the `i`-th basis ray is the
-- normalised squared modulus of the `i`-th coordinate `b.repr ψ i`.
/-- info: 'Projectivization.transProb_srcPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.transProb_srcPoint

-- Wigner converse Stage 1 HEADLINE: the frame-reduced map preserves the modulus
-- profile of the coordinates, `‖b.repr φ i‖²/‖φ‖² = ‖b.repr ψ i‖²/‖ψ‖²`. No
-- ℂ-linearity assumed.
/-- info: 'Projectivization.reducedMap_coord_modulus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.reducedMap_coord_modulus

-- Wigner converse Stage 2 support infrastructure.
/-- info: 'Projectivization.add_basis_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.add_basis_ne_zero

/-- info: 'Projectivization.repr_eq_pair_of_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.repr_eq_pair_of_support

/-- info: 'Projectivization.mk_eq_two_level_of_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.mk_eq_two_level_of_profile

-- Wigner converse Stage 2 HEADLINE: `reducedMap hf b (mk (b i₀ + b i)) =
-- mk (b i₀ + ε • b i)` for a unimodular `ε`. The image ray is pinned up to the
-- single phase `ε`; the phase cocycle (Stage 3) remains the documented open target
-- (stated neither as an axiom nor a sorry). No ℂ-linearity assumed.
/-- info: 'Projectivization.reducedMap_two_level_normal_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.reducedMap_two_level_normal_form

-- Wigner W2 (A) HEADLINE: the concrete antiunitary witness. `conjProj`
-- (coordinatewise complex conjugation as a ray map) is `TransProbPreserving`,
-- an inhabitant of the ANTIUNITARY class (`conjVec` is conjugate-linear, not the
-- underlying map of any `≃ₗᵢ[ℂ]`), so the eventual Wigner dichotomy is non-vacuous
-- on the antiunitary side. Foundational-triple only.
/-- info: 'Projectivization.conjProj_transProbPreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.conjProj_transProbPreserving

-- Wigner W2 (B) HEADLINE: Stage 3 piece 1 (the diagonal-phase reduction). The
-- diagonally-reduced map (frame reduction post-composed with the inverse diagonal
-- isometry built FROM the extracted Stage-2 phases) fixes the two-level rays
-- `mk (b i₀ + b i)`. ℂ-linearity is DERIVED not assumed (`D` is constructed from
-- the phases, not posited of `f`). The residual is pieces 2-3 (the 2-cocycle +
-- the unitary/antiunitary dichotomy). Foundational-triple only.
/-- info: 'Projectivization.diagReducedMap_fixes_two_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.diagReducedMap_fixes_two_level

-- Wigner W3 HEADLINE (heart of piece 2): the two-level relative-phase constraint.
-- `diagReducedMap` preserves `Re(conj d_{i₀} · d_i)/‖φ‖²` (the real part of the
-- relative phase between the anchor coordinate and any other), so
-- `arg(d_i/d_{i₀}) = ± arg(c_i/c_{i₀})` with the ± sign (the cocycle's ℤ/2 datum)
-- genuinely FREE. Derived from the transProb overlap algebra; NO ℂ-linearity of
-- `f`/`h` is assumed. Foundational-triple only.
/-- info: 'Projectivization.diagReducedMap_two_level_relphase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.diagReducedMap_two_level_relphase

-- Wigner W3 (general form + moduli + conditional pairwise leg).
/-- info: 'Projectivization.two_level_relphase_of_fixes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.two_level_relphase_of_fixes

/-- info: 'Projectivization.diagReducedMap_coord_modulus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.diagReducedMap_coord_modulus

-- Conditional (i, j) leg of the 2-cocycle: holds whenever `mk (b i + b j)` is
-- fixed. The non-anchored fixing is discharged by W4 below.
/-- info: 'Projectivization.diagReducedMap_pairwise_relphase_of_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.diagReducedMap_pairwise_relphase_of_fixed

-- Wigner W4 HEADLINE (piece 2 closure, triple-support fixing): the equal triple
-- ray `mk (b i₀ + b i + b j)` is fixed by `diagReducedMap`. Route: Stage-1 moduli
-- (support {i₀,i,j}, equal moduli) + the two anchored two-level relphase relations
-- + saturation (`norm_eq_re_imp_eq`) forcing phase alignment + triple-support
-- reconstruction. The probe is REAL-coordinate, so the fixing is consistent with
-- BOTH the unitary and antiunitary branches: it establishes cocycle coboundary
-- structure, NOT the global sign. NO ℂ-linearity assumed. Foundational-triple only.
/-- info: 'Projectivization.diagReducedMap_fixes_three_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.diagReducedMap_fixes_three_level

-- Wigner W4 HEADLINE (non-anchored two-level fixing): `mk (b i + b j)` fixed for
-- every `i, j ≠ i₀`, using the fixed triple as a both-coordinate probe through
-- `transProb_of_fixed`. Discharges the residual input of piece 2. Foundational-triple.
/-- info: 'Projectivization.diagReducedMap_fixes_two_level_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.diagReducedMap_fixes_two_level_general

-- Wigner W4 HEADLINE (unconditional pairwise relative phase, the 2-cocycle
-- coboundary): `Re(conj d_i d_j)/‖φ‖² = Re(conj c_i c_j)/‖ψ‖²` for ALL `i,j ≠ i₀`,
-- unconditionally. The ± sign of the imaginary parts stays free (resolved only by
-- piece 3). NO ℂ-linearity assumed. Foundational-triple only.
/-- info: 'Projectivization.diagReducedMap_pairwise_relphase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.diagReducedMap_pairwise_relphase

-- Wigner W3 owed helper: the representative-independent ray-map identity for the
-- antiunitary witness `conjProj`, needed for the eventual antiunitary assembly.
/-- info: 'Projectivization.conjProj_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.conjProj_mk

-- Wigner W5 (piece 3): the complex probe pins the IMAGINARY part of the relative
-- phase (the datum invisible to the real probes of pieces 1-2). Fixed complex ray
-- ⟹ Im preserved; flipped complex ray ⟹ Im negated (the antiunitary reading).
-- Pure overlap algebra; NO ℂ-linearity. Foundational-triple only.
/-- info: 'Projectivization.two_level_imrelphase_of_fixes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.two_level_imrelphase_of_fixes

/-- info: 'Projectivization.two_level_imrelphase_of_flips' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.two_level_imrelphase_of_flips

-- Wigner W5 HEADLINE (reconstruction, unitary branch): a preserving map fixing all
-- basis, real two-level AND complex two-level rays is the IDENTITY on rays. The full
-- Gram datum `conj dᵢ dⱼ ‖ψ‖² = conj cᵢ cⱼ ‖φ‖²` forces `φ = λ • ψ`. ℂ-linearity is
-- an OUTPUT, never an input. Foundational-triple only.
/-- info: 'Projectivization.eq_id_of_fixes_all_two_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.eq_id_of_fixes_all_two_level

-- Wigner W5 HEADLINE (reconstruction, antiunitary branch): fixing the real rays but
-- FLIPPING the complex rays gives coordinatewise conjugation in the basis `b`. The
-- genuine antiunitary branch; ℂ-linearity is an OUTPUT. Foundational-triple only.
/-- info: 'Projectivization.eq_bconj_of_flips_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.eq_bconj_of_flips_complex

-- Wigner W5 HEADLINE (the branch-distinguishing complex probe): the diagonally
-- reduced map sends `mk (b i₀ + I • b i)` to itself (+ branch) OR to
-- `mk (b i₀ - I • b i)` (− branch). Unlike the real probes, this ray is NOT
-- conjugation-invariant, so it distinguishes the unitary from the antiunitary
-- branch. The ± is forced by `Re ε = 0`, `‖ε‖ = 1`. Foundational-triple only.
/-- info: 'Projectivization.diagReducedMap_complex_probe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.diagReducedMap_complex_probe

-- Wigner W5 HEADLINE (the reduced-map dichotomy): given the GLOBAL complex-sign
-- closure (all complex two-level rays fixed, or all flipped), the diagonally reduced
-- map is GLOBALLY the identity on rays, or GLOBALLY coordinatewise conjugation. Both
-- branches genuine; ℂ-linearity an OUTPUT. The residual to an unconditional Wigner
-- converse is exactly the global-sign closure. Foundational-triple only.
/-- info: 'Projectivization.diagReducedMap_dichotomy_of_complexSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.diagReducedMap_dichotomy_of_complexSign

-- Wigner W6 HEADLINE (global-sign closure): the per-pair `± I` complex-probe datum
-- is globally consistent (all complex two-level rays fixed, or all flipped),
-- discharged from transition-probability preservation alone via the master witness
-- `masterVec` and the abstract Gram-triple core `sign_link_core`. No `Complex.arg`
-- choice, no linearity; both branches stay alive. Foundational-triple only.
/-- info: 'Projectivization.diagReducedMap_complexSign_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.diagReducedMap_complexSign_closure

-- Wigner W6 HEADLINE (unconditional reduced-map dichotomy): the diagonally reduced
-- map is GLOBALLY the identity on rays, or GLOBALLY coordinatewise conjugation in `b`
-- (the global-sign residual discharged). Both branches genuine; ℂ-linearity an
-- OUTPUT. Foundational-triple only.
/-- info: 'Projectivization.diagReducedMap_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.diagReducedMap_dichotomy

-- Wigner W6 HEADLINE (the converse): every `TransProbPreserving` self-map of
-- `ℂℙ^{N-1}` is `projMap e` for a `≃ₗᵢ[ℂ]` `e` (UNITARY) or `projMap e ∘ conjProj`
-- (ANTIUNITARY). The honest Wigner disjunction. ℂ-linearity of `e` is an OUTPUT of
-- the dichotomy landing on the identity, never assumed; the antiunitary branch is
-- genuinely present; the global sign is forced from transProb preservation alone.
-- No `busch`, no `sorry`, no `native_decide`. Foundational-triple only.
/-- info: 'Projectivization.wigner_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.wigner_rigidity

-- Wigner rigidity, `Matrix.unitaryGroup` reformulation (2026-07-02): the classic
-- `∃ U : unitaryGroup (Fin N) ℂ, ∀ p, f p = U • p` (UNITARY) ∨ `f p = U • conjProj p`
-- (ANTIUNITARY) form, via the isometry→matrix bridge `unitaryOfIsometry` /
-- `projMap_eq_smul_unitary`; the `U • ·` action is the one used by
-- `transProbPreserving_unitary`. Foundational-triple only.
/-- info: 'Projectivization.wigner_rigidity_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.wigner_rigidity_unitaryGroup

-- LF4-todo §13.2 discharge via Wigner (2026-07-02). The `CSDUnitaryBundle.U_isometry`
-- obligation is derived (not posited) from the intrinsic transition-probability
-- condition. `conjProj_ne_projMap`: coordinatewise conjugation is not a unitary
-- projective map (N ≥ 2). `transProbPreserving_isometry_dichotomy`: the honest
-- Hilbert-level dichotomy (unitary isometry ∨ antiunitary anti-isometry; the
-- antiunitary branch is exposed, not dropped). `smul_action_not_antiunitary`: the
-- sector action `g • ·` is not time-reversal (the no-time-reversal selection holds).
-- `u_isometry_of_transProbPreserving` / `ofTransProbPreserving`: Wigner OUTPUTS the
-- isometry `U`, discharging `U_isometry`. `cpSectorActionBundle`: non-vacuous
-- instantiation on the concrete Kähler instance via the sector action. All
-- foundational-triple only; no `busch`, no `sorry`, no `native_decide`. §13.2
-- discharges modulo the sector symmetry (A5); the measure-⟹-metric route is false
-- and not used.
/-- info: 'Projectivization.conjProj_ne_projMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.conjProj_ne_projMap

/-- info: 'Projectivization.transProbPreserving_isometry_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.transProbPreserving_isometry_dichotomy

/-- info: 'Projectivization.smul_action_not_antiunitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.smul_action_not_antiunitary

/-- info: 'CSD.Empirical.CSDBridge.Gates.u_isometry_of_transProbPreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Gates.u_isometry_of_transProbPreserving

/-- info: 'CSD.Empirical.CSDBridge.Gates.CSDUnitaryBundle.ofTransProbPreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Gates.CSDUnitaryBundle.ofTransProbPreserving

/-- info: 'CSD.LF4.cpSectorActionBundle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.cpSectorActionBundle

-- FND-3 (2026-07-10): the §13.2 ontic lift on the NON-TRIVIAL-FIBRE instance kSectorData
-- (π = pr₁ many-to-one, Σ = ℂℙ^{N-1}×T²), the cpSectorActionBundle analogue on the Kähler instance.
-- Part 1 (thread Φ): the sector flow Φ=kFlow descends along π to f_Φ=id on rays
-- (kSectorDataFlow_projectable), which is TransProbPreserving (kProjectedFlow_transProbPreserving)
-- and fed through Wigner realises the unitary branch (kProjectedFlow_unitary_or_antiunitary) —
-- honest but degenerate (ray flow trivial; dynamics live in the T² fibre). Part 2 (genuine, caveat
-- C-1): the sector U(N)-action carries the FS-isometry — kSectorActionBundle's U_isometry is a Wigner
-- OUTPUT (kSectorActionBundle_U_isometry), not a posit. Does NOT derive TPP from measure-preservation
-- (that is the §13.2 trap / open D1 gap); A5 untouched.
/-- info: 'CSD.LF4.kSectorDataFlow_projectable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kSectorDataFlow_projectable

/-- info: 'CSD.LF4.kProjectedFlow_transProbPreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kProjectedFlow_transProbPreserving

/-- info: 'CSD.LF4.kProjectedFlow_unitary_or_antiunitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kProjectedFlow_unitary_or_antiunitary

/-- info: 'CSD.LF4.kSectorActionBundle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kSectorActionBundle

/-- info: 'CSD.LF4.kSectorActionBundle_U_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kSectorActionBundle_U_isometry

/-! ### LF4 §8 ontic-shell instantiation

The first concrete `SectorData` instance and its axiom-free measure bridge.
Both cite only the foundational triple; `cp_measure_bridge` realises the measure
bridge `π∗μL = c • μFS` axiom-free (`c = 1`). This is now the *only* form of the
bridge in the corpus — the abstract `measure_bridge` and the
`invariant_measure_uniqueness` axiom it carried were removed 2026-06-04. -/

/-- info: 'CSD.LF4.cpSectorData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.cpSectorData

/-- info: 'CSD.LF4.cp_measure_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.cp_measure_bridge

-- The non-trivial-fibre compact-Kähler instance Σ = ℂℙ^{N-1} × T² and its
-- axiom-free marginal bridge π∗μL = μFS (c = 1). No invariant_measure_uniqueness.
/-- info: 'CSD.LF4.kSectorData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kSectorData

/-- info: 'CSD.LF4.k_measure_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.k_measure_bridge

-- Tranche A: a non-trivial measure-preserving flow on the Kähler fibre (Φ ≠ id),
-- making the LF1 deterministic-typicality theorem non-vacuous on the instance.
/-- info: 'CSD.LF4.kFlow_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kFlow_measurePreserving

/-- info: 'CSD.LF4.kFlow_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kFlow_ne_id

/-- info: 'CSD.LF4.kFlow_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kFlow_frequency_convergence

-- W2: the Kähler ontic-sector INTERFACE (sector hypotheses as structure fields,
-- no global axioms) + its inhabitation witness (non-vacuity). The projective
-- target matches Wigner's ℙ ℂ (EuclideanSpace ℂ (Fin N)).
/-- info: 'CSD.LF4.trivialKahlerOnticSetup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.trivialKahlerOnticSetup

-- Connectivity fix C1 (manifest link L4): a GENUINE Φ≠id KahlerOnticSetup
-- inhabitant. unitaryFlowSetup builds one from any unitary family
-- (measure-preserving via fubiniStudyMeasure_smul_invariant); the concrete
-- rotationSetup at N=2 (the ℂℙ¹ rotation flow) has projectedFlow ≠ id
-- (rotationSetup_projectedFlow_ne_id, [e₀]↦[e₁] at t=π/2). This flips the
-- Schrödinger pillar off the trivial Φ=id, H=0 witness. See
-- specs/connectivity-manifest.md.
/-- info: 'CSD.LF4.rotationSetup_projectedFlow_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.rotationSetup_projectedFlow_ne_id

/-- info: 'CSD.LF4.unitaryFlowSetup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.unitaryFlowSetup

-- Connectivity fix C5 (manifest link L1): the IsLiouvilleKahlerVolume field is
-- now load-bearing. It carries the formalizable core of "Liouville = Kähler
-- volume" -- that μ_FS is a normalized volume (probability measure) -- and
-- unitaryFlowSetup_liouville_isProbability CONSUMES d.liouville_eq_kahler_volume.
-- IsKahlerSector remains an honestly-unformalizable posit (no Mathlib Kähler API).
/-- info: 'CSD.LF4.unitaryFlowSetup_liouville_isProbability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.unitaryFlowSetup_liouville_isProbability

-- Move up the chain (2026-07-10): UPGRADE the IsLiouvilleKahlerVolume content from "μ is a
-- probability measure" (C5 core) to "μ is THE volume forced by the space + U(N)-symmetry"
-- (IsForcedKahlerVolume: prob + invariant + UNIQUE, via fubiniStudyMeasure_unique). So the Kähler
-- volume is an OUTCOME of Σ = ℂℙ^{N-1} and its symmetry, not posited: fubiniStudyMeasure IS the forced
-- volume, the unitaryFlowSetup sector volume IS it, and the many-to-one instance's ray-space volume
-- π_*(kMuL) IS it (kMuL = forced-FS ⊗ Haar). IsKahlerSector (the 2-form) stays Mathlib-blocked (KG-1);
-- FORWARD (takes G=U(N) as given, does not derive it — FND-1 untouched).
/-- info: 'CSD.LF4.fubiniStudyMeasure_isForcedKahlerVolume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fubiniStudyMeasure_isForcedKahlerVolume

/-- info: 'CSD.LF4.unitaryFlowSetup_liouville_isForcedKahlerVolume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.unitaryFlowSetup_liouville_isForcedKahlerVolume

/-- info: 'CSD.LF4.manyToOneSetup_baseVolume_isForcedKahlerVolume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.manyToOneSetup_baseVolume_isForcedKahlerVolume

/-- info: 'CSD.LF4.manyToOneSetup_liouville_eq_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.manyToOneSetup_liouville_eq_product

-- Connectivity fix C2 (manifest link L3, off the trivial witness): the W-series
-- Schrödinger capstone sigmaFlow_schrodinger_form FIRED on the genuine Φ≠id
-- rotation flow. The rotation R(t) is a one-parameter unitary group (trivial
-- cocycle) with generator J=[[0,-1],[1,0]]; the capstone recovers H=iJ=σ_y
-- (Pauli-Y, Hermitian, ≠0), landing rotationSetup.pi(flow t x) = exp(-it σ_y) •
-- pi x. First fully-instantiated H≠0 Schrödinger statement of the corpus.
/-- info: 'CSD.LF4.rotationSetup_schrodinger_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.rotationSetup_schrodinger_form

/-- info: 'CSD.LF4.rotationSetup_generator_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.rotationSetup_generator_ne_zero

-- Connectivity fix C4 (manifest links L5/L6): BOTH pillars on ONE object. The
-- Born capstone now references the SECTOR'S OWN liouvilleMeasure (defeq
-- fubiniStudyMeasure), so a single rotationSetup instance supports both
-- Schrödinger dynamics (A) and Born frequencies (B).
-- rotationSetup_both_pillars is the structural "one posited object underlies
-- both pillars" theorem. Honest gap: the Born trials still SAMPLE the measure
-- rather than being evolved by the flow (= C6/L7, the A5/D1 frontier).
/-- info: 'CSD.LF4.unitaryFlowSetup_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.unitaryFlowSetup_born_frequency

/-- info: 'CSD.LF4.rotationSetup_both_pillars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.rotationSetup_both_pillars

-- Connectivity fix C7 (Paper-C A3 caveat): BOTH pillars on ONE object with a
-- GENUINE many-to-one π. rotationSetup uses π = id (degenerate); manyToOneSetup
-- has Σ = ℂℙ^{N-1} × T², π = Prod.fst (fibres = T², not points —
-- manyToOneSetup_pi_not_injective) AND a non-trivial projected ray flow. The
-- Born pillar scores the FIBRED region π⁻¹'(bornRegion), whose kMuL-volume = the
-- base Born weight because the fibre volume is normalized (Prod.fst_* kMuL = μFS).
-- Same honest gap as C4: trials sample kMuL, not evolved by the flow (L7/FND-1).
/-- info: 'CSD.LF4.manyToOneSetup_pi_not_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.manyToOneSetup_pi_not_injective

/-- info: 'CSD.LF4.manyToOneSetup_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.manyToOneSetup_born_frequency

/-- info: 'CSD.LF4.manyToOneRotationSetup_both_pillars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.manyToOneRotationSetup_both_pillars

-- General-N unified capstone (2026-07-10): both pillars from the Kähler space Σ = ℂℙ^{N-1}×T² mapped
-- by π = pr₁ onto the ray space, at general N with ARBITRARY Hermitian H. manyToOneSetup driven by
-- U t = exp(-itH) (schrodingerUnitary): (A) Schrödinger π(Φ_t x)=exp(-itH)•π x holds by rfl at general N
-- (no N=2 σ_y, no Wigner selection — the flow is unitary by construction), (B) Born via the already
-- general-N manyToOneSetup_born_frequency. FORWARD delivery (consumes the sector); FND-1 untouched.
/-- info: 'CSD.LF4.manyToOneSchrodingerSetup_schrodinger_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.manyToOneSchrodingerSetup_schrodinger_form

/-- info: 'CSD.LF4.manyToOneSchrodingerSetup_both_pillars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.manyToOneSchrodingerSetup_both_pillars

/-- info: 'CSD.LF4.manyToOneSchrodingerSetup_pi_not_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.manyToOneSchrodingerSetup_pi_not_injective

-- W3: the Wigner selection on the Kähler ontic setup. The per-t disjunction
-- (unitary ∨ antiunitary) consumes W1 wigner_rigidity_unitaryGroup through the W2
-- interface; hTPP (transition-probability preservation) is a HYPOTHESIS, NOT
-- derived from Liouville-preservation (measure ≠ metric). The continuous-from-
-- identity refinement selects the unitary branch, STAGED on the clopen datum
-- (named topological residual: continuity of t ↦ flow + disconnectedness of the
-- antiunitary component), discharged via connectedness of ℝ.
/-- info: 'CSD.LF4.projectedFlow_unitary_or_antiunitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.projectedFlow_unitary_or_antiunitary

/-- info: 'CSD.LF4.projectedFlow_unitary_of_clopen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.projectedFlow_unitary_of_clopen

/-- info: 'CSD.LF4.trivialKahlerOnticSetup_unitary_or_antiunitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.trivialKahlerOnticSetup_unitary_or_antiunitary

/-- info: 'CSD.LF4.trivialKahlerOnticSetup_unitary_of_clopen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.trivialKahlerOnticSetup_unitary_of_clopen

-- W5: projected CSD dynamics = projective action of a one-parameter unitary
-- family. projectedFlow_eq_unitary_family is the MILESTONE (given the W3
-- selection hU: ∀t, ProjUnitary d t, the projected flow is the projective action
-- of a single one-parameter family {U_t}; choice over the per-t existentials,
-- NOT from Liouville-preservation, measure ≠ metric). The ray-level one-parameter
-- projective representation (U(s+t)•p = (U s * U t)•p, U 0•p = p) is proved under
-- EXPLICIT one-parameter-group hypotheses on projectedFlow. exp(-itH) is STAGED:
-- the CONVERSE realizability witness (expNegITH_unitary_group: t ↦ exp(-itH) is a
-- genuine vector-level one-parameter unitary group for Hermitian H) is proved,
-- while the Stone direction (recover H from an abstract projected flow) is the
-- named residual (phase lift S1 + finite-dim Stone S2, absent from Mathlib).
/-- info: 'CSD.LF4.projectedFlow_eq_unitary_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.projectedFlow_eq_unitary_family

/-- info: 'CSD.LF4.unitaryFamily_projective_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.unitaryFamily_projective_representation

/-- info: 'CSD.LF4.projectedFlow_projective_one_parameter_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.projectedFlow_projective_one_parameter_representation

/-- info: 'CSD.LF4.schrodingerGen_exp_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.schrodingerGen_exp_mem_unitaryGroup

/-- info: 'CSD.LF4.expNegITH_unitary_group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.expNegITH_unitary_group

/-- info: 'CSD.LF4.trivialKahlerOnticSetup_eq_unitary_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.trivialKahlerOnticSetup_eq_unitary_family

/-- info: 'CSD.LF4.trivialKahlerOnticSetup_projective_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.trivialKahlerOnticSetup_projective_representation

/-- info: 'CSD.LF4.expNegITH_unitary_group_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.expNegITH_unitary_group_zero

-- W5-S1: the projective-to-vector phase lift. Phase rigidity (the kernel of
-- U(N) → PU(N) is the circle: unitaries acting identically on every ray differ
-- by a unit phase) extracts the U(1) cocycle of the projected-flow family
-- (projectedFlow_phase_cocycle, the named obstruction), which obeys the
-- 2-cocycle law (phase_cocycle_identity). The coboundary datum b (the honest
-- S1 residual input: H²(ℝ,U(1)) ≠ 0 algebraically, so some input is genuinely
-- required) upgrades the family to a GENUINE vector-level one-parameter
-- unitary group realising the same flow (projectedFlow_phase_lift). Wired to
-- the S2 C^1 Stone theorem this gives the W5 capstone: the projected flow is
-- exp(-itH)-conjugation on rays for a Hermitian H
-- (projectedFlow_schrodinger_form). Non-vacuity: the whole chain fires
-- end-to-end on trivialKahlerOnticSetup with U = 1, c = 1, b = 1, H = 0.
/-- info: 'Projectivization.exists_unit_smul_of_smul_eq_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.exists_unit_smul_of_smul_eq_smul

/-- info: 'Projectivization.smul_eq_smul_of_eq_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.smul_eq_smul_of_eq_smul

/-- info: 'Matrix.UnitaryGroup.unit_smul_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.UnitaryGroup.unit_smul_mem

/-- info: 'CSD.LF4.projectedFlow_phase_cocycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.projectedFlow_phase_cocycle

/-- info: 'CSD.LF4.phase_cocycle_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.phase_cocycle_identity

/-- info: 'CSD.LF4.projectedFlow_phase_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.projectedFlow_phase_lift

/-- info: 'CSD.LF4.projectedFlow_schrodinger_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.projectedFlow_schrodinger_form

/-- info: 'CSD.LF4.trivialKahlerOnticSetup_phase_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.trivialKahlerOnticSetup_phase_lift

/-- info: 'CSD.LF4.trivialKahlerOnticSetup_schrodinger_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.trivialKahlerOnticSetup_schrodinger_form

-- The Σ-level capstone: the SUBSTRATE-CONSUMING form. Unlike the ray-level
-- schrodinger_form (which touches only d.projectedFlow), sigmaFlow_schrodinger_form
-- consumes d.projectable + d.flow + d.pi to conclude the deterministic ontic
-- Σ-flow, projected through π, IS exp(-itH)-conjugation: d.pi (d.flow t x) =
-- exp(-itH) • d.pi x. This is the theorem that makes the KahlerOnticSetup
-- substrate load-bearing (guarded by scripts/check-sector-linkage.sh); without
-- it the sector object is carried-but-unused scaffolding.
/-- info: 'CSD.LF4.sigmaFlow_schrodinger_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.sigmaFlow_schrodinger_form

/-- info: 'CSD.LF4.trivialKahlerOnticSetup_sigmaFlow_schrodinger_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.trivialKahlerOnticSetup_sigmaFlow_schrodinger_form

-- W3 clopen-datum closure: the Bargmann discriminator. The Bargmann invariant
-- (normalised triple product on ℙ³) is preserved by unitaries and CONJUGATED
-- by the antiunitary conjProj; on a probe triple with Im Δ ≠ 0 (exists for
-- N ≥ 2) the two Wigner branches sit at the distinct values Δ vs conj Δ of one
-- scalar observable of the flow. This PROVES the branch separation ((ii) of
-- the W3 staged residual, incl. exclusivity of the Wigner disjunction) and
-- DERIVES the clopen datum from a scalar continuity hypothesis ((i) reduced:
-- continuity of t ↦ Δ(Φ_t p, Φ_t q, Φ_t r), the named remaining physical
-- input; deriving IT from flow continuity needs continuity of Δ on ℙ³ = local
-- sections of mk, the named follow-on). N ≤ 1 needs no datum
-- (projUnitary_of_dim_le_one). Non-vacuity: the constant observable of the
-- trivial witness fires the full selection.
/-- info: 'Projectivization.bargmann_smul_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.bargmann_smul_unitary

/-- info: 'Projectivization.bargmann_conjProj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.bargmann_conjProj

/-- info: 'Projectivization.bargmann_probe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.bargmann_probe

/-- info: 'Projectivization.exists_bargmann_im_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Projectivization.exists_bargmann_im_ne_zero

/-- info: 'CSD.LF4.not_projUnitary_and_projAntiunitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.not_projUnitary_and_projAntiunitary

/-- info: 'CSD.LF4.projUnitary_isClopen_of_bargmann_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.projUnitary_isClopen_of_bargmann_continuous

/-- info: 'CSD.LF4.projectedFlow_unitary_of_bargmann_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.projectedFlow_unitary_of_bargmann_continuous

/-- info: 'CSD.LF4.projUnitary_of_dim_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.projUnitary_of_dim_le_one

/-- info: 'CSD.LF4.trivialKahlerOnticSetup_bargmann_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.trivialKahlerOnticSetup_bargmann_selection

-- D1c-1: the concrete compact-Kähler SectorData that carries the genuine
-- measure-preserving Φ = kFlow ≠ id (structural discharge of the "Φ = id in the
-- concrete Kähler instance" debt; cpSectorData still carries Φ = id).
/-- info: 'CSD.LF4.kSectorDataFlow_phi_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kSectorDataFlow_phi_ne_id

/-- info: 'CSD.LF4.kSectorDataFlow_phi_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kSectorDataFlow_phi_measurePreserving

/-- info: 'CSD.LF4.kSectorDataFlow_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kSectorDataFlow_frequency_convergence

-- Tranche 1: the Born weights as the torus moment map on ℂℙ^{N-1} (a forced
-- symplectic invariant of the Kähler structure, not a carving). Headline:
-- momentMap_mk_eq_inner_sq — Φ([ψ])ᵢ = ‖⟨eᵢ,ψ⟩‖² at a unit preparation.
/-- info: 'CSD.LF4.momentMap_sum_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.momentMap_sum_eq_one

/-- info: 'CSD.LF4.momentMap_mk_eq_inner_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.momentMap_mk_eq_inner_sq

-- The measured observable's Hamiltonian flow (the first physically-meaningful Φ≠id):
-- measure-preserving (obsFlow_measurePreserving), and the Born weights are its conserved
-- quantities (momentMap_obsFlow: momentMap (obsFlow p) = momentMap p). Ties the observable's
-- dynamics to the Born volumes; the measurement event (collapse) is still LF5.
/-- info: 'CSD.LF4.obsFlow_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.obsFlow_measurePreserving

/-- info: 'CSD.LF4.momentMap_obsFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.momentMap_obsFlow

-- The observable flow is genuinely non-trivial (Φ ≠ id), witnessed on a SUPERPOSITION ray
-- (every computational-basis ray is a diagonal-phase eigenvector and is FIXED): the |0⟩+|1⟩
-- ray is moved because its two coordinates pick up the distinct phases 1 and -1. Mirrors
-- kFlow_ne_id as the named non-triviality witness.
/-- info: 'CSD.LF4.obsFlow_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.obsFlow_ne_id

-- A5 onramp (TypicalityForcing.lean): WHERE the Fubini–Study typicality measure comes from.
-- (A) fubiniStudy_forced_by_symmetry — any U(N)-invariant probability measure on the sector
-- ℂℙ^{N-1} IS the Fubini–Study measure (restates the axiom-free fubiniStudyMeasure_unique as
-- the typicality-derivation: Born = FS-volume is DERIVED from the sector symmetry G = U(N),
-- not posited). (B) obsFlow_not_uniquely_ergodic — a single ontic flow does NOT force FS: it
-- has ≥2 distinct invariant probability measures (μFS and δ_{[e₀]} at a fixed basis ray).
-- a5_onramp conjoins them. HONEST: typicality is forced by the SYMMETRY, not any flow; residual
-- A5 primitive = G = U(N) itself, which reduces to D1 (G-from-dynamics, NOT done). A5 not closed.
-- Foundational-triple-only (no busch).
/-- info: 'CSD.LF4.fubiniStudy_forced_by_symmetry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fubiniStudy_forced_by_symmetry

/-- info: 'CSD.LF4.obsFlow_not_uniquely_ergodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.obsFlow_not_uniquely_ergodic

/-- info: 'CSD.LF4.a5_onramp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.a5_onramp

-- (B′) STRENGTHENING (TypicalityForcing.lean): the obstruction to unique ergodicity is GENERIC,
-- via a CONSERVED QUANTITY. map_withDensity_of_conserved — reweighting an invariant measure by a
-- conserved density (d ∘ T = d) keeps it invariant (the genuine conserved-quantity mechanism).
-- withDensity_momentMap_obsFlow_invariant — instantiated at the conserved Born coordinate
-- momentMap·i (momentMap_obsFlow): μFS.withDensity (g ∘ momentMap·i) is obsFlow-invariant.
-- obsFlow_continuum_invariant — a CONTINUUM (Set.InjOn on [0,1]) of pairwise-distinct
-- obsFlow-invariant PROBABILITY measures (convex-combo witness s·μFS+(1-s)·δ_{[e₀]}; the
-- conserved Born coordinates are the structural WHY). HONEST: strengthens the obstruction;
-- still does NOT force FS / NOT close A5. Foundational-triple-only (no busch).
/-- info: 'CSD.LF4.map_withDensity_of_conserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.map_withDensity_of_conserved

/-- info: 'CSD.LF4.withDensity_momentMap_obsFlow_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.withDensity_momentMap_obsFlow_invariant

/-- info: 'CSD.LF4.obsFlow_continuum_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.obsFlow_continuum_invariant

-- (B′′) SHARPER, μFS-SPECIFIC obstruction (TypicalityForcing.lean): obsFlow is not even
-- μFS-ERGODIC (distinct from not-uniquely-ergodic, which does NOT imply not-μFS-ergodic).
-- momentMap_obsFlow_nonconstant_conserved — the Born coordinate momentMap·0 is a NON-CONSTANT
-- CONSTANT OF MOTION (conserved via momentMap_obsFlow, measurable, values 1 at [e₀] vs 0 at
-- [e₁]). obsFlow_not_ergodic — therefore ¬ Ergodic obsFlow μFS: the conserved coordinate gives
-- a non-trivial μFS-invariant set {m₀ ≥ m₁} of measure ∈ (0,1) (full support of μFS via the
-- Haar pushforward bounds it away from 0 and 1), contradicting the zero-one law.
-- a5_obstruction_capstone — packages (1)⇒(2): single flow ⇒ non-constant conserved observable
-- ⇒ not μFS-ergodic ⇒ cannot force μFS. HONEST: CLOSES the single-flow obstruction story; an
-- ergodic flow (only-constant conserved observables) is what D1 must supply; residue = G-from-D1.
-- A5 NOT closed. Foundational-triple-only (no busch).
/-- info: 'CSD.LF4.momentMap_obsFlow_nonconstant_conserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.momentMap_obsFlow_nonconstant_conserved

/-- info: 'CSD.LF4.obsFlow_not_ergodic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.obsFlow_not_ergodic

/-- info: 'CSD.LF4.a5_obstruction_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.a5_obstruction_capstone

-- D1c-2: the concrete BASE SectorData carrying a PHYSICALLY-MEANINGFUL Φ = obsFlow ≠ id
-- (the observable's Hamiltonian flow exp(i t Â) on the Fubini–Study Kähler base ℂℙ^{N-1}).
-- Strictly stronger than D1c-1's free T²-fibre translation (kSectorDataFlow): dynamics on
-- the actual projective state space, not a trivial fibre shift. obsFlow is a single
-- observable's periodic phase flow (not de-isolation Φ_vN, not ergodic); A5 ergodicity gap
-- remains.
/-- info: 'CSD.LF4.cpSectorDataFlow_phi_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.cpSectorDataFlow_phi_ne_id

/-- info: 'CSD.LF4.cpSectorDataFlow_phi_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.cpSectorDataFlow_phi_measurePreserving

/-- info: 'CSD.LF4.cpSectorDataFlow_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.cpSectorDataFlow_frequency_convergence

-- Tranche M slice 3: the Born weight as a barycentric volume ratio. The i-th
-- subdivision region of the moment polytope at Φ([ψ]) has Lebesgue-volume
-- fraction ‖⟨eᵢ,ψ⟩‖² (vertex-replacement map det = barycentric coord, via Cramer
-- + addHaar_image_linearMap). Geometric region, not carved; no operational axiom.
/-- info: 'CSD.LF4.replaceMap_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.replaceMap_det

/-- info: 'CSD.LF4.replaceMap_image_volume_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.replaceMap_image_volume_sum

/-- info: 'CSD.LF4.born_eq_volume_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.born_eq_volume_ratio

-- Tranche M slice 2 (reduction): the moment map along the U(N) orbit reduces the
-- Fubini-Study pushforward to the Haar law of the squared-moduli of U·rep (the
-- Dirichlet keystone; N=2 = "|U₀₀|² uniform"). Bridge lemma toward Φ∗μ_FS=uniform.
/-- info: 'CSD.LF4.momentMap_orbit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.momentMap_orbit

-- Tranche M slice 2 (option C): Born = Fubini-Study volume ratio on the ontic
-- Kähler Σ = ℂℙ¹, modulo the explicit N=2 Duistermaat-Heckman hypothesis
-- (the 0-coordinate marginal of the genuine FS measure is uniform[0,1]).
-- Axiom-clean (hypothesis-gated); momentMap measurable via the §12 lift API.
/-- info: 'CSD.LF4.momentMap_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.momentMap_measurable

/-- info: 'CSD.LF4.fs_born_volume_ratio_qubit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_born_volume_ratio_qubit

-- Busch-free empirical capstone: i.i.d. sampling from fubiniStudyMeasure on ℂℙ¹,
-- frequencies of the moment-sublevel outcome → the Born weight ‖⟨e₀,ψ⟩‖² via the
-- volume route (foundational triple + h_uniform hypothesis; NO busch_effect_gleason).
/-- info: 'CSD.LF4.qubit_born_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.qubit_born_frequency_convergence

-- General-N joint Busch-free Born frequency convergence over a finite outcome
-- family (Born = ontic volume as hypothesis hborn). Closes LF4-todo §9.
/-- info: 'CSD.LF4.born_frequency_convergence_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.born_frequency_convergence_partition

-- Plan B step 1: the moment marginal of μ_FS = the Haar law of the
-- squared-modulus ratio of U·rep. Reduces h_uniform to the (deferred) Dirichlet
-- marginal "|U₀₀|² ~ Uniform[0,1] for Haar U(2)".
/-- info: 'CSD.LF4.momentMap_pushforward_eq_haar_marginal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.momentMap_pushforward_eq_haar_marginal

-- (The qubit Duistermaat–Heckman fact `fs_moment_pushforward_uniform` is now a
-- THEOREM, discharged in MomentUniform.lean; its foundational-triple pin lives in
-- the Slice 4 block below, together with the two unconditional Born consumers.)

-- Plan B Part 1 step: a unitary matrix's toEuclideanLin preserves the Euclidean
-- norm (the matrix-analytic core for the Gaussian unitary-invariance step).
/-- info: 'CSD.LF4.unitary_norm_preserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.unitary_norm_preserving

-- Plan B Part 1 (Option 2) C1: the hand-built real coordinate isometry ℝ⁴ ≃ₗᵢ[ℝ] ℂ²
-- (keeps stdGaussian on the clean real space, avoiding the ℝ/ℂ instance diamond).
/-- info: 'CSD.LF4.coords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.coords

-- Plan B Part 1 (Option 2) C4-C5: gaussianCP = fubiniStudyMeasure on ℂℙ¹, via the
-- by-hand real conjugate isometry conjR (restrictScalars ℝ diamonds in the full LF4
-- import context), unitary-invariance of the Gaussian-induced measure, and the
-- axiom-free Fubini-Study uniqueness theorem. All foundational-triple-only.
/-- info: 'CSD.LF4.conjR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.conjR

/-- info: 'CSD.LF4.gaussianH_map_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.gaussianH_map_unitary

/-- info: 'CSD.LF4.gaussianCP_smul_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.gaussianCP_smul_invariant

/-- info: 'CSD.LF4.gaussianCP_eq_fubiniStudy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.gaussianCP_eq_fubiniStudy

-- General-N Part 1 (Slice B): the projectivised standard Gaussian on ℂ^N is the
-- Fubini-Study measure on ℂℙ^{N-1}, via the real coordinate isometry
-- coordsN : ℝ^{N×2} ≃ₗᵢ ℂ^N + stdGaussian U(N)-invariance + fubiniStudyMeasure_unique.
-- The N-general analogue of gaussianCP_eq_fubiniStudy. Foundational triple.
/-- info: 'CSD.LF4.gaussianCPN_eq_fubiniStudy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.gaussianCPN_eq_fubiniStudy

-- Plan B Part 2, Slice 1 (L5.1): the single-block squared-norm law is Exp(1/2).
-- `‖·‖²∗ N(0,I₂) = Exp(1/2)` on plain ℝ × ℝ, via polarCoord + the 1-D s=r²
-- Jacobian change of variables. Foundational triple; entry slice of the route
-- discharging `fs_moment_pushforward_uniform`.
/-- info: 'CSD.LF4.gaussian2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.gaussian2

/-- info: 'CSD.LF4.expHalf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.expHalf

/-- info: 'CSD.LF4.sqNorm_map_gaussian2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.sqNorm_map_gaussian2

-- Plan B Part 2, Slice 2 (L5.2): block product = independence.
-- `gaussian2` is the product of two 1-D standard Gaussians, and the joint law of
-- the two block squared-norms factors as `expHalf × expHalf` (the independence
-- statement; the product measure carries it). Foundational triple.
/-- info: 'CSD.LF4.gaussian2_eq_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.gaussian2_eq_prod

/-- info: 'CSD.LF4.blockSqNorm_map_gaussian2_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.blockSqNorm_map_gaussian2_prod

-- General-N DH Slice C (Part 2a): the N-fold block law. The joint law of the N
-- block squared-norms factors as Exp(1/2)^{⊗N} (Measure.pi_map_pi + Slice 1 per
-- block) — the independence statement at general N. Foundational triple.
/-- info: 'CSD.LF4.blockSqNorm_map_gaussianN_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.blockSqNorm_map_gaussianN_pi

-- Plan B Part 2, Slice 3 (L5.3, the crux): the ratio map sends expHalf × expHalf
-- to uniform on (0,1). 2-D change of variables through the diffeo Ψ(T,S) =
-- (T·S,(1−T)·S) (Jacobian det = S), with the radial S-integral collapsing to 1.
-- Foundational triple.
/-- info: 'CSD.LF4.lintegral_radial_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.lintegral_radial_const

-- General-N DH Slice D.1: the radial moment ∫⁻_{S>0} Sⁿ e^{−S/2} = 2^{n+1}·n!
-- (Γ(n+1)=n!), the normalisation the post-substitution S-integral collapses to in
-- the Gamma→Dirichlet change of variables. Generalises lintegral_radial_const
-- (n=1). Foundational triple.
/-- info: 'CSD.LF4.lintegral_radial_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.lintegral_radial_moment

-- General-N DH Slice D.3 (the crux/gate): the Jacobian determinant of the
-- stick-breaking substitution Ψ_{M+1} is S^M. The bordered matrix (S·I block +
-- border) via the row operation "add all castSucc rows into the last" (det
-- invariant, psiMat_col_sum) → two-block-triangular. The genuine general-N content
-- (no direct Mathlib lemma). Foundational triple.
/-- info: 'CSD.LF4.psiMat_col_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.psiMat_col_sum

/-- info: 'CSD.LF4.psiMat_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.psiMat_det

-- General-N DH Slice D.2: the stick-breaking diffeo Ψ_N + its Fréchet derivative.
-- hasFDerivAt_PsiN (componentwise via hasFDerivAt_pi; derivative = toLin' psiMat)
-- and psiFDerivN_det = (y last)^M (LinearMap.det_toLin' + psiMat_det). Foundational
-- triple.
/-- info: 'CSD.LF4.hasFDerivAt_PsiN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hasFDerivAt_PsiN

/-- info: 'CSD.LF4.psiFDerivN_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.psiFDerivN_det

-- General-N DH Slice D.5c (capstone): the ratio map sends Exp(1/2)^{⊗N} to the
-- Dirichlet(1,…,1) law — M! times uniform on the open simplex (free coords). The
-- general-N analogue of ratioSqNorm_map_expHalf_prod; the genuine general-N DH
-- content, composing D.1-D.5b. Foundational triple. Closes Slice D.
/-- info: 'CSD.LF4.ratioSqNorm_map_expHalf_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.ratioSqNorm_map_expHalf_pi

-- General-N DH Slice D.4: Ψ_N is a bijection domainN (open simplex × Ioi 0) →
-- posQuadrant. PsiN_sum (∑ᵢ Ψ_N(y)ᵢ = S, the inverse-map crux), injOn_PsiN,
-- image_PsiN. Foundational triple.
/-- info: 'CSD.LF4.PsiN_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.PsiN_sum

/-- info: 'CSD.LF4.injOn_PsiN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.injOn_PsiN

/-- info: 'CSD.LF4.image_PsiN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.image_PsiN

/-- info: 'CSD.LF4.psiFDeriv_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.psiFDeriv_det

/-- info: 'CSD.LF4.ratioSqNorm_map_expHalf_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.ratioSqNorm_map_expHalf_prod

-- Plan B Part 2, Slice 4 (assembly + discharge): `fs_moment_pushforward_uniform`
-- (the qubit Duistermaat–Heckman fact) is now a THEOREM, not an axiom. The bridge
-- `regroup4∗ (pi gaussianReal) = gaussian2 × gaussian2` (finSumFinEquiv reindex),
-- the moment marginal `Tpi∗ (pi gaussianReal) = uniform`, and the discharge all
-- depend only on the foundational triple.
/-- info: 'CSD.LF4.regroupPi_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.regroupPi_map

/-- info: 'CSD.LF4.moment_marginal_uniform_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.moment_marginal_uniform_pi

/-- info: 'CSD.LF4.fs_moment_pushforward_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_moment_pushforward_uniform

-- Now foundational-triple-only (the DH input is discharged); previously these
-- carried `fs_moment_pushforward_uniform` as an axiom.
/-- info: 'CSD.LF4.fs_born_volume_ratio_qubit_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_born_volume_ratio_qubit_uncond

/-- info: 'CSD.LF4.qubit_born_frequency_convergence_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.qubit_born_frequency_convergence_uncond

-- General-N DH Slice E (Cat-1 gap): currying a product index preserves Measure.pi.
-- Mathlib proves piCurry measurable but has no measure-preserving statement; both
-- the sigma-index and product-index forms are proved here (pi_eq_generateFrom on the
-- box-of-boxes π-system). Foundational triple. Upstream candidate.
/-- info: 'MeasureTheory.map_curryProd_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.map_curryProd_pi

/-- info: 'MeasureTheory.measurePreserving_piCurry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasureTheory.measurePreserving_piCurry

-- General-N DH Slice E (bridge): the per-block squared-norm map sends the ℝ^{N×2}
-- standard Gaussian to Exp(1/2)^{⊗N}, via the product-index curry + Measure.pi_map_pi
-- + the single-block fact gBlock_map_pi. Bypasses Slice C. Foundational triple.
/-- info: 'CSD.LF4.blockSqNormCurry_map_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.blockSqNormCurry_map_pi

-- General-N DH Slice E (headline): the free-coordinate moment map ratioN ∘ momentMap
-- pushes the genuine Fubini–Study measure on ℂℙ^M to M! · uniform on the open simplex
-- (the joint Dirichlet(1,…,1) law). The general-N analogue of fs_moment_pushforward_uniform
-- (the qubit could give only the scalar Beta marginal). Foundational triple; no Busch.
/-- info: 'CSD.LF4.fs_moment_joint_dirichlet_N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_moment_joint_dirichlet_N

-- General-N DH Slice E (Born lift). E4a: the Duistermaat–Heckman volume law on Σ
-- (μ_FS of a moment region = M!·its Lebesgue volume). E4b: the standard simplex has
-- volume (M!)⁻¹ (forced by μ_FS being a probability measure). E4c: Born weight =
-- FS volume ratio of the i-th barycentric region, for the N-1 free coordinates,
-- now UNCONDITIONAL (the qubit h_uniform is the proved headline). Foundational triple;
-- no busch_effect_gleason.
/-- info: 'CSD.LF4.fs_volume_eq_dirichlet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_volume_eq_dirichlet

/-- info: 'CSD.LF4.volume_openSimplexFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.volume_openSimplexFree

/-- info: 'CSD.LF4.fs_born_volume_ratio_N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_born_volume_ratio_N

-- Apex coordinate (the dropped vertex, index M): the affine apex map (det = 1 - ∑b
-- = b_last via det_one_sub_mul_comm) closes the last Born coordinate. With
-- fs_born_volume_ratio_N this covers all N coordinates. Foundational triple.
/-- info: 'CSD.LF4.fs_born_volume_ratio_N_apex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_born_volume_ratio_N_apex

-- General-N Busch-free capstone: i.i.d. trials from μ_FS on ℂℙ^M, empirical frequencies
-- of the N barycentric Born regions → the Born weights ‖⟨eᵢ,ψ⟩‖² jointly a.s. The Born
-- values come from fs_born_volume_ratio_N(_apex) (the volume route), so the chain is
-- foundational-triple-only — NO busch_effect_gleason. The general-N analogue of
-- qubit_born_frequency_convergence_uncond; the headline empirical payoff.
/-- info: 'CSD.LF4.born_frequency_convergence_N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.born_frequency_convergence_N

-- HY-5 (BornFlowLinkage): the Born-side sigmaFlow fix. The general-N Born capstone, now on trials
-- EVOLVED by the sector's own deterministic flow Φ_t = (unitaryFlowSetup …).flow t, converging to
-- the Born weights. The flow's Liouville-preservation (flow_preserves_volume = U(N)-invariance of
-- μ_FS) pins the evolved law back to μ_FS — the substrate flow is now consumed on the Born side.
-- Still foundational-triple; weights-from-flow (FND-1) untouched.
/-- info: 'CSD.LF4.unitaryFlowSetup_born_frequency_evolved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.unitaryFlowSetup_born_frequency_evolved

/-- info: 'CSD.LF4.povm_born_frequency_volume_evolved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.povm_born_frequency_volume_evolved

-- N=2 consistency cross-check: the qubit fs_moment_pushforward_uniform is kernel-derived
-- from the general-N fs_moment_joint_dirichlet_N (M:=1). Machine-confirms the general-N
-- statement faithfully generalises the independently-proved qubit result. Foundational triple.
/-- info: 'CSD.LF4.fs_moment_pushforward_uniform_of_joint_dirichlet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_moment_pushforward_uniform_of_joint_dirichlet

-- The ofKählerPreparation constructor: a concrete LF3.PureSingletPreparation
-- on the non-trivial-fibre compact-Kähler instance. bridge_op_p is proved
-- Busch-free via born_rank_one_direct + the carving identity kMuPsi_kRegion,
-- so the constructor stays foundational-triple only.
/-- info: 'CSD.LF4.ofKählerPreparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.ofKählerPreparation

-- Applying the LF3 chain capstone to the concrete prep gives a non-vacuous
-- empirical statement. Now foundational-triple-only (2026-06-02): the chain bridge
-- was re-routed off Busch onto the volume-ratio Born step, so this end-to-end
-- ontic capstone no longer cites busch_effect_gleason.
/-- info: 'CSD.LF4.ofKählerPreparation_singlet_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.ofKählerPreparation_singlet_frequency_convergence

-- FND-2 (2026-07-09): the singlet preparation rebuilt over the Φ≠id sector kSectorDataFlow (Φ=kFlow),
-- the ENTANGLED analogue of D1c-1. The LF1 preEvent = Φ⁻¹'Ω, so with Φ=kFlow the capstone scores the
-- flow-EVOLVED trials (kFlow∘X)⁻¹'kRegion, and kFlow's μψ-preservation (kFlow_measurePreserving_muPsi)
-- is load-bearing (bridge_op_p: kMuPsi (kFlow⁻¹'kRegion) = kMuPsi kRegion = P_st). Still foundational-triple.
/-- info: 'CSD.LF4.kFlow_measurePreserving_muPsi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kFlow_measurePreserving_muPsi

/-- info: 'CSD.LF4.ofKählerPreparationFlow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.ofKählerPreparationFlow

/-- info: 'CSD.LF4.ofKählerPreparationFlow_flow_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.ofKählerPreparationFlow_flow_frequency_convergence

-- LF4 §14 discharge (projector observables, single-qubit Stern-Gerlach):
-- the Hilbert ↔ ontic-measure identity, foundational triple only.
/-- info: 'CSD.LF4.sg_observable_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.sg_observable_correspondence

-- The non-vacuous LF3-chain Stern-Gerlach capstone (N = 2 analog of
-- ofKählerPreparation_singlet_frequency_convergence). Foundational triple only.
/-- info: 'CSD.LF4.sg_frequency_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.sg_frequency_convergence

-- LF4 §14.2 first step beyond projectors: Pauli observable σ·a via the
-- spectral-decomposition signed-indicator construction. Foundational triple only.
/-- info: 'CSD.LF4.pauliDot_observable_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.pauliDot_observable_correspondence

-- LF4 §14.2 at N = 4: two-qubit Pauli observables on the singlet (covering
-- all 9 Mermin-Peres observables and the 4 Hardy single-qubit Paulis).
/-- info: 'CSD.LF4.sigmaDotLeft_observable_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.sigmaDotLeft_observable_correspondence

/-- info: 'CSD.LF4.sigmaDotRight_observable_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.sigmaDotRight_observable_correspondence

/-- info: 'CSD.LF4.sigmaDotJoint_observable_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.sigmaDotJoint_observable_correspondence

-- Hardy LF3-chain capstones: the four Hardy probability constraints lifted to
-- ontic frequency-convergence theorems on the Hardy-state Kähler preparation.
-- Headline pin (positive coincidence) + load-bearing zero (A'=+1, B'=+1).
/-- info: 'CSD.LF4.hardy_freq_convergence_AB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hardy_freq_convergence_AB

/-- info: 'CSD.LF4.hardy_freq_convergence_A'_B'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hardy_freq_convergence_A'_B'

-- Hardy §14 observable correspondence (Hilbert ↔ ontic): closes the QM ↔ LF4
-- amplitude loop. Headline pin (the positive-coincidence Hilbert ↔ ontic match)
-- + the load-bearing zero observable correspondence.
/-- info: 'CSD.LF4.hardy_observable_correspondence_AB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hardy_observable_correspondence_AB

/-- info: 'CSD.LF4.hardy_observable_correspondence_A'_B'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hardy_observable_correspondence_A'_B'

-- LF4 §14.2 general N×N spectral expansion of the Hilbert expectation.
-- The Hilbert-side spectral identity ⟨ψ, A ψ⟩ = ∑ᵢ λᵢ · ‖⟨uᵢ, ψ⟩‖²
-- for any Hermitian A and any state ψ — unlocks variance / uncertainty
-- ontic correspondences beyond the projector / ±1-eigenvalue case.
/-- info: 'CSD.LF4.hermitian_inner_spectral_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hermitian_inner_spectral_expansion

/-- info: 'CSD.LF4.hermitian_inner_spectral_expansion_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hermitian_inner_spectral_expansion_re

-- LF4 §14.2 ontic-side multi-region spectral carving (Phase A foundation
-- + Phase C carving identity + Phase D integration headline).
/-- info: 'CSD.LF4.fibreShiftedArc_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fibreShiftedArc_volume

/-- info: 'CSD.LF4.diracProd_spectralRegion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.diracProd_spectralRegion

/-- info: 'CSD.LF4.integral_spectralOntic_eq_inner_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.integral_spectralOntic_eq_inner_re

-- LF4 §14.2 variance: Hilbert-side norm-squared, spectral variance,
-- Hilbert ↔ spectral identity, and ontic ↔ Hilbert variance correspondence.
/-- info: 'CSD.LF4.hilbert_norm_sq_apply_hermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.hilbert_norm_sq_apply_hermitian

/-- info: 'CSD.LF4.spectralVariance_eq_hilbert_norm_sq_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.spectralVariance_eq_hilbert_norm_sq_diff

/-- info: 'CSD.LF4.integral_spectralOnticCentered_eq_variance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.integral_spectralOnticCentered_eq_variance

/-- info: 'CSD.LF4.integral_spectralOnticCentered_eq_hilbert_norm_sq_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.integral_spectralOnticCentered_eq_hilbert_norm_sq_diff

-- LF4 §14.2 Robertson uncertainty on the Kähler instance: ontic-variance
-- bridge to QM variance, and the headline ontic-variance Robertson bound.
/-- info: 'CSD.LF4.QM_variance_eq_spectralVariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.QM_variance_eq_spectralVariance

/-- info: 'CSD.LF4.kahler_robertson_ontic_variance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.kahler_robertson_ontic_variance

-- LF4 §14.2 concrete instance: σ_x, σ_y Robertson saturation on |0⟩.
/-- info: 'CSD.LF4.pauli_xy_robertson_saturation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.pauli_xy_robertson_saturation

-- LF4 §14.2 parametric: Robertson for σ·â, σ·b̂ on |0⟩, geometric form.
/-- info: 'CSD.LF4.pauliDot_robertson_zPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.pauliDot_robertson_zPlus

-- The pure-state ontic Born capstone composes LF1 frequency convergence with the
-- LF2 operational Born derivation, so it cites the Busch axiom (and only it,
-- beyond the foundational triple).
/-- info: 'CSD.LF4.ontic_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound, busch_effect_gleason] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.ontic_born_frequency

-- POVM tranche P.1 (POVM type + Born-weight completeness) and P.2 (Naimark
-- dilation + Born transfer: POVM Born weight = projective Born weight of the
-- dilated state against the ancilla block projector). Both foundational triple
-- only — the dilation is supplied data, no Busch / invariant-measure axiom.
/-- info: 'CSD.LF2.POVM.weights_sum_eq_normSq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF2.POVM.weights_sum_eq_normSq

/-- info: 'CSD.LF2.POVM.weights_sum_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF2.POVM.weights_sum_eq_one

/-- info: 'CSD.LF4.NaimarkDilation.born_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.NaimarkDilation.born_transfer

-- POVM tranche P.3a (block decomposition): the POVM Born weight is the sum, over
-- the i-th ancilla block, of the dilated computational-basis (rank-1) Born
-- weights — each of which the general-N result reads as a Fubini-Study volume.
-- Foundational triple only.
/-- info: 'CSD.LF4.povm_born_eq_block_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.povm_born_eq_block_sum

-- POVM tranche P.3b (FS-volume identification): the POVM Born weight is the sum,
-- over the i-th ancilla block, of the genuine Fubini-Study typicality volumes of
-- the dilated barycentric cells on Σ' = ℂℙ^{N·|ι|−1}. Composes P.3a with the
-- general-N Born = FS-volume result through the reindex isometry. Carving-free,
-- Gleason-free (no busch_effect_gleason); foundational triple only.
/-- info: 'CSD.LF4.povm_born_eq_dilated_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.povm_born_eq_dilated_volume

-- POVM tranche P.4 (empirical capstone): i.i.d. Fubini-Study trials on the dilated
-- Σ' have the i-th POVM outcome's empirical frequency (the block sum of dilated
-- cell frequencies) converge a.s. to the POVM Born weight pᵢ(ψ). The empirical →
-- Born chain for a general POVM, carving-free and Gleason-free. Foundational triple.
/-- info: 'CSD.LF4.povm_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.povm_born_frequency_volume

-- POVM tranche P.5 (existence): the canonical Naimark dilation built from the CFC
-- square roots √Eᵢ inhabits NaimarkDilation P for every POVM, making the Phase-1
-- POVM Born = Kähler-volume results unconditional (no longer needing a supplied
-- dilation). Foundational triple only — the CFC sqrt and isometry/pullback proofs
-- add no axioms.
/-- info: 'CSD.LF4.naimarkV_isom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.naimarkV_isom

/-- info: 'CSD.LF4.naimarkV_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.naimarkV_pullback

/-- info: 'CSD.LF4.canonicalNaimark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.canonicalNaimark

-- LF5-A (von Neumann measurement coupling unitary): the adder permutation
-- σ(j,k) = (j, j+k) on Fin N × Fin N (system × apparatus), its manifestly-unitary
-- permutation matrix, and the ground-apparatus copy σ(j,0) = (j,j). First file of
-- the LF5 measurement-dynamics layer (the D1 frontier). Foundational triple.
/-- info: 'CSD.LF5.vnUnitary_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.vnUnitary_unitary

/-- info: 'CSD.LF5.vnPerm_ground' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.vnPerm_ground

-- LF5-B (measurement flow): the reindexed vN coupling unitary acting on the
-- dilated projective ontic space ℙ ℂ (EuclideanSpace ℂ (Fin m)) (canonically
-- ℂℙ^{N·N−1} at e = finProdFinEquiv). FS-invariance (the Liouville / hΦ_pres
-- content), Φ_vN ≠ id (genuine measurement dynamics, the D1 increment), and the
-- basis-ray adder action (the LF5-C input). Foundational triple.
/-- info: 'CSD.LF5.measurementFlow_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.measurementFlow_measurePreserving

/-- info: 'CSD.LF5.measurementFlow_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.measurementFlow_ne_id

/-- info: 'CSD.LF5.measurementFlow_mk_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.measurementFlow_mk_single

-- LF5-C (de-isolation realises the dilation): the dynamically-realised Naimark
-- dilation isometry V = U_vN ∘ (· ⊗ a₀) of the computational-basis projective
-- POVM — isometry, pointer-block pullback Vᴴ Πᵢ V = |eᵢ⟩⟨eᵢ|, the NaimarkDilation
-- inhabitant, the post-flow coordinates U_vN(ψ⊗a₀) = ∑ⱼ ψⱼ·(eⱼ⊗aⱼ), the block-i
-- Born weight ‖⟨eᵢ,ψ⟩‖², and the projective-level realisation theorem tying the
-- LF5-B flow Φ_vN to the dilation. Foundational triple.
/-- info: 'CSD.LF5.vnNaimark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.vnNaimark

/-- info: 'CSD.LF5.vnDilationV_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.vnDilationV_pullback

/-- info: 'CSD.LF5.vnDilationV_isom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.vnDilationV_isom

/-- info: 'CSD.LF5.vnDilation_block_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.vnDilation_block_weight

/-- info: 'CSD.LF5.measurementFlow_realises_dilation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.measurementFlow_realises_dilation

/-- info: 'CSD.LF5.vnDilationV_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.vnDilationV_mulVec

/-- info: 'CSD.LF5.basisPOVM_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.basisPOVM_weight

-- LF5-D part 1 (the unconditional Born-region engine): the general-N Born =
-- FS-volume results and the POVM tranche wrappers with the hpos genericity
-- hypothesis retired — valid for every unit ψ, vanishing amplitudes included.
-- Per-cell dichotomy: positive cells by the closed-simplex subset argument,
-- zero cells by the det-0 null image + the joint Dirichlet law (the cells
-- genuinely collapse to FS-null sets; no carving). Additive over the audited
-- originals in MomentBornN / BornFrequencyN / POVMVolume. Carving-free,
-- Gleason-free; foundational triple only.
/-- info: 'CSD.LF4.fs_born_volume_ratio_N_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_born_volume_ratio_N_uncond

/-- info: 'CSD.LF4.fs_born_volume_ratio_N_apex_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fs_born_volume_ratio_N_apex_uncond

/-- info: 'CSD.LF4.bornRegion_fs_measure_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.bornRegion_fs_measure_uncond

/-- info: 'CSD.LF4.born_frequency_convergence_N_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.born_frequency_convergence_N_uncond

/-- info: 'CSD.LF4.povm_born_eq_dilated_volume_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.povm_born_eq_dilated_volume_uncond

/-- info: 'CSD.LF4.povm_born_frequency_volume_uncond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.povm_born_frequency_volume_uncond

-- LF5-D part 2 (pointer frequencies of the de-isolation flow → Born): the
-- unconditional engine instantiated at the dynamically-realised dilation
-- vnNaimark, at the non-generic post-flow state Vψ (off-diagonal cells FS-null).
-- Pointer-i committed FS volume = Born weight ‖⟨eᵢ,ψ⟩‖² for every unit ψ, and
-- the empirical capstone: i.i.d. FS trials on the dilated ℂℙ^{N²−1} have
-- pointer-block frequencies → Born a.s. Foundational triple.
/-- info: 'CSD.LF5.vnDilation_pointer_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.vnDilation_pointer_volume

/-- info: 'CSD.LF5.vnDilation_pointer_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.vnDilation_pointer_frequency

-- LF5-E (capstone): the LF5 layer headline measurement_flow_born_frequency —
-- the single named chain theorem: Φ_vN ≠ id (genuine measurement dynamics),
-- FS measure-preserving (Liouville admissibility), context-fixed (the same
-- flow realises the dilation for every preparation), pointer-i committed FS
-- volume = Born weight, and a.s. pointer-block frequencies → Born, for every
-- unit ψ. Pure assembly of the LF5-B/C/D theorems (no new mathematical
-- content); closes the single-system projective tier of D1. Foundational
-- triple.
/-- info: 'CSD.LF5.measurement_flow_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.measurement_flow_born_frequency

-- Trial-witness tranche (2026-06-11): the canonical i.i.d. FS trial process.
-- Until this tranche every volume-frequency capstone quantified over an
-- abstract trial bundle (Ω, Pr, X, hX, hlaw, hindep) that no corpus theorem
-- constructed. The canonical coordinate process (Ω = ℕ → ℂℙ^{N−1},
-- Pr = Measure.infinitePi (fun _ => fubiniStudyMeasure p₀), X n = (· n))
-- inhabits the bundle: marginal law via Measure.infinitePi_map_eval, joint
-- independence via iIndepFun_infinitePi, indicator pairwise independence via
-- IndepFun.comp (the Cat-1 glue iIndepFun.pairwise_indepFun_indicator_preimage).
-- The _canonical capstones are the originals with the trial bundle discharged,
-- conclusions verbatim. Measure-theoretic existence of the sampling law only:
-- the physical i.i.d.-preparation reading remains the LF1 typicality posit
-- (A5). Foundational triple throughout; Gleason-free.
/-- info: 'Set.indicator_const_preimage_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Set.indicator_const_preimage_comp

/--
info: 'ProbabilityTheory.iIndepFun.pairwise_indepFun_indicator_preimage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.iIndepFun.pairwise_indepFun_indicator_preimage

/-- info: 'ProbabilityTheory.iIndepFun_eval_infinitePi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.iIndepFun_eval_infinitePi

/-- info: 'CSD.LF4.fsTrial_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fsTrial_law

/-- info: 'CSD.LF4.fsTrial_pairwise_indepFun_indicator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.fsTrial_pairwise_indepFun_indicator

/-- info: 'CSD.LF4.born_frequency_convergence_N_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.born_frequency_convergence_N_canonical

/--
info: 'CSD.LF5.measurement_flow_born_frequency_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.measurement_flow_born_frequency_canonical

-- LF5-F: bornRegion pairwise disjointness, the per-microstate outcome map, and
-- the outcome-frequency capstone (single union event per pointer, not a sum of
-- cell frequencies). Closes the owed-since-aeece86 outcome function. The cells
-- are the same ψ-indexed moment-subdivision cells (no carving); Φ = id (D1).
-- Foundational triple throughout; Gleason-free.
/-- info: 'CSD.LF4.bornRegion_pairwiseDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.bornRegion_pairwiseDisjoint

/-- info: 'CSD.LF4.bornOutcome_preimage_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.bornOutcome_preimage_some

/-- info: 'CSD.LF4.bornOutcome_ae_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.bornOutcome_ae_isSome

/-- info: 'CSD.LF5.vnPointerOutcome_preimage_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.vnPointerOutcome_preimage_some

/--
info: 'CSD.LF5.measurement_flow_outcome_frequency' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.measurement_flow_outcome_frequency

/--
info: 'CSD.LF5.measurement_flow_outcome_frequency_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.measurement_flow_outcome_frequency_canonical

-- LF5 QEC tranche (SyndromeFlow): the three-qubit bit-flip code's syndrome
-- measurement as a coarse-grained de-isolation flow. The stabilisers Z₁Z₂, Z₂Z₃
-- are diagonal in the computational basis, so the syndrome is a coarse-graining
-- (synClass) of the LF5 N=8 Z-basis measurement flow; the syndrome-block FS
-- volume equals the block sum of computational-basis Born weights = a sum of
-- Fubini–Study volumes (vnDilation_pointer_volume at N=8 + finite additivity);
-- the codeword corollary gives the deterministic syndrome + matrix-transport
-- recovery. Projective / coherent-error tier only; Born numbers reused from the
-- FS-volume engine; A5 posited; decoherence/partial-trace NOT here (gated
-- entangled tier). Foundational triple only.
/-- info: 'CSD.LF5.synClass_fiber_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.synClass_fiber_card

/-- info: 'CSD.LF5.errorSyndrome_synClass3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.errorSyndrome_synClass3

/-- info: 'CSD.LF5.syndromeRegion_fs_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.syndromeRegion_fs_volume

/-- info: 'CSD.LF5.syndromeWeight_eq_fs_volume_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.syndromeWeight_eq_fs_volume_sum

/-- info: 'CSD.LF5.syndromeWeight_X1_logical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.syndromeWeight_X1_logical

/-- info: 'CSD.LF5.syndrome_flow_born_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.syndrome_flow_born_volume

-- LF5 QEC syndrome tranche (SyndromeOutcome): the mechanical syndrome-granularity
-- coarse-graining (synClass) of the pointer-level LF5-D frequency
-- (vnDilation_pointer_frequency) and LF5-F outcome map (vnPointerOutcome). At N=8:
-- the syndrome-class block frequencies converge a.s. to syndromeWeight (a finite
-- class sum of pointer-block limits, tendsto_finset_sum); synOutcome is the
-- per-microstate syndrome outcome function (vnPointerOutcome.map synClass) whose
-- some-s fibre is the class-block union; the syndrome outcome event frequency
-- (a single event per syndrome) converges a.s. to syndromeWeight (union-indicator
-- split over the genuinely disjoint class cells via bornRegion_pairwiseDisjoint +
-- e injectivity). Projective / coherent-error tier; Born numbers reused; A5 posited;
-- decoherence NOT here. Foundational triple only.
/-- info: 'CSD.LF5.syndrome_flow_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.syndrome_flow_born_frequency

/-- info: 'CSD.LF5.syndrome_flow_born_frequency_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.syndrome_flow_born_frequency_canonical

/-- info: 'CSD.LF5.synOutcome_preimage_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.synOutcome_preimage_some

/-- info: 'CSD.LF5.syndrome_flow_outcome_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.syndrome_flow_outcome_frequency

/-- info: 'CSD.LF5.syndrome_flow_outcome_frequency_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF5.syndrome_flow_outcome_frequency_canonical

-- LF6-A.1 (ForcedContextuality): the conceptual crux of the entangled-singlet
-- de-isolation tier (first concrete attack on D1's entangled frontier). A product
-- (setting-local, non-contextual) outcome-partition of Σ on a shared (Λ,μ) IS a
-- deterministic LHV model; by Bell/CHSH no such partition reproduces the singlet,
-- so any de-isolation carve realising the singlet is jointly contextual (FORCED,
-- not posited). no_product_partition_realises_singlet routes through E91
-- lhvCHSH_abs_le_two (the LHV |S|≤2 cap) + Bell.chsh_singlet_at_optimal_angles
-- (the singlet 2√2); it REUSES the corpus Bell machinery, no Bell re-proof.
-- engine_joint_nonfactorises (P_st(s,t) ≠ P_A·P_B = 1/4 at aligned axes) and
-- engine_marginal_factorises (each marginal = 1/2, no-signalling, reusing LF3
-- marginal_*/no_signalling_*) are the Σ-volume engine's non-factorising-joint /
-- factorising-marginal pair. productPartition_nonvacuous: product partitions exist
-- and reproduce SOME (non-singlet) correlation, so the no-go is non-vacuous.
-- Residue A5 (entangled sector posited); LF6-A.2 (full ℂℙ¹⁵ de-isolation flow)
-- deferred. Foundational triple only.
/-- info: 'CSD.LF6.no_product_partition_realises_singlet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.no_product_partition_realises_singlet

/-- info: 'CSD.LF6.productPartition_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.productPartition_nonvacuous

/-- info: 'CSD.LF6.engine_joint_nonfactorises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.engine_joint_nonfactorises

/-- info: 'CSD.LF6.engine_marginal_factorises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.engine_marginal_factorises

-- LF6-C.1 (GHZContextuality): the multipartite analogue of A.1; the first
-- general-N-tier instance of D1's entangled frontier. GHZ forces contextuality
-- DETERMINISTICALLY (Mermin all-or-nothing: no LHV plus/minus 1 assignment at all),
-- a qualitatively stronger forcing than the singlet's statistical CHSH bound.
-- no_product_partition_realises_ghz: a product (setting-local, non-contextual)
-- plus/minus 1 partition reproducing the four GHZ perfect correlations forces each
-- product integrand pointwise-determinate a.e. (pm_ae_eq, where the plus/minus 1
-- hypothesis is load-bearing), yielding ONE microstate with a deterministic local
-- assignment that CSD.Empirical.GHZ.no_lhv_assignment_for_ghz forbids; it ROUTES
-- THROUGH that no-go, no GHZ re-proof. ghz_each_correlation_locally_realisable
-- isolates locality as the other load-bearing leg (each correlation alone is
-- locally realisable). ghz_engine_joint_nonfactorises (<XXX>=1 != 0*0*0) and
-- ghz_engine_marginal_factorises (each single-wing marginal = 0, no-signalling)
-- are the Sigma-volume engine's non-factorising-joint / factorising-marginal pair.
-- productPartition_ghz_nonvacuous: product partitions exist. Residue A5 (GHZ
-- entangled sector posited); LF6-C.2 (full GHZ de-isolation flow) built below.
-- Foundational triple only.
/-- info: 'CSD.LF6.no_product_partition_realises_ghz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.no_product_partition_realises_ghz

/-- info: 'CSD.LF6.productPartition_ghz_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.productPartition_ghz_nonvacuous

/-- info: 'CSD.LF6.ghz_engine_joint_nonfactorises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghz_engine_joint_nonfactorises

/-- info: 'CSD.LF6.ghz_engine_marginal_factorises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghz_engine_marginal_factorises

/-- info: 'CSD.LF6.ghz_each_correlation_locally_realisable' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghz_each_correlation_locally_realisable

/-- info: 'CSD.LF6.ghz_forced_contextuality_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghz_forced_contextuality_capstone

-- LF6-C.2 (GHZDeisolationFlow): the DYNAMICAL realisation of the multipartite GHZ
-- de-isolation tier, mirroring A.2 at three parties. A genuine deterministic
-- FS-measure-preserving de-isolation flow Φ ≠ id (LF5 measurementFlow @ N=8 on the
-- dilated Σ' = ℂℙ^{63} = ℙ(ℂ⁸⊗ℂ⁸)) whose context-fixed BornRegion pointer-block volumes
-- are the GHZ Born weights. ghzDeisolation_pointer_volume (the headline) COMPOSES LF5
-- vnDilation_pointer_volume @ N=8 (pointer-block FS volume = ‖⟨e_i, φ⟩‖², Gleason-free,
-- Born = volume IMPORTED from the DH/FS-volume engine, not re-derived) with the reindex
-- coordinate-Born identity nudgedGHZ_born (nudgedGHZ = ghzState in the Fin 8 computational
-- basis; ghz_normSq_eq_weight GENUINELY COMPUTES the diagonal weights 1/2 on (0,0,0)/(1,1,1),
-- 0 elsewhere). ghzDeisolation_frequency: a.s. block frequencies → the GHZ Born weight (LF5
-- vnDilation_pointer_frequency @ N=8 + nudgedGHZ_born). This is the MINIMAL computational-basis
-- carve (diagonal weights); ghzDeisolation_contextuality_anchor RE-EXPORTS C.1
-- no_product_partition_realises_ghz as the contextuality anchor of the DEFERRED Mermin-context
-- carve (the diagonal carve is NOT itself contextual; the Mermin X/Y carve tying block
-- correlations to C.1, three-party analogue of A.2's blockVolume_correlation, is the deferred
-- increment, as is the local product flow V_0⊗V_1⊗V_2). Flow REALISES (not derives) the GHZ
-- measurement. Residue A5 (GHZ entangled sector posited). Foundational triple only, no busch.
/-- info: 'CSD.LF6.ghzDeisolation_pointer_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzDeisolation_pointer_volume

/-- info: 'CSD.LF6.ghzDeisolation_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzDeisolation_frequency

/-- info: 'CSD.LF6.ghzDeisolation_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzDeisolation_ne_id

/-- info: 'CSD.LF6.ghzDeisolation_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzDeisolation_measurePreserving

/-- info: 'CSD.LF6.ghzDeisolation_contextuality_anchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzDeisolation_contextuality_anchor

/-- info: 'CSD.LF6.ghzDeisolation_flow_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzDeisolation_flow_capstone

-- LF6-C.3 (GHZMerminCarve, 2026-07-01): the GHZ Mermin-context carve — the GENUINE
-- contextual increment C.2 deferred. NEW infrastructure: the GHZ Pauli-context joint
-- eigenstructure (ghzMerminEig, the tensor of the genuine single-qubit sigma_x/sigma_y
-- eigenstates; localEig_eigenvector proves each local factor is a real Pauli eigenvector
-- with eigenvalue signC o = ±1 — the three-party analogue of LF3 singletJointEig), plus
-- the Born identity ghzMerminEig_born (‖⟨ghz, ghzMerminEig ctx o⟩‖² = (1/16)(1+signProd o·pv)²,
-- genuinely computed from the 8 GHZ basis evaluations + the local amplitudes).
-- ghzDeisolation_blockVolume_correlation (THE headline): for every Mermin context with real
-- phase product pv, the carve's sign-product-weighted pointer-block FS-volume sum = pv = the
-- Mermin expectation (⟨XXX⟩=+1, ⟨XYY⟩=⟨YXY⟩=⟨YYX⟩=−1). GENUINELY COMPUTED (LF5
-- vnDilation_pointer_volume @ N=8 block volumes composed with the Mermin Born identity), NOT
-- asserted — this is what C.2's diagonal re-export lacked. carveBlockCorrelation_eq_xxx ties the
-- carve's ⟨XXX⟩ to the QM Hilbert Mermin expectation (via ghz_expectation_xxx) through distinct
-- machinery meeting at +1. ghzDeisolation_carve_not_product (the dynamical carve-tie, FOUR-CONTEXT
-- tie CLOSED): feeds the carve's OWN four achieved Mermin correlations into C.1
-- no_product_partition_realises_ghz — no setting-local ±1 product partition reproduces them,
-- triggering Mermin's +1=−1 all-or-nothing contradiction; upgrades C.2's bare re-export
-- ghzDeisolation_contextuality_anchor to a genuine carve-tied theorem. Born = FS-volume IMPORTED
-- from the DH/moment-map engine, not re-derived; flow realises not derives; only the local
-- single-qubit eigen-equation proved (tripartite eigen-eq is the tensor, definitional). Residue A5
-- (GHZ entangled sector posited). Foundational triple only, no busch, no native_decide.
/-- info: 'CSD.LF6.localEig_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localEig_eigenvector

/-- info: 'CSD.LF6.ghzMerminEig_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzMerminEig_born

/-- info: 'CSD.LF6.ghzDeisolation_blockVolume_correlation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzDeisolation_blockVolume_correlation

/-- info: 'CSD.LF6.merminCarveCorrelation_eq_xxx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.merminCarveCorrelation_eq_xxx

/-- info: 'CSD.LF6.merminCarveCorrelation_eq_xyy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.merminCarveCorrelation_eq_xyy

/-- info: 'CSD.LF6.merminCarveCorrelation_eq_yxy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.merminCarveCorrelation_eq_yxy

/-- info: 'CSD.LF6.merminCarveCorrelation_eq_yyx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.merminCarveCorrelation_eq_yyx

/-- info: 'CSD.LF6.ghzDeisolation_carve_not_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzDeisolation_carve_not_product

/-- info: 'CSD.LF6.ghzMermin_carve_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzMermin_carve_capstone

-- LF6-A.2 (SingletDeisolationFlow): the DYNAMICAL realisation of the entangled
-- de-isolation tier. A genuine deterministic FS-measure-preserving de-isolation
-- flow Φ ≠ id (LF5 measurementFlow @ N=4 on the dilated Σ' = ℂℙ¹⁵ = ℙ(ℂ²⊗ℂ²⊗ℂ²⊗ℂ²))
-- whose CONTEXTUAL joint-BornRegion carve reproduces the LF3 singlet kernel P_st.
-- singletDeisolation_pointer_volume (the headline) COMPOSES LF5 vnDilation_pointer_volume
-- @ N=4 (pointer-block FS volume = ‖⟨e_i, φ⟩‖², Gleason-free, Born=volume IMPORTED from
-- the DH/FS-volume engine) with the nudge coordinate-Born identity nudgedSinglet_born
-- (unitary-invariance step + LF3 singletJointEig_born), at the prepared state
-- φ = (U_A^x⊗U_B^y)† ψ⁻ (singlet in the rotated axis-context basis). The carve is the
-- joint moment subdivision, NEVER a setting-local {ptr_A=i}∩{ptr_B=j} product region.
-- singletDeisolation_blockVolume_correlation: the carve's block-volume correlation is
-- the singlet's −a·b (block volume = P_st + LF3 correlation_eq_neg_dot).
-- singletDeisolation_carve_contextual: ROUTES THROUGH A.1 no_product_partition_realises_singlet
-- — no setting-local ±1 product partition reproduces the carve's −a·b correlation, so the
-- carve is contextual (the safety anchor; does NOT assume the forbidden product structure).
-- singletDeisolation_frequency: a.s. block frequencies → P_st (LF5 vnDilation_pointer_frequency
-- @ N=4 + nudgedSinglet_born). Flow LOCAL (LF5 @ N=4); carve CONTEXTUAL (A.1). Flow
-- factorisation Φ = Φ_A ⊗ Φ_B deferred to LF6-A.3. Residue A5 (entangled sector posited);
-- generic context (P_st > 0, every Bell setting). Foundational triple only, no busch.
/-- info: 'CSD.LF6.singletDeisolation_pointer_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.singletDeisolation_pointer_volume

/-- info: 'CSD.LF6.singletDeisolation_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.singletDeisolation_frequency

/-- info: 'CSD.LF6.singletDeisolation_blockVolume_correlation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.singletDeisolation_blockVolume_correlation

/-- info: 'CSD.LF6.singletDeisolation_carve_contextual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.singletDeisolation_carve_contextual

/-- info: 'CSD.LF6.singletDeisolation_flow_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.singletDeisolation_flow_capstone

-- LF6-A.2 contextuality juxtaposition CLOSED: singletDeisolation_carve_not_product composes
-- the EXHIBITED carve's achieved block-volume correlation (carveBlockCorrelation, the s·t-weighted
-- sum of bornRegion FS volumes, discharged to −a·b via singletDeisolation_blockVolume_correlation)
-- with A.1 no_product_partition_realises_singlet in ONE theorem (no free −a·b; the carve's own
-- value is fed in). Foundational-triple-only.
/-- info: 'CSD.LF6.singletDeisolation_carve_not_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.singletDeisolation_carve_not_product

-- LF6-A.3 (2026-06-28): the LOCAL product de-isolation flow V_A ⊗ V_B realising the singlet.
-- The de-isolation can be local (factorises); the non-locality is entirely in the contextual
-- carve (A.2) and the entangled preparation (A5). Foundational triple only, no busch.
/-- info: 'CSD.LF6.localDeisolation_factorises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localDeisolation_factorises

/-- info: 'CSD.LF6.localDeisolation_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localDeisolation_pullback

/-- info: 'CSD.LF6.localDeisolation_pointer_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localDeisolation_pointer_volume

/-- info: 'CSD.LF6.localDeisolation_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localDeisolation_capstone

-- LF6-A.3 flow ↔ dilation tie (2026-06-28): the LOCAL flow realises the local Naimark
-- dilation, Φ_loc [ψ ⊗ (a₀⊗a₀)] = [V_loc ψ] for every nonzero ψ (matches LF5's
-- measurementFlow_realises_dilation). Closes the auditor Minor: the capstone now ties
-- the bundled flow and dilation. Foundational triple only, no busch.
/-- info: 'CSD.LF6.localDeisolationFlow_realises_localNaimark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.localDeisolationFlow_realises_localNaimark

-- LF6-C.4 (GHZLocalFlow, 2026-07-02): the manifestly LOCAL product de-isolation flow
-- V_loc = V_0 ⊗ V_1 ⊗ V_2 (three genuine N=2 wings) realising the three-qubit GHZ
-- measurement, the three-party analogue of A.3. ghzLocal_pullback GENUINELY composes the
-- three wing LF5 vnDilationV_pullback (via conjTranspose/mul_kronecker_mul + A.3's 2-wing
-- localDeisolation_pullback for the inner factor); the pointer-block FS volume = ghzWeight
-- (povm_born_eq_dilated_volume_uncond ∘ nudgedGHZ_born); the projectivised product flow
-- U_0 ⊗ U_1 ⊗ U_2 is FS-measure-preserving and ≠ id; the flow realises the local dilation.
-- The de-isolation CAN be local (three-party product, no non-local interaction); the GHZ
-- non-locality lives in the contextual carve (C.1/C.3) and the entangled preparation (A5).
-- Born = FS-volume imported, not re-derived. Foundational triple only, no busch.
/-- info: 'CSD.LF6.ghzLocal_factorises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzLocal_factorises

/-- info: 'CSD.LF6.ghzLocal_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzLocal_pullback

/-- info: 'CSD.LF6.ghzLocal_pointer_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzLocal_pointer_volume

/-- info: 'CSD.LF6.ghzLocalFlow_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzLocalFlow_measurePreserving

/-- info: 'CSD.LF6.ghzLocalFlow_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzLocalFlow_ne_id

/-- info: 'CSD.LF6.ghzLocalFlow_realises_localNaimark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzLocalFlow_realises_localNaimark

/-- info: 'CSD.LF6.ghzLocal_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzLocal_capstone

-- LF6-B.1 (Decoherence, 2026-06-28): decoherence as coarse-graining over a CONSERVATIVE
-- de-isolation flow — the first result on the open-system / partial-trace stratum of D1.
-- decohereReduced ψ = partialTraceRight (V |ψ⟩⟨ψ| Vᴴ) GENUINELY COMPUTES to the
-- Born-weighted diagonal mixture ∑ⱼ ‖⟨eⱼ,ψ⟩‖² • |eⱼ⟩⟨eⱼ| (dephases); off-diagonal
-- coherences are explicit zeros; diagonal weights are the Born weights, TIED to the
-- LF5/LF6 pointer-block FS typicality volumes (decoherence_diagonal_eq_pointer_volume,
-- vnDilation_pointer_volume); the de-isolation V is an isometry (conservative on the
-- joint, dissipative only on the marginal). Foundational triple only, no busch (the
-- partial-trace + dilation machinery is measure-theoretic / linear-algebraic, off the
-- ontic Born path). DEFERRED: continuous-time Lindblad / T1-T2; system-marginal
-- FS-volume-drift geometry; purity/entropy. Residue A5 (FS-typicality posited).
/-- info: 'CSD.LF6.decoherence_dephases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decoherence_dephases

/-- info: 'CSD.LF6.decoherence_offdiagonal_vanish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decoherence_offdiagonal_vanish

/-- info: 'CSD.LF6.decoherence_diagonal_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decoherence_diagonal_born

/-- info: 'CSD.LF6.decoherence_diagonal_eq_pointer_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decoherence_diagonal_eq_pointer_volume

/-- info: 'CSD.LF6.deisolation_conservative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.deisolation_conservative

/-- info: 'CSD.LF6.decoherence_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decoherence_capstone

-- LF6-B.2 (Decoherence, 2026-06-29): the QUANTITATIVE purity-drop / irreversibility witness.
-- The reduced state is a genuine density operator (decohereReduced_trace, Tr = ‖ψ‖², via
-- partialTraceRight_trace + deisolation_conservative Vᴴ V = 1); its purity Tr(ρ_red²) =
-- ∑ⱼ (‖⟨eⱼ,ψ⟩‖²)² (decohere_purity_eq, the reduced state being diagonal); purity ≤ 1
-- (decohere_purity_le_one, linear entropy ≥ 0); and STRICTLY < 1 for a measurement-basis
-- superposition with ≥2 nonzero Born weights (decohere_purity_lt_one_of_superposition) —
-- the pure input |ψ⟩⟨ψ| (purity 1) decoheres to a strictly mixed state. The irreversibility
-- narrated in B.1 is now theorem-backed (linear-entropy witness 1 − Tr(ρ²) > 0). The
-- superposition hypothesis is load-bearing (single eigenstate ⟹ purity stays 1). Foundational
-- triple only, no busch. DEFERRED: von Neumann entropy increase; continuous-time Lindblad /
-- environment growth. Residue A5 (FS-typicality posited).
/-- info: 'CSD.LF6.decohereReduced_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decohereReduced_trace

/-- info: 'CSD.LF6.decohere_purity_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decohere_purity_eq

/-- info: 'CSD.LF6.decohere_purity_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decohere_purity_le_one

/-- info: 'CSD.LF6.decohere_purity_lt_one_of_superposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decohere_purity_lt_one_of_superposition

/-- info: 'CSD.LF6.decoherence_irreversibility_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decoherence_irreversibility_capstone

-- LF6-B.3 (Decoherence, 2026-07-01): the von Neumann (Shannon-of-the-Born-vector) entropy-increase
-- witness. The decohered reduced state is diagonal with the Born vector pⱼ = ‖⟨eⱼ,ψ⟩‖² on the
-- diagonal, so its von Neumann entropy is GENUINELY DERIVED (decohereReduced_eq_diagonal ∘
-- QuantumInfo.vonNeumannEntropy_diagonal) to be the Shannon entropy ∑ⱼ negMulLog(pⱼ) = −∑ pⱼ log pⱼ
-- (decohere_vonNeumann_entropy_eq); non-negative (decohere_vonNeumann_entropy_nonneg); and STRICTLY
-- positive for a measurement-basis superposition with ≥2 nonzero Born weights
-- (decohere_vonNeumann_entropy_pos_of_superposition). The pure input |ψ⟩⟨ψ| has S = 0
-- (vonNeumannEntropy_eq_zero_of_pure); the conservative de-isolation + pointer trace jumps it to
-- S > 0 — the entropy-increase irreversibility witness (0 → S > 0), completing B.1/B.2's
-- linear-entropy / purity account. The superposition hypothesis is load-bearing (single eigenstate
-- ⟹ S = 0, one pⱼ = 1 rest 0, negMulLog(1) = negMulLog(0) = 0). Foundational triple only, no busch.
-- DEFERRED: continuous-time Lindblad / environment growth. Residue A5 (FS-typicality posited).
/-- info: 'CSD.LF6.decohere_vonNeumann_entropy_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decohere_vonNeumann_entropy_eq

/-- info: 'CSD.LF6.decohere_vonNeumann_entropy_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decohere_vonNeumann_entropy_nonneg

/-- info: 'CSD.LF6.decohere_vonNeumann_entropy_pos_of_superposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decohere_vonNeumann_entropy_pos_of_superposition

/-- info: 'CSD.LF6.decoherence_vonNeumann_irreversibility_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.decoherence_vonNeumann_irreversibility_capstone

-- LF6-D (MaxEntangledDeisolationFlow, 2026-07-03): the first genuinely DIMENSION-GENERAL entangled
-- de-isolation instance. Before this the tier had only two hand-built instances (2x2 singlet A-tier,
-- 3-qubit GHZ C-tier); this makes "general-N" actually general — the d x d maximally-entangled state
-- Ψ_d = (1/√d)∑ᵢ|i⟩|i⟩, every d ≥ 2. maxEntangled d + medWeight (Born = 1/d on the diagonal, 0 off);
-- maxEntangled_normSq_eq_weight / sum_medWeight (unit-norm) / maxEntangled_marginal_uniform (the DIAGONAL
-- Born-weight marginal is uniform 1/d — not the full ρ_A = I/d). The de-isolation flow + Born-from-volume
-- REUSES the LF5 general-N engine at N = d·d: maxEntangledDeisolation_pointer_volume (the headline)
-- COMPOSES LF5 vnDilation_pointer_volume @ N=d·d (pointer-block FS volume = ‖⟨eᵢ,φ⟩‖², Gleason-free,
-- Born=volume IMPORTED from the DH/FS-volume engine) with the reindex coordinate-Born identity
-- nudgedMaxEntangled_born; maxEntangledDeisolation_frequency (a.s. block frequencies → medWeight);
-- ne_id (Φ≠id, 1<d·d) + measurePreserving. This is the LOAD-BEARING content: the LF6 de-isolation
-- dynamics + Born-from-volume is now genuinely DIMENSION-GENERAL, not tied to 2x2/GHZ. Forced
-- non-factorisation (no_product_partition_realises_maxEntangled, 2026-07-03 rewrite): DERIVED and
-- maxEntangled-specific, no longer a verbatim singlet re-export. (b) maxEntangledSector_eq_phiPlus:
-- Ψ_d's {0,1}² Schmidt sector IS the Bell Φ⁺ state up to √2/√d (FULL state, coherences included,
-- d-dependent). phiPlus_pauli_correlation: ⟨Φ⁺|σ·a⊗σ·b|Φ⁺⟩ = a_x b_x − a_y b_y + a_z b_z, COMPUTED
-- from the Hilbert space (mirrors LF3.expectation_formula on Φ⁺'s (0,0)/(1,1) support). (c)
-- no_product_partition_realises_phiPlus: no product partition reproduces Φ⁺'s OWN correlation — the
-- orthogonal xz-reflection reflectXZ of Bob's axis carries E_{Φ⁺} to the singlet's −a·b
-- (phiPlusCorrelation_reflectXZ), so Φ⁺ reaches the same 2√2 > 2 (LHV cap |S|≤2, lhvCHSH_abs_le_two),
-- reducing to no_product_partition_realises_singlet on the relabeled partition. So the CHSH violation is
-- DERIVED for Φ⁺ (not the singlet's imported by prose). Scope: forced by the CHSH-violating 2x2 Φ⁺
-- sector; a full general-d CGLMP result is NOT claimed. Born IMPORTED not derived (DH engine); flow
-- realises not derives. Residue A5 (entangled sector posited). Foundational triple only, no busch, no
-- native_decide.
/-- info: 'CSD.LF6.maxEntangledDeisolation_pointer_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.maxEntangledDeisolation_pointer_volume

/-- info: 'CSD.LF6.maxEntangledDeisolation_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.maxEntangledDeisolation_frequency

/-- info: 'CSD.LF6.maxEntangledDeisolation_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.maxEntangledDeisolation_ne_id

/-- info: 'CSD.LF6.maxEntangledDeisolation_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.maxEntangledDeisolation_measurePreserving

/-- info: 'CSD.LF6.maxEntangled_sector_marginal_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.maxEntangled_sector_marginal_uniform

/-- info: 'CSD.LF6.maxEntangledSector_eq_phiPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.maxEntangledSector_eq_phiPlus

/-- info: 'CSD.LF6.phiPlus_pauli_correlation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.phiPlus_pauli_correlation

/-- info: 'CSD.LF6.no_product_partition_realises_phiPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.no_product_partition_realises_phiPlus

-- LF6-7 (2026-07-12): the Φ⁺↔ψ⁻ transport recompute. reflectXZ (Bob's xz-axis flip) lifted to the
-- Hilbert-space level: phiPlus_pauli_correlation_reflectXZ recomputes the singlet's −a·b from Φ⁺'s OWN
-- derived expectation; phiPlus_transport_eq_singlet_expectation proves this equals LF3's independently
-- derived ⟨ψ⁻|σ·a⊗σ·b|ψ⁻⟩ — the two independent Bell derivations are one under reflectXZ (consolidation).
/-- info: 'CSD.LF6.phiPlus_pauli_correlation_reflectXZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.phiPlus_pauli_correlation_reflectXZ

/-- info: 'CSD.LF6.phiPlus_transport_eq_singlet_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.phiPlus_transport_eq_singlet_expectation

-- LF6-6 partial (2026-07-12): the partial-Schmidt (non-maximally-entangled) two-qubit correlation,
-- extending the LF6 correlation beyond equal Schmidt coefficients. Ψ(c,s)=c|00⟩+s|11⟩ gives
-- ⟨σ·a⊗σ·b⟩ = a_z b_z + 2cs(a_x b_x − a_y b_y) (psQubit_pauli_correlation), 2cs = concurrence; at
-- c=s=1/√2 it collapses to Φ⁺ (psQubit_pauli_correlation_maximal). Residual (needs Gisin, not in corpus):
-- the non-factorisation witness for unequal c≠s.
/-- info: 'CSD.LF6.psQubit_pauli_correlation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.psQubit_pauli_correlation

/-- info: 'CSD.LF6.psQubit_pauli_correlation_maximal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.psQubit_pauli_correlation_maximal

-- LF6-2 bounded core (2026-07-12): the qubit T2 dephasing quantum dynamical semigroup — the
-- continuous-time open-system de-isolation frontier. Φ_t(ρ) damps coherences by e^{-γt}, preserves
-- populations; dephasingChannel_semigroup (Φ_s∘Φ_t = Φ_{s+t}, the Markovian composition law) and
-- dephasingChannel_coherence_tendsto_zero (coherence → 0 as t→∞, γ>0: continuous-time einselection to
-- the pointer basis). Residual: the general Lindblad generator + complete positivity + T1 damping.
/-- info: 'CSD.LF6.dephasingChannel_semigroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.dephasingChannel_semigroup

/-- info: 'CSD.LF6.dephasingChannel_coherence_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.dephasingChannel_coherence_tendsto_zero

-- LF6-2 T1 amplitude damping (2026-07-14): the population-transferring companion of T2 dephasing.
-- dampingChannel Φ_t(ρ) = [[ρ₀₀+(1-e)ρ₁₁, √e·ρ₀₁],[√e·ρ₁₀, e·ρ₁₁]] (e = e^{-γt}). dampingChannel_
-- semigroup (Φ_s∘Φ_t = Φ_{s+t}), dampingChannel_trace (channel), dampingChannel_ground_population (the
-- T1 signature: population flows 1→0), dampingChannel_excited_tendsto_zero + _coherence_tendsto_zero
-- (relaxation to the ground state as t→∞, γ>0). Foundational triple.
/-- info: 'CSD.LF6.dampingChannel_semigroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.dampingChannel_semigroup

/-- info: 'CSD.LF6.dampingChannel_ground_population' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.dampingChannel_ground_population

/-- info: 'CSD.LF6.dampingChannel_excited_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.dampingChannel_excited_tendsto_zero

/-- info: 'CSD.LF6.no_product_partition_realises_maxEntangled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.no_product_partition_realises_maxEntangled

/-- info: 'CSD.LF6.maxEntangledDeisolation_flow_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.maxEntangledDeisolation_flow_capstone

-- LF6-D QM side (CGLMPQutrit, 2026-07-03): the genuinely d=3-INTRINSIC CGLMP violation for the
-- maximally-entangled qutrit Ψ_3, the QM payoff of the CGLMP infrastructure. pQM x y c = P(A_x−B_y=c)
-- is the GENUINE outcome-difference Born table: bornPair x y k l = ‖⟨outcome_{k,l}, maxEntangled 3⟩‖²
-- (squared inner product with Ψ_3), the outcome vectors the CGLMP phase-basis measurement vectors
-- (aVec_unit/bVec_unit unit vectors), pQM the k−l marginal (bornPair_periodic: Born depends only on
-- k−l). bornPair_value computes it via the roots-of-unity geometric sum ‖1+w+w²‖²=3+4cosφ+2cos2φ
-- (normSq_geom) + the diagonal Ψ_3 contraction (inner_outcome_collapse). Under offsets α₁=0,α₂=1/2,
-- β₁=−1/4,β₂=1/4 the four CGLMP-positive entries are (4+2√3)/9, the four negative 1/9, giving the
-- EXACT value cglmp_maxEntangled_qutrit_eq: cglmp 3 pQM = (12+8√3)/9 ≈ 2.8729. cglmp_maxEntangled_qutrit_gt_two:
-- > 2 (the √3 irrational; no rational/half-integer setting violates — those give exactly 2). The
-- d-intrinsic no-go no_lhv_realises_maxEntangled_cglmp: any LHV reproducing pQM would give
-- cglmpLHV = cglmp 3 pQM > 2, contradicting cglmp_lhv_bound_three (I_3 ≤ 2). SUPERSEDES the 2×2 Φ⁺
-- CHSH sector routing of no_product_partition_realises_maxEntangled for d=3 (that theorem is untouched;
-- this is additive). Scope: d=3 only; general-d (d≥4) CGLMP is the residual. Foundational triple only,
-- no busch, no native_decide (decide for finite ZMod facts only).
/-- info: 'CSD.LF6.CGLMPQutrit.cglmp_maxEntangled_qutrit_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.CGLMPQutrit.cglmp_maxEntangled_qutrit_eq

/-- info: 'CSD.LF6.CGLMPQutrit.cglmp_maxEntangled_qutrit_gt_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.CGLMPQutrit.cglmp_maxEntangled_qutrit_gt_two

/-- info: 'CSD.LF6.CGLMPQutrit.no_lhv_realises_maxEntangled_cglmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.CGLMPQutrit.no_lhv_realises_maxEntangled_cglmp

-- LF6-D QM side GENERAL-d (CGLMPQudit, 2026-07-04): the CGLMP violation for the maximally-entangled
-- qudit Ψ_d = maxEntangled d extended to EVERY d ≥ 2, closing the statistical non-locality axis at
-- full dimensional generality (the d=3 qutrit result above is untouched; this is additive). The Born
-- table is GENUINE: bornPair x y k l = ‖⟨outcome_{k,l}, maxEntangled d⟩‖² (squared inner product with
-- Ψ_d), and pQM_closed derives the standard maximally-entangled closed form
-- pQM x y c = 1/(2 d² sin²(π(c.val+δ)/d)) via the d-th-roots-of-unity Dirichlet/Fejér kernel
-- (dirichlet_kernel: ‖∑_{j<d} e^{ijφ}‖² = sin²(dφ/2)/sin²(φ/2), the general-d analogue of the qutrit
-- normSq_geom), the quarter-integer numerator sin²(π(m+δ))=1/2, and the diagonal Ψ_d contraction. The
-- cglmp value is the closed-form sum cglmp_maxEntangled_qudit_closed = ∑_{k<⌊d/2⌋}(1−2k/(d−1))·
-- (2/d²)(csc²(π(k+1/4)/d)−csc²(π(k+3/4)/d)). cglmp_maxEntangled_qudit_gt_two (hd:2≤d): cglmp d pQM > 2
-- is a REAL analytic inequality for ALL d ≥ 2 (NOT decide over finite d, NOT axiomatised): every
-- bracket term is nonneg (sin-monotonicity) and every coefficient nonneg, so the sum dominates its k=0
-- term, and that term alone is ≥ 32/π²−8/9 > 2 uniformly in d (sin x ≤ x on the π/(4d) arm, Jordan's
-- sin x ≥ 2x/π on the 3π/(4d) arm, π < 3.15). The general-d Bell force
-- no_lhv_realises_maxEntangled_cglmp_d: any LHV reproducing pQM gives cglmpLHV = cglmp d pQM > 2,
-- contradicting cglmp_lhv_bound (I_d ≤ 2, all d). Foundational triple only, no busch, no native_decide.
/-- info: 'CSD.LF6.CGLMPQudit.pQM_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.CGLMPQudit.pQM_closed

/-- info: 'CSD.LF6.CGLMPQudit.cglmpBracket_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.CGLMPQudit.cglmpBracket_closed

/-- info: 'CSD.LF6.CGLMPQudit.cglmp_maxEntangled_qudit_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.CGLMPQudit.cglmp_maxEntangled_qudit_closed

/-- info: 'CSD.LF6.CGLMPQudit.cglmp_maxEntangled_qudit_gt_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.CGLMPQudit.cglmp_maxEntangled_qudit_gt_two

/-- info: 'CSD.LF6.CGLMPQudit.no_lhv_realises_maxEntangled_cglmp_d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.CGLMPQudit.no_lhv_realises_maxEntangled_cglmp_d

-- LF6-1 (2026-07-09): the flow capstone with conjunct 7 REROUTED through the d-intrinsic CGLMP force
-- (no LHV table reproduces pQM d, since cglmp d pQM > 2 in dimension d) instead of the 2×2 Φ⁺/CHSH
-- sector. Conjuncts 1–6 inherited from maxEntangledDeisolation_flow_capstone; still foundational-triple.
/-- info: 'CSD.LF6.maxEntangledDeisolation_flow_capstone_cglmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.maxEntangledDeisolation_flow_capstone_cglmp

-- GHZ_n tranche (GHZnDeisolationFlow, 2026-07-03): the DETERMINISTIC (Mermin) all-or-nothing forcing
-- axis at general PARTY number n, complementing the statistical (CGLMP) axis at general dimension d
-- (MaxEntangledDeisolationFlow + Mathlib/Probability/CGLMP). ghzN n = (|0..0⟩+|1..1⟩)/√2 on Fin (2^n)
-- (support 0 / topIdx n = 2^n−1); ghzNWeight (Born = 1/2 on the two all-equal outcomes, 0 else),
-- ghzN_normSq_eq_weight / sum_ghzNWeight (unit-norm, n≥1) / ghzN_born. The de-isolation flow +
-- Born-from-volume at N = 2^n (the clean general-PARTY core) REUSES the LF5 general-N engine:
-- ghzNDeisolation_pointer_volume COMPOSES LF5 vnDilation_pointer_volume @ N=2^n (pointer-block FS
-- volume = ‖⟨eᵢ,φ⟩‖², Gleason-free, Born=volume IMPORTED from the DH/FS-volume engine) with ghzN_born;
-- ghzNDeisolation_frequency (a.s. block freq → GHZ_n Born); ne_id (Φ≠id, 1<2^n) + measurePreserving.
-- The n-party DETERMINISTIC (Mermin) forcing (the load-bearing thesis part): no_lhvN_assignment_for_ghzN
-- (general n, combinatorial) + no_product_partition_realises_ghzN (general n, measure-theoretic —
-- generalises C.1's no_product_partition_realises_ghz via pm_ae_eq → l₀ → no_lhvN). Mechanism: the
-- three-party Mermin dance on parties {0,1,2}, spectators ≥3 measure X; the full-n product PARITY
-- contradiction (each party's ±1 appears squared → 4 correlations multiply to +1 while product of QM
-- values is −1) is a GENUINE n-party statement (product over Fin n, n-party contexts), NOT a hollow
-- re-export. no_lhv_assignment_for_ghz4 is the essentially-FOUR-party witness (all parties participate,
-- no spectator; via decide-free parity). Honest caveat: general-n forcing routes the contradiction
-- through the 3-party paradox embedded via X-spectators (does not exhibit essential n-party
-- entanglement beyond 3); physical regime n≥3 (targets = GHZ_n's Mermin correlations). Residual: the
-- uniform essentially-all-n-parties construction (n mod 4). Born IMPORTED not derived (DH engine);
-- flow realises not derives. Residue A5.
-- Foundational triple only, no busch, no native_decide (decide not used on headlines; ghz4 via ring/norm_num).
-- GHZ_n QM-link (deliverable 5, 2026-07-03): CLOSES the general-n QM-confirmation residual. The four ±1
-- targets of ReproducesGHZN / no_lhvN_assignment_for_ghzN are DERIVED to be GHZ_n's OWN tensor-Pauli
-- Mermin correlations ⟨GHZ_n|σ_{a_1}⊗…⊗σ_{a_n}|GHZ_n⟩ for every n≥3, NO LONGER n=3-anchored to
-- Empirical.GHZ. ghzN_expectation_corner: the genuine two-corner Hilbert reducer on Fin (2^n) (GHZ_n
-- supported on {0, topIdx n}, half-sum of four corner entries, ((√2)⁻¹)²=1/2 via the smul/single
-- expansion + toELin_single_coord). tensorPauliFin: the n-fold tensor Pauli via the product-of-factor-
-- entries Kronecker formula on the bit-decomposition basis (finFunctionFinEquiv). ghzN_mermin_correlations:
-- ⟨XXX…⟩=+1, ⟨XYY…⟩=⟨YXY…⟩=⟨YYX…⟩=−1 (spectator X-factors → +1 via prod_ghzNCtx; twisted 2-Y → cos π=−1
-- via Complex.I_mul_I). reproducesGHZN_QM_iff: ReproducesGHZN_QM ↔ ReproducesGHZN (the ±1 targets ARE the
-- .re QM correlations). no_product_partition_realises_ghzN_qm: the LF6-E forcing ROUTED through GHZ_n's
-- actual QM correlations, so general-n non-locality is genuinely GHZ_n-specific. Genuine derived Hilbert
-- computation, not asserted; foundational triple only, no busch, no native_decide (decide only on the finite
-- PauliAxis inequality PauliAxis.x ≠ PauliAxis.y). Residual sub-point: fully-general arbitrary-Pauli-tensor
-- reducer (Z factors, arbitrary axis patterns) not delivered; only the X/Y Mermin family the forcing needs.
/-- info: 'CSD.LF6.ghzN_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzN_norm

/-- info: 'CSD.LF6.sum_ghzNWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.sum_ghzNWeight

/-- info: 'CSD.LF6.ghzN_born' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzN_born

/-- info: 'CSD.LF6.ghzNDeisolation_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzNDeisolation_ne_id

/-- info: 'CSD.LF6.ghzNDeisolation_measurePreserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzNDeisolation_measurePreserving

/-- info: 'CSD.LF6.ghzNDeisolation_pointer_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzNDeisolation_pointer_volume

/-- info: 'CSD.LF6.ghzNDeisolation_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzNDeisolation_frequency

/-- info: 'CSD.LF6.no_lhvN_assignment_for_ghzN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.no_lhvN_assignment_for_ghzN

/-- info: 'CSD.LF6.no_product_partition_realises_ghzN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.no_product_partition_realises_ghzN

/-- info: 'CSD.LF6.no_lhv_assignment_for_ghz4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.no_lhv_assignment_for_ghz4

/-- info: 'CSD.LF6.ghzNDeisolation_flow_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzNDeisolation_flow_capstone

/-- info: 'CSD.LF6.ghzN_expectation_corner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzN_expectation_corner

/-- info: 'CSD.LF6.ghzN_mermin_correlations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.ghzN_mermin_correlations

/-- info: 'CSD.LF6.reproducesGHZN_QM_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.reproducesGHZN_QM_iff

/-- info: 'CSD.LF6.no_product_partition_realises_ghzN_qm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF6.no_product_partition_realises_ghzN_qm

-- Build 15a (Einselection, 2026-06-29): the first einselection / pointer-basis-selection
-- result on the LF6-B decoherence machinery. decohereReduced ψ (LF6-B) is diagonal in the
-- measurement (pointer) basis {eⱼ} (decohere_diagonal_in_pointer_basis), but conjugating by
-- the Hadamard qmH rotates it into a basis where the (0,1) coherence = (p₀−p₁)/2 PERSISTS
-- (decohere_hadamard_offDiag), nonzero for any qubit with distinct Born weights p₀≠p₁
-- (decohere_not_diagonal_in_rotated_basis). einselection bundles diagonal-in-pointer + nonzero
-- in the Hadamard rotation for the concrete witness (2,1) (p₀=4≠1=p₂, off-diag 3/2). The
-- preferred basis comes from the de-isolation/partial-trace CONTEXT, contrasting #29's
-- basis-covariant FS typicality (fubiniStudy_forced_by_symmetry, unique U(N)-invariant, picks
-- no basis). QM-validity/open-system layer; basis-SELECTIVITY of decoherence (not derived from
-- an environment Hamiltonian). Foundational triple only (off busch).
/-- info: 'CSD.Empirical.CSDBridge.Einselection.decohere_hadamard_offDiag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.decohere_hadamard_offDiag

/-- info: 'CSD.Empirical.CSDBridge.Einselection.decohere_diagonal_in_pointer_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.decohere_diagonal_in_pointer_basis

/-- info: 'CSD.Empirical.CSDBridge.Einselection.decohere_not_diagonal_in_rotated_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.decohere_not_diagonal_in_rotated_basis

/-- info: 'CSD.Empirical.CSDBridge.Einselection.einselectionWitness_offDiag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.einselectionWitness_offDiag

/-- info: 'CSD.Empirical.CSDBridge.Einselection.einselection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.einselection

-- Build 15a follow-up (#34, 2026-06-30): the degeneracy boundary of einselection + general-N
-- einselection. Qubit boundary: the rotated off-diagonal (p₀−p₁)/2 is nonzero IFF p₀ ≠ p₁
-- (decohere_hadamard_offDiag_ne_zero_iff); at p₀ = p₁ the dephased state is the maximally mixed
-- (1/2)·I (decohere_degenerate_half / degenerateWitness_decohere_half) which is invariant under
-- ANY unitary conjugation (decohere_degenerate_basis_invariant), so NO basis is einselected (the
-- einselection-FAILS side). General-N: the dephasing channel decohereReducedN kills off-diagonals
-- and keeps the diagonal pointer populations (einselectionN), with degenerate locus = equal
-- populations ρ i i = 1/N ⟹ (1/N)·I, basis-invariant (einselectionN_degenerate). Non-vacuity:
-- decohereReducedN_acts_nontrivial (off-diagonal nonzero before, zero after) +
-- decohereReducedN_maximally_mixed. The pointer basis is the COMPUTATIONAL basis by construction;
-- the ontic einselection-from-Σ-dynamics origin is GATED to the entangled tier / D1.
-- Foundational triple only (off busch).
/-- info: 'CSD.Empirical.CSDBridge.Einselection.decohere_hadamard_offDiag_ne_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.decohere_hadamard_offDiag_ne_zero_iff

/-- info: 'CSD.Empirical.CSDBridge.Einselection.decohere_degenerate_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.decohere_degenerate_half

/-- info: 'CSD.Empirical.CSDBridge.Einselection.decohere_degenerate_basis_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.decohere_degenerate_basis_invariant

/-- info: 'CSD.Empirical.CSDBridge.Einselection.einselection_degenerate_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.einselection_degenerate_boundary

/-- info: 'CSD.Empirical.CSDBridge.Einselection.decohere_degenerate_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.decohere_degenerate_scalar

/-- info: 'CSD.Empirical.CSDBridge.Einselection.einselectionN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.einselectionN

/-- info: 'CSD.Empirical.CSDBridge.Einselection.decohereReducedN_acts_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.decohereReducedN_acts_nontrivial

/-- info: 'CSD.Empirical.CSDBridge.Einselection.decohereReducedN_degenerate_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.decohereReducedN_degenerate_scalar

/-- info: 'CSD.Empirical.CSDBridge.Einselection.decohereReducedN_maximally_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.decohereReducedN_maximally_mixed

/-- info: 'CSD.Empirical.CSDBridge.Einselection.einselectionN_degenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.Einselection.einselectionN_degenerate

-- Build 15b (QECDecoherence, 2026-06-30): the QEC-corrects-decoherence companion to 15a. A
-- single-qubit error is the K2 bit-flip CHANNEL (CPTP, bitflip_error_cptp) whose Stinespring /
-- partial-trace origin is bitflip_error_is_decoherence (Φ ρ = traceRight(V ρ Vᴴ), Vᴴ V = 1):
-- the error is environmental entanglement traced away. The three-qubit code CORRECTS it:
-- recover ∘ error = id on a bare qubit (qubit_recover_compose_bitflip) and on the code density
-- (three_qubit_recover_density: Xⱼ(Xⱼ ρ Xⱼᴴ)Xⱼᴴ = ρ); qec_corrects_decoherence bundles the
-- Stinespring origin + syndrome-distinctness + exact vector recovery (bitflip_recovers).
-- Non-vacuity: the SAME channel corrupts a bare qubit (bitFlipChannel_corrupts_bare_qubit:
-- Φ(|0⟩⟨0|) ≠ |0⟩⟨0| for 0<p). csd_qec_decoherence_corrected transports it through a
-- CSDThreeQubitBundle. QM-OPERATIONAL (channel + correction) discharged here; the ontic
-- Σ-volume / partial-trace-volume-loss origin is GATED to the entangled tier (LF6 / D1).
-- Foundational triple only (off busch).
/-- info: 'CSD.Empirical.CSDBridge.QECDecoherence.bitflip_error_cptp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QECDecoherence.bitflip_error_cptp

/-- info: 'CSD.Empirical.CSDBridge.QECDecoherence.bitflip_error_is_decoherence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QECDecoherence.bitflip_error_is_decoherence

/-- info: 'CSD.Empirical.CSDBridge.QECDecoherence.qubit_recover_compose_bitflip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QECDecoherence.qubit_recover_compose_bitflip

/-- info: 'CSD.Empirical.CSDBridge.QECDecoherence.three_qubit_recover_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QECDecoherence.three_qubit_recover_density

-- The in-code channel-correction bridge (one Hilbert space): recoverⱼ ∘ errorⱼ = id on the
-- ENCODED density encodeDensity a b, lifting the correctable X branch to qubit j as the K2
-- unitaryChannel (the conjunct that earns qec_corrects_decoherence's name). error_moves_codeword
-- is the non-vacuity witness (X₁ displaces |000⟩).
/-- info: 'CSD.Empirical.CSDBridge.QECDecoherence.recover_channel_compose_error_on_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QECDecoherence.recover_channel_compose_error_on_code

/-- info: 'CSD.Empirical.CSDBridge.QECDecoherence.error_moves_codeword' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QECDecoherence.error_moves_codeword

/-- info: 'CSD.Empirical.CSDBridge.QECDecoherence.error_moves_encoded_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QECDecoherence.error_moves_encoded_density

/-- info: 'CSD.Empirical.CSDBridge.QECDecoherence.bitFlipChannel_corrupts_bare_qubit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QECDecoherence.bitFlipChannel_corrupts_bare_qubit

/-- info: 'CSD.Empirical.CSDBridge.QECDecoherence.qec_corrects_decoherence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QECDecoherence.qec_corrects_decoherence

/-- info: 'CSD.Empirical.CSDBridge.QECDecoherence.csd_qec_decoherence_corrected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QECDecoherence.csd_qec_decoherence_corrected

-- Volume-series canonical coverage (2026-06-15): the trial-witness discharge,
-- previously wired into only three headlines (born_frequency_convergence_N,
-- measurement_flow_born_frequency, measurement_flow_outcome_frequency), is now
-- applied to EVERY remaining volume-frequency headline. Each _canonical form is
-- a bare term-mode application of its parent with the abstract trial bundle
-- discharged at the in-tree FS coordinate process (fsTrialMeasure / fsTrial):
-- conclusions verbatim, hypothesis sets now Lean-inhabited rather than merely
-- classically satisfiable. The LF4 POVM headline lives in TrialWitness.lean
-- (import-direction constraint POVMVolume → BornRegionUncond → TrialWitness);
-- the Empirical/CSD headlines are centralised in
-- Empirical/CSD/VolumeCanonical.lean. Coverage/completeness, not new
-- mathematics: measure-theoretic existence of the i.i.d. sampling law only; the
-- physical FS-typical preparation reading remains the LF1 typicality / A5 posit.
-- Foundational triple throughout; Gleason-free.

/-- info: 'CSD.LF4.povm_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.LF4.povm_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.BellVolume.bell_singlet_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.BellVolume.bell_singlet_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.GHZVolume.ghz_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.GHZVolume.ghz_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.HardyVolume.hardy_max_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.HardyVolume.hardy_max_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.MalusVolume.csd_malus_law_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MalusVolume.csd_malus_law_canonical

/-- info: 'CSD.Empirical.CSDBridge.SternGerlachVolume.csd_sg_volume_certain_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SternGerlachVolume.csd_sg_volume_certain_canonical

/-- info: 'CSD.Empirical.CSDBridge.SternGerlachVolume.csd_sg_volume_half_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SternGerlachVolume.csd_sg_volume_half_canonical

/-- info: 'CSD.Empirical.CSDBridge.TrineVolume.trine_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.TrineVolume.trine_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.USDVolume.usd_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.USDVolume.usd_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.SICVolume.sic_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SICVolume.sic_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.WeakMeasurement.weak_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.SIC3Volume.sic3_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.SIC3Volume.sic3_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.MUB3Volume.mub3_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MUB3Volume.mub3_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.QutritPOVMVolume.noisy_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.QutritPOVMVolume.noisy_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.ContextVolume.context_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ContextVolume.context_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.ContextVolume.block_born_frequency_volume_event_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ContextVolume.block_born_frequency_volume_event_canonical

/-- info: 'CSD.Empirical.CSDBridge.ContextVolume.zz_parity_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ContextVolume.zz_parity_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.UncertaintyVolume.uncertainty_volume_frequency_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.UncertaintyVolume.uncertainty_volume_frequency_canonical

-- Kochen-Specker (Cabello-18) contextual Born weights as Kähler volumes: the representative
-- context (basis 0) built as a genuine OrthonormalBasis from the complexified/normalised
-- Cabello rays (orthonormality reusing cabello_pairwise_orthogonal_in_basis via the
-- complexification transport), then instantiating the context engine. Carving-free,
-- Gleason-free, foundational triple only.
/-- info: 'CSD.Empirical.CSDBridge.KochenSpecker.ksCtxVec_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.KochenSpecker.ksCtxVec_orthonormal

/-- info: 'CSD.Empirical.CSDBridge.KochenSpecker.ks18_context_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.KochenSpecker.ks18_context_born_frequency_volume

/-- info: 'CSD.Empirical.CSDBridge.KochenSpecker.ks18_context_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.KochenSpecker.ks18_context_born_frequency_volume_canonical

-- Mermin–Peres rank-2 observable (X⊗X) ±1-outcome Born weights as Kähler volumes: the
-- non-diagonal grid observable's eigenbasis (H⊗H) built as a genuine OrthonormalBasis from
-- the explicit (±1/2)-component vectors (orthonormality a clean norm_num computation), then
-- instantiating the degenerate-eigenspace engine block_born_frequency_volume at the
-- sign-parity block. Carving-free, Gleason-free, foundational triple only.
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpXXVec_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpXXVec_orthonormal

-- Eigenbasis-identity faithfulness lemmas: mpXXBasis really is the σx⊗σx eigenbasis,
-- machine-checked against the genuine Pauli observable sigmaX ⊗ₖ sigmaX (not a literal).
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpXXVec_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpXXVec_eigenvector

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpXXBlk_eq_zero_iff_eigval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpXXBlk_eq_zero_iff_eigval_one

-- Z⊗Z (diagonal) eigenbasis-identity lemmas: earn the σz⊗σz label for the engine-file
-- zz_parity_born_frequency_volume by composition (computational basis = σz⊗σz eigenbasis,
-- machine-checked against the genuine sigmaZ ⊗ₖ sigmaZ).
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpZZVec_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpZZVec_eigenvector

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpZZBlk_eq_zero_iff_eigval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpZZBlk_eq_zero_iff_eigval_one

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mp_xx_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mp_xx_born_frequency_volume

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mp_xx_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mp_xx_born_frequency_volume_canonical

-- The remaining seven Mermin–Peres square observables, each with a machine-checked
-- eigenbasis tie to the genuine Pauli observable (sigma_a ⊗ₖ sigma_b reindexed onto Fin 4).
-- Eigenvector faithfulness lemmas (the label earned, not asserted) + volume headlines.
-- Foundational-triple-only (no busch), carving-free, Gleason-free.

-- X⊗I (H⊗I frame)
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpXIVec_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpXIVec_eigenvector

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mp_xi_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mp_xi_born_frequency_volume

-- X⊗Z (H⊗I frame, shared eigenbasis with X⊗I)
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpXZVec_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpXZVec_eigenvector

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mp_xz_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mp_xz_born_frequency_volume

-- I⊗X (I⊗H frame)
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpIXVec_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpIXVec_eigenvector

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mp_ix_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mp_ix_born_frequency_volume

-- Z⊗X (I⊗H frame, shared eigenbasis with I⊗X)
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpZXVec_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpZXVec_eigenvector

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mp_zx_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mp_zx_born_frequency_volume

-- Z⊗I (computational frame)
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpZIVec_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpZIVec_eigenvector

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mp_zi_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mp_zi_born_frequency_volume

-- I⊗Z (computational frame)
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpIZVec_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpIZVec_eigenvector

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mp_iz_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mp_iz_born_frequency_volume

-- Y⊗Y (complex U_Y⊗U_Y frame; the hard cell)
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpYYVec_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpYYVec_eigenvector

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mp_yy_born_frequency_volume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mp_yy_born_frequency_volume

-- Block/+1-eigenspace certificates (the second half of the earned-label faithfulness
-- claim: the collapsed block {…} IS exactly the +1 eigenspace, machine-checked against
-- the eigenvalue vector). X⊗X and Z⊗Z block lemmas are pinned above; these are the
-- remaining seven cells.
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpXIBlk_eq_zero_iff_eigval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpXIBlk_eq_zero_iff_eigval_one

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpXZBlk_eq_zero_iff_eigval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpXZBlk_eq_zero_iff_eigval_one

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpIXBlk_eq_zero_iff_eigval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpIXBlk_eq_zero_iff_eigval_one

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpZXBlk_eq_zero_iff_eigval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpZXBlk_eq_zero_iff_eigval_one

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpZIBlk_eq_zero_iff_eigval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpZIBlk_eq_zero_iff_eigval_one

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpIZBlk_eq_zero_iff_eigval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpIZBlk_eq_zero_iff_eigval_one

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mpYYBlk_eq_zero_iff_eigval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mpYYBlk_eq_zero_iff_eigval_one

-- Z⊗I / I⊗Z canonical FS-trial witnesses (the computational-frame cells; the other
-- non-computational cells already carry _canonical pins above).
/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mp_zi_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mp_zi_born_frequency_volume_canonical

/-- info: 'CSD.Empirical.CSDBridge.MerminPeres.mp_iz_born_frequency_volume_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.MerminPeres.mp_iz_born_frequency_volume_canonical

/-! ### Operator-convexity ladder (Cat-1; L.0 predicate + L.1 inverse operator convexity
+ L.2 shifted-resolvent concavity rungs) -/

/-- info: 'Matrix.fromBlocks_inv_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.fromBlocks_inv_posSemidef

/-- info: 'Matrix.operatorConvexOn_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorConvexOn_inv

/-- info: 'Matrix.inv_loewner_convex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.inv_loewner_convex

/-- info: 'Matrix.cfc_inv_posDef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.cfc_inv_posDef

/-- info: 'Matrix.add_smul_one_posDef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.add_smul_one_posDef

/-- info: 'Matrix.cfc_add_inv_posDef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.cfc_add_inv_posDef

/-- info: 'Matrix.inv_shift_loewner_convex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.inv_shift_loewner_convex

/-- info: 'Matrix.cfc_neg_add_inv_posDef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.cfc_neg_add_inv_posDef

/-- info: 'Matrix.operatorConcaveOn_neg_add_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorConcaveOn_neg_add_inv

/-- info: 'Matrix.cfc_affine_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.cfc_affine_output

/-- info: 'Matrix.OperatorConcaveOn.affine_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.OperatorConcaveOn.affine_output

/-! ### Reframing lemma : operator concavity ↔ ordinary `ConcaveOn` of `A ↦ cfc f A` (L.3a unlock) -/

/-- info: 'Matrix.convex_spectralSet_Ioi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.convex_spectralSet_Ioi

/-- info: 'Matrix.operatorConcaveOn_of_concaveOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorConcaveOn_of_concaveOn

/-- info: 'Matrix.concaveOn_of_operatorConcaveOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.concaveOn_of_operatorConcaveOn

/-- info: 'Matrix.operatorConcaveOn_iff_concaveOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorConcaveOn_iff_concaveOn

/-- info: 'Matrix.operatorConcaveOn_rpow_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorConcaveOn_rpow_zero

/-- info: 'Matrix.operatorConcaveOn_rpow_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorConcaveOn_rpow_one

/-! ### A1 cfc-integral commutation + Löwner-order topology (OperatorConvex.lean `Integral`) -/

/-- info: 'Matrix.cfc_integral_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.cfc_integral_commute

/-- info: 'Matrix.isClosed_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.isClosed_posSemidef

/-! ### `CStarMatrix ↔ Matrix` transport bridge (OperatorConvexBridge.lean) -/

/-- info: 'Matrix.cstar_cfc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.cstar_cfc

/-- info: 'Matrix.cstar_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.cstar_le_iff

/-- info: 'Matrix.cstar_isStrictlyPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.cstar_isStrictlyPositive

/-- info: 'Matrix.matrix_log_le_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.matrix_log_le_log

/-! ### C^1 finite-dimensional Stone theorem (StoneC1.lean, W5-S2 under smoothness) -/

/-- info: 'CSD.StoneC1.eq_exp_of_hasDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.StoneC1.eq_exp_of_hasDeriv

/-- info: 'CSD.StoneC1.exp_smul_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.StoneC1.exp_smul_unitary

/-- info: 'CSD.StoneC1.stone_c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.StoneC1.stone_c1

/-- info: 'CSD.StoneC1.trivial_group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.StoneC1.trivial_group

/-- info: 'CSD.StoneC1.skew_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.StoneC1.skew_witness

/-! ### ECDLP reversible-circuit substrate (Reversible/{Circuit,Cost}.lean) -/

/-- info: 'Reversible.denoteGate_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.denoteGate_involutive

/-- info: 'Reversible.reversible_inverse_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.reversible_inverse_correct

/-- info: 'Reversible.reversible_inverse_correct'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.reversible_inverse_correct'

/-- info: 'Reversible.denote_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.denote_bijective

/-- info: 'Reversible.cost_comp_toffoli_count' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cost_comp_toffoli_count

/-- info: 'Reversible.cost_comp_toffoli_depth_le' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cost_comp_toffoli_depth_le

/-- info: 'Reversible.denoteGate_apply_of_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.denoteGate_apply_of_not_mem

/-- info: 'Reversible.denote_apply_of_forall_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.denote_apply_of_forall_not_mem

/-! ### ECDLP reversible modular addition (Reversible/ModAdd.lean, Tranche 2) -/

/-- info: 'Reversible.regVal_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.regVal_lt_two_pow

/-- info: 'Reversible.regVal_update_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.regVal_update_eq

/-- info: 'Reversible.fullAdder_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.fullAdder_correct

/-- info: 'Reversible.fullAdder_cost' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.fullAdder_cost

/-- info: 'Reversible.rippleAdder_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.rippleAdder_toffoli

/-- info: 'Reversible.rippleAdder_cnot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.rippleAdder_cnot

/-- info: 'Reversible.fullAdder_apply_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.fullAdder_apply_of_ne

/-- info: 'Reversible.fullAdder_correct_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.fullAdder_correct_general

/-! ### ECDLP ripple carry-chain arithmetic correctness (ModAdd.lean, Tranche 2 Pass 2 Stage B) -/

/-- info: 'Reversible.regValRange_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.regValRange_lt

/-- info: 'Reversible.rippleCirc_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.rippleCirc_invariant

/-- info: 'Reversible.rippleCirc_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.rippleCirc_correct

/-! ### ECDLP reversible modular multiplication (ModMul.lean, Tranche 3 Stage A + B.1) -/

/-- info: 'Reversible.mulConst_bijective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulConst_bijective

/-- info: 'Reversible.multiplier_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.multiplier_toffoli

/-- info: 'Reversible.rippleCirc_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.rippleCirc_toffoli

/-- info: 'Reversible.multiplier_ripple_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.multiplier_ripple_toffoli

/-! #### Stage B.1: per-step multiplication-accumulation correctness -/

/-- info: 'Reversible.regValRange_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.regValRange_split

/-- info: 'Reversible.rippleCirc_preserves_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.rippleCirc_preserves_external

/-- info: 'Reversible.accStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.accStep

/-! #### Stage B.2: the fold to `Acc = a · Y` -/

/-- info: 'Reversible.mulCircuit_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulCircuit_correct

/-- info: 'Reversible.mulLayout1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulLayout1

/-- info: 'Reversible.mulCircuit_correct_zmod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulCircuit_correct_zmod

/-! ### ECDLP reversible modular inverse (ModInv.lean, Tranche 4) -/

/-- info: 'Reversible.mul_modInv_of_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mul_modInv_of_unit

/-- info: 'Reversible.modInv_modInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modInv_modInv

/-- info: 'Reversible.modInv_isUnit_iff_coprime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modInv_isUnit_iff_coprime

/-- info: 'Reversible.mulConst_modInv_leftInverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulConst_modInv_leftInverse

/-- info: 'Reversible.mulConst_modInv_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulConst_modInv_bijective

/-! ### ECDLP layered-circuit depth (Depth.lean, Phase 2 S1) -/

/-- info: 'Reversible.denoteLayered_eq_denote_flatten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.denoteLayered_eq_denote_flatten

/-- info: 'Reversible.layeredToffoli_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.layeredToffoli_eq

/-- info: 'Reversible.rippleCirc_sequential_depth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.rippleCirc_sequential_depth

/-- info: 'Reversible.sequential_rippleCirc_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.sequential_rippleCirc_correct

/-- info: 'Reversible.reduceTree4_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.reduceTree4_wf

/-- info: 'Reversible.reduceTree4_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.reduceTree4_correct

/-- info: 'Reversible.parallelXLayer_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.parallelXLayer_wf

/-! ### ECDLP modular reduction (Reversible/ModReduce.lean, Phase 2 S4) -/

/-- info: 'Reversible.rippleCirc_carryout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.rippleCirc_carryout

/-- info: 'Reversible.rippleCirc_modReduce_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.rippleCirc_modReduce_ge

/-! ### ECDLP S6.3a complete single-step modular reduction (Reversible/ModReduceCtrl.lean) -/

/-- info: 'Reversible.modReduce_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modReduce_correct

/-- info: 'Reversible.modReduce_in_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modReduce_in_range

/-- info: 'Reversible.modReduceCtrl_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modReduceCtrl_toffoli

/-! ### ECDLP S6.3b modular adder (Reversible/ModularAdd.lean) -/

/-- info: 'Reversible.modAdd_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modAdd_correct

/-- info: 'Reversible.modAdd_preserves_operand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modAdd_preserves_operand

/-- info: 'Reversible.modAdd_in_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modAdd_in_range

/-- info: 'Reversible.modularAdd_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modularAdd_toffoli

/-! ### ECDLP S6.3c controlled modular adder (Reversible/ModularAddCtrl.lean) -/

/-- info: 'Reversible.cModAdd_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cModAdd_correct

/-- info: 'Reversible.cModAdd_preserves_operand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cModAdd_preserves_operand

/-- info: 'Reversible.cModAdd_preserves_ctrl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cModAdd_preserves_ctrl

/-- info: 'Reversible.cModAdd_in_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cModAdd_in_range

/-- info: 'Reversible.cModularAdd_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cModularAdd_toffoli

/-! ### ECDLP S6.3d-1 modular doubling (Reversible/ModularDouble.lean) -/

/-- info: 'Reversible.modDouble_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modDouble_correct

/-- info: 'Reversible.modDouble_in_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modDouble_in_range

/-- info: 'Reversible.copyReg_correct_operand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.copyReg_correct_operand

/-- info: 'Reversible.copyReg_correct_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.copyReg_correct_B

/-- info: 'Reversible.modDouble_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modDouble_toffoli

/-- info: 'Reversible.copyReg_cnot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.copyReg_cnot

/-! ### ECDLP S6.3d-2a Horner step + proven n=2 modular multiply (Reversible/ModularMul.lean) -/

/-- info: 'Reversible.hornerStep_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.hornerStep_correct

/-- info: 'Reversible.hornerStep_in_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.hornerStep_in_range

/-- info: 'Reversible.hornerStep_preserves_Y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.hornerStep_preserves_Y

/-- info: 'Reversible.mulStep2_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulStep2_correct

/-- info: 'Reversible.hornerStep_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.hornerStep_toffoli

/-- info: 'Reversible.modDouble_preserves_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modDouble_preserves_external

/-- info: 'Reversible.cModAdd_preserves_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cModAdd_preserves_external

/-- info: 'Reversible.hornerStep_preserves_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.hornerStep_preserves_external

/-! ### ECDLP S6.3d-2b general-n modular field multiply X·Y mod N (Reversible/ModularMulLoop.lean) -/

/-- info: 'Reversible.mulLoop_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulLoop_correct

/-- info: 'Reversible.mulLoop_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulLoop_invariant

/-- info: 'Reversible.mulLoop_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulLoop_toffoli

/-- info: 'Reversible.regValRange_eq_hornerVal_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.regValRange_eq_hornerVal_bits

/-- info: 'Reversible.horner_mod_step' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.horner_mod_step

/-- info: 'Reversible.mulLoopUpto_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulLoopUpto_preserves

/-! ### ECDLP S6.3-36a adder-parametric modular multiplier (Reversible/VerifiedAdder.lean) -/

/-- info: 'Reversible.genMul_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.genMul_correct

/-- info: 'Reversible.genMul_toffoli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.genMul_toffoli

/-- info: 'Reversible.genMul_corpusAdder_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.genMul_corpusAdder_correct

/-- info: 'Reversible.genMul_corpusAdder_toffoli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.genMul_corpusAdder_toffoli

/-- info: 'Reversible.genMul_corpusAdder_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.genMul_corpusAdder_eq

/-! ### ECDLP S6.3e-1 modular subtraction a-b mod N (Reversible/ModularSub.lean) -/

/-- info: 'Reversible.modSub_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modSub_correct

/-- info: 'Reversible.modSub_preserves_subtrahend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modSub_preserves_subtrahend

/-- info: 'Reversible.modSub_in_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modSub_in_range

/-- info: 'Reversible.modSub_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modSub_toffoli

/-- info: 'Reversible.rippleSub_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.rippleSub_correct

/-- info: 'Reversible.rippleSub_borrowout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.rippleSub_borrowout

/-- info: 'Reversible.fullSub_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.fullSub_correct

/-! ### ECDLP S6.3e-2a modular const-multiply c*a mod N + negation -b mod N (Reversible/ModularConst.lean) -/

/-- info: 'Reversible.modConstMul_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modConstMul_correct

/-- info: 'Reversible.modConstMul_preserves_operand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modConstMul_preserves_operand

/-- info: 'Reversible.modConstMul_in_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modConstMul_in_range

/-- info: 'Reversible.modConstMul_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modConstMul_toffoli

/-- info: 'Reversible.modNeg_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modNeg_correct

/-- info: 'Reversible.modNeg_in_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modNeg_in_range

/-- info: 'Reversible.modNeg_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modNeg_toffoli

/-! ### ECDLP SLP → circuit router STEP 1 (Reversible/ProgramRouter.lean) -/

/-- info: 'Reversible.contigBlock_injOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.contigBlock_injOn

/-- info: 'Reversible.add_bridge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.add_bridge

/-- info: 'Reversible.mul_bridge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mul_bridge

/-- info: 'Reversible.nsmul_bridge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.nsmul_bridge

/-- info: 'Reversible.neg_bridge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.neg_bridge

/-- info: 'Reversible.sub_bridge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.sub_bridge

/-- info: 'Reversible.modSub_preserves_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modSub_preserves_external

/-- info: 'Reversible.router_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.router_holds

/-- info: 'Reversible.compile_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.compile_correct

/-- info: 'Reversible.worked_compile_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.worked_compile_correct

/-! ### ECDLP SLP → circuit dispatcher STEP 2 (Reversible/ProgramRouterDoubling.lean) -/

/-- info: 'Reversible.mulLoop_preserves_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulLoop_preserves_external

/-- info: 'Reversible.modConstMul_preserves_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modConstMul_preserves_external

/-- info: 'Reversible.addWrap_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.addWrap_correct

/-- info: 'Reversible.subWrap_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.subWrap_correct

/-- info: 'Reversible.compileInstr_emits_mulLoop' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.compileInstr_emits_mulLoop

/-- info: 'Reversible.mulLoopEmissions_eq_mulCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulLoopEmissions_eq_mulCount

/-- info: 'Reversible.doubling_mulLoop_emissions' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.doubling_mulLoop_emissions

/-- info: 'Reversible.doubling_mulLoop_emissions_eq_8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.doubling_mulLoop_emissions_eq_8

/-- info: 'Reversible.worked_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.worked_value

/-! ### ECDLP SLP → circuit STEP 3: PROVEN gadget assembly (Reversible/DoublingAssembly.lean) -/

/-- info: 'Reversible.hornerStep_preserves_ctrl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.hornerStep_preserves_ctrl

/-- info: 'Reversible.mulLoop_preserves_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulLoop_preserves_X

/-- info: 'Reversible.mulLoop_preserves_ctrl_wire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mulLoop_preserves_ctrl_wire

/-- info: 'Reversible.nsmul_step_assembly_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.nsmul_step_assembly_correct

/-- info: 'Reversible.nsmul_step_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.nsmul_step_value

/-- info: 'Reversible.mul_step_assembly_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mul_step_assembly_correct

/-- info: 'Reversible.mul_step_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.mul_step_value

/-- info: 'Reversible.doubling_field_mul_count_eq_8_verified' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.doubling_field_mul_count_eq_8_verified

/-! ### ECDLP per-opcode fold closure STEP 4 (Reversible/DoublingAssemblyOps.lean) -/

/-- info: 'Reversible.modAdd_preserves_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modAdd_preserves_block

/-- info: 'Reversible.modSub_preserves_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.modSub_preserves_block

/-- info: 'Reversible.sq_step_assembly_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.sq_step_assembly_correct

/-- info: 'Reversible.sq_step_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.sq_step_value

/-- info: 'Reversible.add_step_assembly_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.add_step_assembly_correct

/-- info: 'Reversible.add_step_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.add_step_value

/-- info: 'Reversible.sub_step_assembly_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.sub_step_assembly_correct

/-- info: 'Reversible.sub_step_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.sub_step_value

/-- info: 'Reversible.all_six_opcodes_through_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.all_six_opcodes_through_fold

/-! ### ECDLP fast Array-based circuit evaluator + bridge (Reversible/Eval.lean) -/

/-- info: 'Reversible.applyGate_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.applyGate_apply

/-- info: 'Reversible.runArr_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.runArr_apply

/-- info: 'Reversible.regValRangeArr_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.regValRangeArr_eq

/-! ### ECDLP controlled addition (Reversible/CtrlAdd.lean, Phase 2 S2) -/

/-- info: 'Reversible.cfullAdder_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cfullAdder_correct

/-- info: 'Reversible.cfullAdder_correct_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cfullAdder_correct_general

/-- info: 'Reversible.cRippleCirc_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cRippleCirc_correct

/-- info: 'Reversible.cRippleCirc_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cRippleCirc_toffoli

/-- info: 'Reversible.cRippleCirc_anc_restored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cRippleCirc_anc_restored

/-- info: 'Reversible.cRippleCirc_ctrl_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cRippleCirc_ctrl_preserved

/-- info: 'Reversible.cRippleCirc_preserves_external' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cRippleCirc_preserves_external

/-! ### ECDLP quantum x quantum multiply (Reversible/CtrlMul.lean, Phase 2 S2.3) -/

/-- info: 'Reversible.cAccStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cAccStep

/-- info: 'Reversible.cMulCircuit_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cMulCircuit_correct

/-- info: 'Reversible.cMulCircuit_eq_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cMulCircuit_eq_mul

/-- info: 'Reversible.ctrlSum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.ctrlSum_eq

/-! ### ECDLP carry-clean (Cuccaro) in-place adder (Reversible/CuccaroAdd.lean, Phase 2 Stage 1) -/

/-- info: 'Reversible.cuccaroAdd_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroAdd_correct

/-- info: 'Reversible.cuccaroAdd_preserves_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroAdd_preserves_B

/-- info: 'Reversible.cuccaroAdd_ancilla_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroAdd_ancilla_clean

/-- info: 'Reversible.cuccaroAdd_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroAdd_toffoli

/-! ### ECDLP carry-clean (Cuccaro) MODULAR adder (Reversible/CuccaroModAdd.lean, Phase 2 Stage 2) -/

/-- info: 'Reversible.cuccaroModAdd_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModAdd_correct

/-- info: 'Reversible.cuccaroModAdd_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModAdd_clean

/-- info: 'Reversible.cuccaroModAdd_preserves_operand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModAdd_preserves_operand

/-- info: 'Reversible.cuccaroModAdd_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModAdd_toffoli

/-! ### ECDLP carry-clean (Cuccaro) MODULAR multiply (Reversible/CuccaroModMul.lean, Phase 2 Stage 2b)

The Θ(n)-reusable-scratch modular multiply `X·Y mod N` and its two clean sub-gadgets
(`cuccaroModDouble` via in-place shift + parity flag-uncompute, `cuccaroCModAdd` via the masked
operand). All foundational-triple-only. -/

/-- info: 'Reversible.cuccaroModDouble_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModDouble_correct

/-- info: 'Reversible.cuccaroModDouble_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModDouble_clean

/-- info: 'Reversible.cuccaroModDouble_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModDouble_toffoli

/-- info: 'Reversible.cuccaroCModAdd_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroCModAdd_correct

/-- info: 'Reversible.cuccaroCModAdd_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroCModAdd_clean

/-- info: 'Reversible.cuccaroCModAdd_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroCModAdd_toffoli

/-- info: 'Reversible.cuccaroModMul_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModMul_correct

/-- info: 'Reversible.cuccaroModMul_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModMul_clean

/-- info: 'Reversible.cuccaroModMul_preserves_XY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModMul_preserves_XY

/-- info: 'Reversible.cuccaroModMul_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModMul_toffoli

/-! ### ECDLP S6.3-36b carry-clean adder-parametric modular multiplier
(Reversible/VerifiedAdderCarryClean.lean)

The carry-clean (`Θ(n)`-qubit) counterpart of the 36a keystone: a restored-clean step interface
(`clean` precondition + restoration postcondition, single reused scratch bank), the parametric
multiplier + cost, and the faithfulness instance recovering `cuccaroModMul`'s `(X·Y) mod N`
correctness and `20·n²+14·n` Toffoli figure by instantiation. All foundational-triple-only. -/

/-- info: 'Reversible.genMulCC_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.genMulCC_correct

/-- info: 'Reversible.genMulCC_toffoli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.genMulCC_toffoli

/-- info: 'Reversible.genMulCC_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.genMulCC_clean

/-- info: 'Reversible.cuccaroModMulStep_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.cuccaroModMulStep_spec

/-- info: 'Reversible.genMulCC_cuccaroAdder_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.genMulCC_cuccaroAdder_eq

/-- info: 'Reversible.genMulCC_cuccaroAdder_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.genMulCC_cuccaroAdder_correct

/-- info: 'Reversible.genMulCC_cuccaroAdder_toffoli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.genMulCC_cuccaroAdder_toffoli

/-! ### AND-based reversible adder with explicit fresh per-carry AND temporaries (Reversible/AndAdd.lean,
Tier-X / L5-c prerequisite). The fresh-AND compute / uncompute attachment point + the full AND-based
ripple adder (separate sum register, fresh carry ancillas, explicit `inverse` uncompute pass).
Foundational-triple-only; the uncompute half (`andAdd_uncompute_toffoli`) is the measurement-route
saving target for L5-d. No amplitude bridge / no measurement (those are #31 / L5-d). -/

/-- info: 'Reversible.andCarry_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.andCarry_correct

/-- info: 'Reversible.andUncompute_restores' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.andUncompute_restores

/-- info: 'Reversible.andCell_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.andCell_correct

/-- info: 'Reversible.andCell_ancilla_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.andCell_ancilla_clean

/-- info: 'Reversible.andCarryCell_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.andCarryCell_correct

/-- info: 'Reversible.andAdd_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.andAdd_correct

/-- info: 'Reversible.andAdd_ancilla_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.andAdd_ancilla_clean

/-- info: 'Reversible.andCell_toffoli' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.andCell_toffoli

/-- info: 'Reversible.andAdd_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.andAdd_toffoli

/-- info: 'Reversible.andAdd_uncompute_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.andAdd_uncompute_toffoli

-- The two reusable circuit-semantics infra lemmas (Mathlib-upstream candidates, cited by #31/L5-d):
-- pin their axiom footprint at the definition site (auditor recommendation).
/-- info: 'Reversible.denote_apply_of_forall_not_mem_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.denote_apply_of_forall_not_mem_target

/-- info: 'Reversible.denote_agree_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.denote_agree_on

/-! ### Gidney 1-Toffoli-per-carry adder (Reversible/GidneyAdder.lean, Build #35) -/

/-- info: 'Reversible.majCell_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.majCell_correct

/-- info: 'Reversible.majCell_toffoli' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.majCell_toffoli

/-- info: 'Reversible.gidneyAdd_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.gidneyAdd_correct

/-- info: 'Reversible.gidneyAdd_ancilla_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.gidneyAdd_ancilla_clean

/-- info: 'Reversible.gidneyAdd_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Reversible.gidneyAdd_toffoli

/-! ### ECDLP elliptic-curve layer (ECDLP/EllipticCurve.lean, Tranche 5) -/

/-- info: 'ECDLP.scalarMul_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.scalarMul_add

/-- info: 'ECDLP.scalarMul_addOrderOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.scalarMul_addOrderOf

/-- info: 'ECDLP.isDLog_add_addOrderOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.isDLog_add_addOrderOf

/-! ### ECDLP double-and-add scalar multiplication (ECDLP/ScalarMul.lean, Tranche 6) -/

/-- info: 'ECDLP.doubleAndAdd_eq_nsmul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.doubleAndAdd_eq_nsmul

/-- info: 'ECDLP.doubleAndAdd_eq_scalarMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.doubleAndAdd_eq_scalarMul

/-- info: 'ECDLP.doubleAndAddCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.doubleAndAddCost_le

/-- info: 'ECDLP.doubleAndAddWeightedCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.doubleAndAddWeightedCost_le

/-! ### ECDLP secp256k1 capstone (Secp256k1.lean + ResourceBounds.lean, Tranche 7) -/

/-- info: 'ECDLP.Secp256k1.p_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.Secp256k1.p_lt_two_pow

/-- info: 'ECDLP.ResourceBounds.scalarMulToffoli_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.scalarMulToffoli_le

/-- info: 'ECDLP.ResourceBounds.secp256k1_scalarMul_toffoli_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1_scalarMul_toffoli_bound

/-- info: 'ECDLP.ResourceBounds.secp256k1ToffoliBound_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1ToffoliBound_eq

/-- info: 'ECDLP.ResourceBounds.secp256k1_scalarMul_toffoli_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1_scalarMul_toffoli_concrete

/-- info: 'ECDLP.ResourceBounds.secp256k1ToffoliRefined_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1ToffoliRefined_eq

/-- info: 'ECDLP.ResourceBounds.secp256k1_scalarMul_toffoli_refined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1_scalarMul_toffoli_refined

/-- info: 'ECDLP.ResourceBounds.secp256k1ToffoliWindowed_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1ToffoliWindowed_eq

/-- info: 'ECDLP.ResourceBounds.secp256k1ToffoliOptimized_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1ToffoliOptimized_eq

/-- info: 'ECDLP.ResourceBounds.secp256k1DepthSequential_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1DepthSequential_eq

/-- info: 'ECDLP.ResourceBounds.secp256k1DepthOptimized_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1DepthOptimized_eq

/-- info: 'ECDLP.ResourceBounds.secp256k1QubitsBaseline_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1QubitsBaseline_eq

/-- info: 'ECDLP.ResourceBounds.modMultToffoli_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.modMultToffoli_eq

/-- info: 'ECDLP.ResourceBounds.secp256k1ToffoliWithReduction_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1ToffoliWithReduction_eq

/-! ### ECDLP H1 secp256k1 figure from the verified modular arithmetic (ResourceBounds.lean) -/

/-- info: 'ECDLP.ResourceBounds.verifiedModMulToffoli_eq_mulLoop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.verifiedModMulToffoli_eq_mulLoop

/-- info: 'ECDLP.ResourceBounds.verifiedModMulToffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.verifiedModMulToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.verifiedDoublingToffoli_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.verifiedDoublingToffoli_eq

/-- info: 'ECDLP.ResourceBounds.verifiedDoublingToffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.verifiedDoublingToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.verifiedAdditionToffoli_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.verifiedAdditionToffoli_eq

/-- info: 'ECDLP.ResourceBounds.verifiedAdditionToffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.verifiedAdditionToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.secp256k1ToffoliVerifiedArith_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1ToffoliVerifiedArith_eq

/-- info: 'ECDLP.ResourceBounds.secp256k1_scalarMul_toffoli_verified_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1_scalarMul_toffoli_verified_arith

/-! ### ECDLP Stage 3 secp256k1 figure from the carry-clean modular arithmetic (ResourceBounds.lean) -/

/-- info: 'ECDLP.ResourceBounds.cleanModMulToffoli_eq_cuccaro' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.cleanModMulToffoli_eq_cuccaro

/-- info: 'ECDLP.ResourceBounds.cleanModMulToffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.cleanModMulToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.secp256k1ToffoliCleanArith_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1ToffoliCleanArith_eq

/-- info: 'ECDLP.ResourceBounds.secp256k1_scalarMul_toffoli_clean_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1_scalarMul_toffoli_clean_arith

/-- info: 'ECDLP.ResourceBounds.cleanModMulQubits_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.cleanModMulQubits_secp256k1

/-- info: 'ECDLP.ResourceBounds.cleanModMulQubits_inhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.cleanModMulQubits_inhabited

/-! ### ECDLP Fermat modular inversion: algebra + cost fold-in (Inversion.lean + ResourceBounds.lean) -/

/-- info: 'ECDLP.fermatInv_eq_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.fermatInv_eq_inv

/-- info: 'ECDLP.fermatInv_eq_modInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.fermatInv_eq_modInv

/-- info: 'ECDLP.modExpFieldMults_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.modExpFieldMults_le

/-- info: 'ECDLP.fermatInvFieldMults_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.fermatInvFieldMults_le

/-- info: 'ECDLP.ResourceBounds.fermatInvToffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.fermatInvToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.secp256k1ToffoliCleanArithWithInversion_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1ToffoliCleanArithWithInversion_eq

/-! ### ECDLP full quantum core (2nd scalar mult + QFT) + affine variant (ResourceBounds.lean) -/

/-- info: 'ECDLP.ResourceBounds.secp256k1EcdlpQftToffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1EcdlpQftToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.secp256k1EcdlpToffoli_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1EcdlpToffoli_eq

/-- info: 'ECDLP.ResourceBounds.affinePointOpToffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.affinePointOpToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.secp256k1ToffoliAffineWithInversion_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1ToffoliAffineWithInversion_eq

/-! ### ECDSA.fail benchmark: one affine point addition (PointAddBenchmark.lean) -/

/-- info: 'ECDLP.ResourceBounds.classicalOffsetCoordToffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.classicalOffsetCoordToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.classicalOffset_coord_lt_one_qq_mult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.classicalOffset_coord_lt_one_qq_mult

/-- info: 'ECDLP.ResourceBounds.onePointAddToffoli_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.onePointAddToffoli_eq

/-- info: 'ECDLP.ResourceBounds.onePointAdd_toffoli_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.onePointAdd_toffoli_le

/-- info: 'ECDLP.ResourceBounds.onePointAddPeakQubits_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.onePointAddPeakQubits_eq

/-- info: 'ECDLP.ResourceBounds.onePointAddScore_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.onePointAddScore_eq

/-! ### ECDLP L6 binary-GCD / Kaliski modular inversion (SafegcdInversion.lean) -/

/-- info: 'ECDLP.binGcdInv_mul_eq_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.binGcdInv_mul_eq_one

/-- info: 'ECDLP.binGcdInv_eq_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.binGcdInv_eq_inv

/-- info: 'ECDLP.binGcdInv_eq_modInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.binGcdInv_eq_modInv

/-- info: 'ECDLP.ResourceBounds.divstepToffoli_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.divstepToffoli_eq

/-- info: 'ECDLP.ResourceBounds.divstepToffoli_eq_gadgets' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.divstepToffoli_eq_gadgets

-- EC-2 (2026-07-09, cost side): the divstep gadget EXHIBITED as one concrete Circuit
-- (modSub ++ cuccaroCModAdd ++ cuccaroModDouble) whose Toffoli cost IS divstepToffoli n. So the cost is
-- the cost of a real in-DSL circuit, not a count over a hypothetical one. HONEST: this is the modular
-- PROXY circuit (denote ≠ integer divstep); the value-faithful divstepGadget (denote = divstep, with
-- garbage bits since divstep is not injective) is the deferred residue.
/-- info: 'ECDLP.ResourceBounds.divstepProxyGadget_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.divstepProxyGadget_toffoli

/-- info: 'ECDLP.ResourceBounds.safegcdInvToffoli_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.safegcdInvToffoli_eq

/-- info: 'ECDLP.ResourceBounds.safegcdInvToffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.safegcdInvToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.affinePointOpToffoli_safegcd_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.affinePointOpToffoli_safegcd_secp256k1

/-- info: 'ECDLP.ResourceBounds.safegcdInvToffoli_lt_fermat_secp256k1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.safegcdInvToffoli_lt_fermat_secp256k1

/-- info: 'ECDLP.ResourceBounds.safegcdInvToffoli_le_fermat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.safegcdInvToffoli_le_fermat

/-- info: 'ECDLP.ResourceBounds.onePointAddToffoli_safegcd_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.onePointAddToffoli_safegcd_eq

/-- info: 'ECDLP.ResourceBounds.onePointAddScore_safegcd_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.onePointAddScore_safegcd_eq

/-- info: 'ECDLP.ResourceBounds.safegcd_score_improvement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.safegcd_score_improvement

/-- info: 'ECDLP.ResourceBounds.fermat_score_gap_vs_leaderboard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.fermat_score_gap_vs_leaderboard

/-- info: 'ECDLP.ResourceBounds.safegcd_score_gap_vs_leaderboard_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.safegcd_score_gap_vs_leaderboard_lower

/-- info: 'ECDLP.ResourceBounds.safegcd_score_gap_vs_leaderboard_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.safegcd_score_gap_vs_leaderboard_upper

/-! ### ECDLP L2 windowed Fermat inversion — DOCUMENTED COMPARISON, off the critical path
(SafegcdInversion.lean). Cost-model only; safegcd wins even against windowed Fermat. -/

/-- info: 'ECDLP.ResourceBounds.windowedFermatInvToffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.windowedFermatInvToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.windowedFermatInvToffoli_lt_fermat_secp256k1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.windowedFermatInvToffoli_lt_fermat_secp256k1

/-- info: 'ECDLP.ResourceBounds.safegcd_beats_windowed_fermat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.safegcd_beats_windowed_fermat

-- ECDLP L8 (2026-07-09): the sub-quadratic (half-GCD) inversion lever, quantified at 256. It BEATS
-- safegcd at 256 iff the recursion is tuned to ≤1 full Karatsuba multiply per level (k=1, ≤8 total);
-- at k≥2 it loses. So a genuine beat CANDIDATE at the ECDLP width — on the knife-edge — the honest
-- "can we beat, not just reproduce" answer. Documented op-count model over the verified Karatsuba mult.
/-- info: 'ECDLP.ResourceBounds.halfGcd_aggressive_beats_safegcd_256' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.halfGcd_aggressive_beats_safegcd_256

/-- info: 'ECDLP.ResourceBounds.halfGcd_beats_iff_k_one_256' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.halfGcd_beats_iff_k_one_256

-- ECDLP L8 faster-M(n) lever (2026-07-10): substitute the verified Toom-3 multiply (Θ(n^1.465)) into the
-- half-GCD model and characterise the beat threshold in the multiply cost. Toom-3 IMPROVES the k=1 margin
-- (12%→~24%) but does NOT flip the threshold at 256 (still beats iff k≤1); flipping to k=2 needs
-- M(256) ≤ 369311, below both Karatsuba (653388) and Toom-3 (596490) — an FFT-class multiply. The
-- knife-edge at the ECDLP width is structural (8 levels vs safegcd's tight ~90n²), not a Karatsuba artefact.
/-- info: 'ECDLP.ResourceBounds.halfGcdInvToffoli_eq_with' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.halfGcdInvToffoli_eq_with

/-- info: 'ECDLP.ResourceBounds.halfGcd_toom3_beats_iff_k_one_256' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.halfGcd_toom3_beats_iff_k_one_256

/-- info: 'ECDLP.ResourceBounds.halfGcd_toom3_improves_margin_256' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.halfGcd_toom3_improves_margin_256

/-- info: 'ECDLP.ResourceBounds.halfGcd_k2_beats_iff_mult_budget_256' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.halfGcd_k2_beats_iff_mult_budget_256

/-- info: 'ECDLP.ResourceBounds.karatsuba_toom3_miss_k2_budget_256' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.karatsuba_toom3_miss_k2_budget_256

/-- info: 'ECDLP.ResourceBounds.windowedFermatInvToffoli_ge_cubic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.windowedFermatInvToffoli_ge_cubic

/-! ### ECDLP L7 Karatsuba sub-quadratic modular multiply cost model (KaratsubaMul.lean) -/

/-- info: 'ECDLP.ResourceBounds.karatsuba_identity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.karatsuba_identity

/-- info: 'ECDLP.ResourceBounds.kCombineToffoli_eq_adders' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.kCombineToffoli_eq_adders

/-- info: 'ECDLP.ResourceBounds.karatsubaToffoli_secp256k1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.karatsubaToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.karatsubaToffoli_lt_schoolbook_secp256k1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.karatsubaToffoli_lt_schoolbook_secp256k1

-- ECDLP L7-t Toom-3 modular multiply (Θ(n^{log₃5})=Θ(n^1.465)), same verified footing as Karatsuba
-- (base = verified schoolbook, combine = verified modular adders). toom3Toffoli 256 = 596490 < 653388.
/-- info: 'ECDLP.ResourceBounds.toom3_coeff_identity' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.toom3_coeff_identity

/-- info: 'ECDLP.ResourceBounds.toom3CombineToffoli_eq_adders' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.toom3CombineToffoli_eq_adders

/-- info: 'ECDLP.ResourceBounds.toom3Toffoli_secp256k1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.toom3Toffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.toom3Toffoli_lt_karatsuba_secp256k1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.toom3Toffoli_lt_karatsuba_secp256k1

/-- info: 'ECDLP.ResourceBounds.onePointAddToffoli_karatsuba_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.onePointAddToffoli_karatsuba_eq

/-- info: 'ECDLP.ResourceBounds.onePointAddScore_karatsuba_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.onePointAddScore_karatsuba_eq

/-- info: 'ECDLP.ResourceBounds.karatsuba_score_improvement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.karatsuba_score_improvement

/-- info: 'ECDLP.ResourceBounds.karatsuba_score_gap_vs_leaderboard_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.karatsuba_score_gap_vs_leaderboard_lower

/-- info: 'ECDLP.ResourceBounds.karatsuba_score_gap_vs_leaderboard_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.karatsuba_score_gap_vs_leaderboard_upper

/-- info: 'ECDLP.ResourceBounds.affinePointOpToffoli_karatsuba_secp256k1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.affinePointOpToffoli_karatsuba_secp256k1

/-- info: 'ECDLP.ResourceBounds.karatsuba_score_improvement_quant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.karatsuba_score_improvement_quant

/-! ### ECDLP L3 dedicated modular squaring cost model + re-cost (KaratsubaMul.lean) -/

/-- info: 'ECDLP.ResourceBounds.karatsubaSquare_identity' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.karatsubaSquare_identity

/-- info: 'ECDLP.ResourceBounds.schoolbookSquareToffoli_two_mul' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.schoolbookSquareToffoli_two_mul

/-- info: 'ECDLP.ResourceBounds.squareToffoli_secp256k1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.squareToffoli_secp256k1

/-- info: 'ECDLP.ResourceBounds.squareToffoli_lt_multiply_secp256k1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.squareToffoli_lt_multiply_secp256k1

/-- info: 'ECDLP.ResourceBounds.affinePointOpToffoli_squaring_secp256k1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.affinePointOpToffoli_squaring_secp256k1

/-- info: 'ECDLP.ResourceBounds.onePointAddToffoli_squaring_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.onePointAddToffoli_squaring_eq

/-- info: 'ECDLP.ResourceBounds.onePointAddScore_squaring_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.onePointAddScore_squaring_eq

/-- info: 'ECDLP.ResourceBounds.squaring_score_improvement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.squaring_score_improvement

/-- info: 'ECDLP.ResourceBounds.squaring_score_gap_vs_leaderboard_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.squaring_score_gap_vs_leaderboard_lower

/-- info: 'ECDLP.ResourceBounds.squaring_score_gap_vs_leaderboard_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.squaring_score_gap_vs_leaderboard_upper

/-! ### ECDLP two-track resource accounting: verified floor / trusted estimate / frontier (TwoTrack.lean) -/

/-- info: 'ECDLP.ResourceBounds.secp256k1Toffoli_verifiedFloor_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1Toffoli_verifiedFloor_eq

/-- info: 'ECDLP.ResourceBounds.secp256k1Toffoli_trustedEstimate_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1Toffoli_trustedEstimate_eq

/-- info: 'ECDLP.ResourceBounds.verifiedFloor_no_trusted_leak' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.verifiedFloor_no_trusted_leak

/-- info: 'ECDLP.ResourceBounds.trustedEstimate_uses_trusted' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.trustedEstimate_uses_trusted

/-- info: 'ECDLP.ResourceBounds.verificationFrontier_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.verificationFrontier_length

/-- info: 'ECDLP.ResourceBounds.two_track_gap_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.two_track_gap_lower

/-- info: 'ECDLP.ResourceBounds.two_track_gap_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.two_track_gap_upper

/-- info: 'ECDLP.ResourceBounds.trustedEstimate_lt_verifiedFloor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.trustedEstimate_lt_verifiedFloor

/-! ### ECDLP THREE-TRACK score ledger: Verified / Trusted / Leaderboard (ThreeTrackScore.lean, 2026-07-17)
The ecdsa.fail SCORE (peak × Toffoli) split three ways. Verified score = verifiedFloor × peak 2822 =
1.91e12; Trusted score = trustedEstimate × peak 2822 = 2.2e10; Leaderboard (competition convention) =
optimised peak 1156 × CALCULATED avg-executed 1,950,403 = 2,254,665,868 ≈ 2.25e9 -- ~1.44× the live best
(leaderboard_calculated_gap: ratio in (1.4,1.5); leaderboard_not_below_best: ABOVE it, NOT a win). The
avg-executed is COMPUTED (SafegcdExecCost.lean: competition's executed-Toffoli rule MEASURED on the
verified n=3 adder = 25% executed/emitted, × emitted worst-case 7,801,612), a grounded MODEL — not the
frontier's number. The exact figure needs the assembled op-stream + eval_circuit (#7). -/

/-- info: 'ECDLP.ResourceBounds.leaderboardConventionScore_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.leaderboardConventionScore_eq

/-- info: 'ECDLP.ResourceBounds.leaderboard_calculated_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.leaderboard_calculated_gap

/-- info: 'ECDLP.ResourceBounds.leaderboard_not_below_best' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.leaderboard_not_below_best

/-- info: 'ECDLP.ResourceBounds.three_tracks_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.three_tracks_ordered

/-! ### ECDLP Stage-1 trusted leaderboard estimate: measurement + windowing + qubit model + score (TrustedEstimate.lean) -/

/-- info: 'ECDLP.ResourceBounds.secp256k1Toffoli_measGidney_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1Toffoli_measGidney_eq

/-- info: 'ECDLP.ResourceBounds.secp256k1Toffoli_trustedEstimate_v2_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1Toffoli_trustedEstimate_v2_eq

/-- info: 'ECDLP.ResourceBounds.trustedEstimate_v2_lt_trustedEstimate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.trustedEstimate_v2_lt_trustedEstimate

/-- info: 'ECDLP.ResourceBounds.secp256k1Qubits_trustedEstimate_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1Qubits_trustedEstimate_eq

/-- info: 'ECDLP.ResourceBounds.qubits_trustedEstimate_lt_anchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.qubits_trustedEstimate_lt_anchor

/-- info: 'ECDLP.ResourceBounds.secp256k1Score_trustedEstimate_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1Score_trustedEstimate_eq

/-- info: 'ECDLP.ResourceBounds.score_trustedEstimate_lt_squaring_score' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.score_trustedEstimate_lt_squaring_score

/-- info: 'ECDLP.ResourceBounds.trustedEstimate_v2_uses_trusted' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.trustedEstimate_v2_uses_trusted

/-- info: 'ECDLP.ResourceBounds.leaderboardScoreExact_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.leaderboardScoreExact_eq

/-- info: 'ECDLP.ResourceBounds.toffoli_v2_reproduces_leaderboard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.toffoli_v2_reproduces_leaderboard

/-- info: 'ECDLP.ResourceBounds.qubits_trustedEstimate_two_leaderboard' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.qubits_trustedEstimate_two_leaderboard

/-- info: 'ECDLP.ResourceBounds.score_trustedEstimate_vs_leaderboard_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.score_trustedEstimate_vs_leaderboard_lower

/-- info: 'ECDLP.ResourceBounds.score_trustedEstimate_vs_leaderboard_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.score_trustedEstimate_vs_leaderboard_upper

/-- info: 'ECDLP.ResourceBounds.score_trustedEstimate_vs_rounded_leaderboard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.score_trustedEstimate_vs_rounded_leaderboard

/-! ### ECDLP Stage-2 aggressive qubit layout: cited 4.5n = 1152, recomposed score, ~1.07x rank (TrustedEstimate.lean) -/

/-- info: 'ECDLP.ResourceBounds.secp256k1Qubits_trustedEstimate_aggressive_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1Qubits_trustedEstimate_aggressive_eq

/-- info: 'ECDLP.ResourceBounds.qubits_aggressive_matches_leaderboard_benchmark' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.qubits_aggressive_matches_leaderboard_benchmark

/-- info: 'ECDLP.ResourceBounds.qubits_aggressive_half_trustedEstimate' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.qubits_aggressive_half_trustedEstimate

/-- info: 'ECDLP.ResourceBounds.secp256k1Score_trustedEstimate_aggressive_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1Score_trustedEstimate_aggressive_eq

/-- info: 'ECDLP.ResourceBounds.score_aggressive_within_leaderboard_benchmark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.score_aggressive_within_leaderboard_benchmark

/-- info: 'ECDLP.ResourceBounds.trustedEstimate_aggressive_uses_trusted' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.trustedEstimate_aggressive_uses_trusted

-- Stage-2b (2026-07-12): the aggressive 4.5n qubit layout given a register-role breakdown grounded in the
-- corpus's verified measurement-ancilla-recycling. secp256k1Qubits_aggressive_breakdown = 2n + 5n/2 = 9n/2
-- = 1152 (2n coords + 2.5n recycled scratch), = leaderboardQubits (aggressive_breakdown_closes_qubit_gap):
-- the 2x qubit gap (2304→1152) closed via the same discipline that halves the AND-adder Toffoli (EC-6/L5-d).
-- Documented layout model (trusted tier), not a verified circuit.
/-- info: 'ECDLP.ResourceBounds.secp256k1Qubits_aggressive_breakdown_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.secp256k1Qubits_aggressive_breakdown_eq

/-- info: 'ECDLP.ResourceBounds.aggressive_breakdown_closes_qubit_gap' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.ResourceBounds.aggressive_breakdown_closes_qubit_gap

/-! ### ECDLP S6.1 concrete EC doubling: derived field-mult count (PointDouble.lean) -/

/-- info: 'ECDLP.doublingProgram_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.doublingProgram_correct

/-- info: 'ECDLP.M_dbl_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.M_dbl_eq

/-- info: 'ECDLP.doubling_toffoli_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.doubling_toffoli_eq

/-- info: 'ECDLP.doubling_toffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.doubling_toffoli_secp256k1

/-! ### ECDLP S6.2 concrete EC mixed addition: derived field-mult count (PointAdd.lean) -/

/-- info: 'ECDLP.additionProgram_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.additionProgram_correct

/-- info: 'ECDLP.additionProgram_correct_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.additionProgram_correct_vector

/-- info: 'ECDLP.M_add_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.M_add_eq

/-- info: 'ECDLP.addition_toffoli_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.addition_toffoli_eq

/-- info: 'ECDLP.addition_toffoli_secp256k1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ECDLP.addition_toffoli_secp256k1

/-! ### L5-a measurement-based AND-uncomputation (Gidney measure-and-correct gadget) -/

/-- info: 'CSD.Empirical.QM.measureUncompute_uncomputes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.measureUncompute_uncomputes

/-- info: 'CSD.Empirical.QM.measureUncompute_basisState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.measureUncompute_basisState

/-- info: 'CSD.Empirical.QM.andInput_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.andInput_nontrivial

/-- info: 'CSD.Empirical.QM.gadgetGateList_zero_toffoli' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.gadgetGateList_zero_toffoli

/-! ### L5-b operator↔list link and cost as an operator property -/

/-- info: 'CSD.Empirical.QM.gadgetGateList_denotes_measureUncompute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.gadgetGateList_denotes_measureUncompute

/-- info: 'CSD.Empirical.QM.measureUncompute_cost' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.measureUncompute_cost

/-- info: 'CSD.Empirical.QM.measureUncompute_toffoli_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.measureUncompute_toffoli_eq_zero

/-! ### #31 localized amplitude lift of the AND-uncompute block (L5-c bridge, cell granularity) -/

/-- info: 'CSD.Empirical.QM.andUncompMat_lifts_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.andUncompMat_lifts_denote

/-- info: 'CSD.Empirical.QM.andUncompMat_uncomputes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.andUncompMat_uncomputes

/-- info: 'CSD.Empirical.QM.andUncompute_measureUncompute_agree_on_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.andUncompute_measureUncompute_agree_on_block

/-- info: 'CSD.Empirical.QM.andUncompute_measureUncompute_same_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.andUncompute_measureUncompute_same_data

/-- info: 'CSD.Empirical.QM.andUncompute_measurement_saving' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.andUncompute_measurement_saving

-- EC-6 / L5-d (2026-07-09): the circuit-level measurement-discipline saving threaded through the whole
-- AND-adder. Each of the n fresh-AND uncomputes is replaced by the proven-equivalent measurement gadget
-- (same data, 0 Toffoli), so the measurement-discipline AND-adder costs 3n — exactly HALF the unitary 6n
-- (andAdd_measurement_halves). The per-cell data-effect equivalence is proved; the full channel-level
-- composition over all cells is the standing residual.
/-- info: 'CSD.Empirical.QM.andAdd_measurement_toffoli' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.andAdd_measurement_toffoli

/-- info: 'CSD.Empirical.QM.andAdd_measurement_halves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.andAdd_measurement_halves

/-! ### L5-d measurement-based AND-adder re-cost (Build #21) -/

/-- info: 'CSD.Empirical.QM.gadgetBlockToffoli_eq_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.gadgetBlockToffoli_eq_zero

/-- info: 'CSD.Empirical.QM.numUncomputeBlocks_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.numUncomputeBlocks_eq

/-- info: 'CSD.Empirical.QM.measUncomputeGadgets_toffoli' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.measUncomputeGadgets_toffoli

/-- info: 'CSD.Empirical.QM.measAddToffoli_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.measAddToffoli_eq

/-- info: 'CSD.Empirical.QM.andAdd_toffoli_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.andAdd_toffoli_eq

/-- info: 'CSD.Empirical.QM.measAdd_toffoli_saving' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.measAdd_toffoli_saving

/-- info: 'CSD.Empirical.QM.measAdd_toffoli_savings_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.measAdd_toffoli_savings_eq

/-- info: 'CSD.Empirical.QM.measAdd_toffoli_256' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.measAdd_toffoli_256

/-- info: 'CSD.Empirical.QM.perBlock_saving' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.perBlock_saving

/-- info: 'CSD.Empirical.QM.measAdd_saving_aggregates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.measAdd_saving_aggregates

/-! ### Gidney adder measurement re-cost (Empirical/QM/MeasurementGidneyAdder.lean, Build #35) -/

/-- info: 'CSD.Empirical.QM.gidneyMeasAddToffoli_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.gidneyMeasAddToffoli_eq

/-- info: 'CSD.Empirical.QM.gidneyMeasAdd_saving_aggregates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.gidneyMeasAdd_saving_aggregates

/-- info: 'CSD.Empirical.QM.gidney_beats_cuccaro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.gidney_beats_cuccaro

/-- info: 'CSD.Empirical.QM.gidney_toffoli_256' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.gidney_toffoli_256

-- EC-3 capstone (2026-07-09): the measurement-discipline ADDER HIERARCHY, unifying EC-3 (Gidney
-- measurement adder, n) and EC-6/L5-d (AND-adder measurement, 3n). Each of the four costs is a proven
-- circuit figure: meas-Gidney n < unitary-Gidney 2n < meas-AND 3n < unitary-AND 6n. The measurement
-- Gidney adder is the cheapest reversible adder in the corpus (gidneyMeas_cheapest). Channel-level
-- composition over all cells is the standing residual shared by EC-3/EC-6.
/-- info: 'CSD.Empirical.QM.measurement_adder_hierarchy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.measurement_adder_hierarchy

/-- info: 'CSD.Empirical.QM.gidneyMeas_cheapest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.gidneyMeas_cheapest

/-- info: 'CSD.Empirical.QM.ccxAtMat_lifts_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.QM.ccxAtMat_lifts_denote

-- Build 15e (ChannelCapacity, 2026-06-30): channel capacities of the de-isolation /
-- dephasing channel Φ_deph = decohereReducedN (15a), on the K1-A von Neumann entropy.
-- CLASSICAL info survives: computational-basis states are FIXED POINTS
-- (dephasing_fixes_basis_state), single-letter Holevo χ of the basis ensemble = log 2
-- (holevo_classical_eq_log_two, S(½I)−½·0−½·0). QUANTUM coherence destroyed: |+⟩⟨+| ↦ ½I
-- (dephasing_plus_eq_half_one), entropy jump 0 → log 2 (dephasing_destroys_coherence).
-- S(½I)=log 2 via the maximally-mixed value vonNeumannEntropy_const_smul_one (charpoly route).
-- Single-shot Holevo / coherent-information, NOT the regularized capacity; entropy concavity
-- (the general χ≥0 bound) gated on the open SSA fork. Ontic Σ-volume capacity D1-gated (LF6).

/-- info: 'QuantumInfo.vonNeumannEntropy_const_smul_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_const_smul_one

/-- info: 'QuantumInfo.vonNeumannEntropy_maximally_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumInfo.vonNeumannEntropy_maximally_mixed

/-- info: 'CSD.Empirical.CSDBridge.ChannelCapacity.dephasing_fixes_basis_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ChannelCapacity.dephasing_fixes_basis_state

/-- info: 'CSD.Empirical.CSDBridge.ChannelCapacity.holevo_classical_eq_log_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ChannelCapacity.holevo_classical_eq_log_two

/-- info: 'CSD.Empirical.CSDBridge.ChannelCapacity.dephasing_plus_eq_half_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ChannelCapacity.dephasing_plus_eq_half_one

/-- info: 'CSD.Empirical.CSDBridge.ChannelCapacity.dephasing_destroys_coherence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ChannelCapacity.dephasing_destroys_coherence

/-- info: 'CSD.Empirical.CSDBridge.ChannelCapacity.dephasing_classical_vs_quantum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CSD.Empirical.CSDBridge.ChannelCapacity.dephasing_classical_vs_quantum

-- CGLMP qudit Bell inequality (Cat-1, Mathlib/Probability/CGLMP.lean): the
-- general-d deterministic reduction (LHV = mixture of product strategies) + the
-- LHV-to-finite-optimisation bound, and the numeric CGLMP LHV bound I_d <= 2 for
-- d = 2, 3, 4 (finite check via decide on the division-cleared integer functional).
-- All foundational-triple-only. The general-d numeric bound is the named residual.

/-- info: 'ProbabilityTheory.CGLMP.cglmpLHV_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.CGLMP.cglmpLHV_eq_integral

/-- info: 'ProbabilityTheory.CGLMP.cglmpLHV_le_of_det_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.CGLMP.cglmpLHV_le_of_det_le

/-- info: 'ProbabilityTheory.CGLMP.cglmp_lhv_bound_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.CGLMP.cglmp_lhv_bound_three

/-- info: 'ProbabilityTheory.CGLMP.cglmp_lhv_bound_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.CGLMP.cglmp_lhv_bound_four

-- Tightness: the LHV bound is EXACTLY 2 (achieved), not loose -- guards the
-- bound-is-tight claim against future decide / ZMod churn.
/-- info: 'ProbabilityTheory.CGLMP.scaledDetZ_three_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.CGLMP.scaledDetZ_three_tight

/-- info: 'ProbabilityTheory.CGLMP.scaledDetZ_four_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.CGLMP.scaledDetZ_four_tight

-- The GENERAL-d CGLMP classical bound (the sawtooth counting argument, all d >= 2,
-- no decide) -- closes the general-d LHV-bound residual. scaledDetZ_eq_sawtooth is
-- the genuine equality reduction; scaledDetZ_le_general the general-d numeric bound
-- (val-wraparound handled via mod-d divisibility, auditor-verified tight + matching
-- the d=2,3,4 decide anchors); cglmp_lhv_bound the general-d LHV bound.
/-- info: 'ProbabilityTheory.CGLMP.scaledDetZ_eq_sawtooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.CGLMP.scaledDetZ_eq_sawtooth

/-- info: 'ProbabilityTheory.CGLMP.scaledDetZ_le_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.CGLMP.scaledDetZ_le_general

/-- info: 'ProbabilityTheory.CGLMP.cglmp_lhv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.CGLMP.cglmp_lhv_bound

-- LF6-5 tightness (2026-07-11): the general-d bound I_d ≤ 2 is TIGHT for all d. The all-zero local
-- strategy attains scaledDetZ = 2(d-1) (scaledDetZ_tight_general) hence cglmp = I_d = 2
-- (cglmp_detTable_tight_general), so 2 is the EXACT LHV optimum in every dimension (generalising the
-- decide anchors scaledDetZ_three_tight/_four_tight). No decide; sawtooth reduction only.
/-- info: 'ProbabilityTheory.CGLMP.scaledDetZ_tight_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.CGLMP.scaledDetZ_tight_general

/-- info: 'ProbabilityTheory.CGLMP.cglmp_detTable_tight_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProbabilityTheory.CGLMP.cglmp_detTable_tight_general

-- W4 (CV/ApproxCCR): the finite-dimensional obstruction to exact canonical
-- commutation. trace(QP - PQ) = 0 but trace(c•1) = c*card, so no finite matrices
-- satisfy [Q,P] = c•1 when c*card ≠ 0. The physics corollary is c = iℏ.
-- Foundational triple; CSD-free general matrix facts (the CSD reading is docstring
-- only). Motivates the finite-sector reading of position/momentum; does NOT derive CV-QM.
/-- info: 'CSD.CV.trace_commutator_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.trace_commutator_eq_zero

/-- info: 'CSD.CV.trace_scalar_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.trace_scalar_identity

/-- info: 'CSD.CV.no_exact_finite_ccr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.no_exact_finite_ccr

/-- info: 'CSD.CV.no_exact_finite_ccr_ihbar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.no_exact_finite_ccr_ihbar

-- CV-1 (CV/Position): the positive counterpart to W4 — a genuine finite position observable
-- Q_N = diag(x_j) on an N-point symmetric lattice. Hermitian, eigenvalues = the lattice points
-- (standard basis is the position eigenbasis), distinct for a≠0, bounded spectrum, centered (trace 0).
-- Foundational triple; Cat-1 general matrix facts (CSD reading is docstring only).
/-- info: 'CSD.CV.positionOp_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.positionOp_isHermitian

/-- info: 'CSD.CV.positionOp_mulVec_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.positionOp_mulVec_single

/-- info: 'CSD.CV.latticePoint_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.latticePoint_injective

/-- info: 'CSD.CV.abs_latticePoint_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.abs_latticePoint_le

/-- info: 'CSD.CV.positionOp_trace_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.positionOp_trace_eq_zero

-- CV-2/CV-3 (CV/Oscillator): the conjugate (Q,P) pair and the sharp approximate CCR. The N-level
-- truncated oscillator gives a†a = diag(n), aa† = diag(1..N-1,0), hence the truncated CCR
-- [a,a†] = 1 - N·|N-1⟩⟨N-1| (both sides trace 0, per W4). Q=(a+a†)/√2, P=(a-a†)/(i√2) are Hermitian,
-- [Q,P] = i·[a,a†], and [Q,P]·eₙ = i·eₙ exactly for every n ≠ N-1 (exact CCR on the low-energy
-- sector; the W4-forced defect is confined to the top level). Foundational triple; Cat-1.
/-- info: 'CSD.CV.truncated_ccr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.truncated_ccr

/-- info: 'CSD.CV.Q_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.Q_isHermitian

/-- info: 'CSD.CV.P_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.P_isHermitian

/-- info: 'CSD.CV.QP_commutator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.QP_commutator

/-- info: 'CSD.CV.ccr_exact_on_bulk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.ccr_exact_on_bulk

-- CV-4 (CV/OscillatorSpectrum): the energy spectrum. H = a†a + ½ = diag(n+½), Hermitian, with the
-- Fock states as energy eigenstates (H·eₙ = (n+½)·eₙ). The energy Eₙ = n+½ is CUTOFF-INDEPENDENT
-- (oscEnergy has no N), so every finite-energy prediction below the ceiling — zero-point ½, uniform
-- gap 1, each level — is recovered exactly by the truncation. Foundational triple; Cat-1.
/-- info: 'CSD.CV.hamiltonian_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.hamiltonian_isHermitian

/-- info: 'CSD.CV.hamiltonian_mulVec_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.hamiltonian_mulVec_single

/-- info: 'CSD.CV.oscEnergy_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.oscEnergy_gap

/-- info: 'CSD.CV.hamiltonian_groundEnergy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.CV.hamiltonian_groundEnergy

-- Safegcd (Bernstein-Yang) divstep: the GCD invariant as a GENUINE theorem
-- (divstep_gcd, not a ZMod.inv unfolding; Odd f load-bearing), the divstep
-- function, correctness-modulo-termination, and Bezout-up-to-2^k. Termination +
-- the reversible circuit + the 2^{-k} correction are named residuals (still
-- trusted). All foundational-triple.
/-- info: 'ECDLP.Safegcd.divstep_fst_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.divstep_fst_odd

/-- info: 'ECDLP.Safegcd.gcd_two_mul_right_of_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.gcd_two_mul_right_of_odd

/-- info: 'ECDLP.Safegcd.divstep_gcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.divstep_gcd

/-- info: 'ECDLP.Safegcd.divstepIter_gcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.divstepIter_gcd

/-- info: 'ECDLP.Safegcd.divstepIter_natAbs_of_g_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.divstepIter_natAbs_of_g_zero

/-- info: 'ECDLP.Safegcd.divstepIter_natAbs_one_of_coprime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.divstepIter_natAbs_one_of_coprime

-- EC-1 (2026-07-09): termination STABILITY (the fixed-count-loop half). g=0 is absorbing
-- (divstep_snd_snd_zero); once g hits 0 the surviving |f| = gcd(f₀,g₀) and STAYS so for every further
-- step (divstepIter_natAbs_of_g_zero_stable) — so a fixed 3n-step loop reads the right answer on any
-- input that terminates within it. The termination-COUNT bound itself (g reaches 0 within ~2.88·bits,
-- Bernstein-Yang's computer-assisted argument) stays the external residual.
/-- info: 'ECDLP.Safegcd.divstep_snd_snd_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.divstep_snd_snd_zero

/-- info: 'ECDLP.Safegcd.divstepIter_zero_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.divstepIter_zero_stable

/-- info: 'ECDLP.Safegcd.divstepIter_natAbs_of_g_zero_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.divstepIter_natAbs_of_g_zero_stable

-- EC-2 value side (2026-07-09): the divstep is REVERSIBLE on the odd-f domain. Raw divstep is NOT
-- injective (divstep_not_injective: divstep 0 1 2 = divstep 0 1 1), so garbage is genuinely needed;
-- divstepRev keeps the minimal 2-bit branch selector (input sign-δ, parity-g), and divstepRev_injective
-- proves the extended transition injective for f odd — the mathematical basis for a denote=divstep
-- reversible circuit (2 garbage bits/step). The bit-level circuit itself is the deferred build.
/-- info: 'ECDLP.Safegcd.divstep_not_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.divstep_not_injective

/-- info: 'ECDLP.Safegcd.divstepRev_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.divstepRev_injective

/-- info: 'ECDLP.Safegcd.divstepIter_bezout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.divstepIter_bezout

-- ECDLP L6 safegcd divstep CIRCUIT, TRANCHE 1 (2026-07-16, SafegcdDivstepCircuit.lean, #36c-2):
-- the value-faithful divstep bit-circuit (denote = divstep) opened at its exact-halving primitive.
-- shiftDown is a concrete `n`-swap Circuit; halve_correct proves it computes `÷2` on an EVEN register
-- at the `denote`/regValRange level (general n) -- the divstep's third register update, value-faithful
-- (the divstepProxyGadget above is only a modular COST proxy). shiftDown_toffoli: the halving is
-- Toffoli-FREE (pure wire permutation), refining divstepToffoli's `cuccaroModDouble` 6n+4 overcount.
-- Remaining tranches: signed subtraction (2), conditional swap + branch routing (3), assembly = divstepRev (4).
/-- info: 'ECDLP.Safegcd.Circuit.halve_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.halve_correct

/-- info: 'ECDLP.Safegcd.Circuit.shiftDown_apply_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.shiftDown_apply_lt

/-- info: 'ECDLP.Safegcd.Circuit.shiftDown_toffoli' depends on axioms: [propext] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.shiftDown_toffoli

-- ECDLP L6 safegcd divstep CIRCUIT, TRANCHE 2 (2026-07-16, SafegcdDivstepCircuit.lean, #36c-2):
-- the signed integer arithmetic for the divstep numerators g+f / g-f. signedRep is the two's-complement
-- balanced representative (signedRep_of_mem: fixes in-range values); regValZ the signed register value.
-- signedAdd_correct / signedSub_correct: under a no-overflow bound, the VERIFIED mod-2^n gadgets
-- (cuccaroAdd / rippleSub) realise signed ℤ addition / subtraction at the regValZ level -- the branch-B
-- `g+f` and branch-A `g-f` numerators on a value-faithful circuit (two's-complement +/- IS mod-2^n
-- arithmetic, exact whenever the true result fits the signed range).
/-- info: 'ECDLP.Safegcd.Circuit.signedAdd_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.signedAdd_correct

/-- info: 'ECDLP.Safegcd.Circuit.signedSub_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.signedSub_correct

/-- info: 'ECDLP.Safegcd.Circuit.signedRep_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.signedRep_of_mem

-- ECDLP L6 safegcd divstep CIRCUIT, TRANCHE 3 (2026-07-16, SafegcdDivstepCircuit.lean, #36c-2):
-- the branch control. cswap (Fredkin) + condSwapReg: the value-faithful controlled register swap --
-- condSwapReg_swaps proves F,G exchange bitwise exactly when the control is set (divstep branch-A
-- `f ↔ g`), one Toffoli/bit (condSwapReg_toffoli). regValRange_odd_iff / regValZ_odd_iff: the `Odd g`
-- branch test IS a read of wire 0 (parity = low bit, interpretation-independent). Remaining: the `0<δ`
-- sign read + branch-bit ancilla synthesis + assembly = divstepRev (tranche 4).
/-- info: 'ECDLP.Safegcd.Circuit.cswap_correct_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.cswap_correct_general

/-- info: 'ECDLP.Safegcd.Circuit.condSwapReg_swaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.condSwapReg_swaps

/-- info: 'ECDLP.Safegcd.Circuit.regValZ_odd_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.regValZ_odd_iff

/-- info: 'ECDLP.Safegcd.Circuit.condSwapReg_toffoli' depends on axioms: [propext] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.condSwapReg_toffoli

-- ECDLP L6 safegcd divstep CIRCUIT, TRANCHE 4a (2026-07-16, SafegcdDivstepCircuit.lean, #36c-2):
-- the SIGNED halving. Building the assembly exposed that tranche 1's shiftDown halves the UNSIGNED
-- magnitude (fills the vacated top with 0), but the divstep halves SIGNED numerators (g±f)/2 (g,f go
-- negative) -> needs a sign-EXTENDING right shift. signedHalve = shiftDown + one sign-copy CNOT;
-- signedHalve_correct: regValZ ÷2 for an even register (still Toffoli-free). Supporting two's-complement
-- lemmas: signedRep_high (high-half value = v - 2^W), regValZ_signBit (signed = lowbits - sign·2^n).
-- Remaining tranche-4 residual: g-update composition (signedSub;signedHalve), the δ-counter arithmetic
-- layer + `0<δ` read, branch-bit synthesis + conditional selection, then denote = divstepRev.
/-- info: 'ECDLP.Safegcd.Circuit.signedHalve_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.signedHalve_correct

/-- info: 'ECDLP.Safegcd.Circuit.regValZ_signBit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.regValZ_signBit

/-- info: 'ECDLP.Safegcd.Circuit.signedRep_high' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.signedRep_high

-- ECDLP L6 safegcd divstep CIRCUIT, TRANCHE 4b (2026-07-16, SafegcdDivstepCircuit.lean, #36c-2):
-- the g-register update, COMPOSING the tranches. gUpdateSub_correct: the composite rippleSub;signedHalve
-- computes g ↦ (g-f)/2 (branch-A numerator) at the signed regValZ level; gUpdateAdd_correct: cuccaroAdd;
-- signedHalve computes g ↦ (g+f)/2 (branch-B). Composes T2 (signed ±) with T4a (signed halve); f,g odd
-- makes the numerator even (Odd.sub_odd/add_odd), discharging the halving's bottom-bit hypothesis. So the
-- divstep g-update is now a single value-faithful circuit. Remaining: δ-counter arithmetic + branch
-- synthesis + conditional selection, then denote = divstepRev.
/-- info: 'ECDLP.Safegcd.Circuit.gUpdateSub_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.gUpdateSub_correct

/-- info: 'ECDLP.Safegcd.Circuit.gUpdateAdd_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.gUpdateAdd_correct

-- ECDLP L6 safegcd divstep CIRCUIT, TRANCHE 4c (2026-07-16, SafegcdDivstepCircuit.lean, #36c-2):
-- the `0 < δ` control read (the branch discriminant). regValZ_nonneg_iff: 0 ≤ δ iff the sign bit (wire n)
-- is clear; regValZ_pos_iff: 0 < δ iff sign bit clear AND low bits nonzero -- the divstep branch-A test
-- `0<δ` as a bit read, via regValZ_signBit. (The `Odd g` half is regValZ_odd_iff, T3.) Remaining: the
-- δ-counter arithmetic δ ↦ 1±δ, branch-bit synthesis + conditional selection, then denote = divstepRev.
/-- info: 'ECDLP.Safegcd.Circuit.regValZ_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.regValZ_pos_iff

/-- info: 'ECDLP.Safegcd.Circuit.regValZ_nonneg_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.regValZ_nonneg_iff

-- ECDLP L6 safegcd divstep CIRCUIT, TRANCHE 4d (2026-07-16, SafegcdDivstepCircuit.lean, #36c-2):
-- the δ-counter update δ ↦ 1±δ, a tranche-2 corollary (signed ± against constant 1, no new circuit).
-- deltaInc_correct: cuccaroAdd gives δ↦1+δ (branches B,C); deltaDec_correct: rippleSub gives δ↦1-δ
-- (branch A), each with a register holding the value 1. So every divstep sub-operation (swap, signed ±,
-- signed halve, g-update, δ-update, the 0<δ / Odd g reads) is now circuit-backed. Remaining: branch-bit
-- synthesis (needs a reversible nonzero/OR gadget) + conditional selection, then denote = divstepRev.
/-- info: 'ECDLP.Safegcd.Circuit.deltaInc_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.deltaInc_correct

/-- info: 'ECDLP.Safegcd.Circuit.deltaDec_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.deltaDec_correct

-- ECDLP L6 safegcd divstep CIRCUIT, TRANCHE 4e (2026-07-16, SafegcdDivstepCircuit.lean, #36c-2):
-- the reversible nonzero/OR gadget (branch-synthesis prerequisite). orBlock: De Morgan `a ← c ∨ w` into
-- a fresh ancilla (1 Toffoli), c/w restored; orAccum: the ancilla-ladder fold, orAccum_correct proves the
-- top ancilla is `true` iff some low input wire is set -- a reversible nonzero test (the "low bits ≠ 0"
-- half of the 0<δ read, T4c). Preserves the input wires.
/-- info: 'ECDLP.Safegcd.Circuit.orBlock_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.orBlock_correct

/-- info: 'ECDLP.Safegcd.Circuit.orAccum_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.orAccum_correct

-- ECDLP L6 safegcd divstep CIRCUIT, TRANCHE 4f (2026-07-16, SafegcdDivstepCircuit.lean, #36c-2):
-- the branch-A f-recovery. addTwice_correct: two cuccaroAdds give f ← f + 2·g at the signed regValZ level
-- (the in-place resolution of f'=g: run the g-update first, then f_old + 2·(g-f)/2 = g_old recovers f'=g
-- with no swap, no value destroyed). branchA_recovers: the ℤ identity f + 2·((g-f)/2) = g (f,g odd)
-- confirming gUpdateSub (g-update, T4b) + addTwice compose to divstep branch A (f,g) ↦ (g,(g-f)/2).
/-- info: 'ECDLP.Safegcd.Circuit.addTwice_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.addTwice_correct

/-- info: 'ECDLP.Safegcd.Circuit.branchA_recovers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.branchA_recovers

-- ECDLP L6 safegcd divstep CIRCUIT, TRANCHE 4g (2026-07-17, SafegcdDivstepCircuit.lean, #36c-2/#3):
-- lane-0 cswap elision (a real frontier Toffoli lever). cswap_noop_of_eq: a controlled swap of two wires
-- holding EQUAL values is the identity. cswap_lane0_noop: when the branch-A f↔g swap fires, f,g are both
-- odd so wire 0 is true for both -- the lane-0 swap is a no-op, eliminable (the field's `divstep 0..n →
-- 1..n`), here a proved value-exact identity.
/-- info: 'ECDLP.Safegcd.Circuit.cswap_noop_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.cswap_noop_of_eq

/-- info: 'ECDLP.Safegcd.Circuit.cswap_lane0_noop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.cswap_lane0_noop

-- ECDLP L6 safegcd divstep CIRCUIT, TRANCHE 4h (2026-07-17, SafegcdDivstepCircuit.lean, #36c-2/#1):
-- the branch-control-bit synthesis. and3_correct: [CCX a b u, CCX u c t, CCX a b u] sets t = a∧b∧c and
-- restores scratch u (compute-copy-uncompute, 2 Toffoli) -- synthesises the branch-A control
-- bA = sign_clear ∧ nonzero_δ ∧ odd_g into a clean ancilla, the input the conditional gadgets consume.
/-- info: 'ECDLP.Safegcd.Circuit.and3_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ECDLP.Safegcd.Circuit.and3_correct

-- TH1 (thermodynamics track): canonical typicality -- thermal equilibrium from
-- Fubini-Study volume. The FS first moment E[|psi><psi|] = (1/N) I (a genuine
-- twirl/Schur integral via FS U(N)-invariance, sign-flip + permutation
-- unitaries), and the average reduced state E[Tr_E |psi><psi|] = (1/d_S) I_S
-- (canonical typicality IN EXPECTATION, generalising maxEntangled_marginal_uniform).
-- Concentration/Levy (the typical-state upgrade) is the NAMED residual, not
-- proved. Foundational-triple; Gleason-free.
/-- info: 'CSD.Thermo.fs_first_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.fs_first_moment

/-- info: 'CSD.Thermo.canonical_typicality_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.canonical_typicality_expectation

-- TH2: the second law as coarse-grained entropy monotonicity. Pinching
-- (dephasing to the pointer-basis diagonal) never decreases the von Neumann
-- entropy -- S(rho) <= S(pinch rho) -- via Klein's inequality against the
-- diagonal and the cross-term identity Tr(rho log(pinch rho)) = -S(pinch rho).
-- The fine-grained unitary step conserves entropy (vonNeumannEntropy_conj_unitary);
-- the coarse-graining step produces it: the H-theorem form of the second law.
-- Honest scope: strict-positivity (Klein support) hypothesis; a specific
-- coarse-graining, not a universal second law; the pure-state instance is
-- LF6-B.3. Foundational-triple.
/-- info: 'CSD.Thermo.vonNeumannEntropy_le_pinching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.vonNeumannEntropy_le_pinching

/-- info: 'CSD.Thermo.entropy_reversible_then_coarsegrain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.entropy_reversible_then_coarsegrain

/-- info: 'CSD.Thermo.entropy_production_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.entropy_production_nonneg

-- TH3: temperature, free energy, and the Gibbs variational principle. The Gibbs
-- state ρ_β = exp(-βH)/Z (built via the Hermitian functional calculus) minimises
-- the free energy F(ρ) = Re Tr(ρH) - T·S(ρ) among all density operators, with
-- minimum F(ρ_β) = -T log Z. Proof: β(F(ρ) - F(ρ_β)) = D(ρ ‖ ρ_β) ≥ 0 by Klein,
-- using the crux log(ρ_β) = -βH - (log Z)·1 (cfc_eq_conj_diagonal on the
-- H-eigenbasis). Foundational-triple; the variational characterisation of
-- thermal equilibrium. Requires [Nonempty n].
/-- info: 'CSD.Thermo.cfc_log_gibbsState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.cfc_log_gibbsState

/-- info: 'CSD.Thermo.gibbsState_posDef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.gibbsState_posDef

/-- info: 'CSD.Thermo.gibbsState_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.gibbsState_trace

/-- info: 'CSD.Thermo.gibbs_free_energy_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.gibbs_free_energy_eq

/-- info: 'CSD.Thermo.gibbs_free_energy_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.gibbs_free_energy_min

-- TH4: Landauer's principle (Reeb-Wolf bound). A system coupled by a global
-- unitary to a bath in the Gibbs state obeys β·ΔQ ≥ S(ρ_S) − S(ρ_S') -- the
-- entropy removed from the system is at most β times the heat dumped into the
-- bath. Chain: entropy conservation (conj_unitary + kronecker) + subadditivity
-- ⇒ S(ρ_S)−S(ρ_S') ≤ S(ρ_B')−S(τ_B); the bath Clausius inequality
-- (relEntropy_nonneg + the TH3 Gibbs log identity) bounds that by β·ΔQ. One-bit
-- corollary: erasing a maximally-mixed bit to a definite state costs
-- ΔQ ≥ T log 2 = kT ln 2. Foundational-triple.
/-- info: 'CSD.Thermo.bath_clausius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.bath_clausius

/-- info: 'CSD.Thermo.landauer_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.landauer_bound

/-- info: 'CSD.Thermo.landauer_one_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CSD.Thermo.landauer_one_bit

-- FND Tranche 1 (2026-07-12): the Choice A ontology foundation. ConstraintDynamics (deterministic
-- measure-preserving one-parameter-group ontic flow), RecordedFact/RecordSemantics/compatibleSet
-- (records as measurable contextual events; isolation = conditioning muL on the record history),
-- IsolationPreparation (LF1 adapter reusing prepMeasure), ChoiceASector (measurable pi to CP^{N-1}, not
-- injective), and the Kähler adapters. No Born/unitarity/Fubini-Study as fields; those are uninhabited
-- theorem-target predicates (TheoremTargets). Foundational triple only.
/-- info: 'CSD.FND.ConstraintDynamics.flow_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.ConstraintDynamics.flow_bijective

/-- info: 'CSD.FND.compatibleSet_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.compatibleSet_measurable

/-- info: 'CSD.FND.compatibleSet_append_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.compatibleSet_append_singleton

/-- info: 'CSD.FND.Preparation.conditionalMeasure_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.Preparation.conditionalMeasure_apply

/-- info: 'CSD.FND.HistoryPreparation.conditionalMeasure_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.HistoryPreparation.conditionalMeasure_apply

/-- info: 'CSD.FND.ChoiceASector.projectiveLaw_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.ChoiceASector.projectiveLaw_apply

/-- info: 'CSD.FND.kahlerChoiceASector_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.kahlerChoiceASector_pi

-- FND Tranche 2 (2026-07-13): the de-isolation measurement layer + the concrete product forward
-- capstone. productSector_hasFubiniStudyPushforward proves bridge B1 (pi_*(muFS ⊗ vol) = muFS) for the
-- CP^{N-1}×T² product model; productProjectedFlow_hasHamiltonianRealisation inhabits target T5
-- (exp(-itH) realisation); product_choiceA_forward_capstone bundles measure preservation + projectability
-- + T5 + B1, no open hypotheses. DeisolationModel + establishedFact are the measurement/record interface.
/-- info: 'CSD.FND.productSector_hasFubiniStudyPushforward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.productSector_hasFubiniStudyPushforward

/-- info: 'CSD.FND.productProjectedFlow_hasHamiltonianRealisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.productProjectedFlow_hasHamiltonianRealisation

/-- info: 'CSD.FND.product_choiceA_forward_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.product_choiceA_forward_capstone

/-- info: 'CSD.FND.compatibleSet_appendEstablishedFact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.compatibleSet_appendEstablishedFact

-- FND Tranche 2b (2026-07-13): the concrete de-isolation model from the LF5 pointer machinery.
-- vnDeisolationModel is a fully theorem-backed DeisolationModel on CP^{M} (M+1 = N*N): interaction =
-- measurementFlow (measure-preserving unitary), readout = vnPointerOutcome, outcome regions = pointer
-- fibres. vnDeisolationModel_records proves the readout records the established outcome (B5);
-- vnDeisolationModel_ae_total proves the outcome is established for a.e. initial ontic state (target T6),
-- by transferring bornOutcome_ae_isSome through the measure-preserving interaction.
/-- info: 'CSD.FND.vnDeisolationModel_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.vnDeisolationModel_records

/-- info: 'CSD.FND.vnDeisolationModel_ae_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.vnDeisolationModel_ae_total

/-- info: 'CSD.FND.lifted_choiceA_measurement_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.lifted_choiceA_measurement_capstone

-- FND Tranche 2b Born statistics (2026-07-13): the concrete de-isolation model reproduces the Born
-- FREQUENCIES, not merely a defined outcome. vnDeisolationModel_born_frequency transfers the LF5
-- outcome-frequency capstone measurement_flow_outcome_frequency through the measure-preserving
-- interaction (composed trial process measurementFlow ∘ fsTrial), so the pointer-i readout frequency
-- converges a.s. to ‖⟨eᵢ,ψ⟩‖². lifted_choiceA_measurement_born_capstone bundles the full measurement:
-- measure preservation + unique outcome a.e. + record establishment + a.e. total + Born frequencies.
/-- info: 'CSD.FND.vnDeisolationModel_born_frequency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.vnDeisolationModel_born_frequency

/-- info: 'CSD.FND.lifted_choiceA_measurement_born_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.lifted_choiceA_measurement_born_capstone

-- FND Tranche 3 (2026-07-13): the composition/measurement targets (ledger T9-T15) as bridge interfaces
-- and uninhabited predicates (FND/CompositeInterface.lean), inhabited by adapters wiring the existing
-- LF6/Empirical capstones (FND/CompositeAdapters.lean). T15 no-signalling from the singlet marginals;
-- T14 Bell from the d-intrinsic CGLMP no-LHV force and the CHSH Tsirelson saturation; T13 contextuality
-- from Kochen-Specker (Cabello-18), Mermin-Peres and GHZ; T10 POVM normalisation. T9 (mixed states) left
-- out honestly: the ensemble/mixed-Born content is the reported Mathlib density-matrix gap.
/-- info: 'CSD.FND.singlet_hasNoSignalling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.singlet_hasNoSignalling

/-- info: 'CSD.FND.maxEntangled_noLocalHiddenVariable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.maxEntangled_noLocalHiddenVariable

/-- info: 'CSD.FND.singlet_hasTsirelsonSeparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.singlet_hasTsirelsonSeparation

/-- info: 'CSD.FND.cabello18_noNonContextualValuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.cabello18_noNonContextualValuation

/-- info: 'CSD.FND.merminPeres_noNonContextualValuation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.merminPeres_noNonContextualValuation

/-- info: 'CSD.FND.ghz_noNonContextualValuation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.ghz_noNonContextualValuation

/-- info: 'CSD.FND.povm_weightsProbability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.povm_weightsProbability

-- FND interference (T16) + tensor weave (2026-07-14). hadamardTest_hasBornInterference inhabits the
-- two-path Born-interference target from the Hadamard test ((1 + Re⟨ψ,Uψ⟩)/2); interference is a
-- consequence of the complex sector (P7) + Born rule (T1/T2), not a postulate. The tensor weave shows
-- the finite tensor product ℂ^{NA} ⊗ ℂ^{NB} = ℂ^{NA·NB} is DERIVED (tensorIndexEquiv on Fin NA × Fin NB,
-- the local algebra aliceOp_bobOp_commute, operator no-signalling tensorSector_no_signalling); only the
-- composite-is-tensor bridge (CompositeSector.tensor_dimension, B6) is posited (P3 parked).
/-- info: 'CSD.FND.hadamardTest_hasBornInterference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.hadamardTest_hasBornInterference

/-- info: 'CSD.FND.aliceOp_bobOp_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.aliceOp_bobOp_commute

/-- info: 'CSD.FND.tensorSector_no_signalling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.tensorSector_no_signalling

-- FND time-indexed records + persistence (2026-07-15, FND-T5 final follow-on): makes records physical.
-- flowedSemantics event ⟨c,i,t⟩ = Φ_t⁻¹'(region c i) genuinely uses the recorded time (the pointer
-- semantics ignored it). flowedSemantics_event_measure: μL(event ⟨c,i,t⟩) = μL(region c i) -- record
-- probability conserved under isolated evolution. flowedSemantics_event_flow: event ⟨c,i,t+s⟩ =
-- Φ_s⁻¹'(event ⟨c,i,t⟩) -- record covariant with the flow. flowedSemantics_persistence bundles both.
/-- info: 'CSD.FND.flowedSemantics_event_measure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.flowedSemantics_event_measure

/-- info: 'CSD.FND.flowedSemantics_event_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.flowedSemantics_event_flow

/-- info: 'CSD.FND.flowedSemantics_persistence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.flowedSemantics_persistence

-- FND post-outcome preparation (2026-07-15, FND-T5 follow-on): closes the measurement/record loop.
-- HistoryPreparation.appendFact constructs the post-measurement preparation on the extended history
-- (history ++ [r]); its compatible region compatibleSet ∩ event r has PROVEN nonzero measure when the
-- outcome is possible. appendFactOfPos builds it from positive conditional probability
-- (conditionalMeasure(event r) ≠ 0). appendFact_conditionalMeasure_apply: the post-measurement law is
-- the Bayesian update μL(A ∩ (compatible ∩ event))/μL(compatible ∩ event).
/-- info: 'CSD.FND.HistoryPreparation.appendFact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.HistoryPreparation.appendFact

/-- info: 'CSD.FND.HistoryPreparation.appendFact_conditionalMeasure_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.HistoryPreparation.appendFact_conditionalMeasure_apply

/-- info: 'CSD.FND.HistoryPreparation.appendFactOfPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.HistoryPreparation.appendFactOfPos

-- FND conditional->Luders correspondence (2026-07-15, FND-T5 follow-on): connects the two conditioning
-- rules the review flagged as unlinked. bayesianConditional w = w(fine)/w(coarse); BOTH the projective
-- Luders update (ludersUpdate_isBayesianConditional, over the Born weight) and the ontic record-history
-- conditioning (historyConditioning_isBayesianConditional, over the Liouville measure) are instances.
-- luders_record_conditioning_correspondence bundles both -- one conditioning rule, two weights that
-- agree on the sector via Born-from-volume (π_*μL = μFS, B1).
/-- info: 'CSD.FND.luders_record_conditioning_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.luders_record_conditioning_correspondence

/-- info: 'CSD.FND.ludersUpdate_isBayesianConditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.ludersUpdate_isBayesianConditional

/-- info: 'CSD.FND.historyConditioning_isBayesianConditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.historyConditioning_isBayesianConditional

-- FND-T5 unified many-to-one measurement capstone (2026-07-15): dynamics + measurement on ONE ontic
-- model. unified_choiceA_capstone puts BOTH the isolated Hamiltonian flow (productDynamics, exp(-itH)•)
-- AND the de-isolation measurement (measurementFlow on the base fibre) on the SAME (Σ=ℂℙ^{M}×T², μL=μFS⊗
-- vol, π=Prod.fst): flow measure-preserving + Schrödinger-projectable + FS pushforward + interaction
-- measure-preserving + a.e. readout (T6, lifted through π) + record establishment (B5). Removes the
-- forward-vs-measurement model split. unifiedDeisolationModel_ae_total lifts the base a.e. via Prod.fst.
/-- info: 'CSD.FND.unified_choiceA_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.unified_choiceA_capstone

/-- info: 'CSD.FND.unifiedDeisolationModel_ae_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.unifiedDeisolationModel_ae_total

-- FND P3 SOLVED via local tomography (2026-07-15): composite_is_tensor_product. The composite observable
-- algebra IS the tensor product of the local ones -- compositeTensorEquiv (= kroneckerLinearEquiv) is a
-- SUFFICIENCY (2026-07-17 downgrade): BIJECTIVE linear iso M_{NA} ⊗ M_{NB} ≃ M_{NA·NB} sending
-- U ⊗ₜ Q ↦ aliceOp U · bobOp Q -- the standard tensor model REALIZES locality (commuting) + local tomography
-- (joint_mem_span_local). This is SUFFICIENCY, not uniqueness; the NECESSITY half (any composite with
-- commuting, generating local algebras IS the tensor product) is TensorReconstruction.lean below.
/-- info: 'CSD.FND.composite_is_tensor_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.composite_is_tensor_product

-- FND P3 RECONSTRUCTION (2026-07-17, TensorReconstruction.lean): the NECESSITY/uniqueness half.
-- compositeAlgReconstruction: commuting local embeddings M_m, M_n whose images GENERATE 𝒜 give an ALGEBRA
-- EQUIVALENCE M_m ⊗ M_n ≃ₐ 𝒜 (injective since M_m⊗M_n is SIMPLE -- matrixTensor_isSimpleRing; surjective
-- from generation). composite_dim_eq: for 𝒜 = M_k, forces k = m·n -- discharging bridge B6
-- (CompositeSector.tensor_dimension) as a THEOREM. So locality + generation FORCE ⊗, not just admit it.
/-- info: 'CSD.FND.compositeAlgReconstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.compositeAlgReconstruction

/-- info: 'CSD.FND.composite_dim_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.composite_dim_eq

-- FND P3 BRIDGE B6 DISCHARGED (2026-07-17): CompositeSector.ofReconstruction builds a CompositeSector
-- whose tensor_dimension (NA*NB=Njoint) FIELD is filled by composite_dim_eq -- derived from commuting,
-- generating local embeddings, not posited. So B6 is no longer a bare assumption.
/-- info: 'CSD.FND.CompositeSector.ofReconstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.CompositeSector.ofReconstruction

-- ECDLP value-exact CONSTPROP pass (2026-07-17, Reversible/ConstProp.lean, the frontier's Toffoli lever):
-- cprop folds provably-determined CCX (known-0 control -> drop; known-1 -> CX). cprop_denote MACHINE-CHECKS
-- value-exactness (denote (cprop α c) s = denote c s for s the seed α describes), via foldGate_denote
-- (per-gate fold is value-exact) + stepAbs_agree (the forward abstract state stays sound). The informal
-- frontier lever, here a proved circuit-to-circuit transform.
/-- info: 'Reversible.cprop_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Reversible.cprop_denote

/-- info: 'Reversible.foldGate_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Reversible.foldGate_denote

/-- info: 'Reversible.stepAbs_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Reversible.stepAbs_agree

/-- info: 'CSD.FND.compositeTensorEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.compositeTensorEquiv_apply

-- FND P3 resolution + localized A5 (2026-07-15): reducing the two deep posits.
-- P3 (why tensor): single_prod (the joint basis matrix = product of local ones) + joint_mem_span_local
-- (the commuting local subalgebras GENERATE the whole joint algebra) -- the tensor product carries no
-- observables beyond local ones and their products, so B6 reduces from "posit ⊗" to "posit two full
-- local algebras that act and commute". A5 (sector origin) LOCALIZED: forcedVolume_unique /
-- region_measure_symmetry_forced (any two U(N)-invariant measures give the same region weights, so the
-- Born weights are symmetry-forced, not measure-chosen); localised_A5_capstone (the concrete sector's
-- typicality is forced by the U(N) symmetry the flow is part of -- "A5 in the appropriate places").
-- Neither closes the universal posit (P3 "why ⊗" / A5 sector-from-bare-flow); both reduce where it bites.
/-- info: 'CSD.FND.single_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.single_prod

/-- info: 'CSD.FND.joint_mem_span_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.joint_mem_span_local

/-- info: 'CSD.FND.region_measure_symmetry_forced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.region_measure_symmetry_forced

/-- info: 'CSD.FND.localised_A5_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.localised_A5_capstone

-- FND A5 NO-GO (2026-07-15): the single-flow limit made a PROVED boundary. A projective unitary flow with
-- two distinct fixed rays admits an invariant probability measure /= mu_FS (the two fixed-ray Diracs), so a
-- single deterministic flow does NOT pin the sector's typicality measure -- "A5 is posited" is a theorem
-- about the limit, not a formalisation gap. phaseFlip_admits_invariant_ne_fubiniStudy exhibits it on the
-- concrete nontrivial flow diag(1,-1) on CP^1. Positive companion: region_measure_symmetry_forced (full U(N)
-- symmetry DOES pin mu_FS). Matches Paper C (S1.4): Sigma, pi, the A5 sector are assumed, not derived.
/-- info: 'CSD.FND.flow_admits_invariant_ne_fubiniStudy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.flow_admits_invariant_ne_fubiniStudy

/-- info: 'CSD.FND.phaseFlip_admits_invariant_ne_fubiniStudy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.phaseFlip_admits_invariant_ne_fubiniStudy

-- FND Bell/contextuality generality (2026-07-14): the UNIVERSAL bounds behind the per-instance T13/T14
-- witnesses. lhv_chsh_le_two (every LHV: |S| ≤ 2), qm_chsh_le_tsirelson (every state: |S| ≤ 2√2),
-- cglmp_lhv_le_two (every LHV table, every d: cglmp ≤ 2), bell_general_separation (2 < 2√2, gap attained
-- by the singlet), general_ks_noNonContextualValuation (any parity-(18,9) config, not just Cabello-18).
/-- info: 'CSD.FND.lhv_chsh_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.lhv_chsh_le_two

/-- info: 'CSD.FND.qm_chsh_le_tsirelson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.qm_chsh_le_tsirelson

/-- info: 'CSD.FND.bell_general_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.bell_general_separation

/-- info: 'CSD.FND.general_ks_noNonContextualValuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.general_ks_noNonContextualValuation

-- FND T8: the projective (Lüders) update (2026-07-14). luders_capstone bundles the three defining
-- properties of the projective post-measurement update ludersUpdate p x = (‖p x‖)⁻¹ • p x: normalised,
-- repeatable (p fixes it, so re-measurement is certain), and Lüders = conditional probability
-- (ludersUpdate_conditional: the updated Born weight of a finer projection q is projWeight q x /
-- projWeight p x). projWeight_eq_re_inner ties the weight ‖p x‖² to the effect form Re⟨x, p x⟩;
-- isProjection_toEuclideanLin connects matrix projectors. Closes the T8 gap left by MeasurementRecord.
/-- info: 'CSD.FND.luders_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.luders_capstone

/-- info: 'CSD.FND.ludersUpdate_conditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.ludersUpdate_conditional

/-- info: 'CSD.FND.projWeight_eq_re_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.projWeight_eq_re_inner

-- FND T7: the general (non-projective) conditional state update (2026-07-14). conditionalUpdate_capstone
-- bundles the general Kraus/effect update stateUpdate M x = (‖M x‖)⁻¹ • M x for a measurement operator M
-- (effect E = M† M): normalised, outcome weight = Re⟨x, M† M x⟩ (updateWeight_eq_re_inner), and the
-- sequential (Wigner) rule stateUpdate_sequential (updateWeight N (stateUpdate M x) = updateWeight N
-- (M x) / updateWeight M x). Lüders (T8) is the sharp special case (stateUpdate_eq_ludersUpdate); T7
-- needs neither self-adjointness nor idempotence.
/-- info: 'CSD.FND.conditionalUpdate_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.conditionalUpdate_capstone

/-- info: 'CSD.FND.stateUpdate_sequential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.stateUpdate_sequential

/-- info: 'CSD.FND.stateUpdate_eq_ludersUpdate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.stateUpdate_eq_ludersUpdate

-- FND T9: the mixed-state representation (2026-07-14). Closes the density-matrix gap on the statistical
-- side. mixedState_capstone / traceForm_mix: the convex mixture mix p ρ₁ ρ₂ is a density operator and
-- the Born rule traceForm is affine in the state (Tr((p ρ₁ + (1-p) ρ₂) E) = p Tr(ρ₁ E) + (1-p) Tr(ρ₂ E)).
-- rankOneDensity_isPure: pure states are the rank-one projectors; maximallyMixed_not_isPure: I/N is a
-- genuinely mixed state for N ≥ 2 (non-vacuity). Built on LF2.DensityOperator/Effect/traceForm; the
-- purity converse Tr(ρ²)=1 → ρ²=ρ (spectral theorem) is left as a residue.
/-- info: 'CSD.FND.mixedState_capstone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.mixedState_capstone

/-- info: 'CSD.FND.traceForm_mix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.traceForm_mix

/-- info: 'CSD.FND.maximallyMixed_not_isPure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.maximallyMixed_not_isPure

-- T9 purity converse (2026-07-14): the spectral-theorem direction, closing the residue. IsPure ρ ↔
-- Tr(ρ²)=1 (isPure_iff_trace_sq_one); the converse isPure_of_trace_sq_one uses Matrix spectral theory
-- (∑λᵢ = ∑λᵢ² = 1, λᵢ ≥ 0 ⇒ λᵢ ∈ {0,1} ⇒ ρ² = ρ). Foundational triple.
/-- info: 'CSD.FND.isPure_of_trace_sq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.isPure_of_trace_sq_one

/-- info: 'CSD.FND.isPure_iff_trace_sq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CSD.FND.isPure_iff_trace_sq_one

end CSD.Tests.AxiomAudit
