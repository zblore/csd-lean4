/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.Normed.Lp.Matrix
public import CsdLean4.Mathlib.Analysis.Matrix.OperatorConvex
public import CsdLean4.Mathlib.Analysis.Matrix.OperatorConvexBridge
public import CsdLean4.Mathlib.Analysis.Matrix.StoneC1
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Topology
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.MeasureSpace
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Unitary
public import CsdLean4.Mathlib.LinearAlgebra.Matrix.UnitaryCompact
public import CsdLean4.Mathlib.LinearAlgebra.Matrix.UnitaryHaar
public import CsdLean4.Mathlib.LinearAlgebra.Matrix.PartialTrace
public import CsdLean4.Mathlib.MeasureTheory.LintegralFintypeProd
public import CsdLean4.Mathlib.Probability.IIDCoordinateProcess
public import CsdLean4.Mathlib.Probability.CGLMP
public import CsdLean4.Mathlib.QuantumInfo.Channel
public import CsdLean4.Mathlib.QuantumInfo.Stinespring
public import CsdLean4.Mathlib.QuantumInfo.CanonicalChannels
public import CsdLean4.Mathlib.QuantumInfo.TraceDistance
public import CsdLean4.Mathlib.QuantumInfo.DataProcessing
public import CsdLean4.Mathlib.QuantumInfo.Entropy
public import CsdLean4.Mathlib.QuantumInfo.PartialTrace
public import CsdLean4.Mathlib.QuantumInfo.Subadditivity
public import CsdLean4.Mathlib.QuantumInfo.StrongSubadditivity
public import CsdLean4.Mathlib.QuantumInfo.Register
public import CsdLean4.Mathlib.QuantumInfo.Hadamard
public import CsdLean4.Mathlib.QuantumInfo.Fourier
public import CsdLean4.Mathlib.QuantumInfo.Reversible.Circuit
public import CsdLean4.Mathlib.QuantumInfo.Reversible.Cost
public import CsdLean4.Mathlib.QuantumInfo.Reversible.ConstProp
public import CsdLean4.Mathlib.QuantumInfo.Reversible.ModAdd
public import CsdLean4.Mathlib.QuantumInfo.Reversible.ModMul
public import CsdLean4.Mathlib.QuantumInfo.Reversible.ModInv
public import CsdLean4.Mathlib.QuantumInfo.Reversible.ModReduce
public import CsdLean4.Mathlib.QuantumInfo.Reversible.CtrlAdd
public import CsdLean4.Mathlib.QuantumInfo.Reversible.CtrlMul
public import CsdLean4.Mathlib.QuantumInfo.Reversible.ModReduceCtrl
public import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularAdd
public import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularAddCtrl
public import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularDouble
public import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularSub
public import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularConst
public import CsdLean4.Mathlib.QuantumInfo.Reversible.Depth
public import CsdLean4.Mathlib.QuantumInfo.Reversible.Eval
public import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularMul
public import CsdLean4.Mathlib.QuantumInfo.Reversible.ModularMulLoop
public import CsdLean4.Mathlib.QuantumInfo.Reversible.VerifiedAdder
public import CsdLean4.Mathlib.QuantumInfo.Reversible.CuccaroAdd
public import CsdLean4.Mathlib.QuantumInfo.Reversible.CuccaroModAdd
public import CsdLean4.Mathlib.QuantumInfo.Reversible.CuccaroModMul
public import CsdLean4.Mathlib.QuantumInfo.Reversible.VerifiedAdderCarryClean
public import CsdLean4.Mathlib.QuantumInfo.Reversible.AndAdd
public import CsdLean4.Mathlib.QuantumInfo.Reversible.GidneyAdder
public import CsdLean4.Mathlib.Analysis.InnerProductSpace.KahlerForm
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudy
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.UnitaryTransitive
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.FubiniStudyUnique
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.TransitionProbability
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.WignerRigidity
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.PhaseRigidity
public import CsdLean4.Mathlib.LinearAlgebra.Projectivization.Bargmann
public import CsdLean4.Mathlib.Topology.Algebra.Module.LinearMap
public import CsdLean4.LF1.Setup
public import CsdLean4.LF1.Preparation
public import CsdLean4.LF1.Outcomes
public import CsdLean4.LF1.Trials
public import CsdLean4.LF1.Indicators
public import CsdLean4.LF1.Expectation
public import CsdLean4.LF1.Convergence
public import CsdLean4.LF1.MainTheorem
public import CsdLean4.LF1.GeneralFrequency
public import CsdLean4.LF2.Setup
public import CsdLean4.LF2.MeasureBridge
public import CsdLean4.LF2.Weights
public import CsdLean4.LF2.BornWrapper
public import CsdLean4.LF2.EffectGleason
public import CsdLean4.LF2.ReducedDensity
public import CsdLean4.LF2.MixedEnsembleIx
public import CsdLean4.LF2.ChoiConverse
public import CsdLean4.LF2.PhaseInvariance
public import CsdLean4.LF2.EffectFn
public import CsdLean4.LF2.Preparation
public import CsdLean4.LF2.Interface
public import CsdLean4.LF2.POVM
public import CsdLean4.LF2.EffectAux
public import CsdLean4.LF3.Setup
public import CsdLean4.LF3.Hamiltonian
public import CsdLean4.LF3.SectorSeparation
public import CsdLean4.LF3.Projectors.Core
public import CsdLean4.LF3.Projectors.SectorVolume
public import CsdLean4.LF3.Projectors.LF2Interface
public import CsdLean4.LF3.Projectors.TensorModel
public import CsdLean4.LF3.Singlet.State
public import CsdLean4.LF3.Singlet.Expectations
public import CsdLean4.LF3.Singlet.Kernel
public import CsdLean4.LF3.Singlet.JointProjector
public import CsdLean4.LF3.Singlet.JointEig
public import CsdLean4.LF3.Singlet.Leakage
public import CsdLean4.LF3.ContextMap
public import CsdLean4.LF3.SingletProjective
public import CsdLean4.LF3.PurePreparation
public import CsdLean4.LF3.Interface
public import CsdLean4.LF4.Instance
public import CsdLean4.LF4.KahlerInstance
public import CsdLean4.LF4.KahlerFlow
public import CsdLean4.LF4.KahlerOnticSetup
public import CsdLean4.LF4.NonTrivialSetup
public import CsdLean4.LF4.UnitarySelection
public import CsdLean4.LF4.BargmannSelection
public import CsdLean4.LF4.ProjectedDynamics
public import CsdLean4.LF4.PhaseLift
public import CsdLean4.LF4.RotationSchrodinger
public import CsdLean4.LF4.BothPillars
public import CsdLean4.LF4.ManyToOnePillars
public import CsdLean4.LF4.ManyToOneSchrodingerDerived
public import CsdLean4.LF4.MomentMap
public import CsdLean4.LF4.ObservableFlow
public import CsdLean4.LF4.TypicalityForcing
public import CsdLean4.LF4.BornVolume
public import CsdLean4.LF4.MomentPushforward
public import CsdLean4.LF4.BornFS
public import CsdLean4.LF4.QubitBornFrequency
public import CsdLean4.LF4.BornFrequencyPartition
public import CsdLean4.LF4.MomentMarginal
public import CsdLean4.LF4.DuistermaatHeckman
public import CsdLean4.LF4.GaussianFS
public import CsdLean4.LF4.GaussianCP
public import CsdLean4.LF4.GaussianCPN
public import CsdLean4.LF4.MomentMarginalUniform
public import CsdLean4.LF4.MomentRatioUniformN
public import CsdLean4.LF4.MomentRatioUniform
public import CsdLean4.LF4.MomentUniform
public import CsdLean4.LF4.MomentBridgeN
public import CsdLean4.LF4.MomentDirichletN
public import CsdLean4.LF4.MomentBornN
public import CsdLean4.LF4.ObservableCorrespondenceN
public import CsdLean4.LF4.BornFrequencyN
public import CsdLean4.LF4.QubitConsistency
public import CsdLean4.LF4.SingletKahler
public import CsdLean4.LF4.SingletKahlerFlow
public import CsdLean4.LF4.KahlerWignerLift
public import CsdLean4.LF4.KahlerVolumeForced
public import CsdLean4.LF4.SchrodingerKahlerInvariance
public import CsdLean4.LF4.SingleQubitKahler
public import CsdLean4.LF4.SingletObservables
public import CsdLean4.LF4.HardyKahler
public import CsdLean4.LF4.SpectralExpansion
public import CsdLean4.LF4.SpectralCarving
public import CsdLean4.LF4.SpectralVariance
public import CsdLean4.LF4.UncertaintyKahler
public import CsdLean4.LF4.PauliRobertson
public import CsdLean4.LF4.PauliDotRobertson
public import CsdLean4.LF4.OnticBorn
public import CsdLean4.LF4.POVMDilation
public import CsdLean4.LF4.POVMVolume
public import CsdLean4.LF4.POVMNaimark
public import CsdLean4.LF4.BornRegionUncond
public import CsdLean4.LF4.BornRegionDisjoint
public import CsdLean4.LF4.BornFlowLinkage
public import CsdLean4.LF4.TrialWitness
public import CsdLean4.LF5.VonNeumannUnitary
public import CsdLean4.LF5.MeasurementFlow
public import CsdLean4.LF5.DilationFromFlow
public import CsdLean4.LF5.FlowBornFrequency
public import CsdLean4.LF5.Capstone
public import CsdLean4.LF5.CapstoneCanonical
public import CsdLean4.LF5.PointerOutcome
public import CsdLean4.LF5.SyndromeFlow
public import CsdLean4.LF5.SyndromeOutcome
public import CsdLean4.LF6.ForcedContextuality
public import CsdLean4.LF6.GHZContextuality
public import CsdLean4.LF6.SingletDeisolationFlow
public import CsdLean4.LF6.GHZDeisolationFlow
public import CsdLean4.LF6.GHZMerminCarve
public import CsdLean4.LF6.LocalDeisolationFlow
public import CsdLean4.LF6.GHZLocalFlow
public import CsdLean4.LF6.Decoherence
public import CsdLean4.LF6.MaxEntangledDeisolationFlow
public import CsdLean4.LF6.PartialSchmidtCorrelation
public import CsdLean4.LF6.GisinTheorem
public import CsdLean4.LF6.DephasingSemigroup
public import CsdLean4.LF6.AmplitudeDamping
public import CsdLean4.LF6.LindbladGenerator
public import CsdLean4.LF6.CGLMPQutrit
public import CsdLean4.LF6.CGLMPQudit
public import CsdLean4.LF6.MaxEntangledCGLMPCapstone
public import CsdLean4.LF6.GHZnDeisolationFlow
public import CsdLean4.Empirical.QM.Bell
public import CsdLean4.Empirical.QM.NoCloning
public import CsdLean4.Empirical.QM.NoDeleting
public import CsdLean4.Empirical.QM.Resources.SuperdenseCoding
public import CsdLean4.Empirical.QM.Resources.Teleportation
public import CsdLean4.Empirical.QM.NoCommunication
public import CsdLean4.Empirical.QM.NoBroadcasting
public import CsdLean4.Empirical.QM.Protocols.Basic
public import CsdLean4.Empirical.QM.Crypto.QuantumMoney
public import CsdLean4.Empirical.QM.Crypto.E91
public import CsdLean4.Empirical.QM.Crypto.E91KeyRate
public import CsdLean4.Empirical.QM.Crypto.E91FiniteKey
public import CsdLean4.Empirical.QM.Crypto.WiesnerProtocol
public import CsdLean4.Empirical.QM.USD
public import CsdLean4.Empirical.QM.QEC.ThreeQubit
public import CsdLean4.Empirical.QM.QEC.PhaseFlip
public import CsdLean4.Empirical.QM.QEC.BitFlipChannel
public import CsdLean4.Empirical.QM.Uncertainty
public import CsdLean4.Empirical.QM.Multipartite.GHZ
public import CsdLean4.Empirical.QM.Contextuality.KS18
public import CsdLean4.Empirical.QM.Contextuality.MerminPeres
public import CsdLean4.Empirical.QM.Hardy
public import CsdLean4.Empirical.QM.SternGerlach
public import CsdLean4.Empirical.QM.Malus
public import CsdLean4.Empirical.QM.Algorithms.DeutschJozsa
public import CsdLean4.Empirical.QM.Algorithms.Simon
public import CsdLean4.Empirical.QM.Algorithms.SwapTest
public import CsdLean4.Empirical.QM.Algorithms.HadamardTest
public import CsdLean4.Empirical.QM.Algorithms.BernsteinVazirani
public import CsdLean4.Empirical.QM.Algorithms.Grover
public import CsdLean4.Empirical.QM.Algorithms.ShorCore
public import CsdLean4.Empirical.QM.Algorithms.ShorRecovery
public import CsdLean4.Empirical.QM.Algorithms.ShorRandomA
public import CsdLean4.Empirical.QM.Algorithms.ShorCapstone
public import CsdLean4.Empirical.CSD.Framework
public import CsdLean4.Empirical.CSD.Bell
public import CsdLean4.Empirical.CSD.NoCloning
public import CsdLean4.Empirical.CSD.NoDeleting
public import CsdLean4.Empirical.CSD.NoBroadcasting
public import CsdLean4.Empirical.CSD.NoCommunication
public import CsdLean4.Empirical.CSD.Uncertainty
public import CsdLean4.Empirical.CSD.SternGerlach
public import CsdLean4.Empirical.CSD.SternGerlachVolume
public import CsdLean4.Empirical.CSD.MachZehnderVolume
public import CsdLean4.Empirical.CSD.DoubleSlitVolume
public import CsdLean4.Empirical.CSD.MalusVolume
public import CsdLean4.Empirical.CSD.BellVolume
public import CsdLean4.Empirical.CSD.GHZVolume
public import CsdLean4.Empirical.CSD.HardyVolume
public import CsdLean4.Empirical.CSD.ContextVolume
public import CsdLean4.Empirical.CSD.UncertaintyVolume
public import CsdLean4.Empirical.CSD.TrineVolume
public import CsdLean4.Empirical.CSD.USDVolume
public import CsdLean4.Empirical.CSD.SICVolume
public import CsdLean4.Empirical.CSD.QutritPOVMVolume
public import CsdLean4.Empirical.CSD.WeakMeasurement
public import CsdLean4.Empirical.CSD.QuantumZeno
public import CsdLean4.Empirical.CSD.SIC3Volume
public import CsdLean4.Empirical.CSD.MUB3Volume
public import CsdLean4.Empirical.CSD.VolumeCanonical
public import CsdLean4.Empirical.CSD.Resources.SuperdenseCoding
public import CsdLean4.Empirical.CSD.Resources.Teleportation
public import CsdLean4.Empirical.CSD.Crypto.QuantumMoney
public import CsdLean4.Empirical.CSD.Crypto.E91
public import CsdLean4.Empirical.CSD.QEC.ThreeQubit
public import CsdLean4.Empirical.CSD.Contextuality.KS18
public import CsdLean4.Empirical.CSD.Contextuality.KS18Volume
public import CsdLean4.Empirical.CSD.Contextuality.MerminPeres
public import CsdLean4.Empirical.CSD.Contextuality.MerminPeresVolume
public import CsdLean4.Empirical.CSD.Hardy
public import CsdLean4.Empirical.CSD.Multipartite.GHZ
public import CsdLean4.Empirical.QM.Gates.SingleQubit
public import CsdLean4.Empirical.QM.Gates.TwoQubit
public import CsdLean4.Empirical.QM.Gates.BellPrep
public import CsdLean4.Empirical.QM.Gates.MultiQubit
public import CsdLean4.Empirical.QM.MeasurementUncompute
public import CsdLean4.Empirical.QM.MeasurementUncomputeLift
public import CsdLean4.Empirical.QM.MeasurementAdder
public import CsdLean4.Empirical.QM.MeasurementGidneyAdder
public import CsdLean4.Empirical.QM.MeasurementAdderHierarchy
public import CsdLean4.Empirical.CSD.Gates.Framework
public import CsdLean4.Empirical.CSD.Gates.SingleQubit
public import CsdLean4.Empirical.CSD.Gates.TwoQubit
public import CsdLean4.Empirical.CSD.Gates.BellPrep
public import CsdLean4.Empirical.CSD.Gates.MultiQubit
public import CsdLean4.Empirical.CSD.Gates.WignerDischarge
public import CsdLean4.Empirical.CSD.Gates.SingleQubitDischarge
public import CsdLean4.Empirical.CSD.Gates.TwoQubitDischarge
public import CsdLean4.Empirical.CSD.Gates.MultiQubitDischarge
public import CsdLean4.Empirical.CSD.Gates.BellPrepDischarge
public import CsdLean4.Empirical.CSD.Einselection
public import CsdLean4.Empirical.CSD.QECDecoherence
public import CsdLean4.Empirical.CSD.ChannelCapacity
public import CsdLean4.Empirical.Metrology.Ramsey
public import CsdLean4.Empirical.Metrology.QuantumFisher
public import CsdLean4.Empirical.Metrology.Heisenberg
public import CsdLean4.CV.ApproxCCR
public import CsdLean4.CV.Position
public import CsdLean4.CV.Oscillator
public import CsdLean4.CV.OscillatorSpectrum
public import CsdLean4.Thermo.CanonicalTypicality
public import CsdLean4.Thermo.SecondLaw
public import CsdLean4.Thermo.FreeEnergy
public import CsdLean4.Thermo.Landauer
public import CsdLean4.SigmaLayer.ConstraintSurface
public import CsdLean4.SigmaLayer.ConstraintDynamics
public import CsdLean4.SigmaLayer.RecordedFact
public import CsdLean4.SigmaLayer.IsolationPreparation
public import CsdLean4.SigmaLayer.ProjectiveSector
public import CsdLean4.SigmaLayer.TheoremTargets
public import CsdLean4.SigmaLayer.Adapters
public import CsdLean4.SigmaLayer.MeasureBridge
public import CsdLean4.SigmaLayer.DynamicsBridge
public import CsdLean4.SigmaLayer.MeasurementRecord
public import CsdLean4.SigmaLayer.LiftedMeasurement
public import CsdLean4.SigmaLayer.UnifiedMeasurement
public import CsdLean4.SigmaLayer.UnifiedFlowedRecords
public import CsdLean4.SigmaLayer.ConditioningLink
public import CsdLean4.SigmaLayer.ConditioningLuders
public import CsdLean4.SigmaLayer.PostMeasurement
public import CsdLean4.SigmaLayer.TimeIndexedRecord
public import CsdLean4.SigmaLayer.ForwardCapstone
public import CsdLean4.SigmaLayer.CompositeInterface
public import CsdLean4.SigmaLayer.CompositeAdapters
public import CsdLean4.SigmaLayer.BellGenerality
public import CsdLean4.SigmaLayer.TensorGeneration
public import CsdLean4.SigmaLayer.TensorSolved
public import CsdLean4.SigmaLayer.TensorReconstruction
public import CsdLean4.SigmaLayer.LocalisedTypicality
public import CsdLean4.SigmaLayer.SectorPostulateNoGo
public import CsdLean4.SigmaLayer.UniqueErgodicity
public import CsdLean4.SigmaLayer.Interference
public import CsdLean4.SigmaLayer.TensorSector
public import CsdLean4.SigmaLayer.Luders
public import CsdLean4.SigmaLayer.ConditionalUpdate
public import CsdLean4.SigmaLayer.MixedState
-- Tests/ deliberately excluded from the consumer-facing root. Build via
-- `lake build CsdLeanTests` (see lakefile.lean) to exercise the
-- AxiomAudit regression suite and Examples worked computations.

/-!
# CSD

**Category:** Special (canonical top-level import; explicit module list across LF1 + LF2 + LF3 + Empirical + Mathlib upstream-tracking).

Tests/ is deliberately excluded from this consumer-facing root — build
the regression suite separately via `lake build CsdLeanTests`.

Top-level import file for the Constraint-Surface Dynamics Lean4 project.

This file exports:
- **LF1**: volume typicality and repeated-trial frequency convergence for
  deterministic repeated trials.
- **LF2**: the measure bridge from ontic Liouville volume to projective
  Fubini–Study measure, and the Born-weight wrapper packaging the
  finite-dimensional probability assignment under explicit external-theorem
  inputs.
- **LF3**: the singlet kernel `(1 − st a·b)/4`, the operational pointer-sector
  decomposition (kernel + correlation + marginals + no-signalling + pointer-
  completeness, with finite-leakage stability), and the LF1↔LF2↔LF3 empirical
  chain capstone (`LF3_singlet_frequency_convergence`,
  `LF3_singlet_frequency_convergence_born`).
- **Empirical**: named experimentally-verified predictions — the Bell-family
  CHSH content (Phase A1–A6) and the no-cloning theorem (Phase B2). The
  Bell items re-export the LF3 singlet kernel content under
  empirical-prediction names with experimental provenance; the no-cloning
  theorem is QM-generic Hilbert-space content.
- **Mathlib**: project-side patches to Mathlib (currently the
  `Projectivization` quotient-topology infrastructure pending upstream).
-/
